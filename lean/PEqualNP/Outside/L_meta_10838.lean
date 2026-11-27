import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10838
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffefffefffffffffffffffffffffffffefefcfcfffefffefffefffeffeeffeeffeeffeefefefefefafafafaeeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 6 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def nineInputs : List Sig := vars 511
def sampleNine (r : Row) (i : Fin 9) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 6 && x 8)

theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 9 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]
  rfl

theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),nineSampled]
  rfl
def neighborRow (i : Fin 9) : Nat := [4,5,6,7,0,1,0,0,1].getD i.val 0
def absentRowRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = nineEdge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k nineInputs.toFinset := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates nineInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 9, nineInputs.getD i.val zero = a := by
    rw [←nineList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRowRow i) (presentRowRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k nineInputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k nineInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 nineEdge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

def g290Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffff3,0x12),(0x0,0x0),(0x0,0x0),(0x3c,0x28)]
def g290C : List ColumnInfo := []
def g290A : List (List Nat) := [[],[81],[129],[133],[81,129],[129,81]]
def g290D3 (j : Nat) : Nat := 0x7
def g290L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g290D3)
  | _ => emptyPacking
def g290I (_ _ : Nat) : Option (Nat × Nat) := none
def g290 : Forest := ⟨290,3,fun i => g290Y[i]?.getD (0,0),g290C,g290A,g290L,g290I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g290P3_0 : block g290 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g290B3 : block g290 3 0 1=true := g290P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g290T : checkedTables g290 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g290 0 0 0 = true)
  · exact (rfl : block g290 1 0 0 = true)
  · exact (rfl : block g290 2 0 0 = true)
  · exact g290B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g290G : graphValid g290 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low290 : Lower true (varsX 290) (graphGoal 290) 4 := lower_forest (g:=g290) (i:=0) (hints:=4296015952) (before_sound [] baseKnown) g290G g290T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K290 := extendKnown [] 4 [(290,[]),(324,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V290 : Known true K290 := extend_ok (m:=290) baseKnown low290 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffff3f,0xffffffffffffffffffffffffffffffffffff15),(0x0,0x0),(0xcc,0xcc),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffff8f,0x8a),(0x0,0x0),(0xf0,0x20),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := []
def g85A : List (List Nat) := [[],[96,66]]
def g85D3 (j : Nat) : Nat := 0xf
def g85L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g85D3)
  | _ => emptyPacking
def g85I (_ _ : Nat) : Option (Nat × Nat) := none
def g85 : Forest := ⟨85,3,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P3_0 : block g85 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B3 : block g85 3 0 1=true := g85P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact g85B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K290) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 4 := lower_forest (g:=g85) (i:=0) (hints:=1540) (before_sound K290 V290) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K290 4 [(85,[]),(147,[33,118]),(153,[50,118]),(163,[16,32,84,118]),(170,[16,50,84,118]),(195,[33,100,116,84]),(197,[116,84]),(323,[128,112,80,64,16,32]),(337,[130,114,82,50]),(353,[128,112,64,80,48,32]),(387,[16,32,132,100,116,84]),(390,[16,116,84,134]),(449,[130,82,50,116]),(450,[16,98,130,82,50,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V290 low85 (by decide +kernel)
def g294Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffc3f,0xfffffffffffffffffffffffffffffffffffc15),(0xcc,0x4c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffff0f,0x10a),(0x0,0x0),(0x0,0x0),(0x3f0,0x2a0)]
def g294C : List ColumnInfo := [(4,0,290,0,4)]
def g294A : List (List Nat) := [[],[81]]
def g294D4 (j : Nat) : Nat := 0x1f
def g294L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g294D4)
  | _ => emptyPacking
def g294I (_ _ : Nat) : Option (Nat × Nat) := none
def g294 : Forest := ⟨294,4,fun i => g294Y[i]?.getD (0,0),g294C,g294A,g294L,g294I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g294P4_0 : block g294 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g294B4 : block g294 4 0 1=true := g294P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g294T : checkedTables g294 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g294 0 0 0 = true)
  · exact (rfl : block g294 1 0 0 = true)
  · exact (rfl : block g294 2 0 0 = true)
  · exact (rfl : block g294 3 0 0 = true)
  · exact g294B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g294G : graphValid g294 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low294 : Lower true (varsX 294) (graphGoal 294) 5 := lower_forest (g:=g294) (i:=0) (hints:=4296018000) (before_sound K85 V85) g294G g294T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K294 := extendKnown K85 5 [(294,[]),(325,[16,32,133,101]),(354,[98,66,50]),(356,[33,81,97,65,49]),(418,[81,129,114,98,66,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V294 : Known true K294 := extend_ok (m:=294) V85 low294 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffe0ff,0xffffffffffffffffffffffffffffffffffe055),(0x130c,0x110c),(0x0,0x0),(0xc30,0x430),(0xfffffffffffffffffffffffffffffffffff03f,0x102a),(0x0,0x0),(0x0,0x0),(0x1fc0,0xa80),(0x0,0x0)]
def g155C : List ColumnInfo := [(8,0,147,0,4)]
def g155A : List (List Nat) := [[],[49]]
def g155D4 (j : Nat) : Nat := 0x3f
def g155L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g155D4)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,4,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 1=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K294) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 5 := lower_forest (g:=g155) (i:=0) (hints:=28788) (before_sound K294 V294) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K294 5 [(155,[]),(213,[96,80,48,112,65,33]),(465,[96,48,112,65,129,81,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V294 low155 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffff3cf,0xfffffffffffffffffffffffffffffffffff1c5),(0xc7c,0x85c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffe88f,0x80a),(0x10f0,0x10a0),(0x0,0x0),(0x1f00,0x600),(0x0,0x0)]
def g179C : List ColumnInfo := []
def g179A : List (List Nat) := [[],[16,84]]
def g179D4 (j : Nat) : Nat := 0x1f
def g179L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g179D4)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,4,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : block g179 4 0 1=true := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact g179B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 5 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound K155 V155) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K155 5 [(179,[]),(199,[112,97,81,33,49,65]),(227,[100]),(369,[129,113,97,49,33]),(391,[112,16,128,96,80,32,48,64]),(481,[129,65,113,97,49,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
def g307Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff1c3cf,0xfffffffffffffffffffffffffffffffff0c1c5),(0x27cfc,0x2545c),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff38f0f,0x30e0a),(0xc0ff0,0x40ba0),(0x0,0x0),(0x0,0x0),(0xff000,0x9a000)]
def g307C : List ColumnInfo := [(0,16,290,1,5)]
def g307A : List (List Nat) := [[],[64],[81],[129],[133],[64,81],[64,129],[64,133],[81,129],[129,81],[64,81,129],[64,129,81]]
def g307D5 (j : Nat) : Nat := 0x3f
def g307L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g307D5)
  | _ => emptyPacking
def g307I (_ _ : Nat) : Option (Nat × Nat) := none
def g307 : Forest := ⟨307,5,fun i => g307Y[i]?.getD (0,0),g307C,g307A,g307L,g307I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g307P5_0 : block g307 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g307B5 : block g307 5 0 1=true := g307P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g307T : checkedTables g307 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g307 0 0 0 = true)
  · exact (rfl : block g307 1 0 0 = true)
  · exact (rfl : block g307 2 0 0 = true)
  · exact (rfl : block g307 3 0 0 = true)
  · exact (rfl : block g307 4 0 0 = true)
  · exact g307B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g307G : graphValid g307 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low307 : Lower true (varsX 307) (graphGoal 307) 6 := lower_forest (g:=g307) (i:=0) (hints:=4296015956) (before_sound K179 V179) g307G g307T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K307 := extendKnown K179 6 [(307,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V307 : Known true K307 := extend_ok (m:=307) V179 low307 (by decide +kernel)
def g327Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffff960f,0xffffffffffffffffffffffffffffffffff9605),(0x7cc,0x2cc),(0x1870,0x810),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffe07f,0x206a),(0x0,0x0),(0x7f80,0x5500)]
def g327C : List ColumnInfo := [(2,0,325,0,5)]
def g327A : List (List Nat) := [[],[16,134]]
def g327D5 (j : Nat) : Nat := 0x3f
def g327L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g327D5)
  | _ => emptyPacking
def g327I (_ _ : Nat) : Option (Nat × Nat) := none
def g327 : Forest := ⟨327,5,fun i => g327Y[i]?.getD (0,0),g327C,g327A,g327L,g327I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g327P5_0 : block g327 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g327B5 : block g327 5 0 1=true := g327P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g327T : checkedTables g327 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g327 0 0 0 = true)
  · exact (rfl : block g327 1 0 0 = true)
  · exact (rfl : block g327 2 0 0 = true)
  · exact (rfl : block g327 3 0 0 = true)
  · exact (rfl : block g327 4 0 0 = true)
  · exact g327B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g327G : graphValid g327 (boundsBefore K307) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low327 : Lower true (varsX 327) (graphGoal 327) 6 := lower_forest (g:=g327) (i:=0) (hints:=4294968966) (before_sound K307 V307) g327G g327T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K327 := extendKnown K307 6 [(327,[]),(422,[112,96,16,32,80,64,48]),(482,[112,64,32,80,48,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V327 : Known true K327 := extend_ok (m:=327) V307 low327 (by decide +kernel)
def g341Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff4783f,0xfffffffffffffffffffffffffffffffff43815),(0x0,0x0),(0x89fcc,0x48d4c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff0e30f,0xc30a),(0x0,0x0),(0xf03f0,0x102a0),(0x0,0x0),(0x3fc00,0x27000)]
def g341C : List ColumnInfo := [(256,0,85,0,4),(17,0,324,0,4),(0,16,324,1,5),(4,0,337,0,4)]
def g341A : List (List Nat) := [[],[130]]
def g341D4 (j : Nat) : Nat := 0x4fd5131
def g341D5 (j : Nat) : Nat := 0x128200d520fd41ff31fd31
def g341H5 (j : Nat) : Nat := 0x8
def g341D6 (j : Nat) : Nat := 0x4689f
def g341H6 (j : Nat) : Nat := 0xf40000001000010820000000290002
def g341L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g341D4)
  | 5 => (3,1,2,0,0,5,0,g341D5)
  | 6 => (1,0,2,0,0,0,0,g341D6)
  | _ => emptyPacking
def g341I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 1 0 6 1 1 g341H5
  | 6 => lookupWord 2 17 1 7 2 1 g341H6
  | _ => fun _ => none
def g341 : Forest := ⟨341,6,fun i => g341Y[i]?.getD (0,0),g341C,g341A,g341L,g341I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P4_0 : block g341 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B4 : block g341 4 0 1=true := g341P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P5_0 : block g341 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B5 : block g341 5 0 3=true := g341P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P6_0 : block g341 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B6 : block g341 6 0 1=true := g341P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341T : checkedTables g341 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g341 0 0 0 = true)
  · exact (rfl : block g341 1 0 0 = true)
  · exact (rfl : block g341 2 0 0 = true)
  · exact (rfl : block g341 3 0 0 = true)
  · exact g341B4
  · exact g341B5
  · exact g341B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341G : graphValid g341 (boundsBefore K327) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low341 : Lower true (varsX 341) (graphGoal 341) 7 := lower_forest (g:=g341) (i:=0) (hints:=8589936132) (before_sound K327 V327) g341G g341T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K341 := extendKnown K327 7 [(341,[]),(355,[96,128,80,64,33]),(419,[112,96,16,32,80,64]),(426,[112,96,16,82,66,50]),(453,[116,84]),(454,[16,116,84,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V341 : Known true K341 := extend_ok (m:=341) V327 low341 (by decide +kernel)
def g451Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff9983f,0xffffffffffffffffffffffffffffffffe09815),(0x1fcc,0x80d4c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffee630f,0x1a230a),(0x1783f0,0x1702a0),(0x7fc00,0x5d000)]
def g451C : List ColumnInfo := [(128,0,323,0,4),(2,0,449,0,4),(1,0,450,0,4),(64,0,387,0,4),(256,0,195,0,4)]
def g451A : List (List Nat) := [[],[16,134],[96,135],[112,97],[128,113],[129,118],[16,96,112,128],[96,128,16,112],[112,16,128,96],[128,112,96,16]]
def g451D4 (j : Nat) : Nat := 0x57d4d10
def g451D5 (j : Nat) : Nat := 0x1a0fd20fd10
def g451H5 (j : Nat) : Nat := 0x24
def g451D6 (j : Nat) : Nat := 0x20688bf
def g451H6 (j : Nat) : Nat := 0x3f1b4158858dcfb2d2a03c0
def g451L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g451D4)
  | 5 => (2,1,3,0,0,4,0,g451D5)
  | 6 => (1,0,3,0,0,0,0,g451D6)
  | _ => emptyPacking
def g451I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 1 0 6 1 1 g451H5
  | 6 => lookupWord 5 10 3 8 1 3 g451H6
  | _ => fun _ => none
def g451 : Forest := ⟨451,6,fun i => g451Y[i]?.getD (0,0),g451C,g451A,g451L,g451I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P4_0 : block g451 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B4 : block g451 4 0 1=true := g451P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P5_0 : block g451 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B5 : block g451 5 0 2=true := g451P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P6_0 : block g451 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B6 : block g451 6 0 1=true := g451P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451T : checkedTables g451 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g451 0 0 0 = true)
  · exact (rfl : block g451 1 0 0 = true)
  · exact (rfl : block g451 2 0 0 = true)
  · exact (rfl : block g451 3 0 0 = true)
  · exact g451B4
  · exact g451B5
  · exact g451B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451G : graphValid g451 (boundsBefore K341) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low451 : Lower true (varsX 451) (graphGoal 451) 7 := lower_forest (g:=g451) (i:=0) (hints:=4294967414) (before_sound K341 V341) g451G g451T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K451 := extendKnown K341 7 [(451,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V451 : Known true K451 := extend_ok (m:=451) V341 low451 (by decide +kernel)
def g358Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffffffffffffffffffff8e133cf,0xfffffffffffffffffffffffffffffffd2111c5),(0x101ccfc,0x341445c),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffa460f0f,0x2420e0a),(0x4380ff0,0x4280ba0),(0x0,0x0),(0x7bff000,0x14a000)]
def g358C : List ColumnInfo := [(34,0,324,0,4),(68,0,290,0,4)]
def g358A : List (List Nat) := [[],[81],[98],[33,101],[81,98],[97,82],[33,81,97],[97,81,33]]
def g358D4 (j : Nat) : Nat := 0x31825f63547409bd89544426d6215110
def g358D5 (j : Nat) : Nat := 0x10402000400080810880809d15fb660a8f120c02faa3a07bd4940bfa8a81fb40502fea8885f95110beaa2217c54443f280885bd4940
def g358H5 (j : Nat) : Nat := 0x70000000002d11c2ec0000
def g358D6 (j : Nat) : Nat := 0x81204815140ff40fd40fd10
def g358H6 (j : Nat) : Nat := 0x1833218209186426408064700061111b1003e3001a989dc548060
def g358D7 (j : Nat) : Nat := 0x105f
def g358H7 (j : Nat) : Nat := 0x243e6aaac3900000758c000f719401cd9109011cb
def g358L : Nat → Packing
  | 4 => (3,3,1,0,0,4,0,g358D4)
  | 5 => (10,2,1,0,0,7,0,g358D5)
  | 6 => (3,1,1,0,0,5,0,g358D6)
  | 7 => (1,0,1,0,0,0,0,g358D7)
  | _ => emptyPacking
def g358I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g358H5
  | 6 => lookupWord 5 19 4 10 4 2 g358H6
  | 7 => lookupWord 6 16 3 9 2 3 g358H7
  | _ => fun _ => none
def g358 : Forest := ⟨358,7,fun i => g358Y[i]?.getD (0,0),g358C,g358A,g358L,g358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P4_0 : block g358 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B4 : block g358 4 0 3=true := g358P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_0 : block g358 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_1 : block g358 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B5 : block g358 5 0 10=true := (@block_merge g358 5 0 1 9 g358P5_0 g358P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P6_0 : block g358 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B6 : block g358 6 0 3=true := g358P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P7_0 : block g358 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B7 : block g358 7 0 1=true := g358P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358T : checkedTables g358 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g358 0 0 0 = true)
  · exact (rfl : block g358 1 0 0 = true)
  · exact (rfl : block g358 2 0 0 = true)
  · exact (rfl : block g358 3 0 0 = true)
  · exact g358B4
  · exact g358B5
  · exact g358B6
  · exact g358B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358G : graphValid g358 (boundsBefore K451) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low358 : Lower true (varsX 358) (graphGoal 358) 8 := lower_forest (g:=g358) (i:=0) (hints:=4329571920) (before_sound K451 V451) g358G g358T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K358 := extendKnown K451 8 [(358,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V358 : Known true K358 := extend_ok (m:=358) V451 low358 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffe793f,0xfffffffffffffffffffffffffffffffffe5915),(0x47cc,0x434c),(0x18630,0x18630),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffd083f,0x1002a),(0x20fc0,0x20c80),(0x3f000,0x2000),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(0,32,85,2,5)]
def g119A : List (List Nat) := [[],[81],[96,66],[96,81,66]]
def g119D5 (j : Nat) : Nat := 0x7f
def g119L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g119D5)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,5,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 1=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 6 := lower_forest (g:=g119) (i:=0) (hints:=1050196) (before_sound K358 V358) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K358 6 [(119,[]),(238,[16,32,48,84,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V358 low119 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffff203333f,0xfffffffffffffffffffffffffffffff2011315),(0x4ccfcc,0x44454c),(0x0,0x0),(0xdb00c30,0x4900c30),(0xfffffffffffffffffffffffffffffff1c0f03f,0x1c0e02a),(0xe00ffc0,0xe00ba80),(0x0,0x0),(0xfff0000,0x92a0000),(0x0,0x0)]
def g187C : List ColumnInfo := [(17,0,170,0,4),(34,0,153,0,4),(8,0,179,0,5),(0,16,170,1,5),(0,32,153,2,5)]
def g187A : List (List Nat) := [[],[16,84]]
def g187D5 (j : Nat) : Nat := 0x1ef52
def g187D6 (j : Nat) : Nat := 0x468817f
def g187H6 (j : Nat) : Nat := 0x18
def g187L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g187D5)
  | 6 => (1,0,3,0,0,0,0,g187D6)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 1 0 6 1 1 g187H6
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 1=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 7 := lower_forest (g:=g187) (i:=0) (hints:=1077332) (before_sound K119 V119) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K119 7 [(187,[]),(215,[112,97,81,33,49,65]),(221,[96,80,48,64,32,16,112]),(411,[133,101]),(473,[112,97,33,67,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V119 low187 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0xe463cc,0xa4214c),(0xfffffffffffffffffffffffffffffff919933f,0xfffffffffffffffffffffffffffffff9089315),(0x6621c30,0x2600430),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffff883e03f,0x83602a),(0x703ffc0,0x503da80),(0x7fc0000,0x6500000),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,5),(0,4,163,64,5),(0,32,197,2,5),(32,0,199,0,5)]
def g231A : List (List Nat) := [[],[112,97,82]]
def g231D6 (j : Nat) : Nat := 0xb113f
def g231L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g231D6)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,6,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 1=true := g231P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact g231B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 7 := lower_forest (g:=g231) (i:=0) (hints:=1050198) (before_sound K187 V187) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K187 7 [(231,[]),(407,[16,84,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V187 low231 (by decide +kernel)
def g343Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffc3b01ff,0xfffffffffffffffffffffffffffffffc1b0155),(0xc3c90c,0x41490c),(0xc3e30,0x41230),(0x0,0x0),(0xfffffffffffffffffffffffffffffffcf0303f,0xe0302a),(0x0,0x0),(0x3003fc0,0x1002c80),(0x0,0x0),(0x3ffc000,0x2ba8000)]
def g343C : List ColumnInfo := [(2,0,341,0,7)]
def g343A : List (List Nat) := [[]]
def g343D7 (j : Nat) : Nat := 0x7f
def g343L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g343D7)
  | _ => emptyPacking
def g343I (_ _ : Nat) : Option (Nat × Nat) := none
def g343 : Forest := ⟨343,7,fun i => g343Y[i]?.getD (0,0),g343C,g343A,g343L,g343I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g343P7_0 : block g343 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g343B7 : block g343 7 0 1=true := g343P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g343T : checkedTables g343 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g343 0 0 0 = true)
  · exact (rfl : block g343 1 0 0 = true)
  · exact (rfl : block g343 2 0 0 = true)
  · exact (rfl : block g343 3 0 0 = true)
  · exact (rfl : block g343 4 0 0 = true)
  · exact (rfl : block g343 5 0 0 = true)
  · exact (rfl : block g343 6 0 0 = true)
  · exact g343B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g343G : graphValid g343 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low343 : Lower true (varsX 343) (graphGoal 343) 8 := lower_forest (g:=g343) (i:=0) (hints:=4294968964) (before_sound K231 V231) g343G g343T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K343 := extendKnown K231 8 [(343,[]),(373,[81,49]),(430,[112,96,16,32,80,64,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V343 : Known true K343 := extend_ok (m:=343) V231 low343 (by decide +kernel)
def g371Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffe070f3cf,0xffffffffffffffffffffffffffffffe030d1c5),(0x9f4cfc,0x95445c),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffff0e00f0f,0x10c00e0a),(0x3038ff0,0x1028ba0),(0x1c03f000,0x4032000),(0x0,0x0),(0x1ffc0000,0x1a680000)]
def g371C : List ColumnInfo := [(16,0,355,0,7)]
def g371A : List (List Nat) := [[],[81]]
def g371D7 (j : Nat) : Nat := 0x7f
def g371L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g371D7)
  | _ => emptyPacking
def g371I (_ _ : Nat) : Option (Nat × Nat) := none
def g371 : Forest := ⟨371,7,fun i => g371Y[i]?.getD (0,0),g371C,g371A,g371L,g371I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g371P7_0 : block g371 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g371B7 : block g371 7 0 1=true := g371P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g371T : checkedTables g371 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g371 0 0 0 = true)
  · exact (rfl : block g371 1 0 0 = true)
  · exact (rfl : block g371 2 0 0 = true)
  · exact (rfl : block g371 3 0 0 = true)
  · exact (rfl : block g371 4 0 0 = true)
  · exact (rfl : block g371 5 0 0 = true)
  · exact (rfl : block g371 6 0 0 = true)
  · exact g371B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g371G : graphValid g371 (boundsBefore K343) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low371 : Lower true (varsX 371) (graphGoal 371) 8 := lower_forest (g:=g371) (i:=0) (hints:=4296015956) (before_sound K343 V343) g371G g371T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K371 := extendKnown K343 8 [(371,[]),(435,[81,129,118]),(462,[112,80,96,16,32,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V371 : Known true K371 := extend_ok (m:=371) V343 low371 (by decide +kernel)
def g459Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffff8c300ff,0xfffffffffffffffffffffffffffffff8430055),(0xfb30c,0x5910c),(0x0,0x0),(0x10c4c30,0xc0430),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffe30703f,0x210702a),(0x7c07fc0,0x7806a80),(0x7ff8000,0x5ea0000)]
def g459C : List ColumnInfo := [(8,0,451,0,7)]
def g459A : List (List Nat) := [[],[16,134]]
def g459D7 (j : Nat) : Nat := 0x7f
def g459L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g459D7)
  | _ => emptyPacking
def g459I (_ _ : Nat) : Option (Nat × Nat) := none
def g459 : Forest := ⟨459,7,fun i => g459Y[i]?.getD (0,0),g459C,g459A,g459L,g459I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g459P7_0 : block g459 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g459B7 : block g459 7 0 1=true := g459P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g459T : checkedTables g459 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g459 0 0 0 = true)
  · exact (rfl : block g459 1 0 0 = true)
  · exact (rfl : block g459 2 0 0 = true)
  · exact (rfl : block g459 3 0 0 = true)
  · exact (rfl : block g459 4 0 0 = true)
  · exact (rfl : block g459 5 0 0 = true)
  · exact (rfl : block g459 6 0 0 = true)
  · exact g459B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g459G : graphValid g459 (boundsBefore K371) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low459 : Lower true (varsX 459) (graphGoal 459) 8 := lower_forest (g:=g459) (i:=0) (hints:=4294996086) (before_sound K371 V371) g459G g459T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K459 := extendKnown K371 8 [(459,[]),(467,[112,97,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V459 : Known true K459 := extend_ok (m:=459) V371 low459 (by decide +kernel)
def g455Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffa34d8190f,0xfffffffffffffffffffffffffffffa14d80905),(0x81ce6cc,0x80c42cc),(0x40e338f0,0x40613850),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffff8f03c0ff,0x8902c0aa),(0x1f003ff00,0x1e003b400),(0x5fffc0000,0x336900000)]
def g455C : List ColumnInfo := [(4,0,451,0,7),(64,0,391,0,5),(2,0,453,0,7),(1,0,454,0,7),(256,0,199,0,5),(128,0,327,0,6),(0,128,324,3,6)]
def g455A : List (List Nat) := [[],[16,134]]
def g455D5 (j : Nat) : Nat := 0x4ef7259653
def g455D6 (j : Nat) : Nat := 0x400804084106c85b2c0bf59653fbd8953bbd8953bb58853be58053
def g455H6 (j : Nat) : Nat := 0x38
def g455D7 (j : Nat) : Nat := 0x1196e28476541ab81c5962ad07888807f94ffaa7fc53
def g455H7 (j : Nat) : Nat := 0x11c88000004c6200280001000000002
def g455D8 (j : Nat) : Nat := 0x6a1a17f
def g455H8 (j : Nat) : Nat := 0x1c80d402f000080000
def g455L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g455D5)
  | 6 => (5,2,3,0,0,6,0,g455D6)
  | 7 => (3,1,3,0,0,7,0,g455D7)
  | 8 => (1,0,3,0,0,0,0,g455D8)
  | _ => emptyPacking
def g455I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 1 0 6 1 1 g455H6
  | 7 => lookupWord 3 15 1 8 3 1 g455H7
  | 8 => lookupWord 1 11 0 7 2 1 g455H8
  | _ => fun _ => none
def g455 : Forest := ⟨455,8,fun i => g455Y[i]?.getD (0,0),g455C,g455A,g455L,g455I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P5_0 : block g455 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B5 : block g455 5 0 1=true := g455P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P6_0 : block g455 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P6_3 : block g455 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B6 : block g455 6 0 5=true := (@block_merge g455 6 0 3 2 g455P6_0 g455P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P7_0 : block g455 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B7 : block g455 7 0 3=true := g455P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P8_0 : block g455 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B8 : block g455 8 0 1=true := g455P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455T : checkedTables g455 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g455 0 0 0 = true)
  · exact (rfl : block g455 1 0 0 = true)
  · exact (rfl : block g455 2 0 0 = true)
  · exact (rfl : block g455 3 0 0 = true)
  · exact (rfl : block g455 4 0 0 = true)
  · exact g455B5
  · exact g455B6
  · exact g455B7
  · exact g455B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455G : graphValid g455 (boundsBefore K459) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low455 : Lower true (varsX 455) (graphGoal 455) 9 := lower_forest (g:=g455) (i:=0) (hints:=4294968950) (before_sound K459 V459) g455G g455T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K455 := extendKnown K459 9 [(455,[]),(483,[112,97,82,66,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V455 : Known true K455 := extend_ok (m:=455) V459 low455 (by decide +kernel)
def g445Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffff2887ff,0xffffffffffffffffffffffffffffffff288555),(0x0,0x0),(0x1e240c,0x1a240c),(0x117830,0x104830),(0xfffffffffffffffffffffffffffffffe2040ff,0x40aa),(0xc180c0,0x4180c0),(0x0,0x0),(0x101ff00,0x13200),(0x1fe0000,0x1a40000)]
def g445C : List ColumnInfo := [(0,256,153,36,6)]
def g445A : List (List Nat) := [[],[82],[112,67],[112,82,67]]
def g445D6 (j : Nat) : Nat := 0xff
def g445L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g445D6)
  | _ => emptyPacking
def g445I (_ _ : Nat) : Option (Nat × Nat) := none
def g445 : Forest := ⟨445,6,fun i => g445Y[i]?.getD (0,0),g445C,g445A,g445L,g445I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g445P6_0 : block g445 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g445B6 : block g445 6 0 1=true := g445P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g445T : checkedTables g445 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g445 0 0 0 = true)
  · exact (rfl : block g445 1 0 0 = true)
  · exact (rfl : block g445 2 0 0 = true)
  · exact (rfl : block g445 3 0 0 = true)
  · exact (rfl : block g445 4 0 0 = true)
  · exact (rfl : block g445 5 0 0 = true)
  · exact g445B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g445G : graphValid g445 (boundsBefore K455) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low445 : Lower true (varsX 445) (graphGoal 445) 7 := lower_forest (g:=g445) (i:=0) (hints:=8598353924) (before_sound K455 V455) g445G g445T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K445 := extendKnown K455 7 [(445,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V445 : Known true K445 := extend_ok (m:=445) V455 low445 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffff8004c47ff,0xfffffffffffffffffffffffffffff800444555),(0xd8b0240c,0x4810240c),(0x304c3b830,0x104c10830),(0x42700c0c0,0x100c0c0),(0xfffffffffffffffffffffffffffff8380300ff,0x380300aa),(0x0,0x0),(0x7c003ff00,0x6c002b200),(0x7fffc0000,0x7b6a80000),(0x0,0x0)]
def g223C : List ColumnInfo := [(8,0,215,0,7)]
def g223A : List (List Nat) := [[],[49]]
def g223D7 (j : Nat) : Nat := 0xff
def g223L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g223D7)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,7,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 1=true := g223P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact g223B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K445) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 8 := lower_forest (g:=g223) (i:=0) (hints:=30324) (before_sound K445 V445) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K445 8 [(223,[]),(251,[112,65,49,97,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V445 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[(0x8c8d8f0c,0x8484850c),(0xffffffffffffffffffffffffffffe203304cff,0xffffffffffffffffffffffffffffe201104c55),(0xc4c427030,0x44c001030),(0x11700380c0,0x100380c0),(0x0,0x0),(0xffffffffffffffffffffffffffffe1807c00ff,0x1806c00aa),(0x1e007fff00,0x1a007b6a00),(0x1fff800000,0x1d6a000000),(0x0,0x0)]
def g239C : List ColumnInfo := [(8,0,231,0,7)]
def g239A : List (List Nat) := [[]]
def g239D7 (j : Nat) : Nat := 0xff
def g239L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g239D7)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,7,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 1=true := g239P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact g239B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 8 := lower_forest (g:=g239) (i:=0) (hints:=1078870) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 8 [(239,[]),(247,[112,97,82,67]),(415,[16,84,134]),(505,[96,128,32,80,48,64,16,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g443Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffff2010c640824c733f,0xffffffffffffffffffffff2010c24082443315),(0xd82009f11c739fcc,0x8d00c50854c),(0x0,0x0),(0xc3018e67821c30,0x43018a26821c30),(0xffffffffffffffffffffff040c0e087803e03f,0x40c0c087803c02a),(0x1f0ff00f8003ffc0,0xb105500f80037a80),(0x0,0x0),(0xe7f0000ffffc0000,0x97a0000551280000),(0x7fffff000000000,0x6faa72000000000)]
def g443C : List ColumnInfo := [(17,0,426,0,7),(8,0,435,0,8),(128,8,307,0,6),(256,0,187,0,7),(290,0,153,0,4),(0,16,426,1,8),(2,32,153,256,5),(136,0,307,0,6),(32,0,411,0,7),(2,256,153,32,5),(32,256,153,2,5)]
def g443A : List (List Nat) := [[],[133]]
def g443D6 (j : Nat) : Nat := 0x309ed87d4a41cef76d4941
def g443D7 (j : Nat) : Nat := 0x130420420818c1c020b5131c04b521e303c03f6b26a57f5d641fdea520fef52506f6b8ea53fdd941
def g443H7 (j : Nat) : Nat := 0xd40e00
def g443D8 (j : Nat) : Nat := 0x151c4d020d154e0230d18088224d124043545181051d6268106c4c5010e41404d9b59b7758341a00ff593fd54ff947fd51ff907fd41fbd4bed21
def g443H8 (j : Nat) : Nat := 0xe0ba002200003300d53b0000c18400
def g443D9 (j : Nat) : Nat := 0xa70e2037f
def g443H9 (j : Nat) : Nat := 0x6d0b8061403b1aef7a3099800d800a00
def g443L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g443D6)
  | 7 => (6,2,4,0,0,7,0,g443D7)
  | 8 => (8,1,4,0,0,8,0,g443D8)
  | 9 => (1,0,4,0,0,0,0,g443D9)
  | _ => emptyPacking
def g443I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 4 0 6 1 1 g443H7
  | 8 => lookupWord 1 23 0 8 3 1 g443H8
  | 9 => lookupWord 5 15 3 8 3 1 g443H9
  | _ => fun _ => none
def g443 : Forest := ⟨443,9,fun i => g443Y[i]?.getD (0,0),g443C,g443A,g443L,g443I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P6_0 : block g443 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B6 : block g443 6 0 2=true := g443P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_0 : block g443 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_2 : block g443 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B7 : block g443 7 0 6=true := (@block_merge g443 7 0 2 4 g443P7_0 g443P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_0 : block g443 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_2 : block g443 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B8 : block g443 8 0 8=true := (@block_merge g443 8 0 2 6 g443P8_0 g443P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_0 : block g443 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B9 : block g443 9 0 1=true := g443P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443T : checkedTables g443 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g443 0 0 0 = true)
  · exact (rfl : block g443 1 0 0 = true)
  · exact (rfl : block g443 2 0 0 = true)
  · exact (rfl : block g443 3 0 0 = true)
  · exact (rfl : block g443 4 0 0 = true)
  · exact (rfl : block g443 5 0 0 = true)
  · exact g443B6
  · exact g443B7
  · exact g443B8
  · exact g443B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443G : graphValid g443 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low443 : Lower true (varsX 443) (graphGoal 443) 10 := lower_forest (g:=g443) (i:=0) (hints:=4296044628) (before_sound K239 V239) g443G g443T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K443 := extendKnown K239 10 [(443,[]),(477,[112,97,81,33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V443 : Known true K443 := extend_ok (m:=443) V239 low443 (by decide +kernel)
def g475Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffe219800fff,0xffffffffffffffffffffffffffffe209800755),(0x27db310c,0x22c9110c),(0x0,0x0),(0x40624c230,0x6004230),(0xffffffffffffffffffffffffffffe13807003f,0x13007002a),(0x0,0x0),(0x19c03803c0,0x840380080),(0x1e003ffc00,0x1c0036a800),(0x1fffc00000,0x179d000000)]
def g475C : List ColumnInfo := [(16,0,459,0,8)]
def g475A : List (List Nat) := [[],[112,97,67]]
def g475D8 (j : Nat) : Nat := 0xff
def g475L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g475D8)
  | _ => emptyPacking
def g475I (_ _ : Nat) : Option (Nat × Nat) := none
def g475 : Forest := ⟨475,8,fun i => g475Y[i]?.getD (0,0),g475C,g475A,g475L,g475I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_0 : block g475 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B8 : block g475 8 0 1=true := g475P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475T : checkedTables g475 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g475 0 0 0 = true)
  · exact (rfl : block g475 1 0 0 = true)
  · exact (rfl : block g475 2 0 0 = true)
  · exact (rfl : block g475 3 0 0 = true)
  · exact (rfl : block g475 4 0 0 = true)
  · exact (rfl : block g475 5 0 0 = true)
  · exact (rfl : block g475 6 0 0 = true)
  · exact (rfl : block g475 7 0 0 = true)
  · exact g475B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475G : graphValid g475 (boundsBefore K443) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low475 : Lower true (varsX 475) (graphGoal 475) 9 := lower_forest (g:=g475) (i:=0) (hints:=4294996084) (before_sound K443 V443) g475G g475T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K475 := extendKnown K443 9 [(475,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V475 : Known true K475 := extend_ok (m:=475) V443 low475 (by decide +kernel)
def g375Y : Array (Bits × Bits) := #[(0xffffffffffffff8020001c0881b3010271ccff,0xffffffffffffff8020001c0880b3010250cc55),(0xc0cf13100643e6cc4e7fcc,0x50acc010024142cc4215cc),(0x670071e001187c18ff8870f0,0x101644501085408568870f0),(0x0,0x0),(0xffffffffffffff88048000601f8020f00f80ff,0x8048000601f0020f00f00aa),(0x1007000381e0003f000fff00,0x1007000381a0003d000dea00),(0x3ff801fcfe00003ffff00000,0x42968982b2000036a9200000),(0x0,0x0),(0x5ffffe00ffffffc000000000,0x240000084c55aa8000000000)]
def g375C : List ColumnInfo := [(68,0,307,0,6),(17,0,358,0,8),(256,2,85,32,5),(34,0,341,0,7),(0,16,358,1,9),(290,0,85,0,4),(4,0,371,0,8),(256,32,85,2,5),(6,0,369,0,5),(32,2,85,256,5),(0,1,294,80,7)]
def g375A : List (List Nat) := [[],[81]]
def g375D6 (j : Nat) : Nat := 0xc3040000000000021a01e9d1b9a1897159412910f8c0a890786048301802b5f28c0ee4b2e6be13725c5658f74c0e4b8acb9af841c9715972df25c3aca32e5be1f8259465cb7cc2cab90cbd6792595711972df0fc12cba971be5d65d8b529d7ca303b16a51ef9261e65d86b5f24b2ee8b0cf9e4985d8561e97c92caba6a34ed921d9655472df24c28ec90c7ba6375589218f6cc4eda92431ed981db52486adb2a3b6a490d6b65076d4921
def g375D7 (j : Nat) : Nat := 0x8100080cc1000800010008004000000002229854c10008000004102080040010408004100081000800200000004000080040020000400200100082040020000000420202181d01000020000400206305a3109b0208102a510810204306182000040000c60e304002a8100102081001020810218207407374e21800c10000208000002201000c3040430ba02e2180e21710017100166e80b889c4004038841c17100274c7c43e2002e9c42e9c42e9c4287d38850fa710ba66e2144cdd388512f75e1bb773ae0dbbb5d686ca58eb1160abe56fab753aa0d3ba6b4a28dd079f53b6704cc9712ae52c9f933232434798d917e2cc4c87f0ca12c18817015ffbf97d8f45e5bbe770eadd2b98716e15bc3646aed29a2330646c75883035fabc1752e45bcb45622b7554a914ba8a5089dd352644ae94522229446859081fc3ec7c0f19d63926f0d418d2f2594a892f23641c728ca16c288470730b011011000b7d82d9565def85dc965def81dc965ded81dc965f6f85dc965def75dc965f6f65dc965bee871c965f6f651c9659fd82dc565def72dc565dec72dc565bbf845c565bef825c565def725c565dec725c565d7f8759465f6f8259465def825d762eef8259762e7f7559562eef8259562d7f7559562e7f6559562bef8259562bed85d8962eed65d89629fd85dc562bbf845c562def825db52d7f8759752f6f8259752ded87d8b52ded76d8b52f6d85d8b52f6d65d8b52bed81d8b52d7f855d952def825d952f6f8259552f6f8558952f6d6558952def825d7619ff825d761dec825d761bef825d7619fd87997619ff8759761bef82597619ff855cb619fd87d4b61d7d75d4b619fd8754b61d7d7554b61ded7254b619fd82dd561bef8259561dbe65dd161dbd65dd1619fd85dc961dbf7458961dbf74d4961def72d4961dbf7454961bf585d8561bf582d8561f6f82597519fd859d9519fd829d9519ff825d9519fd821d951f6f8259551f6c8259551cff7659551cfc7659551bef82595519fd86dc951d7d65dc9519fe87589519fc8758951e7d6558951bf78258551df772585519fd859d9219ff855d9219fd851d9219fd86dd521bef8259521def7558921eed6558921bed86d4921dee76d4921dec76d4921f6d65d4921bf78558521df77558521fe752585219bf845c76597f8759465d6d655c865d75655c4659bf845c762e6d65d8b529ef825d952e6d65589529ef825d761d3d655d3519bf845d9519ef825d9519bd841d9519ed821d9519bf845d92197d851d9219bd841d921
def g375H7 (j : Nat) : Nat := 0x200908ae12c00d4000c06496518493e0e00155344007294811b8d54f4c21c83c141200223554081
def g375D8 (j : Nat) : Nat := 0x10016988018400400298410a100988100104005a040060020041000a610440a1262288841ac0041a88841ac104004110104a04880204004a2228518ab0a14620a14618aa2214600d18a107a6210118a10010610440410e10b8802e89e210a28e10b8802e200a185880488062287a6606220e1678802e78801e802789228188a1e22801818842883842e200a16200638588024da2788428da0e10788030e162009880168062289a009e248b8802863841e200a38588026200406298420188a18e10606228e1620083858802681018c62ada0016318c16806228ba0788428ba00b6228ba0788a26200a1c78801082c788010ba011e210ba0188a20a168047892395a4606228d8c60042018c61081018c626800616248da4788440ba0136228b305a011e248e56804736228e1011e240b1818842680631842918c6009a06163312307880109a019e220b88018a06219488a009a6c48b88a386062255e55254954353a52b52251950d5074fe4f84ef4e04d44c84bc4b34aa4a149248947746845c44743b42942041740e3fc3ea3d83cc3bd3b13a239038437236635a34b33932d31e3092f42e52dc2cd2bb2af29d28e28527626a25824923a2282132011ef1dd1ce1c21b31a118f1801681531441351261110ff0ed0d50bd0ab09c08a07b06605704803c03002100f0007fd72d97ffb2acbffdc965ffae4b2fff71597feb8acbff5d762ffacbb17ff7558bfebaac5ffd9562ffacab17ff7158bfeb8ac5ff9d761ffaebb0ffe65d87feb2ec3ff5cb61ffac5b0fff52d87fea96c3ff99561ffacab0ffd62587ffa92c3ff54961ffacaa8fff72547feb12a3ff59521bfae5b2dfd71d96febb4cbdfd9665bfae332f7f65597f7b92cb7fdc965fd8e4b2dff71596ff3b0cbdf59465bfae232dfd75d8b7fb2ec5bf59762bfae3b15ff7558b7fb2ac5bf59562fdec4b15ff7158aff3b6a57f5db52efacba97ef62d4afeb8ea57f9d952bfaeca977d6554bf6b12a57f5d761bfae5b0dff75587dfba2c37fdc961feec2b0dfe76d46febb6a3df59751bfeeca8dfe76546febb2a37f1d951efccaa8f7d65546ffb92a3fd58551bfeec90dfe76486febb2437f1d921bfeea90dfd75487f6b1243fbd4921feac290ff551486f7b92cb7b5c865beae232df970196dfba2c36f5d351
def g375H8 (j : Nat) : Nat := 0x30534a70323f15a426f5b25fb4ef46b8d928904012b0bb5006ac10a6830a0000007420007e232d83e00000000083713486793134c44b26eea1c21000c1e94d251670000e0cfc1236622dcdc552aa00003df5e000b1b000b3b56000009645611c51300072073c00042556b73371860e032666247b6542efe7e06c1120750d214ae35b97efd5982795da16548a63a5c11db5302a509224458545f39543535861730c1fb0f55232f83a217000369141b00f015987ee940de600009469a0af96f26d91aa6c244554302649000862a71157f2c5236a60a9938e29a19408f9722b164d4f71504a003201009286483480182b4719308012d30400400204a04100e7aa00e146100
def g375D9 (j : Nat) : Nat := 0xa1c5301623d2710086a4c1114d41962018e2a4c062c48a026688b49c4024e200e80b08711a802d85118f41c402504088c5450c200e23e22dd4f95bf5bcc457a2cc44814803ff65ff997fd65ff197ff62ff58bff52ff54bff61ff587ff51ff547fd21
def g375H9 (j : Nat) : Nat := 0xf35076c186246fb93c001094003500002c5a69606fd740010b0000017b000026a80005440038688378a18c9d6ee4f92a550b1bd15c50003d494d9005c000ce8d7c83173c996cc48bcc400372ec3055405444ab0c80b4ed306f238dc00144088c000001884003c200abf10001aed465d1db39934003010001d4194c000002abc000002b270c051b561930473a38000000001a5b0fdce012cc28e280004ae262ca504f8e8000860001cf576822000001e922648c9d558f45045f6400253b910425c7ee0cd0c0f80798e400000200f5264902d800082e0b783ccd071400343b504654000001236d698b9cbf95c00274a31f3284f0000109c5d17800000196400010400800017436c00002800000015400020009030000000c0685000005144508
def g375D10 (j : Nat) : Nat := 0x8c6227f
def g375H10 (j : Nat) : Nat := 0x2a1070000001256500000e9610009000e5cc68c23827ce8152004851894000902020
def g375L : Nat → Packing
  | 6 => (22,4,4,0,0,8,0,g375D6)
  | 7 => (114,3,4,0,0,11,0,g375D7)
  | 8 => (95,2,4,0,0,12,0,g375D8)
  | 9 => (13,1,4,0,0,9,0,g375D9)
  | 10 => (1,0,4,0,0,0,0,g375D10)
  | _ => emptyPacking
def g375I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 11 27 4 10 5 1 g375H7
  | 8 => lookupWord 44 151 6 12 7 1 g375H8
  | 9 => lookupWord 43 170 6 12 7 1 g375H9
  | 10 => lookupWord 9 27 4 9 4 1 g375H10
  | _ => fun _ => none
def g375 : Forest := ⟨375,10,fun i => g375Y[i]?.getD (0,0),g375C,g375A,g375L,g375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P6_0 : block g375 6 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B6 : block g375 6 0 22=true := g375P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_0 : block g375 7 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_17 : block g375 7 17 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_65 : block g375 7 65 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_113 : block g375 7 113 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B7 : block g375 7 0 114=true := (@block_merge g375 7 0 17 97 g375P7_0 (@block_merge g375 7 17 48 49 g375P7_17 (@block_merge g375 7 65 48 1 g375P7_65 g375P7_113)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_0 : block g375 8 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_6 : block g375 8 6 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_54 : block g375 8 54 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_64 : block g375 8 64 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B8 : block g375 8 0 95=true := (@block_merge g375 8 0 6 89 g375P8_0 (@block_merge g375 8 6 48 41 g375P8_6 (@block_merge g375 8 54 10 31 g375P8_54 g375P8_64)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P9_0 : block g375 9 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B9 : block g375 9 0 13=true := g375P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P10_0 : block g375 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B10 : block g375 10 0 1=true := g375P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375T : checkedTables g375 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0 = true)
  · exact (rfl : block g375 1 0 0 = true)
  · exact (rfl : block g375 2 0 0 = true)
  · exact (rfl : block g375 3 0 0 = true)
  · exact (rfl : block g375 4 0 0 = true)
  · exact (rfl : block g375 5 0 0 = true)
  · exact g375B6
  · exact g375B7
  · exact g375B8
  · exact g375B9
  · exact g375B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375G : graphValid g375 (boundsBefore K475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low375 : Lower true (varsX 375) (graphGoal 375) 11 := lower_forest (g:=g375) (i:=0) (hints:=4296017492) (before_sound K475 V475) g375G g375T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K375 := extendKnown K475 11 [(375,[]),(494,[112,64,48,33,81,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V375 : Known true K375 := extend_ok (m:=375) V475 low375 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffff812998963cc33ff,0xfffffffffffffffffffffff010888822843055),(0x8406301233fd0c,0x8402101211550c),(0x30118469c00c230,0x10118020400c230),(0x469e000e04303c0,0x20a000e04303c0),(0xfffffffffffffffffffffff80e0007007c03ff,0x80e0007007803aa),(0x700078007ffc00,0x700068006ea800),(0x780007fff800000,0x6800075d9000000),(0x7ffff8000000000,0xf4b550000000000),(0x0,0x0)]
def g255C : List ColumnInfo := [(17,0,238,0,6),(34,0,221,0,7),(8,0,247,0,8),(68,0,187,0,7),(128,8,119,0,6),(0,32,221,2,8),(16,0,239,0,8),(0,4,187,64,8),(136,0,119,0,6),(1,16,238,0,6)]
def g255A : List (List Nat) := [[],[112,97,82,67]]
def g255D6 (j : Nat) : Nat := 0x139d98dce40
def g255D7 (j : Nat) : Nat := 0x30bbd87903e7dce40
def g255H7 (j : Nat) : Nat := 0x20
def g255D8 (j : Nat) : Nat := 0x404904aca7100b19808272d01ff5c3df207dd30
def g255H8 (j : Nat) : Nat := 0x20039
def g255D9 (j : Nat) : Nat := 0x161c188c48ff
def g255H9 (j : Nat) : Nat := 0x25310801e982
def g255L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g255D6)
  | 7 => (2,2,4,0,0,3,0,g255D7)
  | 8 => (3,1,4,0,0,6,0,g255D8)
  | 9 => (1,0,4,0,0,0,0,g255D9)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 1 0 6 1 1 g255H7
  | 8 => lookupWord 1 5 0 6 1 1 g255H8
  | 9 => lookupWord 2 6 2 7 2 1 g255H9
  | _ => fun _ => none
def g255 : Forest := ⟨255,9,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 1=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 2=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_2 : block g255 8 2 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 3=true := (@block_merge g255 8 0 2 1 g255P8_0 g255P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 1=true := g255P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 10 := lower_forest (g:=g255) (i:=0) (hints:=1078868) (before_sound K375 V375) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K255 := extendKnown K375 10 [(255,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V255 : Known true K255 := extend_ok (m:=255) V375 low255 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x88020502760e4a4880cf3e2180,0x88020502060c4a4800c73c2080),(0xfffffffffffa81101ffc07a5618b217841684f,0xfffffffffff901501c8005a5200a014845480d),(0xffffffffffeb6e30f4b810c1a2291a8644303d,0xffffffffffe36e111cbc118100091a8604202d),(0x100943008a01884920251c04620,0x100943008200880920051404220),(0x32000090b0ed2044a5a80a19c0,0x32000090b0e12004a528021940),(0x1838071c5d0ed088f1dd2020e03a,0x6807005c0a5088e1dc2000a032),(0x1486e800800842b5a6096151c816,0x16800400042a5a2412041c812),(0x404004223c0301d217202818602,0x404004221c01015217200808402),(0xffffffffffe779dfe3030901521e5414be9861,0x90806303000012142010ba1040)]
def g511C : List ColumnInfo := [(17,0,494,0,11),(136,0,375,0,11),(34,0,477,0,10),(68,0,443,0,10),(320,4,187,0,7),(290,0,221,0,7),(64,256,153,38,7),(16,64,170,261,7),(0,16,494,1,12),(66,0,445,0,7),(256,0,255,0,10),(324,0,187,0,7),(0,8,375,128,12),(258,32,221,0,7),(32,256,153,70,7),(256,4,187,64,8),(36,0,475,0,9),(2,256,153,100,7),(6,0,505,0,8),(8,1,294,208,8),(96,0,415,0,8),(16,128,356,11,8)]
def g511A : List (List Nat) := [[],[112,97,82,67]]
def g511D9 (j : Nat) : Nat := 0x63f060bc2218f05e1f00863c1787c0250d85e1f0080d0270f85e1f00c75f67a1c3c3f00147e1f83c2051252ff6aaacde2a00576fb269b95606bb7d930dcab035dbec996e5581cedf4bd1330b0c3ffba66098586cfadb930c0ac36dd6d49860561
def g511D10 (j : Nat) : Nat := 0x1c147c20a2026170f003428d04c7c3c01c282b1f0f008a20c0bc1c28820a02b1f070830c600bc1c3082a17070c5c20a1b8785c009c20e3f004f083880dc3c00a082a182706170838d87c185c20e2e1707082038b8409c3c0122e1707083820b8409c3c012299f67461300270849187c01bc20c284f0708289c3c0085c261f07083028bc1c20b08261f0f0028985c1c2082617070820885c1c20824ac8ed122093ec76ce21ad31c5ecb214926446c820ed1ac2cc4e0890ec17c2603904c04c002bffa865981bfbe899660777da6e5581ddf61b9560777da2e5581ddf65b9560777f9564981ddfe55826067fda9a6161cffe6298586ff5a1a6161dfbe89985873ff9866161bfbe89985867fea926161cff66098586feda226161bfe68098587bf79860561efd26181587ef58660561fdde9581587f77a5605219dfe9591e0a7efa265b819fbe899858677fa566121
def g511H10 (j : Nat) : Nat := 0x1500c6f0e3b200d8d9f42100
def g511D11 (j : Nat) : Nat := 0x4c3805860a30d09091e1c0147108e161c0102861c90d17091e1c01471212161c02c3051c8870c121c2c3804930f0610a1c51218284c10f0c20e4e8d90e104c380491861e00a222c30f005161e1c0344458308b12160c2104c382104111c2c18420b0b06108223c380289a0163c38028d0b0e008206878704214305090e161c03860a0b06186342c1842090b06108261c1082090c160c2105d00b185c3806987216274097a4e35b231f5c2afd4b2744a48c1071e5386684b894f24c3bc5f89d0f616418000ffec2b05ffd96607ffb0cc0fff64981ffec1303fff98587ffd30b0fff66161ffe4c2c37fd95e0affb23c15ffe5582bffc8b057fd9854bfdb04a95ff65b81bfec97037ff96607eff2ac0dffe4981bffcc2c37fd98587feb02b0dffe6121bfecc243fed82487feb0290ddfe5581
def g511H11 (j : Nat) : Nat := 0x38d462d300246002170c24200000901a9d2a61f41cb665875a341cbc00bdc000000f0000000000f451ae0d56a5744932edf9e456ab14e3892d2349000001008312200008
def g511D12 (j : Nat) : Nat := 0x16445421c035859e54504219050614302035119414108d40a54704210e50614300a51e1410863421a4a83f1385400fff82ffd82ffd52fff81ffd81ffd61ffd21
def g511H12 (j : Nat) : Nat := 0x40b804a54492708b8200000003a896f9a620946a90c005b6818344bead4629627930a140ec841152f1cacc0220000100c4220020
def g511D13 (j : Nat) : Nat := 0x860c4100dff
def g511H13 (j : Nat) : Nat := 0x2508a38eba1c40001ef00021b3401d48c11cb
def g511L : Nat → Packing
  | 9 => (7,4,5,0,0,9,0,g511D9)
  | 10 => (27,3,5,0,0,11,0,g511D10)
  | 11 => (28,2,5,0,0,11,0,g511D11)
  | 12 => (7,1,5,0,0,9,0,g511D12)
  | 13 => (1,0,5,0,0,0,0,g511D13)
  | _ => emptyPacking
def g511I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 3 13 0 8 3 1 g511H10
  | 11 => lookupWord 18 47 4 10 5 1 g511H11
  | 12 => lookupWord 15 34 5 10 5 1 g511H12
  | 13 => lookupWord 6 16 3 8 3 1 g511H13
  | _ => fun _ => none
def g511 : Forest := ⟨511,13,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P9_0 : block g511 9 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B9 : block g511 9 0 7=true := g511P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_0 : block g511 10 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_4 : block g511 10 4 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B10 : block g511 10 0 27=true := (@block_merge g511 10 0 4 23 g511P10_0 g511P10_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_0 : block g511 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_1 : block g511 11 1 18=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_19 : block g511 11 19 9=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B11 : block g511 11 0 28=true := (@block_merge g511 11 0 1 27 g511P11_0 (@block_merge g511 11 1 18 9 g511P11_1 g511P11_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_0 : block g511 12 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B12 : block g511 12 0 7=true := g511P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 1=true := g511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0 = true)
  · exact (rfl : block g511 1 0 0 = true)
  · exact (rfl : block g511 2 0 0 = true)
  · exact (rfl : block g511 3 0 0 = true)
  · exact (rfl : block g511 4 0 0 = true)
  · exact (rfl : block g511 5 0 0 = true)
  · exact (rfl : block g511 6 0 0 = true)
  · exact (rfl : block g511 7 0 0 = true)
  · exact (rfl : block g511 8 0 0 = true)
  · exact g511B9
  · exact g511B10
  · exact g511B11
  · exact g511B12
  · exact g511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 nineInputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound K255 V255) g511G g511T (by decide) (by decide +kernel)
def mo471Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffe000383fc7,0xffffffffffffffffffffffffffffe09048507f),(0x7fc00008,0x4f1c9f1c0),(0x38007c010,0x1b2dad2c0),(0x0,0x0),(0xffffffffffffffffffffffffffffe000000fc1,0x1f6fb7af80),(0x0,0x0),(0x1c0007f022,0xc45052500),(0xff80004,0x1b0e360e00),(0x1ff0000038,0xfffffffffffffffffffffffffffff20820083f)]
def mo471C : List ColumnInfo := [(130,0,341,0,7),(320,4,147,0,4),(4,0,467,0,8),(1,16,454,0,7),(17,0,454,0,7),(256,2,85,128,5),(16,0,455,0,9),(256,0,215,0,7),(64,0,407,0,7),(17,128,324,2,5),(0,144,324,3,6),(65,16,390,0,4),(131,0,324,0,4),(258,0,213,0,5),(81,0,390,0,4),(6,0,465,0,5)]
def mo471A : List (List Nat) := [[]]
def mo471D6 (j : Nat) : Nat := 0x3d1aa6b22c4a162f21d6450560
def mo471D7 (j : Nat) : Nat := 0x2821412f831865d0630cbe0161f602100000000000000000000000000000000000000000000000396594bca00ded751c964ded711c964ded701c964ded505c864df5505c464df9855c064df9505c064f5d6559153fcc8259153bdd8219153f5d6554d62edd6454d62ddd7654d42f5d6554d42f9d6454d42fcd5358942fac8259141ebd6259141ddd7650d41f9d6450d41fd54358541ebc7459160eec8259160ebd42591609fc8750560dec825d940ef96458140ebd6450560ef96458110bcd8219153bd58119153bd98019153ead6458942
def mo471H7 (j : Nat) : Nat := 0x25c00
def mo471D8 (j : Nat) : Nat := 0x90508f1e4141141912160176042db4c01108d8d150147d850492c64a08c35c980b1094a3044da2043a22413108813044d8c043da20439e2413122813044d880438818131361028051761600f20604c4d88005136120044d871448011a04c10f61c58011761620011761620011499018c41490630809071472480440c72230240458c09011088c10d08c10c90c48811491220c11488c29201468c29201459200438c01434a30051031058042101412451731c8c36047c872102c5d81205c87230d811d7c8024400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c3d7eaeb5c4b4d60aac540a45412764ce961262404628890b2073ea7a4ed1cb37869ccd9892ee594ab13e24c450828f91da36c648b41442584507b0d81682102701e001ff5d564ffacab27fd71593feb82c9ff59154ffacab17fd5458bfeb2a85ff55142ffac8b0ffd62587fea12c3ff59141ffac4a0ffd42507feba2c1ff1d160ffac8b07fd72583feb12c1ff50960ffae2b07fd61583feb22a1ff19150ffac4a87fd42543febb281ff59140ffae4a07fd62503fea1281ff5c540ffac2a07fd41503fe90a81ff58520ffa82907fd62443fea1221ff50560ffa42b07fd64443f6392c97f5c864bfae2325fd70193eeb22a7f719153fbac8a1efd6458beea9ac5f750d62bfaeca17bd6450beea9a85f750d42fdac4a17dd43586febb283ef59141fba86a0ff561506febb2437f5d121fba8690fed62487fab0a43fd50521dfac8b05fd76503fcb02817f5d920bfae8907ed42483f690a41fe58120ff280905fd76442feba2217f5c910fea82887f521443fcb02215f5d464bdae4325f571192fcb80c9d759553
def mo471H8 (j : Nat) : Nat := 0x3c6c92b2b00c80000d268694e310f086154b000d3721dcfc0fc336290ee8681962485a080234619031701d20a00c1493c000668400a111210856
def mo471D9 (j : Nat) : Nat := 0x2907901230932858231469904f0b20950ce890123a502a42c11d483802919271521608ed44a85b0073ca85b00641c54b0403a0e3926041d0720e4048e77124980c73a0434c02420e860e45200890061a24a80c59de53881f7739aa605584d10b388b9240620d01f003fd65ff593fc64ff553fd62ff54bfd42ff587fd41ff487fd60ff543fd40ff483fd10f754fdd43
def mo471H9 (j : Nat) : Nat := 0x4a1ea85264a6924c23883e2718b084c2b99288321be0c810b0e91838111581fe9f782a80917a93d1180059a485899113416106f8dc0c78bf1880009ec8a00040200028feab0000003a2b9d80039e3a98002220004a4228e8e4a5a0709b00000021232500009a80000009012a727b21585419d8802c294e8d507a09208f9c000000000120b1d18189519cc16f9109460999718f58658400072028068a82952aca300400842000883048015890040000048c108401180c0180043a0000000401403000679804b
def mo471D10 (j : Nat) : Nat := 0x480c27f
def mo471H10 (j : Nat) : Nat := 0x9040062c002380021f0c60cca90248e43440170d02542f19cfcb8403
def mo471L : Nat → Packing
  | 6 => (2,4,4,0,0,0,0,mo471D6)
  | 7 => (33,3,4,0,0,7,0,mo471D7)
  | 8 => (89,2,4,0,0,11,0,mo471D8)
  | 9 => (17,1,4,0,0,10,0,mo471D9)
  | 10 => (1,0,4,0,0,0,0,mo471D10)
  | _ => emptyPacking
def mo471I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 6 1 1 mo471H7
  | 8 => lookupWord 11 36 6 11 6 1 mo471H8
  | 9 => lookupWord 59 107 5 12 7 1 mo471H9
  | 10 => lookupWord 8 20 3 10 5 1 mo471H10
  | _ => fun _ => none
def mo471 : Forest := ⟨1495,10,fun i => mo471Y[i]?.getD (0,0),mo471C,mo471A,mo471L,mo471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P6_0 : CutRow mo471 6 0 2 := mixedCut (pos:=0xa04120482409108211) (neg:=0x292500e16) (data:=fun _ => 0x231010504210304) rfl (by decide +kernel)
theorem mo471B6 : CutRow mo471 6 0 2 := mo471P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P7_0 : CutRow mo471 7 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P7_4 : CutRow mo471 7 4 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P7_6 : CutRow mo471 7 6 27 := mixedCut (pos:=0xa04120482409108211) (neg:=0x4052816c83400e52) (data:=fun _ => 0x706031300701310307013103022151030221510302215163022151637060313070603120020141030201410370603130020141030201410302014107020141027060315002014106670432230451430304514303535464145354641453546414045143050701310304210364) rfl (by decide +kernel)
theorem mo471B7 : CutRow mo471 7 0 33 := (@joinRow mo471 7 0 4 29 mo471P7_0 (@joinRow mo471 7 4 2 27 mo471P7_4 mo471P7_6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_0 : CutRow mo471 8 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_5 : CutRow mo471 8 5 41 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_46 : CutRow mo471 8 46 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_49 : CutRow mo471 8 49 40 := mixedCut (pos:=0xa04120482409108211) (neg:=0x64202d04a1480e16) (data:=fun _ => 0x70526140705261407052614070526140475245160221010446503516022101044650351670526140022101040221010404310305022101040221010461215224533054155330541553305415533054155330541561205224612052247054614002413104024131040241310461215224044123056121522404412305044123056121522461215224044123050441230504310305043103050221010402210104) rfl (by decide +kernel)
theorem mo471B8 : CutRow mo471 8 0 89 := (@joinRow mo471 8 0 5 84 mo471P8_0 (@joinRow mo471 8 5 41 43 mo471P8_5 (@joinRow mo471 8 46 3 40 mo471P8_46 mo471P8_49)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P9_0 : CutRow mo471 9 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P9_2 : CutRow mo471 9 2 15 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B9 : CutRow mo471 9 0 17 := (@joinRow mo471 9 0 2 15 mo471P9_0 mo471P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P10_0 : CutRow mo471 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B10 : CutRow mo471 10 0 1 := mo471P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471T : mixedTables mo471 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo471 0 0)
  · exact (mixedEmpty mo471 1 0)
  · exact (mixedEmpty mo471 2 0)
  · exact (mixedEmpty mo471 3 0)
  · exact (mixedEmpty mo471 4 0)
  · exact (mixedEmpty mo471 5 0)
  · exact mo471B6
  · exact mo471B7
  · exact mo471B8
  · exact mo471B9
  · exact mo471B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471G : graphValid mo471 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471R : Impossible false (graphGoal 471) 10 (vars 471).toFinset := by
  rw [show graphGoal 471 = targetOf mo471 by decide +kernel]
  exact mixedRoot (g:=mo471) (top:=10) (i:=0) (before_sound K255 (known_down V255)) mo471G mo471T (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mlow471 : Lower false (varsX 471) (graphGoal 471) 11 := plain_low (hints:=4294968948) (by decide +kernel) mo471R
def KM471 := extendKnown K255 11 [(471,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM471 : Known false KM471 := extend_ok (m:=471) (known_down V255) mlow471 (by decide +kernel)
def mo487Y : Array (Bits × Bits) := #[(0x78700036,0x5c99b69614),(0xfffffffffffffffffffffffffffe07800e03c1,0xfffffffffffffffffffffffffffe0c8892414b),(0x3807800c08,0x7dbbb60000),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffec0000e3001,0x1f3776c0000),(0x10007f1c00e,0xffffffffffffffffffffffffffff824448414b),(0x3f80000f0,0x1a3664928a0),(0x1fc0001ff00,0x1beb4)]
def mo487C : List ColumnInfo := [(34,0,453,0,7),(320,4,163,0,4),(68,1,290,128,5),(129,0,358,0,8),(68,0,419,0,7),(258,32,197,0,4),(34,128,324,1,5),(163,0,324,0,4),(36,0,451,0,7),(192,1,294,0,5),(4,0,483,0,9),(256,0,231,0,7),(69,0,418,0,5),(33,0,454,0,7),(292,0,195,0,4),(290,0,197,0,4),(38,0,449,0,4),(324,0,163,0,4),(97,0,390,0,4),(32,0,455,0,9),(5,0,482,0,6),(6,0,481,0,5),(134,0,353,0,4),(1,128,356,2,6),(131,0,356,0,5),(65,0,422,0,6),(260,0,227,0,5)]
def mo487A : List (List Nat) := [[],[112,97,82]]
def mo487D6 (j : Nat) : Nat := 0xcea44194219214833c91064c8648520
def mo487D7 (j : Nat) : Nat := 0x8004020c001008201040205080a0804102920021e3403090c03090b86010b860108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f3b77b3f02a26629a520c06003b9924ba0e6b0e77610735c961ceec20e6b82c39dd821cd70587bb24039ae0b0d7b640845c861cf6c2904bb2839ed8320976507b9906412eca0e7b551821d941cf6a8b043b2839ed41608765073da80c10eca0e7b441821d941cf6bb3043b2839ed756087650775ac8c10eca0eeb551821d941df2b0b043b2839ed70608765077ca20c10eca0e7e5d9801d941ddcb23003b283bf1616007650737aa843ac4a0e7b4848758941f5a3b2c8b0a83eb562591615077a90e41ac2a0fe55908358541deac1106b0a83bd58020d61507daae6b1ac2a0fb54c96358541f6ac22c6b0a63ed58258d614c7daa84b1ac298fb56016358531f6aa02c6b0a63ed52058d614c7daac8b1ac298fb55896358531f6ab02c6b0a639bd956107648737b22c20ec90e6f641841d921cde883083b2439bd546107648737a82c20ec90e6f501841d921ceeaa3063b2439dd4160c764873ba80c18ec90e77441831d9218feca10eb1a439dd4321d634873da4043ac690c7f6588750d21f56a0ac8b1243bd58420d61487baae841ac290ef56008358521e7aba2c6b0a43ed54358d61487dcacab12c290ff120d6258521f72b1ac4b0a43bd4936194148776b0ca1a8290f6d5d94350521bf24c2c4a0a43fa5435894148737ac843a86b067758c8750d608fec890ea1ac1a7d646146158377320c20c2b06b75918318560d76b230430ac19ed9221d4158357930b2282b06af60d6450560cde43ac8a0ac1eb561591415833dac443a42b065f5d98518540dbcb030a30a819bd7661061503772c0c20c2a06775d98318540decb030630a819ed76608615037d2c0c10c2a07b3585634c920fc6a1a64a0a413ed9321921483f8926b0a42907b958d6148520ff0c82c290a41fa54350521482f6b2ca1a82887e558d4350510fe4b1a64902217e89648520443fc2c290a408857364c845c861af4c8108b90c39d48720d6150795ae8b22c490d7325d434c921e6ab9ac6b0a43ec5634c961487d4ac8b128290fe150d32505218f6c910ea1ac11ed9221d4158275b2843242904f364c8648520
def mo487H7 (j : Nat) : Nat := 0x339
def mo487D8 (j : Nat) : Nat := (if j<1 then 0xd3248540ff56148540ff96358140ff96158140ff86158140ff93158140bfd8650530ff56150530bfd8648530fed6248530ff56148530dfd7658d20dfd7458d20bfd8650d20fbd6450d20fdd6350d20fed8250d20fed6350920dfd8758520dfd7658520dfd7458520fdc8358520efd6358520fed4258520fed3258520ff98058520bfd8650520fbd6450520fed8250520ff56150520bfd864c520dfd764c520bfd844c520dfd744c520fdd634c520fed424c520ff5614c520fed6348520fed4348520fed6148520fed4148520ff96358120ff96158120ff93158120ff96350120ff96150120ff93150120dfd7658d10dfd7458d10bfd8650d10bfc8650d10fdd6350d10dfd635c910bfd864c910fdd634c910fed624c910dfd7458510dfd7258510ff58650510ff48650510ff58350510ff56350510bfd8650510bfc8650510fbd6450510ff56150510bfd8648510bfc8648510fed6248510ff56148510ff96358110ff96158110ff96348110ff96148110fbd6450560fbd4350560fbd6450530fbd4350520fed3250520fbd6450d10bf9801c562fcd6358932ddd741cd61ddc741cd61ddc735c961edd634c961ddc735c161dbd825d061dbd805d061d7d7559061ddd645cc61ded845c861dec845c861ded645c861ded805c861d7d7558861dbd7458861ddd7358861df9645c061df9625c061dec825d9419fd821d941bed821d941bf9801d9419fc8758941df48758541fb56458541fd48358541ef563585419fd87585419fd8719131bdd8319131bed8219131bf58119131bf98019131fd56358531ddc835d9219fd841d9219fd831d921b7d851d921bbd841d921bdd831d921bf9801d9219fd87591219fc8759121dbd74591219fd8758d219fc8758d21ddd7358d219fd8750d219fc8750d21dec8758921ded7458921eed6458921ded7358921bed864c921ded764c921fcd634c921fcd434c921df57458521fd48358521df57358521ef56358521fe56258521fe53258521bf58650521df57650521fb56450521fb54350521fe56250521fe532505219fc8750d60ebd6450d60bed821c560b7d8518560bbd8418560bdd8318560bed82185609fc8750560ebd64505609fc87485609fd831d9409fd811d940b7d8518540bbd8418540bdd8318540bed8218540f9d6450d30f9d43505309fd831d9209fd811d920fad6450920ded764c920bed844c920fcd634c920fcd434c920b7d8518520bbd8418520bdd8318520bed8218520bec8648520ded7648520bed8448520bed8348520ded7348520fe56148520fe54148520fe93258120fe92158120fe93250120fe921501209fd841d9109fd821d910ded724c910fb56450510fb54350510fe93248110fe921481109ed821d9419f9801d941ed5635853197d851d9219bd841d9219dd831d9219f9801d921 else (if j<2 then 0x40f22ef4ed6eb0e92e6ce46e20e0adf4ddedc0d9ad74d5ed38d12cfcce6cd0cbac9cc86c60c4ac24bfebd0bb2b7cb56b38b0aaf4adeac8ab2a9ca7ea68a3aa24a0e9f89e29cc9b698896a9549269088e28c48ae89888285c8468288127f47de7c079a77475e74072a7146ee6d06c26a467e66064a62c60e5f05d25a458e5685525345164f84da4bc4a64884724544364103e23bc38e37836234c3363102ea2c42ae29827a2542362202021e41ce1b81a218416e14812a0fc0de0a808a05401e000bfd851c562dfc715c162dfd755d161fdc835d161fec825d161dfd751d161bfd801d161dfd745cd61fdd741cd61fdd641cd61efd7458d61dfd755c961dfd745c961fdc835c961dfd735c961fdc735c961efd635c961efd6458961fdc7358961efd6358961dfd745c161fdc835c161dfd735c161fdc735c161efd635c161dfd725c161dfd805d061dfd7559061dfd7558861dfd825d941dfd805d941fec825d941dfd411d941dfd761d941fed821d941bfd821d941ff5811d941ff9801d941bfc865c941dfd765c941dfd735c941bfd8758941bfc8758941dfd7658941fed7258941bfd874c941bfd864c941dfd764c941fed624c941ff48758541ff47658541ff58558541ff58458541ff58358541ff57358541ff56358541ff58258541ff57258541ff56258541ff53258541ff58058541dfd7658541bfd8458541fbd6458541bfc865c141dfd765c141dfc765c141fbd645c141dfd735c141ff5615c141dfd8759131dfd7659131fec8259131bfd8019131fdd6458d31dfd7658931efd6458931fdd6358931dfd7650931fed6250931ff58458531ff56458531ff58258531ff56258531ff54258531ff58058531dfd7658d21dfd7458d21dfd7650d21fed6358921fed4358921ff58558521ff58458521ff58358521ff56358521ff54358521ff58058521dfd7458521fed6258521ff58650521ff58550521ff58350521ff56350521bfd8650521dfd7650521dfc7650521fbd6450521fed6250521ff56150521efd8359160efd8159160efc8159160efd6458d60bfd8650d60fbd6450d60fdd6350d60bfd864c960fdd634c960fed624c960efd6458560fdc8358560efd6358560bfd8418560efd6418560bfd8218560dfc8750560bfd8650560ff56150560bfd864c560bfd844c560efd644c560fdd634c560ff5614c560bfd8648560bfd8348560fed6248560fed3248560ff56148560dfd7658d40bfd8650d40fbd6450d40fdd6350d40bfd864c940fdd634c940fed624c940dfd8758540dfd7658540fdc8358540efd6358540dfd7618540bfd8418540bfd8218540bfd8650540bfc8650540fbd6450540fbd4350540ff56150540bfd864c540dfd764c540bfd844c540fdd634c540ff5614c540bfd8648540bfc8648540bfd8348540fed6248540fe else 0x8008220020800082200c020c30041080085c302800c1808804440805010c18218e00412066405101a928d00428050a901c207010890041c3aa06400111a81a0004407010a0018a80442a068001101c0420701081c04207010826000830701080821138c40e010838178c044c0090502102c1a10083850244050c181008001404605e306001018140030602034480143c14240050b0014240050b001420600050f8c042ca06050201141438210010840042100108400420701082c1418080450b02010c0c0420b0602800e142c041430b0503011008184030701082c0420401082c15000440001081600043050108201404344010b8c1920348060105101404192044a01081814043840108080420602040110180920301041920043c3021209130e3408310890b10041c34401070f10041c34a01070c170c0838245c30208030c084040f050b0c30143c401070d10041c3c401070c38041c30502081c081430f050b0c301430c01020c122124044080402c3011480230c0440c04204901141c0420701081c0420701085f0c080440400490110100b0c0440701081c0428ac3010c3011240444801890c062424801890c10062430207081c042070108030c083020708a20d022448340890f002f8c140450905020c3d2000181c1461701060c5b282f8c1404616ca0be30501182414083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f6cf56f))
def mo487H8 (j : Nat) : Nat := 0xa6652fa6ba1b0a543fb38c1ce36626c4c648a17f39958d4b42325d92e4859001b072454e233318d92eae42b989471b1421263cd4d33b101769a57562b4a2250000002bb890f5682a608f54c19000e65a6dc75511f53e1a56c90f2da210213563000000000761b5983036e273f5b70dd32000644f3a14f768a3e13500000073de41a7476a79119e837c09b0ec21e60b05328c07d4975200092c01f02d255a1d220c50c43d51c1eab2072000a16000e030002d80000001a2a3456f064446e40c29d31527e4220b90230a75f65a3153b690c306000a046477226a4e5e55c000567f976459702040800004800c01800220000030000d501e0c30000053c60dd64e44b1c01da00000200608002e002001000000041183007040805200000000001004000002140000000
def mo487D9 (j : Nat) : Nat := (if j<1 then 0x88021820e2073502182161a80e084050c3870c1070e1820e18605002e3023040b8c088154050c0038a3d4060b8c00c2f5060e26a082c106000439009506000438c0838418108890318c181040017181802c90410044c6286040020714107087c800083050e38f10182e3003480a1b1801434a000a063023960c08005c72880b2458605000e30838b1008300021c70c2c200818c08e10006021c40c02563022000407184166c3041840136182142430a3040834109102c30e08417001051228d0414488001051220108024021230486146080640c1220b0a8040914084110c10a11008030c508800c3100c894244032250910043050048a008870c5c3050048b0c1070c5c3050048a0218212200060a009140020e18380a84882f506001c517a83000e28bd41800714586001c40c0010712b2157cab4551aa49502a6952a68e5450a05cfa678f3909a94cc26012d795e4a1648f2178f046a62e5157893c41619d0ac845416a08d02b7fdbf81f28f48788bb85d8ce96736b8f5c28df26e83681afcd5c6a0b4619eccbf65232098c0c29603af95786b9a5bc2d59676b20582ab8d54aa7551ba8713e69ca4d0a5fd2ba93448923dd1b88c1448a1a107e80f3f69ebcefe76b39d9bd8d9a6a43481964c526002e49610a9a51626f92bc91a46422490807fc3dc1dd0e446de34d18e8bec5b22b0143897847821a0fc073c36818b0b8051c24a0fc07082fc12c06d0220088001ff5d562ffae8b17fd7358bfeb1ac5ff5c562ff8e2b17fd7058bfebaac3ff5d161ff8e8b0ffd64587feb9ac3ff58d61ffae4b0ffd62587fe992c3ff5c161ffac830ffd62187febb283ff1d941ffae4a0ffd62507fe99283ff58541ffae0a0ffd644c7fe32263ff58931ffa8498ffd76487fe3b243ff5d521ffae890ffd64487feb9a43ff58d21ffa8690ffd61487fea0a43ff5c121ffac8b07fd63583fea1ac1ff58960ffa64b07fc71583feb0ac1ff18560ffa82b07fd31583fe90ac1ff59140ffac6a07fd43503feb1281ff4c940ffac2a07fc61503fea0a81ff4c540ffa42a07fd644c3feb1261ff58530ffa82987fd214c3feb2241ff58d20ffa86907fd61483fe30a41ff50520ffa62907fd64443feb1a21ff50d10ffac4887fd32443feb0a21ff50510ffa42885fd764cbf6b1265f71cd61dfac6b0dfd75186feba0c37f5c861bfae030dfd76506fe3b283fd58541bfaec20dfd70106febb263f758d31feac298dfd76486fe3b2437f5d121bfae690fed62487f699243fd58521fea8290efd64582febb2817f1d940ff2c0a05fd764c2feba261f750d30ff2c0985fd76482fe3b2417f5d120bfae6907ed42483f699241fb48520ff2c0907f940482febb2217f1d910bfae8885fd73442feb9221fd50510ff2c0887f930443fc902215f5d461b7ae830ddd73186f6b90c37e5c061 else 0xc811811088108701083021038410831811030240444901012046046d4012230c2aa0c002c0498c70c092051035354151c304040120030f0a2061e00288043000b012631c32410161820ea88041940510005480a02319506050008a087010c3048800140c63860438281098c010180c0058c20c1874302083841c0848600302503c40414304c6007808c10618082108e00c903400a2060a90101470070c0924010040c60440c10100200460e042818c08618240860808c008010c79511101060a1c08028a9202142000c08388282c4041b1ca00381041b180083230e043088204d86086888010d862921635002123044102182140435008486090091068588090431a202021c41680109122020e19516821821500c860841a8060e0a0a18e486090d043180840b0d402106c41880282863c40208388310430420588083881104318085810e682120439a084041c286141070c2820e1c318041083e220281414310401088040c123088851005940a190083810c084403048a1624a041c50e46043042c30a083)
def mo487H9 (j : Nat) : Nat := (if j<1 then 0x3c0442004f70001c210000000000182b000013e72a310600016fed27b340bcf353fc42287b95870cd006bd64228fcce03418cc0cf99425000c5c0d2fc42b4e749dc50113bc217c7451eb526f4388aa53efc4e6a734dfe26c28c456aa24cc72005898152c653845200f6d4a18178ae4ca8ee694764f0202cc9260089350c32e630003c7030fc000a0f032924cb6e3f2477278407c26741c73582d0000e416d0abc942a640b6154000347300007030000000c205a5de13144300004b9f5271652153511000364e651800063a015c723c0001137ae09aa7571834df1a5cc60d612fb46c52b7f69540eebe2a3dd3d30ba4a5c2f7c64351fae5d99d48ecd85a212b9ff0f836310f1cc032ee118d2ac225b000000d4f90c64441486c60694507cf1b6d29d50dc121234000ac342fd75b8000217eb5311e7cf452ea872c93d504d2814081530512c18b4c80ba18c69a031280002c32c25c10c00030500c2c0001a49b55aafd45a0003058c90795ff3da033dd7dabd84af90b00033057923c11c58f290a3e7636d1018fe49f8086347e5021bff69192cc4c9601982ca08acb75c0544bd52d807c1ad824339ead8f02b95100009480003925e08ca8e531fceead51018d8d1ca6818fd704575cd70001456805815971a0893d065b4780c2c65a49c010c2d705bd5a269a50528ef8879eb8ea3526574e80a90000000000355b081ae390003172000051b5304922107c000000000063c800000018af40a2d2d725a6970000ab18894d58c1e3cbc9ad400080e447162c700df1f6e5bd29e70e90768dab4bed2e0003487d1b98aca265d4dda0800000028579b0380995ac4fd0002c770d344cf8c6413360a721f54418f53875c95d82907f155e13663650ff73a68db72e365ae308835520c34f94004e4a03f72ca91674930df46a54d349470e9ad7312aa77d1d94de017ba47844f09a80044fc55a62bcb5b743653b502a6582441b1f851ef07aec64187d3ca45acabf28a0888c4f326a3454cac2296fbc425c6f8198c27913cf187492c0e12fc552414fac1dc8541370e08a10355917d3e1d6fe1a400c020002060e0000010100090006000800080e04000400000802000201000503000301010f02010007000004010104000508130001010005001c0000070505000002010403010400000202000300080003001200070800000301020102000d010a0003001003030d00800000062a07000637000202020808090b1a05000e0d00020004000000000921011e06000502080d010e0b040000000d0757000202000f00000001053614097401060102010906000000010501030101050c2a020100010c05030103001a000006121604030108010007020000040403030000050010000800000502020c020100290400000004000300000d050000010f210100000804000500 else 0x38b50d2a11f67f9972d440c784eb2460000ad3a67d5262eda255bcbbc312ca4bc8e0c3fccf8dd0002cea43b1d4512435147ca3c340000e96c144c488a0591a6c09ed9a5060498165ad39cac8fafc468b0954c0000000000ebd04208598a663cbe2092382ce3106dc03c8ec73bc17643b2b92d232096ebb40bf24c72cb155dc90000322f131205453815b1150019f11c132d29955a8eb231555673398c1c63521190456e5e8a6f8e584c0c8c79a2d37205d243000290d1c6c0005c134f3b389aabeab0d620000000000284551d40000001b42ed42f374316084957bb08838409c737103e84834829bc649fd3c4000a30000022d80000)
def mo487D10 (j : Nat) : Nat := 0x1050918a20119022625404629750d18028804618c1462002d434600821404620021a1062d403268418c00419a2002285101063b02001062e7b015c9c481f8de60270e45412003fd62ff4cbfd61ff187fd41ff107fd31ff487fd60ff503fd30ff483fd10
def mo487H10 (j : Nat) : Nat := 0x603190cc3900019a8c140040001963e88000f1b80030b7a2fe142046c6142b7aeb1080000003a0007a4bee5d30cc0bb875a344403c2dedf1084b7688d4c8d5bc27a170aaf209f152907cbcf24525d4a200fc32a42415e479c16810b0eeea54623b6f06fabc554e3008f6c9d60b73389e90a143853a144b0a300f921d8fa4f2633c8ed1b448802221200810acb3ed8c30a6881405b2291f6807e52e9e394c01081d840bc7fc6bf144b378704a9075d31c9fc09ad1ac3e591b674448806a9c3a94f73a41718587e46563f316a42a07643c300a65200eaa87998001800f0d58b063286bc262cf766732cb18d9bc001a7153b8003e4363600075e503f33879ab1a0000553239a591a9a0000001124000000c42851502e000489c584000a722444d0dc4e5476be05c904ac47b41b85180d018000392aae001268f0000000a8700000014b2401bbbf89a4d332a9098002e2226ce2ab042cf6c2deafa9ba24600004000800444307a300080000818001002c080000405b0200000001800002080840000000000c08d000038000284070000088060008230000040000080001c348003400802000030000000a604080000000100002b63400000000000004043815000025000c00600000808e00002
def mo487D11 (j : Nat) : Nat := 0x9a861ff
def mo487H11 (j : Nat) : Nat := 0x1680091000000000003510b9635f8fc38800001c1a699165c902006cc0010667a800000000000b59380001fc0062501018
def mo487L : Nat → Packing
  | 6 => (2,5,5,0,0,0,0,mo487D6)
  | 7 => (118,4,5,0,0,8,0,mo487D7)
  | 8 => (371,3,5,0,0,12,0,mo487D8)
  | 9 => (137,2,5,0,0,13,0,mo487D9)
  | 10 => (13,1,5,0,0,9,0,mo487D10)
  | 11 => (1,0,5,0,0,0,0,mo487D11)
  | _ => emptyPacking
def mo487I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 6 1 1 mo487H7
  | 8 => lookupWord 90 152 6 12 7 1 mo487H8
  | 9 => lookupWord 258 578 8 14 9 1 mo487H9
  | 10 => lookupWord 127 214 7 13 8 1 mo487H10
  | 11 => lookupWord 11 41 2 9 4 1 mo487H11
  | _ => fun _ => none
def mo487 : Forest := ⟨1511,11,fun i => mo487Y[i]?.getD (0,0),mo487C,mo487A,mo487L,mo487I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P6_0 : CutRow mo487 6 0 2 := mixedCut (pos:=0x140904120482409108222) (neg:=0x960242) (data:=fun _ => 0x5021073180210635) rfl (by decide +kernel)
theorem mo487B6 : CutRow mo487 6 0 2 := mo487P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P7_0 : CutRow mo487 7 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P7_13 : CutRow mo487 7 13 105 := mixedCut (pos:=0x140904120482409108222) (neg:=0x60148e012c048407) (data:=fun _ => 0x381061023210510338106103321051033810617247306012574020125730201257402017473060124740601214401304473060126110226347406012474060121440130327204664144013036110226327204664574020021440136314401363473060131440130443216140432161401440130343216140144013031460130314401303144013033810610238106102321051023810610261102212036024438321612038106102611022124730601314401304473060135032175347306013144013044730601347306016144013044730601680321756473160132331513003403414573120138321617038106102321051023810610232105103233151203210510232105101321051025740205703315170033151506740205103315150034034140340241432105104473060134730600247306016473060124730601247306013034034144730601313602453473060124730601347306002473060134730600247306016473060064730601247306001536024130520166303403414536024520350346338106141035034621731206257302156614238318032174115210813) rfl (by decide +kernel)
theorem mo487B7 : CutRow mo487 7 0 118 := (@joinRow mo487 7 0 13 105 mo487P7_0 mo487P7_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_0 : CutRow mo487 8 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_7 : CutRow mo487 8 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_55 : CutRow mo487 8 55 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_103 : CutRow mo487 8 103 22 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_125 : CutRow mo487 8 125 6 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_131 : CutRow mo487 8 131 200 := mixedCut (pos:=0x140904120482409108222) (neg:=0x60148e012c048407) (data:=fun _ => 0x3210510414401305144013055740201314401304144013051440130538106104144013041440130414401304144013041440130414401304144013041440130414401304144013041440130414401304146013043810610414401305832161601440130557402013611022241440130414401305144013045730201357302013832161306110222483216130573020138321614032105103573020133210510338106103832161303210510332105103321051033810610332105104321051042331514032105103233151303210510338106103321051033210510323315130381061033210510432105103144013041440130414401304144013043810610414401305144013058321617014401304144013045731201357402013473060130340341557312013034034140340341457302013034034140340341453602415611022236110222447306013473060134730601327204626574020135360247457302013034034150340341561102223611022135730201303403415035034140350341403503484381061045731201314401304144013045730201314401304144013043810610438106104611022236110222447306013473060134730601357402013473060131440130414401304144013045730201338106104144013056110222361102213573020134730601314401305144013041440130414401304611022136110221347306002611022135740201353602474573020133240510332405103034034153210510457312013034034140340341403403414034034143210510453602415321051045360241453602415536024145360241438106163574020135042175350320752536024745730201303403415034034153210510403403414034034140340348403503414035034141521083550320752034034045360240403403404144013641440136414401364381061046110222457312013611022247232465232105104573020136142385306203515611022243210510425201615272046152520161572324651611022246110222450421753252016155730201380321763503207521521083561102213611022136142385315210835) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P8_331 : CutRow mo487 8 331 40 := mixedCut (pos:=0x140904120482409108222) (neg:=0x2904b01c03800e42) (data:=fun _ => 0x47513013475130135721401338013103380131035721401361014224572140133801310383403130380131045761401338013104320161035751401332016103320161048340314032016103320161043801310438013103575140133801310338013104575140134751301347513013475130135721401357214013142103041421030547213013142103041421030514210304142103841421030514210305) rfl (by decide +kernel)
theorem mo487B8 : CutRow mo487 8 0 371 := (@joinRow mo487 8 0 7 364 mo487P8_0 (@joinRow mo487 8 7 48 316 mo487P8_7 (@joinRow mo487 8 55 48 268 mo487P8_55 (@joinRow mo487 8 103 22 246 mo487P8_103 (@joinRow mo487 8 125 6 240 mo487P8_125 (@joinRow mo487 8 131 200 40 mo487P8_131 mo487P8_331))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P9_0 : CutRow mo487 9 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P9_5 : CutRow mo487 9 5 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P9_53 : CutRow mo487 9 53 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P9_55 : CutRow mo487 9 55 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P9_103 : CutRow mo487 9 103 34 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo487B9 : CutRow mo487 9 0 137 := (@joinRow mo487 9 0 5 132 mo487P9_0 (@joinRow mo487 9 5 48 84 mo487P9_5 (@joinRow mo487 9 53 2 82 mo487P9_53 (@joinRow mo487 9 55 48 34 mo487P9_55 mo487P9_103))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P10_0 : CutRow mo487 10 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo487B10 : CutRow mo487 10 0 13 := mo487P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487P11_0 : CutRow mo487 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo487B11 : CutRow mo487 11 0 1 := mo487P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487T : mixedTables mo487 11 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo487 0 0)
  · exact (mixedEmpty mo487 1 0)
  · exact (mixedEmpty mo487 2 0)
  · exact (mixedEmpty mo487 3 0)
  · exact (mixedEmpty mo487 4 0)
  · exact (mixedEmpty mo487 5 0)
  · exact mo487B6
  · exact mo487B7
  · exact mo487B8
  · exact mo487B9
  · exact mo487B10
  · exact mo487B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487G : graphValid mo487 (boundsBefore KM471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo487R : Impossible false (graphGoal 487) 11 (vars 487).toFinset := by
  rw [show graphGoal 487 = targetOf mo487 by decide +kernel]
  exact mixedRoot (g:=mo487) (top:=11) (i:=0) (before_sound KM471 VM471) mo487G mo487T (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mlow487 : Lower false (varsX 487) (graphGoal 487) 12 := plain_low (hints:=4296017494) (by decide +kernel) mo487R
def KM487 := extendKnown KM471 12 [(487,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM487 : Known false KM487 := extend_ok (m:=487) VM471 mlow487 (by decide +kernel)
def mo479Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffe5c001f,0x1554812),(0x1804180,0x1fc0000),(0x218060,0xffffffffffffffffffffffffffffffff5c82a1),(0x3e00,0x1fd5816),(0xfffffffffffffffffffffffffffffffe0c0007,0xfffffffffffffffffffffffffffffffeaab7ed),(0x0,0x0),(0x320078,0xa20548),(0xc03f80,0xfffffffffffffffffffffffffffffffe02a7e9),(0x103c000,0x17816)]
def mo479C : List ColumnInfo := [(8,0,471,0,11)]
def mo479A : List (List Nat) := [[]]
def mo479D11 (j : Nat) : Nat := 0x1ff
def mo479L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,mo479D11)
  | _ => emptyPacking
def mo479I (_ _ : Nat) : Option (Nat × Nat) := none
def mo479 : Forest := ⟨1503,11,fun i => mo479Y[i]?.getD (0,0),mo479C,mo479A,mo479L,mo479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479P11_0 : CutRow mo479 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo479B11 : CutRow mo479 11 0 1 := mo479P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479T : mixedTables mo479 11 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo479 0 0)
  · exact (mixedEmpty mo479 1 0)
  · exact (mixedEmpty mo479 2 0)
  · exact (mixedEmpty mo479 3 0)
  · exact (mixedEmpty mo479 4 0)
  · exact (mixedEmpty mo479 5 0)
  · exact (mixedEmpty mo479 6 0)
  · exact (mixedEmpty mo479 7 0)
  · exact (mixedEmpty mo479 8 0)
  · exact (mixedEmpty mo479 9 0)
  · exact (mixedEmpty mo479 10 0)
  · exact mo479B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479G : graphValid mo479 (boundsBefore KM487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479R : Impossible false (graphGoal 479) 11 (vars 479).toFinset := by
  rw [show graphGoal 479 = targetOf mo479 by decide +kernel]
  exact mixedRoot (g:=mo479) (top:=11) (i:=0) (before_sound KM487 VM487) mo479G mo479T (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mlow479 : Lower false (varsX 479) (graphGoal 479) 12 := plain_low (hints:=4294997620) (by decide +kernel) mo479R
def KM479 := extendKnown KM487 12 [(479,[]),(507,[112,97,82,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM479 : Known false KM479 := extend_ok (m:=479) VM487 mlow479 (by decide +kernel)
def mo495Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffec00c601,0x1fa08400),(0x123101c2,0x1e110a40),(0xc03808,0x1e446100),(0xe0004,0x1fb39ec0),(0x0,0x0),(0x30001d0,0x4e7180),(0x4003e20,0x1b1ac0),(0xffffffffffffffffffffffffffffffe80fc007,0xffffffffffffffffffffffffffffffe04c613f),(0x11f00038,0xffffffffffffffffffffffffffffffe1a0843f)]
def mo495C : List ColumnInfo := [(8,0,487,0,12)]
def mo495A : List (List Nat) := [[]]
def mo495D12 (j : Nat) : Nat := 0x1ff
def mo495L : Nat → Packing
  | 12 => (1,0,1,0,0,0,0,mo495D12)
  | _ => emptyPacking
def mo495I (_ _ : Nat) : Option (Nat × Nat) := none
def mo495 : Forest := ⟨1519,12,fun i => mo495Y[i]?.getD (0,0),mo495C,mo495A,mo495L,mo495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P12_0 : CutRow mo495 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B12 : CutRow mo495 12 0 1 := mo495P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495T : mixedTables mo495 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo495 0 0)
  · exact (mixedEmpty mo495 1 0)
  · exact (mixedEmpty mo495 2 0)
  · exact (mixedEmpty mo495 3 0)
  · exact (mixedEmpty mo495 4 0)
  · exact (mixedEmpty mo495 5 0)
  · exact (mixedEmpty mo495 6 0)
  · exact (mixedEmpty mo495 7 0)
  · exact (mixedEmpty mo495 8 0)
  · exact (mixedEmpty mo495 9 0)
  · exact (mixedEmpty mo495 10 0)
  · exact (mixedEmpty mo495 11 0)
  · exact mo495B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495G : graphValid mo495 (boundsBefore KM479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495R : Impossible false (graphGoal 495) 12 (vars 495).toFinset := by
  rw [show graphGoal 495 = targetOf mo495 by decide +kernel]
  exact mixedRoot (g:=mo495) (top:=12) (i:=0) (before_sound KM479 VM479) mo495G mo495T (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mlow495 : Lower false (varsX 495) (graphGoal 495) 13 := plain_low (hints:=4296046166) (by decide +kernel) mo495R
def KM495 := extendKnown KM479 13 [(495,[]),(503,[112,97,82,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM495 : Known false KM495 := extend_ok (m:=495) VM479 mlow495 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff0000001c07807f0001f,0xfffffffffffffffffff81520c2c2982852524d),(0xe03e0007f8000e20,0x103e24e45a899300000),(0x80f00003f8000003000,0x5f69d7d39a78f00000),(0x1fc00000000001c0,0xfffffffffffffffffffb37e7cecff9fbf6d6cf),(0xfffffffffffffffffff0000000000007f00003,0x7eadf3d3d67d7adadb2),(0xf000000007f801c000,0x6fc1db1ba5766c00000),(0xf0000003ff8000e0004,0x7a096282c6587000000),(0x1fffc000000001f8,0x4c81831300604092930),(0x7ffe0000000000ffe00,0xfffffffffffffffffff80000000000000fffff)]
def mo511C : List ColumnInfo := [(1,16,494,0,11),(128,8,375,0,11),(34,0,477,0,10),(204,1,290,16,5),(8,0,503,0,13),(320,4,187,0,7),(17,0,494,0,11),(102,256,153,0,4),(51,128,324,8,5),(68,0,443,0,10),(258,32,221,0,7),(424,2,85,0,4),(277,64,170,0,4),(16,0,495,0,13),(85,0,426,0,7),(4,0,507,0,12),(68,9,290,144,6),(354,4,153,0,4),(153,0,358,0,8),(32,0,479,0,12),(256,0,255,0,10),(288,10,85,128,5),(326,32,153,0,4),(170,0,341,0,7),(38,0,473,0,7),(130,8,373,0,8),(290,0,221,0,7),(66,36,153,256,5),(36,0,475,0,9),(100,0,411,0,7),(258,36,153,64,5),(136,0,375,0,11),(155,0,356,0,5),(2,144,356,9,7),(324,0,187,0,7),(49,0,462,0,8),(0,24,358,129,10),(320,36,153,2,5),(260,80,170,1,5),(217,0,294,0,5),(260,0,251,0,8),(157,0,354,0,5),(140,0,371,0,8),(32,144,324,11,7),(0,8,375,128,12),(64,16,430,1,9)]
def mo511A : List (List Nat) := [[],[112,97,82,67]]
def mo511D8 (j : Nat) : Nat := 0x1000615166740b96d1a721931
def mo511D9 (j : Nat) : Nat := (if j<1 then 0x8157ee7d27b678f77374c7256fe6e26bb69466d64661f6035d15b559955c53550e4f24cb4af48846c45042940d3e63bf39837c3553232fc2e02b92922602392121f61cf1a818c1651491221060df0b809c06a043027000d779706c09625581d76d706d4a664881d7e9c76c0a664881d7e9706c0a664881c7dd302e5a854961c7f5102e5a854961e775702a4a560561ceddc06d8a854931cfd5606c4a854931d6bd716d89859121d76d702e56554921fb65706155260521fae5706198258521fe65705955258521d6ddc06d8984c521c7ed716c8a959580c7ed716c8a958580c7edb76c8a958580eb75a66158154570eb75a26158154570cfcd316c8a859560cfd5c36c4a859560cedd316d8a854960cfd5c36c4a854960cf5d316d4a858560cfcd316c8a858560cedd316d8a848560cf5d316d4a848560cfcd212e96560930facd516198258930facd856198258930facd816198258930cf5d522e98558530cfcd522e98258530facd526198258530fb55526158158530fb55626158154530fb55866158154530fb55826158154530cf5d652e985485308fddc82e96548530facd656198248530fb55656158148530ceed716d8a854920cfe5c76c4a854920cfe5716c4a854920ceed716d8a848520cf6d716d4a848520e5dcb929d8664d10e5dc9829d8664d10cdddb829d6564d10ed5d8529d6564d10d5dca92dd9360910d5dc982dd9360910cddda82dd9354910dd5d852dd9354910ddcd822dd9354910cf75522e98558510fae5526198258510ecdca76196564d10d7c9c36c0a664881bae5c22618660561baf1c0261866056199f5c72e192605619b75c52e19260561ce9dc46d8a854931af95c12a16454931af8dc22a16458531de64ba5955258521d69dc46d8984c521b69dc6261644c521b71dc5261644c521f2cd96619824c521fac586609614c521aaedc22a58659580e27ca96198559580c7cdb36c8a958580aaedc22a58658580a2fcc9699865458097cdc22e5654c58097cdc22e5614c580c6eca92d99248580ad5dc72c5a521930af4dc22c5a521930eacda66198254930fa4d865958254930af4dc52d9a220530afc9c02d9a220530ceccba2c98658530cf54ba2d58158530fa55855958158530eb55a66158154530eacda66198248530af4cca5955248530eb55a56158148530fb45855498148530fac5866096148530fe45655496148530cfc5c36c4a854920af65c12a175549209ecdc62e1524c5209fc5c12e1524c5208f6dc52e98748520aecdc62a13148520af4dc52a13148520f969875d55260120a5ddc6260a764d10a5ddc2260a764d10c5dcb829d9664d10c5ddb829c9664d10c5dca82dd9364910b5ccc764d9254910dcd4b76199358510dcd4b75959358510a5d9c02e5a721931c59cb96d1a721931a5d5c12e5a721930 else 0xf0c00f4107c09e084e0c0600b080600b09e0805010180c016178100ef003d8001fc087e0403ec00c0600b0ba08077801f4100fb003e8201f6007f344280b0fe6885e8218070061005f89e000388f04060401c018402802fc4f0001c5f0001fa087e03a08070c03803086160e3321a0ef02104a019e043019e042f018642c85e044707e040605e07c00150c21780f021f80095e043f020302f00117c087e0025045f022042f01e043019e042085e040607e01e08110f60905f000784f01d040887e03a08110c040250bc06c10221f80d82044300601c2f0002001860200185e01450030c040030bc030a006180be0400c301600c20114080180b100180804e1808006100b01000c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def mo511H9 (j : Nat) : Nat := 0x24
def mo511D10 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0x48580483fb4baaa4b0241ff25493158120ff926290ac09047fdb62a5874423fe5d30ecb2211ff6e0a95d9108ffb6c54b0a8847fdb82a5654427f6d9150b2a213fd6c4a859510aef972c2aca8857ddb626193442beed9130c9a215f72e19664d10afbb704b326886ddca7619934436ee53b0ac9a21b7729d6564d108ff974c3b248867dca864d92442eee5bb26c1221ebb61982589109dfb6c542a4884ff5b12a152442bbe5cb0aa92217772dd9354910eedaeac92a48877cd9364952442eee5bb26c0a21f5d5d5655c510faeaeaa92e2885df5b72a161442fbada950b0a217f96c8a858510bdeb6c4c2c28876f59861961443f725930cb0a213fd2e98558510bdeb70b2ac28876f59859561443f3ac2acab0a21f9d5d56558510fdab0cc9ac2887ed56564d61443b7ab2b24b0a21ebd6198258510fceacaa92c2884f7db52a1614427f6d9150b0a215bf6d89858510bbb96ec9ac28857ddb626131442beed913098a21fb5619614c5109dfb6c54242884f7db52a121442eee5bb2690a21ebe6196560110fbe30eb8b00887df1755c580443f78c32c2c0221fbc5956160110f5f30cb0b00887ef18658570443f78b2ac2b8221fbc6196154110cfab66d0930a967d9b36809854aaf6db94cc91035db6d4a664881afd3605332440d5f9b729990206bbcda94cc81035fa6c8a664081cfb366d0130b0e774a9295815872ee5cb4e43263b676d1a721931dbab62d390c98facd86609624c66eedb950a92633b76d8a8549319fab62542a498cfd9b02a1524c66eedb950b0a633d76d4a8585319f9b64542c298cfd9b02a1614c72deda34e4c2439af6d1a626121cfb366d013090d5bdb726164486b5edb130b22435cf6d49859121af73604c2c890f2ed9661982486bb65cacaa9243cdd6558560521f6cb0aa930290fae58660961487f32b2aa4b0a435776dc984c521adbb6c4c26290d75db526131486becd813098a4369f6d49661980b5db644b30cc05af5b1259866023f6d9152b2b011fb6c8a958580f4f30cb2b00a865dcb969c864c36ecd834e432613776dca8595309f9b64542ca984fd5b12a1654c27ecd8150b2a61eb361982589309bbb6e542a4984eddb62a1524c27ead8950a92613f66c0a8549309bbb6e542c2984f5db52a1614c27e6d9150b0a613f66c0a858530f6ab0ac0aa2984dddb72a1214c276edb15090a613d76d4a8485309fb360542429872ed98619624826f6db950a92413bb6d8a8549209fcb62542a4904dedb72a121482776db15090a413db6d4a848520f3d30eb9300907ae986589804832eecc14ec9a21977260a764d10cbb94ecb3268865dca7259934432ee53b2ac9a215772dd9364910bba96ec9ac2885dd8b764d80443cf8c3ae2c0221ebc6196160110f9e2ecb0ae0885dd8b764d50443eb8baae2a8221f9c5956154110 else 0x613f72e96560930f5bb0cb2b04987ecd86609624c27eedb150a92613f76c4a8549309fbb74c32a4986edda6619524c37aed330aa92617d76e16554930debb50b2aa4987e5d86595524c37e6d3304a9261ef36198254930fe9b0ac12a4987f4d65609524c2eeedb90cc0a617d76d48660530bf9b6443302985fd9b0219814c37aed314ac0a61bd7298a5605309fb974b2b02987b5d85595814c37ae52b44c0a61ed76155260530ddbb64d3102986ddda7618814c37aec334a40a61bf36d9a220530df996cd1102986fcd86688814c36eed3b0440a61bb76998220530debb4ac1102984fddba588814c36eed3ac440a61bb76996220530debb4ab1102986fcda2588814c37ecc334040a61bf6609a020530deb96ad42c2986fccb26a1614c27eeda950b0a613f76c8a858530bbbb6e542c2985f5db52a1614c2fe6d9150b0a617f66c0a858530ddb974c32c2987eccb2619614c27ee5d30ab0a617b76e16558530ddbb50b2ac2987e5d85595614c27ee5d304b0a61eb76198258530fcbacaa92c2986fd4ba605614c3f6ac3302b0a61fd52d58158530f7ab0ac0ac2987ed565605614c27eedd302b0a613f76e98654530ddbb4cc32a2984fddba219514c2faeda90ca8a617f36c88654530bfab62432a2985fd9b0219514c37aed330aa8a61bf56998154530feab0ac0aa2986f5cb56a1214c27eedb15090a613f76d4a848530bbbb6e54242985eddb62a1214c2faeda95090a617f66c0a8485309fbb74c3242984fdcba619214c376ed330c90a613f76e985485309fb974c2a42986f5da5615214c27eedd2ca90a613f72e96548530df9974c1242986fcda6609214c3de6c330490a61bf36958248530bf9b70a9242986fcda8549214c3fa6c2aa490a61fd35955248530dfab4cc0a42987f54b5605214c37ead2b0290a61ef56158148530ff8b04c0a42987fc552605214c2feadc2c290a61bf56a16148530fdab0cb0a42987ed565585214c3fe2c12c290a61ff15496148530cdf94c50b309047fcba61d9548397ecc30cb2a413fb6d4a85c9209fdb62542e4904fedb12a1524837b6542eaa9241ddb6617554920cefb5252b02907b6d8554981482bfad8930b8a411ff2e99858520e5fb30c32c29047fcba65561483f36b2aa4b0a41edd6158154520fd9b0cb1262905fccb854931483be6cc2a498a417f36d9524c520fe9b0aa9262907f4d65549314827f6da95090a413fb2e987485209fd974c2a42906f6da55d521483df2c3b0290a41fd92d58148520f7cb0ac0a42907ee565585214837e65426290a41df36613148520df9b4c98a42907fc5814c521483fe2b0a6290a41e7e61d7560120f5f30cb2b00905fe8ba54980483df4c3aa4c0241fda5d55260120f3f30eb8b00907af98658580483fe4a9262c02417fa2e92160120f7d30e90b00907fc931) else (if j<3 then 0x2cc2b0290fb758559581487f9a52ac8c0a43eed6156460521fec94ac130290fbe585609814877ba52b40c0a43bdd2d5a858521ddeb50b2ac290f6f59859561486ff25d304b0a43fb95958258521bfc974a92c290d5fdb726161486b7edb130b0a435df6d49858521aff3604c2c290cfecba60961487d76c3304b0a435f76d8984c521afbb72c326290f6dd9661931487bcecc2c898a43de7261644c521ef9b2cc126290fbcd8660931487fc6b230498a43df5659814c521ff2ac8c0a6290ffc58260531486feadc2c298a43df5661614c521fdab0cb0a6290ffc58258531486d7eda92cc33016bf6c49661980bcfb6a4b30cc05eedb225986602f7ad892cc33011ff6c4a9595809fdb6454acac06afca961965603d765930cb2b019bf2a58659580cef952c2acac07a7d8661565603d76c3304b1301abf6998654980f4fb0cb2aa4c067eca964952602f765b324a93011ff6e89624580afdb644b122c057f5b12589160357ed330c48b019fb659a224580d7db0cd1122c056fcb66489160377cd834c40b01a7f69d8620580d6fb0cd2902c06bed86688816033eed9952b0b019fb6c8a958580cfeb6254ac2c067f9b02a561602bf6d9152b0b013fb6c8a958580d5f974c32c2c06afca961961603d765930cb0b019bf2a58658580f5eb0cc0ac2c057f8b968161603d7cc3340b0b011ff2e5a654580d5fb4cc32a2c07b758560551602bee5caca98b01eb7619654c580afb972b0a62c07add86585316023fedb15290b011ff2e5a648580d5fb4cc3242c067eca964921602f765b32490b019fb2a58248580f5eb0cb0a42c04ff5b12a1525c27f6d9150b0ae11ff2e99858570f6eb0ac0aa2b84efdb62a1215c27beda95090ae137f6dca8595609fdb64542cab04ff5b12a1655826fedb950a92c13bf6d8a8549609feb62542a4b0677da9295815832fecc34e40ac19bf661a620560cefb30d2902b067ed9868881582bfad8930b8ac137f6dca8585609efb6a542c2b04fedb22a161583dbac2b02a8ac137f6dca8485609dfb6c54242b04f7db52a121583d7cc32cac02c17fa6c8a160160bbf36e40b00b05ef9b620580582fbcda902c02c17fa6c88160160f3f30eb8b00b07af986585805823fe5d30ecb2a1f9b2c98659550f4fb0cb2b04a87aed86609625423fe5d330b0aa11ff6e89858550adfb6c4c2c2a857f5b126161543b3e54acab0aa15f76d8984c550afbb644c262a87e756558521543d7cc32c2c02a1bf3694a261930df9944d0b0c986fcca2285864c37aed8b4a43261bd72c5a521930dfab6ad090c985dddb7219854c2fe6d910cc2a617f56c48661530bfb3604330a986fccb26a1654c27eed9150b2a613f76c4a859530bbbb6e542ca985fcdb22a1654c2fead8950b2a617f66c0a859530fd9964c32ca986f5cba615654c3f2ec330ab2a else (if j<4 then 0x54433fed432eb2a21dbf65d8659510eefb2ec2aca8877dcb961993443bee4c30cc9a217f76e16564d10febb0ab2b26887afd6561982443bee54b26c1221df72619360910fddb0cc12c48867fda865d524433fed432ca9221ddf65d8554910eefb2cc2aa4886fdda864d52443faec2b26a9221dfb65d8254910efdb2cc12a4887bed8660952443fe6c9b04a9221f7d61d865c510fbeb0cbaae2885ff5b859571443f7ac32cab8a21fdd615655c510fbeb0ec12e2887df57560971442ffadc2a4b8a21fdd615525c510ffcb04a92e2887ef4b961961442ffa5d2a4b0a217fd6e15258510fdeb0ca92c2887f758554961443ff2c12a4b0a213ff6c8a858510fdd964c32c2887afd82619614427fedb15090a21efb6198248510bff370b2ae0887ef98659570443fbcc2acab82217fe6e1525c110fef30aa92e0887fe98254970443df6c3ac4c0a41efd61d8158520fdd964c32ca887edd86595934427fedb150a92219fd6dda126152cfeb6cd0930a967f5b06849854b7b652944cb303ddb2c99625581aefb604b12ac0f5bdb465d86206bf6d814cc9103d6f6d19760881efb30cd1b2040f7d9a3609902073f6d2944cc2c3ddb294a266161cef94ad0330b0ef6ca5289985873f6cc3444c2c3bdb695a226161df5b48d1130b0efcda36889858777ad33424c2c3bdd695a126161dfab46d0930b0efe5a2684985873fccc3404c2c3bf66cda026161dbf34ed0130b0eef9a6680985877bcd2b404c2c3bee691a026161dfb346d0130b0efe9a2680985877f8d0b404c2c337f6dca8649619efb6a54324b0cff9b02a1925867f65d324c12c39fb2a5926096197f970d4aa4b0c7fcb96a1525863fedc950a92c33fd6c4a8549619ff360542a4b0d7ecb960952586efadb930c0ac37dd6d49860561bfcb644c302b0dff1b026181587d7a4c30cc0ac3bdd2a4a560561fceb0c52b02b0fb7595615815877ba52b44c0ac36fd2e19260561f5eb0cc1302b0fb7585549815877ba52b40c0ac357f6dc9864161aefb6a4c320b0d7edb2261905873f6d4944c32a3bf66cda021951f6eb4ec2b02a8fb75a661581547dbac330ac0aa3edd615a260551f6eb0ac1302a8fb758558981547dbac2b40c0aa3bf3694a261931df9944d0b0c98fecd86609624c67eedb150a9263be76a16454931df3950b22a498fbcd86609524c7fc6b2304a9263bf32c9a8585319fbb64542c298ddddb72a1614c6faeda950b0a637f36c8a858531bfb360542c298feccb2619614c77ced42c8b0a63be72a164585319fb974c12c298fadd86609614c7f6ac3302b0a63fe55918158531cdfb6ed313090e6fdb16989848737ed834c4c243b6f6d1a726121dfb366d013090c7fdb62a5854863fedc152b2a435ef6d49859121af7972c2ac890cfecba595824877bad314ac0a43ddd658a560521e7eb else 0xf6c9a620570ddfb04d3102b86efd62698815c37bec334a40ae1bdf609a520570defac4d2902b86fedb6688815c37f65b34440ae1bfb619a2205709ffb6cd1102b86fed62688815c37f659350b0ae13ff6c8a858570dfe974c0ac2b87ef586605615c3fba5ab02b0ae1efd6158158570feeb0ac0aa2b86f7cb56a1215c27fedb15090ae13ff6d4a8485709ffb70d3242b86efd86699215c27fedc34a90ae13ff6d9a548570defb0ad2a42b86fecba609215c37f6d330490ae1efb6198248570dfdb4ac1242b85fedb8549215c37f6d42a490ae1fdb6155248570fedacaa9242b86ff5a6605215c3fba5ab0290ae1bfd6958148570f7eb0ac0a42b87fe582605215c3ff2a930290ae17fd6e16148570dfeb50b0a42b87ef586585215c3f7ab2ac290ae1ff96096148570ffcaa4b0a42b84ffdb12a1955827fed8950b2ac13ff6c4a8549609ffb6a54322b06f7da9295815837bed314ac0ac1bdf688a560560f6facac2b02b07b7d52615815833fecc34e40ac13ff6d4a858560f7eb0ec0ac2b07f74b560561583dfac2b02b0ac1fdd6158154560bfbb70b2a62b05fdcb859531583f6ec32ca98ac1fd7615654c560bfbb70a9262b05fdcb854931583faec2aa498ac1ff3609524c560bfbb70b0a62b05fdcb858531583f6ec32c298ac1ff5605614c5609ffb6a54242b04ffcba61d21583dfac3b0290ac1fdd2d58148560f7eb0ac0a42b06fdda84c5215837ee5426290ac1ff36093148560ffab0298a42b05ff9b720580583fe65930cc2a61ef76198560930dfbb50c2ac4987edd86615624c3fe6c2b04b1261ff32c98660530febb0c52b02987bdd86615814c3deec3304c0a61fd72958260530f7bb0ac1302985fddb8589814c3f6ec32c4c0a61fd72956260530f7bb0ab1302987fcd82589814c2fee5d2a4b0a617f76e15258530dfbb50a92c2987edd86549614c3faec2aa4b0a61ff36095258530ffaaa4c0ac2986fdda8619514c3fe65930ca8a61fd76198554530dfbb50c12a2987bdd86609514c3faec2b04a8a617f76e16254530dfbb50b12a2987edd86589514c3faec2ac4a8a61ff36096254530ffab0cc0aa2987fd582605514c3feab1302a8a617f76e16548530dfbb50b2a42987edd86595214c3faec2aca90a61ff35958248530ffaacac0a429873fd87659814833fed432cb8a41d7f61d965c520dfdb50b12e2907ded8758971483f76c32c4b8a417fb2e1525c520efdb30a92e2905fedb654971483fb6c2aa4b8a41fdb595525c520ffcb6ec0a42906feca85c521483bf6cc2e290a41bfb6997148520ffcb02b8a42907fe57158521483ff4a92e2c0241ffa5c52160120f7f30ec0ac0905ff9b85c560483efcc3ae2b0241ffa5497158120ffd2e290ac09067fd862a5874433fec1152c3a21bfb694a261910dfdb425130c884ffdb22a16))) else (if j<7 then (if j<6 then 0xd12eea5cb4b7296892c8257e4ad895552a1a5364a489421278a4df499a92ed254a49749009191224242c483e90211fb23da477c8eb11cd238846e28d5519ca31d460c8bd117122d545868ab114d228d45008969121a227442087f90f3a1d0437286750c5a17e42d885690a6a11d41da838105fa08a40aa80f900e9ffc3fc07ee8fca1f7d3ec27d14f949f0d3df67b90f641eac3cee796cf1a9e0f3bfa7798ee51dae3b2475d8eaf9d4d3a8074b8e909d0f39fa73ace6f1ccc397e72b4e501c8e390271bce2e9c463868704ce009bef37ba6f2cddc9ba737206dd0db11b50367c6cb0d8d1b0835e26b40d5f1aac352069d0d311a4b34686874d0599f933c4672ccd7999d331665d0cae9946325e6460c7b98db318862a0c4b187f30d06158c1a981e30185fe8bf417d62f885ec8bd0178e2ef85da8ba997412e545c60b8316f42dc45b40b5f16b12d1659e4b3396552c685888b0815fe2bd85768ae195b12b3e5634abd95692aae5514a9995212a1453cca6e14c529525234a3d9464289a50eca14940827ec4f909df13a227164de49b39355267c4c8898592f425ba4b04955129324ee4980922122d242c47fc8f691db239246c88cb118922e445948a99132223643fc87410c7216a42788439070209e40a48090ff61fb43f0c7d38f901ef23d887a30f2a1e263bdc76d8eba1d3c3a087358e4f1c7038847078dfd1be037786e60dba1b5036586c48d771ab634fc6918d0c19fe33c866d8cc9195a324463f8c6d18c031386208c2518122fb45f00bce17642e1c5b30b4516702c705878afd15c22b285598aa615322a3053f8a6d14c0292451b8a2a143028184fc89e213a0270c4d8899512f225b04aa8943126c24a448408e711aa230c45b08a91138223c43e886b10a8211c415881910181fc03ea07c70f741eb43cd877f0ed01d5839f87190e041b9836506b80d381a0033206520c80189030905fb0bbe170c2d605900ae8156029e052009ea136425e84a1091e11e0230844a085c104820003ee07ae0f001cd037406c40d18197830e05da0b6c16202a8051809e812c8242043807d80f201c80376067c0c1817602b404f8098811501f2037406300b40144022c03a005d00a000f8016001a001a00015ff6dc9164182cffb2ed012cc0eff97068096607afed832ec3103d7f6c19760881dfdae0d1130b0e7fd712a5825873feb8152c12c39ff440a960961cffb2054aa4b0e7fd706a5815877fcdbb40432a3bbf5c1a626121defae0d293090e7fd702a5864873febb152c2a439ff5c0a961521cffac054b0a90e7fd702a565486dfedb942c3301aff69d8620580cffb6e54ac2c067fd712a5616027fed8950a92e1fdb6158254970defb4c52b02b86f7ca6295815c37bed114ac0ae1edf5498560570dbfb0cd3902b86dfd8269c815c36feb134e40ae1bb else 0xf07cd02bc4030052021029412140817c0e3fcdd040a17c0e3fcdd040a1741028100c10e000700c40438001c031010e000700c4f0753f1380014505b42f13800145c000a00c3e100800c3e1180020031380604450204153531178012b810307153531178012b8103076004a00c3f4c0c117810385e01811140813421538017381030611454e005ce040c1980128030f806044502041178012b8103051178012b8103056004a00c3f3c1512842e03811b806044502041534fd0b8012b8103071534f1178012b8103076004a00c3040070380500c5014080b42d4fc4e000517c1d4fc4e00051405020212b42f13800145f044af1380014500c0808100170001c03140b60b86020031582e000302020140be180800c4e000800c3e180800c302f8602003130202f8000c4c080bc1803100800c2c000700c302c0800c3c080800c302003080c00c20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000063c8c7498db31a46310c5898a5b12a6212c3c9868b0ba6128c209838305e60a2c111816b0206012bff17f7afe25faabf217ddafae5f2ebe157bc2f6b5ebcbd457a22f375e54bc75785aefe5de2bb91766aeb15d34ba2173dae5f5c9ab8ed714ae175c14b7b96ebadca5b66b6996c52d735ac2b53d69ead2b5a28b4096782ccf595cb24963b2c5a587cb0896032bea5792aeb55c62b7056a8acf55932b145604abc156f2abd5542aa15534aa525476a87d501a9f15396a6e54d3a98b52dea56149e29205208a3a146628b55132a209433284a5070a09940a28024fea9f793e127b54f469e453c227684e989cad38a26f84db89b01354a6924cec996931f26224c1697) else (if j<8 then 0x81128415380e044a1042e0780054411781e0015134fe0342e040c174fe0780128151581020450f42e0381114405780e04451180054030c42e040c0c5412b8083b81114615381030311780e0431500c90b4fe0780054715045e0780128515242e040c104ae060e0d424640c0c54e040c0c1503b8111441538050b81114590b80e0445138090b811144e0042e044510420384ae04451403057810304d3f80e0415105411780e044a174fe0381054412780057811145e0042e0445104500f81030400c45e040c1045e040c0c42e040c0c45e040c0c0e057811144016c1e000301c5020030a090140301c4020250b41020030f5312808f13800446b0505e001e11090090500c1b17866278002c402005f1042e00111b412380b0c050900301c48240700c05100ae000301c403bc4e00051080c180801786e07c4e00111c8e21741040402089e0341044522642e034101c522780d0411108910b80d04111489e03410444f104ae00111018e00080144017c490b800945b0442417800785c3c4201408130f023c4e00111408017c4e0011141b03bc4e0005030602109b0780044542642e02c101c5426c1e0011110910b80b04111509e02c1044401403078071005044030f0000c070c030202c004a00c330403020301c0500c3416c101c3c000700c300c080a05704070e098170006c031509c010eb04111609c020e704111741e0008030402003080800c200f800200c100301c080f86e041de000b1786e041de000b1402044080f80020030c0800c2e008a00c302003080802f82e18031786e00030200b140be1a8202003140800c2e010a00c30200be0b8600c50400c02c0ae0411e18032005e1b810638002c601786e0418e000b1808044202f86c080800c502003080bc08030f86e00030200b15410280800c45040a02003138002c2e000b0b8002c2e000b080500c070c0c00c203202e000b12020300b0c0700c200c0c02c305c0b00c302c0308084080302c40140e02c3030030805030030f86e0709e000b1786e0509e000b14050202e18030200b1380040080c1002020400b0b4fe1b814278002c6d3f86e0709e000b1b8600c0b0f00a08030c0702c202003080702c201c03081002c070c0bc00030f0002c030204028030bc0e3fcd7040a17cd828030c050202f03cdf100a0145f1302f3717014502003080800c2020030bcd828030fcd627c46380a178400c0809c4a06490203e128192408100a127c0043cde04071c21604450204f034ff37810285f034ff37810285e040a04030840a604450205f0045f37810285f0045f37810285e040a0403f1205020382b82f11c00145f360a00c3f134001421108ae0bc4d0005148a01fc4d000514105000700c405bc4f340b0145f03cdf10180145f03cdf100a0145f03cdf1005028505bc4f340b014502402 else (if j<9 then 0x78001c5017c4e000713c4e00070f8601c030c07014030c07014030c1d00c070c1de180301c4014c150803030501741d080303050174101c03030500c0708cf01c0800c400f8001c301741e000301c5017c401d800305f138001c3f138001c3f138001c301c107040c138001fc40140c14100140700c0c14100158000c0717c4e00070304e180700c3f138001c300c070b8001c030fc40178001c4f138001c30300b080b030202808017c40438001c702bc4e00071386e07c4e000717800434101c40434101c3e0010d04071010d078001c4e000700c0c10050040700c0c1407014030c0700c2e180301c3f138001c3014030b86f100c02f81e0054173922407e1bc406c0c02f81e0392269201c2e1bc4e0780e4808180ae1bc41534f0300be0780e48a02b86f1054d3c0c02f81e03922b84e00080304d4f86f13804380c1b53e1bc4e030e030601784e00080305e1805f105ce010e0307e1805f105ce030e0307e1989e000b1189f1092e00071489f1192e00071589f1192e00071489f1192e000717412380b0f84e00080304e1bc4e030e0305e1bc4e010e03050300501f86f10420440802f802805e13800200c1509e1805f13804380c1f09e1805f1380c380c1c0700c0c0c0530b0000c4017c401f000305017c401f000305017c401f000305017c401f0003053070002003100700c0c0c0800c2e020a00c3028030b86058030f8001c030f020300b0c05020200f8002c30200c0b80040080c1002020141600c30280309c2e040c0ed3e040c0ec2e03811144e060e054330b8000cd3839991b81838150d81324080f812384a0f812384a0f812384a0f42e040c0f53117810304d4f80e044a054560408030312b81030312b81030312b810303d4f810303e050e12831084ae040c101515003b4f810306b4f810303127810303d0b8017381030517380e044a054510b8103031504ae040c1054e050e128400c4ae040c120ee044a0c4ae040c0c5412b810304d4c0ee0445138012854e0445144ae040c0d81324080d53e048e0544d4f81238151353e048e054473f81e001511c9e038112841504590b80e044a180c10b80e044a16c9e0780054410acfe0780128590a190303b3d424640c11cf90a19030490a19030302380908cf8648e18cf90a190304509190303509190303509190303509190303509190303509190303509190303509190303a024200c3a024200c317380e040c105ce040c0f81e004a0544117810303604080303057810303d0b810303d0b810303509190303e040c08540304590b81e00151e42e040c0e42e040c0c42e040c0c151504a00f81030605781030310b810303e050e0543057810303e0381054303380e04151042e040c0c5ce040c0c03e040c0d42e040c0f81238150f81238150f81238150f81238150f81238150c54e03 else 0x50a890143c2405020301786e0403c085e1803a083e074fe00070305f340af10187058e02c7014180300b11c6015c1061c002c6057cd60bc602c071815f341102c4f11c0020c1028ce1b4f700970984f34c170008f130203077009781430330200c30330200c302c0c080c02c2a26c60300b100c02c2225820300b100c02c20300b080c02c20300b080c02c20300b080c02c200d820300b13827040c0c0c02c20300b080c02c20300b080c02c20300b080c02c20300b0b0902c0c0c0c02c20300b080b0302c27020300b100800fcdf100714050600c02c40600c02c30300b0bcd017c400c1614050300b0c050300b0c050300b0c030300b0c0c02c2057cd7040702c5057cd02c07100c02c2057cda240b100c02c209805f100c01c5f37c4014071289b000b0f460300b0f460300b0f460300b0c26f101103047044e054305c0801c3055cff36020440b19cff340af101101c6057cd4081602c5f3405f12d201c5f3405f101101c5b180740ac002c5f358271b8101c5f3682b1b8101c5f34491178101c500c40d3fcde04111a49c0b81b00071421c0810e06c001c6f344902b8101c512702e05c001c5f37020440b13cd1178101c40200702c3f340702c3f340702c3f340702c3043cdc0bc0e04071a49c0b81b0007142104381b0007140a043cde04071410f378101c4f3602e04071149809c0e040717c4700187040c148902c0c0c8971805f11c065c0c1e057000b0ec6054030c26f100301c0c17cdf10050a40717c422b4001c402005f134001c5f3405f101b0585057cd6250502c5057cd6250502c5057cd02c0501c5f37c4028111289f1011b000717c4016c001c4057cd0280b01c5057cd0140b01c5e3ec002c3c240c02c30140c02c30140c02c302c0c08050300b06c4057cd00c0502c502c0c090902c0c0f0902c0c0c0c02c2057cd00c0702c5057cd0140b01c500c80e3fcdd04111bcd2140802c4f340a2174101c5a2702d06c001c508410d06c001c5f340ad040713cd2274101c422702d05c001c5f36020288502c5626027034101c5f360202b4101c5f34182140b13cd80a8902c4f34072140b13cd2140b0f8000c070c10e000301c4e180700c3e180700c3e180700c3d4c10e000b138600c070c0301c2e000700c302bc401))))
def mo511H10 (j : Nat) : Nat := 0xd4f50ddcc391833d30526a6ffb3f7349a697d8e641468f4e42d85ebc656441666a610c4500053692e751146a99ab24341057d7025ec993bae20002f0a0915c608c113d4623f220000e0d9300056b0006390b616c2492ef000000000f0fc65d67a383bb63a74d33efd53b1619e6d82790355b0004638200001d621d65f9d2c74300c15332731000000258b4bb4700112b6a0a1f00000064a0002b766100000033514072cc029ba00071b000000c4c000e1e00000000000000000000000061a51754831c0003140001704cd862637e04f55e9ff2ab57d213429182536508cbb079444a262fe699ed14386e70a6563598c5471f0b85a6c7c13a28c5250ef72d2933fa24b66054e5d10ca3c2df99cd06c12b3db60fa10430876400804000885d930048100614502f1812010c34040033c01000840000e65013d200104410a3ca00300502c0510c3001240012000000
def mo511D11 (j : Nat) : Nat := (if j<8 then (if j<4 then (if j<2 then (if j<1 then 0x2fdda859530bf72a1654c3edd8659530fd7615654c3bdd8660930bf76a1624c3edd8658930ff3609624c2fdda854930bf72a1524c2fdda654930fd7615524c3f5d6554930ff3609524c3f5ca560530ef7615814c2fdda620530bf7688814c2fdda858530bf72a1614c3edd8658530fb7595614c3fd58158530bf76a0614c2fdda854530bf7699514c3f5d8554530ff5605514c2fdda848530bf72a1214c2fdda648530bf7695214c3fcd8248530ff3549214c3fd58148530ff5585214c36fca6661209ff69c984827fda5261209ff684984827fda961d209ff6a5864833fd98619209ff6a5854827fda95d5209ff6a56548377d9559520bfb2a172483ded875c920dfb66162483eed8658920bfb2a1524837ed9854920bfb69d52482feda654920fdb61552483f6d7554920fdb595524827fda920520b7f69c81482efda620520bdf69481482feda220520bfe680814837dd984c520df7261314837dd964c520df765531483fcd624c520ff354931482feca848520dfb66121482feda748520dfb65d21482feda648520bfb695214837ed9548520ff960521483fe56148520ff34c521483bf98760120dfe65980483bf98660120dfe65580483fe97260120ffa58980483fe95260120ff64c580483fe92160120bfe6a1604837f99858120ffa5c960483fe95258120ff64c560483fe92158120ddf295984427fda7261109ff698984427fda5261109ff688984427fda961d109ff2a5874433fd9861d109ff6a5864427fca9619109ff6a486442dfda721910bdf69486442feda221910bfd68486442ff9a0219109ff6a5764427fca95d9109ff6a5854427fca9615109ff6a57544377d955d5109ff6a5654427fca959510df7661934437dc9864d10df7659934437dc9664d10df7655934437dd93649109ff6a5824427fca9609109ff6a5724437ed925c9109ff6a5624427fda954910dfb64952443df5875c510f7d5d5714437f59858510bfd69d61443ef58658510fbd5d961443ef56558510ff564d614437f59258510df7661314437dc984c510df7659314437dd924c510ff5585314437f8a960110efe61d804437f99660110efe619804437f99560110ff664d804437f99260110ffc5c580443ff16160110ff64c580442ff9a85c110f7e5d970443ff1615c110bfe6a1504437f99854110bfe69d50443f797554110fde59550443fd99354110ffc5c550443ff161541109fd6849854a7f9a026152d6f691972076bda465881df668d902067eda2261619fe68098587b758560551b7769c864c6f5da521931bf3688864c6fd5a121931bf6680864c65fda7261219bf6989848677da5261219fe68098486ddda721930bd7694864c2fcda221930bf5684864c2fd9a021930b7769c814c2edda620530bd7694814c2fcda220530bf6680814c2ddca764d10 else 0x2fdb6158254b77d9725581ddf6589560777c9625581ddf25592607b7d8554981ddf255906075fda665c81d7f689972075fda065c81dbf69d962076fda265881dbf681962077bda465881d7f65d8620777d8665481dfb69d922077eda664881dfb299922077ed8664881dfb681922075fd9760881dbf6598220777d9560881dfe69d902077f9a664081dfe299902077f98664081dfe689902077f98264081df768d902077eca2661619ff688985867fda026161bfb68898586ff9a0261619ff2a5825877f4a960561fbd61981587f74a560561efd615815867fda9605619ff6a486546dfda721951bdf69486546feda221951bfd68486546ff9a021951fdd61581547fcca261931bf7694864c6fdda121931bf7680864c7bdd8660931fe7591824c6fdda858931fb7619624c7fcd8258931bf76a1524c6fdca854931fd7615524c7f9d6454931ff3609524c7f9d6460531bf76a1614c6fdca858531fb7619614c7f9d6458531ff5605614c777ca5661219ff69c984867fda6261219ff694984867fda026121b7f69c98486efda626121bdf69498486ff9a0261219ff6a5864867fca961921dbf659864867fda9615219ff2a58548777d95615219ff6a5654867fca959521def661644877bc9859121def655644877eca960921dfb65982487bed8660921dfb65582487fad6460921bfb6a1524877ed9854921fdb61552487f6d6554921feb591524877f59660521fdd295814877f59560521efd61581487fb56460521ff960981487fe55260521bfd6a1614877f59858521fbd61961487ef56558521ff960961487fe55258521df7661314877dc984c521df765931487f9d644c521ff360931487fd5814c521ff558531486dfda725980bdf69496602feda225980bfd68496603afc9661980efb28986602dfda721980bdf69486602feda221980bfd684866027fca959580ebf61965602efca664980ebf61962602feda224580b7f69c81602efda620580bdf69481602feda2205809ff2a561603afd86585809ff6a461602bfda818580bfe68061603bdd864c5809ff2a5216027fda920570b7f69c815c2efda620570bdf694815c2feda220570bfe680815c27fda918570bfe680615c37eca2661609ff69c985827fda5261609ff684985827fda920560b7f69c81582efda620560bdf69481582feda220560bfe680815837dd984c560df7261315837f8a960160efe61d80583bf98660160ff64c5805827fda7261509ff698985427fda2261509ff684985427fda9619509ff6a486542dfda721950bdf69486542feda221950bfd68486542ff9a021950ddf66165543e7d8659550f9f595615437dd984c550df7261315437dd964c550fd759531543bf98760150dfe65980543bf98660150fde59580543fd93160150ff3289864c2fdda521930bf7684864c) else (if j<3 then 0x83bfd8760520dff65981483f7ca560520eff61581483fed7260520ffb58981483fed5260520bff69c81482ffda85c520dff661714837fc985c520f7f61d714837fd965c520dff65571483fed625c520ffb549714837fda958520bff6a1614837fd9858520dff65d61483efd8658520dff65561483efd6558520ffb68961483fed7258520ffb54961483ff58158520bff6a1514837fd9854520bff69d51482ffda654520dff65951483f7d8554520fdf5d551483fed6254520ffd60551483fdd864c520ff761531483fdd654c520ff760531483fdd614c520ffb61d21483fed8548520ffb5d521483fed6548520ffb60521483fed7148520ffb58521483ff98760120ffe61580483ff97560120ffe59580483ff8a160120ffe60580483ff97160120ffe58580483ff95160120ffe61d60483ff98558120ffe5d560483ff98158120ffe5c560483ff95158120dff66098442ffda626110bff688984437fd9861d10dff2a1964437fd8765910bff2a1964437fc9865910bff6a0964437fda961910dff661864437fd9761910dff65986443feca261910bff69486442ffda121910dff619954437fd9861510dff65d854437fd9661510dff661754437fd965d510bff6a165442ffca859510dff661654437fd9759510dff65965443efd8659510fdf61565443f7d7559510ff761993443fdd8564d10ff7595934437fd8764910dff615924437fd7564910dff59592442ffca864910dff661824437fd9760910dff65982443bfd8660910dff65582443fdd9360910bff6a162443efd8658910ffb60962442ffda854910bff2a1524437fd9854910dff65d52442ffda654910dff65952443f7d8554910fdf5d552443f7d6554910ff764d52443fed9254910ffb609524437fd9760510dff65981443fdd9360510dff64981443ff5865c510ffd61571443ff5655c510ffd60971443ff5525c510dff661714437fd965c510dff64971443ff5815c510ffd6a161443ff4a858510ffd26161443ff5a758510ffd61d61443ff58658510ffd69561443ff58558510ffd5d561443ff56558510ffd68961443ff58258510ffd54961442ffda858510bff2a1614437fd9858510dff261614437fd9758510fbf61961443fdd9358510dff64961443ff58158510ffd5c561443fdd864c510ff760931442ffda848510bff2a1214437fd9848510dff65d21442ffda648510dff65921443fdd9348510ffb60921443ff58148510ffd5c521443ff56148510ffe26180443ff98760110ffe61980443ff98560110ffe5d580443ff96560110ffe60980443ff95260110ffe60580443ff97160110ffe58580443ff92160110ffe61970443ff9855c110ffe59570443ff9825c110ffe54970443ff9815c110ffe58570443ff9215c110ffe61950443ff982541109ff6849854a7fda02615 else 0x60dff66187582ffca865560dff66185582ffda859560bff2a1655837fd9859560fbf61965583f7d8559560dff66182582ffda854960bff2a1525837fd9854960fdf61552583fed8254960bff2a1915837fda960560dff66181583bfd8760560fdf29581583bfd8560560dff66081582ffda720560bff69881582ffda220560dff661715837fc985c560bff6a161582ffca858560dff66161583efd8658560fbf59561583ff58158560bff6a1515837fd9854560bff69951583f7d8554560ffd60551583fdd864c560ff761531583fdd654c560ff760931583fdd524c560ff760531583fdd614c560bff6a121582ffca848560dff66121582ffda548560ffb60921583fed5248560ffd60521583fdd3148560ffe61d80583ff98660160ffe61580583ff96560160ffe60980583ff95260160ffe28580583ff98160160ffe20580583ff97160160ffe58580583ff95160160ffe485805837fd9861d50dff61d965437fda961950dff661865437fd9661950ffb28986543f7d8759550fdf619655437fd9860950dff65982543bfd8660950fdf59582542ffda858950fbf61962543fed8258950dff661715437fd965c550fdf595715437fda958550dff2a561542ffda858550dff661615437fc9858550dff65961543efd8658550fdf59561543ff58158550ff761931543fdd824c550bff6a1215437fd9848550bff699215437fd9648550fdf59521543fed8248550ffd60521543ff56148550ffe61d80543ff98660150ffe60980543ff97160150ffe58580543ff92160150ff7695864c3fdda261930ff7685864c3fdca161930ff7699854c3fdca661530ff7619854c3fdc8661530ff7689854c3fdda161530ff76a1654c3fdca859530ff7619654c3fdda259530ff7685654c3fdda660930ff7619824c3fdda560930ff7615824c3fdd6560930ff7685824c3fdca160930ff7615624c3fdda854930ff7699524c3fdd8654930ff7685524c3fdda660530ff7299814c3fdd8660530ff7219814c3fdda560530ff7615814c3fdd6560530ff7689814c3fdd8260530ff7589814c3fdd5260530ff7618814c3fdd8220530ff7588814c3fdda858530ff72a1614c3fdd8658530ff7695614c3fdd8558530ff7595614c3fdda258530ff7609614c3fdd5258530ff7605614c3fdd8654530ff7219514c3fdd8254530ff7589514c3fdda848530ff72a1214c3fdda648530ff7619214c3fdda548530ff7615214c3fdd6548530ff7605214c3fdd6148530dff285984837fca961d20dff661874837fd8765920dff61d954837fd9861520dff65d854837fd9661520dff66175482ffda859520dff661654837fd9759520fbf61965483f7d8559520ffb68965483fed855c920ffb59572483fed8758920ffb61562483fed8754920dff6a5814837fd9860520dff65d814)) else (if j<6 then (if j<5 then 0x586ffca864161dff661905877fc9864161dff65d90587efd8664161dff655905877fd9264161ffd605905877fda066061dff6a5865477fd9861951ffb28986546ffda021951fdf619855477fd9860951eff61982547f7d8560951dff66162547fed8258951ffd69d81547ff5a660551ffd61981547ff5a260551ffd60981547ff56260551ffd68181547fdda561931ff7689864c7fdda161931ff7681864c7fdd8661531ff7699824c7fdd8660931ff7695824c7fdd8560931ff7685824c7fdda060931ff7615624c7fdd8654931ff7699814c7fdd8660531ff7689814c7fdd8260531ff7589814c7fdda060531ff76a1614c7fdca858531ff7619614c7fdda258531ff7609614c7fdda058531bff69c98486ffda026121dff661854877fd9661521dff66165487fbd8559121ffb61582487fed6560921ffd69d81487ff5a660521ffd69581487ff58560521ffd59581487ff5a060521dff65981487fbd6460521ffb60981487ff5a858521ffd69d61487ff5a558521ffd61561487ff5a058521bff6a1614877fd9858521dff26161487efd8658521ffb60961487ff58158521ff766131487fdd964c521ff761931487fdd3164121bff69496602ffda125980eff69d86603bfda561980eff68986603bfda161980eff28586603efc9661980ffb28986602ffda521980bff68486603bfd8661580bff2a565602ffda859580fbf61965603bfd8659580fdf61565603bfd8760980eff61982602ffda858980fbf61962603fed8258980bff2a552602ffda854980eff61d52602ffda654980eff61952603f7d8554980fdf59552603fed9254980ffb60952602ffda724580bff698916037fd9624580dff25891603bfd8624580bff688916037fd9224580eff61d81603bfd8660580fdf29581603bfd8560580bff69c81602ffda620580eff61881602ffda220580dff6a5616037fca958580bff2a561602ffda858580eff61d61603efd8658580eff61961603efd6558580ffd60561603ff9a058580bff6a061602ffda854580bff69951603bfd8654580fdf61551603ff58154580ff761931603fdd854c580ff759531603fdd824c580ff754931603fdd814c580ff758531602ffca948580bff6a121603bfd8748580bff69921603bfd8648580bff69521603fed9248580ffb60921603fed5248580ffd60521603ff56148580ff74c5216037fd9860970bff6a1525c2ffca854970dff661525c3fed8254970dff6a5815c37fd9860570fdf295815c3bfd8560570bff698815c2ffda220570dff6a5615c2ffda858570bff2a1615c37fd9858570ffd605615c2ffda818570bff6a1515c3f7d8554570ffd605515c2ffda848570bff2a1215c37fd9848570bff699215c2ffda548570ffb609215c3fed5248570ffd605215c3ff56148570dff285985837fca961d else 0x570fff299815c3ffd8660570fff695815c3ffd8560570fff689815c3ffd8260570fff549815c3ffd8620570fff608815c3ffda858570fff2a1615c3ffda258570fff609615c3ffd8158570fff619515c3ffc8654570fff609515c3ffd6254570fff6a1215c3ffca848570fff699215c3ffd8648570fff695215c3ffd8548570fff595215c3ffd8148570fff585215c3ffd8761960fff6a585583ffd9861560fff69d85583ffd9761560fff61d85583ffda661560fff61985583ffda261560fff68585583ffd8759560fff61d82583ffd8560960fff61591583ffda960560fff66181583ffda760560fff65d81583ffd8760560fff69981583ffd8660560fff69581583ffd9560560fff61581583ffd6560560fff68981583ffd8260560fff54981583ffd9160560fff60971583ffd525c560fff60571583ffd8758560fff61561583ffd8158560fff5c561583ffd9854560fff61951583ffd8254560fff61521583ffd8148560fff5c521583ffda761950fff61d86543ffd8760950fff61971543ffd825c550fff61d85483ffda760520fff61971483ffd855c520fff59571483ffd815c520fff5c561483ffca961910fff26186443ffda761910fff61d86443ffda561910fff68986443ffda161910fff2a582443ffc9860910fff69d82443ffd8760910fff69982443ffd8660910fff69582443ffd8560910fff5d582443ffd6560910fff68582443ffd8558910fff60981443ffd6260510fff61971443ffd825c510fff61961443ffd8258510fff61921443ffd5258570fff61d52583ffd8748560fff61d65483ffd8760520fff61d61483ffd8661510fff61975443ffd8659510fff61952443ffd8660510bff69c9160affda024582dff2459060bf7ca565d81dff65d96607f7ca565981ffb28996606ffda725981dff65c96606ffda025981dff65d956077fd9665581fdf65c95607f7d9625581fdf61895607bfd9761581eff659856077fd9764981dff65992607f7ca564981dff65592607f7c9564981eff61592607bfd8660981fdf25582607bfd8560981dff65d906077fd9664181fdf295906077fd9564181fdf25590607bfd8564181dff649906077fda765881dff681962077fd9761881dff65d822077fd8664081dff609902077fda266161dff68198587feca266161dff66098587fdda326161ffb68898586ffda226161ffd68498587ff9a026161bff68098586ffca864961dff661925877fd9564961bff6a582586ffca960961dff66182587fed9260961bff6a552586ffca954961bff6a152586ffca854961dff66152587fed8254961ffd2a581587ff49860561ffd69d81587ff5a660561ffd69581587ff59560561ffd61581587ff5a260561ffd64981587ff58260561ffd54981587ff5a060561dff66181586ffda660561fbf61981) else (if j<7 then 0x1a4cda425a37da2b1a209a13da04d9f399e499da19cd59b9d9a899951981996e1961595259459936991e990f990098f3d8e718d158c258b118a4589558889879986f18625857d84d5842d838582b98211814580c1803d7fb97f117e697dc17d197c957c357bb17ae579d178bd77f1774976c575f9755174cd73b973117221713170416f096e616ddd6d596cf96c756b616a4d69a5692168c1686167b9673566b1662d658564dd6435638d62e56261619560ed60215f555e895dbd5cf15c495ba15af9599d58d157e157155595545d52dd51c950914fc54f414e094d3d4c4d4af14a25491147fd47794689452d441943294239414940593f693ec13e193d053c5d3b493ac5396938553789360934d13309321930e12fa92e952d392c492bc52ad529e528f5280526f125dd251124452379228921bd20851f711e5d1d491c111b211a5519411875173d15e114f1142512a511b510e90f450e550d890cbd0bf10b250a59094507c506d505e50465037502610104ffccfe70fda4fcb4fbc4fab0f99cf888f7bcf6ccf600f4ecf444f354f21cf12ceff4ef04ee14ed48ec58eb68ea78e964e898e784e670e538e400e334e1fce0c4dfb0dee4de18dd4cdc80dbd8db30da64d9bcd914d86cd710d5fcd530d488d32cd1d0d074cf18cdbccbf4cae0ca5cc9d8c954c8acc774c6a8c570c438c300c1ecc0d8c030bf88bebcbdf0bd24bc34bb68ba0cb8b0b754b5f8b52cb43cb394b2ecb244b19cb0d0b004af38ae6cad7cacf8ac74abf0ab6caae8aa64a9e0a95ca890a7c4a6f8a608a560a4b8a458a3b0a2e4a260a194a0c89ffc9f0c9e1c9d089c3c9b049a389948987c97b096c095889498938492dc91c890b48fa08e8c8d9c8c888b508a6089b888c88844870c861c850883f482e081cc81007fc87e907da07cd47c507b607a9479c878d87830776476987614756c74e87464737472cc720071106ffc6f0c6e886d986c846b4c6a38699068a067b066c065d065286438639062c4621c615060605f4c5e385db45d305c405b745a845994585c576c56c4561c555054a853dc531051fc5130501c4f504e604d944c804b904a7c49f8492c483c477046a445fc450c448843bc4338426c41c440f8402c3f603e943dec3d443cc03bac3b043a8039fc3954388837bc37143690360c3564345033cc332432a031d4315030842fdc2f342e8c2e082cac2c282b142a6c29c428f8282c273c264c258024fc249c23d02328228021d820e820401fbc1ef01e6c1dc41d401c981c141b901b301a881a0419a418fc17e816f8165015601494135c1248111010200f300e400d500c600b4c0a1408dc07ec074406c00618057004c803fc0330026401bc00f00003ffd5264161fff699825c3ffda560970fff615825c3ffda160970fff285825c3ffda854970fff685525c3ffda660 else 0xf65076483636f625b61fb615360875f975e835d6f5c7f5b8f5a9f596758bf57f3574b565b556b54e7541b534f523b514b50a34fb34ee74df74d074c834bdb4b0f4aaf4a07498348b747c746fb45c344af43bf42cf41df40ef40233f7b3e8b3d773cab3bdf3b133a473957388b379b36cf35bb35133447337b3267319b30f32fdf2eef2e232d332c8b2b9b2aab29df291327ff26eb261f255324ab23bb22cb21db20c71fd71f0b1e1b1d731c5f1b6f1aa3198f189f17af169b15ab14bb1413136b12e711d31173105f0f6f0ea30dd70ce70bd30b070a5f0993090f086707bf073b0693060f0543049b04170393030f026701bf01170026ff12fe8efd9efd3efcbafc36fb8efb0afa3ef972f8caf7fef77af642f59af4f2f3baf312f246f156effaef52ee86edbaed36ec6aeb9eeaaee9bee8aae802e6eee646e532e48ae376e2cee1dee15ae046df56def6de72dda6dcb6dc0edb1eda0ad91ad84ed7a6d6dad60ed542d49ad3ced2ded236d18ed10acfaecf06ce16ccdecbcacb22ca56c9d2c852c6aec606c486c3bac312c1fec10ebfb2be7abdf6bc2eba8ab9e2b862b74eb63ab54ab45ab2b6b0eeb046af0eadb2abeaaad6a97aa866a79aa6f2a66ea57ea46aa37aa242a152a0629f729eee9dda9c5a9b8e9a56996698769786964e9582940292ca91b690c68fd68e9e8d668c768b628a2a893a884a875a868e84c683b282c281427fc27ed27d9a7caa7bba7aa6796e787e772275a274d6737a7242712e6ff66ee26e3a6d6e6c7e6bb26b0a6a626972685e676e667e65b2649e63f663966312626a619e60d2602a5fa65f225e7a5dd25d4e5cca5c225b9e5b1a5a7259a658da585657d2569a55f25526545a536a529e516650764faa4e964dca4d224c7a4bae4a9a498648de485a478e46e6463e459644ee4446439e42d24206413a40923f363e8e3de63d1a3c723b823a9239ea396638be3816376e3636358e34c2341a332a328231da30ea30422f522eaa2d4e2c822bb62aea29fa292e27d227062616254a24a223d6230a221a212a20a61fda1f321e8a1de21cf21bde1aee1a22190e188a17be16ce164a157e14b213e612d211be113a106e0fc60f1e0e2e0daa0c720bca0ab609c608b207e6073e062a04f2042603a2031e020a011a0071ff81fe25fd59fc69fb55fa1df909f861f771f65df591f435f2fdf20df0f9f009ef3dee29ed15ecb5eb7deab1e9c1e8ade7e1e6a9e5b9e511e3b5e27de145e00ddf65de09dcf5dbe1db15da25d8edd821d731d641d551d461d3ddd311d245d131d041cf51ce61cd95cca5cbd9cb31ca41c92dc7f5c74dc65dc549c435c345c231c0f9bfc1bf3dbe95be11bd8dbce5bc61bbb9bb35bab1b9e5b919b829b6f1b601b559b4b1b409b361b295b181b0fdb055aed5adc1ad19ac29ab5daa25a8a5a7b5a6e9a61da55))) else (if j<12 then (if j<10 then (if j<9 then 0xa03160cc2e234e0003028f098001d8210160cc2e207a0003028e10038380a0314210902c000e0319820880014062825850069f101c051e130008045830e1836098030b880e028f864100c3e26002803040a0e057130008028d8002f101408178808c00800a280a2408018805016000741040d410400c3080730c0b018a01028203080070c1a018b864082006204303860d00c5086070c1a018a10c0e183403142181070680628162408018941c002006261814030c0a01c040b8811040e058902006250410030f0c0a018601e207410202d05860400c5416028203040a0bc302006260010030f0c0801860bc30200620400a090161816031c02220406058902006250410030c201ac302c062e1814030e0580e20200a2e00064104098001904102027000b018980018203028230c0301710198005920b0400c3c3710100206600163c0817800188050702c06261a0541040405816010a10040a0ac340a8208080c0ac340a8208080c02a0e001610160c820186080184100a4000e031421000380c441400140312040b8300c4080500b000380c605c0010031200070186c14140010101404080186418002006202e00030e05000500c481028061c0810030c06080805000500c48102006180c10100a000b018805e0f039bc40a07070c71029cd0500c68a73d80171043c4810162ec0181102e680c322f042982e073415c4029005c171029cd0500c70d73c05c0e27342e0a2021cd0520492081821cd248289d811821cd248289d811821cd248289d811821cd248289d81181589e68538805040f8fe005015cde20600a463f8014057378818029182e20539a0a018d80408201c2153020e0ca9d3c083842a74f020e10a9d3c083842a73c85800c8a54e790b001914a9cf2160032295085800c8886212000619179e08c0608061218000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000039beb9ad799e798d397779687954f943b934b925b914790578f678e2f8dab8c4f8b838adb8a0f891f880b8787869786138547845783d3829b8163804f7f837e937deb7cd77b9f7ad379bf79177803775b768f75e774f77407735f726f71136fdb6eeb6e1f6d776c876c276aef6a4769e768f76873681366ff665765a else 0x80039389c302388052115f0007251386047100a422be000e4e270c08e20148457c001c947e1811c402908af800392160a0280a080082405c401e000e60301186e200f00071f0c420187802100c34010806181e8380080814040640fc401e0030460700920400c52a7130c81e7e01240820a9c4c36079f80c902082a7130d81e7e032408238986c09530192040e05e221901810400c702a4810031101810400c4080630c07018bc4c00144e08178380e20381428200380e20281c30170d802100c5c495f0c0521603880c041289c30238805c0648840c271386e08148580e20301048630dc10290b01c406020902a190042018a89a16180f41080c89055051c20420c1a0188c1800200620400f0001890903c0182101789800a00c102e0011c4118145e0e038808028a01c020b8805040c0e0500c3c3028061e1810030f0c0a0187860500c3c302806183814030c120a0187c40600f000a17880c01e00142c0b0d41050405815070085080206c350414101301410504040400c20a400140310200a8001c062c0014030d050060828202833a645c083856134c9581070bd32a1089581070c49a112b0181060c4922e02a654c0830725602a781060a54a490893802560418474c1845c083853110ba645c08386e98308b81070a0ce9917020e14074225117018118184921508a980c097082a54e844ac083862a10a9e4a22e0302390895810708542492aa645c060470af3c9442c0604103f3c9442c06042a081f9e54249088b800c8e036790b000c0c8c4224d082b80c08307249148542c0153020c228442c0057020c1b0042c08304a49270015c08306210641c19680642e792b018104105401e008581060dcf2510b03800a8207e79288580c085410380c85420a91701811c8542a7e00a981060e54a1057020e14a94f0190b0045c082082a126844222e070015209380216048a08188b4fc0e002a2857020e0fa61002e180e031b8980070a4102f0701c40702850400701c4050386e20380608102002c301c0628400e0e0280c50702806181624080189860500c3848280618268205c00200630248205040810038380a03143d8008f100a0e181208a1712a780028e09a1712a780028d8002820304d0aa7c4c00146e090a1e4ae26000a392a12c1216020a1b4910092107495c4c0014702e188403138986c010840051b8986c010840051b8986c010840051b8986c01084005180a862100c444d0b0c07a084064482a828e130c1008d051c2e1a820a08081044846828e15138621507001118940804d0b8980028e1b0480a85c4c00147c00141018080a080c3609a171300051b8842c00200a28288580e20200a307a1e11e26000a306c180e048478980029109c31098380088cc1800200620401c0701881003c000a031429000500c460c001005018a1003c) else (if j<11 then 0x4179a820595c1017039bc4a78287a4d1b8208e220a80072042c0e2088102f100a080c3314637139ec010020810b038822040bc0e240b9b17028c49637040b026071018082443c4813000a2d3c11c0e6f1104051d9e08e07378902028fc4028203e071205cd8b81460430581c027f37890202924f047039bc4810147637118102100146e071105cd4b8146e071105cd4b8146e071105cd4b81460291b88c10400c602f3604031182400182046782389cd01c080a38179b020189c48110007cd8b8147e680c10185b801c01f139a890602c9e002845cde26080a384003cd0d00c51170705c002f3415c40602cac10280bc403f34060b20280a0400c03c00b42705cde2088c01f039bc44482860480b9bc405014180b2015c403f079a020882c80882b8802e685816381c1003e071205cd4482c9e0f3493c427028605124101a0b9a49e213814360b9a49e213814320b9a49e213814360b9a49e213814300b801103f37880a1f05c0087349381038fcd24e049c0a1421cd24e04142f34200ac09385e00439a49c081c6c112702c0038a0a24e0821cd276040e402821cd2493b02071c1410e69249d81038f49817348bc6c082870840881c0e6d3f020a2005c0e6d3f020a189302c0b000e2927810222f37020a1d9302606040e28442049e040b9b8103901024903810222f37020a241611e6c0b0207189302c0b000e28442007051279a02c08581657038882e6a5c0a308401c4110205c7820078200227800ae6f100a5f0781cde206014304003cd0d00c5e68638808028bc0e6f1030051781cde20600a2f139a030c01450b7138017e682c0a38501003e009213cde20600a50502dc4e682c0a37038902e6c5c0a305010038170035c4e682c30505381cde201414305381c4057362e051c1003e081f9b09e243830485a13c14160b8940029021452050509c171280052788824bd000a2f038882e6a5c0a30502dc4e682c0a30278016c173788051c280ae07378882028e1604c0b05c4600147e07378902028a0ae07378902028dc0e6f101405141202e0737880a028fc4813000a205913c4e682c0a371381c1e6e3c0407059014e07378805050c0a02f1005cdc78581640591207e23000a3027880ae682c0a37039bc40501450b71213cd0581460b42789cd0581460b02789cd05814603f3788090103016385b89cd058145e00278802e682c0a3a1421c08173682071c2102407039b8fa08288050438102a0f35120b211302a0b000e28291285e0736054103900a03f371e02a08581640400e02e6d05120b1c2007c302006287421860500c5e98400f86018bd30801f0c031421800380c40801f000310200ac30200628430c1a018810c30680620430c1a01881403824100105713001d270d53e20280780038fd30801c1c031421800380c40c61811c402908af else 0x130011141442e20204a283813c40286f00111c12420471300111a13c460e00ae08181380047101c11180b098000c0e28178900c78440e301613000f00c507014060710140560c00060719a605e24031e11038e0584821821e03c000640380a03038909e24000a25038d096089584058000c70d81613c480438223816121b8000c4a334c0b09e24021c111e12086106c0ac18000c802c2411c48006e1c11228208018786c002006261810030d05120386c1c302c06202c06080c11860802c4c3040161e1810030c1282c301c062a0b000e0380c560a5c0a0b4900c6080170c82c0408060c20218102e0b0c031b03860d00c4c08401c0b1011860b00c481618160710342b44a48162869138601833000b1e2e0801871705820062014060ce261a1d811060014561b021d08023000b1c3b860500c405815241d0400c6c36020403060b8003817898181618144020060202f130c0cc0e0014505f0cc1050200630201782c300c5c36000608058a0bc32081003140a0304061ac301416225c10030588050e83806111411860802c4416001c07018ac14b8a01692018c2808619040b0600c7086070416c300c6046182c0310100bc1618062840140bc088b05860190100502f0211c300c7080281781c10330c03200b86e243b0220c0028884e1b020808063000b200a18c302806282c0a920c0200636043b860500c505814300e8100c6058200405c3713034fc0028a0be19820a0400c602e043b860500c605e1a0408018a0bc34081003142d86e200c0b8181600144c0b008901a4816302913868100f000b1f0d800182016282b0d0202e0016305e8208c000c50b8200741c002c605d041003102f410460006282e82080189410400c16250624030589418900c1625041003c002c50100f000b10180208600162e00200b0c078005860b018203816001803100602c002c401833000b102e080182c4c003006183816160018030c0a0b01600062e1807818143b000b1f0d81848401180058e0981618200b143205c002c449040161e042d02c302c5c300c100b10200e05878601e04050ec002c760e00060b101085c35060410181016c350604101b0d818143b000b1b0d09c0840114fc002c80c618060b1124030587810702c30702c2c300c16185b0d8124c0b000b1f0d09c080a9f80058ec101e001626041c0b0c20080806080a05000380c44102c0e182810030e000a0187028001c062016000a0189004101c16230416030408820801c1620140e0b0d040ba0c00062d06000b04080b80504100315040ba0c0006282e01410400c564d06000b040ac98050416081683000182c48140014031205000b00c40400c03c1e0737881c05121000f343403178014e6f1014051856c9e201c10281c11c167f0389cd8104416502182c0e073788c90510070452783c0e2)) else (if j<14 then (if j<13 then 0x861180b000c018a0ac360411c401e002c40281186a08402c30281186a08585c300f0208e26002c38600b860380c504618061610300e0b00c41181700030b0a05c360411c4c00587c36041408e26002c38170c1601880a0182030540a00030b0b028000c0e230414030408828002806220a000a01884961604182124c5810608d324b0b020c1702c2c02648a2b3f008ec09285c06051c151018cf0ab268445c054f024e03028e0a898047604942327024ac005452492b020c109242c012b020c189380a9d0b020c18924ac0830421604181b088b8106084922e0418230b01812288150652584d3c053f024309a7810608d36160302451702c24c83040a915844ac0c3862560302451301812e92842e50aa60ec09146c0604b045119e4264e0700151b004ac0a384a9b3c9415061148580c09353c06051c15148580c09682a2e048580250545649081980c092862132703800a8a15a983094c9a16019f81249415a9e051c2b24b8cfc060494333f0142c083059250a320c130003a14641829248542c083052490b0015c083062490b0142c0830621604181d241981c00545c010b020c109342c08304a1057020c10b80c2290b020e189381216021c190a8e450633f0181a10c08c06051c1514184a649170181a10f42c0a3832150b0181228a49211630181228d81070543a10541d81228a42c0604b04516934fc0e002a2974b04a2290b020e1f0242a4d3f00190a8f8107054302b070c03038bc44702c102224071203898660b083d0e018c0a0400c34481789860b80f00072034034904440de180780e223822385d12080f4483630230d8002f121c111c3a050700c0e2874069208881ec371300050704470dc270dc4c00161c112389802507418280e24110c0b1208870960b083d800280c70d81613c4c004460e7100a0811138601627000b1aa60544f10049201e000e48280a92088205056000f8f608206a9e180780e2238223e3c1586c08238980089008c360485c4c0044701b04101112a60544f13001118941c028238980088e57c07100a08171e0b0190b0141038a4104a240541c00780e20019089e2022828e058d8f0590b0007208207c350a821e4700c62bd041408018a89a1022821ec000c744f128242c015c1038381610230c42c0017890e08900707014060c14520584a4822081811c4c36000a0e088e0a0283806161415c4c310b001b07044807027898008830601b04101110360e049080a08e260022483213c4c36000b0e08900e0461b0203e2600224225021b02823898003900ee20204a206d1c89e261b0005060449e261807800da382238230d8102f1300111c06420da483c281513c40de002230781186c0817898008908ec350420111414424761a8211191c890561a82111820424761a8211191386085051c111b880504060802f else 0x10b2580038c03608200e20170c030388050181c30c0501586c0f130005039242c300c0e26188581e26000e302b0c42c0f13000503918601e078805c001c702e180e03103010c33040e282524070c0e0ae26180642c0e000b922b89860602c11812a600205cc9161801a480e21500fc4c300c0b81c054f24502004074902c5040092407139fc4c36070192040fc4c36070192040dcfe261b025401e03240827898601e0700cfc902084903016181c1405e26181842c0e001603c919c4c306c180bc0e0042102a648b042480e03101405e261b020701e0019922b8986c0e000a08018fc4c36040780c90207e261b0380c90206e261b0380c902060382b89860182c8581c001724582b8986018301780c08869e54c9181802a480e21538986216030392019054a7f130c03c0e03240824a807057130c030590b038002e48ce261b0203c064810382b8986c081c0b80a7e48902f130d81c064806386183860380c5e22381608111312038786a1600210e018c89e26180617c001c7e2618af80870306047130d53c00421c0c2005800701c060c1b8986c054c1c0c1b8986216021c0c181c0303860ac315f01c402c387044240bc4c354f001087030a0c0141c03038a0a84e1885c4c00161c461b8980a98380a361b00108700c1832270c02c4e0016354d13c401248078003900a03e018208141586e0e382207047108580280fc4c3044100bc0108844a482180e2508183e278805c015c1037130c42c015c1832278986216011c050610890280a8380038800642278808a0a381637130c422be021c0c1c11c4c310b0010870308016001c07018306e26188580070306c360701c4210306e261b010e060a0c0283b0c420881f88080580f00622406810471300071f8986c0648840c18180508f130c080382f0042281805e261822070402f00422b0d80215051c101821860881d1d80215048c36008541470406c3600854147040644e1b0042a0a382038430c1103a3b0042a09186c001c8541470c0b056188242c07100b0e24110902f130c42c00421c0c2830050701c062c270c4104603884202c3890582b0c42e26001c05230c08e26008405070e0b054270dc4c00161c44270d8008109830e1e13000181c402c000e03060bc4834244f00038c898001c060c140b000380c402c0006071014c180308060c19a7c4834244f00038e05e20400f00060d0902b040f00018c898001c060c1411c4834242100038e058001c0624480e102810030c13860380c4056001c07018a05c36002c03140b860b00c40500c101e002c030f000e0380c4116180616130c030b0780018583046182c03130c160187860b00c3a0c5c1003122f410502006285e820a018205c3030161f0410070c1586c080c11c4c00588056180e03100b0240830162e1b0102018305c360411c4c005) else (if j<15 then 0x38a896300c04c04702c70af3513020882c644c08180b102bcd810281607181c41a0030162c268c8201d0016351905400803016300ca40b0e8c82058304a320a1d40058a0e058546070301623180e030c4c09e2044182d3f9bc4410440e373789820b01c5e690704c004710144e219fcd0571204d2038fcde220aa41a038dcd248178816038dcd02f110552038dcd02f100607088dcde20282c071414170382040ab3f9b020882c667f3415c4810580e38579b020b02c5e6f100a16038bcde20143c07158cc981300162f349282e36040e373493c6c081c5e692505c6c081c6081258d81038acfe68282302c081c7e6f1b0207139a49c08580e2f3505c6c081c5e682a8c820d6040e3f3505c6c081c524b1b0207139b49410280f81088fcd0c1141581038ccfe6c08220b159fcd08c0b02071b9b020b02c4e6b1a040ac081c6e6b2605810881c6634080ec0058bcd24c08220b1421cd24c094807058e49e004205cdc081c708f349207058ac0087370207158d496002c40290388180402c6e690430056300c60af340a230581c60d0579a0b0281c223f37881d0281c2c37100e05a004450d0579a0a0581c6e6f101407139bc40163d8cc1038e15e68091211058c15e6e3c220b142bcd8482c0a07088fcd03a27880a088c056300b1ec0058c15e6c0814050b02c78122788116001c60af36040a0581c601424180b1389090602c4848301618579b090381416111c1c0b082bcd02c0a1216058e15e6c0a1216058c800cc24160c142bcd0282c0e28579a058102c0e30579a050143a120b1f9a8581058162f350a070589cd0c5040e11168c100586d3c301c0620430c030388034901c3e200f00071007800386d3e200f0007178810c001c4c300c0e183806070f0c1a018610c30280627100780038841c300c0e27130c03c96000e37130c42c002818071f000701878601e078980038c920384030701c3c301c0618141c0303880e0380c3211070c03038bc4c364b00071410034901c40e8170c03038a050181c30e61b021402f130007200b860380c421618060710380ac310b03c4c001c8c02480608130d8021030062b3f0d41a100c1830200ac1a082b0142018309a0e000607119e05c301c06281683860181c5042480e1d4f8803c001c5e261b2580038bc4c31082f80038d89e20170057040dc4c301407800601c7e20430007138986c02241805038e020703016202411c4c02040e0c1c83860181c4e26180642c96000e3e0010030389c4c310b000c038d800380c3e26188580050300e3f130c03c00300e302c18161806070f8986c96000e2f130d80050300e300f89800389c4c31082f80038c0ac310b03c4c001c767a270d41c001c6c310a8380038b86a08280e22270d41c001c50c02b0d41038b86215070007170d410801c4211070c03038bc4c3 else 0xb984c360700070400c80ec240b808700c103c240b808700c1030461386870143c031c1405621080f8f0580c104846130e0280c10333c140bc360423020391170561a020b0400c7c0e02040c0880c60c6041c0503828603b3c118105e1a043f1006c1e6888ae373482c6210300634240b46e2501820c0391c4038203a7f378882633040e08059215e6a08220b142bcd0882c402901be49040a82a009f9ac1038c086310581c40513870b81c1018559fcd8104416371010070c2acfe6844162b3f9bc4810440e305c10070c2acfe68298d020581c8e6f1104c66081c100b202bcd414089216058e15e6a082c0b142bcda3208220b182bcd0b02c40af3415464102c0e3e4f9a4902f10060e0391cde253c2c07179a0ae220a8c17038e822901c102518068281326800b1e8c07a002c4a32080f40058b4603d0016251b88820bd000e3519050264d0016330042170608c6e24098117060d4f0400d01c460f340a972406c14070389cd02a5c880c0b9a050600c6e6c060546018a89410301622258c034103016303016122613414140a800c0590640c82c18203016109b8889038141830b4160c0c180b0821cd20e098c03060e648482c18220a120b06090941030162008180b0c4c0884f108207060e26e22080a2a0601c705830284c08180b101003e6f100e282b9a05e21480e34240b0232060180b1f9a05e20601407088e05e6f12040a038c15e6a258211058c0560809800c058dcd03a2788c101238164009120c058815e681c340b1612020602c40af34040a0581c60af3404890b02c64483016189b88050601c5e6f101405))))
def mo511H11 (j : Nat) : Nat := (if j<1 then 0x521b0861046208607992fa72a316c30056f6c3b2a6801362896969b503a802a1c9460f5b68294012955321b7435bc4900796088f3b084444b8000354bb034b21bd1e7d03fd6ed1382558899c944f07a109409949bae0ad54fab74506eaddbf4b7d1a09b539d8d951d878212e28381dc00058fb00000003c86000024dc80af532a0831d05a90d0b87cbb5bbda39cf1ea4c3d9ecc99f07c8d8bb09da8410b5c609335f9282333cd455386c9b5b52ea36348be3bcd066a4614c054be8910d022bcae6288d5757600009ab392d891d2560d97cd3afe4f44ae43778e51c71ba77859b8f9361ae1b3651eb570a9258f685e611779c8133f3a2ad4ef1ad731f272644876d7d07389e854e71896ac8854715b5d70b4c58448000022b688a000000051b8b077633b116193f738ac3d3b317af694bf689a358a87248488c25c9e089a2e0464280001b13cbde88a84ad1e6a72ffda46075912e0000000151080a7c3e000000005065a58fb89fc342aecc1a60000000000042a62ba00000000000161e4000469454f7ea8e049ceefeb8940b5d204c36bca14032c1fca707aa6f70fd7da2b8903f468796ee91185994c89135a8e87642034389060f0c2f54296d6a51b100ccf1ff0fdc90631d8cbe6859fec52502871127fb04310faa0c00005b209d98c61fa877ae28d3d48e4d2f041e1c176bcdc4b80009a48a5540007a1d22da00000000000d3c6000000071908c300002cffd4916a0f265ec568000041800a6810014400040000280000408000000020004018960008604281800000000041c00008240060001000081008100001851a2408f004428004000890c242970000284045c58402b408212001880204e91024c0830608b030604103000458106081040434690a20819700001012a001800232000081010004144001e0400a0a38004061c900040001202040820020000180020d00341800001188000020d0c1000b003c0001038392020c0000014a0800080020000a805a00680000818e0e0c18504000010000001000c000000438606080152400200001c0810008087000800304042003c045b45400042141410102000c50402381041820006840172a302021404902000410708781800e1408b060010006103810014181a604000060df007e04000182c00102003805800883c600200000c02f02f20800600001281000014141800068280020c180000000100000010814781060c080002008040202041800080044c78004081800601103000928900144801488038001c01f0c2018010480861e381000014000185c0033060082200090304b000a040001c02040001000001020078108040014800400002c000000001c14806180014680001a0870200b801004480004c00000000030800081027c01c0a1050404143003e10001021000a04143804a18081 else (if j<2 then 0xbf1d31027984e980c694084f8d6e2a87a8e03b0563f3c289d963b40e9088868b6665515c94a36a914414c6b9287b9e341578d4416cd448eaa367d4a22664d13ef88161ea42d30236e8cdd41a2b9cb7116c35ccd7070693acb444107a40a1416992aee0400000a6f02ca6a88b4308aa3260a73ded031a750658a084e3a2c3401ba7d9ef373146846c04607b7c27747b58ed019800000000001d59a0cf111e7602d78f426a17be290d8f71d55c0647b6811ce580000a40c00012427be54a64971e0e5c0f4000000000000001639859188dc85a160df714fae196358ab40930a41a42693f0f7c12e5661b4333f2e2928b33ba7f398c4914b02d790e62d402432487b1c08730f33cb621fe883f8e1a4f2c746cc65eda02ce52ca6f578bae518eb7b0ccb81e73b2c3a946f601a1ba5f8e604ef9f9944aa152c6c16a18deee793c6228c7e5ce8c4828f8031f62eb4996916adb4352341983248cb8e11cb544549214b0857ac392c9ee4c37d40bf09b6303583ffa16a1420b8b623eb2269faa2732a4895548c7484236ed88e134f0e0745270ea0dd928f71c9e30747c72564509992f2768eb935f4c0a7657557511088136ea3be0202c853d2175f2b2d3b1b8649774af2c5768b15d5bf009031a4a9994729d2857820d4155e1ae2c98f05511e0263550fa2880858e4600d5c262a5534fe5b4a000217f5935e23e006c4f635cd64eed49d930ca1ef31600029480aed0852617515402f5c5b5b48ca9721b36802000114880000000000000038b7cd06000050cfebae3ce00036d1546a3c7800000005aaf000000000004509000000008a4363e24f800000000d41000000000002df04526000289d000000019882009ec0fccf3e01800030472d9e7be416176716322a4b64bdd67f10e2a25ac94842232bce2d6495cd438431a56e32f4e7e238065ccc500027bcd14821851a2b4019a0002400e65df5a5282fd3350f1e0c3f7396e7e01d22be8a6c00005c6e2fc65dfc7f00001383053d48b00002d3f52878be01837178213352d00000000000207d119c00a26412003c2c90000795b2f7616833bc94ac74938afd8bfe00e46db1f8000169b14d176eb10b39b99d0725c8e98a67dd0e61adcf1fb688be9a52a560f6d6248de494cd32b6228efc480bd3368518e6a6efa000144e729e0f1bf2ea445e46410bfc33d0bf244cc0ac826822354ee223ec5d4abf6448d4f50bf62503c42c9d4b5eff9dd83aa24a3a59e308b1c28690a6f01f148e1203bc9aa567d29564895284257b28a950209582c1e98931d830c4a23aff1aaed56ba6fff366a33e30ac27f8d9392a0136c05511c19a3711c000134262d733b4812629afe49a4b12a6190b2102f5a247434f58c1418d8e4bdc8f431c0a757a0166e7a80ed4934a453981f1f5a7a9fbc33f83843cc8014b8c994ed52aa48fcf else 0x20efba720ad9740e007fa9680bd94d8d0fd24cf60a1120125a202892127f496ff6ff00000c28a80c8894b0e29fe03a283a0000bbb8000000028e4852dd5d10f2951769200003af0e059d90bc1b00ee0001c58c000210fac7f8943e4ce4fb32c0527c8e146cb243685d081000becd44b5134bc7886837314a1880f9a4b34122312fcd818b44847d4825caa073aca32b2a50982f1518977ce981cd21fe767d8cb308b110f4064d054a3f63e6f5a18fa5abde42b7a0743f293e7cebc8340004131fba0000116566d5d3c4bbed129a9ce758c000204939a80000488e1451f050d5b816007b8a860b42960c124baffc4636141735a998143551cfe2f424e057d84b3061b459f0f0f7b5d53da09e2e24c6616cfe69434de1717448b1bc05c816976e318035559a9bd004a326029a5cb0be944bc2d5ca85024015872c28188626585fbe1a246b07108d5bb99a4140000000000007e8000000024d1d49435780000000550a4f71af48004c2e4c31a145a1282072523e6aab14c28a180ba915000021540000000146ba2780006c750000c6f7ea940da0a71d1b50c090c634e38107e62392153baec931881510753db2e7871a1fe7165a1c3e7cb94a445f2102b88b96f736d293468f298eb0088b9309ba3074a91ec5818f8000042ea200864b93859ba87bc01f59c6a906658af620de291da4afc893c306a3b6484556092640506594ad603a540000000000000000000b7f000035bde1a36ba4000269df40b246589d8000827a6ab0000530b0bea0440cd661e8ea542bbf412967a4211693dc4432b9e41e000000045dc0000000000000000001a44e32980000000d42d56c3ac4000000000000000c050a6d00000000d0de852400066e9208aac32029dd32f9e600000000cadb3280003010e9e092bb8ac548da625962b8c0600462ce15c1472cc39984fb1572b34238264755ad803be87905b75f06c0973e26c63a67d0586a30b0eb4e8479472700b1f33400016ffa44a546f61b0000729f580a00001806c7cc176e28453559d7040314f44800000ac6e71e910300000000035c0004e7250afa91293c0e0c5477aa3471afcb08608e497cbb16082bd368ea47e72cf001586ad0a6d8df85))
def mo511D12 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xc8001f647ae1e2c7641d247221c0c6e41b146a61a3c678197463e187c5fc17745be167c578155453a146c50013944ce12cc49c1204472114c438107440a0fdc3e40f343a60e0c3600d0431a0c0c2e40b0429e09fc25c08f421a07cc1d006c418a05ac14404a411203cc0d803040a6021c068012402e004c0007ff65d82ffecb305ffd9560bffb0ac17ff64582ffe48b05ffd9060bffb30a97ff64552ffec82a5ffd97607ffb2cc0fff25981ffec3303ffd95607ffb0ac0fff64981ffec1303ffd52607ffb20c0fff61881ffec1103ffd98587ff930b0fff64961ffec12c3ffd52587ffb02b0fff64161ffec32a3ffc86547ffb04a8fff58951ffecc243ffc98487ffb2e90fff65921ffec3243ffd95487ffb0a90fff59521ffec0a43ffd61487ffb2090fff65d80ffec3b01ffd96603ff92cc07ff61980ffe43301ffd95603ffb0ac07ff59580ffec9301ffd82603ffac4c07ff54980ffec8b01ffc91603ffb02c07ff20580ffeb0b01ffc61603ffaa2c07ff48580ffec12e1ffd525c3ffb02b87ff20570ffeb0ae1ffc615c3ffaa2b87ff48570ffecc2c1ffd97583ffb0eb07ff61960ffecaac1ffd85583ffacab07ff60960ffea92c1ffd91583ffb02b07ff20560ffeb8ac1ffd61583ffaa2b07ff48560ffecc2a1ffd97543ffb0ea87ff65950ffec32a1ffc86543ffb24a87ff60950ffeb92a1ffd62543ffb22a87ff60550ffeb8aa1ffd61543ffa42a87ff66120ffecba41ffd87483ffb0c907ff65520ffec2a41ffd75483ffaca907ff64520ffec0a41ffc81483ffae2907ff58520ffea8a41ffd98443ff930887ff65d10ffec3a21ffd96443ff92c887ff61910ffe43221ffd76443ffb2a887ff61510ffebaa21ffd65443ffb24887ff60910ffeb9221ffd62443ffaa4887ff60510ffeb8a21ffd61443ffa42885ff66152bfe4c2a5fed8254bef92ac0eff61581bfecb9037fd96206ffb2440dff64081bfecc2c37fc98587feb02b0dff66061bfec80c37fd98547efb0aa8ffd60551feec3263fdc864c7fbb0a98ff760931feeb1263fdd524c7fbb0298ff758531bfecc2437fc98486ffb2c90dff65521fdeb2243fed82487fdaa490ffd60521ffab0a43fdd314877fb0ec06ff61980fee98b017fd985c2ffb30b05ff26160fee98ac1ff980582ffb30a85ff26150bfecb2a1f7d65543fba62a87fe60150feec3261fdc864c3fbb0a987f759530feec1261fdd624c3fbaa4987f760530fee40a61fdd614c3fb8c2987f754530fee90a617fd98482ff930905ff65d20bfecb2417fd95483fdae4907fb58920ff6a9241fdd31483fda42907fe60120ffcb02417fd98442ff930885ff65d10bfecb2217fd95443fbb26885ff64910ffab8a21ff561443fba62887fe60110ffcb8221ff950442bfb2e40dbf65881bbeca9037ed92206ff32040fe759131 else 0x814301920a1103009f8804070c16544c160e00566e20290138204490580299b883850a04e0e00566e24982939f8380159b880438d67e0e00566e2011028019f8883819a2e467800a04e0626681028b9493809f88059a0a2e4040480e6e20101a0101205838113059b88460920481600502c166e20a1613820581139b883e0e066e204810c108c03828188041c40d04e781606205668b92359f8380159b8804467e0e00566e2010e9f8093059b023206008668540a48e34939f80159a050246027a4c166c08d8021059b0292360278524e681408f9e9380159a05023e024e681408b1f12058381059b880a4e08112600547e6e20c0a142982139b040b881c40a47c4e0620166828b93820b0588128030a04e081604166e202938012319b880a0438160e047e6e2028e0583800b9b881238c47e044e681208e83001006242c369e240018b011284210c82340c004810401890e2e130da789000638a0480e0c062050711130c2085011c82384830769e200018e2e130d8815000638500e08140046202919228922f0d8815000644301620540018d011220050c821038362498500018c9e85a693010232a4069c0870a92a79e850102329a4a140408a849fa6930102369c08706b8a69e928501023a9a4e7a140408ca9039e850032324a14040884884321c267c040a1089e928501022c78b84c36982e2400192281203830188141c40a44a0c00104028911a70d000b83881c38a448bc302e2054001928300100a242e98482c060e2070e130d8284a7880b00444c00847a143472090130d8285880b003870002e9e2478301900b1fa60183881c3e08104c06241430190140382040b890028104900a20c004c101891028550189050c0638a608404c062014301939f0104830c061038a24e0c002e241430192330082100624343016240018b011220050c821038001624103018c008210062428062040301018c299f8188059a2e38a67e06201668b8e299f8188059a2e38a606201668b8c299f88059a2e324c140a009f647d15f267bfdedc7af5e9679ede607915e1a779ddc47645d6e752dd1873b5cca726dc747145c1e6f8dbb86e25b626ccdb0c6b85aba6a3da686905a1a67ed9d866d599a658d93064158de62fd8a46205862610d8105fd57de5edd7885da573e5c9d6f05b556aa59fd65458a561257ad5bc564556254dd51453d54d652dd49051b5452509d4004f853ae4e2d3644cf53224bcd2c44a6527a493d22c487520a47cd1e446b5196461d15044f511e443d0e8433509e419d04840b4ffe3f7cfc43e24f463c4cef83b04ea239bce403844df6374cdbc3694d8e35dcd4c34b4d16341ccd432e4c9231dcc4c30d4c1a2facbb82e74b762d2cb282bf4ad62adca9429c4a46288ca0027749ae263c974254492a241c8e823348ae222c8702154836205) else (if j<3 then 0x60e002e6e2048103920e141383811388239a04165c4e0a341066201a00592100b829f80239b880f0450420c12066a4e2270512100a93829f819b880f0450401e083e066e224c1122c05830581899a160a484a081206066e20c02939b89058c82100a38b60c160626685829013822d81059b880a4016066e20c028c30351f138380140b88059a0e1668e8c0502e0e066e204810f0398151383800f899b1e041650382e0e0626681048593888d048016a40a3a083a10904018c8301128410060e2440869a7a103c3018e21a70c820f00063a7a1416082c36984e203c00198210c83003406308052143018b12070c8582a789000e48a29a160c30ee2038540019621a69e840f0c063a4e0c3214127e201c0039421040e1c0628a29a4a160c30e27e20501c0039a0e20a6850c06367a0e0864304624001a114a712070c85821589000e544a0e0c302846240062114182982930c85880f000654320c021018a07130d8211880f008448a27a160c30c02e201c003960b890c850301a69e072452e02e24340c001a9a7a1491614a607890d03019e852452a624367c0c0490411890d0300068524382e20740c004018f890d039f012410382e24340c001a7a1491218210c8501a61c06420c0090413818c281d128285011c061024569c3210660c002e2071220a70d00841c0638d074481854360a129e24047190d83008418a7881c40643214069e082e20712130d8300a60a85881c48843402107018ca61d12070c15828589011c5c481a0c3608402e2400621161d1284ae83011c1006245436086402162070e1512070d82111d890084504c360c002a16207110c14061850904018847002406102c3050186469e938305270c0a11882d00066a0c00705018b0c14061940d91c1154305028401e2400b1a462410062084982c10b07018f0c10061c36091c48b0462400512830024062e103118560a4c30b624001040196304782149f0c060a041189002c6884308a10287018e8210240a520630a0744a0c0472147840289164b0d0023881c0a38843210287018c34371206850c141d82a71f890022712ab8502c4a0c021070f29c784018d892018140a13830d0084a788221c60843210287018c3ca7120700841d82151f890c226e24320c02110028e1c0b13008440831d1e06102460d860284e0c04321620887161512071f01821188230c8458588014143018c0a8300050d882010410208904018a830024061028805c143018a83010c10062a7e78440c002e24143019420830300341c063a0c00904018b0c100618d44c0e7c00185046201430598830024062e10340c00e84620543010192200a17050c063140440c002a7e24143019454822410062828840c107018c92390300109f88150c04065c0a4c4856fc06784620143059883002406321030440a4c06205 else 0x620466a10da0a90291839a442d898c0a38560e6a16263028f12858380a79b1f880e4a98b60e6a1626302901083819b8884443e9a304e2210da02902939b83898c140a3056066e20c028c8d888014a40a367e00524e20166842083940e9e058305801493899a2216601a0a06066e2248511269e0493830580140b9b880e60160088d03e6e20511802234040f9b8814403810524e0c16027e2668b05992693058380159a9f880e5248e60e066a7e205101604068c9304158388800e58427c0c06066e241029303018189059b2e0a40884810b44e0e04166e20605991283048183801412040b9b88181670b0382e0c1606266848594500f83800b059a1388361858e))
def mo511H12 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xf2000000000000c44b714ab453e8ab6263341f901b040953059431e1021c1ef3c29a62244ac3eee0faec6ba94df421313bd1b8d4797187e0e3005291175bca00000000f2eccafbfb99a9326400e1ca231a3497040272a119221417cb88530b104fec29eb61d1cff40b7381ac0441c75c4a384de41cc42b39fbb1b572285b89a0a7d454795441fdf92d242af2dd03e9a1e1dc73d9d300c6b2ccaa2b2b09e217a81beb7793cd81338057ba22c22792f5f958523362e101114470941b2b4371e3502b4ae41a958925334dc46ddbbd0355547d70b4d8af4132fc36e10f442d988c8b78e3694895eb0279539046e0724c1fe07ff8584065547f9a12f123a0aec4506374d34f323c4a5d63d82c8299f76167e26b11ff39ce2165131d012ed3762aced82109afb2bbb935f2d76a0d50399aa211fe31dd90ecc94f9208d923c2af69c4811ef0a132728359c255b3b9500b5247f433737b88b771e269c7ac77e0903159638cd40372b403ba1a9151b7ea9d13b74a6e40c499fd62611214cc4d7b2400a571ed51d40423321680a0d32ac32648d4db79ec76e85c50988abf801df46912f6929d9a8200cd481af826bb60a3ea8279840d3419c490842612aefa99a28fc40e02000205100900070008560000073534060608020114330205400049180108595b122001150010190100040311090b091d160400000402060000000100170c0e100203046b0231023f021b190500000216a9090000030400070e00211d010105030007021b1d020007001f12021c130c00010000020405015a17061825000200675a6b040a000c0906040002150207040300170004010405020201011607090005020e0001040b1b1000070105090b00010000970701060e000601031623120202200e00420707681002010e510f132c0107010141030b06026e000202002925010a00570003050d28000024151b00010716282f03020301270003004905040920200b01000b000f810052900003030c12011d093d083b320c0a4503060108181f00000101056e090f0e0011170001020509022709040100080000070000050600000000035705000100021d0e000104041609050203700605720016000b001412050e030b0c05000710133a3a00003304150e211a00060401030210011532060214005a3e09150d0e1600041a031b070402020805000525041000000007012d0800010400082903080200040002430618036b0030064e750a000806050b030116031600080d080901220405020004010101330d190102000ab41613150f1406200062150b0a02250f0c0d2802180e022639000004093c02337c0c020209010800030d01010100000236030c06230d048902090612021c020005020315001400060100030c011006020607090002003002040915020302020f000004070a000602 else 0xec1f7f26299d433be00004b08000074465bacdad71abe7bec0000837d414230510000b0e6284253f671e0021ab3b141f4031e12c9942c80c533db0a9c62b84408e9aba0e0aa96f20083d2ba2a542fd2750000536ff299000043f37c24c07c4075089911f523044a8fd43c0a3cac1c848e528d690109d540ab449163b6fc3a91c20c20221b32a7b2aa4aa581180b4ac351435002ffd1c4a2eb0000e92b00005c25f3a22a0493644ae9c1ea8a48229a38cfc11be49900000000601500003909cc7a2308aac0116b2a4333cb90671ab122bc0000a38542df0000f0878122735800004c8b8a4dfa9a394480fdb96223bff1cdf3ed207ac98dc855d2f781d9638db22488971afa519d349500007215e3031106408400004bb2044f7268807e4390989800000a9b1048c04da1c5000083e2523efba630af70f93bc3430d02b032f8102002497a1a0000539f4277e949b10033416b22425eb10da3a1e9fe3bbeb9dd3354b39d743851bd00008c83449658295a39000011a12324f14d490303f4ebef647138d82b6c92321070abc9a13659f3b0005912c1cec271d237539b73d001d6b2fdf19e726600004230e0b5022cbabdd8b8f99f5af35bb02ac138b982b33148c0c719ec527c9009a26e40d6e99c000034440000204e181573280000000083a9c43989e800000000d9c600001312000034742412901810ccf2828ac52049b3e8143f817cc0109a53815f428449e0219ae1d293f1a1526a55b415336540e90000000063cfa0941c30d12722d6000042e743c91810c1cc0000014529630000000061e700002aa982d31b62e0cf0000b13e13d7094e72cf12f9d11c000040bd0000000000000000202ff8d718faab072b0500f76a875b4d425d93ff028ec8bf633d43ab52481004020a6095625fc03de30ea8ad234400009a57d859f04b420fcb96fb478a71a493fb12ec8a5c4383b342ee63c580bfc4776b8cf09be3af68bb0311bbf44c3182c3000000d22ac4a46810e1006802a5b092a12f71990000d4554270205960b7d15c43a8901400aa59dc0000095af43ee1c092daf09da318000071fc80c2e2bfc2396464615069863bc1e44d5031b06aa2a0b1e6a0a60b6ba0ff8c93524f00002029717beb468816db1099506a3462e5e420a2de22d9e25b0b6a29fc70250194736734422ac6541844322138f03fb85be2422960ab660000044ec33a83a3f0fc518e0000c30c70d4fb95b04a816f8b854346802ef1914a4969ff41c322f4d267a9c1b9ba7a47346790da0000dab8c3b412ea90b3faeec129aa59813f219563df834a00006a516396da588269987a002323c3a9d2a0a40abaf13958d66ab2525813c4910eb173410561cb2a33b4872c413295b2360000641000000000000073c000000000e3e023713bc239eefa8d801a408249c57a75000021b30000b9) else (if j<3 then 0x640481a36143835161e0079254d927c380e38be0eea155c36ce0adb8ed2a1fe37759d76405c0c35158e352b334a17ee131e44879a5220c5110dabc4b8a117583368ac2b04451f15177b89a20b0c891d114da26740cf3339166b170bb14029051f090fb0b0b49f5abaee4565843222908f8509ae9d6622f706388c331d800d9a172132963b21c7cc3fc73ae6283f48bc2db840a31d7012c8186aab38a402153f89084498293038933fe49d9410ad8baf43d083bb0d162e8c321a2fca29eb441735a6286a27f5436c028d00d6a7b42c640d553f99327510cc8080036501fe28c3bd1f22eca89f07df125a2c1d3fbba8612d89427a4838820d2d5a193440612f303c80000e0d851e90000f48f23780000f33e00007a3000005b87000000f132fb73b8cb71948de1ad0298501731d15a9fba9e5297dbd3302793e5891eb210528a3c2b625ce29f6a8862217b3bd0df1b64d9ed72051388a0d0f348f2be628b80bed38fb3dcc353fc6a703200004c0d7bc600006bc50000a27b214100000906f46c79db434b1021000010690c2300005a0b9a16000000000000601349efbb13ba3adc21432e6bf3f95d00006429a4945325d4250000b2ce000000000000312d208b0231000074370000d07900004889e4012a3d8ac70000c4434a7e00000000133c942e0000716db4169c6cbb540b76994a223db391a91b81bc8349847c30a383bbd3b552add1c1946f144012d11b70c09cbaaadaf0f2cae1b60bc0e2e0d32d00000000513c00000000000000000000f2180000f46ac428098fa37203ca90b90000a19000001241e86e7bd800006abb22020000000090600000dbebf1aa540f000000000000000003aa000092acb1980000c366000051a97a7201dc9b340000000091968aff5a5a79f4d2d0a8f900000000395b024bf1e52128a3fd200fd085c130639380edbac9708a422660780000ab82506fa9e520a2d95783e12a290281c94c52abb1fa6399d34ec28510b8f038fc6f114bfa06d2f0d055e4634c4483d3f209009f9c62502d3bccac6e12b9608000997112000000000c32221eec420000036d83d9e26000000000e8063413c0a8c3ecd1356a7611b46c567043903091c919c8822a409133700000d15bf0b65c84bbb67b030000230aa3456398209e7363c3bd3964a488d17a804c201cb38e9011824eb48520f3380923d6f1f682fe7c57c2929462000032a4d98b402670f0f460e108a473f435d459317192a3283a6916a1043999741e943bd430ac9af2e4a287e9b362b5d9e602598157aa9231d000006211c109ba5613380000541d28d30bc4d85ea05051e428e0e9e293a543c60000f45cd2e2f0ce000009bcb3c700000000a18c638a4a180162b3f5e47b721d80f8f06b2b2a00004379f126dba0c1f852b2d3c1c8b07907c05c0000000023d55bbfb183cb else (if j<4 then 0x660144e45aa8d06a94f07b59596a4efb942c4c423a619ba300ec3d28be6386aa54e0dda0dc7c55c197b1474ac81a6923de6894584e28ca6c3c6243a3da7b6e6178416a8ac3a47e3a4438a99a5073f8f475035b1bed6466a16863227313cc3e9be7929b5bcfd465437e32c0605a0000a03a5174b3d4e952321f0340347ab047f35c03eb000000000000000069512b7500005480fb9781afb2b158d23184cba3fa8c4006d373c3a6934331ba000060122ba9d071211f394b817f6b698af2e9b9809313a73a37e045b08623a46ab9e0b261a0d9804b55a8d540cb38bc22520204419fdbb972732811f07793ef7b41d2ba508fe201933730baa9c090764a1ce1a71ba84024022b0000e0e7f064218b4c02908db24400008124743ac82fa1a3327ec26c0000a22d08c5a1601bb31acae0ebcaf12003e1850000c919c042226aa2e67317127a114ef9377a35b008c3e4a330a36a592862d4d3ad02e330e42b068434a0f4bbb4d0a90000d20640db0000abde000051db0000011ae3d100003ab6e38431fb128042d20000616422567a774323000080c1e33243fad2f27b6799f03149000081b982eda39c139eb482d16371a6d08c00003245c310ac6d0c85c0747b1bb27dc2889c228a9871a588b67a1dd3f7a096225a0000d2a8f15d00deb2a64061f854102c39f6a21900004b73f8240000c2f1ca00fc477115000093cc53cea13ad314307311ab2bcd98c118c02c6431760000644791ee48570121a26500002a81c10b2c59b089388b916efa933294592f0000212b82519c48cb5f335d03bc530f82910000000031ac3119e83e1382d31500005240fa2f8c7171a200003478cbb10000a33b0000e107445f884f0c7022c7c8cb318feb8d648a44047c8ec189d182705821400033e395e0cac38758d13be930167113603c4b18d13dfaeff990c489823583395b6da37a21887257220e04520000e31f79b5b34718c4000069b0d9b4000042fa4b9842250000635682c20000118d000041b200000000d2b7f06df46e71be7934532041b021c8841ad03560fe24578134805d3b01b08ef3e640f611209368049ad80a231bd1f9e8ae50ea023fb097d0f551017987cba112468081480f31df803ef39732c599bd00008a3f1424a31c72745c34d169215a10ef4234a16cf040d15ef24cd36b0946319cca74ba5c9c45614f239ab21c5b7298121a32437c4005224a3a52c2763054a9c2eb00d26f048433f260378bbc09c9b36053420a4c334c5c86d40741aeb44cc2a2720d190801b1330981bb7a3b21da10bcb05fe156d2dc40533c2a9002642271430bdc01c619f1406e511681ef71f2f335622371e880c9d03bcb042b8fd192aaeda9beb06619bb635e33012b48a28950625414aa4f9034020ba23b61d583e352539c49011d2945d36ea056e083414cc17d9357e41102 else 0x8331008858ccb2efd302c2bdd0e8100ce278e1039458606ce22060bbfbdac87982cb01ebd45ee88f624dc0d72a5b81a864510bd71492b212248c61de73944c4b0000c0e5a86740e2d4727238499142c4b45b4c5e1375b1ec000000000000805bdbee43f0a80761f300000000515490d39a973813500e70b1e3e7a3a0000098bd789223acd213046b0000000010c800000000d4980ab5e02ab461c3b01b19a022a0c099fa49430000e0f2d2b63bf22307532c0000000042c8d392da73215100000000dc2e2b9f636230017179e2a991d3d01981a4112a588d732f545d1486e9da2872000072e90000d319e9050000000040ac61bfd29c292af222a4767c2c000038c2b14659cab250226d133f3b26ba27d8560000c32b800af20321810000299400000000cc1d789300000000435ff2070000d0410180b9b8095652cd0000c9c3d8380000dbf043ddb8df7316db687445383d437febe5cc3b4137518a305e1296a01e3965c30699)))
def mo511D13 (j : Nat) : Nat := 0xa9df1f184cd88409bf189821f3621c24989bf3e3029b108280405f9f1a6c4044df8c2414d88301017e34d88241117e34f9b1010c26fc61e0a6c41c482017e9cf881888818080a73c90e0a786a77e2001c40946009df9e0a20624109014ef8f8818712b0480bf3c1440c4469e0a681169cf00044d8f1eb829b9ae2d7f5c66215144cce2244b08800ffd82ffd52ffd81ffc81ffd61ffc61ffd51ffd21ffd80ffd70ffd60ffd50ffd20ffd10fdd31fdd30
def mo511H13 (j : Nat) : Nat := 0x1f18d34000000000056e000204777ec6b8961119c658ba000187ed170199b340000000000000000d8a0003a3b2b1e2c00042033064300000140000a12b6a89011b7e5d000297c000cad0000002f7189aca38000000ac000068e4e8d2de000000350986163741e5870bccf22f29555d4b74211cd4001a2450c0000000dd93350b20001bb50002c86cec000e480002f16893f44192b1a00001ef8a2adb30b254b1690af2acf20a000000022a92e3031122a7acb59c280005078978a784a9c6d0005a5c4900a72af800379aeaf000789c170000751800113f205d5f9e71d77eab49500113560006112008000077e07800173460a925c6948b22e6b1bba2dc57044e4680035cb1400003208000000929000000033100053586d881a30e5441f1a000662000130442d7650001d6ba5500000020e20004270000e9c9cf61f2b2746acbee43fb6248764d00001a69b4049a617e9f85276832d299a656541cc9156acc57b0761fd280012e8aaf4aa0001f9deda26c68fa0000000b8f00625159dfaa44fd274040eb2cc169d6b73b2c08742a0172320f599ac6f04007d394ea150b2835132467868dca76deee074a3080d9d0195972619297e46e29d07743ce07e608044000c06f5d1a6c58b415e53258c4f7a89f5ee89400100e838148b865a6046e91e000000091b0001cac0001bae15c0007c3a1880007a191a9e5800345cd99000000000026b0000000000000f70800000127557160bc0000000000001a9200000049ce354000c4a9aa800163cf8e316c001e64a5cc34c0007974b3353c2fb519da220f40f824c0002f05ecfeb37a8f9ff236e170000000a9b6a20005588001c72ef05085cd84c7c5b3c3e40190ba6f8d878dec5ed695af00219bec947262027eb4000106e49e5265588000af6000204d4f627ec9cd20e0d0a7089214298ec1a90012563eddf40000fea30a388fba1c4e9a3f8c7886c1300025493254810814870012420211c40c1053c0920905608428204b2061c94853000c000000d3d118105104c18c2480420050000000580800806070400497800010050401c8b000010030520c10a300000b5c334008c280
def mo511D14 (j : Nat) : Nat := 0x26f9e31a20dff
def mo511H14 (j : Nat) : Nat := 0x11d2a7a400000003d1000f1be74bc100208a1b726754003fb77b40004a50012200003734d530061c0140190000038058000000000418115
def mo511L : Nat → Packing
  | 8 => (1,6,6,0,0,0,0,mo511D8)
  | 9 => (117,5,6,0,0,12,0,mo511D9)
  | 10 => (805,4,6,0,0,15,0,mo511D10)
  | 11 => (1179,3,6,0,0,16,0,mo511D11)
  | 12 => (233,2,6,0,0,14,0,mo511D12)
  | 13 => (16,1,6,0,0,10,0,mo511D13)
  | 14 => (1,0,6,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 1 0 6 1 1 mo511H9
  | 10 => lookupWord 76 184 6 12 7 1 mo511H10
  | 11 => lookupWord 561 1258 7 15 10 1 mo511H11
  | 12 => lookupWord 577 1939 8 16 11 1 mo511H12
  | 13 => lookupWord 110 430 6 13 8 1 mo511H13
  | 14 => lookupWord 9 45 4 9 4 1 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B8 : CutRow mo511 8 0 1 := mo511P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_3 : CutRow mo511 9 3 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_51 : CutRow mo511 9 51 6 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_57 : CutRow mo511 9 57 1 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_58 : CutRow mo511 9 58 59 := mixedCut (pos:=0x5024104812210481221044411) (neg:=0xf05a640f02d8483cb41e) (data:=fun _ => 0x383728459516118595161035951610395056141794031840383720405831405058314055971611478413117038372038951315301847206058314050572140659716114595161140382720403837204282133482821334105831405058314052821334228213348058314050583140514714515302102803021028030210280303102403031024030210280302102303021023016715574303102301471451579413114704102809671557405720405057204050572040559716114597161187951311479513114794131149343585279513114795131147940311430310240303102403031024030210280) rfl (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 117 := (@joinRow mo511 9 0 3 114 mo511P9_0 (@joinRow mo511 9 3 48 66 mo511P9_3 (@joinRow mo511 9 51 6 60 mo511P9_51 (@joinRow mo511 9 57 1 59 mo511P9_57 mo511P9_58))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_48 : CutRow mo511 10 48 40 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_88 : CutRow mo511 10 88 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_136 : CutRow mo511 10 136 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_184 : CutRow mo511 10 184 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_232 : CutRow mo511 10 232 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_280 : CutRow mo511 10 280 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_328 : CutRow mo511 10 328 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_376 : CutRow mo511 10 376 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_424 : CutRow mo511 10 424 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_472 : CutRow mo511 10 472 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_520 : CutRow mo511 10 520 45 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_565 : CutRow mo511 10 565 5 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_570 : CutRow mo511 10 570 200 := mixedCut (pos:=0x5024104812210481221044411) (neg:=0x190079e1e0b416c24b41e) (data:=fun _ => 0x5961811959618119596181195961811459618114596181145961811559618114796121145961811503524205055282087487258574872586035242047931211a5961811503524206796121150357420a79612115035742060352420559618114035742050a52820503524205035242050352420503524204035342040357420503524204035242050352420503524204035242047961219479312194293121940153420989612183144735952871236228712362055214072871236228712352287123522871235205521406055214065961811528712362730218a1055214050552140628712341796121142871235205521405055214059706214105521406055214050552140579612114287123520552140505521405055214070652140727217a5a05521405055214067931211405521406055214050552140559618104164165151641651630210250307102a03071024074812515748125157481251674812516302102403021025030210250307102a0307102403071025030710240307102503071025030210250307102a03071024030710240307102407961211416416515164165157961211416416516302102403021025079612114307102a030710240307102401641659530210240307102401441351674412516144135151441351514413515748125853021026079412115594181157941211459418114594181140547040605470406054704060547040505470405054204055941811405470406054704060547040589512183a0068347a001834727217a5a79412104594181040557147505571475796121157961211579312114172619473021026079312115303142903031425079612114796121147931211493326862703102907961211479612114793121147930211597062151302102503021025079302114302102403021025030210250810237a13021024049312184198157767931219419815776933258614931218430210250793021943021024030210240293121843071025079302194307102a030710240307102403021026017261946307102901726195813261949793121040353427a03534274793021043021024830210248) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_770 : CutRow mo511 10 770 35 := mixedCut (pos:=0x5024104812210481221044411) (neg:=0xf0b5e1095a1e0b590) (data:=fun _ => 0x59210115793141150354329559210115592101159374587959310115592101153041726097724151792141150354329503543209035432055921011538013a680354320605541407796141155921011559210115592101155931011503543206035432040a540205035432050354320503543205592101155921011559210115592101155921011559210115) rfl (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 805 := (@joinRow mo511 10 0 48 757 mo511P10_0 (@joinRow mo511 10 48 40 717 mo511P10_48 (@joinRow mo511 10 88 48 669 mo511P10_88 (@joinRow mo511 10 136 48 621 mo511P10_136 (@joinRow mo511 10 184 48 573 mo511P10_184 (@joinRow mo511 10 232 48 525 mo511P10_232 (@joinRow mo511 10 280 48 477 mo511P10_280 (@joinRow mo511 10 328 48 429 mo511P10_328 (@joinRow mo511 10 376 48 381 mo511P10_376 (@joinRow mo511 10 424 48 333 mo511P10_424 (@joinRow mo511 10 472 48 285 mo511P10_472 (@joinRow mo511 10 520 45 240 mo511P10_520 (@joinRow mo511 10 565 5 235 mo511P10_565 (@joinRow mo511 10 570 200 35 mo511P10_570 mo511P10_770))))))))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 28 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_28 : CutRow mo511 11 28 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_76 : CutRow mo511 11 76 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_124 : CutRow mo511 11 124 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_172 : CutRow mo511 11 172 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_220 : CutRow mo511 11 220 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_268 : CutRow mo511 11 268 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_316 : CutRow mo511 11 316 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_364 : CutRow mo511 11 364 28 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_392 : CutRow mo511 11 392 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_440 : CutRow mo511 11 440 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_488 : CutRow mo511 11 488 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_536 : CutRow mo511 11 536 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_584 : CutRow mo511 11 584 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_632 : CutRow mo511 11 632 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_680 : CutRow mo511 11 680 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_728 : CutRow mo511 11 728 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_776 : CutRow mo511 11 776 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_824 : CutRow mo511 11 824 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_872 : CutRow mo511 11 872 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_920 : CutRow mo511 11 920 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_968 : CutRow mo511 11 968 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_1016 : CutRow mo511 11 1016 36 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_1052 : CutRow mo511 11 1052 11 := by
  apply checkedRow
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_1063 : CutRow mo511 11 1063 116 := mixedCut (pos:=0x5024104812210481221044411) (neg:=0xf0c82d05a0f0f424f05a) (data:=fun _ => 0x30403260791021159731215103826206795021155910711503826206038262060a827206038262060a8272060382620603826206038262060382620603826206591071155910711593328882933288821721495871524985733208820a8272060382620603826206038462060382620603826206038462060a8272060382620603826206038562060382620617214958791021152840236228402362284023622840236228402362285023620582040728412362284023629362888279102115058204072840236228402362284023622840236228402362284023622840236205820407284023622840236228402362058204072840236205820407058204072840236259607115058404072840236293628882058204070582040705840407284023620582040705820407058204070582040705840407974121519741215197412151197087183021626083826a860562340759607115056434070564340705643407056434077950211579502115795021157950211579502115795021151721095879502115795021157950211579502115795021157950211579532115302032603020326081325781795021153040326030203260304032601721095830203260172109583040326017210958) rfl (by decide +kernel)
theorem mo511B11 : CutRow mo511 11 0 1179 := (@joinRow mo511 11 0 28 1151 mo511P11_0 (@joinRow mo511 11 28 48 1103 mo511P11_28 (@joinRow mo511 11 76 48 1055 mo511P11_76 (@joinRow mo511 11 124 48 1007 mo511P11_124 (@joinRow mo511 11 172 48 959 mo511P11_172 (@joinRow mo511 11 220 48 911 mo511P11_220 (@joinRow mo511 11 268 48 863 mo511P11_268 (@joinRow mo511 11 316 48 815 mo511P11_316 (@joinRow mo511 11 364 28 787 mo511P11_364 (@joinRow mo511 11 392 48 739 mo511P11_392 (@joinRow mo511 11 440 48 691 mo511P11_440 (@joinRow mo511 11 488 48 643 mo511P11_488 (@joinRow mo511 11 536 48 595 mo511P11_536 (@joinRow mo511 11 584 48 547 mo511P11_584 (@joinRow mo511 11 632 48 499 mo511P11_632 (@joinRow mo511 11 680 48 451 mo511P11_680 (@joinRow mo511 11 728 48 403 mo511P11_728 (@joinRow mo511 11 776 48 355 mo511P11_776 (@joinRow mo511 11 824 48 307 mo511P11_824 (@joinRow mo511 11 872 48 259 mo511P11_872 (@joinRow mo511 11 920 48 211 mo511P11_920 (@joinRow mo511 11 968 48 163 mo511P11_968 (@joinRow mo511 11 1016 36 127 mo511P11_1016 (@joinRow mo511 11 1052 11 116 mo511P11_1052 mo511P11_1063))))))))))))))))))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_6 : CutRow mo511 12 6 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_54 : CutRow mo511 12 54 39 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_93 : CutRow mo511 12 93 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_141 : CutRow mo511 12 141 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_189 : CutRow mo511 12 189 44 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 233 := (@joinRow mo511 12 0 6 227 mo511P12_0 (@joinRow mo511 12 6 48 179 mo511P12_6 (@joinRow mo511 12 54 39 140 mo511P12_54 (@joinRow mo511 12 93 48 92 mo511P12_93 (@joinRow mo511 12 141 48 44 mo511P12_141 mo511P12_189)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_2 : CutRow mo511 13 2 14 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 16 := (@joinRow mo511 13 0 2 14 mo511P13_0 mo511P13_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : CutRow mo511 14 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : CutRow mo511 14 0 1 := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 14 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo511 0 0)
  · exact (mixedEmpty mo511 1 0)
  · exact (mixedEmpty mo511 2 0)
  · exact (mixedEmpty mo511 3 0)
  · exact (mixedEmpty mo511 4 0)
  · exact (mixedEmpty mo511 5 0)
  · exact (mixedEmpty mo511 6 0)
  · exact (mixedEmpty mo511 7 0)
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
  · exact mo511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore KM495) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 nineInputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=14) (i:=0) (before_sound KM495 VM495) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_10838

theorem PEqualNP.Outside.L_meta_10838 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 6 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact PEqualNP.Outside.L_meta_10838.directSplit PEqualNP.Outside.L_meta_10838.mo511R PEqualNP.Outside.L_meta_10838.g511R ⟨C,hf,by omega,heq⟩
