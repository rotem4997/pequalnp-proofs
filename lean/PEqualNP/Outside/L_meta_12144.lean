import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12144
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 128
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

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [9, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [6, 17]⟩], 18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 13 := rfl

def v0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def v1 : Nat := 0xcccccccccccccccccccccccccccccccc
def v2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def v3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def v4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def v5 : Nat := 0xfafafafafafafafafafafafafafafafa
def v6 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def v7 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def v8 : Nat := 0xffccffccffccffccffccffccffccffcc
def v9 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def v10 : Nat := 0xfefefefefefefefefefefefefefefefe
def v11 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def v12 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def v13 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def v14 : Nat := 0x32323232323232323232323232323232
def v15 : Nat := 0xfffafffafffafffafffafffafffafffa
def v16 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def v17 : Nat := 0x33223322332233223322332233223322
def v18 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def v19 : Nat := 0x54545454545454545454545454545454
def v20 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def v21 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def v22 : Nat := 0x55445544554455445544554455445544
def v23 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def v24 : Nat := 0x55505550555055505550555055505550
def v25 : Nat := 0x33303330333033303330333033303330
def v26 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def v27 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def v28 : Nat := 0x33323332333233323332333233323332
def v29 : Nat := 0x55545554555455545554555455545554
def v30 : Nat := 0x88888888888888888888888888888888
def v31 : Nat := 0x22222222222222222222222222222222
def v32 : Nat := 0x44444444444444444444444444444444
def v33 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def v34 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def v35 : Nat := 0x50505050505050505050505050505050
def v36 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def v37 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def v38 : Nat := 0x55005500550055005500550055005500
def v39 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def v40 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def v41 : Nat := 0x30303030303030303030303030303030
def v42 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def v43 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def v44 : Nat := 0x33003300330033003300330033003300
def v45 : Nat := 0xf000f000f000f000f000f000f000f000
def v46 : Nat := 0xf000f000f000f000f000f000f000f0
def v47 : Nat := 0xf000f000f000f000f000f000f000f00
def v48 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def v49 : Nat := 0x70707070707070707070707070707070
def v50 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def v51 : Nat := 0x77007700770077007700770077007700
def v52 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def v53 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def v54 : Nat := 0xecececececececececececececececec
def v55 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def v56 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def v57 : Nat := 0x5f005f005f005f005f005f005f005f00
def v58 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def v59 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00
def v60 : Nat := 0xeecceecceecceecceecceecceecceecc
def v61 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def v62 : Nat := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def v63 : Nat := 0x50f050f050f050f050f050f050f050f0
def v64 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def v65 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0
def v66 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def v67 : Nat := 0xf300f300f300f300f300f300f300f300
def v68 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30
def v69 : Nat := 0xcf00cf00cf00cf00cf00cf00cf00cf00
def v70 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def v71 : Nat := 0xf030f030f030f030f030f030f030f030
def v72 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def v73 : Nat := 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0
def v74 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def v75 : Nat := 0xcc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c
def v76 : Nat := 0xcfcccfcccfcccfcccfcccfcccfcccfcc
def v77 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def v78 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def v79 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def v80 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def v81 : Nat := 0xff000000ff000000ff000000ff000000
def v82 : Nat := 0xffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0
def v83 : Nat := 0xfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def v84 : Nat := 0xfcccf000fcccf000fcccf000fcccf000
def v85 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def v86 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def v87 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def v88 : Nat := 0x55550000555500005555000055550000
def v89 : Nat := 0xcccc0000cccc0000cccc0000cccc
def v90 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def v91 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def v92 : Nat := 0xff000000ff000000ff000000ff00
def v93 : Nat := 0xff000000ff000000ff000000ff0000
def v94 : Nat := 0x80808080808080808080808080808080
def v95 : Nat := 0x880088008800880088008800880088
def v96 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def v97 : Nat := 0x8888000088880000888800008888
def v98 : Nat := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
def v99 : Nat := 0xa000a000a000a000a000a000a000a0
def v100 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
def v101 : Nat := 0xa0a00000a0a00000a0a00000a0a0
def v102 : Nat := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
def v103 : Nat := 0xffffaa00ffffaa00ffffaa00ffffaa00
def v104 : Nat := 0x55ff000055ff000055ff000055ff0000
def v105 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000
def v106 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa
def v107 : Nat := 0x88cc88cc88cc88cc88cc88cc88cc88cc
def v108 : Nat := 0xa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0
def v109 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def v110 : Nat := 0x5050f0f05050f0f05050f0f05050f0f0
def v111 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00
def v112 : Nat := 0x5500ff005500ff005500ff005500ff00
def v113 : Nat := 0xcccc8888cccc8888cccc8888cccc8888
def v114 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0
def v115 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00
def v116 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa
def v117 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def v118 : Nat := 0xa0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0
def v119 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def v120 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def v121 : Nat := 0x40404040404040404040404040404040
def v122 : Nat := 0xc000c000c000c000c000c000c000c000
def v123 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def v124 : Nat := 0xc000c000c000c000c000c000c000c0
def v125 : Nat := 0x3f003f003f003f003f003f003f003f00
def v126 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def v127 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def v128 : Nat := 0xc0c00000c0c00000c0c00000c0c0
def v129 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def v130 : Nat := 0x30f030f030f030f030f030f030f030f0
def v131 : Nat := 0xaa22aa22aa22aa22aa22aa22aa22aa22
def v132 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def v133 : Nat := 0xaaaa2222aaaa2222aaaa2222aaaa2222
def v134 : Nat := 0xf0f03030f0f03030f0f03030f0f03030
def v135 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc
def v136 : Nat := 0xaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a
def v137 : Nat := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
def v138 : Nat := 0xaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0a
def v139 : Nat := 0xcccc0c0ccccc0c0ccccc0c0ccccc0c0c
def v140 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def v141 : Nat := 0xcccccc00cccccc00cccccc00cccccc00
def v142 : Nat := 0xf0f0f000f0f0f000f0f0f000f0f0f000
def v143 : Nat := 0xcccc00cccccc00cccccc00cccccc00cc
def v144 : Nat := 0xf0f000f0f0f000f0f0f000f0f0f000f0
def v145 : Nat := 0xcc00cccccc00cccccc00cccccc00cccc
def v146 : Nat := 0xf000f0f0f000f0f0f000f0f0f000f0f0
def v147 : Nat := 0xff80ff80ff80ff80ff80ff80ff80ff80
def v148 : Nat := 0xffff8080ffff8080ffff8080ffff8080
def v149 : Nat := 0x7f007f007f007f007f007f007f007f00
def v150 : Nat := 0x7f7f00007f7f00007f7f00007f7f0000
def v151 : Nat := 0x88f888f888f888f888f888f888f888f8
def v152 : Nat := 0x88088808880888088808880888088808
def v153 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def v154 : Nat := 0x88880808888808088888080888880808
def v155 : Nat := 0x88888800888888008888880088888800
def v156 : Nat := 0x77777700777777007777770077777700
def v157 : Nat := 0xa0eca0eca0eca0eca0eca0eca0eca0ec
def v158 : Nat := 0xa020a020a020a020a020a020a020a020
def v159 : Nat := 0xa0a0ececa0a0ececa0a0ececa0a0ecec
def v160 : Nat := 0xa0a02020a0a02020a0a02020a0a02020
def v161 : Nat := 0xa0a0a000a0a0a000a0a0a000a0a0a000
def v162 : Nat := 0x5f5f5f005f5f5f005f5f5f005f5f5f00
def v163 : Nat := 0x40c040c040c040c040c040c040c040c0
def v164 : Nat := 0xb030b030b030b030b030b030b030b030
def v165 : Nat := 0x8c0c8c0c8c0c8c0c8c0c8c0c8c0c8c0c
def v166 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def v167 : Nat := 0xc080c080c080c080c080c080c080c080
def v168 : Nat := 0x3f2a3f2a3f2a3f2a3f2a3f2a3f2a3f2a
def v169 : Nat := 0x30703070307030703070307030703070
def v170 : Nat := 0xfcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8
def v171 : Nat := 0xc080c080c080c080c080c080c080c08
def v172 : Nat := 0xc4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c
def v173 : Nat := 0xfcecfcecfcecfcecfcecfcecfcecfcec
def v174 : Nat := 0x30203020302030203020302030203020
def v175 : Nat := 0x80c080c080c080c080c080c080c080c0
def v176 : Nat := 0x70307030703070307030703070307030
def v177 : Nat := 0x4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c
def v178 : Nat := 0xd5c0d5c0d5c0d5c0d5c0d5c0d5c0d5c0
def v179 : Nat := 0x4040c0c04040c0c04040c0c04040c0c0
def v180 : Nat := 0xb0b03030b0b03030b0b03030b0b03030
def v181 : Nat := 0x8c8c0c0c8c8c0c0c8c8c0c0c8c8c0c0c
def v182 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
def v183 : Nat := 0xc0c08080c0c08080c0c08080c0c08080
def v184 : Nat := 0x3f3f2a2a3f3f2a2a3f3f2a2a3f3f2a2a
def v185 : Nat := 0x30307070303070703030707030307070
def v186 : Nat := 0xfcfcf8f8fcfcf8f8fcfcf8f8fcfcf8f8
def v187 : Nat := 0xc0c08080c0c08080c0c08080c0c0808
def v188 : Nat := 0xc0c4c4c0c0c4c4c0c0c4c4c0c0c4c4c
def v189 : Nat := 0xfcfcececfcfcececfcfcececfcfcecec
def v190 : Nat := 0x30302020303020203030202030302020
def v191 : Nat := 0x8080c0c08080c0c08080c0c08080c0c0
def v192 : Nat := 0x70703030707030307070303070703030
def v193 : Nat := 0x4c4c0c0c4c4c0c0c4c4c0c0c4c4c0c0c
def v194 : Nat := 0xd5d5c0c0d5d5c0c0d5d5c0c0d5d5c0c0
def v195 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea00
def v196 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea
def v197 : Nat := 0xeaea0000eaea0000eaea0000eaea0000
def v198 : Nat := 0xeaea0000eaea0000eaea0000eaea
def v199 : Nat := 0xffff00c0ffff00c0ffff00c0ffff00c0
def v200 : Nat := 0xff3f0000ff3f0000ff3f0000ff3f0000
def v201 : Nat := 0xffff3f00ffff3f00ffff3f00ffff3f00
def v202 : Nat := 0xc0ff0000c0ff0000c0ff0000c0ff0000
def v203 : Nat := 0xff00ffc0ff00ffc0ff00ffc0ff00ffc0
def v204 : Nat := 0xff003f00ff003f00ff003f00ff003f00
def v205 : Nat := 0xff3fff00ff3fff00ff3fff00ff3fff00
def v206 : Nat := 0xc000ff00c000ff00c000ff00c000ff00
def v207 : Nat := 0xc0c0c000c0c0c000c0c0c000c0c0c000
def v208 : Nat := 0x3f3f3f003f3f3f003f3f3f003f3f3f00
def v209 : Nat := 0xc0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0
def v210 : Nat := 0xc0c000c0c0c000c0c0c000c0c0c000c0
def v211 : Nat := 0xc0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0
def v212 : Nat := 0xc000c0c0c000c0c0c000c0c0c000c0c0
def v213 : Nat := 0x50d050d050d050d050d050d050d050d0
def v214 : Nat := 0xa8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a
def v215 : Nat := 0x5050d0d05050d0d05050d0d05050d0d0
def v216 : Nat := 0xa0a8a8a0a0a8a8a0a0a8a8a0a0a8a8a
def v217 : Nat := 0x44c444c444c444c444c444c444c444c4
def v218 : Nat := 0x22a222a222a222a222a222a222a222a2
def v219 : Nat := 0x4444c4c44444c4c44444c4c44444c4c4
def v220 : Nat := 0x2222a2a22222a2a22222a2a22222a2a2
def v221 : Nat := 0x444444cc444444cc444444cc444444cc
def v222 : Nat := 0x505050f0505050f0505050f0505050f0
def v223 : Nat := 0x222222aa222222aa222222aa222222aa
def v224 : Nat := 0x303030f0303030f0303030f0303030f0
def v225 : Nat := 0xa0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa
def v226 : Nat := 0xc0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc
def v227 : Nat := 0x3030f0303030f0303030f0303030f030
def v228 : Nat := 0xc0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c
def v229 : Nat := 0x30f0303030f0303030f0303030f03030
def v230 : Nat := 0xccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c
def v231 : Nat := 0x707070f0707070f0707070f0707070f0
def v232 : Nat := 0x4c4c4ccc4c4c4ccc4c4c4ccc4c4c4ccc
def v233 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def v234 : Nat := 0xfcfca800fcfca800fcfca800fcfca800
def v235 : Nat := 0xa800fcfca800fcfca800fcfca800fcfc
def v236 : Nat := 0xfca8fc00fca8fc00fca8fc00fca8fc00
def v237 : Nat := 0xa8fc00fca8fc00fca8fc00fca8fc00fc
def v238 : Nat := 0x6a6a6a6a6a6a6a6a6a6a6a6a6a6a6a6a
def v239 : Nat := 0x3fc03fc03fc03fc03fc03fc03fc03fc0
def v240 : Nat := 0x3f3fc0c03f3fc0c03f3fc0c03f3fc0c0
def v241 : Nat := 0xfcfc3c00fcfc3c00fcfc3c00fcfc3c00
def v242 : Nat := 0xfc3cfc00fc3cfc00fc3cfc00fc3cfc00
def v243 : Nat := 0x88008800880088008800880088008800
def v244 : Nat := 0xa000a000a000a000a000a000a000a000
def v245 : Nat := 0x22aa22aa22aa22aa22aa22aa22aa22aa
def v246 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
def v247 : Nat := 0x70f070f070f070f070f070f070f070f0
def v248 : Nat := 0x4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc
def v249 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def v250 : Nat := 0xe0e0e0e0e000e000e0e0e0e0e000e00
def v251 : Nat := 0xeeeeeeeeee00ee00eeeeeeeeee00ee00
def v252 : Nat := 0xffffffff00000000ffffffff00000000
def v253 : Nat := 0x32323232320032003232323232003200
def v254 : Nat := 0xfafafafafa00fa00fafafafafa00fa00
def v255 : Nat := 0x54545454540054005454545454005400
def v256 : Nat := 0xfcfcfcfcfc00fc00fcfcfcfcfc00fc00
def v257 : Nat := 0xfefefefefef0fef0fefefefefef0fef0
def v258 : Nat := 0xfefefefefeccfeccfefefefefeccfecc
def v259 : Nat := 0xfefefefefeaafeaafefefefefeaafeaa
def v260 : Nat := 0xeeeeee00eeeeee00eeeeee00eeeeee
def v261 : Nat := 0xfafafa00fafafa00fafafa00fafafa
def v262 : Nat := 0xfcfcfc00fcfcfc00fcfcfc00fcfcfc
def v263 : Nat := 0xa8a8fcfca8a8fcfca8a8fcfca8a8fcfc
def v264 : Nat := 0xa8fca8fca8fca8fca8fca8fca8fca8fc
def v265 : Nat := 0xaaffaaff88cc88ccaaffaaff88cc88cc
def v266 : Nat := 0xaaffaaffa0f0a0f0aaffaaffa0f0a0f0
def v267 : Nat := 0xc8c8fafac8c8fafac8c8fafac8c8fafa
def v268 : Nat := 0xc8fac8fac8fac8fac8fac8fac8fac8fa
def v269 : Nat := 0xccffccff88aa88aaccffccff88aa88aa
def v270 : Nat := 0xccffccffc0f0c0f0ccffccffc0f0c0f0
def v271 : Nat := 0xe0e0eeeee0e0eeeee0e0eeeee0e0eeee
def v272 : Nat := 0xe0eee0eee0eee0eee0eee0eee0eee0ee
def v273 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee0
def v274 : Nat := 0xeeeeeeeee0e0e0e0eeeeeeeee0e0e0e0
def v275 : Nat := 0xffffffffff000000ffffffffff000000
def v276 : Nat := 0xf0fff0ffa0aaa0aaf0fff0ffa0aaa0aa
def v277 : Nat := 0xf0fff0ffc0ccc0ccf0fff0ffc0ccc0cc
def v278 : Nat := 0xfac8fac8fac8fac8fac8fac8fac8fac8
def v279 : Nat := 0xfafafafac8c8c8c8fafafafac8c8c8c8
def v280 : Nat := 0xfca8fca8fca8fca8fca8fca8fca8fca8
def v281 : Nat := 0xfcfcfcfca8a8a8a8fcfcfcfca8a8a8a8
def v282 : Nat := 0xff00ff0000000000ff00ff00
def v283 : Nat := 0xffff000000000000ffff0000
def v284 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def v285 : Nat := 0xffffffffccccccccffffffffcccccccc
def v286 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def v287 : Nat := 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a
def v288 : Nat := 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
def v289 : Nat := 0xf0f0f0f0f000f000f0f0f0f0f000f00
def v290 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def v291 : Nat := 0x33330000333300003333000033330000
def v292 : Nat := 0x33333333222222223333333322222222
def v293 : Nat := 0x33333333303030303333333330303030
def v294 : Nat := 0x33333333330033003333333333003300
def v295 : Nat := 0x55555555444444445555555544444444
def v296 : Nat := 0x55555555505050505555555550505050
def v297 : Nat := 0x55555555550055005555555555005500
def v298 : Nat := 0xaaaaaaaaffffaaaaaaaaaaaaffffaaaa
def v299 : Nat := 0xafaaafaaafaaafaaafaaafaaafaaafaa
def v300 : Nat := 0xafafaaaaafafaaaaafafaaaaafafaaaa
def v301 : Nat := 0xbbaabbaabbaabbaabbaabbaabbaabbaa
def v302 : Nat := 0xbbbbaaaabbbbaaaabbbbaaaabbbbaaaa
def v303 : Nat := 0xccccccccffffccccccccccccffffcccc
def v304 : Nat := 0xcfcfcccccfcfcccccfcfcccccfcfcccc
def v305 : Nat := 0xddccddccddccddccddccddccddccddcc
def v306 : Nat := 0xddddccccddddccccddddccccddddcccc
def v307 : Nat := 0xeeee0000eeee0000eeee0000eeee0000
def v308 : Nat := 0xffffffffff00ff00ffffffffff00ff00
def v309 : Nat := 0xf0f0f0f0fffff0f0f0f0f0f0fffff0f0
def v310 : Nat := 0xf3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0
def v311 : Nat := 0xf5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0
def v312 : Nat := 0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0
def v313 : Nat := 0xfafa0000fafa0000fafa0000fafa0000
def v314 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00
def v315 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000
def v316 : Nat := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def v317 : Nat := 0xffccccccffccccccffccccccffcccccc
def v318 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0

def u0_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def u0_R : List Nat := [0, 1]
def u0_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem u0_B : baseOK u0_T u0_R u0_E = true := by decide +kernel
theorem u0_L : LowN u0_R u0_T 1 := lowCount u0_B (by decide +kernel)

def u1_T : Nat := 0x88888888888888888888888888888888
def u1_R : List Nat := [0, 1]
def u1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem u1_B : baseOK u1_T u1_R u1_E = true := by decide +kernel
theorem u1_L : LowN u1_R u1_T 1 := lowCount u1_B (by decide +kernel)

def u2_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def u2_R : List Nat := [0, 1, 2]
def u2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem u2_B : baseOK u2_T u2_R u2_E = true := by decide +kernel
theorem u2_S0 : SliceN u2_R u2_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) u2_B u1_B u1_L (by decide +kernel)
theorem u2_S1 : SliceN u2_R u2_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) u2_B u1_B u1_L (by decide +kernel)
theorem u2_S2 : SliceN u2_R u2_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) u2_B u0_B u0_L (by decide +kernel)
theorem u2_S3 : SliceN u2_R u2_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) u2_B u0_B u0_L (by decide +kernel)
theorem u2_S4 : SliceN u2_R u2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) u2_B u1_B u1_L (by decide +kernel)
theorem u2_S5 : SliceN u2_R u2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) u2_B u0_B u0_L (by decide +kernel)
def u2_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem u2_Y : ∀ s ∈ u2_Z, SliceN u2_R u2_T s := by
  unfold u2_Z
  simp only [List.forall_mem_cons]
  exact ⟨u2_S0,u2_S1,u2_S2,u2_S3,u2_S4,u2_S5,by simp⟩
def u2_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def u2_P : List (Nat × Nat) := [(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)]
def u2_K : List CutV := u2_C.map (mkCut u2_Z)
theorem u2_W : ∀ c ∈ u2_K, CutP u2_R u2_T c := cutsGood u2_Y (by decide +kernel)
theorem u2_Q : u2_P.all (sepOK u2_T) = true := by decide +kernel
noncomputable def u2_D3 : List StD := [
([v0,v1,v2],[0,1,2,3,4,5],[0,1,2,3,4,5],[[0,1,100,2,3,101,102],[4,1,103,5,3,100],[4,0,101,5,2,104,105]])]
def u2_D2 : List StD := []
theorem u2_I2 : LevelN u2_R u2_T 2 u2_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u2_C3x0 : levelOK u2_T u2_K u2_P 2 (u2_D2.map Prod.fst) ((u2_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem u2_I3 : LevelN u2_R u2_T 3 u2_D3 := levelStep u2_B u2_W u2_Q u2_I2 (chunks 16 u2_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u2_C3x0
  ))
theorem u2_L : LowN u2_R u2_T 4 := lowSearch u2_B u2_I3 (by decide +kernel)

def u3_T : Nat := 0xfefefefefefefefefefefefefefefefe
def u3_R : List Nat := [0, 1, 2]
def u3_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem u3_B : baseOK u3_T u3_R u3_E = true := by decide +kernel
theorem u3_L : LowN u3_R u3_T 2 := lowCount u3_B (by decide +kernel)

def u4_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def u4_R : List Nat := [0, 1, 2, 3]
def u4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem u4_B : baseOK u4_T u4_R u4_E = true := by decide +kernel
theorem u4_S0 : SliceN u4_R u4_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) u4_B u2_B u2_L (by decide +kernel)
theorem u4_S1 : SliceN u4_R u4_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) u4_B u2_B u2_L (by decide +kernel)
theorem u4_S2 : SliceN u4_R u4_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) u4_B u2_B u2_L (by decide +kernel)
theorem u4_S3 : SliceN u4_R u4_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) u4_B u2_B u2_L (by decide +kernel)
theorem u4_S4 : SliceN u4_R u4_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S5 : SliceN u4_R u4_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) u4_B u3_B u3_L (by decide +kernel)
theorem u4_S6 : SliceN u4_R u4_T (0x5050505050505050505050505050505,1,[1, 3]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S7 : SliceN u4_R u4_T (0x550055005500550055005500550055,1,[1, 2]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S8 : SliceN u4_R u4_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S9 : SliceN u4_R u4_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) u4_B u3_B u3_L (by decide +kernel)
theorem u4_S10 : SliceN u4_R u4_T (0x330033003300330033003300330033,1,[0, 2]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S11 : SliceN u4_R u4_T (0xf000f000f000f000f000f000f000f,1,[0, 1]) := mkSlice (w:=0) u4_B u1_B u1_L (by decide +kernel)
theorem u4_S12 : SliceN u4_R u4_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) u4_B u3_B u3_L (by decide +kernel)
theorem u4_S13 : SliceN u4_R u4_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]) := mkSlice (w:=2) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S14 : SliceN u4_R u4_T (0x30303030303030303030303030303030,1,[0, 3]) := mkSlice (w:=4) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S15 : SliceN u4_R u4_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S16 : SliceN u4_R u4_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) u4_B u3_B u3_L (by decide +kernel)
theorem u4_S17 : SliceN u4_R u4_T (0x33003300330033003300330033003300,1,[0, 2]) := mkSlice (w:=8) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S18 : SliceN u4_R u4_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S19 : SliceN u4_R u4_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S20 : SliceN u4_R u4_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S21 : SliceN u4_R u4_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S22 : SliceN u4_R u4_T (0xf000f000f000f000f000f000f000f0,1,[0, 1]) := mkSlice (w:=4) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S23 : SliceN u4_R u4_T (0xf000f000f000f000f000f000f000f00,1,[0, 1]) := mkSlice (w:=8) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S24 : SliceN u4_R u4_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) u4_B u0_B u0_L (by decide +kernel)
theorem u4_S25 : SliceN u4_R u4_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) u4_B u0_B u0_L (by decide +kernel)
def u4_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0x5050505050505050505050505050505,1,[1, 3]),(0x550055005500550055005500550055,1,[1, 2]),(0x3030303030303030303030303030303,1,[0, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0x330033003300330033003300330033,1,[0, 2]),(0xf000f000f000f000f000f000f000f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]),(0x30303030303030303030303030303030,1,[0, 3]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0x33003300330033003300330033003300,1,[0, 2]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0x50505050505050505050505050505050,1,[1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0x55005500550055005500550055005500,1,[1, 2]),(0xf000f000f000f000f000f000f000f0,1,[0, 1]),(0xf000f000f000f000f000f000f000f00,1,[0, 1]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3])]
theorem u4_Y : ∀ s ∈ u4_Z, SliceN u4_R u4_T s := by
  unfold u4_Z
  simp only [List.forall_mem_cons]
  exact ⟨u4_S0,u4_S1,u4_S2,u4_S3,u4_S4,u4_S5,u4_S6,u4_S7,u4_S8,u4_S9,u4_S10,u4_S11,u4_S12,u4_S13,u4_S14,u4_S15,u4_S16,u4_S17,u4_S18,u4_S19,u4_S20,u4_S21,u4_S22,u4_S23,u4_S24,u4_S25,by simp⟩
def u4_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(5,[]),(1,[(1,0,1)]),(3,[(1,0,2)]),(6,[]),(1,[(1,0,2)]),(2,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(8,[]),(9,[]),(3,[(1,1,2)]),(0,[(1,0,2)]),(2,[(1,1,2)]),(10,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(21,[]),(2,[(3,0,1)]),(0,[(3,0,1)]),(0,[(2,0,1)]),(1,[(2,0,1)]),(3,[(3,0,1)]),(0,[(3,0,2)]),(0,[(2,0,2)]),(1,[(2,0,2)]),(22,[]),(23,[]),(1,[(3,0,1)]),(24,[]),(25,[]),(2,[(2,0,1)]),(2,[(3,0,2)]),(0,[(3,1,2)]),(0,[(2,1,2)]),(2,[(2,0,2)]),(1,[(3,0,2)]),(3,[(2,0,1)]),(3,[(2,0,2)]),(3,[(2,1,2)]),(2,[(2,1,2)]),(3,[(3,1,2)]),(2,[(3,1,2)]),(1,[(3,1,2)]),(0,[(0,0,2)]),(1,[(2,1,2)]),(3,[(3,0,2)]),(3,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,0,2)]),(2,[(1,0,2),(1,1,2)]),(2,[(1,0,1),(1,1,2)]),(2,[(1,0,1),(1,0,2)]),(0,[(0,1,2)]),(2,[(1,0,1),(3,2,3)]),(0,[(0,0,1)]),(1,[(1,0,2),(3,1,3)]),(1,[(1,0,2),(1,1,2)]),(1,[(1,0,1),(1,1,2)]),(1,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(3,0,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)])]
def u4_P : List (Nat × Nat) := [(4,5),(2,3),(1,3),(1,5),(8,9),(1,9),(4,6),(2,6),(8,10),(2,10),(8,12),(4,12),(4,11),(7,8)]
def u4_K : List CutV := u4_C.map (mkCut u4_Z)
theorem u4_W : ∀ c ∈ u4_K, CutP u4_R u4_T c := cutsGood u4_Y (by decide +kernel)
theorem u4_Q : u4_P.all (sepOK u4_T) = true := by decide +kernel
noncomputable def u4_D6 : List StD := [
([v0,v1,v2,v3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11],[[0,1,100,101,102],[0,2,101,100,103],[0,3,100,104,105],[1,2,102,106,107],[1,3,102,108,109],[2,3,103,110,111]])]
noncomputable def u4_D5 : List StD := [
([v0,v1,v4,v2,v3],[0,1,4,5,6,2,7,3],[3,5,7,9,10,11],[[0,1],[1],[0,100,2],[0,101,3],[0],[1,102,2],[1,103,3],[2,4,5,6,100,104],[3,4,7,6,101,105],[3,2,100,104,105]]),
([v0,v1,v2,v5,v3],[0,8,2,9,10,1,7,3],[2,5,6,8,9,11],[[0,100,1],[0,2],[2],[0,101,3],[2,102,1],[4,1,5,6,100,103],[3,1,100,103,104],[0],[2,105,3],[3,4,7,6,101,104]]),
([v0,v1,v2,v3,v6],[0,11,12,3,13,1,7,2],[2,3,6,7,8,10],[[0,100,1],[0,101,2],[0,3],[3],[2,1,100,102,103],[3,104,1],[4,1,5,6,100,102],[3,105,2],[4,2,7,6,101,103],[0]]),
([v0,v1,v2,v7,v3],[1,14,2,15,0,16,17,3],[1,0,4,5,9,11],[[0,100,1],[2,101,1],[3,1,4,5,100,102],[6,1,100,102,103],[0,2],[2],[0,104,6],[0],[2,105,6],[6,3,7,5,104,103]]),
([v0,v1,v2,v3,v8],[1,18,19,3,20,0,16,2],[1,0,3,4,7,10],[[0,100,1],[2,1,100,101,102],[3,103,1],[4,1,5,6,100,101],[0,104,2],[0,3],[3],[3,105,2],[4,2,7,6,104,102],[0]]),
([v0,v1,v2,v3,v9],[21,22,2,3,23,0,24,1],[0,1,2,4,6,8],[[0,1,100,101,102],[2,100,1],[3,103,1],[4,1,5,6,100,101],[2,104,0],[3,105,0],[4,0,7,6,104,102],[2,3],[3],[2]])]
noncomputable def u4_D4 : List StD := [
([v1,v4,v2,v5,v3],[0,8,4,16,25,24,9,26,5],[11,9],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([v1,v4,v2,v3,v6],[0,11,27,5,12,28,29,4],[10,7],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([v0,v4,v2,v7,v3],[1,14,4,7,30,24,17,31,5],[11,5],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([v0,v4,v2,v3,v8],[1,18,32,5,19,28,33,4],[10,3],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([v0,v1,v2,v10,v3],[14,4,8,34,7,35,16,36,24,3],[],[[0,1,2],[0,2,1],[3],[0,4],[1,0,2],[5],[2,6],[7],[1,8],[9,4]]),
([v11,v0,v1,v2,v3],[0,4,34,14,3,25,24,36,37,30],[],[[0,1,2],[1,0],[3],[4,5,6],[7,1,8],[1,6],[7,9],[1,6],[8,5],[1,6]]),
([v0,v1,v2,v3,v12],[18,5,11,7,38,16,39,28,2,40],[],[[0,1,2],[0,3],[0,2,1],[4],[2,5],[1,0,2],[6],[1,7],[8,3],[9]]),
([v13,v0,v1,v2,v3],[0,5,38,2,32,28,18,40,41,27],[],[[0,1,2],[1,0],[3,4,5],[6],[7,1,4],[7,4],[1,5],[8,9],[1,5],[1,5]]),
([v1,v2,v5,v3,v6],[12,42,11,43,8,0,9],[8,6],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[6,0,3],[0,1],[5]]),
([v0,v1,v5,v7,v3],[14,8,44,32,45,27,35,46],[9,5],[[0,1],[2],[0,1,3],[0,4],[1,0,5],[6],[1,7],[0,1],[5,4,100],[3,7,101]]),
([v14,v0,v1,v2,v3],[0,8,44,14,3,45,16,35,47,26],[],[[0,1,2],[3],[1,0],[4,5,6],[1,6],[7,1,5],[7,5],[1,6],[1,6],[8,9]]),
([v0,v1,v5,v3,v9],[22,32,2,9,21,33,8],[8,2],[[0,1],[2],[0,3],[0,1],[4,1,100],[1,5],[6,5,101],[3,0,5],[0,1],[2]]),
([v0,v1,v2,v3,v15],[22,32,12,9,48,24,28,1,49,50],[],[[0,1],[0,1],[0,2,3],[4],[2,5],[1,6],[7,1],[1,0,2],[8],[9]]),
([v16,v0,v1,v2,v3],[0,2,1,32,28,22,50,9,51,42],[],[[0,1],[2,3,4],[1,0],[5],[6,3],[6,3],[6,4,7],[8,9],[3,4],[3,4]]),
([v0,v1,v2,v6,v8],[18,11,45,52,46,39,19,12],[7,3],[[0,1],[0,2],[3],[0,1,2],[1,4],[1,0,4],[5],[6,2,100],[7,4,101],[0,1]]),
([v17,v0,v1,v2,v3],[0,11,52,18,2,45,46,16,53,29],[],[[0,1,2],[3],[4,5,6],[1,0],[1,7],[6,5],[6,1,5],[1,6],[1,6],[8,9]]),
([v0,v1,v2,v6,v9],[22,30,12,48,31,21,11,49],[6,2],[[0,1],[0,2],[3],[0,1],[1,4],[5,1,100],[6,4,101],[2,0,4],[7],[0,1]]),
([v18,v0,v1,v2,v3],[0,12,48,1,30,31,22,24,54,43],[],[[0,1,2],[3,4,5],[6],[1,0],[5,4],[1,7],[5,1,4],[1,5],[8,9],[1,5]]),
([v19,v0,v1,v2,v3],[8,14,35,3,31,45,30,46],[],[[0],[0,1,2],[1,0],[3,4,5],[1,6],[1,5],[1,5],[5,1,6],[5,7],[6,4]]),
([v0,v2,v7,v3,v8],[46,42,19,18,43,14,55,17,56],[4,0],[[0,1,2],[3,1,100],[0,4,1],[5,4,101],[6],[2,7],[2,0,1],[6,0,4],[2,1],[8]]),
([v0,v1,v7,v3,v9],[21,27,22,29,14,57,17,2],[4,1],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[5,0,3],[0,1],[7]]),
([v0,v1,v2,v3,v20],[21,27,19,42,43,0,58,59,56],[],[[0,1],[2,3],[1,4],[5,1],[0,1],[0,2,3],[6],[1,0,2],[7],[8]]),
([v21,v0,v1,v2,v3],[0,27,43,2,60,1,19,61,42,29],[],[[0,1,2],[2,3,4],[3,1,5],[6],[7,1],[2,8],[1,2],[2,1,7],[7,2,8],[1,9]]),
([v22,v0,v1,v2,v3],[11,18,39,2,46,45,30,33,38],[],[[0],[0,1,2],[3,4,5],[1,0],[1,6],[1,5],[1,5],[5,4],[5,1,4],[6,7,8]]),
([v0,v1,v2,v8,v9],[21,25,26,22,18,19,58,59],[0,1],[[0,1],[1,2],[3,1,100],[4,2,101],[0,5],[6],[0,1],[5,0,2],[7],[0,1]]),
([v23,v0,v1,v2,v3],[0,25,42,19,21,59,43,26],[],[[0,1,2],[2,3],[4],[3,4],[5,1],[1,2],[2,6],[3,2],[2,1,5],[1,7]]),
([v24,v0,v1,v2,v3],[42,1,33,30,0,49,22,45,31,62],[],[[0],[1,2,3],[4,2,5],[3,6],[2,3],[2,7],[6,3],[3,8],[7,2,9],[3,2,8]]),
([v25,v0,v1,v2,v3],[0,26,25,42,35,21,59,57,29,46],[],[[0,1,2],[3],[4,5,6],[2,1],[1,2],[2,1],[7,8],[5,9],[1,2],[2,1]])]
noncomputable def u4_D3 : List StD := [
([v4,v5,v7,v3],[1,14,44,35,42,45,63,64,26],[12,9,5],[[0,1,2],[1,3],[4,5,100],[0,1],[6,5,101],[7,8,102]]),
([v4,v2,v6,v8],[65,45,1,18,52,66,67,46],[13,7,3],[[0,1,100],[2,3,4],[3,1],[5,1,101],[6,7,102],[2,1,3]]),
([v26,v0,v1,v2],[0,45,46,50,26,68,69,25],[],[[0,1],[1,2],[3,4,5],[4,6,7],[2,1],[1,2]]),
([v27,v0,v1,v3],[0,25,26,36,46,70,71,45],[],[[0,1,2],[3,4,5],[2,1],[2,1],[4,6,7],[2,1]]),
([v1,v5,v6,v9],[72,42,73,30,74,2,0],[13,6,2],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([v28,v0,v2,v3],[0,30,45,46,75,26],[],[[0,1],[1,2,3],[3,2],[3,2],[3,1],[1,4,5]]),
([v0,v7,v8,v9],[76,26,77,25,78,2,1],[13,0,1],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([v29,v1,v2,v3],[0,25,26,46,45],[],[[0,1],[0,2],[0,3,4],[4,3],[2,1],[1,2]])]
def u4_D2 : List StD := []
theorem u4_I2 : LevelN u4_R u4_T 2 u4_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C3x0 : levelOK u4_T u4_K u4_P 2 (u4_D2.map Prod.fst) ((u4_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem u4_I3 : LevelN u4_R u4_T 3 u4_D3 := levelStep u4_B u4_W u4_Q u4_I2 (chunks 16 u4_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u4_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C4x0 : levelOK u4_T u4_K u4_P 3 (u4_D3.map Prod.fst) ((u4_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C4x1 : levelOK u4_T u4_K u4_P 3 (u4_D3.map Prod.fst) ((u4_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem u4_I4 : LevelN u4_R u4_T 4 u4_D4 := levelStep u4_B u4_W u4_Q u4_I3 (chunks 16 u4_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u4_C4x0
  · exact u4_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C5x0 : levelOK u4_T u4_K u4_P 4 (u4_D4.map Prod.fst) ((u4_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem u4_I5 : LevelN u4_R u4_T 5 u4_D5 := levelStep u4_B u4_W u4_Q u4_I4 (chunks 16 u4_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u4_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C6x0 : levelOK u4_T u4_K u4_P 5 (u4_D5.map Prod.fst) ((u4_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem u4_I6 : LevelN u4_R u4_T 6 u4_D6 := levelStep u4_B u4_W u4_Q u4_I5 (chunks 16 u4_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u4_C6x0
  ))
theorem u4_L : LowN u4_R u4_T 7 := lowSearch u4_B u4_I6 (by decide +kernel)

def u5_T : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def u5_R : List Nat := [0, 1, 2]
def u5_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem u5_B : baseOK u5_T u5_R u5_E = true := by decide +kernel
theorem u5_L : LowN u5_R u5_T 2 := lowCount u5_B (by decide +kernel)

def u6_T : Nat := 0x80808080808080808080808080808080
def u6_R : List Nat := [0, 1, 2]
def u6_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem u6_B : baseOK u6_T u6_R u6_E = true := by decide +kernel
theorem u6_L : LowN u6_R u6_T 2 := lowCount u6_B (by decide +kernel)

def u7_T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def u7_R : List Nat := [0, 1, 2]
def u7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem u7_B : baseOK u7_T u7_R u7_E = true := by decide +kernel
theorem u7_L : LowN u7_R u7_T 2 := lowCount u7_B (by decide +kernel)

def u8_T : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def u8_R : List Nat := [0, 1, 2, 3]
def u8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem u8_B : baseOK u8_T u8_R u8_E = true := by decide +kernel
theorem u8_S0 : SliceN u8_R u8_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) u8_B u5_B u5_L (by decide +kernel)
theorem u8_S1 : SliceN u8_R u8_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) u8_B u3_B u3_L (by decide +kernel)
theorem u8_S2 : SliceN u8_R u8_T (0x55555555555555555555555555555555,2,[1, 2, 3]) := mkSlice (w:=0) u8_B u6_B u6_L (by decide +kernel)
theorem u8_S3 : SliceN u8_R u8_T (0x33333333333333333333333333333333,2,[0, 2, 3]) := mkSlice (w:=0) u8_B u7_B u7_L (by decide +kernel)
theorem u8_S4 : SliceN u8_R u8_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S5 : SliceN u8_R u8_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) u8_B u1_B u1_L (by decide +kernel)
theorem u8_S6 : SliceN u8_R u8_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) u8_B u1_B u1_L (by decide +kernel)
theorem u8_S7 : SliceN u8_R u8_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) u8_B u1_B u1_L (by decide +kernel)
theorem u8_S8 : SliceN u8_R u8_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S9 : SliceN u8_R u8_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]) := mkSlice (w:=6) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S10 : SliceN u8_R u8_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) u8_B u1_B u1_L (by decide +kernel)
theorem u8_S11 : SliceN u8_R u8_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]) := mkSlice (w:=0) u8_B u7_B u7_L (by decide +kernel)
theorem u8_S12 : SliceN u8_R u8_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) u8_B u5_B u5_L (by decide +kernel)
theorem u8_S13 : SliceN u8_R u8_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S14 : SliceN u8_R u8_T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]) := mkSlice (w:=0) u8_B u7_B u7_L (by decide +kernel)
theorem u8_S15 : SliceN u8_R u8_T (0x330033003300330033003300330033,1,[0, 2]) := mkSlice (w:=0) u8_B u1_B u1_L (by decide +kernel)
theorem u8_S16 : SliceN u8_R u8_T (0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]) := mkSlice (w:=10) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S17 : SliceN u8_R u8_T (0xf000f000f000f000f000f000f000f000,1,[0, 1]) := mkSlice (w:=12) u8_B u0_B u0_L (by decide +kernel)
theorem u8_S18 : SliceN u8_R u8_T (0xf000f000f000f000f000f000f000f,1,[0, 1]) := mkSlice (w:=0) u8_B u1_B u1_L (by decide +kernel)
def u8_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0x55555555555555555555555555555555,2,[1, 2, 3]),(0x33333333333333333333333333333333,2,[0, 2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0x3030303030303030303030303030303,1,[0, 3]),(0x50505050505050505050505050505050,1,[1, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]),(0x55005500550055005500550055005500,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]),(0x330033003300330033003300330033,1,[0, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]),(0xf000f000f000f000f000f000f000f000,1,[0, 1]),(0xf000f000f000f000f000f000f000f,1,[0, 1])]
theorem u8_Y : ∀ s ∈ u8_Z, SliceN u8_R u8_T s := by
  unfold u8_Z
  simp only [List.forall_mem_cons]
  exact ⟨u8_S0,u8_S1,u8_S2,u8_S3,u8_S4,u8_S5,u8_S6,u8_S7,u8_S8,u8_S9,u8_S10,u8_S11,u8_S12,u8_S13,u8_S14,u8_S15,u8_S16,u8_S17,u8_S18,by simp⟩
def u8_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[])]
def u8_P : List (Nat × Nat) := [(4,5),(12,14),(2,3),(1,3),(10,14),(1,5),(6,14),(8,9),(1,9),(5,6),(0,3),(3,6),(0,5),(3,10),(0,9),(1,7),(1,11),(1,13)]
def u8_K : List CutV := u8_C.map (mkCut u8_Z)
theorem u8_W : ∀ c ∈ u8_K, CutP u8_R u8_T c := cutsGood u8_Y (by decide +kernel)
theorem u8_Q : u8_P.all (sepOK u8_T) = true := by decide +kernel
noncomputable def u8_D5 : List StD := [
([v0,v1,v2,v3],[],[0,1,2,3,4,5,6,7,8],[[100,101,102,103],[102,104,100,105],[100,106,107,108],[103,105,101,104],[103,108,101,106],[105,108,104,106]])]
noncomputable def u8_D4 : List StD := [
([v30,v0,v1,v2,v3],[0,1,2,3,4,5,6,7],[9],[[0],[1],[2],[2],[100,2,3],[2,4],[2,4],[3,5],[3,5],[6,7]]),
([v0,v1,v4,v2,v3],[0,1,3,5,2,4,8,9],[9],[[100,0,1],[2],[3,1],[3,1],[4],[5,0],[5,0],[0],[0],[6,7]]),
([v31,v0,v1,v2,v3],[3,1,2,4,0,9,10],[10,5],[[0],[1],[2,3],[2,3],[2,4,100],[2,3],[2,3],[3,4],[3,4],[101,5,6]]),
([v32,v0,v1,v2,v3],[0,2,4,5,3,1,8],[10,6],[[0],[1],[2,3],[2,3],[4,5,100],[3,2],[3,2],[2,3],[2,3],[6,101]]),
([v33,v0,v1,v2,v3],[9,2,4,8,11,5,7,6],[11],[[0],[1],[2],[1],[1,3],[100,1,4],[1,3],[3,5,6],[7,5],[3,6]]),
([v0,v1,v2,v5,v3],[7,8,9,4,6,2],[11],[[0,1],[100,2,3],[4],[0,1],[1,0],[0],[3,2],[5],[1,0],[0]]),
([v34,v0,v1,v2,v3],[6,2,8,4,9,7,10],[12,3],[[0],[1,2],[3],[1,2],[1,2],[1,4,100],[1,2],[2,5],[101,4,6],[2,4]]),
([v35,v0,v1,v2,v3],[9,8,7,2,6,4],[12,6],[[0],[1,2],[3],[1,2],[2,1],[4,5,100],[2,1],[1,2],[4,101],[1,2]]),
([v36,v0,v1,v2,v3],[12,2,4,13,14,15,7,5,10],[13],[[0],[1],[1],[2],[1,3],[1,3],[100,1,4],[5,6,7],[3,7,8],[3,6,8]]),
([v0,v1,v2,v3,v6],[10,8,4,12,14,16,13,2],[13],[[0,1],[0,2],[100,3,1],[4],[1,5,2],[2,0,6],[0],[1,0,6],[0],[7]]),
([v37,v0,v1,v2,v3],[14,2,13,4,12,7],[14,3],[[0],[1,2],[1,2],[3],[1,2],[1,2],[1,4,100],[101,5],[2,4],[2,4]]),
([v38,v0,v1,v2,v3],[12,14,10,2,13,4],[14,4],[[0],[1,2],[1,2],[3],[2,4],[2,4],[1,5,100],[5,101],[1,2],[1,2]]),
([v0,v39,v1,v2,v3],[6,9,15,4,7,16,8],[14],[[0,1],[0,1],[0,1],[2,3,100],[4],[5],[0,1],[2,6],[0,1],[0,1]]),
([v0,v1,v2,v7,v3],[7,16,6,9,8,4],[2],[[0,1,2],[2,3],[2,1],[0,1,100],[0,1],[4],[2,3],[5],[2,0],[2,0]]),
([v40,v0,v1,v2,v3],[9,8,16,7,6,4],[2,15],[[0,100],[1],[2],[0],[3,0,4],[4,0],[3,5],[5,3,101],[4,0],[4,0]]),
([v41,v0,v1,v2,v3],[6,7,4,16,9,5,8],[0,15],[[0,100],[1],[2],[0],[0,3],[0,4],[5,3,6],[6,3,101],[0,4],[0,3,4]]),
([v0,v42,v1,v2,v3],[6,16,4,14,10,9],[12],[[0,1],[0,1],[0,2,100],[3,1],[4],[2,1],[5],[2,1],[0,3],[0,1,3]]),
([v0,v1,v2,v3,v8],[10,16,15,9,14,4],[2],[[0,1,2],[0,3,100],[2,1],[2,1],[2,1],[0,3],[4],[2,0],[2,0],[5]]),
([v43,v0,v1,v2,v3],[16,14,9,10,15,4],[2,16],[[0,100],[1],[0],[2],[3,0,4],[3,5],[4,0],[4,0],[5,3,101],[4,0]]),
([v44,v0,v1,v2,v3],[9,10,16,4,15,5,13],[7,16],[[0,100],[1],[2],[3],[4,0],[5,0,6],[4,2],[4,2],[6,0,101],[4,0,2]]),
([v0,v1,v45,v2,v3],[15,13,17,6,8,16,9],[10],[[0,1,100],[0,2],[3,1,2],[0,2],[1,2],[0,2,4],[1,2],[5],[6],[3,0]]),
([v0,v1,v2,v3,v9],[10,16,9,18,17,13,6],[10],[[0,1,100],[0,2,3],[3,1],[3,1],[3,1,4],[3,0],[3,0],[0,2],[5],[6]]),
([v46,v0,v1,v2,v3],[16,10,13,9,6,17,18],[0,17],[[0,100],[1],[2],[3],[1,0,4],[1,5,4],[6,0],[6,0,5],[4,1,6],[4,0,101]]),
([v47,v0,v1,v2,v3],[17,16,6,15,13,9,18],[7,17],[[0,100],[0],[1],[2],[3,4,5],[6,0],[3,0],[3,0,6],[4,0],[3,5,101]])]
noncomputable def u8_D3 : List StD := [
([v0,v1,v48,v3],[2,9,6,17,15,18],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1],[2,1]]),
([v49,v0,v1,v3],[2,13,17,18,16,8,10],[],[[0,1],[1,2,3],[1,4],[0,5],[0,5],[3,6]]),
([v0,v1,v2,v50],[2,16,15,17,6,18],[],[[0,1,2],[0,3,4],[0,1,2],[2,1],[4,3,5],[2,1]]),
([v51,v0,v1,v2],[2,16,18,17,6,10,15,13,5],[],[[0,1,2],[2,3,4],[4,5,6],[0,7],[0,7],[2,8,6]]),
([v0,v1,v52,v3],[6,13,16,2,5,18,17],[],[[0,1,2],[0,1,3],[4,2,5],[5,2,6],[0,4],[0,2,1]]),
([v11,v0,v1,v3],[2,13,17,18,16,7,8],[],[[0,1],[2,0,3],[1,4],[5,1],[5,2,6],[1,2]]),
([v0,v1,v53,v2],[15,13,16,18,5,17],[],[[0,1,2],[0,2],[3,1,4],[1,4,5],[0,2],[0,2]]),
([v13,v0,v1,v2],[2,8,17,18,13,16,10],[],[[0,1],[2,0,3],[1,4,5],[6,1],[6,2,4],[1,2]]),
([v0,v54,v2,v3],[2,13,9,18,16,17,8],[],[[0,1],[0,2,3],[0,4,3],[1,4,5],[1,2,5],[6,2]]),
([v55,v0,v2,v3],[2,16,8,17,13,4,10,15],[],[[0,1,2],[2,1,3],[4,3],[0,5],[0,2],[2,6,7]]),
([v0,v1,v2,v56],[2,8,17,18,10,13],[],[[0,1],[0,2,3],[0,1],[1,2],[3,2],[1,4,5]]),
([v57,v0,v1,v2],[2,8,13,10,5,15],[],[[0,1],[2,3],[1,3,2],[0,1],[0,2],[1,4,5]]),
([v0,v58,v2,v3],[2,8,6,13,17,15,9],[],[[0,1],[2,3,4],[5,1,4],[1,0],[2,4,3],[1,6]]),
([v14,v0,v2,v3],[2,13,8,10,5,9],[],[[0,1],[2,0],[1,3],[4,1],[4,2],[1,5,2]]),
([v0,v1,v2,v59],[15,13,9,18,8,2,17],[],[[0,1,2],[3,1,2],[0,4,5],[0,6,3],[1,2,6],[0,2,4]]),
([v16,v0,v1,v2],[2,8,10,9,13,17],[],[[0,1],[2,3,4],[1,0],[2,1],[2,3,4],[1,5]]),
([v0,v60,v2,v3],[2,9,13,16,18,17],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1,5],[2,1,3]]),
([v61,v0,v2,v3],[2,13,18,17,4,10],[],[[0,1],[2,3],[1,3],[0,1],[0,4],[1,5]]),
([v0,v1,v62,v3],[2,13,17,18,10],[],[[0,1],[0,1],[0,2,3],[3,2],[1,2],[1,4]]),
([v63,v0,v1,v3],[2,17,18,16,4,13,8,10],[],[[0,1,2],[2,3,4],[4,3],[0,5],[0,6],[2,7]]),
([v0,v64,v2,v3],[2,18,10,17,13,15],[],[[0,1],[2,3,4],[5,3],[1,3],[1,0],[4,2]]),
([v17,v0,v2,v3],[2,13,18,17,10,5,8],[],[[0,1],[2,3],[1,0],[4,1],[5,3,6],[1,4]]),
([v0,v1,v65,v3],[10,8,17,18,13],[],[[0,1],[0,2,3],[3,1,2],[1,2],[3,0],[1,0,4]]),
([v18,v0,v1,v3],[2,13,17,8,10,7],[],[[0,1],[2,3],[1,0],[4,1],[5,2,3],[1,2]]),
([v0,v39,v7,v3],[18,9,6,17],[15],[[0,1],[2,1],[0,3],[100],[2,1],[0,1,2]]),
([v0,v1,v2,v66],[10,9,6,2,17,8,15,16],[],[[0,1,2],[0,1,2],[3,4,5],[6,4,7],[2,0,1],[2,0,1]]),
([v0,v1,v2,v67],[15,9,6,17,18],[],[[0,1],[2,1],[0,3],[0,3,4],[2,1],[0,1,2]]),
([v0,v1,v2,v68],[10,9,6,2,17,18],[],[[0,1,2],[0,1,2],[3,4,5],[5,4],[2,0,1],[2,0,1]]),
([v0,v1,v69,v2],[6,9,2,8,16,15],[],[[0,1],[2,3],[0,1],[0,1],[3,4,5],[0,1]]),
([v0,v42,v2,v8],[6,16,9,15],[16],[[0,1],[0,2],[3,1],[3,1],[100],[0,1,3]]),
([v0,v1,v70,v3],[15,9,2,6,16],[],[[0,1],[2,1,3],[0,4],[0,4],[3,1],[0,1,3]]),
([v0,v1,v71,v3],[6,16,17,15,18],[],[[0,1],[0,2],[3,1],[3,1],[0,2,4],[0,1,3]]),
([v0,v1,v72,v3],[15,16,2,17,18],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3],[0,1]]),
([v0,v73,v1,v3],[2,9,18,15,16,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]]),
([v0,v1,v45,v9],[15,16,17,18],[17],[[0,1],[0,2],[3,1],[3,1,2],[0,2,3],[100]]),
([v0,v74,v2,v3],[2,16,6,17,18,9],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([v0,v75,v2,v3],[2,16,6,17,18,15],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([v0,v76,v2,v3],[2,16,15,18,17],[],[[0,1,2],[3,4],[2,1],[2,1],[3,4],[2,1]]),
([v0,v77,v2,v3],[2,9,15,18,17,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]])]
def u8_D2 : List StD := []
theorem u8_I2 : LevelN u8_R u8_T 2 u8_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C3x0 : levelOK u8_T u8_K u8_P 2 (u8_D2.map Prod.fst) ((u8_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C3x1 : levelOK u8_T u8_K u8_P 2 (u8_D2.map Prod.fst) ((u8_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C3x2 : levelOK u8_T u8_K u8_P 2 (u8_D2.map Prod.fst) ((u8_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem u8_I3 : LevelN u8_R u8_T 3 u8_D3 := levelStep u8_B u8_W u8_Q u8_I2 (chunks 16 u8_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u8_C3x0
  · exact u8_C3x1
  · exact u8_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C4x0 : levelOK u8_T u8_K u8_P 3 (u8_D3.map Prod.fst) ((u8_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C4x1 : levelOK u8_T u8_K u8_P 3 (u8_D3.map Prod.fst) ((u8_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem u8_I4 : LevelN u8_R u8_T 4 u8_D4 := levelStep u8_B u8_W u8_Q u8_I3 (chunks 16 u8_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u8_C4x0
  · exact u8_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u8_C5x0 : levelOK u8_T u8_K u8_P 4 (u8_D4.map Prod.fst) ((u8_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem u8_I5 : LevelN u8_R u8_T 5 u8_D5 := levelStep u8_B u8_W u8_Q u8_I4 (chunks 16 u8_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u8_C5x0
  ))
theorem u8_L : LowN u8_R u8_T 6 := lowSearch u8_B u8_I5 (by decide +kernel)

def u9_T : Nat := 0xa880a880a880a880a880a880a880a880
def u9_R : List Nat := [0, 1, 2, 3]
def u9_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem u9_B : baseOK u9_T u9_R u9_E = true := by decide +kernel
theorem u9_S0 : SliceN u9_R u9_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) u9_B u2_B u2_L (by decide +kernel)
def u9_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3])]
theorem u9_Y : ∀ s ∈ u9_Z, SliceN u9_R u9_T s := by
  unfold u9_Z
  simp only [List.forall_mem_cons]
  exact ⟨u9_S0,by simp⟩
def u9_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u9_P : List (Nat × Nat) := []
def u9_K : List CutV := u9_C.map (mkCut u9_Z)
theorem u9_W : ∀ c ∈ u9_K, CutP u9_R u9_T c := cutsGood u9_Y (by decide +kernel)
theorem u9_Q : u9_P.all (sepOK u9_T) = true := by decide +kernel
noncomputable def u9_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u9_D3 : List StD := []
theorem u9_I3 : LevelN u9_R u9_T 3 u9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u9_C4x0 : levelOK u9_T u9_K u9_P 3 (u9_D3.map Prod.fst) ((u9_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u9_I4 : LevelN u9_R u9_T 4 u9_D4 := levelStep u9_B u9_W u9_Q u9_I3 (chunks 16 u9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u9_C4x0
  ))
theorem u9_L : LowN u9_R u9_T 5 := lowSearch u9_B u9_I4 (by decide +kernel)

def u10_T : Nat := 0xeaa8a880eaa8a880eaa8a880eaa8a880
def u10_R : List Nat := [0, 1, 2, 3, 4]
def u10_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem u10_B : baseOK u10_T u10_R u10_E = true := by decide +kernel
theorem u10_S0 : SliceN u10_R u10_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[1, 2, 3, 4]) := mkSlice (w:=1) u10_B u4_B u4_L (by decide +kernel)
theorem u10_S1 : SliceN u10_R u10_T (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]) := mkSlice (w:=2) u10_B u8_B u8_L (by decide +kernel)
theorem u10_S2 : SliceN u10_R u10_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]) := mkSlice (w:=4) u10_B u8_B u8_L (by decide +kernel)
theorem u10_S3 : SliceN u10_R u10_T (0xff00ff00ff00ff00ff00ff00ff00ff00,6,[0, 1, 2, 4]) := mkSlice (w:=8) u10_B u8_B u8_L (by decide +kernel)
theorem u10_S4 : SliceN u10_R u10_T (0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3]) := mkSlice (w:=16) u10_B u8_B u8_L (by decide +kernel)
theorem u10_S5 : SliceN u10_R u10_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) u10_B u9_B u9_L (by decide +kernel)
theorem u10_S6 : SliceN u10_R u10_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) u10_B u9_B u9_L (by decide +kernel)
theorem u10_S7 : SliceN u10_R u10_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) u10_B u9_B u9_L (by decide +kernel)
theorem u10_S8 : SliceN u10_R u10_T (0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]) := mkSlice (w:=0) u10_B u9_B u9_L (by decide +kernel)
theorem u10_S9 : SliceN u10_R u10_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,4,[1, 3, 4]) := mkSlice (w:=1) u10_B u2_B u2_L (by decide +kernel)
theorem u10_S10 : SliceN u10_R u10_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,2,[0, 3, 4]) := mkSlice (w:=6) u10_B u5_B u5_L (by decide +kernel)
theorem u10_S11 : SliceN u10_R u10_T (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) u10_B u5_B u5_L (by decide +kernel)
theorem u10_S12 : SliceN u10_R u10_T (0x330033003300330033003300330033,2,[0, 2, 4]) := mkSlice (w:=0) u10_B u6_B u6_L (by decide +kernel)
theorem u10_S13 : SliceN u10_R u10_T (0xcc000000cc000000cc000000cc000000,1,[0, 2]) := mkSlice (w:=26) u10_B u0_B u0_L (by decide +kernel)
theorem u10_S14 : SliceN u10_R u10_T (0xc000c000c000c000c000c000c000c000,1,[0, 4]) := mkSlice (w:=14) u10_B u0_B u0_L (by decide +kernel)
theorem u10_S15 : SliceN u10_R u10_T (0x3030303030303030303030303030303,2,[0, 3, 4]) := mkSlice (w:=0) u10_B u6_B u6_L (by decide +kernel)
theorem u10_S16 : SliceN u10_R u10_T (0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]) := mkSlice (w:=22) u10_B u0_B u0_L (by decide +kernel)
def u10_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[1, 2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,6,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,4,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,2,[0, 3, 4]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(0x330033003300330033003300330033,2,[0, 2, 4]),(0xcc000000cc000000cc000000cc000000,1,[0, 2]),(0xc000c000c000c000c000c000c000c000,1,[0, 4]),(0x3030303030303030303030303030303,2,[0, 3, 4]),(0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3])]
theorem u10_Y : ∀ s ∈ u10_Z, SliceN u10_R u10_T s := by
  unfold u10_Z
  simp only [List.forall_mem_cons]
  exact ⟨u10_S0,u10_S1,u10_S2,u10_S3,u10_S4,u10_S5,u10_S6,u10_S7,u10_S8,u10_S9,u10_S10,u10_S11,u10_S12,u10_S13,u10_S14,u10_S15,u10_S16,by simp⟩
def u10_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[(0,0,1)]),(5,[]),(6,[]),(3,[(0,1,2)]),(4,[(0,1,2)]),(7,[]),(8,[]),(0,[(0,0,2)]),(2,[(0,1,2)]),(4,[(0,1,3)]),(0,[(0,0,3)]),(2,[(0,1,3)]),(3,[(0,1,3)]),(0,[(0,1,2)]),(1,[(0,1,2)]),(4,[(0,2,3)]),(0,[(0,1,3)]),(1,[(0,1,3)]),(3,[(0,2,3)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(2,[(0,2,3)]),(5,[(0,2,3)]),(0,[(0,0,1),(0,2,3)]),(6,[(0,2,3)]),(7,[(0,1,2)]),(8,[(0,1,2)]),(5,[(0,1,3)]),(0,[(0,0,2),(0,1,3)]),(8,[(0,1,3)]),(6,[(0,1,2)]),(7,[(0,2,3)]),(5,[(0,1,2)]),(0,[(0,0,3),(0,1,2)]),(7,[(0,1,3)]),(6,[(0,1,3)]),(8,[(0,2,3)]),(9,[(0,1,2)]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(9,[(0,0,1)]),(15,[]),(16,[]),(9,[(0,0,2)])]
def u10_P : List (Nat × Nat) := [(12,13),(4,7),(10,11),(6,7),(2,19),(9,11),(9,13),(3,7),(5,7),(5,13),(5,21),(3,19),(3,11),(9,25),(2,11),(22,30),(14,30),(2,7),(26,30),(18,19),(28,30),(20,21),(24,25)]
def u10_K : List CutV := u10_C.map (mkCut u10_Z)
theorem u10_W : ∀ c ∈ u10_K, CutP u10_R u10_T c := cutsGood u10_Y (by decide +kernel)
theorem u10_Q : u10_P.all (sepOK u10_T) = true := by decide +kernel
noncomputable def u10_D8 : List StD := [
([v0,v1,v2,v3,v78],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13],[[0,100,1,101],[0,102,2,100],[0,103,3,100],[0,100,4,104],[105,106,1,2,107],[108,109,1,3,105],[105,110,1,4,111],[107,112,2,3,106],[106,111,2,4,110],[109,110,3,4,113]])]
noncomputable def u10_D7 : List StD := [
([v0,v39,v1,v2,v3,v78],[5,6,1,2,7,8,9,3,10,4,11],[3,14,4,15,16,12,11],[[0,1,100],[0,1,2],[0,3,4],[0,100,5,101],[0,100,6,102],[1,3],[1,2],[1,5,7,8,103],[1,6,9,10,104],[1,2],[1,2],[1,2],[3,4],[3,4],[105,106,5,6,103]]),
([v0,v42,v1,v2,v3,v78],[12,10,1,6,13,3,14,2,7,4,11],[2,17,4,18,16,7,11],[[0,1,100],[0,2,3],[0,100,4,101],[0,1,5],[0,100,6,102],[1,2,5],[1,4,7,8,103],[1,2],[1,6,9,10,104],[2,3],[1,2,3],[2,3],[1,4,5],[105,106,4,6,103],[1,5]]),
([v0,v79,v1,v2,v3,v78],[15,11,1,6,16,17,4,2,7,3,10],[19,17,14,18,15,7,12],[[0,1,100],[0,2,3],[0,100,4,101],[0,100,5,102],[0,1,6],[1,2,6],[1,4,7,8,103],[1,5,9,10,104],[1,2],[2,3],[2,3],[1,2,3],[105,106,4,5,103],[1,4,6],[1,5,6]]),
([v0,v1,v45,v2,v3,v78],[18,19,10,2,7,3,20,1,6,4,11],[0,1,4,20,8,10,16],[[0,100,1,101],[0,2,100],[0,3,4],[0,2,5],[0,100,6,102],[2,1,7,8,103],[3,4],[2,1,5],[104,105,1,6,103],[2,3,5],[2,3],[2,6,9,10,106],[2,3,4],[3,4],[2,5]]),
([v0,v1,v80,v2,v3,v78],[21,22,11,2,7,23,4,1,6,3,10],[0,1,21,20,8,9,15],[[0,100,1,101],[0,2,102],[0,3,4],[0,102,5,100],[0,2,6],[2,1,7,8,103],[3,4],[104,105,1,5,103],[2,1,6],[2,3,6],[2,5,9,10,106],[2,3],[3,4],[2,3,4],[2,5,6]]),
([v0,v1,v2,v81,v3,v78],[24,25,26,11,3,10,4,1,6,2,7],[0,1,2,22,5,6,7,20,18],[[0,100,1,101],[0,102,2,100],[0,3,103],[0,4,5],[0,3,6],[104,105,1,2,106],[3,1,7,8,107],[4,5],[3,1,6],[3,2,9,10,108],[4,5],[3,2,6],[3,4,6],[3,4],[3,4,5]])]
noncomputable def u10_D6 : List StD := [
([v0,v39,v1,v2,v81,v3,v78],[27,24,28,25,29,26,30,8,31,9],[3,22],[[0,1,100],[0,2,3],[4,2,5],[6,2,101],[6,2,7],[8,2,9],[5],[3],[0,6],[0,7,6],[0,9,8],[3,0],[0,3],[0,3],[0,3],[4,5],[4,5],[4,5],[9],[7],[7,6]]),
([v0,v42,v1,v80,v2,v3,v78],[32,21,33,22,34,35,13,36,23,14],[2,21],[[0,1,100],[0,2,3],[4,2,101],[5,2,6],[7,2,8],[4,2,9],[8],[0,4],[0,6,5],[3],[0,9,4],[0,3],[0,3],[3,0],[0,3],[9],[4,8,7],[6],[5,6],[6,5],[4,8,7]]),
([v0,v79,v1,v45,v2,v3,v78],[37,18,38,19,39,40,16,17,41,20],[19,0],[[0,1,100],[0,2,3],[4,2,101],[5,2,6],[4,2,7],[8,2,9],[9],[0,4],[0,6,5],[0,7,4],[3],[0,3],[0,3],[0,3],[3,0],[7],[6],[4,9,8],[6,5],[5,6],[4,7]])]
noncomputable def u10_D5 : List StD := [
([v0,v1,v2,v3,v82,v78],[27,42,43,29,30,44,45,31,46,47],[],[[0,1,2],[3,2],[4,1,5],[6,1,2],[7,1,5],[0,8],[0,2],[0,4],[0,2],[1,2],[1,4],[1,2],[0,2],[0,9,4],[0,2]]),
([v0,v1,v2,v83,v3,v78],[32,48,47,35,49,36,34,46,50],[],[[0,1,2],[3,2],[4,1,2],[5,1,2],[6,1,7],[0,7],[0,1],[0,8],[0,2],[0,1],[1,7,5],[0,2,1],[1,5],[0,2],[5,2]]),
([v0,v1,v2,v84,v3,v78],[37,51,47,40,49,39,41,46,50],[],[[0,1,2],[3,2],[4,1,2],[5,1,2],[6,1,7],[0,7],[0,1],[0,8],[0,2],[0,1],[0,7,5],[1,2],[0,5],[1,2],[5,2]])]
def u10_D4 : List StD := []
theorem u10_I4 : LevelN u10_R u10_T 4 u10_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u10_C5x0 : levelOK u10_T u10_K u10_P 4 (u10_D4.map Prod.fst) ((u10_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem u10_I5 : LevelN u10_R u10_T 5 u10_D5 := levelStep u10_B u10_W u10_Q u10_I4 (chunks 16 u10_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u10_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u10_C6x0 : levelOK u10_T u10_K u10_P 5 (u10_D5.map Prod.fst) ((u10_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem u10_I6 : LevelN u10_R u10_T 6 u10_D6 := levelStep u10_B u10_W u10_Q u10_I5 (chunks 16 u10_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u10_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u10_C7x0 : levelOK u10_T u10_K u10_P 6 (u10_D6.map Prod.fst) ((u10_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem u10_I7 : LevelN u10_R u10_T 7 u10_D7 := levelStep u10_B u10_W u10_Q u10_I6 (chunks 16 u10_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u10_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u10_C8x0 : levelOK u10_T u10_K u10_P 7 (u10_D7.map Prod.fst) ((u10_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem u10_I8 : LevelN u10_R u10_T 8 u10_D8 := levelStep u10_B u10_W u10_Q u10_I7 (chunks 16 u10_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u10_C8x0
  ))
theorem u10_L : LowN u10_R u10_T 9 := lowSearch u10_B u10_I8 (by decide +kernel)

def u11_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def u11_R : List Nat := [0, 1, 2, 3]
def u11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem u11_B : baseOK u11_T u11_R u11_E = true := by decide +kernel
theorem u11_S0 : SliceN u11_R u11_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) u11_B u2_B u2_L (by decide +kernel)
def u11_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem u11_Y : ∀ s ∈ u11_Z, SliceN u11_R u11_T s := by
  unfold u11_Z
  simp only [List.forall_mem_cons]
  exact ⟨u11_S0,by simp⟩
def u11_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u11_P : List (Nat × Nat) := []
def u11_K : List CutV := u11_C.map (mkCut u11_Z)
theorem u11_W : ∀ c ∈ u11_K, CutP u11_R u11_T c := cutsGood u11_Y (by decide +kernel)
theorem u11_Q : u11_P.all (sepOK u11_T) = true := by decide +kernel
noncomputable def u11_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u11_D3 : List StD := []
theorem u11_I3 : LevelN u11_R u11_T 3 u11_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u11_C4x0 : levelOK u11_T u11_K u11_P 3 (u11_D3.map Prod.fst) ((u11_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u11_I4 : LevelN u11_R u11_T 4 u11_D4 := levelStep u11_B u11_W u11_Q u11_I3 (chunks 16 u11_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u11_C4x0
  ))
theorem u11_L : LowN u11_R u11_T 5 := lowSearch u11_B u11_I4 (by decide +kernel)

def u12_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def u12_R : List Nat := [0, 1, 2, 3]
def u12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem u12_B : baseOK u12_T u12_R u12_E = true := by decide +kernel
theorem u12_S0 : SliceN u12_R u12_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) u12_B u2_B u2_L (by decide +kernel)
def u12_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem u12_Y : ∀ s ∈ u12_Z, SliceN u12_R u12_T s := by
  unfold u12_Z
  simp only [List.forall_mem_cons]
  exact ⟨u12_S0,by simp⟩
def u12_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u12_P : List (Nat × Nat) := []
def u12_K : List CutV := u12_C.map (mkCut u12_Z)
theorem u12_W : ∀ c ∈ u12_K, CutP u12_R u12_T c := cutsGood u12_Y (by decide +kernel)
theorem u12_Q : u12_P.all (sepOK u12_T) = true := by decide +kernel
noncomputable def u12_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u12_D3 : List StD := []
theorem u12_I3 : LevelN u12_R u12_T 3 u12_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u12_C4x0 : levelOK u12_T u12_K u12_P 3 (u12_D3.map Prod.fst) ((u12_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u12_I4 : LevelN u12_R u12_T 4 u12_D4 := levelStep u12_B u12_W u12_Q u12_I3 (chunks 16 u12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u12_C4x0
  ))
theorem u12_L : LowN u12_R u12_T 5 := lowSearch u12_B u12_I4 (by decide +kernel)

def u13_T : Nat := 0x80008000800080008000800080008000
def u13_R : List Nat := [0, 1, 2, 3]
def u13_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem u13_B : baseOK u13_T u13_R u13_E = true := by decide +kernel
theorem u13_L : LowN u13_R u13_T 3 := lowCount u13_B (by decide +kernel)

def u14_T : Nat := 0x88808880888088808880888088808880
def u14_R : List Nat := [0, 1, 2, 3]
def u14_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem u14_B : baseOK u14_T u14_R u14_E = true := by decide +kernel
theorem u14_L : LowN u14_R u14_T 3 := lowCount u14_B (by decide +kernel)

def u15_T : Nat := 0xe8a8a880e8a8a880e8a8a880e8a8a880
def u15_R : List Nat := [0, 1, 2, 3, 4]
def u15_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem u15_B : baseOK u15_T u15_R u15_E = true := by decide +kernel
theorem u15_S0 : SliceN u15_R u15_T (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]) := mkSlice (w:=2) u15_B u8_B u8_L (by decide +kernel)
theorem u15_S1 : SliceN u15_R u15_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]) := mkSlice (w:=4) u15_B u8_B u8_L (by decide +kernel)
theorem u15_S2 : SliceN u15_R u15_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) u15_B u11_B u11_L (by decide +kernel)
theorem u15_S3 : SliceN u15_R u15_T (0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]) := mkSlice (w:=1) u15_B u2_B u2_L (by decide +kernel)
theorem u15_S4 : SliceN u15_R u15_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) u15_B u12_B u12_L (by decide +kernel)
theorem u15_S5 : SliceN u15_R u15_T (0xaaaa0000aaaa0000aaaa0000aaaa,4,[1, 2, 3]) := mkSlice (w:=1) u15_B u2_B u2_L (by decide +kernel)
theorem u15_S6 : SliceN u15_R u15_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) u15_B u12_B u12_L (by decide +kernel)
theorem u15_S7 : SliceN u15_R u15_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) u15_B u9_B u9_L (by decide +kernel)
theorem u15_S8 : SliceN u15_R u15_T (0xff000000ff000000ff000000ff000000,4,[0, 1, 2]) := mkSlice (w:=24) u15_B u2_B u2_L (by decide +kernel)
theorem u15_S9 : SliceN u15_R u15_T (0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]) := mkSlice (w:=0) u15_B u9_B u9_L (by decide +kernel)
theorem u15_S10 : SliceN u15_R u15_T (0x55555555555555555555555555555555,3,[1, 2, 3, 4]) := mkSlice (w:=0) u15_B u13_B u13_L (by decide +kernel)
theorem u15_S11 : SliceN u15_R u15_T (0x8080808080808080808080808080808,1,[3, 4]) := mkSlice (w:=3) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S12 : SliceN u15_R u15_T (0x33333333333333333333333333333333,3,[0, 2, 3, 4]) := mkSlice (w:=0) u15_B u14_B u14_L (by decide +kernel)
theorem u15_S13 : SliceN u15_R u15_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) u15_B u7_B u7_L (by decide +kernel)
theorem u15_S14 : SliceN u15_R u15_T (0x330033003300330033003300330033,2,[0, 2, 4]) := mkSlice (w:=0) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S15 : SliceN u15_R u15_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S16 : SliceN u15_R u15_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S17 : SliceN u15_R u15_T (0x330000003300000033000000330000,1,[0, 2]) := mkSlice (w:=16) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S18 : SliceN u15_R u15_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S19 : SliceN u15_R u15_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S20 : SliceN u15_R u15_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) u15_B u7_B u7_L (by decide +kernel)
theorem u15_S21 : SliceN u15_R u15_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S22 : SliceN u15_R u15_T (0x50005000500050005000500050005000,1,[1, 4]) := mkSlice (w:=12) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S23 : SliceN u15_R u15_T (0xf000f000f000f000f000f000f000f,2,[0, 1, 4]) := mkSlice (w:=0) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S24 : SliceN u15_R u15_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S25 : SliceN u15_R u15_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S26 : SliceN u15_R u15_T (0x50500000505000005050000050500000,1,[1, 3]) := mkSlice (w:=20) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S27 : SliceN u15_R u15_T (0x88888888888888888888888888888888,2,[2, 3, 4]) := mkSlice (w:=3) u15_B u3_B u3_L (by decide +kernel)
theorem u15_S28 : SliceN u15_R u15_T (0x880088008800880088008800880088,1,[2, 4]) := mkSlice (w:=3) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S29 : SliceN u15_R u15_T (0x3333000033330000333300003333,2,[0, 2, 3]) := mkSlice (w:=0) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S30 : SliceN u15_R u15_T (0x8888000088880000888800008888,1,[2, 3]) := mkSlice (w:=3) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S31 : SliceN u15_R u15_T (0x20202020202020202020202020202020,1,[3, 4]) := mkSlice (w:=5) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S32 : SliceN u15_R u15_T (0x40404040404040404040404040404040,1,[3, 4]) := mkSlice (w:=6) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S33 : SliceN u15_R u15_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S34 : SliceN u15_R u15_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) u15_B u7_B u7_L (by decide +kernel)
theorem u15_S35 : SliceN u15_R u15_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) u15_B u7_B u7_L (by decide +kernel)
theorem u15_S36 : SliceN u15_R u15_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S37 : SliceN u15_R u15_T (0x44004400440044004400440044004400,1,[2, 4]) := mkSlice (w:=10) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S38 : SliceN u15_R u15_T (0x44440000444400004444000044440000,1,[2, 3]) := mkSlice (w:=18) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S39 : SliceN u15_R u15_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]) := mkSlice (w:=5) u15_B u3_B u3_L (by decide +kernel)
theorem u15_S40 : SliceN u15_R u15_T (0xa000a000a000a000a000a000a000a0,1,[1, 4]) := mkSlice (w:=5) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S41 : SliceN u15_R u15_T (0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]) := mkSlice (w:=0) u15_B u6_B u6_L (by decide +kernel)
theorem u15_S42 : SliceN u15_R u15_T (0xa0a00000a0a00000a0a00000a0a0,1,[1, 3]) := mkSlice (w:=5) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S43 : SliceN u15_R u15_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S44 : SliceN u15_R u15_T (0xc000c000c000c000c000c000c000c000,1,[0, 4]) := mkSlice (w:=14) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S45 : SliceN u15_R u15_T (0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]) := mkSlice (w:=22) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S46 : SliceN u15_R u15_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S47 : SliceN u15_R u15_T (0xaa000000aa000000aa000000aa00,1,[1, 2]) := mkSlice (w:=9) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S48 : SliceN u15_R u15_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S49 : SliceN u15_R u15_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) u15_B u1_B u1_L (by decide +kernel)
theorem u15_S50 : SliceN u15_R u15_T (0xaa000000aa000000aa000000aa0000,1,[1, 2]) := mkSlice (w:=17) u15_B u0_B u0_L (by decide +kernel)
theorem u15_S51 : SliceN u15_R u15_T (0x55000000550000005500000055000000,1,[1, 2]) := mkSlice (w:=24) u15_B u1_B u1_L (by decide +kernel)
def u15_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xaaaa0000aaaa0000aaaa0000aaaa,4,[1, 2, 3]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xff000000ff000000ff000000ff000000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]),(0x55555555555555555555555555555555,3,[1, 2, 3, 4]),(0x8080808080808080808080808080808,1,[3, 4]),(0x33333333333333333333333333333333,3,[0, 2, 3, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x330033003300330033003300330033,2,[0, 2, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x330000003300000033000000330000,1,[0, 2]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x300030003000300030003000300030,1,[0, 4]),(0x50005000500050005000500050005000,1,[1, 4]),(0xf000f000f000f000f000f000f000f,2,[0, 1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x50500000505000005050000050500000,1,[1, 3]),(0x88888888888888888888888888888888,2,[2, 3, 4]),(0x880088008800880088008800880088,1,[2, 4]),(0x3333000033330000333300003333,2,[0, 2, 3]),(0x8888000088880000888800008888,1,[2, 3]),(0x20202020202020202020202020202020,1,[3, 4]),(0x40404040404040404040404040404040,1,[3, 4]),(0x3030000030300000303000003030,1,[0, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4]),(0x44004400440044004400440044004400,1,[2, 4]),(0x44440000444400004444000044440000,1,[2, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]),(0xa000a000a000a000a000a000a000a0,1,[1, 4]),(0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]),(0xa0a00000a0a00000a0a00000a0a0,1,[1, 3]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xc000c000c000c000c000c000c000c000,1,[0, 4]),(0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]),(0x220022002200220022002200220022,1,[2, 4]),(0xaa000000aa000000aa000000aa00,1,[1, 2]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0xaa000000aa000000aa000000aa0000,1,[1, 2]),(0x55000000550000005500000055000000,1,[1, 2])]
theorem u15_Y : ∀ s ∈ u15_Z, SliceN u15_R u15_T s := by
  unfold u15_Z
  simp only [List.forall_mem_cons]
  exact ⟨u15_S0,u15_S1,u15_S2,u15_S3,u15_S4,u15_S5,u15_S6,u15_S7,u15_S8,u15_S9,u15_S10,u15_S11,u15_S12,u15_S13,u15_S14,u15_S15,u15_S16,u15_S17,u15_S18,u15_S19,u15_S20,u15_S21,u15_S22,u15_S23,u15_S24,u15_S25,u15_S26,u15_S27,u15_S28,u15_S29,u15_S30,u15_S31,u15_S32,u15_S33,u15_S34,u15_S35,u15_S36,u15_S37,u15_S38,u15_S39,u15_S40,u15_S41,u15_S42,u15_S43,u15_S44,u15_S45,u15_S46,u15_S47,u15_S48,u15_S49,u15_S50,u15_S51,by simp⟩
def u15_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(1,[(0,0,1)]),(3,[]),(4,[]),(5,[]),(6,[]),(1,[(3,0,1)]),(0,[(0,0,1)]),(0,[(3,0,1)]),(0,[(0,0,2)]),(1,[(0,0,2)]),(7,[]),(8,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(0,[(2,0,2)]),(1,[(2,0,2)]),(0,[(3,0,2)]),(1,[(3,0,2)]),(0,[(0,0,3)]),(1,[(0,0,3)]),(9,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(0,[(2,0,3)]),(1,[(2,0,3)]),(0,[(3,0,3)]),(1,[(3,0,3)]),(1,[(0,1,2)]),(1,[(2,1,2)]),(1,[(0,1,3)]),(1,[(2,1,3)]),(0,[(0,1,2)]),(0,[(2,1,2)]),(0,[(0,1,3)]),(0,[(2,1,3)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(0,[(3,2,3)]),(1,[(3,2,3)]),(0,[(2,0,1)]),(10,[]),(5,[(0,0,1)]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(3,[(0,0,1)]),(18,[]),(0,[(1,0,1)]),(19,[]),(3,[(3,0,1)]),(20,[]),(21,[]),(22,[]),(23,[]),(24,[]),(25,[]),(5,[(3,0,1)]),(26,[]),(27,[]),(8,[(0,0,1)]),(28,[]),(29,[]),(3,[(1,0,2)]),(30,[]),(31,[]),(8,[(0,0,2)]),(1,[(2,0,1)]),(8,[(0,1,2)]),(32,[]),(0,[(1,1,2)]),(33,[]),(0,[(1,1,3)]),(8,[(3,0,1)]),(1,[(1,0,1)]),(34,[]),(3,[(2,0,1)]),(35,[]),(36,[]),(37,[]),(5,[(2,0,1)]),(38,[]),(39,[]),(5,[(1,1,2)]),(40,[]),(41,[]),(42,[]),(43,[]),(5,[(2,0,2)]),(8,[(3,0,2)]),(5,[(2,1,2)]),(7,[(0,1,2)]),(1,[(2,1,2),(0,0,2)]),(0,[(2,1,2),(0,0,2)]),(44,[]),(4,[(0,1,2)]),(3,[(2,0,2)]),(3,[(2,1,2)]),(1,[(2,1,3),(0,0,3)]),(0,[(2,1,3),(0,0,3)]),(45,[]),(6,[(0,1,2)]),(46,[]),(0,[(3,1,2)]),(1,[(1,1,2)]),(8,[(2,1,2)]),(1,[(3,1,2)]),(0,[(3,1,3)]),(1,[(1,1,3)]),(1,[(3,1,3)]),(8,[(3,1,2)]),(5,[(0,0,2)]),(3,[(0,1,2)]),(1,[(0,1,2),(1,2,3)]),(9,[(0,2,3)]),(3,[(0,0,2)]),(1,[(0,1,3),(1,2,3)]),(9,[(2,0,1)]),(0,[(0,1,2),(1,2,3)]),(6,[(0,2,3)]),(6,[(2,2,3)]),(0,[(0,1,3),(1,2,3)]),(9,[(2,0,2)]),(0,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(47,[]),(48,[]),(49,[]),(5,[(0,1,2)]),(8,[(2,0,1)]),(0,[(0,0,1),(1,2,4)]),(1,[(0,0,1),(1,2,4)]),(0,[(0,0,1),(1,3,4)]),(1,[(0,0,1),(1,3,4)]),(0,[(0,0,1),(1,0,1)]),(0,[(0,0,1),(3,0,1)]),(0,[(3,0,1),(2,0,1)]),(1,[(2,0,1),(3,0,1)]),(0,[(2,0,1),(3,0,1)]),(1,[(3,0,1),(2,0,1)]),(1,[(3,0,1),(0,0,1)]),(0,[(0,0,1),(1,0,2)]),(0,[(0,0,1),(3,0,2)]),(0,[(0,0,1),(2,2,4)]),(1,[(0,0,1),(2,2,4)]),(0,[(0,0,1),(1,0,3)]),(0,[(0,0,1),(3,0,3)]),(0,[(0,0,1),(1,1,3)]),(0,[(0,0,1),(3,1,3)]),(1,[(0,0,1),(2,3,4)]),(0,[(0,0,1),(2,3,4)]),(0,[(3,0,1),(0,0,1)]),(0,[(3,0,1),(1,1,2)]),(0,[(3,0,1),(1,1,3)]),(0,[(2,1,3),(3,0,1)]),(8,[(0,0,2),(0,1,2)]),(3,[(1,0,1)]),(5,[(1,0,1)]),(5,[(3,0,2)]),(3,[(3,0,2)]),(8,[(2,0,2)]),(1,[(2,1,3),(3,0,1)]),(0,[(1,0,1),(0,0,1)]),(0,[(1,0,1),(3,0,1)]),(0,[(0,0,1),(2,0,1)]),(0,[(2,0,1),(0,0,1)]),(0,[(0,1,2),(2,0,1)]),(0,[(0,1,3),(2,0,1)]),(5,[(3,1,2)]),(3,[(3,1,2)]),(0,[(0,0,2),(0,1,4)]),(0,[(0,0,2),(0,1,2)]),(8,[(1,1,2)]),(0,[(0,1,2),(2,0,2)]),(1,[(0,0,2),(2,1,2)]),(0,[(2,1,2),(2,0,2)]),(0,[(0,0,2),(2,1,2)]),(0,[(1,0,2),(0,1,4)]),(50,[]),(0,[(0,1,3),(2,0,3)]),(0,[(0,0,3),(0,1,3)]),(0,[(0,0,3),(0,1,4)]),(1,[(0,0,3),(2,1,3)]),(0,[(2,1,3),(2,0,3)]),(0,[(0,0,3),(2,1,3)]),(0,[(1,0,3),(0,1,4)]),(0,[(1,0,1),(0,2,4)]),(0,[(1,0,1),(0,3,4)]),(0,[(1,1,2),(2,1,2)]),(0,[(0,1,2),(1,1,2)]),(0,[(3,1,2),(0,1,2)]),(0,[(2,1,2),(3,1,2)]),(0,[(1,1,3),(2,1,3)]),(0,[(0,1,3),(1,1,3)]),(0,[(3,1,3),(0,1,3)]),(0,[(2,1,3),(3,1,3)]),(0,[(2,1,2),(3,1,3)]),(0,[(1,2,3),(0,1,2)]),(0,[(2,1,2),(2,2,3)]),(0,[(0,1,3),(3,2,3)]),(0,[(2,1,3),(0,1,2)]),(0,[(2,1,3),(3,1,2)]),(0,[(1,2,3),(0,1,3)]),(0,[(2,1,3),(3,2,3)]),(0,[(0,1,2),(2,2,3)]),(0,[(1,2,3),(2,1,2)]),(0,[(0,0,1),(3,2,4)]),(0,[(0,0,1),(3,3,4)]),(8,[(0,0,1),(1,2,3)]),(0,[(1,0,1),(3,0,3)]),(8,[(1,0,2)]),(8,[(1,0,1)]),(0,[(0,0,1),(3,1,2)]),(3,[(0,0,1),(1,0,1)]),(8,[(0,1,2),(1,1,2)]),(5,[(0,0,1),(1,0,1)]),(0,[(1,0,2),(0,3,4)]),(0,[(1,0,3),(0,2,4)]),(0,[(1,0,3),(3,2,4)]),(5,[(1,0,1),(0,0,1)]),(3,[(1,0,1),(0,0,1)]),(3,[(0,0,1),(1,2,3)]),(5,[(0,0,1),(1,2,3)]),(5,[(0,0,1),(2,2,3)]),(0,[(2,1,2),(1,2,3)]),(0,[(0,1,2),(3,3,4)]),(0,[(1,0,2),(3,1,4)]),(8,[(0,1,2),(0,0,3)]),(0,[(1,0,1),(3,2,4)]),(3,[(0,0,1),(2,2,3)]),(51,[]),(8,[(0,1,2),(3,0,3)])]
def u15_P : List (Nat × Nat) := [(12,13),(28,30),(5,7),(10,11),(26,30),(3,7),(6,7),(22,30),(3,11),(14,30),(18,19),(3,19),(9,11),(9,13),(5,13),(5,21),(20,21),(1,7),(1,19),(4,7),(7,14),(6,30),(8,11),(2,11),(17,19),(17,21),(7,22),(16,19),(2,19),(3,27),(4,13),(8,13),(1,11),(1,13),(4,21),(1,21),(2,7),(6,15),(6,23),(18,30),(10,30),(20,30),(12,30),(11,14),(24,30),(25,30),(3,15),(9,15),(3,23),(7,9),(8,30)]
def u15_K : List CutV := u15_C.map (mkCut u15_Z)
theorem u15_W : ∀ c ∈ u15_K, CutP u15_R u15_T c := cutsGood u15_Y (by decide +kernel)
theorem u15_Q : u15_P.all (sepOK u15_T) = true := by decide +kernel
noncomputable def u15_D8 : List StD := [
([v0,v1,v2,v3,v78],[0,1],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[[100,101,0,102],[103,104,1,105],[106,107,100,108],[100,109,110,111],[112,113,0,1,101],[102,114,0,101],[102,115,0,101],[105,108,1,104],[105,111,1,104],[108,111,107,109]])]
noncomputable def u15_D7 : List StD := [
([v30,v0,v1,v2,v3,v78],[0,2,3,4,5,6,7],[13,5,14,8,15,11,0,4,16,7,9,1],[[0],[0,1],[100,2,101],[3,102,4,103],[5,104,6,105],[0,1,106],[107,1,2,100],[3,108,109,106,1],[5,106,110,108,1],[0,100,2],[0,3,102,111],[0,5,104,111],[3,103,2,100,101],[5,105,2,107,100],[3,5,102,109,110]]),
([v32,v0,v1,v2,v3,v78],[0,2,1,5,4,7,6,8],[1,4,7,9,0,12,17,18,8,11],[[0],[0,1,100],[1,2,101],[1,3,102,4],[1,5,103,6],[0,1,104],[1,101,7],[1,4,102],[1,6,103],[0,105,7,106],[0,4,105],[0,6,107],[4,7,101,108],[6,7,101,109],[4,6,102]]),
([v33,v0,v1,v2,v3,v78],[1,9,6,4,5,7],[12,2,8,14,11,15,1,3,10,7,9,4],[[0],[100,1,101],[0,2],[3,102,4,103],[2,104,5,105],[106,1,2,100],[0,2,107],[3,108,109,107,2],[2,107,110,108,3],[0,100,1],[3,103,1,100,101],[2,105,1,106,100],[0,3,102,111],[0,2,104,111],[2,3,102,109,110]]),
([v35,v0,v1,v2,v3,v78],[4,1,0,6,10],[1,4,7,9,3,13,17,14,15,11],[[0,1],[0,2,100],[0,1,101],[0,3,102],[0,3,103],[0,100,4],[0,1,104],[0,102,3],[0,3,103],[1,105,4,106],[0,4,100,107],[3,4,100,108],[0,1,105],[1,3,109],[0,3,102]]),
([v36,v0,v1,v2,v3,v78],[4,5,0,1,6,7,11,12,13,14],[12,13,16,19,10,20,7,6,5,15,11,21],[[0,1],[0,2,100],[0,3,101],[0,4],[0,5,4],[0,102,6,103],[0,104,7,102],[0,105,106,8],[0,107,9,102],[100,101,6,7,108],[0,6,100],[4,109,6,9,110],[0,7,101],[4,110,7,9,109],[0,106,4,111]]),
([v0,v1,v2,v3,v6,v78],[4,15,16,14,6,13,0,1,5],[0,22,3,20,12,13,5,7],[[0,100,1,101],[0,102,2,100],[0,103,3,4],[0,5],[0,3,100],[104,105,1,2,106],[0,1,3],[0,1,6],[3,4],[0,2,3],[0,2,7],[3,4],[0,107],[0,3,8],[0,3]]),
([v37,v0,v1,v2,v3,v78],[4,13,5,6,17,18,14],[0,22,3,7,23,12,13,5,15,11],[[0,1],[0,2],[0,2],[0,3],[0,2],[0,100,4,101],[0,102,5,100],[0,103,2,104],[0,6,100],[105,106,4,5,107],[0,2],[3,108,4,6,105],[0,2],[3,109,5,6,106],[0,2]]),
([v38,v0,v1,v2,v3,v78],[4,14,0,1,6,19,20,13],[1,4,7,9,16,10,23,12,13,14,15,8,11],[[0,1],[0,2,100],[0,3,101],[0,102],[0,1,103,4],[0,104,5,100],[0,105,6,101],[0,7,4,106],[0,4,103],[107,108,5,6,100],[0,5,100,109],[4,5,100,110],[0,6,101,111],[4,6,101,112],[0,4,103]]),
([v85,v0,v1,v2,v3,v78],[6,14,0,1,13,4,21,22,23],[24,25,0,19,3,6,26,9,5,14,8,21],[[0,1],[0,2,100],[0,3,101],[0,1,4],[0,5],[0,102,6,103],[0,104,7,102],[0,105,1,102],[0,106,107,8],[100,101,6,7,108],[5,109,1,6,110],[0,6,100],[5,110,1,7,109],[0,7,101],[0,107,5,111]]),
([v0,v1,v2,v3,v78,v86],[4,24,25,14,23,6,0,1,7],[16,27,10,26,12,13,5,9],[[0,100,1,101],[0,102,2,100],[0,100,3],[0,3,103],[0,4],[104,105,1,2,106],[0,1,3],[3,5],[0,1,6],[0,2,3],[3,5],[0,2,7],[0,3,8,5],[0,5],[0,3,107]]),
([v87,v0,v1,v2,v3,v78],[23,6,7,4,26,27,14],[16,27,10,9,28,12,13,5,14,2,8],[[0],[1,2],[1,2],[1,2],[1,3],[1,100,4,101],[1,102,5,100],[1,6,100],[0,1,103,2,104],[105,106,4,5,107],[3,108,4,6,109],[0,1,2],[3,110,5,6,107],[0,1,2],[0,1,2]]),
([v88,v0,v1,v2,v3,v78],[6,14,0,1,4,28,29,23],[1,4,7,9,0,3,28,12,13,14,15,8,11],[[0,1],[0,2,100],[0,3,101],[0,1,102,4],[0,103],[0,104,5,100],[0,105,6,101],[0,4,102],[0,7,4,106],[107,108,5,6,100],[4,5,100,109],[0,5,100,110],[4,6,101,111],[0,6,101,112],[0,4,102]]),
([v0,v39,v1,v2,v3,v78],[4,0,1,14,23],[3,6,0,12,13,7,8,9,10,11,24,25],[[100,101,0],[1,102,103],[2,100,104],[101,105,100,106],[100,107,108,109],[1,2],[1],[0,106,3,105],[4,109,3,107],[1,2],[1,110,103],[1,103,110],[2,111,104],[2,104,111],[106,109,105,107]]),
([v0,v42,v1,v2,v3,v78],[4,13,0,30,14,1,23],[3,0,28,4,9,24,17,14,2,5,11],[[0,1,100],[0,2,101],[0,100,3,101],[0,1,100],[0,100,4,102],[0,2,4],[0,3,5,103],[0,2],[0,4,104,6],[2,105,3,106],[0,2,107],[2,108,4,105],[0,3,103],[109,110,3,4,103],[0,104,107]]),
([v43,v0,v1,v2,v3,v78],[14,4,1,0,5,31],[6,5,11,1,22,3,4,14,9,12],[[0,1,100],[0,1],[0,2,101],[0,3],[0,4,102],[3,103,1,104],[105,106,1,5,100],[0,100,107],[0,108,1,100],[3,109,5,103],[0,3,107],[0,3,109],[0,101,5],[0,102,5,101],[0,102,4]]),
([v0,v79,v1,v2,v3,v78],[23,4,6,0,32,14,1],[10,0,4,7,12,17,2,15,5,8],[[0,1,100,2],[2,3,101],[2,100,4,101],[2,100,5,101],[0,2,100],[0,3,5],[0,4,6,102],[0,5,103,1],[0,3],[3,104,4,105],[3,106,5,104],[0,3,107],[108,109,4,5,102],[0,4,102],[0,103,107]]),
([v89,v0,v1,v2,v3,v78],[14,4,0,6,1,7,33],[6,5,8,1,0,3,4,7,15,24],[[0,1,100],[0,2,3],[0,4,101],[0,5,102],[0,2],[2,103,3,104],[105,106,3,6,100],[0,107,3,100],[0,100,108],[2,109,6,103],[0,2,109],[0,2,108],[0,102,6,101],[0,101,6],[0,102,5]]),
([v0,v1,v45,v2,v3,v78],[4,34,13,1,14,0,6],[0,19,3,28,1,25,17,2,15,9,8,5],[[0,100,1,101],[0,2,100],[0,3,102],[0,2,100],[0,100,4,103],[0,1,5,104],[3,105,1,106],[0,1,104],[107,108,1,4,104],[0,3,4],[0,3],[0,4,109,6],[0,3,110],[3,111,4,105],[0,109,110]]),
([v46,v0,v1,v2,v3,v78],[14,6,0,1,4,5,35],[6,2,15,0,1,4,3,8,9,13],[[0,1,100],[0,2,101],[0,3,4],[0,3],[0,5,102],[103,104,4,6,100],[3,105,4,106],[0,100,107],[0,108,4,100],[3,109,6,105],[0,101,6],[0,102,6,101],[0,3,107],[0,3,109],[0,102,5]]),
([v0,v1,v80,v2,v3,v78],[6,36,23,1,14,0,4],[0,19,16,3,1,13,17,2,14,7,5,11],[[0,100,1,101],[0,2,102],[0,3,103],[0,102,4,100],[0,2,102],[0,1,5,104],[3,105,1,106],[107,108,1,4,104],[0,1,104],[0,3,4],[0,4,109,6],[0,3],[3,110,4,105],[0,3,111],[0,109,111]]),
([v90,v0,v1,v2,v3,v78],[14,4,0,1,6,7,37],[6,2,14,0,1,4,3,7,11,25],[[0,1,100],[0,2,101],[0,3,4],[0,5,102],[0,3],[103,104,4,6,100],[3,105,4,106],[0,107,4,100],[0,100,108],[3,109,6,105],[0,102,6,101],[0,101,6],[0,3,109],[0,3,108],[0,102,5]]),
([v0,v1,v2,v81,v3,v78],[4,38,39,23,14,13,7,5],[0,19,3,12,13,5],[[0,100,1,101],[0,102,2,100],[0,3,4],[0,5,4],[0,3,4],[103,104,1,2,105],[0,1,4],[0,1,4],[3,1,4],[0,2,4],[0,2,4],[3,2,4],[0,6],[0,3,7],[0,3]]),
([v0,v1,v2,v3,v78,v91],[40,4,41,5,6,7],[0,1,2,3,4,7,6,9,12,13,5],[[100,101,0,1,102],[103,104,1,2,100],[1,3,105,4,106],[4,5,107,1,100],[3,106,1],[108,109,0,2,101],[1,102,0,3],[4,102,0,5],[3,102,0],[1,110,2,3],[4,109,2,5],[3,110,2],[1,4,5,3],[3,4],[1]]),
([v92,v0,v1,v2,v3,v78],[7,4,0,1,6,5,42,43,13,14],[3,12,13,0,5,15,11,29],[[0,1,100],[0,2,101],[0,3,102],[0,1,4],[0,5],[1,103,6,100],[1,100,7,103],[1,8,9],[0,1,100],[101,102,6,7,104],[1,6,9],[0,105,6,101],[1,7,9],[0,106,7,102],[0,1,107]]),
([v93,v0,v1,v2,v3,v78],[5,6,0,1,7,13,44,45,23,14],[10,24,25,0,5,14,8,29],[[0,1,100],[0,2,101],[0,3,102],[0,4],[0,1,5],[1,103,6,100],[1,100,7,103],[0,1,100],[1,8,9],[101,102,6,7,104],[0,105,6,101],[1,6,9],[0,106,7,102],[1,7,9],[0,1,107]])]
noncomputable def u15_D6 : List StD := [
([v94,v30,v0,v1,v2,v3,v78],[46,10,4,47,6,9,48,3,49,50,51,52,53],[],[[0],[0],[],[1],[2,3],[3,4],[5],[6],[7],[3,8],[3,8],[5,9],[3,7,10],[3,8],[3,8],[9,5],[9,5],[9,5],[8,7],[8,7],[11,12]]),
([v94,v0,v1,v2,v3,v78],[46,9,8,10,4,50,14,6,3,48,52,47,54,55,56,53,57],[22,3,10,12,14,18,8,13,11,9],[[0],[1,2],[3],[4,5,6],[7,5,6],[1,8,9,100],[1,8,9,101],[10,11,102,12,9,101],[12,11,101,13,14,102],[8,1,103],[14,1,104,15],[9,1,103,16,105],[10,8,106,12],[9,8,107,13,108],[9,10,104,16,15,109,108]]),
([v49,v30,v0,v1,v2,v3,v78],[58,10,6,9,4,59,49,60,3,61,62,63],[],[[0],[0,1],[2,0],[3],[4,5,6],[2,5,6],[1],[7],[8],[5,6],[5,6],[1,9],[8,1],[5,6],[5,6],[1,5],[9,1],[9,1],[6,5],[6,5],[10,11]]),
([v49,v0,v1,v2,v3,v78],[0,10,58,3,60,9,49,4,14,59,6,64,65,66,67,68,63],[22,3,10,12,14,18,5,8,11,9],[[0,1,2,3],[1,4,3],[3,5],[4,6,7,8,9],[10,6,8,9],[1,3,4,100],[3,101,1],[11,9,102,12,6,101],[12,9,101,13,4,102],[3,1,103],[4,1,104,12],[12,1,103,13,105],[4,3,106,107],[14,3,106,108],[14,4,104,15,16,109,108]]),
([v30,v0,v1,v2,v3,v50,v78],[15,4,52,69,14,53,70,49,63,17],[],[[0],[1],[2,3],[1,4],[1],[2,3],[0,1],[5,1],[2,0,6],[0,1],[5,1],[2,0],[1,0,5],[1],[2,0],[1,5],[2,3],[7,6,8],[9],[1,5],[2,3]]),
([v95,v30,v0,v1,v2,v3,v78],[11,4,70,3,71,15,6,53,17,52,72],[],[[0],[0],[1],[2,3,4],[5],[6,4,7],[8],[1],[7,4],[1,2],[7,2,4],[1,7],[7,1],[9,2],[7,1],[9,4],[1,2],[9,2,4],[1,2],[10,2],[1,7]]),
([v30,v0,v1,v2,v3,v78,v96],[24,73,72,69,6,14,57,70,49,71,26],[],[[0],[1],[2,3],[2,3],[4,5],[4],[0,2],[6,3],[6,3],[2,0,7],[0,2],[2,0],[2,0],[4,0,6],[4],[8,7,9],[2,6],[2,3],[2,6],[2,3],[10]]),
([v97,v30,v0,v1,v2,v3,v78],[21,6,70,3,74,4,72,24,26,53,52],[],[[0],[0],[1],[2,3,4],[5,4,6],[7],[8],[1],[6,4],[6,2,4],[1,2],[1,8],[9,1],[10,1,2],[6,2],[6,4],[6,2,4],[1,2],[10,2],[1,2],[1,9,10]]),
([v30,v33,v0,v1,v2,v3,v78],[9,46,4,1,49,57,6,53,75,3],[],[[0,1],[0],[2],[0,3],[2,4,5],[6,4,7],[1],[5,0],[2],[2,8,4],[4,8],[0,2],[2,5],[5,4],[7,2],[0,9],[2,0,7],[6,0,5],[2,7],[4,5,6],[2,5,6]]),
([v30,v33,v1,v2,v3,v78],[9,1,46,4,3,57,76,49,6,53,70,75],[3,14,23,11,28,0,8,15,9],[[0,1,2],[0,3],[0,1,4,100],[3,5,101,6,7,100,102],[8,9,100,6,7,103,104],[0,4,105],[3],[3,5,106,10,11,101],[8,7,103,10,11,107],[4,0],[3,0,101,9],[8,0,107,5],[3,4,106,9],[8,4,103,5],[8,3,101,5,9,108,103]]),
([v35,v30,v1,v2,v3,v78],[58,77,10,4,3,9,6,51,49],[30,16,0,3,11,28,31,14,15,9],[[0,1],[2,3,4],[4,3,5],[3,6,100,101],[3,6,101,102],[2,3],[4,7,103,2],[3,8,103,7],[6,8,104,7,105],[4,2,106],[3,2,107],[6,2,108],[3,4,106],[6,4,104],[3,6,109]]),
([v30,v0,v39,v2,v3,v78],[0,3,8,6,52,56,72,78,49,48,53,59,54,55,4,79,70,68,63],[12,14,32,11,18,1,31,16,30,0,8,9],[[0],[1,2,3],[1,4,100],[5,6,101,7,8,100,102],[9,4,100,7,8,103,104],[1,3,10,105,4],[1,5,106],[4,11,107,12,8,101,108],[6,11,109,13,5,103,107],[0],[5,6,14,10,15,105],[3,4,16,15,105],[4,1,110,12],[6,1,103,13],[6,4,101,17,18,111,103]]),
([v46,v30,v0,v1,v2,v3,v78],[14,70,4,62,0,80,6,53,35,1,49,54],[],[[0],[1,2,3],[1,4],[2],[5],[6,3,7],[8],[2],[7,9],[2,0],[3,0,10],[2,7],[7,2],[3,1],[7,1,2],[11,8],[2,1],[3,1,8],[2,1],[10,1,3],[2,7]]),
([v90,v30,v0,v1,v2,v3,v78],[14,70,6,81,0,49,82,37,57,1,55],[],[[0],[1,2,3],[1,4],[2],[5,3],[6],[7],[2],[8,9],[3,0,5],[2,0],[2,7],[8,2],[8,1,2],[3,1],[10,7],[3,1,5],[2,1],[5,1,3],[2,1],[2,8]]),
([v30,v0,v1,v2,v3,v78,v91],[40,83,53,41,57,4,6,70,55],[5],[[0],[1],[2,3,100],[4,1,5],[2,1,6],[1],[0,5],[2,5],[4,6],[2,5],[5,7],[8,0],[5,0,2],[6,0,4],[0,2],[5,2],[6,4],[100,2],[5,2],[6],[5]]),
([v0,v98,v1,v2,v3,v78],[9,8,6,4,64,3,75,14,49],[0,10,12,18,8,11,9],[[0,1],[0,2,100],[0,1,2],[3,101,2,100],[2,100,3,101],[0,4,5,1],[1,2],[3,6,7,8],[2,6,7,4],[1,0,102],[3,0,102],[2,0,103],[3,1,104],[2,1,105],[2,3,106]]),
([v32,v33,v1,v2,v3,v78],[84,46,9,6,3,76,4,85,8,75],[23,10,3,22,14,8,15,11,9],[[0,1],[2,3,4],[3,0,2],[3,5,100,6,101],[3,6,101,102],[2,7,103,8],[3],[6,9,104,7,105],[3,9,106,7,107],[7,2,103,8],[6,2,103],[3,2,106],[6,8,105],[3,8,107],[3,6,108]]),
([v94,v33,v0,v1,v2,v3,v78],[0,77,8,4,75,6,3,9,56,49,85,64,57,53],[],[[0],[1],[2],[],[3,4],[4,5],[6],[7],[8],[9,4],[9,4],[6,7,10],[6,11],[11,4,12],[13,4],[10,6],[4,7],[4,7],[9,4],[9,4],[11,12,13]]),
([v55,v33,v0,v1,v2,v3,v78],[0,1,9,3,4,49,75,8,86,87,79,88,89],[],[[0],[1,2],[3],[4,1],[4,5,6],[6,5],[7],[2],[8],[5,6],[5,6],[2,7],[7,9],[10,5],[10,5],[2,7],[6,2],[6,2],[5,6],[5,6],[11,12]]),
([v55,v0,v1,v2,v3,v78],[46,8,9,3,86,75,4,14,49,6,55,79,54,90,91,89],[0,3,10,13,2,14,15,8,11,9],[[0,1,2],[2,3],[1,4,2],[4,5,6,7,8],[9,5,7,8],[2,100,1],[1,2,4,101],[10,11,102,12,5,100],[12,11,100,10,4,102],[1,2,103],[4,2,104,105],[13,2,104,106],[4,1,107,12],[12,1,103,10,108],[13,4,105,14,15,109,106]]),
([v33,v0,v1,v2,v3,v56,v78],[16,53,92,93,4,14,64,76,75,89,18],[],[[0],[1,2],[3],[4,5],[4],[1,2],[1,2],[0,4],[6,0,7],[0,4],[1,2],[6,0],[4,1],[6,1],[8,7,9],[4,0,1],[4],[6,0],[10],[4,1],[6,1]]),
([v99,v33,v0,v1,v2,v3,v78],[4,12,76,9,94,16,6,49,18,64,53,95],[],[[0],[1],[2,3,4],[0],[5],[6,4,7],[8],[9,4],[0],[0,2],[7,2,4],[10,0],[0,8],[9,2],[10,0],[9,4],[0,2],[11,2],[0,2],[7,2,4],[0,10]]),
([v33,v0,v1,v2,v3,v78,v100],[25,57,92,6,14,95,76,75,94,27],[],[[0],[1,2],[3],[1,2],[3,4],[3],[1,2],[0,3],[1,2],[5,0,6],[0,3],[5,0],[7,6,8],[3,1],[5,1],[5,0],[3,0,1],[3],[3,1],[5,1],[9]]),
([v101,v33,v0,v1,v2,v3,v78],[22,76,9,96,6,49,25,27,53,64],[],[[0],[0],[1,2,3],[4],[5,3],[6],[7],[8,3],[4],[5,1,3],[4,1],[8,3],[4,7],[9,1],[8,1,5],[9,3],[9,1],[3,1],[5,1,3],[4,1],[3,8,9]]),
([v33,v0,v39,v1,v3,v78],[46,1,9,10,6,64,56,49,78,75,48,53,79,65,66,4,76,91,89],[12,13,8,33,15,11,4,10,23,3,14,9],[[0,1],[2,3,4],[2,5,100,101],[6,7,102,8,9,101,103],[10,5,101,8,9,104,105],[2,4,11,106,5],[2,6,100],[5,12,107,13,7,102,108],[13,12,109,14,6,104,107],[1],[6,7,15,11,12,106],[4,5,16,12,106],[5,2,110,13],[10,2,100,14,104],[10,5,102,17,18,111,104]]),
([v43,v33,v0,v1,v2,v3,v78],[14,76,6,88,64,1,9,53,46,10,4,75,65,31],[],[[0],[1,2,3],[4],[1,5],[6],[2,3,7],[8],[7,6],[9],[10,0],[3,0,11],[7,3,10],[10,7],[3,1],[7,1,10],[12,6,13],[10,1],[11,1,3],[10,1],[3,1,11],[3,7]]),
([v89,v33,v0,v1,v2,v3,v78],[14,76,4,97,32,75,9,46,57,10,6,66,33],[],[[0],[1,2,3],[4],[1,4],[2,3,5],[6],[7],[8,6],[9],[3,0,5],[10,0],[8,3,10],[10,8],[8,1,5],[3,1],[11,6,12],[5,1,3],[5,1,6],[3,1,5],[10,1],[3,8]]),
([v33,v0,v1,v2,v3,v78,v91],[41,57,40,4,14,6,53,76,66],[2],[[0],[1,2,100],[3],[1,4,3],[5,4],[4],[1,3],[0,3],[1,5],[6,3],[3,7],[8,0],[3,6],[5,1],[100,1],[3,0,6],[5,0,1],[0,1],[3,5],[5],[3]]),
([v102,v0,v1,v2,v3,v78],[0,10,58,4,9,55,49,14,75,6,3],[3,10,13,14,15,11,9],[[0,1,2,3],[1,3],[4,5,1],[3,6,7,8],[9,6,7,8],[1,3,10],[10,3,100],[3,101,9,100],[9,100,3,101],[10,1,102],[3,1,103],[9,1,104],[3,8,10,102],[9,8,10,105],[3,9,106]]),
([v61,v0,v1,v2,v3,v78],[17,83,11,4,55,1,89,6,75,14,88,62,13,54,98,91],[13,5,0,10,12,15,11,9],[[0,1,2],[2,3],[4,100,5,6,101],[3,2],[7,8,1,6,9],[2,3,102],[10,3,103,11,102],[2,1,3,102,12],[13,3,102,1,103],[104,2,100],[3,2,104],[14,2,104,1,105],[3,8,100],[13,10,100,1,8,105,106],[3,15,107,14]]),
([v63,v0,v1,v2,v3,v78],[14,99,58,12,66,94,4,6,88,62,13,65,49,100,68],[12,2,16,19,3,13,11,18,9],[[0,1,2,3],[4,100,2,5,101],[3,6],[6,3],[7,8,0,5],[9,6,102,8,103],[3,6,104],[3,1,6,104,10],[11,6,104,1,102],[3,105,100],[4,6,12,100],[11,9,100,1,8,106,107],[6,3,105],[13,3,105,1,106],[6,14,108,13]]),
([v0,v1,v2,v3,v103],[4,13,14,5,0,1],[16,6,10,12,13,2,5,15,11],[[0,100,101],[0,102,100],[0,1,2],[0,2,3],[103,104,105,106],[0,2],[2,107,4],[0,2],[2,108,5],[0,2,3]]),
([v104,v0,v1,v2,v3],[4,14,6,5,0,1,13],[15,11,0,6,3,12,13,2,5,8,14],[[0,1,2,3],[2,4,100],[2,5,101],[0,2,3],[0,102,103],[0,104,102],[0,6,2,102],[105,106,107,108],[0,109,110],[0,110,109]]),
([v36,v0,v39,v1,v2,v3,v78],[17,13,101,1,19,88,6,62,79,56,12,11,14],[12,13,6,20,9],[[0],[1],[2,0,100],[2,3,101],[4],[2],[5,6,102],[7,5],[5,7],[103,8,2],[8,9],[10],[11],[1,8,12],[5,8],[10,11],[2,8,100],[7,5],[2,8,101],[5,7],[2,104]]),
([v43,v36,v0,v1,v2,v78],[4,19,14,11,12,6,5,31,88,102],[5,11,32,33,14,16,10,6,12,13],[[0,1],[0,2,3],[0],[2,4,100],[2,5,101,6],[0,2],[0,1,3,102],[0,7,103],[0,2,104],[3,0,105],[8,0,106,9,105],[2,0,107],[108,3,9,109],[2,3,108],[2,8,100,9]]),
([v46,v36,v0,v1,v2,v78],[4,20,88,14,12,11,6,5,35,62,103],[2,15,32,8,16,19,10,6,13,12],[[0,1],[0,2,3,4],[3,5,100],[0],[3,6,101,7],[0,3],[0,8,102],[0,1,4,103],[0,3,103],[9,0,104,2,105],[2,0,106,4],[3,0,107],[4,108,10,109],[3,9,100,2],[3,2,108,4]]),
([v0,v39,v1,v2,v3,v6,v78],[65,6,104,54,48,19,78,16,15,4,56,17],[20],[[0,1,2],[3,2],[0,2],[100,0,4],[5],[0,6],[7],[8],[9,6],[1],[1,2,6],[7,0],[10,0],[0,5],[0,2,6],[10,3],[3,7],[3,2,6],[11],[4,2,10],[2]]),
([v0,v64,v1,v2,v3,v78],[15,4,62,14,6,54,1,89,5],[0,3,20,13,5],[[0,1],[0,1,100],[101,1,2,100],[1,102,3,4],[3,1,100],[0,1],[5,103,6,7,104],[0,1,3],[3,2,4],[0,103],[1,0,3],[3,0,4],[1,3],[3,4],[1,3,8]]),
([v0,v64,v2,v3,v78],[6,15,5,14,1,4],[0,3,20,12,13,5],[[0,100,1],[0,101,100],[0,2,102],[0,100,3],[103,104,4,105],[2,5],[0,3],[2,5],[0,3],[0,2,5]]),
([v0,v1,v65,v2,v3,v78],[4,88,9,16,5,6,14,65,94],[0,22,3,20,12,2],[[100,0,1,101],[1,0,2,3],[1,0,102,3],[0,103,4,5],[5,100,0,6],[7,104,8,2,105],[3,104],[0,4],[5,1,6],[0],[0,3,4],[5,6],[0,3,4],[5,3,6],[0,4]]),
([v0,v1,v65,v3,v78],[4,16,5,6,14,0],[0,3,20,12,13,2],[[0,100,101],[0,101,1],[0,102,2,3],[0,3,100,4],[103,104,105,5],[0,2],[3,4],[0,2],[3,4],[0,2]]),
([v0,v1,v2,v3,v105],[6,5,21,14,4],[0,6,3,12,13,2,5],[[0,100,101],[0,102,100],[0,1,101],[0,2,3,4],[103,104,105,106],[1,4],[0,2,3],[1,4],[0,3],[0,1,4]]),
([v106,v0,v1,v2,v3],[14,4,21,6,5],[0,3,20,12,13,2,5],[[0,1,2],[0,2,3],[0,3],[0,1,3,4],[1,100,101],[1,101,100],[0,1,102,3],[103,104,105,106],[0,1],[0,1]]),
([v37,v0,v39,v1,v2,v3,v78],[11,5,4,105,56,15,65,104,54,79,86,17,6,14,78],[23],[[0],[1,2],[3,0,4],[3,4],[5],[3,4],[6,2,7],[8,4,7],[6,4,7],[9,3,100],[6,4,9],[10],[11],[2,1],[12,7,13],[11,8],[4,3],[6,7,14],[4,3],[8,7,14],[4,3]]),
([v107,v0,v1,v2,v3,v78],[0,19,15,70,4,54,1,69,6,14,62,88,13,63,75,49],[13,5,0,10,14,15,11,9],[[0,1,2,3],[1,4],[5,100,6,7,101],[4,1],[8,7,9,10],[1,4,102],[11,4,103,10,102],[4,12,8,102],[5,4,102,3,103],[1,100,13],[4,1,104],[8,1,105],[4,14,100,15],[5,8,10,105,11,106],[4,8,107]]),
([v108,v0,v1,v2,v3,v78],[9,20,14,76,65,94,6,12,4,88,62,13,89,49,75],[12,2,16,19,3,11,18,8,9],[[0,1,2,3],[4,100,0,5,101],[1,6],[7,8,1],[6,5,2,9],[10,6,102,9,103],[1,6,104],[8,11,6,104],[4,6,104,8,102],[1,100,12],[5,8,13,100,14],[4,6,9,105,10,106],[8,1,107],[6,1,105],[6,8,108]]),
([v38,v0,v39,v1,v2,v3,v78],[15,4,56,1,11,88,62,48,86,19,14,20,75,49],[9,6,23],[[0],[1],[2,0],[2,3],[4],[2,100],[5,1,101],[6,2,5],[5,2,6],[5,7,102],[100,2],[8],[9],[1,10],[5,10,7],[9,11],[2,9,12],[6,5],[2,11,13],[5,6],[2,100]]),
([v109,v0,v1,v2,v3,v78],[26,83,21,6,54,1,89,4,75,79,14,97,62,106],[13,5,0,3,6,15,34,24,14,35,9],[[0,1,2],[2,3],[4,100,5,6,101],[7,8,1,9,10],[3,2],[2,3,102],[11,3,103,12,102],[12,3,104,1,102],[2,1,3,105,106],[107,2,100],[13,2,107,1,108],[3,2,105],[13,11,101,1,8,100],[3,8,105,109],[3,6,110,12,105]]),
([v110,v0,v1,v2,v3,v78],[27,88,22,65,0,63,6,4,49,14,79,81,107,99],[12,2,0,19,3,6,11,28,25,18,8,9],[[0,1,2],[3,100,4,5,101],[2,6],[7,8,9,10],[6,2],[11,5,102,1,6,103],[1,6,104,2],[1,6,105,3,102],[2,6,106,107],[2,108,100],[12,11,101,3,8,100],[3,6,1,106,109],[12,2,108,13,110],[6,2,106],[6,5,111,1,106]]),
([v0,v1,v2,v111,v78],[6,14,7,23,0,1],[0,6,3,12,13,2,5,14,8],[[0,100,101],[0,102,100],[0,1,2],[0,3,1],[103,104,105,106],[1,107,4],[0,1],[1,108,5],[0,1],[0,1,2]]),
([v112,v0,v1,v2,v78],[4,14,19,7,1,6,23],[14,8,0,6,3,28,12,13,2,5,11,15],[[0,1,2,3],[0,2,100],[0,4,101],[0,1,3,5],[0,102,103],[0,104,102],[0,5,6,105],[106,107,108,109],[5,110,111],[5,111,110]]),
([v85,v0,v39,v1,v2,v3,v78],[26,6,48,1,28,65,54,21,22,79,4,14,81,97],[24,25,6,26,9,21],[[0],[1],[2,0,100],[2,3,101],[2],[4],[5,1,102],[6,2,7],[5,2,8],[9,2],[103,9,5],[8],[7],[10,9,11],[1,9,11],[7,6],[12,5,7],[2,7,100],[13,6,8],[2,8,101],[2,104,105]]),
([v89,v85,v0,v1,v2,v3],[6,28,14,21,22,4,7,33,97,108],[5,8,18,35,15,0,3,6,24,13],[[0,1],[0,2,3],[0],[2,4,100],[2,5,101,6],[0,2],[0,1,3,102],[0,7,103],[0,2,104],[3,0,105],[8,0,106,9,105],[2,0,107],[108,3,9,109],[2,3,108],[2,8,100,9]]),
([v90,v85,v0,v1,v2,v3],[6,29,14,22,21,4,7,37,81,109],[2,14,18,11,0,19,3,6,25,12],[[0,1],[0,2,3],[2,4,100],[0],[2,5,101,6],[0,2],[0,7,102],[0,1,3,103],[0,2,103],[8,0,104,9,105],[3,0,106],[2,0,107],[3,108,9,109],[2,8,100,9],[2,3,108]]),
([v0,v39,v1,v2,v3,v78,v86],[66,4,110,55,78,56,28,86,24,6,48,1,26],[26],[[0,1,2],[3,2],[0,2],[0,4],[100,0,5],[6],[7],[8],[1,2,4],[9,4],[1],[8,3],[0,2,4],[10,0],[0,6],[3,2,4],[10,3],[3,11],[5,2,10],[2],[12]]),
([v0,v113,v1,v2,v3,v78],[24,4,81,6,14,55,1,69,7],[0,10,13,5],[[0,1],[0,1,100],[101,1,2,100],[1,101,3,4],[2,1,100,3,4],[0,1],[5,102,6,7,103],[1,4],[0,3,4],[0,102],[1,0,4],[3,0,4],[1,2,4],[3,4],[1,3,8]]),
([v0,v113,v2,v3,v78],[4,24,14,1,6,7],[0,10,12,13,5],[[0,100,1],[0,101,100],[0,101,2],[0,2,100],[102,103,3,104],[0,2],[2,4],[0,2],[2,4],[0,2,5,4]]),
([v0,v1,v114,v2,v3,v78],[6,97,9,25,4,14,65,94,7],[16,22,3,12,2],[[100,0,1,101],[1,0,2,3],[1,0,102,3],[4,100,0,5],[0,102,3,5],[6,103,7,2,104],[3,103],[4,1,5],[0,5],[0],[4,5],[0,3,5],[4,3,5],[0,3,5],[0,4,8]]),
([v0,v1,v114,v3,v78],[6,25,4,14,0,7],[16,3,12,13,2],[[0,100,101],[0,101,1],[0,2,100,3],[0,101,2,3],[102,103,104,4],[2,3],[0,3],[2,3],[0,3],[0,2,5]]),
([v0,v1,v2,v115,v78],[4,11,14,6,7],[16,6,10,12,13,2,5],[[0,100,101],[0,102,100],[0,1,2,3],[0,2,101],[103,104,105,106],[0,1,2],[2,3],[0,2],[2,3],[0,2,4,3]]),
([v116,v0,v1,v2,v78],[14,6,11,4,7],[30,23,12,13,2,5],[[0,1,2],[0,2,3],[0,3],[0,1,3,4],[1,100,101],[1,101,100],[0,1,100],[102,103,104,105],[0,1],[0,1]]),
([v87,v0,v39,v1,v2,v3,v78],[21,7,6,111,48,24,55,110,66,78,79,90,26,4],[28],[[0],[1,2],[3,0,4],[3,4],[3,4],[5],[6,2,7],[6,4,7],[8,4,7],[6,4,9],[10,3,100],[11],[12],[13,7,9],[2,1],[12,6],[8,7,9],[4,3],[6,7,9],[4,3],[4,3]]),
([v117,v0,v1,v2,v3,v78],[0,28,24,6,55,1,69,4,14,81,97,23,68,62,49],[13,5,0,3,6,28,14,15,11,7],[[0,1,2,3],[1,3],[4,100,5,6,101],[7,6,8,9],[3,1],[1,3,102],[10,3,103,9,102],[4,3,104,7,102],[3,11,7,105],[1,100,12],[7,1,106],[3,1,107],[4,7,9,100,10],[3,13,107,14,108],[3,7,109]]),
([v118,v0,v1,v2,v3,v78],[9,29,6,66,94,4,81,14,97,23,91,49,75],[12,2,0,19,3,6,28,11,18,8,7],[[0,1,2],[3,100,0,4,101],[1,2],[5,6,7,8],[2,1],[6,2,102,8,103],[1,2,104],[3,2,105,5,102],[2,9,5,106],[1,100,10],[3,5,8,100,6],[2,11,107,12,108],[5,1,109],[2,1,107],[2,5,110]]),
([v88,v0,v39,v1,v2,v3,v78],[24,6,48,1,21,97,81,56,90,28,14,29,75,49],[7,6,28],[[0],[1],[2,0],[2,3],[2,100],[4],[5,1,101],[6,2,5],[5,2,6],[100,2],[5,7,102],[8],[9],[5,10,7],[1,10],[9,11],[6,5],[2,9,12],[5,6],[2,11,13],[2,100]]),
([v94,v0,v39,v1,v2,v3,v78],[46,10,8,97,49,3,81,55,79,9,75,62],[9],[[0],[1],[2],[1],[3],[4],[3],[5,3,6],[3,5],[7,4,8],[3,4,7],[5],[9],[3,8],[4,8],[5,9],[6,3],[10,4],[3,5],[4,5],[3,100,11]]),
([v0,v39,v1,v119,v2,v3,v78],[110,6,48,10,79,49,90,46,58,1,84,75],[],[[0,1],[0,2],[3],[0,2],[4,2],[4,0,5],[6],[7],[8],[5,0],[1,4,5],[9,2,3],[8,10],[11,0],[2,4,11],[3,2,7],[0],[4],[5,0],[2,4,5],[2,0]]),
([v120,v0,v39,v1,v2,v3,v78],[9,58,1,79,75,110,85,51,77,46,112,104],[],[[0],[1],[2,0],[0,1,2],[3,4],[3,4],[5],[5,6],[5,7],[3,4],[3,4],[8],[9],[4,3],[4,3],[8,6],[4,3],[4,3],[6,3],[6,3],[10,5,11]]),
([v120,v0,v1,v2,v3,v78],[9,46,77,4,79,14,75,6,68,48,91,104,110,56,63,89],[1,19,4,36,6,8,37,11,38,12,14,9],[[0],[1,2],[0,1,2],[3,4,5,6],[7,4,5,6],[1,8,100,9,101],[2,10,102,9,103],[104,4,11,6,105,106],[104,4,12,6,107,108],[2,1,109],[13,1,110,14],[9,1,109,8,100],[13,2,105,15],[9,2,107,10],[9,13,105,8,11,111,107]]),
([v121,v0,v39,v1,v2,v3,v78],[58,9,3,48,79,56,97,81,8,10,75,49],[9],[[0],[1],[2],[1],[3,4],[5,4],[6,3],[7,3,6],[6,3,7],[4,3],[4,5],[8],[9],[5,4,6],[3,4,10],[8,9],[5,4,7],[3,4,10],[5,4,6],[3,4,11],[3,100,5]]),
([v0,v122,v39,v1,v2,v3,v78],[97,104,81,55,35,31,113,56,30,34,75,49],[],[[0,1],[0,1],[2,0],[0,1],[3,1],[0,3],[4],[5],[4],[6],[7,1],[8],[9],[0,7],[10,1],[8,9],[2,0],[10,1],[0,2],[11,1],[0,1,7]]),
([v0,v39,v1,v2,v3,v123,v78],[55,104,66,79,65,114,80,14,113,62,78,88,35],[],[[0,1],[0,1],[2,1],[0,1],[0,1],[3,0,4],[5],[6],[7,3],[8],[9,1],[5,2],[2,3,4],[2,4],[4,1,2],[0,3,10],[0,5,6],[11,0,1],[12],[9,1],[9,1]]),
([v124,v0,v39,v1,v2,v3,v78],[78,34,30,80,75,55,104,97,115,35,49,62],[6],[[0,100],[1],[2],[1],[3],[4],[5,6],[5,6],[7,6],[5,0],[7,0],[8],[9],[4,0],[4,0,6],[9,5],[4,0,7],[4,0,6],[5,0],[10,0,4],[7,6,11]]),
([v125,v0,v39,v1,v2,v3,v78],[104,65,80,1,34,62,55,116,113,4,79,56,54],[],[[0,1],[2],[3,1,2],[2,3],[4],[0],[1,0],[5,0],[1,0],[5,0],[1,6],[7],[8],[9,10],[5,0],[7,1],[11,1],[1,0,5],[6,7,12],[12,0,6],[5,0]]),
([v0,v126,v39,v1,v2,v3,v78],[55,110,65,37,33,75,117,32,36,6,49,48],[],[[0,1],[0,1],[0,1],[2,1],[0,2],[2,0],[3],[4],[3],[5,1],[6],[7],[8],[5,1],[5,9],[7,2],[5,1],[2,8,5],[0,1,10],[8,0,5],[11,1]]),
([v0,v39,v1,v2,v3,v78,v127],[55,104,65,118,82,97,14,79,117,81,78,54,110,37],[],[[0,1],[0,1],[2,1],[0,1],[2,0],[2,0],[3],[4],[5,6,7],[6,1],[8],[3,2],[9,2,4],[2,1,10],[2,3],[0,3,5],[11,0],[4,3],[5,1,12],[5,7],[13]]),
([v128,v0,v39,v1,v2,v3,v78],[78,36,32,110,82,55,65,115,37,81,75,54],[6],[[0,100],[1],[2],[1],[3],[4],[5,3],[5,3],[6,3],[5,0],[6,0],[7],[8],[9,0,3],[10,0],[8,5],[9,0,3],[6,0],[5,0],[11,0],[9,3]]),
([v129,v0,v39,v1,v2,v3,v78],[65,55,82,1,81,36,110,119,117,6,104,66,54],[],[[0,1],[2],[0,2,3],[2,3],[4],[5],[0,6],[1,6],[0,4],[1,0],[0,1],[7],[8],[4,6],[9,10],[7,0],[4,0,6],[0,8,11],[1,4,12],[12,1],[4,6]]),
([v0,v39,v1,v2,v81,v3,v78],[55,6,38,65,39,78,81,4,48,42,44,56],[6],[[0,1,100],[0,2],[3,4],[0,5],[0,3],[3,0],[4],[2],[1,5],[6,5,7],[1,5],[2,0],[3,2,5],[6,2],[3,2,5],[0,4,5],[0,4,5],[8,0],[9],[10],[11,6]]),
([v0,v39,v1,v2,v3,v78,v91],[55,6,104,65,41,40,4,14,66,78,54,110,44,42],[6],[[0,1,2],[0,2],[3,2],[0,2],[3,0],[100,0],[4],[5],[6,7],[1,2,7],[7],[4,3],[8,3],[3,2,8],[3,5],[0,4,9],[10,0],[0,4],[11,2],[12],[13]]),
([v92,v0,v39,v1,v2,v3,v78],[78,54,0,65,38,40,6,110,66,115,42,4,56],[29],[[0,1],[0],[0,2,3],[0,1],[4],[5],[1,6,7],[1,7],[3,7],[8,0],[1,0],[9],[10],[11,0],[6,0],[10,1],[8,0],[3,0],[12,0],[1,0],[12,7,100]]),
([v93,v0,v39,v1,v2,v3,v78],[78,66,1,55,40,38,6,104,54,90,44,4,48],[29],[[0,1],[0],[0,1],[0,2,3],[4],[5],[1,6,7],[3,7],[1,7],[1,0],[8,0],[9],[10],[11,0],[6,0],[10,3],[1,0],[12,0],[3,0],[8,0],[12,7,100]]),
([v130,v0,v1,v2,v3,v78],[4,66,81,35,14,30,6,104,75,13,65,120],[3,6,0,28,12,18,11,9],[[0,1,100,2,101],[3,1,4,5],[0],[0,2,4,3],[6,7,4,8],[2,0,102,3],[1,0,100,2,5],[0,9,100],[2,0,100,1,103],[1,3,104,5],[0,3,104],[10,3,104,1,105],[0,2,5,3],[5,106,11],[0,107,2]]),
([v46,v0,v42,v1,v2,v78],[14,121,4,80,35,30,5,13],[6,15,8,23,0,3,33],[[0,1,2,100],[2,0,3],[0,3,4,5],[2],[0,6,101],[2,7,102,103],[4,2,104],[5,2,105],[0,2,100],[0],[2,5,4],[0,2,102],[5,4,106],[0,4,101],[0,5,106]]),
([v0,v42,v1,v80,v2,v3,v78],[66,6,81,36,4,121,14,122,1,30],[3,16],[[0,1,100],[2,3],[0,4,101],[0,2],[0,5,6],[2,0],[6],[1,4],[7,8],[3],[1,6],[0,3],[0,3,9],[3,2],[5,0],[6],[2,6,4],[9],[7,2,6],[6,5],[2,7]]),
([v0,v42,v1,v2,v78,v91],[4,13,6,40,66,123,14,41,44],[3,0,6,39,13,2,5],[[0,1,2,100],[3,0,101],[4,0,100,5,101],[6,0,100],[6,0,102],[3,0,6],[0,5,7,103],[0,3,2],[6,0,8],[4,3,104,5],[6,3,105],[6,3,105],[6,104,5],[6,106,5],[0]]),
([v131,v0,v1,v2,v3,v78],[17,14,11,4,91,1,51,79,6,88,63,5],[5,13,1,10,6,12],[[0,1],[2,3],[4,100,5,6,101],[1,2,3],[1,7,8,6],[2,3,102],[9,3,103,104],[1,2,3,103],[1,3,104],[105,2,10,101],[1,2,3],[1,2,105],[1,3],[1,9,100,7],[1,3,11]]),
([v0,v1,v71,v2,v3,v78],[34,63,60,66,81,4,31,14,75,88,6,5],[0,6,3,12,14,5,11],[[0,1,100,2],[3,101,4,2,5,100],[3,102,4,2,6],[3,101,7,8],[4,1,100,3,2,7],[2,0,1,5],[3,0,103,1,6],[2,0,104,1],[7,0,103],[6,7],[0,2,4,5],[7,9,10,1],[0,6,7],[7,6,105],[4,2,104,7,11,106]]),
([v43,v0,v1,v45,v2,v78],[4,14,113,1,34,5,13,31],[6,11,0,3,32,14],[[0,1,100],[0],[0,1,2],[1,3,4],[1,5,101],[4,0,102],[0,6,102],[7,0,103],[1,0,100],[0,2,4,7],[7,4,104],[1,4,104],[1],[0,1,105],[1,7,101]]),
([v132,v0,v1,v2,v3,v78],[6,66,81,37,33,32,4,91,5,120,23,88],[3,6,0,11,28,12,2,18,8,7],[[0,1,100,2,101],[3,1,4,5],[0],[6,7,8,2],[0,5],[2,0,102,3],[1,0,100,2,5],[1,0,101,9,100],[0,10,103,104],[1,3,105,5],[1,2,106,3,9,105],[0,3,107],[5,108,9],[0,5,3],[0,109,11]]),
([v0,v79,v1,v45,v2,v3,v78],[124,4,55,34,6,65,32,33,5,125,14],[10,0],[[0,1,100],[2,3],[2,4,101],[5,6],[2,5],[0,2],[7],[0,1],[0,6],[0,8,1],[3],[5,3],[2,3],[9,3,5],[3,10],[10],[6],[0,10],[6,10],[0,2],[0,9]]),
([v90,v0,v79,v1,v2,v3],[14,125,6,82,37,32,7,23],[6,14,11,28,0,3,12,8],[[0,1,2,100],[2,0,3],[0,3,4,5],[2],[0,6,101],[2,7,102,103],[4,2,104],[5,2,105],[0,2,100],[0],[2,5,4],[0,2,102],[5,4,106],[0,4,101],[0,5,107]]),
([v0,v79,v1,v2,v3,v91],[23,4,6,40,65,126,14,41,42],[10,0,6,40,12,17,2,5],[[0,1,2,100],[3,2,101],[4,2,100,5,101],[6,2,100],[6,2,102],[3,0,6],[0,5,7,103],[0,3,1],[6,0,8],[4,3,104,5,105],[6,3,106],[6,3,106],[6,107,5],[6,107,5],[0]]),
([v133,v0,v1,v2,v3,v78],[26,14,21,127,6,91,1,51,4,97,63,75,7],[5,13,1,3,6,24],[[0,1],[2,3,4],[5,100,6,7,101],[1,5,8,7],[1,2,4],[2,4,102],[9,4,103,104],[1,4,104],[1,2,4,103],[105,2,10,101],[1,2,105],[1,2,4],[1,9,100,11],[1,4],[1,4,12]]),
([v0,v1,v134,v2,v3,v78],[36,68,67,65,81,6,33,14,75,97,4,7],[0,6,3,12,14,5],[[0,1,100,2],[3,101,4,2,5,100],[3,102,4,2,6],[7,1,101,2],[3,100,7,8],[2,0,1,5],[3,0,103,1,6],[7,0,104],[2,0,103,1,6],[6,7],[7,9,10,1],[0,2,6],[7,6,105],[0,6,7],[2,7,104,11]]),
([v89,v0,v1,v80,v2,v3],[14,122,6,117,1,36,7,23,33],[6,8,0,15,34,3,13,14],[[0,1,2,100],[2],[2,0,3],[0,4,5],[0,6,101],[5,2,102],[2,7,103,104],[8,2,105],[0,2,100],[2,3,5,8],[8,5,106],[0,5,107],[0],[0,2,103],[0,8,101]]),
([v135,v0,v1,v2,v3,v78],[4,81,97,35,115,34,23,75,88,7,31,13,54],[0,6,3,28,13,15,11,9],[[0,1,100,2,101],[0],[3,4,5],[0,2,3,1],[6,7,4,8,9],[1,0,100,2,5],[2,0,102,1,10],[0,11,100],[1,0,100,4,103],[10,5,104],[0,2,5,10],[5,105,4],[0,1,10,104],[12,8,104,4,7,10,106],[0,107,1]]),
([v0,v1,v45,v2,v78,v91],[55,4,128,13,6,41,129,40,130,45],[0,19,3,6,41,12,2,5],[[0,1,100,2,101],[0,1,3,4,100],[5,1,102],[6,1,100],[6,1,103],[1,2,7,104],[5,0,105,2],[6,105,2],[6,106,2],[5,1,8],[1,5,4],[6,1,9],[6,5,107],[6,5,107],[1]]),
([v136,v0,v1,v2,v3,v78],[18,14,63,0,85,12,4,23,62,91,79,5],[2,12,16,6,4,13],[[0,1],[2,100,3,4,101],[5,6],[1,5,4,6],[1,2,7,4],[8,2,102,6,103],[5,6,104],[1,5,4,102],[1,2,103,4],[4,105,2,5,9,101],[1,6],[1,8,100,10],[1,4,6],[1,4,105,2],[1,6,11]]),
([v0,v75,v1,v2,v3,v78],[55,88,4,35,86,89,30,14,75,23,5],[6,3,0,13,2,8,11],[[0,100,1,2,101],[0,102,1,3,4],[1,5,101,6,4],[0,100,7,8],[7,5,100,4],[3,7],[2,0,3],[2,3,6],[7,8,9,1],[6,0,103,3],[4,3,6,7],[7,3,104],[0,6,105,3],[7,1,103,6],[7,105,10,106]]),
([v137,v0,v1,v2,v3,v78],[6,55,88,37,36,4,75,14,97,33,115,23],[0,6,3,11,28,13,14,5,7],[[0,1,100,2,101],[0],[3,1,4],[5,6,7,8],[0,2,3,4],[1,0,100,2,4],[2,0,102,9],[1,0,101,10,100],[0,11,103,104],[9,1,105,4],[4,106,10],[0,2,4,9],[1,8,107,9,10,105],[0,6,9,103],[0,108,2]]),
([v0,v1,v80,v2,v3,v91],[54,6,131,23,4,41,14,40,43],[0,19,16,3,6,42,12,2,5],[[0,1,100,2,101],[0,1,3,4,102],[5,1,103],[6,1,102],[6,1,104],[1,2,7,105],[5,0,106,2],[6,107,2],[6,107,2],[5,1,6],[1,5,4],[6,1,8],[6,5,108],[6,5,108],[1]]),
([v138,v0,v1,v2,v3,v78],[14,63,0,85,22,132,6,91,4,81,7],[2,12,0,6,4,25],[[0],[1,100,2,3,101],[4,5,6],[0,7,8,3],[0,1,4,3,6],[9,1,102,6,103],[4,6,104],[0,6,103],[0,1,4,3,102],[3,105,1,4,7,101],[0,9,100,7],[0,6],[0,3,105,4],[0,3,6],[0,6,10]]),
([v0,v139,v1,v2,v3,v78],[81,88,4,37,90,91,32,14,75,7],[6,3,0,13,2,8],[[0,100,1,2,101],[0,102,1,3,4],[1,5,101,0,4,6],[1,5,100,7,4],[0,100,7,8],[3,7],[4,3],[2,0,7,5],[3,6],[6,3,103],[7,0,104,3],[4,3,6,7],[7,6,105],[4,1,103,5,6,3],[0,1,105,5,7,9]]),
([v0,v1,v2,v81,v91],[6,133,134,23,14,38,39],[0,19,3,6,12,13,5,14,8,29],[[0,100,1,101],[0,102,2,100],[0,3,4],[0,4,103],[104,105,1,2,106],[0,1,4],[4,107,1,5],[0,2,4],[4,108,2,6],[0,4,109]]),
([v140,v0,v1,v2,v3,v78],[6,14,63,0,135,91,1,136,137,4,7],[2,12,5,13,1,4,6],[[0,1],[2,100,3,4,101],[5,102,6,4,103],[0],[0,1],[0,104,7],[0,105,8],[1,0,106],[0,106,1],[101,103,2,5,100],[1,9],[0,1],[1,9],[0,1],[0,1,10]]),
([v0,v141,v1,v2,v3,v78],[81,104,4,40,125,91,14,121,89,55,1,137,7],[6,3,0,5,4,13,2,14],[[0,100,1,2,101],[0,102,1,3,4],[101,5,0,4,100],[6,5,100,7],[0,8,100,6,4],[3,6],[9,103,10,5,104],[2,0,3,6],[3,2,4],[3,105,11],[4,0,106,3,6],[6,3,106],[4,103,6,0],[6,103,1],[0,4,107,3,5,12,1]]),
([v0,v1,v142,v2,v3,v78],[63,88,122,104,4,41,68,14,138,85,0,136,97,7],[0,2,19,6,3,1,12,5,8],[[100,0,1,2,101,102],[1,103,3,2,4,100],[1,104,3,2,5],[1,6,103,3,7,8],[7,0,100,2],[9,101,0,10,105],[5,106,11],[2,101,0,7,12],[7,101,1],[5,7],[2,5,7],[5,2],[2,5,107,7],[7,1,107,0],[7,108,5,13]]),
([v0,v143,v1,v2,v3,v78],[55,4,88,42,81,13,14,1,91,65,75,7],[3,6,0,13,5,12,14],[[0,1,100,2,101],[0,1,102,2,3],[2,1,100,4,101],[0,1,5,6],[4,1,100,0,6],[1],[0,103,7,8,104],[1,3],[3,6],[9,0,103,3],[1,3,6],[6,3,105],[0,1,4,6],[6,2,103,10],[1,6,11,106]]),
([v0,v1,v144,v2,v3,v78],[54,4,88,137,43,13,14,85,0,62,7],[0,19,6,3,12,2,13,8],[[0,1,100,2,101],[0,1,100,3,102],[2,1,103,3,4],[1,5,6],[0,1,100,6],[7,104,3,8,105],[4,0,104],[1,6],[3,9,104,6,2],[1],[1,4],[4,6],[1,4,6],[0,2,106,4,6],[1,6,10,107]]),
([v0,v145,v1,v2,v3,v78],[81,6,97,44,14,23,55,1,89,66,5],[0,6,3,13,5,14,15],[[0,1,100,2,101],[0,1,100,2,3],[2,1,102,0,100],[4,1,101],[0,1,5,4],[1],[6,103,7,8,104],[3,4],[1,3],[9,3,103],[4,0,105,2,3],[1,3,4],[4,2,104,0],[1,4],[0,1,4,10,106]]),
([v0,v1,v146,v2,v3,v78],[81,6,88,45,14,23,85,137,0,55,97,5],[0,19,3,6,12,2,8,11],[[0,1,100,2,101],[2,1,102,0,100],[2,1,102,0,3],[2,1,103,4],[0,1,5,4],[6,104,7,8,105],[3,9,104],[4,0,105,10],[1,2,4],[1],[3,4],[1,3],[4,3,106],[1,3,4],[0,1,4,11,107]])]
noncomputable def u15_D5 : List StD := [
([v55,v30,v0,v2,v3,v78],[46,9,10,81,70,4,6,8,49,90,89,55,91],[17],[[0,1],[0,1],[2,1],[3,4,5],[6,4],[1],[1,7,100],[3,8],[9,8,10],[1,3,9],[11,8,12],[3,8,10],[8,3],[8,11,9],[3,10,12]]),
([v30,v0,v1,v2,v147,v78],[139,83,140,55,3,19,89,49,141,51,70,6,91],[],[[0],[1],[2,3],[4,0,5],[6,0,7],[2,3],[2,8,9],[3,7,10],[6,3,7],[3,2],[9,2],[9,2],[3,4,6],[7,3,8],[11,6,12]]),
([v30,v0,v1,v2,v3,v148],[139,83,142,55,91,49,3,143,51,89,81],[],[[0],[1],[2,3],[4,0,5],[6,0,5],[2,3],[2,7,8],[3,5,4],[9,3,5],[3,2],[8,2],[8,2],[3,7,5],[5,3,6],[10,4]]),
([v49,v94,v0,v1,v3,v78],[0,9,144,145,55,81,89,49,48,146,60,67,91,51],[17],[[0],[1,2,3],[4,1],[4,5,6],[7,4,8],[9],[100],[5,10],[6,11],[4,3],[4,7,12],[5,4],[5,3],[13,3],[5,6,12]]),
([v120,v94,v1,v2,v3,v78],[0,81,9,91,51,89,147,148,104,110,49],[6],[[0],[1,2],[2,1],[3,4],[1,4,5],[6],[7],[1,8,100],[4,9,100],[4,3],[1,3],[4,5],[10,1],[10,3,8],[1,3]]),
([v55,v94,v0,v2,v3,v78],[0,81,9,51,91,49,149,86,90,89,150],[17],[[0],[1,2],[3,2],[1,4],[3,5],[6],[100],[1,7],[3,8],[2,1,3],[4,3],[1,3,9],[5,1],[5,4,10],[1,4]]),
([v94,v0,v1,v2,v147,v78],[104,4,49,14,141,140,81,51,91,89],[],[[0],[],[],[1],[2,3],[4,5,6],[5,4,7],[8,2],[6,2,9],[7,4,5],[6,2],[7,2],[2,4],[2,4],[6,8]]),
([v149,v94,v0,v1,v2,v78],[14,91,151,152,81,49,86,60,153,56,89,154,51],[6],[[0],[1,2,3],[4,1],[5,4],[4,1],[100],[6],[7],[5],[4,8],[1,4,9],[4,5,10],[9,1,11],[12,5],[5,1,11]]),
([v94,v0,v1,v2,v3,v148],[110,51,14,6,143,142,81,91,89,49],[],[[0],[],[],[1,2],[3],[4,5,6],[5,1,4],[7,1],[6,1,8],[1,4,5],[1,5],[1,5],[9,4],[9,4],[6,7]]),
([v150,v94,v0,v1,v2,v3],[14,89,155,156,51,49,157,158,56,90,67,159,160,48,91],[6],[[0],[1,2,3],[4,1],[5,6,7],[8,1],[100],[9],[10],[4],[11,12,13],[1,4],[14,4],[4,1],[4,5],[5,1,11]]),
([v49,v30,v33,v1,v3,v78],[144,10,6,4,89,91,161,146,60,49,3,81,75],[],[[0],[0,1],[2,0],[3,4],[2,5],[6,7],[8],[5,9],[4,9],[10,1,11],[5,12],[4,12],[11,5],[12,4],[11,4,5]]),
([v49,v30,v0,v39,v3,v78],[58,10,9,56,81,49,75,3,60,63,55,54,68,67],[],[[0],[0,1],[1,2],[3,4,5],[5,6],[1],[7,1],[4,5],[6,5],[4,8,9],[10,5,11],[4,5,9],[4,9,8],[5,12,13],[4,9,12]]),
([v49,v33,v0,v1,v3,v78],[0,10,9,144,145,8,3,4,75,49,60,91,89],[17],[[0,1,2],[2,3,4],[5,6],[7,8,9],[9,8],[6],[6,1,100],[9,8],[9,8],[6,4,10],[11,8],[12,8],[8,4],[8,4],[10,11,12]]),
([v46,v49,v0,v1,v3,v78],[60,56,54,62,63,10,162,35,49],[17],[[0,1],[2,0,3],[4,5,100],[6],[4,3],[7,0],[0,4],[0,2],[2,3,8],[2,0,4],[3,2],[2,0,4],[0,4],[3,8],[0,4]]),
([v90,v49,v0,v1,v3,v78],[91,6,55,60,81,68,10,163,49,164,67],[17],[[0,1],[2,3,4],[5,6,100],[0,4],[7],[0,1],[1,0],[2,4,8],[1,0],[2,9],[0,8],[4,2],[4,0],[10,5],[4,0]]),
([v30,v33,v0,v39,v3,v78],[9,46,6,90,56,49,91,48,89,54,55],[],[[0,1],[0],[0,2,3],[4,5,6],[7,5,8],[1],[0,2],[4,9],[5,10,7],[0,2,6],[6,5],[8,4],[4,8],[2,6],[4,6,7]]),
([v55,v30,v33,v2,v3,v78],[68,9,4,91,81,6,8,88,49,89,90,54,55,150],[],[[0,1],[1],[2,0],[2,3,4],[5,0],[1,4],[1,6,7],[0,8],[9,8],[10],[0,11,12],[4,12],[8,0],[7,3,13],[4,0]]),
([v30,v33,v39,v3,v78],[9,1,46,6,3,48,56,91,66,165,49,65,89,55,54,75,4,79,53,57],[8,9,11],[[0,1,2],[0,1,3,4,5],[6,7,8,9,10,11],[5,12,11,8,10],[0,5],[6,7,13,14,15],[5,10,14,13,15],[6,10,16,12,17,18],[3,10,7,17,19],[5,6,100,7,12,101,102]]),
([v30,v39,v119,v2,v3,v78],[48,90,10,58,55,65,56,49,75,46,79,54,110],[],[[0,1],[2],[0,3,4,5],[6,5],[0,7,8],[9],[3],[6,10,7],[0,10,7],[2,0,9],[4,0,11],[11,4],[4,8,7],[0,4],[0,12]]),
([v120,v30,v39,v2,v3,v78],[46,9,58,55,54,65,110,75,49,79,81],[],[[0,1],[2],[0,2],[3,4],[4,3],[5,6],[3,6,5],[7,5,8],[5,6],[0],[7,6],[7,9],[3,4],[4,3],[10,6]]),
([v151,v0,v1,v2,v3,v78],[0,6,54,58,55,11,75,1,19,49,89,166,53,62],[],[[0,1],[1,0],[2,3,4],[5,6,7,8],[1,9,10],[2,11,12],[10,11],[13,2],[2,9,10],[2,10],[11,9,12],[13,9],[9,2,11],[2,13,9],[11,10]]),
([v152,v0,v1,v2,v3,v78],[139,56,58,46,75,49,55,86,53,54,89],[],[[0],[1],[1,2,3],[1,0],[4,0,5],[6,7,8],[8,7],[6,4,9],[8,4],[6,10],[4,5],[4,5],[5,4],[5,4],[7,8]]),
([v30,v0,v75,v2,v3,v78],[35,86,56,55,30,49,75,53,54],[17],[[0],[1,2],[3,4,100],[1,5,6],[6,5],[3,1,7],[7,1],[3,5,8],[7,1],[1,0],[0,6],[6,5],[1,6,0],[5,3,6],[1,7]]),
([v153,v0,v1,v2,v3,v78],[0,4,55,58,54,49,14,21,167,68,91,81],[],[[0,1],[1,0],[2,3,4],[1,5,6],[7,5,6],[2,8,9],[10,8],[2,5,9],[11,2],[2,8,10],[11,5],[8,5,9],[2,9,5],[5,2,8],[8,9]]),
([v154,v0,v1,v2,v3,v78],[139,83,54,58,6,4,90,53,55,91,81,70],[],[[0],[1],[2,3,4],[5,0],[4,0],[2,6,7],[7,6],[8,2],[2,8],[2,9],[10,7,9],[6,11],[8,2],[2,8],[6,7,9]]),
([v30,v0,v139,v2,v3,v78],[37,70,83,55,32,81,49,90,53,91],[17],[[0],[1,2],[3,4,100],[5,1,6],[7,1],[1,7,8],[9,5,7],[3,1],[5,1],[3,0],[5,1,6],[0,1],[3,1],[6,1,7],[5,9]]),
([v155,v0,v1,v2,v3,v78],[139,98,55,1,11,19,121,53,70,81,91],[],[[0],[1],[2,3],[4,0,5],[1,0],[2,6,7],[7,6],[2,6,8],[7,2,9],[2,10],[6,7,10],[6,8],[2,7],[6,2],[6,7,10]]),
([v156,v0,v1,v2,v3,v78],[0,55,14,83,70,136,19,11,28,21,91,168,169],[],[[0,1,2],[3,4],[5,1],[6,2,7],[8,2,9],[1,5],[10,11],[1,4],[5,1],[1,5],[12,4],[11,4],[1,4],[5,1],[11,10]]),
([v30,v140,v1,v2,v3,v78],[55,0,6,137,14,91,81,4,70],[36,31],[[0,1],[2],[0,3,100],[3,4],[2,4],[0,1],[5,6,101],[0,2],[2,0],[0,5],[7,5,8],[2,8],[0,8],[2,0],[2,5]]),
([v30,v0,v141,v2,v3,v78],[40,121,98,91,137,14,70,53,125,55],[17],[[0],[1,2],[3,4,100],[1,5,4],[1,5],[6,1,7],[3,1],[3,1],[7,6,8],[9,3],[0,1],[0,6],[8,6],[1,3],[1,0,3]]),
([v33,v0,v1,v2,v147,v78],[170,53,99,9,4,75,140,85,65,91,68,6],[43],[[0],[1],[2],[3,0,4],[1,0,5],[1,6,7],[100,1,8],[9,4],[1,5],[7,6,10],[5,1,3],[5,6],[7,1,4],[7,5],[11,1,9]]),
([v33,v0,v1,v2,v3,v148],[170,53,99,91,75,142,85,65,68,4],[43],[[0],[1],[2],[3,0,4],[1,0,4],[1,5,6],[100,1,7],[3,4],[1,4],[6,3,8],[4,1,3],[4,5],[6,1,4],[6,3,4],[9,1]]),
([v55,v33,v0,v39,v3,v78],[0,1,9,4,56,91,75,49,8,86,65,89,90,88],[],[[0],[1,2],[3,1,2],[4,5,6],[6,7],[8],[2,8],[5,6],[7,6],[2,9,5],[5,6],[10,6,11],[6,11,9],[6,5,12],[13,5,11]]),
([v43,v55,v0,v2,v3,v78],[86,56,65,88,53,8,9,75],[17],[[0,1],[2,0,3],[4,5,100],[6],[4,3],[4,0],[0,6],[0,2],[2,3,7],[2,0,4],[3,2],[2,0,4],[0,4],[3,7],[0,4]]),
([v89,v55,v0,v2,v3,v78],[90,48,55,97,8,86,75,9,14,171,91],[17],[[0,1],[2,0,3],[2,4,100],[5,3,6],[7],[2,0,3],[0,7],[6,3],[0,8],[3,0,9],[2,0,10],[3,2],[2,6,3],[0,2],[0,10]]),
([v33,v39,v1,v119,v3,v78],[172,173,56,55,8,75,49,86,174,79,88,65,66,110,48],[],[[0,1],[2,0,3],[4],[2,5,6],[6,3,5],[7],[8],[2,9,5],[5,9],[4,0],[2,0,5],[5,0],[10,5,11],[11,2,12],[2,13,14]]),
([v120,v33,v39,v1,v3,v78],[0,46,9,144,1,88,75,65,79,175,148,55,77,91,89],[],[[0,1,2],[3],[4,2],[5,6,7],[7,6,8],[9,10],[7,1,11],[8,6],[5,6],[12],[6,8],[5,8],[6,7,8],[6,5],[5,13,14]]),
([v157,v0,v1,v2,v3,v78],[1,19,15,65,4,89,75,53,166,88,63],[],[[0,1,2],[3,1,4],[4,0],[4,1],[5,6],[7,8],[3,8,5],[9,3],[3,6,5],[3,5,10],[6,3,8],[3,5,6],[8,5],[9,6],[8,5]]),
([v158,v0,v1,v2,v3,v78],[170,65,0,4,56,88,75,53,60,89,63],[],[[0],[1,2,3],[4],[3,0],[5,0,6],[7,5,8],[1,8,7],[5,1],[1,6,7],[1,9,10],[6,1,8],[1,5,6],[8,6,7],[5,6],[5,7]]),
([v33,v0,v1,v71,v3,v78],[176,65,60,56,75,14,89,63,88],[17],[[0],[1,0,100],[2,3],[2,4,5],[6,4],[7,2],[1,2,6],[8,1],[1,2,6],[1,6,2],[2,1],[1,6,4],[2,4,6],[8,4],[2,6]]),
([v159,v0,v1,v2,v3,v78],[76,170,6,0,4,68,167,91,97,66],[],[[0,1],[2,3],[0,2],[4,0],[2,0],[5,6],[0,6,7],[5,0,6],[8,0],[9,5],[9,0],[6,0],[8,0,5],[6,0],[6,5]]),
([v160,v0,v1,v2,v3,v78],[170,65,0,6,48,4,63,67,89,91,76,66,97,75],[],[[0],[1,2,3],[4],[5,0],[3,0],[6,7],[1,7,8],[9,1,7],[1,10],[1,6],[11,1],[1,8,10],[12,8,13],[7,6,9],[7,6,9]]),
([v33,v0,v1,v134,v3,v78],[177,66,67,48,97,14,75,68,91],[17],[[0],[1,0,100],[2,3],[4,5,6],[2,5],[7,2],[1,2,8],[1,2,7],[4,1],[1,7],[1,4,6],[2,1],[4,6],[2,6,8],[2,7]]),
([v161,v0,v1,v2,v3,v78],[170,66,0,100,138,178,68,91,97,76],[],[[0],[1,2],[3],[4,5],[3,0],[6,4],[1,4,7],[1,4,6],[8,1],[1,6],[1,7,9],[4,1],[4,6,8],[4,7],[4,6]]),
([v162,v0,v1,v2,v3,v78],[170,76,137,0,66,99,178,138,68,179],[],[[0,1],[2,3,4],[5,1],[6,7],[6,0],[8,6],[1,2,4],[2,1],[2,1],[4,2],[2,1],[2,1],[9,1],[6,1],[6,8]]),
([v33,v140,v1,v2,v3,v78],[66,14,170,136,6,68,9,1,76,4],[19,22],[[0,1,2],[0,3,100],[4],[3,1],[3,1],[5,6,101],[0,7],[0,4],[4,0],[0,5],[0,8],[4,0],[9,5,8],[4,8],[4,5]]),
([v33,v0,v1,v142,v3,v78],[170,68,136,122,76,91,138,97,66],[17],[[0],[1,2,100],[2,0],[1,0,2],[2,0],[1,3],[4,3,5],[1,4,6],[7,3,4],[8,1],[3,4],[6,1],[3,1,4],[3,6],[3,1,6]]),
([v163,v0,v1,v2,v3,v78],[66,58,14,86,60,6,55,56,97,81,75,65,88],[9],[[0,1,2],[3],[4],[3,2],[5,2],[6,7,8],[0,7,9],[0,10,11],[8,0],[0,6],[0,8,9],[10,0,11],[6,9,8],[12,6,10],[7,100]]),
([v0,v164,v1,v2,v3,v78],[97,0,170,81,180,75,65,66,4,56,6,88,91],[17],[[0,1,2],[3,0],[0,3],[4,5,6],[0,5,7],[6,1,8],[9],[0,1,3],[10,2],[6,4,100],[3,0],[5,4],[0,3],[11,5],[0,12]]),
([v40,v61,v0,v2,v3,v78],[86,56,81,88,11,83,98,55,68,90,75,54],[17],[[0,1],[2,0,3],[4],[0,5],[6,3,5],[2,0,3],[7,8,100],[0,4],[9,3,8],[3,0,2],[3,10,8],[2,0,7],[0,2,11],[3,7,10],[0,8,2]]),
([v46,v61,v0,v1,v2,v78],[35,11,75,83,91,181,98,4,54,1,97,103,88,81],[],[[0,1,2],[3,2,4],[2,1],[5],[6,4],[3,0],[7],[8,9,10],[2,3,10],[8,7,11],[12,7,13],[8,2,3],[8,11],[2,3,11],[8,2,3]]),
([v165,v0,v1,v2,v3,v78],[70,10,58,139,56,6,81,86,88,75,54,55,68,97],[17],[[0,1,2,3],[4],[4,1],[4,0],[5,0],[6,7,8],[8,6],[8,9,10],[6,7,11],[10,12,100],[6,13],[9,8],[7,6,10],[8,9],[6,12]]),
([v41,v63,v0,v1,v3,v78],[0,4,56,88,62,166,99,66,60,80,35,65,91,97],[17],[[0,1,2],[3,1,4],[5],[1,6],[3,4],[3,4],[7,0,100],[8,9,10],[3,4],[4,3],[3,11],[11,7],[7,11],[4,3],[3,12,13]]),
([v43,v63,v0,v1,v2,v78],[35,68,97,88,4,14,75,98,62,99,65,102],[],[[0,1,2],[1,3,4],[4],[2,1],[2,1],[2,4,5],[6,0],[4],[3,5,7],[8,2],[2,4,8],[2,4,9],[10,11],[6,3],[3,6]]),
([v0,v39,v1,v2,v3,v103],[88,6,110,62,78,79,28,115,120,4,55,66,44],[],[[0,1,2],[3,0],[0,2],[0,4],[5,2,6],[7],[8],[9,2,4],[0,4,5],[10,11],[11,2,4],[3,0],[10,2,4],[0,3],[0,2,12]]),
([v0,v1,v2,v7,v3,v103],[62,166,88,182,79,68,91,120,115,44],[],[[0,1,2],[2,0],[0,1],[0,3],[4,1],[5,6],[7],[1,3],[0,2],[8],[1,3],[2,0],[1,3],[0,3],[0,5,9]]),
([v40,v0,v1,v2,v3,v103],[62,4,88,56,166,14,115,79,28,55,68,86,44],[17],[[0,1,2],[3],[4],[1,5],[0,2],[0,2],[2,0],[0,6],[7,6,8],[9,10,100],[11,6],[0,2],[9,6],[2,0],[0,10,12]]),
([v41,v0,v1,v2,v3,v103],[88,4,62,166,56,14,120,79,28,66,91,60,44],[17],[[0,1,2],[3],[4],[1,5],[0,2],[2,0],[0,2],[0,6],[7,6,8],[9,10,100],[9,6],[2,0],[11,6],[0,2],[0,10,12]]),
([v104,v0,v39,v1,v2,v3],[79,24,28,62,88,40,44,4,48,86,60,14,55,66,65,97],[6],[[0,1,2],[3,0],[3,0],[4,0],[3,5,6],[3,7,100],[3,4],[4,3],[0,8],[9],[10],[7,0,11],[12,13],[13,0,14],[12,0,15]]),
([v104,v0,v1,v2,v7,v3],[182,28,79,62,88,6,40,44,167,68,91,67,166,81,86,97,14],[],[[0,1,2],[3,1],[4,2],[5,1],[3,6,7],[3,4],[4,3],[3,5],[2,8],[9,10],[11],[12,2,13],[14],[12,2,15],[12,2,16]]),
([v40,v104,v0,v1,v2,v3],[62,88,56,166,14,115,28,79,40,44,90,55,68,86,81,97],[17],[[0,1],[0,1],[2],[3],[2,4],[5,6,7],[0,1],[1,0],[0,8,9],[0,1],[1,0],[0,10,7],[11,12,100],[13,7,14],[11,7,15]]),
([v41,v104,v0,v1,v2,v3],[0,62,97,166,56,14,24,79,67,88,40,66,91,81],[17],[[0,1],[2,1],[3],[4],[2,5,3],[2,6,7],[1,0],[8,1,9],[1,10,2],[1,2],[2,1],[1,8,7],[11,12,100],[11,2,13],[2,7]]),
([v0,v1,v166,v2,v3,v78],[62,56,88,14,104,79,86,55,66,135],[],[[0,1,2],[0,1,3],[2,0],[0,4],[5,1],[1,6],[1,7,8],[1,5,9],[0,2],[1,9],[1,3],[0,3,4],[1,5,9],[2,0],[0,4]]),
([v36,v0,v1,v71,v2,v78],[183,60,81,97,14,62,181,180,88,79,66,184],[],[[0],[1,0,2],[1,2,3],[1,2,3],[1,4,2],[5,1,6],[7,1,5],[8,1,5],[9,1],[1,6],[10,6,11],[5,4,6],[4],[8,4,5],[8,4,5]]),
([v36,v0,v75,v1,v2,v78],[185,11,81,86,97,14,79,62,186,88,55],[],[[0],[1,0,2],[2,0],[3,2,4],[2,5],[6,3],[7,3,8],[9,3,7],[6,3],[5],[3,1],[7,5,9],[10,8],[7,5,6],[9,5,6]]),
([v0,v167,v1,v2,v3,v78],[9,4,46,55,56,88,62,187,78,97,86,60,6,104],[],[[0,1,2],[3,4,5],[5,4,6],[3,7,8],[9,3],[10],[11],[1,8],[5,8,12],[3,7],[4,7,8],[6,5],[3,8],[5,3,6],[4,13]]),
([v168,v0,v1,v2,v3,v78],[46,4,9,86,56,14,6,54,104,65,79,48,78],[],[[0,1,2],[3,4],[0,1],[1,5],[6,5],[7,4,8],[9,4,8],[10,7,11],[7,4,10],[4,7,9],[4,9],[9,8,12],[4,7],[7,8,12],[4,8]]),
([v0,v39,v64,v2,v3,v78],[62,4,104,65,56,78,115,15,1,48],[],[[0,1,2],[0,2],[3,0],[0,2],[3,4,5],[3,1,6],[7],[1,5],[0,2],[3,8],[4,3],[0,2],[4,5],[9,0,5],[0,2]]),
([v0,v39,v1,v65,v3,v78],[65,6,104,54,88,78,115,0,4,56],[],[[0,1,2],[3,2],[0,2],[4,0],[0,5],[6],[3,1,7],[8,5],[1,2,4],[0,7,3],[9,0],[0,2,5],[9,3],[3,2,4],[4,2]]),
([v0,v39,v1,v2,v3,v105],[65,4,104,54,56,26,86,60,14,6,78],[6],[[0,1,2],[3,2],[0,2],[100,0],[0,4,5],[6],[7],[1,8],[9,2,8],[3,0],[4,0],[0,2,10],[4,3],[3,2,10],[4,2]]),
([v106,v0,v39,v1,v2,v3],[26,56,21,14,6,78,48,104,54,65,55,115,120],[],[[0,1,2],[3,4],[5,0,6],[5,6],[1,6,7],[8,1,7],[8,1,7],[9,1,7],[10,5],[11],[12],[1,3],[8,9],[1,5],[1,5]]),
([v169,v0,v1,v2,v3,v78],[0,6,78,62,67,104,65,120,89,60],[17],[[0,1],[1,0],[2],[0,2],[1,2],[3,4,5],[6,3],[3,4,5],[6,7],[6,8,100],[9,6],[3,5],[9,7],[4,3,7],[3,5]]),
([v40,v0,v64,v2,v3,v78],[104,6,90,48,15,4,14,62,54,115,1,86],[3,17],[[0,1,100],[2,3],[4],[5,6],[0,6,1],[4,2],[100,0],[7,0],[8,9],[8,10,101],[4,9],[2,0,7],[11,8],[2,0,9],[2,0,7]]),
([v0,v167,v64,v2,v3,v78],[54,6,104,65,62,78,90,67,4,56],[],[[0,1,2],[0,2],[3,2],[4,0],[0,5],[6],[7],[8,5],[1,2,4],[0,3],[9,3],[3,2,4],[9,0],[0,2,5],[4,2]]),
([v0,v64,v2,v170,v3,v78],[62,166,104,89,15,1,60,182,86,167],[],[[0,1,2],[3,0,1],[4,0,1],[0,2],[3,1],[5,3],[6],[1,7],[0,2],[8],[1,3],[9,0,7],[1,7],[9,0,7],[0,2]]),
([v171,v0,v64,v2,v3,v78],[104,4,56,166,14,6,62,54,86,115,1],[3,17],[[0,1,100],[2],[3],[1,4],[0,4,5],[6,0],[100,0],[6,0],[7,8,9],[7,10,101],[8,9],[6,0],[8,7],[7,0,9],[6,0]]),
([v169,v0,v64,v2,v3,v78],[15,4,166,56,14,6,62,60,104,89,65,67,120],[17],[[0,1],[2],[3],[0,4],[5,4],[6,7,8],[9,6,7],[6,8],[9,7],[10,9,100],[7,10],[6,8],[7,9],[11,6,12],[6,8]]),
([v172,v0,v1,v2,v3,v78],[46,4,9,56,14,62,6,90,104,88,54,115,63,86],[17],[[0,1,2],[3],[1,0],[1,4],[5,4,6],[5,7,8],[9,5],[5,7,8],[10,11],[10,12,100],[13,11],[5,8],[13,10],[7,5,9],[5,8]]),
([v41,v0,v1,v65,v3,v78],[104,4,166,0,56,14,6,9,62,88,65,120,60],[0,17],[[0,1,100],[2],[3,1,4],[1,5],[0,5,6],[100,0],[7,0,8],[9,0],[10,11],[10,3,101],[12,10],[10,0,11],[12,11],[9,0],[9,0]]),
([v0,v167,v1,v65,v3,v78],[88,4,104,54,56,78,86,0,65],[],[[0,1,2],[3,0],[0,2],[0,2],[3,4,5],[6],[7],[1,5],[0,2],[3,8],[4,5],[8,0,5],[4,3],[0,2],[0,2]]),
([v0,v1,v65,v173,v3,v78],[63,166,9,46,16,88,187],[],[[0,1],[2,1,3],[4,1],[5,6],[0,1],[6],[6],[1,0],[6],[6],[1,6],[5,0],[1,6],[6],[1,0]]),
([v172,v0,v1,v65,v3,v78],[16,4,56,0,14,63,88,86,62,187,115,54,90],[],[[0,1],[2],[3],[0,4],[5,4,6],[5,6,7],[6,7,8],[6,9,10],[5,7],[11,5,9],[7,5],[12,6,10],[7,10],[6,5],[6,5]]),
([v174,v0,v1,v65,v3,v78],[88,4,182,78,6,60,46,187],[0],[[0,1,100],[2],[3],[1,2],[0,2,4],[100,0],[0,5,6],[0,7],[7],[7],[5,7],[7],[5,7],[0,7],[0,7]]),
([v0,v1,v2,v7,v3,v105],[63,166,89,104,136,120,167,182,115],[],[[0,1],[2,1],[1,3],[4,3],[0,1],[0,2],[5],[1,0],[6,2,7],[8],[1,2],[4,0,7],[1,5],[6,0,5],[1,0]]),
([v40,v0,v1,v2,v3,v105],[104,6,97,48,167,4,14,63,90,137,115,54,86],[17],[[0,1,2],[3],[4],[5,2,6],[0,6,1],[7,0,8],[2,0],[9,0],[2,10],[11,7,100],[9,2,7],[8,0,10],[2,10,12],[8,0,10],[2,0,12]]),
([v41,v0,v1,v2,v3,v105],[104,6,81,167,48,4,14,89,67,136,120,65,60],[17],[[0,1,2],[3],[4],[5,2,6],[0,6,1],[2,0],[7,0,8],[9,0],[2,10],[11,7,100],[2,10,12],[8,0,10],[9,2,7],[8,0,10],[2,0,12]]),
([v106,v0,v1,v2,v7,v3],[26,166,21,182,167,89,63,104,91,120,115],[],[[0,1,2],[3,0,4],[3,4],[3,0,4],[1,4,5],[6,1],[5,1],[1,7],[8,3,4],[6,5],[9],[1,3],[10],[1,3],[1,3]]),
([v106,v40,v0,v1,v2,v3],[14,6,26,86,21,115,90,104,78,182,63,55],[3,17],[[0,1],[2,3,4],[5,2,6],[5,6],[3,6,7],[7,1,100],[8],[9],[3,0],[10,3],[100,3,7],[11,5],[11,10,101],[3,5],[3,5]]),
([v106,v41,v0,v1,v2,v3],[0,6,14,26,60,21,120,67,104,167,48,89,91,65],[0,17],[[0,1,2],[3,4,5],[6,0,7],[6,7],[4,7,8],[8,1,100],[9],[10],[4,2],[100,4,8],[11,4],[12,6,7],[13,11,101],[4,6],[4,6]]),
([v175,v0,v1,v2,v3,v78],[9,6,46,90,67,91,80,35,4,14,63,48,89,55,65,56,62],[],[[0,1,2],[3],[4],[5,6,7,8],[1,9],[10,11],[12,11],[13,11,14],[10,13,14],[11,10,12],[15,10],[11,12,16],[13,12],[11,10,13],[11,10,15]]),
([v176,v0,v1,v2,v3,v78],[0,6,48,4,62,14,67,63,65,60,88,81,97],[],[[0,1],[1,0],[2],[3,0],[1,4,5],[4,6,7],[8,4],[4,6,8],[7,9],[8,7],[9,7],[4,10],[9,11,12],[6,4,10],[4,7]]),
([v107,v0,v39,v2,v3,v78],[0,19,15,48,90,1,65,11,78,62,63,88,54,56,70],[],[[0,1,2],[3,4],[3,5,6],[7,1],[3,8],[9,3,10],[11,3,9],[9,3,12],[10,13],[1],[13,10],[3,14],[13,12],[3,9,11],[3,10,9]]),
([v177,v0,v1,v2,v3,v78],[46,6,9,48,4,35,80,14,62,90,88,54,86,89,97,81],[],[[0,1,2],[3],[1,0],[4,5,6],[1,7],[8,9,10],[10,8],[8,9,11],[11,12,13],[11,13],[12,14,15],[8,10],[12,11],[9,8,10],[8,13]]),
([v108,v0,v39,v1,v3,v78],[9,48,46,54,56,62,88,89,65,90,76],[],[[0,1,2],[1,0],[1,0,3],[4,3],[1,5,6],[5,1,7],[5,1,6],[5,1,8],[7,4],[9],[4,7],[1,10],[4,8],[1,6,5],[1,7,4]]),
([v0,v1,v178,v2,v3,v78],[62,48,88,46,104,89,56,90,63,80,35],[],[[0,1,2],[0,1,3],[2,0],[0,1,4],[5,6],[1,7],[1,5,8],[6,8],[0,2],[1,3],[6,9,10],[0,4],[6,5],[1,0,2],[0,4]]),
([v179,v0,v1,v2,v3,v78],[88,58,14,90,67,4,62,48,65,55,81,97],[9],[[0,1,2],[3],[4],[5,2],[0,2,3],[6,0],[0,6],[0,7,8],[8,9],[7,9,8],[10,8,11],[6,0],[9,10,11],[0,6],[0,100]]),
([v0,v180,v1,v2,v3,v78],[65,0,62,67,88,66,48,4,81,97,89],[17],[[0,1,2],[2,3,4],[0,2],[2,0],[0,5],[0,1,3],[6],[7,8,9],[3,1],[0,10,100],[5,0],[0,4,2],[9,8],[3,2,4],[2,10]]),
([v40,v109,v0,v2,v3,v78],[90,48,81,97,21,83,55,63,54,62],[17],[[0,1],[2,0,3],[4],[2,3],[0,5],[2,0,3],[6,7,100],[2,3],[0,4],[3,0,2],[6,0,8],[2,6],[3,2],[0,6],[0,7,9]]),
([v90,v109,v0,v1,v2,v3],[37,21,62,97,6,81,55,1,88,83,109],[],[[0,1,2],[3,4,5],[2,1],[4],[2,5,3],[2,0,3],[4],[6,7,8],[5,3],[2,3],[3,2],[2,4,9],[6,10],[5,3],[3,5]]),
([v181,v0,v1,v2,v3,v78],[81,10,97,48,37,82,55,90,54,63,88,62],[17],[[0,1,2],[3],[3,1],[0,2],[3,4,5],[0,2],[2,0],[6,7,8],[0,6],[6,9,100],[0,2],[7,10,11],[2,0],[7,6],[0,9,10]]),
([v41,v110,v0,v1,v3,v78],[0,6,48,97,81,167,99,65,67,82,37,88,66,89],[17],[[0,1,2],[3,1,4],[5],[3,4],[1,6],[3,4],[7,0,100],[3,4],[8,9,10],[4,3],[11,7],[3,12],[4,3],[7,11,12],[3,13,11]]),
([v89,v110,v0,v1,v2,v3],[37,63,88,6,81,66,62,97,99,108],[],[[0,1,2],[1,3],[3],[2,1],[2,1],[2,3,4],[5,0,6],[3],[6,4,7],[4,2],[2,3,4],[2,3,8],[5,9],[4,7],[7,4]]),
([v0,v39,v1,v2,v111,v78],[81,6,104,97,79,19,78,115,120,54,65,42],[],[[0,1,2],[0,2],[3,0],[4,2,5],[0,6],[7],[8],[0,4],[1,2,6],[9,10],[0,3],[10,2,6],[3,0],[9,2,6],[0,2,11]]),
([v0,v1,v2,v7,v111,v78],[81,97,6,79,15,19,182,63,89,120,167,90,42],[],[[0,1],[1,0],[0,2],[3,4,5],[0,6],[7,8],[9],[0,1],[10,3,6],[11],[1,0],[10,3,6],[0,6],[2,3,6],[0,7,12]]),
([v40,v0,v1,v2,v111,v78],[81,6,97,48,167,14,79,15,19,115,54,63,90,42],[17],[[0,1,2],[3],[4],[0,2],[1,5],[0,2],[2,0],[6,7,8],[0,9],[10,11,100],[0,2],[12,6,9],[2,0],[10,6,9],[0,11,13]]),
([v41,v0,v1,v2,v111,v78],[97,6,81,167,48,14,79,15,19,120,65,89,67,42],[17],[[0,1,2],[3],[4],[0,2],[1,5],[2,0],[0,2],[6,7,8],[0,9],[10,11,100],[2,0],[10,6,9],[0,2],[12,6,9],[0,11,13]]),
([v112,v0,v39,v1,v2,v78],[78,19,79,97,81,40,42,6,66,90,67,14,54,48,88],[6],[[0,1,2],[3,2],[4,1],[3,2],[3,5,6],[3,7,100],[4,3],[3,4],[2,8,3],[9],[10],[7,2,11],[12,8],[13,2,8],[12,2,14]]),
([v112,v0,v1,v2,v7,v78],[79,15,19,81,97,4,40,42,166,63,89,67,167,62,90,88,14],[],[[0,1,2],[3,0],[4,0],[5,0],[3,6,7],[3,4],[4,3],[3,5],[0,8],[9,10],[11],[12,0,13],[14],[12,0,15],[11,0,16]]),
([v40,v112,v0,v1,v2,v78],[79,97,81,48,167,14,15,19,40,42,86,54,63,90,62,88],[17],[[0,1],[2,1],[3],[4],[0,5,3],[0,6,7],[2,0],[1,0],[1,8,9],[2,1],[1,2],[0,10],[11,12,100],[13,0,14],[11,0,15]]),
([v41,v112,v0,v1,v2,v78],[0,81,97,167,48,14,120,19,79,40,42,60,66,89,67,88],[17],[[0,1],[2,1],[3],[4],[3,5],[6,7,8],[1,0],[2,1],[1,9,10],[1,2],[2,1],[1,11,8],[12,13,100],[14,8,12],[14,8,15]]),
([v0,v1,v182,v2,v3,v78],[81,48,97,14,79,110,90,54,65,188],[],[[0,1,2],[0,1,3],[2,0],[4,1],[0,5],[1,6],[1,7,8],[0,2],[1,4,9],[1,9],[0,3,4],[1,3],[2,0],[1,4,9],[0,5]]),
([v85,v0,v1,v134,v2,v3],[189,67,62,88,14,81,190,191,97,79,65,192],[],[[0],[1,0,2],[1,2,3],[1,2,3],[1,4,2],[5,1,6],[7,1,5],[8,1,5],[9,1],[1,6],[10,6,11],[5,4,6],[4],[8,4,5],[8,4,5]]),
([v85,v0,v139,v1,v2,v3],[193,21,62,90,88,14,79,81,194,97,54],[],[[0],[1,0,2],[2,0],[3,2,4],[2,5],[6,3],[7,3,8],[9,3,7],[6,3],[5],[3,1],[7,5,9],[10,8],[7,5,6],[9,5,6]]),
([v0,v183,v1,v2,v3,v78],[9,6,46,54,48,97,81,88,195,78,90,67,4,110],[],[[0,1,2],[3,4,5],[5,4,6],[7,3],[3,8,9],[10],[11],[5,9,12],[1,9],[3,8],[6,5],[4,7,9],[5,3,6],[3,9],[4,13]]),
([v184,v0,v1,v2,v3,v78],[46,6,9,90,48,4,14,55,110,66,78,79,56],[],[[0,1,2],[3,4],[0,1],[5,6],[1,6],[7,4,8],[9,4,8],[7,4,10],[11,7,12],[4,7,9],[9,8,10],[4,9],[7,8,10],[4,7],[4,8]]),
([v0,v39,v113,v2,v3,v78],[66,6,110,0,28,48,78,81,90,24,1,56],[],[[0,1,2],[3,2,4],[0,2],[0,5,6],[7,0],[0,1,8],[9],[7,2],[1,6],[0,10],[0,2,6],[3,0],[11,2,6],[5,6],[5,2]]),
([v0,v39,v1,v114,v3,v78],[66,6,110,55,48,78,97,90,0],[],[[0,1,2],[3,2],[0,2],[0,4,5],[6,0],[7],[3,1,8],[6,2],[1,5],[0,8,3],[0,2,5],[4,0],[3,2,5],[4,3],[4,2]]),
([v0,v39,v1,v2,v115,v78],[66,6,110,55,48,17,90,67,4,14,78],[6],[[0,1,2],[3,2],[0,2],[0,4,5],[100,0],[6],[7],[8,2,9],[1,9],[3,0],[0,2,10],[4,0],[3,2,10],[4,3],[4,2]]),
([v116,v0,v39,v1,v2,v78],[17,48,11,14,110,4,78,56,55,66,54,86,60],[],[[0,1,2],[3,4,5],[6,0,7],[6,4,7],[1,4],[8,1,4],[8,1,4],[9,1,4],[10,4],[11],[12],[1,3],[8,9],[1,6],[1,6]]),
([v185,v0,v1,v2,v3,v78],[0,4,56,14,81,60,110,66,120,91,67],[17],[[0,1],[1,0],[2],[1,3],[0,3],[4,5,6],[7,4],[7,8],[4,5,6],[7,9,100],[4,6],[10,7],[5,4,8],[10,8],[4,6]]),
([v40,v0,v113,v2,v3,v78],[110,4,86,56,24,14,6,55,115,81,1,90],[10,17],[[0,1,100],[2,3],[4],[0,5,1],[6,5],[4,2],[100,0],[7,8],[9,0],[7,10,101],[2,0,8],[4,8],[2,0,8],[11,7],[2,0,9]]),
([v0,v183,v113,v2,v3,v78],[81,6,110,66,48,78,90,67,55],[],[[0,1,2],[0,2],[3,0],[3,4,5],[0,2],[6],[7],[0,2],[1,5],[8,3],[0,2],[4,3],[8,0,5],[4,5],[0,2]]),
([v0,v113,v2,v186,v3,v78],[81,167,110,91,24,1,67,182,90,166],[],[[0,1,2],[3,0,1],[4,0,1],[3,1],[0,2],[5,3],[6],[0,2],[1,7],[8],[9,0,7],[1,3],[9,0,7],[1,7],[0,2]]),
([v187,v0,v113,v2,v3,v78],[110,6,48,167,14,4,81,55,115,1,32,119,90],[10,17],[[0,1,100],[2],[3],[0,4,5],[1,4],[6,0],[100,0],[7,8],[6,0],[7,9,101],[6,0],[10,8,11],[7,0,8],[12,7],[6,0]]),
([v185,v0,v113,v2,v3,v78],[24,6,167,48,4,14,81,67,110,91,66,60,120],[17],[[0,1],[2],[3],[4,5],[0,5],[6,7,8],[9,6,7],[9,7],[6,8],[10,9,100],[6,8],[7,10],[11,6,12],[7,9],[6,8]]),
([v188,v0,v1,v2,v3,v78],[46,6,9,48,81,14,4,86,110,97,55,115,68,90],[17],[[0,1,2],[3],[1,0],[4,5,6],[1,5],[4,7,8],[9,4],[10,11],[4,7,8],[10,12,100],[4,8],[13,11],[7,4,9],[13,10],[4,8]]),
([v41,v0,v1,v114,v3,v78],[110,6,167,0,48,14,4,9,60,66,120,97,67],[16,17],[[0,1,100],[2],[3,1,4],[0,5,6],[1,5],[100,0],[7,0,8],[9,10],[11,0],[9,3,101],[8,0,10],[12,9],[8,0,10],[12,10],[8,0,11]]),
([v0,v183,v1,v114,v3,v78],[97,6,110,55,48,78,90,0,66],[],[[0,1,2],[3,0],[0,2],[3,4,5],[0,2],[6],[7],[0,2],[1,5],[3,8],[8,0,5],[4,5],[0,2],[4,3],[0,2]]),
([v0,v1,v114,v189,v3,v78],[68,167,9,46,25,97,195],[],[[0,1],[2,1,3],[4,1],[0,1],[5,6],[6],[6],[6],[1,0],[6],[5,0],[1,6],[6],[1,6],[1,0]]),
([v188,v0,v1,v114,v3,v78],[55,6,97,48,0,68,14,90,110,86,115],[17],[[0,1,2],[3],[4],[5,2],[1,6],[0,2],[2,7,8],[0,7,5],[2,0],[0,5,100],[9,2,10],[7,5],[0,5,2],[7,0],[2,5]]),
([v190,v0,v1,v114,v3,v78],[97,6,167,48,14,4,60,46,66,120,67,110],[16,17],[[0,1,100],[2],[3],[0,4,5],[1,4],[100,0],[0,6,7],[8,9],[0,6,8],[8,7,101],[6,0,9],[10,8],[0,9,6],[10,9],[0,11]]),
([v0,v1,v2,v7,v115,v78],[68,167,91,110,136,120,166,182,115],[],[[0,1],[2,1],[1,3],[0,1],[4,3],[0,2],[5],[6,2,7],[1,0],[8],[4,0,7],[1,2],[6,0,5],[1,5],[1,0]]),
([v40,v0,v1,v2,v115,v78],[110,4,88,56,166,14,6,68,86,90,137,55,115],[17],[[0,1,2],[3],[4],[0,5,1],[6,2,5],[7,0,8],[2,0],[2,9,7],[10,0],[11,7,100],[8,0,12],[9,2,7],[8,0,12],[2,11,9],[2,0,9]]),
([v41,v0,v1,v2,v115,v78],[110,6,62,167,48,14,4,91,67,136,66,120],[17],[[0,1,2],[3],[4],[0,5,6],[1,2,5],[2,0],[7,0,8],[2,8,7],[9,0],[10,7,100],[10,0,11],[2,10,8],[9,0,11],[8,2,7],[2,0,8]]),
([v116,v0,v1,v2,v7,v78],[17,167,11,182,166,91,68,110,89,60,86],[],[[0,1,2],[3,0,4],[3,4],[3,0,4],[1,4,5],[6,1],[5,1],[1,7],[8,3,4],[6,5],[9],[1,3],[10],[1,3],[1,3]]),
([v116,v40,v0,v1,v2,v78],[110,4,14,17,90,11,115,86,56,166,68,54],[23,17],[[0,1,2],[3,4,5],[6,0,7],[6,0,7],[4,0],[0,1,100],[8],[9],[4,2],[10,0,4],[100,0],[11,0],[11,10,101],[4,6],[4,6]]),
([v116,v41,v0,v1,v2,v78],[0,4,14,17,67,11,120,60,110,182,78,91,89,66],[30,17],[[0,1,2],[3,4,5],[6,0,7],[6,7],[4,7,8],[8,1,100],[9],[10],[4,2],[100,4,8],[11,4],[12,6,7],[13,11,101],[4,6],[4,6]]),
([v191,v0,v1,v2,v3,v78],[9,14,46,86,60,89,6,68,56,91,48,54,66,81],[],[[0,1,2],[3],[4],[3,1],[5,1,6],[7,8],[9,8],[7,10],[11,8,12],[8,7,9],[8,9,13],[10,7],[8,7,11],[10,9],[8,7,10]]),
([v192,v0,v1,v2,v3,v78],[0,110,6,48,4,68,14,60,66,81,67,97,62,88],[],[[0,1,2],[2,0],[3],[4,5,6],[2,0],[5,7],[8,7,9],[5,10],[9,7,8],[8,5],[7,11,9],[10,5],[7,5,11],[10,12,13],[7,5,9]]),
([v117,v0,v39,v2,v3,v78],[0,28,24,56,86,1,66,97,81,21,68,48,55,70],[],[[0,1,2],[3,4],[3,5,6],[3,7,8],[9,1],[7,3,10],[7,3,8],[10,11],[7,3,12],[1],[3,13],[11,10],[3,8,7],[11,12],[3,10,7]]),
([v193,v0,v1,v2,v3,v78],[46,4,9,56,14,6,81,86,97,55,90,54,91,88,62],[],[[0,1,2],[3],[1,0],[1,4],[5,4],[6,7,8],[8,6],[9,10,11],[6,7,9],[9,12],[6,8],[10,13,14],[7,6,8],[10,9],[6,12]]),
([v118,v0,v39,v1,v3,v78],[9,56,46,55,81,97,48,91,66,86,76],[],[[0,1,2],[1,0],[1,0,3],[1,4,5],[6,3],[4,1,7],[4,1,5],[7,6],[4,1,8],[9],[1,10],[6,7],[1,5,4],[6,8],[1,7,4]]),
([v0,v1,v194,v2,v3,v78],[81,56,97,46,91,48,110,86,54,68,82,37],[],[[0,1,2],[0,1,3],[2,0],[4,5],[0,1,6],[1,7],[1,4,8],[0,2],[5,9],[1,3],[0,4],[5,10,11],[1,0,2],[5,4],[0,4]]),
([v0,v39,v1,v2,v147,v78],[140,104,97,81,110,19,78,115,88,54,62],[],[[0,1,2],[3,0],[0,1,2],[4,1,5],[2,6],[7],[0],[2,4],[8,1],[0,9],[3,0],[10,0],[2,3],[8,1],[2,1,4]]),
([v149,v0,v39,v1,v2,v78],[110,15,19,4,81,56,97,66,86,60,62,79,54,88],[6],[[0,1,2],[3,0,4],[4,0],[5,0,6],[4,0],[4,3,100],[4,5,6],[6,4],[4,5,7],[8],[9],[10,11],[12,7],[10,7,11],[12,10,13]]),
([v0,v39,v1,v2,v3,v148],[142,110,97,81,88,54,115,117,62],[],[[0,1,2],[3,0],[0,1,2],[4,5],[2,1],[6],[0],[2,1],[4,6,7],[0,5],[3,0],[8,0],[2,1],[4,8],[2,1]]),
([v150,v0,v39,v1,v2,v3],[81,24,66,4,82,117,56,62,54,88,104,6,90,67,79,97],[6],[[0,1,2],[3,4,5,6],[7,1],[8,4,9],[0,10,6],[0,11,100],[0,9],[2,0],[2,8],[12],[13],[0,14],[8,2],[0,14],[15,0]]),
([v94,v1,v119,v2,v3,v78],[90,173,81,104,4,110,9,48,144,54,62,66,56,88],[],[[0],[],[1],[2,3,4],[0,5],[2,6],[7,8,9],[2,5],[7,3,10],[6,2],[10,5,9],[2,3,11],[12,2,9],[7,3,13],[2,3,5]]),
([v0,v39,v1,v195,v2,v78],[88,196,110,62,48,17,79,56,90,35,81,55],[],[[0,1,2],[3,0],[0,4,5],[0,1,2],[6,2,7],[8],[7,2,9],[1],[0,6],[7,1,10],[1,11],[3,0],[7,2,9],[0,2,4],[0,3]]),
([v196,v0,v39,v1,v2,v78],[17,48,11,35,4,79,81,34,56,110,54,65,86,60,14,78],[],[[0,1,2],[3,4,5],[6,0],[3,5,7],[1,8,9],[10,1,9],[10,1,9],[11,1,9],[5,8],[12],[13],[1,5,14],[10,11],[1,5,15],[1,5,15]]),
([v0,v39,v1,v197,v2,v3],[81,197,110,65,79,48,86,37,62,54,56],[],[[0,1,2],[0,1],[0,2],[3,0],[4,3,5],[6],[5,4,7],[1],[0,2],[3,1,8],[1,9],[0,1],[5,4,7],[0,2],[10,0,9]]),
([v198,v0,v39,v1,v2,v3],[26,56,21,37,6,79,62,36,48,110,55,66,86,60,14,78],[],[[0,1,2],[3,4,5],[6,0],[3,5,7],[1,8,9],[10,1,9],[10,1,9],[11,1,9],[5,8],[12],[13],[1,5,14],[10,11],[1,5,15],[1,5,15]]),
([v120,v121,v1,v2,v3,v78],[86,56,10,54,55,68,175,48,79,148,81,62,110],[],[[],[0,1],[2,0],[0,3],[3,4],[5],[6],[7,8],[1,8],[1,9,3],[1,8,10],[7,8,11],[1,3],[3,4],[1,12,7]]),
([v0,v122,v1,v2,v123,v78],[62,104,66,81,115,198,199,55,54],[],[[0,1],[0,1],[2,0],[0,1],[3,2],[4],[5],[],[0,1],[2,6,7],[2,6,3],[0,1],[6,3],[8,0,7],[0,1]]),
([v0,v39,v1,v2,v3,v199],[62,110,66,78,54,115,120,81,117,55],[],[[0,1],[0,1],[2,0],[0,3],[4,1],[5],[6],[7,1],[0,3,8],[4,2],[2,1,3],[0,2,8],[9,1,3],[4,0,3],[0,1,7]]),
([v0,v39,v1,v2,v3,v200],[62,6,104,66,54,115,120,81,78,55],[],[[0,1,2],[0,2],[3,0],[0,2],[4,3],[5],[6],[7,5],[0,2],[4,3],[3,8],[0,2],[9,4],[4,0,8],[0,2]]),
([v124,v125,v0,v1,v2,v78],[54,4,79,86,200,62,110,56,35,78,81,66,201],[],[[],[0,1,2],[3],[4],[5,6],[5,0],[7,8,9],[7,0],[2,9,10],[0,6],[11,5],[0,6],[0,12],[5,2],[0,2,9]]),
([v0,v39,v1,v2,v3,v201],[54,4,110,66,79,56,86,60,14,36,78,62,44],[],[[0,1,2],[0,2],[3,2],[3,0],[4,0,5],[6],[7],[1,2,8],[9,4,8],[0,3],[3,2,10],[11,3,4],[5,0],[9,0,4],[5,2,12]]),
([v0,v39,v202,v1,v2,v3],[54,4,110,66,36,79,37,86,60,81,62,56],[],[[0,1,2],[0,2],[0,2],[3,2],[3,0],[4,5,6],[7],[8],[1,2,9],[10,3,4],[0,5,6],[9,2],[0,3],[3,2,9],[11,0]]),
([v0,v126,v1,v2,v3,v127],[54,110,66,115,202,81,203,62,55],[],[[0,1],[0,1],[2,1],[2,0],[0,1],[3],[4],[5,1],[],[0,6],[2,1,5],[7,2,6],[8,0],[0,6],[5,1]]),
([v0,v39,v1,v2,v203,v78],[54,110,66,115,120,81,62,104,55],[],[[0,1],[0,1],[2,1],[2,0],[0,1],[3],[4],[5,1],[6,3,7],[0,2],[2,1,5],[6,2,7],[8,0],[0,6,8],[5,1]]),
([v0,v39,v1,v2,v204,v78],[66,4,110,55,78,81,86,60,62,65,54],[],[[0,1,2],[3,2],[0,2],[0,4],[5,0],[6],[7],[1,2,4],[8,4],[3,0],[0,2,4],[8,0,9],[3,2,4],[10,3],[5,2]]),
([v128,v129,v0,v1,v2,v3],[78,6,79,90,204,81,104,55,115,37,62,65,205],[],[[],[0,1,2],[3],[4],[5,6],[5,7],[8,0],[9,0],[2,0,10],[5,6],[11,5],[2,0,7],[0,12,7],[5,0,2],[7,0]]),
([v0,v39,v1,v2,v205,v78],[55,6,104,65,79,48,90,67,34,35,14,81,78,42],[],[[0,1,2],[0,2],[3,2],[4,0,5],[3,0],[6],[7],[8,4,9],[1,2,10],[0,3],[11,3,4],[3,2,12],[8,0,4],[5,0],[5,2,13]]),
([v0,v206,v39,v1,v2,v78],[55,48,65,104,34,79,35,56,90,67,62],[],[[0,1,2],[0,1,3],[0,1,3],[2,1,3],[2,0],[4,5,6],[7,2],[0,5,6],[1,3,7],[8],[9],[1,3,10],[0,2],[1,3,10],[1,0]]),
([v0,v39,v1,v2,v81,v91],[62,6,104,65,78,90,133,55,88],[6,29],[[0,1,2],[0,2],[3,0],[0,4],[100,2],[5],[6],[1,2,4],[0,4],[6,7],[3,2,4],[0,3,6],[7,2,4],[8,0],[101]]),
([v0,v207,v1,v2,v3,v78],[65,6,104,55,115,120,34,113,136,81,66,78,62],[],[[0,1,2],[3,2],[0,2],[3,0],[0,3],[4],[5],[6,1,7],[1,2,4],[0,8,3],[9,0,10],[0,2,10],[3,9,11],[8,2,3],[9,2,12]]),
([v208,v0,v1,v2,v3,v78],[104,65,115,0,113,34,36,55,136,66,78,110],[],[[0,1],[2,1],[3,2],[4,2,5],[0,2,6],[7,0],[1,0],[7,0],[1,7],[1,8,7],[9,1],[1,0,9],[7,10],[8,0,7],[0,11]]),
([v0,v39,v141,v2,v3,v78],[55,104,65,14,115,40,81,110,62,1,78,54],[],[[0,1],[0,1],[2,1],[0,1],[2,0],[2,3,4],[5],[6,3,7],[8,1],[0,9,2],[5,2],[2,1,8],[0,6,10],[11,0],[6,1,7]]),
([v0,v39,v1,v142,v3,v78],[65,104,54,55,115,0,136,66,88],[],[[0,1],[2,1],[0,1],[3,0],[0,3],[4],[2,4,5],[6,4],[6,1,4],[0,5,2],[7,0],[0,1,7],[3,2],[2,1,3],[8,1]]),
([v0,v209,v1,v2,v3,v78],[55,104,66,54,0,115,6,78,65,88],[],[[0,1],[0,1],[2,1],[0,1],[3,0],[2,4,5],[0,3],[6,5],[6,1,5],[0,2],[2,7],[8,1,2],[0,3],[3,0],[9,1]]),
([v0,v210,v1,v2,v3,v78],[54,6,110,88,115,120,65,66,55,81],[],[[0,1,2],[0,2],[3,2],[3,0],[0,2],[4],[5],[1,2,4],[1,4],[0,6],[7,2,6],[6,3,7],[8,0],[0,8],[3,2,9]]),
([v0,v211,v1,v2,v3,v78],[54,55,104,65,0,115,34,113,6,66,48,110],[],[[0,1],[0,2],[3,2],[1,0],[0,1],[3,4,5],[0,1],[6,5,7],[8,2,5],[0,3],[9,3],[3,2,9],[1,0],[0,1],[10,2,11]]),
([v0,v212,v1,v2,v3,v78],[54,6,104,66,90,67,34,14,113,78,48,55,88],[],[[0,1,2],[0,2],[3,2],[3,0],[0,3],[4],[5],[6,7,8],[1,2,7],[0,3],[3,9],[10,2,3],[11,0],[0,2,9],[10,2,12]]),
([v130,v0,v1,v80,v3,v78],[88,6,81,14,36,4,89,120,66,65,206],[44],[[0,1,2],[3,4],[1,3],[4,2,3],[0,3,1],[2,0],[0,5,6],[0,7],[2,7],[8,6,100],[2,7,8],[9,0,7],[2,6,5],[10],[0,2]]),
([v130,v0,v1,v2,v78,v91],[66,6,81,40,14,207,97,137,120,104,208],[],[[0,1,2],[0,3,4],[5],[1,4],[6,2],[2,6],[0,2],[2,0],[7,0],[0,7],[7,0],[2,0,6],[8,9],[6,2],[10]]),
([v0,v1,v2,v83,v3,v78],[81,121,88,104,182,66,54,122],[],[[0,1,2],[2,0],[0,1,3],[2,1,3],[0,4],[5,4,6],[1,4],[0,4,5],[1,2,4],[4,6],[7,0,4],[1,3,2],[0,1,7],[1,3,2],[0,3,2]]),
([v137,v0,v42,v2,v3,v78],[81,88,115,78,0,66,117,6,68,54,36,55],[44],[[0,1],[2,3],[2,4],[0,2,5],[6,1],[0,7,8],[1,0],[1,2],[0,2],[9,8,100],[10],[1,2,7],[11,0,2],[1,2,9],[0,1]]),
([v0,v42,v1,v80,v2,v91],[66,6,104,54,4,89,137,14,68,209,179,122,81],[],[[0,1,2],[3,2],[0,4,5],[0,2],[6,0],[7],[1,2,4],[3,8],[9],[0,2],[0,6],[6,0],[7],[10],[11,3,12]]),
([v0,v42,v1,v142,v2,v78],[66,138,68,81,122,104,14,97,0,137],[],[[0,1,2],[3,4,5],[0,4,5],[0,3],[3,0],[6],[3,2,7],[4,2,7],[1,2],[0,8,3],[0,9],[9,0],[6],[3,4],[4,5,6]]),
([v213,v0,v1,v2,v3,v78],[14,58,10,66,86,60,6,68,56,99,97,65,88,79],[6],[[0,1,2],[3,1,4],[5],[4,0],[6,0],[7,8],[3,8,100],[3,9],[10,3],[3,7],[3,9],[11,3],[8,7,9],[12,9,13],[8,7,10]]),
([v214,v0,v1,v2,v3,v78],[76,4,0,6,68,60,89,170,62,85],[],[[0],[1,2],[0,1],[1,0],[3,0],[4,5],[6,5],[4,7,8],[6,5],[9,4],[5,7],[8,4,6],[5,4,6],[9,7,8],[5,4,6]]),
([v132,v0,v1,v45,v3,v78],[66,4,62,34,14,210,6,91,120,97,211],[44],[[0,1,2],[0,3,4],[1,4],[1,4],[3,2,4],[2,5],[0,6,7],[0,8],[9,0],[0,5,100],[0,5,8],[2,0,5],[10],[2,7,6],[2,9]]),
([v132,v0,v1,v2,v3,v91],[66,4,62,40,14,212,88,120,137,110,213],[],[[0,1,2],[0,3,4],[5],[1,4],[6,2],[2,6],[0,2],[0,7],[8,0],[0,8],[0,7],[2,0,6],[7,9],[6,2],[10]]),
([v0,v1,v2,v84,v3,v78],[62,125,97,110,182,65,137,117,138],[],[[0,1,2],[2,0],[0,1,3],[0,4],[2,1,3],[5,4,6],[1,4],[1,2,4],[0,4,5],[4,7],[1,3,2],[8,0,4],[1,3,2],[0,1,7],[0,3,2]]),
([v135,v0,v79,v2,v3,v78],[62,125,97,106,35,34,14,137,63,115,54],[44],[[0,1,2],[1,3],[4,5],[1,2,4],[0,6,7],[0,1,8],[2,0],[0,9],[2,1,9],[10,8,100],[1,8],[5],[1,9],[10,0,9],[0,2]]),
([v0,v79,v1,v45,v2,v91],[137,4,110,62,6,91,97,106,138,63,214,65,215,178],[],[[0,1,2],[3,2],[0,4,5],[6,0],[0,2],[7],[1,2,4],[8,9],[10],[0,2],[11,0],[0,6,3],[12],[13],[6,3]]),
([v0,v79,v1,v142,v2,v3],[62,122,63,138,97,110,65,14,88,0,137],[],[[0,1,2],[0,3,4],[4,3,5],[4,0],[0,3,6],[7],[0,2,8],[3,2,8],[1,2],[0,9],[6,10],[10,4,6],[7],[0,3],[3,5,4]]),
([v215,v0,v1,v2,v3,v78],[97,58,14,65,137,76,4,63,48,88,99,66,68],[6],[[0,1,2],[3,1,4],[5],[0,2,6],[6,2],[7,0,8],[0,8,100],[9,3],[0,10],[3,7],[11,0,3],[3,9,10],[0,10,12],[8,7,9],[0,7,9]]),
([v216,v0,v1,v2,v3,v78],[76,6,0,4,68,67,91,63,170,85,81],[],[[0],[1,2],[0,1],[3,0],[1,0],[4,5],[6,5],[4,5],[7,8,9],[9,4],[10,6],[5,4],[9,4],[5,6],[5,4]]),
([v135,v0,v1,v2,v78,v91],[68,6,78,81,34,128,97,115,136,54,214],[],[[0,1],[2],[2,0],[1,0],[3,0,4],[3,5],[6,3],[3,7],[8,7],[9,5],[5,7],[3,4],[8,7],[6,3],[10]]),
([v0,v141,v1,v45,v2,v78],[81,138,110,97,121,91,14,1,55,207,125,136],[],[[0,1,2],[0,2],[3,4,5],[3,0],[0,2],[6],[0,2],[3,7],[1,6],[0,2],[8,9],[10,6,9],[6],[0,2],[11,6]]),
([v217,v0,v1,v2,v3,v78],[14,0,70,56,60,6,81,91,83,55,62,89,54],[6],[[0,1],[2],[3,4],[3,0],[5,0],[6,3,100],[7,3],[7,8,9],[6,3,8],[3,7,9],[3,7,6],[10,8,11],[3,6,8],[12,7],[3,7,6]]),
([v218,v0,v1,v2,v3,v78],[70,0,4,6,68,86,216,91,139,88,97,51,63],[],[[0],[0,1],[2,1],[1,0],[3,0],[4,5],[6,5,7],[4,8,9],[10,5,8],[11,4,6],[5,6,8],[11,4,6],[5,4,8],[9,7,12],[5,4,10]]),
([v137,v0,v1,v2,v3,v91],[63,4,78,62,36,131,88,115,136,55,209],[],[[0,1],[2],[2,0],[1,0],[3,0,4],[3,5],[6,3],[3,7],[8,7],[9,5],[5,7],[3,4],[8,7],[6,3],[10]]),
([v0,v141,v1,v80,v2,v3],[136,122,110,62,88,14,40,1,54,121],[],[[0,1,2],[3,0],[0,2],[4,2],[0,5],[5],[3,6],[0,7,4],[1,2,5],[3,6],[8,0],[9,2,5],[5],[3,2,5],[0,2,5]]),
([v219,v0,v1,v2,v3,v78],[14,0,70,48,67,4,62,91,54,83,81,55],[6],[[0,1],[2],[3,4],[5,0],[3,0],[6,3,100],[7,3],[6,3,7],[8,9],[3,7,8],[10,7],[3,9],[11,8],[3,6,7],[3,7]]),
([v220,v0,v1,v2,v3,v78],[70,0,6,4,63,90,217,91,139,97,51,110],[],[[0],[0,1],[2,1],[3,0],[1,0],[4,5],[6,5,7],[7,5],[4,8,9],[10,4,6],[10,4,6],[5,6,8],[9,8,11],[5,4,7],[5,4,7]]),
([v221,v0,v1,v2,v3,v78],[14,0,70,51,91,21,62,98,136,83],[],[[0,1],[2],[3,4],[3,0,4],[3,0,5],[6,7,8],[4,3],[4,3],[8,3,9],[3,4],[3,4],[3,9,7],[8,9],[7,4],[6,4,7]]),
([v222,v0,v1,v2,v3,v78],[14,58,10,85,63,76,6,97,100,137,99,107],[],[[0,1,2],[3,1,4],[5],[3,0,6],[3,0,4],[4,3],[7,8,9],[9,3,10],[4,3],[3,4],[9,4],[8,10],[3,10,11],[3,4],[7,4,11]]),
([v223,v0,v1,v2,v3,v78],[70,0,91,51,63,121,139,125],[],[[0],[0,1],[2,3],[1,0],[1,0],[4,5],[2,3],[2,3],[4,3],[3,2],[3,2],[3,6,5],[7,6],[5,2],[5,2]]),
([v224,v0,v1,v2,v3,v78],[97,6,62,14,0,78,120,85,91,137,110],[],[[0,1,2],[3,4],[5],[0,3,4],[1,2,3],[2,0],[0,2],[2,6],[0,6],[7,8,9],[9,0,6],[2,6,9],[0,6,10],[7,2],[0,8]]),
([v225,v0,v1,v2,v3,v78],[76,63,0,85,58,46,178,91,138,122,170],[],[[0],[1,2,3],[0,4,5],[6,3],[1,0,3],[1,3],[7,8],[7,3],[1,3],[3,1],[9,1],[8,10],[3,10,9],[3,1],[8,1,7]]),
([v226,v0,v1,v2,v3,v78],[110,6,97,78,0,63,62,115,51,136,88],[],[[0,1,2],[3],[3,4],[0,2],[1,3],[5,0,6],[2,0],[6,7],[2,0],[8,5,9],[8,0],[6,7,10],[2,0],[9,5,7],[2,0]]),
([v227,v0,v1,v2,v3,v78],[97,6,62,14,0,78,178,120,85,136,60,88,91],[17],[[0,1,2],[3,4],[5],[0,3,6],[1,2,3],[2,0],[0,2],[2,7],[0,7],[8,9,100],[10,0,7],[2,7,11],[0,7,9],[8,2],[0,12]]),
([v40,v0,v143,v2,v3,v78],[62,98,88,115,78,42,4,137,51,86,110,81],[17],[[0,1,2],[3,4],[5],[6,3],[0,2],[0,2],[2,0],[0,3],[7,3],[8,7,100],[7,3],[0,2],[9,3],[2,0],[0,10,11]]),
([v228,v0,v1,v2,v3,v78],[62,6,88,56,0,35,80,115,81,51,137,86,110],[17],[[0,1,2],[3],[3,4],[3,5,6],[0,2],[0,2],[2,0],[0,7],[8,7],[9,10,100],[8,7,10],[0,2],[11,7],[2,0],[0,12,8]]),
([v41,v0,v1,v144,v3,v78],[110,4,62,166,0,56,14,100,88,120,97,85,60],[17],[[0,1,2],[3],[4,1,5],[0,6,1],[7,2,6],[2,0],[8,0],[2,9],[10,0],[11,4,100],[12,0,9],[2,8],[10,0],[8,2],[2,0,10]]),
([v229,v0,v1,v2,v3,v78],[88,4,62,14,0,78,120,97,85,136,81,89],[17],[[0,1,2],[3,4],[5],[1,3],[0,2],[2,0],[0,2],[0,6],[7,6],[8,9,100],[10,6,7],[2,0],[7,6,9],[0,2],[0,11]]),
([v40,v0,v145,v2,v3,v78],[81,106,97,115,78,44,62,6,51,137,90,63],[17],[[0,1,2],[3,4],[5],[0,2],[6,3,7],[0,2],[2,0],[6,3],[0,3],[8,9,100],[0,2],[6,3,5],[2,0],[10,3],[0,11,6]]),
([v230,v0,v1,v2,v3,v78],[62,6,97,48,0,113,14,115,51,137,81,90,63],[17],[[0,1,2],[3],[1,4],[5,2,6],[0,6,1],[0,2],[2,0],[0,7],[2,7],[8,9,100],[8,2],[0,7,9],[2,7,10],[11,0,7],[0,12]]),
([v41,v0,v1,v146,v3,v78],[97,6,81,182,0,78,88,120,85,67,89],[17],[[0,1,2],[3],[4,1,5],[0,2],[1,3],[2,0],[0,2],[6,7],[0,7],[8,4,100],[2,0],[9,6,7],[0,2],[6,7,9],[0,10,6]])]
noncomputable def u15_D4 : List StD := [
([v0,v1,v48,v147,v78],[218,104,81,89,99,62,51,58,56,54],[],[[0,1,2],[3,1,4],[5,0],[2,0],[6,3],[2,0,7],[5,0,1],[8,0],[9,0],[2,1,5]]),
([v49,v0,v1,v147,v78],[89,81,99,51,4,54,97,62],[],[[0,1,2],[3,0],[4,0,1],[5,2],[1,6],[7,3,5],[0,3],[1,6],[3,0],[1,0,7]]),
([v0,v1,v48,v3,v148],[218,110,62,89,99,219,51,55,54],[],[[0,1,2],[3,1,4],[2,0],[3,0,5],[6,3],[6,0,1],[2,0,3],[7,0],[8,0],[2,1,3]]),
([v49,v0,v1,v3,v148],[89,220,99,51,97,55,54,62],[],[[0,1,2],[3,0],[4,0,5],[6,1],[5,4],[5,3,6],[0,3],[3,4],[3,0],[4,0,7]]),
([v55,v0,v2,v147,v78],[62,221,140,51,89,54,97,222,55],[],[[0,1,2],[3,2],[3,1,2],[0,1,4],[2,0,3],[0,3,5],[4,3],[6,4,7],[5,0,8],[0,4]]),
([v55,v0,v2,v3,v148],[54,97,182,142,51,89,55,62],[],[[0,1],[0,2,3],[4,1],[4,2,3],[1,4,5],[6,0],[0,4,5],[1,0,6],[0,6],[1,5,7]]),
([v150,v0,v1,v2,v147],[89,51,54,14,55,62,97],[],[[0,1],[1,0],[2,3,4],[5,0],[2,6],[0,1],[4,1,2],[1,0],[1,6],[4,0]]),
([v149,v0,v1,v2,v148],[62,51,54,14,97,55,89],[],[[0,1,2],[1,3],[4,2,3],[0,3,4],[0,4],[4,0],[2,1,5],[1,6],[0,6],[2,0,5]]),
([v149,v150,v0,v1,v2],[97,89,14,55,51,54],[],[[0,1,2],[3,4,5],[4,0],[0,1,3],[0,3],[4,1],[5,3],[3,0],[0,4,1],[3,1]]),
([v231,v0,v1,v3,v78],[89,58,10,51,55,54,97,62],[],[[0,1,2],[3,0],[4,0],[5,4],[4,6],[4,3,5],[0,3],[3,6],[3,0],[6,0,7]]),
([v0,v54,v2,v147,v78],[63,97,54,104,110,19,85,56,65,14],[],[[0,1,2],[1,3],[4,3,5],[0,6],[6,0],[7,0],[8,3,9],[1,4],[6,0],[1,0,4]]),
([v0,v54,v2,v3,v148],[63,97,54,110,88,85,65,66],[],[[0,1,2],[1,3],[4,5,6],[0,3,1],[5,0],[7,0],[6,4,7],[1,3],[4,0],[1,0,3]]),
([v232,v0,v2,v3,v78],[54,0,97,89,66,65,62,55],[],[[0,1,2],[0,1,3],[4,2,5],[5,3,4],[2,6],[4,0],[0,4],[2,0,7],[0,6,7],[2,3,6]]),
([v163,v0,v7,v3,v78],[97,58,89,166,62,182,167,56,65,223,55],[17],[[0,1,2],[100],[0,2,3],[4,5,6],[0,7],[4,8],[0,9,2],[7,0,8],[8,2,10],[0,2,4]]),
([v0,v39,v7,v3,v103],[55,166,89,56,62,224,28,104],[17],[[0,1,2],[3,4],[0,5],[2,0,6],[100],[1,2],[4,5,7],[0,5],[0,2],[4,2]]),
([v233,v1,v2,v3,v103],[4,166,60,86,14,89,28,63,62,88],[],[[0,1,2],[0,1,3],[0,4],[5,4,6],[1,7,5],[1,7],[8,5],[1,5],[9,7],[1,5]]),
([v0,v1,v2,v234,v3],[62,88,89,24,28,182,63,137,136],[],[[0,1],[1,0],[2,3,4],[0,5],[2,6],[0,1],[7,5],[1,0],[8,2],[0,2]]),
([v104,v0,v39,v7,v3],[224,28,89,62,104,65,55,166,56],[17],[[0,1,2],[3,4],[5,1,6],[3,2],[2,7],[3,8],[3,5],[100],[7,2],[6,5]]),
([v235,v0,v1,v2,v3],[89,28,24,106,125,107,62,122,88,167,91,55,137,63],[],[[0,1,2],[3,0,4],[5,6,7],[3,0],[6,8],[0,6,8],[6,9,10],[11,0],[12,10,13],[11,0]]),
([v104,v233,v1,v2,v3],[63,24,28,62,88,14,89,166],[],[[0,1,2],[3,1],[4,0],[3,0],[0,4,3],[4,3],[3,5],[0,6],[7,0],[7,6]]),
([v0,v166,v7,v3,v78],[62,58,63,56,104,223,135,55],[45],[[0,1,2],[100,0,3],[0,4],[2,5],[3,1,6],[5,2],[0,4],[3,6],[6,0,7],[0,2]]),
([v168,v0,v7,v3,v78],[46,166,9,56,63,104,182,137,79,225,223,78],[17],[[0,1,2],[100,0,3],[1,4],[5,6,7],[3,5],[8,5,9],[4,10],[3,8,11],[9,4,11],[9,4,10]]),
([v0,v39,v7,v3,v105],[63,166,56,137,226],[],[[0,1],[2,3],[3,4],[0,4],[4],[1,0],[3,4],[2,4],[4],[4]]),
([v106,v0,v39,v7,v3],[26,223,21,182,167,78,48,225,63,104,55],[17],[[0,1,2],[3,4],[5,0,6],[1,7,8],[8,1],[1,9],[10,7,9],[100],[1,3],[1,5]]),
([v0,v167,v170,v3,v78],[63,104,55,48,223,167,182,78],[17],[[0,1,2],[1,3],[2,1],[0,2,4],[100],[4,0],[5,1,6],[2,7],[3,0,2],[4,0]]),
([v0,v167,v173,v3,v78],[9,104,167,48,88,63,224,223],[17],[[0,1,2],[1,3],[4,1],[5,6,7],[100],[7,5],[2,1,4],[7,6],[3,1,6],[4,1]]),
([v233,v1,v2,v3,v105],[6,167,67,90,4,226],[],[[0,1,2],[0,1,3],[4,5],[0,5],[5],[5],[1,5],[5],[1,5],[1,5]]),
([v106,v233,v1,v2,v3],[26,6,14,62,88,167,104,4,63,89,166],[],[[0,1,2],[3,0],[4,3],[3,5,6],[1,5,6],[1,5,6],[7,2],[5,8,9],[10,8],[10,9]]),
([v179,v0,v7,v3,v78],[182,58,10,166,48,88,225,65,55,63],[17],[[0,1,2],[100],[3,0],[3,0],[4,5],[5,6,7],[7,8],[8,7],[4,5,8],[5,9]]),
([v0,v39,v7,v111,v78],[63,167,48,104,137,224,0,225,42],[17],[[0,1],[2,3],[4,3],[0,5,4],[100],[4,0],[1,3,5],[5,6],[2,0,5],[7,0,8]]),
([v233,v1,v2,v111,v78],[70,167,67,90,137,89,0,63,68,97,91],[],[[0,1,2],[1,3],[4,0],[1,0],[1,4,5],[4,6,7],[1,5,8],[9,5,8],[1,7,10],[1,5,8]]),
([v0,v1,v2,v236,v78],[63,104,81,89,97,137,182,136],[],[[0,1,2],[3,1,4],[5,1],[0,6,2],[0,3],[2,0,4],[5,1,6],[4,2],[7,0,6],[2,0,6]]),
([v112,v0,v39,v7,v78],[224,19,91,137,63,56,65,223,78],[17],[[0,1,2],[3,4],[5,1,6],[7,2,4],[2,7],[3,5],[3,7,4],[100],[3,2],[6,4,8]]),
([v237,v0,v1,v2,v78],[91,19,15,63,83,76,166,86,97,65,89,62,88],[],[[0,1,2],[3,0,4],[5,6,7],[3,0,8],[3,6],[0,6],[3,6],[9,0,3],[9,10,11],[12,0,3]]),
([v112,v233,v1,v2,v78],[4,15,65,166,63,89,14,62,88],[],[[0,1,2],[3,1,4],[3,5],[3,4],[0,2],[0,3,5],[2,6],[3,4,5],[7,5],[8,4]]),
([v0,v182,v7,v3,v78],[182,58,10,97,48,91,225,110,188,65],[45],[[0,1,2],[100,3,4],[5,6],[3,7],[4,1,8],[3,0,7],[6,0],[8,3,9],[4,8],[3,5]]),
([v184,v0,v7,v3,v78],[46,166,9,56,182,117,36,110,91,224,225,79,223],[17],[[0,1,2],[100,0,3],[1,4],[5,4,6],[3,7],[8,9,10],[11,7,12],[3,7,9],[10,9],[10,7]]),
([v0,v39,v7,v115,v78],[91,167,48,88,225,137,227],[],[[0,1],[2,3],[0,4],[5,6],[6],[5,6],[1,0],[6],[2,3,6],[3,0,4]]),
([v116,v0,v39,v7,v78],[17,225,11,182,166,78,56,223,91,110,65],[17],[[0,1,2],[3,4],[5,0,6],[1,7,8],[8,1],[1,9],[10,7,9],[100],[1,3],[1,5]]),
([v0,v183,v186,v3,v78],[91,166,56,110,224,225,81],[17],[[0,1],[2,3],[0,4,5],[6,3],[100],[1,3,4],[5,0],[2,0,4],[5,4],[5,0]]),
([v0,v183,v189,v3,v78],[9,110,167,48,91,225,65,166,182,56,78],[17],[[0,1,2],[1,3],[4,5],[6,1],[100],[7,1,8],[2,4],[9,1,6],[3,10],[5,1]]),
([v233,v1,v2,v115,v78],[6,167,67,90,11,14,4,137,91,81,88,62,166,97],[],[[0,1,2],[0,1,3],[4,5,6],[0,5],[1,7,8],[7,4,9],[1,10,11],[12,9,13],[1,8],[1,8]]),
([v116,v233,v1,v2,v78],[17,4,97,81,166,91,60,6,228],[],[[0,1,2],[3,0],[2,3],[2,4,5],[1,4,6],[1,4,5],[7,8],[8],[8],[8]]),
([v149,v0,v39,v7,v78],[91,15,19,166,80,229,56,65,97,223,79,88,55],[17],[[0,1,2],[3,4,5],[6,0,7],[5,0],[0,3],[6,8],[7,9,10],[100],[11,0,10],[7,10,12]]),
([v150,v0,v39,v7,v3],[97,24,79,166,230,48,55,91,167,225,65],[17],[[0,1,2],[3,2,4],[5,1,6],[0,7],[0,8,7],[0,5],[2,9],[100],[0,2],[6,0,10]]),
([v238,v1,v2,v3,v78],[86,56,10,65,55,79,62,97,48,110],[36],[[0,1],[2,0,1],[0,3],[3,4],[1,100,4],[1,3],[3,5,6],[1,5,7],[8,4],[1,9,7]]),
([v196,v0,v39,v7,v78],[17,225,11,35,166,79,65,56,223,110,182,78],[17],[[0,1,2],[3,4,5],[6,0,7],[1,8,9],[6,1,9],[1,9],[5,8],[100],[1,5,10],[1,5,11]]),
([v198,v0,v39,v7,v3],[26,223,21,37,167,182,78,48,225,110,55,224],[17],[[0,1,2],[3,4,5],[6,0,7],[1,8,9],[10,1,9],[1,9],[10,8,11],[100],[1,5],[1,6]]),
([v239,v0,v1,v2,v78],[55,6,65,115,34,110,78,88,79],[46],[[0,1,2],[3,2],[0,3,4],[1,3],[0,5],[2,5],[2,0],[0,100],[2,6],[7,0,8]]),
([v0,v39,v7,v3,v199],[65,110,231,88,97,82,117,78],[47],[[0,1],[1,2],[3,0],[0,1],[100],[4,1],[3,5,6],[2,0],[0,3,7],[3,1,4]]),
([v125,v0,v1,v2,v200],[110,65,115,120,78,97,55,137,88],[],[[0,1],[2,1],[3,4],[0,2,5],[6,0],[1,0],[1,4],[1,7],[1,0,4],[8,0]]),
([v0,v39,v7,v3,v200],[97,167,89,48,88,224,137,55],[17],[[0,1,2],[0,3],[4,5],[0,5],[100],[0,2,6],[1,5],[7,0,5],[3,2,5],[0,2,4]]),
([v0,v39,v7,v3,v201],[88,110,56,224,137,44],[17],[[0,1],[0,2],[0,3],[4,1],[100],[4,1,3],[0,3,4],[2,1,3],[0,3],[0,1,5]]),
([v0,v39,v202,v7,v3],[88,110,137,56,225,65,89,97,55],[17],[[0,1],[2,1],[0,3],[0,4,5],[0,6],[100],[2,1,7],[4,0,8],[0,1,4],[3,1,5]]),
([v240,v0,v1,v2,v3],[97,6,55,115,78,37,4,48,110,81],[48],[[0,1,2],[3,4],[5,1,2],[0,3,6],[2,0],[0,7,8],[2,4],[2,100],[9,0],[0,4,2]]),
([v0,v39,v7,v203,v78],[55,110,232,224,81,88,104],[49],[[0,1],[1,2],[0,3],[4,0],[100],[4,1],[5,3,6],[0,1,3],[2,0],[4,1]]),
([v129,v0,v1,v2,v204],[81,55,115,78,120,88,137,65],[],[[0,1],[2,3],[4,1],[0,2,5],[0,5],[5,0],[1,3],[1,6,7],[0,3,6],[1,0,3]]),
([v0,v39,v7,v204,v78],[81,110,233,88,224,137,55],[17],[[0,1],[0,2],[3,4],[0,1],[100],[0,1],[3,4,5],[6,0,4],[2,3,4],[0,1]]),
([v0,v39,v7,v205,v78],[55,167,110,48,137,35,182,225],[17],[[0,1,2],[2,3],[4,0],[4,0],[100],[4,2,5],[1,6],[0,2],[3,0],[7,2]]),
([v0,v206,v39,v7,v78],[55,225,65,110,34,35,104,88],[17],[[0,1,2],[0,1,3],[1,3],[2,0],[4,3,5],[0,2],[1,3],[100],[1,6,7],[1,0]]),
([v208,v0,v1,v2,v81],[110,6,55,115,78,38,88,137,65],[],[[0,1,2],[3,4],[5,2,3],[0,3,1],[2,0],[6,0],[2,4],[2,7,8],[7,0,4],[2,0,4]]),
([v0,v209,v7,v3,v78],[55,65,88,56,166,80,35,182,117,110,104],[],[[0,1],[2,3],[0,1],[1,0],[0,1],[4,5,6],[2,7,8],[0,1],[1,0],[2,9,10]]),
([v0,v210,v7,v3,v78],[88,110,56,224,65,166,117,81],[17],[[0,1],[0,2],[0,3],[4,1],[100],[5,1,3],[0,3,6],[2,1,3],[4,0,3],[0,1,7]]),
([v0,v211,v7,v3,v78],[65,110,48,55,34,182,166,225],[],[[0,1],[1,2],[3,0],[0,1],[0,3],[4,1,5],[6,5],[3,0],[0,3],[7,1]]),
([v0,v212,v7,v3,v78],[65,166,104,48,55,182,225,88],[17],[[0,1,2],[2,3],[4,0],[0,4],[100],[1,5],[1,2,5],[4,0],[0,2,4],[6,2,7]]),
([v130,v0,v1,v80,v91],[88,122,81,14,131,110,137,234,179],[50],[[0,1,2],[3,4],[1,3],[0,2],[2,0],[0,1,5],[6,1,5],[6,7,100],[2,0],[8]]),
([v137,v0,v42,v2,v91],[110,4,88,14,40,137,6,104,55,209,81],[50],[[0,1,2],[0,3,1],[3,4],[5,2,3],[2,6,7],[2,0],[5,0],[8,0,100],[9],[2,8,10]]),
([v132,v0,v1,v45,v91],[110,137,55,128,6,235,62,104,210,178],[50],[[0,1],[2,1,3],[0,4],[5,2,6],[2,0],[1,4,7],[1,0],[1,0,100],[1,8,6],[9]]),
([v135,v0,v79,v2,v91],[55,6,97,110,207,137,104,214,81],[50],[[0,1,2],[1,3],[0,3,4],[5,2,3],[0,3],[2,3],[5,0],[0,6,100],[7],[2,0,8]])]
noncomputable def u15_D3 : List StD := [
([v163,v233,v3,v78],[104,10,89,81,137,79,62,65,55],[],[[0,1,2],[3,2,4],[4,5,6],[4,7],[2,8,3],[3,2,6]]),
([v233,v39,v3,v103],[55,110,65,137,89,104,62],[],[[0,1],[0,2],[3,0],[3,1,4],[3,5,6],[6,1,4]]),
([v0,v39,v234,v3],[62,110,137,224],[],[[0,1],[2,1],[0,3],[0,3,2],[2,1,3],[0,1,3]]),
([v104,v233,v39,v3],[81,24,104,137,62,167,89,78],[],[[0,1,2],[3,2,4],[0,2,4],[0,5,6],[3,7],[0,6,3]]),
([v168,v233,v3,v78],[46,137,9,89,91,55,236],[],[[0,1,2],[1,3],[1,4],[5,6],[3,5,6],[6]]),
([v233,v39,v3,v105],[89,104,81,137,62],[],[[0,1,2],[3,1],[0,4],[2,0,3],[3,1,4],[2,0,4]]),
([v106,v233,v39,v3],[26,62,21,104,89,55,166],[],[[0,1,2],[1,3],[1,3],[4,3,5],[5,3],[6,4]]),
([v233,v167,v3,v78],[9,137,46,55,187],[],[[0,1,2],[3,4],[4],[1,4],[1,4],[4]]),
([v179,v233,v3,v78],[55,58,89,137,82,37,65,62],[],[[0,1,2],[3,2],[3,4,5],[0,6],[2,0,3],[7,2]]),
([v233,v39,v111,v78],[89,104,55,137,91,81],[],[[0,1,2],[3,1],[0,2,3],[3,0],[3,1,4],[5,0,4]]),
([v0,v39,v236,v78],[89,104,81,137,224],[],[[0,1,2],[3,1],[0,4,2],[2,0,3],[3,1,4],[2,0,4]]),
([v112,v233,v39,v78],[137,15,91,89,81,166,78],[],[[0,1,2],[0,3],[4,2],[2,5],[0,6],[0,2]]),
([v184,v233,v3,v78],[46,137,9,89,91,78,56,65,223,104],[],[[0,1,2],[1,3],[1,3],[4,5,6],[7,5],[8,4,9]]),
([v233,v39,v115,v78],[56,166,91,78,65,110,81,137],[],[[0,1,2],[0,3],[4,3],[1,5,6],[7,2],[6,2]]),
([v116,v233,v39,v78],[17,56,78,81,166,89,230,65,167,91],[],[[0,1,2],[3,4,5],[3,6,5],[1,4,5],[5,2,7],[8,9]]),
([v233,v183,v3,v78],[9,166,46,56,65,195],[],[[0,1,2],[3,4],[4,5],[1,5],[5],[5]]),
([v149,v233,v39,v78],[56,15,65,166,80,81,91,237,137],[],[[0,1,2],[3,4,5],[5,6],[0,3,6],[2,7],[8,6]]),
([v150,v233,v39,v3],[81,24,237,137,82,91,167,89],[],[[0,1,2],[3,4,5],[0,5],[0,6,5],[3,2],[0,7,3]]),
([v196,v233,v39,v78],[17,81,11,91,89,238],[],[[0,1,2],[1,3],[1,3],[4,5],[4,5],[5]]),
([v198,v233,v39,v3],[26,48,78,37,89,36,91,229,56,166,110,85],[],[[0,1,2],[3,4,5],[6,4,7],[1,7,6],[6,2,8],[9,10,11]]),
([v233,v39,v3,v199],[231,110,78,89,48,81,230,82,117],[],[[0,1],[0,2],[3,1,4],[5,1],[6,7,8],[5,1]]),
([v233,v39,v3,v200],[239,167,89,78,48,81,137,82,230],[],[[0,1,2],[0,3],[2,3,4],[5,2,6],[1,7,8],[5,2,8]]),
([v233,v39,v3,v201],[56,166,110,78,137,240,230,44],[],[[0,1,2],[0,3],[4,2],[1,2,5],[4,5],[6,2,7]]),
([v0,v39,v241,v3],[91,110,65,137,182,56],[],[[0,1,2],[3,1],[0,2,3],[2,0,3],[3,1,4],[5,0,2]]),
([v233,v39,v202,v3],[56,166,110,237,241,36,89,37,81],[],[[0,1,2],[3,2,4],[0,3],[5,6,7],[1,2,8],[8,2]]),
([v233,v39,v203,v78],[81,110,91,78,56,85,104],[],[[0,1],[2,3,4],[0,1],[0,1],[5,2,6],[0,1]]),
([v233,v39,v204,v78],[56,166,110,78,81,85,91,137],[],[[0,1,2],[0,3],[4,2],[1,2,4],[5,6,7],[4,2]]),
([v233,v39,v205,v78],[81,110,91,78,137,104,240],[],[[0,1],[2,3,4],[0,1],[0,1],[4,5,6],[0,1]]),
([v0,v39,v242,v78],[81,110,91,104,137,182],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3,5],[0,1]]),
([v233,v206,v39,v78],[91,104,137,237,241,35,81,62],[],[[0,1,2],[3,1,4],[2,3],[2,0,5],[6,0],[2,1,7]]),
([v233,v209,v3,v78],[91,104,62,137,78,80,35],[],[[0,1,2],[0,1,2],[3,4],[3,5,6],[2,0,1],[2,0,1]]),
([v233,v210,v3,v78],[62,110,78,137,35,91,81],[],[[0,1],[0,2],[3,1],[3,1,4],[0,5,3],[0,1,6]]),
([v233,v211,v3,v78],[81,110,137,78,82,37],[],[[0,1],[2,3],[0,1],[0,1],[2,4,5],[0,1]]),
([v233,v212,v3,v78],[81,104,137,78,91,62],[],[[0,1],[2,1],[0,3],[0,4,2],[2,1,4],[0,1,5]])]
def u15_D2 : List StD := []
theorem u15_I2 : LevelN u15_R u15_T 2 u15_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C3x0 : levelOK u15_T u15_K u15_P 2 (u15_D2.map Prod.fst) ((u15_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C3x1 : levelOK u15_T u15_K u15_P 2 (u15_D2.map Prod.fst) ((u15_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C3x2 : levelOK u15_T u15_K u15_P 2 (u15_D2.map Prod.fst) ((u15_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem u15_I3 : LevelN u15_R u15_T 3 u15_D3 := levelStep u15_B u15_W u15_Q u15_I2 (chunks 16 u15_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C3x0
  · exact u15_C3x1
  · exact u15_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C4x0 : levelOK u15_T u15_K u15_P 3 (u15_D3.map Prod.fst) ((u15_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C4x1 : levelOK u15_T u15_K u15_P 3 (u15_D3.map Prod.fst) ((u15_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C4x2 : levelOK u15_T u15_K u15_P 3 (u15_D3.map Prod.fst) ((u15_D4.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C4x3 : levelOK u15_T u15_K u15_P 3 (u15_D3.map Prod.fst) ((u15_D4.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C4x4 : levelOK u15_T u15_K u15_P 3 (u15_D3.map Prod.fst) ((u15_D4.drop (4*16)).take 16) = true := by decide +kernel
theorem u15_I4 : LevelN u15_R u15_T 4 u15_D4 := levelStep u15_B u15_W u15_Q u15_I3 (chunks 16 u15_D4 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C4x0
  · exact u15_C4x1
  · exact u15_C4x2
  · exact u15_C4x3
  · exact u15_C4x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x0 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x1 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x2 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x3 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x4 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x5 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x6 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x7 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x8 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x9 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x10 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x11 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x12 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (12*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C5x13 : levelOK u15_T u15_K u15_P 4 (u15_D4.map Prod.fst) ((u15_D5.drop (13*16)).take 16) = true := by decide +kernel
theorem u15_I5 : LevelN u15_R u15_T 5 u15_D5 := levelStep u15_B u15_W u15_Q u15_I4 (chunks 16 u15_D5 14 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C5x0
  · exact u15_C5x1
  · exact u15_C5x2
  · exact u15_C5x3
  · exact u15_C5x4
  · exact u15_C5x5
  · exact u15_C5x6
  · exact u15_C5x7
  · exact u15_C5x8
  · exact u15_C5x9
  · exact u15_C5x10
  · exact u15_C5x11
  · exact u15_C5x12
  · exact u15_C5x13
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x0 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x1 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x2 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x3 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x4 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x5 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C6x6 : levelOK u15_T u15_K u15_P 5 (u15_D5.map Prod.fst) ((u15_D6.drop (6*16)).take 16) = true := by decide +kernel
theorem u15_I6 : LevelN u15_R u15_T 6 u15_D6 := levelStep u15_B u15_W u15_Q u15_I5 (chunks 16 u15_D6 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C6x0
  · exact u15_C6x1
  · exact u15_C6x2
  · exact u15_C6x3
  · exact u15_C6x4
  · exact u15_C6x5
  · exact u15_C6x6
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C7x0 : levelOK u15_T u15_K u15_P 6 (u15_D6.map Prod.fst) ((u15_D7.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C7x1 : levelOK u15_T u15_K u15_P 6 (u15_D6.map Prod.fst) ((u15_D7.drop (1*16)).take 16) = true := by decide +kernel
theorem u15_I7 : LevelN u15_R u15_T 7 u15_D7 := levelStep u15_B u15_W u15_Q u15_I6 (chunks 16 u15_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C7x0
  · exact u15_C7x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u15_C8x0 : levelOK u15_T u15_K u15_P 7 (u15_D7.map Prod.fst) ((u15_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem u15_I8 : LevelN u15_R u15_T 8 u15_D8 := levelStep u15_B u15_W u15_Q u15_I7 (chunks 16 u15_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u15_C8x0
  ))
theorem u15_L : LowN u15_R u15_T 9 := lowSearch u15_B u15_I8 (by decide +kernel)

def u16_T : Nat := 0xe880e880e880e880e880e880e880e880
def u16_R : List Nat := [0, 1, 2, 3]
def u16_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem u16_B : baseOK u16_T u16_R u16_E = true := by decide +kernel
theorem u16_S0 : SliceN u16_R u16_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) u16_B u2_B u2_L (by decide +kernel)
theorem u16_S1 : SliceN u16_R u16_T (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]) := mkSlice (w:=2) u16_B u2_B u2_L (by decide +kernel)
theorem u16_S2 : SliceN u16_R u16_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) u16_B u2_B u2_L (by decide +kernel)
theorem u16_S3 : SliceN u16_R u16_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) u16_B u2_B u2_L (by decide +kernel)
theorem u16_S4 : SliceN u16_R u16_T (0x55555555555555555555555555555555,2,[1, 2, 3]) := mkSlice (w:=0) u16_B u6_B u6_L (by decide +kernel)
theorem u16_S5 : SliceN u16_R u16_T (0x88888888888888888888888888888888,1,[2, 3]) := mkSlice (w:=3) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S6 : SliceN u16_R u16_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,1,[1, 3]) := mkSlice (w:=5) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S7 : SliceN u16_R u16_T (0xaa00aa00aa00aa00aa00aa00aa00aa00,1,[1, 2]) := mkSlice (w:=9) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S8 : SliceN u16_R u16_T (0x33333333333333333333333333333333,2,[0, 2, 3]) := mkSlice (w:=0) u16_B u6_B u6_L (by decide +kernel)
theorem u16_S9 : SliceN u16_R u16_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]) := mkSlice (w:=6) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S10 : SliceN u16_R u16_T (0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]) := mkSlice (w:=10) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S11 : SliceN u16_R u16_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]) := mkSlice (w:=0) u16_B u6_B u6_L (by decide +kernel)
theorem u16_S12 : SliceN u16_R u16_T (0xf000f000f000f000f000f000f000f000,1,[0, 1]) := mkSlice (w:=12) u16_B u0_B u0_L (by decide +kernel)
theorem u16_S13 : SliceN u16_R u16_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S14 : SliceN u16_R u16_T (0x30303030303030303030303030303030,1,[0, 3]) := mkSlice (w:=4) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S15 : SliceN u16_R u16_T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]) := mkSlice (w:=0) u16_B u6_B u6_L (by decide +kernel)
theorem u16_S16 : SliceN u16_R u16_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S17 : SliceN u16_R u16_T (0x33003300330033003300330033003300,1,[0, 2]) := mkSlice (w:=8) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S18 : SliceN u16_R u16_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]) := mkSlice (w:=2) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S19 : SliceN u16_R u16_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S20 : SliceN u16_R u16_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S21 : SliceN u16_R u16_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S22 : SliceN u16_R u16_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S23 : SliceN u16_R u16_T (0xf000f000f000f000f000f000f000f00,1,[0, 1]) := mkSlice (w:=8) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S24 : SliceN u16_R u16_T (0xf000f000f000f000f000f000f000f0,1,[0, 1]) := mkSlice (w:=4) u16_B u1_B u1_L (by decide +kernel)
theorem u16_S25 : SliceN u16_R u16_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) u16_B u1_B u1_L (by decide +kernel)
def u16_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]),(0x55555555555555555555555555555555,2,[1, 2, 3]),(0x88888888888888888888888888888888,1,[2, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,1,[1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa00,1,[1, 2]),(0x33333333333333333333333333333333,2,[0, 2, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]),(0xf000f000f000f000f000f000f000f000,1,[0, 1]),(0x50505050505050505050505050505050,1,[1, 3]),(0x30303030303030303030303030303030,1,[0, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]),(0x55005500550055005500550055005500,1,[1, 2]),(0x33003300330033003300330033003300,1,[0, 2]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0x44444444444444444444444444444444,1,[2, 3]),(0xf000f000f000f000f000f000f000f00,1,[0, 1]),(0xf000f000f000f000f000f000f000f0,1,[0, 1]),(0x22222222222222222222222222222222,1,[2, 3])]
theorem u16_Y : ∀ s ∈ u16_Z, SliceN u16_R u16_T s := by
  unfold u16_Z
  simp only [List.forall_mem_cons]
  exact ⟨u16_S0,u16_S1,u16_S2,u16_S3,u16_S4,u16_S5,u16_S6,u16_S7,u16_S8,u16_S9,u16_S10,u16_S11,u16_S12,u16_S13,u16_S14,u16_S15,u16_S16,u16_S17,u16_S18,u16_S19,u16_S20,u16_S21,u16_S22,u16_S23,u16_S24,u16_S25,by simp⟩
def u16_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[(0,0,1)]),(3,[(0,0,1)]),(6,[]),(1,[(0,0,1)]),(3,[(0,0,2)]),(7,[]),(1,[(0,0,2)]),(2,[(0,0,2)]),(8,[]),(9,[]),(0,[(0,0,1)]),(3,[(0,1,2)]),(10,[]),(0,[(0,0,2)]),(2,[(0,1,2)]),(1,[(0,1,2)]),(0,[(0,1,2)]),(11,[]),(12,[]),(1,[(2,0,1)]),(0,[(2,0,1)]),(0,[(3,0,1)]),(13,[]),(14,[]),(1,[(3,0,1)]),(1,[(2,0,2)]),(0,[(2,0,2)]),(0,[(3,0,2)]),(15,[]),(16,[]),(17,[]),(1,[(3,0,2)]),(2,[(2,0,1)]),(18,[]),(3,[(2,0,1)]),(19,[]),(20,[]),(21,[]),(2,[(3,0,1)]),(22,[]),(3,[(2,0,2)]),(0,[(2,1,2)]),(0,[(3,1,2)]),(23,[]),(2,[(3,0,2)]),(2,[(2,0,2)]),(24,[]),(25,[]),(3,[(3,0,1)]),(3,[(3,0,2)]),(3,[(2,1,2)]),(3,[(3,1,2)]),(1,[(3,1,2)]),(0,[(1,1,2)]),(2,[(3,1,2)]),(1,[(2,1,2)]),(0,[(1,0,1)]),(0,[(1,0,2)]),(3,[(0,0,2),(0,1,2)]),(3,[(0,0,1),(0,1,2)]),(3,[(0,0,1),(0,0,2)]),(2,[(0,0,1),(0,0,2)]),(3,[(0,0,2),(2,1,3)]),(1,[(0,0,1),(0,0,2)]),(0,[(0,0,2),(0,1,2)]),(0,[(0,0,1),(0,1,2)]),(0,[(0,0,1),(0,0,2)])]
def u16_P : List (Nat × Nat) := [(12,13),(12,14),(5,7),(10,11),(10,14),(6,7),(6,14),(9,11),(9,13),(5,13),(3,7),(3,11),(2,11),(4,13),(2,7),(8,13),(1,11),(4,14),(1,7),(8,14),(4,7),(8,11),(1,13),(2,14),(0,11),(0,13),(0,14),(0,7)]
def u16_K : List CutV := u16_C.map (mkCut u16_Z)
theorem u16_W : ∀ c ∈ u16_K, CutP u16_R u16_T c := cutsGood u16_Y (by decide +kernel)
theorem u16_Q : u16_P.all (sepOK u16_T) = true := by decide +kernel
noncomputable def u16_D6 : List StD := [
([v0,v1,v2,v3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11],[[100,101,0,1,102],[103,104,0,2,100],[105,106,0,3,100],[107,108,1,2,101],[102,109,1,3,101],[110,111,2,3,104]])]
noncomputable def u16_D5 : List StD := [
([v30,v0,v1,v2,v3],[0,1,4,2,5,3,6,7],[8,10,9,11,4,6],[[0,1],[0],[2,100,3,4,101],[2,102,5,4,103],[0,1],[0,104,6],[0,105,7],[1,100,6],[1,102,7],[101,103,7,6,100]]),
([v33,v0,v1,v2,v3],[0,2,4,1,8,3,9,10],[7,2,11,9,1,6],[[0,1],[2,100,3,4,101],[0],[2,102,5,4,103],[0,104,6],[0,1],[0,105,7],[1,100,6],[101,103,7,6,100],[1,102,7]]),
([v36,v0,v1,v2,v3],[0,3,4,1,11,2,12,13],[2,7,10,8,1,4],[[0,1],[2,100,3,4,101],[2,102,5,4,103],[0],[0,104,6],[0,105,7],[0,1],[101,103,7,6,100],[1,100,6],[1,102,7]]),
([v0,v39,v1,v2,v3],[14,15,0,16,1,2,17,3],[3,5,0,6,11,9],[[0,100,1,2,101],[0,102,1,3,4],[5,100,3],[101,103,6,3,100],[4,5],[4],[0,104,6,1,7,103],[4,5],[0,105,4,6],[5,104,6]]),
([v0,v42,v1,v2,v3],[14,18,0,19,1,20,3,2],[5,3,0,4,10,8],[[0,100,1,2,101],[0,102,1,3,4],[101,103,5,3,100],[6,100,3],[4,6],[0,104,5,1,7,103],[4],[0,105,4,5],[4,6],[6,104,5]]),
([v0,v1,v45,v2,v3],[21,22,23,24,0,2,3,1],[0,1,2,5,3,7],[[100,101,0,1,102],[2,103,3,1,4,100],[2,104,3,1,5],[6,103,1],[2,102,3,0,7,101],[2,105,3,0,5],[6,102,0],[5,6],[5],[5,6]])]
noncomputable def u16_D4 : List StD := [
([v94,v0,v1,v2,v3],[25,26,27,23,3,6,16,9,4,14],[],[[0],[1],[2],[3,4],[5,6,7],[3,5],[8,6],[3,5],[9,7],[3,5]]),
([v49,v0,v1,v2,v3],[1,0,16,23,3,28,27,6,29,30],[],[[0,1],[1,0],[2],[3,4,5],[5,6],[3,6,7],[5,6],[3,5],[8,9],[3,5]]),
([v243,v0,v1,v2,v3],[31,32,14,2,33,19,12,4,34,7],[],[[0],[1],[2,3],[4],[2,5,6],[7,5],[6,5,7],[2,6],[2,6],[8,9]]),
([v51,v0,v1,v2,v3],[1,0,34,2,35,19,33,7,36,37],[],[[0,1],[1,0],[2,3,4],[5],[4,6],[4,6],[2,6,7],[8,9],[2,4],[2,4]]),
([v30,v33,v1,v2,v3],[6,38,0,9,23,4,10,14,7,29,39],[12,13],[[0,1],[2],[3,0,4],[5,6,100],[0,3,7],[2],[5,8,101],[0,3],[9,3],[10,0]]),
([v30,v36,v1,v2,v3],[7,40,0,4,13,34,1,14,6,36,12,41],[14,15],[[0,1],[2],[3,4,100],[3,0,5],[0,6,7],[3,8,101],[2],[9,10],[0,10],[11,0]]),
([v30,v0,v39,v2,v3],[38,16,23,14,17,4,6,28,27,7,42],[16,17],[[0],[1,0],[1,0,2],[3,4,100],[3,1,5],[1,6],[7,1],[8],[3,9,101],[10,6]]),
([v30,v0,v42,v2,v3],[40,19,14,20,34,4,35,7,6,33,43],[18,19],[[0],[1,0],[2,3,100],[1,0,4],[2,1,5],[6,1],[1,7],[2,8,101],[9],[10,6]]),
([v55,v0,v1,v2,v3],[2,0,16,14,3,39,26,44,45],[],[[0,1],[2],[1,0],[3,4,5],[3,5],[5,6,7],[8,6],[3,7,8],[3,5],[5,7]]),
([v244,v0,v1,v2,v3],[46,4,1,47,48,22,23,13,34,10],[],[[0],[1,2],[3],[4],[1,5],[1,5],[1,5],[6,7],[8,9],[5,7,6]]),
([v57,v0,v1,v2,v3],[46,10,34,1,35,22,48,49,50],[],[[0,1],[2,3,4],[2,0,1],[5],[4,6],[1,6,4],[2,1],[7,8],[2,1],[2,1]]),
([v33,v36,v1,v2,v3],[34,2,51,35,12,0,3,9,23,49,13,52],[20,21],[[0,1,2],[3,4,100],[5],[0,6],[3,7,101],[3,1,8],[5],[9,10],[11,3],[3,10]]),
([v33,v0,v39,v1,v3],[25,16,14,23,17,35,9,45,26,53],[22,23],[[0],[1,0],[1,0,2],[3,4,100],[3,1,5],[1,6],[7,1],[8],[3,5,101],[9,6]]),
([v33,v0,v1,v45,v3],[46,23,21,22,34,35,10,9,43,48],[18,19],[[0],[1,2,100],[3,0],[1,0,4],[5,3],[1,3,5],[3,6],[1,7,101],[8,5],[9]]),
([v61,v0,v1,v2,v3],[31,12,19,14,45,32,41,54],[],[[0,1],[2],[3,4],[2,0],[3,1],[4,5],[1,5,4],[3,1],[3,1],[6,7]]),
([v63,v0,v1,v2,v3],[23,0,3,1,52,22,28,47,55],[],[[0,1,2],[0,3,4],[5],[0,2,1],[6,7],[0,4],[4,7,6],[0,4],[4,8],[0,6]]),
([v36,v0,v42,v1,v2],[3,19,33,1,14,45,20,12,34,13,53],[22,23],[[0],[1,2],[1,3,4],[5,6,100],[5,1],[1,7],[5,1],[0],[8,9,101],[10,5]]),
([v36,v0,v1,v45,v2],[3,34,21,22,48,2,23,28,13,12,42],[16,17],[[0],[1,2,100],[3,4],[1,5,6],[7,3],[1,3,7],[3,8],[1,9,101],[10,7],[0]]),
([v120,v0,v1,v2,v3],[9,26,16,28,3,42,45,53],[],[[0],[1,2],[0,1],[3,4,5],[3,2],[6,2],[3,2],[2,3,5],[7,6],[5,3]]),
([v0,v122,v1,v2,v3],[23,0,14,21,53,20,34,17,56,57,58],[],[[0,1],[2,3],[0,4,5],[6,4,7],[8],[9],[10],[0,3,2],[2,3],[0,5]]),
([v125,v0,v1,v2,v3],[34,0,49,59,17,21,36,58,60],[],[[0,1,2],[0,2],[0,3,4],[5],[6,7],[2,8],[0,2],[2,7,6],[0,2],[0,4]]),
([v0,v39,v42,v2,v3],[49,19,36,16,20,52,1,3],[20,21],[[0,1,100],[2,3,101],[0,4],[5,0],[0,4],[6],[4,7,5],[0,4],[6],[2,4]]),
([v0,v39,v1,v45,v3],[49,22,36,21,16,41,56,58],[14,15],[[0,1,100],[2,3],[0,4,101],[5,0],[6],[2,3],[3,6,5],[0,3,2],[0,3],[7]]),
([v245,v0,v1,v2,v3],[12,32,19,45,2,53,28,43,40],[],[[0],[1,2],[3,4,5],[0,1],[6,2],[3,2],[3,2],[5,3],[2,3,5],[7,6,8]]),
([v130,v0,v1,v2,v3],[49,0,52,17,1,29,61,23],[],[[0,1,2],[0,2],[3],[4,3],[5,6],[0,2],[2,0],[0,2],[2,0],[7,5]]),
([v0,v42,v1,v45,v2],[52,22,29,21,19,39,3,2],[12,13],[[0,1,100],[2,3],[0,4,101],[5,0],[6],[2,3],[3,7,5],[0,3,2],[0,3],[6]]),
([v246,v0,v1,v2,v3],[10,28,1,43,0,22,45,42,46],[],[[0],[1,2,3],[0,3,4],[1,0,5],[1,3],[6,3],[1,5],[7,1],[3,6,8],[3,1,7]]),
([v135,v0,v1,v2,v3],[29,0,39,17,62,26,41,56,36],[],[[0,1,2],[3],[3,4,5],[0,2],[0,2],[2,0],[6,7],[8,6],[0,2],[2,0]])]
noncomputable def u16_D3 : List StD := [
([v149,v0,v1,v2],[52,0,36,63,29,39,41],[],[[0,1,2],[0,3,4],[5,2,4],[2,5],[5,0],[2,0,6]]),
([v247,v0,v1,v3],[39,0,52,36,27,41,29],[],[[0,1,2],[3,2,4],[0,3,5],[3,0],[2,3],[2,0,6]]),
([v30,v33,v39,v3],[16,1,52,29,64,39,65,66],[24,25,26],[[0,1,2],[0,2],[3,4,100],[0,1],[5,6,101],[3,7,102]]),
([v30,v36,v42,v2],[19,3,52,36,33,41,29,67],[27,25,26],[[0,1,2],[0,1],[3,2,100],[0,4],[5,6,101],[3,7,102]]),
([v248,v0,v2,v3],[29,0,41,36,63,52,68,39],[],[[0,1,2],[3,2],[0,4,5],[6,0,7],[2,3],[2,0,3]]),
([v33,v36,v1,v45],[22,3,52,28,41,39,69],[27,24,26],[[0,1,2],[3,4,100],[0,1],[2,5,101],[0,3],[2,6,102]]),
([v249,v1,v2,v3],[28,0,36,39,52,41,29],[],[[0,1,2],[3,1],[0,1,4],[2,0,5],[4,3,6],[3,0]]),
([v0,v39,v42,v45],[39,70,52,71,72,3,1,58],[27,24,25],[[0,1,100],[2,3,101],[0,4,102],[0,5,2],[2,5],[0,6,7]])]
def u16_D2 : List StD := []
theorem u16_I2 : LevelN u16_R u16_T 2 u16_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u16_C3x0 : levelOK u16_T u16_K u16_P 2 (u16_D2.map Prod.fst) ((u16_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem u16_I3 : LevelN u16_R u16_T 3 u16_D3 := levelStep u16_B u16_W u16_Q u16_I2 (chunks 16 u16_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u16_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u16_C4x0 : levelOK u16_T u16_K u16_P 3 (u16_D3.map Prod.fst) ((u16_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u16_C4x1 : levelOK u16_T u16_K u16_P 3 (u16_D3.map Prod.fst) ((u16_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem u16_I4 : LevelN u16_R u16_T 4 u16_D4 := levelStep u16_B u16_W u16_Q u16_I3 (chunks 16 u16_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u16_C4x0
  · exact u16_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u16_C5x0 : levelOK u16_T u16_K u16_P 4 (u16_D4.map Prod.fst) ((u16_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem u16_I5 : LevelN u16_R u16_T 5 u16_D5 := levelStep u16_B u16_W u16_Q u16_I4 (chunks 16 u16_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u16_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u16_C6x0 : levelOK u16_T u16_K u16_P 5 (u16_D5.map Prod.fst) ((u16_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem u16_I6 : LevelN u16_R u16_T 6 u16_D6 := levelStep u16_B u16_W u16_Q u16_I5 (chunks 16 u16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u16_C6x0
  ))
theorem u16_L : LowN u16_R u16_T 7 := lowSearch u16_B u16_I6 (by decide +kernel)

def u17_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def u17_R : List Nat := [0, 1, 2, 3]
def u17_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem u17_B : baseOK u17_T u17_R u17_E = true := by decide +kernel
theorem u17_S0 : SliceN u17_R u17_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) u17_B u2_B u2_L (by decide +kernel)
def u17_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3])]
theorem u17_Y : ∀ s ∈ u17_Z, SliceN u17_R u17_T s := by
  unfold u17_Z
  simp only [List.forall_mem_cons]
  exact ⟨u17_S0,by simp⟩
def u17_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u17_P : List (Nat × Nat) := []
def u17_K : List CutV := u17_C.map (mkCut u17_Z)
theorem u17_W : ∀ c ∈ u17_K, CutP u17_R u17_T c := cutsGood u17_Y (by decide +kernel)
theorem u17_Q : u17_P.all (sepOK u17_T) = true := by decide +kernel
noncomputable def u17_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u17_D3 : List StD := []
theorem u17_I3 : LevelN u17_R u17_T 3 u17_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u17_C4x0 : levelOK u17_T u17_K u17_P 3 (u17_D3.map Prod.fst) ((u17_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u17_I4 : LevelN u17_R u17_T 4 u17_D4 := levelStep u17_B u17_W u17_Q u17_I3 (chunks 16 u17_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u17_C4x0
  ))
theorem u17_L : LowN u17_R u17_T 5 := lowSearch u17_B u17_I4 (by decide +kernel)

def u18_T : Nat := 0xfee8eaa8fee8eaa8fee8eaa8fee8eaa8
def u18_R : List Nat := [0, 1, 2, 3, 4]
def u18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,6,22)]
theorem u18_B : baseOK u18_T u18_R u18_E = true := by decide +kernel
theorem u18_S0 : SliceN u18_R u18_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) u18_B u16_B u16_L (by decide +kernel)
theorem u18_S1 : SliceN u18_R u18_T (0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]) := mkSlice (w:=16) u18_B u4_B u4_L (by decide +kernel)
theorem u18_S2 : SliceN u18_R u18_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) u18_B u12_B u12_L (by decide +kernel)
theorem u18_S3 : SliceN u18_R u18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) u18_B u12_B u12_L (by decide +kernel)
theorem u18_S4 : SliceN u18_R u18_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) u18_B u17_B u17_L (by decide +kernel)
theorem u18_S5 : SliceN u18_R u18_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) u18_B u12_B u12_L (by decide +kernel)
theorem u18_S6 : SliceN u18_R u18_T (0xffff0000ffff0000ffff0000ffff,6,[0, 1, 2, 3]) := mkSlice (w:=0) u18_B u8_B u8_L (by decide +kernel)
theorem u18_S7 : SliceN u18_R u18_T (0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]) := mkSlice (w:=2) u18_B u17_B u17_L (by decide +kernel)
theorem u18_S8 : SliceN u18_R u18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) u18_B u17_B u17_L (by decide +kernel)
def u18_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,6,[0, 1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4])]
theorem u18_Y : ∀ s ∈ u18_Z, SliceN u18_R u18_T s := by
  unfold u18_Z
  simp only [List.forall_mem_cons]
  exact ⟨u18_S0,u18_S1,u18_S2,u18_S3,u18_S4,u18_S5,u18_S6,u18_S7,u18_S8,by simp⟩
def u18_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(0,[(0,0,1)]),(2,[]),(3,[]),(1,[(0,1,2)]),(0,[(2,0,1)]),(0,[(3,0,1)]),(4,[]),(5,[]),(6,[]),(0,[(1,0,1)]),(7,[]),(8,[]),(1,[(1,1,2)]),(1,[(2,1,2)]),(1,[(3,1,2)]),(0,[(0,0,2)]),(1,[(0,1,3)]),(0,[(2,0,2)]),(0,[(1,0,2)]),(1,[(1,1,3)]),(0,[(3,0,2)]),(1,[(2,1,3)]),(1,[(3,1,3)]),(0,[(0,1,2)]),(1,[(0,2,3)]),(0,[(2,1,2)]),(0,[(1,1,2)]),(1,[(1,2,3)]),(0,[(3,1,2)]),(1,[(2,2,3)]),(1,[(3,2,3)]),(0,[(1,0,1),(0,0,1)]),(1,[(0,1,2),(1,1,2)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(6,[(1,1,2)]),(5,[(0,1,2)]),(4,[(0,1,2)]),(6,[(0,1,2)]),(0,[(1,0,2),(0,0,2)]),(1,[(0,1,3),(1,1,3)]),(8,[(1,1,2)]),(3,[(1,1,2)]),(6,[(1,1,3)]),(3,[(0,1,2)]),(8,[(0,1,2)]),(6,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(1,[(0,2,3),(1,2,3)]),(7,[(1,1,2)]),(2,[(1,1,2)]),(2,[(0,1,2)]),(7,[(0,1,2)]),(6,[(1,2,3)]),(6,[(0,2,3)])]
def u18_P : List (Nat × Nat) := [(2,3),(4,5),(8,9),(1,3),(1,5),(12,14),(10,14),(1,9),(6,14),(12,28),(6,22),(10,26),(6,7),(24,26),(24,28),(20,22),(18,22),(18,26),(1,7),(20,28),(10,11),(1,11),(12,13),(1,13),(3,6),(0,3),(3,10),(2,14),(5,12),(4,14)]
def u18_K : List CutV := u18_C.map (mkCut u18_Z)
theorem u18_W : ∀ c ∈ u18_K, CutP u18_R u18_T c := cutsGood u18_Y (by decide +kernel)
theorem u18_Q : u18_P.all (sepOK u18_T) = true := by decide +kernel
noncomputable def u18_D8 : List StD := [
([v0,v1,v2,v3,v78],[0,1],[0,1,2,3,4,5,6,7,8,9,10,11],[[0,100,101],[0,101,100],[0,102,100],[0,1,100],[103,104,105,106],[103,107,105,108],[1,109,110],[104,107,106,108],[1,111,109],[1,110,109]])]
noncomputable def u18_D7 : List StD := [
([v0,v39,v1,v2,v3,v78],[2,3,4,5,6,7,8,9,10],[12,2,8,13,3,14,4,10,11],[[0,1,100],[0,1,100],[0,2,100],[0,101,100],[0,3,100],[1,4],[1,2,5],[1,6,102,7],[1,3,8],[1,2],[1,103,104],[1,3,104],[2,105,106],[2,3,106],[3,107,108]]),
([v0,v1,v2,v7,v3,v78],[11,12,13,14,7,6,9,8,10],[1,0,2,15,5,16,6,7,10,11],[[0,1,100],[0,2,101],[0,1,102],[0,102,100],[0,3,100],[1,2],[1,4],[1,103,104],[1,3,104],[1,2,5],[2,105,106],[2,3,106],[1,6,107,7],[1,3,8],[3,108,109]]),
([v40,v0,v1,v2,v3,v78],[6,3,2,11,8,9,1,15,10,13],[0,17,2,18,5,15,4,14,10,11],[[0,1,100],[1,2],[1,3],[1,4,101,5],[1,6,7,8],[0,1,100],[0,9,100],[0,102,100],[0,7,100],[1,9,103],[1,104,105],[1,7,104],[9,106,107],[7,9,106],[7,108,109]]),
([v41,v0,v1,v2,v3,v78],[7,12,11,2,8,9,1,16,10,13,4],[1,19,2,18,3,13,6,16,10,11],[[0,1,100],[1,2],[1,3],[1,4,101,5],[1,6,7,8],[0,1,100],[0,9,100,10],[0,102,100],[0,7,100],[1,10,103],[1,104,105],[1,7,104],[10,106,107],[7,10,106],[7,108,109]]),
([v0,v42,v1,v2,v3,v78],[17,9,12,3,18,19,13,4,10],[20,1,6,15,3,19,7,11,10],[[0,1,100],[0,2,100,3],[0,101,100],[0,1,100],[0,4,100],[1,3,5],[1,6,102,7],[1,2],[1,4,8],[3,103,104],[1,2,3],[3,4,104],[1,105,106],[4,107,108],[1,4,106]]),
([v0,v1,v2,v3,v8,v78],[20,12,8,21,22,4,13,19,10],[1,0,13,5,17,8,4,11,10],[[0,1,100],[0,100,101],[0,2,100],[0,1,100],[0,3,100],[1,102,103],[1,2],[1,4],[1,3,103],[2,104,105],[1,5,106,6],[3,107,108],[1,2,7],[2,3,105],[1,3,8]]),
([v43,v0,v1,v2,v3,v78],[19,8,17,13,4,20,1,23,10,12,3],[0,16,1,5,13,21,7,19,11,10],[[0,1,100],[1,2],[1,3,101,4],[1,5],[1,6,7,8],[0,9,100,10],[0,102,100],[0,1,100],[0,7,100],[10,103,104],[1,10,105],[7,10,103],[1,106,107],[7,108,109],[1,7,106]]),
([v44,v0,v1,v2,v3,v78],[22,12,20,13,4,17,1,24,10,9],[2,14,1,3,15,21,8,17,11,10],[[0,1,100],[1,2],[1,3,101,4],[1,5],[1,6,7,8],[0,1,100],[0,102,100],[0,9,100],[0,7,100],[1,103,104],[1,9,105],[1,7,103],[9,106,107],[7,108,109],[7,9,106]]),
([v0,v1,v45,v2,v3,v78],[25,9,13,4,26,12,3,27,10],[0,1,22,5,16,4,17,7,9,10],[[0,100,101],[0,1,102],[0,2,101,3],[0,1,102],[0,4,100],[1,5,103,6],[3,104,105],[1,106,107],[4,108,109],[1,3,7],[1,2],[1,4,8],[1,2,3],[3,4,105],[1,4,107]]),
([v0,v1,v2,v3,v9,v78],[28,13,8,29,3,12,30,27,10],[0,1,14,6,19,8,3,9,10],[[0,100,101],[0,1,100],[0,2,100],[0,1,100],[0,3,100],[1,102,103],[2,104,105],[1,4,106,5],[3,107,108],[1,2],[1,6],[1,3,103],[1,2,7],[2,3,105],[1,3,8]]),
([v46,v0,v1,v2,v3,v78],[27,8,12,3,25,28,1,31,10,13,4],[1,15,0,6,14,7,17,9,10,23],[[0,1,100],[1,2,101,3],[1,4],[1,5],[1,6,7,8],[0,102,100],[0,9,100,10],[0,1,100],[0,7,100],[10,103,104],[1,105,106],[7,107,108],[1,10,109],[7,10,103],[1,7,105]]),
([v47,v0,v1,v2,v3,v78],[30,9,12,3,28,25,1,32,10,13],[2,13,0,4,16,8,19,9,10,23],[[0,1,100],[1,2,101,3],[1,4],[1,5],[1,6,7,8],[0,102,100],[0,9,100],[0,1,100],[0,7,100],[9,103,104],[1,105,106],[7,107,108],[1,9,109],[7,9,103],[1,7,105]])]
noncomputable def u18_D6 : List StD := [
([v0,v39,v7,v3,v78],[33,3,13,34,35,36,37,38,39,40],[24,25,2,0,18,8,3,7,10,11],[[0,1,100],[0,2,101],[0,102,103],[0,3,102],[1,2,104],[1,4,105,5],[1,3,6],[2,7,106,8,107],[2,3,9],[3,108,109]]),
([v0,v42,v2,v8,v78],[41,9,8,42,43,44,45,46,47,48],[26,1,0,8,27,21,3,4,11,10],[[0,1,100],[0,101,102],[0,2,101],[0,3,101],[1,4,103,5,104],[1,2,105],[1,3,6],[2,7,106,8,107],[3,108,109],[2,3,9]]),
([v0,v1,v45,v9,v78],[49,4,13,50,51,52,53,54,55,56],[0,1,28,8,29,3,9,10,23],[[0,100,101],[0,1,102],[0,2,100],[0,3,100],[1,4,103,5,104],[2,6,105,7],[3,106,107],[1,2,108],[1,3,8],[2,3,9]])]
def u18_D5 : List StD := []
theorem u18_I5 : LevelN u18_R u18_T 5 u18_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u18_C6x0 : levelOK u18_T u18_K u18_P 5 (u18_D5.map Prod.fst) ((u18_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem u18_I6 : LevelN u18_R u18_T 6 u18_D6 := levelStep u18_B u18_W u18_Q u18_I5 (chunks 16 u18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u18_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u18_C7x0 : levelOK u18_T u18_K u18_P 6 (u18_D6.map Prod.fst) ((u18_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem u18_I7 : LevelN u18_R u18_T 7 u18_D7 := levelStep u18_B u18_W u18_Q u18_I6 (chunks 16 u18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u18_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u18_C8x0 : levelOK u18_T u18_K u18_P 7 (u18_D7.map Prod.fst) ((u18_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem u18_I8 : LevelN u18_R u18_T 8 u18_D8 := levelStep u18_B u18_W u18_Q u18_I7 (chunks 16 u18_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u18_C8x0
  ))
theorem u18_L : LowN u18_R u18_T 9 := lowSearch u18_B u18_I8 (by decide +kernel)

def u19_T : Nat := 0xa8808000a8808000a8808000a8808000
def u19_R : List Nat := [0, 1, 2, 3, 4]
def u19_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23)]
theorem u19_B : baseOK u19_T u19_R u19_E = true := by decide +kernel
theorem u19_S0 : SliceN u19_R u19_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[1, 2, 3, 4]) := mkSlice (w:=1) u19_B u16_B u16_L (by decide +kernel)
def u19_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[1, 2, 3, 4])]
theorem u19_Y : ∀ s ∈ u19_Z, SliceN u19_R u19_T s := by
  unfold u19_Z
  simp only [List.forall_mem_cons]
  exact ⟨u19_S0,by simp⟩
def u19_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u19_P : List (Nat × Nat) := []
def u19_K : List CutV := u19_C.map (mkCut u19_Z)
theorem u19_W : ∀ c ∈ u19_K, CutP u19_R u19_T c := cutsGood u19_Y (by decide +kernel)
theorem u19_Q : u19_P.all (sepOK u19_T) = true := by decide +kernel
noncomputable def u19_D7 : List StD := [
([v0,v1,v2,v3,v78],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def u19_D6 : List StD := []
theorem u19_I6 : LevelN u19_R u19_T 6 u19_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u19_C7x0 : levelOK u19_T u19_K u19_P 6 (u19_D6.map Prod.fst) ((u19_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem u19_I7 : LevelN u19_R u19_T 7 u19_D7 := levelStep u19_B u19_W u19_Q u19_I6 (chunks 16 u19_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u19_C7x0
  ))
theorem u19_L : LowN u19_R u19_T 8 := lowSearch u19_B u19_I7 (by decide +kernel)

def u20_T : Nat := 0xeeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0
def u20_R : List Nat := [0, 1, 2, 3, 4]
def u20_E : List (Nat × Nat × Nat) := [(0,4,5),(1,12,14),(2,1,5),(3,1,9),(4,1,17)]
theorem u20_B : baseOK u20_T u20_R u20_E = true := by decide +kernel
theorem u20_S0 : SliceN u20_R u20_T (0xcccccccccccccccccccccccccccccccc,7,[0, 2, 3, 4]) := mkSlice (w:=2) u20_B u4_B u4_L (by decide +kernel)
def u20_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,7,[0, 2, 3, 4])]
theorem u20_Y : ∀ s ∈ u20_Z, SliceN u20_R u20_T s := by
  unfold u20_Z
  simp only [List.forall_mem_cons]
  exact ⟨u20_S0,by simp⟩
def u20_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u20_P : List (Nat × Nat) := []
def u20_K : List CutV := u20_C.map (mkCut u20_Z)
theorem u20_W : ∀ c ∈ u20_K, CutP u20_R u20_T c := cutsGood u20_Y (by decide +kernel)
theorem u20_Q : u20_P.all (sepOK u20_T) = true := by decide +kernel
noncomputable def u20_D7 : List StD := [
([v0,v1,v2,v3,v78],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def u20_D6 : List StD := []
theorem u20_I6 : LevelN u20_R u20_T 6 u20_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u20_C7x0 : levelOK u20_T u20_K u20_P 6 (u20_D6.map Prod.fst) ((u20_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem u20_I7 : LevelN u20_R u20_T 7 u20_D7 := levelStep u20_B u20_W u20_Q u20_I6 (chunks 16 u20_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u20_C7x0
  ))
theorem u20_L : LowN u20_R u20_T 8 := lowSearch u20_B u20_I7 (by decide +kernel)

def ptopT : Nat := 0xfee8fe00fe80e800fee8fe00fe80e800
def ptopR : List Nat := [0,1,2,3,4,5]
def ptopE : List (Nat × Nat × Nat) := [(0,10,11),(1,9,11),(2,9,13),(3,3,11),(4,7,23),(5,9,41)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,9,[3,4,2,1,0]) := mkSlice (w:=0) ptopB u10_B u10_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,9,[3,1,0,5,4]) := mkSlice (w:=0) ptopB u15_B u15_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0x33333333333333333333333333333333,9,[3,2,0,5,4]) := mkSlice (w:=0) ptopB u15_B u15_L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0x55555555555555555555555555555555,9,[3,2,1,5,4]) := mkSlice (w:=0) ptopB u15_B u15_L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff0000,9,[3,2,1,0,5]) := mkSlice (w:=16) ptopB u18_B u18_L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff,8,[4,5,2,1,0]) := mkSlice (w:=0) ptopB u19_B u19_L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0xffffffff00000000ffffffff00000000,8,[3,4,2,1,0]) := mkSlice (w:=32) ptopB u20_B u20_L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00,7,[4,2,1,0]) := mkSlice (w:=8) ptopB u4_B u4_L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff00,7,[5,2,1,0]) := mkSlice (w:=8) ptopB u4_B u4_L (by decide +kernel)
theorem ptopS9 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff0000,7,[5,2,1,0]) := mkSlice (w:=16) ptopB u16_B u16_L (by decide +kernel)
theorem ptopS10 : SliceN ptopR ptopT (0xffff000000000000ffff000000000000,7,[3,2,1,0]) := mkSlice (w:=48) ptopB u4_B u4_L (by decide +kernel)
theorem ptopS11 : SliceN ptopR ptopT (0xaaaaaaaa00000000aaaaaaaa,6,[3,4,2,1]) := mkSlice (w:=1) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS12 : SliceN ptopR ptopT (0xcccccccc00000000cccccccc,6,[3,4,2,0]) := mkSlice (w:=2) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS13 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f0,6,[3,4,1,0]) := mkSlice (w:=4) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS14 : SliceN ptopR ptopT (0xffff000000000000ffff0000,6,[3,2,1,0]) := mkSlice (w:=16) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS15 : SliceN ptopR ptopT (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,6,[3,5,4,1]) := mkSlice (w:=1) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS16 : SliceN ptopR ptopT (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,6,[3,5,4,0]) := mkSlice (w:=2) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS17 : SliceN ptopR ptopT (0x22222222222222222222222222222222,6,[3,5,4,2]) := mkSlice (w:=1) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS18 : SliceN ptopR ptopT (0x30303030303030303030303030303030,6,[3,5,4,0]) := mkSlice (w:=4) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS19 : SliceN ptopR ptopT (0x44444444444444444444444444444444,6,[3,5,4,2]) := mkSlice (w:=2) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS20 : SliceN ptopR ptopT (0x50505050505050505050505050505050,6,[3,5,4,1]) := mkSlice (w:=4) ptopB u8_B u8_L (by decide +kernel)
theorem ptopS21 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f,5,[3,4,1,0]) := mkSlice (w:=0) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS22 : SliceN ptopR ptopT (0x333333330000000033333333,5,[3,4,2,0]) := mkSlice (w:=0) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS23 : SliceN ptopR ptopT (0x555555550000000055555555,5,[3,4,2,1]) := mkSlice (w:=0) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS24 : SliceN ptopR ptopT (0xaa00aa00aa00aa00aa00aa00aa00aa,5,[4,5,2,1]) := mkSlice (w:=1) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS25 : SliceN ptopR ptopT (0xcc00cc00cc00cc00cc00cc00cc00cc,5,[4,5,2,0]) := mkSlice (w:=2) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS26 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f0,5,[4,5,1,0]) := mkSlice (w:=4) ptopB u9_B u9_L (by decide +kernel)
theorem ptopS27 : SliceN ptopR ptopT (0xaaaa0000aaaa0000aaaa0000aaaa0000,5,[3,5,2,1]) := mkSlice (w:=17) ptopB u17_B u17_L (by decide +kernel)
theorem ptopS28 : SliceN ptopR ptopT (0xcccc0000cccc0000cccc0000cccc0000,5,[3,5,2,0]) := mkSlice (w:=18) ptopB u17_B u17_L (by decide +kernel)
theorem ptopS29 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f00000,5,[3,5,1,0]) := mkSlice (w:=20) ptopB u17_B u17_L (by decide +kernel)
theorem ptopS30 : SliceN ptopR ptopT (0xaa000000aa000000aa000000aa0000,4,[5,2,1]) := mkSlice (w:=17) ptopB u2_B u2_L (by decide +kernel)
theorem ptopS31 : SliceN ptopR ptopT (0xcc000000cc000000cc000000cc0000,4,[5,2,0]) := mkSlice (w:=18) ptopB u2_B u2_L (by decide +kernel)
theorem ptopS32 : SliceN ptopR ptopT (0xf0000000f0000000f0000000f00000,4,[5,1,0]) := mkSlice (w:=20) ptopB u2_B u2_L (by decide +kernel)
def ptopZ : List SliceD := [(0xffffffff00000000ffffffff,9,[3,4,2,1,0]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,9,[3,1,0,5,4]),(0x33333333333333333333333333333333,9,[3,2,0,5,4]),(0x55555555555555555555555555555555,9,[3,2,1,5,4]),(0xffff0000ffff0000ffff0000ffff0000,9,[3,2,1,0,5]),(0xff00ff00ff00ff00ff00ff00ff00ff,8,[4,5,2,1,0]),(0xffffffff00000000ffffffff00000000,8,[3,4,2,1,0]),(0xff00ff0000000000ff00ff00,7,[4,2,1,0]),(0xff000000ff000000ff000000ff00,7,[5,2,1,0]),(0xff000000ff000000ff000000ff0000,7,[5,2,1,0]),(0xffff000000000000ffff000000000000,7,[3,2,1,0]),(0xaaaaaaaa00000000aaaaaaaa,6,[3,4,2,1]),(0xcccccccc00000000cccccccc,6,[3,4,2,0]),(0xf0f0f0f000000000f0f0f0f0,6,[3,4,1,0]),(0xffff000000000000ffff0000,6,[3,2,1,0]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,6,[3,5,4,1]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,6,[3,5,4,0]),(0x22222222222222222222222222222222,6,[3,5,4,2]),(0x30303030303030303030303030303030,6,[3,5,4,0]),(0x44444444444444444444444444444444,6,[3,5,4,2]),(0x50505050505050505050505050505050,6,[3,5,4,1]),(0xf0f0f0f000000000f0f0f0f,5,[3,4,1,0]),(0x333333330000000033333333,5,[3,4,2,0]),(0x555555550000000055555555,5,[3,4,2,1]),(0xaa00aa00aa00aa00aa00aa00aa00aa,5,[4,5,2,1]),(0xcc00cc00cc00cc00cc00cc00cc00cc,5,[4,5,2,0]),(0xf000f000f000f000f000f000f000f0,5,[4,5,1,0]),(0xaaaa0000aaaa0000aaaa0000aaaa0000,5,[3,5,2,1]),(0xcccc0000cccc0000cccc0000cccc0000,5,[3,5,2,0]),(0xf0f00000f0f00000f0f00000f0f00000,5,[3,5,1,0]),(0xaa000000aa000000aa000000aa0000,4,[5,2,1]),(0xcc000000cc000000cc000000cc0000,4,[5,2,0]),(0xf0000000f0000000f0000000f00000,4,[5,1,0])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,ptopS9,ptopS10,ptopS11,ptopS12,ptopS13,ptopS14,ptopS15,ptopS16,ptopS17,ptopS18,ptopS19,ptopS20,ptopS21,ptopS22,ptopS23,ptopS24,ptopS25,ptopS26,ptopS27,ptopS28,ptopS29,ptopS30,ptopS31,ptopS32,by simp⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ptopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(0,[(0,0,1)]),(0,[(0,0,1),(0,2,5)]),(0,[(0,0,1),(0,3,5)]),(0,[(0,0,1),(0,4,5)]),(0,[(0,0,1),(1,2,5)]),(0,[(0,0,1),(1,3,5)]),(0,[(0,0,1),(1,4,5)]),(0,[(0,0,1),(2,2,5)]),(0,[(0,0,1),(2,3,5)]),(0,[(0,0,1),(2,4,5)]),(0,[(0,0,2)]),(0,[(0,0,3)]),(0,[(0,0,4)]),(0,[(0,2,3)]),(0,[(0,2,4)]),(0,[(0,3,4)]),(0,[(1,0,2)]),(0,[(1,0,2),(0,3,5)]),(0,[(1,0,2),(0,4,5)]),(0,[(1,0,2),(1,3,5)]),(0,[(1,0,2),(1,4,5)]),(0,[(1,0,2),(2,3,5)]),(0,[(1,0,2),(2,4,5)]),(0,[(1,0,2),(3,3,5)]),(0,[(1,0,2),(3,4,5)]),(0,[(1,0,3)]),(0,[(1,0,3),(0,2,5)]),(0,[(1,0,3),(0,4,5)]),(0,[(1,0,3),(2,2,5)]),(0,[(1,0,3),(3,2,5)]),(0,[(1,0,3),(3,4,5)]),(0,[(1,0,4)]),(0,[(1,0,4),(0,2,5)]),(0,[(1,0,4),(0,3,5)]),(0,[(1,0,4),(3,2,5)]),(0,[(1,0,4),(3,3,5)]),(0,[(1,1,2)]),(0,[(1,1,3)]),(0,[(1,1,4)]),(0,[(1,2,3)]),(0,[(1,2,3),(0,0,1)]),(0,[(1,2,3),(0,0,1),(2,5,6)]),(0,[(1,2,3),(0,0,5)]),(0,[(1,2,3),(0,0,5),(0,4,6)]),(0,[(1,2,3),(0,0,5),(2,4,6)]),(0,[(1,2,3),(0,1,5)]),(0,[(1,2,3),(0,4,5)]),(0,[(1,2,3),(1,0,4)]),(0,[(1,2,3),(1,0,4),(0,5,6)]),(0,[(1,2,3),(1,1,5)]),(0,[(1,2,3),(3,0,5)]),(0,[(1,2,3),(3,1,5)]),(0,[(1,2,4)]),(0,[(1,2,4),(0,0,1)]),(0,[(1,2,4),(0,0,1),(2,5,6)]),(0,[(1,2,4),(0,0,5)]),(0,[(1,2,4),(0,0,5),(0,3,6)]),(0,[(1,2,4),(0,0,5),(2,3,6)]),(0,[(1,2,4),(0,1,5)]),(0,[(1,2,4),(0,3,5)]),(0,[(1,2,4),(1,0,3)]),(0,[(1,2,4),(1,0,3),(0,5,6)]),(0,[(1,2,4),(1,1,5)]),(0,[(1,2,4),(3,0,5)]),(0,[(1,2,4),(3,1,5)]),(0,[(1,3,4)]),(0,[(1,3,4),(0,0,1)]),(0,[(1,3,4),(0,0,1),(2,5,6)]),(0,[(1,3,4),(0,0,5)]),(0,[(1,3,4),(0,0,5),(0,2,6)]),(0,[(1,3,4),(0,0,5),(2,2,6)]),(0,[(1,3,4),(0,1,5)]),(0,[(1,3,4),(0,2,5)]),(0,[(1,3,4),(1,0,2)]),(0,[(1,3,4),(1,0,2),(0,5,6)]),(0,[(1,3,4),(1,0,5)]),(0,[(1,3,4),(1,1,5)]),(0,[(1,3,4),(1,2,5)]),(0,[(1,3,4),(2,2,5)]),(0,[(1,3,4),(3,1,5)]),(0,[(2,0,2)]),(0,[(2,0,2),(0,3,5)]),(0,[(2,0,2),(0,4,5)]),(0,[(2,0,2),(1,3,4)]),(0,[(2,0,2),(1,3,4),(3,5,6)]),(0,[(2,0,2),(1,3,5)]),(0,[(2,0,2),(1,4,5)]),(0,[(2,0,2),(2,3,5)]),(0,[(2,0,2),(2,4,5)]),(0,[(2,0,2),(3,3,5)]),(0,[(2,0,2),(3,4,5)]),(0,[(2,0,3)]),(0,[(2,0,3),(0,2,5)]),(0,[(2,0,3),(1,2,4)]),(0,[(2,0,3),(1,2,4),(3,5,6)]),(0,[(2,0,3),(1,2,5)]),(0,[(2,0,3),(1,4,5)]),(0,[(2,0,3),(2,2,5)]),(0,[(2,0,3),(2,4,5)]),(0,[(2,0,4)]),(0,[(2,0,4),(1,2,3)]),(0,[(2,0,4),(1,2,3),(3,5,6)]),(0,[(2,0,4),(1,2,5)]),(0,[(2,0,4),(1,3,5)]),(0,[(2,0,4),(2,2,5)]),(0,[(2,0,4),(2,3,5)]),(0,[(2,1,2)]),(0,[(2,1,2),(0,3,5)]),(0,[(2,1,2),(0,4,5)]),(0,[(2,1,2),(1,3,4)]),(0,[(2,1,2),(1,3,4),(3,5,6)]),(0,[(2,1,2),(1,3,5)]),(0,[(2,1,2),(1,4,5)]),(0,[(2,1,2),(2,3,5)]),(0,[(2,1,2),(2,4,5)]),(0,[(2,1,3)]),(0,[(2,1,3),(0,2,5)]),(0,[(2,1,3),(1,2,4)]),(0,[(2,1,3),(1,2,4),(3,5,6)]),(0,[(2,1,3),(1,2,5)]),(0,[(2,1,3),(1,4,5)]),(0,[(2,1,3),(2,2,5)]),(0,[(2,1,3),(2,4,5)]),(0,[(2,1,4)]),(0,[(2,1,4),(1,2,3)]),(0,[(2,1,4),(1,2,3),(3,5,6)]),(0,[(2,1,4),(1,2,5)]),(0,[(2,1,4),(1,3,5)]),(0,[(2,1,4),(2,2,5)]),(0,[(2,1,4),(2,3,5)]),(0,[(2,2,3)]),(0,[(2,2,4)]),(0,[(2,3,4)]),(0,[(3,0,1)]),(0,[(3,0,1),(1,2,3)]),(0,[(3,0,1),(1,2,4)]),(0,[(3,0,1),(1,3,4)]),(0,[(3,0,2)]),(0,[(3,0,2),(1,3,4),(0,0,6)]),(0,[(3,0,3)]),(0,[(3,0,3),(1,2,4),(0,0,6)]),(0,[(3,0,4)]),(0,[(3,0,4),(1,2,3),(0,0,6)]),(0,[(3,1,2)]),(0,[(3,1,3)]),(0,[(3,1,4)]),(0,[(3,2,3)]),(0,[(3,2,4)]),(0,[(3,3,4)]),(1,[]),(1,[(0,0,1)]),(1,[(0,0,1),(3,4,5)]),(1,[(0,0,2)]),(1,[(0,0,2),(3,4,5)]),(1,[(0,0,4)]),(1,[(0,0,4),(1,1,5)]),(1,[(0,0,4),(1,2,5)]),(1,[(0,0,4),(1,3,5)]),(1,[(0,0,4),(2,1,5)]),(1,[(0,0,4),(2,2,5)]),(1,[(0,1,4)]),(1,[(0,2,4)]),(1,[(1,0,1)]),(1,[(1,0,1),(0,2,5)]),(1,[(1,0,1),(3,2,5)]),(1,[(1,0,2)]),(1,[(1,0,2),(0,1,5)]),(1,[(1,0,2),(2,1,5)]),(1,[(1,0,2),(3,1,5)]),(1,[(1,0,3)]),(1,[(1,0,3),(0,1,5)]),(1,[(1,0,3),(0,1,5),(1,2,6)]),(1,[(1,0,3),(0,1,5),(3,2,6)]),(1,[(1,0,3),(0,2,5)]),(1,[(1,0,3),(0,2,5),(1,1,6)]),(1,[(1,0,3),(0,2,5),(3,1,6)]),(1,[(1,0,3),(3,1,5)]),(1,[(1,0,3),(3,2,5)]),(1,[(1,0,4)]),(1,[(1,1,2)]),(1,[(1,1,2),(0,0,4)]),(1,[(1,1,2),(0,0,4),(1,3,6)]),(1,[(1,1,2),(0,0,4),(2,5,6)]),(1,[(1,1,2),(0,0,5)]),(1,[(1,1,2),(0,3,5)]),(1,[(1,1,2),(0,4,5)]),(1,[(1,1,2),(1,0,3)]),(1,[(1,1,2),(1,0,3),(0,5,6)]),(1,[(1,1,2),(3,0,5)]),(1,[(1,1,2),(3,4,5)]),(1,[(1,1,3)]),(1,[(1,1,3),(0,2,5)]),(1,[(1,1,3),(3,0,5)]),(1,[(1,1,3),(3,2,5)]),(1,[(1,1,4)]),(1,[(1,2,3)]),(1,[(1,2,3),(0,1,5)]),(1,[(1,2,3),(3,0,5)]),(1,[(1,2,3),(3,1,5)]),(1,[(1,2,4)]),(1,[(2,0,1)]),(1,[(2,0,1),(1,2,3)]),(1,[(2,0,1),(1,2,3),(3,5,6)]),(1,[(2,0,1),(1,2,5)]),(1,[(2,0,1),(2,2,5)]),(1,[(2,0,1),(2,3,5)]),(1,[(2,0,2)]),(1,[(2,0,2),(1,1,3)]),(1,[(2,0,2),(1,1,3),(3,5,6)]),(1,[(2,0,2),(1,1,5)]),(1,[(2,0,2),(2,1,5)]),(1,[(2,0,2),(2,3,5)]),(1,[(2,0,3)]),(1,[(2,0,3),(1,1,2)]),(1,[(2,0,4)]),(1,[(2,1,2)]),(1,[(2,1,2),(1,0,3),(0,2,6)]),(1,[(2,1,4)]),(1,[(2,2,4)]),(1,[(3,0,1)]),(1,[(3,0,1),(0,4,5)]),(1,[(3,0,1),(2,4,5)]),(1,[(3,0,2)]),(1,[(3,0,2),(0,4,5)]),(1,[(3,0,2),(2,4,5)]),(1,[(3,0,4)]),(1,[(3,0,4),(1,1,2)]),(1,[(3,1,2)]),(1,[(3,1,2),(0,0,5)]),(1,[(3,1,2),(1,0,3),(0,1,6)]),(1,[(3,1,2),(3,0,5)]),(1,[(3,1,2),(3,4,5)]),(1,[(3,1,3)]),(1,[(3,1,4)]),(1,[(3,1,4),(1,2,5)]),(1,[(3,1,4),(2,2,5)]),(1,[(3,2,3)]),(1,[(3,2,4)]),(1,[(3,2,4),(1,1,5)]),(1,[(3,2,4),(2,1,5)]),(1,[(3,3,4)]),(1,[(3,3,4),(1,1,2)]),(1,[(3,3,4),(1,1,5)]),(1,[(3,3,4),(1,2,5)]),(2,[]),(2,[(0,0,1)]),(2,[(0,0,2)]),(2,[(0,0,2),(3,4,5)]),(2,[(0,0,4)]),(2,[(0,0,4),(1,1,5)]),(2,[(0,0,4),(1,2,5)]),(2,[(0,0,4),(1,3,5)]),(2,[(0,0,4),(2,1,5)]),(2,[(0,0,4),(2,2,5)]),(2,[(0,1,4)]),(2,[(0,2,4)]),(2,[(1,0,1)]),(2,[(1,0,1),(0,2,5)]),(2,[(1,0,1),(3,2,5)]),(2,[(1,0,2)]),(2,[(1,0,2),(0,1,5)]),(2,[(1,0,2),(3,1,5)]),(2,[(1,0,3)]),(2,[(1,0,3),(0,1,5)]),(2,[(1,0,3),(0,2,5)]),(2,[(1,0,3),(0,2,5),(1,1,6)]),(2,[(1,0,3),(0,2,5),(3,1,6)]),(2,[(1,0,3),(3,1,5)]),(2,[(1,0,3),(3,2,5)]),(2,[(1,0,4)]),(2,[(1,1,2)]),(2,[(1,1,2),(0,0,4)]),(2,[(1,1,2),(0,0,4),(1,3,6)]),(2,[(1,1,2),(0,0,4),(2,5,6)]),(2,[(1,1,2),(0,0,5)]),(2,[(1,1,2),(0,3,5)]),(2,[(1,1,2),(0,4,5)]),(2,[(1,1,2),(1,0,3)]),(2,[(1,1,2),(1,0,3),(0,5,6)]),(2,[(1,1,2),(3,0,5)]),(2,[(1,1,2),(3,4,5)]),(2,[(1,1,3)]),(2,[(1,1,3),(0,2,5)]),(2,[(1,1,3),(3,0,5)]),(2,[(1,1,3),(3,2,5)]),(2,[(1,1,4)]),(2,[(1,2,3)]),(2,[(1,2,3),(0,1,5)]),(2,[(1,2,3),(3,0,5)]),(2,[(1,2,3),(3,1,5)]),(2,[(1,2,4)]),(2,[(2,0,1)]),(2,[(2,0,1),(1,2,3)]),(2,[(2,0,1),(1,2,3),(3,5,6)]),(2,[(2,0,1),(1,2,5)]),(2,[(2,0,1),(2,2,5)]),(2,[(2,0,1),(2,3,5)]),(2,[(2,0,2)]),(2,[(2,0,2),(1,1,3)]),(2,[(2,0,2),(1,1,3),(3,5,6)]),(2,[(2,0,2),(1,1,5)]),(2,[(2,0,2),(2,1,5)]),(2,[(2,0,2),(2,3,5)]),(2,[(2,0,3)]),(2,[(2,0,3),(1,1,2)]),(2,[(2,0,4)]),(2,[(2,1,2)]),(2,[(2,1,2),(1,0,3),(0,2,6)]),(2,[(2,2,4)]),(2,[(3,0,1)]),(2,[(3,0,2)]),(2,[(3,0,2),(0,4,5)]),(2,[(3,0,2),(1,1,5)]),(2,[(3,0,2),(2,4,5)]),(2,[(3,0,4)]),(2,[(3,0,4),(1,1,2)]),(2,[(3,1,2)]),(2,[(3,1,2),(1,0,3),(0,1,6)]),(2,[(3,1,3)]),(2,[(3,1,4)]),(2,[(3,1,4),(1,2,5)]),(2,[(3,1,4),(2,2,5)]),(2,[(3,2,3)]),(2,[(3,2,4)]),(2,[(3,2,4),(1,1,5)]),(2,[(3,2,4),(2,1,5)]),(2,[(3,3,4)]),(2,[(3,3,4),(1,1,2)]),(2,[(3,3,4),(1,1,5)]),(2,[(3,3,4),(1,2,5)]),(3,[]),(3,[(0,0,1)]),(3,[(0,0,2)]),(3,[(0,0,4)]),(3,[(0,0,4),(1,1,5)]),(3,[(0,0,4),(1,2,5)]),(3,[(0,0,4),(1,3,5)]),(3,[(0,0,4),(2,1,5)]),(3,[(0,0,4),(2,2,5)]),(3,[(0,1,4)]),(3,[(0,2,4)]),(3,[(1,0,1)]),(3,[(1,0,1),(0,2,5)]),(3,[(1,0,1),(3,2,5)]),(3,[(1,0,2)]),(3,[(1,0,2),(0,1,5)]),(3,[(1,0,2),(3,1,5)]),(3,[(1,0,3)]),(3,[(1,0,3),(0,1,5)]),(3,[(1,0,3),(0,2,5)]),(3,[(1,0,3),(3,1,5)]),(3,[(1,0,3),(3,2,5)]),(3,[(1,1,2)]),(3,[(1,1,2),(0,0,4)]),(3,[(1,1,2),(0,0,4),(1,3,6)]),(3,[(1,1,2),(0,0,4),(2,5,6)]),(3,[(1,1,2),(0,0,5)]),(3,[(1,1,2),(0,3,5)]),(3,[(1,1,2),(0,4,5)]),(3,[(1,1,2),(1,0,3)]),(3,[(1,1,2),(1,0,3),(0,5,6)]),(3,[(1,1,2),(3,0,5)]),(3,[(1,1,2),(3,4,5)]),(3,[(1,1,3)]),(3,[(1,1,3),(0,2,5)]),(3,[(1,1,3),(3,0,5)]),(3,[(1,1,3),(3,2,5)]),(3,[(1,1,4)]),(3,[(1,2,3)]),(3,[(1,2,3),(0,1,5)]),(3,[(1,2,3),(3,0,5)]),(3,[(1,2,3),(3,1,5)]),(3,[(1,2,4)]),(3,[(2,0,1)]),(3,[(2,0,1),(1,2,3)]),(3,[(2,0,1),(1,2,3),(3,5,6)]),(3,[(2,0,1),(1,2,5)]),(3,[(2,0,1),(2,2,5)]),(3,[(2,0,1),(2,3,5)]),(3,[(2,0,2)]),(3,[(2,0,2),(1,1,3)]),(3,[(2,0,2),(1,1,3),(3,5,6)]),(3,[(2,0,2),(1,1,5)]),(3,[(2,0,2),(2,1,5)]),(3,[(2,0,2),(2,3,5)]),(3,[(2,0,3)]),(3,[(2,0,3),(1,1,2)]),(3,[(2,0,4)]),(3,[(2,1,2)]),(3,[(2,1,2),(1,0,3),(0,2,6)]),(3,[(3,0,1)]),(3,[(3,0,2)]),(3,[(3,0,4)]),(3,[(3,0,4),(1,1,2)]),(3,[(3,1,2)]),(3,[(3,1,2),(1,0,3),(0,1,6)]),(3,[(3,1,3)]),(3,[(3,1,4)]),(3,[(3,1,4),(1,2,5)]),(3,[(3,1,4),(2,2,5)]),(3,[(3,2,3)]),(3,[(3,2,4)]),(3,[(3,2,4),(1,1,5)]),(3,[(3,2,4),(2,1,5)]),(3,[(3,3,4)]),(3,[(3,3,4),(1,1,2)]),(3,[(3,3,4),(1,1,5)]),(3,[(3,3,4),(1,2,5)]),(4,[]),(4,[(1,0,1)]),(4,[(1,0,1),(3,2,5)]),(4,[(1,0,1),(3,3,5)]),(4,[(1,0,2)]),(4,[(1,0,2),(3,1,5)]),(4,[(1,0,2),(3,3,5)]),(4,[(1,0,3)]),(4,[(1,0,3),(3,1,5)]),(4,[(1,0,3),(3,2,5)]),(4,[(1,0,4)]),(4,[(1,0,4),(1,1,2)]),(4,[(1,0,4),(1,1,3)]),(4,[(1,0,4),(1,2,3)]),(4,[(1,0,4),(3,1,5)]),(4,[(1,0,4),(3,2,5)]),(4,[(1,0,4),(3,3,5)]),(4,[(1,1,2)]),(4,[(1,1,2),(0,0,5)]),(4,[(1,1,2),(0,3,5)]),(4,[(1,1,2),(1,0,3)]),(4,[(1,1,2),(1,0,3),(0,5,6)]),(4,[(1,1,2),(1,0,4)]),(4,[(1,1,2),(1,0,4),(0,5,6)]),(4,[(1,1,2),(1,3,4)]),(4,[(1,1,2),(1,3,4),(0,5,6)]),(4,[(1,1,2),(3,0,5)]),(4,[(1,1,3)]),(4,[(1,1,3),(0,0,5)]),(4,[(1,1,3),(0,2,5)]),(4,[(1,1,3),(1,0,2)]),(4,[(1,1,3),(1,0,2),(0,5,6)]),(4,[(1,1,3),(1,0,4)]),(4,[(1,1,3),(1,0,4),(0,5,6)]),(4,[(1,1,3),(1,2,4)]),(4,[(1,1,3),(1,2,4),(0,5,6)]),(4,[(1,1,3),(3,0,5)]),(4,[(1,1,4)]),(4,[(1,1,4),(3,2,5)]),(4,[(1,1,4),(3,3,5)]),(4,[(1,2,3)]),(4,[(1,2,3),(0,0,5)]),(4,[(1,2,3),(0,1,5)]),(4,[(1,2,3),(1,0,1)]),(4,[(1,2,3),(1,0,1),(0,5,6)]),(4,[(1,2,3),(1,0,4)]),(4,[(1,2,3),(1,0,4),(0,5,6)]),(4,[(1,2,3),(1,1,4)]),(4,[(1,2,3),(1,1,4),(0,5,6)]),(4,[(1,2,3),(1,1,5)]),(4,[(1,2,3),(3,0,5)]),(4,[(1,2,4)]),(4,[(1,2,4),(3,1,5)]),(4,[(1,2,4),(3,3,5)]),(4,[(1,3,4)]),(4,[(1,3,4),(3,1,5)]),(4,[(1,3,4),(3,2,5)]),(4,[(2,0,1)]),(4,[(2,0,1),(1,2,3)]),(4,[(2,0,1),(1,2,3),(3,5,6)]),(4,[(2,0,1),(1,2,4)]),(4,[(2,0,1),(1,2,4),(3,5,6)]),(4,[(2,0,1),(1,2,5)]),(4,[(2,0,1),(1,3,4)]),(4,[(2,0,1),(1,3,4),(3,5,6)]),(4,[(2,0,1),(1,3,5)]),(4,[(2,0,2)]),(4,[(2,0,2),(1,1,3)]),(4,[(2,0,2),(1,1,3),(3,5,6)]),(4,[(2,0,2),(1,1,4)]),(4,[(2,0,2),(1,1,4),(3,5,6)]),(4,[(2,0,2),(1,1,5)]),(4,[(2,0,2),(1,3,4)]),(4,[(2,0,2),(1,3,4),(3,5,6)]),(4,[(2,0,2),(1,3,5)]),(4,[(2,0,3)]),(4,[(2,0,3),(1,1,2)]),(4,[(2,0,3),(1,1,2),(3,5,6)]),(4,[(2,0,3),(1,1,4)]),(4,[(2,0,3),(1,1,4),(3,5,6)]),(4,[(2,0,3),(1,1,5)]),(4,[(2,0,3),(1,2,4)]),(4,[(2,0,3),(1,2,4),(3,5,6)]),(4,[(2,0,3),(1,2,5)]),(4,[(2,0,4)]),(4,[(2,0,4),(1,1,2)]),(4,[(2,0,4),(1,1,3)]),(4,[(2,0,4),(1,2,3)]),(4,[(2,1,2)]),(4,[(2,1,3)]),(4,[(2,2,3)]),(4,[(3,1,2)]),(4,[(3,1,3)]),(4,[(3,1,4)]),(4,[(3,2,3)]),(4,[(3,2,4)]),(4,[(3,3,4)]),(5,[]),(5,[(1,1,2)]),(5,[(1,1,3)]),(5,[(1,1,4)]),(5,[(1,2,3)]),(5,[(1,2,3),(0,1,5)]),(5,[(1,2,3),(0,4,5)]),(5,[(1,2,4)]),(5,[(1,2,4),(0,1,5)]),(5,[(1,2,4),(0,3,5)]),(5,[(1,3,4)]),(5,[(1,3,4),(0,1,5)]),(5,[(1,3,4),(0,2,5)]),(5,[(2,0,1)]),(5,[(2,0,2)]),(5,[(2,0,3)]),(5,[(2,0,4)]),(5,[(2,1,2)]),(5,[(2,1,3)]),(5,[(2,1,4)]),(5,[(2,2,3)]),(5,[(2,2,4)]),(5,[(2,3,4)]),(5,[(3,2,3)]),(5,[(3,2,4)]),(5,[(3,3,4)]),(6,[]),(6,[(0,0,1)]),(6,[(1,0,2)]),(6,[(1,0,3)]),(6,[(1,0,4)]),(6,[(1,2,3)]),(6,[(1,2,4)]),(6,[(1,3,4)]),(6,[(2,0,2)]),(6,[(2,0,3)]),(6,[(2,0,4)]),(6,[(2,1,2)]),(6,[(2,1,3)]),(6,[(2,1,4)]),(6,[(3,0,1)]),(7,[]),(7,[(1,0,1)]),(7,[(1,0,2)]),(7,[(1,0,3)]),(7,[(1,1,2)]),(7,[(1,1,2),(0,3,4)]),(7,[(1,1,3)]),(7,[(1,1,3),(0,2,4)]),(7,[(1,2,3)]),(7,[(1,2,3),(0,1,4)]),(7,[(1,2,3),(3,0,4)]),(7,[(2,0,1)]),(7,[(2,0,2)]),(7,[(2,0,3)]),(7,[(2,1,2)]),(7,[(2,1,3)]),(7,[(2,2,3)]),(7,[(3,1,2)]),(7,[(3,1,3)]),(7,[(3,2,3)]),(8,[]),(8,[(1,0,1)]),(8,[(1,0,1),(0,2,4)]),(8,[(1,0,1),(0,3,4)]),(8,[(1,0,2)]),(8,[(1,0,2),(0,1,4)]),(8,[(1,0,2),(0,3,4)]),(8,[(1,0,3)]),(8,[(1,0,3),(0,1,4)]),(8,[(1,0,3),(0,2,4)]),(8,[(1,1,2)]),(8,[(1,1,2),(0,3,4)]),(8,[(1,1,3)]),(8,[(1,1,3),(0,2,4)]),(8,[(1,2,3)]),(8,[(1,2,3),(0,1,4)]),(8,[(2,1,2)]),(8,[(2,1,3)]),(8,[(2,2,3)]),(8,[(3,1,2)]),(8,[(3,1,3)]),(8,[(3,2,3)]),(9,[]),(9,[(1,1,2)]),(9,[(1,1,3)]),(9,[(1,2,3)]),(10,[]),(10,[(1,0,1)]),(10,[(1,0,2)]),(10,[(1,0,3)]),(10,[(1,1,2)]),(10,[(1,1,2),(0,3,4)]),(10,[(1,1,2),(3,0,4)]),(10,[(1,1,3)]),(10,[(1,1,3),(0,2,4)]),(10,[(1,1,3),(3,0,4)]),(10,[(1,2,3)]),(10,[(1,2,3),(0,1,4)]),(10,[(1,2,3),(3,0,4)]),(10,[(2,1,2)]),(10,[(2,1,3)]),(10,[(2,2,3)]),(10,[(3,1,2)]),(10,[(3,1,3)]),(10,[(3,2,3)]),(11,[]),(11,[(0,0,1)]),(11,[(2,0,2)]),(11,[(2,0,3)]),(11,[(3,0,1)]),(12,[]),(12,[(0,0,1)]),(12,[(2,0,3)]),(12,[(3,0,1)]),(13,[]),(14,[]),(15,[]),(15,[(0,0,2)]),(15,[(0,0,2),(1,1,4)]),(15,[(3,0,2)]),(16,[]),(17,[]),(17,[(0,0,2)]),(17,[(0,0,2),(1,1,4)]),(17,[(3,0,2)]),(18,[]),(19,[]),(19,[(0,0,2)]),(19,[(0,0,2),(1,1,4)]),(19,[(3,0,2)]),(20,[]),(21,[]),(22,[]),(23,[]),(24,[]),(25,[]),(26,[]),(27,[]),(28,[]),(29,[]),(30,[]),(31,[]),(32,[])]
def ptopP : List (Nat × Nat) := [(11,1),(11,2),(11,3),(11,7),(11,8),(11,9),(11,10),(11,19),(11,35),(13,1),(13,4),(13,5),(13,7),(13,8),(13,9),(13,12),(13,21),(13,37),(14,2),(14,4),(14,6),(14,7),(14,8),(14,10),(14,12),(14,38),(23,3),(23,5),(23,6),(23,7),(23,17),(23,18),(23,19),(23,20),(23,21),(23,22),(23,39),(25,1),(25,8),(25,9),(25,16),(25,17),(25,24),(25,49),(25,56),(26,10),(26,16),(26,18),(26,24),(26,50),(26,56),(28,12),(28,16),(28,20),(28,24),(28,52),(28,56),(41,1),(41,8),(41,9),(41,33),(41,40),(41,56),(42,2),(42,8),(42,10),(42,34),(42,40),(42,56),(44,4),(44,8),(44,12),(44,36),(44,40),(44,56),(51,3),(51,17),(51,18),(51,19),(51,35),(51,48),(51,49),(51,50),(53,20),(53,21),(53,37),(53,48),(53,49),(53,52),(54,22),(54,38),(54,50),(54,52),(57,49),(57,56),(58,56),(60,56)]
def ptopK : List CutV := ptopC.map (mkCut ptopZ)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := []
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := by intro s h; cases h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD7 : List StD := [
([v250,v0,v1,v251,v2,v3,v78,v252],[70,188,267,621],[5,6,8,11,14,15,24,26,27,28,29,30,31,32,34,35,39,52,53,56,59,60,65,71,79],[[101,115],[100,114],[0],[104],[118,121],[110,116],[120,123],[2,100,101],[101,105,115],[101,112,113],[101,115],[101,109,110],[101,120,122],[100,106,114],[100,111,113],[100,114],[100,108,110],[100,120,122],[1,3,113],[103,118,121],[110,116],[120,123],[113,117,118],[107,110,116],[113,119,120],[110,116],[102,118,121],[110,120,124]]),
([v253,v0,v1,v2,v254,v3,v78,v252],[57,176,279,617],[2,5,6,8,14,15,23,26,27,28,29,30,32,33,34,35,39,46,47,50,59,60,65,71,79],[[105,115],[101],[104,112],[0],[118,121],[110,116],[120,122],[105,113,114],[1,104,105],[102,105,115],[105,115],[105,109,110],[105,120,122],[104,111,112],[2,3,114],[114,117,118],[108,110,116],[114,119,120],[104,106,112],[104,112],[104,107,110],[104,120,123],[100,118,121],[110,116],[120,122],[110,116],[103,118,121],[110,120,124]]),
([v255,v0,v1,v2,v256,v3,v78,v252],[44,173,361,612],[2,5,6,8,14,23,24,26,27,28,29,31,32,33,34,35,37,39,40,41,44,45,57,58,59,65,66,71,79],[[102],[106,114],[105,112],[0],[119,126],[110,121],[124,125],[106,113,114],[105,111,112],[2,3,115],[115,118,119],[109,110,121],[115,120,123],[1,105,106],[101,106,114],[106,114],[106,108,110],[106,124,125],[104,105,112],[105,112],[105,107,110],[105,124,127],[100,119,126],[110,121],[124,125],[110,116,117],[103,119,122],[110,124,128]]),
([v0,v1,v251,v2,v257,v3,v78,v252],[69,71,139,188,265,266,308,350,390,455,517,539,581,621],[5,6,8,11,14,15,23,24,27,28,29,32,34,35,39,53,59,60,65,71,79],[[5,100,101],[101,105,113],[101,104,106],[6,7,101],[101,113],[101,109,110],[101,116,118],[100,107,112],[100,104,106],[4,8,100],[100,112],[100,108,110],[100,116,118],[3,13,104],[1],[103,115,117],[110,114],[116,119],[111],[104,115,117],[104,110,114],[104,116,119],[2,10,115],[9,12,110],[0,11,116],[110,114],[102,115,117],[110,116,120]]),
([v0,v1,v2,v254,v258,v3,v78,v252],[56,58,141,174,175,217,279,349,396,442,514,538,579,617],[2,5,6,8,14,15,23,24,26,28,29,32,34,35,39,47,59,60,65,71,79],[[101,105,107],[4,104,105],[102,105,113],[5,7,105],[105,113],[105,109,110],[105,116,118],[101,104,107],[6,13,101],[112],[101,115,117],[101,110,114],[101,116,118],[104,106,111],[3,8,104],[104,111],[104,108,110],[104,116,119],[1],[100,115,117],[110,114],[116,118],[2,10,115],[9,12,110],[0,11,116],[110,114],[103,115,117],[110,116,120]]),
([v0,v1,v2,v256,v259,v3,v78,v252],[43,45,143,171,172,230,264,318,361,432,511,537,577,612],[2,5,6,8,14,15,23,24,26,27,29,32,34,35,37,39,41,45,57,59,65,66,71,79],[[102,105],[102,105],[8,13,102],[113],[102,116,121],[102,110,117],[102,119,120],[4,106,107],[101,107,112],[5,6,107],[107,112],[107,109,110],[107,119,120],[104,106,111],[3,7,106],[106,111],[106,108,110],[106,119,122],[1],[100,116,121],[110,117],[119,120],[2,10,116],[9,12,110],[0,11,119],[110,114,115],[103,116,118],[110,119,123]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopW ptopQ ptopI6 (chunks 4 ptopD7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([v260,v0,v1,v2,v3,v78,v252],[0,3,4,9,10,68,76,77,80,150,183,245,248,254,311,312,314,339,409,459,516,532,557,605,621,641],[0,1,2,3,5,6,7,8,9,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,51,53,54,56,57,59,60,65,71,73,78,79,81,82],[[2,4,11,13,17,105,111,125],[1,3,13,104,114,127],[9,10,24,25,110,131],[6,12,14,18,19,20,102,124,130],[7,8,15,16,19,22,118,123,129],[0,5,21,23,134,137],[13,104,105,125,127],[10,17,105,110,113,121],[17,101,102,105,112,121],[17,105,117,118,121,129],[5,17,105,126,134,136,142],[10,13,104,110,113,120],[13,100,102,104,109,120],[13,104,116,118,120,129],[5,13,104,128,134,136,141],[10,20,102,103,108,109,110,119],[10,19,110,115,118,119,140],[5,10,23,110,132,134,137,138],[13,19,102,106,118,129,130],[5,20,102,107,133,134,135,139],[5,19,118,122,134,139,140]]),
([v261,v0,v1,v2,v3,v78,v252],[0,2,4,8,10,21,55,63,64,65,150,154,160,224,225,245,274,338,409,445,513,532,602,617,641],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,45,47,48,50,54,56,57,59,60,65,67,71,78,79,85,87,88],[[2,4,10,12,17,104,111,125],[15,16,23,24,103,129],[1,3,12,110,113,131],[5,8,11,18,19,20,101,124,128],[7,9,13,14,19,118,123,127],[0,6,21,22,134,136],[16,17,103,111,114,121],[12,110,111,125,131],[17,101,108,111,112,121],[17,111,117,118,121,127],[6,17,111,126,134,136,143],[12,103,110,114,119],[16,20,100,101,103,109,120],[16,19,103,116,118,120,141],[6,16,22,103,130,134,136,137],[12,101,102,107,109,110,119],[12,110,115,118,119,127],[6,12,110,132,134,138,142],[12,19,101,105,118,127,128],[6,20,101,106,133,134,135,139],[6,19,118,122,134,139,140]]),
([v262,v0,v1,v2,v3,v78,v252],[0,2,3,8,9,20,42,50,51,52,150,152,159,221,222,253,331,356,409,435,510,532,599,612,642],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,54,56,57,58,59,60,61,65,71,78,79,90,91,92],[[16,17,23,24,104,123],[2,4,10,12,15,103,112,125],[1,3,12,108,111,127],[5,8,11,18,19,20,101,122],[7,9,13,14,19,116,121],[0,6,21,22,131,134],[15,104,109,112,118],[12,104,109,111,117],[17,20,100,101,104,110,119],[17,19,104,115,116,119,138],[6,17,22,104,124,130,131,133,134],[12,111,112,125,127],[15,101,107,112,118],[15,112,114,116,118,121],[6,15,112,126,131,134,140],[12,101,102,107,111,117],[12,111,113,116,117,121],[6,12,111,128,131,135,139],[12,19,101,105,116,121,122],[6,20,101,106,129,131,132,136],[6,19,116,120,131,136,137]]),
([v263,v0,v1,v2,v3,v78,v252],[0,47,50,52,126,129,130,150,228,240,245,326,331,363,428,506,532,547,577,598],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,54,56,57,58,59,60,61,65,71,78,79,91,92],[[1,8,13,104,119,123],[6,7,9,10,11,103,112,125],[5,7,9,108,111,127],[15,17,18,101,122],[2,3,12,13,14,116,121],[0,4,16,19,131,134],[11,104,109,112,118],[9,104,109,111,117],[13,18,100,101,104,110],[9,13,104,115,116,123],[4,13,104,124,130,131,133,134],[9,111,112,125,127],[11,101,107,112,118],[11,112,114,116,118,121],[4,11,112,126,131,134,139],[9,101,102,107,111,117],[9,111,113,116,117,121],[4,9,111,128,131,135,138],[14,101,105,116,121,122],[4,18,101,106,129,131,132,136],[4,14,116,120,131,136,137]]),
([v264,v0,v1,v2,v3,v78,v252],[0,20,47,51,102,105,106,150,168,211,228,245,302,331,362,409,486,510,532,567,578,642],[1,2,3,5,6,7,8,11,14,20,22,23,24,26,27,28,29,31,32,33,34,35,36,39,41,42,44,45,48,50,54,56,57,58,59,60,61,65,67,71,73,78,79],[[2,8,10,14,104,121,125],[6,7,9,11,12,103,112,120],[5,7,9,108,111,118],[1,3,13,14,17,101,109,124],[15,16,19,20,116,123],[0,4,18,21,134,141],[12,112,119,120,121,125],[9,111,117,118,121,125],[9,14,100,101,121,125],[14,115,116,121,127,136],[4,14,121,126,133,134,136,137],[9,110,111,112,128,130],[12,101,107,112,120],[12,112,114,116,120,123],[4,12,112,129,134,137,138],[9,101,102,107,111,118],[9,111,113,116,118,123],[4,9,111,131,134,139,140],[16,17,101,105,116,123,124],[4,17,101,106,132,134,135,141],[4,16,20,116,122,134,141,142]]),
([v0,v265,v1,v2,v3,v78,v252],[0,16,26,106,140,149,150,209,245,303,331,371,409,491,508,567,573,621,639],[1,2,3,5,6,7,8,9,11,13,14,15,22,23,24,26,28,29,32,35,36,39,41,42,44,45,48,50,53,56,59,60,64,65,67,71,73,78,79,81,82],[[1,5,11,104,111,119],[9,111,114,119,139],[7,11,109,110,111,113,123],[3,11,100,101,111,119,128],[11,111,116,117,119,125],[3,111,124,133,137,140],[0,3,8,9,103,114,139],[6,7,17,18,110,118],[2,4,10,11,14,101,108],[12,13,15,16,117,121],[0,3,130,133,137],[7,9,110,112,113,114,126],[9,101,108,114,139],[9,114,117,121,126],[3,114,127,132,133,134,135],[7,14,101,102,107,108,110,118],[7,13,16,110,115,117,118,121],[3,110,129,133,135,136],[13,14,101,105,117,121,122],[3,101,106,131,133,137],[3,117,120,133,137,138]]),
([v0,v266,v1,v2,v3,v78,v252],[0,15,17,105,138,148,150,212,245,300,331,366,409,488,507,567,570,617,638],[0,1,2,4,5,6,7,11,14,15,17,22,23,24,27,28,29,34,35,36,39,41,42,44,45,47,50,54,56,59,60,64,65,67,71,73,79,82,84,87],[[1,5,11,105,109,118],[9,11,103,104,105,113,122],[7,105,112,118,139],[3,11,101,102,105,118,125],[11,105,115,116,118,124],[3,105,123,132,137,138],[8,9,17,18,104,117],[0,3,6,7,108,112,139],[2,4,10,11,14,102,107],[12,13,15,16,116,120],[0,3,129,132,138],[7,104,111,112,113,127],[9,14,100,102,104,107,117],[9,13,16,104,114,116,117,120],[3,104,126,131,132,133,134],[7,102,107,112,139],[7,112,116,120,127],[3,112,128,132,134,135],[13,14,102,106,116,120,121],[3,102,110,130,132,138],[3,116,119,132,136,138]]),
([v0,v267,v1,v2,v3,v78,v252],[0,60,63,65,117,119,122,123,150,216,232,236,245,256,281,404,438,506,532,547,579,601],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,45,48,50,54,56,57,59,60,65,67,71,78,79,87,88],[[7,8,11,13,15,104,111,125],[14,103,111,114,121],[11,110,111,125,130],[15,101,108,111,112,121],[15,111,117,118,121,127],[5,15,111,126,133,135,141],[1,9,10,14,103,120,128],[4,6,11,110,113,130],[17,19,20,101,124],[2,3,12,14,16,118,123,127],[0,5,18,21,133,135],[11,103,110,114,119],[14,20,100,101,103,109],[11,14,103,116,118,128],[5,14,103,129,133,135,136],[11,101,102,107,109,110,119],[11,110,115,118,119,127],[5,11,110,131,133,137,140],[16,101,105,118,124,127],[5,20,101,106,132,133,134,138],[5,16,118,122,133,138,139]]),
([v0,v268,v1,v2,v3,v78,v252],[0,21,60,64,93,95,98,99,150,205,216,231,245,247,280,384,409,477,513,532,567,580,641],[0,2,3,5,6,7,8,11,13,14,15,20,23,26,27,28,29,30,32,33,34,35,36,39,42,44,45,47,48,50,54,56,58,59,61,63,65,66,67,71,73,78,79],[[7,8,9,13,15,104,110,121],[14,110,119,120,121,128],[9,108,109,110,124,130],[15,101,110,111,121],[15,110,115,116,121,126],[5,15,110,125,132,133,134,136],[2,10,11,14,103,120,128],[4,6,9,109,112,118],[1,3,12,14,18,101,107,127],[16,17,20,21,116,123],[0,5,19,22,133,141],[9,109,117,118,120,128],[9,14,100,101,120,128],[14,114,116,120,123,138],[5,14,120,129,133,136,138],[9,101,102,109,111,118],[9,109,113,116,118,123],[5,9,109,131,133,139,140],[17,18,101,105,116,123,127],[5,18,101,106,133,135,137,141],[5,17,21,116,122,133,141,142]]),
([v0,v1,v269,v2,v3,v78,v252],[0,16,32,99,133,142,150,203,245,247,289,385,409,482,509,567,576,621,640],[0,2,3,5,6,7,8,10,11,13,14,15,18,20,22,23,24,26,27,29,32,34,36,38,39,42,44,45,47,48,50,53,56,58,59,61,65,66,71,73,78,79,81,82],[[10,111,116,121,143],[0,3,9,11,104,111,143],[7,11,109,110,111,115,125],[11,101,107,111,113,143],[11,111,119,123,125,127],[3,111,126,133,134,135,138],[1,4,10,103,116,121],[7,10,110,114,115,116,129],[3,10,100,101,116,121,131],[10,116,118,119,121,124],[3,116,130,134,140,142],[6,7,17,18,110,120],[2,5,8,10,14,101,108,113],[12,13,15,16,119,124],[0,3,134,136,140],[7,14,101,102,110,112,113,120],[7,13,16,110,117,119,120,124],[3,110,132,134,138,139],[13,14,101,105,119,124,128],[3,101,106,134,137,140],[3,119,122,134,140,141]]),
([v0,v1,v270,v2,v3,v78,v252],[0,14,17,93,98,138,147,206,245,284,331,382,409,479,507,567,569,612,638],[0,1,2,4,5,6,7,9,11,13,14,15,20,23,24,25,27,28,29,34,35,36,39,41,44,45,48,50,54,56,57,58,59,61,65,66,71,73,79,81,84,87,89,91],[[9,103,104,105,111,126],[10,11,17,18,105,120],[7,105,109,110,111,128],[11,14,101,102,105,112,120],[11,13,16,105,117,118,120,125],[4,105,124,131,132,133,136],[1,6,9,104,114,119],[7,104,110,119,143],[4,9,100,102,104,119,123],[9,104,116,118,119,122],[4,104,127,132,139,142],[0,3,4,7,110,113,141],[2,5,8,9,14,102,108,112],[12,13,15,16,118,122],[0,4,132,134,140],[7,102,107,110,112,141],[7,110,118,122,128],[4,110,129,132,136,137],[13,14,102,106,118,122,123],[4,102,115,130,132,135,140],[4,118,121,132,138,140]]),
([v0,v1,v271,v2,v3,v78,v252],[0,73,77,79,80,108,109,111,114,115,150,190,245,322,400,451,506,532,547,581,604],[0,1,2,3,5,6,8,9,11,14,15,16,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,51,54,56,57,59,60,65,71,73,78,81,82,85],[[11,13,104,105,125,127],[6,9,12,13,14,105,110,125],[11,105,109,113,121],[14,101,102,105,112,121],[14,105,117,118,121,129],[7,14,105,126,133,135,140],[5,8,13,104,114,127],[11,104,109,113,120],[13,100,102,104,108,120],[13,104,116,118,120,129],[7,13,104,128,133,135,139],[1,3,11,109,119,130],[16,18,19,102,124],[2,4,10,11,15,118,123,129],[0,7,17,20,133,136],[11,19,102,103,107,108,109],[11,109,115,118,130],[7,11,109,131,133,136,137],[15,102,111,118,124,129],[7,19,102,106,132,133,134,138],[7,15,118,122,133,138,141]]),
([v0,v1,v272,v2,v3,v78,v252],[0,73,76,79,82,83,85,88,89,150,189,245,296,311,313,378,409,468,516,532,567,582,641],[2,4,5,6,9,11,14,15,16,17,20,24,26,27,28,29,30,31,32,34,35,36,39,42,44,45,48,50,53,54,56,58,59,61,65,67,69,71,72,73,78,79],[[10,12,101,102,103,123,126],[5,8,11,12,15,103,107,120],[10,103,117,118,120,129],[15,103,105,110,120],[15,103,114,115,120,125],[6,15,103,124,131,132,133,134],[4,7,12,102,111,119],[10,102,116,118,119,129],[12,102,105,110,119],[12,102,113,115,119,122],[6,12,102,127,132,134,135],[1,3,10,14,106,118,129],[2,9,10,13,18,100,105,128],[16,17,20,21,115,122],[0,6,19,22,132,140],[10,104,105,118,129],[10,112,115,118,122,139],[6,10,118,130,132,137,139],[17,18,105,108,115,122,128],[6,18,105,109,132,136,138,140],[6,17,21,115,121,132,140,141]]),
([v0,v1,v273,v2,v3,v78,v252],[0,18,19,22,23,69,73,75,79,150,184,245,258,298,343,409,453,518,532,555,567,581],[2,3,5,6,11,14,15,16,17,20,23,24,27,28,29,32,34,35,36,39,45,51,53,54,56,59,65,69,71,72,73,78,79,81,82],[[10,12,14,102,103],[2,4,11,12,14,103,106,134],[10,103,105,110,117],[14,103,104,109,117],[14,103,113,114,117,120],[7,14,103,125,126,134],[1,3,12,102,111,133],[10,102,105,110,116],[12,102,104,109,116],[12,102,112,114,116,119],[7,12,102,125,126,133],[6,8,10,105,115,123],[5,9,10,13,17,100,104,122],[15,16,20,21,114,121],[0,7,18,19,125,128],[10,17,101,104,105],[10,105,114,119,123],[7,10,105,124,125,128,130],[16,17,19,104,107,114,119,122],[7,17,19,104,108,125,127,129,131],[7,16,19,114,118,125,131,132]]),
([v0,v1,v274,v2,v3,v78,v252],[0,14,15,73,79,147,148,185,245,283,365,409,457,506,547,556,567,603,638],[0,1,2,4,5,6,7,11,14,15,17,20,24,27,28,29,34,35,36,39,41,42,44,45,48,50,54,56,59,60,70,71,73,79,81,82,84,87,89,91],[[3,9,103,104,105,121,124],[2,6,8,9,10,105,109,117],[7,105,117,126,137],[10,101,102,105,111,117],[10,105,114,115,117,123],[3,105,122,131,135,136],[1,5,9,104,112,116],[7,104,116,126,139],[9,100,102,104,107,116],[9,104,113,115,116,119],[3,104,125,131,134,138],[0,3,4,7,108,126,137],[13,14,15,18,102,107],[11,12,16,17,115,119],[0,3,128,131,136],[7,102,107,126,137],[7,115,119,126,132],[3,7,126,127,130,131,132],[12,15,17,102,106,115,119,120],[3,102,110,129,131,136],[3,115,118,131,133,136]]),
([v0,v1,v251,v2,v3,v78,v252],[0,12,13,69,140,142,150,188,245,265,298,350,409,455,517,555,567,581,621],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,39,45,53,56,59,60,65,66,71,73,79,81,82],[[3,9,11,101,102],[2,5,8,9,11,102,105,114],[7,11,102,104,106,114],[11,102,114,117,120],[11,102,110,111,114,116],[3,102,119,121,127],[1,4,9,101,107,113],[7,9,101,104,106,113],[9,101,113,117,122],[9,101,109,111,113,115],[3,101,119,121,126],[6,7,18,104,112],[0,3,10,14,100,117,120],[12,13,16,17,111,115],[0,3,119,123],[7,14,15,104,112,117,120],[7,13,17,104,108,111,112,115],[3,104,118,119,123,124],[13,14,15,111,115,117,120],[3,14,103,117,119,120],[3,13,111,119,125]]),
([v0,v1,v4,v2,v3,v78,v275],[67,158,182,252,337,419,422,454,506,516,532,539,567,581,613,625,641,643],[0,1,2,3,5,6,7,8,9,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,43,54,55,59,65,71,78,79,81,82,85,90],[[3,4,104,105],[3,111],[2,4,105,110,113,121],[4,101,102,105,112,121],[4,105,117,118,121,136],[4,105,128,129,134],[3,4,114],[2,3,104,110,113,120],[3,100,102,104,109,120],[3,104,116,118,120,135],[3,104,128,129,133],[1,2,14,15,16,17,110,126],[8,9,102,127],[5,7,12,13,118],[10,11,128,130],[2,9,102,103,108,109,110,119],[2,7,110,115,118,119,132],[2,11,110,126,128,130],[3,7,9,102,106,118,125],[0,7,102,107,124,125,128,131],[0,6,7,118,122,123,128,131,132]]),
([v0,v1,v2,v276,v3,v78,v252],[0,15,32,83,89,132,142,150,198,245,294,379,409,473,509,567,575,617,640],[1,2,4,5,6,9,11,14,15,16,17,19,20,22,23,24,26,27,29,32,34,36,38,39,42,44,45,47,50,54,56,58,59,61,63,65,67,71,72,78,79,82,84,87,88],[[10,11,102,103,104,115,124],[8,104,114,119,144],[0,3,4,11,104,108,141],[11,100,104,106,112,141],[11,104,118,122,124,126],[4,104,125,131,132,133,135],[8,103,113,114,115,129],[9,10,17,18,103,120],[10,14,103,106,111,112,120],[10,13,16,103,117,118,120,123],[4,103,128,132,135,136],[1,5,8,107,114,119],[4,8,105,106,114,119,127],[8,114,116,118,119,123],[4,114,130,132,142,143],[2,6,7,8,14,101,106,112],[12,13,15,16,118,123],[0,4,132,137,139],[13,14,106,109,118,123,127],[4,106,110,132,134,138,139],[4,118,121,132,139,140]]),
([v0,v1,v2,v277,v3,v78,v252],[0,14,26,82,88,131,140,150,193,297,331,376,409,470,508,567,572,612,639],[0,2,4,5,6,9,10,11,13,14,15,16,20,23,24,25,26,28,29,32,35,36,39,41,44,45,48,50,54,56,57,58,59,61,65,67,71,72,78,79,81,87,89,92],[[9,102,103,104,110,126],[8,104,108,109,110,128],[10,11,17,18,104,120],[11,14,104,106,107,112,120],[11,13,16,104,117,118,120,125],[4,104,124,131,132,133,134],[8,103,109,119,143],[0,3,4,9,103,114,140],[9,100,103,107,112,140],[9,103,118,122,126],[4,103,127,132,134,135],[1,5,8,109,113,119],[4,8,105,107,109,119,123],[8,109,116,118,119,122],[4,109,129,132,141,142],[2,6,7,8,14,101,107,112],[12,13,15,16,118,122],[0,4,132,136,138],[13,14,107,111,118,122,123],[4,107,115,130,132,137,138],[4,118,121,132,138,139]]),
([v0,v1,v2,v278,v3,v78,v252],[0,27,28,29,56,60,62,91,150,164,216,229,245,275,311,346,409,440,515,532,553,567,579],[2,3,5,6,7,8,11,12,14,15,20,23,24,26,28,29,32,34,35,36,39,45,47,48,50,59,63,65,66,67,71,78,79,87,88],[[13,102,109,112,118],[9,15,108,109],[2,8,9,14,15,103,109,134],[15,100,109,110,118],[15,109,114,115,118,121],[6,15,109,125,127,134],[9,102,108,112,116],[5,10,11,13,102,117,123],[9,13,18,100,102,107],[13,102,115,120,123],[6,13,102,124,125,127,129],[1,3,9,108,111,133],[9,100,101,108,110,116],[9,108,113,115,116,120],[6,9,108,125,130,133],[4,7,12,13,18,100,106,122],[16,17,21,22,115,121],[0,6,19,20,125,127],[17,18,20,100,104,115,120,122],[6,18,20,100,105,125,126,128,131],[6,17,20,115,119,125,131,132]]),
([v0,v1,v2,v279,v3,v78,v252],[0,14,16,60,131,149,150,192,216,276,370,409,444,506,547,554,567,600,639],[2,3,5,6,7,8,9,10,11,13,14,15,20,23,26,28,29,32,35,36,39,41,42,44,45,48,50,54,56,59,60,64,65,67,78,79,81,87,88,89,92],[[9,111,118,125,136],[3,7,109,110,111,122,127],[2,5,6,7,10,103,111,118],[10,100,107,111,112,118],[10,111,115,116,118,124],[3,111,123,132,134,138],[7,110,117,125,140],[0,3,8,9,102,125,136],[9,100,108,125,136],[9,116,120,125,133],[3,9,125,126,131,132,133],[1,4,7,110,113,117],[7,100,101,106,108,110,117],[7,110,114,116,117,120],[3,110,128,132,137,139],[13,14,15,18,100,108],[11,12,16,17,116,120],[0,3,129,132,134],[12,15,17,100,104,116,120,121],[3,100,105,130,132,134],[3,116,119,132,134,135]]),
([v0,v1,v2,v254,v3,v78,v252],[0,11,13,56,91,138,142,150,174,245,279,331,349,409,442,514,553,567,579,617],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,39,45,47,50,59,60,65,67,71,72,79,87,88],[[10,12,101,105,107,114],[3,8,12,104,105],[2,6,7,8,12,102,105,114],[12,105,114,117,120],[12,105,110,111,114,116],[3,105,119,121,127],[8,101,104,107,112],[9,10,19,101,113],[10,15,16,101,113,117,120],[10,14,18,101,109,111,113,115],[3,101,118,119,121,122],[1,5,8,11,12,104,106,112],[8,104,112,117,124],[8,104,108,111,112,115],[3,104,119,123,126],[0,3,4,15,100,117,120],[13,14,17,18,111,115],[0,3,119,121],[14,15,16,111,115,117,120],[3,15,103,117,119,120],[3,14,111,119,125]]),
([v0,v1,v2,v5,v3,v78,v275],[54,158,252,273,337,419,421,441,506,513,532,538,567,579,613,630,641,642],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,43,48,49,59,65,71,78,79,85,87,88,90],[[3,4,103,111,114,121],[1,4,110,111],[1,104],[4,101,108,111,112,121],[4,111,117,118,121,136],[4,111,128,129,135],[1,103,110,114,119],[2,3,14,15,16,17,103,126],[3,9,100,101,103,109,120],[3,7,103,116,118,120,133],[3,11,103,126,128,129],[1,4,113],[1,101,102,107,109,110,119],[1,110,115,118,119,132],[1,110,128,130,134],[8,9,101,127],[5,7,12,13,118],[10,11,128,129],[1,7,9,101,105,118,125],[0,7,101,106,124,125,128,131],[0,6,7,118,122,123,128,131,132]]),
([v0,v1,v2,v280,v3,v78,v252],[0,33,34,43,47,49,90,150,167,228,245,261,331,357,409,430,512,532,551,567,577],[2,3,5,6,7,8,11,14,15,20,21,23,24,26,27,29,32,34,35,36,38,39,41,42,44,45,57,58,59,60,61,65,71,78,79,91,92],[[11,103,108,112,117],[8,103,108,111,116],[4,9,13,103,118,123],[8,13,16,100,103,110],[13,103,115,120,123,125],[5,13,103,124,127,128,130,131],[8,11,111,112],[2,7,8,10,11,102,112,136],[11,100,106,112,117],[11,112,114,115,117,121],[5,11,112,128,131,136],[1,7,8,107,111,135],[8,100,101,106,111,116],[8,111,113,115,116,121],[5,8,111,128,132,135],[3,6,12,13,16,100,109,122],[14,15,19,20,115,121],[0,5,17,18,128,131],[15,16,18,100,104,115,121,122],[5,16,18,100,105,126,128,129,133],[5,15,18,115,119,128,133,134]]),
([v0,v1,v2,v281,v3,v78,v252],[0,15,16,47,132,133,150,197,228,288,358,409,434,506,547,552,567,597,640],[2,3,5,6,7,8,11,14,20,22,23,24,26,27,29,32,34,36,38,39,41,42,44,45,48,50,54,56,57,58,59,60,61,65,78,79,82,84,88,91,92],[[9,111,116,121,136],[7,110,115,121,138],[0,3,8,10,103,121,136],[10,100,108,121,136],[10,114,118,121,123,132],[3,10,121,122,129,130,132],[3,7,109,110,111,124,126],[2,5,6,7,9,102,111,116],[9,100,106,111,116],[9,111,113,114,116,119],[3,111,125,130,134,140],[1,4,7,107,110,115],[7,100,101,106,110,115],[7,110,112,114,115,119],[3,110,127,130,137,139],[13,14,15,18,100,108],[11,12,16,17,114,119],[0,3,130,133,134],[12,15,17,100,104,114,119,120],[3,100,105,128,130,131,134],[3,114,117,130,134,135]]),
([v0,v1,v2,v256,v3,v78,v252],[0,11,12,43,90,138,140,150,171,245,264,331,361,409,432,511,551,567,577,612],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,37,39,41,44,45,57,58,59,60,61,65,66,71,72,79,91,92],[[10,102,105,107,113],[8,102,105,106,112],[11,12,19,102,114],[12,15,16,102,114,117,126],[12,14,18,102,110,111,114,119],[3,102,118,121,122,124,125],[3,8,10,106,107],[2,6,7,8,10,101,107,113],[10,107,113,117,126],[10,107,109,111,113,116],[3,107,122,125,131],[1,5,8,9,10,104,106,112],[8,106,112,117,128],[8,106,108,111,112,116],[3,106,122,127,130],[0,3,4,15,100,117,126],[13,14,17,18,111,119],[0,3,122,125],[14,15,16,111,115,116,117,123],[3,15,103,117,120,122,123],[3,14,111,122,129]]),
([v0,v1,v2,v7,v3,v78,v275],[41,158,252,337,355,419,420,431,506,510,532,537,567,577,618,635,641],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,43,59,65,71,78,79,85,90,91,92],[[2,104,109,112,118],[1,104,109,111,117],[3,4,14,15,16,104,123],[4,9,100,101,104,110,119],[4,7,104,115,116,119,131],[4,11,104,123,125,126],[1,2,111,112],[1,103],[2,101,107,112,118],[2,112,114,116,118,130],[2,112,125,126,133],[1,2,108],[1,101,102,107,111,117],[1,111,113,116,117,129],[1,111,125,127,132],[8,9,101,124],[5,7,12,13,116],[10,11,125,126],[1,7,9,101,105,116,124],[0,7,101,106,122,124,125,128],[0,6,7,116,120,121,125,128,129]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x3 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x4 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x5 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x6 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopW ptopQ ptopI7 (chunks 4 ptopD8 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  · exact ptopC8x3
  · exact ptopC8x4
  · exact ptopC8x5
  · exact ptopC8x6
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([v282,v0,v1,v4,v2,v3,v78,v252],[0,66,133,149,180,213,214,245,304,331,386,449,493,496,506,516,532,539,547,555,567,581,612,621],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,39,45,51,54,57,59,60,66,72,73,75,76,77,78,79,81,82,84,89,93],[[9,10,102,113],[7,8,101,112],[14,15,18,19],[4,6,15,19,103,111],[1,100],[11,13,15,19,110,115],[1,15,120],[8,10,101,102],[2,8,104],[6,10,102,103,105,113],[10,102,113,121,122],[10,102,109,110,113,116],[1,102,127,128,131,133],[3,8,10,106],[6,8,101,103,105,112],[8,101,112,121,122],[8,101,108,110,112,115],[1,101,126,128,130,132],[5,6,22,23,103,118],[14,15,121,123],[12,13,20,21,110,117],[0,1,16,17,128],[6,15,103,111,121,123],[6,13,21,103,107,110,111,115],[1,103,124,128,132],[13,15,110,115,121,134],[1,15,119,121,128],[1,17,110,114,125,128,129]]),
([v282,v0,v1,v2,v5,v3,v78,v252],[0,53,132,148,150,213,271,304,305,331,386,436,493,495,506,513,532,538,547,553,567,579,612,617],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,39,45,48,57,59,60,66,67,72,75,78,79,83,84,87,88,89,93],[[9,10,104,113],[6,8,15,19,101,112],[4,5,103,111],[14,15,18,19],[1,100],[11,13,15,19,110,115],[1,15,119],[8,10,101,104,106,113],[5,10,103,104],[2,5,102],[10,104,113,120,121],[10,104,109,110,113,116],[1,104,125,127,130,131],[5,101,103,106,111],[7,8,22,23,101,117],[8,15,101,112,120,121],[8,13,21,101,108,110,112,115],[1,101,122,125,128],[3,5,10,105],[5,103,111,120,123],[5,103,107,110,111,115],[1,103,125,128,129],[14,15,120,121],[12,13,20,21,110,116],[0,1,16,17,125],[13,15,110,115,120,132],[1,15,118,120,125],[1,17,110,114,124,125,126]]),
([v282,v0,v1,v2,v7,v3,v78,v252],[0,40,131,147,150,213,245,304,353,386,387,426,493,494,506,510,532,537,547,551,567,577,612,617],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,39,42,45,57,59,60,61,66,72,75,78,79,84,89,91,92,93],[[8,10,15,19,102,113],[6,7,106,112],[4,5,105,111],[14,15,18,19],[1,100],[11,13,15,19,110,115],[1,15,119],[7,102,104,106,112],[5,102,104,105,111],[9,10,22,23,102,116],[10,15,102,113,120,122],[10,13,21,102,109,110,113,117],[1,102,121,125,128],[5,7,105,106],[2,5,101],[7,106,112,120,122],[7,106,108,110,112,115],[1,106,125,127,130],[3,5,7,103],[5,105,111,120,123],[5,105,107,110,111,115],[1,105,125,127,129],[14,15,120,122],[12,13,20,21,110,115],[0,1,16,17,125],[13,15,110,115,120,131],[1,15,118,120,125],[1,17,110,114,124,125,126]]),
([v283,v0,v1,v4,v2,v3,v78,v252],[0,66,133,149,180,241,242,245,327,331,405,409,449,516,519,532,539,547,555,567,581,612,621,622,632],[0,1,2,3,5,6,8,9,11,14,15,20,23,24,29,32,34,35,41,53,54,57,59,60,65,71,73,75,78,79,81,82,85,90],[[9,10,105,117],[7,8,104,116],[15,16,21,23],[4,6,16,24,109,115],[13,16,18,102,118],[1,114],[1,12,128],[8,10,104,105],[2,8,110],[6,10,105,109,112,117],[10,101,102,105,111,117],[10,105,117,129,133],[1,105,122,124,131],[3,8,10,113],[6,8,104,109,112,116],[8,100,102,104,108,116],[8,104,116,129,132],[1,104,122,124,130],[5,6,21,22,109,120],[14,17,18,20,102,119],[11,12,19,20,129],[0,1,122,125],[6,18,20,102,103,107,108,109,115],[6,12,109,115,129,132],[1,109,122,125,126],[12,18,102,118,129],[1,16,102,106,121,122,123],[1,12,122,127,129]]),
([v283,v0,v1,v2,v5,v3,v78,v252],[0,53,132,148,150,241,271,327,328,331,405,409,436,513,519,532,538,547,553,567,579,612,617,622,627],[0,2,3,5,6,8,9,10,11,14,15,20,23,24,29,32,34,35,41,47,48,57,59,60,65,67,71,75,78,79,85,87,88,90],[[9,10,110,117],[6,8,16,24,103,116],[4,5,109,115],[15,16,21,23],[13,16,18,101,118],[1,114],[1,12,128],[8,10,103,110,113,117],[5,10,109,110],[2,5,104],[10,101,107,110,111,117],[10,110,117,129,133],[1,110,122,124,132],[5,103,109,113,115],[7,8,21,22,103,120],[8,18,20,100,101,103,108,116],[8,12,103,116,129,130],[1,103,122,124,125],[3,5,10,112],[5,101,102,106,108,109,115],[5,109,115,129,130],[1,109,122,126,131],[14,17,18,20,101,119],[11,12,19,20,129],[0,1,122,124],[12,18,101,118,129],[1,16,101,105,121,122,123],[1,12,122,127,129]]),
([v283,v0,v1,v2,v7,v3,v78,v252],[0,40,131,147,150,241,245,327,353,405,406,409,426,510,519,532,537,547,551,567,577,612,617,622,623],[1,2,3,5,6,8,11,14,15,20,23,24,29,32,34,35,41,42,57,58,59,60,61,65,71,75,78,79,85,90,91,92],[[8,10,16,24,104,115],[6,7,111,114],[4,5,110,113],[15,16,22,23],[13,16,18,101,116],[1,112],[1,12,126],[7,104,108,111,114],[5,104,108,110,113],[9,10,21,22,104,117],[10,18,20,100,101,104,109,115],[10,12,104,115,127,129],[1,104,119,120,122,123],[5,7,110,111],[2,5,103],[7,101,106,111,114],[7,111,114,127,128],[1,111,120,123,131],[3,5,7,107],[5,101,102,106,110,113],[5,110,113,127,128],[1,110,120,124,130],[14,17,18,20,101,116],[11,12,19,20,127],[0,1,120,123],[12,18,101,116,127],[1,16,101,105,118,120,121],[1,12,120,125,127]]),
([v13,v0,v1,v4,v2,v3,v78,v252],[66,180,245,247,260,311,392,449,516,539,547,555,567,581,612,623],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,39,45,51,53,54,55,56,59,65,69,71,72,73,78,79,81,82],[[2,3,5,6,102,113],[2,5,101,112],[3,8],[1,11,15,103,111],[4,11,100],[7,11,13,110,115],[0,9,11,122,128],[5,6,101,102],[5,104],[6,102,103,105,113],[5,6,102,113,118],[6,102,109,110,113,116],[6,102,122,123,131],[5,6,106],[5,101,103,105,112],[5,101,112,118],[5,101,108,110,112,115],[5,101,122,123,130],[14,15,103,119],[8,10,11,14,118],[12,13,110,117],[10,11,122,125],[8,11,15,103,111,118],[13,103,107,110,111,115],[11,103,121,122,125,127],[8,11,110,115,118,126],[8,11,118,120,122,124,126,128],[11,110,114,122,128,129]]),
([v16,v0,v1,v2,v5,v3,v78,v252],[53,64,150,153,166,223,271,280,391,436,445,513,538,547,553,567,579,612,627,628],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,39,45,47,48,49,50,59,63,65,66,67,71,78,79,87,88],[[2,3,5,8,104,113],[6,7,14,18,101,112],[2,5,103,111],[3,11],[4,14,100],[9,10,14,16,110,115],[0,1,12,14,121,127],[7,8,101,104,106,113],[5,8,103,104],[5,102],[5,8,104,113,117],[8,104,109,110,113,116],[1,8,104,121,123,130],[5,101,103,106,111],[7,17,19,101,118],[7,11,14,101,112,117],[7,10,16,101,108,110,112,115],[1,7,14,101,120,121,123,125],[5,8,105],[5,103,111,117],[5,103,107,110,111,115],[1,5,103,121,126,129],[11,13,14,17,117],[10,15,16,110,116],[1,14,121,123],[10,11,14,110,115,117,124],[1,11,14,117,119,121,122,124,127],[1,10,14,110,114,121,127,128]]),
([v21,v0,v1,v2,v7,v3,v78,v252],[40,51,150,151,163,220,310,353,362,426,435,510,537,547,551,567,577,617,623,633],[2,5,6,14,15,23,24,26,27,28,29,32,34,35,36,37,39,41,42,43,44,45,57,58,59,60,61,65,71,78,79,91,92],[[7,8,14,18,102,113],[2,3,5,6,106,112],[2,5,105,111],[3,11],[4,14,100],[9,10,14,16,110,116],[0,1,12,14,124,129],[6,102,104,106,112],[5,102,104,105,111],[8,17,19,102,118],[8,11,14,102,113,117],[8,10,16,102,109,110,113,121],[1,8,14,102,120,123,124,126,127],[5,6,105,106],[5,101],[5,6,106,112,117],[6,106,108,110,112,116],[1,6,106,124,127,132],[5,6,103],[5,105,111,117],[5,105,107,110,111,116],[1,5,105,124,128,131],[11,13,14,17,117],[10,15,16,110,116],[1,14,124,127],[10,11,14,110,115,116,117,125],[1,11,14,117,119,122,124,125,129],[1,10,14,110,114,124,129,130]]),
([v93,v0,v1,v4,v2,v3,v78,v252],[66,134,137,180,226,227,245,249,270,315,331,393,409,449,506,516,539,546,547,555,589,592,616,626,647,649],[0,1,2,3,5,6,8,9,11,14,15,20,23,24,29,32,34,35,37,39,41,45,51,54,56,57,59,60,65,71,72,73,78,81,82],[[10,11,105,117],[6,9,104,116],[18,19,20,21],[3,5,19,21,109,115],[8,13,120],[7,13,15,114],[0,2,16,19,126,132],[9,11,104,105],[9,110],[5,11,105,109,112,117],[11,101,102,105,111,117],[11,105,117,119,121],[2,11,105,126,128,134],[9,11,113],[5,9,104,109,112,116],[9,100,102,104,108,116],[9,104,116,119,121],[2,9,104,126,128,133],[4,5,22,23,24,25,109,123],[14,15,18,19,102,130],[12,13,119,122],[1,2,17,19,126,129],[5,15,19,102,103,107,108,109,115],[5,13,109,115,119,122],[2,5,19,109,124,126,129,131],[13,15,102,118,119],[2,15,19,102,106,125,126,127,132],[2,13,19,119,126,132]]),
([v93,v0,v1,v2,v5,v3,v78,v252],[53,134,136,150,155,179,226,271,315,316,331,393,409,436,506,513,538,546,547,553,589,591,616,631,647,648],[0,2,3,5,6,8,9,10,11,14,15,20,23,24,29,32,34,35,37,39,41,45,48,50,51,57,59,60,65,66,67,71,78,87,88],[[10,11,110,117],[7,9,19,21,103,116],[3,6,109,115],[18,19,20,21],[5,13,120],[4,13,15,114],[0,2,16,19,126,132],[9,11,103,110,113,117],[6,11,109,110],[6,104],[11,101,107,110,111,117],[11,110,117,119,121],[2,11,110,126,128,134],[6,103,109,113,115],[8,9,22,23,24,25,103,122],[9,15,19,100,101,103,108,116],[9,13,103,116,119,121],[2,9,19,103,123,126,128,130],[6,11,112],[6,101,102,106,108,109,115],[6,109,115,119,124],[2,6,109,126,131,133],[14,15,18,19,101,129],[12,13,119,121],[1,2,17,19,126,128],[13,15,101,118,119],[2,15,19,101,105,125,126,127,132],[2,13,19,119,126,132]]),
([v93,v0,v1,v2,v7,v3,v78,v252],[40,134,135,150,155,179,226,245,315,353,393,394,409,426,506,510,537,546,547,551,589,590,620,636,647],[1,2,3,5,6,8,11,14,15,20,23,24,29,32,34,35,37,39,41,42,44,45,51,57,58,59,60,61,65,71,78,91,92],[[9,11,19,21,104,115],[7,8,111,114],[3,6,110,113],[18,19,20,21],[5,13,118],[4,13,15,112],[0,2,16,19,125,130],[8,104,108,111,114],[6,104,108,110,113],[10,11,22,23,24,104,119],[11,15,19,100,101,104,109,115],[11,13,104,115,117,121],[2,11,19,104,120,124,125,127,128],[6,8,110,111],[6,103],[8,101,106,111,114],[8,111,114,117,121],[2,8,111,125,128,132],[6,8,107],[6,101,102,106,110,113],[6,110,113,117,122],[2,6,110,125,129,131],[14,15,18,19,101,126],[12,13,117,121],[1,2,17,19,125,128],[13,15,101,116,117],[2,15,19,101,105,123,125,126,130],[2,13,19,117,125,130]]),
([v11,v0,v1,v2,v3,v78,v252],[0,14,15,147,148,180,216,228,317,395,409,506,532,547,567,612,621,643,646,649],[0,1,2,5,6,7,8,11,13,14,15,20,22,24,27,28,29,34,35,36,39,41,45,54,56,57,59,60,65,71,73,78,79,81,82],[[2,4,5,6,8,104,110],[1,3,5,7,8,103,113],[5,15,109],[11,13,16,102,107],[10,14,16,116,120],[0,12,15,16,126,129],[5,8,103,104,110,113],[5,9,104,108,110,123],[9,101,102,104,111,118],[9,104,115,116,118,122],[9,104,126,128,134],[5,8,103,112,113,123],[8,100,102,103,107,117],[8,103,114,116,117,120],[8,103,126,128,133],[5,16,102,107,123],[5,116,120,123,130],[5,123,124,126,129,130],[17,18,19,102,105,116,120,121],[15,16,102,106,125,126,127,131],[15,16,116,119,126,131,132]]),
([v47,v0,v1,v4,v2,v3,v78,v252],[66,81,84,150,180,216,228,245,292,331,374,449,466,467,506,516,539,540,567,581,612,614,621,623],[2,5,6,9,11,14,15,16,17,20,24,26,27,28,29,30,31,32,34,35,36,39,45,51,53,59,65,69,71,72,78,79,81,82,87,91],[[9,10,102,119],[7,8,101,118],[14,15,20,23],[4,15,105],[4,100],[11,13,15,19,114,121],[0,2,15,16,125,128],[8,10,101,102],[5,8,106],[4,102,116,117,119,135],[10,102,104,109,119],[10,102,113,114,119,122],[2,10,102,125,126,133],[6,8,10,110],[4,101,115,117,118,134],[8,101,104,109,118],[8,101,112,114,118,121],[2,8,101,125,126,132],[3,4,22,23,117],[14,15,104,124],[12,13,18,19,114,123],[1,2,17,21,125,128],[4,15,103,104,117],[4,19,111,114,117,121],[2,4,117,125,128,134],[13,15,104,107,114,121,124],[2,15,104,108,125,127,129,130],[2,13,19,114,120,125,130,131]]),
([v47,v0,v1,v2,v3,v78,v252,v284],[0,11,17,81,150,196,287,292,293,331,374,463,466,472,506,509,532,540,567,574,617,621,627],[2,5,6,9,11,14,16,17,19,20,24,26,27,29,32,34,36,39,44,45,53,59,61,65,67,72,78,79,82,84,86,87,88,91],[[9,10,122,128],[6,8,15,20,101,110],[2,5,15,105],[1,5,100],[11,13,15,19,113,117],[0,3,121,126],[14,15,16,17],[8,10,101,110,122,128],[5,114,122,130,132,133],[10,104,109,122,128],[10,113,119,122,128],[3,10,118,121,122],[3,102],[5,101,110,114,131],[8,15,101,104,108,109,115],[8,13,19,101,112,113,115,117],[3,101,121,124,126],[7,8,17,22,101,110],[5,15,103,104,114],[5,19,111,113,114,117],[3,114,121,129,131],[4,5,17,21,114],[13,15,104,106,113,117,120],[3,104,107,121,125,126],[14,15,104,109],[3,113,116,121,126,127],[12,13,17,18,113,119],[3,10,123]]),
([v47,v0,v1,v2,v3,v78,v252,v285],[0,11,17,81,150,191,245,292,369,374,375,460,466,469,506,508,532,540,567,571,612,621,623],[2,5,6,9,10,11,14,15,16,20,25,26,28,29,32,35,36,39,45,50,53,59,61,65,67,72,78,79,81,87,89,91,92],[[8,10,15,20,102,107],[6,7,124,128],[2,5,15,106],[1,5,100],[11,13,15,19,113,117],[0,3,123,126],[14,15,16,17],[7,102,107,124,128],[5,102,107,114,131],[10,15,102,104,105,109,115],[10,13,19,102,112,113,115,118],[3,102,122,123,126],[9,10,17,22,102,107],[5,114,124,129,132],[7,105,109,124,128],[7,113,117,124,128],[3,7,119,123,124],[3,101],[5,15,103,105,114],[5,19,111,113,114,117],[3,114,123,129,130],[4,5,17,21,114],[13,15,105,108,113,117,120],[3,105,110,123,125,126],[14,15,105,109],[3,113,116,123,126,127],[12,13,17,18,113,117],[3,7,121]]),
([v18,v0,v1,v2,v3,v78,v252],[0,11,15,35,81,148,166,207,223,245,262,374,409,417,530,532,547,567,617,621],[0,2,4,5,6,7,8,11,14,15,20,24,27,28,29,34,35,36,39,41,44,45,50,57,58,59,60,61,65,67,71,78,79,91],[[2,5,6,7,11,104,109],[9,10,18,19,103,111],[6,16,108],[1,4,6,8,11,101,107],[12,13,17,114,118],[0,3,15,16,125,130],[10,11,102,103,104,109,111],[6,11,104,109,133],[6,11,101,104,110,116],[11,104,113,114,116,121],[3,11,104,120,124,125,127,128],[6,10,103,111,133],[10,14,16,100,101,103,107,115],[10,13,17,103,112,114,115,118],[3,10,16,103,122,125,128,129],[6,16,101,107,133],[6,17,114,118,133],[3,6,125,130,133],[13,14,16,101,105,114,118,119],[3,14,16,101,106,123,125,126,131],[3,13,16,114,117,125,131,132]]),
([v23,v0,v1,v2,v3,v78,v252],[0,11,14,30,81,147,163,201,220,292,331,347,409,414,529,532,547,567,612,621],[1,2,4,5,6,7,8,9,11,14,15,20,24,27,28,29,34,35,36,39,44,45,47,50,58,59,61,63,65,66,67,71,78,79,87],[[10,11,18,19,104,110],[2,5,6,7,9,103,112],[6,16,109],[1,4,6,8,9,101,108],[12,13,17,115,119],[0,3,15,16,125,131],[9,102,103,104,110,112],[6,11,104,110,134],[11,14,16,100,101,104,111,117],[11,13,17,104,114,115,117,121],[3,11,16,104,120,124,125,126,128],[6,9,103,112,134],[6,9,101,103,108,116],[9,103,113,115,116,119],[3,9,103,123,125,128,130],[6,16,101,107,108,134],[6,17,115,119,134],[3,6,125,131,134],[13,14,16,101,105,115,119,122],[3,14,16,101,106,125,127,129,132],[3,13,16,115,118,125,132,133]]),
([v286,v0,v1,v4,v2,v3,v78,v252],[66,107,110,150,180,216,228,245,320,331,398,409,449,516,520,539,543,555,558,567,581,603,612,623],[0,1,2,3,5,6,8,9,11,14,15,16,20,23,24,26,27,28,29,32,34,35,36,39,41,51,53,57,59,60,65,71,73,78,81,82,85],[[9,10,105,135],[7,8,104,134],[19,20,22,23],[4,12,119],[13,17,20,102,124],[4,123],[0,2,15,20,128,133],[8,10,104,105],[5,8,110],[4,105,109,113,121],[10,101,102,105,112,121],[10,105,117,118,121,125],[2,10,105,128,130,135],[6,8,10,114],[4,104,109,113,120],[8,100,102,104,108,120],[8,104,116,118,120,125],[2,8,104,128,130,134],[3,4,109,132],[14,18,20,102,126],[11,12,118,125],[1,2,16,21,128,131],[4,20,102,103,107,108,109],[4,12,109,115,118],[2,4,109,128,131,132],[12,102,111,118,124,125],[2,20,102,106,127,128,129,133],[2,12,118,122,128,133,136]]),
([v287,v0,v1,v2,v3,v78,v252],[0,15,53,148,196,245,290,397,409,464,506,532,547,565,567,593,617,621,632],[0,2,5,6,7,8,10,11,13,14,15,20,22,23,24,27,28,29,34,35,36,39,41,44,45,54,57,59,60,61,65,67,71,78,79],[[0,1,3,4,103,110,129],[5,6,16,17,102,114],[2,4,11,109],[10,12,13,17,101,107],[8,9,14,15,117,121],[0,3,127,130,132],[6,7,102,110,114,119],[3,4,7,108,110,113,129],[7,101,106,110,111,119],[7,110,116,117,119,124],[3,110,123,127,129,132],[4,102,112,113,114,125],[6,13,18,100,101,102,107,118],[6,9,15,102,115,117,118,121],[3,102,127,131,133],[4,17,101,107,113],[4,113,117,121,125],[3,113,127,132],[9,13,15,101,104,117,121,122],[3,101,105,126,127,128,133],[3,117,120,127,133,134]]),
([v288,v0,v1,v2,v3,v78,v252],[0,14,40,147,191,319,331,372,409,461,506,532,547,564,567,593,612,621,637],[1,2,5,6,7,8,9,11,13,14,15,20,22,23,24,27,28,29,34,35,36,39,41,45,50,54,59,60,61,65,67,71,78,79],[[6,7,16,17,103,110],[0,1,3,4,102,114,130],[2,4,11,113],[10,12,13,17,101,107],[8,9,14,15,117,123],[0,3,126,129,131],[5,103,110,114,118],[4,103,108,109,110,125],[7,13,18,100,101,103,111,119],[7,9,15,103,116,117,119,123],[3,103,128,129,132],[3,4,5,109,112,114,130],[5,101,107,114,118],[5,114,115,117,118,121],[3,114,124,129,130,131],[4,17,101,106,107,109],[4,109,117,121,125],[3,109,129,131],[9,13,15,101,104,117,121,122],[3,101,105,127,129,132],[3,117,120,129,132,133]]),
([v289,v0,v1,v2,v3,v78,v252],[0,11,17,81,170,245,268,331,351,409,423,523,532,547,567,612,617,621,632],[2,4,5,6,8,9,10,11,14,15,16,19,20,24,26,27,28,29,32,34,35,36,39,44,45,50,53,58,59,60,61,65,67,71,79,84],[[7,8,15,17,103,109],[5,6,16,17,102,113],[2,4,12,108],[0,1,3,4,100,107,129],[9,10,14,117,122],[0,3,128,133],[6,8,18,101,102,103,109,113],[4,8,103,109,118],[8,11,13,103,106,107,112,120],[8,10,14,103,116,117,120,124],[3,103,123,127,128,130,131],[4,6,102,113,118],[6,11,13,102,107,111,112,119],[6,10,14,102,115,117,119,122],[3,102,125,128,131,132],[3,4,13,105,107,118,129],[4,14,114,117,118,122],[3,118,128,133],[10,11,13,107,110,117,122,126],[3,104,107,128,129,135],[3,117,121,128,134,135]]),
([v14,v0,v1,v2,v3,v78,v252],[0,14,16,131,149,150,180,228,271,389,409,506,532,547,567,612,617,642,645,648],[1,2,3,4,5,6,7,8,9,11,14,15,20,22,23,26,28,29,32,35,36,39,41,45,48,50,57,59,60,65,67,71,78,79,82,87],[[2,4,5,7,8,105,111],[6,8,15,104],[1,3,7,110,114],[11,13,16,101,109],[10,14,16,117,121],[0,12,15,16,127,129],[7,8,9,103,105,111,124],[7,105,110,111,114],[9,100,101,105,112,119],[9,105,116,117,119,123],[9,105,127,129,134],[7,110,113,114,124],[8,16,101,109,124],[8,117,121,124,130],[8,124,125,127,129,130],[7,101,102,108,109,110,118],[7,110,115,117,118,121],[7,110,127,131,135],[17,18,19,101,106,117,121,122],[15,16,101,107,126,127,128,132],[15,16,117,120,127,132,133]]),
([v44,v0,v1,v2,v5,v3,v78,v252],[53,92,94,150,151,163,201,245,271,331,380,436,475,476,506,513,538,541,567,579,612,615,617,627,628],[0,2,3,5,6,7,8,11,14,15,20,23,26,27,28,29,30,32,33,34,35,36,39,45,47,59,63,65,66,71,78,79,81,87,88,92],[[9,10,109,120],[5,8,15,103],[3,6,108,117],[14,15,20,24],[4,8,107],[11,13,15,19,115,122],[0,2,15,16,125,127],[8,109,118,119,120,135],[6,10,108,109],[6,104],[10,101,109,110,120],[10,109,114,115,120,123],[2,10,109,125,127,134],[6,108,116,117,119,132],[7,8,22,23,119],[8,15,100,101,119],[8,19,113,115,119,122],[2,8,119,125,127,132],[6,10,111],[6,101,102,108,110,117],[6,108,112,115,117,122],[2,6,108,125,129,133],[14,15,101,124],[12,13,18,19,115,123],[1,2,17,21,125,127],[13,15,101,105,115,122,124],[2,15,101,106,125,126,128,130],[2,13,19,115,121,125,130,131]]),
([v44,v0,v1,v2,v3,v78,v252,v284],[0,12,26,92,196,201,202,245,287,331,380,463,475,481,506,509,532,541,567,574,617,621,632],[0,2,3,5,6,7,8,11,14,18,20,23,26,27,29,32,34,36,39,44,45,47,59,61,65,66,73,78,79,80,81,82,84,88,92],[[9,10,123,131],[2,8,15,103],[4,6,15,21,108,111],[1,8,107],[11,13,15,19,114,118],[0,3,122,127],[14,15,16,17],[8,116,123,129,131,134],[6,10,108,111,123,133],[10,101,110,123,131],[10,114,120,123,131],[3,10,119,122,123],[3,104],[6,8,108,111,116,130],[8,15,100,101,116],[8,19,113,114,116,118],[3,116,122,127,130],[7,8,17,20,116],[6,15,101,102,108,109,110,115],[6,13,19,108,112,114,115,118],[3,108,122,126,132],[5,6,17,22,108,111],[13,15,101,105,114,118,121],[3,101,106,122,125,127],[14,15,101,110],[3,114,117,122,127,128],[12,13,17,18,114,120],[3,10,124]]),
([v44,v0,v1,v2,v3,v78,v252,v290],[0,12,26,92,150,201,245,282,364,380,381,446,475,478,506,507,532,541,567,568,612,617,628],[0,1,2,5,6,7,11,14,15,20,25,27,28,29,34,35,36,39,45,47,56,59,61,66,71,73,79,81,84,87,89,91,92],[[8,10,15,20,104,108],[2,7,15,103],[4,5,125,129],[1,7,106],[11,13,15,19,113,117],[0,3,124,128],[14,15,16,17],[7,104,108,114,132],[5,104,108,125,129],[10,15,101,102,104,109,115],[10,13,19,104,112,113,115,118],[3,104,122,124,128],[9,10,17,22,104,108],[5,114,125,127,131],[7,15,100,102,114],[7,19,111,113,114,117],[3,114,124,127,130],[6,7,17,21,114],[5,102,109,125,129],[5,113,117,125,129],[3,5,120,124,125],[3,107],[13,15,102,105,113,117,119],[3,102,110,123,124,128],[14,15,102,109],[3,113,116,124,126,128],[12,13,17,18,113,117],[3,5,121]]),
([v17,v0,v1,v2,v3,v78,v252],[0,12,16,36,92,149,150,169,260,298,311,380,409,418,531,532,547,567,617,621],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,35,36,39,41,44,45,56,57,58,59,60,61,65,71,73,78,79,92],[[2,5,8,9,11,104,111],[8,16,103],[6,7,18,19,110,113],[1,4,8,10,11,101,108],[12,13,17,116,120],[0,3,15,16,127,130],[8,11,104,111,135],[7,11,104,109,110,111,113],[8,11,100,101,104,112,118],[11,104,115,116,118,123],[3,11,104,122,126,127,129,130],[7,8,110,113,135],[8,16,101,108,135],[8,17,116,120,135],[3,8,127,130,135],[7,14,16,101,102,107,108,110,117],[7,13,17,110,114,116,117,120],[3,7,16,110,124,127,131,132],[13,14,16,101,105,116,120,121],[3,14,16,101,106,125,127,128,133],[3,13,16,116,119,127,133,134]]),
([v25,v0,v1,v2,v3,v78,v252],[0,12,14,24,92,131,150,163,201,257,331,344,409,411,526,532,547,567,612,617],[0,1,2,3,5,6,7,8,11,13,14,15,20,23,26,28,29,32,35,36,39,44,45,47,56,58,59,61,63,65,66,71,73,78,79,81],[[10,11,18,19,105,111],[7,9,16,104],[2,5,8,110,113],[1,4,6,8,9,102,108],[12,13,17,116,120],[0,3,15,16,126,129],[9,11,105,111,135],[8,105,109,110,111,113],[11,14,16,101,102,105,112,118],[11,13,17,105,115,116,118,122],[3,11,16,105,121,125,126,127,129],[8,110,113,135],[8,9,16,100,102,108,135],[9,17,116,120,135],[3,9,126,129,135],[8,102,103,108,110,117],[8,110,114,116,117,120],[3,8,110,124,126,131,132],[13,14,16,102,106,116,120,123],[3,14,16,102,107,126,128,130,133],[3,13,16,116,119,126,133,134]]),
([v291,v0,v1,v2,v5,v3,v78,v252],[53,116,118,150,161,195,234,245,271,331,402,409,436,513,521,538,544,553,559,567,579,600,612,628],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,45,47,57,59,60,65,67,71,78,79,84,87,88],[[9,10,111,137],[5,8,12,120],[3,6,110,136],[19,20,22,23],[13,17,20,101,124],[4,8,123],[0,2,15,20,128,135],[8,103,111,114,121],[6,10,110,111],[6,104],[10,101,108,111,112,121],[10,111,117,118,121,125],[2,10,111,128,130,137],[6,103,110,114,119],[7,8,103,131],[8,20,100,101,103,109],[8,12,103,116,118],[2,8,103,128,130,131],[6,10,113],[6,101,102,107,109,110,119],[6,110,115,118,119,125],[2,6,110,128,132,136],[14,18,20,101,126],[11,12,118,125],[1,2,16,21,128,130],[12,101,105,118,124,125],[2,20,101,106,127,128,129,133],[2,12,118,122,128,133,134]]),
([v292,v0,v1,v2,v3,v78,v252],[0,16,66,149,150,199,287,401,409,465,506,532,547,566,567,593,617,621,627],[1,2,3,4,5,6,7,8,9,11,14,15,20,22,23,24,26,28,29,32,35,36,39,41,44,45,48,57,59,60,61,65,73,78,79,84],[[0,1,3,6,105,111,130],[2,6,11,104],[4,5,16,17,110,114],[10,12,13,16,101,109],[8,9,14,15,118,122],[0,3,128,131],[3,6,7,103,105,115,130],[5,7,105,110,114,120],[7,100,101,105,112,120],[7,105,117,118,120,125],[3,105,124,128,130,131],[5,6,110,113,114,115,126],[6,16,101,109,115],[6,115,118,122,126],[3,115,128,131],[5,13,18,101,102,108,109,110,119],[5,9,15,110,116,118,119,122],[3,110,128,132,135],[9,13,15,101,106,118,122,123],[3,101,107,127,128,129,133],[3,118,121,128,133,134]]),
([v293,v0,v1,v2,v3,v78,v252],[0,14,40,131,233,282,331,367,409,447,506,532,547,561,567,593,612,617,633],[0,1,2,3,4,5,6,7,8,11,14,15,20,22,23,24,26,28,29,32,35,36,39,41,45,48,51,56,59,60,61,64,65,71,73,78,79],[[6,7,16,17,106,111],[2,5,11,115],[0,1,3,4,110,114,134],[10,12,13,17,102,109],[8,9,14,15,118,126],[0,3,128,132,133],[5,104,105,106,111,125],[4,106,111,114,119],[7,13,18,101,102,106,112,120],[7,9,15,106,117,118,120,124],[3,106,130,132,135],[3,4,105,113,114,134],[5,17,100,102,105,109],[5,105,118,122,125],[3,105,131,132,133],[4,102,103,109,114,119],[4,114,116,118,119,122],[3,114,127,132,133,134],[9,13,15,102,107,118,122,123],[3,102,108,129,132,135],[3,118,121,132,135,136]]),
([v294,v0,v1,v2,v3,v78,v252],[0,12,26,92,150,177,263,331,352,409,424,524,532,547,567,612,617,621,627],[0,1,2,3,5,6,7,8,11,13,14,15,18,20,23,26,27,28,29,32,34,35,36,39,44,45,47,56,58,59,60,61,65,71,73,78,79],[[7,8,15,16,105,111],[2,6,12,104],[4,5,16,17,110,114],[0,1,3,6,102,108,130],[9,10,14,118,123],[0,3,129,132],[6,8,105,111,120],[5,8,18,105,109,110,111,114],[8,11,13,101,102,105,113,121],[8,10,14,105,117,118,121,125],[3,105,124,128,129,131,132],[5,6,110,114,120],[3,6,13,100,102,120,130],[6,14,116,118,120,123],[3,120,129,132],[5,11,13,102,103,110,112,113,119],[5,10,14,110,115,118,119,123],[3,110,127,129,133,134],[10,11,13,102,106,118,123,126],[3,102,107,129,130,135],[3,118,122,129,135,136]]),
([v19,v0,v1,v2,v3,v78,v252],[0,15,16,132,133,150,180,216,307,353,409,506,532,547,567,612,641,644,647],[0,2,3,4,5,6,7,8,9,11,13,14,20,23,24,26,27,29,32,34,36,38,39,41,42,44,45,57,58,59,60,61,65,71,78,79,81,87],[[6,9,15,105],[2,4,5,7,8,104,114],[1,3,7,111,113],[11,13,15,101,112],[10,14,15,117,126],[0,12,15,129,132],[7,8,103,104,114,124],[7,110,111,113,124],[9,15,101,112,124],[9,117,121,124,126,131],[9,124,125,128,129,131,132],[7,104,111,113,114],[8,100,101,104,109,119],[8,104,116,117,119,122],[8,104,129,132,136],[7,101,102,108,109,111,118],[7,111,115,117,118,122],[7,111,129,133,137],[16,17,18,101,106,117,122,123],[15,101,107,127,129,130,134],[15,117,120,129,134,135]]),
([v38,v0,v1,v2,v7,v3,v78,v252],[40,100,101,150,153,166,207,245,298,331,353,426,484,485,506,510,537,542,567,577,612,617,619,623,633],[1,2,3,5,6,7,8,11,14,20,23,24,26,27,28,29,31,32,33,34,35,36,39,41,45,57,59,60,65,71,78,79,82,88,91,92],[[5,10,15,104],[7,8,111,119],[3,6,110,117],[14,15,21,24],[4,10,109],[11,13,15,19,115,124],[0,2,15,16,126,128],[8,111,118,119,120,133],[6,110,116,117,120,132],[9,10,20,23,120],[10,15,100,101,120],[10,19,114,115,120,124],[2,10,120,126,128,132],[6,8,110,111],[6,103],[8,101,107,111,119],[8,111,113,115,119,122],[2,8,111,126,128,135],[6,8,108],[6,101,102,107,110,117],[6,110,112,115,117,122],[2,6,110,126,129,134],[14,15,101,123],[12,13,18,19,115,122],[1,2,17,22,126,128],[13,15,101,105,115,122,123],[2,15,101,106,125,126,127,130],[2,13,19,115,121,126,130,131]]),
([v38,v0,v1,v2,v3,v78,v252,v285],[0,13,32,100,191,207,208,245,298,331,369,460,484,490,506,508,532,542,567,571,612,621,637],[1,2,3,5,6,7,8,9,11,14,20,23,26,28,29,32,35,36,39,41,45,50,59,60,65,67,73,78,79,80,81,82,88,89,92],[[2,10,15,104],[7,8,125,130],[4,6,15,21,109,111],[1,10,110],[11,13,15,19,114,120],[0,3,124,127],[14,15,16,17],[8,116,125,129,130,132],[6,10,109,111,116,131],[10,15,100,101,116],[10,19,113,114,116,120],[3,116,124,127,131],[9,10,17,20,116],[6,8,109,111,125,134],[8,101,108,125,130],[8,114,118,125,130],[3,8,121,124,125],[3,103],[6,15,101,102,107,108,109,115],[6,13,19,109,112,114,115,118],[3,109,124,126,133],[5,6,17,22,109,111],[13,15,101,105,114,118,119],[3,101,106,123,124,127],[14,15,101,108],[3,114,117,124,127,128],[12,13,17,18,114,118],[3,8,122]]),
([v38,v0,v1,v2,v3,v78,v252,v290],[0,13,32,100,150,207,282,298,299,331,364,446,484,487,506,507,532,542,567,568,612,617,633],[0,1,2,5,6,7,11,14,17,20,24,27,28,29,34,35,36,39,41,45,56,59,60,67,71,73,79,82,84,87,88,89,91],[[2,10,15,104],[6,8,15,21,103,110],[4,5,125,129],[1,10,109],[11,13,15,19,113,119],[0,3,124,128],[14,15,16,17],[8,10,103,110,115,130],[5,115,125,127,129],[10,15,101,102,115],[10,19,112,113,115,119],[3,115,124,127,128],[9,10,17,20,115],[5,103,110,125,132],[8,15,100,102,103,106,114],[8,13,19,103,111,113,114,117],[3,103,123,124,131],[7,8,17,22,103,110],[5,102,106,125,129],[5,113,117,125,129],[3,5,120,124,125],[3,107],[13,15,102,105,113,117,118],[3,102,108,122,124,128],[14,15,102,106],[3,113,116,124,126,128],[12,13,17,18,113,117],[3,5,121]]),
([v22,v0,v1,v2,v3,v78,v252],[0,13,16,31,100,133,150,165,245,260,298,345,409,415,528,532,547,567,612,621],[0,2,3,5,6,7,8,9,10,11,14,20,23,24,26,27,29,32,34,36,39,41,45,50,56,57,59,60,65,67,71,73,78,79,88],[[9,11,16,104],[2,5,10,103,113],[6,7,18,19,110,112],[1,4,8,10,11,101,111],[12,13,17,116,122],[0,3,15,16,126,128],[10,103,113,134],[7,11,110,112,134],[10,11,16,101,108,111,134],[11,17,116,122,134],[3,11,126,128,134],[7,10,103,110,112,113],[10,100,101,103,109,118],[10,103,115,116,118,120],[3,10,103,123,126,128,129],[7,14,16,101,102,107,109,110,117],[7,13,17,110,114,116,117,120],[3,7,16,110,124,126,130,131],[13,14,16,101,105,116,120,121],[3,14,16,101,106,125,126,127,132],[3,13,16,116,119,126,132,133]]),
([v24,v0,v1,v2,v3,v78,v252],[0,13,15,25,100,132,150,166,207,245,259,342,409,412,527,532,547,567,612,617],[0,1,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,36,39,41,45,50,56,57,59,60,65,67,71,73,78,79,82],[[7,11,16,105],[9,10,18,19,104,113],[2,5,8,110,112],[1,4,6,8,11,102,111],[12,13,17,116,122],[0,3,15,16,126,128],[10,11,104,113,134],[8,110,112,134],[8,11,16,101,102,111,134],[11,17,116,122,134],[3,11,126,128,134],[8,104,110,112,113],[10,14,16,100,102,104,109,118],[10,13,17,104,115,116,118,120],[3,10,16,104,123,126,128,129],[8,102,103,108,109,110,117],[8,110,114,116,117,120],[3,8,110,124,126,130,131],[13,14,16,102,106,116,120,121],[3,14,16,102,107,125,126,127,132],[3,13,16,116,119,126,132,133]]),
([v88,v0,v1,v2,v7,v3,v78,v252],[40,124,125,150,162,200,238,245,324,331,353,409,426,510,522,537,545,551,560,567,577,597,617,633],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,45,47,57,58,59,60,61,65,71,78,79,89,91,92],[[5,10,12,119],[7,8,112,136],[3,6,111,135],[19,20,22,23],[13,17,20,101,124],[4,10,123],[0,2,15,20,127,134],[8,104,109,112,118],[6,104,109,111,117],[9,10,104,129],[10,20,100,101,104,110],[10,12,104,115,116],[2,10,104,126,127,129,130],[6,8,111,112],[6,103],[8,101,107,112,118],[8,112,114,116,118,121],[2,8,112,127,130,136],[6,8,108],[6,101,102,107,111,117],[6,111,113,116,117,121],[2,6,111,127,131,135],[14,18,20,101,122],[11,12,116,121],[1,2,16,21,127,130],[12,101,105,116,121,122],[2,20,101,106,125,127,128,132],[2,12,116,120,127,132,133]]),
([v295,v0,v1,v2,v3,v78,v252],[0,16,66,133,150,194,323,369,409,462,506,532,547,563,567,593,612,621,623],[0,2,3,4,5,6,7,8,9,10,11,13,14,15,20,23,24,26,27,29,32,34,36,38,39,41,42,45,50,57,58,59,60,65,67,73,78,79,84],[[2,7,11,105],[0,1,3,6,104,116,134],[4,5,16,17,112,115],[10,12,13,16,101,114],[8,9,14,15,119,127],[0,3,131,133],[3,6,103,104,113,134],[5,7,111,112,113,115,126],[7,16,101,109,113,114],[7,113,119,123,126,127],[3,113,130,131,133],[5,6,104,112,115,121],[6,100,101,104,110,121],[6,104,118,119,121,124],[3,104,128,131,133,134],[5,13,18,101,102,108,110,112,120],[5,9,15,112,117,119,120,124],[3,112,131,135,138],[9,13,15,101,106,119,124,125],[3,101,107,129,131,132,136],[3,119,122,131,136,137]]),
([v296,v0,v1,v2,v3,v78,v252],[0,15,53,132,237,245,285,364,409,448,506,532,547,562,567,593,612,617,628],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,29,32,34,36,38,39,41,42,45,51,56,57,58,59,60,65,67,71,73,78,79],[[2,7,11,113],[5,6,16,17,105,116],[0,1,3,4,112,115,137],[10,12,13,16,102,114],[8,9,14,15,119,128],[0,3,132,134,136],[6,7,104,105,106,116,126],[3,4,106,111,112,137],[7,16,101,102,106,114],[7,106,119,123,126,127],[3,106,131,132,136],[4,105,112,116,120],[6,13,18,100,102,105,110,121],[6,9,15,105,118,119,121,124],[3,105,132,135,138],[4,102,103,109,110,112,120],[4,112,117,119,120,124],[3,112,129,132,136,137],[9,13,15,102,107,119,124,125],[3,102,108,130,132,133,138],[3,119,122,132,138,139]]),
([v297,v0,v1,v2,v3,v78,v252],[0,13,32,100,150,178,245,269,348,409,425,525,532,547,567,612,617,621,623],[0,1,2,3,5,6,7,8,9,11,14,20,23,24,26,27,28,29,32,34,35,36,39,41,45,50,56,57,59,60,65,66,67,71,73,78,79],[[2,8,12,105],[6,7,15,16,104,113],[4,5,15,17,110,112],[0,1,3,8,102,111,131],[9,10,14,117,124],[0,3,128,130],[7,8,104,113,120],[5,8,110,112,120],[3,8,13,101,102,120,131],[8,14,116,117,120,124],[3,120,128,130],[5,7,18,104,110,112,113],[7,11,13,100,102,104,109,119],[7,10,14,104,115,117,119,122],[3,104,125,128,130,132],[5,11,13,102,103,108,109,110,118],[5,10,14,110,114,117,118,122],[3,110,126,128,133,134],[10,11,13,102,106,117,122,123],[3,102,107,127,128,129,135],[3,117,121,128,135,136]]),
([v0,v298,v1,v2,v3,v78,v252],[0,39,124,146,150,244,245,330,405,505,506,532,547,550,567,612,617,621,623],[0,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,35,36,39,41,42,45,57,59,60,65,67,71,73,78,79,90],[[2,8,11,104],[7,8,103,112,118,122],[5,8,109,111,118,122],[8,101,110,118,122],[1,8,9,115,118,133],[1,118,125,127],[6,7,15,16,103,112],[4,5,15,17,109,111],[10,12,13,14,101,110],[0,1,3,8,115,123,133],[0,1,125,127],[5,7,18,103,109,111,112],[7,13,14,100,101,103,108,117],[7,9,103,114,115,117,120],[1,103,125,127,128],[5,13,14,101,102,107,108,109,116],[5,9,109,113,115,116,120],[1,109,125,129,130],[9,101,105,115,120,121],[1,101,106,124,125,126,131],[1,115,119,125,131,132]]),
([v0,v299,v1,v2,v3,v78,v252],[0,15,32,87,132,142,150,166,207,245,295,374,409,474,506,532,567,584,612,617],[0,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,29,32,34,36,38,39,41,42,44,45,50,51,57,58,59,60,61,65,67,71,78,79,87,91],[[8,11,14,112],[10,11,103,104,105,115,125],[7,105,110,111,141],[7,11,14,101,105,113],[11,105,118,122,125,127],[3,11,105,126,131,132,134,135],[9,10,18,19,104,115],[1,4,7,111,114,141],[2,5,6,7,11,101,113],[12,13,16,17,118,129],[0,3,15,18,132,137],[7,104,111,115,119],[10,14,100,101,104,109,120],[10,13,17,104,117,118,120,123],[3,10,18,104,128,132,135,136],[7,101,102,108,109,111,119],[7,111,116,118,119,123],[3,7,111,132,137,140],[13,14,101,106,118,123,124],[3,14,101,107,130,132,133,138],[3,13,17,118,121,132,138,139]]),
([v0,v300,v1,v2,v3,v78,v252],[0,15,39,113,132,146,150,200,238,245,321,398,498,506,532,547,567,607,612,617],[0,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,36,39,41,42,44,45,50,51,57,59,60,65,67,71,73,78,79,82],[[8,11,16,104],[10,11,103,112,121,135],[7,109,111,121],[11,101,110,121,135],[7,11,12,115,121,125],[3,11,121,122,127,129,135],[9,10,18,19,103,112],[1,4,7,109,111],[13,15,16,101,110],[2,5,6,7,11,115,123,125],[0,3,14,17,127,129],[7,103,109,111,112],[10,16,100,101,103,108,117],[10,12,103,114,115,117,119],[3,10,17,103,124,127,129,130],[7,101,102,107,108,109,116],[7,109,113,115,116,119],[3,7,109,127,131,132],[12,101,105,115,119,120],[3,16,101,106,126,127,128,133],[3,12,115,118,127,133,134]]),
([v0,v301,v1,v2,v3,v78,v252],[0,16,32,97,133,142,150,204,245,260,298,380,409,483,506,532,567,585,612,621],[0,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,29,32,34,36,38,39,41,42,44,45,56,57,58,59,60,61,65,71,73,78,79,81,92],[[10,11,14,105],[9,103,104,112,140],[7,11,110,111,112,114,125],[9,11,14,101,112,113],[11,112,118,122,125,127],[3,11,112,126,130,131,133,134],[1,4,9,104,115,140],[6,7,18,19,111,114],[2,5,8,9,11,101,113],[12,13,16,17,118,127],[0,3,15,18,131,134],[7,9,104,111,114,120],[9,100,101,104,109,120],[9,104,117,118,120,123],[3,9,104,131,134,139],[7,14,101,102,108,109,111,119],[7,13,17,111,116,118,119,123],[3,7,18,111,128,131,135,136],[13,14,101,106,118,123,124],[3,14,101,107,129,131,132,137],[3,13,17,118,121,131,137,138]]),
([v0,v302,v1,v2,v3,v78,v252],[0,16,39,121,133,146,150,235,245,291,324,402,499,506,532,547,567,608,612,621],[0,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,36,39,41,42,44,45,56,57,59,60,65,67,71,73,78,79,88],[[10,11,16,104],[9,103,112,121],[7,11,109,111,121,134],[11,101,110,121,134],[9,11,12,115,121,123],[3,11,121,122,126,128,134],[1,4,9,103,112],[6,7,18,19,109,111],[13,15,16,101,110],[2,5,8,9,11,115,123],[0,3,14,17,126,128],[7,9,103,109,111,112],[9,100,101,103,108,117],[9,103,114,115,117,119],[3,9,103,126,128,129],[7,16,101,102,107,108,109,116],[7,12,109,113,115,116,119],[3,7,17,109,124,126,130,131],[12,101,105,115,119,120],[3,16,101,106,125,126,127,132],[3,12,115,118,126,132,133]]),
([v0,v1,v303,v2,v3,v78,v252],[0,38,116,145,150,243,327,331,408,504,506,532,547,549,567,612,617,621,627],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,34,35,36,39,41,45,48,57,58,59,60,61,65,71,73,78,79,85],[[6,104,111,118,124],[7,8,15,16,104,111],[5,8,18,104,109,110,111,113],[8,13,14,100,101,104,112,119],[8,9,104,115,116,119,123],[1,104,126,127,129,130],[2,6,11,103],[5,6,110,113,118,124],[6,101,108,118,124],[1,6,9,116,118,135],[1,118,127,130],[4,5,16,17,110,113],[10,12,13,14,101,108],[0,1,3,6,116,121,135],[0,1,127,130],[5,13,14,101,102,107,108,110,117],[5,9,110,114,116,117,123],[1,110,127,131,132],[9,101,105,116,122,123],[1,101,106,125,127,128,133],[1,116,120,127,133,134]]),
([v0,v1,v76,v2,v3,v78,v252],[0,14,26,86,131,140,150,163,201,292,331,377,409,471,506,532,567,583,612,617],[1,2,3,4,5,6,7,8,9,11,14,15,20,22,23,24,26,28,29,32,35,36,39,44,45,47,48,50,51,58,59,61,63,65,66,67,71,78,79,87],[[9,103,104,105,111,126],[10,11,18,19,105,111],[7,105,111,114,119],[11,14,100,101,105,112,120],[11,13,17,105,117,118,120,124],[3,11,19,105,123,129,130,131,133],[8,9,14,115],[7,104,113,114,139],[7,9,14,101,104,109],[9,104,118,122,126],[3,9,104,127,130,133,135],[1,4,7,110,114,139],[2,5,6,7,9,101,109],[12,13,16,17,118,128],[0,3,15,19,130,136],[7,101,102,108,109,114,119],[7,114,116,118,119,122],[3,7,114,130,136,139],[13,14,101,106,118,122,125],[3,14,101,107,130,132,134,137],[3,13,17,118,121,130,137,138]]),
([v0,v1,v304,v2,v3,v78,v252],[0,14,38,112,131,145,150,195,234,320,331,399,497,506,532,547,567,606,612,617],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,35,36,39,41,44,45,48,50,51,57,58,59,60,61,65,71,73,78,79,81],[[9,104,111,124,137],[10,11,18,19,104,111],[7,104,109,110,111,113],[11,16,100,101,104,112,118],[11,12,104,115,116,118,123],[3,11,17,104,122,128,129,131,132],[8,9,16,103],[7,110,113,124],[9,101,108,124,137],[7,9,12,116,124,126],[3,9,124,125,129,132,137],[1,4,7,110,113],[13,15,16,101,108],[2,5,6,7,9,116,120,126],[0,3,14,17,129,132],[7,101,102,107,108,110,117],[7,110,114,116,117,123],[3,7,110,129,133,134],[12,101,105,116,121,123],[3,16,101,106,127,129,130,135],[3,12,116,119,129,135,136]]),
([v0,v1,v305,v2,v3,v78,v252],[0,16,26,104,140,149,150,210,247,260,298,345,409,492,506,532,567,588,617,621],[1,2,3,4,5,6,7,8,9,11,14,15,20,22,23,24,26,28,29,32,35,36,39,41,45,48,50,56,57,59,60,65,67,71,73,78,79,82,88],[[10,11,103,105,115,138],[1,5,9,10,11,105,111,138],[7,11,105,110,114,120],[10,11,100,101,105,112,120],[11,105,117,118,120,124],[3,11,105,129,131,137],[10,14,104],[7,10,110,113,114,115,125],[10,14,101,109,115],[10,115,118,122,125],[3,10,115,126,129,131,132],[6,7,18,19,110,114],[2,4,8,10,11,101,109],[12,13,16,17,118,122],[0,3,15,18,129,131],[7,14,101,102,108,109,110,119],[7,13,17,110,116,118,119,122],[3,7,18,110,127,129,133,134],[13,14,101,106,118,122,123],[3,14,101,107,128,129,130,135],[3,13,17,118,121,129,135,136]]),
([v0,v1,v306,v2,v3,v78,v252],[0,16,38,128,145,149,150,239,256,291,324,373,503,506,532,547,567,611,617,621],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,35,36,39,41,45,48,50,56,57,58,59,60,61,65,71,73,78,79,92],[[10,11,104,111,123],[1,5,9,10,11,104,111],[7,11,104,109,110,111,113],[11,100,101,104,112,118],[10,11,104,115,116,118,122],[3,11,104,127,128,130,131],[10,16,103],[7,10,110,113,123,136],[10,101,108,123,136],[10,12,116,120,123],[3,10,123,124,128,131,136],[6,7,18,19,110,113],[13,15,16,101,108],[2,4,8,10,11,116,120],[0,3,14,17,128,131],[7,16,101,102,107,108,110,117],[7,12,110,114,116,117,120],[3,7,17,110,125,128,132,133],[12,101,105,116,120,121],[3,16,101,106,126,128,129,134],[3,12,116,119,128,134,135]]),
([v0,v1,v53,v4,v2,v3,v78,v252],[66,69,180,184,245,247,298,311,333,449,450,506,516,539,581,612,623],[2,5,6,14,23,26,27,28,29,32,34,35,36,39,45,51,53,54,55,56,59,65,69,71,72,73,78,79,81,82,88,92],[[5,8,101,102],[4,5,7,8,102,111],[5,130],[3,8,102,103,104,111],[5,8,102,111,116],[8,102,107,108,111,114],[1,8,102,120,121,129],[4,5,101,110],[5,8,131],[3,5,101,103,104,110],[5,101,110,116],[5,101,106,108,110,113],[1,5,101,120,121,128],[7,12],[2,3,12,16,103,109],[6,12,100],[9,10,12,14,108,113],[0,1,12,13,120,123],[3,15,16,103,117],[11,12,15,116],[10,14,108,115],[1,15,120,123],[3,12,103,109,116],[3,10,14,103,105,108,109,113],[1,3,15,103,119,120,123,125],[10,12,108,113,116,124],[1,12,116,118,120,122,124,126],[1,10,14,108,112,120,126,127]]),
([v0,v1,v307,v4,v2,v3,v78,v252],[66,72,180,186,245,256,309,324,341,449,516,539,555,567,581,603,612,623],[0,1,2,3,5,6,8,9,11,14,15,20,23,24,29,32,34,35,41,51,53,54,56,57,59,60,65,71,73,78,81,82],[[5,8,104,105],[4,5,6,8,105,117],[5,110],[3,8,105,109,112,117],[8,101,102,105,111,117],[5,8,105,117,119],[1,8,105,124,126,131],[4,5,104,116],[5,8,113],[3,5,104,109,112,116],[5,100,102,104,108,116],[5,104,116,119],[1,5,104,124,126,130],[6,9],[2,3,14,17,109,115],[10,12,14,102,118],[7,9,14,114],[0,1,11,14,124,129],[3,16,17,109,121],[13,14,102,120],[9,13,14,119],[1,15,124,127],[3,14,102,103,107,108,109,115],[3,9,109,115,119],[1,3,15,109,122,124,127,128],[9,14,102,118,119],[1,14,102,106,123,124,125,129],[1,9,14,119,124,129]]),
([v0,v1,v4,v2,v81,v3,v78,v252],[1,66,67,155,180,181,245,249,306,315,331,334,409,449,506,516,533,539,567,581,603,612,613,617,624,632,641,643],[0,1,2,3,5,6,7,8,9,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,54,56,57,59,60,65,71,72,73,78,79,81,82,85,90],[[7,11,104,105],[7,111],[5,11,105,110,113,121],[10,11,15,21,105],[11,101,102,105,112,121],[11,105,117,118,121,139],[2,11,105,128,130,137],[7,11,114],[5,7,104,110,113,120],[6,7,15,23,104],[7,100,102,104,109,120],[7,104,116,118,120,138],[2,7,104,128,130,136],[3,5,22,24,26,27,110,125],[14,15,21,26],[14,15,102,132],[12,13,18,19,118],[0,2,16,20,128,131],[4,5,15,25,110,125],[5,15,102,103,108,109,110,119],[5,13,110,115,118,119,135],[2,5,20,110,126,128,131,133],[8,13,124],[9,13,15,123],[1,2,15,17,128],[13,15,102,106,118],[2,15,102,107,127,128,129,134],[2,13,118,122,128,134,135]]),
([v0,v1,v4,v2,v3,v9,v78,v252],[17,66,74,150,180,216,228,245,257,331,342,410,449,452,506,516,534,539,547,555,567,581,612,623],[2,3,5,6,11,14,15,16,17,20,23,24,27,28,29,32,34,35,36,39,45,51,53,54,56,59,65,69,71,72,73,78,79,81,82],[[8,10,102,103],[5,8,106],[4,103,105,110,117],[10,103,104,109,117],[9,10,103,134],[10,103,113,114,117,120],[2,10,103,125,126,134],[6,8,10,111],[4,102,105,110,116],[8,102,104,109,116],[7,8,102,133],[8,102,112,114,116,119],[2,8,102,125,126,133],[3,4,105,123],[14,15,18,19,104,122],[18,19,22,23],[11,13,20,21,114,121],[0,2,16,19,125,128],[4,15,101,104,105],[4,15,115],[4,105,114,119,123],[2,4,105,124,125,128,130],[4,100],[13,15,19,104,107,114,119,122],[2,15,19,104,108,125,127,129,131],[12,13,19,21,114,132],[1,2,17,19,125,131],[2,13,19,114,118,125,131,132]]),
([v0,v1,v4,v2,v3,v78,v252,v290],[0,66,133,149,150,180,245,282,331,364,446,449,456,507,516,532,539,547,555,568,581,603,612],[0,1,2,5,6,7,11,14,15,17,20,24,27,28,29,34,35,36,39,41,45,51,53,56,59,60,71,73,79,81,82,84,87,89,91],[[7,9,103,104],[2,7,108],[5,104,116,127,132],[9,101,102,104,110,116],[9,104,113,114,116,120],[1,104,126,130,131],[8,9,104,116],[3,7,9,111],[5,103,115,127,134],[7,100,102,103,106,115],[7,103,112,114,115,118],[1,103,126,129,133],[6,7,103,115],[4,5,127,132],[13,17,18,22,102,122],[10,12,19,21,114,121],[0,1,126,131],[15,16,22],[5,102,106,127,132],[5,114,118,127,132],[1,5,123,126,127],[1,107],[12,18,21,102,105,114,118,119],[1,102,109,125,126,131],[14,16,18,102,106],[1,114,117,126,128,131],[11,12,16,20,114,118],[1,5,124]]),
([v0,v1,v4,v2,v3,v78,v252,v308],[0,66,133,149,170,180,187,245,263,331,348,419,449,454,506,516,532,539,547,555,567,581,612,621,632],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,39,45,51,54,56,59,60,65,66,71,72,73,78,79,81,82,93],[[8,10,101,102],[2,8,105],[6,10,102,104,106,114],[10,102,114,121,123],[10,102,110,111,114,116],[1,102,120,122,130],[9,10,102,114],[3,8,10,107],[6,8,101,104,106,113],[8,101,113,121,123],[8,101,109,111,113,115],[1,101,120,122,129],[7,8,101,113],[4,6,22,23,104,118],[14,15,18,19,121,125],[11,13,20,21,111,117],[0,1,120,124],[16,17,22],[6,15,19,104,112,121,125],[6,13,21,104,108,111,112,115],[1,104,119,120,124,126],[5,6,17,24,104,112],[13,15,19,111,115,121,131],[1,15,103,120,121],[1,100],[1,13,111,120,128],[12,13,17,21,111,115],[1,15,127]]),
([v0,v1,v2,v309,v3,v78,v252],[0,37,107,144,241,245,329,331,407,502,506,532,547,548,567,612,617,621,632],[0,1,2,4,5,6,8,11,14,15,16,20,24,27,28,29,32,34,35,36,39,41,51,54,57,58,59,60,61,65,67,71,79,84],[[6,8,18,103,104,105,109,112],[4,105,109,116,123],[7,8,15,17,105,109],[8,13,14,101,102,105,111,118],[8,9,105,114,115,118,122],[1,105,125,126,128,129],[4,104,112,116,123],[5,6,16,17,104,112],[6,13,14,100,102,104,107,117],[6,9,104,113,115,117,122],[1,104,126,129,130],[2,4,11,108],[4,102,107,116,123],[1,4,9,115,116,132],[1,116,126,131],[10,12,13,14,102,107],[0,1,3,4,115,120,132],[0,1,126,131],[9,102,110,115,121,122],[1,102,106,124,126,127,133],[1,115,119,126,132,133]]),
([v0,v1,v2,v72,v3,v78,v252],[0,14,17,96,138,147,151,163,201,257,331,383,409,480,506,532,567,586,612,621],[0,1,2,5,6,7,8,11,13,14,15,20,22,23,24,27,28,29,34,35,36,39,44,45,47,54,56,58,59,61,63,65,66,71,73,78,79,81],[[9,104,110,114,118],[8,104,108,109,110,125],[10,11,18,19,104,110],[11,14,101,102,104,111,119],[11,13,17,104,116,117,119,123],[3,11,19,104,122,127,128,129,131],[8,9,109,112,114,137],[1,5,7,8,9,103,114,137],[8,9,100,102,107,114,118],[9,114,115,117,118,121],[3,9,114,128,131,137],[8,14,113],[8,14,102,107,109],[8,109,117,121,125],[3,8,109,126,128,133,134],[2,4,6,8,9,102,107],[12,13,16,17,117,123],[0,3,15,19,128,131],[13,14,102,105,117,121,124],[3,14,102,106,128,130,132,135],[3,13,17,117,120,128,135,136]]),
([v0,v1,v2,v310,v3,v78,v252],[0,14,37,120,144,147,161,195,234,286,331,403,500,506,532,547,567,609,612,621],[0,1,2,4,5,6,7,8,11,14,15,20,24,27,28,29,34,35,36,39,41,44,45,51,54,56,57,58,59,60,61,65,67,71,78,79,87],[[9,103,104,105,110,112],[8,105,110,124,136],[10,11,18,19,105,110],[11,16,101,102,105,111,117],[11,12,105,114,115,117,122],[3,11,17,105,121,127,128,130,131],[8,9,104,112,124],[1,5,7,8,9,104,112],[9,100,102,104,108,116],[8,9,104,113,115,116,123],[3,9,104,128,131,132],[8,16,109],[8,102,108,124,136],[8,12,115,122,124],[3,8,124,125,128,133,136],[13,15,16,102,108],[2,4,6,8,9,115,119,122],[0,3,14,17,128,133],[12,102,106,115,120,122],[3,16,102,107,126,128,129,134],[3,12,115,118,128,134,135]]),
([v0,v1,v2,v311,v3,v78,v252],[0,15,17,103,138,148,153,166,207,245,301,342,409,489,506,532,567,587,617,621],[0,1,2,5,6,7,8,11,13,14,15,20,22,23,24,27,28,29,34,35,36,39,41,45,50,54,56,57,59,60,65,67,71,73,78,79,82],[[10,11,103,110,114,119],[8,11,108,110,113,136],[1,5,7,8,11,104,110,136],[8,11,101,102,110,111,119],[11,110,116,117,119,123],[3,11,110,128,130,136],[8,103,112,113,114,125],[9,10,18,19,103,114],[10,14,100,102,103,107,118],[10,13,17,103,115,117,118,121],[3,10,19,103,124,128,130,131],[8,14,109],[8,14,102,107,113],[8,113,117,121,125],[3,8,113,126,128,132,133],[2,4,6,8,11,102,107],[12,13,16,17,117,121],[0,3,15,19,128,130],[13,14,102,105,117,121,122],[3,14,102,106,127,128,129,134],[3,13,17,117,120,128,134,135]]),
([v0,v1,v2,v312,v3,v78,v252],[0,15,37,127,144,148,162,200,238,245,325,368,501,506,532,547,567,610,617,621],[0,1,2,4,5,6,7,8,11,14,15,20,24,27,28,29,34,35,36,39,41,50,51,54,56,57,58,59,60,61,65,67,71,78,79,91],[[10,11,103,104,105,110,112],[8,11,105,110,123],[1,5,7,8,11,105,110],[11,101,102,105,111,117],[8,11,105,114,115,117,122],[3,11,105,126,127,129,130],[8,104,112,123,135],[9,10,18,19,104,112],[10,16,100,102,104,108,116],[10,12,104,113,115,116,119],[3,10,17,104,121,127,130,131],[8,16,109],[8,102,108,123,135],[8,12,115,119,123],[3,8,123,124,127,132,135],[13,15,16,102,108],[2,4,6,8,11,115,119],[0,3,14,17,127,132],[12,102,106,115,119,120],[3,16,102,107,125,127,128,133],[3,12,115,118,127,133,134]]),
([v0,v1,v2,v59,v5,v3,v78,v252],[53,56,150,153,207,223,271,275,332,436,437,506,513,538,579,612,627,628],[2,5,14,15,24,26,27,28,29,32,34,35,36,39,45,47,48,49,50,59,63,65,66,67,71,78,79,82,87,88,91],[[7,8,101,103,104,111],[3,8,102,103],[2,3,5,8,103,111],[3,127],[3,8,103,111,115],[8,103,107,108,111,114],[1,8,103,119,121,129],[3,101,102,104,109],[6,7,12,16,101,110],[7,15,17,101,116],[7,12,101,110,115],[7,10,14,101,106,108,110,113],[1,7,15,101,118,119,121,123],[2,3,102,109],[3,8,130],[3,102,109,115],[3,102,105,108,109,113],[1,3,102,119,124,128],[5,12],[4,12,100],[9,10,12,14,108,113],[0,1,12,13,119,121],[11,12,15,115],[10,14,108,114],[1,15,119,121],[10,12,108,113,115,122],[1,12,115,117,119,120,122,125],[1,10,14,108,112,119,125,126]]),
([v0,v1,v2,v313,v5,v3,v78,v252],[53,59,150,162,219,238,271,277,340,436,513,538,553,567,579,600,612,627,628],[0,2,3,5,6,8,9,10,11,14,15,20,23,24,29,32,34,35,41,45,47,48,50,57,59,60,65,67,71,78,87,88],[[7,8,103,110,113,117],[3,8,109,110],[2,3,4,8,110,117],[3,104],[8,101,107,110,111,117],[3,8,110,117,119],[1,8,110,124,126,131],[3,103,109,113,115],[6,7,14,17,103,116],[7,16,18,103,121],[7,14,100,101,103,108,116],[7,9,103,116,119],[1,7,15,103,122,124,126,127],[2,3,109,115],[3,8,112],[3,101,102,106,108,109,115],[3,109,115,119],[1,3,109,124,128,130],[4,9],[10,12,14,101,118],[5,9,14,114],[0,1,11,14,124,129],[13,14,101,120],[9,13,14,119],[1,15,124,126],[9,14,101,118,119],[1,14,101,105,123,124,125,129],[1,9,14,119,124,129]]),
([v0,v1,v2,v5,v81,v3,v78,v252],[1,53,54,150,155,215,226,249,271,272,331,334,409,436,506,513,533,538,567,579,600,612,613,621,627,629,641,642],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,48,50,57,59,60,65,66,67,71,78,79,85,87,88,90],[[9,11,103,111,114,121],[4,11,110,111],[4,104],[10,11,15,21,111],[11,101,108,111,112,121],[11,111,117,118,121,139],[2,11,111,128,130,138],[4,103,110,114,119],[7,9,22,25,26,27,103,125],[8,9,15,24,103,125],[9,15,100,101,103,109,120],[9,13,103,116,118,120,136],[2,9,20,103,126,128,130,132],[4,11,113],[3,4,15,23,110],[4,101,102,107,109,110,119],[4,110,115,118,119,135],[2,4,110,128,133,137],[14,15,21,26],[14,15,101,131],[12,13,18,19,118],[0,2,16,20,128,130],[5,13,124],[6,13,15,123],[1,2,15,17,128],[13,15,101,105,118],[2,15,101,106,127,128,129,134],[2,13,118,122,128,134,135]]),
([v0,v1,v2,v5,v3,v8,v78,v252],[26,53,61,150,163,201,220,245,271,331,345,413,436,439,506,513,535,538,547,553,567,579,612,628],[2,3,5,6,7,8,11,12,14,15,20,23,24,26,28,29,32,34,35,36,39,45,47,48,50,59,63,65,66,67,71,78,79,84,85,87,88],[[8,102,109,112,118],[4,10,108,109],[4,103],[10,100,109,110,118],[9,10,109,136],[10,109,114,115,118,121],[2,10,109,125,127,136],[4,102,108,112,116],[7,8,102,123],[8,15,100,102,107],[5,8,15,117],[8,102,115,120,123],[2,8,102,124,125,127,129],[4,10,111],[4,100,101,108,110,116],[3,4,108,135],[4,108,113,115,116,120],[2,4,108,125,130,135],[14,15,18,19,100,122],[18,19,22,23],[11,13,20,21,115,121],[0,2,16,19,125,127],[6,8,106],[13,15,19,100,104,115,120,122],[2,15,19,100,105,125,126,128,131],[12,13,19,21,115,134],[1,2,17,19,125,133],[2,13,19,115,119,125,131,132]]),
([v0,v1,v2,v5,v3,v78,v252,v285],[0,53,132,148,150,191,245,271,331,369,436,443,460,508,513,532,538,547,553,571,579,600,612],[2,3,5,6,7,8,9,10,11,14,15,20,23,26,28,29,32,35,36,39,41,45,47,50,59,60,65,67,78,79,81,87,88,89,92],[[7,110,117,127,130],[5,9,109,110],[2,5,103],[9,100,107,110,111,117],[9,110,114,115,117,121],[1,110,126,128,132],[8,9,110,117],[5,109,116,127,134],[6,7,127,130],[7,100,108,127,130],[7,115,119,127,130],[1,7,123,126,127],[1,102],[3,5,9,112],[5,100,101,106,108,109,116],[5,109,113,115,116,119],[1,109,126,131,133],[4,5,109,116],[13,17,18,22,100,122],[11,12,19,21,115,121],[0,1,126,128],[15,16,22],[11,18,21,100,104,115,119,120],[1,100,105,125,126,128],[14,16,18,100,108],[1,115,118,126,128,129],[10,11,16,20,115,119],[1,7,124]]),
([v0,v1,v2,v5,v3,v78,v252,v308],[0,53,132,148,150,170,263,271,278,331,348,419,436,441,506,513,532,538,547,553,567,579,612,617,627],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,39,45,48,50,59,60,65,66,67,71,72,78,79,87,88,93],[[8,10,101,105,107,114],[5,10,104,105],[2,5,102],[10,105,114,120,122],[10,105,110,111,114,116],[1,105,119,121,129],[9,10,105,114],[5,101,104,107,112],[6,8,22,23,101,117],[8,15,19,101,113,120,122],[8,13,21,101,109,111,113,115],[1,101,118,119,121,123],[7,8,17,24,101,113],[3,5,10,106],[5,104,112,120,125],[5,104,108,111,112,115],[1,104,119,124,128],[4,5,104,112],[14,15,18,19,120,122],[11,13,20,21,111,116],[0,1,119,121],[16,17,22],[13,15,19,111,115,120,130],[1,15,103,119,120],[1,100],[1,13,111,119,127],[12,13,17,21,111,115],[1,15,126]]),
([v0,v1,v2,v314,v7,v3,v78,v252],[40,43,150,151,201,220,246,353,357,426,427,506,510,537,577,617,623,633],[2,6,15,23,24,26,27,28,29,32,34,35,36,37,39,41,42,43,44,45,57,58,59,60,61,65,71,78,79,81,87,91,92],[[6,101,102,104,110],[3,101,102,103,109],[7,8,12,16,101,111],[8,15,17,101,116],[8,12,101,111,115],[8,10,14,101,107,108,111,119],[1,8,15,101,118,121,122,124,125],[3,6,103,104],[2,3,5,6,104,110],[3,129],[3,6,104,110,115],[6,104,106,108,110,114],[1,6,104,122,125,132],[2,3,103,109],[3,6,130],[3,103,109,115],[3,103,105,108,109,114],[1,3,103,122,126,131],[5,12],[4,12,100],[9,10,12,14,108,119],[0,1,12,13,122,125],[11,12,15,115],[10,14,108,114],[1,15,122,125],[10,12,108,113,114,115,123],[1,12,115,117,120,122,123,127],[1,10,14,108,112,122,127,128]]),
([v0,v1,v2,v315,v7,v3,v78,v252],[40,46,150,161,218,234,255,353,359,426,510,537,551,567,577,597,617,623,633],[1,2,3,5,6,8,11,14,15,20,23,24,29,32,34,35,37,39,41,42,44,47,57,58,59,60,61,65,71,78,91,92],[[6,104,108,111,114],[3,104,108,110,113],[7,8,14,17,104,115],[8,16,18,104,119],[8,14,100,101,104,109,115],[8,9,104,115,117],[1,8,15,104,120,123,124,126,127],[3,6,110,111],[2,3,4,6,111,114],[3,103],[6,101,106,111,114],[3,6,111,114,117],[1,6,111,124,127,131],[2,3,110,113],[3,6,107],[3,101,102,106,110,113],[3,110,113,117],[1,3,110,124,128,130],[4,9],[10,12,14,101,121],[5,9,14,112],[0,1,11,14,124,129],[13,14,101,118],[9,13,14,117],[1,15,124,127],[9,14,101,116,117,118],[1,14,101,105,122,124,125,129],[1,9,14,117,124,129]]),
([v0,v1,v2,v7,v81,v3,v78,v252],[1,40,41,150,155,215,226,245,249,334,353,354,409,426,506,510,533,537,567,577,597,617,618,621,623,634,641,642],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,57,58,59,60,61,65,71,78,79,85,90,91,92],[[8,104,109,112,118],[4,104,109,111,117],[9,11,22,25,26,104,123],[10,11,15,24,104,123],[11,15,100,101,104,110,119],[11,13,104,115,116,119,135],[2,11,20,104,124,126,127,129,130],[4,8,111,112],[4,103],[7,8,15,21,112],[8,101,107,112,118],[8,112,114,116,118,134],[2,8,112,127,130,137],[4,8,108],[3,4,15,23,111],[4,101,102,107,111,117],[4,111,113,116,117,133],[2,4,111,127,131,136],[14,15,21,27],[14,15,101,128],[12,13,18,19,116],[0,2,16,20,127,130],[5,13,122],[6,13,15,121],[1,2,15,17,127],[13,15,101,105,116],[2,15,101,106,125,127,128,132],[2,13,116,120,127,132,133]]),
([v0,v1,v2,v7,v3,v6,v78,v252],[32,40,48,150,166,207,223,245,260,331,353,416,426,429,506,510,536,537,547,551,567,577,617,633],[2,3,5,6,7,8,11,14,15,20,21,23,24,26,27,29,32,34,35,36,38,39,41,42,44,45,57,58,59,60,61,65,71,78,79,89,90,91,92],[[8,103,108,112,117],[4,103,108,111,116],[9,10,103,123],[10,15,100,103,110],[5,10,15,118],[10,103,115,120,123,125],[2,10,103,124,127,128,130,131],[4,8,111,112],[4,102],[8,100,106,112,117],[7,8,112,138],[8,112,114,115,117,121],[2,8,112,128,131,138],[4,8,107],[4,100,101,106,111,116],[3,4,111,137],[4,111,113,115,116,121],[2,4,111,128,132,137],[14,15,18,19,100,122],[18,19,22,23],[11,13,20,21,115,121],[0,2,16,19,128,131],[6,10,109],[13,15,19,100,104,115,121,122],[2,15,19,100,105,126,128,129,133],[12,13,19,21,115,136],[1,2,17,19,128,135],[2,13,19,115,119,128,133,134]]),
([v0,v1,v2,v7,v3,v78,v252,v284],[0,40,131,147,150,196,245,287,331,353,426,433,463,509,510,532,537,547,551,574,577,597,617],[2,3,5,6,7,8,11,14,20,23,24,26,27,29,32,34,36,39,41,44,45,57,59,60,61,65,78,79,82,84,88,91,92],[[7,110,115,124,128],[5,109,114,124,130],[8,9,124,128],[9,100,108,124,128],[9,113,120,124,128],[1,9,119,122,124],[1,103],[5,7,109,110],[2,5,102],[7,100,106,110,115],[7,110,112,113,115,117],[1,110,122,126,132],[6,7,110,115],[3,5,7,107],[5,100,101,106,109,114],[5,109,111,113,114,117],[1,109,122,129,131],[4,5,109,114],[13,17,18,22,100,118],[11,12,19,21,113,117],[0,1,122,126],[15,16,22],[11,18,21,100,104,113,117,118],[1,100,105,121,122,123,126],[14,16,18,100,108],[1,113,116,122,126,127],[10,11,16,20,113,120],[1,9,125]]),
([v0,v1,v2,v7,v3,v78,v252,v308],[0,40,131,147,150,170,245,263,348,353,360,419,426,431,506,510,532,537,547,551,567,577,612,617,623],[2,5,6,8,14,15,23,24,26,27,28,29,32,34,35,39,42,44,45,58,59,60,61,65,66,71,72,78,79,91,92,93],[[7,102,105,107,113],[5,102,105,106,112],[8,10,22,23,102,116],[10,15,19,102,114,121,124],[10,13,21,102,110,111,114,118],[1,102,117,119,120,122,123],[9,10,17,24,102,114],[5,7,106,107],[2,5,101],[7,107,113,121,124],[7,107,109,111,113,115],[1,107,120,123,130],[6,7,107,113],[3,5,7,104],[5,106,112,121,126],[5,106,108,111,112,115],[1,106,120,125,129],[4,5,106,112],[14,15,18,19,121,124],[11,13,20,21,111,115],[0,1,120,123],[16,17,23],[13,15,19,111,115,121,131],[1,15,103,120,121],[1,100],[1,13,111,120,128],[12,13,17,21,111,115],[1,15,127]]),
([v0,v1,v2,v10,v3,v78,v252],[0,78,180,216,228,271,353,409,458,506,532,547,567,612,641,647],[0,1,2,3,5,6,7,8,9,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,45,48,54,57,59,60,65,71,78,79,81,82,87],[[2,5,104,105,111,114],[2,105,110,111,113],[3,6,13,125],[6,101,102,105,112,121],[6,105,117,118,121,126],[1,6,105,130,132,137],[2,104,110,113,114],[4,5,13,127],[5,100,102,104,109,120],[5,104,116,118,120,123],[1,5,104,130,132,136],[2,13,128],[2,102,103,108,109,110,119],[2,110,115,118,119,123],[1,2,110,130,133,138],[9,11,13,102],[7,8,12,13,118],[0,1,10,13,130],[8,14,15,102,106,118,123,124],[1,13,102,107,129,130,131,134],[1,8,13,118,122,130,134,135]]),
([v0,v1,v2,v3,v316,v78,v252],[0,7,32,39,142,146,150,157,245,251,334,388,393,416,506,532,596,612,617,621,623],[0,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,36,39,41,42,44,45,50,56,57,59,60,62,65,67,71,73,78,79,90,94],[[9,10,17,103,112,121],[7,10,17,109,111,121],[10,14,101,110,121],[10,14,104],[10,13,115,121,129,136],[1,10,121,122,127,130,137],[7,9,20,103,109,111,112],[9,14,100,101,103,108,117],[8,9,17,18,103,112],[9,13,103,114,115,117,119],[1,9,16,103,124,127,130,131],[7,14,101,102,107,108,109,116],[6,7,17,19,109,111],[7,13,109,113,115,116,119],[1,7,16,109,125,127,132,133],[2,4,10,11,13,101,110],[10,13,101,105,115,119,120],[1,14,101,106,126,127,128,134],[3,5,10,12,13,115,123,136],[0,1,15,16,127,130],[1,13,115,118,127,134,135]]),
([v0,v1,v2,v3,v317,v78,v252],[0,6,26,38,140,145,150,156,249,306,315,331,336,413,506,532,595,612,617,621,627],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,35,36,39,44,45,47,48,50,56,57,58,59,60,61,65,68,71,73,78,79,85,95],[[8,18,104,111,124],[7,12,20,104,109,110,111,113],[12,14,100,101,104,112,118],[11,12,17,18,104,111],[12,13,104,115,116,118,122],[1,12,16,104,121,128,129,131,132],[7,8,18,110,113,124],[8,14,101,108,124],[8,14,103],[8,13,116,124,133,138],[1,8,124,125,129,132,139],[7,14,101,102,107,108,110,117],[6,7,18,19,110,113],[7,13,110,114,116,117,122],[1,7,16,110,126,129,134,135],[2,4,8,9,13,101,108],[8,13,101,105,116,122,123],[1,14,101,106,127,129,130,136],[3,5,8,10,13,116,120,138],[0,1,15,16,129,132],[1,13,116,119,129,136,137]]),
([v0,v1,v2,v3,v318,v78,v252],[0,5,17,37,138,144,155,215,226,245,250,331,335,410,506,532,594,612,617,621,632],[0,1,2,4,5,6,7,8,11,14,15,20,24,27,28,29,34,35,36,39,44,50,51,53,54,56,57,58,59,60,61,65,67,71,74,78,79,96],[[10,12,20,103,104,105,110,112],[6,19,105,110,124],[12,14,101,102,105,111,117],[11,12,17,19,105,110],[12,13,105,114,115,117,122],[1,12,16,105,120,127,128,130,131],[6,19,104,112,124],[10,14,100,102,104,108,116],[9,10,18,19,104,112],[10,13,104,113,115,116,122],[1,10,16,104,121,128,131,132],[6,14,102,108,124],[6,14,109],[6,13,115,124,134,136],[1,6,124,125,128,133,137],[2,4,6,7,13,102,108],[6,13,102,106,115,122,123],[1,14,102,107,126,128,129,135],[3,5,6,8,13,115,119,136],[0,1,15,16,128,133],[1,13,115,118,128,135,136]]),
([v0,v1,v2,v3,v78,v275],[1,158,252,337,419,506,532],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,43,48,54,59,65,71,78,79,85,90],[[2,3,104,105,106,113,116],[1,3,106,111,112,113,115],[3,5,101,102,106,114,123],[3,4,106,119,120,123,137],[3,6,106,127,131,132],[1,2,105,112,115,116],[2,5,100,102,105,110,122],[2,4,105,118,120,122,136],[2,6,105,129,131,132],[1,5,102,103,109,110,112,121],[1,4,112,117,120,121,135],[1,6,112,130,131,133],[4,5,102,107,120,128],[0,4,102,108,126,128,131,134],[0,4,120,124,125,131,134,135]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x2 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x3 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x4 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x5 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x6 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x7 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (7*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x8 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (8*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x9 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (9*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x10 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (10*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x11 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (11*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x12 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (12*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x13 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (13*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x14 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (14*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x15 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (15*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x16 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (16*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x17 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (17*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x18 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (18*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC9x19 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (19*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := levelStep ptopB ptopW ptopQ ptopI8 (chunks 4 ptopD9 20 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  · exact ptopC9x2
  · exact ptopC9x3
  · exact ptopC9x4
  · exact ptopC9x5
  · exact ptopC9x6
  · exact ptopC9x7
  · exact ptopC9x8
  · exact ptopC9x9
  · exact ptopC9x10
  · exact ptopC9x11
  · exact ptopC9x12
  · exact ptopC9x13
  · exact ptopC9x14
  · exact ptopC9x15
  · exact ptopC9x16
  · exact ptopC9x17
  · exact ptopC9x18
  · exact ptopC9x19
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([v282,v0,v1,v2,v3,v78,v252],[0,150,213,245,304,331,386,409,493,506,532,547,567],[2,4,5,6,13,14,15,23,24,26,27,28,29,32,34,35,36,39,45,57,59,60,61,66,67,72,73,75,78,79,84,89,93],[[5,6,9,11,103,115],[3,4,9,11,102,114],[1,2,9,11,105,113],[0,100],[7,8,9,11,112,117],[0,9,120],[4,6,101,102,103,106,108],[2,6,103,104,105,106,107],[6,9,103,115,121,123],[6,8,12,103,111,112,115,118],[0,103,122,128,131],[2,4,102,105,107,108],[4,9,102,114,121,123],[4,8,12,102,110,112,114,117],[0,102,124,128,130],[2,9,105,113,121,125],[2,8,12,105,109,112,113,117],[0,105,126,128,130],[8,9,112,117,121,132],[0,9,119,121,128],[0,10,112,116,127,128,129]]),
([v283,v0,v1,v2,v3,v78,v252],[0,150,241,245,327,331,405,409,506,532,547,567],[0,1,2,3,4,5,6,8,9,11,13,14,15,20,23,24,29,32,34,35,41,57,58,59,60,61,65,67,71,73,75,78,79,85,90],[[5,6,9,106,119],[3,4,9,105,118],[1,2,9,111,117],[8,9,10,102,120],[0,116],[0,7,131],[4,6,104,105,106,112,115],[2,6,106,110,111,112,114],[6,10,11,101,102,106,113,119],[6,7,106,119,132,134],[0,106,122,123,125,126],[2,4,105,111,114,115],[4,10,11,100,102,105,109,118],[4,7,105,118,132,133],[0,105,123,126,127],[2,10,11,102,103,108,109,111,117],[2,7,111,117,132,133],[0,111,123,128,129],[7,10,102,120,132],[0,9,102,107,121,123,124],[0,7,123,130,132]]),
([v93,v0,v1,v2,v3,v78,v252],[0,134,150,226,245,315,331,393,409,506,532,547,589],[0,1,2,3,4,5,6,8,9,11,13,14,15,20,23,24,29,32,34,35,37,39,41,44,45,50,51,56,57,58,59,60,61,65,67,71,73,78],[[6,7,11,12,106,119],[4,5,11,12,105,118],[2,3,11,12,111,117],[8,122],[8,9,116],[0,1,10,11,130,137],[5,7,104,105,106,112,115],[3,7,106,110,111,112,114],[7,9,11,101,102,106,113,119],[7,8,106,119,121,124],[1,7,11,106,123,129,130,132,133],[3,5,105,111,114,115],[5,9,11,100,102,105,109,118],[5,8,105,118,121,124],[1,5,11,105,125,130,133,134],[3,9,11,102,103,108,109,111,117],[3,8,111,117,121,126],[1,3,11,111,127,130,135,136],[8,9,102,120,121],[1,9,11,102,107,128,130,131,137],[1,8,11,121,130,137]]),
([v47,v0,v1,v2,v3,v78,v252],[0,81,150,245,292,331,374,409,466,506,532,567],[2,4,5,6,9,10,11,14,15,16,17,19,20,24,26,27,28,29,32,34,35,36,39,44,45,50,53,58,59,61,65,67,69,71,72,78,79,87,91],[[5,6,9,103,108],[3,4,9,102,113],[2,9,107],[2,100],[7,8,9,11,117,122],[0,1,9,10,128,133],[4,6,101,102,103,108,113],[2,103,108,118,138],[6,9,103,105,106,112,120],[6,8,11,103,116,117,120,124],[1,6,103,123,127,128,129,130],[2,102,113,118,137],[4,9,102,106,111,112,119],[4,8,11,102,115,117,119,122],[1,4,102,125,128,130,131],[2,9,104,106,118],[2,11,114,117,118,122],[1,2,118,128,133,137],[8,9,106,109,117,122,126],[1,9,106,110,128,132,134,135],[1,8,11,117,121,128,135,136]]),
([v286,v0,v1,v2,v3,v78,v252],[0,107,150,245,320,331,398,409,506,532,547,567,593],[0,1,2,3,4,5,6,8,9,11,13,14,15,16,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,51,57,58,59,60,61,65,67,71,73,78,85],[[5,6,11,106,127],[3,4,11,105,129],[2,7,121],[8,10,11,102,126],[2,125],[0,1,9,11,134,141],[4,6,104,105,106,112,116],[2,106,110,111,112,115],[6,11,101,102,106,114,123],[6,7,106,119,120,123,131],[1,6,12,106,128,133,134,136,137],[2,105,111,115,116],[4,11,100,102,105,109,122],[4,7,105,118,120,122,131],[1,4,12,105,130,134,137,138],[2,11,102,103,108,109,111],[2,7,111,117,120],[1,2,111,134,139,140],[7,102,113,120,126,131],[1,11,102,107,132,134,135,141],[1,7,120,124,134,141,142]]),
([v44,v0,v1,v2,v3,v78,v252],[0,92,150,201,245,331,380,409,475,506,532,567],[0,1,2,3,5,6,7,8,11,13,14,15,18,20,23,26,27,28,29,32,34,35,36,39,44,45,47,56,58,59,61,63,65,66,71,73,78,79,81,92],[[5,6,9,105,111],[4,9,104],[2,3,9,110,114],[4,108],[7,8,9,11,118,123],[0,1,9,10,129,132],[4,105,111,120,139],[3,6,105,109,110,111,114],[6,9,101,102,105,113,121],[6,8,11,105,117,118,121,125],[1,6,105,124,128,129,130,132],[3,4,110,114,120,138],[4,9,100,102,120],[4,11,116,118,120,123],[1,4,120,129,132,138],[3,9,102,103,110,112,113,119],[3,8,11,110,115,118,119,123],[1,3,110,127,129,134,135],[8,9,102,106,118,123,126],[1,9,102,107,129,131,133,136],[1,8,11,118,122,129,136,137]]),
([v291,v0,v1,v2,v3,v78,v252],[0,116,150,234,245,331,402,409,506,532,547,567,593],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,45,54,56,57,58,59,60,61,65,67,71,73,78,79,84],[[5,6,11,106,127],[4,7,122],[2,3,11,112,130],[8,10,11,102,126],[4,125],[0,1,9,11,134,143],[4,104,105,106,113,116],[3,6,106,111,112,113,115],[6,11,101,102,106,114,123],[6,7,106,119,120,123,129],[1,6,12,106,128,133,134,136,137],[3,4,105,112,115,116],[4,11,100,102,105,110],[4,7,105,118,120],[1,4,105,134,137,138],[3,11,102,103,109,110,112,121],[3,7,112,117,120,121,129],[1,3,12,112,131,134,139,140],[7,102,107,120,126,129],[1,11,102,108,132,134,135,141],[1,7,120,124,134,141,142]]),
([v38,v0,v1,v2,v3,v78,v252],[0,100,150,207,245,298,331,409,484,506,532,567],[0,1,2,3,5,6,7,8,9,11,14,20,23,24,26,27,28,29,32,34,35,36,39,41,45,50,56,57,59,60,65,67,71,73,78,79,82,88],[[6,9,105],[4,5,9,104,113],[2,3,9,110,112],[6,111],[7,8,9,11,117,124],[0,1,9,10,128,130],[5,6,104,113,120,137],[3,6,110,112,120,136],[6,9,101,102,120],[6,11,116,117,120,124],[1,6,120,128,130,136],[3,5,104,110,112,113],[5,9,100,102,104,109,119],[5,8,11,104,115,117,119,122],[1,5,104,125,128,130,131],[3,9,102,103,108,109,110,118],[3,8,11,110,114,117,118,122],[1,3,110,126,128,132,133],[8,9,102,106,117,122,123],[1,9,102,107,127,128,129,134],[1,8,11,117,121,128,134,135]]),
([v88,v0,v1,v2,v3,v78,v252],[0,124,150,238,245,324,331,409,506,532,547,567,593],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,45,47,48,50,54,56,57,58,59,60,61,65,67,71,73,78,79,89],[[6,7,123],[4,5,11,105,129],[2,3,11,112,131],[8,10,11,102,128],[6,127],[0,1,9,11,135,144],[5,6,104,105,106,113,116],[3,6,106,111,112,113,115],[6,11,101,102,106,114],[6,7,106,119,120],[1,6,106,134,135,137,138],[3,5,105,112,115,116],[5,11,100,102,105,110,122],[5,7,105,118,120,122,125],[1,5,12,105,130,135,138,139],[3,11,102,103,109,110,112,121],[3,7,112,117,120,121,125],[1,3,12,112,132,135,140,141],[7,102,107,120,125,126],[1,11,102,108,133,135,136,142],[1,7,120,124,135,142,143]]),
([v0,v1,v4,v2,v3,v78,v252],[0,66,150,180,245,331,409,449,506,532,547,567,612,623],[0,1,2,3,5,6,7,8,9,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,45,51,53,54,56,57,59,60,65,71,73,78,79,81,82],[[4,5,104,105],[4,111],[3,5,105,110,113,121],[5,101,102,105,112,121],[5,105,117,118,121,125],[1,5,105,131,133,139],[4,5,114],[3,4,104,110,113,120],[4,100,102,104,109,120],[4,104,116,118,120,123],[1,4,104,131,133,138],[2,3,12,13,110,128],[8,10,12,102,127],[6,7,11,12,118,126],[0,1,9,12,131,134],[3,102,103,108,109,110,119],[3,7,110,115,118,119,123],[1,3,110,129,131,134,135],[7,102,106,118,123,124],[1,102,107,130,131,132,136],[1,7,118,122,131,136,137]]),
([v0,v1,v2,v5,v3,v78,v252],[0,53,150,245,271,331,409,436,506,532,547,567,612,628],[0,2,3,5,6,7,8,9,10,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,45,47,48,50,57,59,60,65,67,71,78,79,87,88],[[4,5,103,111,114,121],[2,5,110,111],[2,104],[5,101,108,111,112,121],[5,111,117,118,121,125],[1,5,111,130,132,138],[2,103,110,114,119],[3,4,12,13,103,127],[4,100,101,103,109,120],[4,7,103,116,118,120,123],[1,4,103,128,130,132,133],[2,5,113],[2,101,102,107,109,110,119],[2,110,115,118,119,123],[1,2,110,130,134,137],[8,10,12,101,126],[6,7,11,12,118,125],[0,1,9,12,130,132],[7,101,105,118,123,124],[1,101,106,129,130,131,135],[1,7,118,122,130,135,136]]),
([v0,v1,v2,v7,v3,v78,v252],[0,40,150,245,331,353,409,426,506,532,547,567,617,633],[1,2,3,5,6,7,8,11,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,45,57,58,59,60,61,65,71,78,79,91,92],[[3,104,109,112,118],[2,104,109,111,117],[4,5,12,13,104,123],[5,100,101,104,110,119],[5,7,104,115,116,119,125],[1,5,104,124,127,128,130,131],[2,3,111,112],[2,103],[3,101,107,112,118],[3,112,114,116,118,121],[1,3,112,128,131,136],[2,3,108],[2,101,102,107,111,117],[2,111,113,116,117,121],[1,2,111,128,132,135],[8,10,12,101,122],[6,7,11,12,116,121],[0,1,9,12,128,131],[7,101,105,116,121,122],[1,101,106,126,128,129,133],[1,7,116,120,128,133,134]]),
([v0,v1,v2,v81,v3,v78,v252],[0,1,150,155,245,249,331,334,409,506,532,593],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,42,44,48,50,54,56,57,58,59,60,61,65,67,71,73,78,79,85,90],[[5,7,104,105,106,113,116],[3,7,106,111,112,113,115],[6,7,9,106,127],[7,9,101,102,106,114,123],[7,8,106,119,120,123,145],[1,7,11,106,128,134,135,137,138],[3,5,105,112,115,116],[4,5,9,105,129],[5,9,100,102,105,110,122],[5,8,105,118,120,122,144],[1,5,11,105,130,135,138,139],[2,3,9,112,131],[3,9,102,103,109,110,112,121],[3,8,112,117,120,121,143],[1,3,11,112,132,135,140,141],[8,126],[8,9,125],[0,1,9,10,135],[8,9,102,107,120],[1,9,102,108,133,135,136,142],[1,8,120,124,135,142,143]]),
([v0,v1,v2,v3,v6,v78,v252],[0,32,150,166,245,260,331,409,416,506,532,547,567],[0,2,3,4,5,6,7,8,9,11,13,14,15,20,21,23,24,26,27,29,32,34,35,36,38,39,41,42,44,45,50,56,57,58,59,60,61,65,67,71,73,78,79,89,90,91,92],[[5,6,103,104,105,112,116],[3,6,105,110,111,112,115],[6,9,101,105,114],[6,9,122],[6,105,119,124,127,129],[1,6,105,128,133,134,136,137],[3,5,104,111,115,116],[5,9,11,100,101,104,109,121],[4,5,11,104,146],[5,8,12,104,118,119,121,125],[1,5,11,104,130,134,137,138],[3,9,11,101,102,108,109,111,120],[2,3,11,111,145],[3,8,12,111,117,119,120,125],[1,3,11,111,131,134,139,140],[6,113],[8,9,11,101,106,119,125,126],[1,9,11,101,107,132,134,135,141],[7,8,11,12,119,144],[0,1,10,11,134,143],[1,8,11,119,123,134,141,142]]),
([v0,v1,v2,v3,v8,v78,v252],[0,26,150,163,245,331,345,409,413,506,532,547,567],[1,2,3,4,5,6,7,8,11,12,13,14,15,18,20,23,24,26,28,29,32,34,35,36,39,44,45,47,48,50,56,58,59,61,63,65,66,67,71,73,78,79,84,85,87,88],[[4,103,104,105,112,116],[3,6,105,110,111,112,115],[6,9,11,100,101,105,114,122],[5,6,11,105,145],[6,8,12,105,118,119,122,126],[1,6,11,105,125,131,132,133,135],[3,4,104,111,115,116],[4,9,101,104,109],[4,9,121],[4,104,119,124,128],[1,4,104,129,132,135,137],[3,9,11,101,102,111,113,114,120],[2,3,11,111,144],[3,8,12,111,117,119,120,124],[1,3,11,111,130,132,138,139],[4,108],[8,9,11,101,106,119,124,127],[1,9,11,101,107,132,134,136,140],[7,8,11,12,119,143],[0,1,10,11,132,142],[1,8,11,119,123,132,140,141]]),
([v0,v1,v2,v3,v9,v78,v252],[0,17,150,245,257,331,342,409,410,506,532,547,567],[2,3,4,5,6,10,11,13,14,15,16,17,19,20,23,24,27,28,29,32,34,35,36,39,44,45,50,53,54,56,58,59,61,65,67,69,71,72,73,78,79,81,82],[[4,6,102,103,104,109,115],[2,104,107,108,109,114],[6,9,11,104,105,106,113,121],[5,6,11,104,142],[6,8,12,104,117,118,121,125],[1,6,11,104,124,130,131,132,133],[2,103,108,114,115],[4,9,11,103,106,112,113,120],[3,4,11,103,141],[4,8,12,103,116,118,120,123],[1,4,11,103,126,131,133,134],[2,9,101,106,108],[2,9,119],[2,108,118,123,128],[1,2,108,129,131,136,138],[2,100],[8,9,11,106,110,118,123,127],[1,9,11,106,111,131,135,137,139],[7,8,11,12,118,140],[0,1,10,11,131,139],[1,8,11,118,122,131,139,140]]),
([v0,v1,v2,v3,v78,v252,v284],[0,150,196,245,287,331,409,463,506,532,547,567,593],[0,2,3,5,6,7,8,9,11,14,20,23,24,26,27,29,32,34,36,39,41,44,45,57,59,60,61,65,67,73,78,79,82,84,88],[[4,5,103,112,126,132],[2,5,109,111,126,134],[5,101,110,126,132],[5,115,122,126,132],[0,5,121,124,126],[0,104],[2,4,103,109,111,112],[4,10,100,101,103,108,117],[4,7,12,103,114,115,117,119],[0,103,124,128,130],[3,4,9,103,112],[2,10,101,102,107,108,109,116],[2,7,12,109,113,115,116,119],[0,109,124,129,133],[1,2,9,109,111],[7,10,12,101,105,115,119,120],[0,101,106,123,124,125,130],[8,9,10,101,110],[0,115,118,124,130,131],[6,7,9,11,115,122],[0,5,127]]),
([v0,v1,v2,v3,v78,v252,v285],[0,150,191,245,331,369,409,460,506,532,547,567,593],[1,2,3,5,6,7,8,9,11,13,14,15,20,23,26,28,29,32,35,36,39,41,45,50,59,60,61,65,67,73,78,79,81,89,92],[[3,104,111,128,132],[2,5,104,109,110,111,113],[5,10,100,101,104,112,118],[5,7,12,104,115,116,118,122],[0,104,126,127,130],[4,5,9,104,111],[2,3,110,113,128,134],[3,101,108,128,132],[3,116,120,128,132],[0,3,123,127,128],[0,103],[2,10,101,102,107,108,110,117],[2,7,12,110,114,116,117,120],[0,110,127,129,133],[1,2,9,110,113],[7,10,12,101,105,116,120,121],[0,101,106,125,127,130],[8,9,10,101,108],[0,116,119,127,130,131],[6,7,9,11,116,120],[0,3,124]]),
([v0,v1,v2,v3,v78,v252,v290],[0,150,245,282,331,364,409,446,506,532,547,567,593],[0,1,2,4,5,6,7,11,14,15,17,20,24,27,28,29,34,35,36,39,41,45,56,59,60,61,67,71,73,79,84,87,89,91],[[3,5,103,104,105,109,112],[1,105,109,128,131],[5,10,101,102,105,111,117],[5,7,12,105,114,115,117,121],[0,105,125,127,130],[4,5,9,105,109],[1,104,112,128,133],[3,10,100,102,104,107,116],[3,7,12,104,113,115,116,119],[0,104,126,127,132],[2,3,9,104,112],[1,102,107,128,131],[1,115,119,128,131],[0,1,122,127,128],[0,108],[7,10,12,102,106,115,119,120],[0,102,110,124,127,130],[8,9,10,102,107],[0,115,118,127,129,130],[6,7,9,11,115,119],[0,1,123]]),
([v0,v1,v2,v3,v78,v252,v308],[0,150,170,245,263,331,348,409,419,506,532,547,567],[2,4,5,6,8,13,14,15,23,24,26,27,28,29,32,34,35,39,44,45,50,56,58,59,60,61,65,66,67,71,72,73,78,79,93],[[4,6,101,102,103,107,109],[2,6,103,105,106,107,108],[6,9,11,103,116,124,127],[6,8,12,103,112,113,116,119],[0,103,118,122,123,125,126],[5,6,10,103,116],[2,4,102,106,108,109],[4,9,11,102,115,124,127],[4,8,12,102,111,113,115,117],[0,102,120,123,126,128],[3,4,10,102,115],[2,9,11,106,114,124,130],[2,8,12,106,110,113,114,117],[0,106,121,123,129,131],[1,2,10,106,114],[8,9,11,113,117,124,134],[0,9,104,123,124],[0,100],[0,8,113,123,133],[7,8,10,12,113,117],[0,9,132]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC10x1 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC10x2 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC10x3 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC10x4 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopW ptopQ ptopI9 (chunks 4 ptopD10 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  · exact ptopC10x1
  · exact ptopC10x2
  · exact ptopC10x3
  · exact ptopC10x4
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([v0,v1,v2,v3,v78,v252],[0,150,245,331,409],[0,1,2,3,4,5,6,7,8,9,11,13,14,15,20,23,24,26,27,28,29,32,34,35,36,39,41,44,45,50,56,57,58,59,60,61,65,67,71,73,78,79],[[2,3,104,105,106,113,116],[1,3,106,111,112,113,115],[3,101,102,106,114,123],[3,4,106,119,120,123,128],[0,3,106,127,132,133,135,136],[1,2,105,112,115,116],[2,100,102,105,110,122],[2,4,105,118,120,122,125],[0,2,105,129,133,136,137],[1,102,103,109,110,112,121],[1,4,112,117,120,121,125],[0,1,112,130,133,138,139],[4,102,107,120,125,126],[0,102,108,131,133,134,140],[0,4,120,124,133,140,141]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK ptopT ptopK ptopP 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI11 : LevelN ptopR ptopT 11 ptopD11 := levelStep ptopB ptopW ptopQ ptopI10 (chunks 4 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_12144

theorem PEqualNP.Outside.L_meta_12144 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12144.replaceShort
