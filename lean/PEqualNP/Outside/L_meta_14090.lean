import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14090_aux
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

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
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

abbrev Cuts := List (Sig × Nat)

def budget (T : Sig) (total lower room : Nat) (cs : Cuts) (ws : List Sig) : Prop :=
  ∀ c ∈ cs, ∃ (f : Row → Row) (roots : List Sig) (p : Nat) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.1 = true) ∧ p + c.2 + room ≤ total ∧
    Reach true (roots.map observe) p bank ∧ poolSupply true f bank ws ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ k next, Reach true (roots.map observe) k next →
      Available true next (restrictRows f (observe T)) → lower ≤ k

def advanceCuts (cs : Cuts) (a b z : Sig) : Cuts :=
  cs.map fun c => (c.1, c.2 + (if availableB true c.1 [a, b] z then 1 else 0))

def cutsOK (total lower : Nat) (cs : Cuts) (ws : List Sig) : Bool :=
  cs.all fun c => decide (lower + c.2 + ws.countP (isMaskedConstant c.1) ≤ total)

lemma child_mem {ws : List Sig} {a b w : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hm : w ∈ childTwo ws a b d ka kb) :
    w = bin d a b ∨ w ∈ ws := by
  rcases List.mem_cons.mp hm with eq | tail
  · exact Or.inl eq
  · right
    rcases mem_kept tail with rfl | tail
    · exact ha
    · rcases mem_kept tail with rfl | tail
      · exact hb
      · exact List.mem_of_mem_erase (List.mem_of_mem_erase tail)

lemma child_nodup {ws : List Sig} (hn : ws.Nodup) {a b : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) (fresh : bin d a b ∉ ws) :
    (childTwo ws a b d ka kb).Nodup := by
  let rest := (ws.erase a).erase b
  have hrest : rest.Nodup := (hn.erase _).erase _
  have har : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
  have hbr : b ∉ rest := (hn.erase a).not_mem_erase
  have hark : a ∉ kept kb b rest := by cases kb <;> simp [kept, har, hne]
  apply List.nodup_cons.mpr
  refine ⟨?_, kept_nd ka a _ (kept_nd kb b _ hrest hbr) hark⟩
  intro hm
  rcases mem_kept hm with e | tail
  · exact fresh (e.symm ▸ ha)
  rcases mem_kept tail with e | hl
  · exact fresh (e.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hl))

lemma keep_membership {α : Type} {a x : α} {l : List α} {k : Bool} :
    x ∈ kept k a l ↔ (k = true ∧ x = a) ∨ x ∈ l := by
  cases k <;> simp [kept,eq_comm]

lemma child_swap (ws : List Sig) (hn : ws.Nodup) (a b : Sig)
    (d : Nat) (hd : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).toFinset =
      (childTwo ws b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_membership,(hn.erase _).mem_erase_iff,hn.mem_erase_iff,bin_flip hd a b]
  tauto

lemma budget_next {T total lower room cs ws} (h : budget T total lower (room+1) cs ws)
    {a b : Sig} {d : Nat} {ka kb : Bool}
    (ha : a ∈ ws) (hb : b ∈ ws) (hd : allowed true d) :
    budget T total lower room (advanceCuts cs a b (bin d a b)) (childTwo ws a b d ka kb) := by
  intro c hc
  obtain ⟨c₀, ch, rfl⟩ := List.mem_map.mp hc
  obtain ⟨f, roots, p, bank, dom, size, reach, avail, nonconst, bound⟩ := h c₀ ch
  let z := bin d a b
  by_cases old : availableB true c₀.1 [a, b] z = true
  · refine ⟨f, roots, p, bank, dom, ?_, reach, ?_, nonconst, bound⟩
    · change p + (c₀.2 + (if availableB true c₀.1 [a, b] z then 1 else 0)) + room ≤ total
      rw [if_pos old]
      omega
    · intro v hv
      rcases child_mem ha hb hv with rfl | raw
      · exact availableB_sound dom (fun u hu => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          exact avail _ (hu.elim (· ▸ ha) (· ▸ hb))) old
      · exact avail _ raw
  · obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime hd (avail _ ha) (avail _ hb)
    refine ⟨f, roots, p+1, _, dom, ?_, Reach.two op reach hx hy, ?_, nonconst, bound⟩
    · change p + 1 + (c₀.2 + (if availableB true c₀.1 [a, b] z then 1 else 0)) + room ≤ total
      rw [if_neg old]
      omega
    · intro v hv
      rcases child_mem ha hb hv with rfl | raw
      · rw [obs_bin,restrict_comb,e]
        exact Or.inl (by simp)
      · exact available_cons _ (avail _ raw)

lemma cutsOK_run {T total lower room cs ws k}
    (h : budget T total lower room cs ws) (hk : k ≤ room)
    (hn : ws.Nodup) (run : Live true T k ws.toFinset) :
    cutsOK total lower cs ws = true := by
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨f, roots, p, bank, dom, size, reach, avail, nonconst, bound⟩ := h c hc
  have supplyP : supply true bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact avail a ha
  have limit := projected_bound f (list_run run ws hn rfl) nonconst reach supplyP bound
  have count := count_constants dom ws
  exact decide_eq_true (by omega)

abbrev PairIndex := Fin 156

def leftRow (j : PairIndex) : Row := ⟨128+j.val, by have := j.isLt; omega⟩
def rightRow (j : PairIndex) : Row := ⟨284+j.val, by have := j.isLt; omega⟩

def separation (a : Sig) : BitVec 156 := ((a >>> 128) ^^^ (a >>> 284)).setWidth 156

lemma separation_bit (a : Sig) (j : PairIndex) :
    (separation a).getLsbD j.val = true ↔ bit (leftRow j) a ≠ bit (rightRow j) a := by
  have lo : j.val + 128 < 512 := by have := j.isLt; omega
  have hi : j.val + 284 < 512 := by have := j.isLt; omega
  simp only [separation,BitVec.getLsbD_setWidth,j.isLt,decide_true,Bool.true_and,
    BitVec.getLsbD_xor,BitVec.getLsbD_ushiftRight]
  change ((a.getLsbD (128+j.val)) ^^ (a.getLsbD (284+j.val))) = true ↔ _
  simp [leftRow,rightRow,bit]

def cover (ws : List Sig) : BitVec 156 :=
  ws.foldr (fun a z => separation a ||| z) 0

lemma cover_bit (j : PairIndex) (ws : List Sig) :
    (cover ws).getLsbD j.val = true ↔ ∃ a ∈ ws, bit (leftRow j) a ≠ bit (rightRow j) a := by
  induction ws with
  | nil => simp [cover]
  | cons a ws ih =>
    change (separation a ||| cover ws).getLsbD j.val = true ↔ _
    simp only [BitVec.getLsbD_or,Bool.or_eq_true,separation_bit,ih,List.mem_cons,exists_eq_or_imp]

def coverOK (T : Sig) (ws : List Sig) : Bool :=
  ((separation T) &&& cover ws) == separation T

lemma coverOK_run {T ws k} (run : Live true T k ws.toFinset) : coverOK T ws = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : PairIndex := ⟨j,hj⟩
  change ((separation T) &&& cover ws).getLsbD i.val = (separation T).getLsbD i.val
  rw [BitVec.getLsbD_and]
  cases h : (separation T).getLsbD i.val
  · rfl
  · obtain ⟨a,ha,hd⟩ := live_row_difference run ((separation_bit T i).mp h)
    have hc := (cover_bit i ws).mpr ⟨a,List.mem_toFinset.mp ha,hd⟩
    simp [hc]

def flags : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]

lemma mem_flags (a b : Bool) : (a,b) ∈ flags := by
  cases a <;> cases b <;> simp [flags]

def checkChildren (room : Nat) (ws : List Sig) (a b : Sig) (d : Nat)
    (check : List Sig → Bool) : Bool :=
  let z := bin d a b
  if z == zero || z == one || ws.contains z then true
  else flags.all fun (ka,kb) =>
    let child := childTwo ws a b d ka kb
    if child.length ≤ room+1 then check child else true

lemma checkChildren_at {room ws a b d check} (h : checkChildren room ws a b d check = true)
    {ka kb : Bool} (fresh : bin d a b ∉ ws) (properB : proper (bin d a b))
    (size : (childTwo ws a b d ka kb).length ≤ room+1) :
    check (childTwo ws a b d ka kb) = true := by
  have invalid : (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = false := by
    simp [properB.1, properB.2, fresh]
  simp only [checkChildren, invalid, Bool.false_eq_true, ite_false] at h
  have each := List.all_eq_true.mp h (ka,kb) (mem_flags ka kb)
  simpa only [if_pos size] using each

def checkNode (T : Sig) (total lower room : Nat) (cs : Cuts) (ws : List Sig)
    (next : Cuts → List Sig → Bool) : Bool :=
  if !coverOK T ws || !cutsOK total lower cs ws then true
  else !ws.contains T && ws.all fun a => ws.all fun b =>
    if a.toNat < b.toNat then (List.range 4).all fun d =>
      checkChildren room ws a b d (next (advanceCuts cs a b (bin d a b)))
    else true

lemma rejectZero {T : Sig} {ws : List Sig} (h : !ws.contains T = true) :
    Impossible true T 0 ws.toFinset := by
  intro k hk run
  have eq : k = 0 := by omega
  subst k
  have ht : T ∈ ws := by
    apply List.mem_toFinset.mp
    rw [run.1]
    simp
  have con : ws.contains T = true := List.contains_iff_mem.mpr ht
  rw [con] at h
  exact Bool.noConfusion h

set_option maxHeartbeats 1000000 in
lemma checkNode_sound {T total lower room cs ws} {next : Cuts → List Sig → Bool}
    (hn : ws.Nodup) (hb : budget T total lower (room+1) cs ws)
    (next_sound : ∀ c w, w.Nodup → budget T total lower room c w →
      next c w = true → Impossible true T room w.toFinset)
    (hc : checkNode T total lower room cs ws next = true) :
    Impossible true T (room+1) ws.toFinset := by
  unfold checkNode at hc
  split at hc
  next h =>
    intro k hk run
    simp [cutsOK_run hb hk hn run, coverOK_run run] at h
  next h =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨noTarget, allMoves⟩ := hc
    have noGoal : T ∉ ws := by
      intro hm
      have con : ws.contains T = true := List.contains_iff_mem.mpr hm
      rw [con] at noTarget
      exact Bool.noConfusion noTarget
    apply enum_step hn noGoal
    intro a ha b hm d hd ka kb hab fresh pr size
    have oneSide (a b : Sig) (ha : a ∈ ws) (hm : b ∈ ws)
        (ordered : a.toNat < b.toNat) (d : Nat) (hd : allowed true d)
        (ka kb : Bool) (hab : a ≠ b) (fresh : bin d a b ∉ ws)
        (pr : proper (bin d a b)) (size : (childTwo ws a b d ka kb).length ≤ room+1) :
        Impossible true T room (childTwo ws a b d ka kb).toFinset := by
      have all := List.all_eq_true.mp (List.all_eq_true.mp allMoves a ha) b hm
      rw [if_pos ordered] at all
      have hlt : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
      have ok := List.all_eq_true.mp all d (List.mem_range.mpr hlt)
      have childCheck := checkChildren_at ok fresh pr size
      exact next_sound _ _ (child_nodup hn ha hm hab fresh) (budget_next hb ha hm hd) childCheck
    rcases lt_or_gt_of_ne (fun e => hab (BitVec.eq_of_toNat_eq e)) with ordered | ordered
    · exact oneSide a b ha hm ordered d hd ka kb hab fresh pr size
    · have e := bin_flip hd a b
      rw [child_swap ws hn a b d hd ka kb]
      have len : (childTwo ws b a (flipOp d) kb ka).length ≤ room+1 := by
        have nc1 := child_nodup hn ha hm hab fresh (ka:=ka) (kb:=kb)
        have nc2 := child_nodup hn hm ha hab.symm (e ▸ fresh) (ka:=kb) (kb:=ka)
        rw [←List.toFinset_card_of_nodup nc2, ←child_swap ws hn a b d hd ka kb,
          List.toFinset_card_of_nodup nc1]
        exact size
      exact oneSide b a hm ha ordered (flipOp d) (flip_flip hd).1 kb ka hab.symm
        (e ▸ fresh) (e ▸ pr) len

def reject (T : Sig) (total lower : Nat) : Nat → Cuts → List Sig → Bool
  | 0, _, ws => !ws.contains T
  | room+1, cs, ws => checkNode T total lower room cs ws (reject T total lower room)

lemma reject_sound {T total lower} :
    ∀ {room cs ws}, ws.Nodup → budget T total lower room cs ws →
      reject T total lower room cs ws = true → Impossible true T room ws.toFinset := by
  intro room
  induction room with
  | zero =>
    intro cs ws hn hb hc
    exact rejectZero hc
  | succ room ih =>
    intro cs ws hn hb hc
    exact checkNode_sound hn hb (fun _ _ => ih) hc

def rejectPrefix (T : Sig) (total lower : Nat) (finish : Cuts → List Sig → Bool) :
    Nat → Nat → Cuts → List Sig → Bool
  | 0, _, cs, ws => finish cs ws
  | _+1, 0, _, ws => !ws.contains T
  | depth+1, room+1, cs, ws =>
      checkNode T total lower room cs ws (rejectPrefix T total lower finish depth room)

lemma rejectPrefix_sound {T total lower} {finish : Cuts → List Sig → Bool} :
    ∀ {depth room : Nat}, (∀ c ws, ws.Nodup → budget T total lower room c ws →
       finish c ws = true → Impossible true T room ws.toFinset) →
    ∀ cs ws, ws.Nodup → budget T total lower (depth+room) cs ws →
       rejectPrefix T total lower finish depth (depth+room) cs ws = true →
        Impossible true T (depth+room) ws.toFinset := by
  intro depth
  induction depth with
  | zero =>
    intro room close cs ws nd hb ok
    simp only [Nat.zero_add, rejectPrefix] at hb ok ⊢
    exact close cs ws nd hb ok
  | succ depth ih =>
    intro room close cs ws nd hb ok
    have eq : depth+1+room=depth+room+1 := by omega
    rw [eq] at hb ok ⊢
    exact checkNode_sound nd hb (ih close) ok

def inputWords : List Sig :=
  [0x82082082082082082082082082082082082082fc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0x104104104104104104104104104104104104104fff000fff000fff000fff03ffc003ffc0fff03fcccccccccccccccccccccccccccccccc,
   0x208208208208208208208208208208208208208ffffff000000ffffff00003fffffc0000ffffc0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0x410410410410410410410410410410410410410ffffffffffff00000000003ffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff00,
   0x820820820820820820820820820820820820820ffffffffffffffffffffffc0000000000000000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000]

def threshold3 : Sig := 0xffffc0fc0000ffffc0fc003ffff03f000ffffffe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def threshold4 : Sig := 0xffffffffffc0ffffc0fc003fffffffffffffffffee8fee8fee8fee8fee8fee8fee8fee8
def threshold5 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffefee8fffefee8fffefee8fffefee8
def threshold6 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffefffefee8fffffffefffefee8

def input (i : Nat) : Sig := inputWords.getD i zero

def roots (n : Nat) : List Sig := (List.range n).map input

lemma input_mem {n : Nat} (i : Fin n) : input i.val ∈ roots n :=
  List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

lemma input_index {n : Nat} {a : Sig} (ha : a ∈ roots n) :
    ∃ i : Fin n, input i.val = a := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ha
  exact ⟨⟨i, List.mem_range.mp hi⟩, he⟩

def checkEssential (T : Sig) (xs : List Sig) (a : Sig) (r s : Row) : Bool :=
  (bit r T != bit s T) && xs.all (fun w => w == a || bit r w == bit s w)

lemma checkEssential_sound {T xs a r s}
    (h : checkEssential T xs a r s = true) : Essential T xs a := by
  simp only [checkEssential,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  exact ⟨r,s,h.1,fun w hw hne => (h.2 w hw).resolve_left hne⟩

def lowSingle (i : Nat) : Row := if i = 0 then 2 else 1

def highSingle (i : Nat) : Row :=
  Fin.ofNat 512 ((lowSingle i).val + (1 <<< i))

lemma threshold4EssentialTest : ∀ i : Fin 4,
    checkEssential threshold4 (roots 4) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma threshold5EssentialTest : ∀ i : Fin 5,
    checkEssential threshold5 (roots 5) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma threshold6EssentialTest : ∀ i : Fin 6,
    checkEssential threshold6 (roots 6) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

def positiveRows : List Nat := [3,5,6,7,9,10,11,12,13,14,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def negativeRows : List Nat := [0,1,2,4,8,16]

def assignment (r : Row) : Nat :=
  if r.val < 128 then r.val
  else if r.val < 284 then positiveRows.getD ((r.val-128)/6) 0
  else if r.val < 440 then negativeRows.getD ((r.val-284)%6) 0
  else 0

def selectRows (i : Nat) (r : Row) : Row :=
  let base := 1 <<< i
  let a := assignment r
  Fin.ofNat 512 ((a % base + 2 * (a - a % base)) % 128)

def inBase (base : List Sig) (a : Sig) : Bool := a == zero || base.contains a

lemma inBase_sound {base : List Sig} {f : Row → Row} {a : Sig}
    (h : inBase base (rename f a) = true) :
    Available true (base.map observe) (restrictRows f (observe a)) := by
  simp only [inBase, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [←observe_rename]
  rcases h with hz | hm
  · rw [hz]
    exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

lemma threshold3EssentialTest : ∀ i : Fin 3,
    checkEssential threshold3 (roots 3) (input i.val) (lowSingle i.val) (highSingle i.val) = true := by
  decide +kernel

lemma reject3 : reject threshold3 3 0 3 [] (roots 3) = true := by decide +kernel

lemma lower3 : Lower true (roots 3) threshold3 4 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    obtain ⟨i,rfl⟩ := input_index ha
    exact checkEssential_sound (threshold3EssentialTest i)
  · exact reject_sound (by decide +kernel) (by simp [budget]) reject3

def initial4 : Cuts := (List.finRange 4).map fun i => (neg (input i.val), 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma cutTo3 : ∀ i : Fin 4,
    rename (selectRows i.val) threshold4 = threshold3 ∧
    (∀ r : Row, bit (selectRows i.val r) (neg (input i.val)) = true) ∧
    (roots 4).all (fun w => inBase (roots 3) (rename (selectRows i.val) w)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma initialBudget4 : budget threshold4 6 4 6 initial4 (roots 4) := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  obtain ⟨eq, dom, check⟩ := cutTo3 i
  have heq : restrictRows (selectRows i.val) (observe threshold4) = observe threshold3 :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨selectRows i.val, roots 3, 0, _, dom, Nat.le_refl _, Reach.start,
    (fun _ hm => inBase_sound (List.all_eq_true.mp check _ hm)), ?_, ?_⟩
  · rw [heq]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [heq]
    exact lower3

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma reject4 : reject threshold4 6 4 6 initial4 (roots 4) = true := by decide +kernel

lemma lower4 : Lower true (roots 4) threshold4 7 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    obtain ⟨i,rfl⟩ := input_index ha
    exact checkEssential_sound (threshold4EssentialTest i)
  · exact reject_sound (by decide +kernel) initialBudget4 reject4

open PEqualNP.MetaComplexity
def vars : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def boolTable : Sig := 0xfffffffffffffffffffffefeffffeeccfffffefeffffeeccfefefafaeeccaa00fffffffffffffffffffffefeffffeeccfffffefeffffeeccfefefafaeeccaa00
def projMask : Sig := 0x500050000000000050005000000000005000500000000000500050000000000050005000000000005000500000000000500050000000000050005
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample (r : Row) (i : Fin 8) : Bool := bit r (vars.getD i.val zero)
def lo (i : Fin 8) : Row := ![8,16,32,1,2,1,2,2] i
def hi (i : Fin 8) : Row := Fin.ofNat 512 ((lo i).val + (1 <<< i.val))
def select (r : Row) : Row := Fin.ofNat 512 ((if bit r (input 0) then 2 else 0) +
    (if bit r (input 1) then 16 else 0) + (if bit r (input 2) then 64 else 0) +
    (if bit r (input 3) then 128 else 0))

lemma rawInit : List.ofFn (fun i : Fin 8 => vars.getD i.val zero) = vars := by decide +kernel
lemma sampled (r : Row) : List.ofFn (sample r) = vars.map (bit r) := by
  conv_rhs => rw [←rawInit, List.map_ofFn]
  rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma graphTable : ∀ r : Row, bit r boolTable = target (sample r) := by decide +kernel

lemma graphEssential : ∀ i : Fin 8,
    checkEssential boolTable vars (vars.getD i.val zero) (lo i) (hi i) = true := by decide +kernel

lemma indices {a : Sig} (h : a ∈ vars) : ∃ i : Fin 8, vars.getD i.val zero = a := by
  rw [←rawInit] at h
  exact List.mem_ofFn.mp h

lemma physical (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true boolTable k vars.toFinset := by
  have eq : (execute C.gates vars).getD C.output zero = boolTable := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1), ←sampled]
    exact (correct (sample r)).trans ((graphTable r).symm)
  have hp : proper boolTable := by unfold proper; decide +kernel
  have hit := get_rep (u:=true) (execute C.gates vars) C.output
  rw [eq] at hit
  unfold Repr at hit
  rw [nrm_id (show bit 0 boolTable = false by decide +kernel)] at hit
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates vars legal (by simp) hp (hit.resolve_right (fun h => h hp))
  rw [nrm_map (show vars.all plainWord = true by decide +kernel)] at sub
  have sets : vars.toFinset = S := by
    ext w
    rw [List.mem_toFinset]
    refine ⟨fun hw => ?_, sub w⟩
    obtain ⟨i,rfl⟩ := indices hw
    obtain ⟨l,h,hd,hi⟩ := checkEssential_sound (graphEssential i)
    exact raw_required run _ _ sub l h hd hi
  exact ⟨k,hk,sets.symm ▸ run⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 32000 in
lemma checkedProjection :
    rename select boolTable = threshold4 ∧
    (∀ r : Row, bit (select r) projMask = true) ∧
    vars.all (fun w => inBase (roots 4) (rename select w)) = true ∧
    vars.countP (isMaskedConstant projMask) = 4 := by decide +kernel

lemma eleven {k} (run : Live true boolTable k vars.toFinset) : 11 ≤ k := by
  obtain ⟨eq,dom,check,count⟩ := checkedProjection
  have heq : restrictRows select (observe boolTable) = observe threshold4 :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  have available : supply true ((roots 4).map observe) ((vars.map observe).map (restrictRows select)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact inBase_sound (List.all_eq_true.mp check _ hw)
  have nonconst : ¬ Constant (restrictRows select (observe boolTable)) := by
    rw [heq]
    exact observe_proper (by unfold proper; decide +kernel)
  have lb : ∀ q bank, Reach true ((roots 4).map observe) q bank →
      Available true bank (restrictRows select (observe boolTable)) → 7 ≤ q := by
    rw [heq]
    exact lower4
  have v := projected_bound select (list_run run vars (by decide +kernel) rfl) nonconst Reach.start available lb
  have lost := count_constants dom vars
  rw [count] at lost
  omega

def monoCircuit : Circuit := ⟨[⟨.or,[1,4]⟩,⟨.or,[6,7]⟩,⟨.and,[8,9]⟩,⟨.and,[1,4]⟩,⟨.and,[6,7]⟩,
  ⟨.or,[10,11]⟩,⟨.or,[13,12]⟩,⟨.or,[3,5]⟩,⟨.and,[0,15]⟩,⟨.and,[2,5]⟩,⟨.or,[16,17]⟩,⟨.or,[14,18]⟩],19⟩
lemma legal_witness : ∀ g ∈ monoCircuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monoCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

set_option maxHeartbeats 1000000 in
lemma evaluates : ∀ x : Fin 8 → Bool, monoCircuit.eval (List.ofFn x) = target x := by decide +kernel
end PEqualNP.Outside.L_meta_14090_aux

open PEqualNP.Outside.L_meta_14090_aux in
theorem PEqualNP.Outside.L_meta_14090 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 1, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal oneNot correct
  by_cases h : 12 ≤ gs.length
  · exact ⟨monoCircuit.gates, monoCircuit.output, legal_witness, h, evaluates⟩
  · by_cases present : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    · obtain ⟨g, hm, hn⟩ := present
      have short : gs.countP (fun w => !isNot w) < gs.length := by
        rw [List.countP_eq_length_filter]
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨g, hm, by simp [isNot,hn]⟩
      have fan : PEqualNP.MetaComplexity.FanInTwo ⟨gs,o⟩ := by
        intro w hw
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal w hw
      obtain ⟨k,hk,run⟩ := physical ⟨gs,o⟩ fan correct
      have bound := eleven run
      change k ≤ gs.countP (fun w => !isNot w) at hk
      exfalso
      omega
    · refine ⟨gs,o,fun g hg => ⟨?_, (legal g hg).2⟩, Nat.le_refl _,correct⟩
      exact (legal g hg).1.imp_right (fun hor => hor.resolve_right (fun hn => present ⟨g,hg,hn⟩))
