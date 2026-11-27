import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11317

-- The signed-circuit checker below is adapted from L_meta_10698 (Apache-2.0).
-- Its credits follow. The certificates and the 11-gate circuit are for the present graph.
-- The circuit semantics and the live wire restriction lemmas are adapted from
-- L_meta_10802 and its predecessors L_meta_1674, L_meta_670 and L_meta_1667.
-- Signals are truth tables on the 128 assignments to the seven inputs.

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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
  if h : r.val < 128-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(128-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 128 (128-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 128-d.val <;> simp [shifted,h,r.isLt]

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

-- A restriction is stored with its lower bound and the restricted signals
-- available at the stated cost. Constants among the live wires save gates.
abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

-- Each child has one of three witnesses. Two rows can disagree on the target
-- and agree on every live wire. A restriction can exceed the remaining gate
-- budget. A previously checked state can have exactly the same live wires.
def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 16384 then
    let r := Fin.ofNat 128 (code % 128)
    let s := Fin.ofNat 128 (code / 128)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 32768 then
    match cuts[code-16384]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-32768]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 65536) &&
      checkMoves T k cuts links rest (data / 65536)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 7).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input

-- Setting the missing vertices to zero gives the induced subgraph.
def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6)

def fixes (q : Nat) : List Move :=
  ((List.range 7).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 128 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 7).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 128 r,Fin.ofNat 128 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2



def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x281008812800208128402800281028402810208108810881208108902080281020c02080208120c02081281008900890088120c00880284008900880088108900881284020c020c0 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

def cuts105 : Cuts (goalAt 105) := []

def state105_0 : List Sig := roots 105
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude105_0 : Impossible true (goalAt 105) 3 state105_0.toFinset :=
  node_ok cuts105 [] 0x3081208120a120810481208114600481140014001408048120802080208104880488140820e004880480048004811420 (by decide +kernel)

theorem lower105 : Claim 105 4 :=
  fromSearch 3145731 (by decide +kernel) exclude105_0

def cuts57 : Cuts (goalAt 57) := []

def state57_0 : List Sig := roots 57
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude57_0 : Impossible true (goalAt 57) 3 state57_0.toFinset :=
  node_ok cuts57 [] 0x881188114180881140014001408048104810881143004810488140808b0048808800880088104880480048004810890 (by decide +kernel)

theorem lower57 : Claim 57 4 :=
  fromSearch 3145731 (by decide +kernel) exclude57_0

theorem lower89 : Claim 89 5 :=
  fromLift 5 8 3 lower81 (by decide +kernel)


def rule121_0 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower81 none (by decide +kernel)

def rule121_1 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower105 none (by decide +kernel)

def rule121_2 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower57 none (by decide +kernel)

def rule121_3 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower89 none (by decide +kernel)

def rule121_4 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower89 (some (0,input 0,input 3)) (by decide +kernel)

def cuts121 : Cuts (goalAt 121) := [rule121_0,rule121_1,rule121_2,rule121_3,rule121_4]

def state121_0 : List Sig := [0xffffaaaaffffaaaa,input 0,input 4,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_0 : Impossible true (goalAt 121) 4 state121_0.toFinset :=
  node_ok cuts121 [] 0x14001400140804812c00280028082800280038001c1828002080308020a02080208024800481208020802800088120802081140830812081048128180481208108812800088128000488208020812080 (by decide +kernel)

def state121_1 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_1 : Impossible true (goalAt 121) 5 state121_1.toFinset :=
  node_ok cuts121 [⟨state121_0,exclude121_0⟩] 0x3081208120a1208104812081281804811400140014080481048108811c30048114200481048114200881208128100881088118811c180881284020812810208108900890140808b0140804810c9004810890088108900498048820818000208140021c1814081c181408 (by decide +kernel)

def state121_2 : List Sig := [0xffffffff0000aaaaffffffff0000aaaa,input 0,input 4,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_2 : Impossible true (goalAt 121) 4 state121_2.toFinset :=
  node_ok cuts121 [] 0x4812081281804810481188114300481140014000481400028002800281018811c08188108810881208128102081089004810c900481140108800880188128400488048808b014082081340820811408 (by decide +kernel)

def state121_3 : List Sig := [0xaaaa0000aaaa0000aaaa0000aaaa,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_3 : Impossible true (goalAt 121) 5 state121_3.toFinset :=
  node_ok cuts121 [⟨state121_2,exclude121_2⟩] 0x3081208120a120810481208128180481140014001408048104811c201430048128002800281020811c0814081418140820812810208108900890140808b0140804810c900481089008800890284020812810208128104003140880001408048114200481142008810488 (by decide +kernel)

def state121_4 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa,0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_4 : Impossible true (goalAt 121) 4 state121_4.toFinset :=
  node_ok cuts121 [] 0x28002800281008811c001400088114002081281020812810088108a008812840048014003400208114000481281020810481048114300881048114010481048104a04004 (by decide +kernel)

def state121_5 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_5 : Impossible true (goalAt 121) 5 state121_5.toFinset :=
  node_ok cuts121 [⟨state121_4,exclude121_4⟩] 0x2810088128002081284028002810284028102081088108811c1828401c081408088108811c18088108811408284014082c18048104812081346020812c18346028182081048104812c480481048108811c3008812c481c301430088104810481140880001400400004811400140804810481400040004000208108b02081281020e02810208120e02081281008b02810088120e00881284008b008a0088108b00881284020e02840048108b004811420400004a0048140000481142008b01401400340030488208114082081281034483408208134482081281014081408 (by decide +kernel)

def state121_6 : List Sig := [0xffff0000ffff0000aaaa0000aaaa,input 0,input 6,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_6 : Impossible true (goalAt 121) 4 state121_6.toFinset :=
  node_ok cuts121 [] 0x380028002820280014001400140804812c002800280828000880188008a0088008800c800481088008802800208108800881140818810881048114200481088108812800208128000488088008810880 (by decide +kernel)

def state121_7 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_7 : Impossible true (goalAt 121) 5 state121_7.toFinset :=
  node_ok cuts121 [⟨state121_6,exclude121_6⟩] 0x3081208120a1208114083448344814080881188114180881088120812840088180000881088140011400140014080481048108811430048104812081346004811420048104811420281020c0140820e0140808812840088120c00481142004811420208120c004c80488 (by decide +kernel)

def state121_8 : List Sig := [0xffffffff00000000ffffffffaaaaaaaa,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_8 : Impossible true (goalAt 121) 4 state121_8.toFinset :=
  node_ok cuts121 [] 0x28002800281008811c08088108811408048108811430048104813081281804811400140004814000088108a0088120c0048104a00481140120802080308128100488048808b014083081340820812081 (by decide +kernel)

def state121_9 : List Sig := [0xaaaaaaaaaaaaaaaa,input 0,input 6,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_9 : Impossible true (goalAt 121) 5 state121_9.toFinset :=
  node_ok cuts121 [⟨state121_8,exclude121_8⟩] 0x14083408283014080881188114180881280028002810088114001400140804810481088114300481048128102818048120c0140820e0140808812840088120c00481142004811420208020c0281040031408800014080881284008812840048114200481142020810488 (by decide +kernel)

def state121_10 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_10 : Impossible true (goalAt 121) 5 state121_10.toFinset :=
  node_ok cuts121 [] 0x140828102830140814081c181c1814081400140014080481048128102818048104811c301c30048104811c301c3004810488140808b0048804800480048108900488281020c004880488089008900488048808900890048820811c1814081c1814082810284040020881 (by decide +kernel)

def state121_11 : List Sig := roots 121
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_11 : Impossible true (goalAt 121) 6 state121_11.toFinset :=
  node_ok cuts121 [⟨state121_1,exclude121_1⟩,⟨state121_3,exclude121_3⟩,⟨state121_5,exclude121_5⟩,⟨state121_7,exclude121_7⟩,⟨state121_9,exclude121_9⟩,⟨state121_10,exclude121_10⟩] 0x400330a1140830814003208134482081400330a1344820a14003208114082081400228100881280040012081284028008005281028402810400220810881088140031c18088108814003140818a1188140031c1818a11418400314080881088140002c1804810481400020813460208140002c18346028184000208104810481400314080481140040034000142014004003140814201408400340030481048140002c4804810481400008811c30088140002c481c301430400008810481048140022081048820808004281020c020808003208120c02081400228100488048840034003048804884003140818b014084003800218b008b0400314080488048840010881048808808001284008900880800008810890088140012840048804884000048108900480400014200488048040000481048804814000142008900890 (by decide +kernel)

theorem lower121 : Claim 121 7 :=
  fromSearch 3145731 (by decide +kernel) exclude121_11

def cuts82 : Cuts (goalAt 82) := []

def state82_0 : List Sig := roots 82
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x281009022800210228402800281028402810210209020902210209102100281021402100210221402102281009100910090221400900284009100900090209100902284021402140 (by decide +kernel)

theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 17891392 lower82 (by decide +kernel)


theorem lower83 : Claim 83 5 :=
  fromLift 5 1 68 lower82 (by decide +kernel)


def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x881188108a1088111001100110209100900090009020881118211021103110208800880088109020890091011210890 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 1048644 (by decide +kernel) exclude51_0

def cuts99 : Cuts (goalAt 99) := []

def state99_0 : List Sig := roots 99
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude99_0 : Impossible true (goalAt 99) 3 state99_0.toFinset :=
  node_ok cuts99 [] 0x3081208120a12081210021002102208111001100110221402080208020812102118211021103110211a0112011211120 (by decide +kernel)

theorem lower99 : Claim 99 4 :=
  fromSearch 1048662 (by decide +kernel) exclude99_0

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)

def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower81 none (by decide +kernel)

def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)

def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 (some (1,input 4,input 5)) (by decide +kernel)

def rule115_4 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower51 none (by decide +kernel)

def rule115_5 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower99 none (by decide +kernel)

def rule115_6 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 (some (1,input 5,input 6)) (by decide +kernel)

def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3,rule115_4,rule115_5,rule115_6]

def state115_0 : List Sig := [0xffffffffffffffffffffffffffff0000,input 6,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 4 state115_0.toFinset :=
  node_ok cuts115 [] 0x92009100910111009102810114009101100110011024001089009101121089008a00890089020c00890281020a10890118211021103110228102820281008a108812081 (by decide +kernel)

def state115_1 : List Sig := [0xffffffffffff0000,input 6,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_1 : Impossible true (goalAt 115) 4 state115_1.toFinset :=
  node_ok cuts115 [] 0x9200910091011102100210021022081089009101121089008a00890089020c020802080208121022800280028402081110011001102214011021182110311020881088108a111022810 (by decide +kernel)

def state115_2 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_2 : Impossible true (goalAt 115) 5 state115_2.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_1,exclude115_1⟩] 0x21020910210020812140210021022140210220810910208140011120092008a10910091040010910091008a111201110110221401100400109101100110209101102400121402140208108902080210220c02080208120c0208121020890210211a10890089009104003091011a14001112109100890089008a120c008a028600890089008a108900890286020c020c0118320c01182110208901102118308901103110220c01102281008a12810208128602081281028602810208108a12081400240020881281011023081208180012081281080002810208111022081 (by decide +kernel)

def state115_3 : List Sig := [0x55555555555555555555000055550000,input 4,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_3 : Impossible true (goalAt 115) 4 state115_3.toFinset :=
  node_ok cuts115 [] 0x3080208020a020801100110011020910218020802082208009800880088208800880188008a0088008802080281008800890110218901102089011200910089021022080281020800902088008900880 (by decide +kernel)

def state115_4 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_4 : Impossible true (goalAt 115) 5 state115_4.toFinset :=
  node_ok cuts115 [⟨state115_3,exclude115_3⟩,⟨state115_0,exclude115_0⟩] 0x110228102830110211024002800111021100110011020910091028102140091011200910091011201120091009101120118211021103110208900910112108900890281020c0089020c00890089020c08000089008904000208128401102286011022810284040040881 (by decide +kernel)

def state115_5 : List Sig := [0xffff0000ffff0000ffff00000000,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_5 : Impossible true (goalAt 115) 4 state115_5.toFinset :=
  node_ok cuts115 [] 0x910281011400910090009000902088108900910112108900890281020a1089008800880088109022800280028100881110011001102091011021182110311022081208120a1110208a1 (by decide +kernel)

def state115_6 : List Sig := [0xffffffffffffffffffffffff00000000,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_6 : Impossible true (goalAt 115) 5 state115_6.toFinset :=
  node_ok cuts115 [⟨state115_0,exclude115_0⟩,⟨state115_5,exclude115_5⟩] 0x28300881088120a12840282028302840283020a108810881800108810881110218a11881800018a108a111020881088109021120090008810910090009020910090208811120088140010910091020a12140212040012140114020a109100910110209101100400111201100110211201102400109100910088120c00880090208900880088108900881090220c0090211a10890089009104006091011a14001112109100890089020a108900890283020c020a020a120c020a1283008900890118308901182110218b01102118318b01103110208901102400240022081 (by decide +kernel)

def state115_7 : List Sig := roots 115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude115_7 : Impossible true (goalAt 115) 6 state115_7.toFinset :=
  node_ok cuts115 [⟨state115_2,exclude115_2⟩,⟨state115_4,exclude115_4⟩,⟨state115_6,exclude115_6⟩] 0x400230a1110230814002208140022081400230a1800220a14002208111022081400428100881280040052081284028008001281028402810400420810881088140024002088108814002110218a118814002800018a108a1400211020881088140012102091021004001208121402100400121022140210240012081091020814002110209101100400240011120110040021102112011024002400209100910400109021120090040010881091009004001090209100902400108811120088140002081089020804000210220c020804000208120c02081400021020890210240021183089011824002110218b011024002118318b0110340021102089011024000088120c00880400009020890088040000881089008814000090220c00902400011a1089008904000091040000910400011a1400111214000091008900890 (by decide +kernel)

theorem lower115 : Claim 115 7 :=
  fromSearch 1048644 (by decide +kernel) exclude115_7

def cuts43 : Cuts (goalAt 43) := []

def state43_0 : List Sig := roots 43
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude43_0 : Impossible true (goalAt 43) 3 state43_0.toFinset :=
  node_ok cuts43 [] 0x1400140014080481110011001102140805810481048304811182110211031102048004800481142004880588048a0488 (by decide +kernel)

theorem lower43 : Claim 43 4 :=
  fromSearch 1048659 (by decide +kernel) exclude43_0

def cuts106 : Cuts (goalAt 106) := []

def state106_0 : List Sig := roots 106
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude106_0 : Impossible true (goalAt 106) 3 state106_0.toFinset :=
  node_ok cuts106 [] 0x110221021448110225022102210a21021400140014081102210021002102112011001100110214081120142021481120 (by decide +kernel)

theorem lower106 : Claim 106 4 :=
  fromSearch 17846352 (by decide +kernel) exclude106_0

def cuts75 : Cuts (goalAt 75) := []

def state75_0 : List Sig := roots 75
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude75_0 : Impossible true (goalAt 75) 3 state75_0.toFinset :=
  node_ok cuts75 [] 0x4812081210a048121002100210220810581048104830481208020802081210204800480048120c004880588048a0488 (by decide +kernel)

theorem lower75 : Claim 75 4 :=
  fromSearch 99 (by decide +kernel) exclude75_0

def rule107_0 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower105 none (by decide +kernel)

def rule107_1 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower43 none (by decide +kernel)

def rule107_2 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower106 none (by decide +kernel)

def rule107_3 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower99 none (by decide +kernel)

def rule107_4 : {c : Cut // CutGood (goalAt 107) c} :=
  ruleFor 107 lower75 none (by decide +kernel)

def cuts107 : Cuts (goalAt 107) := [rule107_0,rule107_1,rule107_2,rule107_3,rule107_4]

def state107_0 : List Sig := [0xeeeeeeeeeeeeeeee,input 0,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_0 : Impossible true (goalAt 107) 4 state107_0.toFinset :=
  node_ok cuts107 [] 0x1400140014080481210031001102210021002500048321002080308011032080208024800481208020802100048a208020811408308120810481210a0481208120812100218121002102208020812080 (by decide +kernel)

def state107_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_1 : Impossible true (goalAt 107) 5 state107_1.toFinset :=
  node_ok cuts107 [⟨state107_0,exclude107_0⟩] 0x3081208120a1208104812081210a04811400140014080481218120812102208111811181110214080581048104830481112020812102208121021182110211031102048105820481142011a1058a048a0488208180002081400111021408110214080481142004811420 (by decide +kernel)

def state107_2 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_2 : Impossible true (goalAt 107) 5 state107_2.toFinset :=
  node_ok cuts107 [] 0x3081208120a12081210021002102208111001100110214080581048104830481112011a111a1112004812081250a0481048114811408048114202081210220812102118311021183110204880588048a048804810488142120c020812102208121021183110211831102 (by decide +kernel)

def state107_3 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa,input 0,input 5,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_3 : Impossible true (goalAt 107) 4 state107_3.toFinset :=
  node_ok cuts107 [] 0x210021002102208115001400140214001400340020a114000480248020810480048005800482048004801400110304800481210220810481048104830581048104811400148114001420048004810480 (by decide +kernel)

def state107_4 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_4 : Impossible true (goalAt 107) 5 state107_4.toFinset :=
  node_ok cuts107 [⟨state107_3,exclude107_3⟩] 0x4812081210a04810481148114200481800004810481400321002100210220810581048104830481118111811183214021401120112021403081208120a1208111022081210220812102048114200481142011a0112011211120118330e0110304882081210220812102 (by decide +kernel)

def state107_5 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_5 : Impossible true (goalAt 107) 5 state107_5.toFinset :=
  node_ok cuts107 [] 0x3081208120a120811102118311831102140014001408048104812081346004811420048104811420110011001102140805810481048304812181208120832081112011a111a1112021021183110211831102048114200481142011a1112011a11120208120c021030488 (by decide +kernel)

def state107_6 : List Sig := [0xffccffcc00000000ffccffcc,input 1,input 3,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_6 : Impossible true (goalAt 107) 4 state107_6.toFinset :=
  node_ok cuts107 [] 0x20802080208121021480140014011400118011001101110014003400210a1400110031002102110011001400048311001102208121022081110211031182110204811400150214001408110011021100 (by decide +kernel)

def state107_7 : List Sig := [0xffccffccffccffccffccffccffccffcc,input 1,input 3,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_7 : Impossible true (goalAt 107) 5 state107_7.toFinset :=
  node_ok cuts107 [⟨state107_6,exclude107_6⟩] 0x3081208120a120812080208020812102118211021103110205820582058320c004880588048a048820c00488048820c025022081210a20811502110214081102048121022081210220811102140811021408058325480483112021022081210220811102800011024004 (by decide +kernel)

def state107_8 : List Sig := [0xffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_8 : Impossible true (goalAt 107) 5 state107_8.toFinset :=
  node_ok cuts107 [] 0x4812081210a048104811102110a048104810583058304812080208020812102048004800481142011821102110311020488058a058a04880488058a058a04881102208130a1208114082102208121022081058304810583048111021120140a21402102208121022081 (by decide +kernel)

def state107_9 : List Sig := [0xffffffffffffffffcccccccccccccccc,input 1,input 6,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_9 : Impossible true (goalAt 107) 5 state107_9.toFinset :=
  node_ok cuts107 [] 0x11022102344811021408110211021408140014001408048104812102210a048104810583058304811182110211031102048004800481142021822102210321020488058a058a04880488058a058a04882081110214081102140805830481058304812102214020831120 (by decide +kernel)

def state107_10 : List Sig := [0xffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_10 : Impossible true (goalAt 107) 5 state107_10.toFinset :=
  node_ok cuts107 [] 0x210021002102208115081408140a140811201420254811202140112011202140208020802081210204880588048a04880488140830e0048814a004880488142020c00488048820c01408208130a120811102250a2081250a208114081420110a0481250a2081250a2081 (by decide +kernel)

def state107_11 : List Sig := [0x55555555555555555500550055005500,input 3,input 6,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_11 : Impossible true (goalAt 107) 4 state107_11.toFinset :=
  node_ok cuts107 [] 0x3080208020a02080110011001102140821802080208220800580048004820480048014801408048004802080210a048004881102140811020488048a0588048821022080248820801420048004880480 (by decide +kernel)

def state107_12 : List Sig := [0xffffffffffffffffff00ff00ff00ff00,input 3,input 6,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_12 : Impossible true (goalAt 107) 5 state107_12.toFinset :=
  node_ok cuts107 [⟨state107_11,exclude107_11⟩] 0x11023408144811021102140814081102110011001102140825082508250a112011202540214811201120214021401120118211021103110204880588048a04880488248820c0048820c00488048820c0800004880488400220811408110214081102250a3460210a0481 (by decide +kernel)

def state107_13 : List Sig := [0x33333333333333333333333300000000,input 5,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_13 : Impossible true (goalAt 107) 4 state107_13.toFinset :=
  node_ok cuts107 [] 0x250021002108210015001100110811000480048004811420218021002101210011801100110111001100210020a1110011200481142004811120048811a0048820812100312021001408110011201100 (by decide +kernel)

def state107_14 : List Sig := [0xffffffffffffffffffffffff00000000,input 5,input 6,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_14 : Impossible true (goalAt 107) 5 state107_14.toFinset :=
  node_ok cuts107 [⟨state107_13,exclude107_13⟩] 0x481342014600481048114201420048104811420142004810581048104830481112031202140112021401120112021408000112011204000048004800481142004880588048a0488048830a030a10488048830c020e00488048820c020c00488208130a1344820a11102 (by decide +kernel)

def state107_15 : List Sig := roots 107
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude107_15 : Impossible true (goalAt 107) 6 state107_15.toFinset :=
  node_ok cuts107 [⟨state107_1,exclude107_1⟩,⟨state107_2,exclude107_2⟩,⟨state107_4,exclude107_4⟩,⟨state107_5,exclude107_5⟩,⟨state107_7,exclude107_7⟩,⟨state107_8,exclude107_8⟩,⟨state107_9,exclude107_9⟩,⟨state107_10,exclude107_10⟩,⟨state107_12,exclude107_12⟩,⟨state107_14,exclude107_14⟩] 0x400130a1110230814004208134482081800930a1344820a140012081110220814001250a0481048140032081346020818008250a3460210a4001208104810481400414080481140040031102142014008007140814201408400411020481048140012102112021004000208121402100800621022140210240012081112020814004110221401100400014081120110080051102112011024004140821401408400305831120058140000481254804818004058325480483400304811120048140012081048820804002210220c020808003208120c02081400121020488210240041183048811824002110230e011028002118330e0110340041102048811024003048120c00480400214200488048080010481048804814003142020c01420400011a10488048840021120058a0588800011a1058a048a4000112004880488 (by decide +kernel)

theorem lower107 : Claim 107 7 :=
  fromSearch 1048659 (by decide +kernel) exclude107_15

def cuts27 : Cuts (goalAt 27) := []

def state27_0 : List Sig := roots 27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude27_0 : Impossible true (goalAt 27) 3 state27_0.toFinset :=
  node_ok cuts27 [] 0x4810881090a0481090009000902088105810481048304810880088008810902048004800481089004880588048a0488 (by decide +kernel)

theorem lower27 : Claim 27 4 :=
  fromSearch 67 (by decide +kernel) exclude27_0

def rule91_0 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 none (by decide +kernel)

def rule91_1 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower82 none (by decide +kernel)

def rule91_2 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower83 none (by decide +kernel)

def rule91_3 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 (some (1,input 3,input 4)) (by decide +kernel)

def rule91_4 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 (some (1,input 3,input 6)) (by decide +kernel)

def rule91_5 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower27 none (by decide +kernel)

def rule91_6 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower75 none (by decide +kernel)

def cuts91 : Cuts (goalAt 91) := [rule91_0,rule91_1,rule91_2,rule91_3,rule91_4,rule91_5,rule91_6]

def state91_0 : List Sig := [0xffffffffffffffffffffff00ffffff00,input 6,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_0 : Impossible true (goalAt 91) 4 state91_0.toFinset :=
  node_ok cuts91 [] 0x9080908090a214021082108210a0910058104810483048104880588048a048804880888049004880488208804c004880480048004814001280828082810090a08812081 (by decide +kernel)

def state91_1 : List Sig := [0xffffff00ffffff00,input 6,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_1 : Impossible true (goalAt 91) 4 state91_1.toFinset :=
  node_ok cuts91 [] 0x9080908090a2140210021002102208104880588048a0488048808880490048820802080208121022800280028402081048105810483048104800480048120c004810881090a0481210a (by decide +kernel)

def state91_2 : List Sig := [0xffffff00ffffff00ffffff00ffffff00,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_2 : Impossible true (goalAt 91) 5 state91_2.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_1,exclude91_1⟩] 0x210209102100208121402100210221402102208109102081090a21400908284809100908090a0910090a284821402140058321400581048109100481058309100483048121400481208104882080210220c02080208120c020812102048821024003048804880910058a05884001058a048a091004880488400104880488090a08900888400108900490090a04880488048120c00480400104880480048104880481400120c020c02810090a28082081284820812810284828102081090a2081400240020881250a04810481208180012081250a8000210a208104810481 (by decide +kernel)

def state91_3 : List Sig := [0xffff0000ffff0000ff000000ff00,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_3 : Impossible true (goalAt 91) 4 state91_3.toFinset :=
  node_ok cuts91 [] 0x21082108210a0910090009000902088104880588048a04880488208804c00488088008800881090228002800281008810481058104830481048004800481089004812081210a0481090a (by decide +kernel)

def state91_4 : List Sig := [0xffffffffffffffffff00ff00ff00ff00,input 6,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_4 : Impossible true (goalAt 91) 5 state91_4.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_3,exclude91_3⟩] 0x281808810881210a28402808281828402818210a0881088180010881088104810d0a048180000d0a090a048108810481090221400900088109100900090209100902088121400881210a09102108281821402108210a2140210a28180910091005830910058104810d18048105830d1804830481091004810881048808800902089008800881089008810902048809024004048804880910058a05884001058a048a091004880488400104880488210a20c02088400120c004c0210a04880488048108900480400104880480048104880481400108900890400240022081 (by decide +kernel)

def state91_5 : List Sig := [0x33333333333333333333000033330000,input 4,input 6,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_5 : Impossible true (goalAt 91) 4 state91_5.toFinset :=
  node_ok cuts91 [] 0x25002100210821000d000900090809000480048004810890218021002101210009800900090109000900210028100900091004810d100481089004880890048820812100281021000881090009100900 (by decide +kernel)

def state91_6 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_6 : Impossible true (goalAt 91) 5 state91_6.toFinset :=
  node_ok cuts91 [⟨state91_5,exclude91_5⟩,⟨state91_0,exclude91_0⟩] 0x481281028180481048128402848048104814002800104810581048104830481091028102140091021400910091021408000091009104000048004800481089004880588048a04880488281020c004880488089008900488048808900890048820812810284040050881 (by decide +kernel)

def state91_7 : List Sig := roots 91
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_7 : Impossible true (goalAt 91) 6 state91_7.toFinset :=
  node_ok cuts91 [⟨state91_2,exclude91_2⟩,⟨state91_4,exclude91_4⟩,⟨state91_6,exclude91_6⟩] 0x40052810088128004006208128402800800228102840281040052081088108814002250a0481048140022081400220814002250a8001210a400220810481048140020d0a04810481400208814002088140020d0a8000090a4002088104810481400021020910210040002081214021004000210221402102400020810910208140000902214009004000088109100900400009020910090240000881214008814002058309100581400204810d180481400205830d180483400204810910048140012081048820804001210220c020804001208120c02081400121020488210240010881048808804001090208900880400108810890088140010902048809024002048108900480400240010488048040020481048804814002400208900890400040000488048840000910058a058840004001058a048a4000091004880488 (by decide +kernel)

theorem lower91 : Claim 91 7 :=
  fromSearch 67 (by decide +kernel) exclude91_7

def cuts58 : Cuts (goalAt 58) := []

def state58_0 : List Sig := roots 58
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude58_0 : Impossible true (goalAt 58) 3 state58_0.toFinset :=
  node_ok cuts58 [] 0x90211021418090214001400140811020d020902090a09021100110011021408090009000902112009100d1009180910 (by decide +kernel)

theorem lower58 : Claim 58 4 :=
  fromSearch 1134656 (by decide +kernel) exclude58_0

def rule59_0 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower57 none (by decide +kernel)

def rule59_1 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower43 none (by decide +kernel)

def rule59_2 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower58 none (by decide +kernel)

def rule59_3 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower51 none (by decide +kernel)

def rule59_4 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower27 none (by decide +kernel)

def cuts59 : Cuts (goalAt 59) := [rule59_0,rule59_1,rule59_2,rule59_3,rule59_4]

def state59_0 : List Sig := [0xeeee0000eeee0000eeee0000eeee,input 0,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_0 : Impossible true (goalAt 59) 4 state59_0.toFinset :=
  node_ok cuts59 [] 0x1400140014080481090019001102090009000d0004830900088018801103088008800c800481088008800900048a088008811408188108810481090a0481088108810900098109000902088008810880 (by decide +kernel)

def state59_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 1,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_1 : Impossible true (goalAt 59) 5 state59_1.toFinset :=
  node_ok cuts59 [⟨state59_0,exclude59_0⟩] 0x881188114180881140014001408048104810881090a0481118111811102140809810881090208810581048104830481091011821102110311020881090208810902048105820481142011a1058a048a0488110214081102140808818000088140010481142004811420 (by decide +kernel)

def state59_2 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_2 : Impossible true (goalAt 59) 5 state59_2.toFinset :=
  node_ok cuts59 [] 0x88118811418088111001100110214080900090009020881058104810483048109100d180d1809100481148114080481048108810d0a048114201183110211831102088109020881090204880588048a0488048104880898089011831102118311020881090208810902 (by decide +kernel)

def state59_3 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_3 : Impossible true (goalAt 59) 5 state59_3.toFinset :=
  node_ok cuts59 [] 0x1400140014080481048108811c30048114200481048114201100110011021408058104810483048109810881088308811120091009101120088118811c1808810902118311021183110204810c90048108900890091011a1089008810890090304881183110211831102 (by decide +kernel)

def state59_4 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa,input 0,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_4 : Impossible true (goalAt 59) 4 state59_4.toFinset :=
  node_ok cuts59 [] 0x1c001400141014000900090009020881150014001402140004800c8008810480048005800482048004801400110304800481090208810481048104830581048104811400148114000890048004810480 (by decide +kernel)

def state59_5 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_5 : Impossible true (goalAt 59) 5 state59_5.toFinset :=
  node_ok cuts59 [⟨state59_4,exclude59_4⟩] 0x881188108a10881090208810881090204810881090a048104811481142004818000048104814003090009000902088105810481048304811181118111830910091011201120091011020881090208810902048114200481142011a0091011210910118318b011030488 (by decide +kernel)

def state59_6 : List Sig := [0xffccffcc00000000ffccffcc,input 1,input 3,input 0,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_6 : Impossible true (goalAt 59) 4 state59_6.toFinset :=
  node_ok cuts59 [] 0x8800880088109021480140014011400118011001101110014001c00090a1400110019000902110011001400048311000902088109020881110211031182110204811400150214001408110011021100 (by decide +kernel)

def state59_7 : List Sig := [0xffccffccffccffccffccffccffccffcc,input 1,input 3,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_7 : Impossible true (goalAt 59) 5 state59_7.toFinset :=
  node_ok cuts59 [⟨state59_6,exclude59_6⟩] 0x88118811418088111821102110311020880088008810902058205820583089004880588048a0488089004880488089015021102140811020d020881090a088104811102140811021408090208810902088105830d180483091011028000110240040902088109020881 (by decide +kernel)

def state59_8 : List Sig := [0xffffccccffffccccffffccccffffcccc,input 1,input 4,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_8 : Impossible true (goalAt 59) 5 state59_8.toFinset :=
  node_ok cuts59 [] 0x140014001408048104810902090a048104810583058304811182110211031102048004800481089009820902090309020488058a058a04880488058a058a0488090211021c18090208811102140811021408058304810583048109020910088311201102140811021408 (by decide +kernel)

def state59_9 : List Sig := [0xffffffffccccccccffffffffcccccccc,input 1,input 5,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_9 : Impossible true (goalAt 59) 5 state59_9.toFinset :=
  node_ok cuts59 [] 0x881110218a10881088109020902088104810881090a048104811102110a048104810583058304810880088008810902048004800481089011821102110311020488058a058a04880488058a058a048814080902088109020881058304810583048111021120140a0910 (by decide +kernel)

def state59_10 : List Sig := [0x55555500555555005555550055555500,input 3,input 4,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_10 : Impossible true (goalAt 59) 4 state59_10.toFinset :=
  node_ok cuts59 [] 0x1100110011021408098008800882088005800480048204800880188014180880048014801408048004800880090a048004881102140811020488048a05880488090208800c8808800890048004880480 (by decide +kernel)

def state59_11 : List Sig := [0xffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_11 : Impossible true (goalAt 59) 5 state59_11.toFinset :=
  node_ok cuts59 [⟨state59_10,exclude59_10⟩] 0x11001100110214080d080d080d0a112009100d10091809101120091009101120118211021103110204880588048a048804880c8808900488089004880488089080000488048840021c08110214181102088114081102140811020d0a1c30090a04811408110214081102 (by decide +kernel)

def state59_12 : List Sig := [0xffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_12 : Impossible true (goalAt 59) 5 state59_12.toFinset :=
  node_ok cuts59 [] 0x88114081418088108810d0a0d0a0881090009000902088115081408140a140809100d180d18091009100d180d180910088008800881090204880588048a04880488140818b004880890048804880890089004880488089011020d0a08810d0a088114081420110a0481 (by decide +kernel)

def state59_13 : List Sig := [0x33333333333300003333333333330000,input 4,input 5,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_13 : Impossible true (goalAt 59) 4 state59_13.toFinset :=
  node_ok cuts59 [] 0x15001100110811000d000900090809000480048004810890118011001101110009800900090109000900110014180900091004810d100481089004880890048814081100191011000881090009100900 (by decide +kernel)

def state59_14 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_14 : Impossible true (goalAt 59) 5 state59_14.toFinset :=
  node_ok cuts59 [⟨state59_13,exclude59_13⟩] 0x4811c101c18048104811c201430048104811420142004810581048104830481091019101120091011200910091011208000091009104000048004800481089004880588048a04880488189008b004880488089008900488048808900890048811021c1818a114180881 (by decide +kernel)

def state59_15 : List Sig := roots 59
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_15 : Impossible true (goalAt 59) 6 state59_15.toFinset :=
  node_ok cuts59 [⟨state59_1,exclude59_1⟩,⟨state59_2,exclude59_2⟩,⟨state59_3,exclude59_3⟩,⟨state59_5,exclude59_5⟩,⟨state59_7,exclude59_7⟩,⟨state59_8,exclude59_8⟩,⟨state59_9,exclude59_9⟩,⟨state59_11,exclude59_11⟩,⟨state59_12,exclude59_12⟩,⟨state59_14,exclude59_14⟩] 0x40041c18088108814001110218a1188180091c1818a114184004110208810881400414080481140040031102142014008008140814201408400411020481048140010d0a04810481400308811c30088180070d0a1c30090a4001088104810481400411020910110040001408112011008006110211201102400414080910140840010902112009004000088109100900800509020910090240010881112008814003058309100581400004810d180481800405830d180483400304810910048140041183048811824002110218b011028003118318b01103400411020488110240010881048808804002090208900880800208810890088140010902048809024003048108900480400214200488048080010481048804814003142008900890400011a10488048840020910058a0588800011a1058a048a4000091004880488 (by decide +kernel)

theorem lower59 : Claim 59 7 :=
  fromSearch 1048643 (by decide +kernel) exclude59_15

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)

def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)

def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 none (by decide +kernel)

def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)

def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)

def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4]

def state123_0 : List Sig := roots 123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 8 state123_0.toFinset :=
  node_ok cuts123 [] 0x400430a1110230814004208134482081400430a1344820a14004208111022081400428100881280040042081284028004004281028402810400420810881088140031c18088108814003110218a1188140031c1818a1141840031102088108814004250a0481048140042081346020814004250a3460210a4004208104810481400314080481140040031102142014004003140814201408400311020481048140020d0a04810481400208811c30088140020d0a1c30090a40020881048104814004210209102100400420812140210040042102214021024004208109102081400311020910110040031408112011004003110211201102400314080910140840020902112009004002088109100900400209020910090240020881112008814001058309100581400104810d180481400105830d180483400104810910048140042081048820804004210220c020804004208120c02081400421020488210240031183048811824003110218b011024003118318b01103400311020488110240020881048808804002090208900880400208810890088140020902048809024001048108900480400114200488048040010481048804814001142008900890400011a10488048840000910058a0588400011a1058a048a4000091004880488 (by decide +kernel)

theorem lower123 : Claim 123 9 :=
  fromSearch 1048643 (by decide +kernel) exclude123_0

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 127
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6]
def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The four products cover the eleven listed edges.
def smallCircuit : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[0,7]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,3]⟩, ⟨.and,[8,4]⟩, ⟨.and,[9,5]⟩, ⟨.and,[10,6]⟩, ⟨.or,[11,12]⟩, ⟨.or,[13,14]⟩, ⟨.or,[15,16]⟩], 17⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 11 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := roots 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (1 <<< ([3, 4, 4, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 0, 1, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 9 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 11 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

-- Input 2 is essential and vanishes on this restriction. Any computation
-- using at most nine binary gates would give at most eight on the six inputs.
theorem lowerGraph : Impossible true graph 9 sevenInputs.toFinset :=
  (ruleFor 127 lower123 none (by decide +kernel)).property 9 sevenInputs
    (by decide +kernel) (by decide +kernel)



end PEqualNP.Outside.L_meta_11317

open PEqualNP.Outside.L_meta_11317 in
theorem PEqualNP.Outside.L_meta_11317 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
