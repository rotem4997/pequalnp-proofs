import PEqualNP.Defs

-- The displayed monotone circuit uses fourteen gates. For the lower bound,
-- complements are free: a circuit for the target still needs thirteen binary
-- gates. The search checks the necessary live wires and restrictions to cliques.
-- The live-circuit framework and the four- and five-input clique bounds
-- adapt the project proofs L_meta_8449 and L_meta_8724 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_10454_aux.LiveCircuits
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
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
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
def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
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




end PEqualNP.Outside.L_meta_10454_aux.LiveCircuits

namespace PEqualNP.Outside.L_meta_10454_aux.FiveInputBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 512 rows at once, NOT gates cost nothing.
def ins_fffefee8 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082, 0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104, 0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208, 0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410, 0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]

theorem spec_fffefee8 : ∀ j : Fin 512, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (ins_fffefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

-- A live run mapped through a bitwise homomorphism is a build of the mapped goal; a wire
-- mapped to zero saves its gate.
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

-- Fixing input i to zero (restriction i) leaves the same four-input search, which fails at six.
def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4exact : search 6 k4inputs = false := by decide +kernel

def vinput (i : Fin 5) : W := ins_fffefee8.getD i.val 0

def pairIx : Fin 5 → List ℕ := ![[12, 14, 15, 16, 17, 30, 32, 33, 34, 35, 42, 44, 45, 46, 47, 54, 56, 57, 58, 59, 72, 74, 75, 76, 77, 84, 86, 87, 88, 89, 96, 98, 99, 100, 101, 108, 110, 111, 112, 113, 120, 122, 123, 124, 125, 132, 134, 135, 136, 137, 144, 146, 147, 148, 149],
[6, 7, 9, 10, 11, 24, 25, 27, 28, 29, 42, 43, 45, 46, 47, 48, 49, 51, 52, 53, 66, 67, 69, 70, 71, 84, 85, 87, 88, 89, 90, 91, 93, 94, 95, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 132, 133, 135, 136, 137, 138, 139, 141, 142, 143],
[0, 1, 2, 4, 5, 24, 25, 26, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 66, 67, 68, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131],
[0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 66, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 107],
[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64]]

def sourceRow (i : Fin 5) (j : Fin 512) : Fin 512 :=
  ⟨((if j.val < 256 then 0 else 256) + (pairIx i).getD ((j.val % 256) % 55) 0) % 512,
    Nat.mod_lt _ (by decide)⟩

def restriction (i : Fin 5) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(sourceRow i k).val]))).cast List.length_ofFn

theorem restriction_bit (i : Fin 5) (w : W) (j : ℕ) (hj : j < 512) :
    (restriction i w)[j] = w[(sourceRow i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [restriction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
theorem restriction_not (i : Fin 5) (u : W) : restriction i (~~~u) = ~~~restriction i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_not]

theorem restriction_ops (i : Fin 5) (a b z : W) (hz : z ∈ basicOps a b) :
    restriction i z ∈ basicOps (restriction i a) (restriction i b) := by
  have hand (u v : W) : restriction i (u &&& v) = (restriction i u &&& restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_and]
  have hor (u v : W) : restriction i (u ||| v) = (restriction i u ||| restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, restriction_not]

def remaining (i : Fin 5) : List W :=
  ((List.finRange 5).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 5, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 5, restriction i goal = goal := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_nd : ∀ i : Fin 5, (remaining i).Nodup := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_same : ∀ i : Fin 5, remaining i = k4inputs := by decide +kernel

theorem remaining_reject (i : Fin 5) : search 6 (remaining i) = false := by
  rw [remaining_same]
  exact k4exact

set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ ins_fffefee8, ∃ i : Fin 5, vinput i = w := by
  intro w hw
  simp only [ins_fffefee8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩

theorem restricted_available : ∀ i j : Fin 5, holds (remaining i).toFinset (restriction i (vinput j)) := by
  intro i j
  by_cases h : i = j
  · subst j
    exact Or.inl (projected_input i)
  · right; right
    exact ⟨_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, by simp [Ne.symm h],rfl⟩), Or.inl rfl⟩

-- The first gate, on inputs i and j, does not separate some pair that only input i separates,
-- so input i stays live after it.
def changes (w : W) (r : Fin 256) : Bool :=
  w.getLsbD (256+r.val) != w.getLsbD r.val

set_option maxRecDepth 8000 in
theorem separating_pair : ∀ i j : Fin 5, i ≠ j → ∀ op : Fin 4, ∃ r : Fin 256,
    changes ((ops (vinput i) (vinput j)).getD op.val 0) r = false ∧
    ∀ q : Fin 5, q ≠ i → changes (vinput q) r = false := by decide +kernel

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

theorem unchanged (w : W) (r : Fin 256) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem input_not_goal : ∀ i : Fin 5, vinput i ≠ goal ∧ vinput i ≠ ~~~goal := by decide +kernel

theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel

theorem restricted_new (i j : Fin 5) (z : W) (hz : z ∈ basicOps (vinput i) (vinput j)) :
    holds (remaining i).toFinset (restriction i z) := by
  exact mem_ops_zero (restricted_available i i) (restricted_available i j)
    (Or.inl (projected_input i))
    (restriction_ops i _ _ _ hz)

theorem raw_present {t : W} (ht : t = goal ∨ t = ~~~goal) (i j : Fin 5) (hij : i ≠ j)
    {z : W} (hz : z ∈ basicOps (vinput i) (vinput j)) (rest : Finset W)
    (hsub : rest ⊆ ins_fffefee8.toFinset)
    (h : live basicOps t 7 (insert z rest)) : vinput i ∈ rest := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  obtain ⟨r, hrz, hrq⟩ := separating_pair i j hij o
  rw [ho] at hrz
  have hd : differs r t := by
    rcases ht with rfl|rfl
    · exact (goal_changes r).1
    · exact (goal_changes r).2
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) h
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact False.elim (unchanged _ _ hrz hdw)
  · obtain ⟨q,rfl⟩ := input_index _ (List.mem_toFinset.mp (hsub hw))
    by_contra hn
    have qi : q ≠ i := by intro eq; exact hn (eq ▸ hw)
    exact unchanged _ _ (hrq q qi) hdw

set_option maxRecDepth 4000 in
theorem projected_impossible (i : Fin 5) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (h : SignedBuild 6 (remaining i).toFinset (restriction i t)) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have signs : restriction i t = goal ∨ restriction i t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact Or.inl (projected_goal i)
    · exact Or.inr (by rw [restriction_not, projected_goal])
  have opposite : ~~~restriction i t = goal ∨ ~~~restriction i t = ~~~goal := by
    rcases signs with h|h <;> simp [h]
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (run : build basicOps u 6 (remaining i).toFinset) : False := by
    have hit := search_complete hu 6 (remaining i) (remaining_nd i) run
    exact Bool.noConfusion ((remaining_reject i).symm.trans hit)
  rcases h with c | c | run | run
  · rcases signs with h|h
    · exact ne.1 (h.symm.trans c)
    · exact ne.2.2.1 (h.symm.trans c)
  · rcases signs with h|h
    · exact ne.2.1 (h.symm.trans c)
    · exact ne.2.2.2 (h.symm.trans c)
  · exact no signs run
  · exact no opposite run

theorem no_eight_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 ins_fffefee8.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl|rfl
    · exact (input_not_goal i).1 hi
    · exact (input_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput eq)
    have sub : rest ⊆ ins_fffefee8.toFinset := by
      intro u hu
      exact hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have keep := raw_present ht i j hij hz rest sub tail
    have pg : vinput i ≠ t := by rcases ht with rfl|rfl; exact (input_not_goal i).1; exact (input_not_goal i).2
    apply projected_impossible i t ht
    apply live_transport_save (restriction_ops i)
      tail (Finset.mem_insert_of_mem keep) pg (projected_input i)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact restricted_new i j w hz
    · obtain ⟨k,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hw))
      exact restricted_available i k


end PEqualNP.Outside.L_meta_10454_aux.FiveInputBounds

namespace PEqualNP.Outside.L_meta_10454_aux.GraphTarget
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits

def cols7 : List Sig := inputs.take 7
def full : Sig := 0xfffffffffffffffefffffffefffefea0fffffffffffffffefffffffefffefea0fffffffffffffffefffffffefffefea0fffffffffffffffefffffffefffefea0

end PEqualNP.Outside.L_meta_10454_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit
open PEqualNP.CircuitLowerBounds

def upper : Circuit :=
  ⟨[⟨.or, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [15, 2]⟩,
    ⟨.and, [0, 2]⟩,
    ⟨.and, [9, 16]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem upperComputes : ∀ x : Fin 7 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel

theorem upperLegal : ∀ g ∈ upper.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem upperSize : upper.gates.length = 14 := rfl
end PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit

namespace PEqualNP.Outside.L_meta_10454_aux.CliqueBounds
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits
open PEqualNP.Outside.L_meta_10454_aux.FiveInputBounds

theorem convert {T : Sig} {k : Nat} {S : Finset Sig}
    (h : Live true T k S) {av : Finset Sig} (sub : S ⊆ av) : build basicOps T k av := by
  induction h using Live.ind generalizing av with
  | stop hp => exact sub (Finset.mem_singleton_self T)
  | @binary k U a b d hd ha hb hab hf ht ih =>
    have op : bin d a b ∈ basicOps a b := by
      rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [bin,basicOps,ops,BitVec.and_comm]
    apply Or.inr
    refine ⟨a,sub (by simp),b,sub (by simp),hab,bin d a b,op,ih ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (sub (by simp [hw]))

theorem buildLift {T : Sig} {A : Finset Sig} {k l : Nat} (h : k ≤ l)
    (g : build basicOps T k A) : build basicOps T l A := by
  induction h with
  | refl => exact g
  | step _ ih => exact Or.inl ih

theorem packedLower5 : Lower true ins_fffefee8 goal 9 := by
  intro p bank h hit
  have pT : proper goal := by unfold proper; decide +kernel
  have gT : plainWord goal = true := by decide +kernel
  have pR : ins_fffefee8.all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,hs⟩ := reach_live pT gT pR h hit
  by_contra! hlow
  apply no_eight_binary goal (.inl rfl)
  apply buildLift (by omega : k ≤ 8)
  exact convert run (fun w hw => List.mem_toFinset.mpr (hs w hw))

def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def packedRow (j : Row) : Row :=
  ⟨(List.range 5 |>.foldl (fun acc q => acc + if bit j (ins_fffefee8.getD q 0) then 2^q else 0) 0) % 512, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4000 in
theorem rowTable : ∀ j : Row, bit (packedRow j) k5 = bit j goal := by decide +kernel

set_option maxRecDepth 4000 in
theorem rowInputs : ∀ q : Fin 5, ∀ j : Row, bit (packedRow j) (inputs.getD q.val 0) = bit j (ins_fffefee8.getD q.val 0) := by decide +kernel

set_option maxRecDepth 12000 in
theorem standardLower5 : Lower true (inputs.take 5) k5 9 := by
  have hT : proper k5 := by unfold proper; decide +kernel
  have hN : plainWord k5=true := by decide +kernel
  have hR : (inputs.take 5).all plainWord =true := by decide +kernel
  have pT : proper goal := by unfold proper; decide +kernel
  have eq : rename packedRow k5 = goal := bit_ext fun j => (bit_rename _ _ _).trans (rowTable j)
  have supp : ∀ a ∈ inputs.take 5, Available true (ins_fffefee8.map observe) (observe (rename packedRow a)) := by
    intro a ha
    have asList : inputs.take 5 = List.ofFn (fun q : Fin 5 => inputs.getD q.val 0) := rfl
    rw [asList, List.mem_ofFn] at ha
    obtain ⟨q,rfl⟩ := ha
    have same : rename packedRow (inputs.getD q.val 0) = ins_fffefee8.getD q.val 0 :=
      bit_ext fun j => (bit_rename _ _ _).trans (rowInputs q j)
    have mem : ∀ q : Fin 5, ins_fffefee8.getD q.val 0 ∈ ins_fffefee8 := by decide +kernel
    rw [same]
    exact Or.inl (List.mem_map_of_mem (mem q))
  simpa using lower_slice hT hN hR pT packedRow eq supp ∅ (by simp) (by simp) 9 packedLower5

theorem packedLower4 : Lower true k4inputs goal 7 := by
  intro p bank h hit
  have pT : proper goal := by unfold proper; decide +kernel
  have gT : plainWord goal = true := by decide +kernel
  have pR : k4inputs.all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,hs⟩ := reach_live pT gT pR h hit
  by_contra! hlow
  have hb := convert run (av := k4inputs.toFinset) (fun w hw => List.mem_toFinset.mpr (hs w hw))
  have hbad := search_complete (Or.inl (Eq.refl goal)) 6 k4inputs (by decide +kernel) (buildLift (by omega : k ≤ 6) hb)
  exact Bool.noConfusion (k4exact.symm.trans hbad)

def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def packedRow4 (j : Row) : Row :=
  ⟨(List.range 4 |>.foldl (fun acc q => acc + if bit j (k4inputs.getD q 0) then 2^q else 0) 0) % 512, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4000 in
theorem rowTable4 : ∀ j : Row, bit (packedRow4 j) k4 = bit j goal := by decide +kernel

set_option maxRecDepth 4000 in
theorem rowInputs4 : ∀ q : Fin 4, ∀ j : Row, bit (packedRow4 j) (inputs.getD q.val 0) = bit j (k4inputs.getD q.val 0) := by decide +kernel

set_option maxRecDepth 12000 in
theorem standardLower4 : Lower true (inputs.take 4) k4 7 := by
  have hT : proper k4 := by unfold proper; decide +kernel
  have hN : plainWord k4=true := by decide +kernel
  have hR : (inputs.take 4).all plainWord =true := by decide +kernel
  have pT : proper goal := by unfold proper; decide +kernel
  have eq : rename packedRow4 k4 = goal := bit_ext fun j => (bit_rename _ _ _).trans (rowTable4 j)
  have supp : ∀ a ∈ inputs.take 4, Available true (k4inputs.map observe) (observe (rename packedRow4 a)) := by
    intro a ha
    have asList : inputs.take 4 = List.ofFn (fun q : Fin 4 => inputs.getD q.val 0) := rfl
    rw [asList, List.mem_ofFn] at ha
    obtain ⟨q,rfl⟩ := ha
    have same : rename packedRow4 (inputs.getD q.val 0) = k4inputs.getD q.val 0 :=
      bit_ext fun j => (bit_rename _ _ _).trans (rowInputs4 q j)
    have mem : ∀ q : Fin 4, k4inputs.getD q.val 0 ∈ k4inputs := by decide +kernel
    rw [same]
    exact Or.inl (List.mem_map_of_mem (mem q))
  simpa using lower_slice hT hN hR pT packedRow4 eq supp ∅ (by simp) (by simp) 7 packedLower4

end PEqualNP.Outside.L_meta_10454_aux.CliqueBounds

namespace PEqualNP.Outside.L_meta_10454_aux.GraphTarget
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def sample7 (r : Row) (j : Fin 7) := bit r (cols7.getD j.val zero)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenTable : ∀ r : Row, bit r full = PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.target (sample7 r) := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenList : List.ofFn (fun i : Fin 7 => cols7.getD i.val zero) = cols7 := rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem sevenSampled (r : Row) : List.ofFn (sample7 r) = cols7.map (bit r) := by
  rw [←sevenList,List.map_ofFn]; rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem eval7 (C : Circuit) (h : FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cols7).getD i zero) =
      (C.wires (List.ofFn (sample7 r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem binaryLower (low : Lower true cols7 full 13) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.target x) :
    13 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have goalEq : (execute C.gates cols7).getD C.output zero = full := by
    apply bit_ext
    intro r
    exact (eval7 C legal C.output r).trans ((computes (sample7 r)).trans (sevenTable r).symm)
  have rep := get_rep (u:=true) (execute C.gates cols7) C.output
  rw [goalEq] at rep
  unfold PEqualNP.Outside.L_meta_10454_aux.LiveCircuits.Repr at rep
  have pg : bit 0 full = false := by decide +kernel
  have pfull : proper full := by unfold proper; decide +kernel
  rw [nrm_id pg] at rep
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates cols7 legal (by simp) pfull (rep.resolve_right (fun h => h pfull))
  have plain : cols7.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have rs := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hs : supply true (cols7.map observe) ((S.toList.map observe).map (restrictRows (id : Row → Row))) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  have b := projected_bound (id : Row → Row) rs (observe_proper pfull) Reach.start hs (L:=13) low
  omega
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem gateLower (low : Lower true cols7 full 13) (C : Circuit) (legal : FanInTwo C)
    (negUsed : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.target x) :
    14 ≤ C.gates.length := by
  obtain ⟨g,hg,ng⟩ := negUsed
  have hc := binaryLower low C legal computes
  by_contra! h
  have all := (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length (by omega : C.gates.length ≤ C.gates.countP (fun g => !isNot g)))) g hg
  simp [isNot,ng] at all


theorem finish (low : Lower true cols7 full 13) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _uniq computes
  change ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.target x at computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have hl : FanInTwo ⟨gates,o⟩ := by
      intro g hg
      obtain ⟨ht,hw⟩ := legal g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht, hw⟩
    have hs := gateLower low ⟨gates,o⟩ hl hn computes
    refine ⟨PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.upper.gates, PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.upper.output, PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.upperLegal, ?_, ?_⟩
    · exact hs
    · intro x
      exact PEqualNP.Outside.L_meta_10454_aux.ExplicitCircuit.upperComputes x
  · refine ⟨gates,o,?_,Nat.le_refl _,computes⟩
    intro g hg
    obtain ⟨hor,hw⟩ := legal g hg
    rcases hor with ha | ho | hnot
    · exact ⟨Or.inl ha,hw⟩
    · exact ⟨Or.inr ho,hw⟩
    · exact (hn ⟨g,hg,hnot⟩).elim
end PEqualNP.Outside.L_meta_10454_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_10454_aux.GraphSymmetry
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits
abbrev T := PEqualNP.Outside.L_meta_10454_aux.GraphTarget.full
abbrev ws0 := PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7
def low (s : Fin 7) : Sig :=
  match s.val with
  | 0 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
  | 1 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
  | 2 => 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
  | 3 => 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000
  | 5 => 0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000
  | _ => 0xffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff00000000
def high (s : Fin 7) : Sig :=
  match s.val with
  | 0 => 0x50505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050
  | 1 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
  | 2 => 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
  | 3 => 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000
  | 5 => 0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000
  | _ => 0xffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff0000000000000000
def shiftN (s : Fin 7) : Nat :=
  match s.val with
  | 0 => 3
  | 1 => 8
  | 2 => 24
  | 3 => 56
  | 4 => 16
  | 5 => 48
  | _ => 32
def plan (p : Fin 48) : List (Fin 7) :=
  match p.val with
  | 0 => []
  | 1 => [6]
  | 2 => [4]
  | 3 => [5, 6]
  | 4 => [4, 6]
  | 5 => [5]
  | 6 => [1]
  | 7 => [1, 6]
  | 8 => [2, 4]
  | 9 => [3, 5, 6]
  | 10 => [2, 4, 6]
  | 11 => [3, 5]
  | 12 => [1, 4]
  | 13 => [1, 5, 6]
  | 14 => [2]
  | 15 => [3, 6]
  | 16 => [2, 5]
  | 17 => [3, 4, 6]
  | 18 => [1, 4, 6]
  | 19 => [1, 5]
  | 20 => [2, 6]
  | 21 => [3]
  | 22 => [2, 5, 6]
  | 23 => [3, 4]
  | 24 => [0]
  | 25 => [0, 6]
  | 26 => [0, 4]
  | 27 => [0, 5, 6]
  | 28 => [0, 4, 6]
  | 29 => [0, 5]
  | 30 => [0, 1]
  | 31 => [0, 1, 6]
  | 32 => [0, 2, 4]
  | 33 => [0, 3, 5, 6]
  | 34 => [0, 2, 4, 6]
  | 35 => [0, 3, 5]
  | 36 => [0, 1, 4]
  | 37 => [0, 1, 5, 6]
  | 38 => [0, 2]
  | 39 => [0, 3, 6]
  | 40 => [0, 2, 5]
  | 41 => [0, 3, 4, 6]
  | 42 => [0, 1, 4, 6]
  | 43 => [0, 1, 5]
  | 44 => [0, 2, 6]
  | 45 => [0, 3]
  | 46 => [0, 2, 5, 6]
  | _ => [0, 3, 4]

def stepWord (s : Fin 7) (w : Sig) : Sig :=
  (w &&& ~~~(low s ||| high s)) ||| ((w >>> shiftN s) &&& low s) |||
    ((w <<< shiftN s) &&& high s)

def stepRow (s : Fin 7) (r : Row) : Row :=
  if bit r (low s) then ⟨(shiftN s + r.val) % 512, Nat.mod_lt _ (by decide)⟩
  else if bit r (high s) then ⟨r.val - shiftN s, by have := r.isLt; omega⟩ else r

def permWord (p : Fin 48) (w : Sig) : Sig :=
  (plan p).foldl (fun v s => stepWord s v) w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem stepChecks : ∀ s : Fin 7, ∀ r : Row,
    (bit r (low s) = true → bit r (high s) = false ∧ shiftN s + r.val < 512) ∧
    (bit r (high s) = true → shiftN s ≤ r.val) ∧ stepRow s (stepRow s r) = r := by
  decide +kernel

theorem stepEq (s : Fin 7) (w : Sig) : stepWord s w = rename (stepRow s) w := by
  apply bit_ext
  intro r
  rw [bit_rename]
  obtain ⟨safeL,safeH,inv⟩ := stepChecks s r
  cases hL : bit r (low s)
  · cases hH : bit r (high s)
    · simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, BitVec.getLsbD_or, BitVec.getLsbD_and]
    · have cut := safeH hH
      have left : r.val - shiftN s < 512 := Nat.lt_of_le_of_lt (Nat.sub_le ..) r.isLt
      simp [bit] at hL hH
      simp only [bit]
      simp [stepWord,stepRow,bit,hL,hH,r.isLt, Nat.not_lt.mpr cut, left, BitVec.getLsbD_or, BitVec.getLsbD_and]
  · obtain ⟨hH,lt⟩ := safeL hL
    simp [bit] at hL hH
    simp only [bit]
    simp [stepWord,stepRow,bit,hL,hH,lt,r.isLt,Nat.mod_eq_of_lt lt, BitVec.getLsbD_or, BitVec.getLsbD_and]

set_option maxRecDepth 2000 in
theorem stepTarget : ∀ s : Fin 7, stepWord s T = T := by decide +kernel

theorem stepLive {k ws} (s : Fin 7) (h : Live true T k (List.toFinset ws)) :
    Live true T k (ws.map (stepWord s)).toFinset := by
  have hr := live_rename h (stepRow s) (fun y => ⟨stepRow s y,(stepChecks s y).2.2⟩)
  have e : rename (stepRow s) = stepWord s := funext (fun w => (stepEq s w).symm)
  rw [e,stepTarget] at hr
  have he : ws.toFinset.image (stepWord s) = (ws.map (stepWord s)).toFinset := by
    ext t
    simp
  exact he ▸ hr

theorem planLive {k : Nat} (ss : List (Fin 7)) {ws : List Sig} (h : Live true T k ws.toFinset) :
    Live true T k (ws.map fun w => ss.foldl (fun v s => stepWord s v) w).toFinset := by
  induction ss generalizing ws with
  | nil => simpa using h
  | cons s ss ih =>
    have v := ih (stepLive s h)
    simpa only [List.map_map,List.foldl_cons,Function.comp_def] using v

theorem isoTransfer (p : Fin 48) (ws : List Sig) (k : Nat)
    (h : Impossible true T k (ws.map (permWord p)).toFinset) : Impossible true T k ws.toFinset := by
  intro n hn bad
  exact h n hn (planLive (plan p) bad)

theorem isoTransferOf (p : Fin 48) (ws rep : List Sig) (k : Nat)
    (equal : (ws.map (permWord p)).toFinset = rep.toFinset)
    (h : Impossible true T k rep.toFinset) : Impossible true T k ws.toFinset :=
  isoTransfer p ws k (equal.symm ▸ h)

end PEqualNP.Outside.L_meta_10454_aux.GraphSymmetry

namespace PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits
def masks : List Nat := [61, 93, 109, 117, 121, 122, 124, 29, 45, 53, 57, 58, 60, 77, 85, 89, 90, 92, 101, 105, 106, 108, 113, 114, 116, 120, 13, 21, 25, 26, 28, 37, 41, 42, 44, 49, 50, 52, 56, 69, 73, 74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 112]
def cliqueDomain : Nat → Sig
  | 61 => 0x3333333333333333000000000000000033333333333333330000000000000000333333333333333300000000000000003333333333333333
  | 93 => 0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333
  | 109 => 0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333
  | 117 => 0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033
  | 121 => 0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303
  | 122 => 0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505
  | 124 => 0x11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
  | 29 => 0x33333333000000000000000000000000333333330000000000000000000000003333333300000000000000000000000033333333
  | 45 => 0x333300003333000000000000000000003333000033330000000000000000000033330000333300000000000000000000333300003333
  | 53 => 0x33003300330033000000000000000000330033003300330000000000000000003300330033003300000000000000000033003300330033
  | 57 => 0x303030303030303000000000000000003030303030303030000000000000000030303030303030300000000000000000303030303030303
  | 58 => 0x505050505050505000000000000000005050505050505050000000000000000050505050505050500000000000000000505050505050505
  | 60 => 0x1111111111111111000000000000000011111111111111110000000000000000111111111111111100000000000000001111111111111111
  | 77 => 0x33330000000000003333000000000000333300000000000033330000000000003333000000000000333300000000000033330000000000003333
  | 85 => 0x3300330000000000330033000000000033003300000000003300330000000000330033000000000033003300000000003300330000000000330033
  | 89 => 0x30303030000000003030303000000000303030300000000030303030000000003030303000000000303030300000000030303030000000003030303
  | 90 => 0x50505050000000005050505000000000505050500000000050505050000000005050505000000000505050500000000050505050000000005050505
  | 92 => 0x111111110000000011111111000000001111111100000000111111110000000011111111000000001111111100000000111111110000000011111111
  | 101 => 0x33000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033
  | 105 => 0x303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303
  | 106 => 0x505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505
  | 108 => 0x1111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111
  | 113 => 0x30003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003
  | 114 => 0x50005000500050005000500050005000500050005000500050005000500050005000500050005000500050005000500050005000500050005000500050005
  | 116 => 0x110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011
  | 120 => 0x1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101
  | 13 => 0x3333000000000000000000000000000033330000000000000000000000000000333300000000000000000000000000003333
  | 21 => 0x330033000000000000000000000000003300330000000000000000000000000033003300000000000000000000000000330033
  | 25 => 0x3030303000000000000000000000000030303030000000000000000000000000303030300000000000000000000000003030303
  | 26 => 0x5050505000000000000000000000000050505050000000000000000000000000505050500000000000000000000000005050505
  | 28 => 0x11111111000000000000000000000000111111110000000000000000000000001111111100000000000000000000000011111111
  | 37 => 0x3300000033000000000000000000000033000000330000000000000000000000330000003300000000000000000000003300000033
  | 41 => 0x30300000303000000000000000000000303000003030000000000000000000003030000030300000000000000000000030300000303
  | 42 => 0x50500000505000000000000000000000505000005050000000000000000000005050000050500000000000000000000050500000505
  | 44 => 0x111100001111000000000000000000001111000011110000000000000000000011110000111100000000000000000000111100001111
  | 49 => 0x3000300030003000000000000000000030003000300030000000000000000000300030003000300000000000000000003000300030003
  | 50 => 0x5000500050005000000000000000000050005000500050000000000000000000500050005000500000000000000000005000500050005
  | 52 => 0x11001100110011000000000000000000110011001100110000000000000000001100110011001100000000000000000011001100110011
  | 56 => 0x101010101010101000000000000000001010101010101010000000000000000010101010101010100000000000000000101010101010101
  | 69 => 0x330000000000000033000000000000003300000000000000330000000000000033000000000000003300000000000000330000000000000033
  | 73 => 0x3030000000000000303000000000000030300000000000003030000000000000303000000000000030300000000000003030000000000000303
  | 74 => 0x5050000000000000505000000000000050500000000000005050000000000000505000000000000050500000000000005050000000000000505
  | 76 => 0x11110000000000001111000000000000111100000000000011110000000000001111000000000000111100000000000011110000000000001111
  | 81 => 0x300030000000000030003000000000003000300000000000300030000000000030003000000000003000300000000000300030000000000030003
  | 82 => 0x500050000000000050005000000000005000500000000000500050000000000050005000000000005000500000000000500050000000000050005
  | 84 => 0x1100110000000000110011000000000011001100000000001100110000000000110011000000000011001100000000001100110000000000110011
  | 88 => 0x10101010000000001010101000000000101010100000000010101010000000001010101000000000101010100000000010101010000000001010101
  | 97 => 0x3000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003
  | 98 => 0x5000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005
  | 100 => 0x11000000110000001100000011000000110000001100000011000000110000001100000011000000110000001100000011000000110000001100000011
  | 104 => 0x101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000101
  | 112 => 0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001
  | _ => 0
def cliqueSize : Nat → Nat
  | 61 => 5
  | 93 => 5
  | 109 => 5
  | 117 => 5
  | 121 => 5
  | 122 => 5
  | 124 => 5
  | 29 => 4
  | 45 => 4
  | 53 => 4
  | 57 => 4
  | 58 => 4
  | 60 => 4
  | 77 => 4
  | 85 => 4
  | 89 => 4
  | 90 => 4
  | 92 => 4
  | 101 => 4
  | 105 => 4
  | 106 => 4
  | 108 => 4
  | 113 => 4
  | 114 => 4
  | 116 => 4
  | 120 => 4
  | 13 => 3
  | 21 => 3
  | 25 => 3
  | 26 => 3
  | 28 => 3
  | 37 => 3
  | 41 => 3
  | 42 => 3
  | 44 => 3
  | 49 => 3
  | 50 => 3
  | 52 => 3
  | 56 => 3
  | 69 => 3
  | 73 => 3
  | 74 => 3
  | 76 => 3
  | 81 => 3
  | 82 => 3
  | 84 => 3
  | 88 => 3
  | 97 => 3
  | 98 => 3
  | 100 => 3
  | 104 => 3
  | 112 => 3
  | _ => 0
def cliqueBound (m : Nat) := match cliqueSize m with | 5 => 9 | 4 => 7 | 3 => 4 | _ => 0
def embeds : Nat → List Row
  | 61 => [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61]
  | 93 => [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93]
  | 109 => [0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 64, 65, 68, 69, 72, 73, 76, 77, 96, 97, 100, 101, 104, 105, 108, 109]
  | 117 => [0, 1, 4, 5, 16, 17, 20, 21, 32, 33, 36, 37, 48, 49, 52, 53, 64, 65, 68, 69, 80, 81, 84, 85, 96, 97, 100, 101, 112, 113, 116, 117]
  | 121 => [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 48, 49, 56, 57, 64, 65, 72, 73, 80, 81, 88, 89, 96, 97, 104, 105, 112, 113, 120, 121]
  | 122 => [0, 2, 8, 10, 16, 18, 24, 26, 32, 34, 40, 42, 48, 50, 56, 58, 64, 66, 72, 74, 80, 82, 88, 90, 96, 98, 104, 106, 112, 114, 120, 122]
  | 124 => [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116, 120, 124]
  | 29 => [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29]
  | 45 => [0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45]
  | 53 => [0, 1, 4, 5, 16, 17, 20, 21, 32, 33, 36, 37, 48, 49, 52, 53, 0, 1, 4, 5, 16, 17, 20, 21, 32, 33, 36, 37, 48, 49, 52, 53]
  | 57 => [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 48, 49, 56, 57, 0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 48, 49, 56, 57]
  | 58 => [0, 2, 8, 10, 16, 18, 24, 26, 32, 34, 40, 42, 48, 50, 56, 58, 0, 2, 8, 10, 16, 18, 24, 26, 32, 34, 40, 42, 48, 50, 56, 58]
  | 60 => [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]
  | 77 => [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77]
  | 85 => [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85]
  | 89 => [0, 1, 8, 9, 16, 17, 24, 25, 64, 65, 72, 73, 80, 81, 88, 89, 0, 1, 8, 9, 16, 17, 24, 25, 64, 65, 72, 73, 80, 81, 88, 89]
  | 90 => [0, 2, 8, 10, 16, 18, 24, 26, 64, 66, 72, 74, 80, 82, 88, 90, 0, 2, 8, 10, 16, 18, 24, 26, 64, 66, 72, 74, 80, 82, 88, 90]
  | 92 => [0, 4, 8, 12, 16, 20, 24, 28, 64, 68, 72, 76, 80, 84, 88, 92, 0, 4, 8, 12, 16, 20, 24, 28, 64, 68, 72, 76, 80, 84, 88, 92]
  | 101 => [0, 1, 4, 5, 32, 33, 36, 37, 64, 65, 68, 69, 96, 97, 100, 101, 0, 1, 4, 5, 32, 33, 36, 37, 64, 65, 68, 69, 96, 97, 100, 101]
  | 105 => [0, 1, 8, 9, 32, 33, 40, 41, 64, 65, 72, 73, 96, 97, 104, 105, 0, 1, 8, 9, 32, 33, 40, 41, 64, 65, 72, 73, 96, 97, 104, 105]
  | 106 => [0, 2, 8, 10, 32, 34, 40, 42, 64, 66, 72, 74, 96, 98, 104, 106, 0, 2, 8, 10, 32, 34, 40, 42, 64, 66, 72, 74, 96, 98, 104, 106]
  | 108 => [0, 4, 8, 12, 32, 36, 40, 44, 64, 68, 72, 76, 96, 100, 104, 108, 0, 4, 8, 12, 32, 36, 40, 44, 64, 68, 72, 76, 96, 100, 104, 108]
  | 113 => [0, 1, 16, 17, 32, 33, 48, 49, 64, 65, 80, 81, 96, 97, 112, 113, 0, 1, 16, 17, 32, 33, 48, 49, 64, 65, 80, 81, 96, 97, 112, 113]
  | 114 => [0, 2, 16, 18, 32, 34, 48, 50, 64, 66, 80, 82, 96, 98, 112, 114, 0, 2, 16, 18, 32, 34, 48, 50, 64, 66, 80, 82, 96, 98, 112, 114]
  | 116 => [0, 4, 16, 20, 32, 36, 48, 52, 64, 68, 80, 84, 96, 100, 112, 116, 0, 4, 16, 20, 32, 36, 48, 52, 64, 68, 80, 84, 96, 100, 112, 116]
  | 120 => [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120]
  | 13 => [0, 1, 4, 5, 8, 9, 12, 13, 0, 1, 4, 5, 8, 9, 12, 13, 0, 1, 4, 5, 8, 9, 12, 13, 0, 1, 4, 5, 8, 9, 12, 13]
  | 21 => [0, 1, 4, 5, 16, 17, 20, 21, 0, 1, 4, 5, 16, 17, 20, 21, 0, 1, 4, 5, 16, 17, 20, 21, 0, 1, 4, 5, 16, 17, 20, 21]
  | 25 => [0, 1, 8, 9, 16, 17, 24, 25, 0, 1, 8, 9, 16, 17, 24, 25, 0, 1, 8, 9, 16, 17, 24, 25, 0, 1, 8, 9, 16, 17, 24, 25]
  | 26 => [0, 2, 8, 10, 16, 18, 24, 26, 0, 2, 8, 10, 16, 18, 24, 26, 0, 2, 8, 10, 16, 18, 24, 26, 0, 2, 8, 10, 16, 18, 24, 26]
  | 28 => [0, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24, 28, 0, 4, 8, 12, 16, 20, 24, 28]
  | 37 => [0, 1, 4, 5, 32, 33, 36, 37, 0, 1, 4, 5, 32, 33, 36, 37, 0, 1, 4, 5, 32, 33, 36, 37, 0, 1, 4, 5, 32, 33, 36, 37]
  | 41 => [0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41, 0, 1, 8, 9, 32, 33, 40, 41]
  | 42 => [0, 2, 8, 10, 32, 34, 40, 42, 0, 2, 8, 10, 32, 34, 40, 42, 0, 2, 8, 10, 32, 34, 40, 42, 0, 2, 8, 10, 32, 34, 40, 42]
  | 44 => [0, 4, 8, 12, 32, 36, 40, 44, 0, 4, 8, 12, 32, 36, 40, 44, 0, 4, 8, 12, 32, 36, 40, 44, 0, 4, 8, 12, 32, 36, 40, 44]
  | 49 => [0, 1, 16, 17, 32, 33, 48, 49, 0, 1, 16, 17, 32, 33, 48, 49, 0, 1, 16, 17, 32, 33, 48, 49, 0, 1, 16, 17, 32, 33, 48, 49]
  | 50 => [0, 2, 16, 18, 32, 34, 48, 50, 0, 2, 16, 18, 32, 34, 48, 50, 0, 2, 16, 18, 32, 34, 48, 50, 0, 2, 16, 18, 32, 34, 48, 50]
  | 52 => [0, 4, 16, 20, 32, 36, 48, 52, 0, 4, 16, 20, 32, 36, 48, 52, 0, 4, 16, 20, 32, 36, 48, 52, 0, 4, 16, 20, 32, 36, 48, 52]
  | 56 => [0, 8, 16, 24, 32, 40, 48, 56, 0, 8, 16, 24, 32, 40, 48, 56, 0, 8, 16, 24, 32, 40, 48, 56, 0, 8, 16, 24, 32, 40, 48, 56]
  | 69 => [0, 1, 4, 5, 64, 65, 68, 69, 0, 1, 4, 5, 64, 65, 68, 69, 0, 1, 4, 5, 64, 65, 68, 69, 0, 1, 4, 5, 64, 65, 68, 69]
  | 73 => [0, 1, 8, 9, 64, 65, 72, 73, 0, 1, 8, 9, 64, 65, 72, 73, 0, 1, 8, 9, 64, 65, 72, 73, 0, 1, 8, 9, 64, 65, 72, 73]
  | 74 => [0, 2, 8, 10, 64, 66, 72, 74, 0, 2, 8, 10, 64, 66, 72, 74, 0, 2, 8, 10, 64, 66, 72, 74, 0, 2, 8, 10, 64, 66, 72, 74]
  | 76 => [0, 4, 8, 12, 64, 68, 72, 76, 0, 4, 8, 12, 64, 68, 72, 76, 0, 4, 8, 12, 64, 68, 72, 76, 0, 4, 8, 12, 64, 68, 72, 76]
  | 81 => [0, 1, 16, 17, 64, 65, 80, 81, 0, 1, 16, 17, 64, 65, 80, 81, 0, 1, 16, 17, 64, 65, 80, 81, 0, 1, 16, 17, 64, 65, 80, 81]
  | 82 => [0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82, 0, 2, 16, 18, 64, 66, 80, 82]
  | 84 => [0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84, 0, 4, 16, 20, 64, 68, 80, 84]
  | 88 => [0, 8, 16, 24, 64, 72, 80, 88, 0, 8, 16, 24, 64, 72, 80, 88, 0, 8, 16, 24, 64, 72, 80, 88, 0, 8, 16, 24, 64, 72, 80, 88]
  | 97 => [0, 1, 32, 33, 64, 65, 96, 97, 0, 1, 32, 33, 64, 65, 96, 97, 0, 1, 32, 33, 64, 65, 96, 97, 0, 1, 32, 33, 64, 65, 96, 97]
  | 98 => [0, 2, 32, 34, 64, 66, 96, 98, 0, 2, 32, 34, 64, 66, 96, 98, 0, 2, 32, 34, 64, 66, 96, 98, 0, 2, 32, 34, 64, 66, 96, 98]
  | 100 => [0, 4, 32, 36, 64, 68, 96, 100, 0, 4, 32, 36, 64, 68, 96, 100, 0, 4, 32, 36, 64, 68, 96, 100, 0, 4, 32, 36, 64, 68, 96, 100]
  | 104 => [0, 8, 32, 40, 64, 72, 96, 104, 0, 8, 32, 40, 64, 72, 96, 104, 0, 8, 32, 40, 64, 72, 96, 104, 0, 8, 32, 40, 64, 72, 96, 104]
  | 112 => [0, 16, 32, 48, 64, 80, 96, 112, 0, 16, 32, 48, 64, 80, 96, 112, 0, 16, 32, 48, 64, 80, 96, 112, 0, 16, 32, 48, 64, 80, 96, 112]
  | _ => []
def ranks : Nat → List Nat
  | 61 => [0, 7, 1, 2, 3, 4, 7]
  | 93 => [0, 7, 1, 2, 3, 7, 4]
  | 109 => [0, 7, 1, 2, 7, 3, 4]
  | 117 => [0, 7, 1, 7, 2, 3, 4]
  | 121 => [0, 7, 7, 1, 2, 3, 4]
  | 122 => [7, 0, 7, 1, 2, 3, 4]
  | 124 => [7, 7, 0, 1, 2, 3, 4]
  | 29 => [0, 7, 1, 2, 3, 7, 7]
  | 45 => [0, 7, 1, 2, 7, 3, 7]
  | 53 => [0, 7, 1, 7, 2, 3, 7]
  | 57 => [0, 7, 7, 1, 2, 3, 7]
  | 58 => [7, 0, 7, 1, 2, 3, 7]
  | 60 => [7, 7, 0, 1, 2, 3, 7]
  | 77 => [0, 7, 1, 2, 7, 7, 3]
  | 85 => [0, 7, 1, 7, 2, 7, 3]
  | 89 => [0, 7, 7, 1, 2, 7, 3]
  | 90 => [7, 0, 7, 1, 2, 7, 3]
  | 92 => [7, 7, 0, 1, 2, 7, 3]
  | 101 => [0, 7, 1, 7, 7, 2, 3]
  | 105 => [0, 7, 7, 1, 7, 2, 3]
  | 106 => [7, 0, 7, 1, 7, 2, 3]
  | 108 => [7, 7, 0, 1, 7, 2, 3]
  | 113 => [0, 7, 7, 7, 1, 2, 3]
  | 114 => [7, 0, 7, 7, 1, 2, 3]
  | 116 => [7, 7, 0, 7, 1, 2, 3]
  | 120 => [7, 7, 7, 0, 1, 2, 3]
  | 13 => [0, 7, 1, 2, 7, 7, 7]
  | 21 => [0, 7, 1, 7, 2, 7, 7]
  | 25 => [0, 7, 7, 1, 2, 7, 7]
  | 26 => [7, 0, 7, 1, 2, 7, 7]
  | 28 => [7, 7, 0, 1, 2, 7, 7]
  | 37 => [0, 7, 1, 7, 7, 2, 7]
  | 41 => [0, 7, 7, 1, 7, 2, 7]
  | 42 => [7, 0, 7, 1, 7, 2, 7]
  | 44 => [7, 7, 0, 1, 7, 2, 7]
  | 49 => [0, 7, 7, 7, 1, 2, 7]
  | 50 => [7, 0, 7, 7, 1, 2, 7]
  | 52 => [7, 7, 0, 7, 1, 2, 7]
  | 56 => [7, 7, 7, 0, 1, 2, 7]
  | 69 => [0, 7, 1, 7, 7, 7, 2]
  | 73 => [0, 7, 7, 1, 7, 7, 2]
  | 74 => [7, 0, 7, 1, 7, 7, 2]
  | 76 => [7, 7, 0, 1, 7, 7, 2]
  | 81 => [0, 7, 7, 7, 1, 7, 2]
  | 82 => [7, 0, 7, 7, 1, 7, 2]
  | 84 => [7, 7, 0, 7, 1, 7, 2]
  | 88 => [7, 7, 7, 0, 1, 7, 2]
  | 97 => [0, 7, 7, 7, 7, 1, 2]
  | 98 => [7, 0, 7, 7, 7, 1, 2]
  | 100 => [7, 7, 0, 7, 7, 1, 2]
  | 104 => [7, 7, 7, 0, 7, 1, 2]
  | 112 => [7, 7, 7, 7, 0, 1, 2]
  | _ => []
def k4 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def k5 : Sig := 0xfffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8fffefee8
def standard : Nat → Sig | 5 => k5 | 4 => k4 | _ => k3
def embed (m : Nat) (r : Fin 32) : Row := (embeds m).getD r.val 0
def arg (m : Nat) (i : Fin 7) := (inputs.take (cliqueSize m)).getD ((ranks m).getD i.val 7) zero
def low (r : Row) : Fin 32 := ⟨r.val % 32,Nat.mod_lt _ (by decide)⟩
def toRow (j : Fin 32) : Row := ⟨j.val,by omega⟩
def ref (m : Nat) (r : Row) : Row := embed m (low r)

def cert (m : Nat) : Bool := decide (∀ j : Fin 32,
  bit (embed m j) (cliqueDomain m) = true ∧
    bit (embed m j) PEqualNP.Outside.L_meta_10454_aux.GraphTarget.full = bit (toRow j) (standard (cliqueSize m)) ∧
    ∀ i : Fin 7, bit (embed m j) (PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7.getD i.val zero) = bit (toRow j) (arg m i))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem certs : masks.all cert = true := by decide +kernel

end PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits
def smalls := zero :: k3 :: k4 :: k5 :: inputs.take 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem periods : smalls.all (fun w => decide (∀ r : Row, bit (toRow (low r)) w = bit r w)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem facts : masks.all (fun m => decide (
    (cliqueSize m=3 ∨ cliqueSize m=4 ∨ cliqueSize m=5) ∧ standard (cliqueSize m) ∈ smalls ∧
    ∀ i : Fin 7, arg m i ∈ smalls)) = true := by decide +kernel

theorem fromWord {xs : List Sig} (j : Nat) :
    Available true (xs.map observe) (observe (xs.getD j zero)) := by
  by_cases h : j < xs.length
  · apply Or.inl
    apply List.mem_map_of_mem
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using (List.getElem_mem h)
  · have hz : xs.getD j zero = zero := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [hz]; exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem validParam (m : Nat) (hm : m ∈ masks)
    (lower : Lower true (inputs.take (cliqueSize m)) (standard (cliqueSize m)) (cliqueBound m)) :
    Slice true PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_10454_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  have tbl0 := List.all_eq_true.mp certs m hm
  unfold cert at tbl0
  have tbl := of_decide_eq_true tbl0
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  have periodic (x : Sig) (hx : x ∈ smalls) : ∀ r, bit (toRow (low r)) x = bit r x :=
    of_decide_eq_true (List.all_eq_true.mp periods x hx)
  have tgt : restrictRows (ref m) (observe PEqualNP.Outside.L_meta_10454_aux.GraphTarget.full) = observe (standard (cliqueSize m)) :=
    funext fun r => ((tbl (low r)).2.1).trans (periodic _ info.2.1 r)
  refine ⟨ref m,inputs.take (cliqueSize m),fun r => (tbl (low r)).1,?_,?_,?_⟩
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    let i : Fin 7 := ⟨j,by exact hj⟩
    have eq : restrictRows (ref m) (observe (PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7.getD i.val zero)) = observe (arg m i) :=
      funext fun r => ((tbl (low r)).2.2 i).trans (periodic _ (info.2.2 i) r)
    have same : PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7.getD i.val zero = PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7[j] := by
      simp [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [← same,eq]; exact fromWord _
  · rw [tgt]
    apply observe_proper
    rcases info.1 with e|e|e <;> rw [e] <;> unfold proper <;> decide +kernel
  · rw [tgt]; exact lower
end PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_10454_aux.TriangleBound
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.Outside.L_meta_10454_aux.CliqueBounds PEqualNP.Outside.L_meta_10454_aux.FiveInputBounds

def k3 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def blocked (T : Sig) : Nat → List Sig → Bool
  | 0, ws => !ws.contains T
  | k+1, ws => !ws.contains T && ws.all fun a => ws.all fun b =>
      (ops a b).all fun z => blocked T k (z::ws)

theorem blockedSound (T : Sig) (k) (ws : List Sig) (h : blocked T k ws = true) :
    ∀ l ≤ k, ¬build basicOps T l ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    intro l hl; have e : l=0 := by omega
    subst l
    simpa [blocked,build] using h
  | succ k ih =>
    simp only [blocked,Bool.and_eq_true,List.all_eq_true] at h
    intro l le
    induction l with
    | zero => simpa [build] using h.1
    | succ l hl =>
      rintro (prev|⟨a,ha,b,hb,_,z,hz,htail⟩)
      · exact hl (by omega) prev
      · have v := h.2 a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) z (List.mem_toFinset.mp hz)
        exact ih (z::ws) v l (by omega) (by simpa using htail)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem standardLower3 : Lower true (inputs.take 3) k3 4 := by
  intro p bank h hit
  have pT : proper k3 := by unfold proper; decide +kernel
  have gT : plainWord k3 = true := by decide +kernel
  have pR : (inputs.take 3).all plainWord=true := by decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT gT pR h hit
  by_contra! bad
  have no := blockedSound k3 3 (inputs.take 3) (by decide +kernel) k (by omega)
  exact no (convert run (fun w hw => List.mem_toFinset.mpr (sub w hw)))

end PEqualNP.Outside.L_meta_10454_aux.TriangleBound

namespace PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits

theorem valid (m : Nat) (hm : m ∈ masks) :
    Slice true PEqualNP.Outside.L_meta_10454_aux.GraphTarget.cols7 PEqualNP.Outside.L_meta_10454_aux.GraphTarget.full (cliqueDomain m) (cliqueBound m) := by
  apply validParam m hm
  have info := of_decide_eq_true (List.all_eq_true.mp facts m hm)
  unfold cliqueBound
  rcases info.1 with h|h|h <;> rw [h]
  · exact PEqualNP.Outside.L_meta_10454_aux.TriangleBound.standardLower3
  · exact PEqualNP.Outside.L_meta_10454_aux.CliqueBounds.standardLower4
  · exact PEqualNP.Outside.L_meta_10454_aux.CliqueBounds.standardLower5
end PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.Outside.L_meta_10454_aux.GraphTarget

abbrev Entry := Nat × List Nat × Nat × List Nat
def Entry.cap (x : Entry) : Nat := x.1
def Entry.program (x : Entry) : List Nat := x.2.1
def Entry.livingMask (x : Entry) : Nat := x.2.2.1
def Entry.codes (x : Entry) : List Nat := x.2.2.2

def unpackGates (ws : List Sig) : List Nat → List Choice
  | [] => []
  | g :: gs =>
    let c : Choice := (g / 256, ws.getD (g % 16) 0, ws.getD ((g/16) % 16) 0)
    c :: unpackGates (ws ++ [choiceVal c]) gs

def selectMask {α : Type} (m : Nat) (ws : List α) : List α :=
  (ws.zipIdx.filter fun p => m.testBit p.2).map Prod.fst

def choicesOf (e : Entry) := unpackGates cols7 e.program

def stateOf (e : Entry) : List Sig :=
  selectMask e.livingMask (cols7 ++ (choicesOf e).map choiceVal)

def negativeRows : List Row := [0,1,2,3,4,6,8,16,32,64]

def candidates (r : Row) : List Sig → Sig
  | [] => full
  | w :: ws => (if bit r w then w else ~~~w) &&& candidates r ws

def indist (ws : List Sig) := negativeRows.any fun r => candidates r ws != 0

def pop (x : Nat) : Nat := (BitVec.ofNat 16 x).cpop.toNat

def readCode (e : Entry) (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Nat :=
  let ia := ws.idxOf a
  let ib := ws.idxOf b
  let lo := min ia ib
  let hi := max ia ib
  let block := e.codes.getD (hi*(hi-1)/2+lo) 0
  let dir := ia < ib
  let slot := 4 * (if dir then d else flipOp d) +
    (if dir then ka.toNat + 2*kb.toNat else kb.toNat + 2*ka.toNat)
  if block.testBit slot then
    let rank := pop (block % (2^slot))
    (block >>> (16+20*rank)) % (2^20)
  else 0

theorem candBit (r s : Row) (ws : List Sig) :
    bit s (candidates r ws) = true ↔ bit s full = true ∧ ∀ w ∈ ws, bit r w = bit s w := by
  induction ws with
  | nil => simp [candidates]
  | cons a ws ih =>
    have ba (x y : Sig) : bit s (x &&& y) = (bit s x && bit s y) := BitVec.getLsbD_and
    have bn (x : Sig) : bit s (~~~x) = !bit s x := by
      simp only [bit,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and]
    cases hr : bit r a <;> cases hs : bit s a <;>
      simp only [candidates,hr,Bool.false_eq_true,ite_false,ite_true,ba,bn,hs,Bool.and_eq_true,
        ih,List.forall_mem_cons] <;> simp_all

set_option maxRecDepth 8192 in
theorem indistSound {ws : List Sig} (bad : indist ws = true) (k : Nat) :
    Impossible true full k ws.toFinset := by
  obtain ⟨s,hs,hbad⟩ := List.any_eq_true.mp bad
  have hn : bit s full = false := (by decide +kernel : ∀ r ∈ negativeRows, bit r full = false) s hs
  intro l _ run
  have z : candidates s ws = 0 := by
    apply bit_ext
    intro r
    cases e : bit r (candidates s ws)
    · exact (bit_zero _).symm
    · obtain ⟨yes,all⟩ := (candBit _ _ _).mp e
      obtain ⟨w,hw,sep⟩ := live_row_difference run (show bit r full ≠ bit s full by simp [yes,hn])
      exact False.elim (sep (all w (List.mem_toFinset.mp hw)).symm)
  simp [z] at hbad
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.GraphTarget
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits

theorem childSwap {u : Bool} {d : Nat} (hd : allowed u d) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip hd a b, List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem enumStepOrdered {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb ne fresh pr sz
  rcases lt_or_gt_of_ne (fun eq => ne (BitVec.toNat_inj.mp eq)) with lt | gt
  · exact twoStep a ha b hb d hd ka kb lt fresh pr sz
  · have eq := bin_flip hd a b
    have perm := childSwap hd ws a b ka kb
    have hs := twoStep b hb a ha (flipOp d) (flip_flip hd).1 kb ka gt
      (eq ▸ fresh) (eq ▸ pr) (perm.length_eq ▸ sz)
    have eqSet : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext x
      simpa only [List.mem_toFinset] using (perm.mem_iff : x ∈ _ ↔ x ∈ _)
    exact eqSet.symm ▸ hs

end PEqualNP.Outside.L_meta_10454_aux.GraphTarget

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.Outside.L_meta_10454_aux.GraphTarget PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions PEqualNP.Outside.L_meta_10454_aux.GraphSymmetry

def verifyCut (cap : Nat) (cs : List Choice) (ch : List Sig) (code : Nat) : Bool :=
  let m := (code-1)/256
  let witness := selectMask ((code-1) % 256) cs
  let mask := cliqueDomain m
  masks.contains m &&
    match makePool true mask cols7 witness with
    | none => false
    | some pool => poolCut true mask (cliqueBound m) cap witness.length pool ch

def verifyIso (db : Array Entry) (cap : Nat) (ch : List Sig) (code : Nat) : Bool :=
  let key := code-65536
  let j := key/48
  let p : Fin 48 := Fin.ofNat 48 (key % 48)
  let dest := db[j]?.getD default
  decide (j < db.size) && (dest.cap==cap) &&
    decide ((ch.map (permWord p)).toFinset = (stateOf dest).toFinset)

def verifyChild (db : Array Entry) (e : Entry) (steps : List Choice) (ws : List Sig)
    (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  let y := bin d a b
  let ch := childTwo ws a b d ka kb
  if b.toNat ≤ a.toNat then true else
  if a == b || ws.contains y || y == zero || y == one || decide (e.cap < ch.length) then true
  else if indist ch then true
  else
    let code := readCode e ws a b d ka kb
    if code==0 then false else if 65536 ≤ code then verifyIso db (e.cap-1) ch code
      else verifyCut (e.cap-1) (steps++[(d,a,b)]) ch code

def verify (db : Array Entry) (e : Entry) : Bool :=
  let ws := stateOf e
  let cs := choicesOf e
  decide (0 < e.cap) && decide ws.Nodup && !ws.contains full &&
    ws.all fun a => ws.all fun b => [0,1,2,3].all fun d =>
      [false,true].all fun ka => [false,true].all fun kb => verifyChild db e cs ws a b d ka kb
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
def n0 : Entry := ⟨12, [], 127, [0x03d011108007a0107c011003003d01a8a8,0x0790107a0107a01079018888,0x0790103d0111098079011004803d018cc8,0x0750107a01110e0075018888,0x0750103d010750103d018888,0x0750107901110f8075018888,0x06d0107a01110e606d018888,0x06d0103d0106d0103d018888,0x06d0107901110fe06d018888,0x06d01075011267006d018888,0x05d0107a01110e805d018888,0x05d0103d0105d0103d018888,0x05d01079011110005d018888,0x05d01075011267205d018888,0x05d0106d011267c05d018888,0x03d0107a01110e903d018888,0x03d0103d0103d0103d018888,0x03d01079011110103d018888,0x03d01075011267303d018888,0x03d0106d011267d03d018888,0x03d0105d011268003d018888]⟩
def n1 : Entry := ⟨11, [272], 253, [0x079010790107a0107a010790107901c88c,0x0750107a0107a0107a0110060075018cc8,0x075010790107a01075018888,0x06d0107a0107a0107a011006606d018cc8,0x06d010790107a0106d018888,0x06d010750110bd006d018888,0x05d0107a0107a0107a011006805d018cc8,0x05d010790107a0105d018888,0x05d010750110bd205d018888,0x05d0106d0110bdc05d018888,0x03d0107a0107a0107a011006903d018cc8,0x03d010790107a0103d018888,0x03d010750110bd303d018888,0x03d0106d0110bdd03d018888,0x03d0105d0110be003d018888,0x03d0103d0103d01e000,0x07a0107a010790107a0107a0107901a8a8,0x07c010750107c01075018888,0x07c0106d0107c0106d018888,0x07c0105d0107c0105d018888,0x07c0103d0107c0103d018888]⟩
def n2 : Entry := ⟨10, [272,304], 508, [0x0750107501075010750107a0107501a8a8,0x06d030790307a0106d038888,0x06d030750107501075011009006d038cc8,0x05d030790307a0105d038888,0x05d030750107501075011009205d038cc8,0x05d0306d031060005d038888,0x03d030790307a0103d038888,0x03d030750107501075011009303d038cc8,0x03d0306d031060103d038888,0x03d0305d031060403d038888,0x07a0107a010790307a0107a0107903a8a8,0x0750107c0107501075010750107501c88c,0x07c0106d0307c0106d038888,0x07c0105d0307c0105d038888,0x07c0103d0307c0103d038888,0x07a01079030790107a0107903079018a8a,0x0750107a0107501e000,0x072010720106d030720110ab006d03a8a8,0x072010720105d030720110ab205d03a8a8,0x072010720103d030720110ab303d03a8a8,0x0750103d0303d01075010750103d018a8a]⟩
def n3 : Entry := ⟨9, [272,304,323], 1012, [0x06d0306d0306d0306d0307a0506d03a8a8,0x05d070790707a0505d078888,0x05d0706d0306d0306d03100c005d078cc8,0x03d070790707a0503d078888,0x03d0706d0306d0306d03100c103d078cc8,0x03d0705d071033003d078888,0x07a0507a050790707a0507a0507907a8a8,0x06d0306d0306d0306d0307c0506d038cc8,0x07c0505d0707c0505d078888,0x07c0503d0707c0503d078888,0x07a050790707a05079078888,0x06d030720106d0306d0306d0306d03c88c,0x072010720105d07072011045005d07a8a8,0x072010720103d07072011045103d07a8a8,0x0750103d0706d0306d038888,0x07a0507a050790707a0507a0507907a8a8,0x06d030750106d03e000,0x065010650105d07065011054005d07a8a8,0x065010650103d07065011054103d07a8a8,0x07c0507c0507c0106d0307c0507c018a8a,0x06d0307a0507a0106d0306d0306d038a8a]⟩
def n4 : Entry := ⟨8, [272,304,323,340], 2020, [0x05d0705d0705d0705d0707a0d05d07a8a8,0x03d0f0790f07a0d03d0f8888,0x03d0f05d0705d0705d07100f003d0f8cc8,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x05d0705d0705d0705d0707c0d05d078cc8,0x07c0d03d0f07c0d03d0f8888,0x07a0d0790f07a0d0790f8888,0x05d0705d0705d0705d0705d070720905d07101b005d07acf8,0x072090720903d0f072091027003d0fa8a8,0x0750903d0f05d0705d078888,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x05d070650105d0705d0705d0705d07c88c,0x065010650103d0f06501102d003d0fa8a8,0x07c0d07c0d06d0307c0d8888,0x06d0307a0d06d0306d038888,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x05d0706d0305d07e000,0x04d0304d0303d0f04d031030003d0fa8a8,0x07c0d07c0d07c0d07c0d07c0d07c0da8a8,0x04d0304d030720104d0304d0304d038a8a,0x05d07075090750105d0705d0705d078a8a]⟩
def n5 : Entry := ⟨7, [272,304,323,340,357], 4036, [0x03d0f07a1d2020,0x07a1d07a1d2020,0x03d0f07c1d0440,0x0000,0x03d0f03d0f0721903d0f101202470,0x0000,0x07a1d07a1d2020,0x03d0f03d0f0651103d0f101502470,0x0000,0x0000,0x07a1d07a1d2020,0x04d0303d0f4004,0x07c1d07c1d2020,0x0000,0x0000,0x07a1d07a1d2020,0x05d0703d0f6000,0x07c1d07c1d2020,0x01d0701d0701d0707219101802470,0x0650101d070202,0x06d0303d0f0202]⟩
def n6 : Entry := ⟨6, [272,304,323,340,357,390], 7812, [0x07a3d07a3d2020,0x07a3d07a3d2020,0x0000,0x07a3d07a3d2020,0x07c3d07c3d2020,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0320104d234004,0x0000]⟩
def n7 : Entry := ⟨6, [272,304,323,340,357,406], 7556, [0x07a3d07a3d2020,0x0000,0x0000,0x07a3d07a3d2020,0x07c3d07c3d2020,0x0000,0x07a3d07a3d2020,0x07c3d07c3d2020,0x0000,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x0350105d274004,0x0650105d274004]⟩
def n8 : Entry := ⟨6, [272,304,323,340,357,440], 5828, [0x03d2f07a3d2020,0x07a3d07a3d2020,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x0000,0x0000,0x0520103d2f6000,0x0000,0x01a0106d334004,0x0320106d334004]⟩
def n9 : Entry := ⟨7, [272,304,323,340,389], 3780, [0x03d1f0791f07a1d03d1f8888,0x07a1d07a1d0791f07a1d07a1d0791fa8a8,0x07c1d03d1f07c1d03d1f8888,0x07a1d07a1d0791f07a1d07a1d0791fa8a8,0x065110651103d1f06511101e003d1fa8a8,0x07c1d07c1d06d1307c1d8888,0x07a1d07a1d0791f07a1d07a1d0791fa8a8,0x04d0304d0303d1f04d03101ee03d1fa8a8,0x07c1d07c1d07c1d07c1d8888,0x05d070751905d0705d078888,0x07a1d0791f07a1d0791f8888,0x052011024003d1f102101018003d1fa8a8,0x07c1d03d1f05d0705d078888,0x05a0505a0106d1306d1306d1306d13c88c,0x04d030720106d1306d1306d1306d13c88c]⟩
def n10 : Entry := ⟨6, [272,304,323,340,389,406], 7364, [0x03d1f07a3d2020,0x07a3d07a3d2020,0x03d1f07c3d0440,0x07a3d07a3d2020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a3d07a3d2020,0x0651103d1f6000,0x0000,0x0000,0x05a0102d130202]⟩
def n11 : Entry := ⟨6, [272,304,323,340,389,438], 7876, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x052011000,0x0000,0x06d330001,0x06d330001,0x0000,0x0000,0x0000,0x01a0106d131001,0x0320106d131001,0x0000]⟩
def n12 : Entry := ⟨6, [272,304,323,340,389,950], 5828, [0x0000,0x07a3d07a3d2020,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x0000,0x0000,0x0520103d1f0060,0x0000,0x0000,0x0000]⟩
def n13 : Entry := ⟨7, [272,304,323,340,390], 3812, [0x05d1707a1d2020,0x03d0f07a1d2020,0x03d0f03d0f03d0f05d17101202470,0x07a1d07a1d2020,0x05d1707c1d0440,0x0000,0x07a1d07a1d2020,0x0651105d174004,0x0000,0x0000,0x07a1d07a1d2020,0x06d1305d176000,0x03d0f03d0f04d1303d0f101ef2470,0x07c1d07c1d2020,0x0751105d170202,0x0000,0x05d1705d17102a005d17101802470,0x0720903d0f6000,0x0000,0x0000,0x0320104d134004]⟩
def n14 : Entry := ⟨6, [272,304,323,340,390,437], 7876, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x0000,0x052011000,0x0000,0x06d130001,0x06d130001,0x0000]⟩
def n15 : Entry := ⟨7, [272,304,323,340,406], 3556, [0x05d1707a1d2020,0x03d0f07a1d2020,0x03d0f03d0f03d0f05d17101502470,0x07a1d07a1d2020,0x05d1707c1d0440,0x03d0f07c1d0440,0x0000,0x05d1705d170721905d17101e02470,0x0000,0x0000,0x07a1d07a1d2020,0x06d1305d176000,0x0000,0x07c1d07c1d2020,0x0000,0x07a1d07a1d2020,0x0250105d174004,0x0650103d0f6000,0x0000,0x0000,0x0350105d174004]⟩
def n16 : Entry := ⟨7, [272,304,323,340,422], 3044, [0x05d1707a1d2020,0x03d0f07a1d2020,0x0000,0x07a1d07a1d2020,0x05d1707c1d0440,0x03d0f07c1d0440,0x0000,0x05d1705d170721905d17101ee2470,0x03d0f03d0f0721903d0f101ef2470,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x02d0305d176000,0x04d0303d0f6000,0x07c1d07c1d2020,0x07201072010202,0x07501075010202]⟩
def n17 : Entry := ⟨8, [272,304,323,357], 2036, [0x06d0b07a0d2020,0x05d0707a0d2020,0x05d0705d0705d0706d0b100f02470,0x03d0707a0d2020,0x03d0703d0703d0706d0b100f12470,0x03d0705d0703d0703d0703d074207,0x07a0d07a0d2020,0x06d0b07c0d0440,0x05d0707c0d0440,0x03d0707c0d0440,0x0000,0x0720906d0b4004,0x05d0705d070720905d07103602470,0x03d0703d070720903d07103612470,0x0000,0x07a0d07a0d2020,0x0750906d0b6000,0x05d0705d070650905d07102d42470,0x03d0703d070650903d07102d52470,0x07c0907c090202,0x07a0906d0b0202,0x07a0d0790707a0d079072222,0x06d0b06d0b06d0306d0301d0706d0b1030006d032772,0x03d0703d076000,0x05d0703d076000,0x07c0d07c0507c0d07c052222,0x01d0701d07072010720101d07072091039001d072772,0x01d0701d07065010650101d0706509103f001d072772]⟩
def n18 : Entry := ⟨7, [272,304,323,357,389], 3796, [0x06d1b07a1d2020,0x03d1707a1d2020,0x03d1703d1703d1706d1b101212470,0x07a1d07a1d2020,0x06d1b07c1d0440,0x03d1707c1d0440,0x07a1d07a1d2020,0x0751906d1b6000,0x03d1703d170651903d17101e52470,0x0000,0x07a1d07a1d2020,0x06d1b06d1b01d0706d1b101ee2470,0x05d0703d176000,0x0000,0x0000,0x0000,0x0520106d1b4004,0x0520103d174004,0x0000,0x05a0106d1b4004,0x0720103d174004]⟩
def n19 : Entry := ⟨7, [272,304,323,357,424], 2804, [0x06d1b07a1d2020,0x05d1707a1d2020,0x05d1705d1705d1706d1b101802470,0x03d1707a1d2020,0x03d1703d1703d1706d1b101812470,0x0000,0x07a1d07a1d2020,0x06d1b07c1d0440,0x0000,0x0000,0x07a1d07a1d2020,0x0751906d1b6000,0x0000,0x0000,0x0000,0x0000,0x103c006d1b4004,0x0320105d176000,0x0520103d176000,0x0000,0x01a0106d1b4004]⟩
def n20 : Entry := ⟨6, [272,304,323,357,424,948], 6884, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x052011000,0x0000,0x0000,0x0000]⟩
def n21 : Entry := ⟨7, [272,304,323,357,425], 2548, [0x06d1b07a1d2020,0x05d1707a1d2020,0x0000,0x03d1707a1d2020,0x0000,0x0000,0x07a1d07a1d2020,0x06d1b07c1d0440,0x05d1707c1d0440,0x03d1707c1d0440,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0150106d1b6000,0x0250105d176000,0x0450103d176000,0x1042007c0107c1d07c0107c014207,0x07a0107a010202]⟩
def n22 : Entry := ⟨6, [272,304,323,357,425,951], 6516, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07c010100]⟩
def n23 : Entry := ⟨8, [272,304,323,389], 1780, [0x06d0b06d0b06d0b06d0b07a0d06d0ba8a8,0x05d0705d0705d0705d0707a0d05d07a8a8,0x05d0705d0705d0705d0705d0705d0706d0b101b005d07acf8,0x03d0f0790f07a0d03d0f8888,0x03d0f06d0b06d0b06d0b1027103d0f8cc8,0x03d0f05d0705d0705d071036003d0f8cc8,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x06d0b06d0b06d0b06d0b07c0d06d0b8cc8,0x05d0705d0705d0705d078888,0x07c0d03d0f07c0d03d0f8888,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x06d0b0750906d0be000,0x05d0705d0705d0705d078888,0x065090650903d0f065091048003d0fa8a8,0x07c0d07c0d06d0b07c0d8888,0x07a0d0790f07a0d0790f8888,0x06d0b0520106d0b06d0b06d0b06d0bc88c,0x05d070720105d07e000,0x052011051003d0f104b01039003d0fa8a8,0x07c0d03d0f05d0705d078888,0x05a0505a0106d0b06d0b06d0b06d0bc88c]⟩
def n24 : Entry := ⟨7, [272,304,323,389,406], 3316, [0x06d1b07a1d2020,0x05d1707a1d2020,0x05d1705d1705d1706d1b101e02470,0x03d0f07a1d2020,0x0000,0x03d0f03d0f03d0f05d17101e52470,0x07a1d07a1d2020,0x06d1b07c1d0440,0x0000,0x03d0f07c1d0440,0x0000,0x0000,0x0721105d176000,0x0000,0x0000,0x07a1d07a1d2020,0x0350906d1b6000,0x0000,0x0650903d0f6000,0x0000,0x05a0102d0b0202]⟩
def n25 : Entry := ⟨7, [272,304,323,389,422], 3828, [0x0000,0x0000,0x102100010,0x0000,0x102a10010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0520106d1b1001,0x0000,0x052011000,0x0000,0x06d1b0001,0x0000,0x104e006d0b1001,0x032011000,0x0000,0x0000,0x01a0106d0b1001,0x0000]⟩
def n26 : Entry := ⟨6, [272,304,323,389,422,948], 5860, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x0000,0x0000,0x0000,0x0000]⟩
def n27 : Entry := ⟨7, [272,304,323,389,934], 2804, [0x06d1b07a1d2020,0x05d1707a1d2020,0x05d1705d1705d1706d1b102402470,0x0000,0x03d0f03d0f0440,0x03d0f05d172020,0x07a1d07a1d2020,0x06d1b07c1d0440,0x0000,0x0000,0x07a1d07a1d2020,0x0751906d1b6000,0x0000,0x0000,0x0000,0x0000,0x0520106d1b4004,0x05d1703d0f2020,0x0520103d0f0060,0x0000,0x0000]⟩
def n28 : Entry := ⟨8, [272,304,323,405], 1524, [0x06d0b06d0b06d0b06d0b07a0d06d0ba8a8,0x05d0705d0705d0705d0707a0d05d07a8a8,0x05d0705d0705d0705d078888,0x03d0f0790f07a0d03d0f8888,0x03d0f06d0b06d0b06d0b102d103d0f8cc8,0x03d0f05d0705d0705d07102d403d0f8cc8,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x06d0b06d0b06d0b06d0b07c0d06d0b8cc8,0x05d0705d0705d0705d0707c0d05d078cc8,0x07c0d03d0f07c0d03d0f8888,0x07a0d0790f07a0d0790f8888,0x06d0b06d0b06d0b06d0b8888,0x05d0705d0705d0705d078888,0x072090720903d0f072091048103d0fa8a8,0x0750903d0f05d0705d078888,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x06d0b0550106d0be000,0x05d070650105d07e000,0x04501105d003d0f10570103f003d0fa8a8,0x07c0d07c0d07c0107c0d07c0d07c018a8a,0x04d0307a0d07a0107a0d07a0d07a018a8a]⟩
def n29 : Entry := ⟨7, [272,304,323,405,422], 3572, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0450103d0f1001,0x0000,0x0000,0x0000,0x015011000,0x025011000,0x0000,0x105a007c0d1001,0x0000,0x0000]⟩
def n30 : Entry := ⟨6, [272,304,323,405,422,951], 5492, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n31 : Entry := ⟨7, [272,304,323,405,934], 2548, [0x06d1b07a1d2020,0x05d1707a1d2020,0x0000,0x0000,0x03d0f06d1b2020,0x03d0f05d172020,0x07a1d07a1d2020,0x06d1b07c1d0440,0x05d1707c1d0440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x06d1b03d0f2020,0x05d1703d0f2020,0x0450103d0f0060,0x07c0107c010202,0x03a0103a010202]⟩
def n32 : Entry := ⟨9, [272,304,340], 1020, [0x0750507505075050750507a0507505a8a8,0x06d0306d0306d0306d0307a0506d03a8a8,0x06d0306d0306d0306d0306d0306d0307505100c006d03acf8,0x05d0305d0305d0305d0307a0505d03a8a8,0x05d0305d0305d0305d0305d0305d0307505100c205d03acf8,0x05d0305d0305d0306d0305d0305d0305d0305d03ca0f,0x03d070790707a0503d078888,0x03d070750507505075051033303d078cc8,0x03d0706d0306d0306d031063003d078cc8,0x03d0705d0305d0305d031063203d078cc8,0x07a0507a050790707a0507a0507907a8a8,0x0750507c050750505d030750507505c88c,0x06d0306d0306d0306d0307c0506d038cc8,0x05d0305d0305d0305d0307c0505d038cc8,0x07c0503d0707c0503d078888,0x07a05079070790507a0507907079058a8a,0x0750507a0507505e000,0x06d0306d0306d0306d0306d030720506d031045c06d03acf8,0x05d0305d0305d0305d0305d030720505d031045e05d03acf8,0x072050720503d07072051069003d07a8a8,0x0750503d0703d0505d0305d0303d058a8a,0x07a0507a05079070790307a0507a050790707903aaaa,0x0750507505075050750507501075010750504d0307505105400750507501affa,0x05d0305d0305d03e000,0x05d0306d0305d03e000,0x04d0304d0303d0703d0304d03108a003d0703d03aaaa,0x07c0507c0507c0507c0107c0507c0507c0507c01aaaa,0x04d0304d0304d0304d03072010720104d0304d03072051096004d0304d03affa]⟩
def n33 : Entry := ⟨8, [272,304,340,356], 2028, [0x0750d07a0d2020,0x05d0b07a0d2020,0x05d0b05d0b05d0b0750d100f22470,0x03d0707a0d2020,0x03d0703d0703d070750d100f32470,0x03d0703d0703d0705d0b106602470,0x07a0d07a0d2020,0x07c0d0750d4004,0x05d0b07c0d0440,0x03d0707c0d0440,0x0790d0790d0202,0x07a0d0750d6000,0x05d0b05d0b0720d05d0b102842470,0x03d0703d070720d03d07102852470,0x03d0503d050202,0x07a0d07a0d2020,0x0750d0750d04d030750d102d12470,0x06d0305d0b6000,0x04d0303d0303d0703d0303d034207,0x07c0d07c0d2020,0x04d0304d0304d030720d1039d2470,0x07a0d07a0d2020,0x0750d0750d02d030750d102d02470,0x02d0305d0305d0b05d0305d034207,0x06d0303d076000,0x07c0d07c0d2020,0x02d0302d0302d030720d1039c2470,0x03d0305d0303d0303d0703d034207]⟩
def n34 : Entry := ⟨7, [272,304,340,356,357], 3980, [0x0751d07a1d2020,0x07a1d07a1d2020,0x07c1d0751d4004,0x0791d0791d0202,0x07a1d0751d6000,0x03d0503d050202,0x07a1d07a1d2020,0x0751d0751d04d030751d101512470,0x07c1d07c1d2020,0x04d0304d0304d030721d101932470,0x07a1d07a1d2020,0x0751d0751d02d030751d101502470,0x07c1d07c1d2020,0x02d0302d0302d030721d101922470,0x03d0305d0303d0303d0703d034207,0x07a1d07a1d2020,0x0751d0751d01d030751d101522470,0x07c1d07c1d2020,0x01d0301d0301d030721d101942470,0x03d0306d0303d0303d0703d034207,0x05d0306d0305d0305d0b05d034207]⟩
def n35 : Entry := ⟨8, [272,304,340,390], 1788, [0x0750d07a0d2020,0x06d0b07a0d2020,0x06d0b06d0b06d0b0750d102702470,0x05d0b07a0d2020,0x05d0b05d0b05d0b0750d102722470,0x05d0b06d0b05d0b05d0b05d0b4207,0x03d0707a0d2020,0x0000,0x03d0703d0703d0706d0b102852470,0x03d0703d0703d0705d0b102872470,0x07a0d07a0d2020,0x0000,0x06d0b07c0d0440,0x05d0b07c0d0440,0x0000,0x07a0d0790b07a0d0790b2222,0x0750d0750d075090750904d0b0750d10481075092772,0x05d0b05d0b6000,0x06d0b05d0b6000,0x03d0703d0703d0303d0304d0b03d071048f03d032772,0x07c0d07c0907c0d07c092222,0x07905079050202,0x03a050750d6000,0x06d0b06d0b106c006d0b1039c2470,0x05d0b05d0b106c205d0b1039e2470,0x0720503d076000,0x03d0503d050202,0x0320104d0b0320104d0b107e004d0b1072004d0b7474]⟩
def n36 : Entry := ⟨7, [272,304,340,390,420], 3820, [0x0000,0x0000,0x102a20010,0x0000,0x0000,0x102b70010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x05d1b106f00110,0x0000,0x0000,0x032011000,0x0000,0x02a011000,0x05d0b0001,0x062011000,0x0000,0x05d0b0001,0x0000]⟩
def n37 : Entry := ⟨6, [272,304,340,390,420,421], 6860, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x05d0b0001]⟩
def n38 : Entry := ⟨7, [272,304,340,390,425], 2300, [0x0751d07a1d2020,0x06d1b07a1d2020,0x0000,0x05d1b07a1d2020,0x0000,0x0000,0x03d1707a1d2020,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x107500790107a1d07901079014207,0x107800751d6000,0x1078606d1b6000,0x1078805d1b6000,0x1078903d176000,0x107b003d0103d1703d0103d014207]⟩
def n39 : Entry := ⟨6, [272,304,340,390,425,946], 6392, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d370001,0x0000,0x0000,0x0000,0x0000,0x0000,0x079010100]⟩
def n40 : Entry := ⟨6, [272,304,340,390,425,947], 6388, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n41 : Entry := ⟨6, [272,304,340,390,425,951], 6268, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a3d0001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n42 : Entry := ⟨7, [272,304,340,390,425], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x108100790b1001,0x108401000,0x0000,0x0000,0x108551000,0x1087003d031001,0x0000]⟩
def n43 : Entry := ⟨6, [272,304,340,390,425,946], 5368, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n44 : Entry := ⟨6, [272,304,340,390,425,947], 5364, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n45 : Entry := ⟨6, [272,304,340,390,425,951], 5244, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n46 : Entry := ⟨8, [272,304,340,406], 1532, [0x0750d07a0d2020,0x06d0b07a0d2020,0x06d0b06d0b06d0b0750d103002470,0x05d0b07a0d2020,0x05d0b05d0b05d0b0750d103022470,0x0000,0x03d0707a0d2020,0x03d0703d0703d070750d103032470,0x0000,0x0000,0x07a0d07a0d2020,0x07c0d0750d4004,0x06d0b07c0d0440,0x05d0b07c0d0440,0x03d0707c0d0440,0x0790d0790d0202,0x07a0d0750d6000,0x06d0b06d0b0720d06d0b1048c2470,0x05d0b05d0b0720d05d0b1048e2470,0x03d0703d070720d03d071048f2470,0x03d0503d050202,0x07a0d0790307a0d079032222,0x0750d0750d0750107501108d00750d103f0075012772,0x01d0306d0b6000,0x02d0305d0b6000,0x04d0303d076000,0x07c0d07c0107c0d07c012222,0x0720d0720d0720107201109000720d10720072012772]⟩
def n47 : Entry := ⟨7, [272,304,340,406,419], 3572, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x015011000,0x025011000,0x045011000,0x07c0d0001,0x0000,0x075011000]⟩
def n48 : Entry := ⟨7, [272,304,340,406,424], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0790d0001,0x0000,0x109301000,0x109321000,0x109331000,0x03d050001,0x072011000]⟩
def n49 : Entry := ⟨6, [272,304,340,406,424,948], 5356, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n50 : Entry := ⟨8, [272,304,340,408], 1276, [0x0750d0750d0750d0750d07a0d0750da8a8,0x06d0b06d0b06d0b06d0b07a0d06d0ba8a8,0x06d0b06d0b06d0b06d0b8888,0x05d0b05d0b05d0b05d0b07a0d05d0ba8a8,0x05d0b05d0b05d0b05d0b8888,0x05d0b05d0b05d0b05d0b8888,0x03d0f0790f07a0d03d0f8888,0x03d0f0750d0750d0750d1039303d0f8cc8,0x03d0f06d0b06d0b06d0b1039d03d0f8cc8,0x03d0f05d0b05d0b05d0b103a003d0f8cc8,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x0750d0750d05d0b0750d8888,0x06d0b06d0b06d0b06d0b8888,0x05d0b05d0b05d0b05d0b8888,0x07c0d03d0f07c0d03d0f8888,0x07a0d0790f0790107a0d0790f079018a8a,0x0750d04a010750de000,0x06d0b0520106d0be000,0x05d0b0620105d0be000,0x10a8010a5003d0f109901072003d0fa8a8,0x07c0d03d0f03d0105d0b05d0b03d018a8a]⟩
def n51 : Entry := ⟨7, [272,304,340,408,422], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x107891000,0x0000,0x109c00790f1001,0x109f01000,0x109f61000,0x109f81000,0x0000,0x10a2003d0f1001,0x0000]⟩
def n52 : Entry := ⟨6, [272,304,340,408,422,946], 5368, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n53 : Entry := ⟨6, [272,304,340,408,422,947], 5364, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n54 : Entry := ⟨6, [272,304,340,408,422,951], 5244, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n55 : Entry := ⟨7, [272,304,340,408,934], 2300, [0x0751d07a1d2020,0x06d1b07a1d2020,0x0000,0x05d1b07a1d2020,0x0000,0x0000,0x0000,0x03d0f0751d2020,0x03d0f06d1b2020,0x03d0f05d1b2020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x07901079010202,0x0751d03d0f2020,0x06d1b03d0f2020,0x05d1b03d0f2020,0x1078903d0f0060,0x03d0103d010202]⟩
def n56 : Entry := ⟨7, [272,304,340,408,934], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x103c30010,0x103cd0010,0x103d00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x107890010,0x0000,0x0000,0x04a0103d0f1001,0x0520103d0f1001,0x0620103d0f1001,0x0000,0x0000,0x0000]⟩
def n57 : Entry := ⟨9, [272,304,388], 764, [0x0750507505075050750507a0507505a8a8,0x06d0306d0306d0306d0307a0506d03a8a8,0x06d0306d0306d0306d038888,0x05d070790707a0505d078888,0x05d070750507505075051045205d078cc8,0x05d0706d0306d0306d031045c05d078cc8,0x03d070790707a0503d078888,0x03d070750507505075051045303d078cc8,0x03d0706d0306d0306d031045d03d078cc8,0x03d0705d071069403d078888,0x07a0507a050790707a0507a0507907a8a8,0x075050750506d03075058888,0x06d0306d0306d0306d038888,0x07c0505d0707c0505d078888,0x07c0503d0707c0503d078888,0x07a05079070790107a0507907079018a8a,0x0750506a0107505e000,0x06d030720106d03e000,0x0620110b7005d0710ae01096005d07a8a8,0x0620110b7103d0710ae11096103d07a8a8,0x07c0503d0703d0106d0306d0303d018a8a]⟩
def n58 : Entry := ⟨8, [272,304,388,405], 1788, [0x0750d07a0d2020,0x06d0b07a0d2020,0x0000,0x05d0707a0d2020,0x05d0705d070440,0x05d0705d070440,0x0000,0x0750d104b30440,0x06d0b104bd0440,0x05d07106c40440,0x07a0d07a0d2020,0x0000,0x0000,0x0000,0x0000,0x07a0d0790f07a0d0790f2222,0x06a090750d6000,0x0720906d0b6000,0x0620105d070620105d0705d0705d077206,0x0620103d0f10b1003d0f2222,0x07c0d03d0f05d0705d072222,0x07a0d0790707a0d079072222,0x04a010750d04a017000,0x0520106d0b052017000,0x0620105d076000,0x10b4003d07107e403d072222,0x07c0d03d0705d0703d072222,0x05d0705d076000]⟩
def n59 : Entry := ⟨7, [272,304,388,405,406], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x106f40010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x109f91000,0x0000,0x0000,0x0000,0x0000,0x109f81000,0x0000,0x0000,0x03d0f03d070011]⟩
def n60 : Entry := ⟨7, [272,304,388,405,934], 2812, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x104e30010,0x104ed0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x109f90010,0x0000,0x0000,0x04a0103d071001,0x0520103d071001,0x0000,0x0000,0x0000,0x03d0f03d070011]⟩
def n61 : Entry := ⟨8, [272,304,388,917], 1276, [0x0750d0750d0750d0750d07a0d0750da8a8,0x06d0b06d0b06d0b06d0b07a0d06d0ba8a8,0x06d0b06d0b06d0b06d0b8888,0x05d0705d0705d0705d078888,0x05d0705d0705d0705d070750d05d07a8a8,0x05d0705d0705d0705d0706d0b05d07a8a8,0x03d0f0790f07a0d03d0f8888,0x03d0f0750d0750d0750d1051303d0f8cc8,0x03d0f06d0b06d0b06d0b1051d03d0f8cc8,0x03d0f05d0705d0703d0f8888,0x07a0d07a0d0790f07a0d07a0d0790fa8a8,0x0750d0750d05d070750d8888,0x06d0b06d0b06d0b06d0b8888,0x05d0705d0705d0705d078888,0x07c0d03d0f07c0d03d0f8888,0x07a0d0790f0790107a0d0790f079018a8a,0x0750d0750d05d0705d0705d0705d07a8a8,0x06d0b06d0b05d0705d0705d0705d07a8a8,0x05d070620105d0700e0,0x062010620103d0f0620110ba003d0fa8a8,0x07c0d05d0705d0105d0705d0705d018a8a]⟩
def n62 : Entry := ⟨7, [272,304,388,917,422], 2300, [0x0751d07a1d2020,0x06d1b07a1d2020,0x0000,0x0000,0x05d170751d2020,0x05d1706d1b2020,0x03d0f07a1d2020,0x0000,0x0000,0x03d0f05d172020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x07901079010202,0x0751d05d172020,0x06d1b05d172020,0x03d0f05d172020,0x0620103d0f6000,0x05d0105d010202]⟩
def n63 : Entry := ⟨10, [272,323], 509, [0x079030790307a0307a030790307903c88c,0x07501075010750107501075010750107a031009007501acf8,0x0750107501075010750107a0307501a8a8,0x06d0106d0106d0106d0106d0106d0107a031009606d01acf8,0x06d0106d0106d0106d0107a0306d01a8a8,0x06d0106d0106d010750106d0106d0106d0106d01ca0f,0x05d0307a0307a0307a031060805d038cc8,0x05d030790307a0305d038888,0x05d0307501075010750110c0005d038cc8,0x05d0306d0106d0106d0110c0605d038cc8,0x03d0307a0307a0307a031060903d038cc8,0x03d030790307a0303d038888,0x03d0307501075010750110c0103d038cc8,0x03d0306d0106d0106d0110c0703d038cc8,0x03d0305d0310db003d038888,0x03d0303d0303d03e000,0x07a0307a030790307a0307a0307903a8a8,0x0750107501075010750107c03075018cc8,0x06d0106d0106d0106d0107c0306d018cc8,0x07c0305d0307c0305d038888,0x07c0303d0307c0303d038888,0x07a0307a0307a0307a0307a0107a0107a030650107a0310ab007a0307a01affa,0x07a0307a03079030790107a0307a030790307901aaaa,0x06d0106d0106d01e000,0x06d010750106d01e000,0x065010650105d0305d010650110f0005d0305d01aaaa,0x065010650103d0303d010650110f0103d0303d01aaaa,0x07c0307c0307c0307c0107c0307c0307c0307c01aaaa]⟩
def n64 : Entry := ⟨9, [272,323,339], 1013, [0x079070790707a0707a070790707907c88c,0x06d0506d0506d0506d0506d0506d0507a07100c606d05acf8,0x06d0506d0506d0506d0507a0706d05a8a8,0x05d0305d0305d0305d0305d0305d0307a07100c805d03acf8,0x05d0305d0305d0305d0307a0705d03a8a8,0x05d0305d0305d0305d0305d0305d0306d0510c3005d03acf8,0x03d0707a0707a0707a071063903d078cc8,0x03d070790707a0703d078888,0x03d0706d0506d0506d0510cc003d078cc8,0x03d0705d0305d0305d0310cc203d078cc8,0x03d0703d0703d07e000,0x07a0707a070790707a0707a0707907a8a8,0x06d0506d0506d0506d0507c0706d058cc8,0x05d0305d0305d0305d0307c0705d038cc8,0x07c0703d0707c0703d078888,0x07a0707a0707a0707a0707a070650107a071045207a07acf8,0x07a0707a070790707a0707a0707907a8a8,0x06d050750106d05e000,0x05d030650105d0305d0105d0305d0305d0305d0105d01ca8f,0x065010650103d070650110d2003d07a8a8,0x07c0707c0707c0707c0707c0707c07a8a8,0x07a0707a0707a0707a0707a070550107a071045007a07acf8,0x07a0707a070790707a0707a0707907a8a8,0x06d050550106d0506d0105d0306d0506d0506d0106d01ca8f,0x05d030750105d03e000,0x055010550103d070550110d2203d07a8a8,0x07c0707c0707c0707c0707c0707c07a8a8,0x05d0305d0106d0506d0105d0305d0305d0105d0305d01ca8f]⟩
def n65 : Entry := ⟨8, [272,323,339,340], 1989, [0x0790f0790f07a0f07a0f0790f0790fc88c,0x03d0f07a0f07a0f07a0f1066903d0f8cc8,0x03d0f0790f07a0f03d0f8888,0x03d0f03d0f03d0fe000,0x07a0f07a0f0790f07a0f07a0f0790fa8a8,0x07c0f03d0f07c0f03d0f8888,0x07a0f07a0f07a0f07a0f07a0f0650107a0f101b207a0facf8,0x07a0f07a0f0790f07a0f07a0f0790fa8a8,0x065010650103d0f0650110c6003d0fa8a8,0x07c0f07c0f07c0f07c0f07c0f07c0fa8a8,0x07a0f07a0f07a0f07a0f07a0f0550107a0f101b007a0facf8,0x07a0f07a0f0790f07a0f07a0f0790fa8a8,0x055010550103d0f0550110c6203d0fa8a8,0x07c0f07c0f07c0f07c0f07c0f07c0fa8a8,0x05d0305d0106d0506d0105d0305d0305d0105d0305d01ca8f,0x07a0f07a0f07a0f07a0f07a0f04d0107a0f101b607a0facf8,0x07a0f07a0f0790f07a0f07a0f0790fa8a8,0x04d0104d0103d0f04d0110c6c03d0fa8a8,0x07c0f07c0f07c0f07c0f07c0f07c0fa8a8,0x05d0305d01075090750105d0305d0305d0105d0305d01ca8f,0x06d0506d01075090750105d0306d0506d0106d0506d01ca8f]⟩
def n66 : Entry := ⟨7, [272,323,339,340,390], 3781, [0x0791f0791f4004,0x03d0f03d0f03d0f07a1f1015b2470,0x03d0f07a1f2020,0x03d0f03d0f6000,0x07a1f07a1f2020,0x03d0f07c1f0440,0x07a1f07a1f0551107a1f101e02470,0x07a1f07a1f2020,0x0000,0x07c1f07c1f2020,0x07a1f07a1f04d1107a1f101e62470,0x07a1f07a1f2020,0x0000,0x07c1f07c1f2020,0x0000,0x07a1f07a1f10c9007a1f101822470,0x07a1f07a1f2020,0x0650103d0f6000,0x07c1f07c1f2020,0x02d0105d0105d1305d0105d014207,0x0350105d0105d1305d0105d014207]⟩
def n67 : Entry := ⟨6, [272,323,339,340,390,432], 7876, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x05d330001,0x05d330001,0x0000,0x062011000,0x0000,0x02a011000,0x032011000,0x0000]⟩
def n68 : Entry := ⟨8, [272,323,339,356], 2021, [0x0790f0790f4004,0x05d0b05d0b05d0b07a0f100f82470,0x05d0b07a0f2020,0x03d0703d0703d0707a0f100ff2470,0x03d0707a0f2020,0x03d0703d0703d0705d0b10cf02470,0x03d0703d076000,0x07a0f07a0f2020,0x05d0b07c0f0440,0x03d0707c0f0440,0x07a0f07a0f0650107a0f103622470,0x07a0f07a0f2020,0x0650105d0b4004,0x0650103d074004,0x07c0f07c0f2020,0x07a0f07a0f0550907a0f102712470,0x07a0f07a0f2020,0x0750905d0b6000,0x03d0703d070550903d0710c632470,0x07c0f07c0f2020,0x06d0105d0b0202,0x07a0f07a0f02d0507a0f102762470,0x07a0f07a0f2020,0x05d0b05d0b02d0505d0b10c6c2470,0x06d0503d076000,0x07c0f07c0f2020,0x0750103d070202,0x02d010550102d0102d0502d014207]⟩
def n69 : Entry := ⟨7, [272,323,339,356,357], 3973, [0x0791f0791f4004,0x03d0703d076000,0x07a1f07a1f2020,0x07a1f07a1f0651107a1f101242470,0x07a1f07a1f2020,0x07c1f07c1f2020,0x07a1f07a1f0550907a1f101212470,0x07a1f07a1f2020,0x07c1f07c1f2020,0x0000,0x07a1f07a1f02d0507a1f101262470,0x07a1f07a1f2020,0x07c1f07c1f2020,0x0000,0x02d010550102d0102d0502d014207,0x07a1f07a1f01d0307a1f101282470,0x07a1f07a1f2020,0x07c1f07c1f2020,0x01d010650101d0101d0301d014207,0x0000,0x0000]⟩
def n70 : Entry := ⟨8, [272,323,339,390], 1781, [0x0790f0790f4004,0x06d0d06d0d06d0d07a0f102d62470,0x06d0d07a0f2020,0x05d0b05d0b05d0b07a0f103082470,0x05d0b07a0f2020,0x05d0b05d0b05d0b06d0d10c602470,0x03d0703d0703d0707a0f102db2470,0x03d0707a0f2020,0x0000,0x03d0703d0703d0705d0b10c652470,0x03d0703d076000,0x07a0f07a0f2020,0x06d0d07c0f0440,0x05d0b07c0f0440,0x03d0707c0f0440,0x07a0f07a0f0550907a0f104802470,0x07a0f07a0f2020,0x0000,0x0750905d0b6000,0x0000,0x07c0f07c0f2020,0x07a0f07a0f10d5007a0f103922470,0x07a0f07a0f2020,0x0350106d0d6000,0x0250105d0105d0b05d0105d014207,0x0650103d076000,0x07c0f07c0f2020,0x02d0105d0105d0b05d0105d014207]⟩
def n71 : Entry := ⟨7, [272,323,339,390,416], 3828, [0x0000,0x0000,0x10c900010,0x0000,0x0000,0x10c950010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0250105d1b1001,0x0000,0x0000,0x05d1b0001,0x0000,0x032011000,0x10d801000,0x062011000,0x0000,0x02a011000,0x0000]⟩
def n72 : Entry := ⟨6, [272,323,339,390,416,949], 5844, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x062011000,0x0000,0x0000,0x0000]⟩
def n73 : Entry := ⟨9, [272,323,357], 1021, [0x07907079074004,0x07505075050750507a07103302470,0x0750507a072020,0x06d0506d0506d0507a07103362470,0x06d0507a072020,0x06d050750506d0506d0506d054207,0x05d0305d0305d0307a07103402470,0x05d0307a072020,0x05d0305d0305d030750510cc22470,0x05d0305d0305d0306d0510ccc2470,0x03d0303d0303d0307a07103412470,0x03d0307a072020,0x03d0303d0303d030750510cc32470,0x03d0303d0303d0306d0510ccd2470,0x03d0305d0303d0303d0303d034207,0x03d0303d036000,0x07a0707a072020,0x0750507c070440,0x06d0507c070440,0x05d0307c070440,0x03d0307c070440,0x07a0707a0707a0507a050650507a071069407a052772,0x07a070790507a07079052222,0x06d0506d056000,0x0750506d056000,0x05d0305d0305d0105d010650505d0310d2a05d012772,0x03d0303d0303d0103d010650503d0310d2b03d012772,0x07c0707c0507c0707c052222,0x07a0707a0707a0307a0301d0307a071069807a032772,0x07a070790307a07079032222,0x0750507505075010750101d030750510d22075012772,0x06d0506d0506d0106d0101d0306d0510d2c06d012772,0x03d0303d036000,0x05d0303d036000,0x07c0707c0307c0707c032222,0x01d0101d0301d0101d03065010650101d030650510de001d0101d0301d017777]⟩
def n74 : Entry := ⟨8, [272,323,357,408], 1277, [0x0790f0790f4004,0x0750d0750d0750d07a0f103f02470,0x0750d07a0f2020,0x06d0d06d0d06d0d07a0f103f62470,0x06d0d07a0f2020,0x0000,0x05d0b05d0b05d0b07a0f103f82470,0x05d0b07a0f2020,0x0000,0x0000,0x03d0b03d0b03d0b07a0f103f92470,0x03d0b07a0f2020,0x0000,0x0000,0x0000,0x03d0b03d0b6000,0x07a0f07a0f2020,0x0750d07c0f0440,0x06d0d07c0f0440,0x05d0b07c0f0440,0x03d0b07c0f0440,0x07a0f07a0f07a0107a0110e1007a0f1072007a012772,0x07a0f0790107a0f079012222,0x00d010750d6000,0x0150106d0d6000,0x0250105d0b6000,0x0450103d0b6000,0x10ed007c0f10e7007c0107c0f07c0f07c0107c017227]⟩
def n75 : Entry := ⟨7, [272,323,357,408,416], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x107b007c0f1001,0x0790f0001,0x10e401000,0x10e461000,0x10e481000,0x10e491000,0x03d0b0001,0x07a011000]⟩
def n76 : Entry := ⟨6, [272,323,357,408,416,947], 5364, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n77 : Entry := ⟨7, [272,323,357,408,935], 2173, [0x0791f0791f4004,0x0751d0751d0440,0x0000,0x06d1d06d1d0440,0x0000,0x0000,0x05d1b05d1b0440,0x0000,0x0000,0x0000,0x03d1b03d1b0440,0x0000,0x0000,0x0000,0x0000,0x10ea007a1f0060,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x0000]⟩
def n78 : Entry := ⟨6, [272,323,357,408,935,432], 6268, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0791f0001,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n79 : Entry := ⟨7, [272,323,357,408,935], 3197, [0x0000,0x104200010,0x0000,0x104260010,0x0000,0x0000,0x104280010,0x0000,0x0000,0x0000,0x104290010,0x0000,0x0000,0x0000,0x0000,0x07a1f107b00110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07c010100]⟩
def n80 : Entry := ⟨9, [272,323,389], 765, [0x079070790707a0707a070790707907c88c,0x07505075050750507505075050750507a071054007505acf8,0x0750507505075050750507a0707505a8a8,0x06d0506d0506d0506d0506d0506d0507a071054606d05acf8,0x06d0506d0506d0506d0507a0706d05a8a8,0x06d0506d0505d0306d058888,0x05d0305d0305d0305d0305d0305d0307a071054805d03acf8,0x05d0305d0305d0305d0307a0705d03a8a8,0x05d0305d0305d0305d038888,0x05d0305d0305d0305d038888,0x03d0707a0707a0707a07108a903d078cc8,0x03d070790707a0703d078888,0x03d0707505075050750510d2103d078cc8,0x03d0706d0506d0506d0510d2703d078cc8,0x03d0705d0305d0305d0310d2a03d078cc8,0x03d0703d0703d07e000,0x07a0707a070790707a0707a0707907a8a8,0x0750507505075050750507c07075058cc8,0x06d0506d0506d0506d0507c0706d058cc8,0x05d0305d0305d0305d0307c0705d038cc8,0x07c0703d0707c0703d078888,0x07a0707a0707a0707a0707a0107a0107a0710f3007a071096007a0707a01affa,0x07a0707a07079070790107a0707a070790707901aaaa,0x0750504d0107505e000,0x06d050550106d05e000,0x05d030650105d03e000,0x045011102003d0703d0110fc010de003d0703d01aaaa,0x07c0707c0707c0707c0107c0707c0707c0707c01aaaa]⟩
def n81 : Entry := ⟨8, [272,323,389,400], 1788, [0x0750d07a072020,0x06d0d07a072020,0x0000,0x05d0b07a072020,0x0000,0x0000,0x0000,0x0750d10d510440,0x06d0d10d570440,0x05d0b10d5a0440,0x07a0707a072020,0x0750d07c070440,0x06d0d07c070440,0x05d0b07c070440,0x0000,0x07a070790f07a070790f2222,0x04d090750d6000,0x0550906d0d6000,0x0650905d0b6000,0x0450103d0f10f6003d0f2222,0x07c0707c0705d0b07c072222,0x07907079070202,0x04a010750d04a017000,0x0520106d0d052017000,0x0620105d0b062017000,0x10f90109092020,0x03d0703d070202,0x07a0707a0707a017000]⟩
def n82 : Entry := ⟨7, [272,323,389,400,406], 3324, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10e491000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10a2007c071001,0x07a0103d0f0110]⟩
def n83 : Entry := ⟨7, [272,323,389,400,934], 2812, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10d810010,0x10d870010,0x10d8a0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0f10e490110,0x0000,0x0000,0x04a011000,0x052011000,0x062011000,0x0000,0x0000,0x07a0103d0f1010]⟩
def n84 : Entry := ⟨8, [272,323,389,406], 1789, [0x0000,0x105700010,0x0000,0x105760010,0x0000,0x0000,0x105780010,0x0000,0x0000,0x0000,0x108d90010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a0f10f600110,0x0000,0x0000,0x0000,0x0000,0x0450103d071001,0x0000,0x07a07109090110,0x0000,0x00d011000,0x015011000,0x025011000,0x0000,0x10ff007c071001,0x03d011000]⟩
def n85 : Entry := ⟨7, [272,323,389,406,935], 2685, [0x0000,0x105a00010,0x0000,0x105a60010,0x0000,0x0000,0x105a80010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1f10a200110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n86 : Entry := ⟨8, [272,323,389,918], 1277, [0x0790f0790f4004,0x0750d0750d0750d07a0f105d02470,0x0750d07a0f2020,0x06d0d06d0d06d0d07a0f105d62470,0x06d0d07a0f2020,0x0000,0x05d0b05d0b05d0b07a0f105d82470,0x05d0b07a0f2020,0x0000,0x0000,0x03d0703d070440,0x0000,0x03d070750d2020,0x03d0706d0d2020,0x03d0705d0b2020,0x03d0703d076000,0x07a0f07a0f2020,0x0750d07c0f0440,0x06d0d07c0f0440,0x05d0b07c0f0440,0x0000,0x07a0f07a0f07a0107a010450107a0f1105007a012772,0x07a0f0790107a0f079012222,0x0750d03d0103d0703d012222,0x06d0d03d0103d0703d012222,0x05d0b03d0103d0703d012222,0x0450103d070060,0x07c0f07c0107c0f07c012222]⟩
def n87 : Entry := ⟨7, [272,323,389,918,416], 2300, [0x0751d07a0f2020,0x06d1d07a0f2020,0x0000,0x05d1b07a0f2020,0x0000,0x0000,0x0000,0x03d170751d2020,0x03d1706d1d2020,0x03d1705d1b2020,0x07a0f07a0f2020,0x0000,0x0000,0x0000,0x0000,0x07901079010202,0x0751d03d172020,0x06d1d03d172020,0x05d1b03d172020,0x03d1703d172020,0x03d0103d010202]⟩
def n88 : Entry := ⟨11, [784], 253, [0x079010790107901079018888,0x075010750107501075018888,0x075010750107501075018888,0x06d0106d0106d0106d018888,0x06d0106d0106d0106d018888,0x06d0106d0106d0106d018888,0x05d0105d0105d0105d018888,0x05d0105d0105d0105d018888,0x05d0105d0105d0105d018888,0x05d0105d0105d0105d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0107a0100e0,0x03d0103d0103d0103d0103d0103d0107901110b003d01acf8,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888]⟩
def n89 : Entry := ⟨10, [784,370], 377, [0x075010750107501075018888,0x06d0106d0106d0106d018888,0x06d0106d0106d0106d018888,0x05d0105d0105d0105d018888,0x05d0105d0105d0105d018888,0x05d0105d0105d0105d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x03d0103d0103d0103d018888,0x079010790107901079018888,0x075010750107501075018888,0x06d0106d0106d0106d018888,0x05d0105d0105d0105d018888,0x03d0103d0103d0103d018888]⟩
def n90 : Entry := ⟨11, [304], 255, [0x03d02075010750107501075010750107a011006003d02acf8,0x0790207a0107a0107a0107a01079028cc8,0x0750103d02075010750107a0103d028cc8,0x07501075010750107a01075010750107501ca0e,0x0750103d020750103d028888,0x0750107501075010750107a0107501a8a8,0x06d0207a0107a0107a011111006d028cc8,0x06d0203d0206d0203d028888,0x06d020790207a0106d028888,0x06d020750107501075011189006d028cc8,0x05d0207a0107a0107a011111205d028cc8,0x05d0203d0205d0203d028888,0x05d020790207a0105d028888,0x05d020750107501075011189205d028cc8,0x05d0206d0211e9005d028888,0x03d0207a0107a0107a011111303d028cc8,0x03d0203d0203d0203d028888,0x03d020790207a0103d028888,0x03d020750107501075011189303d028cc8,0x03d0206d0211e9103d028888,0x03d0205d0211e9403d028888,0x075010750107501e000,0x075010750103d0203d01075010750103d0203d01aaaa,0x07a0107a01079020790107a0107a010790207901aaaa,0x0750107a0107501e000,0x072010720106d0206d01072011255006d0206d01aaaa,0x072010720105d0205d01072011255205d0205d01aaaa,0x072010720103d0203d01072011255303d0203d01aaaa]⟩
def n91 : Entry := ⟨10, [304,320], 510, [0x06d0203d0406d0206d0207a0103d048cc8,0x06d0203d0406d0203d048888,0x0750307503075030750307a0107503a8a8,0x06d0203d0406d0203d048888,0x06d0206d0206d0206d0207a0106d02a8a8,0x06d0206d0206d0206d0206d0206d02075031114006d02acf8,0x05d0403d0405d0403d048888,0x05d040790407a0105d048888,0x05d04075030750307503114a005d048cc8,0x05d0406d0206d0206d02114a605d048cc8,0x03d0403d0403d0403d048888,0x03d040790407a0103d048888,0x03d04075030750307503114a103d048cc8,0x03d0406d0206d0206d02114a703d048cc8,0x03d0405d041171003d048888,0x06d0206d0203d0406d0206d0203d04a8a8,0x07a0107a010790407a0107a0107904a8a8,0x0750307a0107503e000,0x06d020720106d0206d0106d0206d0206d0206d01ca8e,0x072010720105d0407201117a005d04a8a8,0x072010720103d0407201117a103d04a8a8,0x06d0206d0203d0406d0206d0203d04a8a8,0x07a0107a010790407a0107a0107904a8a8,0x0750306a01075030750106d02075030750307501ca8e,0x06d0207a0106d02e000,0x06a0106a0105d0406a01117a605d04a8a8,0x06a0106a0103d0406a01117a703d04a8a8,0x06d0206d01075030750106d0206d0206d0106d0206d01ca8f]⟩
def n92 : Entry := ⟨9, [304,320,323], 998, [0x06d0203d0806d0206d0207a0503d088cc8,0x05d0803d0805d0803d088888,0x05d080790807a0505d088888,0x03d0803d0803d0803d088888,0x03d080790807a0503d088888,0x03d0805d081117003d088888,0x06d0206d0203d0806d0206d0203d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x072010720105d0807201112f005d08a8a8,0x072010720103d0807201112f103d08a8a8,0x06d0206d0203d0806d0206d0203d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x06a0106a0105d0806a01112f605d08a8a8,0x06a0106a0103d0806a01112f703d08a8a8,0x06d0206d01075030750106d0206d0206d0106d0206d01ca8f,0x06d0203d0806d0203d088888,0x07a0507a050790807a0507a0507908a8a8,0x065010650105d0806501113e005d08a8a8,0x065010650103d0806501113e103d08a8a8,0x06d0206d0107a0507a0106d0206d0206d0106d02ca8e,0x075030750107a0507a0106d02075030750107503ca8e]⟩
def n93 : Entry := ⟨8, [304,320,323,357], 2022, [0x03d0807a0d0440,0x03d0803d082020,0x05d0807a0d2020,0x03d0803d082020,0x03d0807a0d2020,0x03d0805d0803d0803d0803d084207,0x03d0803d082020,0x07a0d07a0d2020,0x05d0805d080720905d08111a02470,0x03d0803d080720903d08111a12470,0x03d0803d082020,0x07a0d07a0d2020,0x05d0805d0806a0905d08111a62470,0x03d0803d0806a0903d08111a72470,0x06d090750906d0906d0a06d094207,0x0000,0x07a0d07a0d2020,0x05d0805d080650905d08112302470,0x03d0803d080650903d08112312470,0x06d0907a0906d0906d0a4206,0x0750907a09075090750b4206,0x03d0803d0803d0803d082222,0x07a0d0790807a0d079082222,0x03d0803d086000,0x05d0803d086000,0x01d0801d08072010720101d08072091126001d082772,0x01d0801d0806a0106a0101d0806a091126601d082772,0x01d0801d08065010650101d08065091129001d082772]⟩
def n94 : Entry := ⟨7, [304,320,323,357,373], 3910, [0x03d1807a1d0440,0x03d1803d182020,0x03d1807a1d2020,0x03d1803d182020,0x07a1d07a1d2020,0x03d1803d1806a1903d18111d02470,0x0000,0x07a1d07a1d2020,0x03d1803d180651903d18112002470,0x0000,0x0000,0x07a1d07a1d2020,0x05d0803d186000,0x0000,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x0520103d184004,0x0550106d1a4004,0x05a0106d1a4004,0x0720103d184004]⟩
def n95 : Entry := ⟨6, [304,320,323,357,373,390], 7686, [0x03d1807a3d0440,0x0000,0x07a3d07a3d2020,0x0000,0x07a3d07a3d2020,0x0000,0x03d1803d182020,0x07a3d07a3d2020,0x0000,0x0000,0x03d1803d182020,0x07a3d07a3d2020,0x0000,0x0000,0x02d010550102d0102d1202d014207]⟩
def n96 : Entry := ⟨6, [304,320,323,357,373,406], 7430, [0x03d1807a3d0440,0x03d1803d182020,0x07a3d07a3d2020,0x0000,0x07a3d07a3d2020,0x0000,0x03d1803d182020,0x07a3d07a3d2020,0x0000,0x0000,0x0000,0x07a3d07a3d2020,0x0000,0x0000,0x02d0105a0102d0102d124206]⟩
def n97 : Entry := ⟨7, [304,320,323,357,405], 3526, [0x03d1807a1d0440,0x03d1803d182020,0x03d1807a1d2020,0x03d1803d182020,0x07a1d07a1d2020,0x03d1803d180721903d18112012470,0x03d1803d182020,0x07a1d07a1d2020,0x03d1803d1806a1903d18112072470,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x05d0803d186000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0450103d184004,0x04d0107a1d4004,0x0550107a1d4004,0x0650103d184004]⟩
def n98 : Entry := ⟨7, [304,320,323,357,423], 2918, [0x03d1807a1d0440,0x0000,0x05d1807a1d2020,0x0000,0x03d1807a1d2020,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x0320105d186000,0x0520103d186000,0x0150106d0106d1a06d0106d014207,0x01a0106d0106d1a06d014206]⟩
def n99 : Entry := ⟨7, [304,320,323,357,425], 2534, [0x03d1807a1d0440,0x03d1803d182020,0x05d1807a1d2020,0x03d1803d182020,0x03d1807a1d2020,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x0000,0x0000,0x03d1803d182020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x112c003d184004,0x07a1d07a1d2020,0x0250105d186000,0x0450103d186000,0x00d0107a0107a1d07a014206,0x0150107a0107a1d07a014206]⟩
def n100 : Entry := ⟨6, [304,320,323,357,425,945], 6628, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n101 : Entry := ⟨8, [304,320,323,373], 1894, [0x05d0803d1005d0805d0807a0d03d108cc8,0x05d0803d1005d0803d108888,0x05d0805d0805d0805d0807a0d05d08a8a8,0x03d1003d1003d1003d108888,0x03d100791007a0d03d108888,0x03d1005d0805d0805d08111a003d108cc8,0x05d0805d0803d1005d0805d0803d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d0805d0805d0805d088888,0x06a0906a0903d1006a091132003d10a8a8,0x05d0803d1005d0803d108888,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d0805d0805d0805d088888,0x065090650903d10065091135003d10a8a8,0x0750b07a0d06d0a0750b8888,0x05d0805d0803d1005d0805d0803d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d080720105d08e000,0x05201113b003d10113801126003d10a8a8,0x055030550106d0a06d0106d0a06d0a06d0a06d0106d01ca8f,0x05a0505a0106d0a06d0106d0a06d0a06d0a06d01ca8e]⟩
def n102 : Entry := ⟨7, [304,320,323,373,390], 3686, [0x03d1007a1d0440,0x0000,0x05d1807a1d2020,0x0000,0x03d1007a1d2020,0x03d1003d1003d1005d18111d02470,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x0721105d186000,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x06a0903d106000,0x0000,0x02d010550102d0102d0a02d014207]⟩
def n103 : Entry := ⟨7, [304,320,323,373,406], 3430, [0x03d1007a1d0440,0x0000,0x05d1807a1d2020,0x03d1003d102020,0x03d1007a1d2020,0x03d1003d1003d1005d18112002470,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x0721105d186000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0650903d106000,0x0000,0x02d0105a0102d0102d0a4206]⟩
def n104 : Entry := ⟨7, [304,320,323,373,422], 3942, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0520103d101001,0x06d1a0001,0x06d1a0001,0x0000,0x0000,0x032011000,0x0000,0x0150106d0a1001,0x01a0106d0a1001,0x0000]⟩
def n105 : Entry := ⟨7, [304,320,323,373,934], 2918, [0x03d1007a1d0440,0x0000,0x05d1807a1d2020,0x0000,0x0000,0x03d1005d182020,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x05d1803d102020,0x0520103d100060,0x02d0102d010202,0x02d0102d010202]⟩
def n106 : Entry := ⟨8, [304,320,323,405], 1510, [0x05d0803d1005d0805d0807a0d03d108cc8,0x05d0805d0803d1005d0805d0803d10a8a8,0x05d0805d0805d0805d0807a0d05d08a8a8,0x03d1003d1003d1003d108888,0x03d100791007a0d03d108888,0x03d1005d0805d0805d081123003d108cc8,0x05d0805d0803d1005d0805d0803d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d0805d0805d0805d088888,0x072090720903d10072091135103d10a8a8,0x05d0805d0803d1005d0805d0803d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d0805d0805d0805d088888,0x06a0906a0903d1006a091135703d10a8a8,0x06d0a0750b06d0a06d0a8888,0x05d0803d1005d0803d108888,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x05d080650105d08e000,0x045011147003d10114101129003d10a8a8,0x04d0204d0107a0d07a0107a0d07a0d07a0d07a01ca8e,0x055030550107a0d07a0107a0d07a0d07a0d07a01ca8e]⟩
def n107 : Entry := ⟨7, [304,320,323,405,422], 3558, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0450103d101001,0x07a1d0001,0x07a1d0001,0x1144003d101001,0x0000,0x025011000,0x0000,0x00d0107a0d1001,0x0150107a0d1001,0x0000]⟩
def n108 : Entry := ⟨6, [304,320,323,405,422,945], 5604, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n109 : Entry := ⟨7, [304,320,323,405,934], 2534, [0x03d1007a1d0440,0x03d1003d102020,0x05d1807a1d2020,0x0000,0x0000,0x03d1005d182020,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x05d1803d102020,0x0450103d100060,0x03a0103a010202,0x03a0103a010202]⟩
def n110 : Entry := ⟨9, [304,320,339], 1014, [0x05d0403d0805d0405d0407a0503d088cc8,0x05d0403d0805d0403d088888,0x06d0606d0606d0606d0607a0506d06a8a8,0x05d0405d0403d0805d0405d0403d08a8a8,0x05d0405d0405d0405d0407a0505d04a8a8,0x05d0405d0405d0405d0405d0405d0406d06114d005d04acf8,0x03d0803d0803d0803d088888,0x03d080790807a0503d088888,0x03d0806d0606d0606d061156003d088cc8,0x03d0805d0405d0405d04115c003d088cc8,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x06d060720106d0606d0606d0606d06c88c,0x05d040720105d0405d0405d0405d04c88c,0x072010720103d08072011162003d08a8a8,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x06d0607a0506d06e000,0x05d0405d0405d0405d0405d0406a0505d04112f805d04acf8,0x06a0506a0503d0806a051165003d08a8a8,0x06d06075030750106d0606d0606d068a8a,0x05d0403d0805d0403d088888,0x07a0507a050790807a0507a0507908a8a8,0x06d0606d0606d0606d0606d060550306d06113e006d06acf8,0x05d040750305d04e000,0x055030550303d0805503116b003d08a8a8,0x05d0407a0507a0105d0405d0405d048a8a,0x05503055010550306a0104d02055030550105503ca8e]⟩
def n111 : Entry := ⟨8, [304,320,339,340], 1990, [0x05d0403d1005d0405d0407a0d03d108cc8,0x03d1003d1003d1003d108888,0x03d100791007a0d03d108888,0x05d0405d0403d1005d0405d0403d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x072090720903d10072091150003d10a8a8,0x05d0405d0403d1005d0405d0403d10a8a8,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x06a0506a0503d1006a051150603d10a8a8,0x06d060750b06d0606d068888,0x05d0403d1005d0403d108888,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x055030550303d10055031153003d10a8a8,0x05d0407a0d05d0405d048888,0x05503055010550306a0104d02055030550105503ca8e,0x05d0403d1005d0403d108888,0x07a0d07a0d0791007a0d07a0d07910a8a8,0x04d0204d0203d1004d021153603d10a8a8,0x04d0204d0104d020720104d0204d0204d0104d02ca8e,0x05d0407a0d05d0405d048888,0x06d060750b06d0606d068888]⟩
def n112 : Entry := ⟨7, [304,320,339,340,374], 3910, [0x03d1007a1d0440,0x0000,0x03d1007a1d2020,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x03d1003d1004d1203d101120f2470,0x0000,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x0720903d106000,0x0000,0x0000,0x0320104d0104d1204d014206]⟩
def n113 : Entry := ⟨7, [304,320,339,340,406], 3526, [0x03d1007a1d0440,0x03d1003d102020,0x03d1007a1d2020,0x03d1003d102020,0x07a1d07a1d2020,0x0000,0x03d1003d102020,0x07a1d07a1d2020,0x03d1003d1006a1503d10112092470,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0550303d106000,0x0000,0x0150106a0106a1506a014206,0x0000]⟩
def n114 : Entry := ⟨8, [304,320,339,356], 2022, [0x03d0807a0d0440,0x03d0803d082020,0x05d0c07a0d2020,0x03d0803d082020,0x03d0807a0d2020,0x03d0803d0803d0805d0c115902470,0x03d0803d082020,0x07a0d07a0d2020,0x0720905d0c4004,0x03d0803d080720903d08111af2470,0x03d0803d082020,0x07a0d07a0d2020,0x05d0c05d0c06a0505d0c111a82470,0x06a0503d084004,0x0000,0x0000,0x07a0d07a0d2020,0x0750b05d0c6000,0x03d0803d080550b03d08115312470,0x07a0905d0c0202,0x06a010550b0202,0x0000,0x07a0d07a0d2020,0x05d0c05d0c02d0605d0c115362470,0x06d0603d086000,0x0720102d060202,0x07a0503d080202,0x02d0602d0602d060550b112902470]⟩
def n115 : Entry := ⟨7, [304,320,339,356,357], 3974, [0x03d0807a1d0440,0x03d0803d082020,0x07a1d07a1d2020,0x03d0803d082020,0x07a1d07a1d2020,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x03d0803d082020,0x07a1d07a1d2020,0x0000,0x0000,0x0000,0x0000]⟩
def n116 : Entry := ⟨8, [304,320,339,357], 2006, [0x03d0807a0d0440,0x0000,0x06d0e07a0d2020,0x03d0803d082020,0x03d0807a0d2020,0x03d0803d0803d0806d0e115902470,0x03d0803d082020,0x07a0d07a0d2020,0x0720906d0e4004,0x03d0803d080720903d08115f02470,0x03d0803d082020,0x07a0d07a0d2020,0x07a0d06d0e6000,0x03d0803d0806a0d03d081150b2470,0x0750906d0e0202,0x0000,0x07a0d07a0d2020,0x06d0e06d0e0550306d0e112302470,0x0550303d084004,0x0000,0x05501055014004,0x03d0803d082020,0x07a0d07a0d2020,0x06d0e06d0e01d0406d0e115362470,0x05d0403d086000,0x0720101d040202,0x01d0401d0401d0406a0d112682470,0x0750303d080202]⟩
def n117 : Entry := ⟨7, [304,320,339,357,374], 3862, [0x03d0807a1d0440,0x0000,0x06d1e07a1d2020,0x03d0803d082020,0x07a1d07a1d2020,0x07a1d06d1e6000,0x0000,0x07a1d07a1d2020,0x06d1e06d1e0551306d1e112012470,0x0000,0x0000,0x07a1d07a1d2020,0x06d1e06d1e01d0406d1e1120f2470,0x0000,0x0000,0x03d0803d082020,0x07a1d07a1d2020,0x0320106d1e4004,0x0350106d1e4004,0x03a0105d144004,0x0720105d144004]⟩
def n118 : Entry := ⟨8, [304,320,339,374], 1910, [0x03d0807a0d0440,0x0000,0x06d0e07a0d2020,0x03d0803d082020,0x05d0c07a0d2020,0x05d0c05d0c05d0c06d0e115002470,0x0000,0x03d0807a0d2020,0x03d0803d0803d0806d0e111af2470,0x03d0803d0803d0805d0c115f02470,0x03d0803d082020,0x07a0d07a0d2020,0x07a0d06d0e6000,0x05d0c05d0c06a0d05d0c113242470,0x0000,0x0000,0x07a0d07a0d2020,0x06d0e06d0e0550b06d0e113512470,0x0750b05d0c6000,0x0000,0x0000,0x03d0803d082020,0x07a0d07a0d2020,0x0320106d0e4004,0x0320105d0c4004,0x0720103d086000,0x0350106d0e4004,0x03a0105d0c4004]⟩
def n119 : Entry := ⟨8, [304,320,339,390], 1782, [0x03d0807a0d0440,0x0000,0x06d0e07a0d2020,0x03d0803d082020,0x05d0c07a0d2020,0x05d0c05d0c05d0c06d0e115062470,0x0000,0x03d0807a0d2020,0x0000,0x03d0803d0803d0805d0c1150b2470,0x03d0803d082020,0x07a0d07a0d2020,0x0000,0x0720905d0c4004,0x0000,0x0000,0x07a0d07a0d2020,0x06d0e06d0e0550b06d0e113572470,0x0750b05d0c6000,0x03d0803d080550b03d08113592470,0x07a0905d0c0202,0x03d0803d082020,0x07a0d07a0d2020,0x03a0506d0e6000,0x05d0c05d0c1168005d0c112682470,0x06a0503d086000,0x07501075010202,0x02a01055010550b055014206]⟩
def n120 : Entry := ⟨7, [304,320,339,390,421], 3798, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x02a011000,0x0000,0x0000,0x01a011000,0x04a011000,0x0750b0001,0x0750b0001,0x0000]⟩
def n121 : Entry := ⟨8, [304,320,339,406], 1526, [0x03d0807a0d0440,0x0000,0x06d0e07a0d2020,0x03d0803d082020,0x05d0c07a0d2020,0x05d0c05d0c05d0c06d0e115302470,0x03d0803d082020,0x03d0807a0d2020,0x03d0803d0803d0806d0e115312470,0x0000,0x03d0803d082020,0x07a0d07a0d2020,0x0720906d0e4004,0x0000,0x0000,0x03d0803d082020,0x07a0d07a0d2020,0x07a0d06d0e6000,0x05d0c05d0c06a0d05d0c113582470,0x03d0803d0806a0d03d08113592470,0x0750906d0e0202,0x0000,0x07a0d07a0d2020,0x06d0e06d0e116e006d0e112902470,0x0350305d0c6000,0x0550303d086000,0x07a0107a010202,0x0150106a0106a0d06a014206]⟩
def n122 : Entry := ⟨7, [304,320,339,406,420], 3558, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x015011000,0x0000,0x0000,0x025011000,0x045011000,0x0000,0x07a0d0001,0x0000]⟩
def n123 : Entry := ⟨9, [304,320,357], 1022, [0x03d0407a050440,0x0000,0x0750707a052020,0x0000,0x06d0607a052020,0x06d0606d0606d0607507111702470,0x03d0403d042020,0x05d0407a052020,0x05d0405d0405d0407507115c02470,0x05d0405d0405d0406d06115c62470,0x03d0403d042020,0x03d0407a052020,0x03d0403d0403d0407507115c12470,0x03d0403d0403d0406d06115c72470,0x03d0405d0403d0403d0403d044207,0x03d0403d042020,0x07a0507a052020,0x07a05075076000,0x0720506d0506d0606d054206,0x05d0405d040720505d04116342470,0x03d0403d040720503d04116352470,0x03d0403d042020,0x07a0507a052020,0x06a050750507507075054206,0x07a0506d066000,0x05d0405d0406a0505d041162a2470,0x03d0403d0406a0503d041162b2470,0x06d050750506d0506d0606d054207,0x03d0403d0403d0403d042222,0x07a050790407a05079042222,0x0750707507075030750301d0407507116b0075032772,0x06d0606d0606d0206d0201d0406d06116b606d022772,0x03d0403d046000,0x05d0403d046000,0x01d0401d04072010720101d04072051174001d042772,0x01d0401d0406a0106a0101d0406a051174601d042772]⟩
def n124 : Entry := ⟨8, [304,320,357,407], 1406, [0x03d0c07a0d0440,0x0000,0x0750f07a0d2020,0x0000,0x06d0e07a0d2020,0x06d0e06d0e06d0e0750f112602470,0x0000,0x05d0c07a0d2020,0x0000,0x05d0c05d0c05d0c06d0e1126e2470,0x0000,0x03d0c07a0d2020,0x0000,0x03d0c03d0c03d0c06d0e1126f2470,0x0000,0x03d0c03d0c2020,0x07a0d07a0d2020,0x0000,0x07a0d06d0e6000,0x0000,0x0000,0x03d0c03d0c2020,0x07a0d07a0d2020,0x01a010750f6000,0x1177006d0106d0e06d014206,0x0320105d0c6000,0x0520103d0c6000,0x0150106d0106d0e06d0106d014207]⟩
def n125 : Entry := ⟨7, [304,320,357,407,932], 3438, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a011000,0x032011000,0x052011000,0x0000,0x0000]⟩
def n126 : Entry := ⟨9, [304,320,373], 894, [0x05d0403d0805d0405d0407a0503d088cc8,0x05d0403d0805d0403d088888,0x0750707507075070750707a0507507a8a8,0x05d0403d0805d0403d088888,0x06d0606d0606d0606d0607a0506d06a8a8,0x06d0606d0606d0606d0606d0606d0607507112f006d06acf8,0x05d0403d0805d0403d088888,0x05d0405d0405d0405d0407a0505d04a8a8,0x05d0405d0405d0405d048888,0x05d0405d0405d0405d0405d0405d0406d06112fe05d04acf8,0x03d0803d0803d0803d088888,0x03d080790807a0503d088888,0x03d080750707507075071162103d088cc8,0x03d0806d0606d0606d061165703d088cc8,0x03d0805d0405d0405d041163403d088cc8,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x075070750706d06075078888,0x06d0607a0506d06e000,0x05d0405d0405d0405d048888,0x06a0506a0503d0806a05117d003d08a8a8,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0507a050790807a0507a0507908a8a8,0x0750705a0107507e000,0x06d060520106d0606d0106d0606d0606d0606d01ca8e,0x05d040720105d04e000,0x052011186003d08118001174003d08a8a8,0x055030550106d0606d0106d0606d0606d0606d0106d01ca8f]⟩
def n127 : Entry := ⟨8, [304,320,373,390], 1662, [0x03d0807a0d0440,0x0000,0x0750f07a0d2020,0x0000,0x06d0e07a0d2020,0x06d0e06d0e06d0e0750f113202470,0x0000,0x05d0c07a0d2020,0x0000,0x05d0c05d0c05d0c06d0e1132e2470,0x0000,0x03d0807a0d2020,0x03d0803d0803d080750f113252470,0x0000,0x03d0803d0803d0805d0c113302470,0x03d0803d082020,0x07a0d07a0d2020,0x05a090750f6000,0x0000,0x0720905d0c6000,0x0000,0x03d0803d082020,0x07a0d07a0d2020,0x0000,0x03a0506d0e6000,0x0000,0x06a0503d086000,0x02d010550102d0102d0602d014207]⟩
def n128 : Entry := ⟨8, [304,320,373,406], 1918, [0x0000,0x0000,0x0000,0x0000,0x0000,0x113800010,0x0000,0x0000,0x0000,0x1138e0010,0x0000,0x0000,0x0000,0x116870010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0520106d0e1001,0x0000,0x0520103d081001,0x06d0e0001,0x0000,0x0000,0x01a011000,0x1183006d061001,0x032011000,0x0000,0x0150106d061001,0x0000]⟩
def n129 : Entry := ⟨7, [304,320,373,406,932], 2926, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x01a011000,0x032011000,0x0000,0x0000,0x0000]⟩
def n130 : Entry := ⟨8, [304,320,373,918], 1406, [0x03d0807a0d0440,0x0000,0x0750f07a0d2020,0x0000,0x06d0e07a0d2020,0x06d0e06d0e06d0e0750f113b02470,0x0000,0x05d0c07a0d2020,0x0000,0x05d0c05d0c05d0c06d0e113be2470,0x0000,0x0000,0x03d080750f2020,0x03d0803d080440,0x03d0805d0c2020,0x03d0803d082020,0x07a0d07a0d2020,0x0000,0x07a0d06d0e6000,0x0000,0x0000,0x03d0803d082020,0x07a0d07a0d2020,0x0750f03d082020,0x0520106d0106d0e06d014206,0x05d0c03d082020,0x0520103d080060,0x02d0102d010202]⟩
def n131 : Entry := ⟨10, [304,323], 503, [0x03d0406d0206d0206d0206d0206d0207a031009003d04acf8,0x0790407a0307a0307a0307a03079048cc8,0x06d0203d0406d0206d0207a0303d048cc8,0x06d0206d0206d0206d0206d0206d0207a031114006d02acf8,0x06d0206d0203d0406d0206d0203d04a8a8,0x06d0206d0206d0206d0207a0306d02a8a8,0x05d0407a0307a0307a03114a205d048cc8,0x05d0403d0405d0403d048888,0x05d040790407a0305d048888,0x05d0406d0206d0206d02118c005d048cc8,0x03d0407a0307a0307a03114a303d048cc8,0x03d0403d0403d0403d048888,0x03d040790407a0303d048888,0x03d0406d0206d0206d02118c103d048cc8,0x03d0405d0411b6003d048888,0x075010750107501e000,0x06d0206d0203d0406d0206d0203d04a8a8,0x07a0307a030790407a0307a0307904a8a8,0x06d020720106d0206d0106d0206d0206d0206d0106d01ca8f,0x072010720105d040720111cb005d04a8a8,0x072010720103d040720111cb103d04a8a8,0x07a030650107a0307a0106d0207a0307a0307a01ca8e,0x06d0203d0406d0203d048888,0x07a0307a030790407a0307a0307904a8a8,0x06d020750106d02e000,0x065010650105d040650111da005d04a8a8,0x065010650103d040650111da103d04a8a8,0x06d0206d0107a0307a0106d0206d0206d0106d0206d01ca8f]⟩
def n132 : Entry := ⟨9, [304,323,340], 999, [0x03d0805d0405d0405d0405d0405d0407a07100c003d08acf8,0x0790807a0707a0707a0707a07079088cc8,0x05d0403d0805d0405d0407a0703d088cc8,0x05d0405d0405d0405d0405d0405d0407a07114d205d04acf8,0x05d0405d0403d0805d0405d0403d08a8a8,0x05d0405d0405d0405d0407a0705d04a8a8,0x03d0807a0707a0707a07115c303d088cc8,0x03d0803d0803d0803d088888,0x03d080790807a0703d088888,0x03d0805d0405d0405d04118f003d088cc8,0x075050750507505e000,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0707a070790807a0707a0707908a8a8,0x05d0405d0405d0405d0405d040720505d04119b005d04acf8,0x072050720503d080720511a7003d08a8a8,0x07a070650107a0706d0207a0707a07c88c,0x05d0403d0805d0403d088888,0x07a0707a070790807a0707a0707908a8a8,0x05d040650105d0405d0405d0405d04c88c,0x065010650103d080650111ad003d08a8a8,0x06d0206d0107a0706d0206d0206d01c88c,0x07a0707a0707a0707a0707a0704d0207a07112f607a07acf8,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0707a070790807a0707a0707908a8a8,0x05d0406d0205d04e000,0x04d0204d0203d0804d0211b0003d08a8a8,0x04d0204d0104d020720104d0204d0204d0104d0204d01ca8f,0x05d04075050750105d0405d0405d048a8a]⟩
def n133 : Entry := ⟨8, [304,323,340,357], 1991, [0x03d0803d0803d0807a0f100f02470,0x07a0f07a0f0440,0x03d0807a0f0440,0x03d0803d0803d0807a0f115932470,0x03d0803d082020,0x03d0807a0f2020,0x0750d0750d6000,0x03d0803d082020,0x07a0f07a0f2020,0x03d0803d080720d03d08119202470,0x0650907a0f4004,0x0000,0x07a0f07a0f2020,0x03d0803d080650903d08119502470,0x06d0906d094004,0x07a0f07a0f04d0207a0f111a62470,0x03d0803d082020,0x07a0f07a0f2020,0x04d0203d084004,0x04d0104d014004,0x0000,0x07a0f07a0f01d0407a0f115082470,0x03d0803d082020,0x07a0f07a0f2020,0x05d0403d086000,0x01d0401d0401d040720d119802470,0x0650101d040202,0x06d0203d080202]⟩
def n134 : Entry := ⟨7, [304,323,340,357,374], 3847, [0x03d0803d0803d0807a1f101202470,0x07a1f07a1f0440,0x03d0807a1f0440,0x0000,0x0000,0x07a1f07a1f2020,0x07a1f07a1f04d1207a1f111d12470,0x03d0803d082020,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0000,0x0350507a1f6000,0x03d0803d082020,0x07a1f07a1f2020,0x0000,0x0320104d0104d1204d0104d014207,0x0000]⟩
def n135 : Entry := ⟨7, [304,323,340,357,390], 3719, [0x03d0803d0803d0807a1f101502470,0x07a1f07a1f0440,0x03d0807a1f0440,0x0751d0751d6000,0x03d0803d082020,0x07a1f07a1f2020,0x07a1f07a1f04d1207a1f112062470,0x03d0803d082020,0x07a1f07a1f2020,0x0000,0x07a1f07a1f01d0407a1f1120b2470,0x03d0803d082020,0x07a1f07a1f2020,0x0000,0x0000,0x0250107a1f4004,0x0000,0x07a1f07a1f2020,0x02d0107a1f4004,0x0350105d144004,0x0650105d144004]⟩
def n136 : Entry := ⟨7, [304,323,340,357,423], 2887, [0x03d1803d1803d1807a1f101802470,0x07a1f07a1f0440,0x03d1807a1f0440,0x0000,0x0000,0x03d1807a1f2020,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0000,0x0150107a1f6000,0x03d1803d182020,0x07a1f07a1f2020,0x0520103d186000,0x01a0106d0106d1a06d0106d014207,0x0320106d0106d1a06d0106d014207]⟩
def n137 : Entry := ⟨8, [304,323,340,373], 1863, [0x03d1005d0405d0405d0405d0405d0407a0f101b003d10acf8,0x0791007a0f07a0f07a0f07a0f079108cc8,0x05d0403d1005d0405d0407a0f03d108cc8,0x03d1007a0f07a0f07a0f115f303d108cc8,0x03d1003d1003d1003d108888,0x03d100791007a0f03d108888,0x07a0f07a0f06d0a07a0f8888,0x05d0403d1005d0403d108888,0x07a0f07a0f0791007a0f07a0f07910a8a8,0x065090650903d1006509119e003d10a8a8,0x07a0f07a0f07a0f07a0f8888,0x05d0403d1005d0403d108888,0x07a0f07a0f0791007a0f07a0f07910a8a8,0x04d0204d0203d1004d02119ee03d10a8a8,0x05d040750d05d0405d048888,0x07a0f0550107a0fe000,0x05d0405d0403d1005d0405d0403d10a8a8,0x07a0f07a0f0791007a0f07a0f07910a8a8,0x0520111a4003d1011a101198003d10a8a8,0x05a0305a0106d0a06d0106d0a06d0a06d0a06d0106d01ca8f,0x04d020720106d0a06d0106d0a06d0a06d0a06d0106d01ca8f]⟩
def n138 : Entry := ⟨7, [304,323,340,373,390], 3655, [0x03d1003d1003d1007a1f101e02470,0x07a1f07a1f0440,0x03d1007a1f0440,0x03d1003d1003d1007a1f112052470,0x03d1003d102020,0x03d1007a1f2020,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0551107a1f6000,0x03d1003d102020,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x0000,0x07a1f07a1f2020,0x0650903d106000,0x0000,0x02d0105a0102d0102d0a02d014207]⟩
def n139 : Entry := ⟨7, [304,323,340,373,422], 3911, [0x102100010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0520103d101001,0x06d1a0001,0x06d1a0001,0x015011000,0x0000,0x0000,0x0000,0x01a0106d0a1001,0x0320106d0a1001,0x0000]⟩
def n140 : Entry := ⟨7, [304,323,340,373,934], 2887, [0x03d1003d1003d1007a1f102402470,0x07a1f07a1f0440,0x03d1007a1f0440,0x03d1007a1f2020,0x0000,0x0000,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x07a1f07a1f2020,0x0000,0x0000,0x07a1f03d102020,0x03d1003d102020,0x07a1f07a1f2020,0x0520103d100060,0x02d0102d010202,0x02d0102d010202]⟩
def n141 : Entry := ⟨8, [304,323,340,374], 1895, [0x03d0803d0803d0807a0f102702470,0x07a0f07a0f0440,0x03d0807a0f0440,0x05d0c05d0c05d0c07a0f115022470,0x03d0803d082020,0x05d0c07a0f2020,0x0000,0x0000,0x03d0807a0f2020,0x03d0803d0803d0805d0c119202470,0x0000,0x0000,0x07a0f07a0f2020,0x0650905d0c4004,0x0000,0x07a0f07a0f04d0a07a0f113212470,0x03d0803d082020,0x07a0f07a0f2020,0x06d0a05d0c6000,0x03d0803d0804d0a03d08119ef2470,0x0750905d0c0202,0x0350507a0f6000,0x03d0803d082020,0x07a0f07a0f2020,0x05d0c05d0c11aa005d0c119802470,0x0720503d086000,0x06d0106d010202,0x0320104d0104d0a04d0104d014207]⟩
def n142 : Entry := ⟨7, [304,323,340,374,421], 3911, [0x102a00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x015011000,0x0000,0x0000,0x052011000,0x06d0a0001,0x06d0a0001,0x0000]⟩
def n143 : Entry := ⟨8, [304,323,340,390], 1767, [0x03d0803d0803d0807a0f102d02470,0x07a0f07a0f0440,0x03d0807a0f0440,0x05d0c05d0c05d0c07a0f115322470,0x03d0803d082020,0x05d0c07a0f2020,0x03d0803d0803d0807a0f112332470,0x03d0803d082020,0x03d0807a0f2020,0x03d0803d0803d0805d0c119502470,0x0750d0750d6000,0x03d0803d082020,0x07a0f07a0f2020,0x05d0c05d0c0720d05d0c119e02470,0x0000,0x07a0f07a0f04d0a07a0f113562470,0x03d0803d082020,0x07a0f07a0f2020,0x06d0a05d0c6000,0x0000,0x0000,0x0250107a0f4004,0x0000,0x07a0f07a0f2020,0x0250105d0c4004,0x0650103d086000,0x02d0107a0f4004,0x0350105d0c4004]⟩
def n144 : Entry := ⟨8, [304,323,340,406], 1511, [0x03d0803d0803d0807a0f103002470,0x07a0f07a0f0440,0x03d0807a0f0440,0x05d0c05d0c05d0c07a0f115382470,0x03d0803d082020,0x05d0c07a0f2020,0x03d0803d0803d0807a0f115392470,0x03d0803d082020,0x03d0807a0f2020,0x0000,0x0750d0750d6000,0x03d0803d082020,0x07a0f07a0f2020,0x05d0c05d0c0720d05d0c119ee2470,0x03d0803d080720d03d08119ef2470,0x0650907a0f4004,0x0000,0x07a0f07a0f2020,0x0000,0x0000,0x06d0906d094004,0x07a0f07a0f11b3007a0f112662470,0x03d0803d082020,0x07a0f07a0f2020,0x02d0205d0c6000,0x04d0203d086000,0x00d01072010720d07201072014207,0x07501075010202]⟩
def n145 : Entry := ⟨7, [304,323,340,406,416], 3558, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x00d011000,0x0000,0x0000,0x0000,0x02a011000,0x04a011000,0x0750d0001,0x0000,0x0000]⟩
def n146 : Entry := ⟨9, [304,323,357], 1015, [0x03d0403d0403d0407a07103302470,0x07a0707a070440,0x03d0407a070440,0x06d0606d0606d0607a07111702470,0x03d0403d042020,0x06d0607a072020,0x05d0405d0405d0407a07115622470,0x03d0403d042020,0x05d0407a072020,0x05d0405d0405d0406d06118f02470,0x03d0403d0403d0407a07115632470,0x03d0403d042020,0x03d0407a072020,0x03d0403d0403d0406d06118f12470,0x03d0405d0403d0403d0403d044207,0x07505075056000,0x03d0403d042020,0x07a0707a072020,0x0720506d0506d0606d0506d054207,0x05d0405d040720505d0411b902470,0x03d0403d040720503d0411b912470,0x0650507a0507a0707a054206,0x0000,0x07a0707a072020,0x0750506d066000,0x05d0405d040650505d0411ad42470,0x03d0403d040650503d0411ad52470,0x06d0507a0506d0506d0606d054207,0x07a0707a0707a0307a0301d0407a071165207a032772,0x03d0403d0403d0403d042222,0x07a070790407a07079042222,0x06d0606d0606d0206d0201d0406d0611b0006d022772,0x03d0403d046000,0x05d0403d046000,0x01d0401d04072010720101d040720511bc001d042772,0x01d0401d04065010650101d040650511c2001d042772]⟩
def n147 : Entry := ⟨8, [304,323,357,373], 1879, [0x03d0c03d0c03d0c07a0f103602470,0x07a0f07a0f0440,0x03d0c07a0f0440,0x06d0e06d0e06d0e07a0f111a02470,0x03d0c03d0c2020,0x06d0e07a0f2020,0x03d0c03d0c03d0c07a0f111b02470,0x03d0c03d0c2020,0x03d0c07a0f2020,0x03d0c03d0c03d0c06d0e119212470,0x0000,0x0000,0x07a0f07a0f2020,0x0750d06d0e6000,0x03d0c03d0c0650d03d0c119e52470,0x0000,0x0000,0x07a0f07a0f2020,0x06d0e06d0e01d0406d0e119ee2470,0x05d0403d0c6000,0x0000,0x0550107a0f6000,0x03d0c03d0c2020,0x07a0f07a0f2020,0x0520106d0e4004,0x0520103d0c4004,0x05a0106d0e4004,0x0720103d0c4004]⟩
def n148 : Entry := ⟨8, [304,323,357,407], 1399, [0x03d0c03d0c03d0c07a0f103902470,0x07a0f07a0f0440,0x03d0c07a0f0440,0x06d0e06d0e06d0e07a0f112602470,0x03d0c03d0c2020,0x06d0e07a0f2020,0x0000,0x0000,0x05d0c07a0f2020,0x05d0c05d0c05d0c06d0e119802470,0x0000,0x0000,0x03d0c07a0f2020,0x03d0c03d0c03d0c06d0e119812470,0x0000,0x0000,0x0000,0x07a0f07a0f2020,0x0750d06d0e6000,0x0000,0x0000,0x0150107a0f6000,0x03d0c03d0c2020,0x07a0f07a0f2020,0x11bf006d0106d0e06d0106d014207,0x0320105d0c6000,0x0520103d0c6000,0x01a0106d0106d0e06d0106d014207]⟩
def n149 : Entry := ⟨7, [304,323,357,407,932], 3431, [0x103c00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x015011000,0x0000,0x0000,0x032011000,0x052011000,0x0000,0x06d010100]⟩
def n150 : Entry := ⟨8, [304,323,357,408], 1271, [0x03d0c03d0c03d0c07a0f103f02470,0x07a0f07a0f0440,0x03d0c07a0f0440,0x06d0e06d0e06d0e07a0f112902470,0x03d0c03d0c2020,0x06d0e07a0f2020,0x05d0c05d0c05d0c07a0f112922470,0x03d0c03d0c2020,0x05d0c07a0f2020,0x0000,0x03d0c03d0c03d0c07a0f112932470,0x03d0c03d0c2020,0x03d0c07a0f2020,0x0000,0x0000,0x0750d0750d6000,0x03d0c03d0c2020,0x07a0f07a0f2020,0x0000,0x0000,0x0000,0x11c5007a0107a0f07a014206,0x11c8003d0c4004,0x07a0f07a0f2020,0x0150106d0e6000,0x0250105d0c6000,0x0450103d0c6000,0x00d0107a0107a0f07a0107a014207]⟩
def n151 : Entry := ⟨7, [304,323,357,408,928], 3318, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x104201000,0x0000,0x015011000,0x025011000,0x045011000,0x0000,0x0000]⟩
def n152 : Entry := ⟨7, [304,323,357,408,929], 3317, [0x0000,0x112c00010,0x0000,0x112c20010,0x0000,0x0000,0x112c30010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1f0001,0x104201000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n153 : Entry := ⟨9, [304,323,373], 887, [0x03d0805d0405d0405d0405d0405d0407a071045003d08acf8,0x0790807a0707a0707a0707a07079088cc8,0x05d0403d0805d0405d0407a0703d088cc8,0x06d0606d0606d0606d0606d0606d0607a07112f006d06acf8,0x05d0405d0403d0805d0405d0403d08a8a8,0x06d0606d0606d0606d0607a0706d06a8a8,0x05d0405d0405d0405d048888,0x05d0403d0805d0403d088888,0x05d0405d0405d0405d0407a0705d04a8a8,0x05d0405d0405d0405d0405d0405d0406d06119b005d04acf8,0x03d0807a0707a0707a071162303d088cc8,0x03d0803d0803d0803d088888,0x03d080790807a0703d088888,0x03d0806d0606d0606d0611a7103d088cc8,0x03d0805d0405d0405d0411b9003d088cc8,0x07a0707a0706d0607a078888,0x05d0403d0805d0403d088888,0x07a0707a070790807a0707a0707908a8a8,0x06d060750506d06e000,0x05d0405d0405d0405d048888,0x065050650503d080650511ce003d08a8a8,0x07a070550107a07e000,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0707a070790807a0707a0707908a8a8,0x06d060520106d0606d0106d0606d0606d0606d0106d01ca8f,0x05d040720105d04e000,0x0520111d7003d0811d1011bc003d08a8a8,0x05a0305a0106d0606d0106d0606d0606d0606d0106d01ca8f]⟩
def n154 : Entry := ⟨8, [304,323,373,390], 1655, [0x03d0803d0803d0807a0f104802470,0x07a0f07a0f0440,0x03d0807a0f0440,0x06d0e06d0e06d0e07a0f113502470,0x03d0803d082020,0x06d0e07a0f2020,0x0000,0x0000,0x05d0c07a0f2020,0x05d0c05d0c05d0c06d0e119e02470,0x03d0803d0803d0807a0f113552470,0x03d0803d082020,0x03d0807a0f2020,0x0000,0x03d0803d0803d0805d0c119e52470,0x0550907a0f6000,0x03d0803d082020,0x07a0f07a0f2020,0x0000,0x0720905d0c6000,0x0000,0x0000,0x0000,0x07a0f07a0f2020,0x0350506d0e6000,0x0000,0x0650503d086000,0x02d0105a0102d0102d0602d014207]⟩
def n155 : Entry := ⟨8, [304,323,373,406], 1911, [0x104b00010,0x0000,0x0000,0x113800010,0x0000,0x0000,0x0000,0x0000,0x0000,0x11a100010,0x0000,0x0000,0x0000,0x11aa10010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0520106d0e1001,0x0000,0x0520103d081001,0x06d0e0001,0x015011000,0x0000,0x0000,0x11d4006d061001,0x032011000,0x0000,0x01a0106d061001,0x0000]⟩
def n156 : Entry := ⟨7, [304,323,373,406,932], 2919, [0x104e00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x015011000,0x0000,0x0000,0x032011000,0x0000,0x0000,0x06d010100]⟩
def n157 : Entry := ⟨8, [304,323,373,918], 1399, [0x03d0803d0803d0807a0f105102470,0x07a0f07a0f0440,0x03d0807a0f0440,0x06d0e06d0e06d0e07a0f113b02470,0x03d0803d082020,0x06d0e07a0f2020,0x0000,0x0000,0x05d0c07a0f2020,0x05d0c05d0c05d0c06d0e11a402470,0x03d0807a0f2020,0x0000,0x0000,0x03d0803d080440,0x03d0805d0c2020,0x0000,0x0000,0x07a0f07a0f2020,0x0750d06d0e6000,0x0000,0x0000,0x07a0f03d082020,0x03d0803d082020,0x07a0f07a0f2020,0x0520106d0106d0e06d0106d014207,0x05d0c03d082020,0x0520103d080060,0x02d0102d010202]⟩
def n158 : Entry := ⟨9, [304,323,389], 759, [0x03d0805d0405d0405d0405d0405d0407a071054003d08acf8,0x0790807a0707a0707a0707a07079088cc8,0x05d0403d0805d0405d0407a0703d088cc8,0x06d0606d0606d0606d0606d0606d0607a07113e006d06acf8,0x05d0405d0403d0805d0405d0403d08a8a8,0x06d0606d0606d0606d0607a0706d06a8a8,0x05d0405d0405d0405d0405d0405d0407a07113e205d04acf8,0x05d0405d0403d0805d0405d0403d08a8a8,0x05d0405d0405d0405d0407a0705d04a8a8,0x05d0405d0405d0405d048888,0x03d0807a0707a0707a07116b303d088cc8,0x03d0803d0803d0803d088888,0x03d080790807a0703d088888,0x03d0806d0606d0606d0611ad103d088cc8,0x03d0805d0405d0405d0411ad403d088cc8,0x075050750507505e000,0x05d0405d0403d0805d0405d0403d08a8a8,0x07a0707a070790807a0707a0707908a8a8,0x06d0606d0606d0606d068888,0x05d0405d0405d0405d048888,0x072050720503d080720511ce103d08a8a8,0x07a070450107a0707a0107a0707a0707a0707a01ca8e,0x05d0403d0805d0403d088888,0x07a0707a070790807a0707a0707908a8a8,0x06d060550106d06e000,0x05d040650105d04e000,0x0450111e6003d0811dd011c2003d08a8a8,0x04d0204d0107a0707a0107a0707a0707a0707a0107a01ca8f]⟩
def n159 : Entry := ⟨8, [304,323,389,406], 1783, [0x105700010,0x0000,0x0000,0x114100010,0x0000,0x0000,0x114120010,0x0000,0x0000,0x0000,0x116e30010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0450107a0f1001,0x0000,0x0000,0x0000,0x0000,0x0450103d081001,0x07a0f0001,0x11e0007a071001,0x11e3003d081001,0x0000,0x015011000,0x025011000,0x0000,0x00d0107a071001,0x0000]⟩
def n160 : Entry := ⟨7, [304,323,389,406,928], 2806, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x105a01000,0x0000,0x015011000,0x025011000,0x0000,0x0000,0x0000]⟩
def n161 : Entry := ⟨7, [304,323,389,406,929], 2805, [0x0000,0x114400010,0x0000,0x114420010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1f0001,0x105a01000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n162 : Entry := ⟨8, [304,323,389,918], 1271, [0x03d0803d0803d0807a0f105d02470,0x07a0f07a0f0440,0x03d0807a0f0440,0x06d0e06d0e06d0e07a0f114702470,0x03d0803d082020,0x06d0e07a0f2020,0x05d0c05d0c05d0c07a0f114722470,0x03d0803d082020,0x05d0c07a0f2020,0x0000,0x03d0803d080440,0x0000,0x0000,0x03d0806d0e2020,0x03d0805d0c2020,0x0750d0750d6000,0x03d0803d082020,0x07a0f07a0f2020,0x0000,0x0000,0x0000,0x0450107a0107a0f07a014206,0x0000,0x07a0f07a0f2020,0x06d0e03d082020,0x05d0c03d082020,0x0450103d080060,0x03a0103a010202]⟩
def n163 : Entry := ⟨10, [304,340], 511, [0x03d0405d0205d0205d0205d0205d0207a031060003d04acf8,0x0790407a0307a0307a0307a03079048cc8,0x05d0203d0405d0205d0207a0303d048cc8,0x07503075030750307a03075030750307503ca0e,0x05d0203d0405d0203d048888,0x0750307503075030750307a0307503a8a8,0x06d0206d0206d0206d0206d0206d0207a03114a606d02acf8,0x05d0205d0203d0405d0205d0203d04a8a8,0x06d0206d0206d0206d0207a0306d02a8a8,0x06d0206d0206d0206d0206d0206d0207503118c006d02acf8,0x05d0205d0205d0205d0205d0205d0207a03114a805d02acf8,0x05d0205d0203d0405d0205d0203d04a8a8,0x05d0205d0205d0205d0207a0305d02a8a8,0x05d0205d0205d0205d0205d0205d0207503118c205d02acf8,0x05d0205d0205d0206d0205d0205d0205d0205d02ca0f,0x03d0407a0307a0307a031171303d048cc8,0x03d0403d0403d0403d048888,0x03d040790407a0303d048888,0x03d0407503075030750311b6303d048cc8,0x03d0406d0206d0206d0211ec003d048cc8,0x03d0405d0205d0205d0211ec203d048cc8,0x075030750307503e000,0x05d0205d0203d0403d0305d0205d0203d0403d03aaaa,0x07a0307a03079040790307a0307a030790407903aaaa,0x0750307a0307503e000,0x06d0206d0206d0206d0206d0106d0106d020720306d0211cbc06d0206d01affa,0x05d0205d0205d0205d0205d0105d0105d020720305d0211cbe05d0205d01affa,0x072030720303d0403d030720311f2003d0403d03aaaa,0x07a0307a0307a0307a0307a0107a0107a0304d0207a03117a607a0307a01affa,0x05d0205d0203d0403d0205d0205d0203d0403d02aaaa,0x07a0307a03079040790207a0307a030790407902aaaa,0x0750307503075030750307501075010750304d020750311da00750307501affa,0x05d0205d0205d02e000,0x05d0206d0205d02e000,0x04d0204d0203d0403d0204d021225003d0403d02aaaa,0x04d0204d0104d0204d0104d0204d02072010720104d0204d0207203123d004d0204d0104d0204d01ffff]⟩
def n164 : Entry := ⟨9, [304,340,356], 1007, [0x03d0403d0403d0407a07106302470,0x07a0707a070440,0x03d0407a070440,0x0750707a0707507075074206,0x0000,0x0750707a072020,0x05d0605d0605d0607a07115c82470,0x03d0403d042020,0x05d0607a072020,0x05d0605d0605d0607507118f22470,0x03d0403d0403d0407a07115c92470,0x03d0403d042020,0x03d0407a072020,0x03d0403d0403d0407507118f32470,0x03d0403d0403d0405d0611ef02470,0x07507075076000,0x03d0403d0303d0403d032222,0x07a070790707a07079072222,0x07a07075076000,0x05d0605d0605d0505d050720705d0611a8405d052772,0x03d0403d0403d0303d030720703d0411a8503d032772,0x07a0707a0704d0207a07116272470,0x03d0403d042020,0x07a0707a072020,0x075070750704d020750711ad12470,0x06d0205d066000,0x04d0203d0203d0403d0203d024207,0x04d0104d0204d0104d0204d020720711bcd04d017474,0x07a0707a0702d0207a07116262470,0x03d0403d042020,0x07a0707a072020,0x075070750702d020750711ad02470,0x02d0205d0205d0605d0205d024207,0x06d0203d046000,0x02d0102d0202d0102d0202d020720711bcc02d017474,0x03d0205d0203d0203d0403d024207]⟩
def n165 : Entry := ⟨8, [304,340,356,357], 1935, [0x03d0403d0403d0407a0f106602470,0x07a0f07a0f0440,0x03d0407a0f0440,0x0750f07a0f0750f0750f4206,0x0000,0x0750f07a0f2020,0x0750f0750f6000,0x03d0403d0303d0403d032222,0x07a0f0790f07a0f0790f2222,0x07a0f0750f6000,0x07a0f07a0f04d0207a0f115f72470,0x03d0403d042020,0x07a0f07a0f2020,0x0750f0750f04d020750f119512470,0x04d0104d0204d0104d0204d020720f1199304d017474,0x07a0f07a0f02d0207a0f115f62470,0x03d0403d042020,0x07a0f07a0f2020,0x0750f0750f02d020750f119502470,0x02d0102d0202d0102d0202d020720f1199202d017474,0x03d0205d0203d0203d0403d024207,0x07a0f07a0f01d0207a0f115f82470,0x03d0403d042020,0x07a0f07a0f2020,0x0750f0750f01d020750f119522470,0x01d0101d0201d0101d0201d020720f1199401d017474,0x03d0206d0203d0203d0403d024207,0x05d0206d0205d0205d0605d024207]⟩
def n166 : Entry := ⟨9, [304,340,374], 895, [0x03d0403d0403d0407a07106902470,0x07a0707a070440,0x03d0407a070440,0x0000,0x0000,0x0750707a072020,0x06d0606d0606d0607a07116562470,0x03d0403d042020,0x06d0607a072020,0x06d0606d0606d060750711a702470,0x05d0605d0605d0607a07116582470,0x03d0403d042020,0x05d0607a072020,0x05d0605d0605d060750711a722470,0x05d0606d0605d0605d0605d064207,0x0000,0x0000,0x03d0407a072020,0x0000,0x03d0403d0403d0406d0611a852470,0x03d0403d0403d0405d0611a872470,0x07a0707a0707a0507a0504d0607a07117d107a052772,0x03d0403d0203d0403d022222,0x07a070790607a07079062222,0x0750707507075050750504d060750711ce1075052772,0x05d0605d066000,0x06d0605d066000,0x03d0403d0403d0203d0204d0603d0411cef03d022772,0x0350307a076000,0x03d0403d0303d0403d032222,0x07a070790307a07079032222,0x03a03075076000,0x06d0606d0606d0106d0111f5006d0611bcc06d012772,0x05d0605d0605d0105d0111f5205d0611bce05d012772,0x0720303d046000,0x0320104d060320104d0604d0104d011216004d0611fb004d0604d0104d017777]⟩
def n167 : Entry := ⟨8, [304,340,374,404], 1903, [0x106c00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x116880010,0x0000,0x0000,0x11aa20010,0x0000,0x0000,0x0000,0x0000,0x11ab70010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x05d0e11f800110,0x0000,0x0320104d061001,0x025011000,0x0000,0x0000,0x02a011000,0x05d060001,0x062011000,0x05d060001,0x06d011000]⟩
def n168 : Entry := ⟨7, [304,340,374,404,405], 3407, [0x106f00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x05d060001,0x0000,0x0000,0x0000,0x0000,0x0000,0x06d060001,0x05d060001]⟩
def n169 : Entry := ⟨8, [304,340,374,408], 1151, [0x03d0c03d0c03d0c07a0f107202470,0x07a0f07a0f0440,0x03d0c07a0f0440,0x0000,0x0000,0x0750f07a0f2020,0x0000,0x0000,0x06d0e07a0f2020,0x0000,0x0000,0x0000,0x05d0e07a0f2020,0x0000,0x0000,0x0000,0x0000,0x03d0c07a0f2020,0x0000,0x0000,0x0000,0x11fe007a0f6000,0x1204003d0c1201003d0103d0c03d0c03d0103d017227,0x1210007a0f120a00790107a0f07a0f07901079017227,0x121300750f6000,0x1213606d0e6000,0x1213805d0e6000,0x1213903d0c6000]⟩
def n170 : Entry := ⟨7, [304,340,374,408,928], 3198, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a0f0001,0x0000,0x0000,0x0000,0x0000,0x107b01000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n171 : Entry := ⟨7, [304,340,374,408,929], 2173, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1f03d0c2020,0x07a1f07a1f2020,0x0000,0x0000,0x0000,0x0000]⟩
def n172 : Entry := ⟨7, [304,340,374,408,929], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1207007a1f1001,0x0000,0x0000,0x0000,0x0000,0x107b01000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n173 : Entry := ⟨6, [304,340,374,408,929,930], 6265, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n174 : Entry := ⟨7, [304,340,374,408,930], 2171, [0x03d1c07a0f2020,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x120d003d1c4004,0x0000,0x0000,0x0000,0x0000]⟩
def n175 : Entry := ⟨6, [304,340,374,408,930,945], 6265, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n176 : Entry := ⟨7, [304,340,374,408,930], 3195, [0x107500010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1207003d1c1001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x079010100]⟩
def n177 : Entry := ⟨7, [304,340,374,408,931], 3191, [0x107800010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n178 : Entry := ⟨8, [304,340,374,408], 1663, [0x107e00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x121901000,0x121c003d021001,0x121f0079061001,0x122201000,0x0000,0x0000,0x122351000,0x04d011000]⟩
def n179 : Entry := ⟨7, [304,340,374,408,928], 2686, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x108701000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n180 : Entry := ⟨7, [304,340,374,408,929], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x108701000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n181 : Entry := ⟨7, [304,340,374,408,930], 2683, [0x108100010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n182 : Entry := ⟨7, [304,340,374,408,931], 2679, [0x108400010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n183 : Entry := ⟨9, [304,340,390], 767, [0x03d0403d0403d0407a07108a02470,0x07a0707a070440,0x03d0407a070440,0x0750707a0707507075074206,0x0000,0x0750707a072020,0x06d0606d0606d0607a07116b62470,0x03d0403d042020,0x06d0607a072020,0x06d0606d0606d060750711b002470,0x05d0605d0605d0607a07116b82470,0x03d0403d042020,0x05d0607a072020,0x05d0605d0605d060750711b022470,0x0000,0x03d0403d0403d0407a07116b92470,0x03d0403d042020,0x03d0407a072020,0x03d0403d0403d040750711b032470,0x0000,0x0000,0x07507075076000,0x03d0403d0303d0403d032222,0x07a070790707a07079072222,0x07a07075076000,0x06d0606d0606d0506d050720706d0611cec06d052772,0x05d0605d0605d0505d050720705d0611cee05d052772,0x03d0403d0403d0303d030720703d0411cef03d032772,0x07a0707a0707a0107a011228007a071174607a012772,0x03d0403d0203d0403d022222,0x07a070790207a07079022222,0x07507075070750107501122e00750711c20075012772,0x01d0206d066000,0x02d0205d066000,0x04d0203d046000,0x00d010720700d01072070720107201123100720711fb00720707201072017777]⟩
def n184 : Entry := ⟨8, [304,340,390,400], 1790, [0x0000,0x0000,0x0000,0x0000,0x0000,0x11b300010,0x0000,0x0000,0x11b320010,0x0000,0x0000,0x0000,0x11b330010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0750f122b00110,0x0000,0x0000,0x0000,0x00d01072071001,0x0000,0x0000,0x0000,0x01a011000,0x02a011000,0x04a011000,0x075070001,0x07a011000]⟩
def n185 : Entry := ⟨7, [304,340,390,400,403], 3318, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x075070001,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a070001,0x0000]⟩
def n186 : Entry := ⟨8, [304,340,390,403], 1783, [0x108d00010,0x0000,0x0000,0x116e60010,0x0000,0x0000,0x116e80010,0x0000,0x0000,0x0000,0x116e90010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a0f122b00110,0x0000,0x0000,0x0000,0x0000,0x0000,0x00d01072071001,0x0000,0x0000,0x0000,0x015011000,0x025011000,0x045011000,0x07a070001,0x075011000]⟩
def n187 : Entry := ⟨8, [304,340,390,407], 1663, [0x109000010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1234003d031001,0x12370079071001,0x0000,0x123a01000,0x123a21000,0x123a31000,0x072011000]⟩
def n188 : Entry := ⟨7, [304,340,390,407,929], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n189 : Entry := ⟨7, [304,340,390,407,930], 2683, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n190 : Entry := ⟨7, [304,340,390,407,932], 2671, [0x109300010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n191 : Entry := ⟨9, [304,340,391], 639, [0x03d0805d0605d0605d0605d0605d0607a071096003d08acf8,0x0790807a0707a0707a0707a07079088cc8,0x05d0603d0805d0605d0607a0703d088cc8,0x075070750705d06075078888,0x05d0603d0805d0603d088888,0x0750707507075070750707a0707507a8a8,0x06d0606d0606d0606d068888,0x05d0603d0805d0603d088888,0x06d0606d0606d0606d0607a0706d06a8a8,0x06d0606d0606d0606d068888,0x05d0605d0605d0605d068888,0x05d0603d0805d0603d088888,0x05d0605d0605d0605d0607a0705d06a8a8,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x03d0807a0707a0707a071174303d088cc8,0x03d0803d0803d0803d088888,0x03d080790807a0703d088888,0x03d0807507075070750711bc303d088cc8,0x03d0806d0606d0606d0611bcd03d088cc8,0x03d0805d0605d0605d0611bd003d088cc8,0x07a070450107a07e000,0x05d0605d0603d0803d0105d0605d0603d0803d01aaaa,0x07a0707a07079080790107a0707a070790807901aaaa,0x0750704a0107507e000,0x06d060520106d06e000,0x05d060620105d06e000,0x12520124f003d0803d011240011fb003d0803d01aaaa]⟩
def n192 : Entry := ⟨8, [304,340,391,406], 1663, [0x109900010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1213903d081001,0x124301000,0x1246003d081001,0x12490079081001,0x124c01000,0x124c61000,0x124c81000,0x0000,0x03d011000]⟩
def n193 : Entry := ⟨7, [304,340,391,406,928], 2686, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10a201000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n194 : Entry := ⟨7, [304,340,391,406,929], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10a201000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n195 : Entry := ⟨7, [304,340,391,406,930], 2683, [0x109c00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n196 : Entry := ⟨7, [304,340,391,406,931], 2679, [0x109f00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n197 : Entry := ⟨8, [304,340,391,918], 1151, [0x03d0803d0803d0807a0f10a502470,0x07a0f07a0f0440,0x03d0807a0f0440,0x0000,0x0000,0x0750f07a0f2020,0x0000,0x0000,0x06d0e07a0f2020,0x0000,0x0000,0x0000,0x05d0e07a0f2020,0x0000,0x0000,0x03d0807a0f2020,0x0000,0x0000,0x03d080750f2020,0x03d0806d0e2020,0x03d0805d0e2020,0x07a0f03d0103d0803d012222,0x03d0803d0103d0803d012222,0x07a0f0790107a0f079012222,0x0750f03d0103d0803d012222,0x06d0e03d0103d0803d012222,0x05d0e03d0103d0803d012222,0x1213903d080060]⟩
def n198 : Entry := ⟨8, [304,340,391,918], 1663, [0x10a800010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x117730010,0x0000,0x0000,0x11bf30010,0x11bfd0010,0x11c000010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d08121390110,0x0450103d081001,0x0000,0x0000,0x04a0103d081001,0x0520103d081001,0x0620103d081001,0x0000,0x03d010100]⟩
def n199 : Entry := ⟨10, [304,372], 383, [0x03d0406d0206d0206d0206d0206d0207a0310ab003d04acf8,0x0790407a0307a0307a0307a03079048cc8,0x06d0203d0406d0206d0207a0303d048cc8,0x075030750306d02075038888,0x06d0203d0406d0203d048888,0x0750307503075030750307a0307503a8a8,0x06d0206d0206d0206d028888,0x06d0203d0406d0203d048888,0x06d0206d0206d0206d0207a0306d02a8a8,0x06d0206d0206d0206d028888,0x05d0407a0307a0307a03117a205d048cc8,0x05d0403d0405d0403d048888,0x05d040790407a0305d048888,0x05d0407503075030750311cb205d048cc8,0x05d0406d0206d0206d0211cbc05d048cc8,0x03d0407a0307a0307a03117a303d048cc8,0x03d0403d0403d0403d048888,0x03d040790407a0303d048888,0x03d0407503075030750311cb303d048cc8,0x03d0406d0206d0206d0211cbd03d048cc8,0x03d0405d0411f2403d048888,0x07a030650107a03e000,0x06d0206d0203d0403d0106d0206d0203d0403d01aaaa,0x07a0307a03079040790107a0307a030790407901aaaa,0x0750306a0107503e000,0x06d020720106d02e000,0x062011261005d0405d0112580123d005d0405d01aaaa,0x062011261103d0403d0112581123d103d0403d01aaaa]⟩
def n200 : Entry := ⟨9, [304,372,389], 895, [0x05d0405d0405d0407a0710ae02470,0x07a0707a070440,0x05d0407a070440,0x0000,0x0000,0x0750707a072020,0x0000,0x0000,0x06d0607a072020,0x0000,0x05d0405d040440,0x0000,0x05d0407a072020,0x05d0405d040440,0x05d0405d040440,0x07a07118030440,0x0000,0x0000,0x0750711d130440,0x06d0611d1d0440,0x05d0411f540440,0x0650507a076000,0x05d0403d0805d0403d082222,0x07a070790807a07079082222,0x06a05075076000,0x0720506d066000,0x0620105d040620105d0405d0405d0405d047207,0x0620103d08125b003d082222,0x0450107a07045017000,0x05d0403d0405d0403d042222,0x07a070790407a07079042222,0x04a010750704a017000,0x0520106d06052017000,0x0620105d046000,0x125e003d041216403d042222,0x05d0405d0405d017000]⟩
def n201 : Entry := ⟨8, [304,372,389,390], 1663, [0x10b100010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x11f840010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x124c903d041001,0x0000,0x0000,0x0000,0x0000,0x0000,0x124c805d041001,0x0000,0x03d0105d0103d0803d041111]⟩
def n202 : Entry := ⟨8, [304,372,389,918], 1407, [0x10b400010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x118330010,0x0000,0x0000,0x11d430010,0x11d4d0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d08124c90110,0x0450103d041001,0x0000,0x0000,0x04a0103d041001,0x0520103d041001,0x0000,0x0000,0x05d0103d0103d0803d041111]⟩
def n203 : Entry := ⟨9, [304,372,901], 639, [0x03d0805d0405d0405d0405d0405d0407a0710b7003d08acf8,0x0790807a0707a0707a0707a07079088cc8,0x05d0403d0805d0405d0407a0703d088cc8,0x075070750705d04075078888,0x05d0403d0805d0403d088888,0x0750707507075070750707a0707507a8a8,0x06d0606d0606d0606d068888,0x05d0403d0805d0403d088888,0x06d0606d0606d0606d0607a0706d06a8a8,0x06d0606d0606d0606d068888,0x05d0405d0405d0405d0407a0705d04a8a8,0x05d0403d0805d0403d088888,0x05d0405d0405d0405d048888,0x05d0405d0405d0405d040750705d04a8a8,0x05d0405d0405d0405d0406d0605d04a8a8,0x03d0807a0707a0707a071186303d088cc8,0x03d0803d0803d0803d088888,0x03d080790807a0703d088888,0x03d0807507075070750711d7303d088cc8,0x03d0806d0606d0606d0611d7d03d088cc8,0x03d0805d0405d0403d088888,0x07a0707a0705d0405d0105d0405d0405d0405d01aaaa,0x05d0405d0403d0803d0105d0405d0403d0803d01aaaa,0x07a0707a07079080790107a0707a070790807901aaaa,0x075070750705d0405d0105d0405d0405d0405d01aaaa,0x06d0606d0605d0405d0105d0405d0405d0405d01aaaa,0x05d040620105d0400e0,0x062010620103d0803d01062011264003d0803d01aaaa]⟩
def n204 : Entry := ⟨8, [304,372,901,406], 1151, [0x03d0803d0803d0807a0f10ba02470,0x07a0f07a0f0440,0x03d0807a0f0440,0x0000,0x0000,0x0750f07a0f2020,0x0000,0x0000,0x06d0e07a0f2020,0x0000,0x05d0c07a0f2020,0x0000,0x0000,0x05d0c0750f2020,0x05d0c06d0e2020,0x0000,0x0000,0x03d0807a0f2020,0x0000,0x0000,0x03d0805d0c2020,0x07a0f05d0105d0c05d012222,0x03d0803d0103d0803d012222,0x07a0f0790107a0f079012222,0x0750f05d0105d0c05d012222,0x06d0e05d0105d0c05d012222,0x03d0803d0105d0c03d012222,0x0620103d086000]⟩
def n205 : Entry := ⟨11, [323], 255, [0x03d0206d0106d0106d0110bd003d02a8a8,0x0790207a0207a02079028888,0x06d0103d0206d0106d0110be803d028cc8,0x075010750107501075011189007501a8a8,0x06d0106d0103d0206d0106d0103d02a8a8,0x07501075010750107501118a807501a8a8,0x06d0106d0106d0106d011189606d01a8a8,0x06d0106d0103d0206d0106d0103d02a8a8,0x06d0106d0106d0106d01118ae06d01a8a8,0x06d0106d0106d010750106d0106d0106d0106d01ca0f,0x05d0207a0211e9805d028888,0x05d0203d0205d0203d028888,0x05d020790211eb005d028888,0x05d02075010750107501126a005d028cc8,0x05d0206d0106d0106d01126a605d028cc8,0x03d0207a0211e9903d028888,0x03d0203d0203d0203d028888,0x03d020790211eb103d028888,0x03d02075010750107501126a103d028cc8,0x03d0206d0106d0106d01126a703d028cc8,0x03d0205d02128b003d028888,0x065010650107a0207a01065011255007a0207a01aaaa,0x06d0106d0103d0203d0106d0106d0103d0203d01aaaa,0x0650106501079020790106501125680790207901aaaa,0x06d0106d0106d01e000,0x06d010750106d01e000,0x065010650105d0205d010650112d0005d0205d01aaaa,0x065010650103d0203d010650112d0103d0203d01aaaa]⟩
def n206 : Entry := ⟨10, [323,339], 503, [0x03d0405d0205d0205d0210c0003d04a8a8,0x0790407a0407a04079048888,0x05d0203d0405d0205d0210c1803d048cc8,0x06d0306d0306d0306d03118c606d03a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x06d0306d0306d0306d03118de06d03a8a8,0x05d0205d0205d0205d02118c805d02a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x05d0205d0205d0205d02118e005d02a8a8,0x05d0205d0205d0205d0205d0205d0206d03126d005d02acf8,0x03d0407a0411ec903d048888,0x03d0403d0403d0403d048888,0x03d040790411ee103d048888,0x03d0406d0306d0306d031279003d048cc8,0x03d0405d0205d0205d021279203d048cc8,0x065010650107a040650111cb207a04a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x0650106501079040650111cca07904a8a8,0x06d030750106d03e000,0x05d020650105d0205d0105d0205d0205d0205d0105d01ca8f,0x065010650103d0406501127f003d04a8a8,0x055010550107a040550111cb007a04a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x0550105501079040550111cc807904a8a8,0x06d030550106d0306d0105d0206d0306d0306d0106d01ca8f,0x05d020750105d02e000,0x055010550103d0405501127f203d04a8a8,0x05d0205d0106d0306d0105d0205d0205d0105d0205d01ca8f]⟩
def n207 : Entry := ⟨9, [323,339,340], 967, [0x03d0805d0205d0205d0210c3003d08a8a8,0x0790807a0807a08079088888,0x05d0203d0805d0205d0210c4803d088cc8,0x03d0807a0811ef903d088888,0x03d0803d0803d0803d088888,0x03d080790811f1103d088888,0x065010650107a0806501119b207a08a8a8,0x05d0205d0203d0805d0205d0203d08a8a8,0x06501065010790806501119ca07908a8a8,0x065010650103d08065011270003d08a8a8,0x055010550107a0805501119b007a08a8a8,0x05d0205d0203d0805d0205d0203d08a8a8,0x05501055010790805501119c807908a8a8,0x055010550103d08055011270203d08a8a8,0x05d0205d0106d0306d0105d0205d0205d0105d0205d01ca8f,0x04d0104d0107a0804d01119b607a08a8a8,0x05d0205d0203d0805d0205d0203d08a8a8,0x04d0104d010790804d01119ce07908a8a8,0x04d0104d0103d0804d011270c03d08a8a8,0x05d0205d01075050750105d0205d0205d0105d0205d01ca8f,0x06d0306d01075050750105d0206d0306d0106d0306d01ca8f]⟩
def n208 : Entry := ⟨8, [323,339,340,374], 1863, [0x03d0803d0803d0803d0810c6003d08a8a8,0x0791007a1007a10079108888,0x03d0803d0803d0803d0810c7803d088cc8,0x03d0803d0803d0803d081195b03d08a8a8,0x03d0803d0803d0803d0803d0803d08a8a8,0x03d0803d0803d0803d081197303d08a8a8,0x055090550907a1005509119e007a10a8a8,0x03d0803d0803d0803d0803d0803d08a8a8,0x05509055090791005509119f807910a8a8,0x03d0803d0803d0803d088888,0x04d0904d0907a1004d09119e607a10a8a8,0x03d0803d0803d0803d0803d0803d08a8a8,0x04d0904d090791004d09119fe07910a8a8,0x03d0803d0803d0803d088888,0x06d0b0750d05d0a06d0b8888,0x025011276007a10127301198207a10a8a8,0x03d0803d0803d0803d0803d0803d08a8a8,0x025011277807910127481199a07910a8a8,0x03d080650103d08e000,0x02d0302d0105d0a05d0105d0a05d0a05d0a05d0105d01ca8f,0x035050350105d0a05d0105d0a05d0a05d0a05d0105d01ca8f]⟩
def n209 : Entry := ⟨7, [323,339,340,374,416], 3911, [0x10c900010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0250107a101001,0x0000,0x0000,0x0000,0x05d1a0001,0x05d1a0001,0x0000,0x0000,0x0000,0x062011000,0x02a0105d0a1001,0x0320105d0a1001,0x0000]⟩
def n210 : Entry := ⟨7, [323,339,340,374,928], 2887, [0x03d1807a102020,0x0000,0x03d1807a100440,0x03d1803d180440,0x0000,0x03d1807a102020,0x0000,0x0000,0x07a1007a102020,0x0000,0x0000,0x0000,0x07a1007a102020,0x0000,0x0000,0x0250107a100060,0x03d1803d182020,0x07a1007a102020,0x03d1803d182020,0x0550102d130202,0x04d01035150202]⟩
def n211 : Entry := ⟨9, [323,339,356], 999, [0x03d0403d0403d0403d0410cc003d04a8a8,0x0790807a0807a08079088888,0x03d0403d0403d0403d0410cd803d048cc8,0x05d0605d0605d0605d06118f805d06a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x05d0605d0605d0605d061191005d06a8a8,0x03d0403d0403d0403d04118ff03d04a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x03d0403d0403d0403d041191703d04a8a8,0x03d0403d0403d0403d0403d0403d0405d06127c003d04acf8,0x065010650107a080650111b9207a08a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x0650106501079080650111baa07908a8a8,0x05d060650105d0605d0605d0605d06c88c,0x03d040650103d0403d0403d0403d04c88c,0x055050550507a080550511a7107a08a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x0550505505079080550511a8907908a8a8,0x05d060750505d06e000,0x03d0403d0403d0403d0403d040550503d041270303d04acf8,0x05d0606d0306d0105d0605d0605d068a8a,0x02d0302d0307a0802d0311a7607a08a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x02d0302d030790802d0311a8e07908a8a8,0x05d0605d0605d0605d0605d0602d0305d061270c05d06acf8,0x03d0406d0303d04e000,0x03d04075050750103d0403d0403d048a8a,0x02d0302d0102d030550101d0202d0302d0102d0302d01ca8f]⟩
def n212 : Entry := ⟨8, [323,339,356,357], 1927, [0x03d0403d0403d0403d0410cf003d04a8a8,0x0791007a1007a10079108888,0x03d0403d0403d0403d0410d0803d048cc8,0x065090650907a10065091192407a10a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x065090650907910065091193c07910a8a8,0x055050550507a10055051192107a10a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x055050550507910055051193907910a8a8,0x05d0606d0b05d0605d068888,0x02d0302d0307a1002d031192607a10a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x02d0302d030791002d031193e07910a8a8,0x03d040750d03d0403d048888,0x02d0302d0102d030550101d0202d0302d0102d0302d01ca8f,0x01d0201d0207a1001d021192807a10a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x01d0201d020791001d021194007910a8a8,0x01d0201d0101d020650101d0201d0201d0101d0201d01ca8f,0x03d040750d03d0403d048888,0x05d0606d0b05d0605d068888]⟩
def n213 : Entry := ⟨9, [323,339,374], 887, [0x03d0403d0403d0403d0410d2003d04a8a8,0x0790807a0807a08079088888,0x03d0403d0403d0403d0410d3803d048cc8,0x06d0706d0706d0706d0711ad606d07a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x06d0706d0706d0706d0711aee06d07a8a8,0x05d0605d0605d0605d0611b0805d06a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x05d0605d0605d0605d0611b2005d06a8a8,0x05d0605d0605d0605d0605d0605d0606d071270005d06acf8,0x03d0403d0403d0403d0411adb03d04a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x03d0403d0403d0403d0411af303d04a8a8,0x03d0403d0403d0403d048888,0x03d0403d0403d0403d0403d0403d0405d061270503d04acf8,0x055050550507a080550511ce007a08a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x0550505505079080550511cf807908a8a8,0x06d0706d0705d0606d078888,0x05d060750505d06e000,0x03d0403d0403d0403d048888,0x025011288007a081282011bc207a08a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x0250112898079081283811bda07908a8a8,0x06d070350106d07e000,0x05d060250105d0605d0105d0605d0605d0605d0105d01ca8f,0x03d040650103d04e000,0x02d0302d0105d0605d0105d0605d0605d0605d0105d01ca8f]⟩
def n214 : Entry := ⟨8, [323,339,374,400], 1911, [0x10d500010,0x0000,0x0000,0x0000,0x0000,0x0000,0x11b380010,0x0000,0x0000,0x127300010,0x0000,0x0000,0x0000,0x0000,0x127350010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0250107a081001,0x0000,0x0000,0x0000,0x0250105d0e1001,0x0000,0x05d0e0001,0x0000,0x0000,0x0000,0x032011000,0x1285005d061001,0x062011000,0x02a0105d061001,0x0000]⟩
def n215 : Entry := ⟨7, [323,339,374,400,933], 2903, [0x10d800010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x032011000,0x062011000,0x0000,0x05d010100]⟩
def n216 : Entry := ⟨8, [323,339,374,912], 1399, [0x03d0c07a082020,0x0000,0x03d0c07a080440,0x06d0f06d0f0440,0x0000,0x06d0f07a082020,0x05d0e07a082020,0x03d0c03d0c2020,0x05d0e07a082020,0x05d0e05d0e05d0e06d0f127602470,0x03d0c03d0c0440,0x0000,0x03d0c07a082020,0x0000,0x03d0c03d0c03d0c05d0e127652470,0x0000,0x0000,0x07a0807a082020,0x0000,0x0750d05d0e6000,0x0000,0x0250107a080060,0x03d0c03d0c2020,0x07a0807a082020,0x06d0f06d0f2020,0x0250105d0105d0e05d0105d014207,0x03d0c03d0c2020,0x0550102d0b0202]⟩
def n217 : Entry := ⟨10, [323,357], 511, [0x03d0203d0203d0203d0210db003d02a8a8,0x0790407a0407a04079048888,0x03d0203d0203d0203d0210dc803d028cc8,0x0750307503075030750311b6007503a8a8,0x03d0203d0203d0203d0203d0203d02a8a8,0x0750307503075030750311b7807503a8a8,0x06d0306d0306d0306d0311b6606d03a8a8,0x03d0203d0203d0203d0203d0203d02a8a8,0x06d0306d0306d0306d0311b7e06d03a8a8,0x06d0306d0306d030750306d0306d0306d0306d03ca0f,0x05d0205d0205d0205d0211b7005d02a8a8,0x03d0203d0203d0203d0203d0203d02a8a8,0x05d0205d0205d0205d0211b8805d02a8a8,0x05d0205d0205d0205d0205d0205d02075031279205d02acf8,0x05d0205d0205d0205d0205d0205d0206d031279c05d02acf8,0x03d0203d0203d0203d0211b7103d02a8a8,0x03d0203d0203d0203d0203d0203d02a8a8,0x03d0203d0203d0203d0211b8903d02a8a8,0x03d0203d0203d0203d0203d0203d02075031279303d02acf8,0x03d0203d0203d0203d0203d0203d0206d031279d03d02acf8,0x03d0203d0203d0205d0203d0203d0203d0203d02ca0f,0x065030650307a0407a030650311f2407a0407a03aaaa,0x03d0203d0203d0203d0103d0203d0203d0203d01aaaa,0x065030650307904079030650311f3c0790407903aaaa,0x06d0306d0306d03e000,0x06d030750306d03e000,0x05d0205d0205d0205d0205d0105d0105d020650305d02127fa05d0205d01affa,0x03d0203d0203d0203d0203d0103d0103d020650303d02127fb03d0203d01affa,0x01d0201d0207a0407a0201d0211f2807a0407a02aaaa,0x03d0203d0203d0203d0203d0203d0203d0203d02aaaa,0x01d0201d02079040790201d0211f400790407902aaaa,0x0750307503075030750307501075010750301d0207503127f20750307501affa,0x06d0306d0306d0306d0306d0106d0106d0301d0206d03127fc06d0306d01affa,0x03d0203d0203d02e000,0x03d0205d0203d02e000,0x01d0201d0101d0201d0101d0201d02065010650101d0201d0206503128e001d0201d0101d0201d01ffff]⟩
def n218 : Entry := ⟨9, [323,357,391], 639, [0x03d0603d0603d0603d0610de003d06a8a8,0x0790807a0807a08079088888,0x03d0603d0603d0603d0610df803d068cc8,0x0750707507075070750711c2007507a8a8,0x03d0603d0603d0603d0603d0603d06a8a8,0x0750707507075070750711c3807507a8a8,0x06d0706d0706d0706d0711c2606d07a8a8,0x03d0603d0603d0603d0603d0603d06a8a8,0x06d0706d0706d0706d0711c3e06d07a8a8,0x06d0706d0703d0606d078888,0x05d0605d0605d0605d0611c2805d06a8a8,0x03d0603d0603d0603d0603d0603d06a8a8,0x05d0605d0605d0605d0611c4005d06a8a8,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x03d0603d0603d0603d0611c2903d06a8a8,0x03d0603d0603d0603d0603d0603d06a8a8,0x03d0603d0603d0603d0611c4103d06a8a8,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x12ac012a3007a0807a011291011fb007a0807a01aaaa,0x03d0612c7003d0612b2003d0603d0103d0603d0603d0603d0603d0103d01faaf,0x12ad812a4807908079011292811fc80790807901aaaa,0x0750700d0107507e000,0x06d070150106d07e000,0x05d060250105d06e000,0x03d060450103d06e000]⟩
def n219 : Entry := ⟨8, [323,357,391,400], 1663, [0x10e100010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x11fe007a081001,0x1294003d0e1001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x129a003d061001,0x129d0079081001,0x12a001000,0x12a061000,0x12a081000,0x12a091000,0x07a011000]⟩
def n220 : Entry := ⟨7, [323,357,391,400,913], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12970079081001,0x0000,0x0000,0x0000,0x0000,0x107b01000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07c010100]⟩
def n221 : Entry := ⟨6, [323,357,391,400,913,930], 6265, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n222 : Entry := ⟨7, [323,357,391,400,929], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0103d060101]⟩
def n223 : Entry := ⟨7, [323,357,391,400,930], 2683, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x1297003d1e1001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n224 : Entry := ⟨7, [323,357,391,400,931], 2679, [0x10e400010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n225 : Entry := ⟨8, [323,357,391,912], 1151, [0x03d0e07a082020,0x07910079104004,0x03d0e07a080440,0x0750f0750f0440,0x0000,0x0750f07a082020,0x06d0f06d0f0440,0x0000,0x06d0f07a082020,0x0000,0x05d0e05d0e0440,0x0000,0x05d0e07a082020,0x0000,0x0000,0x03d0e03d0e0440,0x0000,0x03d0e07a082020,0x0000,0x0000,0x0000,0x11fe007a080060,0x12a6003d0e10e7003d0103d0e03d0e03d0103d017227,0x07a080790107a08079012222,0x0750f075010750f075012222,0x06d0f06d0106d0f06d012222,0x05d0e05d0105d0e05d012222,0x03d0e03d0103d0e03d012222]⟩
def n226 : Entry := ⟨7, [323,357,391,912,929], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x107b00010,0x0000,0x0000,0x0000,0x0000,0x0000,0x12a900010,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n227 : Entry := ⟨6, [323,357,391,912,929,432], 5244, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n228 : Entry := ⟨8, [323,357,391,912], 1663, [0x0000,0x0000,0x0000,0x11c500010,0x0000,0x0000,0x11c560010,0x0000,0x0000,0x0000,0x11c580010,0x0000,0x0000,0x0000,0x0000,0x11c590010,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a0811fe00110,0x12af003d0e1001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10ed003d061001,0x0000,0x00d01075071001,0x0150106d071001,0x0250105d061001,0x0450103d061001,0x07a010100]⟩
def n229 : Entry := ⟨7, [323,357,391,912,913], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12a900010,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0103d0e0101]⟩
def n230 : Entry := ⟨8, [323,357,391,913], 1149, [0x0790807a1007a10079088888,0x075070750707507075078888,0x075070750707507075078888,0x06d0706d0706d0706d078888,0x06d0706d0706d0706d078888,0x06d0706d0703d0606d078888,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x03d0603d0603d0603d068888,0x12c4010e7007a1012be012b5007a10a8a8,0x12c5810e880790812bf812b6807908a8a8,0x0750703d0603d0603d068888,0x06d0703d0603d0603d068888,0x05d0603d0603d0603d068888,0x03d0603d0603d0603d068888]⟩
def n231 : Entry := ⟨7, [323,357,391,913,416], 2173, [0x07a1007a100440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10ea007a106000,0x12bb007a1012b8007a1007a107024,0x0000,0x0000,0x0000,0x0000]⟩
def n232 : Entry := ⟨6, [323,357,391,913,416,946], 4217, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n233 : Entry := ⟨6, [323,357,391,913,416,946], 6265, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n234 : Entry := ⟨7, [323,357,391,913,416], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10ea01000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12c10079081001,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n235 : Entry := ⟨6, [323,357,391,913,416,946], 5241, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n236 : Entry := ⟨7, [323,357,391,913,928], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a1010ea00110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n237 : Entry := ⟨8, [323,357,391,913], 1661, [0x0000,0x0750711c802020,0x0750711c982020,0x06d0711c862020,0x06d0711c9e2020,0x0000,0x05d0611c882020,0x05d0611ca02020,0x0000,0x0000,0x03d0611c892020,0x03d0611ca12020,0x0000,0x0000,0x0000,0x12af007a101294007a102222,0x12b080790812958079082222,0x00d01075076000,0x0150106d076000,0x0250105d066000,0x0450103d066000,0x10ed012ca02020,0x10ee812cb82020,0x00d0103d064004,0x0150103d064004,0x0250103d064004,0x0450103d064004,0x03d0603d0603d010700]⟩
def n238 : Entry := ⟨7, [323,357,391,913,416], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12a9007a101001,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12cd01000,0x0000,0x0000,0x0000,0x0000,0x03d0103d060101]⟩
def n239 : Entry := ⟨6, [323,357,391,913,416,946], 4729, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n240 : Entry := ⟨10, [323,373], 383, [0x03d0405d0205d0205d0210f0003d04a8a8,0x0790407a0407a04079048888,0x05d0203d0405d0205d0210f1803d048cc8,0x0750307503075030750311da007503a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x0750307503075030750311db807503a8a8,0x06d0306d0306d0306d0311da606d03a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x06d0306d0306d0306d0311dbe06d03a8a8,0x06d0306d0305d0206d038888,0x05d0205d0205d0205d0211da805d02a8a8,0x05d0205d0203d0405d0205d0203d04a8a8,0x05d0205d0205d0205d0211dc005d02a8a8,0x05d0205d0205d0205d028888,0x05d0205d0205d0205d028888,0x03d0407a041225903d048888,0x03d0403d0403d0403d048888,0x03d04079041227103d048888,0x03d04075030750307503127f103d048cc8,0x03d0406d0306d0306d03127f703d048cc8,0x03d0405d0205d0205d02127fa03d048cc8,0x0450112df007a0407a0112d30123d007a0407a01aaaa,0x05d0205d0203d0403d0105d0205d0203d0403d01aaaa,0x0450112e08079040790112d48123e80790407901aaaa,0x0750304d0107503e000,0x06d030550106d03e000,0x05d020650105d02e000,0x0450112fd003d0403d0112eb0128e003d0403d01aaaa]⟩
def n241 : Entry := ⟨9, [323,373,384], 895, [0x05d0605d0605d0607a0410f302470,0x07a0407a040440,0x05d0607a040440,0x0750707a042020,0x05d0605d062020,0x0750707a042020,0x06d0707a042020,0x05d0605d062020,0x06d0707a042020,0x0000,0x05d0607a042020,0x05d0605d062020,0x05d0607a042020,0x0000,0x0000,0x07a04122890440,0x0000,0x0000,0x07507128210440,0x06d07128270440,0x05d061282a0440,0x0450107a040450107a0407a0407a0407a047207,0x05d0603d0805d0603d082222,0x07a040790807a04079082222,0x04d05075076000,0x0550506d076000,0x0650505d066000,0x0450103d0812d6003d082222,0x0450107a046000,0x05d0603d0405d0603d042222,0x07a040790407a04079042222,0x04a010750704a017000,0x0520106d07052017000,0x0620105d06062017000,0x12dc003d041231903d042222,0x07a0407a0407a017000]⟩
def n242 : Entry := ⟨8, [323,373,384,390], 1663, [0x10f600010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x122b90010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12a0903d041001,0x1243007a041001,0x12d9003d081001,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0107a0103d0803d041111]⟩
def n243 : Entry := ⟨7, [323,373,384,390,929], 2685, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10a201000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n244 : Entry := ⟨8, [323,373,384,918], 1407, [0x10f900010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x128510010,0x128570010,0x1285a0010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0812a090110,0x0000,0x0000,0x0000,0x04a0103d041001,0x0520103d041001,0x0620103d041001,0x0000,0x07a0103d0103d0803d041111]⟩
def n245 : Entry := ⟨9, [323,373,896], 639, [0x03d0805d0605d0605d0607a0403d08a8a8,0x0790807a0407a04079088888,0x05d0603d0805d0605d0607a0403d088cc8,0x0750707507075070750707507075078cc8,0x05d0603d0805d0603d088888,0x0750707507075070750707a0407507a8a8,0x06d0706d0706d0706d0706d0706d078cc8,0x05d0603d0805d0603d088888,0x06d0706d0706d0706d0707a0406d07a8a8,0x06d0706d0705d0606d078888,0x05d0605d0605d0605d0605d0605d068cc8,0x05d0603d0805d0603d088888,0x05d0605d0605d0605d0607a0405d06a8a8,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x03d0807a0407a0403d088888,0x03d0803d0803d0803d088888,0x03d080790807a0403d088888,0x03d080750707507075071288103d088cc8,0x03d0806d0706d0706d071288703d088cc8,0x03d0805d0605d0605d061288a03d088cc8,0x07a040450107a0400e0,0x05d0605d0603d0803d0105d0605d0603d0803d01aaaa,0x07a0407a04079080790107a0407a040790807901aaaa,0x0750707507075070750107507075070750707501aaaa,0x06d0706d0706d0706d0106d0706d0706d0706d01aaaa,0x05d0605d0605d0605d0105d0605d0605d0605d01aaaa,0x045010450103d0803d010450112e2003d0803d01aaaa]⟩
def n246 : Entry := ⟨8, [323,373,896,406], 1151, [0x03d0807a0c2020,0x0000,0x03d0807a0c0440,0x0750f0750f0440,0x0000,0x0750f07a0c2020,0x06d0f06d0f0440,0x0000,0x06d0f07a0c2020,0x0000,0x05d0e05d0e0440,0x0000,0x05d0e07a0c2020,0x0000,0x0000,0x03d0807a0c2020,0x03d0803d082020,0x03d0807a0c2020,0x0000,0x0000,0x0000,0x03d0803d0107a0c03d012222,0x12e8003d0812e5003d0103d0803d0803d0103d017227,0x07a0c0790107a0c079012222,0x0750f075010750f075012222,0x06d0f06d0106d0f06d012222,0x05d0e05d0105d0e05d012222,0x0450103d086000]⟩
def n247 : Entry := ⟨7, [323,373,896,406,929], 2173, [0x0000,0x0750f0750f0440,0x0000,0x06d0f06d0f0440,0x0000,0x0000,0x05d0e05d0e0440,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d0807a1c2020,0x07a1c07a1c2020,0x0000,0x0000,0x0000,0x0000]⟩
def n248 : Entry := ⟨7, [323,373,896,406,929], 3197, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d010100]⟩
def n249 : Entry := ⟨9, [323,373,390], 895, [0x03d0410fc02020,0x0000,0x03d0410fd80440,0x0750711dd02020,0x03d0403d042020,0x0750711de82020,0x06d0711dd62020,0x03d0403d042020,0x06d0711dee2020,0x0000,0x05d0611dd82020,0x03d0403d042020,0x05d0611df02020,0x0000,0x0000,0x03d04122e92020,0x03d0403d042020,0x03d04123012020,0x03d0403d040440,0x03d0403d040440,0x03d0403d040440,0x0450107a0812d6007a082222,0x03d0403d0403d0403d042222,0x045010790812d78079082222,0x04d05075076000,0x0550506d076000,0x0650505d066000,0x0450103d040450103d0403d0403d0403d047207,0x12ee007a041231907a042222,0x12fa003d0412f1003d0403d0403d0403d0403d047227,0x12ef80790412331079042222,0x00d010750700d017000,0x0150106d07015017000,0x0250105d06025017000,0x0450103d046000,0x03d0403d0403d017000]⟩
def n250 : Entry := ⟨8, [323,373,390,912], 1407, [0x0000,0x0000,0x0000,0x11e000010,0x0000,0x0000,0x11e060010,0x0000,0x0000,0x0000,0x11e080010,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x07a08124300110,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x10ff003d041001,0x0000,0x00d01075031001,0x0150106d031001,0x0250105d021001,0x0000,0x03d0107a0103d0403d0c1111]⟩
def n251 : Entry := ⟨8, [323,373,390,913], 1405, [0x0000,0x0750711e302020,0x0750711e482020,0x06d0711e362020,0x06d0711e4e2020,0x0000,0x05d0611e382020,0x05d0611e502020,0x0000,0x0000,0x0000,0x0000,0x03d0403d040440,0x03d0403d040440,0x03d0403d040440,0x0450107a1012d9007a102222,0x045010790812da8079082222,0x04d05075076000,0x0550506d076000,0x0650505d066000,0x03d0403d0403d0403d042222,0x10ff012f402020,0x1100812f582020,0x00d0103d044004,0x0150103d044004,0x0250103d044004,0x0000,0x03d0403d0403d0403d044444]⟩
def n252 : Entry := ⟨7, [323,373,390,913,416], 2429, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x12f701000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n253 : Entry := ⟨6, [323,373,390,913,416,946], 4473, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000]⟩
def n254 : Entry := ⟨8, [323,373,390,913], 1917, [0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0450103d041001,0x0000,0x0000,0x00d011000,0x015011000,0x025011000,0x0000,0x03d041000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x0000,0x03d040100]⟩
def n255 : Entry := ⟨9, [323,373,902], 639, [0x03d0403d0403d0403d041102003d04a8a8,0x0790807a0807a08079088888,0x03d0403d0403d0403d041103803d048cc8,0x0750707507075070750711e6007507a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x0750707507075070750711e7807507a8a8,0x06d0706d0706d0706d0711e6606d07a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x06d0706d0706d0706d0711e7e06d07a8a8,0x06d0706d0703d0406d078888,0x05d0605d0605d0605d0611e6805d06a8a8,0x03d0403d0403d0403d0403d0403d04a8a8,0x05d0605d0605d0605d0611e8005d06a8a8,0x05d0605d0605d0605d068888,0x05d0605d0605d0605d068888,0x03d0403d0403d0403d048888,0x03d0403d0403d0403d048888,0x03d0403d0403d0403d048888,0x03d0403d0403d0403d040750703d04a8a8,0x03d0403d0403d0403d0406d0703d04a8a8,0x03d0403d0403d0403d0405d0603d04a8a8,0x045010450107a0807a01045011300007a0807a01aaaa,0x03d0403d0403d0403d0103d0403d0403d0403d01aaaa,0x0450104501079080790104501130180790807901aaaa,0x075070750703d0403d0103d0403d0403d0403d01aaaa,0x06d0706d0703d0403d0103d0403d0403d0403d01aaaa,0x05d0605d0603d0403d0103d0403d0403d0403d01aaaa,0x03d040450103d0400e0]⟩
def n256 : Entry := ⟨8, [323,373,902,400], 1151, [0x03d0c03d0c03d0c07a08110502470,0x07a0807a080440,0x03d0c07a080440,0x0000,0x0000,0x0750f07a082020,0x0000,0x0000,0x06d0f07a082020,0x0000,0x0000,0x0000,0x05d0e07a082020,0x0000,0x0000,0x03d0c03d0c0440,0x0000,0x0000,0x03d0c0750f2020,0x03d0c06d0f2020,0x03d0c05d0e2020,0x0450107a086000,0x03d0c03d0103d0c03d012222,0x07a080790107a08079012222,0x0750f03d0103d0c03d012222,0x06d0f03d0103d0c03d012222,0x05d0e03d0103d0c03d012222,0x03d0c03d0103d0c03d012222]⟩
def nodes : Array Entry := #[n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13,n14,n15,n16,n17,n18,n19,n20,n21,n22,n23,n24,n25,n26,n27,n28,n29,n30,n31,n32,n33,n34,n35,n36,n37,n38,n39,n40,n41,n42,n43,n44,n45,n46,n47,n48,n49,n50,n51,n52,n53,n54,n55,n56,n57,n58,n59,n60,n61,n62,n63,n64,n65,n66,n67,n68,n69,n70,n71,n72,n73,n74,n75,n76,n77,n78,n79,n80,n81,n82,n83,n84,n85,n86,n87,n88,n89,n90,n91,n92,n93,n94,n95,n96,n97,n98,n99,n100,n101,n102,n103,n104,n105,n106,n107,n108,n109,n110,n111,n112,n113,n114,n115,n116,n117,n118,n119,n120,n121,n122,n123,n124,n125,n126,n127,n128,n129,n130,n131,n132,n133,n134,n135,n136,n137,n138,n139,n140,n141,n142,n143,n144,n145,n146,n147,n148,n149,n150,n151,n152,n153,n154,n155,n156,n157,n158,n159,n160,n161,n162,n163,n164,n165,n166,n167,n168,n169,n170,n171,n172,n173,n174,n175,n176,n177,n178,n179,n180,n181,n182,n183,n184,n185,n186,n187,n188,n189,n190,n191,n192,n193,n194,n195,n196,n197,n198,n199,n200,n201,n202,n203,n204,n205,n206,n207,n208,n209,n210,n211,n212,n213,n214,n215,n216,n217,n218,n219,n220,n221,n222,n223,n224,n225,n226,n227,n228,n229,n230,n231,n232,n233,n234,n235,n236,n237,n238,n239,n240,n241,n242,n243,n244,n245,n246,n247,n248,n249,n250,n251,n252,n253,n254,n255,n256]
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.Outside.L_meta_10454_aux.GraphTarget PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions PEqualNP.Outside.L_meta_10454_aux.GraphSymmetry

theorem verifiedCut {cap cs ch code} (validSlice : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (nd : ch.Nodup) (ok : verifyCut cap cs ch code = true) : Impossible true full cap ch.toFinset := by
  let m := (code-1)/256
  let witness := selectMask ((code-1) % 256) cs
  unfold verifyCut at ok
  simp only [Bool.and_eq_true,List.contains_iff_mem] at ok
  obtain ⟨hm,h⟩ := ok
  change (match makePool true (cliqueDomain m) cols7 witness with
    | none => false
    | some pool => poolCut true (cliqueDomain m) (cliqueBound m) cap witness.length pool ch) = true at h
  cases hp : makePool true (cliqueDomain m) cols7 witness with
  | none => rw [hp] at h; contradiction
  | some pool =>
    apply poolCut_sound (validSlice m hm) witness hp nd
    rw [hp] at h
    exact h

theorem verifiedIso {db cap ch code} (ok : verifyIso db cap ch code = true)
    (prev : ∀ j, j < db.size →
      (db[j]?.getD default).cap = cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full cap ch.toFinset := by
  let j := (code-65536)/48
  let p : Fin 48 := Fin.ofNat 48 ((code-65536) % 48)
  let dest := db[j]?.getD default
  simp only [verifyIso,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨hj,hcap⟩,eq⟩ := ok
  apply isoTransferOf p ch (stateOf dest) cap eq
  exact hcap ▸ prev j hj hcap

set_option maxRecDepth 8192 in
theorem nodeSound {db e}
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (ok : verify db e = true)
    (prev : ∀ j, j < db.size → (db[j]?.getD default).cap < e.cap →
      Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset) :
    Impossible true full e.cap (stateOf e).toFinset := by
  let ws := stateOf e
  let cs := choicesOf e
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
  obtain ⟨⟨⟨pos,nd⟩,notout⟩,all⟩ := ok
  apply enumStepOrdered nd (by simpa using notout)
  intro a ha b hb d hd ka kb lt fresh prop len
  have reverse : ¬b.toNat ≤ a.toNat := Nat.not_le.mpr lt
  have ne : a ≠ b := fun eq => (Nat.lt_irrefl _) (eq ▸ lt)
  have op : d ∈ [0,1,2,3] := by rcases allowed_four hd with h|h|h|h <;> simp_all
  have ka' : ka ∈ [false,true] := by cases ka <;> simp
  have kb' : kb ∈ [false,true] := by cases kb <;> simp
  have chk := all a ha b hb d op ka ka' kb kb'
  have nz := prop.1
  have no := prop.2
  simp only [verifyChild,beq_iff_eq,List.contains_iff_mem,Bool.or_eq_true,decide_eq_true_eq,
    reverse,ne,fresh,nz,no,Nat.not_lt.mpr len,or_self,ite_false] at chk
  split at chk
  next bad => exact indistSound bad _
  next =>
    split at chk
    next => contradiction
    next =>
      split at chk
      next =>
        have dec : e.cap-1 < e.cap := by omega
        exact verifiedIso chk (fun j hj heq => prev j hj (heq.trans_lt dec))
      next =>
        apply verifiedCut slices _ chk
        unfold childTwo kept
        have nodup := nd
        have rn : ((ws.erase a).erase b).Nodup := (nodup.erase a).erase b
        have notA : a ∉ (ws.erase a).erase b := fun h => ((nodup.mem_erase_iff).mp (List.mem_of_mem_erase h)).1 rfl
        have notB : b ∉ (ws.erase a).erase b := fun h => (((nodup.erase a).mem_erase_iff).mp h).1 rfl
        have old : ∀ x ∈ (ws.erase a).erase b, x ∈ ws := fun _ h => List.mem_of_mem_erase (List.mem_of_mem_erase h)
        have ya : bin d a b ≠ a := by intro eq; apply fresh; rw [eq]; exact ha
        have yb : bin d a b ≠ b := by intro eq; apply fresh; rw [eq]; exact hb
        have yr : bin d a b ∉ (ws.erase a).erase b := fun h => fresh (old _ h)
        change (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))).Nodup
        cases ka <;> cases kb <;> simp [kept,ya,yb,yr,notA,notB,rn,ne]


theorem forestSound (db : Array Entry)
    (slices : ∀ m ∈ masks, Slice true cols7 full (cliqueDomain m) (cliqueBound m))
    (good : ∀ j, j < db.size → verify db (db[j]?.getD default) = true)
    (j : Nat) (hj : j < db.size) :
    Impossible true full (db[j]?.getD default).cap (stateOf (db[j]?.getD default)).toFinset := by
  suffices ∀ k i, i < db.size → (db[i]?.getD default).cap = k →
      Impossible true full (db[i]?.getD default).cap (stateOf (db[i]?.getD default)).toFinset from this _ j hj rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hi hc
    apply nodeSound slices (good i hi)
    intro j hj lt
    exact ih _ (hc ▸ lt) j hj rfl
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok0 : verify nodes n0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok8 : verify nodes n8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok16 : verify nodes n16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok24 : verify nodes n24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok32 : verify nodes n32 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok40 : verify nodes n40 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok48 : verify nodes n48 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok56 : verify nodes n56 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok64 : verify nodes n64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok72 : verify nodes n72 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok80 : verify nodes n80 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok88 : verify nodes n88 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok96 : verify nodes n96 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok104 : verify nodes n104 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok112 : verify nodes n112 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok120 : verify nodes n120 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok128 : verify nodes n128 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok136 : verify nodes n136 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok144 : verify nodes n144 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok152 : verify nodes n152 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok160 : verify nodes n160 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok168 : verify nodes n168 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok176 : verify nodes n176 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok184 : verify nodes n184 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok192 : verify nodes n192 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok200 : verify nodes n200 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok208 : verify nodes n208 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok216 : verify nodes n216 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok224 : verify nodes n224 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok232 : verify nodes n232 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok240 : verify nodes n240 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok248 : verify nodes n248 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok256 : verify nodes n256 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok1 : verify nodes n1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok9 : verify nodes n9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok17 : verify nodes n17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok25 : verify nodes n25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok33 : verify nodes n33 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok41 : verify nodes n41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok49 : verify nodes n49 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok57 : verify nodes n57 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok65 : verify nodes n65 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok73 : verify nodes n73 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok81 : verify nodes n81 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok89 : verify nodes n89 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok97 : verify nodes n97 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok105 : verify nodes n105 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok113 : verify nodes n113 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok121 : verify nodes n121 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok129 : verify nodes n129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok137 : verify nodes n137 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok145 : verify nodes n145 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok153 : verify nodes n153 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok161 : verify nodes n161 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok169 : verify nodes n169 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok177 : verify nodes n177 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok185 : verify nodes n185 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok193 : verify nodes n193 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok201 : verify nodes n201 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok209 : verify nodes n209 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok217 : verify nodes n217 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok225 : verify nodes n225 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok233 : verify nodes n233 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok241 : verify nodes n241 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok249 : verify nodes n249 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok2 : verify nodes n2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok10 : verify nodes n10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok18 : verify nodes n18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok26 : verify nodes n26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok34 : verify nodes n34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok42 : verify nodes n42 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok50 : verify nodes n50 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok58 : verify nodes n58 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok66 : verify nodes n66 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok74 : verify nodes n74 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok82 : verify nodes n82 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok90 : verify nodes n90 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok98 : verify nodes n98 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok106 : verify nodes n106 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok114 : verify nodes n114 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok122 : verify nodes n122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok130 : verify nodes n130 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok138 : verify nodes n138 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok146 : verify nodes n146 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok154 : verify nodes n154 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok162 : verify nodes n162 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok170 : verify nodes n170 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok178 : verify nodes n178 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok186 : verify nodes n186 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok194 : verify nodes n194 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok202 : verify nodes n202 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok210 : verify nodes n210 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok218 : verify nodes n218 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok226 : verify nodes n226 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok234 : verify nodes n234 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok242 : verify nodes n242 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok250 : verify nodes n250 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok3 : verify nodes n3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok11 : verify nodes n11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok19 : verify nodes n19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok27 : verify nodes n27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok35 : verify nodes n35 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok43 : verify nodes n43 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok51 : verify nodes n51 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok59 : verify nodes n59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok67 : verify nodes n67 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok75 : verify nodes n75 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok83 : verify nodes n83 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok91 : verify nodes n91 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok99 : verify nodes n99 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok107 : verify nodes n107 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok115 : verify nodes n115 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok123 : verify nodes n123 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok131 : verify nodes n131 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok139 : verify nodes n139 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok147 : verify nodes n147 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok155 : verify nodes n155 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok163 : verify nodes n163 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok171 : verify nodes n171 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok179 : verify nodes n179 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok187 : verify nodes n187 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok195 : verify nodes n195 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok203 : verify nodes n203 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok211 : verify nodes n211 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok219 : verify nodes n219 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok227 : verify nodes n227 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok235 : verify nodes n235 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok243 : verify nodes n243 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok251 : verify nodes n251 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok4 : verify nodes n4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok12 : verify nodes n12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok20 : verify nodes n20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok28 : verify nodes n28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok36 : verify nodes n36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok44 : verify nodes n44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok52 : verify nodes n52 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok60 : verify nodes n60 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok68 : verify nodes n68 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok76 : verify nodes n76 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok84 : verify nodes n84 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok92 : verify nodes n92 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok100 : verify nodes n100 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok108 : verify nodes n108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok116 : verify nodes n116 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok124 : verify nodes n124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok132 : verify nodes n132 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok140 : verify nodes n140 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok148 : verify nodes n148 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok156 : verify nodes n156 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok164 : verify nodes n164 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok172 : verify nodes n172 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok180 : verify nodes n180 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok188 : verify nodes n188 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok196 : verify nodes n196 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok204 : verify nodes n204 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok212 : verify nodes n212 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok220 : verify nodes n220 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok228 : verify nodes n228 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok236 : verify nodes n236 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok244 : verify nodes n244 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok252 : verify nodes n252 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok5 : verify nodes n5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok13 : verify nodes n13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok21 : verify nodes n21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok29 : verify nodes n29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok37 : verify nodes n37 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok45 : verify nodes n45 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok53 : verify nodes n53 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok61 : verify nodes n61 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok69 : verify nodes n69 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok77 : verify nodes n77 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok85 : verify nodes n85 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok93 : verify nodes n93 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok101 : verify nodes n101 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok109 : verify nodes n109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok117 : verify nodes n117 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok125 : verify nodes n125 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok133 : verify nodes n133 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok141 : verify nodes n141 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok149 : verify nodes n149 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok157 : verify nodes n157 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok165 : verify nodes n165 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok173 : verify nodes n173 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok181 : verify nodes n181 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok189 : verify nodes n189 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok197 : verify nodes n197 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok205 : verify nodes n205 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok213 : verify nodes n213 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok221 : verify nodes n221 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok229 : verify nodes n229 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok237 : verify nodes n237 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok245 : verify nodes n245 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok253 : verify nodes n253 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok6 : verify nodes n6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok14 : verify nodes n14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok22 : verify nodes n22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok30 : verify nodes n30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok38 : verify nodes n38 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok46 : verify nodes n46 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok54 : verify nodes n54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok62 : verify nodes n62 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok70 : verify nodes n70 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok78 : verify nodes n78 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok86 : verify nodes n86 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok94 : verify nodes n94 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok102 : verify nodes n102 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok110 : verify nodes n110 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok118 : verify nodes n118 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok126 : verify nodes n126 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok134 : verify nodes n134 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok142 : verify nodes n142 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok150 : verify nodes n150 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok158 : verify nodes n158 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok166 : verify nodes n166 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok174 : verify nodes n174 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok182 : verify nodes n182 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok190 : verify nodes n190 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok198 : verify nodes n198 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok206 : verify nodes n206 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok214 : verify nodes n214 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok222 : verify nodes n222 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok230 : verify nodes n230 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok238 : verify nodes n238 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok246 : verify nodes n246 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok254 : verify nodes n254 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok7 : verify nodes n7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok15 : verify nodes n15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok23 : verify nodes n23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok31 : verify nodes n31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok39 : verify nodes n39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok47 : verify nodes n47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok55 : verify nodes n55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok63 : verify nodes n63 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok71 : verify nodes n71 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok79 : verify nodes n79 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok87 : verify nodes n87 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok95 : verify nodes n95 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok103 : verify nodes n103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok111 : verify nodes n111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok119 : verify nodes n119 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok127 : verify nodes n127 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok135 : verify nodes n135 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok143 : verify nodes n143 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok151 : verify nodes n151 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok159 : verify nodes n159 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok167 : verify nodes n167 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok175 : verify nodes n175 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok183 : verify nodes n183 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok191 : verify nodes n191 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok199 : verify nodes n199 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok207 : verify nodes n207 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok215 : verify nodes n215 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok223 : verify nodes n223 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok231 : verify nodes n231 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok239 : verify nodes n239 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok247 : verify nodes n247 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000000 in
theorem ok255 : verify nodes n255 = true := by decide +kernel
end PEqualNP.Outside.L_meta_10454_aux.Certificate

namespace PEqualNP.Outside.L_meta_10454_aux.Certificate
open PEqualNP.Outside.L_meta_10454_aux.LiveCircuits PEqualNP.Outside.L_meta_10454_aux.GraphTarget
set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem allChecks : ∀ j : Nat, j < nodes.size → verify nodes (nodes[j]?.getD default) = true
  | 0, _ => ok0
  | 1, _ => ok1
  | 2, _ => ok2
  | 3, _ => ok3
  | 4, _ => ok4
  | 5, _ => ok5
  | 6, _ => ok6
  | 7, _ => ok7
  | 8, _ => ok8
  | 9, _ => ok9
  | 10, _ => ok10
  | 11, _ => ok11
  | 12, _ => ok12
  | 13, _ => ok13
  | 14, _ => ok14
  | 15, _ => ok15
  | 16, _ => ok16
  | 17, _ => ok17
  | 18, _ => ok18
  | 19, _ => ok19
  | 20, _ => ok20
  | 21, _ => ok21
  | 22, _ => ok22
  | 23, _ => ok23
  | 24, _ => ok24
  | 25, _ => ok25
  | 26, _ => ok26
  | 27, _ => ok27
  | 28, _ => ok28
  | 29, _ => ok29
  | 30, _ => ok30
  | 31, _ => ok31
  | 32, _ => ok32
  | 33, _ => ok33
  | 34, _ => ok34
  | 35, _ => ok35
  | 36, _ => ok36
  | 37, _ => ok37
  | 38, _ => ok38
  | 39, _ => ok39
  | 40, _ => ok40
  | 41, _ => ok41
  | 42, _ => ok42
  | 43, _ => ok43
  | 44, _ => ok44
  | 45, _ => ok45
  | 46, _ => ok46
  | 47, _ => ok47
  | 48, _ => ok48
  | 49, _ => ok49
  | 50, _ => ok50
  | 51, _ => ok51
  | 52, _ => ok52
  | 53, _ => ok53
  | 54, _ => ok54
  | 55, _ => ok55
  | 56, _ => ok56
  | 57, _ => ok57
  | 58, _ => ok58
  | 59, _ => ok59
  | 60, _ => ok60
  | 61, _ => ok61
  | 62, _ => ok62
  | 63, _ => ok63
  | 64, _ => ok64
  | 65, _ => ok65
  | 66, _ => ok66
  | 67, _ => ok67
  | 68, _ => ok68
  | 69, _ => ok69
  | 70, _ => ok70
  | 71, _ => ok71
  | 72, _ => ok72
  | 73, _ => ok73
  | 74, _ => ok74
  | 75, _ => ok75
  | 76, _ => ok76
  | 77, _ => ok77
  | 78, _ => ok78
  | 79, _ => ok79
  | 80, _ => ok80
  | 81, _ => ok81
  | 82, _ => ok82
  | 83, _ => ok83
  | 84, _ => ok84
  | 85, _ => ok85
  | 86, _ => ok86
  | 87, _ => ok87
  | 88, _ => ok88
  | 89, _ => ok89
  | 90, _ => ok90
  | 91, _ => ok91
  | 92, _ => ok92
  | 93, _ => ok93
  | 94, _ => ok94
  | 95, _ => ok95
  | 96, _ => ok96
  | 97, _ => ok97
  | 98, _ => ok98
  | 99, _ => ok99
  | 100, _ => ok100
  | 101, _ => ok101
  | 102, _ => ok102
  | 103, _ => ok103
  | 104, _ => ok104
  | 105, _ => ok105
  | 106, _ => ok106
  | 107, _ => ok107
  | 108, _ => ok108
  | 109, _ => ok109
  | 110, _ => ok110
  | 111, _ => ok111
  | 112, _ => ok112
  | 113, _ => ok113
  | 114, _ => ok114
  | 115, _ => ok115
  | 116, _ => ok116
  | 117, _ => ok117
  | 118, _ => ok118
  | 119, _ => ok119
  | 120, _ => ok120
  | 121, _ => ok121
  | 122, _ => ok122
  | 123, _ => ok123
  | 124, _ => ok124
  | 125, _ => ok125
  | 126, _ => ok126
  | 127, _ => ok127
  | 128, _ => ok128
  | 129, _ => ok129
  | 130, _ => ok130
  | 131, _ => ok131
  | 132, _ => ok132
  | 133, _ => ok133
  | 134, _ => ok134
  | 135, _ => ok135
  | 136, _ => ok136
  | 137, _ => ok137
  | 138, _ => ok138
  | 139, _ => ok139
  | 140, _ => ok140
  | 141, _ => ok141
  | 142, _ => ok142
  | 143, _ => ok143
  | 144, _ => ok144
  | 145, _ => ok145
  | 146, _ => ok146
  | 147, _ => ok147
  | 148, _ => ok148
  | 149, _ => ok149
  | 150, _ => ok150
  | 151, _ => ok151
  | 152, _ => ok152
  | 153, _ => ok153
  | 154, _ => ok154
  | 155, _ => ok155
  | 156, _ => ok156
  | 157, _ => ok157
  | 158, _ => ok158
  | 159, _ => ok159
  | 160, _ => ok160
  | 161, _ => ok161
  | 162, _ => ok162
  | 163, _ => ok163
  | 164, _ => ok164
  | 165, _ => ok165
  | 166, _ => ok166
  | 167, _ => ok167
  | 168, _ => ok168
  | 169, _ => ok169
  | 170, _ => ok170
  | 171, _ => ok171
  | 172, _ => ok172
  | 173, _ => ok173
  | 174, _ => ok174
  | 175, _ => ok175
  | 176, _ => ok176
  | 177, _ => ok177
  | 178, _ => ok178
  | 179, _ => ok179
  | 180, _ => ok180
  | 181, _ => ok181
  | 182, _ => ok182
  | 183, _ => ok183
  | 184, _ => ok184
  | 185, _ => ok185
  | 186, _ => ok186
  | 187, _ => ok187
  | 188, _ => ok188
  | 189, _ => ok189
  | 190, _ => ok190
  | 191, _ => ok191
  | 192, _ => ok192
  | 193, _ => ok193
  | 194, _ => ok194
  | 195, _ => ok195
  | 196, _ => ok196
  | 197, _ => ok197
  | 198, _ => ok198
  | 199, _ => ok199
  | 200, _ => ok200
  | 201, _ => ok201
  | 202, _ => ok202
  | 203, _ => ok203
  | 204, _ => ok204
  | 205, _ => ok205
  | 206, _ => ok206
  | 207, _ => ok207
  | 208, _ => ok208
  | 209, _ => ok209
  | 210, _ => ok210
  | 211, _ => ok211
  | 212, _ => ok212
  | 213, _ => ok213
  | 214, _ => ok214
  | 215, _ => ok215
  | 216, _ => ok216
  | 217, _ => ok217
  | 218, _ => ok218
  | 219, _ => ok219
  | 220, _ => ok220
  | 221, _ => ok221
  | 222, _ => ok222
  | 223, _ => ok223
  | 224, _ => ok224
  | 225, _ => ok225
  | 226, _ => ok226
  | 227, _ => ok227
  | 228, _ => ok228
  | 229, _ => ok229
  | 230, _ => ok230
  | 231, _ => ok231
  | 232, _ => ok232
  | 233, _ => ok233
  | 234, _ => ok234
  | 235, _ => ok235
  | 236, _ => ok236
  | 237, _ => ok237
  | 238, _ => ok238
  | 239, _ => ok239
  | 240, _ => ok240
  | 241, _ => ok241
  | 242, _ => ok242
  | 243, _ => ok243
  | 244, _ => ok244
  | 245, _ => ok245
  | 246, _ => ok246
  | 247, _ => ok247
  | 248, _ => ok248
  | 249, _ => ok249
  | 250, _ => ok250
  | 251, _ => ok251
  | 252, _ => ok252
  | 253, _ => ok253
  | 254, _ => ok254
  | 255, _ => ok255
  | 256, _ => ok256
  | j+257,h => by change j+257 < 257 at h; omega

set_option maxRecDepth 16384 in
theorem complete : Lower true cols7 full 13 := by
  have impossible := forestSound nodes PEqualNP.Outside.L_meta_10454_aux.CliqueRestrictions.valid allChecks 0 (by decide +kernel)
  have home : stateOf n0 = cols7 := by decide +kernel
  change Impossible true full 12 (stateOf n0).toFinset at impossible
  rw [home] at impossible
  let xs : List (Sig × Row × Row) := [
    (cols7.getD 0 zero,4,5),
    (cols7.getD 1 zero,8,10),
    (cols7.getD 2 zero,1,5),
    (cols7.getD 3 zero,1,9),
    (cols7.getD 4 zero,1,17),
    (cols7.getD 5 zero,1,33),
    (cols7.getD 6 zero,1,65)]
  have er := essential_ok (T:=full) (raw:=cols7) (xs:=xs) (by decide +kernel)
  have eq : (xs.map Prod.fst).toFinset = cols7.toFinset := by decide +kernel
  rw [eq] at er
  exact lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun a h => er a (List.mem_toFinset.mpr h)) impossible
end PEqualNP.Outside.L_meta_10454_aux.Certificate


theorem PEqualNP.Outside.L_meta_10454 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10454_aux.GraphTarget.finish PEqualNP.Outside.L_meta_10454_aux.Certificate.complete
