import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_11008.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_11008
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
def graph : Sig := 0xfffffffffffffffffffffffffffffffcffffffffffffffffffffffeeffffffccfffffffffffffffafffffffffffff0f0fffefffefffafffaeeeeeeee00000000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
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


abbrev Bits := BitVec 62
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 62 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 62 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 62 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 62 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 62) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 62) (j : Fin 9) :
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 62) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 62) :
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
    if (rs ||| column d z.2) != BitVec.allOnes 62 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 62) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 62 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 62) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 62) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 62) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^63*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^63 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 62) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (63*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^63)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 63*(i+1)-63=63*i := by omega
      have ge : ¬63*(i+1)<63 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 62 = (a==BitVec.allOnes 62) := by
  by_cases h : a=BitVec.allOnes 62
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^62-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^62 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (63*i) =
      (f xs[i]==BitVec.allOnes 62) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^63*u+x+(2^63*v+1)=2^63*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^63 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬63*(i+1)+62<63 := by omega
      have di : 63*(i+1)+62-63=63*i+62 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 63) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (63*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 63) (i:=i) (by simpa using hi) _ ok.2
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
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 62 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 62
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

def kwDir (u p n : Bool) : Prop := p≠n ∧ (u=false → p=true)
structure KWRooms (u : Bool) (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (u : Bool) (T : Sig) : KWRooms u {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,by simp [kwDir,hp,hn]⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwBoolGate (d : Nat) (x y : Bool) : Bool :=
  if d=0 then x && y else if d=1 then x || y else if d=2 then x && !y else !x && y
def kwTurn (d : Nat) (a : Bool) :=
  (if d=3 then !a else a) == decide (d=1)
def kwTurnGate (d : Nat) (p n value : Bool) :=
  if value=decide (d=1) then kwTurn d p else kwTurn d n
theorem kwGateTable : ∀ (u : Bool) (d : Fin 4) (pa pb na nb : Bool),
    allowed u d.val → kwDir u (kwBoolGate d.val pa pb) (kwBoolGate d.val na nb) →
      kwDir u (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then pa else pb)
        (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then na else nb) := by
  unfold kwDir allowed
  decide +kernel

def kwFork {u : Bool} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms u (insert (bin d a b) U) T) : KWRooms u (insert a (insert b U)) T := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir u (bit p z) (bit n z)) :
      kwDir u (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable u ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir u (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
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
      exact ⟨inS,separates p n (H.valid hv).2⟩
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
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {u T k S} (run : Live u T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf u T⟩
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
    exact ⟨kwFork hd ha hb fresh H⟩

def onlyWire (u : Bool) (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, kwDir u (bit p w) (bit n w) → w=v

theorem kwOwn {u S T v p n} (H : KWRooms u S T) (one : onlyWire u S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2
  exact eq ▸ hw

theorem kwCross {u S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire u S T a p na) (B : onlyWire u S T b p nb)
    (C : onlyWire u S T a pa n) (D : onlyWire u S T b pb n) : Impossible u T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwEnabled (u p n : Bool) : Bool := if u then p != n else p && !n
theorem kwEnabled_iff (u p n : Bool) : kwEnabled u p n=true ↔ kwDir u p n := by
  cases u <;> cases p <;> cases n <;> unfold kwEnabled kwDir <;> decide
def kwWireB (u : Bool) (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !(kwEnabled u (bit p w) (bit n w)) || w==v)
theorem kwWireB_sound {u ws T v p n} (h : kwWireB u ws T v p n=true) :
    onlyWire u ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hz
  have cut := (kwEnabled_iff _ _ _).mpr hz
  simpa only [cut,Bool.not_true,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (u : Bool) (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB u ws T a p (kwProbe neg (field 4)) && kwWireB u ws T b p (kwProbe neg (field 5)) &&
    kwWireB u ws T a (kwProbe pos (field 6)) n && kwWireB u ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {u pos neg T ws k v} (h : kwWord u pos neg T ws k v=true) : Impossible u T k ws.toFinset := by
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

def shortcut (u : Bool) (T : Sig) (ws : List Sig) (k v : Nat) : Bool :=
  if v.testBit 63 then
    let p := kwProbe v 0
    let n := kwProbe v 1
    bit p T && !bit n T && ws.all (fun w => !(kwEnabled u (bit p w) (bit n w)))
  else kwWord u ((v >>> 8) &&& 134217727) (v >>> 35) T ws k ((v &&& 255)+555810816)
theorem shortcut_sound {u T ws k v} (ok : shortcut u T ws k v=true) : Impossible u T k ws.toFinset := by
  unfold shortcut at ok
  split at ok
  · simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at ok
    intro j _ h
    cases u with
    | false =>
      obtain ⟨w,hw,hp,hn⟩ := mono_row_difference h rfl ok.1.1 ok.1.2
      have no := ok.2 w (List.mem_toFinset.mp hw)
      rw [hp,hn] at no
      exact (by decide : kwEnabled false true false ≠ false) no
    | true =>
      have diff : bit (kwProbe v 0) T ≠ bit (kwProbe v 1) T := by
        rw [ok.1.1,ok.1.2]
        decide
      obtain ⟨w,hw,hn⟩ := live_row_difference h diff
      have yes := (kwEnabled_iff true _ _).2 ⟨hn,fun q => by cases q⟩
      exact Bool.false_ne_true ((ok.2 w (List.mem_toFinset.mp hw)).symm.trans yes)
  · exact kwWord_sound ok
def shortcutBatch (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun j => shortcut g.mode (targetOf g) (stateSet g k (start+j)) k (packedAt data (64*j) 64))
theorem shortcutBlock {g k start n data} (h : shortcutBatch g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  right
  have hh := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have sum : start+(j-start)=j := by omega
  change shortcut _ _ (stateSet g k (start+(j-start))) _ _=true at hh
  rw [sum] at hh
  exact shortcut_sound hh
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
theorem lowerMixed {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def neighbor11008 (i : Fin 9) : Nat := [5, 5, 6, 6, 7, 0, 0, 2, 1].getD i.val 0
def absentRow11008 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor11008 i)
def presentRow11008 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor11008 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow11008 i) graph ≠ bit (presentRow11008 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow11008 i) (inputs.getD j.val zero) =
      bit (presentRow11008 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
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

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow11008 i) (presentRow11008 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g99Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g99C : List ColumnInfo := []
def g99A : List (List Nat) := [[],[80,97]]
def g99D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g99L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g99D3)
  | _ => emptyPacking
def g99I (_ _ : Nat) : Option (Nat × Nat) := none
def g99 : Forest := ⟨99,3,fun i => g99Y[i]?.getD (0,0),g99C,g99A,g99L,g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P3_0 : CutRow g99 3 0 1 := shortcutBlock (data:=fun _ => 0x22021188862120) (by decide +kernel)
theorem g99B3 : CutRow g99 3 0 1 := g99P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : mixedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g99 0 0)
  · exact (mixedEmpty g99 1 0)
  · exact (mixedEmpty g99 2 0)
  · exact g99B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS99 : Lower true (varsX 99) (graphGoal 99) 4 := lowerMixed (g:=g99) (i:=0) (hints:=85) (before_sound [] baseKnown) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS99 := extendKnown [] 4 [(99,[]),(101,[33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(178,[112,32,50,67,100]),(197,[32,16,101,117]),(225,[80,97,33,50,67,116]),(228,[32,81,49,67,116]),(291,[16,134,118]),(323,[128,16,101,81,117]),(326,[96,32,133,117]),(354,[128,81,32,50,67,116]),(418,[16,112,32,50,67,134]),(452,[96,113,32,49,67,82,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS99 : Known true KS99 := extend_ok (m:=99) baseKnown lowS99 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[33,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : CutRow g103 4 0 1 := shortcutBlock (data:=fun _ => 0x22021188862130) (by decide +kernel)
theorem g103B4 : CutRow g103 4 0 1 := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : mixedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g103 0 0)
  · exact (mixedEmpty g103 1 0)
  · exact (mixedEmpty g103 2 0)
  · exact (mixedEmpty g103 3 0)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore KS99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS103 : Lower true (varsX 103) (graphGoal 103) 5 := lowerMixed (g:=g103) (i:=0) (hints:=1621) (before_sound KS99 VS99) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS103 := extendKnown KS99 5 [(241,[80,65,98,49,50,112,48]),(422,[80,33,129,48,67,116,97]),(454,[96,114,48,67,133,66]),(481,[113,130,49,66]),(482,[16,96,114,48,66,133,83,67]),(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS103 : Known true KS103 := extend_ok (m:=103) VS99 lowS103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := []
def g109A : List (List Nat) := [[],[50]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g109L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g109D4)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,4,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : CutRow g109 4 0 1 := shortcutBlock (data:=fun _ => 0x240121904a4140) (by decide +kernel)
theorem g109B4 : CutRow g109 4 0 1 := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : mixedTables g109 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g109 0 0)
  · exact (mixedEmpty g109 1 0)
  · exact (mixedEmpty g109 2 0)
  · exact (mixedEmpty g109 3 0)
  · exact g109B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore KS103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS109 : Lower true (varsX 109) (graphGoal 109) 5 := lowerMixed (g:=g109) (i:=0) (hints:=26117) (before_sound KS103 VS103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS109 := extendKnown KS103 5 [(179,[112,33,16,49,67,84,101]),(227,[33,115,67,101]),(327,[128,49,32,33,81,117]),(357,[131,67,116]),(419,[16,32,115,67,133,101]),(453,[32,131,67,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS109 : Known true KS109 := extend_ok (m:=109) VS103 lowS109 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[(0x19e6799e6799e679,0x1866198661986619),(0x0,0x0),(0x1b56d5b56d5b56d5,0x1154551545515455),(0x0,0x0),(0x0,0x0),(0x2759d6759d6759d6,0x2318c6318c6318c6),(0x26b9ae6b9ae6b9ae,0x2689a2689a2689a2),(0x3caf2bcaf2bcaf2b,0xca328ca328ca328),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,4),(4,0,225,0,4),(32,0,197,0,4),(64,0,165,0,4),(128,0,101,0,4)]
def g229A : List (List Nat) := [[],[114,101],[32,117],[32,80,96,112],[80,118],[80,98,112,32],[96,82],[96,114,80,82],[112,32,82,101],[112,98]]
def g229D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30fd20fd10
def g229D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g229H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb6e300a260fe00450000fa0011006b47008
def g229L : Nat → Packing
  | 5 => (2,1,3,0,0,3,0,g229D5)
  | 6 => (1,0,3,0,0,0,0,g229D6)
  | _ => emptyPacking
def g229I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 2 8 1 3 g229H6
  | _ => fun _ => none
def g229 : Forest := ⟨229,6,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P5_0 : CutRow g229 5 0 2 := shortcutBlock (data:=fun _ => 0x84040b050a44310408002a144aa042) (by decide +kernel)
theorem g229B5 : CutRow g229 5 0 2 := g229P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P6_0 : CutRow g229 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B6 : CutRow g229 6 0 1 := g229P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : mixedTables g229 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g229 0 0)
  · exact (mixedEmpty g229 1 0)
  · exact (mixedEmpty g229 2 0)
  · exact (mixedEmpty g229 3 0)
  · exact (mixedEmpty g229 4 0)
  · exact g229B5
  · exact g229B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore KS109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS229 : Lower true (varsX 229) (graphGoal 229) 7 := lowerMixed (g:=g229) (i:=0) (hints:=536872453) (before_sound KS109 VS109) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS229 := extendKnown KS109 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS229 : Known true KS229 := extend_ok (m:=229) VS109 lowS229 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,7)]
def g231A : List (List Nat) := [[],[112,98]]
def g231D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 1=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore KS229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=536872533) (before_sound KS229 VS229) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS231 := extendKnown KS229 8 [(231,[]),(245,[32,65,49,117]),(359,[33,101,135]),(435,[16,66,50,134]),(438,[64,33,48,117,134]),(470,[64,48,133,118]),(483,[16,112,98,50,67,132]),(485,[32,129,80,49,67,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS231 : Known true KS231 := extend_ok (m:=231) VS229 lowS231 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0x21f90fc87e43f21f,0x1e80f407a03d01e),(0x344fa27d13e89f44,0x204f027813c09e04),(0x0,0x0),(0x0,0x0),(0x72e3971cb8e5c72,0x62c31618b0c5862),(0x1ed4f6a7b53da9ed,0x1e10f087843c21e1),(0x2e27713b89dc4ee2,0x2e07703b81dc0ee0),(0x2b4b5a5ad2d696b4,0x21430a1850c28614),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,5),(16,0,227,0,5),(64,0,179,0,5),(1,64,178,0,4),(128,16,99,0,4)]
def g243A : List (List Nat) := [[],[112,100]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f731
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x221c17f
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa
def g243L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g243D5)
  | 6 => (1,0,3,0,0,0,0,g243D6)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g243H6
  | _ => fun _ => none
def g243 : Forest := ⟨243,6,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 1=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1=true := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore KS231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS243 : Lower true (varsX 243) (graphGoal 243) 7 := lower_forest (g:=g243) (i:=0) (hints:=1074200661) (before_sound KS231 VS231) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS243 := extendKnown KS231 7 [(246,[32,65,117]),(373,[33,101,135]),(374,[16,64,32,133,101,118]),(423,[16,50,66,134]),(455,[32,16,49,65,101,117,133]),(467,[64,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS243 : Known true KS243 := extend_ok (m:=243) VS231 lowS243 (by decide +kernel)
def g486Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1724e5c939724e5c,0x132424c90932424c),(0xf2633c98cf2633c,0xd24234908d24234),(0x0,0x0),(0x0,0x0),(0x8f9523e548f9523,0x851521454851521),(0x32d55cb5572d55cb,0x129154a45529154a),(0x399a8e66a399a8e6,0x308a8c22a308a8c2),(0x3c4baf12ebc4baf1,0x2c4a8b12a2c4a8b1)]
def g486C : List ColumnInfo := [(34,0,452,0,4),(68,0,418,0,4),(132,0,354,0,4),(160,0,326,0,4),(258,0,228,0,4),(320,0,166,0,4)]
def g486A : List (List Nat) := [[],[133,118],[33,101,135],[33,117,134],[81,98,135],[81,98,113,130,33],[97,82],[97,82,130,113],[113,130,82,97],[113,130],[129,114,81,98,101],[129,114,101]]
def g486D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc3fa61fd10
def g486D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b8881bf
def g486H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6f00015e02031d1cc20000000006800003560090
def g486L : Nat → Packing
  | 6 => (2,1,3,0,0,3,0,g486D6)
  | 7 => (1,0,3,0,0,0,0,g486D7)
  | _ => emptyPacking
def g486I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 17 4 9 1 4 g486H7
  | _ => fun _ => none
def g486 : Forest := ⟨486,7,fun i => g486Y[i]?.getD (0,0),g486C,g486A,g486L,g486I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P6_0 : CutRow g486 6 0 2 := shortcutBlock (data:=fun _ => 0x88030380c8844104080032184ca042) (by decide +kernel)
theorem g486B6 : CutRow g486 6 0 2 := g486P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P7_0 : CutRow g486 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g486B7 : CutRow g486 7 0 1 := g486P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486T : mixedTables g486 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g486 0 0)
  · exact (mixedEmpty g486 1 0)
  · exact (mixedEmpty g486 2 0)
  · exact (mixedEmpty g486 3 0)
  · exact (mixedEmpty g486 4 0)
  · exact (mixedEmpty g486 5 0)
  · exact g486B6
  · exact g486B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486G : graphValid g486 (boundsBefore KS243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS486 : Lower true (varsX 486) (graphGoal 486) 8 := lowerMixed (g:=g486) (i:=0) (hints:=4866442832) (before_sound KS243 VS243) g486G g486T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS486 := extendKnown KS243 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS486 : Known true KS486 := extend_ok (m:=486) VS243 lowS486 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,8)]
def g247A : List (List Nat) := [[],[32,65,117]]
def g247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g247L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g247D8)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,8,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 1=true := g247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact g247B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore KS486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS247 : Lower true (varsX 247) (graphGoal 247) 9 := lower_forest (g:=g247) (i:=0) (hints:=537331285) (before_sound KS486 VS486) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS247 := extendKnown KS486 9 [(247,[]),(375,[33,101,135]),(439,[16,66,134]),(471,[32,16,65,101,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS247 : Known true KS247 := extend_ok (m:=247) VS486 lowS247 (by decide +kernel)
def g487Y : Array (Bits × Bits) := #[(0x250fb29bea60943e,0x210722806a20841c),(0x1b8443b48b2a6e11,0x98421b0832a2610),(0x2fe301a84a92bf8c,0x2fc301080a02bf0c),(0x0,0x0),(0x0,0x0),(0x26f0744e25659bc1,0x660c44e00451983),(0x6e8d77958401ba,0x28cc77858000a3),(0x10150691563b4054,0x1014029154384050),(0x3d130a40585df44c,0x341302005855d04c)]
def g487C : List ColumnInfo := [(1,0,486,0,8),(2,0,485,0,8),(4,0,483,0,8),(128,0,359,0,8),(256,0,231,0,8),(32,0,455,0,7),(64,0,423,0,7),(132,0,355,0,7),(258,0,229,0,7),(0,2,197,288,6),(0,4,291,192,6),(0,128,323,36,6),(0,256,165,66,6),(3,0,484,0,5),(5,0,482,0,5),(6,0,481,0,5),(32,2,197,256,5),(32,128,323,4,5),(33,0,454,0,5),(34,0,453,0,5),(64,4,291,128,5),(64,256,165,2,5),(65,0,422,0,5),(68,0,419,0,5),(130,0,357,0,5),(160,0,327,0,5),(256,2,197,32,5),(260,0,227,0,5),(35,0,452,0,4),(36,128,323,0,4),(66,256,165,0,4),(161,0,326,0,4),(192,4,291,0,4)]
def g487A : List (List Nat) := [[],[33,101,135],[113,130],[129,114,101]]
def g487D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x56ee5175d0110
def g487D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3a100830850800000a0200000016090400000501beaf4bbae8b8adcb5ad0b2ac4afab8acaaca9aa0a6a94a3a88a0a7c9da709aa6497a5894a4c91a408ea348ba2888a1c85a1082a047f9f87c9ec799e0769d4739c8709bc6d9b06a9a4679986498c619805e9745b9685895c55950529444f9384c92c499204691443908408fc3d8f03a8e4378d8348cc318c02e8b42b8a82888a1c86c198601444b1143f0e42106c1503c009ff805d243df8805d2439fd80dc543dfb81dc143df981dc143dfb71dc143df971dc143bfa871c143dfb711c143df9711c1439fd83dd1519fd80dd151ddf7350d51bfb8050d519fd84dc1519fd83dc151fbb8050f41fb88050f41dbd435c3419fd80dd5419ff805d541bef8255141fbb8050d41fb88050d41cff7650d41bfb8050d419fd83dc9419fd80dc941b7f854c941f755454541bf780545419fd83dc141dbd43dc1419ff805d331dfb805d331df8805d3319fd87d0b31df57550731df5415c3319fd84dd5319ff845d5319ff805d5319ff805d131bef8255131b7d85d0d31bfb8050d31b7f854c931df77454531bf780545319fd84dc1319ff805cd21bfb8050d219fd83dc121df541dc121dfb805d330fdb8050f30bdd83d0b30bfb8050b30df971d0330dfb805d1309fd87d0d30bf581d0d30bf980d0d30bdd8490d30fdb8050d30bfb8050d309fd87d0930bdd83d0930b7f854c9309fd84dc5309fd87d0530bdd83d0530f9d43d0530aff8650530f9d43505309fd84dd5109ff845d510bef8255110bfb8055110b7d85d0d10bfb8050d10bfb8050910b7f854c910ddf734c910df77550510dfb75d0110bf983d0110fb943d0110bf982d0110ff131d0110fd9434c110bfb8348110bf98348110ff14148110ff13148110f9b8050c43f988050c43d9d435c043bd78350731bd983d0330dbb74d0110f9d434c941df975d01109f980dd1519ef825d5419fb805d33197f855cb318ff865d1319fb805d13197f855cd2197f855cb30f9943d03309fb805d1309df835d5108ff865d11097d85dc910
def g487H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g487D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x201111040282c280c0800252070c0b0a098685c4c3c2c1402f130f0b05021a147c4c3c2c18685401c244c206040302011511101405402c241402221c606c018100c181502221c6061120082c08030c5220407131114881014285c20b0503021488161c104078300884711106002211c40506101e0c0440783110605881014140220291c506084710102c280c090040787880b190c14280c08004620703141d0c501a14202450a0603021188121c2c1a211c7050600884710142c28240c0a20707130b0a03020088102052211c70411084710102c28180c0a21004c888100f0c3c02221c5050608871010181502221c3c60c0a46040302011110802858545044411a001480c0904014714192200244c4468508302c2824100c080448916120c0b0a09040302012854444050485060515121480183010511c7050b0a06030248091c1a02211c4450b0605808847101c2c2825180c0a207080d0b0a460302808810270c40343091c0a20511c704808847141014511a0020405050900081c14340216211854610881c1038351a1402211c71005c3c014c81d1e1a17231c41a0c8610c0c7811e04901e80c404a0190068003fe9fe8fee7f43f89fb8fd67e83f29f88fbe7dc3ec9f58fa67d03e69f28f8e7c43e09ef8f767b83da9ec8f5e7ac3d49e58ef67603a69ce8e5671437e9bb8d7e6b435299e8cb662c30697b8bc65b42cc9628ade5642a294b8a4650427a93889964bc25692588fe46c22690f883e4101fc8f687863ac1c68da86ae3441908c485f62e81668a884fe264128891843e1f40ee870835618c0ba855826610c07e83c81be0c8058826810607002880c803e0007ff7150ffeb8a87ffdc143ffae0a1ffd54507fea1a83ff95131ffaa898ffd534c7ffa1a63ff50d31ffa6498fff42cc3fea1661ff9d130ffae8987ff434c3fea1a61ff5c930ffe84987fd424c3fe99261ff54530ffe82987fd414c3fe90a61ff95110ffaa8887fd53443ffa1a21ff50d10ffe84887fd42443fe99221e7d0e43f3a8621fff43547fea1aa3ff4c941ffe8598fff424c7fea1263ff50d21ffac5987fd624c2feba4877f5ca43bfae321dfd7090effb8a877fdc143ff6e0a1ff87050efeb88877f5c043bfee8a8dff73546ffb82a37f5d741bfae7a0fbd43d06feb96837f5c341dfeeca0dff75506febaa837fdcd41f7e86a0fbd43506ffb9283fd54541bfee0a0dfd75cc6feba6637f5cb31fea8398dfd70cc6ffbaa637f5d531bfee898dfd744c6ffb9263fd54531bfee098dff73486feb9a43fd50521bfee090dfd74cc3eea1e617f5cb30bfae3987fb40cc2ffba2617f5d130fbc86987dd434c2ffb92617fdc530bfeea885fd75442ffba2217f5d110bfee6885fd73442ffb92217f5c910fea82887f531443fda0221fe4c110ff240885ed7290efdb82873fdd941 else 0x811118101016050044604068443011d0a1018290a042441309420611084c2431481400f1014310800286c5421b0a0c100c080454504440001814b0a1d0920244c30c0a050403)
def g487H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x651896cbda7dcbe925c56ddb5081020af6be6aa8002f8d666b8c80014cf86500039b0001a28bad6834001ab5cb78000000000b59078f824adc337c81c34626e00077bb440000c2d6d7458a000101390c41f5e24ee88b6cc169500018010d2272a91800142c0bb59ce5b5cc200036b81cc24da6d00059ac84ff9d22547ad97af5c9340000ec689762f8001cb299cd4b41360820000004143c2e000977000203b653bf80000000490551c172fdee6a00058ca88c000000300dc080006b57150859b623a47fb7bb985230af83397380bd1b800211a0000511badce1423b6371924aa43400005c2420a1e1174ac000089d408e9c40018edb0dca73d7e84be2dabbf872a18e2b5018abdada52638f602800020512be7d4000373000000183c131c4a721720910f8003a56a380006db845472582163c01c6cea0006962c33cba8a1d989579ab1e2e800107da05022086a452b40a19904d89d6083e38002c56f6be1f826d092cb470e000000024f6289a6340340e02050310a60d1000622400001302171400591424001402000006050151040605030609010b02020000000a030a06
def g487D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10111201a0488e1490100305911c62844a9081223860a4860a62010101c70a508408e2030e182c03c423881c311811c28818305002639c1038f0c14a40202039018890911c0051cf860b20047383860a348008e207992347bdb86054a468e32946e0dc00ff90ffd43ff10ffd51ffd07fd41ffcc7fd31ff487ff30ff4c3fd10
def g487H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41d63480f106000072466bc84e00051ac37c81c00002e80000000000000107d45e2fe4c8000000be8c0d9594001e0849011120bfe43926dad8744c3a00020cc000f22123000000169da078003c3d203000000000000000030114230230001b2a077a3faf48000e8783822dedc957a000000485471886700061c14a3ade000756400151782b00034c6ed2000390a80ce1f226694c000c25c2578015a292c342cb1e00f00122d14410bd62900000010120009068002282000276857c001df2b6e9d6d5a8034f083999c81b022309b34e1555d000011ee8903d02839a80002e6f9e800289ce9c5b5e5c795cb6800000000014d55b65b860921859291d6a85b0cefb37048000017673c4600019ed9e0c160000c9262cb9b01c5e1a634393dca800023279bc001c32b301abd0da5d400000026aece8bab20a144d414332cd604560000000520001e2a537184e0ae000735f860001a2490e401536c0377eae883c5de36b748bcbdb280a410d0c52bd05c9aa0000cc4000bde91c40001360000000000ce500044116c0000b162db400009e1630003c8a00000590598e4000e88abc5c720000003a30da600000046bb43200009763040000004010001fe3a2231f412f0190550103049a09000909270a04030103100102120106051c1302001e000006000602010008070000010734000002120a0d000009
def g487D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40e1ff
def g487H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d622c00f10000d2ca003a30000000000003c9002356440045441997a000000000000000040377002c700000000000000051400001f64c35200003000000000016c0000000690000000085dd890ad4002260000000000000d000327c200000000c18000000014510860
def g487L : Nat → Packing
  | 6 => (1,4,6,0,0,0,0,g487D6)
  | 7 => (116,3,6,0,0,10,0,g487D7)
  | 8 => (115,2,6,0,0,13,0,g487D8)
  | 9 => (12,1,6,0,0,10,0,g487D9)
  | 10 => (1,0,6,0,0,0,0,g487D10)
  | _ => emptyPacking
def g487I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g487H7
  | 8 => lookupWord 46 227 8 13 7 2 g487H8
  | 9 => lookupWord 50 277 8 13 7 2 g487H9
  | 10 => lookupWord 8 83 4 10 4 2 g487H10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun i => g487Y[i]?.getD (0,0),g487C,g487A,g487L,g487I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_0 : CutRow g487 6 0 1 := shortcutBlock (data:=fun _ => 0x8000000000000041) (by decide +kernel)
theorem g487B6 : CutRow g487 6 0 1 := g487P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_0 : CutRow g487 7 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_13 : CutRow g487 7 13 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_15 : CutRow g487 7 15 96 := shortcutBlock (data:=fun _ => 0x840312094c843630840312094c8436300a8130380c8854100a8130380c8854100a8130380c8854100420c06830422310084040b050a444200c8230380c88642040012110cc42172002202118886213000420c068304223100a8130380c8853100a8130380c8853100c4240b050a467200c4240b050a464200c4240b050a464200a242118886252000a8130380c8853100a8130380c885312098030380c98452040012110cc4217200642121904a434000c2480c8606263100a2460381822530002206138986212000c4241b0d0e463100c4240b050a464200c4240b050a46720846080c8606623100a8130380c8854100a8130380c885410088030380c8845200c4241b0d0e463100c4241b0d0e463100420c068304223100420c06830422310042080c860622310042080c860622310800440a15824473102c0121904ac1400800112094c84173102c0121904ac1400084040b0d0a443100240121904e41300042080c860622310042080c86062231040012110cc4217200240121904a414000220603818621200846080c8606622000a8130380c885310088030380c884420084040b050a443100a8130380c88541040012110cc42172002202118886213000c4241b0d0e46310486040b050a64310088030380c884420088030380c884310486040b050a643100220211888621300088030380c884420486040b050a64420022021188862130002206038182213000c4241b0d0e463200c4240a850a467200c42c070308464200c4240a850a46720846080c860662310846080c860662310800440a1582447300a8130380c885410486040b050a64420486040b050a64310084040b050a44310486040b050a644200c2482c960e267100c4241b0d0e46310088130380c885410486040b050a6431048602110c8c64610408002a144aa0420088030380c884300088030380c884310486040b050a64310486040b050a64310408002a144aa0310810001c0c874042800000000000842280000000000084228000000000008422800000000000002280000000000080618000000000000041) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_111 : CutRow g487 7 111 5 := shortcutBlock (data:=fun _ => 0x846080c8606623100a8130380c8854100220603818221300486040b050a64310486040b050a6431) (by decide +kernel)
theorem g487B7 : CutRow g487 7 0 116 := (@joinRow g487 7 0 15 101 (@joinRow g487 7 0 13 2 g487P7_0 g487P7_13) (@joinRow g487 7 15 96 5 g487P7_15 g487P7_111))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_0 : CutRow g487 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_3 : CutRow g487 8 3 67 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_70 : CutRow g487 8 70 9 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_79 : CutRow g487 8 79 36 := shortcutBlock (data:=fun _ => 0x88030380c884520088030380c884520088030380c884520088030380c8845200220211888621300088030380c884521818041e0d87c0641818041e0d87c06400240121904a41400088030380c884520088030380c8845200240121904a41400050030580c502610050030580c502610486040b050a64420486040b050a64420088030380c884520088030380c884520486040b050a64420050030580c502610050030580c502610050030580c502610084040b050a444200c4241b0d0e464200c4241b0d0e464200c4241b0d0e46420408002a144aa0531818041e0d87c0640084040b050a44420088030380c884520088030380c884520408002a144aa0530408002a144aa05308100034188d406480000000000002618000000000008422) (by decide +kernel)
theorem g487B8 : CutRow g487 8 0 115 := (@joinRow g487 8 0 70 45 (@joinRow g487 8 0 3 67 g487P8_0 g487P8_3) (@joinRow g487 8 70 9 36 g487P8_70 g487P8_79))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P9_0 : CutRow g487 9 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B9 : CutRow g487 9 0 12 := g487P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P10_0 : CutRow g487 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B10 : CutRow g487 10 0 1 := g487P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487T : mixedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g487 0 0)
  · exact (mixedEmpty g487 1 0)
  · exact (mixedEmpty g487 2 0)
  · exact (mixedEmpty g487 3 0)
  · exact (mixedEmpty g487 4 0)
  · exact (mixedEmpty g487 5 0)
  · exact g487B6
  · exact g487B7
  · exact g487B8
  · exact g487B9
  · exact g487B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487G : graphValid g487 (boundsBefore KS247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS487 : Lower true (varsX 487) (graphGoal 487) 11 := lowerMixed (g:=g487) (i:=0) (hints:=4831839829) (before_sound KS247 VS247) g487G g487T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS487 := extendKnown KS247 11 [(487,[]),(499,[16,66,50,134]),(501,[32,16,65,49,101,117,133]),(502,[64,48,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS487 : Known true KS487 := extend_ok (m:=487) VS247 lowS487 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0x19b7c447e46b84bb,0x18b7c443e42b8019),(0xc20e188abef9afc,0xc2061808bef8af8),(0x11c3163ea090e34f,0x11c1163ea010230f),(0x0,0x0),(0x20041830d3037f8e,0x2000181091017f8e),(0x21f81e3f1c1c7c0f,0x21401a3c10107506),(0x3e001fc01fe07ff0,0x240029801bc45ce0),(0x3fffe0001fff8000,0xe3ee1010eee8030),(0x3fffffffe0000000,0x13df866f60000001)]
def g503C : List ColumnInfo := [(1,0,502,0,11),(2,0,501,0,11),(4,0,499,0,11),(16,0,487,0,11),(32,0,471,0,9),(64,0,439,0,9),(128,0,375,0,9),(256,0,247,0,9),(33,0,470,0,8),(65,0,438,0,8),(68,0,435,0,8),(36,0,467,0,7),(48,0,455,0,7),(129,0,374,0,7),(130,0,373,0,7),(257,0,246,0,7)]
def g503A : List (List Nat) := [[],[33,101,135],[16,66,134],[16,64,32,133,101,118],[32,16,65,101,117,133],[32,65,117],[64,133,118],[64,33,117,134]]
def g503D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x244278d982a4878c12181806979976809761464d5736cd20eac00c967a6c2975d582952b3adb54ac8cecaa5c3eb85d9655d154f07970bb2caba2a98fcec5a9dd3805530fcd4f2fba700aa5af1b125964e0154c7d764d4d0dc02a98be6a796a1b80553e1cbb2caba700aa5af1b121964e0154
def g503D8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x76e0154afe2a576e0154afee9176e0154afe6a774e0154e7ee5f74e0154afe69b74e0154e7e5db74e0154afeea574e0154afe6a574e0154e7ee5d74e0154e7e25d74e0154afee9974e0154e7edd974e0154e7e5d974e0154afe6a764e0154afe69f64e0154ebee5b64e0154afeea564e0154afe6a564e0154afee9d64e0154afe69d64e0154ebee5964e0154ebe25964e0154afe69f86e0154ebea5b86e0154ebe65b86e0154afe6a686e0154afe69e86e0154ebee5a86e0154afe69686e0154afe69286e0154afeea586e0154cfeea586e0154afee9d86e0154ebee5986e0154ebe25986e0154afee9586e0154edee9586e0154afee9186e0154eeee9186e0154efae8986e0154ebee1986e0154bfae8986e0154afeaa486e0154afe69c86e0154ebe65886e0154afeaa086e0154bfc68486e0154bde69676e0154bfc68676e0154afeea176e0154afeaa176e0154afe6a176e0154afe2a176e0154bf6e8d76e0154e7ee1f74e0154bde69774e0154beeaa674e0154beeaa274e0154bee69e74e0154fce99674e0154eee2a174e0154f6ee5d74e0154f6e25d74e0154f6ee1d74e0154f6e21d74e0154f6edd974e0154f6e5d974e0154fcee9574e0154fce29574e0154fce99574e0154fce59574e0154fece8574e0154e7ee1d74e0154e7e21d74e0154bdee9574e0154bfce8574e0154ebee1b64e0154bde69764e0154afe6a164e0154ebee1964e0154ebe21964e0154bdee9564e01549f7e8d979d8548ff6a5879d854abfe99879d854cbfea5869d854cbf65d869d854cfd6a1919d854cfd61d919d854cf7e8f985d8548ffe99985d854cbfe99985d854cf7e8d985d854e3fe9d865d854e3f29d865d854a7fe9d865d854cf7ea3935d854cf76a3935d854cf761b935d854eb761b935d854af769e9660c54cf7a5e9660c54af7e9d9660c54af76a67660c54af769e7660c54eb765a7660c54af7ea57660c54cf7ea57660c54af76a57660c54cf72a57660c54eb7a597660c54eb76597660c54af76a47660c548fee81989d6648dfea585215648fee81989d564add6849761464ade6809761464ccf615941d4648fe6a47560064abe6987560064aee6907560064af668c7560064afc68475600648fb68b9661e54abba9a9760a54abb69a9760a54aeb6929760a54afa6829760a548fb6a77660a54af96867660a54afae819560a54aeb6936560a54afa6836560a548fde8597e1954cfae4b90619548bfea586219548fee81989d9548f768e985d9548fee81985d954f0f5d9655d1548fee819859154afae8996e0154afc68496e0154afc68676e0154af6e8d76e01548fe6a774e0154afce8574e01548fe6a686e0154afae8986e0154afc68486e0154cbd619919d8548f7e8d985d8548f76a3935d854af56867660c548f7ea57660c54af66807660c54 else 0x4cfee81989d954abf69b879d954cdfe1d959d954dcfe91959d954dcf291959d9549efe91959d9549dfe95949d954cfdaa1919d954cfd6a1919d954cfde1d919d954ddda95919d954ddd695919d954cbf69a985d954cf768e985d9548ffaa2985d954cefe91985d954cfee81985d9549df697945d954c7f6a787dd154a7f69b87dd1548ffaa196dd1548ffea586dd154a7fe9d86dd154cbf65986dd154afbe8986dd154afee8186dd154d5fe1d95dd1549dfe9995dd154c7fe1d95dd154cfeaa190dd154cfe6a190dd154cfee1990dd154cfe61990dd154ddea9590dd154dde69590dd154dee69190dd154dcf295979d154cefa63879d154cefa61879d154bcfe95879d154bede85879d154beee81879d154bcf696869d154bee682869d154bcfe95869d154bebe89869d154beee81869d154bed684869d154aefaa2769d154aef6a2769d154bcf696769d154bed686769d154aefea1769d154aef2a1769d1549ef6a7659d154bee683659d154dcfa62659d154bcf69a659d154bee682865d154bebe89865d154beee81865d154bed684865d154dcf263955d154f4fe1f955d154bcf69b955d154beee81955d154bcfaa4955d154bcfaa0955d154f4fe1c955d154f4f21c955d154bcf698955d1549efaa7655d1549ef6a7655d154b6f69f655d154bee683655d154bcfaa6655d154bcfaa2655d154f4fe1e655d154f4f21e655d154bcf69a655d154f4fdda655d154bcfaa5655d154dcf2a5655d154f8fe19655d154f8f219655d154f8f9d9655d1549df69b955d154c7fe1f955d154e5fe1f955d154e5fe1c955d1549dfaa6655d1549dfaa5655d1549df2a5655d154f1f5d9655d1548ffaa197d91549f7e8d97d91548ffea587d9154abfe9987d9154afee8187d9154cbf6a786d9154d9fe1995d9154dcfe9195d9154ddbe8995d9154cbfe1995d91549fbe8995d9154dcf65574d91548ffe9d9859154cfee8198591548ffea197591549dfe9597591549f7e8d97591549fde8597591548ffea587591548ff6a58759154abfe998759154afee818759154eaf6938659154afee818659154abfaa08659154bbd6848659154cdfe1b9559154d9fe1b9559154d9f21b9559154dcf6939559154cbfe1b9559154cdf6639559154e9fe1b9559154cbfe1995591549efe9195591549fbe8995591549fee8195591549dfaa49559154e9fe189559154dcfe557459154afe69f96e0154cfee5f96e0154afe6a696e0154afe69e96e0154ebee5a96e0154afe69696e0154afe69296e0154afee9d96e0154cfee5d96e0154cfe65d96e0154ebee5996e0154afee9596e0154afee9196e0154efae8996e0154afe69c96e0154ebe65896e0154afeaa676e0154afe6a676e0154afe69e76e0154afe69676e0154afe69276e0154afeea576e0154afeaa576e0154afe6a5) else (if j<3 then 0xf9061564cfea1f9061564cfe61f9061564dbee9b9061564afe6828721564afde858721564cdfea58521564adfe918521564ecfe918521564edee818521564cefe91989d564cfee81989d564adf697879d5649bfe99949d5649fee81949d564cdf696985d5648ffaa2985d5649bf69b945d564e5fe5e9761464e5fe5d9761464adfaa49761464e5f65c9761464c7f69d989d464c7f6a5879d464e5fe95879d4648ff6a5879d464adfe95879d464cdfea5859d464e5fa9d859d464e5f69d859d464cdf65d859d4648ffe95985d464cdfe95985d464e5fe9d855d464e5f29d855d464a7fe9d855d464cfe681981d464cefea1941d464daf699941d464afe69e7560064cfb68b9661e54cfb68998dda549efe9195dda54cefea194dda54cef61994dda549efe91959da548ff6a69661654cbfe5a9661654aef69296616548ffaa49661654adf6967661654cfea9b9061654cfe29b9061654cfe9db9061654cfea5b9061654cfe25b9061654c7fea587dd654c7f61d96dd6549f7e8d96dd654cefea194dd654dede8594dd654c7f61f965d654cef6a3945d654cef61f945d654e6f61f945d654cefea194d96549efe9d94d9654afb69a9760a54afb6969760a54afbe999760a54afbe959760a54afb69e9660a54cfb65e9660a54afb6969660a54afbe9d9660a54afbe959660a54afb6a77660a54e7b65f7660a54afb6977660a54afb6a67660a54afb69e7660a54afb6967660a54afbe9d9560a54cfb65d9560a54afbe999560a54efae819560a54afb6a77560a54e7b65f7560a54afb69b7560a54afbea57560a54afb6a57560a54e7ba5d7560a54e7b65d7560a54afbe997560a54afb6a76560a54afb69f6560a54ebb65b6560a548ff69597e19548ff69197e1954cfde8597e1954afee8195e1954cbf6a786a1954cfe6a190a1954cfee1d90a1954cfea1d90a1954dde69590a1954dee69190a1954cfee9f9061954cfea9f9061954cfe69f9061954cfe29f9061954cfee9b9061954cfee979061954cfee939061954cfee5f9061954cfea5f9061954cfe65f9061954cfe25f9061954ebee9b9061954cfee579061954edee579061954efae4b9061954afe6828761954e9fe1b9561954eafe1b9461954cfbe1f9261954cfba1f9261954cfb61f9261954cfbe1b9261954debe939261954ebbe1b9261954cfee1f9061954cfea1f9061954cfe61f9061954cfee1b9061954ddee979061954deee939061954ebee1b9061954afe6828721954afde858721954afee818721954cbfea58621954abfe958621954e9fe958621954abfe918621954eafe918621954ebbe898621954ebee818621954cfdaa19121954cfde1d9121954cfda1d9121954cfd61d9121954cfd21d9121954ddda959121954ddd69591219548ffe95989d954cdfe95989d954cefe91989d95 else 0xdc13704035c40b101c604df10237c4080373608037f308dc100003c0100000000003c3cfcbc440003604003c740203cb43c4300d8164040000000c6ec68c62c5cc56c50c4ac44c3ec38c32c2cc26c20c1ac14c0ec08c02bfcbf6bf0beabe4bdebd8bd2bccbc6bc0bbabb4baeba8ba2b9cb96b90b8ab84b7eb78b72b6cb66b60b5ab54b4eb48b42b3cb36b30b2ab24b1eb18b12b0cb06b00afaaf4aeeae8ae2adcad6ad0acaac4abeab8ab2aacaa6aa0a9aa94a8ea88a82a7ca76a70a6aa64a5ea58a52a4ca46a40a3aa34a2ea28a22a1ca16a10a0aa049fe9f89f29ec9e69e09da9d49ce9c89c29bc9b69b09aa9a499e99899298c98698097a97496e96896295c95695094a94493e93893292c92692091a91490e9089028fc8f68f08ea8e48de8d88d28cc8c68c08ba8b48ae8a88a289c89689088a88487e87887286c86686085a85484e84884283c83683082a82481e81881280c8068007fa7f47ee7e87e27dc7d67d07ca7c47be7b87b27ac7a67a079a79478e78878277c77677076a76475e75875274c74674073a73472e72872271c71671070a7046fe6f86f26ec6e66e06da6d46ce6c86c26bc6b66b06aa6a469e69869268c68668067a67466e66866265c65665064a64463e63863262c62662061a61460e6086025fc5f65f05ea5e45de5d85d25cc5c65c05ba5b45ae5a85a259c59659058a58457e57857256c56656055a55454e54854253c53653052a52451e51851250c5065004fa4f44ee4e84e24dc4d64d04ca4c44be4b84b24ac4a64a049a49448e48848247c47647046a46445e45845244c44644043a43442e42842241c41641040a4043fe3f83f23ec3e63e03da3d43ce3c83c23bc3b63b03aa3a439e39839238c38638037a37436e36836235c35635034a34433e33833232c32632031a31430e3083022fc2f62f02ea2e42de2d82d22cc2c62c02ba2b42ae2a82a229c29629028a28427e27827226c26626025a25424e24824223c23623022a22421e21821220c2062001fa1f41ee1e81e21dc1d61c81ba1b419e19018216c15615013a13411e11010a1040fe0f00ea0e40de0d80d20cc0c60a009a09408608007a06405e04003a02c01e01801200c0060008ffaa49561a64cfee9f9061664cfea9f9061664cfe69f9061664cfe29f9061664cfee9b9061664cfe69b9061664cfee5f9061664cfea5f9061664cfe65f9061664cfe25f9061664cfe65b9061664cfee81989d6649efe91969d6649fbe89969d664cdf6a785a1564cfd6a191a1564cfde1d91a1564cfda1d91a1564dbd69991a1564afe6828761564cfee1))
def g503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ce00000000e04000000008500000000000000000000000000006080000000000000000203181000002b0800ad000000000a82e2d23a00e9128781927000001828000000000000000041fc6000000000000002140000000000000342000000000000005f20000000000000200
def g503D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xeca4ecaa5ffa61765537fd30bb2a9bfd985d954dfe4c2ecaa5ffe5176553bff0fba2a97fd96dd154dffc36e8aa6ff61b74552ffb2bba2a9fbf879d154fdec3ce8aa7efe1a74553f7d0d3a2a9fbd869d154fde434e8aa7ef9da74553f7aed3a2a9fbf659d154fde4c2e8aa7efe1974553f7d0cba2a9fbd865d154fde432e8aa7efe5574553f7b2aba2a9fbf655d154dffc32e8aa5ffe5574553eff2aba2a9f7c955d154fbf32ae8aa7df59574552ffb2fb22a9bff87d9154dfec3ec8aa7bfe1b64552ffb2bb22a9fbd74d9154bffcbac8aa5ff65d645537ff0eb22a9bfd8759154dffc32c8aa7bfe19645537fb0cb22a9efc8659154bffcaac8aa7dfe5564552ffb2ab22a9f7c9559154fbf32ac8aa7df59564553f7ae8b22a9ffb96e0154ffd4b700aa7fe65b80553ff12dc02a9ffb86e0154ffd43700aa7fe61b80553ff10dc02a9ffa76e0154ffdba700aa7fe5d380553ff6c9c02a9ff964e0154dffcbb0c2a6ffa5d861537fb2ec30a9bfc9761854bfecbcec2a6ff61e761537ff30bb0a9bfd985d854dfec32ec2a7f7e4d76152ffb2f3aac97fd979d954ffcbb700aa4ffe5d859937f720c2cc93fd989d6649fecbf0ab26dfe1685592feb2342ac97fb9061564dbec290ab24ffa62755927fb313aac93fe985d5649fe4c2eab26dfe5d851936fd2ec28c9b7d9761464dbe4bb0a324ffe5d851927fb313a8c99fd879d464dbec2cea324ffe61751927fb30ba8c9b7d855d4649fecc0ea325ef650751937f6eac00c9bfa7560064dfcbab00326fe1d5801927ff2cc3ca93ff9761a549fecc6ed2a5ef653769527fb313b4a9bfb9061654cfec3eeb2a5ef653759533fb0ebaca97bf945d654bdeca6cb2a6fba5d829537db2ec14a9bee9660a54df6cb3052a6fbdd9829537dcecc14a9bed9560a54df7bab052a6fb5d5829537decac14a93fd97e1954d7fc350caa5fe642865527ff2ec32a93ff9561954dbfcab0caa6fee41865535ff0cc32a97ef9261954bfdc830caa4ffa60865535fb0c432a97f591219549ff4c4ecaa4ff66276552efb2b3b2a97f5919d9549ff4c2ecaa4ff661765527f930bb2a99ff87dd154bbecaee8aa5fe64374552f7d313a2a97bd979d154f9f32ce8aa7cfe5574553e792aba2a9f3e655d154f9eb2ae8aa5dfe55745535ff0db22a977d95d91549fecc2c8aa6bfe1964552eff2ab22a9bfb96e0154dfd4b700aa6fe65b805537f12dc02a9bfa76e0154dfcbb700aa6fedd3805537f2e9c02a9bfb64e0154dfcb2700aa6fee1b805537f50dc02a9bf986e0154dfc43700aa7ee9d380553f72e9c02a93ff97618549fecc4ec2a6bf61a76152feb233b0a93ff985d8549fecc2ec2a6bf61976152fbf26bb0a93fd981d854def4b3062a6f7659831537bcecc18a9bdd7660c54dee3b3062a4fee41859927f720c2ca93fb9061954 else (if j<2 then 0xae2270fb871c32e16709b841c1ae0a703b811c02dfe6fdb7e1beadf26f7b7b1bd2de66f1b781bbadda6ebb751ba2dce6e5b721b8adc26dfb6f1b72db66d9b6c1b5adaa6d3b691b42d9e6cdb661b2ad926c7b631b12d866c1b601afad7a6bbb5d1ae2d6e6b5b5a1acad626afb571ab2d566a9b541a9ad4a6a3b511a82d3e69db4e1a6ad32697b4b1a52d26691b481a3ad1a68bb451a22d0e685b421a0ad0267fb3f19f2cf6679b3c19dacea673b3919c2cde66db3619aacd2667b331992cc6661b30197acba65bb2d1962cae655b2a194aca264fb271932c96649b24191ac8a643b211902c7e63db1e18eac72637b1b18d2c66631b1818bac5a62bb151894c4061430417f0be3deb2eeb73eb91db96d7968cb27585ebc15a9ab954d29ed4bfa40d10e80b3c79c4cd4a6372e4956c9da47f20f8efc6a22f1148888c36a147073821c031faaf977b03c89dc8ead737b8c5be6dca6d435c5a74cfc6743319964c7b62230197d6bad5b7ad19610aca54d29e1474a0a4e9a6392ca92e47f233913c86e418201cfd87b53c29d54e586e735b9a00c926122ed9690acc52f27c130493046f2188fe878638c1aa8c5c5b229b13588b43ec1b80c085282180ce048018006e000dff4ab0d326ff255869937ff2ec2cc9bfe9761664dfecbb0b326ff25d859937fb2cc2cc97fd969d664dfec34eb326ffe5f855937fd2fc2ac9bfd97e1564dfe4bf0ab25ff65f855937ff0fc2ac97fd97a1564dffc3d0ab26ffa1e85593eff0b42ac97ff9761564dffc3b0ab26ffa1d855937fb0ec2ac9f7f8561564fdfca30ab27fee4185592ffd3042ac97fd9721564dffc390ab26ffa1c855937fb0e42ac9bfc8721564fbec290ab25ffa6275592ffb313aac9bff879d564bfeca4eab25ffa61755937fd30baac9bfd985d564dfe4c2eab25ffe51755937ff2ec28c9bfe9761464dfecbb0a326ff25d85192ffb2f3a8c9bfd879d464dffcc2ea326ff661751937fb0aba8c9bff9661e54dff4b30f2a6ff659879537f92cc3ca9bfd9561e54dffcbb0d2a6ffa5d869537fb2ec34a9bfc9761a54dffcab0d2a6ff65586952ffb2bbb4a97fd959da54dff4b30b2a6ff259859537fcecc2ca97fd96dd654dfec36eb2a6ff61d75952fff2cbaca9bfd865d654fdfca2eb2a6ff61f659537ff2fc32a9bfe97e1954dfecbf0caa6ff25f865537fb2bc32a9bfd94e1954bfecbf0caa6ffe1f86552ffb2f432a9bff87a1954dff43d0caa7bfe1a865537ff2ec32a9bfe9761954dfecbb0caa6ff25d865537ff2ac32a97ff9761954dffc3b0caa6ffa1d865537fb0ec32a9bff8661954f7fc330caa7dfe5586553f7f28c32a9fef9261954ffdc830caa5ffa6086552ffb2e432a9bff8721954dff4390caa6ff61c865537f90e432a9efd8621954bff4c4ecaa5ff662765537ff0f3b2a97fd959d954bf else 0x27802670020bcf970e3106ccc39f1e51060bcf971e0906e7cb8f00a2f3e25432b9b231e7cb80f5736461cf9711caf2e0186081f9f1e5c0a901f9f1e5c050c139f2e3c060e18284e7cb8f021bc689cb873e23c689cf8f2e0dc76f1a273e5c780f1a273e5c78371c3056fcb873e3108ae1b970e7c521521372e1cf8a4aa3874c93970e7c4a915d355e7cb8f048457aa99273e5c781056ba6e7cb8f0484174dcf971e0552105caf3e5c78661dac6e7c79486e3b78dcb9f190d476f19af3e5c640ede373e5c64351c305e3c39c4e4386e1cf97188304e7c78722e307e6178f0e4907e1cf9714858661179f2e31068a129f1e5c0b8e1e2f3e5c38a41cbf3e2939708a3f38bcb8f048306e7c7970483364bc79f016dc76ed92f1e1cc58edd2d2e7c780b6c4376c97871e62c76c945f089cf8b721ba589c25f3e2d886ed85f3e3c050e2db2589cf8f06e40b6eda273e3c12902dba5e3139f06c473e41b8f0179712dc04cb93996e5c580e18284e7cb8f01c3040fcf8f2e0948e5c02e7c5872139700ab65c9cd971e03d6cb939f2e2c070a103f3e3c391623916e01b13d972732dcb81014207e7c39712c407e7cb8f0142f34a18272e3c088e7b2e4e65b97020284e5c39f11b9f2e3c040e18284e7cb87122223e5c3897192f32fcb8f08838f139b9a92fcb8c424284e5c780a102f3e5c0bf11f9f2e1c52c4192c4e7cb8711b944e7c78251a272e7c38a5192c40a139f2e3c084bcb8f0882f1e05834bcf896e1ca20f103f3e3cb80c5b9f2e3c220c97971e11054b41bb649979f2e24b7e7cb8906c3656edb9f1e54076fcf92549c5b0edd2a4e7cb8b61d2a46edb971e63b649c92f3e2dc7a0ddb25e5cd27121ba549cf9716c3b76c979f2e29076e412a4e7c790edf9f2e2d851adf9f1e42b720979f249c5b1095bf3a1cb8a41dbd0e7c9225e23868bcf970e31070bcf97049c4b0e1780749cf9712c40e8f979702dcf2101c325e1cf9714842549c39f2e2316e01d2f2e3cd2111e365e5c78641cba5e7cb8f02c9086fc22f2e231b0eddb45e3c390c1c63789c22f2e2d8818ddb708b13971206378b13971e0d88cd579f2e31068bcf971882d6cb91873e5c47e8e745ba21d0ae8273fb9f1cf2e76739b9c1cdae6a733b991cc2e5e72db961caae52727b931c92e46721b901c7ae3a71bb8d1c62e2e715b8a1c4))
def g503H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x25301c5725a0b2e0000000e064c071e3770000442532caf50481a886dd206cb174b6e5512fa0b6492a08e0a05291c1101b00009118a35e31d191b39189045ac1e1609d80e7d5d3d17b2291007b815b7ab731e858115aba1a29a03022ac03c7232ee0b3c3a6503b411b2130c16ba1d894ce30aea058b1ac00b4b3253166b085318ea14584f2902371934181605de0921157602a30496cce0000f075e02ea06d318ca1aa7f051f3ca0784039b52ab1b684de8149712cc1a0f107f2da5155709f800cf173ff07d14692d5e2d9e1365b036194d262dadd80476177618340244b9641986069c1bbc4f180414dae815f9a2771bdd7e0711304519d0653026f06c2978026016daf2ff1d6c411410a000030a9107ac11595be50c40000c0a2a0b81080c2667312012da8d04299b01190af92d0a12ad090518d90760000c06f130590251040ad0500003826908c0a240079b01a40677019e2f271474f3d3253dd9e7108c19b699938e474df85b8802c885a745cd1705917df3041b9a14248ce71ba000080b74311ef357159407292e88bce91c5032b5195b03ef1de000ff097dbcd30420000e1e20000b0e85063a095f0ec0b5db11fd0ead169f73d0000114fe3a290c5929bc14051a2c0f8a101f1880043f0eb4156d06b46e6d16fb102db26d19c9162a1e4a0ee9185e0ca9055711af1b23adee14a71750000a00bf164f2e500006b60c18bd0f444f070e9f15d51af913f042651a450a79161c08f605ad301e2e9f2d8a3ca0000c825000062f928eb0000d151403560a371da9ad4b002d070a01445b4904d58de12e6a0320000213a2b5629765ecc407f0000a086a290817c927f0000206e311e000098f9291fb28901ec6b245152210f93a4000d48dfc09ca093d2ee60d3a2548158e15cf08e602730c29028005060a6c192c0c6f34e20e43190b0821919b0c322940000b5cce09af034c0d4523ae1d2fc67808dc178bcdcf091d18f03a121a5e3a3700174cd8006f04e94f360d024236036304c8bd0000014e3812b715430338124625a000001bf0000f10bf07e0000119627ce41538126b03ae91a813d412e5326100ed1ddad76d1cfac4aa1a9b821a0c0cb25a15a50bedf3b3d2a603f0000d04f32c80000b03dfad2813e705bb0680140103c0e0180008808098181893009834178ea124110d0bb0300934809398020d91606c3602428128150987206419024060ac110180601c03004070040313c02464000700e014bb06c060100e010008440c1e831060120fc1e0000c038010486d000021fc04000030ac2e0080b014690d4000000004008008000201b020260300201808000070041a0340005405044020180102800038200046c13c4e0880107017014070bc2d03c0a108051a801070370181426c010007e00c3b0040500c4a000020d00c038280180001002 else 0x74e113cb702b4045e127703720773f2961e3c061013bc1bc508bb114fbcf813170f55182b1db013800002293f723817ef6bba11c01193084000011c4cbd16b2250659ab9d128e133913c05b930380148a06af02900001010b16ce1e5e00a81e6c012000054ec2013b0aa005910c1905c107381b400dfc923b17d6179c04b41764c11831ed1b5205ed184a6e7a1c890a83144d277e25701c042b246dcb34d019a5018834ca1106b0430fd1088771a51c391806100000000e541b8b0a470cf74cbc0a5e1b791d070626776810591c6c5765116c03114f8b0ed28dc81eb0272b10ca0fb30bb82bf60178db470078009aacf9918c3a51094d22e302210577165bb58d005000050bd000021c200000000d0a1a3990000a17f15c10000b9b40000a0fc10c94ecd000091e7000080ab9098f12040f6c0ef114b81eacb2b446240ac10f720d656c6e10d201d518a000000000000b01fe91ce4d032c7910e901eaf323099000491211046c1dc807d116721c92087f0d1d5c9f083819f72e3a22d41a311e971cee02f0000c4ed7241e11d4abb0000d2489ac2109e700300002509b1b0f5d430bf018771a791d7000090fad6ded172716330568186108a0191a07c2f340000d2e7503c609b7e24d242a1d530b081b1814310e633038125b17130d5a02d51a1b1cdb1eda05fa0d7e132d0b13060e16eb24e60adc26f917a3109072600fe0000f197001514eb01686fab533900bc15d930ff608131602117000044e20000d45d902000009a2880cefca20000a150000071990000799c4137e45b0096e0b5e4f63a0fbedb0000000036da57dff02180744016b0a03044000041ad52f0316a53277141619de72b000860899c)
def g503D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5e6c32c73564206117566933cb1c0a5e6932c33c55217995933c72c085c6126933cb1c152979a4cb0cf15485d5926cf2c702171e6cb0cf1564247157564cf2c7098a5e6cf2c70564216973c31c979085e5cf0cb15a4226585cf0cb15e42665d61f3c7017290a9d7173c72c16909117156973932c70297964cf2c705885d6964cf1cb0217144964cf2c7058a157964cf2c705895d6925cf0cb12169a5173132c705ca5e65a51c5cf2c7010b5e7945cf2c701162a75d6946173cb1c042d7930cb3c655881c65d6c24cb1ce5297972c73c169081c5106cf2c70207566cf1cb01081841d59a4cf1cb0287546cf2c70108197973cb1c042075a5cf1c321081c6105cf2c702051075a5933c72c0a1d6964cf1cb02255c4cf2c311c71445e5cf2c31250964cf2c461d6173cb1c04206105cf2c701c6133cb1c061b3cb12052e5133c70190964cf2c46305132c701a88277a6a25ca4c23ea31222211a041f69e91da1c99ba9aa19c98f17e96f96215193f92f11d10f8ff0f18e40d68c60b88ab09d89007f87206605704c83f03302881f81500a8003ff9d664fff85593ffa1564ffd85593ff21564ffe75593ff5d564ffe75193ff5d464ffc75193ffdda54ffe76953ffdd654ffd75953ffd9654fff86553ffa1954ffd86553ff21954ffe76553ff5d954fff74553ff5d154fff64553ff59154ffe76153ff5d854ffc76152ff61a64bfd85992ffe1564bfd85192ff61e54bfd86952ff61654bff86552ff61954fbe74553ef5d154ffb80552ff61854b7e85192df61464bf980192fb60a54bfb80552f760c54
def g503H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x85a548a8c0003815d001098eb69c600162c7dbbd5830172d40002449200f000000002e298000251030a4e148f8473e29de2a2c487424640040001e16800013be000024ab000014c2400030af40003414883b80002c96800003b230333a8f840630ab74291845800018175e0aab0cd2301437d90a52a6e830c000101ab82af797400020158000041800000089800031466546f03288496ca280001509b730c00025a8f8816508f997980880001001c5cc00003b3e772780000000000000000c30548440000392400000000000000000003ebefc1d3909c0002081fc4d05afbcc4adba13b1e433a02b6c09000000276c863d45084bac2640002047400e5147602300a54c0cb0881005c00000000809dc2340003cb69a8f743480003835a83ed42ca8308ca2c00032800402b814604b400008b4288b0c1b0813a22f4149c84d40cbcc118c1f3c1d400033ad852c45044820c00025066bb08000204c8433c000241b4c48b829c000142db4a3e44be6c7bb16a10a1a969126743ea40ab10a9e9c18366882800d8823cc12f80aec46d1416c4668a13c85002fdc1afe8930084409840c60bdc0000041802a00001403a0bcba2a938d8447c000154d80001c0c00001431783b0aad283bf8c42416c819000036885ca4a039883a6018842d7b3080002031aa3c8000041db80090b25426000000000c2d342dc0000c3600000000041a400000003142142480002820362b880fe81a1088f83694a9c0002497b005b2c4c000104540000c0400001c8bdc8540000000000038321442800000002d4bdd16c0003844a8ad5c25a0242420581980002c077028e80b4c37bb835c38f440b046000008c3fccc1807fcb090c4c000000000003e88aa970000040e800000ad00000c21aa0a4000283e4487fc2f282e22a5883a14a7101548c3800039c3a802cc048a0a282f7885c000171e892a8c1e3c1e8449c0000c2e7a09f84c2c4db80200000000043f400030294000231dc000343cc000314df83abc270c1c400014a780000caec000003d0f8d6c3830848b96f012404b30167440344804b4ad0adc438cb0638d300cc0000c34d0122811400000000008f9a72b1fc0003439c023800000000000000005489ca27026c846800000000000331580000ca900000c2218b6e312981944a1d62a40387c1dfc32c0000000001cd0334843720b800ee40a2c225021d2bba8371c44012270c0807e0408824280e058802eb90105cc207118ccc7360715806260880c5c1d00024100b00800c815458740c5d030ec000104128020b0081804090c8280a0b0002c2e050307c000017800060c00818021b039d01608018780c6611014080d130180612000087a0c0087800020600c1c0906874000a0780014060180436040600c0800000041007000000c010000c7a03020000c01001d8107e else 0x2435c08180003527b03fb8133841582cd2146425c412b417aca3a5a4e927f5968546ac24fc4ce80a58064020acbd8293ec0810412c1fbd2b00002413c8a1ada9a81fdc2bf89b742b23025c3d403e3018fc3d8c07bc3c2444c838b916a028689b341e740f68a340003416340440169c1f60a20697b0a316149c444a0bd01bd4025c22b52c804dfb06ce14343c4085ac3c88327ca9988c2884ec43d52ad921902c2d2a14aaac0ba803c4b3980f9c8a00002049a209a68eac14e6c398940806e44523a9401124250022f82a5c9ec52a489454394d29ac4aa8b3f041e7a79ba7e52bb80334bd6834182b9918143ddc3f30255427d81ed80738b92aa53804fc28908684478c0df82ab52c141536a560a672a860135e2fb9190011f42c7c45f42eec31c0003a917c2f944071bc50002800dc29aeb6188654c44f319414000d7c4230872006aaa5e92be7968b3d1c19f04a38104440cea7388744bbc00034216c1854a76f00c000044c50035417c80b0eaf9b31400e340d3a3bf83b5810f529f843033c6835000018019c36c0002c1b8826942780003c37682e809fb03110173a96c0000000000000002c0500000835604a6c48e8281c1c900540000c425c42c0390000000020a4148e80000000300be7ad49174c09604afc1c1ca1492d3c87b4100000283fccaf3f310021012d8ea98c3adc34501)
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe5346139108394c49ca3020e534e518108398b38c24420e6292728c08398b28c264239ae22970b803ff327fd64ff8c9ff953feaa7fc54
def g503H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c590004814000000000000000000070b20740000000000001c1c00000000070b000080d6928bb762660e6036d20c61f058001808000e2e689c001020641903000000068c8000001e11000415bc962ac6eb10ac8288060000000000000210c8947876847168000000000000716eaac000000506754e000814d75c0010240000000821d57b155923000012d0530a28afeab80b81183450074117a160aaa5da34e68542686680c3aa9c3f794a2f1823436000870d2286425435eab827512000b48807800000072f800000000000002b705c4491018002d5cb22854d23e01e00000010b182a000201419dc460000002a5800000068504d02308c1035d30008890411cb281000
def g503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404ff
def g503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x431c062f8492f8000f034a003915307a0000000382003ea0c89d0152d000100027183400000019134b76800000f601
def g503L : Nat → Packing
  | 7 => (13,5,4,0,0,7,0,g503D7)
  | 8 => (494,4,4,0,0,12,0,g503D8)
  | 9 => (312,3,4,0,0,13,0,g503D9)
  | 10 => (47,2,4,0,0,12,0,g503D10)
  | 11 => (6,1,4,0,0,8,0,g503D11)
  | 12 => (1,0,4,0,0,0,0,g503D12)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 83 2 11 4 3 g503H8
  | 9 => lookupWord 164 719 10 16 9 3 g503H9
  | 10 => lookupWord 138 683 9 16 9 3 g503H10
  | 11 => lookupWord 24 149 6 13 6 3 g503H11
  | 12 => lookupWord 6 37 3 10 3 3 g503H12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : CutRow g503 7 0 13 := shortcutBlock (data:=fun _ => 0x40012150cc4216310220122114aa165048052150cc4257200c4241b0d0e4651020809078260906320220184406221600c042c0e0f4062722400101c0e472173040816130dc4a1520846082c960e62201800102a158ac1740c1201a4d0e9e076040816130dc42152) (by decide +kernel)
theorem g503B7 : CutRow g503 7 0 13 := g503P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : CutRow g503 8 0 44 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_44 : CutRow g503 8 44 96 := shortcutBlock (data:=fun _ => 0x8460c0e870662300800112094c841740800112094c841740486040b050a64410800112294c841640846080c8606623008460c0e8706623008460c0e870662300846080c86066230040012110cc421730846080e86066230040012110cc421730800112094c8417408460c0e8706623008460c0e870662300846080c8606623008460c0e87066230040812130cc4a16308460c0e8706623008460c0e870662300486040b050a644108460c0e8706628008460c0e8706622008460c0e870662301020528151a085840846080c86066230040012110cc421730846080c8606623008460c0e8706623000a8129348ac85400c0c029348e4e04300e8329348ac8740040012110cc421730846080c860662300846080c86066230040012110cc421731021182c570a918404860c0f070a644100a8128340a8854100a8130380c8854100a8128340a8854100a8128340a885410228182e162a91320800112094c8416300a8128340a8854100a8128340a8854100a8128340a8854100a8128340a8854100a8128340a885410c1201a4d0e9608300a8128340a8853108420121104c22700228182e162a913218060291c9a4e07300e8329348ac873004860c0f070a64410800112094c8416400a8128340a8854100e8329348ac87400846080e860662300a0c09068260d04208460c0e870662300486040b050a64410408160305c021630a0c09068260d0420243080c86063231002206038182214000220603818221400022060381822140002206038182214000220211888621300400280c0e42227302230291c8a6313000220603818221400022060381822140022306038182313000220603818221400022060381822140002206038182214002230291c8a6313002230603818231300223060381823130022306038182313000220291c8a6213002230291c8a6313000220291c8a6213000220291c8a6213000220291c8a6213000220291c8a6213000220291c8a6213002230291c8a6313000220291c8a6213002230291c8a6313000220291c8a6213000220291c8a6213000220291c8a62130) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_140 : CutRow g503 8 140 96 := shortcutBlock (data:=fun _ => 0x18060291c9a4e0741818041e0d87e0650084040b050a446208420121104c227102080826122890731024028240a241500c0c029348e4e0860084040b050a44720846080c8606624100240184c062418000240184c06241800084040b050a44720084040b050a447208420121104c22410c1201a4d0e9e0870846080c8606624110010824530890850846080c860662410846080c86066241040012110cc42183084608068204624102080826122890730042080c860622610a0c09269268d04208460806820462411000428151a084850a0c09068260d0430846080c8606624108460c068304623000220211888621400a0c08261228d053100108245308908500c8229348ac865100220603818221400846080c860662410486040b050a64520800112094c8418408460826120c62610800112094c841840486040b050a64520088029348ac847108460c068304624102080826122890730208082612289073008404028108446208460c068304624108460c0683046241002401028042418008460c06830462410042080c860622711000428151a0848500a8128340a885510a0c09068260d053002401028042418000840c06830844620846080c860662300846080c860662300846080c86066230040012110cc421730846080c86066230040012110cc421730800112094c841740846080c860662300846080c860662300846080c860662300846080c860662300846080c860662300486040b050a64410846082c960e6220040012110cc421730846080c860662300846080c860662300846080c86066230040012110cc42173040012110cc421730800112094c84174040012110cc421730846080c860662300846080c86066230040012110cc42173040012110cc421730486040b050a64410486040b050a6441040012110cc42173040012110cc421630846080c860662300846080c860662300486040b050a64410800112494c841640800112094c841740800112094c841640800112094c841640846080c86066230040012110cc421730846080e8606623008460c0e87066230) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_236 : CutRow g503 8 236 96 := shortcutBlock (data:=fun _ => 0x10220122104a214010220122104a214010220122104a21400042080c8606224110220122104a218010220122104a2130040811209508218300642121904a43400c04280c0e42627300220211888621300c04280c0e426273002202118886213000c4241b0d0e466100c4241b0d0e466100840c070308445200840c07030844720042080c860622710486040b050a64410846080c860662410846080c860662410042080c8606226108420121104c22710042080c8606227100840c070308447200642121904a434000642121904a43400c04280c0e42627300c4241b0d0e466100c4241b0d0e46610846080c860662410a47080c8606723100220211888621400846080c860662810846080c860662300a0c08261228d05304860c07030864520486040b050a645208460c06830462410486040b050a64520486040b050a645208460c068304624100a2421188862530040012110cc4218304860416090c647202080907826090530088028340a884620846080c86066230040012110cc4217308460c0e8706623008460c0e870662300088028340a884410088030380c884410088030380c8844108420121104c22710846080c8606628120220184406221600084040b050a446200c8228340a8864100a8128340a885410a0c09068260d04300a8128340a8854100840c06830844621000428151a0848400a8128340a885410088029348ac84410486040b050a64420486040b050a644218060291c9a4e07400c8229348ac86410022021188862170002202118886217018060291c9a4e08500a8128340a88541020808261228904318060291c9a4e07400a8128340a885411000428151a0848400a8128340a885410088029348ac84410084040b050a44620088028340a884420084040b050a446200a8128340a885410084040b050a446208420121104c227108420121104c2261202201844062215008420121104c227104860602818864421002082c970aa0753012082c970ba06500a8128340a885410084040b050a4462020808261228904302080826122890432022018440622150) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_332 : CutRow g503 8 332 96 := shortcutBlock (data:=fun _ => 0x42080c8606227108460c068304624108460806820462410a0c09068260d05308460c06830462410c0c029348e4e054040012110cc42173040012110cc42173040012110cc42173040012110cc42173040012110cc42173002401058042415000240105804241500285040b050a54420084040b050a444200c4241b0d0e463108460c06830462410046080502046241002609058242614000220205008221800042080c86062271008404038108444200a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a2421188862530048052110cc4258200a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a24211888625300846080c860662410846080c860662410c04280c0e42628308460c0e870662300846080682046241040012110cc421730846080c86066230040012110cc4217300a8130380c8854100a8130380c885410846080c86066230040012110cc421730846080c86066230040012110cc421730846080c860662300846080c860662300486040b050a64410846080c86066230040012110cc421730846080c86066230040012110cc4217308460c0e8706623008460c068304623008460c068304623008460c068304622008460c0e8706623008460c068304624108460c06830462710846082c960e623100a24211888625300846082c960e623108460c068304623100c2482c960e266108460c06830462310846080c86066230040012110cc421730846080c8606623008460c068304623000a8130380c8854100a8130380c8854108460c0683046230040012110cc421830400280c0e422283040012110cc42183) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_428 : CutRow g503 8 428 66 := shortcutBlock (data:=fun _ => 0x8460c06830462410846080c86066230040012110cc421730846080c86066230040012110cc421730846080c860662300846080c860662300846080c86066230040012110cc421730846080c86066230040012110cc4217308460c0e8706623008460c0e870662300042080c860622710800440a15824484002606038182614004002c060b40227300642121904a4340002202118886213000642121904a434008460c06830462300800112094c84174040012110cc421730800112094c841740486040b050a64410400160305c021830400280c0e42228308420121104c22410042080c8606224108420121104c228108420121104c22300042080c8606227108460c06830462300846080c860662410486040b050a64520800112094c84184002409058242418000220603818221400486040b050a6452002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140040012110cc4218300240121904a414010220122104a2170040012110cc4217300240925924a414000240925924a414000420c068304227100420c06830422710084040b050a4442) (by decide +kernel)
theorem g503B8 : CutRow g503 8 0 494 := (@joinRow g503 8 0 236 258 (@joinRow g503 8 0 44 192 g503P8_0 (@joinRow g503 8 44 96 96 g503P8_44 g503P8_140)) (@joinRow g503 8 236 96 162 g503P8_236 (@joinRow g503 8 332 96 66 g503P8_332 g503P8_428)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : CutRow g503 9 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_3 : CutRow g503 9 3 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_99 : CutRow g503 9 99 20 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_119 : CutRow g503 9 119 3 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_122 : CutRow g503 9 122 96 := shortcutBlock (data:=fun _ => 0x8460c068304624108460c068304624102080826122890830a0c09068260d0530a0c09068260d0530a0c09068260d0520a0c09068260d052020808261228906302080826122890630846080c8606624100220211888621400846080c860662410022021188862140020808261228909302080826122890630a0c08261228d0630846080c860662410a0c08261228d06300500184c065027102080826122890630846080c860662410846080c86066241002202118886214006120416092530730088028340a8846206120416092530730486040b050a64520486040b050a64520088028340a884620088028340a884520088028340a8845202080826122890530a0c09068260d0530a0c09068260d05302080826122890533012082c970ba0753012082c970ba07518060291c9a4e0850088028340a8845202080826122890530a0c09068260d0530a0c09068260d05302080826122890530088028340a884520088028340a8845218060291c9a4e0850486040b050a64520088028340a884620084040b050a44720084040b050a44720208082612289053240601a1d26960962098030380c984620846080c860662410846080c8606624102080826122890830a0c09068260d0630c1201a4d0e960642098030380c98462061204160925307304860c070308645204860c07030864520486040b050a645202080826122890830486040b050a645202080826122890830a0c09068260d06300500184c06502610a0c09068260d06300500184c065026100500184c065026100500184c06502610c1201a4d0e960640228182e162a91520a0c09068260d0520a0c09068260d0520228182e162a91520228182e162a91520a0c09068260d0520a0c09068260d0520228182e162a915200701184c065036000a8128340a8855100a8128340a8855100701184c065036000701184c065036000220603818221400022060381822140002206038182214000220603818221400042080c860622410042080c860622410022021188862140002206038182214000220603818221400243080c86063231) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_218 : CutRow g503 9 218 94 := shortcutBlock (data:=fun _ => 0x486040b050a645200500184c065027108460c068304624108460c068304624108460c068304624108460c068304624108460c0683046241102c09058242c15000500184c065027108460c068304624108460c068304624108460c068304624108460c068304624100240905824241500810001c0c8740750486040b050a64520486040b050a645200220603818221400486040b050a64920486040b050a64520486040b050a645208460c06830462410486040b050a64520486040b050a64920486040b050a64420486040b050a644100500184c065027100240905824241500408082e164aa06400220603818221400408082e164aa06400220603818221400486040b050a648200240905824241500486040b050a64520408082e164aa06404860c070308645200240905824241500846080c860662410846080c86066241002206038182214004860c070308645200220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000240905824241500024090582424150002409058242415000240905824241500846080c860662410084040b050a44520084040b050a44520084040b050a44520084040b050a445208460c068304624108460c06830462410088028340a884620a0c08261228d0630a0c09068260d063020808261228906300500184c06502710084040b050a44520084040b050a44520846080c860662410810041e0d87407508460c06830462410088028340a88452002409058242415008460c068304624108460c068304624108460c068304624108460c068304624108460c06830462410486040b050a6452020808261228906308460c06830462410a0c08261228d0630846080c860662410022021188862140020808261228908308460c068304624108460c068304624108460c068304624108460c068304624108460c06830462410a0c08261228d06308460c06830462410486040b050a6452) (by decide +kernel)
theorem g503B9 : CutRow g503 9 0 312 := (@joinRow g503 9 0 119 193 (@joinRow g503 9 0 3 116 g503P9_0 (@joinRow g503 9 3 96 20 g503P9_3 g503P9_99)) (@joinRow g503 9 119 3 190 g503P9_119 (@joinRow g503 9 122 96 94 g503P9_122 g503P9_218)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : CutRow g503 10 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_6 : CutRow g503 10 6 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_19 : CutRow g503 10 19 28 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : CutRow g503 10 0 47 := (@joinRow g503 10 0 6 41 g503P10_0 (@joinRow g503 10 6 13 28 g503P10_6 g503P10_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : CutRow g503 11 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : CutRow g503 11 0 6 := g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P12_0 : CutRow g503 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B12 : CutRow g503 12 0 1 := g503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : mixedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g503 0 0)
  · exact (mixedEmpty g503 1 0)
  · exact (mixedEmpty g503 2 0)
  · exact (mixedEmpty g503 3 0)
  · exact (mixedEmpty g503 4 0)
  · exact (mixedEmpty g503 5 0)
  · exact (mixedEmpty g503 6 0)
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
  · exact g503B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore KS487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS503 : Lower true (varsX 503) (graphGoal 503) 13 := lowerMixed (g:=g503) (i:=0) (hints:=4832298581) (before_sound KS487 VS487) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS503 := extendKnown KS487 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS503 : Known true KS503 := extend_ok (m:=503) VS487 lowS503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0)]
def g511C : List ColumnInfo := [(8,0,503,0,13)]
def g511A : List (List Nat) := [[],[16,66,134],[32,65,117],[64,33,117,134]]
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ff
def g511L : Nat → Packing
  | 13 => (1,0,1,0,0,0,0,g511D13)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,13,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
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
  · exact (rfl : block g511 9 0 0 = true)
  · exact (rfl : block g511 10 0 0 = true)
  · exact (rfl : block g511 11 0 0 = true)
  · exact (rfl : block g511 12 0 0 = true)
  · exact g511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore KS503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound KS503 VS503) g511G g511T (by decide) (by decide +kernel)
def mo328Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x33cf3cf3cf3cf3cf,0x1145145145145145),(0x0,0x0),(0x0,0x0),(0x3cf3cf3cf3cf3cf3,0x2492492492492492),(0x0,0x0),(0xf3cf3cf3cf3cf3c,0xa28a28a28a28a28)]
def mo328C : List ColumnInfo := []
def mo328A : List (List Nat) := [[],[134],[99],[99,131],[131,99],[131]]
def mo328D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def mo328L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,mo328D3)
  | _ => emptyPacking
def mo328I (_ _ : Nat) : Option (Nat × Nat) := none
def mo328 : Forest := ⟨1352,3,fun i => mo328Y[i]?.getD (0,0),mo328C,mo328A,mo328L,mo328I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328P3_0 : block mo328 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo328B3 : block mo328 3 0 1=true := mo328P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328T : checkedTables mo328 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo328 0 0 0 = true)
  · exact (rfl : block mo328 1 0 0 = true)
  · exact (rfl : block mo328 2 0 0 = true)
  · exact mo328B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328G : graphValid mo328 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM328 : Lower false (varsX 328) (graphGoal 328) 4 := lower_forest (g:=mo328) (i:=0) (hints:=12935258112) (before_sound [] (known_down baseKnown)) mo328G mo328T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM328 := extendKnown [] 4 [(328,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM328 : Known false KM328 := extend_ok (m:=328) (known_down baseKnown) lowM328 (by decide +kernel)
theorem lowM99 : Lower false (varsX 99) (graphGoal 99) 4 := lower_down lowS99
def KM99 := extendKnown KM328 4 [(105,[49,33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(204,[32,49,101,117]),(228,[32,81,49,67,116]),(298,[16,48,32,133,101,118]),(353,[96,81,33,50,67,64,132,116]),(418,[16,112,32,50,67,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM99 : Known false KM99 := extend_ok (m:=99) VM328 lowM99 (by decide +kernel)
def mo329Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo329C : List ColumnInfo := [(1,0,328,0,4)]
def mo329A : List (List Nat) := [[],[131]]
def mo329D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo329L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo329D4)
  | _ => emptyPacking
def mo329I (_ _ : Nat) : Option (Nat × Nat) := none
def mo329 : Forest := ⟨1353,4,fun i => mo329Y[i]?.getD (0,0),mo329C,mo329A,mo329L,mo329I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329P4_0 : block mo329 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo329B4 : block mo329 4 0 1=true := mo329P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329T : checkedTables mo329 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo329 0 0 0 = true)
  · exact (rfl : block mo329 1 0 0 = true)
  · exact (rfl : block mo329 2 0 0 = true)
  · exact (rfl : block mo329 3 0 0 = true)
  · exact mo329B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329G : graphValid mo329 (boundsBefore KM99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM329 : Lower false (varsX 329) (graphGoal 329) 5 := lower_forest (g:=mo329) (i:=0) (hints:=12884926470) (before_sound KM99 VM99) mo329G mo329T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM329 := extendKnown KM99 5 [(329,[]),(330,[16,134]),(332,[32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM329 : Known false KM329 := extend_ok (m:=329) VM99 lowM329 (by decide +kernel)
theorem lowM103 : Lower false (varsX 103) (graphGoal 103) 5 := lower_down lowS103
def KM103 := extendKnown KM329 5 [(230,[112,98,48,67]),(236,[32,49,80,16,65,100,116]),(299,[16,50,134,118]),(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM103 : Known false KM103 := extend_ok (m:=103) VM329 lowM103 (by decide +kernel)
theorem lowM229 : Lower false (varsX 229) (graphGoal 229) 7 := lower_down lowS229
def KM229 := extendKnown KM103 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM229 : Known false KM229 := extend_ok (m:=229) VM103 lowM229 (by decide +kernel)
def mo331Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo331C : List ColumnInfo := [(1,0,330,0,5)]
def mo331A : List (List Nat) := [[],[16,134]]
def mo331D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo331L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo331D5)
  | _ => emptyPacking
def mo331I (_ _ : Nat) : Option (Nat × Nat) := none
def mo331 : Forest := ⟨1355,5,fun i => mo331Y[i]?.getD (0,0),mo331C,mo331A,mo331L,mo331I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331P5_0 : block mo331 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo331B5 : block mo331 5 0 1=true := mo331P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331T : checkedTables mo331 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo331 0 0 0 = true)
  · exact (rfl : block mo331 1 0 0 = true)
  · exact (rfl : block mo331 2 0 0 = true)
  · exact (rfl : block mo331 3 0 0 = true)
  · exact (rfl : block mo331 4 0 0 = true)
  · exact mo331B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331G : graphValid mo331 (boundsBefore KM229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM331 : Lower false (varsX 331) (graphGoal 331) 6 := lower_forest (g:=mo331) (i:=0) (hints:=4294992006) (before_sound KM229 VM229) mo331G mo331T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM331 := extendKnown KM229 6 [(331,[]),(334,[16,32,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM331 : Known false KM331 := extend_ok (m:=331) VM229 lowM331 (by decide +kernel)
def mo333Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo333C : List ColumnInfo := [(1,0,332,0,5)]
def mo333A : List (List Nat) := [[],[131],[32],[32,131]]
def mo333D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo333L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo333D5)
  | _ => emptyPacking
def mo333I (_ _ : Nat) : Option (Nat × Nat) := none
def mo333 : Forest := ⟨1357,5,fun i => mo333Y[i]?.getD (0,0),mo333C,mo333A,mo333L,mo333I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333P5_0 : block mo333 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo333B5 : block mo333 5 0 1=true := mo333P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333T : checkedTables mo333 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo333 0 0 0 = true)
  · exact (rfl : block mo333 1 0 0 = true)
  · exact (rfl : block mo333 2 0 0 = true)
  · exact (rfl : block mo333 3 0 0 = true)
  · exact (rfl : block mo333 4 0 0 = true)
  · exact mo333B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333G : graphValid mo333 (boundsBefore KM331) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM333 : Lower false (varsX 333) (graphGoal 333) 6 := lower_forest (g:=mo333) (i:=0) (hints:=12884928006) (before_sound KM331 VM331) mo333G mo333T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM333 := extendKnown KM331 6 [(333,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM333 : Known false KM333 := extend_ok (m:=333) VM331 lowM333 (by decide +kernel)
def mo361Y : Array (Bits × Bits) := #[(0x3c1e0f0783c1e0f,0x190c86432190c864),(0x0,0x0),(0x0,0x0),(0x1c0e070381c0e070,0x944a25128944a25),(0x0,0x0),(0xc06030180c0603,0x26f379bcde6f379b),(0x273399cce673399c,0x26130984c2613098),(0x0,0x0),(0x383c1e0f0783c1e0,0x10a8542a150a8542)]
def mo361C : List ColumnInfo := [(32,0,329,0,5),(1,32,328,0,4),(8,0,353,0,4),(256,0,105,0,4)]
def mo361A : List (List Nat) := [[],[131]]
def mo361D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30fd41fd31
def mo361D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7089f
def mo361H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4002a
def mo361L : Nat → Packing
  | 5 => (2,1,2,0,0,3,0,mo361D5)
  | 6 => (1,0,2,0,0,0,0,mo361D6)
  | _ => emptyPacking
def mo361I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 mo361H6
  | _ => fun _ => none
def mo361 : Forest := ⟨1385,6,fun i => mo361Y[i]?.getD (0,0),mo361C,mo361A,mo361L,mo361I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P5_0 : CutRow mo361 5 0 2 := shortcutBlock (data:=fun _ => 0x20260141a052413001260141a0524130) (by decide +kernel)
theorem mo361B5 : CutRow mo361 5 0 2 := mo361P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P6_0 : CutRow mo361 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo361B6 : CutRow mo361 6 0 1 := mo361P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361T : mixedTables mo361 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo361 0 0)
  · exact (mixedEmpty mo361 1 0)
  · exact (mixedEmpty mo361 2 0)
  · exact (mixedEmpty mo361 3 0)
  · exact (mixedEmpty mo361 4 0)
  · exact mo361B5
  · exact mo361B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361G : graphValid mo361 (boundsBefore KM333) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM361 : Lower false (varsX 361) (graphGoal 361) 7 := lowerMixed (g:=mo361) (i:=0) (hints:=12884926469) (before_sound KM333 VM333) mo361G mo361T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM361 := extendKnown KM333 7 [(361,[]),(362,[16,134]),(460,[32,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM361 : Known false KM361 := extend_ok (m:=361) VM333 lowM361 (by decide +kernel)
def mo488Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo488C : List ColumnInfo := [(0,32,328,128,5)]
def mo488A : List (List Nat) := [[],[134],[117],[117,134],[99],[99,131],[99,117],[99,117,131],[131,99],[131],[131,117,99],[131,117]]
def mo488D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo488L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo488D5)
  | _ => emptyPacking
def mo488I (_ _ : Nat) : Option (Nat × Nat) := none
def mo488 : Forest := ⟨1512,5,fun i => mo488Y[i]?.getD (0,0),mo488C,mo488A,mo488L,mo488I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488P5_0 : block mo488 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo488B5 : block mo488 5 0 1=true := mo488P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488T : checkedTables mo488 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo488 0 0 0 = true)
  · exact (rfl : block mo488 1 0 0 = true)
  · exact (rfl : block mo488 2 0 0 = true)
  · exact (rfl : block mo488 3 0 0 = true)
  · exact (rfl : block mo488 4 0 0 = true)
  · exact mo488B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488G : graphValid mo488 (boundsBefore KM361) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM488 : Lower false (varsX 488) (graphGoal 488) 6 := lower_forest (g:=mo488) (i:=0) (hints:=14284775424) (before_sound KM361 VM361) mo488G mo488T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM488 := extendKnown KM361 6 [(488,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM488 : Known false KM488 := extend_ok (m:=488) VM361 lowM488 (by decide +kernel)
theorem lowM231 : Lower false (varsX 231) (graphGoal 231) 8 := lower_down lowS231
def KM231 := extendKnown KM488 8 [(231,[]),(237,[32,49,80,96,112]),(485,[32,129,80,49,67,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM231 : Known false KM231 := extend_ok (m:=231) VM488 lowM231 (by decide +kernel)
def mo238Y : Array (Bits × Bits) := #[(0x0,0x0),(0x101010101010101,0x39b9b9b9b9b9b9b9),(0x3636363636363636,0x1313131313131313),(0x808080808080808,0x3b3b3b3b3b3b3b3b),(0x0,0x0),(0x1c1c1c1c1c1c1c1,0x646464646464646),(0xe0e0e0e0e0e0e0e,0x4c4c4c4c4c4c4c4),(0x30f0f0f0f0f0f0f0,0x28a8a8a8a8a8a8a8),(0x0,0x0)]
def mo238C : List ColumnInfo := [(0,2,204,32,5),(0,8,166,64,5),(2,0,236,0,5),(8,0,230,0,5)]
def mo238A : List (List Nat) := [[],[49,114,101]]
def mo238D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd813f
def mo238L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,mo238D6)
  | _ => emptyPacking
def mo238I (_ _ : Nat) : Option (Nat × Nat) := none
def mo238 : Forest := ⟨1262,6,fun i => mo238Y[i]?.getD (0,0),mo238C,mo238A,mo238L,mo238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238P6_0 : block mo238 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo238B6 : block mo238 6 0 1=true := mo238P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238T : checkedTables mo238 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo238 0 0 0 = true)
  · exact (rfl : block mo238 1 0 0 = true)
  · exact (rfl : block mo238 2 0 0 = true)
  · exact (rfl : block mo238 3 0 0 = true)
  · exact (rfl : block mo238 4 0 0 = true)
  · exact (rfl : block mo238 5 0 0 = true)
  · exact mo238B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238G : graphValid mo238 (boundsBefore KM231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM238 : Lower false (varsX 238) (graphGoal 238) 7 := lower_forest (g:=mo238) (i:=0) (hints:=571500112) (before_sound KM231 VM231) mo238G mo238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM238 := extendKnown KM231 7 [(238,[]),(249,[16,48,82,64,32,96,112]),(430,[33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM238 : Known false KM238 := extend_ok (m:=238) VM231 lowM238 (by decide +kernel)
theorem lowM243 : Lower false (varsX 243) (graphGoal 243) 7 := lower_down lowS243
def KM243 := extendKnown KM238 7 [(423,[16,50,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM243 : Known false KM243 := extend_ok (m:=243) VM238 lowM243 (by decide +kernel)
def mo250Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo250C : List ColumnInfo := []
def mo250A : List (List Nat) := [[],[99],[65,117],[65,99,117]]
def mo250D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo250L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo250D5)
  | _ => emptyPacking
def mo250I (_ _ : Nat) : Option (Nat × Nat) := none
def mo250 : Forest := ⟨1274,5,fun i => mo250Y[i]?.getD (0,0),mo250C,mo250A,mo250L,mo250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250P5_0 : CutRow mo250 5 0 1 := shortcutBlock (data:=fun _ => 0xe0c20924864a053) (by decide +kernel)
theorem mo250B5 : CutRow mo250 5 0 1 := mo250P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250T : mixedTables mo250 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo250 0 0)
  · exact (mixedEmpty mo250 1 0)
  · exact (mixedEmpty mo250 2 0)
  · exact (mixedEmpty mo250 3 0)
  · exact (mixedEmpty mo250 4 0)
  · exact mo250B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250G : graphValid mo250 (boundsBefore KM243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM250 : Lower false (varsX 250) (graphGoal 250) 6 := lowerMixed (g:=mo250) (i:=0) (hints:=1125605456) (before_sound KM243 VM243) mo250G mo250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM250 := extendKnown KM243 6 [(429,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM250 : Known false KM250 := extend_ok (m:=250) VM243 lowM250 (by decide +kernel)
def mo335Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo335C : List ColumnInfo := [(1,0,334,0,6)]
def mo335A : List (List Nat) := [[],[32]]
def mo335D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo335L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo335D6)
  | _ => emptyPacking
def mo335I (_ _ : Nat) : Option (Nat × Nat) := none
def mo335 : Forest := ⟨1359,6,fun i => mo335Y[i]?.getD (0,0),mo335C,mo335A,mo335L,mo335I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335P6_0 : block mo335 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo335B6 : block mo335 6 0 1=true := mo335P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335T : checkedTables mo335 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo335 0 0 0 = true)
  · exact (rfl : block mo335 1 0 0 = true)
  · exact (rfl : block mo335 2 0 0 = true)
  · exact (rfl : block mo335 3 0 0 = true)
  · exact (rfl : block mo335 4 0 0 = true)
  · exact (rfl : block mo335 5 0 0 = true)
  · exact mo335B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335G : graphValid mo335 (boundsBefore KM250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM335 : Lower false (varsX 335) (graphGoal 335) 7 := lower_forest (g:=mo335) (i:=0) (hints:=4294993542) (before_sound KM250 VM250) mo335G mo335T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM335 := extendKnown KM250 7 [(335,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM335 : Known false KM335 := extend_ok (m:=335) VM250 lowM335 (by decide +kernel)
def mo363Y : Array (Bits × Bits) := #[(0x30038f0038f0038f,0x12a2852a2852a285),(0xe0700e0700e070,0x1069a1069a1069a1),(0x0,0x0),(0x31c0031c0031c00,0x3124931249312493),(0x0,0x0),(0x30007f0007f0007f,0x2d145ad145ad145a),(0xc1f80c1f80c1f80,0x459604596045960),(0x0,0x0),(0xfe000fe000fe000,0xa820ca820ca820c)]
def mo363C : List ColumnInfo := [(1,0,362,0,7),(2,0,361,0,7),(8,0,355,0,7),(0,32,328,3,6),(32,0,331,0,6),(64,0,299,0,5)]
def mo363A : List (List Nat) := [[],[16,134]]
def mo363D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30bb58854be58054
def mo363D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4398a16a60d45d03faa9fc54
def mo363H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a00880000000
def mo363D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def mo363H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f40000
def mo363L : Nat → Packing
  | 6 => (2,2,3,0,0,3,0,mo363D6)
  | 7 => (2,1,3,0,0,5,0,mo363D7)
  | 8 => (1,0,3,0,0,0,0,mo363D8)
  | _ => emptyPacking
def mo363I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 1 1 mo363H7
  | 8 => lookupWord 1 7 0 5 1 0 mo363H8
  | _ => fun _ => none
def mo363 : Forest := ⟨1387,8,fun i => mo363Y[i]?.getD (0,0),mo363C,mo363A,mo363L,mo363I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P6_0 : block mo363 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B6 : block mo363 6 0 2=true := mo363P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P7_0 : block mo363 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B7 : block mo363 7 0 2=true := mo363P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P8_0 : block mo363 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B8 : block mo363 8 0 1=true := mo363P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363T : checkedTables mo363 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo363 0 0 0 = true)
  · exact (rfl : block mo363 1 0 0 = true)
  · exact (rfl : block mo363 2 0 0 = true)
  · exact (rfl : block mo363 3 0 0 = true)
  · exact (rfl : block mo363 4 0 0 = true)
  · exact (rfl : block mo363 5 0 0 = true)
  · exact mo363B6
  · exact mo363B7
  · exact mo363B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363G : graphValid mo363 (boundsBefore KM335) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM363 : Lower false (varsX 363) (graphGoal 363) 9 := lower_forest (g:=mo363) (i:=0) (hints:=4294991957) (before_sound KM335 VM335) mo363G mo363T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM363 := extendKnown KM335 9 [(363,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM363 : Known false KM363 := extend_ok (m:=363) VM335 lowM363 (by decide +kernel)
def mo365Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo365C : List ColumnInfo := [(4,0,361,0,7)]
def mo365A : List (List Nat) := [[],[131]]
def mo365D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo365L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo365D7)
  | _ => emptyPacking
def mo365I (_ _ : Nat) : Option (Nat × Nat) := none
def mo365 : Forest := ⟨1389,7,fun i => mo365Y[i]?.getD (0,0),mo365C,mo365A,mo365L,mo365I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365P7_0 : block mo365 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo365B7 : block mo365 7 0 1=true := mo365P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365T : checkedTables mo365 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo365 0 0 0 = true)
  · exact (rfl : block mo365 1 0 0 = true)
  · exact (rfl : block mo365 2 0 0 = true)
  · exact (rfl : block mo365 3 0 0 = true)
  · exact (rfl : block mo365 4 0 0 = true)
  · exact (rfl : block mo365 5 0 0 = true)
  · exact (rfl : block mo365 6 0 0 = true)
  · exact mo365B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365G : graphValid mo365 (boundsBefore KM363) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM365 : Lower false (varsX 365) (graphGoal 365) 8 := lower_forest (g:=mo365) (i:=0) (hints:=12884928005) (before_sound KM363 VM363) mo365G mo365T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM365 := extendKnown KM363 8 [(365,[]),(461,[32,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM365 : Known false KM365 := extend_ok (m:=365) VM363 lowM365 (by decide +kernel)
def mo366Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo366C : List ColumnInfo := [(4,0,362,0,7)]
def mo366A : List (List Nat) := [[]]
def mo366D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo366L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo366D7)
  | _ => emptyPacking
def mo366I (_ _ : Nat) : Option (Nat × Nat) := none
def mo366 : Forest := ⟨1390,7,fun i => mo366Y[i]?.getD (0,0),mo366C,mo366A,mo366L,mo366I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366P7_0 : block mo366 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo366B7 : block mo366 7 0 1=true := mo366P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366T : checkedTables mo366 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo366 0 0 0 = true)
  · exact (rfl : block mo366 1 0 0 = true)
  · exact (rfl : block mo366 2 0 0 = true)
  · exact (rfl : block mo366 3 0 0 = true)
  · exact (rfl : block mo366 4 0 0 = true)
  · exact (rfl : block mo366 5 0 0 = true)
  · exact (rfl : block mo366 6 0 0 = true)
  · exact mo366B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366G : graphValid mo366 (boundsBefore KM365) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM366 : Lower false (varsX 366) (graphGoal 366) 8 := lower_forest (g:=mo366) (i:=0) (hints:=4329596496) (before_sound KM365 VM365) mo366G mo366T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM366 := extendKnown KM365 8 [(366,[]),(377,[16,66,134]),(462,[33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM366 : Known false KM366 := extend_ok (m:=366) VM365 lowM366 (by decide +kernel)
theorem lowM486 : Lower false (varsX 486) (graphGoal 486) 8 := lower_down lowS486
def KM486 := extendKnown KM366 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM486 : Known false KM486 := extend_ok (m:=486) VM366 lowM486 (by decide +kernel)
def mo489Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo489C : List ColumnInfo := [(128,0,361,0,7)]
def mo489A : List (List Nat) := [[],[131]]
def mo489D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo489L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo489D7)
  | _ => emptyPacking
def mo489I (_ _ : Nat) : Option (Nat × Nat) := none
def mo489 : Forest := ⟨1513,7,fun i => mo489Y[i]?.getD (0,0),mo489C,mo489A,mo489L,mo489I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489P7_0 : block mo489 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo489B7 : block mo489 7 0 1=true := mo489P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489T : checkedTables mo489 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo489 0 0 0 = true)
  · exact (rfl : block mo489 1 0 0 = true)
  · exact (rfl : block mo489 2 0 0 = true)
  · exact (rfl : block mo489 3 0 0 = true)
  · exact (rfl : block mo489 4 0 0 = true)
  · exact (rfl : block mo489 5 0 0 = true)
  · exact (rfl : block mo489 6 0 0 = true)
  · exact mo489B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489G : graphValid mo489 (boundsBefore KM486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM489 : Lower false (varsX 489) (graphGoal 489) 8 := lower_forest (g:=mo489) (i:=0) (hints:=14227103749) (before_sound KM486 VM486) mo489G mo489T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM489 := extendKnown KM486 8 [(489,[]),(490,[16,134]),(492,[32,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM489 : Known false KM489 := extend_ok (m:=489) VM486 lowM489 (by decide +kernel)
def mo239Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo239C : List ColumnInfo := [(2,0,237,0,8)]
def mo239A : List (List Nat) := [[],[49,114,101]]
def mo239D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo239L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo239D8)
  | _ => emptyPacking
def mo239I (_ _ : Nat) : Option (Nat × Nat) := none
def mo239 : Forest := ⟨1263,8,fun i => mo239Y[i]?.getD (0,0),mo239C,mo239A,mo239L,mo239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239P8_0 : block mo239 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo239B8 : block mo239 8 0 1=true := mo239P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239T : checkedTables mo239 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo239 0 0 0 = true)
  · exact (rfl : block mo239 1 0 0 = true)
  · exact (rfl : block mo239 2 0 0 = true)
  · exact (rfl : block mo239 3 0 0 = true)
  · exact (rfl : block mo239 4 0 0 = true)
  · exact (rfl : block mo239 5 0 0 = true)
  · exact (rfl : block mo239 6 0 0 = true)
  · exact (rfl : block mo239 7 0 0 = true)
  · exact mo239B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239G : graphValid mo239 (boundsBefore KM489) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM239 : Lower false (varsX 239) (graphGoal 239) 9 := lower_forest (g:=mo239) (i:=0) (hints:=536897109) (before_sound KM489 VM489) mo239G mo239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM239 := extendKnown KM489 9 [(239,[]),(253,[32,49,80,65,96,112]),(443,[16,66,134]),(446,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM239 : Known false KM239 := extend_ok (m:=239) VM489 lowM239 (by decide +kernel)
theorem lowM247 : Lower false (varsX 247) (graphGoal 247) 9 := lower_down lowS247
def KM247 := extendKnown KM239 9 [(247,[]),(375,[33,101,135]),(439,[16,66,134]),(471,[32,16,65,101,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM247 : Known false KM247 := extend_ok (m:=247) VM239 lowM247 (by decide +kernel)
def mo251Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo251C : List ColumnInfo := [(2,0,249,0,7)]
def mo251A : List (List Nat) := [[]]
def mo251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo251L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo251D7)
  | _ => emptyPacking
def mo251I (_ _ : Nat) : Option (Nat × Nat) := none
def mo251 : Forest := ⟨1275,7,fun i => mo251Y[i]?.getD (0,0),mo251C,mo251A,mo251L,mo251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251P7_0 : block mo251 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo251B7 : block mo251 7 0 1=true := mo251P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251T : checkedTables mo251 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo251 0 0 0 = true)
  · exact (rfl : block mo251 1 0 0 = true)
  · exact (rfl : block mo251 2 0 0 = true)
  · exact (rfl : block mo251 3 0 0 = true)
  · exact (rfl : block mo251 4 0 0 = true)
  · exact (rfl : block mo251 5 0 0 = true)
  · exact (rfl : block mo251 6 0 0 = true)
  · exact mo251B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251G : graphValid mo251 (boundsBefore KM247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM251 : Lower false (varsX 251) (graphGoal 251) 8 := lower_forest (g:=mo251) (i:=0) (hints:=1074225237) (before_sound KM247 VM247) mo251G mo251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM251 := extendKnown KM247 8 [(431,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM251 : Known false KM251 := extend_ok (m:=251) VM247 lowM251 (by decide +kernel)
def mo367Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo367C : List ColumnInfo := [(4,0,363,0,9)]
def mo367A : List (List Nat) := [[]]
def mo367D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo367L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo367D9)
  | _ => emptyPacking
def mo367I (_ _ : Nat) : Option (Nat × Nat) := none
def mo367 : Forest := ⟨1391,9,fun i => mo367Y[i]?.getD (0,0),mo367C,mo367A,mo367L,mo367I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367P9_0 : block mo367 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo367B9 : block mo367 9 0 1=true := mo367P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367T : checkedTables mo367 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo367 0 0 0 = true)
  · exact (rfl : block mo367 1 0 0 = true)
  · exact (rfl : block mo367 2 0 0 = true)
  · exact (rfl : block mo367 3 0 0 = true)
  · exact (rfl : block mo367 4 0 0 = true)
  · exact (rfl : block mo367 5 0 0 = true)
  · exact (rfl : block mo367 6 0 0 = true)
  · exact (rfl : block mo367 7 0 0 = true)
  · exact (rfl : block mo367 8 0 0 = true)
  · exact mo367B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367G : graphValid mo367 (boundsBefore KM251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM367 : Lower false (varsX 367) (graphGoal 367) 10 := lower_forest (g:=mo367) (i:=0) (hints:=4294993493) (before_sound KM251 VM251) mo367G mo367T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM367 := extendKnown KM251 10 [(367,[]),(379,[16,66,134]),(477,[32,65,117]),(478,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM367 : Known false KM367 := extend_ok (m:=367) VM251 lowM367 (by decide +kernel)
def mo381Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo381C : List ColumnInfo := [(4,0,377,0,8)]
def mo381A : List (List Nat) := [[]]
def mo381D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo381L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo381D8)
  | _ => emptyPacking
def mo381I (_ _ : Nat) : Option (Nat × Nat) := none
def mo381 : Forest := ⟨1405,8,fun i => mo381Y[i]?.getD (0,0),mo381C,mo381A,mo381L,mo381I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381P8_0 : block mo381 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo381B8 : block mo381 8 0 1=true := mo381P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381T : checkedTables mo381 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo381 0 0 0 = true)
  · exact (rfl : block mo381 1 0 0 = true)
  · exact (rfl : block mo381 2 0 0 = true)
  · exact (rfl : block mo381 3 0 0 = true)
  · exact (rfl : block mo381 4 0 0 = true)
  · exact (rfl : block mo381 5 0 0 = true)
  · exact (rfl : block mo381 6 0 0 = true)
  · exact (rfl : block mo381 7 0 0 = true)
  · exact mo381B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381G : graphValid mo381 (boundsBefore KM367) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM381 : Lower false (varsX 381) (graphGoal 381) 9 := lower_forest (g:=mo381) (i:=0) (hints:=12885452293) (before_sound KM367 VM367) mo381G mo381T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM381 := extendKnown KM367 9 [(381,[]),(382,[16,66,134]),(463,[32,65,117]),(475,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM381 : Known false KM381 := extend_ok (m:=381) VM367 lowM381 (by decide +kernel)
theorem lowM487 : Lower false (varsX 487) (graphGoal 487) 11 := lower_down lowS487
def KM487 := extendKnown KM381 11 [(487,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM487 : Known false KM487 := extend_ok (m:=487) VM381 lowM487 (by decide +kernel)
def mo491Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo491C : List ColumnInfo := [(128,0,363,0,9)]
def mo491A : List (List Nat) := [[],[16,134]]
def mo491D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo491L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo491D9)
  | _ => emptyPacking
def mo491I (_ _ : Nat) : Option (Nat × Nat) := none
def mo491 : Forest := ⟨1515,9,fun i => mo491Y[i]?.getD (0,0),mo491C,mo491A,mo491L,mo491I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491P9_0 : block mo491 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo491B9 : block mo491 9 0 1=true := mo491P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491T : checkedTables mo491 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo491 0 0 0 = true)
  · exact (rfl : block mo491 1 0 0 = true)
  · exact (rfl : block mo491 2 0 0 = true)
  · exact (rfl : block mo491 3 0 0 = true)
  · exact (rfl : block mo491 4 0 0 = true)
  · exact (rfl : block mo491 5 0 0 = true)
  · exact (rfl : block mo491 6 0 0 = true)
  · exact (rfl : block mo491 7 0 0 = true)
  · exact (rfl : block mo491 8 0 0 = true)
  · exact mo491B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491G : graphValid mo491 (boundsBefore KM487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM491 : Lower false (varsX 491) (graphGoal 491) 10 := lower_forest (g:=mo491) (i:=0) (hints:=5637169237) (before_sound KM487 VM487) mo491G mo491T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM491 := extendKnown KM487 10 [(491,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM491 : Known false KM491 := extend_ok (m:=491) VM487 lowM491 (by decide +kernel)
def mo493Y : Array (Bits × Bits) := #[(0x1fc00003f800007f,0xc65d7918cbaf231),(0x0,0x0),(0x2000078c0000f180,0x22d342945a68528b),(0x7c07000f80e00,0x28c0d195181a32a3),(0x0,0x0),(0x7c03800f807001f,0x239a082c7341058e),(0x3838007f07000fe0,0x1108286a21050d44),(0x3f800007f000,0x1c24b5438496a870),(0x3fc00007f80000,0x6370600c6e0c018)]
def mo493C : List ColumnInfo := [(1,0,492,0,8),(4,0,489,0,8),(8,0,485,0,8),(32,0,461,0,8),(128,0,365,0,8),(256,0,237,0,8),(0,32,332,129,7),(0,128,329,36,7),(33,0,460,0,7),(132,0,361,0,7),(264,0,229,0,7),(0,8,165,320,6),(0,256,165,72,6),(1,128,328,36,6),(4,32,328,129,6),(5,0,488,0,6),(32,128,329,4,6),(64,0,429,0,6),(160,0,333,0,6),(9,0,484,0,5),(64,8,165,256,5),(64,256,165,8,5),(129,32,332,0,5)]
def mo493A : List (List Nat) := [[],[131],[32,117],[32,131,117]]
def mo493D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc29f32c3a2a09057c6447454120
def mo493D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x470b00311c2c00e74884f0f009fd811d120df87454120fe94254120ff141501108fd861d1209f5811d120
def mo493H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x103
def mo493D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7083a44a14203022e50a1c340944458028a07294884e2272822508305870c142030442a9320a0854a2711045c9e370f81bddd6df69b1cea22e866aad124b14803fea9a85ff50d42ffa84a87fd72503fea1281ff5c540ffa82a07fd41483fea12217f1d132bfae8905fc74483f6a1241fe54120ff280905fd74442feb9221fe50110
def mo493H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa800089a030000400000000000020800000000
def mo493D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa87209485910a883851c62e9a0a19090828e143a8725614daa92044cd2e92881aa2483c4fcd8ae8a66481e00ff54ffd43ff50bfd32ff543fd40ff483fd10
def mo493H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x95a24118000722c9017f0ea0c33653b8095d53fc0983b0af159488b211410005313137038380061a6080010cb94003478478a0a864576af4608f54411904
def mo493D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x52501ff
def mo493H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81000000000001e66c6e0000000c480000000010000a6004d8460000000000000000000000000cbd9005c800000000000002a000000088800000000000010410d1c000d00000000008
def mo493L : Nat → Packing
  | 6 => (2,4,5,0,0,3,0,mo493D6)
  | 7 => (6,3,5,0,0,7,0,mo493D7)
  | 8 => (18,2,5,0,0,9,0,mo493D8)
  | 9 => (8,1,5,0,0,8,0,mo493D9)
  | 10 => (1,0,5,0,0,0,0,mo493D10)
  | _ => emptyPacking
def mo493I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 5 1 0 mo493H7
  | 8 => lookupWord 1 23 0 7 3 0 mo493H8
  | 9 => lookupWord 9 41 5 11 5 2 mo493H9
  | 10 => lookupWord 4 67 2 9 3 2 mo493H10
  | _ => fun _ => none
def mo493 : Forest := ⟨1517,10,fun i => mo493Y[i]?.getD (0,0),mo493C,mo493A,mo493L,mo493I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P6_0 : CutRow mo493 6 0 2 := shortcutBlock (data:=fun _ => 0x1818106c3489416318105c0e17804562) (by decide +kernel)
theorem mo493B6 : CutRow mo493 6 0 2 := mo493P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P7_0 : CutRow mo493 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P7_2 : CutRow mo493 7 2 4 := shortcutBlock (data:=fun _ => 0x2498102a144aa053248c0c0f030a4430058c044b251a44200c18160315c02151) (by decide +kernel)
theorem mo493B7 : CutRow mo493 7 0 6 := (@joinRow mo493 7 0 2 4 mo493P7_0 mo493P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_0 : CutRow mo493 8 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_9 : CutRow mo493 8 9 9 := shortcutBlock (data:=fun _ => 0x30324603818221302498130380c88451058c044b251a44413026060381822130302606038182213030260603818221303026060381822130248c030380c884512498102a144aa053) (by decide +kernel)
theorem mo493B8 : CutRow mo493 8 0 18 := (@joinRow mo493 8 0 9 9 mo493P8_0 mo493P8_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P9_0 : CutRow mo493 9 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B9 : CutRow mo493 9 0 8 := mo493P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P10_0 : CutRow mo493 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B10 : CutRow mo493 10 0 1 := mo493P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493T : mixedTables mo493 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo493 0 0)
  · exact (mixedEmpty mo493 1 0)
  · exact (mixedEmpty mo493 2 0)
  · exact (mixedEmpty mo493 3 0)
  · exact (mixedEmpty mo493 4 0)
  · exact (mixedEmpty mo493 5 0)
  · exact mo493B6
  · exact mo493B7
  · exact mo493B8
  · exact mo493B9
  · exact mo493B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493G : graphValid mo493 (boundsBefore KM491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM493 : Lower false (varsX 493) (graphGoal 493) 11 := lowerMixed (g:=mo493) (i:=0) (hints:=13421798917) (before_sound KM491 VM491) mo493G mo493T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM493 := extendKnown KM491 11 [(493,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM493 : Known false KM493 := extend_ok (m:=493) VM491 lowM493 (by decide +kernel)
def mo494Y : Array (Bits × Bits) := #[(0x0,0x0),(0x703c000703c0007,0x948d1f0948d1f09),(0x380007c780007c78,0x1b154245b154245b),(0x1c003801c00380,0x1b0c40d1b0c40d1b),(0x0,0x0),(0x700380070038007,0x36350a0f6350a0f6),(0x38e0003f8e0003f8,0x2460992a460992a4),(0x3fc00003fc00,0xcab5b00cab5b00),(0xffc0000ffc0000,0x93260409326040)]
def mo494C : List ColumnInfo := [(2,0,492,0,8),(4,0,490,0,8),(8,0,486,0,8),(32,0,462,0,8),(128,0,366,0,8),(0,32,332,130,7),(0,128,330,36,7),(34,0,460,0,7),(64,0,430,0,7),(132,0,362,0,7),(256,0,238,0,7),(0,2,204,288,6),(0,4,298,192,6),(0,8,166,320,6),(2,32,332,128,6),(2,128,328,36,6),(4,32,328,130,6),(6,0,488,0,6),(32,128,330,4,6),(128,32,332,2,6),(64,4,298,128,5),(64,8,166,256,5),(256,2,204,32,5),(256,8,166,64,5),(76,0,418,0,4),(266,0,228,0,4),(320,8,166,0,4)]
def mo494A : List (List Nat) := [[],[33,117,134]]
def mo494D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x236082eb4ba889c580ded731c964dec725c164bed8219153bf98019153fac8259140ebd6458940ebd6458540ead6458942
def mo494D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc98f0e04428406040221a30404045a71460b0c14203020082f0822e28a8610181042c54b00b06203960d3240e58410101811628d14101c20300b1100b0a2a2292f1ca885e1072c22684a439614ac20e5841828203042c618284498e2c6821cb064c80ad22070c58a0dd2284671ca63c45458ad220887d0e21942c84d0820d41481d022013fc7ecfc1f53e47bcf61e93cc78cf01dd3b475cea1bfb4f64cba16a2b95209d52d23841e744d798d2d6508900f01802943a83e001ff5cd64ffae0b27fd6458ffeb22a7ff19153ffac8a1ffd6550bfeaa285ff58d42ffaa6a17fd4350bfeb22c1ff50960ffa82b07fd64543feb12a1ff50950ffac8a07fd62503fea1281ff58540ffa82a07fd61483fea0a41ff59110ffa84887ec72592feb90c97f5c064bfaeca17bd6450bf6b12857f5d940f7ac8a07f960503fca82817f5d920bfae8907ed62483f690a41fe58120ff2a0907f940482feba2217f5c910ff280885dd73192f6b90c97e5c064
def mo494H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x770000000095640000000000000000bb0000ea0036002f0052000000000000000000000000000e00000000732100
def mo494D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6142a676865861545692a7209288912887407288162247187288912887407286142a6769820a2244876901c808b3e96471d62888891c61ca88f5a91c628808fa5a1c7522247445841d4691745110e378ae1f85409000ff593fc64ff58ffd53ff50ffd42ff4cbfd60ff543fd40ff483fd10
def mo494H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc24006b0d5c29400381e3ae7c000000004b4d17170011ab87a928a800000670001a100002315e00000000d1016c00000637e1db2800ca0fa5603980009160018600076570b1cd43e5b6f4cfcced7ed64da7940004f791328002a1000000003d580064c001c725291aeabb15cc00035ec98000d6a15886295dcaa0001c300000237e0b000001c1520d320000000000180c0a800d35293854a7e180022a9184d000001c4c020249
def mo494D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x124e1ff
def mo494H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1650000001d60065400007245c014754c2245b900003a28bd00035400d90528d210000000a3007cc018
def mo494L : Nat → Packing
  | 7 => (8,3,5,0,0,6,0,mo494D7)
  | 8 => (49,2,5,0,0,11,0,mo494D8)
  | 9 => (12,1,5,0,0,10,0,mo494D9)
  | 10 => (1,0,5,0,0,0,0,mo494D10)
  | _ => emptyPacking
def mo494I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 47 0 8 3 1 mo494H8
  | 9 => lookupWord 18 113 5 11 6 1 mo494H9
  | 10 => lookupWord 5 37 1 9 4 1 mo494H10
  | _ => fun _ => none
def mo494 : Forest := ⟨1518,10,fun i => mo494Y[i]?.getD (0,0),mo494C,mo494A,mo494L,mo494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_0 : CutRow mo494 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_1 : CutRow mo494 7 1 7 := shortcutBlock (data:=fun _ => 0x18524c0683042a2018524c0683042a2018524c0683042220248c2c060b402272248c2c070308445101cc2457011c447124980032184ca043) (by decide +kernel)
theorem mo494B7 : CutRow mo494 7 0 8 := (@joinRow mo494 7 0 1 7 mo494P7_0 mo494P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_0 : CutRow mo494 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_3 : CutRow mo494 8 3 20 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_23 : CutRow mo494 8 23 26 := shortcutBlock (data:=fun _ => 0x18524c068304223018524c0683042230248c2c070308444118524c068304223018524c06830422302498030380c8845118524c068304223018524c0683042230058c24432118444118524c06830422302498030380c8845118524c068304223018524c068304223018524c0683042230248c2c0703084441248c2453291c4441058c2453291c44412498030380c8845101cc2453291c444101cc2453291c444124980032184ca053248c230380c8845124980032184ca053248c230380c8845124980032184ca053058c2453291c4441) (by decide +kernel)
theorem mo494B8 : CutRow mo494 8 0 49 := (@joinRow mo494 8 0 3 46 mo494P8_0 (@joinRow mo494 8 3 20 26 mo494P8_3 mo494P8_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P9_0 : CutRow mo494 9 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B9 : CutRow mo494 9 0 12 := mo494P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P10_0 : CutRow mo494 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B10 : CutRow mo494 10 0 1 := mo494P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494T : mixedTables mo494 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo494 0 0)
  · exact (mixedEmpty mo494 1 0)
  · exact (mixedEmpty mo494 2 0)
  · exact (mixedEmpty mo494 3 0)
  · exact (mixedEmpty mo494 4 0)
  · exact (mixedEmpty mo494 5 0)
  · exact (mixedEmpty mo494 6 0)
  · exact mo494B7
  · exact mo494B8
  · exact mo494B9
  · exact mo494B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494G : graphValid mo494 (boundsBefore KM493) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM494 : Lower false (varsX 494) (graphGoal 494) 11 := lowerMixed (g:=mo494) (i:=0) (hints:=4866467408) (before_sound KM493 VM493) mo494G mo494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM494 := extendKnown KM493 11 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM494 : Known false KM494 := extend_ok (m:=494) VM493 lowM494 (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo255C : List ColumnInfo := [(2,0,253,0,9)]
def mo255A : List (List Nat) := [[],[32,65,117]]
def mo255D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo255L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo255D9)
  | _ => emptyPacking
def mo255I (_ _ : Nat) : Option (Nat × Nat) := none
def mo255 : Forest := ⟨1279,9,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : block mo255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B9 : block mo255 9 0 1=true := mo255P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : checkedTables mo255 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo255 0 0 0 = true)
  · exact (rfl : block mo255 1 0 0 = true)
  · exact (rfl : block mo255 2 0 0 = true)
  · exact (rfl : block mo255 3 0 0 = true)
  · exact (rfl : block mo255 4 0 0 = true)
  · exact (rfl : block mo255 5 0 0 = true)
  · exact (rfl : block mo255 6 0 0 = true)
  · exact (rfl : block mo255 7 0 0 = true)
  · exact (rfl : block mo255 8 0 0 = true)
  · exact mo255B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore KM494) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM255 : Lower false (varsX 255) (graphGoal 255) 10 := lower_forest (g:=mo255) (i:=0) (hints:=537355861) (before_sound KM494 VM494) mo255G mo255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM255 := extendKnown KM494 10 [(255,[]),(447,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM255 : Known false KM255 := extend_ok (m:=255) VM494 lowM255 (by decide +kernel)
def mo383Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo383C : List ColumnInfo := [(4,0,379,0,10)]
def mo383A : List (List Nat) := [[],[16,66,134]]
def mo383D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo383L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,mo383D10)
  | _ => emptyPacking
def mo383I (_ _ : Nat) : Option (Nat × Nat) := none
def mo383 : Forest := ⟨1407,10,fun i => mo383Y[i]?.getD (0,0),mo383C,mo383A,mo383L,mo383I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383P10_0 : block mo383 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo383B10 : block mo383 10 0 1=true := mo383P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383T : checkedTables mo383 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo383 0 0 0 = true)
  · exact (rfl : block mo383 1 0 0 = true)
  · exact (rfl : block mo383 2 0 0 = true)
  · exact (rfl : block mo383 3 0 0 = true)
  · exact (rfl : block mo383 4 0 0 = true)
  · exact (rfl : block mo383 5 0 0 = true)
  · exact (rfl : block mo383 6 0 0 = true)
  · exact (rfl : block mo383 7 0 0 = true)
  · exact (rfl : block mo383 8 0 0 = true)
  · exact (rfl : block mo383 9 0 0 = true)
  · exact mo383B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383G : graphValid mo383 (boundsBefore KM255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM383 : Lower false (varsX 383) (graphGoal 383) 11 := lower_forest (g:=mo383) (i:=0) (hints:=4295517781) (before_sound KM255 VM255) mo383G mo383T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM383 := extendKnown KM255 11 [(383,[]),(479,[32,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM383 : Known false KM383 := extend_ok (m:=383) VM255 lowM383 (by decide +kernel)
def mo495Y : Array (Bits × Bits) := #[(0x3c3800000787,0x193430515326860a),(0x300003c01e000078,0x347c0a40468f8148),(0x1f0c000003e1800,0x109190fcaa12321f),(0xf0001e001e000,0x103500c86206a019),(0x0,0x0),(0xe0003f801c0007f,0x283c5aea85078b5),(0xffc060001ff80,0x264a4f0204c949e0),(0xff0000001fe0000,0x2d6c2a0155ad8540),(0x30000007fe000000,0x980b03599301606)]
def mo495C : List ColumnInfo := [(1,0,494,0,11),(2,0,493,0,11),(8,0,487,0,11),(4,0,491,0,10),(128,0,367,0,10),(32,0,463,0,9),(132,0,363,0,9),(256,0,239,0,9),(0,32,332,131,8),(0,128,331,36,8),(64,0,431,0,8),(258,0,237,0,8),(264,0,231,0,8),(4,32,328,131,7),(32,128,331,4,7),(65,0,430,0,7),(72,0,423,0,7),(128,32,332,3,7),(160,0,335,0,7),(36,128,331,0,6)]
def mo495A : List (List Nat) := [[]]
def mo495D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x156182156182156182fc7cbd9e6f076ba9cee470b79b6d86ab499ecc64b1986c05eae96eb458ab956a852a893e9c4ca59269046a290e84409f8f6783a9c8de6c34998c6602e968ae54289389648229087e3c1c8d86630168a84e240c03000cfd69d9121576cfd6919121576ebb2999460875cfb6599460875afb6989460875cfe6599460075dbb699921d5659fd684955d974cfb6a1921d564cfb2a1921d564deb691921d564cfe6a1901d564dbe699901d564cf7619931d554cfb619921d554deb691921d554cfd619911d554cfe619901d554bd768c7559554bdb6887559554bdd6847559554bde6807559554cfd69d9121572cfd6919121572cfd2919121572cbf6598521572cef6159421572cf76159321572df36899321572cfd6159121572df96899121572cfe6159021572b3f698855d572b6f690855d572b7768c855d572b7d684855d572b7e680855d572af768c8561172afd6848561172afe68085611729fb6899521172af768c8521172afd6848521172afe6808521172af768c855d172afd684855d172afe680855d172cfb68898551728ff6959815172d7b5d59215172bbb698955c952beb690955c952bf368c955c952bf9684955c952bfa680955c952afb2a1945c952cfb260845c952b7b69c545c952cf7615931d542cfb615921d542cfd615911d542cfe6a1901d542cfe615901d542dfa689901d542be768c7555142beb6887555142bed6847555142bee6807555142bf368c955c942bf9684955c942bfa680955c942e7b615755c942f6b5d5545c9429f368c955c9429f9684955c9429fa680955c942
def mo495D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xac3e2e1e00e1828238b8783186c7e1e010c6171c2b8b83185c7e2e10fc6178fb8e38cb8b389b88386b85383b82380b7f37db7c37ab79377b76374b73371b7036eb6d36bb6a368b67365b64362b6135fb5e35cb5b359b58356b55353b52350b4f34db4c34ab49347b46344b43341b4033eb3d33bb3a338b37335b34332b3132fb2e32cb2b329b28326b25323b22320b1f31db1c31ab19317b16314b13311b1030eb0d301af62e8add2cfac22b4aa929ba90282a77269a5a24ca3d22da22216a0b1ff9f61ea9df1d39c61b89ab1a199618c98317996815a94b13d93212491910b8fe0f08e30d58ca0be8af0a389608a87f07186405884b03d83002281700b8003feb2242aedbfd8661175bfecb108badff648845d77fb08c12ebbfc8460975dfeca3043aeff251821d7dfaecbaacb7fc955d974dfebb10aba77f5d9755d37fb24c28e9bfd985d564dfe4c2eab26ff61d755937fb0ebaaa9bfd865d554dfec30eaaa5ff64875553efaeab2aa9f7c7559554fdebaae8aa6ff649871537fb0eba8a9bfd865d454dfebab042a7bf658855cb7fb0a42ae5fbd9421572feec990ab97fb648855cbfeb2242ae5ff99021572efe42aeab977f651755cbbf928baae57fc9561172dfec2b08b96ff215845cbbfaeac22e57fd9521172dfec2908b96ff214845cbbfaea422e57fc955d172dfe42ae8b977f5d5745caff930aa2e5dfd7555172bfecc0a8b95ff65c545cbbfaea2a2e5bfd9461d52dfe4a30ea96ff61d8454b7f90ec22a57fd9721152dfec3908a96ff21c8454aff930ba2a5bfd875d152bfecc0e8a95ff6547454b7fb0eaa2a57fd9715152dfec38a8a97fb2617254bfdb2ab92a5fec955c952ff6baae4a97fb6517254bfd928b92a5fed845c952ff6422e4a97fb5d17254bfdaa8b92a5fec545c952dfecc2eaa16ff2617550b7fb0ebaa85bfd855d542dfec28eaa17ef5d55450bf78eaaa285fed955c942ff64aae4a17fb5d57250afeb2242aedbed9660875df6ca3043aefb251821d77f32cc00ebbf99460075dfcc93003adfe64087596f7b283aacb7dd931d565bf6c90eab2dfd64475596ff3203aacb3fd92215749fe4c2caba6fb655821d27fb2e42ac97dd931d564bf6c90eab25fd64475592ff3203aac97ed9221d549fe4c2ecaa5bf65875552fbb263aaa97ed921d554bfac88eaaa5fe64075552dfb2c42ae57bd9421572beec990ab95fd644855caff32042ae53fc98551729fecc0a8b957f65c545cafdb242a2e56fd961d552bdeca0eaa95f764c7554afeb223aaa57f9901d5529fe4c2e8a94ff6607454afdb243a2a57ec985c952ef6baae4a94ff65c8550afbb263aa857ed921d542bfac88eaa15fe6407550afd92ab9285bed855c942ef6baae4a17eb5517250a7eb2242aed2fd96215729deca10ab94f764c855ca7eb2242ae53f99021572 else 0x38987831a38565e2e1e0261629921f8b87806e2e1e02365159787883e1d986646387e20fe119961f8b85983c6e2e160c68e149c478b8783186c5e1e02cc617149f8b8781186c5e2e02bc617149c3f8b87186080713e2e1e0661c1c178b87829868564878ee2e1e01c1c1423878b831870ac6e1e02c14289f87838850ac6e0e22b143c9f1b87885e2e1e091138b87803a98527e2e113e017130f84b3805c44327e2e1e01b130c9f8987806c4c327e2e10f1b838b844c4e00de2e1c6158b838718461e0e2c611838b871840a0705c6e2e1e00d202097831b8b8460a0725e0e2e1c61c2b838b849518627e2e1e01314349f8b8783186c5c6e1e02c17149f898783186c5270fe2e1c6181c178b87831860725c6e2e1e018951b8b87809c627e2e1e086141f83861b88508050ae2e1e0c61c2b8780b31850ae2e1e02746182b8b80af1850f27e2e1c6143b8b878218a86e2e1e0074886181f83878a1852ae2e1e086481a3b1c2b8b831860)
def mo495H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a02926f5e0203b898e6cbec6850ab780ba4e176195d60f00000117ba146bac8a171f00000298d9c467694007ac0008300049900000148d8463000000000571655618000006bae513b715c74002cb0006fc003b6b83220007965520000001a846000007c511d01f6400023c00388000b7c0340000046909911582a8eef309b1b3560011b8000000000000054e00184c05729ec000000054001895006606d00a062035b1009
def mo495D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc5870461c28e4b87026c431115152e0c38931097263c38310c383e4c787025c4425c38136217161c09e30e188878a970e0c518822262e2c382327203e2c09b08e223870a37160c24471c283c4490d1880b8316130507c5830a622388141c908c382362205091187046c49c80a37161c09c88e283e24d8700e2240e88921a30e202e1c580b1d12188c587027223a7223b0e2c09881c911e1c11710e352e0c31b10c343a5c18b0c61c68a8a943e0c38a31383146c23450f831618c946c18a3611a28a0f8a361c034715831618c9461a9d2c6c38310e37161c11938c343c54b870628c40d8b8b0e08c9c74f8b0c6c03464b8b0e08c28a0f8a360c23474b8b0e08c9c68e9f1618d8068f1f161c11928c2839311870628c4131423161c11939022387c58700a8c407c5870261c30a0e47161c03471420287c587026213e1c18a30e19387c5870061c3e2c3813111c3090f14288cd8b0e01450a0e17161c02531038385cd8b0e01c3e2c38098a293e2c1844461c445c58700a8c3a7238b0e01a307c5870084c362c3813111c3270e37161c04470e28705cd8b0e0205070b8b0e012988140f161c04c6111c3e2c38054623061c518410153e0c38a30e1d3e0c58430c293e0c5844461c3e2c38044618445c58700a8c3e2c38044615387901b062c24c8141f161c04c614203e6c58700e2b361c030515903e2c3806159b1601628f0f9b161142e40f8b0e0263c071fd8fae7bf3d01e2eee7754b9adc68dfd6d1b595a4ece965931d1842be35d2adb967cb075612a654d2a40504a76534497249a23f519a8a4436a0f500c7d63cc1d68e386ec35a99dcc8e6102f01650aac51f27b12fc9104582140fe07823831a28c545ae2b513f093842e1e70d8061c29211907102e411206001b8003ff21576ffd865d7ff5d975ffd845d7ff21175ffd825d7ff21d65ffd75597ff1d565ffd765d3ff21574ffd755d3ff59574ffd75593ff1d564ffc87553ff5d954ffd75553ff1d554ffd65553ff5d454ffd855cbff21572ffd755cbff61172ffc845cbff5d172ffd545cbff15172ffd8754bff21d52ffd7554bff1d552ffd8454bff21152ffd7454bff1d152ffd5454bff15152ffd7550bff1d542bfc855daff61875bfd841d6ff60875bfd87597bf5d965dfd765d2ff21574bfd861d2ff61474bfd821d2ff61d64bfc85592ff61d54bfd86553df59554fbd74552ff61c54bfd86152ff60854bfc855cb7f5d572bfd8754bfb5c952bfd8750aff61542bfc8550bef55142fed7250abf61875bbd841d6f760c75bed821d6fd60475bf9801d6fb60874
def mo495H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x69fa49000611b84f412865b3da7c4492268a9841022c6a400bc7ae410fc7ec400000074734a90780079474633f800637000000517281d904850000001b000032d98cf0299913daa6800220bc391669efb10005b63c2715e2b80030d0004858007a8b9c80000072480032f2bbca579333f000000543734e9280028dc9780000c5b1d1dc9219e114c8964a43570a00050800000070b0002a439f00012840b81b49d0293b243e78ef03d27496c409331bb338b3aab5e9100071aa1a000019fa1a075c54835230000004be8001b6b22c210ad6c80004ac00f5b9ac2f30f8fd00c3413972a823dab5a0000000115093aba0004813a58000000c58aedaf93ca188000006183a611c2a9e1b9acc8020e73d688e2a5329c1d37c384c88007c9d06f8980000080d080418a18104820321980483c2870c3818c0a3c407022420b0208000
def mo495D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c53a28601871479a182218a9a28601c61c53a28601871c52268a08473879a28601471d22218221871c52268a180728e9a28601471478228461871628601861d3222860187fc73b4974a2451c8b4421686000ffaedff5d7fe3affd65ffae9ff1d3feb27fd54ff8a9ff5cbfea97fd42
def mo495H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x121ddc62cb3ad0f0fd01f31e23180064204d804dc2201a4ea5784b324841e000048278005c112f922e348ef2ce881580019200352e3d00191eca30cb1fa705bd1b0012cc0043a368aec00000523ab8000003340010564c000afc00000372c5698800a06002601a0e51437d38b20010f84158b652000536c5954000227cb46acbf91f05f252b5b12d1821d44401ad0853010c155d
def mo495D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc20804ff
def mo495H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4aa00290000e1008b0800435590020627081
def mo495L : Nat → Packing
  | 8 => (76,4,5,0,0,9,0,mo495D8)
  | 9 => (150,3,5,0,0,12,0,mo495D9)
  | 10 => (77,2,5,0,0,13,0,mo495D10)
  | 11 => (12,1,5,0,0,9,0,mo495D11)
  | 12 => (1,0,5,0,0,0,0,mo495D12)
  | _ => emptyPacking
def mo495I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 19 113 4 11 7 0 mo495H9
  | 10 => lookupWord 37 191 7 12 8 0 mo495H10
  | 11 => lookupWord 19 97 6 11 7 0 mo495H11
  | 12 => lookupWord 3 17 4 8 4 0 mo495H12
  | _ => fun _ => none
def mo495 : Forest := ⟨1519,12,fun i => mo495Y[i]?.getD (0,0),mo495C,mo495A,mo495L,mo495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P8_0 : CutRow mo495 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P8_3 : CutRow mo495 8 3 73 := shortcutBlock (data:=fun _ => 0x3032421188862130117242118886213001f2482c960e223101f2482c960e223130324211888621301172480c860622303032421188862130302c2121904a4140303246138986213030324211888621303032461389862180249816130dc4217318524c0e830622303032421188862130303242118886213001f2482c960e22613032421188862130249812110cc421731842c924b0c84887058c292592584872058c292192584872058c292192584872303242118886213011724211888621303032460381822130303242118886214030324211888621703032421188862130303242118886212030324211888621303032421188862120249812110cc421733032421188862140303242118886218030324211888621303032421188862130249812110cc4218301f2480c860622312480f80c0e42228301f2480c86062230303242118886213030324211888621303032421188862130249812110cc42183302c2141a0524140302c2141a052414018581140a4d041843032421188862130303242118886214030324210888621303032421188862130303242118886218030324211888621203032421188862120249812110cc4218230324210888621303032421088862130303242108886213020b242118886213020b242118886213020b24211888621301172480c86062230249052110cc4217301f2482c960e222001f2482c960e227101f2482c960e22712480f82c1e4a228701f2482c960e227001f2482c960e22212480f82c1e4a228201f2482c960e222020b242118886213001f2482c960e2271) (by decide +kernel)
theorem mo495B8 : CutRow mo495 8 0 76 := (@joinRow mo495 8 0 3 73 mo495P8_0 mo495P8_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_0 : CutRow mo495 9 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_6 : CutRow mo495 9 6 56 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_62 : CutRow mo495 9 62 88 := shortcutBlock (data:=fun _ => 0x30324211888621303032421188862140303242108886214030324210888621403032421188862140303242108886214001f2482c960e224130324211888621403032421188862140302c2121904a41503032421088862140302c2905824241503032421188862140303242118886214030324210888621403032461389862140303242118886214030324211888621403032421188862140058c2925925848531858130580c50261058c2921925848832498130380c884523032421088862140303242108886214030324210888621403032421088862140303242118886214030324211888621403032421188862190303242118886213030324211888621303032421188862130249812110cc42193303242118886214030324211888621403032421088862140303242108886214001f2480c8606224101f2480c8606224101f2480c8606224130324211888621403032421188862140303242118886214030324211888621403032421088862140302c2141a0524150302c290582424150303242118886214001f81164b05d02913032421088862140303242108886214030324210888621403032421188862140303242108886214020b242118886214020b24211888621403032421088862140303242108886214030324210888621403032421088862140302c2121904a415030324211888621403032421188862140058c29058250485330324210888621403032421088862140303242118886213030324211888621303032421188862130303242118886213001f2480c86062231303242118886213020b2421188862130303242108886213020ac2121904a4140058c29259258484230324210888621303032421188862140303242108886214001f2480c8606224120b242118886214020b242118886214001f2482c960e228101f2482c960e228101f2482c960e223101f2482c960e223101f2482c960e2231) (by decide +kernel)
theorem mo495B9 : CutRow mo495 9 0 150 := (@joinRow mo495 9 0 6 144 mo495P9_0 (@joinRow mo495 9 6 56 88 mo495P9_6 mo495P9_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_0 : CutRow mo495 10 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_7 : CutRow mo495 10 7 29 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_36 : CutRow mo495 10 36 41 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B10 : CutRow mo495 10 0 77 := (@joinRow mo495 10 0 7 70 mo495P10_0 (@joinRow mo495 10 7 29 41 mo495P10_7 mo495P10_36))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P11_0 : CutRow mo495 11 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B11 : CutRow mo495 11 0 12 := mo495P11_0
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
  · exact mo495B8
  · exact mo495B9
  · exact mo495B10
  · exact mo495B11
  · exact mo495B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495G : graphValid mo495 (boundsBefore KM383) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM495 : Lower false (varsX 495) (graphGoal 495) 13 := lowerMixed (g:=mo495) (i:=0) (hints:=4831864405) (before_sound KM383 VM383) mo495G mo495T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM495 := extendKnown KM383 13 [(495,[]),(507,[16,66,134]),(509,[32,65,117]),(510,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM495 : Known false KM495 := extend_ok (m:=495) VM383 lowM495 (by decide +kernel)
theorem lowM503 : Lower false (varsX 503) (graphGoal 503) 13 := lower_down lowS503
def KM503 := extendKnown KM495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM503 : Known false KM503 := extend_ok (m:=503) VM495 lowM503 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x383e000000003c1f,0x86d56909a902436),(0x7c000f0000003e0,0x2d440235b1b156a2),(0xfc3c000,0x8dacd581646046d),(0x1f00003c0000,0x8c6031090d40463),(0x1e001f0000000,0x1bc22112704ccde1),(0x7fe000e000003ff,0x1292a94a444e8949),(0x38000000003ffc00,0x370020276129db80),(0xfffc00000,0x242512a589b13212),(0x1fff000000000,0x39dcc80e02201c)]
def mo511C : List ColumnInfo := [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13),(8,0,503,0,13),(16,0,495,0,13),(32,0,479,0,11),(128,0,383,0,11),(33,0,478,0,10),(34,0,477,0,10),(64,0,447,0,10),(132,0,379,0,10),(144,0,367,0,10),(256,0,255,0,10),(36,0,475,0,9),(40,0,471,0,9),(48,0,463,0,9),(65,0,446,0,9),(68,0,443,0,9),(72,0,439,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(258,0,253,0,9),(264,0,247,0,9),(272,0,239,0,9)]
def mo511A : List (List Nat) := [[],[16,66,134],[32,65,117],[64,33,117,134]]
def mo511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x185523cc2460c051eb750b72d9a226165c3e65bb865b3444c2cb87e8b7700b6688985970bdbae653644c2ecb2e1db754ca6c8985d965c3d6ea194d9130bb2cb87cdd3329b2261765970fcba2653644c2ecb2e1fa740ca6c8985d965
def mo511D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xf87d872997661565be3dc42997661565bc7dc72197661565be3dc42197661565be5dc32197661565be6dc22197661565be75c12197661565be79c02197661565c7f4a96c49761565ae7cca6d57661565f87d876d57661565c7edca6c8985d565c7ecca6c8985d565d76dc56c8985d565a7edc2261a65d56587fdcb6a5865d565c7f9a66c0a766065c7f9a86c0a865c65c7f9a66c0a865c65b5f9c02e19761c65c7f9c96c0a85d865a7f9c02a1975d865b5bdc669d8765065c7bcba6d98765065d7b9ca6c08765065d7b9c66c08765065b7b9c021d866506597bdca2e1766506597bdcb6a17665065e5bcca61d7665065f1bda861d7665065b55dc32e99765486b579c02e99765486b55dc32d59765486b56dc22d59765486b579c02d59765486b74dc22dd9564c86b759c02dd9564c86b5b9c42d59764086b5d9c32d59764086b5e9c22d59764086b5f1c12d59764086b739c42dd9564086b759c32dd9564086b769c22dd9564086b771c12dd9564086d65db56cca865875d4f5b76c4a865875d675b56c4a865875d6b5b46c4a865875d6d5b36c4a865875d4f9b76c0a865875d679b56c0a865875d6b9b46c0a865875d6d9b36c0a865875d6e9b26c0a865875d6f1b16c0a865875c7b9b46c1a921875c7d9b36c1a921875c7e9b26c1a921875c7f1b16c1a921875e47da7659a521875e65d96695a321875e1f99869da021875e4f9a7659a021875e37998695a021875e67996695a021875e6b996691a021875e3d99868da021875e6d99668da021875e3e998689a021875e6e996689a021875e6f196685a021875975dc52e1a664c7597d5c12e1a664c7597d9c02e1a664c7587dccb6a1a664c75e2dda86998664c75c75dba6d48664c75d55db76d48664c75c7d9ba6c08664c75d5d9b76c08664c75d759b56c08664c75d799b46c08664c75d7c9b26c08664c75d7d1b16c08664c75c5f9ba6dc8664075c779ba6d48664075d579b76d48664075c7b9ba6d08664075d5b9b76d08664075d739b56d08664075c7d9ba6cc8664075d5d9b76cc8664075d759b56cc8664075d799b46cc8664075c7e9ba6c88664075d5e9b76c88664075d769b56c88664075d7a9b46c88664075d7c9b36c88664075c7f1ba6c48664075d5f1b76c48664075d771b56c48664075d7b1b46c48664075d7d1b36c48664075d7e1b26c48664075a6edc62dda226165a76dc52dda226165a7adc42dda226165a7cdc32dda226165a7e5c12dda226165a7e9c02dda226165a5edc72d9a226165a76dc52d9a226165a7adc42d9a226165a7cdc32d9a226165a7e5c12d9a226165a7e9c02d9a226165a7e5c2261a125d65a5f5c12e5a72196587ecca6c8985d965a75dc32dca961565a76dc22dca961565a779c02dca961565c774a96c4976156597b9c02e1a76506597b9c02e17665065 else (if j<2 then 0xb779c029d8665486c7dda66cca765486d75dc56cca765486c7eda86c8a765486c7eda66c8a765486c7f9a86c0a765486c7f9a66c0a765486d779c56c0a765486d75dc96cca765486d779c96c0a765486f47dc62e99765486f55dc32e99765486f579c02e9976548697ddc96cca765486c7f9b869da564086cdf9b76d5a021975d6dda86cca865875d6f5a86c4a865875d6f9a86c0a865875c7dda86cca865875d6ddc66cca865875c7f5a86c4a865875c7f9a86c0a865875b6ddc32e19661875b6f5c12e19661875b6f9c02e19661875e7b9b46c1a921875e7d9b36c1a921875e7e9b26c1a921875e7f1b16c1a921875e67dc8659a521875a77dc9619a521875e67d96619a521875e75dc36a5a521875e76dc26a5a521875e779c06a5a521875e6ddc8659a321875a7ddc9619a321875e6dd96619a321875e7d9c06a5a321875e3f9c6661a021875e6f9c8659a021875a7f9c9619a021875e3f998619a021875e6f996619a021875e7b9c46a5a021875e7d9c36a5a021875e7e9c26a5a021875e7f1c16a5a021875e3dda86998664c75c7ddba6988664c75c7ddba6188664c75d75da66d48664c75d75d866d48664c75d75dba6d48664c75d7d9ca6c08664c75d7d9a86c08664c75d7d9a66c08664c75d7d9866c08664c75d7d9ba6c08664c75c7f9ba6188664075d5f9b76188664075d779866d48664075d7b9866d08664075d7d9866cc8664075d7e9866c88664075d7f1866c48664075a7edc62dda226165a7edc52dda226165a7edc72d9a226165c7ecb72d9a226165a7edc52d9a226165c7edb76d5a226165a77dc969da526165a7edc96dda226165af6dc52d9a226165af6dc86d5a226165cf6db76d5a226165d76dc56c89865d65d76db56c89865d65c7edca6c89825d65c7eda86c89825d65d76db56c89825d65a7f5c96e1a125d65a7f5cb261a125d65e775c5261a125d65e7e5c2261a125d65cef5b86d9a125d65e6f5986d9a125d65c7f5a96c4a661d65e5f5c12e5a721965a7ddc961da321965a7f5c96dda121965aef5c66dda121965a7f9c961da021965d4fca96dc985d9659eecca6c8985d965d6eca96c8985d965dcedc76c8985d965de6dc56c8985d965de6db56c8985d965c7edca6c8985d96597ecca6c8985d965c7ecca6c8985d965d5edc76c8985d965d6edc66c8985d965b73dc42dca961565b75dc32dca961565b76dc22dca961565b775c12dca961565b779c02dca961565d37ca96e09761565c77ca96e097615659f74ca6c49761565cf74a96c49761565d774a96c49761565db75c86c49761565de75c66c49761565e67cb92a57661565be79c02e17661565bc7dc72617661565be6dc22617661565f87dc961d7661565f87cc961d7661565f87cb961d7661565f87ca961d7661565c77dba2a57661565f87d876997661565 else 0xf801c386cf8be010003e4f8be1f808e140000000000000000000000000000000000000000000f8fe01343f8fe00443f8f62f803d881d8810011f902000047e408110411f9020002341000000e90103a5744e7dce39972ce4dc838d714e1dc23816fcdedbc3756e4dbdb63696ccd8db035d6b4d5daa35169cd2da4345684cfd9e33966cccd9832d654c9d9232163cc6d8c315624c3d8630960cc0d802fd5f4bdd7a2f15dcbad742e55c4b7d6e2d95acb4d682cd594b1d622c157caed5c2b5564abd562a954ca8d5029d534a5d4a29151ca2d442855049fd3e2794ec9cd3826d4d499d322614bc96d2c2554a493d2624948c90d2023d4748dd1a23145c8ad1422544487d0e21942c84d0820d41481d022013fc7ecfc1f53e47bcf61e93cc78cf01dd3b475cea1d139c72ce41c53846fcde1b936c6ccd81ad35469cd21a133c66ccc19532463cc618930c60cc017d2f45dcba1712dc5acb41652c457cae1592ac54ca814d29451ca214127c4ec9991c2324587d0f71e83c4770eb1d0394710df1b83646b0d31a0334650c71883045f0bb1702d4590af1582a4530a31221fc368650ba1682684a08e0e81902504407c0b81402203805803000d75dc66cca765486d779c86c0a765486d779c66c0a765486977dc72e98665486b75dc329d8665486b76dc229d8665486))
def mo511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf3000000000057e2e8000650f40000000041f500000000
def mo511D10 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then 0x65d9021bbbcdbb2ac810ddde2dd95640868ffb744c12cbac7fdb66a4865d67eed9952432eb3fe6c0a921975dafb4ed290cbae7ddb968c865d73eed4b46432ebbd7695a321975cff372d010cbaedf9b7680865d73fcd4b40432ebb7e69da021975def34ad010cbaefb9a4680865d77ecd1b40432ebbfa689a021975dfe342d010cbaf67db52a1961d7b6ed9950cb0ebdbd6c4a865875edf3605432c3ad7ddb32a1961d6bfad8950cb0eb5fe6c0a865875cfbb66d490c3ae7f9b06a4861d73becb34a430eb9df6a5a521875dafb4ed290c3af67d96694861d73eedcb46430eb9f7659a321875cfbb52d190c3af6dd9668c861d77aed2b46430eb9fe6e5a021875cff330d010c3ae7f996680861d73fcd4b40430ebcfe661a021875dbf34ed010c3af6f996680861d77bcd2b40430ebbee691a021875dfb346d010c3aefe9a2680861d77f8d0b40430eb5f72e1a664c75cfbb50d33263ad7ddba619931d73ee5d30cc98ebdb76998664c75afbb74433263ae7ddba219931d7baeda90cc98ebdf66c08664c75cff374433203af5f9b7219901d7bbcda90cc80ebdee6d08664075efb366433203af7e9b2219901d7bf8d890cc80eb1ff6d9a726165cfdb6ed1130b2e7ecb7688985973f6db3444c2cb9fb2d9a226165cfdb6ad1130b2e7ed98688985977b6dab444c2cbbdb695a226165afdb644c32eb2c7fdba26097596bf6d91304bacb9fd661a125d65cfe930d092eb2eef5b6684975972fe5cb4e432cb97f661a721965cfbb30d190cb2e7dd9768c865973f6cc344432cb9fd65da121965cff330d010cb2e7f99768086596e7edb930bb2cb7bb6c8985d965afdb644c2ecb2deddb321976596f7ad890cbb2cb7be6c0865d965cefb6e54b0ab2e77cb72a5855967be5d32ec2acb9df2a59761565cef9524bb0ab2db7db825d85596fbad892ec2acb9df2a5a661565be7b685330ab2dd7db721985596faed990cc2acb7db6c88661565bef3604330ab2ee7ca95d985597cbec3aecc2acbe3f61d76615658ffb74cc2eab2c7fdba26175596bf6d9130baacb5df2e5855d565aff36053b3032d7f9b02a1971967fcd8150bb0cb1ff6e9985d8658ff974cc2ec32f1fd9861d76196bdedb350ca0cb5ef2e1a765065af7b6cd3b2832d7bdba61d941973de5d30eca0cbcef6a18765065eb7b4ec3b2832d7bdba21d94196bdedb10eca0cb5ef6e17665065af7970bb32832f5bd875d994196baed994eca90d5db6c8a765486aef36053b2a4356ddb32a1961d6b7ad8950cb0eb5be6c0a865875ccfb2cd290c3ae6dd9668c861d71fccc340430eb9be659a0218758fbb74433263ad75db5219931d6becd810cc98eb1fe6e88664075abf36e433203ad779b5219901d6bdcda10cc80eb5f66cc8664075afd364433203ad7f1b1219901d7c3ec3aecc2acb5ee6c08765065 else (if j<2 then 0xcb7fb6c8985d965eefb6e54b0ab2f77cb72a585596fbedb952c2acb7df2e99761565def974cbb0ab2ef7ca965d85597bbe54b2ec2acbbdf2a49761565eef9524bb0ab2df7db825d85597bbe54b4cc2acb7df6dca661565befb6e4330ab2fe7dba5d985597f3e5d2ecc2acbf9f2e57661565fcf952bb30ab2fe7db85d985597f3e5c2ecc2acbf9f2617661565fcfb4ebb30ab2df7dba5d985596fbe5d2ecc2acbddf2a57661565befb70bb30ab2fd7d875d985597f3ed32ecc2acbf9f2997661565fcfb0cbb30ab2fe7c865d9855973fe5bb52c2acb9ff6dca961565cff96e54b0ab2cffcba65d855973fe54b2ec2acb9ff6a49761565cff9524bb0ab2dbfdb825d85596ffad892ec2acb9ff2a5a661565bf7b685330ab2df7db561985596efedb90cc2acb7df6d48661565bfbb664330ab2dfedb221985596ffcd810cc2acbbbf6e97661565ddf974bb30ab2eefca95d985597d7ec3aecc2acbf9f6d576615659ff974bb30ab2e7fda95d985597cfec3aecc2acbbbf6997661565cff970d4aeab2e7fdb96a1755973fe5cb50baacb3ff6d8a85d565cffb74cc2eab2e7fcba66175596bfedd130baacb5ff6dc985d565bfdb644c2eab2e7fda865d755973fe5432ebaacb5ff6e5875d565aff972c3aeab2e7fd98699755973fe4c34cbaacb3ff6e9865d5659ff974c32eab2e7fda9619755967fedd10cbaacb77f6dc865d565bf7b68432eab2dfddb321975596ff6d910cbaacb7fd6c4865d565bff360432eab2eefda85d97559777e542ecbaacbddf2e5855d565defb4cc2aeab2fe7d76615755973fed314ecc0cb9ff6dda666065cff96ed333032e7fda82a1971973fed3150cb8cbdfe6c0a865c65ebf970cbb0e32e7fda9699871979fecc34cc38cbd7f65da661c65cffb30d310e32d7fcba65d86196bfedcb0ec30cbcff6618761865ebfb2ec3b0c32d7fdb921d86196ffcd8150bb0cb5ff6e9985d865aff974cc2ec32e7fcba661761973fed4330bb0cb9ff6a1975d865cff950cbaec32f5fdb961d76197afecc30ebb0cb5ff6e5875d865e7fb30c3aec32f5fd9761d76197bdedbb50ca0cbdef2dda865065ef7b6cd432832f7bdb869d94197bde5c34eca0cbdef6d9a765065ef7b74c3b2832f7bda861d94197bded3b0eca0cbdef6d98765065ef7b5043b2832f7bda861994197bdedbb0cca0cbdef2dd8665065ef7b4ec332832f7bd8761994197bde43b0cca0cbdef6e17665065ef7970bb32832f7bda85d994197bded3aecca0cbdef61d7665065aef974c332a4357ddb329d9521abf6d914eca90d5fe6c0a765486bebb6653b2a435f6db229d9521afbcd814eca90dd5f2e99765486eafb6acbb2a43757cb565d9521b3eed3b4ac990ddd76dd9564c86eeb96ecab264357f9b869d9021abfcdc34ac810d9fe69da564086ebf36acbb204375f8b5 else 0x6ecab204367fdb56a0965d67fedb3504b2eb3ff6d5a825975affb6c4c12cbacffdba260965d6bfe5c32c4b2eb9ff6a19625975cffb6c54b0cbae7fdb52a5865d67fe5d32cc32eb9ff2a59661975cffb524b30cbae7fca9259865d73fe54b4ac32eb3ff6d9a921975cffb52cb10cbad7fcb9618865d73fed4b0c432ebbdf2e5a521975defb2cd290cbaef7d86694865d77bed4b4a432ebb7f69da521975dfbb72d190cbaefdd9668c865d77eec3346432ebbf76d5a321975dfbb52d190cbaefdda568c865d77fcdcb40432ebbfe661a021975dff36ed010cbaeff996680865d77fcc3340432ebbfe6d5a021975dff352d010cbaeff9a7680865d77fcd2b40432ebdbf6a0a865875cffb505432c3af77db52a1961d7beed9950cb0ebdfd6c4a865875eff3605432c3af6fcb8659861d7beed9b52430ebdfe6c1a921875edfb70cb10c3ad7fdb9618861d73fed4b0c430ebdbf6598621875defb0cd290c3aefdd8668c861d77fcc3340430ebdf76e1a664c75efb970d33263af7ddba619931d7beed330cc98ebdf76e88664c75efbb4c433263af7dd86219931d7bfcc310cc80eb9ff6d9a726165cff96cd3930b2e7fdb569c985973fecc34e4c2cb3ff6d9a726165defb4ed2930b2ef7da6694985977f6cc3444c2cbbfb6dda226165dfd96ed1130b2efedb6688985977f65b3444c2cbbfb6d5a226165dfdb4ed1130b2efeda668898597fb6dab444c2cbbfb695a226165cffb505432eb2f77db526197597bf6d9130cbacb7fb6c89865d659ffb6cd412eb2e7fda826097597bbeda9304bacbdfb6c89825d659ffb744c12eb2dfedb2260975977fadc3424bacbbfd661a125d65dfe930d092eb2eff5b6684975977fadab424bacb9ff6d8a961d65cffb6a54b0eb2e7fca9699875973fed494cc3acb9ff2a4a661d65bfeb625330eb2d7fcb9695875973fe54b4ac3acb7fb6c89861965cffb5253b0cb2e7fca929d865973fe5d32ec32cb7fd6c49761965affb72c3b0cb2d7fcb961d865976fe5cb4e432cbb7f661a721965dbfb6ad390cb2e7fd9869c865976fed3b2e432cb3ff6e89721965dbfb4e4b90cb2dff5b125c86596bfedcb0e432cb5ff2e58721965df7b30d210cb2efbdb7690865977decbb48432cbbef25da421965df7b6ad210cb2efdd9868c865977eecbb46432cbbf725da321965dfbb0ed190cb2efed98688865977f6cbb44432cbbfb25da221965dfeb30d090cb2eff5b7684865977facbb42432cbbfd25da121965dfeb0ed090cb2eff5b5684865977fccc340432cbbfe65da021965dff12ed010cb2eff98768086596f7edc152bb2cbbbf2e9985d965edf952cc2ecb2defcba26176597b7e54930bb2cb7bf6dc985d965f9fb6e4c2ecb2fe7db526176597f76d9130bb2cb7bf2e1a55d965cff974cc2ecb2e7fda866176596efedb930bb2)) else (if j<4 then 0x6559953654194d6529947651194164f993b64e193564c992f64b19296499923648191d64699176451911643990b642190564098ff63f18f963d98f363c18ed63a98e763918e163798db63618d563498cf63318c963198c363018bd62e98b762d18b162b98ab62a18a5628989f62718996259893624188d6229887621188161f987b61e187561c986f61b18696199863618185d61698576151851613984b6121845610983f60f183960d983360c182d60a98276091821607981b6061815604980f6031809601980360017fd5fe97f75fd17f15fb97eb5fa17e55f897df5f717d95f597d35f417cd5f297c75f117c15ef97bb5ee17b55ec97af5eb17a95e997a35e8179d5e697975e517915e3978b5e217855e0977f5df17795dd97735dc176d5da97675d917615d7975b5d617555d4974f5d317495d197435d0173d5ce97375cd17315cb972b5ca17255c8971f5c717195c597135c4170d5c297075c117015bf96fb5be16f55bc96ef5bb16e95b996e35b816dd5b696d75b516d15b396cb5b216c55b096bf5af16b95ad96b35ac16ad5aa96a75a916a15a7969b5a616955a4968f5a316895a196835a0167d59e967759d167159b966b59a1665598965f59716595959653594164d5929647591164158f963b58e163558c962f58b16295899623588161d58696175851611583960b582160558095ff57f15d9d6b958bd5815425491506538f4c15269473514342e50413f24f3f3ad4e2b36ccd2931ecc032de4b0129dc9ff25d48fd221480d1e5471d1a9463f171c54f13a445f0f5434b0b0422506b413502f4044feebf30fa53e0af5bbce4f1b3be2ed63ae0e95b9cce5538cae1037b6dcb36b4d8ab5a0d4a349ed09b3aeccdb2d0c843198c4830a8c07afa6bc72ea4b8b2db4b4f2ca0b05ab9eac0aa78a72a952a3b28749ff27609ba2670975256e934a45a8f8a36a8bca27a880a18a84020888041f867c39e8477e9d707399c6e6f49b5a6b41a58678196863c187860017885c896aa59115a854c14a650713a44cb12b4486118e445907a4008f8a3c48eac3960dce3510ccc3108bb82c70a9227d896c23888581f387441ae863016504e611703e40db02f409f0204063011402b80013ff6e89725586eefb6cd3b2a43777cba6199521bbbedbb0cca90dddf2dd8665486eefb4ec332a43777ca76199521b3fed314eca90d9ff2e98665486eefb6ac332a43777cb56199521bafe5d32eca90dddf6d59765486eef96acbb2a4377ddb56199321bbee5ab0cc990ddf76dda564c86efb96ed2b264377ddb76559321bbee5bb2ac990ddfe6e1a764086eff36ad3b204377f8b569d9021bbfcdbb0cc810ddfe2dd8664086eff36ac33204377f8b56199021bbfcdc34ac810ddfe6dda564086eff16ed2b204377f9b565d9021bbfc5ab2ec810ddfe6dd9564086eff1 else (if j<5 then 0x6793c5e1f00c98a3b1bc9e3f17848e331bc9e3f1786c0c51d8de4f1f8bc360628fe4f1f8bc229628cc662f93c7e2f0ca4716793c7e2f08c38a3b198be4f1f8bc2291c59e4f1f8bc230628fe3f17847030e28c3216793c5e1187147188b3c9e3f08c38a3f93c7e21b0c38a361bc9e1f17821c6c1cd869f278bc3e01b0d85f278bc3e01b0de4f1787c08e1bc9e1f17811c2e14d869c303bc9a3f1787c0561bc9e2f0f80d2361bc9e2f0f80d2361b0be4f1784d2361b0be4f1f8bc2691fc9e3f17870e69190f86f278fc5e1348f86f1f8bc387348d86f278bc387348d86f278fc387348d86f278fc587348d0c0299bc3e4f1f83c443258b0cf1f87c1e41fc9e1f1f82c4e61a18e662f93c3e3b1780808f8fc3e0f218992384618c973793c762f0f80973792c5e3f0f80608f8fc362f00a2cf278ec5e1f00c0cf278fc2e2f00c0953017c9e3f1787c04793c7e1f06174c349bc9e2b0f8fc03051932662f93c7e2f01126f1f8bc0481412c5f278fc5e1f0118823793c5e3f0f80663793c512f0f80606792c7e1f1780663792c5e3f0f80606107c9e3f1780663793c5e3f0d80606793c7e18878860489bc9e1f1f8bc03f91c5e1c2f8fc03617c24cf278fc0361bc9e109617c5e01f0de4c2f8fc5e01b0de4f0e17c610f10e098678fc9e2f0f807f278fc5e1f0215cc3833c809f1f8bc3e01c19e4f1f87c5e01813e4f1f8bc3e082d988f278bc666f0f806f2789c2343378fc03d9bc9e2f1f87c03393c5e324f87c03793c5e324f87c03793c4e324f87c03791c5e324f87c03793c5e324f85c03793c305f1f8bc0378fc5e4f0f805f1f87c1e4f16146f278fc5e1f00a4c04a9bc7e4f1787c0462499e3f2787c03027c7e4f1787c04c1f1266f278fc5e1438f89f278fc5e1438c2cf278fc5e1e28c05f0f83c9e3f10c0903793c7e2f0f828a4227c3e0f1b17c9e21ccd85f1787c1e31b49e3f0f801fe2159b083678fc3e0c2f88604e17c7e2f0f806c4f83c7e2f0a3c6d278bc7e1478be3f0f891e203cd9e0f1f8bc22b1fc185d278fc5e1448f85f0f8349e3f10d85f1f8bc3e0849b07d2787c185f1c27c43e3312e333793c5e1f0118cc4f93c7e1f01a87c6625c066f278fc5e121c786c2f93c5e1f00ee1c3617c9e3f178077061b0be4f1f8bc239158de4f1f8bc3e01ec6c662f93c5e1f00f6063317c9e3f17847b03198be4f1f8bc239b0d386c2f93c5e1f0106c34e8d0b86f278bc3e0271ce0c3617c9e2f08f86f278fc5e1438c86f278fc5e1c38d86f278fc5e1438ce4c378fc5e1c38ce3c3793c5e1c38ce2c3793c7e1c38ce1c3793c7e2c38de3f278bc3e017498f70624cd85f1f8bc24e7219c567099bf66f19b966d99b366c19ad66a99a766919a1667999b6661995664998f66319896619983660197d65e997765d197165b996b65a1965658995f6571959 else 0x19bc9e3f1787c0251ceb8cc4b8ccde4f1787c04e3313e4f1f87c06a1ce78cc4b80cde4f1f8bc2499bc9e2f0f83123793c7e1f01ab12319bc9e3f178712343213e4f1f8bc3e01e1909f1f93c5e1f00f0c84f93c7e2f0f814a4198cbe4f1787c01709110c84e8fc9e2f0f80786793c5e1f0449cc3997c5e18878fc8319bc9e3f1443c2319bc9e3f1784ca101e1909f1f93c5e1d00f0cf278fc5e18839478678fc9e2f0c40686793c7e2f0c41cc3830120602f93c7e2f0f80906793c7e1f17806160a5c7e4f1787c038b3c7e4f17846030b3c7e4f1787c0291c6e32f278bc3e0185829b1f93c5e1f00e2cf278bc3e0190c0c18793c7e2f08de3f0d83c9e2180c2cf1f93c5e1180c2cf1f93c5e1180c2cf1f93c5e1180de3f1784703014642cf278bc2301859e318f93c2301bc7e4f10d8602e1bc9e3f1787c06c1f0d85f278bc3e0360f86c2f93c7e2f01b07c3617c9e3f1784d839ddc786f278bc3e0c29186f278fc5e0440d86f278fc5e1438d45f278bc3e0a30d46f278fc5e1a28cc6f278fc5e1f0114714f93c7e2f0f818c38b053e4f1f8bc3e0a290c6f278fc5e1f00a47633146fe4f1787c032218de4b1f8bc3e0628fe4f1787c029628cc662f93c5e1f00a471)))
def mo511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81e23725a549c41eb2e420d292000083c485c00008430e26236c38aa0000432f400c21940fcc8b5c3cf27cc068807e06180870000a1d3c07823bd0bd423800068b0d07b68dc480184ca406490540460933097094907d8000b13521bf213c88c58bc61b1617f025e1bec13842baaa3c10550fc53c8a86f12dc3900187024b001a21a444f8f3a117f06c80de07f81c5602905230eaa4ea51750220000c13e0000434c86710faa1000001884306ed889b20780d01ba009a979c88501e8c97541f0e2f68bfc361626000095b12b91a28b8e1e1514411611ac45406d200a8529012b173e339e354e5621b44869650800060a200038290000000080ac00060b23176439e062e83f617e000000018f7c1a48188029b06ee0d0ab3a00ca033805f812a050902730e6c0e517f0000113682c6821190280300001c238000ec53c3268268000100f68bf0748000dc5da0ea620c0b4c016000042b705db13b50e8857289ec82aa89e80d00f6f1c6e2fb47f207071d7908b86c88fa20b5ea88d2ac0f2f0c60003c04cc4ab1dce3344329242211bc2f0009f0200059085916698f809b1f13733ea83119e61393c08727d910018734233458f451625d0396c5c5076aa5605d2c316838000304cf8ec185ce2de05ae00e40534352880b8db1189e033d422028e8f4a32ba1b18c061ab5897467f81c9144000250ba0d0983e21ec85680006c76634642cb90521a7a1c6d50dc7d7183589163ff848fcbe3a9bb22fa45814023b5830caddc0ee715d44a547b94b6e3fdc19101de15963a000018c7486940a9c7ea864802cc31b81c28a310b1a40c20f50f0ec46e04463e7223c0ab62ac83d041d7911abd4b2c308fc0ec4244024aa158901e2cfc36c09c31aeb20411f40e62042a014b1e28f540b8a323c6e2a21902aa205141e8bd5905c9ee87cfcddb15e80ba42a725c2044c29c26f206a40cdc143f2ca0a9c1f80002072944941dfc10d016825f9198a1d5022800038a0e30942ff04f000022db02d80002cccc20c00030141c4c000006f1003a5b9635918298e04047e0d5a148000840801ad8307435d00c607ab79be27d529822ab0ba017a079496b002389000020860b033c810009903c44170a83c1c06082b00e04a9040201c000405a074b0b856003c8080a140422c7a3b1b19c4a003e01c0202050100002060040200250d00202028201c7a048041e020789c48460207014000186050cb018140400002640000019c43003018040002
def mo511D11 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x7ffd9761565fff25d85597ffda661565fff29985597ffd8661565fff21985597ffd7661565fff2a575597ffda85d565fff2a175597ffd985d565fff26175597ffd875d565fff69975597ffca65d565fff61975597ffc865d565fff5d975597ffda661c65fff69d86197ffca761865fff61d86197ffc8761865fff6a176197ffca85d865fff61d76197ffd8761965dff65d9561affda725586dff65c9561b7fc9725586dff69d9521b7fca765486dff6199521bf7da765486fdf29d9521b7fd9765486bff2a1965d77fd9865975bff6a0965d77fd9825975dff260965d77fd9625975bff6a5865d77fda961975bff2a5865d77fca961975bff6a4865d77fda921975bff2a4865d6ffda521975fdf694865d7fdda321975ffe680865d77fda865875dff2a1961d77fda961875dff659861d77fda921875dff658861d7f7da521875ff768c861d7ff9a021875dff69d985977fca766165dff66098596ffda726165fdf69498597feda226165dff6a1975977fca865d65bff2a1975977fd9865d65dff26197596ffda825d65dff660975977fc9825d65dff6a5875977fca961d65dff661865977fd9761965dff66086596ffda721965dff65c86597efca95d965fbf66176597efc985d965fbf695765977fd985d965dff26176597efd865d965fbf21976597f7ca961565fdf65d85597f7c9761565fdf69985597f7ca661565fdf61985597f7c8661565fdf5d9855977fca961565bff69985597efd7661565bff6a175596ffca85d565dff661755977fc985d565dff65d75596ffda65d565fbf5d975597f7d855d565dff69d981977fca766065dff6a1971977fca865c65dff6a5871977fd9861c65dff65d87196ffda621c65dff661861977fd9761865bff6a176196ffca85d865dff661761977fd975d865f7f61d7619777da765486ddf29d9521b77d8665486d7f65d9521b7dd8664c86df76959321b7dd9564c86dfe69d9021b7f98664086dfe6959021b7f99764086dfe6559021a7fda8259759ff2a5865d67fda921975bdf694865d6fdda321975bfe680865d76fda865875dbf2a1961d67fda961875dbf659861d67fda921875dbf658861d6f7da521875bf768c861d6ff9a021875df7699931d77dd8664c75df7219931d77f98664075dfe219901d67fda726165bfb68898596ff5a125d659ff6a5875967fca961d65b7f69c86596fbda421965bf768c86596feda221965bfd68486596ff9a021965ddf2a585597e7d76615659ff6a5855967fca9615659ff6a5755967fda6660659ff6a5871973fd9861c65d7f65d871967fda921c65def6a1941977bda765065def61d941977bc8765065def619941977bd7665065d5f65d9521b75d9564c86d7e65d9021b7799564086dee6519021b7d99364086dfa6499021b7f191640869fb6889859677ca961565 else 0x9024e38f8b87809c6c52ce4e2e1e012231b14b3938f8780448c6c5610936e4e3e2e0271b14b3938f8b844080c49e2e4e3e0e11c159b938f8b878072c064985e4e2e3e1e024183027938f8b87821490c492685e4e3e1e2e02418302617938b87838c9a64945e0e3e2e1e4229927838f8b87911480649e0e3e2e1e44521249b938f8b878114866a489e2e0e3e10f219a278f8783883c70f66a48f8985e0e3e2e129b292178f8b8781988668f09a485e2e1e0e3263c259a9217878f838890c09e4e3e2e1e01c33938b87804860ce4e3e2e1101833938f8b84406e3e2e11810144833938b84406110ce4e3e1101b938f8858405c50ce4e3e1e0183027938f8b87807baaaea4ba7ae98ba4ae8cba1ae80b9eae74b9bae68b98ae5cb95ae50b92ae44b8fae38b8cae2cb89ae20b86ae14b83ae08b80adfcb7dadf0b7aade4b77add8b74adccb71adc0b6eadb4b6bada8b68ad9cb65ad90b62ad84b5fad78b5cad6cb59ad60b56ad54b53ad48b50ad3cb4dad30b4aad24b47ad18b44ad0cb41ad00b3eacf4b3bace8b38acdcb35acd0b32acc4b2facb8b2cacacb29ac78b0eabecaedab78accaadca9faa40a7ea99ca59a928a38a894a0da7f09f0a7849cda6d89a6a65c983a5c0960a54c945a4d8926a45c905a3d08e2a3448bfa2b88a0a24c881a1b085ea144845a0d0822a04c7ff9fb87de9f2c7bd9ea07989e1c7779d887529d0c7339c887149c0c6ef9b706ca9ae46ab9a7068e99fc66b997864a98f462d987860c97e45e797585c696dc5a7965058295c4561954054094b451994204f893944d793184b2928c4939208470917c44d90f042a90644058fd03e28f443bf8eb83968e1436f8d7834c8cf432d8c7830e8bf42ed8b782ce8afc2b18a8028c89fc271897824e88f422d885820487c41df87381ba86a41998628176858c14f84f012a846410783d80e483540bf82b809a821c07781a805c813c04380d8028807400f8000fff69d9561bffca765586fff65d9561bffd9725586fff25c9561bffda561886fff2958621bffda765486fff29d9521bffda865975fff2a1965d7ffd9865975fff6a0965d7ffd9825975fff260965d7ffd9625975fff694965d7ffda961975fff2a5865d7ffd9661975fff259865d7ffda561975fff6a4865d7ffd9621975fff618865d7ffda521975fff618861d7ffda766165fff29d98597ffd9826165fff69c98597ffda626165fff69498597ffda865d65fff2a197597ffd9865d65fff26197597ffd9825d65fff26097597ffda961d65fff2a587597ffda661d65fff29987597ffda561d65fff2a586597ffc9861965fff69d86597ffca761965fff65d86597ffc9761965fff69586597ffd9821965fff65c86597ffc9721965fff61c86597ffca95d965fff66176597ffc985d965fff61976597ffda55d965fff2a58559) else (if j<3 then 0xa48e3e4e2e1e0171b17938b87838c72c290605e3e4e2e1e027191b14302517938b87838cb2c29e3e4e2e1e01cb38f938b8780a472c0605e3e4e2e1e0292430241b938f8b87811492ce3e4e2e1e0291cb3938b8780c862ce3e4e2e1301a1793861b8b838c786e4e3e2e1e0851d1917938b87838c70c46e4e1e2e0e345211b938f8b878114a484645e4e3e2e1e02920b3938f8b8780a71882cc6e4e2e1e032c520b31b938f8b84c314866e4e2e3e1e01b938b8f87819866685e4e2e3e1e02c20b02598149b938b8f8780ae4e3e2e1e02c198b938f8780b06e4e3e1e2e015249917938f878b808a626e4e3e2e1e02c20b09b938f8b878070c492645e4e3e1e2e02424149b938f8b8780885e4e2e3e1e0a61d261517938f8b8782989c5e0e3e2e1e4192714301917838f8b8790a4645e4e2e1e0e31c9a143393878f8b80846e4e2e3e1e0891f14b025189b938f8b8780a0ce4e3e1e2e0891c9b9385178f8b8078526e4e2e1e3e01c9a151793878f8b80845e4e1e3e2e018b2141b93878b8f808850945e1e4e3e0e24c261a14991793878f8b8098685e4e1e3e2e0092198b127938f8b878082ce4e3e2e1e01817938b8f878198766e4e2e3e1e01817938b8f87812470c660905e4e2e1e3e027938b8f87812462c660509e4e3e1e2e027938f8b83861462c26e4e2e3e1e01c9b938f8b87821474c8609e3e2e4e1e0221817909b8f8b8780b092c8906e4e2e3e1e02226178f938b87813084c49e3e4e1e2e01cb09b938f878b80726e4e3e185e2e01cb226189b938f8b87809668985e2e0e3e1e42227938f8b8782159888985e3e1e0e4e21c9a27938f8b878214849e045e3e2e1e41c3299278b838f87911490c09e3e1e0e226e445249b1783938f8b852480945e2e0e4e1e31c30249917938b87838c9e1e0e4e3e2c51b17938f8b8780b22482c060945e1e4e3e0e2249917938f8783887c5e1e0e3e4e2891d9a32278f938b878088c89e4e3e2e1e06621983027938b87838c8a50c09e4e3e2e1e021999433938b87804886665e4e217e1e01221999433938b87804886665a08ce1e4e3e21025999433938b878c40866658ce4e3e2e11021999433938f8b8440866650ce4e3e2e110231b142793878f8b80806050c09c6c5e4e3e2e1e02f14b0a78f938b8780809c6062c29e3e4e2e1e02b158cb0cb938b87808c5602c30e3e4e2e1221a17938b87838c78685e4e3e2e1e01d151b938b87838c746e4e2e1e0e3451c251b938f8b87811484645e4e3e2e1e01d17938f8b878318763c6e4e2e1e0c51d831b938f8b8714786e4e1e2e00e183a3a1a17938b878080e6c698685e4e2e1e0261b938b878e1c686e4e3e2e18718259b14338b938f878092cc562e4e3e1e01f1584d09b938f8b808a6c5e4e3e2e1e01c181430269b17938f8b8780bc52c09e4e3e2e1e0231b15 else 0x9a15928f0052625e4e2e1e0e31c30259897938b87838c9e1e0e4e3e2a51b938f8b87819a947668c89e4e3e2e1e02232242497938f8b878198a8666850c0925e4e2e1e0e32e338f938b87822478ce4e3e2e1e08966219a9498943027938f8b8780be3e4e2e1e02c18b0a78f938b87807290605e4e3e1e2e020b0261a178f8b83938490c8646854509e4e3e2e1e02e1a17938f878b8))
def mo511H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xa4836400000001859831e0003cf38000304948c1cf1800020186546fb5e0aa80ac00000004a06722483c40000000925fd331d95800001b9531a034b15912b8a42000001c90a36c3e00bc0000000000038aa69890000d320e2f80c426ca00008bdcb3730f1b6d021d80000001429800072645084000308018d3b0c480600ad348941279be056f1c42b81493df99648a7418d34fdca64063a046e68b0b6a26b502759fb8070000d9d060c3aaf08b5000184604baeda4b9d6a72ec26f15723730224c494484c0a76c5fc1d8000653133a73a10000835c000397e8000b35405fc00031b752684b4400008310000f6c886da939e3360002ae30c94232003a24c6b916a015262d417e8d250b00003006d8e921bb29eb475c943000127800006128a173431c14b000002b00002c2822ebb30d13d0ae70000b1424aa32127ae0108c008949161c2bc11e52693e91e8964754850db1835000062d12888040c104a795c87aa375e8e04fc000000000014834de012e9b0a5c406a3e30e0bbc9e9ccce7e96f000000038b700007024c5b18ce0000424e39bff4dd8678165af1c0002950738b21f1ca700007284433f8648000e88b083b7b35eec11bf09800007805000023e8000000000000001043e6fd220802facecf30b04b000000000000307e997a4a28000c294000204a68f72a2ee431056c4de000151bf0813021b1c36c4440f68d1e3cd39c2c5ef9dd631c773202f0c3d711c0001cba62457bc4c55800071ca28bdea95cc4449b976c653f016faf81a24000105d00007003511f4379cc7b12f626e4150000000000028dd385d0512000146500008007a1100005099c0da000242ad4ee52a5eb260f83f56d050000000031bdc1ea0001d1770650000447f01000003ed40d9b4ec627ef17fec1a860800000000002092800070fcb00e04f118321ab03ce63ad43ce15fa8bdc21d11be232c454a37398559d96912cb4be05000000000002845129000008b45ca200000000000096643ae00038d800006140000301e6f5393c8000203aa9d400011b5958fd0a8978b1b9dc7800000000a0d8000300440dd3a34caed86103b883026f0da5ddd19041945149b8f428c5e908a38ecd410c7bc602110a327d874640b112e9a3dabb38a38881f33aac80b022b325785b49390168ae04090b2e0640102bc92b0606001a0001082e2d180a14071f1609250a00831402d00329000302195a06110b2d000d0602002a00720c0100011b1e080b01020c1300295c210a020e0701140b0007022302163f0206031402002b1002060513110c090201081201250503010e0625070f010504100202000437340a0b05052d0d060e0010000229241d28150303000302000b221325000113000100220004090005000b071a1300020403011e3f0012080a02170e140f0909491c1222020402 else 0x204c7010a3ee80d0000211e00038d2acc4920bec5b2309e09000184f40003246b022e629c1f3480ed29039ea8110ee234e052cf7310475386609bcf1798038fac3c9852a057f0eca6c64ca4885bf400e554af3874c2656be58cae11d191bd3fdc86d1db925b3db7a07907d40a9c60603fcb0f016663d16460000100430400005165027728108cc886408fd64c0000180065bea738000408cd01e0003204a907311ae22cb38fbcbccbee500cb9f0791532a0a64e9800002efa6446728000635600018139a6d00000000ce6b81bba0004d4000584182d46040000485152fd2d18000687011ca5477804f891899a80ac0004080a5c866ef40bd8d761b5ea500004acc3cb00001d7f89c490d030e124801232a7bc90c064096331c64314c1d0c08e0e7075787c899e09f86242c9b0000802971c50b8000000000000a8a5964b4e000e0419183d03d4c7308d9ca76d9cdc66a405f9bfa240d4585820000e3a0d6e002e01820000a1b184ed82cd2e57dbe86c9f6ce24240e54ade8710000e0540001e9af695e7a4000000090ef49e00000000000142e20250000f26344dfc733ad0000142d8000212c81bd0272d8132e67d84212d06a0b05b2f97dc0735af5fe234c6a0cd633e92da0e83fef191d6e09d6c0fc6b18952186445f83560b1c37ccc640000000003ac8244a9f439921d4779088592b0001216b9e1800000016fbccd21d1c9b469308000000011df658b842787af32f06800001aa9d2cfe3b400061c80001c5f50580000c2700002516d5c168b4d69b5d031269890a580c664161816f6a340005481f517c6b6196800001ec00001533866facc464a32e5929e3c2c7b4000232972f24bf86432cfec2aa00010ed68e20000b044a7b19b4a2e200034a0a9a6a8d60000043219685dc640f24d48fc0001217fd970000490701ee8c3f25fa1b126bdf06bef90000e16da12881c2069e0cf509b92a614781af339cc2c705d6392865d096206e516f84c74fd000184e88afa9460000c01e427e9d2f4b223394cfa65b9134e3a80003b28b3460003eafd1b55cc000034e02a71000000015c9c0bc0000a53444528c20001b48b0d4e1eb946600014034819e24826f20f600000000101c0000b33d2ed277e21730830000581c0000000e3096be800059930001e719ca27ee9b1566120775ac7208f5a09789e509f83dd696e0898000609362b191c38bbc1fd04cd884abbf2b41a2a640f9ee8778800034cc398c08180003a303872dd132eec00078d033826472ce38060b23d51128d08000a11000014888)
def mo511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1325c98b0e0c63e4c5870634a3264a33262c3831892532519931e2c3804931a2e3c9871601e3050d154e3c98b0e0286098d17262c3831922434558a71e4c5870151b262c3831c51e364c78b0e08a3a68b93163c380712982c559931e2c380a8a9b263c38b00f142e4c78b0e04c40c129a2e3c587260246464c242c5c987163c05c68ab3263c587009244860a9a2e4c38f160286098c982e4c78b0e0284860a9b263c5870129a4e0c78b0e48a449c98f161c09a290984e4c5870638a4261387263c18a290192851827263c58701433263c5870091c664c58701218664c78b0901a3060b17263c587009286060b931e2c38080d17262c78700e162e4c78b0e01840c4d17263c38b010193058b930e3c5809c98b1e1c02861217263c587010313061217263c587014304e4c78b0e01d18c2593161c03a01843263c58470c17263c58700e38305c98b0e01c364c78b0871920f12171e2c3808a7fa4fa0a9c598e9428fd8b187a84380c7c078974b7066b366e6225d65915535154d749944d4163e63b636a32c2f52b727923420b1cd18114a1130dc0a506e03e000ffecab0dffc9561bffb0c437ff65486ffecb2ebffc965d7ffb0cbafff21975ffec30ebffc861d7ffb30b2fff26165ffecbacbffc97597ffb0eb2fff61965ffe432cbffd76597ffb0ab2fff5d565ffec38cbffc87197ffb0c32fff5d865bfeca90df7d9521bfbb26437fe64086bfe4b2eb7fd961d6ffb30b2dff26165bfecbacbefd76597efb0ab2dff66065bfecb8cb77d9521afbb26435fe64086b7ecb0eb7dd931d6ff3203adef65065
def mo511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c6d1863d2983526b252558ee0003c7ec08882700014c93592421326903b5dc086a906dc1511a2e694ad68ca00010ec022b15ac1437d5c1958e010d8cb852c6c49a113aa90000000200f1ec63055b3dbbc87330f5165721ef1e236500e118066ce0134f252ce03e0048000d3563d6938c8ddd368b8daaf24e700005195aae46eb3960f8dcf3c7000018b4334c93c53c208c66e6075325e02a106562c00020fbb203ac7a2a37a92029c4370a34304e11a256eb400038d4457b24fcce3668afaa2c163f95880f9e07382eeacf84dc3a9deb8a85861f05d05aa87f8d1c226cc3202db5b7634000418d3b0617c000904086210514f7db99cdf0003c8f8154000fad2842eabc7d123f8f07861d95c104d4fda22c000d970000000245996116d0d2440000002e080001439908c000e160000f3ac047f9c75f2a0b43ba1218000ca36029913000012d804b00034deb9aa0380000000e2e400022b94a4b89a30c0000000a07400081d97b200000000002c32f116106debf96af20a91d0001e3c4ccdc000920841952e07c00028a3000066d63cce1dea10053e265374e904c77000247b0002e49032c000000042447080000000000c3080003706007d6248a7013db2a12f475a157bc2fe9194e49063caa000000000000001178000226c0000003431823a0db0002a7023d4000ad2730494ccc400001c1a728a8d61c94cdc83c4000fa400005310435d81c000000095fd15000096fc0006c7c0005496885e034c7d8330000aecc7d000010baf006d2a533c8c6f39b52da574000430000062f000022fd8be30b0cd7f914000ebaa0bb746f8ffbee40009015c64a284f3a000050400000e223400004dd5af90000000f251e3e0003e5f902000023480006c9b048e8cf4c708a901f024b04e0871852000280c000282000024a0a49baae84e74cd5237b45a16e49cf0fc000f31586f21584fae5bcc1170966fc53f0000d25800000f3cabaaa8000d73492fb2a6e56256ec83fb19c16b2b74f6729ae59e1e70660000c4681ae4ed51b37ae2a3e834e279a04721189f91ea00fe1c40006b44c4aa177467d22000006cb037c2d5cc8a3a48ef35ca07f0003f1d3147642000245c336234c33d20b72294000e00a49dc0ac0e87463cafc09a1e800008e10002c7262b18062025c696a944b221e31ba40e87d44a1948160ce4745078490d8e85bcb2600003c140216272100070000150002020b010c041c041009000104280a0627200d22260d0c34061f00029d1a180000010b0404002c03011000011101031109090f001a083a16040022020806060b041e120430003802131a0200080603060f000416030901
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1859228608c71853099238a18091858e48a18071a48e28601471859238a18072648e2860147fcc090603000ffd86ffc86ffd75ffc75ffd65ffc65
def mo511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xad7b12000429000c2b000d21bd02dbfd839460be23000b13a4e40551b21800029000600031ed4100000061429b000a92204f98f86000708d161240009557840c420200c64bd103dc000e2288d0005034abd81f2a61c00000010f743007a6610d00081531fc19000b5c5500007580a810992631a62839c24fc2041d30a125faaa5bf27e0160e617e67a44395011593ad58c18011805929078ce680001003012003
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20c4100bff
def mo511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe0002a36994216a1840000143a22c8000198f18050
def mo511L : Nat → Packing
  | 8 => (9,6,5,0,0,6,0,mo511D8)
  | 9 => (262,5,5,0,0,11,0,mo511D9)
  | 10 => (497,4,5,0,0,14,0,mo511D10)
  | 11 => (256,3,5,0,0,14,0,mo511D11)
  | 12 => (44,2,5,0,0,12,0,mo511D12)
  | 13 => (6,1,5,0,0,8,0,mo511D13)
  | 14 => (1,0,5,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 23 0 8 4 0 mo511H9
  | 10 => lookupWord 96 419 9 15 9 2 mo511H10
  | 11 => lookupWord 190 937 8 15 9 2 mo511H11
  | 12 => lookupWord 99 491 8 14 8 2 mo511H12
  | 13 => lookupWord 20 97 6 12 6 2 mo511H13
  | 14 => lookupWord 3 17 5 9 3 2 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 9 := shortcutBlock (data:=fun _ => 0x30324211888625303032421188862530249812111cc4257330324211888625403032421188862580303242118886253030324211888625303032421188862530249812110cc42583) (by decide +kernel)
theorem mo511B8 : CutRow mo511 8 0 9 := mo511P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_96 : CutRow mo511 9 96 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_97 : CutRow mo511 9 97 96 := shortcutBlock (data:=fun _ => 0x249812110cc42173249812110cc42173249812110cc42173249812110cc421733032421188862140302c2121904a415030324211888621403032421188862540302c2121904a415003f2482c960e224130324211888621803032421188862140078c29259258484203f248088606227103f2482c960e227130324211888621903032421188862190303242118886214030324211888621403032421188862190303242118886214030324211888621403032421188862190303242118886213003ec241b0d0e44713032421188862140303242118886214030324211888621403032421188862140303242118886214003ec240b050a4471249812110cc421843032421188862150116c2c0b071248723032421188862140078c29261258487203f2482c960e2261078c29259258487230324211888621403032421188862540303242118886214030324211888621403032421188862140302c2121904a4140302c2121904a4140302c2121904a4140302c2121904a41401858112094c84194302c2121904a41503032421188862190078c290582504a42078c290582504842302c2121904a4140078c29058250484203ec2c0c870a44613032421188862180116c280c86124862116c280886124863116c280886124862116c280c86124853116c2808861248530e0c229348e5e086078c2907825048733032421188862180078c282e161a4873116c280c86124853116c280c86124863116c280c86124863116c280c861248631848b80c26424896116c280c86124862116c280c86124862116c280c86124862302c2121904a4150078c290582504883078c29078250487330324613898621403032421188862140303246138986219030324211888621403032421188862150249812110cc42184249812110c442184249812110cc42184249812110c4421941852480c86062240249812110c442194303242108886214030324291c8a631400e1812914ce421830e1812110c442183249812110c4421933032421088862140303242108886214030324291c8a631403032421088862140) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_193 : CutRow mo511 9 193 69 := shortcutBlock (data:=fun _ => 0x30324211888621701852480c860622700e1812110cc42187303242108886218030324211888621703032421188862170249812110cc421971843c904a2c04885302c2121904a4140302c2121904a4150078c2905825048521858112094c84185078c2905825048521172480c8606227030324211888621701852480c8606227030324211888621603032421188862160249812110cc42196302c2121904a41501172480c8606224011724c0e8706224030324211888621403032421188862140249812110cc42184303242118886214030324211888621403032421188862140249812110cc4218430324211888621403032421188862140249812110cc42194249812110cc42183249812110cc42183249812110cc42183249812110cc4218330324211888621703032421188862180303242118886217030324211888621703032421188862170249812110cc42197303242118886214030324211888621403032421188862140249812110cc42193249812110cc42174249812110cc42174249812110cc42184249812110cc42174249812110cc42174249812110cc42173249812110cc42173249812110cc42173249812110cc421733032421188862140303242118886214030324211888621403032421188862180303242118886218030324211888621801852480c86062230249812110cc42183249812110cc42183249812110cc42183249812110cc42183249812110cc42194249812110cc421743032421188862187) (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 262 := (@joinRow mo511 9 0 97 165 (@joinRow mo511 9 0 96 1 mo511P9_0 mo511P9_96) (@joinRow mo511 9 97 96 69 mo511P9_97 mo511P9_193))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 22 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_22 : CutRow mo511 10 22 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_118 : CutRow mo511 10 118 54 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_172 : CutRow mo511 10 172 96 := shortcutBlock (data:=fun _ => 0x78c292112584853078c290582504853078c292192584863078c2905825048531843c924b0c848a5078c292592584852078c292192584852078c290582504893078c292112584893078c290582504893078c290582504893078c290582504893078c29211258486330324211888621500798130700d108a3078c29058250489330324211888621503032461389862150302c2121904a41602498130380c884723032421188862150303246138986215030324613898621503032461389862150078c292592584852303246138986215030324211888621503032461389862150303246138986215030324211888621503032421188862150078c290582504863078c2905825048633032421188862150078c290582504863078c292192584863078c2921925848531843c924b0c848a5078c292592584852078c292192584852078c292192584852078c290582504893078c290582504893302c2121904a4150078c290582504853078c2905825048a330324211888621503032421188862150303242118886215030324210888621503032421188862150249812110c4421a43032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150249812110c4421a4303242118886215030324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_268 : CutRow mo511 10 268 96 := shortcutBlock (data:=fun _ => 0x78c292192584852302c2121904a416030324613898621503032430191c084a63032421188862150303242118886215030324211888621502498138240e8846130324211888621503032421188862150078c292192584863078c292192584863078c2921925848633032421188862150078c292192584863078c292192584863078c292192584863078c29219258485230324211888621503032421188862150078c292192584853078c292192584853078c292192584853078c292192584853078c2921925848531843c924b0c848951843c924b0c848951843c924b0c848951843c924b0c84895078c292592584852078c292592584852078c292592584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c2921925848520e0c229348e4e065078c2905825048a33032421188862150078c2921925848933032421188862150078c290582504893078c290782504883078c290582504883078c292592584882078c290582504893303242118886215030324211888621500e0c229348e4a0a50e0c229348e4a064302c2121904a4150302c2121904a4150078c290582504853078c290582504853078c290582504853078c290582504853302c2121904a4150078c290582504853302c2121904a4150078c290582504853302c2121904a4150078c292112584853078c292192584853116c280c86124873116c280c8612487318470291c9a4e085078c290582504893116c280c86124873116c280c86124873116c280886124873116c280c86124873078c290582504853078c292112584853116c2c0b071248532498130380c884622498182e164aa097078c290582504893116c280c8612487318470291c9a4a085116c280c861248733032421188862150302c2121904a4160302c2121904a4160078c290582504863302c2121904a41603032421188862150302c2121904a4160078c290582504863078c290582504852302c2121904a4160) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_364 : CutRow mo511 10 364 96 := shortcutBlock (data:=fun _ => 0x303242108886215030324613898621503032421088862150303242108886215030324210888621503032461389862150303246138986215030324210888621503032421088862150303242108886215030324210888621503032461389862150303246138986215030324210888621503032461389862150302c2121904a4150303246138986219030324613898621903032461389862190302c2121904a4160303246138986214030324613898621403032461389862140302c2121904a41503032461389862140302c2121904a4150249816130dc42194249816130dc4219418524c0e87062240249816130dc42194249816130dc4219411724c0e87062240249816130dc42194249816130dc421941858112094c841953032421188862150303242118886215030324211888621a030324211888621403032421188862140249812110cc421a430324211888621503032421188862140249812110cc421a4303242118886215030324211888621503032421188862150303242118886215030324211888621903032421188862140249812110cc421943032421188862140303242118886214030324211888621403032421188862140303242118886214030324211888621403032421188862140249812110cc4218430324211888621503032421188862150303246138986215030324211888621502498130380c88472078c2905825048532498130380c88462078c292592584852078c292592584852078c292592584852078c2925925848520e18192692689063078c292592584852078c2925925848523032430191c0849603f24828960e2271078c292592584852303242118886215030324211888621a03032421188862140078c2925925848522498130380c88472303242118886215030324211888621a03032421188862140078c290582504863078c292592584852078c290582504852078c290582504852078c2905825048522498138240e88461078c2905825048523032421188862150302c2121904a4160303242118886215030324211888621503032421188862150) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_460 : CutRow mo511 10 460 37 := shortcutBlock (data:=fun _ => 0x3032421088862150303246138986218030324210888621803032421188862180303242118886218030324613898621803032421188862180078c290582504863303242108886215030324211888621803032421088862180302c2121904a41603032461389862180303242118886218030324211888621403032421088862140302c2121904a4150302c2121904a4150302c2121904a4150302c2121904a41501852480c860622401852480c86062240248c241b0d0e4451249812110cc42184249812110cc42184249812110cc42184249812110c4421841172480c860622401172480c860622401172480c86062240249816130dc42184249812110cc421841858112094c841851858112094c84185303246138986215030324613898621503032461389862150) (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 497 := (@joinRow mo511 10 0 172 325 (@joinRow mo511 10 0 22 150 mo511P10_0 (@joinRow mo511 10 22 96 54 mo511P10_22 mo511P10_118)) (@joinRow mo511 10 172 192 133 (@joinRow mo511 10 172 96 96 mo511P10_172 mo511P10_268) (@joinRow mo511 10 364 96 37 mo511P10_364 mo511P10_460)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_10 : CutRow mo511 11 10 59 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_69 : CutRow mo511 11 69 96 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_165 : CutRow mo511 11 165 3 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_168 : CutRow mo511 11 168 1 := by
  apply checkedRow
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_169 : CutRow mo511 11 169 87 := shortcutBlock (data:=fun _ => 0x3032421188862150303242118886215030324211888621503032421088862150303242108886215030324211888621503032421088862150302c2121904a4160302c2121904a41603032461389862150303246138986215030324613898621503032461389862150303246138986215030324613898621503032461389862150302c2121104a416030324613898621503032461389862150303246138986215030324613898621503032461389862150303246138986215030324613898621503032461389862150302c2121904a41603032421188862150078c290582504863078c290582504863078c290582504863078c2905825048632498130380c88472078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c2905825048631178161709950883078c292192584863078c2905825048632498130380c884722498130380c884722498130380c884722498130280c884722498130380c884722498138240e884722498130380c88472078c292192584863078c292192584863078c292192584863078c2921925848630e0c229348e4a0750e0c229348e4a0750e0c229348e4a0750e0c229348e4a0750e0c229348e4a075078c290582504863078c290582504863078c290582504863078c290582504863078c2921125848632498130380c88472078c2921925848630798130580d10883078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c2905025048632498130380c88472078c29219258486318581144a055028130324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150) (by decide +kernel)
theorem mo511B11 : CutRow mo511 11 0 256 := (@joinRow mo511 11 0 165 91 (@joinRow mo511 11 0 10 155 mo511P11_0 (@joinRow mo511 11 10 59 96 mo511P11_10 mo511P11_69)) (@joinRow mo511 11 165 3 88 mo511P11_165 (@joinRow mo511 11 168 1 87 mo511P11_168 mo511P11_169)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_7 : CutRow mo511 12 7 13 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_20 : CutRow mo511 12 20 24 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 44 := (@joinRow mo511 12 0 7 37 mo511P12_0 (@joinRow mo511 12 7 13 24 mo511P12_7 mo511P12_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 6 := mo511P13_0
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
theorem mo511G : graphValid mo511 (boundsBefore KM503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 inputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=14) (i:=0) (before_sound KM503 VM503) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11008
open PEqualNP.Outside.L_meta_11008 in
theorem PEqualNP.Outside.L_meta_11008 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩
