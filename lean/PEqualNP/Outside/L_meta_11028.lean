import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_11028.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_11028
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
def graph : Sig := 0xfffffffffffffffffffffffefffffffcfffffffffffffffffffefffafffefff0fffffffefffffffefffffefefffffcfcfffefffaffeeffaafefefafaeeee0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8)
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


abbrev Bits := BitVec 448
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 448 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 448 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 448 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 448 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 448) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 448) (j : Fin 9) :
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 448) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 448) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 448 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 448) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 448) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 448) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^449*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^449 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 448) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (449*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^449)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 449*(i+1)-449=449*i := by omega
      have ge : ¬449*(i+1)<449 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 448 = (a==BitVec.allOnes 448) := by
  by_cases h : a=BitVec.allOnes 448
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^448-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^448 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (449*i) =
      (f xs[i]==BitVec.allOnes 448) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^449*u+x+(2^449*v+1)=2^449*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^449 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬449*(i+1)+448<449 := by omega
      have di : 449*(i+1)+448-449=449*i+448 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 449) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (449*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 449) (i:=i) (by simpa using hi) _ ok.2
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 448 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 448
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
def neighbor11028 (i : Fin 9) : Nat := [4, 4, 5, 6, 0, 0, 0, 1, 2].getD i.val 0
def absentRow11028 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor11028 i)
def presentRow11028 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor11028 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow11028 i) graph ≠ bit (presentRow11028 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow11028 i) (inputs.getD j.val zero) =
      bit (presentRow11028 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 14 else 15) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 14 else 15) := by
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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow11028 i) (presentRow11028 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 15 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

def sl7 (a0 a1 a2 a3 a4 a5 a6 : Nat) : Bits := BitVec.ofNat 448 ((a0 <<< 0) ||| (a1 <<< 64) ||| (a2 <<< 128) ||| (a3 <<< 192) ||| (a4 <<< 256) ||| (a5 <<< 320) ||| (a6 <<< 384))
def sL0 : Nat := 0x3fffffffffff
def sL1 : Nat := 0xffffffffffffff
def sL2 : Nat := 0x7ffffffffffffff
def sL3 : Nat := 0xa28504012071049
def sL4 : Nat := 0xfffffffffffffff
def sL5 : Nat := 0x2049204920492049
def sL6 : Nat := 0x4092409240924092
def sL7 : Nat := 0x4c326089204368db
def sL8 : Nat := 0x8124812481248124
def sL9 : Nat := 0x9040851240088724
def sL10 : Nat := 0xe083060384982db6
def sL11 : Nat := 0xf63ff63ff63ff63f
def sL12 : Nat := 0xf800000000000000
def sL13 : Nat := 0xfbc7fbc7fbc7fbc7
def sL14 : Nat := 0xfdf8fdf8fdf8fdf8
def sL15 : Nat := 0xff03fffff8f71fc7
def sL16 : Nat := 0xfffc07e3ff0be838
def sL17 : Nat := 0xfffff803ffeee63f
def sL18 : Nat := 0xfffffffc00000000
def sL19 : Nat := 0xfffffffc00193dc0
def sL20 : Nat := 0xffffffffc0000000
def sL21 : Nat := 0xffffffffff800000
def sL22 : Nat := 0xffffffffffc00000
def sL23 : Nat := 0xffffffffffe00000
def sL24 : Nat := 0xfffffffffffc0000
def sL25 : Nat := 0xfffffffffffe0000
def sL26 : Nat := 0xfffffffffffff800
def sL27 : Nat := 0xfffffffffffffe00
def sL28 : Nat := 0xffffffffffffffc0
def sL29 : Nat := 0xfffffffffffffff8
def sL30 : Nat := 0xfffffffffffffffe
def sL31 : Nat := 0xffffffffffffffff
def sR0 : Bits := 0x45c94e4bcb285413844750003ffffe00000
def sR1 : Bits := 0x8b9a4e4bcb285c13a44750003fff0000000
def sR2 : Bits := 0x2754920534ad14b58f8813fffff800000000
def sR3 : Bits := 0x33aa420534ad14b5cf8813fffc0000000000
def sR4 : Bits := 0x48b9a4e4bcb285e17a4455000007f0000000
def sR5 : Bits := 0x6754920534ad14b5cf8813fffc0000000000
def sR6 : Bits := 0x4ea924f70cd3e0baf803a80ffff0000000000
def sR7 : Bits := 0x915349287c9ef0209eca5cc0000ffff000000
def sR8 : Bits := 0x3265c62f04071c388415e061978650913580ffe00000000000ffffc0000
def sR9 : Bits := 0x449a8596e90f20c6b1516200501d0256e86700000007ffffff000000000
def sR10 : Bits := 0x33b481810199052c9c32a5d2849abb11c02703ffffff8000000000000000
def sR11 : Bits := 0x58c775f0c81ad0c6107fa8c30d96300d09c27ff800000000007ff00000000000
def sR12 : Bits := 0x1936a52ce9099033fc550b45031181042a831800000ffffffff80000000000000
def sR13 : Bits := 0x76018cf4912109835ab4398a38a4678927f1a00000000000000000fffffc00000
def sR14 : Bits := 0xced20222199622b270da64a1083af831e6a663fffff0000000000000000000000
def sR15 : Bits := 0x6ec9da86114d3630c40a9a8181b38a235040475fff0000000001ffffff8000000000
def sR16 : Bits := 0x8b3696e4a18d80ceb3476adc2641c090128a2d80000007fffffe0000000000000000
def sR17 : Bits := 0x3c2b42338e5486405688539d1a136ebd6387d99200000000000000000007ffc000000
def sR18 : Bits := 0x674920d3cd3744ac98374249c402836ae2930685ffffff80000000000000000000000
def sR19 : Bits := sl7 0x9b45573c000f8000 0x45e 0 sL26 sL31 sL1 0
def sR20 : Bits := 0x7fffffffffffffffffffffff00000000001ffffffffffffffffffe000000000000000508339d4022db3c4743ab501fc000fe00000
def sR21 : Bits := 0x1ffffffffffffe00000000003fffffffffffffffffff0000000000000003ffffffffffa41303ed1b46c0aa358d9e0003f80000007f
def sR22 : Bits := 0x43f00000021f80000021f80000021f8000001e000003c00001060c22a000504088411a021150600013480c582c160b0582c160b0582c
def sR23 : Bits := 0x4fc00013c00013e00009f00009f00009f0001c0004fc00027e00027e00027e0003c001e000110e8bc02a60e022248c1c3870e1c3870e
def sR24 : Bits := 0xb00b1c00016016380002c02cbc00404f001013c4010101b32220953e1081410b90054518901a90a067033819c0ce067033819c0ce067
def sR25 : Bits := 0x14580001160000c58000214001280005160000a3000052c00014500048001280005080023000604180100a21a603862060c183060c183
def sR26 : Bits := 0x303f000000607e000000c0fc000010f000043c0004a40da00014d200044029a0001928a21404003409804c026013009804c0260130098
def sR27 : Bits := 0x8030f0000401870000401870000401878000011800002300002440222880644100480885118017242009109148a45229148a45229148a
def sR28 : Bits := 0x160b800000b03800000b03800000b05e00020f000107801c04000220297440102800276051096190c800380700e01c0380700e01c03807
def sR29 : Bits := 0x1617800582e001617000b05c010b000b0bc021700160b800581c002c0e00160bc020f0083c1083215402098304743a950e1c3870e1c387
def sR30 : Bits := 0x3070000c1c000c1c00060e00060e00060e000460030700018380018380018380008c0046000044842424b2840138001491224489122448
def sR31 : Bits := 0x307c00000183e00000183e00000183e0000008e000011c0000000988496490a2002a140600050080254606026130984c26130984c26130
def sR32 : Bits := 0x3e0828c22050d00019a0090257369b02610c02802444404cd833c992534248030f030f030f030f030f030f030f030f030f030f030f030f
def sR33 : Bits := sl7 0 0xffff0000 0xffff00000000 0x4cd8b3c99a5f66c8 0x12650c02852444c1 0x2099a2090677769b 0x3e1828c33050d0
def sR34 : Bits := 0x3f80000001fc0000001fc0000001fc0000000f000001e00000222081010099012c1412a410000a131140260381c0e070381c0e070381c0
def sR35 : Bits := 0x3f80000fe0000fe00007f00007f00007f000078003f80001fc0001fc0001fc0000f0007800338a4004348514058c8013e1c3870e1c3870
def sR36 : Bits := 0x3ffffffffffff0000007fffff8000007fffff80003fffffffffffe000001ffffffffff8000140d310fe314086c85bae70000000fe03f80
def sR37 : Bits := 0x3fffffffffffffffffe000000001fffffffffffffffe00000021809336356892dc51e180acc25c05d4b922d400000000001ff00003fe00
def sR38 : Bits := sl7 0x803fe00000000000 0x2892cc00740000ff 0x4410e64b58c5bb75 0x345a76831321 0 sL27 0x3fffffffffffff
def sR39 : Bits := 0x63e00018f800063e00018f8004700031f800063f00031f8000c7e0011e004780031f8008f004e61e8ac28264402024861c3870e1c3870e
def sR40 : Bits := 0x804465a480b1620360062dc58446021386436091a62100208a09ba3b048b10b6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6cc
def sR41 : Bits := sl7 0xffffffff00000000 0 0 0x20ea59fa3b048b14 0x33865b6091a62120 0x3688fefc5844e02 0x844467a688b162
def sR42 : Bits := 0x98180026130009858004c260022c004c2c0045800984c002612001309000984c004480112048a1003a21880000c095b02850a142850a14
def sR43 : Bits := 0x984c009004c24009004c24009004c2600804480402240808902481543b0410100b02011002c4b0132008a1142284508a1142284508a114
def sR44 : Bits := 0xc0c1041851092164201266c40040004114c0500051228902014c3004082092f800f800f800f800f800f800f800f800f800f800f800f800
def sR45 : Bits := sl7 0xffff0000 0xffff00000000 0 0xae70064c52b3184a 0x50bba35706021f86 0x5a714b6860e9f43 0x120041406380747
def sR46 : Bits := 0x1448948240011488200734111a1004c01010490d050204031000980048ee010c700c700c700c700c700c700c700c700c700c700c700c700
def sR47 : Bits := sl7 0 0xffffffff00000000 0xffff 0x31080984158fe810 0xd0184d0d050355e 0x8604734111a1204d 0x1678b49240653e8
def sR48 : Bits := 0x2003691050aa20801c4041019a00024300812811d8a01108000800268a4942004f004f004f004f004f004f004f004f004f004f004f004f0
def sR49 : Bits := 0x202521181658024401800008804a0a08a5e500008864019400e02128900030520aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa
def sR50 : Bits := sl7 0 0xffffffff 0xffff000000000000 0xc091a4126eb49438 0x704812891dce8150 0x1e7441059a10034 0x20836914d0bb608
def sR51 : Bits := 0x240024c20048004984009000930c01004880401220010212200c86003810400930080b83850861080c41420a105082841420a1050828414
def sR52 : Bits := sl7 0 0 0xffffffffffff0000 0x86014c31a44820d2 0xc114c2518af92289 0x74201266e6da408e 0x2c0e10c98510921
def sR53 : Bits := 0x2cb21e243ee4890915ea094281a9381a448598d760130300a3680c70001524e00000000ffff0000ffff000000000000ffff000000000000
def sR54 : Bits := 0xa03960280a580a02960280b58202b05016580a02c405016301405960809c20270501650404a241203290b06c02224899e2c58b162c58b16
def sR55 : Bits := 0x1382c38fc02705871f804e0b0e3f002088f008223c00c2a02338e5486405688539d1a136abd638598916deb6f5b7adbd6deb6f5b7adbd6de
def sR56 : Bits := 0x14e06005381c014e0600a7038014300a70300286014e07005381c029c0e014e070028700a1c044201e8bd4a2644180042ab162c58b162c58
def sR57 : Bits := 0x14e07004e0a703804e0a703804e0a70380104870082438056010c74912108015ab4398808a0670922f122dc5b8b716e2dc5b8b716e2dc5b8
def sR58 : Bits := 0x18ff800000c7fc00000c7fc00000c7fc00008f800047c00018c665d0401890c4107da8c30d923001014201f03e07c0f81f03e07c0f81f03e
def sR59 : Bits := 0x18ff80063fe0018ff800c7fc0027c00c7fc004f8018ff80063fe0031ff0018ff8004f8013e0048b1a4e4bca205c16a4455bd7af5ebd7af5e
def sR60 : Bits := 0x1c03fc00003807f80000700ff0000041f000107c00000b1494a4018c804eb14728dc2641408010082518e0c7063831c18e0c7063831c18e0
def sR61 : Bits := 0x1f00000700f80000700f80000700f8000020f00010780000826a524c8080032fc5503010010010020811310620c4188310620c4188310620
def sR62 : Bits := 0x1f000007c00001f00000f8000038000f8000070001f000007c00003e00001f0000070001c00027541200142410a10a0002c183060c183060
def sR63 : Bits := 0x1ffc0000003ff80000007ff00000007e00001f8000023492040cd0104ac183742494402830862920681f00f807c03e01f00f807c03e01f00
def sR64 : Bits := 0x1ffffffffffffe000000ffffffc0000fffffffffffffffff8000003ffffffffffff80001ffffbe2d6552da519822172148000007f01fc07f
def sR65 : Bits := 0x2108014842005210801484200211001084005210802908400a421000844021100108400422000108e04000690b9801104142850a142850a1
def sR66 : Bits := 0x2aa5200aa9480aa9480554a40154a40254a4029140525200552900d5290095290052280b14050ec4a14026458a13808851a3468d1a3468d1
def sR67 : Bits := 0x2aa52800aa5529400aad529400aa952940055522402aac4805552c01c1c153d00b05712a642462828dac840092a351a8d46a351a8d46a351
def sR68 : Bits := 0x3306028cc1810cc1814660c02260c06360c0432204986028983014983014d83014644092204994093109c204086c81aa63264c993264c993
def sR69 : Bits := 0x3c0002caf0e000164f0e000164f0e0001657878008f0f0011e1e1452768213204410c04958c5ba7528828800741e0f0783c1e0f0783c1e0f
def sR70 : Bits := 0x420001520a10003520a10002520a100014822002c11001420029180208446a2a4400042c40290a08c085520a4148290520a4148290520a41
def sR71 : Bits := 0x4200055080005420006a1000128001a1000290002820001508001a84000942000290002c000a320c41000251982215200042850a142850a1
def sR72 : Bits := 0x482828001a905050002520a0a00029042002c10800a7041e04420012805a80284426560140080024542921490a485242921490a485242921
def sR73 : Bits := 0x4c52181314c604c53181314c60424c26298604c5308262984098a6181091042442629860848c18211b22308250658cc698b972e5cb972e5c
def sR74 : Bits := 0x501d810010100c912802f942204209584020840862409c641e61504100132008490149014901490149014901490149014901490149014901
def sR75 : Bits := 0x707c001c1f000707c001c1f0008780383e000707c00383e000e0f80021e008780383e0010f0008a9a0c4b4b005c11a4401d1a3468d1a3468
def sR76 : Bits := 0x7f80001fe00007f80001fe0000f8003fc00007f80003fc0000ff00003e000f8003fc0001f00063108005342d10a58f8011e1c3870e1c3870
def sR77 : Bits := 0x7ffffffffffffffffffffffffffffffffffff8000003ffffffffffffc0000fffffffffffffffb98ae94063697bd80511410000000fe03fff
def sR78 : Bits := 0x8000001ffffff8000001ffffff00003ffffffffffffc000000fffffffffff00003fffffe0000412e841a8114a21e6afaea01fc07f01fc000
def sR79 : Bits := 0x804522604c02292604c02293604c02291904012482009265150489202900688028848d4a6e6c2a01a440c658cb19632c658cb19632c658cb
def sR80 : Bits := 0x8045466011489804504c02291b0092c0228320124c045226011493008a4d8045232012480493000ae901c802cd5c256201162c58b162c58b
def sR81 : Bits := 0x8130012293026002453604c0048a3208022482008934e042005b200110004a3840215906852749a748230b1858c2c61630b1858c2c61630b
def sR82 : Bits := 0x982004040218060305a704b6060a1f0350a0a34706001f868e70044c5231184a185518551855185518551855185518551855185518551855
def sR83 : Bits := 0xb30600a0cc9830050cc9830050ccd83005066644044cc8808999a1801114116810cc516100acc25c0590b920d48a45229148a45229148a45
def sR84 : Bits := 0xbc000b2f0003af00039780014b80014b80016bc00ae000b2e00058e00058e0005978013c009e0c2113d80a0063f0411e800e1c3870e1c387
def sR85 : Bits := 0xc000300cff0001806ff0001806ff00018067f800817f00102fe01cc032d40542228343ac41c50ca480a00491c026130984c26130984c2613
def sR86 : Bits := 0xc0080c3002023002021801018c01018c01018c00130080c30040610040610040618002200110013048121100518006558048912244891224
def sR87 : Bits := 0xe0000000003fffffffffffffffffff8000001fffffff0c1e644a0c1a805ee8a8442656957089a064d420000000000000000ffffffc001fff
def sR88 : Bits := 0xe0000007ff0000007ff0000007ff0000003f00001f80000ce120022199420b230d824210822c821e6a243e07c0f81f03e07c0f81f03e07c0
def sR89 : Bits := 0xe0000007ffffffffffff00000000000ffffff80001ffffffffffffc000001ffffffffffe0000219ae929cd02cd5c2576030003f800003f80
def sR90 : Bits := 0xe20b2082432e4090101e8090281a9181a448180d26001030083480450001104c003300330033003300330033003300330033003300330033
def sR91 : Bits := sl7 0xffff0000ffff 0xffff 0 0x1e65596100333129 0x422084286240dc64 0x6a12fd4a29420d78 0xfc1dc1841010ac9b
def sR92 : Bits := sl7 0xffffffff 0 0xffff 0x590e021ac9008305 0x8bfe740628964a19 0x481800319804b1a0 0xfe12de11b1658035
def sR93 : Bits := sl7 0xff8000000 0x82a014bdc801ff00 0x22a353ec4bc50ca6 0x1cc232d40552 0 0 0xffc0000000000000
def sR94 : Bits := sl7 0x9001fc07f0000000 0x13d80a04e3f0791e 0x3da1 sL27 0xf80000000003ffff 0x7ffffffffff 0xffc0000000000000
def sR95 : Bits := sl7 0x99000000001fff80 0x3b3a308358678cf6 0xfc00000000001821 sL31 sL31 63 0xffffffe000000000
def sR96 : Bits := sl7 0xb0fe000000003fff 0x33a21ca4909c8d7 0xffffffffffffdae1 sL31 0x1ffffff 0 0xfffffff800000000
def sR97 : Bits := 0xfffffff8000000007fffffffffffffffffc000001ffffff220691f524e446aeae40804ac42298aa9c285400000000000007ff001ffc007ff
def sR98 : Bits := sl7 0x59000000001fc07f 0xad506645fa138089 0xffff00007fffcec5 0xfe000001ffffffff sL31 sL31 0xfffffffff000000f
def sR99 : Bits := sl7 0x3ffe000 0x4920000000003ffe 0xe1615d068d674daf 0x845b608111024a78 0xffffe0000004f142 0x7fffffffffff sL22
def sR100 : Bits := sl7 0x7fc01ff 0x8dae854094000000 0xb05712a64357282 0xffffec01cdc1d3d6 0xfffffff0000001ff 0x1fffffffffff sL25
def sR101 : Bits := 0xffffffffffffffff8000000007ffffffffffffffe000000d9584892129806c813c949d4a6e6c7e01a541c00000000003ff800000003ff800
def sR102 : Bits := sl7 0x5dc49781bff00000 0x33aa 0 0 0 0xff00000000000000 sL31
def sR103 : Bits := sl7 0xfff0000000000000 0x92a000fff8000001 0x5d0fd10d451cd11a 0x1b32220fd3f1587 0x40101 0xffff800000000000 sL31
def sR104 : Bits := sl7 0x800003f800003fff 0xc93a15435d8c06f7 0xffffffffffffc930 sL31 0x3ffff 0xfffff80000000000 sL31
def sR105 : Bits := sl7 0xffe00000000 0x90d80007ff001ffc 0x13296237e8710971 0x1e14c0022169f648 4 0xfffffffff8000000 sL31
def sR106 : Bits := sl7 0x33aa61bff8000 0xffff800000000000 sL31 0xffc0007fffffffff 0x19d530d sL22 sL31
def sR107 : Bits := sl7 0x86fe00000fe00000 0x5e8bc6aa6761a024 0x6e6 0 0 sL28 sL31
def sR108 : Bits := sl7 0xae0000000fffc000 0x5e8bd6a26643e024 0x4426 0 0xfffffffffe000000 sL31 sL31
def sR109 : Bits := sl7 0x3ffffff 0xa0c0000007ffc000 0x9332bafa39508e11 0x3201c87283c11431 0xfffffffffff81261 sL31 sL31
def sR110 : Bits := sl7 0x8efe0000001fc000 0x6e8bc2aa62e3a224 0x253 0 sL24 sL31 sL31
def sR111 : Bits := sl7 0x3fffff 0x1724000000ffe000 0x58cb030d5402e6b2 0x8b6248d743f0510 sL29 sL31 sL31
def sR112 : Bits := sl7 0x7fc000000003ffff 0x72e2029188000000 0x4c50049ca8597a45 0xffffca45032e88ae sL31 sL31 sL31
def packet (value j : Nat) := if 1 ≤ j then 0 else value
abbrev Chart (g : Forest) (known : List (Nat × Nat)) := graphValid g (boundsBefore known) = true
def g146Y : Array Signals := #[(0,0),((sl7 sL11 sL11 sL11 sL11 sL11 sL11 sL11),(sl7 sL5 sL5 sL5 sL5 sL5 sL5 sL5)),(0,0),(0,0),((sl7 sL13 sL13 sL13 sL13 sL13 sL13 sL13),(sl7 sL6 sL6 sL6 sL6 sL6 sL6 sL6)),(0,0),(0,0),((sl7 sL14 sL14 sL14 sL14 sL14 sL14 sL14),(sl7 sL8 sL8 sL8 sL8 sL8 sL8 sL8)),(0,0)]
def g146C : List ColumnInfo := []
def g146A : List (List Nat) := [[],[116],[65],[65,113],[113,65],[113]]
def g146D3 := packet 0x7
def g146L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g146D3)
  | _ => emptyPacking
def g146I (_ _ : Nat) : Option (Nat × Nat) := none
def g146 : Forest := ⟨146,3,fun i => g146Y[i]?.getD (0,0),g146C,g146A,g146L,g146I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146P3_0 : block g146 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g146T : checkedTables g146 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g146P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146G : Chart g146 [] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low146 : Lower true (varsX 146) (graphGoal 146) 4 := lower_forest (g:=g146) (i:=0) (hints:=268501056) (before_sound [] baseKnown) g146G g146T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K146 := extendKnown [] 4 [(146,[]),(328,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
theorem V146 : Known true K146 := extend_ok (m:=146) baseKnown low146 (by decide +kernel)
def g51Y : Array Signals := #[((sl7 sL15 sL15 sL15 sL15 sL15 sL15 sL15),(sl7 sL3 sL3 sL3 sL3 sL3 sL3 sL3)),((sl7 sL16 sL16 sL16 sL16 sL16 sL16 sL16),(sl7 sL7 sL7 sL7 sL7 sL7 sL7 sL7)),(0,0),(0,0),((sl7 sL17 sL17 sL17 sL17 sL17 sL17 sL17),(sl7 sL9 sL9 sL9 sL9 sL9 sL9 sL9)),((sl7 sL19 sL19 sL19 sL19 sL19 sL19 sL19),(sl7 sL10 sL10 sL10 sL10 sL10 sL10 sL10)),(0,0),(0,0),(0,0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 := packet 0xf
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : block g51 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : Chart g51 K146 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K146 V146) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K146 4 [(51,[]),(53,[33,84]),(83,[101]),(89,[49,33,100,84]),(101,[33,84,100]),(105,[49,33,100]),(149,[112,16,33,82,101]),(165,[32,16,84,116,100]),(177,[64,81,33,50,115,99]),(180,[32,65,49,115,99]),(209,[64,97,33,50,117]),(325,[128,16,33,100,82,117]),(337,[96,65,33,50,48,133,117]),(404,[32,65,49,115,133,99,101]),(452,[32,97,49,132,117,84])]
set_option maxRecDepth 32768 in
theorem V51 : Known true K51 := extend_ok (m:=51) V146 low51 (by decide +kernel)
def g147Y : Array Signals := #[(0xffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007fe03f1f3f1fc400ffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007,0xdb2a5148544878adb654a290a890f15b6ca945215121e2b6d9528a42a243c56db2a5148544878adb654a290a890f15b6ca945215121e2b6d),(0xf1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8fffc01fffe27c3f1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8,0x9230619080810b892460c3210102171248c1864202042e2491830c8404085c49230619080810b892460c3210102171248c1864202042e249),(0,0),(0,0),(0x7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3ffffffe03ffdcbc7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3f,0x2440820101000012488104020200002491020804040000492204100808000092440820101000012488104020200002491020804040000492),(0,0),(0,0),(0x81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0fffffffc00337f81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0,0x4983040206126464930608040c24c8c9260c1008184991924c18201030932324983040206126464930608040c24c8c9260c1008184991924),(0,0)]
def g147C : List ColumnInfo := [(1,0,146,0,4)]
def g147A : List (List Nat) := [[],[113]]
def g147D4 := packet 0x1f
def g147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g147D4)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,4,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P4_0 : block g147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : Chart g147 K51 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=268435524) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(150,[32,116]),(329,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g55Y : Array Signals := #[(0xfff800ffffff001ffe03fffffff001fffffc07fe9c3590787fffc001fff001fff001fffffe003ffc07ffffffe003fffff80ffd386b20f0f,0xa0550aa0aa02a0d409468291402a0d4128148b14898251088882a81540aa1540aa1541540541a8128d052280541a82502916291304a21111),(0xffffff000fffffe00003ff80fffffe003ffff80d1bea400787fffffe000001fffffe001fffffc00007ff01fffffc007ffff01a37d4800f0,0xc4660cc8cc44c0988d8b0322644c4989b1191226c1ae242aaaa3311988cc9988cc1991988981311b160644c89893136232244d835c485555),(0xf000000000ffffffffffc0000ffffffffc0000001fa03ef8007fffffffffffe000000001ffffffffff80001ffffffff80000003f407df000,0x1782f02f01702e02e0c0bc381700e01c05e1c3819a03a99998bc05e02f01e02f05e05e02e05c05c18178702e01c0380bc38703340753333),(0,0),(0xffffffffff000000000000000fffffffffffffff331fbb007ffffffffffffffffffffffe000000000000001ffffffffffffffe663f7600ff,0x980300300980b0130102c04098090120260000032118a55554c02601300201300600601301602602058081301202404c00000642314aaaa),((sl7 0x19dd38dff00 0xffffffe000000000 sL31 0x807fffffffffffff 0xcee9c6ff 0xfffffffff0000000 sL31),0xe00400c00e00c01c00030000e00e01c0380204046498466667003801c00c01c00801801c01803800060001c01c038070040808c9308cccc),(0,0),(0,0),(0,0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 := packet 0x1f
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : Chart g55 K147 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K147 V147) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K147 5 [(55,[]),(109,[33,49,84,100]),(167,[32,16,84,116,100]),(213,[64,33,97,49,112,80]),(217,[49,114,100,84,82]),(453,[128,16,114,49,100,82,67,84])]
set_option maxRecDepth 32768 in
theorem V55 : Known true K55 := extend_ok (m:=55) V147 low55 (by decide +kernel)
def g115Y : Array Signals := #[(0xfffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7fffc003ffffffffffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7,0x5001401400a00200001401400a002000008040080420b249002802801400a005001401400a00200001401400a002000008040080420b249),(0x7fffffe000fff007fffffe000fff007ffffe00169f6d038ffffffc001fff0007fffffe000fff007fffffe000fff007ffffe00169f6d038,0x262498898a4c42429249891894c484252490904a140f4d6db493093249824c5262498898a4c42429249891894c484252490904a140f4d6db),(0,0),(0,0),(0x7fffffffff000007fffffffff000007fffffff2b97e603ffffffffffe0000007fffffffff000007fffffffff000007fffffff2b97e603f,0x4849211210909485249212212109284a492120902b90a09249241240921490a4849211210909485249212212109284a492120902b90a0924),((sl7 0x1369f81c0 0x7ffffffffffffff8 sL12 sL4 0x800000001369f81c sL2 0xff80000000000000),0x7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6e3823831c18e0c7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6),((sl7 0xcea8c5e00 0x8000000000000000 sL31 sL4 0xcea8c5e0 sL12 sL31),0x807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6fc03c03e01f00f807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6),(0,0),(0,0)]
def g115C : List ColumnInfo := [(32,0,83,0,4)]
def g115A : List (List Nat) := [[],[101]]
def g115D4 := packet 0x3f
def g115L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g115D4)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,4,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115T : checkedTables g115 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : Chart g115 K55 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 5 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K55 V55) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K55 5 [(115,[]),(117,[33,84]),(121,[49,33,100,84])]
set_option maxRecDepth 32768 in
theorem V115 : Known true K115 := extend_ok (m:=115) V55 low115 (by decide +kernel)
def g151Y : Array Signals := #[(0xf001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007fff000fff001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007,0xa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d8aa8aa8aa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d),(0x1fffffe00007ffffe0000fffffffffc00ffffc068db9401f8ffffff000001fffffe00007ffffe0000fffffffffc00ffffc068db9401f8,0xc198198198332604c098362c191204c1306c0c891340d38412490cc0cc0cc198198198332604c098362c191204c1306c0c891340d3841249),(0xfffe00000000007fffffffff00007fffffff0000000ff00e8e00fffffffffffe00000000007fffffffff00007fffffff0000000ff00e8e00,0x1e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db2f02f02f01e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db),(0,0),((sl7 0xffffff99af6d703f 0x7fffffff sL21 0x703fffffffffffff 0xffffffffff99af6d 0x7fff 0xffffffffffffff80),0x200600600c000180300c040602018020080300000190c082492300300300200600600c000180300c040602018020080300000190c082492),(0,0),(0,0),((sl7 0x6754f2ffc0 0xffffffff80000000 sL31 0xffc0ffffffffffff 0x6754f2 0xffffffffffff8000 sL31),0xc018018010000600c0100008000600c0300c010202200724924c00c00c00c018018010000600c0100008000600c0300c010202200724924),(0,0)]
def g151C : List ColumnInfo := [(1,0,150,0,5)]
def g151A : List (List Nat) := [[],[32,116]]
def g151D5 := packet 0x3f
def g151L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g151D5)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,5,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P5_0 : block g151 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g151P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : Chart g151 K115 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=268437316) (before_sound K115 V115) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K115 6 [(151,[])]
set_option maxRecDepth 32768 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g179Y : Array Signals := #[(0xffe00ffe00fffff001ff87fc3ff803fffffffe1e6b067b003e0ffff001ffc01ffc01ffffe003ff0ff87ff007fffffffc3cd60cf6007c1f,0xa4150a4150a0520a4140510089052290a4102044009046b4a5294a0a41482a1482a140a4148280a201120a45214820408801208d694a529),(0xff00000fffff007ffffe0007fffffffc00ff87ffe1a8bdc107c1f07ffffe00001ffffe00fffffc000ffffffff801ff0fffc3517b820f83e0,0x4c0984c0980c2604c0982620900260304c02104805201cc118c63184c09813098130184c0981304c412004c060980420900a403982318c63),(0,0),(0,0),(0xfffffff00000007ffffffff8003fffffff0007fffe56ec8ef801ffffffffffffe0000000fffffffff0007ffffffe000ffffcadd91df003ff,0x90120101205048090120480121048040101420900052a00421084209012024020240a0901202409002420900802028412000a54008421084),(0xffffffffffffff8000000000003ffffffffff800002793f4003e007fffffffffffffffff0000000000007ffffffffff000004f27e8007c00,0xe09c0609c060704e09c17045c2270482609804e088269394b5ad6b4e09c1380c1380c0e09c1382e08b844e0904c13009c1104d27296b5ad6),(0,0),(sR106,0xe0180e018080700e0180060038070380e04701108d4308c6318c700e01c0301c030100e01c03000c00700e0701c08e02211a86118c6318),(0,0)]
def g179C : List ColumnInfo := [(0,32,146,1,5),(32,0,147,0,5),(1,32,146,0,4),(2,0,177,0,4),(128,0,51,0,4)]
def g179A : List (List Nat) := [[],[113]]
def g179D4 := packet 0x4fd5121
def g179D5 := packet 0x60880480e140fd41ff21fd21
def g179H5 := packet 0x8
def g179D6 := packet 0x8635f
def g179H6 := packet 0x1100000000000ba000000084000c403000
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (3,1,3,0,0,5,0,g179D5)
  | 6 => (1,0,3,65537,0,0,1028,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g179H5
  | 6 => lookupWord 1 19 0 7 2 1 g179H6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g179P4_0
  · exact g179P5_0
  · exact g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : Chart g179 K151 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=268435524) (before_sound K151 V151) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K151 7 [(179,[]),(182,[32,116]),(211,[101]),(345,[49,33,100,84,135]),(361,[49,33,100,135]),(364,[32,49,132,100,118])]
set_option maxRecDepth 32768 in
theorem V179 : Known true K179 := extend_ok (m:=179) V151 low179 (by decide +kernel)
def g181Y : Array Signals := #[(0xffe00ffe007ffff801ff87fc3ff803ffffc3fffe6a3e2b0001fffff001ffc01ffc00fffff003ff0ff87ff007ffff87fffcd47c560003ff,0xa4150a41505029052140510089052290a40881040280e0b4a5294a0a41482a1482a0a0520a4280a201120a4521481102080501c1694a529),(0,0),(0xff00000fffff803ffffe0007fffffffc00fffc3fe1a9a9d107fe007ffffe00001fffff007ffffc000ffffffff801fff87fc35353a20ffc00,0x2c0582c058160b0160181620500160302c0500808521289118c63182c0580b0580b02c1602c0302c40a002c060580a01010a425122318c63),(0,0),(0xfffffff00000003ffffffff8003fffffff00003ffe57e88ef8000fffffffffffe00000007ffffffff0007ffffffe00007ffcafd11df0001f,0xb016030160582c0580a0580161058040301611050053a084318c630b01602c0602c0b0580b0140b002c20b0080602c220a00a741086318c6),((sl7 0x80004d2fe8007fe0 0x7fffffffffff 0xffffffff80000000 0x3ff07fffffffff 0xffffffc0002697f4 0x3fffff sL28),0xc09804098060302604c16045822604824098002608069164a5294a4c098130081300c0604c0982c08b044c09048130004c100d22c94a5294),(0,0),(sR106,0xe0180e01804038070180060038070380e02238108c5308c6318c700e01c0301c030080700e03000c00700e0701c044702118a6118c6318),(0,0)]
def g181C : List ColumnInfo := [(1,0,180,0,4),(4,0,177,0,4),(16,0,165,0,4),(32,0,149,0,4),(128,0,53,0,4)]
def g181A : List (List Nat) := [[],[114,84],[32,116],[32,64,80,112],[64,117],[64,82,112,32],[80,66],[80,114,64,66],[112,32,66,84],[112,82]]
def g181D4 := packet 0x57d4d10
def g181D5 := packet 0x4e4120443f
def g181H5 := packet 0x3
def g181D6 := packet 0x58d11f
def g181H6 := packet 0x73009baace27000000d01200b5000016b1
def g181L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g181D4)
  | 5 => (2,1,3,65537,0,4,1025,g181D5)
  | 6 => (1,0,3,65537,0,0,1029,g181D6)
  | _ => emptyPacking
def g181I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g181H5
  | 6 => lookupWord 2 17 0 8 1 3 g181H6
  | _ => fun _ => none
def g181 : Forest := ⟨181,6,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P4_0 : block g181 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181T : checkedTables g181 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g181P4_0
  · exact g181P5_0
  · exact g181P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : Chart g181 K179 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 7 := lower_forest (g:=g181) (i:=0) (hints:=536872196) (before_sound K179 V179) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K179 7 [(181,[])]
set_option maxRecDepth 32768 in
theorem V181 : Known true K181 := extend_ok (m:=181) V179 low181 (by decide +kernel)
def g218Y : Array Signals := #[(0,0),(0xf003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03ffff000fff003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03f,0xa2282288a0282284a08a210802284a0280220882200a5314514508a08a08a2282288a0282284a08a210802284a0280220882200a53145145),(0,0),(0x3fffff003fffff0000ffc3fffff003fffffc009adfd000fc0ffffff000003fffff003fffff0000ffc3fffff003fffffc009adfd000fc0,0xc8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d342c42c42c8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d3),(0xfffc00000003fffffffff0003fffffffc000fffd77e88afc003ffffffffffffc00000003fffffffff0003fffffffc000fffd77e88afc003f,0xc04c1302c04c090130026104c0100c0584120152a08828a28a1301301300c04c1302c04c090130026104c0100c0584120152a08828a28a),(0,0),((sl7 0x12697f4000fc0 sL0 sL18 0xfc0ffffffffffff 0xffff00012697f400 0x3fffffff sL24),0x302701c0302702e09c08b822702609026009c11269264b2cb2c9c09c09c0302701c0302702e09c08b822702609026009c11269264b2cb2c),((sl7 0x39d530dfff000 0xffffc00000000000 sL31 0xf000ffffffffffff 0x39d530dff sL20 sL31),0xc0380200c0380300e000c00380380e03808e0208d5104c30c30e00e00e00c0380200c0380300e000c00380380e03808e0208d5104c30c30),(0,0)]
def g218C : List ColumnInfo := [(0,8,146,64,5)]
def g218A : List (List Nat) := [[],[116],[99],[99,116],[65],[65,113],[65,99],[65,99,113],[113,65],[113],[113,99,65],[113,99]]
def g218D5 := packet 0x3f
def g218L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g218D5)
  | _ => emptyPacking
def g218I (_ _ : Nat) : Option (Nat × Nat) := none
def g218 : Forest := ⟨218,5,fun i => g218Y[i]?.getD (0,0),g218C,g218A,g218L,g218I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218P5_0 : block g218 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g218P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : Chart g218 K181 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=318857280) (before_sound K181 V181) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K181 6 [(218,[]),(346,[49,100,135]),(410,[134]),(458,[49,100,84,117,133]),(466,[99,83,133]),(472,[49,33,66,98,82,117,133])]
set_option maxRecDepth 32768 in
theorem V218 : Known true K218 := extend_ok (m:=218) V181 low218 (by decide +kernel)
def g119Y : Array Signals := #[(0xfffffc00000fffffc00003fffff00000ffffffffffc00003ffffe0003fffffffffffffc00003fffffffffe0003fff97e43a62aa9edf07c1f,0x2a8000aa0002a8002a8000aa000aa000550000a8001a80009400680014800a0000a8001a800128000a4005800a05c00862081c0108421),(0xfffffffffff00000000003ffffffffff000007fffffffffc000000003ffffc0007fffffffffc00003ffffffffc0000b5fc47c9174a0003e0,0x452331148cc45233115331148cc450cc4546622913114131148d824b11419049322913114931149b1148c824904930b4e846c8154ab5ad6b),((sl7 0xbada15c4320f8000 0xc000000000000676 sL2 sL20 0x7ffffffffff 0xfffffc0000000000 sL31),0x160bc0582f0160bc0583c0582f0162f0161780b05c0585c0582e042c0585e085c0b05c0581c0581c0582f041e083c27692ca058432739ce7),(0,0),((sl7 0x9707c5fea40003ff 0xfffffffffffffe81 sL2 0 0xfffff80000000000 sL31 sL31),0x984c0261300984c02604026130098300981804c260261602613008b02616011604c260261202612026130089011206011701056a254a5294),((sl7 0x6978fe62520ffc00 0x645 sL12 sL31 sL31 sL31 sL31),0xe0700381c00e070038180381c00e0400e06007038038180381c010c038180218070380381c0381c0381c010e021c04016930da62018c6318),(0x33aa5b8895b2bf00000,0xff8003fe000ff8003fe003fe000ff800ff8007fc003fe003fe001f003fe003e007fc003fe003fe003fe001f003e00322a538895a2bef7bde),(0,0),(0,0)]
def g119C : List ColumnInfo := [(2,0,117,0,5),(4,0,115,0,5),(64,0,55,0,5),(16,2,101,0,4),(32,4,83,0,4)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D5 := packet 0x17e50
def g119D6 := packet 0xa888ff
def g119H6 := packet 0x8
def g119L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g119D5)
  | 6 => (1,0,3,65537,0,0,1029,g119D6)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | _ => fun _ => none
def g119 : Forest := ⟨119,6,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g119P5_0
  · exact g119P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : Chart g119 K218 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 7 := lower_forest (g:=g119) (i:=0) (hints:=1348) (before_sound K218 V218) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K218 7 [(123,[50,101]),(125,[33,49,84,100]),(249,[49,114,100,84]),(497,[113,130,49,101,50]),(500,[32,65,96,48,113,133,83])]
set_option maxRecDepth 32768 in
theorem V119 : Known true K119 := extend_ok (m:=119) V218 low119 (by decide +kernel)
def g183Y : Array Signals := #[(0xfffe01fffc0007ffe01fff807fff80007fff8001fffe0007ffffffe0007fff00fffffffff8001fffffff00ff1d203397a2ac000003f03f,0xaa01545480a90350094340290b2055205520552154815485520aa4054835204a1a41485101520d4825205216141d002390a2a91451451451),(0xff000001fffffff800001fffffffffffff80000001fffffff8000fffffff800000fffc03ffffffe0007fffff00637e8b807608003f000fc0,0xcc119898113022608d858232120466046604660998119806608cc0898026046c2c0190982260498136046424262336098066085145145145),(0x1ffffffffffffe000007ffffffffffffffe00000000000fffffffffffff000003ffffffffff800000009d8e48e9a5400fc0fc0000,0xf005e0e005c00b802e0600bc1c01780178017801e005e017802f002e00b801703005e0e00b800e003801783838150a48c1a54030c30c30c3),(0,0),((sl7 0x85ccf7f000000fff 0xffffffffffa049c5 0x3ffffffff 0xfffff00000000000 sL31 0x7fffff 0xfffffffe00000000),0x26000026004c01300804c02009800980098002002600180030013002c00980401601004c00900240098000008048c0050854a28a28a28a),((sl7 0x3e5b400000fff000 0x917538 sL18 sL31 sL31 0x7fffff 0),0xb8010138027005c0101700404e004e004e004c0138012004c009c013004e00009800027004e013804e0040408075102e5802cb2cb2cb2c),(0,0),((sl7 0x60389bffff000000 0x4e9376 0 0 0 sL21 sL31),0xc00001c003800600001800007000700070007001c001c007000e001c00700080e002038007001c00700080804881362010830c30c30c30),(0,0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,32,146,5,6),(32,0,151,0,6),(16,0,167,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[],[32,116]]
def g183D5 := packet 0x4f77159653
def g183D6 := packet 0x10420806284506c85b2c0bf59653fdd8553bdd8553bd58453be58053
def g183H6 := packet 0xa0
def g183D7 := packet 0x1c0038007643a985f3c129aa629ff
def g183H7 := packet 0x730000000000000000000000280000000000000000000064001100000070000000000000000052000000000000000000000000
def g183D8 := packet 0xb1a23f
def g183H8 := packet 0x3c03969000000000000000000000
def g183L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g183D5)
  | 6 => (5,2,3,0,0,6,0,g183D6)
  | 7 => (3,1,3,65537,0,5,1031,g183D7)
  | 8 => (1,0,3,65537,0,0,1029,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g183H6
  | 7 => lookupWord 1 53 0 8 3 1 g183H7
  | 8 => lookupWord 1 17 0 7 2 1 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_3 : block g183 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 5=true := (@block_merge g183 6 0 3 2 g183P6_0 g183P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g183P5_0
  · exact g183B6
  · exact g183P7_0
  · exact g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : Chart g183 K119 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=268436804) (before_sound K119 V119) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K119 9 [(183,[]),(365,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V183 : Known true K183 := extend_ok (m:=183) V119 low183 (by decide +kernel)
def g215Y : Array Signals := #[(0x1ffff80001ffff000ffff8007ffff00007ffffffffc0001ffffffffffffffffffffffffc0001ffffffffc003ffd524a373e833c0007c1f,0x548015200d4004a01a002900b200aa405520154802a901548055200a900948052014400a900d4804a40148058051520013288339294a529),(0x1ffffffffe0000000ffffffffffffffff80001ffffffffe00007fffc0001ffff000ffffffffe0000fffffffc003ed51a38816c800f83e0,0x4980a2602898146c22c0a32112028cc0466051980a330219814660113018d808641260513014980a6c0519049049be541230016086318c63),(0x1ffffffffffffffff00000007ffffffffffffe00000000000007fffffffe0000000fffffffffffff0000000000073b22915bd881f00000,0x9e02cb80b2e059704b02cbc25c0b2f00978065e02cbc075e039780a5c052e02d782b8165c058e02c70165e09e09e063922115bd88e739ce7),(0,0),((sl7 0xe43c4e4f7e0003ff 0xffffffffffffc859 0xfffffffffff 0xfffff80000000000 sL31 0x7fffff 0xffe0000000000000),0x10030c00c30061808c030c04600c30011800860030c00460021800c600630031804c0186006100308018601101100009e00c420c48421084),(0,0),((sl7 0x9b47773c00007c00 0x456 0xfffff00000000000 sL31 sL31 0x7fffff 0),0xe013f004fc017e00f00bf007804fc009e004f8013f00278013e004f8027c013e007009f8027e013f009f801e01e000569a45770c2d6b5ad6),((sl7 0x5dc49781bfff8000 0x33aa 0 0 0 sL21 sL31),0x1c000700018000000c00000070000e00070001c00038001c000700038001c000800e00038001c000e00020020001820dc08401318c6318),(0,0)]
def g215C : List ColumnInfo := [(4,0,211,0,7)]
def g215A : List (List Nat) := [[]]
def g215D7 := packet 0x7f
def g215L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g215D7)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,7,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215T : checkedTables g215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g215P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : Chart g215 K183 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 8 := lower_forest (g:=g215) (i:=0) (hints:=268437316) (before_sound K183 V183) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K183 8 [(215,[]),(407,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g219Y : Array Signals := #[(0xe007fff80007fff801ffff80001ffff80007fffe0001ffffffff80007fffc00ffffffffffe0001ffffffff003ff1d10d5daa29900003f03f,0x49510153035202922ca05528154a055285528154a154a0aa50152835281291a50524514054a0d4a094a052459141d0015da2288451451451),(0x7ffffffffffffffffffffffe000000007fffffffe0000ffffffff8000000ffff003fffffffe0001ffffffc006fd62ae3438003f000fc0,0x8260226022602320480466011980466026601198019808cc02260026011b02c00640980898049804d804640902627122ac30180145145145),(0,0),(0x7fffffff8000001fffffffffffffffff8000000000000fffffffffffffff0000003fffffffffffe0000000009dae8e542564000fc0000,0x13820b820b830bc470c178305e0c1783078305e0c5e0c2f060b830b8305c23061788e182e0c0e0c0e0c1788e2381dac8e5021644d34d34d3),((sl7 0x4e1393ffc0000fff 0xfffffffffffa0659 0x3ffffffffff 0 sL31 0x1ffffffffffffff 0xfff8000000000000),0x4c004c004c008009800260009800080026000600030004c002c00260040058010013000900090009800000080448020103728a28a28a),(0,0),((sl7 0x91ddcf0000fff000 0x915a6 0xfffffc0000000000 sL31 sL31 0x1ffffffffffffff 0),0x404700470047001010e00438010e0043004380108010c0087004300438000086000021c010e010e010e001004080526005dc10b2cb2cb2c),((sl7 0x7125e06fff000000 0x4ea97 0 0 0 0xfe00000000000000 sL31),0x180780078007800601f0007c001f0007c007c001f001f000f8007c007c00380f800e03e001f001f001f000e038048a955104e00c30c30c30),(0,0)]
def g219C : List ColumnInfo := [(8,0,211,0,7)]
def g219A : List (List Nat) := [[],[113]]
def g219D7 := packet 0x7f
def g219L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g219D7)
  | _ => emptyPacking
def g219I (_ _ : Nat) : Option (Nat × Nat) := none
def g219 : Forest := ⟨219,7,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219T : checkedTables g219 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g219P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : Chart g219 K215 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 8 := lower_forest (g:=g219) (i:=0) (hints:=268460100) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 8 [(219,[]),(347,[49,100,135]),(467,[131,83]),(470,[32,99,116,83,133]),(473,[49,33,114,100,82,133])]
set_option maxRecDepth 32768 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array Signals := #[(0x7ffff00001ffffc000fffff80000fffff80000fffffffffffffff00001ffffe0007fffffffffffffffffffffffff9961a4fab95940003ff,0x51002a600d48014901650055280aa50055280aa500aa500aa5002a500d4a009480d28052405140152804a500a480a1921244a9119094a529),(0,0),((sl7 0x6f136450a0f8000 0x80000ffffe0005df 0x7ffff0003ffff 0xfffffffffe00000 0xfffff0000 0xfffffffffffff000 sL2),0x60554c0aa98155904a405566012cc05566036cc02acc06acc0554c04a980aad8156025640a9814a602b6c054c81335c70671364408739ce7),(0x7ffffffffe00000000ffffffffffffffffffff0000000000ffffffffffffffffff800000003fffffffff00000000053e3e4d5a478007c00,0x82067040ce0c19e213860678304f060678304f060cf060cf06067060ce0c0ce10983067884e1813830270606f105c013a2e491a478b5ad6b),((sl7 0x8e2545fea5f0001f 0xfffffffffffffaa5 0x3ffff 0xf000000000000000 sL31 0xfffffffffffff sL12),0x67800cf0019e009c00678002700067800270004f0004f000678006f000cf002e003780170019c003380067002600250c2144e6246318c6),(0,0),((sl7 0x795afe6252007fe0 0x245 sL24 sL31 sL31 0xfffffffffffff 0),0x478008f0011e000e0087800438008780043800870008700087800870010f0003004380018021e0043c0087800380244491a4642034a5294),((sl7 0xa5b8895b2bff8000 0x73a 0 0 0 0xfff0000000000000 sL31),0x78000f0001e0003000f80007c000f80007c000f8000f8000f8000f8001f0001c007c000e003e0007c000f8001c00218a1888919038c6318),(0,0)]
def g221C : List ColumnInfo := [(0,4,89,128,5),(0,8,149,64,5),(4,0,217,0,5),(8,0,213,0,5)]
def g221A : List (List Nat) := [[],[64,50,118]]
def g221D6 := packet 0xe413f
def g221L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g221D6)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,6,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221T : checkedTables g221 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g221P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : Chart g221 K219 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 7 := lower_forest (g:=g221) (i:=0) (hints:=536897284) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 7 [(221,[]),(237,[80,50,114,64,98]),(343,[96,49,33,64,132,116]),(455,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array Signals := #[(0,0),(0x3ffffc00007fffffffff0007fffffffe00003ffffe00003fffffffffffffe00003ffff8003fffffffffffffffff99c559a751938003f03f,0xa8140a828350504a0505220b105014154142a814154142a81055040aa020540c1a81025086814150284a050a421498055087411305145145),(0x3fffffffff80000ffffffff8003fffffffffc0000000003ffff80000fffffffffc00000003ffff80000ffffe00036ad462289af40fc0000,0x3059530b2a61656c1656445222985959818b305959839b3025660eacc14a98295305ab612b058a60b36c164c846632ad4622898f0f3cf3cf),((sl7 0x74def58a00000fc0 0xffff00000000067a sL31 0xfffffff 0xfffffffffffffffc 0x3ffff 0x3ffffffffffffff),0xc1019c00338006704067809c04e1019e0813c1019e0813c1067820cf040ce0819c1033804c1013820270406f00b806727484358a134d34d3),((sl7 0xcca8bed4bf00003f 0xffffffffffff58b1 0x3fffff 0xfffffffff0000000 sL31 0x3ffff 0xfc00000000000000),0x61e00c3c018780187808e0470061e0021c0061e0021c00478008f0018f0031e0063c0270061c00c380187008c000b00c289ec48a28a28a),(0,0),((sl7 0x2b5fcc4a40000fc0 0x48af sL22 sL31 sL31 0x3ffff 0),0x27e002fc005f8009f800f0078027e0013e0027e0013e00278004f0009f0013e0027c0038027e004fc009f800f00488d0b5bc8406cb2cb2c),((sl7 0xb7112b657ffff000 0xe754 0 0 0 sL24 sL31),0x380003000060000e0000000000380001c000380001c0003800070000e0001c000380004003800070000e00010004540a110202070c30c30),(0,0)]
def g222C : List ColumnInfo := [(0,8,150,64,6)]
def g222A : List (List Nat) := [[],[99],[65],[65,99]]
def g222D6 := packet 0x7f
def g222L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g222D6)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,6,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_0 : block g222 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222T : checkedTables g222 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g222P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : Chart g222 K221 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 7 := lower_forest (g:=g222) (i:=0) (hints:=318859072) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 7 [(222,[]),(411,[32,116,134]),(459,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array Signals := #[((sl7 0x7f4aa09de8000fff 0xfffffffffffff36d sL31 0x7fffff0000f sL30 0xffffff000003f 0xfffc0003fffffc00),0x14840582802a8280aa0a00aa0a02a8280550500aa0a00541403505004a101a0a014840502802a0a01282805210143646c0a809880249249),(0xfffffffffffffffffff000000000003fffff800000fffffffffff8000000000fffffc0003fffff000003fffff0000fbe04ebf62231fc0000,0x5590129002ab30012cc00aacc00db3001566006acc00aa98012a600556c02ac0095900a980294c00adb002a640266f8e0463e400311c71c7),(0,0),((sl7 0xc4359bd0f703f000 0xfffc0000000000a7 0x3fffffff 0xfffffffffffffff0 0xffffff sL28 0x3ffffffff),0x19e084e0b033c0b04f02c0cf02c13c0b0678160cf02c0ce05833816067021302c19e084e0b02702c09c0b037820b802744119ad0f36db6db),(0,0),((sl7 0x1674157ff000003f 0xfffffffffffff54b 0x3fffffff 0 0xffffffffff000000 sL31 0x3ffffffff),0x9e012702c33c02c2700b0cf00b09c02c2780584f00b0cf0161bc058678045c0b0de011702c3380b0ce02c338044c040b1274156770db6db6),((sl7 0xfbb7e9c20e03ffc0 0x48a sL20 sL31 sL31 sL31 0x3ffffffff),0xe002380303c00303800c0f000c0e00303800607000c0f00181c006078008600c0e002180303c00c0f00303c00870048893a461020c924924),((sl7 0x4a985f269dfc0000 0xe75 0 0 0 0 sL18),0x3c003fc0003fc000ff0000ff0003fc0007f8000ff0001fe0007f8000f800ff0003e003fc000ff0003fc000f8000714a981b268ce38e38),(0,0)]
def g235C : List ColumnInfo := [(0,2,105,128,5)]
def g235A : List (List Nat) := [[],[113],[96,83],[96,113,83]]
def g235D5 := packet 0x7f
def g235L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g235D5)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,5,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235T : checkedTables g235 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : Chart g235 K222 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 6 := lower_forest (g:=g235) (i:=0) (hints:=268460149) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 6 [(235,[]),(238,[32,49,118]),(252,[32,49,65,118])]
set_option maxRecDepth 32768 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g243Y : Array Signals := #[(0x7fffe001ffff000ffffe0000ffffffffffffffffff80003ffffffffffffffff00007fffffffffffffffc003ffd76f2131c876400ffc1f,0x500014004000200210014200a10028400a10028400508028400a10010000800a100508014200200010008008001128002088721294a529),(0xfff80000001ffffffffffffffff00003ffff00003ffffffffc0000ffff8007ffffffff80001ffff000fffffffc003891d26fa15c81f003e0,0x92602498128092409002498024c04930024c029300926011300a4c02120290124c024601298048404a0249012012b8110263015486318c63),(0,0),(0,0),((sl7 0x8eba768b7e0003ff 0xffffffffffcc30 sL23 0xffffff00000007ff 0x3fffffff 0xfffffffffffffc sL23),0x24804920240124812404920049001240149005240124802240109004a4052024900488024200928094049202402404008c18648848421084),((sl7 0x64166f4d80007c00 0xff00000000000353 sL31 0x7ff sL20 sL1 0),0xc70571c0c715c70638a71c148e0a638298e0a63829c7053b829ce0a73829c538e0a710538c14e30518a71c14714702536416670dad6b5ad6),(sR19,0xf8067e017819f80bc0c7e018f00c7c031f00c7c031f8063c031f00c7c04e063f00c7e063f018fc09e0c7e027827804569b45570c2d6b5ad6),(sR102,0x78001801e000c00f8001f000f8003e000f8003e0007c003e000f8007007c000f8007c001f000e00f80038038003aa51849201318c6318),(0,0)]
def g243C : List ColumnInfo := [(32,0,211,0,7)]
def g243A : List (List Nat) := [[],[101],[113],[113,101]]
def g243D7 := packet 0x7f
def g243L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g243D7)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,7,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243T : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g243P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : Chart g243 K235 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 8 := lower_forest (g:=g243) (i:=0) (hints:=268435524) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 8 [(243,[])]
set_option maxRecDepth 32768 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g245Y : Array Signals := #[(0x7fffe001ffff000ffffe0000fffffffff80003fffffffffffffffffffffffff00007ffffffff8007fffffffffde2d8339c932c00f83ff,0x500014004000200210014200a10028400508028400a10028400a10010000800a100508014200100100008008001a29002080321294a529),(0,0),(0xfff80000001ffffffffffffffff00003ffffffffc0000ffffc0000ffff8007ffffffff80001fffffff8007fffc0039d3724fa05c01f07c00,0x28601458118051408801458022c028b00516010b00a2c008b0062c010a02500a2c014600a58028a02402500a1011b953224b001006318c63),(0,0),((sl7 0xe9a768b7e00001f 0x7ffffffcd32 sL23 0xffffff00000007ff 0xfff 0xfffffffffffffc sL23),0xb2805960250165812c0596004b0032c0165803ac01cb0052c014b005ac05602cb0058802c600b2c04e04e02ca02505120e1a64884c6318c6),((sl7 0xe4366f4d80007fe0 0xfffff80000000251 sL31 0x7ff 0xfffffffffffff000 sL1 0),0xc3056180c615860630a618148c0a430298605230290c0a630298c0a630298530c0a610530814c30288288530c1460000c4146f4da94a5294),(sR19,0xfc067e017819f80bc0c7e018f00c7c031f8063c031f00c7c031f00c7c04e063f00c7e063f018fc04f04f063f027804569b45570c2d6b5ad6),(sR102,0x78001801e000c00f8001f000f8003e0007c003e000f8003e000f8007007c000f8007c001f0007007007c0038002a851849301b18c6318),(0,0)]
def g245C : List ColumnInfo := [(64,0,181,0,7)]
def g245A : List (List Nat) := [[],[114,84]]
def g245D7 := packet 0x7f
def g245L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g245D7)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,7,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245T : checkedTables g245 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g245P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : Chart g245 K243 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 8 := lower_forest (g:=g245) (i:=0) (hints:=536872196) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 8 [(245,[]),(373,[100,135]),(437,[32,116,134]),(485,[32,132,118])]
set_option maxRecDepth 32768 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g469Y : Array Signals := #[(0xfffc0003fffffffc007fffe0000ffffc0003ffff0000ffffffffc0001ffff001fffe003fffffffffffffffffffffcc65acb88be2400003ff,0x202a902a202a10098149015240a9202a502a480a940a900a9202a4815200a5052004a0a4815240a92025012404a00c04aca083a22318c631),(0,0),(0xfffffffc0003fffffffffffffff000000003ffffffff0000ffffffffe0000001ffffffffffe0000ffff001fffe003b843a5ae0e501f07c00,0xab005300ab00550140055800ac00ab006b002ac012c02ac00ab0029802ac05802a80a0015801ac0094034014805a980225a806506318c63),(0,0),((sl7 0x3d9111a400f801f 0x1ffffffef3b 0x3ffffffff0 sL30 0xfffc000000000000 0x7fffffffffffff sL24),0xcc006400cc086602610660413020cc084c0833021b0233020cc08320433009043301308260413020d805841900923390358101054a5294a),(0,0),((sl7 0xe5744e4dbe0003e0 0xfffffe0000002059 0x3fffffffff 0 sL31 0x7fffffffffffff 0),0x4f0027804f002780380278009c004f00070013c001c003c004f0013c00bc00e00bc01c0138009c004e006009e00e20590054484d8c6318c6),((sl7 0x9a07773c000ffc00 0x2456 0xffffffc000000000 sL31 sL31 0x7fffffffffffff 0),0x7003380370033802c0638018e00c700318031c00c600c400c70031c018c009018c012031c018e00c7009818e0130044698056708294a5294),((sl7 0x5dc49781bff00000 0x13aa 0 0 0 0xff80000000000000 sL31),0x8003c0038003c003007c001f000f8003e003e000f800f800f8003e001f000e01f001c03e001f000f800e01f001c012225d801780318c6318)]
def g469C : List ColumnInfo := [(16,0,453,0,5),(17,0,452,0,4),(65,0,404,0,4),(132,0,337,0,4),(144,0,325,0,4),(260,0,209,0,4),(320,0,149,0,4)]
def g469A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118],[64,130,118],[64,130,112,96,98],[96,114,64,132,66],[96,114,132],[112,98,66,128],[112,98],[128,66],[128,66,98,112]]
def g469D5 := packet 0xbbd8940
def g469D6 := packet 0x40c3fa81fd10
def g469H6 := packet 0xa0
def g469D7 := packet 0x6b1667f
def g469H7 := packet 0x1c81000312a10053001e35280001e70000362002
def g469L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g469D5)
  | 6 => (2,1,3,0,0,3,0,g469D6)
  | 7 => (1,0,3,65537,0,0,1030,g469D7)
  | _ => emptyPacking
def g469I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g469H6
  | 7 => lookupWord 2 17 2 9 1 4 g469H7
  | _ => fun _ => none
def g469 : Forest := ⟨469,7,fun i => g469Y[i]?.getD (0,0),g469C,g469A,g469L,g469I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P5_0 : block g469 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P6_0 : block g469 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P7_0 : block g469 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469T : checkedTables g469 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g469P5_0
  · exact g469P6_0
  · exact g469P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469G : Chart g469 K245 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low469 : Lower true (varsX 469) (graphGoal 469) 8 := lower_forest (g:=g469) (i:=0) (hints:=9126807300) (before_sound K245 V245) g469G g469T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K469 := extendKnown K245 8 [(469,[])]
set_option maxRecDepth 32768 in
theorem V469 : Known true K469 := extend_ok (m:=469) V245 low469 (by decide +kernel)
def g474Y : Array Signals := #[(0,0),(0x3fff07fff8001ffffffe0ffff0000ffff0003fffc000fffffffc000ffff07ffffffff0003ffffffc1ffffc92d389940f740000007fc01ff,0x2800a11045209404500842208a208a208a2228822888a2028822884a208a110840208a212880a2008441100829308000f708a45229148a45),(0,0),(0xfc00007ffffffe0007ffffffffffff00000003fffffff0003fffffff000007ffe0fffffffc000ffffffff81a52a0abb8d8801ff00003fe00,0xb022c20216041821604280042c042c042c08b010b002c08b010b000c042c200282042c043012c0450008209a50a02b1090026130984c2613),(0x7ffffffffff80000fffffffffffffffc00000000003ffffffffffff80000fffffffffff00001ffffefe1835e2102c0000ff80001ff,0xc10b04209801200982130441304130413040c104c113042c104c10904130021304413040410304160882402700815a2100d148a45229148a),(0,0),((sl7 0x4d3fe0000003fe00 0xfe0000209965726e sL1 0xc000000000000000 sL31 0xffffffffff 0xffffff8000000000),0x4c0004e009c04e009c0809c009c009c0030027001c0030027002e009c0405c0809c00980240098001381208141106c4d0582c160b0582c),((sl7 0x3c00000ffffc0000 0x24d69a0557 0xff00000000000000 sL31 sL31 0xffffffffff 0),0x2700847004e017004e0108e008e008e008c0238022008c0238023008e000460008e008e023808e0111c0200d60a05560826130984c26130),((sl7 0x81bffff000000000 0x132a5dc497 0 0 0 0xffffff0000000000 sL31),0x380007800700180070000f000f000f000f003c003c00f003c003c00f000878010f000f003c00f0021e004012a1cc48300b81c0e070381c0)]
def g474C : List ColumnInfo := [(0,2,328,144,6),(0,8,146,320,6),(0,16,328,130,6),(0,64,146,264,6),(0,128,328,18,6),(2,0,472,0,6),(8,0,466,0,6),(16,0,458,0,6),(64,0,410,0,6),(128,0,346,0,6)]
def g474A : List (List Nat) := [[],[134],[116],[116,134],[99],[99,131],[99,116],[99,116,131],[131,99],[131],[131,116,99],[131,116],[49,100,135],[49,100,116,132],[49,132,100,118],[49,132,118],[49,65,97,135],[49,65,97,113,129],[49,65,129,97,118],[49,65,129,118],[49,113,100,65,132],[49,113,100,129],[49,113,132,97],[49,113,132,100,97],[65],[65,134],[65,113],[65,113,134],[65,99],[65,99,131],[65,99,113],[65,99,113,131],[65,131,99],[65,131],[65,131,113,99],[65,131,113],[97,49,67,135],[97,49,67,116,132],[97,49,132,67,115],[97,49,132,115],[97,67,135],[97,67,113,129],[97,67,131,115],[97,67,131,113,49],[97,115,67,132],[97,115,67,65,129],[97,115,132],[97,115,132,65],[113,65],[113,65,134],[113],[113,134],[113,99,65],[113,99,65,131],[113,99],[113,99,131],[113,131,65,99],[113,131,65],[113,131,99],[113,131],[129,49,67,100,118],[129,49,67,118],[129,49,100,115],[129,49,100,116,67],[129,67,97,118],[129,67,118],[129,67,99,49,115],[129,67,99,115],[129,115,67,97,100],[129,115,67,100],[129,115,100,65],[129,115,100]]
def g474D8 := packet 0x94837261502bf
def g474L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,g474D8)
  | _ => emptyPacking
def g474I (_ _ : Nat) : Option (Nat × Nat) := none
def g474 : Forest := ⟨474,8,fun i => g474Y[i]?.getD (0,0),g474C,g474A,g474L,g474I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474P8_0 : block g474 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g474T : checkedTables g474 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g474P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474G : Chart g474 K469 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low474 : Lower true (varsX 474) (graphGoal 474) 9 := lower_forest (g:=g474) (i:=0) (hints:=13203759168) (before_sound K469 V469) g474G g474T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K474 := extendKnown K469 9 [(474,[])]
set_option maxRecDepth 32768 in
theorem V474 : Known true K474 := extend_ok (m:=474) V469 low474 (by decide +kernel)
def g127Y : Array Signals := #[((sl7 0x1e4500ff00ff00ff 0x4e9d22197ea01eb8 0x3fffffee484 sL29 0xffffff800000003f 0x3ffffffffff sL26),0x955400002955000015aa80000a95400002a950000155a80000aa9400002aa90005558002aa840044a8502181c800e981a00010101010101),(0x1ffffffffffffffffc00000001ffffffffffffffffc00000001ffffffffffffffc000000ab697b034497848c7c13b9ab00000000ff00,0xd9988a283266228a193311450cd988a283326228a199311450ccd88a2833320889990444cccab696a030493048c7c12b889555555555555),((sl7 0x461a0000ff000000 0xba158933917d287a 0x1527e 0xffffffe000000000 sL31 0x1ff 0xffffe00000000000),0x2e1e02c02bc780b00de3c05806f1e02c02bc380b009e1c05804f0e02c02bc3c101e1e080f0f0507cba15801391352878461a333333333333),((sl7 0x4cb4ff0000000000 0xf8e218d25092a39d 0x13b9d 0 0 sL27 sL31),0x4fe0000b33f80002c9fc000164fe0000b33fc0002cdfe000166ff0000b33fc0012fe00097f01239d58c218d25090229d4c340f0f0f0f0f0f),((sl7 0xe57e00000000ffff 0x9308e7c496e3c0b5 0xffffffffffff40c9 sL31 sL31 sL31 sL31),0x7000130c3c0004c30e00026187000130c3c0004c30e00026187000130c3c000223000111800100809108e144826380254576aaaaaaaaaaaa),(0x122a64d6ea9e0695f7e4321910000ffff0000,0x80001c0fc0000703f0000381f80001c0fc0000703f0000381f80001c0fc000043c00021e00012282056a29e0604a50032181cccccccccccc),(0x9d52a4f3b55f8326d10e5b80ffff00000000,0x1ff0000007fc000003fe000001ff0000007fc000003fe000001ff0000007c00003e000009c42a430a5058326d1020180f0f0f0f0f0f0),(0,0),(0,0)]
def g127C : List ColumnInfo := [(2,0,125,0,7)]
def g127A : List (List Nat) := [[],[50,101],[33,84],[33,49,84,100],[49,33,100,84],[49,100]]
def g127D7 := packet 0xff
def g127L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g127D7)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,7,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127T : checkedTables g127 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g127P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : Chart g127 K474 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 8 := lower_forest (g:=g127) (i:=0) (hints:=25924) (before_sound K474 V474) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K474 8 [(127,[])]
set_option maxRecDepth 32768 in
theorem V127 : Known true K127 := extend_ok (m:=127) V474 low127 (by decide +kernel)
def g223Y : Array Signals := #[((sl7 0x6d8bc0000003f03f 0x8241494599e356c9 0xfff800000fffffee sL0 sL26 0xfffffff80000003f 0xf80000003fffffff),0x52801aaa94009554a00295528015aa9400a954a002a95280155a9400aa94a002aa9201556402aa8e8041490518e156c9040b411451451451),(0xffffffffc0000001ffffffffffffffc0000001ffffffffffffffc0000001fffffffffffff000000afa9ffc3060045308544d6c003f000fc0,0x600a13330050d998028326600a19330050cd98028332600a19930050ccd80283332022664044ccc2a29dd82020045108544d685145145145),((sl7 0x3a196c0fc0000000 0x2be74a28b1790895 21 sL25 0x1ffffffffff 0 sL30),0x802c5c3c0162e1e00b2bc7802cde3c0166f1e00b2bc3802c9e1c0164f0e00b2bc3c04787808f0f142be74828a13900953a196cf3cf3cf3cf),((sl7 0x9212d00000fc0000 0xb5ff181f8265b242 19 0 0xfffffe0000000000 sL31 sL31),0x3009fc01804fe00c033f803009fc01804fe00c033fc0300dfe01806ff00c033fc040bf80817f00395f71817826592421212c134d34d34d3),((sl7 0xa936eff000000fff 0xcb260d0ce115566 0xfffffffffffffff4 sL31 sL31 sL31 sL31),0x30e000018700000c3c000030e000018700000c3c000030e000018700000c3c00008c00011800100c2220d0c6100004a91084a28a28a28a),(0,0),(0x122a49a54f279ea821f695300000fff000,0x43f000021f800010fc000043f000021f800010fc000043f000021f800010fc00000f00001e000102a08a448251a2820e08432cb2cb2cb2c),(0x9d5249ea134f8aebe00ea03ffff000000,0x7c000003e000001f0000007c000003e000001f0000007c000003e000001f000000700000e0000095000060110c0ae2200a2030c30c30c30),(0,0)]
def g223C : List ColumnInfo := [(4,0,219,0,8)]
def g223A : List (List Nat) := [[]]
def g223D8 := packet 0xff
def g223L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g223D8)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,8,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223T : checkedTables g223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g223P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : Chart g223 K127 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 9 := lower_forest (g:=g223) (i:=0) (hints:=268461892) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 9 [(223,[]),(463,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array Signals := #[(0x7fffffffc00000003fffffffffffffffffffffffe00000001ffffffff0000007fffffffffffffd504a283598ceac015ff2f19400001fc07f,0x50012aa828016aa828014aa8280152a82800aa541400aad41400554a100aad05002aa90805551500a2814884e28005fe270008912244891),(0x80000000000000003fffffffc00000003fffffffffffffffe000000000000007fffffff80000035f57ea93407101929443e4ec07f0000000,0x555b33002adb33002a5933002ad9b3002aacc980154cc980155666c01333600553332009999a5557ea91407101029442c4ec78f1e3c78f),((sl7 0xe8182bf800003f80 0xf8fdd464cc534485 0xa5 sL29 0x3fffffffffffffff 0xc000000000000000 sL31),0x181c3c000c1c3c000c1e3c000c1e3c000c0f0e00060f0e000607870021c3800183c3c010e1e00478ac9460c0134085e818202850a14285),((sl7 0x7532d0000fe00000 0x3bf208a34b426aaa 0x276 0 0xc000000000000000 sL31 sL31),0x16019fc00b009fc00b009fc00b009fc00b00cff005806ff0058067f80205fc01601bfc0102fe00723af208834b42628a7130d19b366cd9b3),(0,0),((sl7 0xd795f80000003fff 0x925c231f125b8f02 0xfffffffffffffe81 sL31 sL31 sL31 sL31),0x5861e0002c30e0002c30e0002c30e0002c30f000161870001618780004460005861c0002230002818050231710408f001585db56ad5ab56a),(0x2454d25baa781a57df90c8644000fffc000,0x607e0000303f0000303f0000303f0000303f0000181f8000181f80000878000607e000043c0002054505a22480851d200c860664c993264c),(0x13aa493ced57e0c9b44396e03fff0000000,0x7f8000003fc000003fc000003fc000003fc000001fe000001fe000000f800007f8000007c000012a80114a950e0c9940112203870e1c3870),(0,0)]
def g239C : List ColumnInfo := [(2,0,237,0,7)]
def g239A : List (List Nat) := [[],[32,49,118]]
def g239D7 := packet 0xff
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
theorem g239T : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g239P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : Chart g239 K223 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 8 := lower_forest (g:=g239) (i:=0) (hints:=268461429) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 8 [(239,[])]
set_option maxRecDepth 32768 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array Signals := #[(sR64,sR71),(sR89,sR80),(sR20,sR29),(0,0),(sR96,sR42),(sR108,sR56),(sR4,sR59),(sR2,sR62),(0,0)]
def g247C : List ColumnInfo := [(64,0,183,0,9)]
def g247A : List (List Nat) := [[]]
def g247D9 := packet 0xff
def g247L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247T : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g247P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : Chart g247 K239 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=268436804) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 10 [(247,[]),(439,[32,116,134]),(493,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array Signals := #[((sl7 0xe0000000ffff00ff 0xaaaa2a40d5b2c2c0 0xf00000fffff785cb 0x1fffffffffffff sL25 sL31 0x7ffffffffffff),0x55050002a828000a82800128280014840050280005414000d41400094140005210016100147008a2a22220014b2c0004021212121212121),(0xfff80000003ffffffc0000003ffffffc00003fffffffffffffe0000001ffffffffffff000005217c25ccb4a338e639105b00ff000000ff00,0x8660024a330012113001231b00122190044980122898009149800914d8009146401124011261015c248c208318c609105a0b0b0b0b0b0b0b),(0,0),((sl7 0xf0000ff00000000 0x77636101c5a51f25 0xb5a46 0xfffffffffe000000 sL0 sL20 0x3fffff),0xd781601cbc0b00a5c0b00a5c0b00b5e080ae0b00b2e058058e058058e05805978202782027834a4267636001c5a41f250367676767676767),((sl7 0x13ff00000000ffff 0x6834129cb24837ce 0xfffffffffffa5e21 sL31 sL0 0 sL22),0x18000490c00024c600024c600024c60009300024c300012610001261000126180024400244081e2100101008a00836cc0114141414141414),((sl7 0x3800000000ff0000 0xd4c86db6ed18390d 0x886cb 0 0xffffc00000000000 sL31 sL31),0xe005871f002c38f802c38f802c38f80111c02c38fc0161c7e0161c7e0161c7e00447804478088641d4c84db6e908390d38dedededededede),(sR7,0x607e000303f000303f000303f00021e00303f000181f800181f800181f8000878008780081534908489ee020920808c98989898989898),(sR6,0x7f800003fc00003fc00003fc00003e0003fc00001fe00001fe00001fe00000f8000f80004e0824b60cd340321802280e0e0e0e0e0e0e0),(0,0)]
def g251C : List ColumnInfo := [(8,0,243,0,8),(32,0,219,0,8),(0,32,218,1,7),(2,0,249,0,7),(64,8,179,0,7),(128,0,123,0,7),(0,2,105,144,6),(0,128,105,18,6),(1,0,218,0,6),(1,32,218,0,6),(16,0,235,0,6),(2,128,105,16,5),(16,2,105,128,5),(16,128,105,2,5),(130,0,121,0,5),(18,128,105,0,4)]
def g251A : List (List Nat) := [[],[113]]
def g251D6 := packet 0x309bd87cc640abf864c640
def g251D7 := packet 0xf116a0a0328230220205354cc31202d3bbe564b025c2d617cc5d314dd85737df7fb7cff3190131
def g251H7 := packet 0x1e00
def g251D8 := packet 0x2fa104ce66304d652130f96043b003be6018ee018ef02384f3994b6cd10286a38b1349a8068503c271300ac3cc698f30a61440a1a40ffef
def g251H8 := packet 0x15590004401efe800008c03c3c9
def g251D9 := packet 0x12a62837f
def g251H9 := packet 0x2a8017800000000ca180000000000000000000000000002cc00009c00000002440000000154f750038000000000000001
def g251L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g251D6)
  | 7 => (6,2,4,262147,34,6,1033,g251D7)
  | 8 => (8,1,4,131073,16,8,1043,g251D8)
  | 9 => (1,0,4,0,0,0,0,g251D9)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 1 0 g251H7
  | 8 => lookupWord 2 13 1 8 3 1 g251H8
  | 9 => lookupWord 2 59 1 8 3 1 g251H9
  | _ => fun _ => none
def g251 : Forest := ⟨251,9,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_2 : block g251 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 6=true := (@block_merge g251 7 0 2 4 g251P7_0 g251P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2 : block g251 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 8=true := (@block_merge g251 8 0 2 6 g251P8_0 g251P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251T : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g251P6_0
  · exact g251B7
  · exact g251B8
  · exact g251P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : Chart g251 K247 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 10 := lower_forest (g:=g251) (i:=0) (hints:=268460100) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 10 [(251,[]),(379,[49,100,135]),(494,[32,49,132,118]),(499,[131]),(502,[32,99,116,131]),(508,[32,49,65,129,118])]
set_option maxRecDepth 32768 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array Signals := #[(0x7fffffffffffffe0000001ffffffffffffff00000fffffffffffffffffffffffffffffff705c92e8e16429de2c2c0c3000000ff00ffff,0x55050002a8280005414000d41400094140005210016100140a0002a0a0004a0a0005210014500c80a0a020019e2c2004121212121212121),(0,0),(0xfff80000003fffffffffffffe0000001ffffffffffff00000fffffff0000000fffffff000005b95e9144b8a160f633117200ff0000ff0000,0x26600142b3000a0a980050a980050ad80050564010a4010a6002814c002836c0028264010661995c8004188140d60311520b0b0b0b0b0b0b),((sl7 0xe0000ff00000000 0xc76b6101d5a51f24 0xbd2e4 0xffffffffffffff0 0 sL30 0x3fffff),0xb781601b3c0b00ace05804ce05804ce0580567820338203382c02a702c02a702c02b78202b83d2e0476b6001d5a41b240267676767676767),((sl7 0x12ff0000000000ff 0xc8341a9cb24837ce 0xfffffffffffadea1 sL4 0 0 sL22),0x38000593c0002ccf000166f000166f000166780025c0025c000b338000b338000b3380024c0ade2180141888a00835cc121e1e1e1e1e1e1e),((sl7 0x3900000000ffff00 0x74c865b6ed18390d 0x8064b 0xf000000000000000 sL31 sL31 sL31),0xc005861c002c30f0016187001618700161878004460044600b0c3c00b0c3c00b0c3c00447008060374c06536a408380c28d4d4d4d4d4d4d4),(sR7,0x607e000303f000181f800181f800181f80008780087800c0fc000c0fc000c0fc0008780080514908489ee020924818c98989898989898),(sR6,0x7f800003fc00001fe00001fe00001fe00000f8000f8000ff00000ff00000ff00000f8000420824f60c5360b21802280e0e0e0e0e0e0e0),(0,0)]
def g253C : List ColumnInfo := [(0,8,181,64,8),(8,0,245,0,8),(4,0,249,0,7),(16,0,237,0,7),(32,0,221,0,7),(64,8,181,0,7),(128,0,125,0,7),(0,4,89,160,6),(1,0,252,0,6),(4,128,105,16,5),(16,128,105,4,5),(32,4,89,128,5),(36,0,217,0,5),(132,0,121,0,5),(20,128,105,0,4)]
def g253A : List (List Nat) := [[],[114,84]]
def g253D7 := packet 0x400e040000c0400000200802582231c2f569305cae4c78a0a016e0e5d2e98db7432e8750ccb9cb7306ec85da3ba0fbdfedf3f8c21050d314c110
def g253D8 := packet 0x779004dec09297025bd01288a8250404ac9039801126b1d609d22520c458e358e79634e3926120050d61505318c13084110ff
def g253H8 := packet 0x8803210060004988003500000020073a280b80a70
def g253D9 := packet 0x2c864a37f
def g253H9 := packet 0xd00001c80000000004ac00000000000002d40022f00000000000000000000f1a7401246800000000000001c000000000019c2
def g253L : Nat → Packing
  | 7 => (11,2,4,262150,35,7,1029,g253D7)
  | 8 => (8,1,4,65537,0,8,1041,g253D8)
  | 9 => (1,0,4,0,0,0,0,g253D9)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 17 4 9 4 1 g253H8
  | 9 => lookupWord 3 53 2 8 3 1 g253H9
  | _ => fun _ => none
def g253 : Forest := ⟨253,9,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_3 : block g253 7 3 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 11=true := (@block_merge g253 7 0 3 8 g253P7_0 g253P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253T : checkedTables g253 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g253B7
  · exact g253P8_0
  · exact g253P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : Chart g253 K251 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 10 := lower_forest (g:=g253) (i:=0) (hints:=536896772) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 10 [(253,[]),(375,[49,100,135]),(445,[32,116,134]),(487,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array Signals := #[(0,0),(0x80000000fffffffffffffffc00000007fffffff000007ffffffffffffffffffffffffffff606845947e807eb553a18e5c00000ffc00003ff,0x8a50aa01148154022840a80451835008a20520110b008a282a011450940228a148044280020450432805eb503a18e14154551545515455),((sl7 0xf003ff00000ffc00 0x9581dd19d0eb8a9a 0xfffc000000f031b0 0xffff00000001ffff sL31 sL31 0xffffffff00000001),0x2c04cc0058159800b0153001602a6002c056402052002c014c005806d800b00990080cc030119095818419c0ea8888a0cc330cc330cc33),((sl7 0x900000003ff00000 0x481b2fce82f63582 0xcbe5a8c sL25 0x7fff sL29 1),0x1400e6f02801d9e0500299c0a0053381400b6782029c1400b270280164e05002cde0809704b45a0848092bce80762582943d0f43d0f43d0f),((sl7 0x9ffc0000000003ff 0x24a5a2c12a43cd4d 0xffffffffff61cf82 sL31 0x7fff 0 sL30),0x130870002611e0004c31e0009863c00130c780044e00130c3800261870004c30e0011181e61c1820485a2000241c50c92a8aa2a8aa2a8aa),((sl7 0x70000000000ffc00 0x8a5ccbae3c495753 0x184c9930 0 0xffffffffffff8000 sL31 sL31),0x59c0f800b381e0016703e002ce07c0059c0f8004870059c0fc00b381f8016703f00121e0184c88200a5c4ba63c0157535f33ccf33ccf33cc),(0x1a6a64d6ea9e8415f7a43319000000003ff00000,0x61ff0000c3fe000187fc00030ff800061ff00008f80061ff0000c3fe000187fc00023e001a4a24d6a2968411778012190bc2f0bc2f0bc2f0),(0x1952a4f3b5578326d10e4b80fffffffc0000000,0x7e000000fc000001f8000003f0000007e000000f00007e000000fc000001f8000003c00001842a0d285058002d0020100c0300c0300c0300),(0,0)]
def g254C : List ColumnInfo := [(0,8,182,64,8)]
def g254A : List (List Nat) := [[],[99],[65],[65,99]]
def g254D8 := packet 0xff
def g254L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g254D8)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,8,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254T : checkedTables g254 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g254P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : Chart g254 K253 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 9 := lower_forest (g:=g254) (i:=0) (hints:=320955712) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 9 [(254,[]),(382,[49,100,135]),(443,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g471Y : Array Signals := #[(sR98,sR66),(sR36,sR68),(sR94,sR84),(0,0),(sR104,sR86),(0,0),(sR110,sR23),(sR0,sR30),(sR3,sR35)]
def g471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(16,0,455,0,7),(128,0,343,0,7),(144,0,325,0,4)]
def g471A : List (List Nat) := [[],[32,116,134]]
def g471D7 := packet 0x17ddc553
def g471D8 := packet 0x76cba85923fd53
def g471H8 := packet 0x40
def g471D9 := packet 0x7d63447f
def g471H9 := packet 0x60
def g471L : Nat → Packing
  | 7 => (1,2,3,0,0,0,0,g471D7)
  | 8 => (1,1,3,0,0,0,0,g471D8)
  | 9 => (1,0,3,65537,0,0,1031,g471D9)
  | _ => emptyPacking
def g471I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 g471H8
  | 9 => lookupWord 1 2 0 4 0 0 g471H9
  | _ => fun _ => none
def g471 : Forest := ⟨471,9,fun i => g471Y[i]?.getD (0,0),g471C,g471A,g471L,g471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_0 : block g471 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_0 : block g471 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_0 : block g471 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471T : checkedTables g471 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g471P7_0
  · exact g471P8_0
  · exact g471P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471G : Chart g471 K254 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 10 := lower_forest (g:=g471) (i:=0) (hints:=8858371908) (before_sound K254 V254) g471G g471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K471 := extendKnown K254 10 [(471,[]),(477,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V471 : Known true K471 := extend_ok (m:=471) V254 low471 (by decide +kernel)
def g475Y : Array Signals := #[(0x1fffffffffffe000003fffffc000fffffffffffffff800000fffffffffffe0007ffe56e1be36cec4440a35203000000000007fc01ff,0x94a1552941552940552941aa52812891a94a0a448a4a50154a506a94a0952940a448b122856e1ba240ec4440a35002a8d46a351a8d46a351),(0xfffffe000001fffffffffffc000000000fffffe0007fffffffffff000001fffffffff8000806bdacc591e606033dc40000001ff00003fe00,0x1801983011983008983001306011b102c1800c88130c02260c024c1804d83008c8812204c802b5a8450144060319c4229148a45229148a45),(0,0),((sl7 0x7fc0000ff8000000 0x20515076f1e800 0x1cf8ccb5 sL25 0xf0000000007fffff sL31 0x1ffff),0xc5e00185e00182e00185c00305c023000c2f011c0060b800607000c0e00182f011c0470438c8b50020411062e1e00984c26130984c2613),((sl7 0x3fe0000003ffff 0xb35424ab01a0bb00 0xffffffffe6b040cb sL31 0x7fffff 0 sL25),0x200600400600401300401600802600040200b000201004c010048020090040130000000002904041a210208800a01945229148a45229148a),(0,0),((sl7 0x8000000ffffc0000 0xac2a998d9a8a1cff 0x1099718 0 sL21 sL31 sL31),0x10800021800021c00021800043800000010c00000008700008700010e00021c0002000800000408ac029009180a1c160b0582c160b0582c),(0x22e6a165acbca6174053400003ffff000000000,0xc1f00183e00183e00183e00307c002380c1f0011c060f80060f800c1f00183e0011c0470002c0a1618ca8a61740420984c26130984c26130),(0x19d52160534a2adc6d5842ffffc0000000000000,0xfe0001fc0001fc0001fc0003f80003c00fe0001e007f00007f0000fe0001fc0001e0078019c5214053482ac4051002e070381c0e070381c0)]
def g475C : List ColumnInfo := [(1,0,474,0,9),(2,0,473,0,8),(128,0,347,0,8),(256,0,219,0,8),(0,2,329,144,7),(0,8,147,320,7),(0,16,328,131,7),(0,64,146,265,7),(0,128,329,18,7),(0,256,147,72,7),(16,0,459,0,7),(64,0,411,0,7),(130,0,345,0,7),(264,0,211,0,7),(1,16,328,130,6),(2,16,328,129,6),(8,64,146,257,6),(16,2,329,128,6),(16,128,329,2,6),(64,256,147,8,6),(18,0,329,0,5)]
def g475A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g475D6 := packet 0x61fe1b7550931
def g475D7 := packet 0x1a390dd7bab5fd093150931
def g475H7 := packet 0x40
def g475D8 := packet 0x78408805841044708a041290fc7b080e18406db8208b3af6b25201ffd0b31ffe8498ffd424c6fdb82875fdd531
def g475H8 := packet 0x38bb00000180001e12
def g475D9 := packet 0x1f80c70fe077080e001ce8067e0410f81043dc01a23ca18d4d20d01c5b492cc4608f766354422b150090d4310f41507314c521ff
def g475H9 := packet 0x233a0513c0800000007004490f0c42c0ac0
def g475D10 := packet 0xdac07f
def g475H10 := packet 0x224000000000000254000000000000000000c6003007c988000000000000085000000000000000a0c0048bd80000051c00c840000000001410000000000000000000000292003c40000000000002b1000003a000000c200000ed0000000000000003a30000000000000000000000000f5c00000001cc000000000000003d10000000000000000000000000000000000000000000000000000253
def g475L : Nat → Packing
  | 6 => (1,4,5,0,0,0,0,g475D6)
  | 7 => (2,3,5,65538,1,4,1025,g475D7)
  | 8 => (5,2,5,0,0,8,0,g475D8)
  | 9 => (8,1,5,65537,0,8,1041,g475D9)
  | 10 => (1,0,5,65537,0,0,1027,g475D10)
  | _ => emptyPacking
def g475I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g475H7
  | 8 => lookupWord 1 11 0 7 1 2 g475H8
  | 9 => lookupWord 2 17 4 10 3 3 g475H9
  | 10 => lookupWord 6 127 0 10 3 3 g475H10
  | _ => fun _ => none
def g475 : Forest := ⟨475,10,fun i => g475Y[i]?.getD (0,0),g475C,g475A,g475L,g475I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P6_0 : block g475 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P7_0 : block g475 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_0 : block g475 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_2 : block g475 8 2 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B8 : block g475 8 0 5=true := (@block_merge g475 8 0 2 3 g475P8_0 g475P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P9_0 : block g475 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P10_0 : block g475 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475T : checkedTables g475 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g475P6_0
  · exact g475P7_0
  · exact g475B8
  · exact g475P9_0
  · exact g475P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475G : Chart g475 K471 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low475 : Lower true (varsX 475) (graphGoal 475) 11 := lower_forest (g:=g475) (i:=0) (hints:=13153361988) (before_sound K471 V471) g475G g475T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K475 := extendKnown K471 11 [(475,[]),(478,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V475 : Known true K475 := extend_ok (m:=475) V471 low475 (by decide +kernel)
def g501Y : Array Signals := #[(sR77,sR65),(0,0),(sR78,sR25),(0,0),(sR21,sR54),(sR95,sR73),(sR107,sR39),(sR1,sR75),(sR5,sR76)]
def g501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7)]
def g501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def g501D7 := packet 0x800603b9b73fbddd10
def g501D8 := packet 0x6cba8591ffd10
def g501H8 := packet 0x4060
def g501D9 := packet 0x7d63447f
def g501H9 := packet 0x6
def g501L : Nat → Packing
  | 7 => (2,2,3,131073,16,4,1025,g501D7)
  | 8 => (1,1,3,0,0,0,0,g501D8)
  | 9 => (1,0,3,65537,0,0,1031,g501D9)
  | _ => emptyPacking
def g501I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 5 1 0 g501H8
  | 9 => lookupWord 1 2 0 4 0 0 g501H9
  | _ => fun _ => none
def g501 : Forest := ⟨501,9,fun i => g501Y[i]?.getD (0,0),g501C,g501A,g501L,g501I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_0 : block g501 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_1 : block g501 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B7 : block g501 7 0 2=true := (@block_merge g501 7 0 1 1 g501P7_0 g501P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P8_0 : block g501 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P9_0 : block g501 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501T : checkedTables g501 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g501B7
  · exact g501P8_0
  · exact g501P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501G : Chart g501 K475 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low501 : Lower true (varsX 501) (graphGoal 501) 10 := lower_forest (g:=g501) (i:=0) (hints:=9126806788) (before_sound K475 V475) g501G g501T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K501 := extendKnown K475 10 [(501,[])]
set_option maxRecDepth 32768 in
theorem V501 : Known true K501 := extend_ok (m:=501) V475 low501 (by decide +kernel)
def g255Y : Array Signals := #[(0xf80000000003ffffffffffffffffffff80000001fffffff9d0800168592d242c871992f42c5013fd0121dec000000000007ff001ffc007ff,0x5050000155a8280000aa941400002aa908002aac2000aaa1d000002800250428051190d4244003e001215ec1012024048090120240480901),((sl7 0x3ff800 0xeb470cf000001ffc 0x38068264b80fb782 0x210982324f1cecc 0xfffffffe00000006 0x1ffffffffff sL24),0x600228a19930011450ccd8008a28333200444cc8011133320200882300518ccc28048260380eb382e3070cf0550aa1542a8550aa1542a855),((sl7 0xffe00000000 0x24accbe000ffe000 0x4913e10b26a4090b 0xb0e6fc9a005297cc 0 0xfffffe0000000000 sL31),0x8000b009e1c0005804f0e0002c02bc3c0080f0f00203c3c0b086dc9a0042978c411381032484010b202c88e0330660cc198330660cc19833),(0x3ec2ad28c088ba4397da1243541b6c440e755ec9800000003ff80000000000000,0x16002cdfe00b00166ff005800b33fc010097f004025fc03e42a928c088ba4381d01243540b60440c755ec9b0f61ec3d87b0f61ec3d87b0f),((sl7 0x3fffff 0x981084bfff000000 0x9562784376142409 0x2f115712de065a12 0xfffffffffffffff9 sL31 sL31),0x4c30e000002618700000130c3c000011180000446000029105510de025212902260034210040908108008aa1542a8550aa1542a8550aa),(0x4265ab452698787388b96e2302f99cb6c20909480000000000000fffffc00000,0x58703f00002c381f8000161c0fc0000221e000088780000026123452698685388a86e2002399c14c200010eccd99b33666ccd99b33666cc),(0x8b9a49756713118d62aecc90c902f84832ac312800000003fffff00000000000,0x607fc00000303fe00000181ff00000043e000010f8000000b9049516710118562ae48008900f80830880124f09e13c2784f09e13c2784f0),(0x67549069da2e88593064c198c8069435055d24307fffffffc0000000000000000,0x7f800000003fc00000001fe000000007c000001f00000044449020420a800010648188c8061405014c0430700e01c0380700e01c0380700),(0,0)]
def g255C : List ColumnInfo := [(0,8,183,64,10),(2,0,253,0,10),(4,0,251,0,10),(8,0,247,0,10),(0,64,182,9,9),(1,0,254,0,9),(32,0,223,0,9),(64,0,183,0,9),(64,8,183,0,9),(0,32,218,5,8),(16,0,239,0,8),(128,0,127,0,8),(0,2,109,144,7),(0,128,105,22,7),(1,32,218,4,7),(4,32,218,1,7),(18,0,237,0,7),(33,0,222,0,7),(132,0,123,0,7),(2,128,105,20,6),(16,128,105,6,6),(17,0,238,0,6),(144,2,109,0,5)]
def g255A : List (List Nat) := [[]]
def g255D8 := packet 0x12836426420000010020040c161b158bc7c1f3a6cc972a4878c14202c28056541f22fb7467c8aa6491b22919042ca19e509f224f9111c8c0e4647225dbf7f5febfb7eef7cfd61f4061e745d1549d1505d1501d150a1d4061d405d14060074
def g255D9 := packet 0xa591ef1900518b8622e18b2e28601f2df9942e3a68802f43a591899a1be30083ca012fbd30055f4f804cfaf2005df4f804cebf3404bdeb0016794025d38043710051b3bc0274e400b5d80393f1c00529c8016d4c014d4c014f7320145e5590a1deb20140674e38056b00127d3ac414de9c68052deb201579ac4272d204464e8d1204c3251324400a9963d2114b94aa12d9830e1b17394c81c20b14270e3c583d8edfa5e4f7ed633eca718c12edb5ab8a6a7c97a4088a0b7d1dc6f5a56416e5593e4990a3acce298921c04e0c815002774395d0e774299d0a574291d0a6871961c6774195d05184c4e119180b461e118087e05538054600118774e1cd184a65d2938446dd119744461e53871461c617011e09977482e05418501608098103600058270616bffffbfddff6fbfefebf6fbb7f75dd370d0274951755d1705515050074
def g255H9 := packet 0xcb0000000000620000000000c000fa000000000000000099000000e84c0000d600d10063000000005dc400650000b70000000000
def g255D10 := packet 0x100097a00143400586800c7c340069e04e062001280048000b7e8002defc00e80029e8002d612851154d8e52451a638b2a79208a1893edcace58a5506712f1105618006eabaee93a2e83a4a8aa6e0b82a1a0281ff
def g255H10 := packet 0xd82e5b605e00022002427778e00010104540039f4840093fa4b5ed2968cc32a0084403a7000a13061345595800002c7000c514d8936d9928f0802c102c06e700000
def g255D11 := packet 0x66290e20808ff
def g255H11 := packet 0x15145600000000348000003f34ee800580000000000029c00000003e40116000000026c8
def g255L : Nat → Packing
  | 8 => (14,3,5,458762,52,7,1031,g255D8)
  | 9 => (38,2,5,655373,68,10,1063,g255D9)
  | 10 => (13,1,5,65537,0,9,1045,g255D10)
  | 11 => (1,0,5,0,0,0,0,g255D11)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 3 53 0 8 4 0 g255H9
  | 10 => lookupWord 9 47 6 10 6 0 g255H10
  | 11 => lookupWord 3 37 2 8 4 0 g255H11
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_3 : block g255 8 3 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 14=true := (@block_merge g255 8 0 3 11 g255P8_0 g255P8_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_9 : block g255 9 9 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_28 : block g255 9 28 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 38=true := (@block_merge g255 9 0 9 29 g255P9_0 (@block_merge g255 9 9 19 10 g255P9_9 g255P9_28))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255T : checkedTables g255 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g255B8
  · exact g255B9
  · exact g255P10_0
  · exact g255P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : Chart g255 K501 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 12 := lower_forest (g:=g255) (i:=0) (hints:=268461380) (before_sound K501 V501) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K255 := extendKnown K501 12 [(255,[]),(383,[49,100,135]),(447,[32,116,134]),(495,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V255 : Known true K255 := extend_ok (m:=255) V501 low255 (by decide +kernel)
def g479Y : Array Signals := #[(sR100,sR67),(sR37,sR83),(sR38,sR69),(sR93,sR85),(sR112,sR27),(0,0),(sR8,sR22),(sR9,sR31),(sR10,sR34)]
def g479C : List ColumnInfo := [(1,0,478,0,11)]
def g479A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g479D11 := packet 0x1ff
def g479L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g479D11)
  | _ => emptyPacking
def g479I (_ _ : Nat) : Option (Nat × Nat) := none
def g479 : Forest := ⟨479,11,fun i => g479Y[i]?.getD (0,0),g479C,g479A,g479L,g479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P11_0 : block g479 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479T : checkedTables g479 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g479P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479G : Chart g479 K255 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 12 := lower_forest (g:=g479) (i:=0) (hints:=8858396484) (before_sound K255 V255) g479G g479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K479 := extendKnown K255 12 [(479,[])]
set_option maxRecDepth 32768 in
theorem V479 : Known true K479 := extend_ok (m:=479) V255 low479 (by decide +kernel)
def g503Y : Array Signals := #[(sR97,sR70),(sR101,sR79),(sR105,sR28),(0,0),(sR111,sR43),(sR13,sR57),(sR11,sR58),(sR12,sR61),(sR14,sR88)]
def g503C : List ColumnInfo := [(1,0,502,0,10),(2,0,501,0,10),(4,0,499,0,10),(16,0,487,0,10),(32,0,471,0,10),(64,0,439,0,10),(128,0,375,0,10)]
def g503A : List (List Nat) := [[],[32,116,134]]
def g503D11 := packet 0xfac688ff
def g503L : Nat → Packing
  | 11 => (1,0,3,65537,0,0,1031,g503D11)
  | _ => emptyPacking
def g503I (_ _ : Nat) : Option (Nat × Nat) := none
def g503 : Forest := ⟨503,11,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503T : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : Chart g503 K479 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 12 := lower_forest (g:=g503) (i:=0) (hints:=8858371396) (before_sound K479 V479) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K479 12 [(503,[]),(509,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V503 : Known true K503 := extend_ok (m:=503) V479 low503 (by decide +kernel)
def g507Y : Array Signals := #[(sR87,sR72),(sR99,sR81),(0,0),(sR103,sR24),(sR109,sR51),(sR17,sR55),(sR15,sR26),(sR16,sR60),(sR18,sR63)]
def g507C : List ColumnInfo := [(32,0,475,0,11)]
def g507A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g507D11 := packet 0x1ff
def g507L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g507D11)
  | _ => emptyPacking
def g507I (_ _ : Nat) : Option (Nat × Nat) := none
def g507 : Forest := ⟨507,11,fun i => g507Y[i]?.getD (0,0),g507C,g507A,g507L,g507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P11_0 : block g507 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507T : checkedTables g507 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g507P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507G : Chart g507 K503 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low507 : Lower true (varsX 507) (graphGoal 507) 12 := lower_forest (g:=g507) (i:=0) (hints:=13153361988) (before_sound K503 V503) g507G g507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K507 := extendKnown K503 12 [(507,[]),(510,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V507 : Known true K507 := extend_ok (m:=507) V503 low507 (by decide +kernel)
def g511Y : Array Signals := #[(sR91,sR74),(sR45,sR82),(sR53,sR90),(sR33,sR32),(sR92,sR49),(sR41,sR40),(sR50,sR48),(sR47,sR46),(sR52,sR44)]
def g511C : List ColumnInfo := [(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(16,0,495,0,12),(32,0,479,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(0,8,183,320,11),(0,32,474,5,11),(33,0,478,0,11),(36,0,475,0,11),(0,16,364,131,10),(0,64,182,265,10),(0,128,361,22,10),(0,256,179,76,10),(1,32,474,4,10),(3,0,508,0,10),(10,0,501,0,10),(12,0,499,0,10),(16,2,365,128,10),(17,0,494,0,10),(18,0,493,0,10),(34,0,477,0,10),(40,0,471,0,10),(64,8,183,256,10),(66,0,445,0,10),(72,0,439,0,10),(128,2,365,16,10),(132,0,379,0,10),(136,0,375,0,10),(256,8,183,64,10),(260,0,251,0,10),(264,0,247,0,10),(1,16,364,130,9),(1,64,182,264,9),(4,128,361,18,9),(4,256,179,72,9),(5,0,474,0,9),(5,32,474,0,9),(16,128,361,6,9),(48,0,463,0,9),(64,256,179,12,9),(68,0,443,0,9),(128,16,364,3,9),(129,0,382,0,9),(144,0,365,0,9),(144,2,365,0,9),(256,64,182,9,9),(320,0,183,0,9),(320,8,183,0,9),(20,128,361,2,8),(68,256,179,8,8),(129,16,364,2,8),(257,64,182,8,8)]
def g511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g511D8 := packet 0x59d5f4d86e57a15d120
def g511D9 := packet 0xc598a82f0a0bc3040a17180a77dcbad4a961d64afd7c361ba15d120e77586e57a15d120b75fc361b9550520
def g511H9 := packet 0xb0
def g511D10 := packet 0x37f00226fe00443f0090fc024033ab07d962000ff4b8cc011e186ca6dd941827f436402f0c605e18c6ff03a5109240bc33580cf3fc01b10724ab8720c00013fa66006fea90ca9427c013941c9601c33640bffcbb8a521595ac8015e29940ffbc0d9417f0bc8a5234999a0ae0a734ed9b4b8c2b0a4b9ae646f1af1bab6978063d936498160980e20c2b4da4e5cc5306d9152c67139ae53e6f0fe6791e345dc2b8d61cb1cdf82c4c95a43039562e12195a3f05c03871661dcb719a359184f09e1e8963492c58171538b8d5ff74da75c54f404b921447063eae2b38b72aa97a0068166440d82684c00576b2a6d655dab29b566f40d4ecd38c31ad863a7662c61879ca873950356ac66d58fcbac7b381766e1ecdeecba8fb34432c796c087d9943b38af2a7eff777f7fb9ffcff67f73ef9dfceedfdefed777afbd7d4a95d98461b915d186e517061b925c1865d17068392590a961d64e8d86553a36194061972501865c140e8574483955d12061970483a959120e5541481865052060d414816350520
def g511H10 := packet 0x5cd40000a06275000001330000
def g511D11 := packet 0x6f6f5da5da6c66b4f2fed2a2d0159a80bc23c7e5042719b03b00fb49238cd45fc13f2240a59a43f827e44814b348dd6c727680260dd71a13b4013334e1d05a00348017c7f998b2d4cc4f00cfff20cde20646c004fffa662db58913c0138f93a512d201decc9d3d4d39ffdb610c6672fe7a83a4d3b19ac33ec3d38cc1d066f95a71a40bc71b4b660e8607c2b4b690bff0b00051fc7c5b2228806191f42c823501e352ffe0f11282ffcf138c6aee250005440df1af85210a5813e35ec298296bb9383f9c90a7ce0f9f23c5bce6ff91d7ff67f85c28b96c313d3ff41c17a11a2be8382f42340df179e7ea1c9451d32c33300378f0ccc15e15f4f004006a8d89b9e459a01bc13a6996800d407ae3427680266e311c9b680264797e112d001a175af9b0482557fcb1b3012340704f4b353397c032d8001a33f97f01332103537d7fc880019c03ffe08c0440d25ff0886094000d41fffacf09502c5f843e0556d9404e08ff5b141164d21fbe70c100b0fffeec900502dd8dd7110c02587ff2823041340dfae12a923bff282306338017f4f738200d51ffa5980919cbe502e9c260a34edcd20ae954785f0319d1460ace2e200a2c296676a2ee165c6d8ad4d72a82d138a7269753acc5783c0904974ca6b5954804f40a214b59325900b1bccb9a32a5460b04f523124d0480d8d1285aec3182e36eca5c2f4629a599cccc61e4b2728f1ab02521a3a928141b2f0d8b122a46aa55345f13429763683479b22ac24992616bd9e84e6e890ee436e8784c160095c7ab31a913545d6e8d9661e3387c1c86c48c04bcbb90b55b21aecab9a72a2e9e89b397f94e9108e78b488a8568017c979073c7056cf6a36796506045d05a156b54551f4e24b447744140d3d83a93753493182dd2ac2732372021c218b15c1260f50c109806902f000d6195ab1ab58636b0c2d60c5ab18a3a0b43416a696cbd3523979af5125e99ebd43a186e4b0d88e5332ba66394bcae97861b70c1ee163dc32ec865d70cba31864e3069c58d30cb1a1981432c2c618b8c19716328153f761bc054d59a5b034161696c5d1ccba3897470068ba5d1e83a269746c0ea4edca9db9531f4260ea48dca913a02372a36e544dca86d62297460fffffeffafdff7fdffdfdddfbffbfebfdbf7bdf9ff5d984e4574e5970e5170e49706197060d705d17058d70e496461d6461d54619545d95461951619416154159541659406194060d405c9405c14058d40611205d1205c1205912058520505204c52061910
def g511H11 := packet 0x157e88d4c00003fc40000000018c000000000000006580018f00000048800c6000386800000000000147160000008600000000000000000000000000000000000000273000000000000000000014c000000001d1000000000000000000000000000180c00000000000000000000000019700000000000a000018266f00000000485a02001048240000000000011400000000d04000000003e00c40028e0000000021300000000000000aa171264000000000000000000000000124000000000000005e80000000000052b6480b50
def g511D12 := packet 0x1b15cf4840254ffe258a500959c7802e883105af62be9b5009436d7e8154b71e029de684687200026cf8e7e847312400014379a19b9800013636d79046213350fcffc7b4000125889bc2c548bf0764b14df830f0c53b893f8051e7127e82a387f69514219d7ec6c729104b99f03ea048256af81f4844128bff5404000d06a7b00ba7fe60cc82adff8c20841267df83804124bfed440040d0befc1502093bf5e6225200026cfffafd160004abf3e18e0015ce79e49a11012cffbc0bcaff83beb0319e7916169004c13f1b13a8f18945e20de5004d007fb9e57a51246f8ac42246e7fc004479cff41088f3f03f9a1009280fc7001123bdbc000119e7e6b14201277fb07394024cfbde4f90093b8e7ad4d3a012fb18d20a900699cff2840d6c804d2ff2dfc05033f37d00012a2ff4ff95002c19f67aa00012e7ef96f1000947f81cefc2015de7b200a271fa1674004aa7f4601409ff4ab42004a2ff7ff5100a872fefa000250d46fb385800136ffeee00140ebfc75001200ffff096402497ec7be6300b37e04ff4940491e157c2549007fd57e4a024d8a7ce4cad16b02f9841ae2c542a2a8284600b8614e24040b9a23150c3020f008b15daa542c5208384b1aee28803088513a3af54ba49a11be166e605c5cc1507c3c11b46871216132b26cda62412991c4ba5a363971ac26321e430cf2dcb4661e0e3861f601deb5db5cadae589d6dd52534520d0e4fb4e7cd44bdca4c8c473c5b44cc36c1fc09bf13db3be3a2b8c371b4cb32b172ff2e5ad22beaab291a7da67a51a3a2232079ee9d09bd1a598c97395b1421319189080ee8d78c00a389007986004782e81900065dab72b59869cc3bee55f724f9875cc32e5d9730ad9864cc31e614f2ca79833cb19e54cf30d19838cb1c658a330e59862cbb1660cb2e659632cc1165c8b2c459841cba0e59072c239411c988e618330619630cc10658832640b96a5c852e5dd32ef18475c93ae41d730ab9755cb2ae6213310b9686bb42e521ae90b9284cc1265c932c51642ab8126506ae0279191ca8fffffdfbfbfdffbfb77d845d17059161551515054048110
def g511H12 := packet 0x109000539000000711e520000000000000000000003ddce465e14e0008db000c23000605f2400000000000000000000000000024cc3a000000fce00000001d000000000a0ed5b000000000a6c000000000000000000000462e190000000003ba7cc00063b00000050600000063400000000020000000051a7355867155ac00000000000063081b518dc4000f2f000d25b1c09e000000000000000000000000b01000f04000000000000b0b000464000000000000000426344dea2b072735d000000000b08e8400000000000000000000072874000000050260d000000000713000000000000b1eadc000000dde000000000000000000d12e2a00012c00091f000000000000000000ed2000000000000dec716000d10f0c000c36000000000000000000000000020000000000321a2900000000000034300000000000000000000000036e000000000337aa420363812b42d000550a32fc0000ac3000f83000de3000d57000d499da000aefb33000d31c7870f0000000008f200014aa0a051cd0000f1700000092e314000407000d5c000e59000000622b680000000003f8000078202013001000441010011002
def g511D13 := packet 0xfcd220b05a7f980580a8f12380d7e1a00bbf4391829bf7e000517fe5404e7e0e44941ffe661031fef6d0050ffdb4814f7ff00204366270c982809a9713114930ce06a18404d876f1c58415366413c32316910ee74c97449dccb55a24c8410f801845d16455161545414c57050120443ff
def g511H13 := packet 0x3823e095528e7c41ec41000000102abbc2db88f40000009d34c08276bb3405000047c09dd1f80000004260007a14c49825814b2200006a4b13907400181b0000001e43e34edeea540013b161b04f5345f95105d0ec001a83000100000120da8760af04762ed5c0001179f9b000727d83d01841918d40000000002c58000000d5dccb0000fb200070535522827140000438404e09ac1e07830cecc20b3b57639146625cf5572288570047713baa50a2c3432000997381c00022000000000016add0322b0000000000383000000000000000019ad4c1d089606433ed0904a481630d91ee7000042db2128bd41c18895148e1c3581f221a67b80662a2593841c2d037702aebb4740000007ad9705c96f1882e4001817259a008410000ccc8001842000000000002c0006cc351000514114210e002142284080002040003105
def g511D14 := packet 0x1038c20609a611ff
def g511H14 := packet 0x56003f27a0c6d6ba9c428462023c0000f976000000425b7001cb94d9520b970037341c000c10300041816b8c2a62661f5e49db002a70662403859a3
def g511L : Nat → Packing
  | 8 => (1,6,6,0,0,0,0,g511D8)
  | 9 => (4,5,6,0,0,6,0,g511D9)
  | 10 => (25,4,6,917523,69,10,1102,g511D10)
  | 11 => (60,3,6,917536,69,12,1170,g511D11)
  | 12 => (68,2,6,458763,52,12,1121,g511D12)
  | 13 => (12,1,6,65537,0,9,1060,g511D13)
  | 14 => (1,0,6,0,0,0,0,g511D14)
  | _ => emptyPacking
def g511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g511H9
  | 10 => lookupWord 1 19 0 8 2 2 g511H10
  | 11 => lookupWord 9 149 2 11 5 2 g511H11
  | 12 => lookupWord 27 277 4 12 6 2 g511H12
  | 13 => lookupWord 33 181 6 13 7 2 g511H13
  | 14 => lookupWord 8 43 6 10 4 2 g511H14
  | _ => fun _ => none
def g511 : Forest := ⟨511,14,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P8_0 : block g511 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P9_0 : block g511 9 0 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_0 : block g511 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_2 : block g511 10 2 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_13 : block g511 10 13 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B10 : block g511 10 0 25=true := (@block_merge g511 10 0 2 23 g511P10_0 (@block_merge g511 10 2 11 12 g511P10_2 g511P10_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_0 : block g511 11 0 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_25 : block g511 11 25 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_54 : block g511 11 54 6=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B11 : block g511 11 0 60=true := (@block_merge g511 11 0 25 35 g511P11_0 (@block_merge g511 11 25 29 6 g511P11_25 g511P11_54))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_0 : block g511 12 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_2 : block g511 12 2 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_26 : block g511 12 26 42=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B12 : block g511 12 0 68=true := (@block_merge g511 12 0 2 66 g511P12_0 (@block_merge g511 12 2 24 42 g511P12_2 g511P12_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P14_0 : block g511 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511T : checkedTables g511 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g511P8_0
  · exact g511P9_0
  · exact g511B10
  · exact g511B11
  · exact g511B12
  · exact g511P13_0
  · exact g511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : Chart g511 K507 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 14 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=14) (i:=0) (before_sound K507 V507) g511G g511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11028

namespace PEqualNP.Outside.L_meta_11028
theorem finishWhenMonotone (mono : Impossible false graph 15 inputs.toFinset) :
    ∀ t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 9 edge t → 16 ≤ t := by
  rintro t ⟨C,legal,sz,h⟩
  by_contra! bad
  exact directSplit mono g511R ⟨C,legal,by omega,h⟩
namespace CrossCheck
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

def positiveAt (p n : Row) (w : Sig) := bit p w && !(bit n w)
def onlyAt (ws : List Sig) (p n : Row) : Option Sig :=
  match ws.filter (positiveAt p n) with
  | [v] => some v
  | _ => none

theorem onlyAt_sound (ws : List Sig) (T : Sig) (p n : Row) (v : Sig)
    (hp : bit p T=true) (hn : bit n T=false) (hv : onlyAt ws p n=some v) :
    onlyWire ws.toFinset T v p n := by
  refine ⟨hp,hn,?_⟩
  intro w hw wp wn
  have mem : w ∈ ws.filter (positiveAt p n) := List.mem_filter.mpr
    ⟨List.mem_toFinset.mp hw,by simp [positiveAt,wp,wn]⟩
  unfold onlyAt at hv
  split at hv
  next z eq =>
    have hE : z=v := Option.some.inj hv
    subst v
    simpa [eq] using mem
  next => contradiction

abbrev Corners := Row × Row × Row × Row × Row × Row

def cross (ws : List Sig) (T : Sig) (k : Nat) (f : Corners) : Bool :=
  let (p,n,pa,pb,na,nb) := f
  (ws.length==k+1) && bit p T && bit pa T && bit pb T &&
    !(bit n T) && !(bit na T) && !(bit nb T) &&
    match onlyAt ws p na, onlyAt ws p nb with
    | some a,some b => a != b && onlyAt ws pa n==some a && onlyAt ws pb n==some b
    | _,_ => false

theorem cross_sound {ws : List Sig} (nd : ws.Nodup) (T : Sig) (k : Nat) (c : Corners)
    (h : cross ws T k c=true) : Impossible false T k ws.toFinset := by
  obtain ⟨p,n,pa,pb,na,nb⟩ := c
  simp only [cross,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨size,hp⟩,hpa⟩,hpb⟩,hn⟩,hna⟩,hnb⟩,hh⟩ := h
  cases ha : onlyAt ws p na with
  | none => simp [ha] at hh
  | some a =>
    cases hb : onlyAt ws p nb with
    | none => simp [ha,hb] at hh
    | some b =>
      simp only [ha,hb,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at hh
      exact kwCross (by rw [List.toFinset_card_of_nodup nd,size]) hh.1.1
        (onlyAt_sound ws T p na a hp hna ha) (onlyAt_sound ws T p nb b hp hnb hb)
        (onlyAt_sound ws T pa n a hpa hn hh.1.2) (onlyAt_sound ws T pb n b hpb hn hh.2)

end CrossCheck
namespace Tier

structure Forced (S : Finset Sig) (T x : Sig) (p n : Row) : Prop where
  mem : x ∈ S
  py : bit p T=true
  nn : bit n T=false
  yes : bit p x=true
  no : bit n x=false
  unique : ∀ v∈S, bit p v=true → bit n v=false → v=x

structure Incompatible (S : Finset Sig) (T x y : Sig) : Prop where
  diff : x≠y
  existsRows : ∃ p n pa pb na nb, Forced S T x p na ∧ Forced S T y p nb ∧
    Forced S T x pa n ∧ Forced S T y pb n

structure Colors (S : Finset Sig) (T : Sig) where
  rank : Sig → Nat
  disjoint : ∀ {x y}, Incompatible S T x y → rank x≠rank y
  horn : ∀ {a b c p n pa na}, Forced S T a p na → Forced S T b pa n → Forced S T c p n →
    rank a=rank b → rank c≤rank a

def transferred (old : Sig → Nat) (localId : Sig→Option Nat) (f : Sig→Sig) (delta : Nat) (x : Sig) :=
  match localId x with
  | some j => j
  | none => delta+old (f x)

theorem same_singleton {S T a b p n pa na} (A : Forced S T a p na)
    (B : Forced S T a pa n) (C : Forced S T b p n) : a=b :=
  C.unique a A.mem A.yes B.no

def lift {S U T} (old : Colors U T) (f : Sig→Sig) (g : Sig→Option Nat) (delta : Nat)
    (small : ∀ {v j}, g v=some j → j<delta)
    (inject : ∀ {v w i}, g v=some i → g w=some i → v=w)
    (push : ∀ {v p n}, g v=none → Forced S T v p n → Forced U T (f v) p n)
    (apart : ∀ {v w}, g v=none → g w=none → Incompatible S T v w → f v≠f w) :
    Colors S T where
  rank := transferred old.rank g f delta
  disjoint := by
    intro x y xy
    cases gx : g x with
    | some a =>
      cases gy : g y with
      | some b =>
        intro eq
        have h : a=b := by simpa only [transferred,gx,gy] using eq
        subst b
        exact xy.diff (inject gx gy)
      | none =>
        have h := small gx
        have bound := Nat.le_add_right delta (old.rank (f y))
        simp only [transferred,gx,gy]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h bound)
    | none =>
      cases gy : g y with
      | some b =>
        have h := small gy
        have bound := Nat.le_add_right delta (old.rank (f x))
        simp only [transferred,gx,gy]
        exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le h bound))
      | none =>
        obtain ⟨p,n,pa,pb,na,nb,A,B,C,D⟩ := xy.existsRows
        have q : old.rank (f x)≠old.rank (f y) := old.disjoint ⟨apart gx gy xy,
          p,n,pa,pb,na,nb,push gx A,push gy B,push gx C,push gy D⟩
        simp only [transferred,gx,gy]
        exact fun e => q (Nat.add_left_cancel e)
  horn := by
    intro a b c p n pa na A B C eq
    cases ga : g a with
    | some i =>
      cases gb : g b with
      | some j =>
        have e : i=j := by simpa only [transferred,ga,gb] using eq
        subst j
        have ab := inject ga gb
        subst b
        have ac := same_singleton A B C
        subst c
        exact Nat.le_refl _
      | none =>
        have h := small ga
        have bound := Nat.le_add_right delta (old.rank (f b))
        simp only [transferred,ga,gb] at eq
        exact ((Nat.ne_of_lt (Nat.lt_of_lt_of_le h bound)) eq).elim
    | none =>
      cases gb : g b with
      | some j =>
        have h := small gb
        have bound := Nat.le_add_right delta (old.rank (f a))
        simp only [transferred,ga,gb] at eq
        exact ((Nat.ne_of_lt (Nat.lt_of_lt_of_le h bound)) eq.symm).elim
      | none =>
        cases gc : g c with
        | some j =>
          have h := small gc
          simp only [transferred,ga,gc]
          exact (Nat.le_of_lt h).trans (Nat.le_add_right delta (old.rank (f a)))
        | none =>
          have e : old.rank (f a)=old.rank (f b) := by
            simp only [transferred,ga,gb] at eq
            exact Nat.add_left_cancel eq
          have q := old.horn (push ga A) (push gb B) (push gc C) e
          simp only [transferred,gc,ga]
          exact Nat.add_le_add_left q delta

def nextWire (a b z x : Sig) := if x=a ∨ x=b then z else x

theorem splitGate {a b : Sig} {d : Nat} (hd : d=0 ∨ d=1) {p n : Row}
    (hp : bit p (bin d a b)=true) (hn : bit n (bin d a b)=false) :
    (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
  rcases hd with rfl | rfl <;> rw [bit_bin] at hp hn <;>
    cases x : bit p a <;> cases y : bit p b <;> cases z : bit n a <;> cases t : bit n b <;> simp_all

theorem pushGate {a b T x : Sig} {k d : Nat} {U : Finset Sig} {p n : Row} (hd : d=0 ∨ d=1)
    (tail : Live false T k (insert (bin d a b) U))
    (reg : ¬((x=a ∨ x=b) ∧ x∈U)) (h : Forced (insert a (insert b U)) T x p n) :
    Forced (insert (bin d a b) U) T (nextWire a b (bin d a b) x) p n := by
  have uniq (v : Sig) (hv : v∈insert (bin d a b) U) (hp : bit p v=true) (hn : bit n v=false) :
      v=nextWire a b (bin d a b) x := by
    rcases Finset.mem_insert.mp hv with rfl | vu
    · rcases splitGate hd hp hn with A | B
      · have e := h.unique a (by simp) A.1 A.2
        simp [nextWire,e.symm]
      · have e := h.unique b (by simp) B.1 B.2
        simp [nextWire,e.symm]
    · have e := h.unique v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem vu)) hp hn
      subst v
      have ne : ¬(x=a ∨ x=b) := fun t => reg ⟨t,vu⟩
      simp [nextWire,ne]
  obtain ⟨v,hv,hp,hn⟩ := mono_row_difference tail rfl h.py h.nn
  have e := uniq v hv hp hn
  exact ⟨e ▸ hv,h.py,h.nn,e ▸ hp,e ▸ hn,uniq⟩

theorem siblings {a b T : Sig} {k d : Nat} {U : Finset Sig} (hd : d=0 ∨ d=1)
    (tail : Live false T k (insert (bin d a b) U)) (ha : a∉U) :
    ¬Incompatible (insert a (insert b U)) T a b := by
  intro H
  obtain ⟨p,n,pa,pb,na,nb,A,B,C,D⟩ := H.existsRows
  have reg : ¬((a=a ∨ a=b) ∧ a∈U) := fun t => ha t.2
  have left := pushGate hd tail reg A
  have right := pushGate hd tail reg C
  rcases hd with rfl | rfl
  · have h : bit pa a=true ∧ bit pa b=true := by simpa [nextWire,bit_bin] using right.yes
    exact H.diff (C.unique b B.mem h.2 D.no).symm
  · have h : bit na a=false ∧ bit na b=false := by simpa [nextWire,bit_bin] using left.no
    exact H.diff (A.unique b B.mem B.yes h.2).symm

theorem swapConflict {S T a b} (h : Incompatible S T a b) : Incompatible S T b a := by
  obtain ⟨p,n,pa,pb,na,nb,A,B,C,D⟩ := h.existsRows
  exact ⟨Ne.symm h.diff,p,n,pb,pa,nb,na,B,A,D,C⟩

theorem mappedApart {a b T x y : Sig} {k d : Nat} {U : Finset Sig} (hd : d=0 ∨ d=1)
    (tail : Live false T k (insert (bin d a b) U)) (fresh : bin d a b∉insert a (insert b U))
    (xr : ¬((x=a ∨ x=b) ∧ x∈U)) (yr : ¬((y=a ∨ y=b) ∧ y∈U))
    (H : Incompatible (insert a (insert b U)) T x y) :
    nextWire a b (bin d a b) x≠nextWire a b (bin d a b) y := by
  obtain ⟨p,n,pa,pb,na,nb,A,B,C,D⟩ := H.existsRows
  have nx : x≠bin d a b := fun e => fresh (e ▸ A.mem)
  have ny : y≠bin d a b := fun e => fresh (e ▸ B.mem)
  by_cases xx : x=a ∨ x=b
  · by_cases yy : y=a ∨ y=b
    · have no : False := by
        rcases xx with rfl | rfl <;> rcases yy with rfl | rfl
        · exact H.diff rfl
        · exact siblings hd tail (fun m => xr ⟨Or.inl rfl,m⟩) H
        · exact siblings hd tail (fun m => yr ⟨Or.inl rfl,m⟩) (swapConflict H)
        · exact H.diff rfl
      exact no.elim
    · simpa only [nextWire,xx,yy,ite_true,ite_false] using Ne.symm ny
  · by_cases yy : y=a ∨ y=b
    · simpa only [nextWire,xx,yy,ite_true,ite_false] using nx
    · simpa only [nextWire,xx,yy,ite_true,ite_false] using H.diff

end Tier
namespace Tier

def increment (a b : Sig) (U : Finset Sig) := (if a∈U then 1 else 0) + (if b∈U then 1 else 0)
def localId (a b : Sig) (U : Finset Sig) (w : Sig) : Option Nat :=
  if w=a ∧ a∈U then some 0 else if w=b ∧ b∈U then some (if a∈U then 1 else 0) else none

theorem lowNumber {a b w : Sig} {U : Finset Sig} {j : Nat} (h : localId a b U w=some j) :
    j < increment a b U := by
  unfold localId at h
  unfold increment
  split_ifs at * <;> simp_all <;> omega

theorem numberUnique {a b x y : Sig} {U : Finset Sig} {j : Nat}
    (hx : localId a b U x=some j) (hy : localId a b U y=some j) : x=y := by
  unfold localId at hx hy
  split_ifs at * <;> simp_all <;> omega

theorem isRegular {a b x : Sig} {U : Finset Sig} (h : localId a b U x=none) :
    ¬((x=a ∨ x=b) ∧ x∈U) := by
  rintro ⟨hx,mem⟩
  rcases hx with rfl|rfl <;> unfold localId at h <;> split_ifs at h <;> simp_all

theorem stepCount {a b z : Sig} {U : Finset Sig} (ne : a≠b) (fresh : z∉U) :
    (insert a (insert b U)).card + increment a b U = (insert z U).card + 1 := by
  rw [Finset.card_insert_of_notMem fresh]
  by_cases ha : a∈U
  · have ab : a ∈ insert b U := Finset.mem_insert_of_mem ha
    rw [Finset.insert_eq_of_mem ab]
    by_cases hb : b∈U
    · rw [Finset.insert_eq_of_mem hb]
      simp [increment,ha,hb] <;> omega
    · rw [Finset.card_insert_of_notMem hb]
      simp [increment,ha,hb]
  · have ab : a∉insert b U := by simp [ne,ha]
    rw [Finset.card_insert_of_notMem ab]
    by_cases hb : b∈U
    · rw [Finset.insert_eq_of_mem hb]
      simp [increment,ha,hb]
    · rw [Finset.card_insert_of_notMem hb]
      simp [increment,ha,hb]

theorem mappedMember {a b z x : Sig} {U : Finset Sig} (h : x∈insert a (insert b U)) :
    nextWire a b z x ∈ insert z U := by
  by_cases hx : x=a ∨ x=b
  · simp [nextWire,hx]
  · have nx : x≠a := fun e => hx (Or.inl e)
    have ny : x≠b := fun e => hx (Or.inr e)
    have xu : x∈U := by simpa only [Finset.mem_insert,nx,ny,false_or] using h
    simp [nextWire,hx,xu]

theorem budget {T : Sig} {k : Nat} {S : Finset Sig} (r : Live false T k S) :
    ∃ coloring : Colors S T, ∀ v∈S, coloring.rank v+S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    let H : Colors {T} T := {
      rank := fun _ => 0
      disjoint := by
        intro x y xy
        obtain ⟨p,n,pa,pb,na,nb,A,B,C,D⟩ := xy.existsRows
        have xx : x=T := Finset.mem_singleton.mp A.mem
        have yy : y=T := Finset.mem_singleton.mp B.mem
        exact False.elim (xy.diff (xx.trans yy.symm))
      horn := by intros; exact Nat.le_refl 0 }
    refine ⟨H,?_⟩
    intro x hx
    simp [H]
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ne,fresh,tail⟩ := r
    let z := bin d a b
    let f := nextWire a b z
    let g := localId a b U
    let δ := increment a b U
    have hz : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    obtain ⟨H,lim⟩ := ih tail
    let newColors := lift H f g δ (fun h => lowNumber h) (fun h j => numberUnique h j)
      (fun h c => pushGate hd01 tail (isRegular h) c)
      (fun h j c => mappedApart hd01 tail fresh (isRegular h) (isRegular j) c)
    refine ⟨newColors,?_⟩
    intro v hv
    have count : (insert a (insert b U)).card+δ=(insert z U).card+1 := stepCount ne hz
    have card := live_size tail
    change (insert z U).card ≤ k+1 at card
    change transferred H.rank g f δ v+(insert a (insert b U)).card≤k+1+1
    cases h : g v with
    | some i =>
      have hi : i<δ := lowNumber h
      simp only [transferred,h]
      omega
    | none =>
      have limv := lim (f v) (mappedMember hv)
      change H.rank (f v)+(insert z U).card ≤ k+1 at limv
      simp only [transferred,h]
      change (δ+H.rank (f v))+(insert a (insert b U)).card≤k+1+1
      rw [Nat.add_comm δ (H.rank (f v)),Nat.add_assoc,Nat.add_comm δ _,count]
      omega
end Tier
namespace Tier

def firstSlot (code : Nat) := code &&& 15
def secondSlot (code : Nat) := (code >>> 4) &&& 15
def outputSlot (code : Nat) := (code >>> 8) &&& 15

def relation (v : Nat→Nat) (c : Nat) : Prop :=
  if outputSlot c=0 then v (firstSlot c)≠v (secondSlot c) else
    v (firstSlot c)=v (secondSlot c) → v (outputSlot c-1)≤v (firstSlot c)

def violates (p : List Nat) (c : Nat) : Bool :=
  let a := p.getD (firstSlot c) 0
  let b := p.getD (secondSlot c) 0
  let d := outputSlot c
  decide (firstSlot c<p.length ∧ secondSlot c<p.length) &&
    if d=0 then a==b else
      decide (d-1<p.length) && (a==b) && decide (a<p.getD (d-1) 0)

theorem violates_sound {p c v} (agrees : ∀ i<p.length, p.getD i 0=v i)
    (r : relation v c) : violates p c≠true := by
  intro bad
  simp only [violates,Bool.and_eq_true,decide_eq_true_eq] at bad
  have ha := agrees (firstSlot c) bad.1.1
  have hb := agrees (secondSlot c) bad.1.2
  by_cases h : outputSlot c=0
  · simp only [relation,h,ite_true] at r
    have eq : p.getD (firstSlot c) 0=p.getD (secondSlot c) 0 := by
      simpa only [h,ite_true,beq_iff_eq] using bad.2
    exact r (ha.symm.trans (eq.trans hb))
  · simp only [relation,h,ite_false] at r
    have bx := bad.2
    simp only [h,ite_false,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at bx
    have hc := agrees (outputSlot c-1) bx.1.1
    have low := r (ha.symm.trans (bx.1.2.trans hb))
    omega

def exhaustive (levels : Nat) (rules : List Nat) : Nat → List Nat → Bool
  | 0,ps => rules.any (violates ps)
  | n+1,ps => rules.any (violates ps) ||
      (List.range levels).all fun j => exhaustive levels rules n (ps++[j])

theorem append_agree {p : List Nat} {v : Nat→Nat} (h : ∀ i<p.length, p.getD i 0=v i) :
    ∀ i<(p++[v p.length]).length, (p++[v p.length]).getD i 0=v i := by
  intro i hi
  by_cases e : i<p.length
  · have eq : (p++[v p.length]).getD i 0=p.getD i 0 := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,e]
    exact eq.trans (h i e)
  · have x : i=p.length := by simp at hi; omega
    subst i
    simp [List.getD_eq_getElem?_getD,List.getElem?_append]

theorem exhaustive_sound {levels rules n ps v} (reject : exhaustive levels rules n ps=true)
    (small : ∀ i, v i<levels) (model : ∀ c∈rules, relation v c)
    (agrees : ∀ i<ps.length, ps.getD i 0=v i) : False := by
  have noBad (p : List Nat) (h : ∀ i<p.length, p.getD i 0=v i) : rules.any (violates p)≠true := by
    intro e
    obtain ⟨c,hc,b⟩ := List.any_eq_true.mp e
    exact violates_sound h (model c hc) b
  induction n generalizing ps with
  | zero => exact noBad ps agrees reject
  | succ n ih =>
    have casesOf : rules.any (violates ps)=true ∨ (List.range levels).all (fun j => exhaustive levels rules n (ps++[j]))=true := by
      simpa only [exhaustive,Bool.or_eq_true] using reject
    have r : (List.range levels).all (fun j => exhaustive levels rules n (ps++[j]))=true :=
      casesOf.resolve_left (noBad ps agrees)
    exact ih (List.all_eq_true.mp r (v ps.length) (List.mem_range.mpr (small _))) (append_agree agrees)

end Tier
namespace Tier

def uniqueB (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all fun w => !bit p w || bit n w || w==v

theorem uniqueB_force {ws T v p n k} (run : Live false T k (List.toFinset ws))
    (hb : uniqueB ws T v p n=true) : Forced ws.toFinset T v p n := by
  simp only [uniqueB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hb
  have uniq (x) (hx : x∈ws.toFinset) (hp : bit p x=true) (hn : bit n x=false) : x=v := by
    simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using hb.2 x (List.mem_toFinset.mp hx)
  obtain ⟨w,hw,py,nn⟩ := mono_row_difference run rfl hb.1.1 hb.1.2
  have eq := uniq _ hw py nn
  exact ⟨eq ▸ hw,hb.1.1,hb.1.2,eq ▸ py,eq ▸ nn,uniq⟩

def proofRow (v i : Nat) : Row := Fin.ofNat 512 ((v >>> (9*i)) &&& 511)
def localEvidence (wire : Nat→Sig) (ws : List Sig) (T : Sig) (rule data : Nat) : Bool :=
  let a := wire (firstSlot rule)
  let b := wire (secondSlot rule)
  let atRow := proofRow (data >>> 1)
  let x := if data.testBit 0 then b else a
  let y := if data.testBit 0 then a else b
  if outputSlot rule=0 then
    (decide (x≠y) && uniqueB ws T x (atRow 0) (atRow 2) && uniqueB ws T y (atRow 0) (atRow 3)) &&
      (uniqueB ws T x (atRow 4) (atRow 1) && uniqueB ws T y (atRow 5) (atRow 1))
  else
    (uniqueB ws T x (atRow 0) (atRow 2) && uniqueB ws T y (atRow 4) (atRow 1)) &&
      uniqueB ws T (wire (outputSlot rule-1)) (atRow 0) (atRow 1)

theorem localEvidence_sound {ws T k levels} (run : Live false T k (List.toFinset ws))
    (H : Colors (List.toFinset ws) T) (limit : ∀ x∈ws.toFinset, H.rank x<levels)
    (wire : Nat→Sig) (c data : Nat) (ok : localEvidence wire ws T c data=true) :
    relation (fun j => H.rank (wire j) % levels) c := by
  have bound {v p n} (t : Forced ws.toFinset T v p n) : H.rank v % levels=H.rank v :=
    Nat.mod_eq_of_lt (limit _ t.mem)
  unfold localEvidence at ok
  by_cases out : outputSlot c=0
  · simp only [out,ite_true,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨⟨⟨xy,qa⟩,qb⟩,qc,qd⟩ := ok
    have A := uniqueB_force run qa
    have B := uniqueB_force run qb
    have C := uniqueB_force run qc
    have D := uniqueB_force run qd
    have ne := H.disjoint ⟨xy,_,_,_,_,_,_,A,B,C,D⟩
    simp only [relation,out,ite_true]
    cases swap : data.testBit 0 <;> simp only [swap,Bool.false_eq_true,ite_false,ite_true] at *
    · simpa only [bound A,bound B] using ne
    · simpa only [bound A,bound B] using Ne.symm ne
  · simp only [out,ite_false,Bool.and_eq_true] at ok
    obtain ⟨⟨qa,qb⟩,qc⟩ := ok
    have A := uniqueB_force run qa
    have B := uniqueB_force run qb
    have C := uniqueB_force run qc
    simp only [relation,out,ite_false]
    cases swap : data.testBit 0 <;> simp only [swap,Bool.false_eq_true,ite_false,ite_true] at *
    · intro eq
      rw [bound A,bound B] at eq
      rw [bound C,bound A]
      exact H.horn A B C eq
    · intro eq
      rw [bound B,bound A] at eq
      rw [bound C,bound B]
      exact (H.horn A B C eq.symm).trans (Nat.le_of_eq eq.symm)

def checkPairs (wire : Nat→Sig) (ws : List Sig) (T : Sig) (entry : Nat→Nat) :
    List Nat → Nat → Bool
  | [],_ => true
  | c::cs,i => localEvidence wire ws T c (entry i) && checkPairs wire ws T entry cs (i+1)

theorem checkPairs_sound {ws T k levels} (run : Live false T k (List.toFinset ws)) (H : Colors (List.toFinset ws) T)
    (limit : ∀ x∈ws.toFinset, H.rank x<levels) (wire : Nat→Sig) (f : Nat→Nat)
    {rules i} (ok : checkPairs wire ws T f rules i=true) :
    ∀ c∈rules, relation (fun j => H.rank (wire j) % levels) c := by
  induction rules generalizing i with
  | nil => simp
  | cons c cs ih =>
    simp only [checkPairs,Bool.and_eq_true] at ok
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hh
    · exact localEvidence_sound run H limit wire _ _ ok.1
    · exact ih ok.2 _ hh

def verifyShape (ws : List Sig) (T : Sig) (k levels : Nat) (rules : List Nat)
    (indices : Nat) (entry : Nat→Nat) :=
  decide (k+2≤ws.toFinset.card+levels ∧ 0<levels) &&
    checkPairs (fun j => ws.getD ((indices >>> (4*j)) &&& 15) zero) ws T entry rules 0

theorem verifyShape_sound {ws T k levels rules depth indices entry}
    (reject : exhaustive levels rules depth []=true) (ok : verifyShape ws T k levels rules indices entry=true) :
    Impossible false T k ws.toFinset := by
  simp only [verifyShape,Bool.and_eq_true,decide_eq_true_eq] at ok
  intro k' hk run
  obtain ⟨H,hr⟩ := budget run
  have limit (x : Sig) (hx : x∈ws.toFinset) : H.rank x<levels := by
    have e := hr x hx
    omega
  let wire := fun j => ws.getD ((indices >>> (4*j)) &&& 15) zero
  exact exhaustive_sound (v:=fun j => H.rank (wire j) % levels) reject
    (fun _ => Nat.mod_lt _ ok.1.2) (checkPairs_sound run H limit wire entry ok.2)
    (by simp)

end Tier

namespace Tier
def shape0 : List Nat := [16,544,289,35,771,787]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape0No : exhaustive 2 shape0 4 []=true := by decide +kernel
def shape1 : List Nat := [16,32,33,560,816,305,817,67,576,832,1089,1330,1090]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape1No : exhaustive 3 shape1 5 []=true := by decide +kernel
def shape2 : List Nat := [16,32,33]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape2No : exhaustive 2 shape2 3 []=true := by decide +kernel
def shape3 : List Nat := [16,514,274,35,515,787,835,516,276,1060,69,517,277,1317,1333]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape3No : exhaustive 3 shape3 6 []=true := by decide +kernel
def shape4 : List Nat := [16,32,33,560,816,305,817,67,1088,1089,1330,1090,592,848,337,849,594,1333,1093,101,608,864,353,865,1874,610,1634,1334,1094]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape4No : exhaustive 4 shape4 7 []=true := by decide +kernel
def shape5 : List Nat := [16,32,33,560,816,305,817,306,562,52,576,832,1089,1090,53,69,1104,1360,1601,1602,1045,1301,1061,1317]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape5No : exhaustive 4 shape5 6 []=true := by decide +kernel
def shape6 : List Nat := [16,32,33,560,816,67,576,832,1329,1089,1330,1090]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape6No : exhaustive 3 shape6 5 []=true := by decide +kernel
def shape7 : List Nat := [16,33,544,35,816,787,64,67,1328,276,1060]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape7No : exhaustive 3 shape7 5 []=true := by decide +kernel
def shape8 : List Nat := [16,32,33,560,816,305,817,67,1088,1089,1330,1090]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape8No : exhaustive 3 shape8 5 []=true := by decide +kernel
def shape9 : List Nat := [16,33,544,3,787,547,67,1088,788,548,84,1104,849,1363,1317,865,355,1636,550,1366,118,2144,1904,881,371,1652,551,1367]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape9No : exhaustive 4 shape9 8 []=true := by decide +kernel
def shape10 : List Nat := [16,33,544,50,560,305,817,64,67,1328,321,1090,592,1360,337,849,594,1106,101,608,1376,353,865,610,1122,1875,1635,1876,1636]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape10No : exhaustive 4 shape10 7 []=true := by decide +kernel
def shape11 : List Nat := [16,32,289,49,560]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape11No : exhaustive 2 shape11 4 []=true := by decide +kernel
def shape12 : List Nat := [16,32,33,560,816,67,576,832,1329,1089,1330,1090,592,848,337,1333,1093,101,1632,1873,353,1633,1874,1634,1334,1094]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape12No : exhaustive 4 shape12 7 []=true := by decide +kernel
def shape13 : List Nat := [16,514,274,50,515,275]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape13No : exhaustive 2 shape13 4 []=true := by decide +kernel
def shape14 : List Nat := [16,33,544,48,787,547,67,1088,833,1299,548,84,849,1363]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape14No : exhaustive 3 shape14 6 []=true := by decide +kernel
def shape15 : List Nat := [16,33,544,35,816,787,67,1328,576,321,1090,1299,80,1568,337,851,1061,1093,70,86,1376,1632,1873,1377,867,1379,1861,1574]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape15No : exhaustive 4 shape15 7 []=true := by decide +kernel
def shape16 : List Nat := [16,32,33,560,305,562,67,1328,1088,1329,1089,1330,1090,592,337,849,1363,101,1872,608,1632,353,865,1874,1634,1379,1861,1606]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape16No : exhaustive 4 shape16 7 []=true := by decide +kernel
def shape17 : List Nat := [16,514,274,35,515,787]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape17No : exhaustive 2 shape17 4 []=true := by decide +kernel
def shape18 : List Nat := [16,32,33,48,49,66,832,833,1330]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape18No : exhaustive 3 shape18 5 []=true := by decide +kernel
def shape19 : List Nat := [16,32,33,560,816,305,817,67,576,832,321,833,1330,1090]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape19No : exhaustive 3 shape19 5 []=true := by decide +kernel
def shape20 : List Nat := [16,32,33,67,1328,1088,1329,1089,1330,848,849,1602,1363,1108]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape20No : exhaustive 3 shape20 6 []=true := by decide +kernel
def shape21 : List Nat := [16,32,33,48,35,305,817,64,52,321,833,1089,548,81,84,1104,1360,594,1363,1572]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape21No : exhaustive 4 shape21 6 []=true := by decide +kernel
def shape22 : List Nat := [16,32,289,49,560,562,832,1089,69,1572,773,277,1317,1333,101,608,1636,1648,2069,1909]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape22No : exhaustive 3 shape22 8 []=true := by decide +kernel
def shape23 : List Nat := [16,32,33,49,560,816,291,547,67,832,1089,1060,80,69,1584,1600,277,789,293,1317,1333,101,1632,865,1635,1636]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape23No : exhaustive 4 shape23 7 []=true := by decide +kernel
def shape24 : List Nat := [16,32,289,49,560,306,66,67,832,833,1089,1330,80,277,1045,293,1317,565,1333,101,864,1376,1121,1378,1635,1636,1861]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape24No : exhaustive 4 shape24 7 []=true := by decide +kernel
def shape25 : List Nat := [16,33,544,35,560,305,817,64,67,1328,321,1090,1360,849,1106,101,1872,1376,1632,1873,1633,1874,1634,1875,1635,1876,1636]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape25No : exhaustive 4 shape25 7 []=true := by decide +kernel
def shape26 : List Nat := [16,32,33,48,305,306,52,1088,1329,1089,1330,1090,69,592,848,1104,1601,1602,277,789,293,549,1333,101,1120,1633,1634,1635,1636]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem shape26No : exhaustive 4 shape26 7 []=true := by decide +kernel
def shapeAt (j : Fin 27) : Nat × Nat × List Nat := match j.val with
  | 0 => (2,4,shape0)
  | 1 => (3,5,shape1)
  | 2 => (2,3,shape2)
  | 3 => (3,6,shape3)
  | 4 => (4,7,shape4)
  | 5 => (4,6,shape5)
  | 6 => (3,5,shape6)
  | 7 => (3,5,shape7)
  | 8 => (3,5,shape8)
  | 9 => (4,8,shape9)
  | 10 => (4,7,shape10)
  | 11 => (2,4,shape11)
  | 12 => (4,7,shape12)
  | 13 => (2,4,shape13)
  | 14 => (3,6,shape14)
  | 15 => (4,7,shape15)
  | 16 => (4,7,shape16)
  | 17 => (2,4,shape17)
  | 18 => (3,5,shape18)
  | 19 => (3,5,shape19)
  | 20 => (3,6,shape20)
  | 21 => (4,6,shape21)
  | 22 => (3,8,shape22)
  | 23 => (4,7,shape23)
  | 24 => (4,7,shape24)
  | 25 => (4,7,shape25)
  | _ => (4,7,shape26)
theorem shapeAt_ok (j : Fin 27) : exhaustive (shapeAt j).1 (shapeAt j).2.2 (shapeAt j).2.1 []=true := by
  fin_cases j
  · exact shape0No
  · exact shape1No
  · exact shape2No
  · exact shape3No
  · exact shape4No
  · exact shape5No
  · exact shape6No
  · exact shape7No
  · exact shape8No
  · exact shape9No
  · exact shape10No
  · exact shape11No
  · exact shape12No
  · exact shape13No
  · exact shape14No
  · exact shape15No
  · exact shape16No
  · exact shape17No
  · exact shape18No
  · exact shape19No
  · exact shape20No
  · exact shape21No
  · exact shape22No
  · exact shape23No
  · exact shape24No
  · exact shape25No
  · exact shape26No
abbrev Leaves := (Nat → Nat → Nat) × (Nat → Nat)
def judge (ws : List Sig) (T : Sig) (k v : Nat) (f : Nat→Nat) :=
  let sh := shapeAt (Fin.ofNat 27 (v &&& 31))
  verifyShape ws T k sh.1 sh.2.2 ((v >>> 5) &&& 4294967295) (fun j => f ((v >>> 37)+j))
theorem judge_sound {ws T k v f} (h : judge ws T k v f=true) :
    Impossible false T k ws.toFinset :=
  verifyShape_sound (shapeAt_ok (Fin.ofNat 27 (v &&& 31))) h

end Tier
namespace ImprovedCofactor

def Virtual {R S} (D : Wire R → Wire S → Prop) (a : Wire R) := ∃ w, D a w ∧ Constant w
noncomputable def virtualCost {R S} (D : Wire R → Wire S → Prop) (a : Wire R) : Nat := by
  classical exact if Virtual D a then 1 else 0
noncomputable def virtualMass {R S} (D : Wire R → Wire S → Prop) (ws : List (Wire R)) : Nat :=
  (ws.map (virtualCost D)).sum

def supplied {R S} (D : Wire R → Wire S → Prop) (bank : List (Wire S)) (a : Wire R) : Prop :=
  ∃ w, D a w ∧ Available false bank w

theorem originalCost {R S} {D : Wire R → Wire S → Prop} {a w} (h : D a w) :
    cost w ≤ virtualCost D a := by
  classical
  by_cases c : Constant w
  · have v : Virtual D a := ⟨w,h,c⟩
    simp [cost,virtualCost,c,v]
  · simp [cost,c]

theorem pick {R S} {D : Wire R → Wire S → Prop} {bank a} (h : supplied D bank a) :
    ∃ w, D a w ∧ Available false bank w ∧ cost w = virtualCost D a := by
  classical
  by_cases v : Virtual D a
  · obtain ⟨w,hw,c⟩ := v
    have hv : Virtual D a := ⟨w,hw,c⟩
    exact ⟨w,hw,Or.inr (Or.inl c),by simp [cost,virtualCost,c,hv]⟩
  · obtain ⟨w,hw,ha⟩ := h
    have c : ¬Constant w := fun e => v ⟨w,hw,e⟩
    exact ⟨w,hw,ha,by simp [cost,virtualCost,c,v]⟩

theorem extend {R S} {D : Wire R → Wire S → Prop}
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (roots : List (Wire S)) {p bank a b} (op) (hp : Reach false roots p bank)
    (ha : supplied D bank a) (hb : supplied D bank b) :
    ∃ q next, Reach false roots q next ∧ supplied D next (combine op a b) ∧
      (∀ v, supplied D bank v → supplied D next v) ∧
      q + virtualCost D a + virtualCost D b ≤ p+1+virtualCost D (combine op a b) := by
  obtain ⟨x,hx,sx,ex⟩ := pick ha
  obtain ⟨y,hy,sy,ey⟩ := pick hb
  obtain ⟨q,next,hq,hz,inc,le⟩ := extend_two roots op hp sx sy
  have hz' := compatible op a x b y hx hy
  refine ⟨q,next,hq,⟨_,hz',hz⟩,?_,?_⟩
  · rintro v ⟨w,h,hs⟩
    exact ⟨w,h,inc w hs⟩
  · have il := originalCost hz'
    omega

theorem extendComb {R S} {D : Wire R → Wire S → Prop}
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (roots : List (Wire S)) {p bank a b} (d) (hd : allowed false d) (hp : Reach false roots p bank)
    (ha : supplied D bank a) (hb : supplied D bank b) :
    ∃ q next, Reach false roots q next ∧ supplied D next (comb d a b) ∧
      (∀ v, supplied D bank v → supplied D next v) ∧
      q + virtualCost D a + virtualCost D b ≤ p+1+virtualCost D (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨bad,_⟩ | ⟨bad,_⟩
  · exact extend compatible roots false hp ha hb
  · exact extend compatible roots true hp ha hb
  · cases bad
  · cases bad

theorem massCons {R S} (D : Wire R → Wire S → Prop) (a) (ws) :
    virtualMass D (a::ws) = virtualCost D a + virtualMass D ws := by
  simp [virtualMass]
theorem massKept {R S} (D : Wire R → Wire S → Prop) (a ws) (k : Bool) :
    virtualMass D ws ≤ virtualMass D (kept k a ws) := by
  cases k <;> simp [kept,massCons]

theorem dominatedContraction {R S} {goal : Wire R} {wanted : Wire S} (nc : ¬Constant wanted)
    (D : Wire R → Wire S → Prop)
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (closed : ∀ w, D goal w → w=wanted)
    {s ws} (h : Run false goal s ws) (roots : List (Wire S)) {p bank}
    (hp : Reach false roots p bank) (hs : ∀ v ∈ ws, supplied D bank v) :
    ∃ q next, Reach false roots q next ∧ Available false next wanted ∧ q+virtualMass D ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    obtain ⟨w,hw,ha⟩ := hs goal (by simp)
    have v : ¬Virtual D goal := by
      rintro ⟨w',hw',hc⟩
      exact nc (closed w' hw' ▸ hc)
    exact ⟨p,bank,hp,closed w hw ▸ ha,by simp [virtualMass,virtualCost,v]⟩
  | perm eq _ ih =>
    have hsub := fun v (hv : v ∈ _) => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [virtualMass,←(eq.map (virtualCost D)).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extendComb compatible roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : ∀ v ∈ comb op a b :: kept ka a (kept kb b rest), supplied D T v := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hh := massKept D a (kept kb b rest) ka
    have hj := massKept D b rest kb
    rw [massCons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [massCons,massCons]
    omega

def better {R : Type} (p n : R → Prop) (le : R → R → Prop) (a b : Wire R) : Prop :=
  (∀ r, p r → a r=true → b r=true) ∧
  (∀ r, n r → a r=false → b r=false) ∧
  (∀ r s, le r s → b r=true → b s=true)

private theorem boolCombine (op a b x y c : Bool) (h : a=c → x=c) (j : b=c → y=c) :
    (if op then a || b else a && b)=c → (if op then x || y else x && y)=c := by
  cases c <;> cases op <;> cases a <;> cases b <;> cases x <;> cases y <;> simp_all

theorem betterCompatible {R : Type} (p n : R → Prop) (le : R → R → Prop)
    (op : Bool) (a x b y : Wire R) (hx : better p n le a x) (hy : better p n le b y) :
    better p n le (combine op a b) (combine op x y) := by
  refine ⟨?_,?_,?_⟩
  · intro r pr
    have hb := boolCombine op (a r) (b r) (x r) (y r) true (hx.1 r pr) (hy.1 r pr)
    cases op <;> exact hb
  · intro r nr
    have hb := boolCombine op (a r) (b r) (x r) (y r) false (hx.2.1 r nr) (hy.2.1 r nr)
    cases op <;> exact hb
  · intro r s hrs
    have hb := boolCombine op (x r) (y r) (x s) (y s) true (hx.2.2 r s hrs) (hy.2.2 r s hrs)
    cases op <;> exact hb

def projected {R S} (rows : S → R) (p n : R → Prop) (le : R → R → Prop)
    (a : Wire R) (b : Wire S) : Prop :=
  ∃ v, better p n le a v ∧ b = restrictRows rows v

theorem projectedCompatible {R S} (rows : S → R) (p n : R → Prop) (le : R → R → Prop)
    (op : Bool) (a : Wire R) (x : Wire S) (b : Wire R) (y : Wire S)
    (hx : projected rows p n le a x) (hy : projected rows p n le b y) :
    projected rows p n le (combine op a b) (combine op x y) := by
  obtain ⟨v,hv,rfl⟩ := hx
  obtain ⟨w,hw,rfl⟩ := hy
  refine ⟨combine op v w,betterCompatible p n le op a v b w hv hw,?_⟩
  cases op <;> rfl

theorem projectedClosed {R S} (rows : S → R) {p n : R → Prop} {le : R → R → Prop}
    {g : Wire R}
    (hp : ∀ r, g (rows r)=true → ∃ x, p x ∧ g x=true ∧ le x (rows r))
    (hn : ∀ r, g (rows r)=false → ∃ x, n x ∧ g x=false ∧ le (rows r) x)
    (w : Wire S) (h : projected rows p n le g w) : w=restrictRows rows g := by
  obtain ⟨v,hv,rfl⟩ := h
  funext r
  change v (rows r) = g (rows r)
  cases e : g (rows r) with
  | false =>
    obtain ⟨x,xn,xe,xr⟩ := hn r e
    have no := hv.2.1 x xn xe
    cases j : v (rows r) with
    | false => rfl
    | true => have bad := hv.2.2 (rows r) x xr j; simp_all
  | true =>
    obtain ⟨x,xp,xe,xr⟩ := hp r e
    exact hv.2.2 x (rows r) xr (hv.1 x xp xe)

theorem chargedBound {R S} (rows : S → R) {p n : R → Prop} {le : R → R → Prop}
    {g : Wire R} (hp : ∀ r, g (rows r)=true → ∃ x, p x ∧ g x=true ∧ le x (rows r))
    (hn : ∀ r, g (rows r)=false → ∃ x, n x ∧ g x=false ∧ le (rows r) x)
    (nc : ¬Constant (restrictRows rows g)) {s ws} (h : Run false g s ws)
    (roots : List (Wire S)) {base bank L}
    (hr : Reach false roots base bank)
    (cover : ∀ v ∈ ws, supplied (projected rows p n le) bank v)
    (lo : ∀ q out, Reach false roots q out → Available false out (restrictRows rows g) → L≤q) :
    L + virtualMass (projected rows p n le) ws ≤ base + s := by
  obtain ⟨q,out,hq,hv,ineq⟩ := dominatedContraction nc (projected rows p n le)
    (projectedCompatible rows p n le) (projectedClosed rows hp hn) h roots hr cover
  have b := lo q out hq hv
  omega

end ImprovedCofactor

namespace TestedCube
def rowLe (m : Nat) (r s : Row) : Bool :=
  (r.val &&& s.val &&& m) == (r.val &&& m)
def cover (m : Nat) (g domain : Sig) (pos negs : List Row) (r : Row) : Bool :=
  !bit r domain || (if bit r g then pos.any (fun p => bit p g && rowLe m p r)
                    else negs.any (fun n => !bit n g && rowLe m r n))

theorem witnesses (m : Nat) (g domain : Sig) (pos negs : List Row)
    (ok : ∀ r, cover m g domain pos negs r=true)
    (f : Row → Row) (dom : ∀ r, bit (f r) domain=true) :
    (∀ r, observe g (f r)=true → ∃ x ∈ pos, observe g x=true ∧ rowLe m x (f r)=true) ∧
    (∀ r, observe g (f r)=false → ∃ x ∈ negs, observe g x=false ∧ rowLe m (f r) x=true) := by
  constructor
  · intro r h
    change bit (f r) g=true at h
    have q := ok (f r)
    simpa [cover,dom r,h,List.any_eq_true,observe] using q
  · intro r h
    change bit (f r) g=false at h
    have q := ok (f r)
    simpa [cover,dom r,h,List.any_eq_true,observe] using q

def geometry (m : Nat) (g d : Sig) (p n : List Row) := ∀ r, cover m g d p n r=true

abbrev Dom (m : Nat) (p n : List Row) (f : Row → Row) :=
  ImprovedCofactor.projected f (fun r => r ∈ p) (fun r => r ∈ n) (fun r s => rowLe m r s=true)

def monotoneSig (m : Nat) (w : Sig) := ∀ r s, rowLe m r s=true → bit r w=true → bit s w=true

def constTest (p n : List Row) (a : Sig) :=
  p.all (fun r => !(bit r a)) || n.all (fun r => bit r a)

theorem constTest_sound {m : Nat} {p n : List Row} (f : Row → Row) {a : Sig}
    (h : constTest p n a=true) : ImprovedCofactor.Virtual (Dom m p n f) (observe a) := by
  simp only [constTest,Bool.or_eq_true,List.all_eq_true,Bool.not_eq_true'] at h
  rcases h with z | o
  · refine ⟨fun _ => false,⟨fun _ => false,⟨?_,?_,?_⟩,rfl⟩,⟨false,rfl⟩⟩
    · intro r hr on
      exact False.elim (by simpa [observe,z r hr] using on)
    · intros; rfl
    · intro _ _ _ h; exact h
  · refine ⟨fun _ => true,⟨fun _ => true,⟨?_,?_,?_⟩,rfl⟩,⟨true,rfl⟩⟩
    · intros; rfl
    · intro r hr off
      exact False.elim (by simpa [observe,o r hr] using off)
    · intros; rfl

theorem costCount {m : Nat} (p n : List Row) (f : Row → Row) (ws : List Sig) :
    ws.countP (constTest p n) ≤ ImprovedCofactor.virtualMass (Dom m p n f) (ws.map observe) := by
  classical
  induction ws with
  | nil => simp [ImprovedCofactor.virtualMass]
  | cons w ws ih =>
    simp only [List.countP_cons,List.map_cons,ImprovedCofactor.massCons]
    cases h : constTest p n w
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc := constTest_sound (m:=m) f h
      simpa [ImprovedCofactor.virtualCost,hc,Nat.add_comm] using Nat.succ_le_succ ih

theorem suppliedOf {m : Nat} {p n : List Row} (f : Row → Row) {a : Sig} {bank : List (Wire Row)}
    (mon : monotoneSig m a)
    (ready : constTest p n a=true ∨ Available false bank (restrictRows f (observe a))) :
    ImprovedCofactor.supplied (Dom m p n f) bank (observe a) := by
  rcases ready with con | av
  · obtain ⟨w,hw,c⟩ := constTest_sound (m:=m) f con
    exact ⟨w,hw,Or.inr (Or.inl c)⟩
  · exact ⟨_,⟨observe a,⟨fun _ _ h => h,fun _ _ h => h,mon⟩,rfl⟩,av⟩

theorem constantPoolCut {raw : List Sig} {T : Sig} {c : BoundPool}
    (valid : ValidPool false raw T c) (m : Nat) (pos negs : List Row)
    (geom : geometry m T c.domain pos negs) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (mon : ∀ w ∈ choiceVal choice :: rest, monotoneSig m w)
    (known : ∀ a ∈ rest, constTest pos negs a=true ∨ availableB false c.domain c.wires a=true)
    (buy : if paid then choiceOK false c.domain c.wires choice=true
       else constTest pos negs (choiceVal choice)=true ∨ availableB false c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (constTest pos negs))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible false T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  obtain ⟨geoP,geoN⟩ := witnesses m T c.domain pos negs geom f dom
  let ws := choiceVal choice :: rest
  have done (b : Nat) (out : List (Wire Row)) (reach : Reach false (roots.map observe) b out)
      (supply : ∀ a ∈ ws, constTest pos negs a=true ∨ Available false out (restrictRows f (observe a)))
      (ex : b = c.paid+paid.toNat) : False := by
    have cover : ∀ v ∈ ws.map observe, ImprovedCofactor.supplied (Dom m pos negs f) out v := by
      intro v hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact suppliedOf f (mon a ha) (supply a ha)
    have bnd := ImprovedCofactor.chargedBound f geoP geoN nc
      (list_run run ws nd rfl) (roots.map observe) reach cover lo
    have cnt := costCount (m:=m) pos negs f ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (constTest pos negs) at bound
    change c.bound + ImprovedCofactor.virtualMass (Dom m pos negs f) (ws.map observe) ≤ b+t at bnd
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact buy.imp_right (availableB_sound dom hs)
    · exact (known a hm).imp_right (availableB_sound dom hs)
  | true =>
    obtain ⟨out,hr,used⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact Or.inr (used _ (by simp))
    · exact (known a hm).imp_right (availableB_sound dom (fun v h => used v (List.mem_cons_of_mem _ h)))

def rowsOf (s : Sig) : List Row := (List.finRange 512).filter fun r => bit r s
def inRows {s : Sig} {r : Row} (h : r ∈ rowsOf s) : bit r s=true :=
  (List.mem_filter.mp h).2

def virtualWord (ps ns w : Sig) := (ps &&& w == zero) || (ns &&& neg w == zero)

theorem virtualWord_sound {ps ns w : Sig} (h : virtualWord ps ns w = true) :
    constTest (rowsOf ps) (rowsOf ns) w = true := by
  simp only [virtualWord,Bool.or_eq_true,beq_iff_eq] at h
  simp only [constTest,Bool.or_eq_true,List.all_eq_true,Bool.not_eq_true']
  rcases h with v | v
  · left
    intro r hr
    have hp := inRows hr
    have eq := congrArg (bit r) v
    rw [bit_zero] at eq
    have eb : bit r (ps &&& w) = (bit r ps && bit r w) := by simp [bit]
    simpa only [eb,hp,Bool.true_and] using eq
  · right
    intro r hr
    have hn := inRows hr
    have eq := congrArg (bit r) v
    rw [bit_zero] at eq
    have hrw : bit r (ns &&& neg w) = (bit r ns && !(bit r w)) := by
      rw [show bit r (ns &&& neg w) = (bit r ns && bit r (neg w)) by simp [bit],bit_neg]
    rw [hrw,hn,Bool.true_and] at eq
    simpa using eq

theorem countUnder {α : Type} (p q : α → Bool) (sub : ∀ a, p a=true → q a=true) (xs : List α) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases e : p a <;> cases f : q a <;> simp_all [List.countP_cons] <;> omega

def gateCut (ps ns : Sig) (c : BoundPool) (k : Nat) (rest : List Sig) (g : Choice) :=
  let vir := virtualWord ps ns
  let supply := fun a => vir a || availableB false c.domain c.wires a
  let paid := !(supply (choiceVal g))
  ((k+c.paid+paid.toNat < c.bound+(choiceVal g::rest).countP vir) && rest.all supply) &&
    (!paid || choiceOK false c.domain c.wires g)

theorem gateCut_sound {raw T c} (valid : ValidPool false raw T c) (m) (ps ns : Sig)
    (geom : geometry m T c.domain (rowsOf ps) (rowsOf ns)) {k rest g}
    (mon : ∀ w ∈ choiceVal g :: rest, monotoneSig m w)
    (nd : (choiceVal g::rest).Nodup) (cut : gateCut ps ns c k rest g = true) :
    Impossible false T k (choiceVal g :: rest).toFinset := by
  let supply := fun a => virtualWord ps ns a || availableB false c.domain c.wires a
  let paid := !(supply (choiceVal g))
  change (((k+c.paid+paid.toNat < c.bound+(choiceVal g::rest).countP (virtualWord ps ns)) &&
    rest.all supply) && (!paid || choiceOK false c.domain c.wires g))=true at cut
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true] at cut
  have okay {a : Sig} (h : supply a = true) :
      constTest (rowsOf ps) (rowsOf ns) a=true ∨ availableB false c.domain c.wires a=true := by
    have h2 : virtualWord ps ns a=true ∨ availableB false c.domain c.wires a=true := by simpa [supply] using h
    exact h2.imp virtualWord_sound id
  apply constantPoolCut valid m _ _ geom k rest g paid mon (fun a ha => okay (cut.1.2 a ha)) _ _ nd
  · cases eq : supply (choiceVal g)
    · simpa [paid,eq] using cut.2
    · simpa [paid,eq] using okay eq
  · have ct := countUnder (virtualWord ps ns) (constTest (rowsOf ps) (rowsOf ns))
      (fun _ => virtualWord_sound) (choiceVal g :: rest)
    omega
end TestedCube
namespace CheckedNode
abbrev Rule := Nat → List Sig → Choice → Bool
def WellFoundedCut (u : Bool) (T : Sig) (cap : Nat) (good : Sig → Prop) (rules : Rule) :=
  ∀ (rest : List Sig) (op : Choice), (choiceVal op :: rest).Nodup →
    (∀ x ∈ choiceVal op :: rest, good x) → rules cap rest op=true → Impossible u T cap (choiceVal op :: rest).toFinset
def evalMove (rule : Rule) (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 448 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      rule (cap-1) rest (movedChoice op a b)

theorem evalMove_sound {good : Sig → Prop} {rule : Rule} {u T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (allGood : ∀ v ∈ ws, good v.1) (opGood : good (dbin op a b).1)
    (valid : WellFoundedCut u T (cap-1) good rule)
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove rule (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact valid (rest.map Prod.fst) (movedChoice op a b) ndc (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hm
    · exact opGood
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact allGood w (sub.subset hw)) test k hk h

def testPair (rule : Rule) (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove rule ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (rule : Rule) (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair rule ctx a b))
def testAll (rule : Rule) (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow rule ctx a bs && testAll rule ctx bs

theorem all_binary {rule : Rule} {ctx ws} (h : testAll rule ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair rule ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair rule ctx b a d=true) := by
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

theorem testPair_at {rule : Rule} {ctx a b d} (h : testPair rule ctx a b d = true) (ka kb : Bool) :
    evalMove rule ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem node_sound {good : Sig → Prop} {rule : Rule} {u T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (allGood : ∀ v ∈ ws, good v.1)
    (stable : ∀ d a b, allowed u d → good a → good b → good (bin d a b))
    (valid : WellFoundedCut u T (cap-1) good rule)
    (checks : testAll rule (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
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
  have one (a b : Decor) (d : Nat) (legalOp : allowed u d) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair rule (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' allGood (stable d a.1 b.1 legalOp (allGood _ aa) (allGood _ bb)) valid
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) (flip_flip hd).1 hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



end CheckedNode
namespace SearchRule
abbrev Regions := List (Sig × Sig × Sig)
def extrema (regions : Regions) (domain : Sig) : Sig × Sig :=
    ((regions.find? fun it => it.1 == domain).map Prod.snd).getD (one,one)

theorem rowLe_self (m : Nat) (r : Row) : TestedCube.rowLe m r r = true := by
  simp [TestedCube.rowLe]

theorem domain_default (m : Nat) (T d : Sig) :
    TestedCube.geometry m T d (TestedCube.rowsOf one) (TestedCube.rowsOf one) := by
  intro r
  have hm : r ∈ TestedCube.rowsOf one := List.mem_filter.mpr ⟨by simp,bit_one r⟩
  cases hd : bit r d
  · simp [TestedCube.cover,hd]
  · cases ht : bit r T
    · simp only [TestedCube.cover,hd,ht,Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false,List.any_eq_true,Bool.and_eq_true]
      exact ⟨r,hm,by simp [ht],rowLe_self m r⟩
    · simp only [TestedCube.cover,hd,ht,Bool.not_true,Bool.false_or,ite_true,List.any_eq_true,Bool.and_eq_true]
      exact ⟨r,hm,ht,rowLe_self m r⟩

theorem extrema_sound {m T regions} (ok : ∀ c ∈ regions,
    TestedCube.geometry m T c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2)) (d) :
    TestedCube.geometry m T d (TestedCube.rowsOf (extrema regions d).1)
      (TestedCube.rowsOf (extrema regions d).2) := by
  unfold extrema
  cases found : regions.find? (fun it => it.1==d) with
  | none => exact domain_default m T d
  | some c =>
    have eq : c.1=d := beq_iff_eq.mp (List.find?_some (p:=fun z : Sig × Sig × Sig => z.1==d) (a:=c) found)
    subst d
    exact ok c (List.mem_of_find?_eq_some found)

abbrev Prepared := Nat × Nat × Nat × Nat × Nat × List Nat
def describe (regions : Regions) (p : BoundPool) : Prepared :=
  let en := extrema regions p.domain
  (en.1.toNat,en.2.toNat,p.domain.toNat,p.paid,p.bound,p.wires.map (nmask p.domain.toNat))

noncomputable def withSpec {β : Type} (regions : Regions) (p : BoundPool) (f : Prepared → β) : β :=
  let en := extrema regions p.domain
  force en.1.toNat fun yes => force en.2.toNat fun no => force p.domain.toNat fun domain =>
  force p.paid fun paid => force p.bound fun bound => forceMap (nmask domain) p.wires fun bank =>
    f (yes,no,domain,paid,bound,bank)

noncomputable def withSpecs {β : Type} (regions : Regions) (ps : List BoundPool) (f : List Prepared → β) : β :=
  match ps with
  | [] => f []
  | p::xs => withSpec regions p fun v => withSpecs regions xs fun vs => f (v::vs)

theorem withSpecs_eq {β : Type} (regions : Regions) (ps : List BoundPool) (f : List Prepared → β) :
    withSpecs regions ps f = f (ps.map (describe regions)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p xs ih => simp only [withSpecs,withSpec,force_eq,forceMap_eq,ih,List.map_cons,describe]

def vword (p n w : Nat) := Nat.beq (Nat.land p w) 0 || Nat.beq (Nat.land n w) n
theorem inclusionMask (n w : Sig) : (n &&& w == n) = (n &&& neg w == zero) := by
  rw [Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq]
  constructor
  · intro h
    apply bit_ext
    intro r
    have q := congrArg (bit r) h
    simp [bit,neg,zero,r.isLt] at q ⊢
    cases h1 : n.getLsbD r.val <;> cases h2 : w.getLsbD r.val <;> simp_all
  · intro h
    apply bit_ext
    intro r
    have q := congrArg (bit r) h
    simp [bit,neg,zero,r.isLt] at q ⊢
    cases h1 : n.getLsbD r.val <;> cases h2 : w.getLsbD r.val <;> simp_all

theorem vword_eq (p n w : Sig) : vword p.toNat n.toNat w.toNat = TestedCube.virtualWord p n w := by
  have z : zero.toNat=0 := by simp [zero]
  unfold vword TestedCube.virtualWord
  change ((p.toNat &&& w.toNat).beq 0 || (n.toNat &&& w.toNat).beq n.toNat) = _
  rw [←BitVec.toNat_and,←BitVec.toNat_and,←z,beq_toNat,beq_toNat,inclusionMask]

noncomputable def fastGate (p : Prepared) (k : Nat) (ws : List Sig) (g : Choice) : Bool :=
  let (pm,nm,d,spent,bound,bank) := p
  let isv := fun a : Sig => vword pm nm a.toNat
  let has := fun a : Sig => navail false d bank (nmask d a)
  let ready := fun a => isv a || has a
  let w := choiceVal g
  let extra := !(ready w)
  ((k+spent+extra.toNat < bound+(w::ws).countP isv) && ws.all ready) &&
    (!extra || allowedB false g.1 && (has g.2.1 && has g.2.2))

theorem fastGate_eq (rs : Regions) (c : BoundPool) (k : Nat) (ws : List Sig) (g : Choice) :
    fastGate (describe rs c) k ws g =
      TestedCube.gateCut (extrema rs c.domain).1 (extrema rs c.domain).2 c k ws g := by
  simp only [fastGate,describe,vword_eq,navail_eq,TestedCube.gateCut,choiceOK]

noncomputable def poolTest (rs : Regions) (po : List BoundPool) :
    Nat → List Sig → Choice → Bool :=
  withSpecs rs po fun qs => fun k ws g => qs.any fun q => fastGate q k ws g

theorem poolTest_eq (rs : Regions) (po : List BoundPool) (k : Nat) (ws : List Sig) (g : Choice) :
    poolTest rs po k ws g = po.any (fun c => let en := extrema rs c.domain
                                            TestedCube.gateCut en.1 en.2 c k ws g) := by
  simp only [poolTest,withSpecs_eq,List.any_map,Function.comp_def,fastGate_eq]

noncomputable def step (T : Sig) (rs : Regions) (po : List BoundPool) (links : Nat → List (List Sig))
    (crosses : Nat → Option CrossCheck.Corners) : CheckedNode.Rule := fun k rest op =>
  let ws := choiceVal op::rest
  let tag := keySet ws
  (links tag).any (sameWords ws) ||
    poolTest rs po k rest op ||
    ((crosses tag).map (CrossCheck.cross ws T k)).getD false

theorem step_sound {raw T} (m : Nat) (rs : Regions) (po : List BoundPool) (ls crosses k)
    (geometry : ∀ c ∈ rs, TestedCube.geometry m T c.1 (TestedCube.rowsOf c.2.1)
      (TestedCube.rowsOf c.2.2))
    (pv : ∀ p∈po, ValidPool false raw T p)
    (link : ∀ tag xs, xs∈ls tag → Impossible false T k (List.toFinset xs)) :
    CheckedNode.WellFoundedCut false T k (TestedCube.monotoneSig m) (step T rs po ls crosses) := by
  intro rest op nd mon ok
  simp only [step,poolTest_eq,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with (⟨ws,hl,eq⟩ | ⟨c,hc,cut⟩) | kw
  · rw [sameWords_sound eq]
    exact link _ _ hl
  · exact TestedCube.gateCut_sound (pv c hc) m _ _ (extrema_sound geometry _) mon nd cut
  · cases atKey : crosses (keySet (choiceVal op::rest)) with
    | none => simp [atKey] at kw
    | some witness =>
      apply CrossCheck.cross_sound nd T k witness
      simpa [atKey] using kw
end SearchRule
namespace MonotoneForest
open TestedCube

def legalProgram : Nat → Nat → Bool
  | 0,_ => true
  | n+1,ops => decide (((ops >>> 8) &&& 3)<2) && legalProgram n (ops >>> 10)

theorem stable (m d : Nat) (a b : Sig) (ok : allowed false d)
    (ha : monotoneSig m a) (hb : monotoneSig m b) : monotoneSig m (bin d a b) := by
  rcases allowed_four ok with rfl | rfl | ⟨bad,_⟩ | ⟨bad,_⟩
  · intro r s le h
    have pair : bit r a=true ∧ bit r b=true := by simpa [bit_bin] using h
    simpa [bit_bin] using And.intro (ha r s le pair.1) (hb r s le pair.2)
  · intro r s le h
    have either : bit r a=true ∨ bit r b=true := by simpa [bit_bin] using h
    simpa [bit_bin] using either.imp (ha r s le) (hb r s le)
  · cases bad
  · cases bad

theorem getMono (m : Nat) (ws : List Decor) (all : ∀ v ∈ ws, monotoneSig m v.1) (j : Nat) :
    monotoneSig m (ws.getD j defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : ws[j]? with
  | none =>
    intro r s le h
    change bit r zero=true at h
    rw [bit_zero] at h
    contradiction
  | some v => exact all v (List.mem_of_getElem? eq)

theorem decMono (m d ops : Nat) (ws : List Decor) (ok : legalProgram d ops=true)
    (all : ∀ v ∈ ws, monotoneSig m v.1) : ∀ v ∈ decodeBank d ops ws, monotoneSig m v.1 := by
  induction d generalizing ops ws with
  | zero => exact all
  | succ d ih =>
    simp only [legalProgram,Bool.and_eq_true,decide_eq_true_eq] at ok
    apply ih _ _ ok.2
    intro v hv
    rcases List.mem_append.mp hv with hm | hm
    · exact all v hm
    · obtain rfl := List.mem_singleton.mp hm
      exact stable _ _ _ _ (Or.inl ok.1) (getMono m ws all _) (getMono m ws all _)

theorem wireMono (g : Forest) : ∀ v ∈ wiresOf g, monotoneSig g.mask v.1 := by
  intro v hv
  obtain ⟨⟨j,a⟩,ha,rfl⟩ := List.mem_map.mp hv
  obtain ⟨lt,rfl⟩ := selected_entry ha
  have edge : g.mask.testBit j=true := by
    obtain ⟨u,hu,h⟩ := List.mem_filterMap.mp ha
    split at h
    next on => cases h; exact on
    next => contradiction
  intro r s le h
  rw [input_coords ⟨j,lt⟩] at h ⊢
  have he := congrArg (fun x : Nat => x.testBit j) (beq_iff_eq.mp le)
  simpa [Nat.testBit_and,edge,h] using he

def programOK (g : Forest) (k i : Nat) :=
  legalProgram (g.levels k).2.1 (readNode g k i).1

theorem stateMono (g : Forest) (k i : Nat) (ok : programOK g k i=true) :
    ∀ v∈(readNode g k i).2.2, monotoneSig g.mask v.1 := by
  intro v hv
  exact decMono g.mask (g.levels k).2.1 (readNode g k i).1 (wiresOf g) ok
    (wireMono g) v ((selectLive_sub _ _).subset hv)

theorem splitContext (g : Forest) (k i : Nat) :
    let ctx := contextOf g k i
    let ws := (readNode g k i).2.2
    ctx = (k,ws.length,ws,(coverage (!g.mode) ws,g.mode),ctx.2.2.2.2.1,ctx.2.2.2.2.2) := by
  rcases hl : g.levels k with ⟨num,d,w,j,y,z,mask,pack⟩
  rcases hn : readNode g k i with ⟨ops,bank,ws⟩
  simp only [contextOf,hl,hn,preCov]

noncomputable def strictVector {n : Nat} {β : Type} (a : BitVec n) (f : BitVec n → β) :=
  force a.toNat fun w => f (BitVec.ofNat n w)

theorem strictVector_eq {n : Nat} {β : Type} (a : BitVec n) (f : BitVec n → β) :
    strictVector a f = f a := by simp [strictVector,force_eq]

noncomputable def withWires {β : Type} (xs : List Decor) (f : List Decor → β) : β :=
  match xs with
  | [] => f []
  | w::ws => strictVector w.1 fun a => strictVector w.2.1 fun b => strictVector w.2.2 fun c =>
      withWires ws fun rest => f ((a,b,c)::rest)

theorem withWires_eq {β : Type} (xs : List Decor) (f : List Decor → β) : withWires xs f=f xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [withWires,strictVector_eq,ih]

noncomputable def withCov {β : Type} (c : Cov) (f : Cov → β) :=
  strictVector c.1 fun a => strictVector c.2.1 fun b => strictVector c.2.2 fun w => f (a,b,w)

theorem withCov_eq {β : Type} (c : Cov) (f : Cov → β) : withCov c f=f c := by
  simp only [withCov,strictVector_eq]

noncomputable def verify (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (g : Forest) (k i : Nat) :=
  let old := contextOf g k i
  let rule := SearchRule.step (targetOf g) rs old.2.2.2.2.1 old.2.2.2.2.2 crosses
  withWires (readNode g k i).2.2 fun ws =>
    withCov (coverage (!g.mode) ws) fun cov =>
      let context : NodeContext := (k,ws.length,ws,(cov,g.mode),old.2.2.2.2.1,old.2.2.2.2.2)
      (programOK g k i && decide ((ws.map Prod.fst).Nodup) && !(ws.map Prod.fst).contains (targetOf g)) &&
        (if k=0 then true else CheckedNode.testAll rule context ws)

theorem verify_sound {g : Forest} (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (k i : Nat)
    (hu : g.mode=false)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (geo : ∀ c ∈ rs, geometry g.mask (targetOf g) c.1 (rowsOf c.2.1) (rowsOf c.2.2))
    (checked : verify rs crosses g k i = true) :
    Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [verify,withWires_eq,withCov_eq,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have pr := checked.1.1.1
  have nd := checked.1.1.2
  have out : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    obtain rfl : t=0 := by omega
    exact out (List.mem_toFinset.mp (by rw [h.1]; exact Finset.mem_singleton_self _))
  let ctx := contextOf g k i
  let rule := SearchRule.step (targetOf g) rs ctx.2.2.2.2.1 ctx.2.2.2.2.2 crosses
  have tests : CheckedNode.testAll rule ctx (readNode g k i).2.2=true := by
    change CheckedNode.testAll rule (contextOf g k i) _ = true
    conv_lhs => arg 2; rw [splitContext g k i]
    simpa only [h0,ite_false] using checked.2
  have pv : ∀ c∈ctx.2.2.2.2.1, ValidPool false (vars g.mask) (targetOf g) c := by
    intro c hc
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hc
    simpa only [hu] using buildRule_sound g cols h
  have lv : ∀ tag xs, xs∈ctx.2.2.2.2.2 tag → Impossible false (targetOf g) (k-1) xs.toFinset := by
    intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa [ctx,contextOf] using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    simpa only [hu] using linkedSet_sound g _ names (prior (by omega)) h
  have wsFaith : ∀ v∈(readNode g k i).2.2, faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) v := by
    intro v hv
    exact decode_faithful _ _ _ _ _ (wires_faithful g) v ((selectLive_sub _ _).subset hv)
  have testFalse : CheckedNode.testAll rule
      (k,(readNode g k i).2.2.length,(readNode g k i).2.2,preCov false (readNode g k i).2.2,
        ctx.2.2.2.2.1,ctx.2.2.2.2.2) (readNode g k i).2.2=true := by
    rw [←hu]
    exact tests
  rw [hu]
  exact CheckedNode.node_sound samples wsFaith nd out (stateMono g k i pr) (stable g.mask)
    (SearchRule.step_sound g.mask rs _ _ crosses _ geo pv lv) testFalse

def pieces (pred : Nat → Bool) (start n : Nat) : Nat → Prop
  | 0 => (List.range n).all (fun j => pred (start+j)) = true
  | d+1 => pieces pred start (n/2) d ∧ pieces pred (start+n/2) (n-n/2) d

theorem pieces_ok {pred start n d} (ok : pieces pred start n d) (j : Nat) (hj : j<n) :
    pred (start+j) = true := by
  induction d generalizing start n j with
  | zero => exact List.all_eq_true.mp ok j (List.mem_range.mpr hj)
  | succ d ih =>
    by_cases e : j<n/2
    · exact ih ok.1 j e
    · have t := ih ok.2 (j-n/2) (by omega)
      have splitAt : start+n/2+(j-n/2) = start+j := by omega
      rwa [splitAt] at t

theorem fromZero {pred n d} (ok : pieces pred 0 n d) (j : Nat) (hj : j<n) : pred j=true := by
  simpa only [Nat.zero_add] using pieces_ok ok j hj


noncomputable def treeCheck (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners)
    (leaf : Tier.Leaves) (g : Forest) (k i : Nat) :=
  let h := leaf.1 k i
  if h=0 then verify rs crosses g k i else Tier.judge (stateSet g k i) (targetOf g) k (h-1) leaf.2

theorem treeSound {g : Forest} (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (leaf : Tier.Leaves) (k i : Nat)
    (hu : g.mode=false)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (geo : ∀ c ∈ rs, geometry g.mask (targetOf g) c.1 (rowsOf c.2.1) (rowsOf c.2.2))
    (checked : treeCheck rs crosses leaf g k i = true) :
    Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  by_cases zeroCase : leaf.1 k i=0
  · apply verify_sound rs crosses k i hu samples cols names prior geo
    simpa only [treeCheck,zeroCase,ite_true] using checked
  · rw [hu]
    apply Tier.judge_sound (v:=leaf.1 k i-1) (f:=leaf.2)
    simpa only [treeCheck,zeroCase,ite_false] using checked

abbrev TreeChecked (r : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (leaf : Tier.Leaves) (g : Forest) :=
  ∀ k ≤ g.cap, ∀ i < (g.levels k).1, treeCheck r crosses leaf g k i = true

theorem allTree {rs crosses leaf} (g : Forest) (hu : g.mode=false)
    (prior : Nat → Nat) (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (geo : ∀ c ∈ rs, TestedCube.geometry g.mask (targetOf g) c.1 (rowsOf c.2.1) (rowsOf c.2.2))
    (rows : TreeChecked rs crosses leaf g) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact treeSound rs crosses leaf 0 i hu (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) geo (rows 0 hk i hi)
  | succ k ih =>
    intro hk i hi
    exact treeSound rs crosses leaf _ i hu (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega)) geo (rows _ hk i hi)

theorem fromRoot {g : Forest} (all : ∀ i<(g.levels g.cap).1,
    Impossible g.mode (targetOf g) g.cap (stateSet g g.cap i).toFinset)
    {idx l} (row : indexedRoot g g.cap idx l=true) : Impossible g.mode (targetOf g) g.cap l.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at row
  rw [←sameWords_sound row.2]
  exact all idx row.1

theorem fromImpossible {g : Forest} {hints} (ok : Impossible g.mode (targetOf g) g.cap (vars g.mask).toFinset)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ ok
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def corners (p n : List Row) (bits : Nat) : CrossCheck.Corners :=
  (p.getD (bits &&& 15) 0,n.getD ((bits >>> 4) &&& 15) 0,p.getD ((bits >>> 8) &&& 15) 0,
   p.getD ((bits >>> 12) &&& 15) 0,n.getD ((bits >>> 16) &&& 15) 0,n.getD ((bits >>> 20) &&& 15) 0)
end MonotoneForest

def rowMask (xs : List Nat) : Sig := BitVec.ofNat 512 (xs.foldl (fun w r => w ||| (1 <<< r)) 0)
def geoRows (palette : Array Nat) (w : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => palette[(w >>> (5*j)) &&& 31]?.getD 0 ||| (geoRows palette w n (j+1) <<< 9)
def entryWord (palette : Array Nat) (dw : Nat) (entries dictionary : Nat → Nat) (j : Nat) :=
  let code := packedAt dictionary (31*(packedAt entries (dw*j) dw)) 31
  (code &&& 1) ||| (geoRows palette (code >>> 1) 6 0 <<< 1)


abbrev SparseRegion := Sig × List Row × List Row
def expandRegion (c : SparseRegion) : Sig × Sig × Sig :=
  (c.1,rowMask (c.2.1.map Fin.val),rowMask (c.2.2.map Fin.val))
def sparseOK (m : Nat) (T : Sig) (c : SparseRegion) :=
  (List.finRange 512).all (TestedCube.cover m T c.1 c.2.1 c.2.2) &&
    c.2.1.all (fun r => bit r (expandRegion c).2.1) &&
    c.2.2.all (fun r => bit r (expandRegion c).2.2)

theorem growAny {α} {xs ys : List α} (p : α → Bool) (sub : ∀ x∈xs, x∈ys)
    (ok : xs.any p=true) : ys.any p=true := by
  obtain ⟨x,h,px⟩ := List.any_eq_true.mp ok
  exact List.any_eq_true.mpr ⟨x,sub x h,px⟩

theorem sparseSound {m : Nat} {T : Sig} (c : SparseRegion) (ok : sparseOK m T c=true) :
    TestedCube.geometry m T c.1 (TestedCube.rowsOf (expandRegion c).2.1)
      (TestedCube.rowsOf (expandRegion c).2.2) := by
  simp only [sparseOK,Bool.and_eq_true,List.all_eq_true] at ok
  have yp : ∀ x ∈ c.2.1, x ∈ TestedCube.rowsOf (expandRegion c).2.1 :=
    fun x h => List.mem_filter.mpr ⟨by simp,ok.1.2 x h⟩
  have yn : ∀ x ∈ c.2.2, x ∈ TestedCube.rowsOf (expandRegion c).2.2 :=
    fun x h => List.mem_filter.mpr ⟨by simp,ok.2 x h⟩
  intro r
  have h := ok.1.1 r (by simp)
  cases b : bit r c.1 with
  | false => simp [TestedCube.cover,b]
  | true =>
    cases e : bit r T with
    | false =>
      simp only [TestedCube.cover,b,e,Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false] at h ⊢
      exact growAny _ yn h
    | true =>
      simp only [TestedCube.cover,b,e,Bool.not_true,Bool.false_or,ite_true] at h ⊢
      exact growAny _ yp h

theorem sparseAll {m : Nat} {T : Sig} {cs : List SparseRegion} (ok : cs.all (sparseOK m T)=true) :
    ∀ c ∈ cs.map expandRegion, TestedCube.geometry m T c.1
      (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := by
  intro c hc
  obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp hc
  exact sparseSound raw (List.all_eq_true.mp ok raw hr)

def mK51 := extendKnown K507 4 [(390,[32,116,133,100,101]),(356,[128,81,32,49,66,99,116]),(353,[96,81,33,50,64,131,67,116])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV51 : Known false mK51 := extend_ok (m:=51) (known_down V507) (lower_down low51) (by decide +kernel)
def mK55 := extendKnown mK51 5 [(468,[32,65,96,48,113,133,49]),(465,[113,130,49,101,82])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV55 : Known false mK55 := extend_ok (m:=55) mV51 (lower_down low55) (by decide +kernel)
def mK115 := extendKnown mK55 5 [(241,[113,33,50]),(421,[32,16,84,116,134])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV115 : Known false mK115 := extend_ok (m:=115) mV55 (lower_down low115) (by decide +kernel)
def mK119 := extendKnown mK115 7 [(119,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV119 : Known false mK119 := extend_ok (m:=119) mV115 (lower_down low119) (by decide +kernel)
def mK147 := extendKnown mK119 5 [(332,[32,49,132,84,101,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV147 : Known false mK147 := extend_ok (m:=147) mV119 (lower_down low147) (by decide +kernel)
def mK151 := extendKnown mK147 6 [(333,[49,100,84,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV151 : Known false mK151 := extend_ok (m:=151) mV147 (lower_down low151) (by decide +kernel)
def mK179 := extendKnown mK151 7 [(406,[32,116,133,101])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV179 : Known false mK179 := extend_ok (m:=179) mV151 (lower_down low179) (by decide +kernel)
def mK181 := extendKnown mK179 7 [(357,[130,84,100,114])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV181 : Known false mK181 := extend_ok (m:=181) mV179 (lower_down low181) (by decide +kernel)
def mK219 := extendKnown mK181 8 [(476,[32,49,65,129,81,118]),(462,[32,49,132,84,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV219 : Known false mK219 := extend_ok (m:=219) mV181 (lower_down low219) (by decide +kernel)
def mK221 := extendKnown mK219 7 [(231,[80,49,33,98,66,64])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV221 : Known false mK221 := extend_ok (m:=221) mV219 (lower_down low221) (by decide +kernel)
def mK223 := extendKnown mK221 9 [(415,[32,116,134]),(351,[49,100,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV223 : Known false mK223 := extend_ok (m:=223) mV221 (lower_down low223) (by decide +kernel)
def mK243 := extendKnown mK223 8 [(377,[49,33,100,84,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV243 : Known false mK243 := extend_ok (m:=243) mV223 (lower_down low243) (by decide +kernel)
def mK251 := extendKnown mK243 10 [(505,[49,33,114,100,130]),(446,[32,116,134])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV251 : Known false mK251 := extend_ok (m:=251) mV243 (lower_down low251) (by decide +kernel)
def mK254 := extendKnown mK251 9 [(491,[32,49,132,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV254 : Known false mK254 := extend_ok (m:=254) mV251 (lower_down low254) (by decide +kernel)
abbrev forestCases (g : Forest) := ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset
open MonotoneForest
def mo247Y : Array Signals := #[(sR64,sR71),(sR89,sR80),(sR20,sR29),(0,0),(sR96,sR42),(sR108,sR56),(sR4,sR59),(sR2,sR62),(0,0)]
def mo247C : List ColumnInfo := [(64,0,183,0,9),(0,64,182,1,8),(2,0,245,0,8),(4,0,243,0,8),(32,0,215,0,8),(1,0,182,0,7),(16,0,231,0,7),(36,0,211,0,7),(128,0,119,0,7),(0,2,101,144,6),(0,4,83,160,6),(0,32,146,5,6),(96,0,151,0,6),(1,32,146,4,5),(2,64,180,1,5),(6,0,241,0,5),(16,2,101,128,5),(100,0,147,0,5),(128,2,101,16,5),(128,4,83,32,5),(3,64,180,0,4),(38,0,209,0,4),(82,0,165,0,4)]
def mo247A : List (List Nat) := [[]]
def mo247D7 := packet 0x4018913902c7ac6efbb74c96058120
def mo247D8 := packet 0x2f42379c081fdb42600000000ac84800000000005f3344d7cb21285f10c0001f00827211000003c2c94000f912c40628826565a1cc28357a816247888e882c225030450e4eab4292c762b0d82bc9d4e26d34994ae4a1fcee6f2f11c7e370f85c01d327e90bf58c50c6c9549a38ca58d5ac6895344aa42550d2a6695328991558482c6f93078990c48472c035310a9086580326005646ffffbfbfbfbf7f9fbf58d615815454d324c52148110
def mo247H8 := packet 0x9d
def mo247D9 := packet 0x19d823ff1ca048017e704b770804e5f404c00472a4cf7322127c90130052c495ed6408b1236ec055413932564238512942cf32234880508790693c1dfee564ac552913a96ca63e1205001592b1c63a874cab0d41a63486b0530a41440aa153ffdf
def mo247H9 := packet 0x1c1000580000002dc0000000000065003184624001a6dd51000500000000200170000000000000000000000000000f794c000000534d400f93e2998200002c1cb0041c00000000000002a8004e02
def mo247D10 := packet 0x8218402ff
def mo247H10 := packet 0x9e000000008c009b008100001a6400a000f7995d00a695e8b302
def mo247L : Nat → Packing
  | 7 => (2,3,5,131074,17,4,1026,mo247D7)
  | 8 => (25,2,5,524298,52,9,1051,mo247D8)
  | 9 => (15,1,5,131073,16,9,1048,mo247D9)
  | 10 => (1,0,5,0,0,0,0,mo247D10)
  | _ => emptyPacking
def mo247I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 mo247H8
  | 9 => lookupWord 6 67 3 9 5 0 mo247H9
  | 10 => lookupWord 3 29 0 8 4 0 mo247H10
  | _ => fun _ => none
def mo247 : Forest := ⟨1271,10,fun i => mo247Y[i]?.getD (0,0),mo247C,mo247A,mo247L,mo247I⟩
def rm0 : List Row := [65,82,100,194,196,208]
def rm1 : List Row := [70,84,98,112,224]
def rm2 : List Row := [17,33,36,65,132,144]
def rm3 : List Row := [5,84,112,129,224]
def rm4 : List Row := [17,18,65,130,132,144]
def rm5 : List Row := [7,70,84,129,192]
def rm6 : List Row := [17,18,65,130,144]
def rm7 : List Row := [3,66,80,129,192]
def rm8 : List Row := [7,70,98]
def rm9 : List Row := [7,70,84]
def rm10 : List Row := [98,112,224]
def rm11 : List Row := [17,18,130,132,144]
def rm12 : List Row := [84,112,224]
def rm13 : List Row := [18,130,132,144,260,320]
def rm14 : List Row := [70,84,192,258,272,384]
def rm15 : List Row := [17,65,132,144,260,320]
def rm16 : List Row := [5,84,192,272,385]
def rm17 : List Row := [17,18,65,130,144,320]
def rm18 : List Row := [66,80,192,259,272,385]
def rm19 : List Row := [17,18,130,132,144,260]
def rm20 : List Row := [7,20,259,272,385]
def rm21 : List Row := [70,84,192]
def rm22 : List Row := [259,272,385]
def rm23 : List Row := [18,130,132,144,260]
def rm24 : List Row := [6,20,258,272,384]
def rm25 : List Row := [7,70,259]
def rm26 : List Row := [33,36,65,132,260,320]
def rm27 : List Row := [5,68,224,385,416]
def rm28 : List Row := [17,33,36,132,144,260]
def rm29 : List Row := [5,20,304,385,416]
def rm30 : List Row := [17,33,36,65,260,320]
def rm31 : List Row := [5,84,112,257,304]
def rm32 : List Row := [33,36,65,260,320]
def rm33 : List Row := [5,68,96,257,288]
def rm34 : List Row := [18,72,130,132,144,260,264,320]
def rm35 : List Row := [14,28,70,84,136,192,258,272,384]
def rm36 : List Row := [17,65,72,132,144,260,264,320]
def rm37 : List Row := [13,28,84,137,192,272,385]
def rm38 : List Row := [17,18,65,72,130,144,264,320]
def rm39 : List Row := [11,24,66,80,137,192,259,272,385]
def rm40 : List Row := [17,18,65,130,132,144,260,320]
def rm41 : List Row := [7,70,84,192,259,272,385]
def rm42 : List Row := [17,33,36,65,132,144,260,320]
def rm43 : List Row := [5,84,112,224,304,385,416]
def rm44 : List Row := [17,18,33,36,130,132,144,260]
def rm45 : List Row := [7,20,259,290,304,385,416]
def rm46 : List Row := [17,18,33,36,65,130,132,144]
def rm47 : List Row := [7,70,84,98,112,129,224]
def rm48 : List Row := [18,36,130,132,144,260,320]
def rm49 : List Row := [70,84,98,112,224,290,304,416]
def rm50 : List Row := [17,18,33,65,130,144,320]
def rm51 : List Row := [98,112,224,259,290,304,385,416]
def rm52 : List Row := [7,70,98,259,290]
def rm53 : List Row := [259,290,304,385,416]
def rm54 : List Row := [273,274,289,320,386,400]
def rm55 : List Row := [33,50,104,162,176,296,352]
def rm56 : List Row := [42,56,98,112,168,224,290,304,416]
def rm57 : List Row := [17,33,65,72,144,264,320]
def rm58 : List Row := [56,112,137,168,224,304,385,416]
def rm59 : List Row := [17,18,33,65,72,264,320]
def rm60 : List Row := [11,42,56,98,112,259,290,304]
def rm61 : List Row := [17,18,33,65,72,130,144]
def rm62 : List Row := [11,42,56,98,112,137,168,224]
def rm63 : List Row := [18,72,130,144,264,320]
def rm64 : List Row := [137,168,224,385,416]
def rm65 : List Row := [15,42,70,98,259,290]
def rm66 : List Row := [15,28,42,56,137,168]
def mo247S : List SparseRegion := [
(subcube 64 0,[17,18,33,36,130,132,144],[7,20,34,48,129,160]),
(subcube 0 64,rm0,rm1),
(subcube 2 0,rm2,rm3),
(subcube 4 0,[17,18,33,65,130,144],[3,98,112,129,224]),
(subcube 32 0,rm4,rm5),
(subcube 1 0,[18,36,130,132,144],rm1),
(subcube 16 0,[33,36,65,130,132],[7,70,98,129,224]),
(subcube 36 0,rm6,rm7),
(subcube 128 0,[17,18,33,36,65],[7,70,84,98,112]),
(subcube 0 2,[18,35,38,67,130],rm8),
(subcube 0 4,[21,22,36,69,132],rm9),
(subcube 0 32,[33,36,50,162,176],rm10),
(subcube 96 0,rm11,[7,20,129]),
(subcube 1 32,[36,50,162,176],rm10),
(subcube 2 64,[65,100,196,208],rm12),
(subcube 6 0,[17,33,65,144],[112,129,224]),
(subcube 16 2,[35,38,67,130],rm8),
(subcube 100 0,[17,18,130,144],[3,16,129]),
(subcube 128 2,[18,35,38,67],rm8),
(subcube 128 4,[21,22,36,69],rm9),
(subcube 3 64,[100,196,208],rm12),
(subcube 38 0,[17,65,144],[80,129,192]),
(subcube 82 0,[33,36,132],[5,129,160])]
def mo247Q := mo247S.map expandRegion
def mo247X := packet 0x79016000000000002c57400011406a00000000000000000000000900000003580000000008000000002
def mo247Z : Array Nat := #[2500179,2511670,5379088,5452818,5510160,5518370,5649426]
def mo247F (h : Nat) := ((lookupWord 2 53 1 7 3 0 mo247X h).map fun a => corners [17,18,33,36,65,130,132,144] [7,70,84,98,112,129,224] (mo247Z[a.1]?.getD 0))
def mo247Palette : Array Nat := #[0,7,17,18,33,36,65,70,84,98,112,129,130,132,144,224]
def mo247Entry := packet 0x226275444020830b2c2a88c6f19d367658948567d5219b52dac08c8d2494387902756d5340029220715499ac8df592902ca7391cf0caea1a4c1c82aad5d2de1b9c519d852227b1730cf0ca0a1a4c56626b57f304858c4485a0e9aa385f098259230bd660f648f3134995a6360c6
def mo247Item := packet 0x7312a78ce6054b1dc65a9e2b8cb53c47150f536e2a1ea69c34bd4cb8697a9868d4b0b8d1a5e865a34bd0c30a87a5b6150f4b4c29de96d8353d2e14cb79c92996f390532d4824a65a4e414c179c82350f59646a1eb28665a9228ccb52441982a48a330507100e03d0501c05bc90380b51007016a100e0256401c03bda0380179207002a240e0054201c00a040340f4160681e1240d03c2401a05bc80340a588068141240d0282201a04848034080880601eb200c02de4018052c90180f5380301e9600603d0d00c07a0b0180f4140301e7600603ce580c05a9c0180a7ba0301491c060292300c04bd80180950c03010f6806021e580c043ca018077b403002a180503d4e80a07a1c0140f4340281e7600502d4e00a05a840140b43802814718050282300a00a060100a5b802012b60040216d808042da00c0f4b00181e82c0303d05006079da00c0f3b00181e72c0303c2500605a8900c0b5080181092c020256c80404ad8
def mo247Row8 := packet 0x9c0000a20619000004a06184000040261780000a4081000000000006c0000a2801600000a46015400004a061480000a40813c00006a081000000000000000000000000000000000300000260412400002a401000000000000000000000018000006a210c000006a41000000000000000004a62100000000000
def mo247Row9 := packet 0xdc00062c844000000000000000000000000000000000c200080c622000000000000000000000000000000000a8000082c6200000000000000000000000000000000000000000000
def mo247Rows : Nat → Nat → Nat
  | 8 => fun i => packedAt mo247Row8 (i*44) 44
  | 9 => fun i => packedAt mo247Row9 (i*44) 44
  | _ => fun _ => 0
def mo247Leaf : Tier.Leaves := (mo247Rows,entryWord mo247Palette 7 mo247Entry mo247Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247G : Chart mo247 mK254 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247E : ∀ c ∈ mo247Q, TestedCube.geometry mo247.mask (targetOf mo247) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo247S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247T : TreeChecked mo247Q mo247F mo247Leaf mo247 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo247Q mo247F mo247Leaf mo247 7) 0 2 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo247Q mo247F mo247Leaf mo247 8) 0 25 3 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo247Q mo247F mo247Leaf mo247 9) 0 15 2 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo247Q mo247F mo247Leaf mo247 10) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo247All : forestCases mo247 := allTree mo247 (by decide) (boundsBefore mK254) (before_sound mK254 mV254) mo247G mo247E mo247T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247R : Impossible false (targetOf mo247) 10 (vars 247).toFinset := fromRoot (g:=mo247) (mo247All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247Low : Lower false (varsX 247) (graphGoal 247) 11 := fromImpossible (g:=mo247) (hints:=268436804) mo247R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo247K := extendKnown mK254 11 [(439,[32,116,134]),(247,[]),(493,[32,49,132,118]),(381,[49,100,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247V : Known false mo247K := extend_ok (m:=247) mV254 mo247Low (by decide +kernel)
def mo471Y : Array Signals := #[(sR98,sR66),(sR36,sR68),(sR94,sR84),(0,0),(sR104,sR86),(0,0),(sR110,sR23),(sR0,sR30),(sR3,sR35)]
def mo471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(0,256,147,68,7),(16,0,455,0,7),(65,0,406,0,7),(260,0,211,0,7),(0,1,390,80,6),(1,256,146,68,6),(320,0,151,0,6),(3,0,468,0,5),(16,1,390,64,5)]
def mo471A : List (List Nat) := [[],[32,116,134]]
def mo471D8 := packet 0x140158581cd95d54802a8498890ab02a83fdfd58110
def mo471D9 := packet 0xfe02800000026282ad86a4d4149eed59b15eb5426488058d5314d43505315815048110ff
def mo471H9 := packet 0x2cd400000018c888
def mo471D10 := packet 0x82462ff
def mo471H10 := packet 0x1d4860071000000003c0001c900000000000000240000002a60020ed80000007d000009300001f900010000084416e0004
def mo471L : Nat → Packing
  | 8 => (5,2,4,131074,17,6,1029,mo471D8)
  | 9 => (10,1,4,65537,0,7,1036,mo471D9)
  | 10 => (1,0,4,0,0,0,0,mo471D10)
  | _ => emptyPacking
def mo471I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 11 0 7 3 0 mo471H9
  | 10 => lookupWord 4 43 1 9 4 1 mo471H10
  | _ => fun _ => none
def mo471 : Forest := ⟨1495,10,fun i => mo471Y[i]?.getD (0,0),mo471C,mo471A,mo471L,mo471I⟩
def mo471S : List SparseRegion := [
(subcube 1 0,rm13,rm14),
(subcube 2 0,rm15,rm16),
(subcube 4 0,rm17,rm18),
(subcube 64 0,rm19,rm20),
(subcube 256 0,rm4,rm5),
(subcube 0 256,[260,273,274,320,386,400],rm22),
(subcube 16 0,[65,130,132,260,320],[7,70,192,259,385]),
(subcube 65 0,rm23,rm24),
(subcube 260 0,rm6,rm7),
(subcube 0 1,[17,65,131,133,261],[7,259,385]),
(subcube 1 256,[260,274,320,386,400],[258,272,384]),
(subcube 320 0,rm11,[7,20,129]),
(subcube 3 0,[132,144,260,320],[84,192,272,384]),
(subcube 16 1,[65,131,133,261],[7,259,385])]
def mo471Q := mo471S.map expandRegion
def mo471X := packet 0x39000c84
def mo471Z : Array Nat := #[2504260,2512468,3564039]
def mo471F (h : Nat) := ((lookupWord 1 5 0 6 2 0 mo471X h).map fun a => corners [17,18,65,130,132,144,260,320] [7,70,84,192,259,272,385] (mo471Z[a.1]?.getD 0))
def mo471Palette : Array Nat := #[0,7,17,18,65,70,84,130,132,144,192,259,260,272,320,385]
def mo471Entry := packet 0x9aa4ec98b90d903236fd1b2c1d2b5f68881242d2aec2c91623815f8fca086111c684cf001a98a2e1daa0ccf60c38f6ecd40e985373f99f408f0ee56aeb19831140881242d2aec2c91628908224bc61c943c85e6270569285cae546c53a24c9156c5d464e9346d756a1c4965e04eab1c99d55d96a4858e3
def mo471Item := packet 0xe419ea65c27a9a4b84f53486114f0bac229e1712c33da8a5867b5049d6d78c93adaa1d275b54324eb328649cad50e923daa15235bda7a46b7b4e48d6a31e81b5e54d036bca9206d51533b0cf5a07605eb44e36bd698c8b694511d6d78c0701ed480e03da201c07ace0380f3200701e5380e035e901c06ac60380d5240701a5180e02de701c05b460380b51c070166180e028c901c0514e038067a20700c5180e014c301c00bd1038017a00601ed100c03d67018078510300d7a40601ab180c02de701805b460300b68806014f740c029ee01207b440240f53a0481e6740903cce01205b440240a7ba04814f7009029e48120535d0240a6b80480cf6409019ac81200bd1024017a00401ea740803d4e01006a920200b51c0381ea700703d4480e07a8801c0d78a0381ab18070356280e053dd01c067b20380cb64070196c00e00bd101c017a00201ea740403cc88080794e0100f0a20201a5180402d4700803291010065200181e6640303cc88060795d00c0f2b20181e5440303ca40060785100c0a5ba01016d1c02029ae804033d1
def mo471Row8 := packet 0x240000824011800006a8210c0000a684100000000000000000826a1
def mo471Row9 := packet 0xf60008062a2d80060a4c84ba008026a44a00004c26a2860004c62a2680060a4c84000000000004a00628c4a430000c8a62200000000000
def mo471Rows : Nat → Nat → Nat
  | 8 => fun i => packedAt mo471Row8 (i*44) 44
  | 9 => fun i => packedAt mo471Row9 (i*44) 44
  | _ => fun _ => 0
def mo471Leaf : Tier.Leaves := (mo471Rows,entryWord mo471Palette 7 mo471Entry mo471Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471G : Chart mo471 mo247K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471E : ∀ c ∈ mo471Q, TestedCube.geometry mo471.mask (targetOf mo471) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo471S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471T : TreeChecked mo471Q mo471F mo471Leaf mo471 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo471Q mo471F mo471Leaf mo471 8) 0 5 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo471Q mo471F mo471Leaf mo471 9) 0 10 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo471Q mo471F mo471Leaf mo471 10) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo471All : forestCases mo471 := allTree mo471 (by decide) (boundsBefore mo247K) (before_sound mo247K mo247V) mo471G mo471E mo471T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471R : Impossible false (targetOf mo471) 10 (vars 471).toFinset := fromRoot (g:=mo471) (mo471All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471Low : Lower false (varsX 471) (graphGoal 471) 11 := fromImpossible (g:=mo471) (hints:=8858371908) mo471R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo471K := extendKnown mo247K 11 [(477,[49,100,135]),(471,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471V : Known false mo471K := extend_ok (m:=471) mo247V mo471Low (by decide +kernel)
def mo501Y : Array Signals := #[(sR77,sR65),(0,0),(sR78,sR25),(0,0),(sR21,sR54),(sR95,sR73),(sR107,sR39),(sR1,sR75),(sR5,sR76)]
def mo501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7),(144,0,357,0,7),(320,0,181,0,7),(0,16,356,129,6),(0,64,180,257,6),(0,128,353,20,6),(0,256,177,68,6),(1,16,356,128,5),(1,64,180,256,5),(4,128,353,16,5),(4,256,177,64,5),(80,0,421,0,5),(176,0,325,0,4)]
def mo501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def mo501D7 := packet 0x381ff14154110
def mo501D8 := packet 0x1fa063a823104000000000000380c4a4050080a0a3c9411c341de9af9b2e4c78b0e01141a2c445084b1a1768acb15522a9c8731aa07fffdf7efdfd504c910
def mo501H8 := packet 0x9
def mo501D9 := packet 0xbb8133c58087eb014de00e00c0820c08934a00b80846106388690716ec6606c980589424c9504c110ff
def mo501H9 := packet 0x26464eb078c00300440008329c9036000b080078800003f400000002c7000009200000000000000000000000003c600000624000014100000000e5c80000000011470
def mo501D10 := packet 0x20c400a0e3ff
def mo501H10 := packet 0x1340000000016d4d8000000006490a001980000000030044000000248000000000000000000000000000002880128030000000000000000000072f9461000000000004
def mo501L : Nat → Packing
  | 7 => (1,3,5,0,0,0,0,mo501D7)
  | 8 => (10,2,5,327683,50,7,1037,mo501D8)
  | 9 => (6,1,5,65537,0,7,1042,mo501D9)
  | 10 => (1,0,5,0,0,0,0,mo501D10)
  | _ => emptyPacking
def mo501I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 mo501H8
  | 9 => lookupWord 5 53 2 10 4 2 mo501H9
  | 10 => lookupWord 3 59 1 9 3 2 mo501H10
  | _ => fun _ => none
def mo501 : Forest := ⟨1525,10,fun i => mo501Y[i]?.getD (0,0),mo501C,mo501A,mo501L,mo501I⟩
def mo501S : List SparseRegion := [
(subcube 16 0,rm26,rm27),
(subcube 32 0,rm15,rm16),
(subcube 64 0,rm28,rm29),
(subcube 128 0,rm30,rm31),
(subcube 256 0,rm2,rm3),
(subcube 1 0,[36,132,144,260,320],[84,112,224,304,416]),
(subcube 4 0,[17,33,65,144,320],[112,224,304,385,416]),
(subcube 144 0,rm32,rm33),
(subcube 320 0,[17,33,36,132,144],[5,20,48,129,160]),
(subcube 0 16,[17,52,144,276,336],[84,112,304]),
(subcube 0 64,[65,100,196,208,320],rm12),
(subcube 0 128,[132,144,161,193,448],[224,385,416]),
(subcube 0 256,[260,273,289,320,400],[304,385,416]),
(subcube 1 16,[52,144,276,336],[84,112,304]),
(subcube 1 64,[100,196,208,320],rm12),
(subcube 4 128,[144,161,193,448],[224,385,416]),
(subcube 4 256,[273,289,320,400],[304,385,416]),
(subcube 80 0,[33,36,132,260],[5,385,416]),
(subcube 176 0,[65,260,320],[5,68,257])]
def mo501Q := mo501S.map expandRegion
def mo501X := packet 0x6f000380000060
def mo501Z : Array Nat := #[3564295,4603909]
def mo501F (h : Nat) := ((lookupWord 1 11 0 5 1 0 mo501X h).map fun a => corners [17,33,36,65,132,144,260,320] [5,84,112,224,304,385,416] (mo501Z[a.1]?.getD 0))
def mo501Palette : Array Nat := #[0,5,17,33,36,65,84,112,132,144,224,260,304,320,385,416]
def mo501Entry := packet 0x1a1ca0a03c031125695505c6048894a43437944e115291721d0d779226548690b6663908da6df
def mo501Item := packet 0xd219e75da3729e5b46e53ca5954f0b69599ec4523731e2204c78534098f0a43599ee246b33dc40d617b890340f62406818f480d019eb01a033d00340679006802f240b03dc30160730402c0c70805814e280903945012053da0240a71604814c6809019e401200bc90200f5360401e124080394500a0784800c0c7a401814f6c03029c5006033d000c067900180ce4003005e480407849
def mo501Row8 := packet 0xf00002098058000031200a4000008621300000c410230000020a84000005342080000000000
def mo501Row9 := packet 0x2400524013200000000000
def mo501Rows : Nat → Nat → Nat
  | 8 => fun i => packedAt mo501Row8 (i*43) 43
  | 9 => fun i => packedAt mo501Row9 (i*43) 43
  | _ => fun _ => 0
def mo501Leaf : Tier.Leaves := (mo501Rows,entryWord mo501Palette 6 mo501Entry mo501Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501G : Chart mo501 mo471K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501E : ∀ c ∈ mo501Q, TestedCube.geometry mo501.mask (targetOf mo501) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo501S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501T : TreeChecked mo501Q mo501F mo501Leaf mo501 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo501Q mo501F mo501Leaf mo501 7) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo501Q mo501F mo501Leaf mo501 8) 0 10 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo501Q mo501F mo501Leaf mo501 9) 0 6 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo501Q mo501F mo501Leaf mo501 10) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo501All : forestCases mo501 := allTree mo501 (by decide) (boundsBefore mo471K) (before_sound mo471K mo471V) mo501G mo501E mo501T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501R : Impossible false (targetOf mo501) 10 (vars 501).toFinset := fromRoot (g:=mo501) (mo501All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501Low : Lower false (varsX 501) (graphGoal 501) 11 := fromImpossible (g:=mo501) (hints:=9126806788) mo501R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo501K := extendKnown mo471K 11 [(501,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501V : Known false mo501K := extend_ok (m:=501) mo471V mo501Low (by decide +kernel)
def mo479Y : Array Signals := #[(sR100,sR67),(sR37,sR83),(sR38,sR69),(sR93,sR85),(sR112,sR27),(0,0),(sR8,sR22),(sR9,sR31),(sR10,sR34)]
def mo479C : List ColumnInfo := [(1,0,478,0,11),(2,0,477,0,11),(4,0,475,0,11),(8,0,471,0,11)]
def mo479A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def mo479D11 := packet 0x188200ba2c8322a9ff
def mo479D12 := packet 0x4e4ff
def mo479H12 := packet 0x1d8000305cf540200010802a35d
def mo479L : Nat → Packing
  | 11 => (4,1,2,65537,0,5,1024,mo479D11)
  | 12 => (1,0,2,65537,0,0,1028,mo479D12)
  | _ => emptyPacking
def mo479I : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 2 13 1 8 2 2 mo479H12
  | _ => fun _ => none
def mo479 : Forest := ⟨1503,12,fun i => mo479Y[i]?.getD (0,0),mo479C,mo479A,mo479L,mo479I⟩
def mo479S : List SparseRegion := [
(subcube 1 0,rm34,rm35),
(subcube 2 0,rm36,rm37),
(subcube 4 0,rm38,rm39),
(subcube 8 0,rm40,rm41)]
def mo479Q := mo479S.map expandRegion
def mo479F (_ : Nat) : Option CrossCheck.Corners := none
def mo479Palette : Array Nat := #[0,15,17,18,28,65,70,72,84,130,132,137,144,192,259,260,264,272,320,385]
def mo479Entry := packet 0x2a5068c3618ad4dabeb4dce97920c48b0a3c0ab46c3820f981658d5731b2f1da14091cba8d0dbcdac38901058f05c460d2953e74309bd7400d223d150166664a1184507a4129cf6698f176415a27b78979c932304129149bf7b56a57
def mo479Item := packet 0x4a0b6ccf9416d71f2811b13e4a44daf48eb9b6191c93443214db12e076cd7240ed986581db124903a264958f44e2a312e8cc7624d168ec2ce2d118374e292871699850dd342497a26e51238cdcc0cb38985125d198e090271601204d02824089860480e88c0901c818120350c02403206040138b0080271141004dc902008cd80401198a08022e181003a69020074460400d8b0080113541001a2301e09c4503c1198a0781b3900f02e7001809c4503013694060268940c04d1201808b65030114480601b1940c036320180690e0300b8c2060171800c02d0781805a0e030089ca060111900c01270818024600300469e060088380a04db281409b6402813414050268100a0356701405b4e024136ca04822d90090366581205ce10240b69e0481139009021cf812024e00240469c038268540704c8a00e08b5801c1130c02826d900504d0a00a08b580141130c02816d3805021aa80609a2500c1343c018268500304cd28060999f00c1332a0182662c0303632804074d30080d8ca0101b1900202e300040445f
def mo479Row11 := packet 0xa200ea6c286680c4806ae5300a0e4c2900000ae6c286
def mo479Rows : Nat → Nat → Nat
  | 11 => fun i => packedAt mo479Row11 (i*44) 44
  | _ => fun _ => 0
def mo479Leaf : Tier.Leaves := (mo479Rows,entryWord mo479Palette 7 mo479Entry mo479Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479G : Chart mo479 mo501K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479E : ∀ c ∈ mo479Q, TestedCube.geometry mo479.mask (targetOf mo479) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo479S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479T : TreeChecked mo479Q mo479F mo479Leaf mo479 := by
  intro k hk
  change k ≤ 12 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo479Q mo479F mo479Leaf mo479 11) 0 4 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo479Q mo479F mo479Leaf mo479 12) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo479All : forestCases mo479 := allTree mo479 (by decide) (boundsBefore mo501K) (before_sound mo501K mo501V) mo479G mo479E mo479T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479R : Impossible false (targetOf mo479) 12 (vars 479).toFinset := fromRoot (g:=mo479) (mo479All 12 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479Low : Lower false (varsX 479) (graphGoal 479) 13 := fromImpossible (g:=mo479) (hints:=8858396484) mo479R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo479K := extendKnown mo501K 13 [(479,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479V : Known false mo479K := extend_ok (m:=479) mo501V mo479Low (by decide +kernel)
def mo503Y : Array Signals := #[(sR97,sR70),(sR101,sR79),(sR105,sR28),(0,0),(sR111,sR43),(sR13,sR57),(sR11,sR58),(sR12,sR61),(sR14,sR88)]
def mo503C : List ColumnInfo := [(2,0,501,0,11),(32,0,471,0,11),(64,0,439,0,11),(256,0,247,0,11),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(128,0,375,0,10),(0,2,357,144,9),(0,64,182,257,9),(0,256,179,68,9),(1,64,182,256,8),(4,256,179,64,8),(16,2,357,128,8),(18,0,485,0,8),(34,0,469,0,8),(64,256,179,4,8),(66,0,437,0,8),(96,0,407,0,8),(128,2,357,16,8),(130,0,373,0,8),(256,64,182,1,8),(288,0,215,0,8),(68,256,179,0,7),(144,2,357,0,7),(146,0,357,0,7),(257,64,182,0,7)]
def mo503A : List (List Nat) := [[],[32,116,134]]
def mo503D8 := packet 0x1c61440c20400187830926c249045874b08b4818991fb0dda6ecb56bab36888358d606848358d602856358120
def mo503D9 := packet 0x4fb4330e4661c8c2e1689de620bda181e50d634299a100000000000000000000000000000000003ff001c0000000000000000000000000000000000000000004e840000000143c8c00600180001c4e3a5e8290c4e0caac0e034b97083853e2d9763b142f45a31778bc3e3e20625690e3085e067c5dc729b96c5a96859964589605795c5695855954549505394c51844108400f83c0e8380d8340c8300b82c0a82809824088200781c05f15c4f11c3f0b01e04008001369503b44a21a152249c5f58deab2a4908434cb182258c0baa5268909b2984cb61d072ca82d8441cb22126810134084920418c39cf594e630873d643a8901d661dab308d15a269ecbb8f655c7b28e05a4592d22c16896f260c15a44ba50a5e6412530f03565814c240d59208241024981b0c09466904d9082789313c990a128452a64208a90c642020590102c600da2688d0b406916e2642ffaff2feefeafbefbcfbafb7fb6fb5fb2faef6ef67eeeeddeb7dfddfcdfbdfadf7df6dbddbbdb7cfdcfbcf7cefbfdbfbbbebb7bb5bb39fe8ff8ef5d1435c185205635498158093605604c9705809158d6020d635816354d6026153580835496058d325819220d6064483581635c120211704809158d2021163481635812054d604815258120
def mo503H9 := packet 0x4500000000000000000000000a4000180050001b8000c60004700000000000000a000000
def mo503D10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xc009c09408c08404f02802001801000800084838e158e38552a2154a585329e1655685735a158d485635e14c91686381061ed4184b50612c6974a90612b7d75a5f55297d40a505d4741541d05c0741401d04807419719065064174190648641521905c0641401904806219479c5cde713079a619d698575a595d695375a605d695175a201d696075a4c1d2197708655c697471a501c713071a5d1b717369c4c1a697465a5019713065250764930d9718ee5d41b9218f54930d5265f34186cd25db35c85cda50734964d1250744930d1265f24976c9721724974c925cf27c91c9265f02196c1061b04976c1721706964c125cf06941c2024307130c125db15c85c525d315c85bd25d2f4973bc865e14187856596121948506121596484864a1599799661e65995996652659849965d26597399650e659829965026593098865e641879965da659659886526596499658a62098916592459639204c2420988d6592359638e04c23717389c58e271438a06422813089061e85965a1061285964a1060a84187956596559649525da749749d6592749739d658e781309da60d368634da605369514da4c5369604da4c13688461060d820985886516688459f2456596059a211481865e0591781835e058d780635e050d781815e0585781415e04c5768845d060d781605e04c17809856065d581765605955816456024d581835605cd5816356054d581435606495816256054958132560645581815605c5581615605455814155a50d2813049658907d413604c0d717331c50cc7d742df548b7d402d25d9149744525cd1418245f50517d3145f4851813046065cf81943e05d0f81923e0548f21973d6590f81703e0500f689429e4c8a7d4129f4c4a7d212a05c0a81602a04c0a3985a4e61292d7424b50092d2024c6548317520c6408317020c480839751ce550739701ce500739201cf65c63d7518f65063d7418f55063d9218f54863d4218064863d7018f50063d20180261f61307515d3005978436561119484664a11d9184265264c839942466553098026246d3091358e21493a095905299710a6504297410b5d832d740cb5903319708c6582317608d5d81357404d5901397600e5d00396400c605364845d5595564845555915556355d54957532540260e6d30395594f55643fffffeffbfeffd7f7fedfbff77e7fbfeffdf7bdf6fdffb7effdfdbf77deefdbfaff3fdffbfb7eefbdefbbf6febfcff5d9705d1705cd705917058d705857050d704c57021570615635d5635cd635516320563605605c16058d605856054d60549604c96020d605d1545d95358d535d14358d435513154d3150d315cd205c12058d205812054d20211205d1105c110591105811054d10549104c9104c510481106146361063604636006361c306183061430610306083060430 else 0x47f1a4332877e58040b3a8f6c5140139798d983b601ec333817e328b2847c9a59660cf6c81b99ebe33882cce3788407f240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fee52014000000000000000000000000000000000000000006562000000c8c690ccc000000000000000000000000000000000001bd4631c8c00000000000000000000000027eaace36d243ba0f1a8ce0000000000173fc35180000000000000000000000000000000000023086031986eb8acdd0a4800000007816a50ce000000000000000000000000000000000000078189b6c94000000be06af91800000000000094f8c98000167e0b8a30000000000004e001f11d0a48000037f0800cc00000000000000000000000000000000000000000000000000000001d00f1508ce000000760182fe30008e0076018ec03004fdf022005b49130df518004800000000000000000000000000000000006fb280e660000000bfefe5ec28162f13f2b0470000000000378a824a25424e8d44498892228356b8c3208785934594647a5036142707055480588c66678ec7c6a1c2a61a261397c5a7574b482947524c2a23469a4d2c98043863c065a5a061c1e0608b2e18a3840be262a2c4e3e1d4fd23d06cdecb3c8fc68c3ec15bebbe3bdbbd3bcbbc3bbbbb3babba3b9bb93b8bb83b7bb73b6bb63b5bb53b4bb43b3bb33b2bb23b1bb13b0bb03afbaf3aebae3adbad3acbac3abbab3aabaa3a9ba93a8ba83a7ba73a6ba63a5ba53a4ba43a3ba33a2ba23a1ba13a0ba039fb9f39eb9e39db9d39cb9c39bb9b39ab9a399b99398b98397b97396b96395b95394b94393b93390f9078ff8f78ef8e78df8d78cf8c78bf8b78af8a789f89788f88787f87786f85c85484c8448218198118098017f97f17e97e17d97d17c97c17b97b17a97a179979176d76575d75574d74573d73572d72571d71570d6de6b56ad6a569d69568d66a66265a65264a64263a63262a62261a61260a6025fa5f25ea5e25da5b658757f57756f54553d53552d52551d51550d5054fd4f54ed4e54dd4d54cd4c54bd4b548948147947144e44643e43642e42641e4023fa3f23cf3c73bf3b73af3a739f36f36735f3393313293213193113093012f92f12e92e12d92d12c92c12b92b12a92a12992912892812792712692612592312292212192061e11d91c61b31ab18f18716f1481401381301281201181101081000f80f00e80e00d80d00c80)
def mo503H10 := packet 0x49000a985240051f000000003d50002b000000000000000000000000000000000000000000000000000000000000000000397da5000000007360000000000000000000111000a684180000000000000000003d3800000000000000000009000000000000000e5b608000000000000000000000251172c0e0025800010c0000000084c001a240a0000000000000000084000000000000000000000000000000000000000000000000000000000000000000000000000005c80000000000000000000000f000000031d0000000000022fdc59c981001814000000000020f000000003af0007570600000000000000000000000000000000000000000000000000000000007161480000000000000000000000f2800000b660011c6f3a36000068000000000000000184c00000854002070000000000000000000307800e6e00000000000003e3000246000006f5d2a00000609000830000000000000000000000000000001e6400510000000000000000000000000000000000001250000000000011a000000000000000000000000000000000000000dd0000006394a4005b100000000000000000002b200000000000000000000000000000000095c000000000000000058b00000000000000000000000000029a800a42000006a8000410cc10d500
def mo503D11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xfa5d0053687909800023fc86134a4f79600454673f004e00713bc01480004fcaa01159280000000000000000000000000000000000000000000000000000000000029fbed04297eb727bdf40200069fbe8090ac0000000002b9ec84852000001cdf44194f103b6295fe360824800d1c2180005e790a13949ff1844507a94cc281e30120000bddcb470363e14977f3002280004e318011afd3cd805000000001bf930124700000000005e50ae323a5f90d71e03230c4fa0460000007ef9004800000000000000000001f7f730228001f1e8114fe689be8016000000005f9b004e007de018003cae131f1644d38c600463cd804dbe200291cc780fbf808484721e8398f01e7c602023992b2972a223c0830a25d38004abb72e284438240b14b5609a04e90626341e3428a8e3c03038322423420b4b13063c58708b06afdaf56f36ea2dfaddadbad46cdecbec32c12bf2bd2bb2b92b72b52acaaaaa8aa6aa4aa2aa0a9ea9ca9aa98a96a94a8da86e7fa7626c66425964de4be40a3723522aa28a26a24a22a20a1ea12e10e08a01dffdfddf3dea9e29e09d81d61d41c8dc6dc4dc2dc0dbedbcdbadb8db6db4db2db0daedacdaada8da6da4da2da0d9ed9cd9ad98d96d94d92d90d8ed8cd83576974969d67d65d63d61d5fd56954952950948d4053653452f12d12b12111891050a9089068fccf6cef0ed0eb0e2cd98d78d58d38d18c84c64c44c24c04be4b50afca80a049e49c49a49309108f08d08b08908708508308107f07547346bc6005e05c05a05805084e848c46c4003983142a821c1c81340e008c003d65ff553fd85df5d77d84df5537d73df5d47d541f5dabd74af5cebd63af61e3d868f5da3d858f5d63d658f5ce3d638f54e3d828f6063c808f5da7d749f5927d739f50e7d757f5cdfd537f5d57d745f5517d735f54d7d435f593bd63ef18fbd43ef587bd41ef4c7bd87cf5db3d65cf6133d74cf5933c83cf5cf3d63cf54f3d43cf60b3d52cf4cb3d81cf5c73d61cf5473d41cf5c33d656f58dbc636f54dbd616f545bd316f581bd764f5953d744f5913d734f58d3d534f50d3d624f5493d324f5c53d514f5053d314f5c13d604f5013d760f5d03d640f60cfd733f58cfc633f54cfd433f604fd513f504fd313f5c0fd603f4c0fd762f594bd742f590bd732f54cbd432f588bd522f4c8bd702f580bd402f4c0bd202b5d2f481d76145d84176045d801761aa965ac5ce9d868b5d22d648a59669539d5c66d43785dba885e85d3a173e761f2565c95932563cb50db1534c50d39604761c1d86076141d84076081d810b210dd833e5c0f9603761c9d822d544b5412d4c4b5212e580b930226144d841560459801061c0586026140d840460815810ffffeff7f7fbfdfeff7fbfefebf6fbbbedfafe7f5cd7058d605515354543505404c5304811018c30 else 0x139ebcc08d4c853b2800b4e94b0954ebe84110900001bc15e4583ed498009b99f414000000000000001cfa7c44e00000000000000000000000170a764c40ed89cf28724d7fe5226144f18c950487f9e648499a8e5e852c26321a1f94b000cc7a5c20a5a2336038a4002f18240e2900000000000017ff38fca00a80)
def mo503H11 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x3c00000000000000000b257403000081e00000000001059000000000000000000000ca8c000000000000000005278000c9f000000000000000000a10000071a000072ed048e48c000000000000000000000000000000000000000000000000000000000000ab40000001c4600000000000000c12800000020e700000000000000ea5c0000000000000004900000000003b2772e80000000000000345b00000000000000000000000000000000000331c0000000000b350000000000000000000000000000083000000000002c5c000000000000000000000000000000000000000000000000000000000003ee20000000000144c0000000d4600000000000000000000000000000000000000000000000000000000000000020b900000000000000a2a40000000000931800000000000000000000000000000000000000306c000b0e400000004b00002ccb0003806aaaf44548f800000000000000000d0410de00000000000000000000000007160000000000308300000f53304000000000071f00000000000633c000000000000000000000000000000000000003c98000043400001c34da03f0000000000000000000000000000309100000000000000000000000000000001061b17c0000001c7b0000000000000000000000000000000000000020010000000000000031f400000018930003c37842c00000000000000000000000000000000000000000001d913f6c8f3140000000000000000000000000000000000000000000000000000000000000000000001516000000040640000000000000000000028b8000000000000000000000844400000000000001eb80000000000000000000000000d0a00039060000000000000000000000000000000000011c40000000000000000000000000000000000000000008ee0000000413800000000000000000000000000000000000000d150c74643e83661b80000003900000000000034ed00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002218000f21c0000000000000000000000000000000000000000014d332a28580000000000000000000000000000000000000000000000000000000000000000000000000000000000000002efc0000000000000000000000000000d290ce600000000001e81000000000000000000000000000000008470000000000000052b000000000000001b1800000000000000000287a00000000000097000000000000000000000b00000000000000000000633909f730c00000000000000000d1121200002cbd00000001ac74d2d430000000000048e4000622c00040c6028400211210018000208088608041000008000200405200008240040400001000242000 else 0x18cc0000000c38f7199c500000000000347800000010a1000182300000000000000000302e0000000000000000000000000000000000000000007af385191800000000000000000013a000000000000002c630002e3ba031eaa000000000028c00001cf300000000000000000000000000006be5d0e0000000b2f902c00000000000000000000000000f60000000000000000000000000000000000000000000003a0a000000000000000000000000000000000000000000793800000000000000000000000000000000001409000000014644a50000000000000000010350000000000000000000000000000d2580000000000000000000000000000000000000000000000000000000000000000000000000b9ec00000000000000000f0ec00000024557414000d4900000000000000248200000000000000000000000008320001ea20000000000000000000000000000000000000000000000000000000032700000000000b02c000d3c0000000000000000007c958ef0000000000000000000000000000805400000000000000000000000000000000002aaca1cc000804c000000000000000000000000db94000000000070340000000000000000000000000000000000000000000000000e76000000000000000000000000000062300000000000000000011940006a6000000000000000000000000071fc000d044517e984000000000000000000000000000000000000000000000000000001f800000000000000000149c000000386c000000000004980000000000000082340000000000000201a000242d000000000000000000000000000000020c40000000000000063880000000000000000022cc000a21400023e8000000292a0002cb171e4000801c000000000000000000000000000000000000000000000000000000000000003d0700038bc000101200000000001289000191f00000000000000b824000000000000000000003ca700000000000000000351000000000380000000000000036d5505800019c00000001c2200000000000000000000000000000000000000000003f80000000000000000000000000000000bc55ce1000000000000000000000000383a000000000036710000000823c000000000001908f200020240003d22000000000000000000000000091b00000000000000000000083dc000000000000000000000000139400000000000000000000000038190a0707000060e000083e400000011090000000000082f00000000000cb212ac0000000000000000000000000000921000000000000000000000535400000000000000000000000000000000000000000000000000000000000c358000000000000000000000000c07d0c900000000000000000000000000000000000c142a9b000000000) else (if j<3 then 0xa080000000000000000000000000000000000000000000000000000000000000000000000000000000000028af03ac000000000000014990000000000000000000000000000000000000000000000000a17800000000000000000000000000000000000000f36d4a3bae800000000000002c2900000000000000eb0c000000000000000000000000000000000026410000000d468000214800000000000001c72000000000000000000000000000040500000000000000000000038cd71dc000000000000000000000000000000000000000002c88000372900000000002c3c000000000000000000000000000080080000000000000000000000000000cd800000000002c5d0002cff0003323000000000000000000000000000021e0000000000000000000000000000000000000000000000000000000018ea000000058fd8d1000000000000000000000000000000008f490d0000000000000033240000000e2280000003404000000000000000000000000092900000000003c76000000000024ae045000000000002084000000000000000000000000000249d0000000000303e00000000001ee0981400000000008098000000000000000000003cfbb224000000000000000000000000f0628e900000000000000000000000000000000000000000000000000000000000048eb49b925000163a7340000000103d71080000000000000000000008b66c88000000000000000005104000c16b43300020a2000000000000000000000515c000000000000000000000000000000012b400000000000000000e014000819c0000001c0e00000000002b210000000793503f000000043e0000000104b00000000001a2113280000000000000000000036b0000000000000000000000000000000000000000000000091200000000000000c40c000000000082d0000000000000000000002c2a00000000000000000000000000000000c5382480000000000000000000000000000000920168e000006a0000000000000000000000003c9a00000000002e5900000000001e95000000000018e4000000000004dd00000000000000000000000000000000000725000014770f10000000c2100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034df0000000000000000000004198000000089b235e8d900000000001cfd00014170000000000000000032bb000000061b4000000000041a4000000000029700000000000000000000000000000000000000000000000000000d8218bf000000000000000000000c10c000fb4c0000003c9000020ec540446b00000000001eae81d4000000000000000000000000000392800000000002c6f00000 else 0x7081a8d0000000000000060ac00000000000000000f91800000000000001ea400000000003e960000000cb9000000000000000502720400084100000000000000000000000000000c27000000000000009189a9400024aa00000000000000000000093700000001cb73454000000000000024080000000000000000000000000000000000000000007308000000000000000000000000000000000000000000000742042500000000000000000000000000000000000502800000000000002d1300000007135d1c0000000000000000000000000000a1584c8000000022d4000000000000000000000000000000000000005298000000000000000000000000000000000000000))
def mo503D12 := packet 0x39e8157c02de84093ac0843f85067a8021a803895e0e2b80ec283273d0380043dbc031ff580417f8c0ed201d6102175123892886836010021478a11a08c4ae5265b19813b1b2c357a750a752e9044e14002eaaa2e6b18c6a9a86a8a8298ae0b02809806090221ff
def mo503H12 := packet 0x187916e76257800303c66f0007830627081a0a0001137016ac331b2c1f60b848c9a972320a0000a02cbea6b93ec953c3121ca15ac94000682000594714c95db41c908000000ea5309b4986452468929cc801bb231ac0670d354080911463a7893415180002670010003d55e660000002228000d1f50812d109f79429b56ad27fccc20bc00198ba5180000000003c000000004a07959d1c000000929c90c94576f00050c124e00019085f0000e6500000025640001b66229157a4f6ba000000064dd520000001b32f4395d54dc0002428001ea660ed0a800045a000a12000000000029f39f00018270000000000000891625001395b212800354ba50a3a00000000009398002f32a634afecf6a98c1dd830000b06c92d2480024589115258d22cb5fa0411b86400069c71a3970c0806964f5cfc000000000623000000001d7d78001b6e30be9800005098043c8e091c5700078ff00a00001500024f60000004254000000ca18000000fac058b11c000679000601f9130389208000d1c3125d6fd50b50000d5655c9cc4000e508003f4c601eb28003d2c0002bc32180356000006cc000038a13934800007450004275426c7514ca8dad20e4e0002d9c03e4ae74c48dc00067e7c3a17505c000d1ee9dc000070000796c000012dcf49c5f6000000000010640000003966662000000597a4780000a78003d2e000000714bd4e0000002e5c00032d00000022a40000000aa5d50000000000000054900020ec000000cbff2b40000000002e86935c2900000008b0000901ec3a110000447fa10720000114000087200000000000009440003eabf47e35c2b7538cf4e939c93845c45d709199157c1b8067aa9e087266400000000ac67895b36084a5457b818628039b0060c020244620004b0c024e08210458d4045140120850430801c04002430c224210318028000004b
def mo503D13 := packet 0x610084ff
def mo503H13 := packet 0xc209683ecb556140000174800000014744704800000000015c17ca0001d60051101248001831058d7384ca180000000007c4828000041f40698e69c3c10000
def mo503L : Nat → Packing
  | 8 => (8,5,5,327683,50,6,1024,mo503D8)
  | 9 => (58,4,5,2555924,101,10,1052,mo503D9)
  | 10 => (299,3,5,2228279,102,12,1110,mo503D10)
  | 11 => (179,2,5,1048592,68,12,1079,mo503D11)
  | 12 => (17,1,5,65537,0,9,1045,mo503D12)
  | 13 => (1,0,5,0,0,0,0,mo503D13)
  | _ => emptyPacking
def mo503I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 41 0 7 3 0 mo503H9
  | 10 => lookupWord 17 367 2 11 6 1 mo503H10
  | 11 => lookupWord 92 1889 3 14 9 1 mo503H11
  | 12 => lookupWord 65 389 6 13 8 1 mo503H12
  | 13 => lookupWord 7 47 5 10 5 1 mo503H13
  | _ => fun _ => none
def mo503 : Forest := ⟨1527,13,fun i => mo503Y[i]?.getD (0,0),mo503C,mo503A,mo503L,mo503I⟩
def mo503S : List SparseRegion := [
(subcube 2 0,rm42,rm43),
(subcube 32 0,rm40,rm41),
(subcube 64 0,rm44,rm45),
(subcube 256 0,rm46,rm47),
(subcube 1 0,rm48,rm49),
(subcube 4 0,rm50,rm51),
(subcube 16 0,[33,36,65,130,132,260,320],[7,70,98,224,259,290,385,416]),
(subcube 128 0,[17,18,33,36,65,260,320],[7,70,84,98,112,259,290,304]),
(subcube 0 2,[18,35,38,67,130,262,322],rm52),
(subcube 0 64,[65,82,100,194,196,208,320],rm1),
(subcube 0 256,[260,273,274,289,320,386,400],rm53),
(subcube 1 64,[82,100,194,196,208,320],rm1),
(subcube 4 256,rm54,rm53),
(subcube 16 2,[35,38,67,130,262,322],rm52),
(subcube 18 0,rm26,rm27),
(subcube 34 0,rm15,rm16),
(subcube 64 256,[260,273,274,289,386,400],rm53),
(subcube 66 0,rm28,rm29),
(subcube 96 0,rm19,rm20),
(subcube 128 2,[18,35,38,67,262,322],rm52),
(subcube 130 0,rm30,rm31),
(subcube 256 64,rm0,rm1),
(subcube 288 0,rm4,rm5),
(subcube 68 256,[273,274,289,386,400],rm53),
(subcube 144 2,[35,38,67,262,322],rm52),
(subcube 146 0,rm32,rm33),
(subcube 257 64,[82,100,194,196,208],rm1)]
def mo503Q := mo503S.map expandRegion
def mo503X (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x3ac0000000000003d9e240000000000000000060c0064c000000000000000000000000000000000000000000002180000000000000000000000000000004640000000000000000000000000000000037400d7400000009cc00000007740000000000000000000000d5c0000000000000000000000000000000000000000000000000000001dd003160000000000a0c000000000000000950000000000000000000000000000000000000000000000030f00000000000000000017000ea0000000000000000000000345000000000000000000000000000000000000000001c000000015c0000000000000000000000002c7000000006200000000000000000000000000000000000000000000000000000000000056400000b677c000000000000000004c400000000000000000000000000000000000000000000000000000000074c0000000000000000000000000000000000000000000000000000001de0000000000003120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000247000000000014c000000085c000000000000001b000000000000000000000000c60000090c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000093000003b315f9d003170000000000a4c0000000d70000000000000003a70000000000000000000000000000000000000000000560000000000000000000000000000000000021c0000000000000000000000000000000042400f2400000000000000199000000000000000000000019d000000000000000000170000000000001570001200000000000000000000000000000000000ddc000000000000000000027575c000000000000000000000000000000000000000149000000000000000000000000000000000000000000000000008240000000000000000000000000000000000000000000000000000000000000000289000000000000000001d000000000000000065c0015c0014400000000000000000000000000000000000000000000000000000000000000001820000000053000000000000000414000000000000000000000000000000000000000000855dc00000000000000000257000000000000000000000000026c000000000000000000000000000000000000000297000000000000000000000000000000000000000000000000000000000000000000031700000000000000000000cccea00000002600b00000000000005040000000d70000000000000c3800000000000084411009010000011010000000200010030100400408 else 0xd8000000000000c8c000026200000003c035e8c0000000000000000000000152d4c0000000000000000000000000000000000000000000000000000000000000088c0000000578000000000000000000000035c000000068800000000000000000000000000000000000000030f0000000000001220000000000002a2000000000000000000000000000022000000000000000000000000085c000000000000000000000000000e8800000230000000000000000000000000b3000000000000000000000000000000000000000009d00000d24000000000000000000000000000000000000000000002220dc0000000001a200000c700000000000000000000000003ac00133000000000000122000000000000000000000000000000000000000000000000000000000000ecc008d000000000000000000000008de3400000000000000000000000006cc00018000000000000003e40000000000000000000007000000000025b000000009b000000000000000c4800000000000000000000004cc00000000000098c00000000000000000000000019d0000000000000000000000000000000000000000e640000000001d9000000000000000acc00000c50000000000001b30000000000000000000000392000000000000000000000000000000000000000000000b8800003e489400000000000000000000000000000000000000000091c000000000000001f361400000000000053468000000580000000000000000000000000000000000000000000016eecc000000057c000000000000000000000000000f880000000003f200012000000000000000000000000000000000000000000000003d500000f4c00000000026200000000000000000000000000000000000000000000000000000000000000132000000000094c00000000000000000000000024c76632000000000000000000000000000000000000020500000000000000000000001470000000000000000000000000002f300000000000000000000001160000000000000000000000000000000000000000000000000000000d5c00000000000000000000000000000000000000000007c00000000000000000000000000089c00000000000000000000000000000000000000000000000674000000000000000000000000000e5400000004cf3000047001a200000000004cc000000000000000000001d00057000000000000000000000001d00000001a287c00000000000000000000220000000000000000c0000000000000000000038a00000000000000000000e7400000000000004c0098800002d7001560000042427a6c00000000000000000d4c57000000000051c000000000000330570000000000000000000000000000000000000000001a20000000000000000) else (if j<3 then 0x18a9a0000000000003d70000000000a740000000000000025781c0000000000000000000000000000000000000002e2000000000000000000000015db9800000000000000000000000008100127000000015600000000000000000000e700000000000000000000000c240065c0000000002930021d0000000000003f300000000000000000097c4e1cf58000008700000003570000084800000000000000000000000000000000000000000000000000870000000000000000000000249000000000000000000000000000000001730000000000000000000000000000000000000000024000000075400000000000000000000000000000000fcc0000000000003d800000000000000000c740000000002f30034a002220039700055000000000000000000003d2b7000000037600000000000000000000000000000000387000000000000000000000007300333000000000000000000000000000000000000000000000c58000000000000b5c006595c000000000096400000000000000000b5c000000000000000000000000000000000009700000001b3003c70000000397003dc000000000000000000000000000000000d70000000087000000000000000000005cc000000000000000000000000000000000000000000000000000000000ccc00000007cc0000000000000000000000000000000000000c880000000000000018941c000000000000002120000000000a6db30000000000000000000000000000001bdf300000000000000000000000000000000001fc80000000000000000000000000000003500000ea4000000000000000009de96003d900000000000000000000000000000000000000000000000000ad4000000000000000000000000000000000000000000000000000004c0000000000007240000000000004840000000000000000000000002150000000217000004dc00b54000000000000000000000000000000000000000000000000000000000002c90021300000000007880000000000000000081cc7000000000000000000000000000000000000000000000001d400000000000000000000000000000000000000000000000009000000000000337324000035600000000000000000000f880000000000000000000000000000000000000000000000000000d880000000000003d400000000000098b15002b2c2000000000000000000a04000000000000001f500009000000000000000000000039d00000000000000000000000000000000000000000000000000001c900000d480000000fca050000000000000000000000000000000000000207000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0xbdc0000000000000019c00000002d200000000000000069c00003930037300000000000000000000000000000000000000000000000000000008c80000000000000000000056000000000000000000000000000004002f694c000000000000000000000000000000000000000000000000000000000000000036b000000037200000000000000000000000000000000000000000000000000000000000000000000000000000000002e20000000000488e0000000000000000b74000000055c0000000000000000000000000000000000000000000000000000002ef0000000000000000000000000000000000000000000dc00000fda860000000000000000000000000003530004a00000000f70000000000002d20000000000bb4000000000000b075ca880000000000000000000289e5549000000005c0000000000000000000000000000000000000000000000000000000002f300000000000000000000000000000000000000000000000000000000000000000000000028f0000000000000000000000000000dc000000000000000000000000005ad7000000000000000000000000000000003890000000112000000000000000000000000000000003cd00000000000000000000024000000000112000000000000000000000000000000000000000000000000000000000000d5c00000000000000000000000000065800000000000000000000000031b0000000033954000000000000000000000000000000000000000000000000000000000b1c0062c0000000000000002c0000000000024007880000000870000000000000164000000000000))
def mo503Z : Array Nat := #[135728,136208,136214,332598,529424,594736,612448,612454,620646,665699,677990,1661030,2113808,2446134,2454340,2454342,2507024,2566243,2659144,2703632,2707760,2709606,2718084,2762851,2762899,2773814,2777351,2782022,3700049,5932041,6820464,6845841,7501201,7865745,7894353,7894417,7894433,7958821,8020261,8024357,8024389,8741143,9007906,9060631,9064759,9064807,9573392,9597520,9671284,9736836,9802356,9802404,9909266,9966192,9990816,9991248]
def mo503F (h : Nat) := ((lookupWord 88 2939 2 10 6 0 mo503X h).map fun a => corners [17,18,33,36,65,130,132,144,260,320] [7,70,84,98,112,224,259,290,304,385,416] (mo503Z[a.1]?.getD 0))
def mo503Palette : Array Nat := #[0,7,17,18,33,36,65,70,84,98,112,130,132,144,224,259,260,290,304,320,385,416]
def mo503Entry (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then 0x69394e8f4b91763e18896e71f09220089a4e53a3d2e45d8f86225b9c7c248802269394e8fa96b7b10fd35a4c01046a8d9a5a99c8d5f8b6e3d8462c7d68eacac6a3ab2b1a8eac6c709ce0a69713f64a08de4a517d48acca2ab7b128eadecca2ab7b128eadecca3ab7b31126d2db7c0dda5288adec0a86afb228ead6c8a96b5b10270aa9a0152590e8ead6c8a3ab2b19207425955027a628ead6c809dcba697948655a3ab7b32a5ad6c408de4a517d48ac8a2ab5b1023792945f522b3023792945f522b316b45a6b85621b31174b96c63c671ae6a81609b36aca1d6c63ecc45d2e9a92273135466cc0919c5c14c7c113a54df6d6db5c19c4661d852da8863f89618b328fae16f462db85621b31126d2db7c0dda5023792945ed22b116b45a6b85621b316f462db85621b3023792945f522b316f462db85621b3095250d87ddf903da17b0c5096769fe6ab68f10f6da681eb9d9126d2db7c0dda502375a945ecffb1823792945f522b30fd6967753023a50236be945dd0cb1c23792945f522b30e43a2d04a908b88ed3929e4358c9a1a71c6e252a01bc59d4d8ea18672220bc16cba79d63a319856ef1625233c0569ec882f05b2c1db5764f6615bbc653a4e8e33499a41236467a6151f9b8ba21e5035cc3bac718aee3390e8b412a422e2264ccaed2f47e6e191a7b89f138a5c75087a3c3757a675785899de77528fa3ab2b1a53a4e8e5f81b980872ea8e2c1dba2858656667f44b99d496dadb8e5448282c9a9e91b014170582ee676b4c1951f116e5d525b6b6df313697511b29adb21e48a0526b80a269094a3a5e8bba1e8fa8e2f549b685b8ea665784a99de77528f56962bc5d479e8e7c45b975496dadb5a5b4b6dfb3769a6d169b6cdd7eedd94e93a39696d2db7ecdda69695bedb89641a39126d2db7c0dda51696d2db7ecdda68cd306bb22990aea8ead6c895ec4ad4756cae77f4e2b5a0519eaa4b516b9c756cae77c4e2b51b21e6e752a01a9da305edb310269d823792945ed22b29a305edb310269d8756cae77f4e29985c7f6676c944ba0756cae77c4e2971b21e6e752a01bc5126d2db7c0dda50756cae77f4e2990756cae77c4e2968756cae77f4e29985c7f6656c944ba05c7f6676c944ba1630f10787614bc1ce105d470acca3ea4a3aa3b30391029e60925b2282acec8af6d099250b32b730aec1e2e8b695a7deec61dd99e4756cae77f4e29985c7f6676c944ba0756cae77c4e2971b21e6e752a01bbd126d2db7c0dda528eadecca32b2b1a8eadecc449b4b6df03769405db4b6df0376947259f7be49a02dab3ed29a9125a6db7b8d49267f9aada09c2aa6982496c808de4b717d48acca3ab7b30756cae77f4e2b54756cae77c4e2b4c1768edb098c69201768edb098c6920756cae77f4e2998756cae77c4e2970176d2db7c0ddb3a7f9aada else (if j<2 then 0x21c87c24084a26b7b2288adec017857b44ec776733ae71162d09928eadecca3ab7b3286aaecca22b7b028eadecca3ab1b1e8eadecc7cc4da5d446cae74402f4387a232e68622383e36ae2c59610d43ee58623fade8eadecca32adb085e7fed16c944ba05e7fed16c944ba0ef52af01d22fb98393b69e5e1209105e15e9f3b1dd9cd233b27015cb8a79ff17a9d511b2b9dff17a9d511b2b9ce43b69e6310db968eadec8a2ab7b1080012a42143291e8ead6c820004a90850ca47a2ab5b128ead6c8a3ab7b328eadec8a3ab5b228ead6c8a3ab5b328ead6cca2ab5b115e1726575dd0ae55e1726575dd0ae55e1726575dd0ae45e582bc741d7ae95e1726575dd0ae55e1726575dd0ae68ead6c8a3ab5b228eadecca3ab7b228ead6c8a3ab5b228ead6cca3ab5b228ead6c893ac4ad55e1726775dd0ae55e1726775dd0ae5571429975dd0ae409172676e1ca911794869e6e5cb91009172676e1ca9115e412381da6773d456cdbe8556cb352e45ee75ad16b9e15886cc1d5b2b9dfd38a66289be0598fb243f45d2e4105c8e2676cd45ba20519ea24b516b9d7d6f98f05acd78d2e45cf87cd11a5d456cee705516b9e15886cc1d5b2b9df138a5c6c879b9d4a806f11d5b2b9dfd38a641d5b2b9dfd38a64171fd995b2512e85b18f45c89202e88863f89618b328fae05c7f6676c944ba0756cae77c4e2969ff17ad1511b2b9c756cae77f4e2991b21e6e752a01bb4756cae77f4e2990756cae77c4e2968be1dd9a388b4b6dc756e3a8eebe992d02f549b685b8ea645ad16b9e15886cc5785c995d7742b91d5b2b9dfd38a64171fd995b2512e85ad16b9e15886cc6c879b9d4a806ed1d5b2b9dfd38a660250499dbe73ac8a22b7b017b6e8ac62ac578c334a4f812524a5dda3ae7b48cec9ec492d6968e53ab785c7aa66a3ab7b31894a27b27882b116b45ae785621b30c2bb078ba2da30aec1e2e8b68da082eb711ed9e0557deec365d99e8756cae77f4e29985c7f6676c944ba0756cae77c4e2971b21e6e752a01bbd442aae83985c99d5e1726775dd0ae45c7f6676c944ba1b21e6e752a01bbd5e412676f9ceb214f3e2976f9ceb228eadec85790499dbe73acc0d03e9989e20ac44b91763615906e7200891f092adacda39946793221c7e9d08424089202cca3eb863d6c4ba25862e72109022480b328fae18f5b12e89618b9c8424089202cca3eb86519e4c8871fa722109022480b328fae18f5b12e89618b9c8424089202cca3eb863d6c4ba25862e72109022480b328fae18f5b12e89618b9c8424089202cca3eb463d6c4ba25862e72109022480b328fae16c63d1722480ba2218fe25862cca3eb84c9396507e21e721f09220089b36b8a3d8d4452e90615b9c90210921f2b7a3acd4b91763615906e7200891f092ae2cda39324e5941f8879d07c2488022 else 0x3608b663d84a0b81a8eac6c75a99a5c23c86eda906158fe21a3ab7b3027380df6d69a3f99a5a9710981892cf268adb489cc4d519b302467170531f044e9537db5b6d6a6696e8f1c5b6a3683e3f87e8aadec47f8e34ae25426418563f886e4174e7224921f090210576595f4166679dbe795cea3ab7b3159578ab196677a0b36a1d489509a3c2d596e25910839c54b8a2638dfe905e757e8e6585799de80b28f424e44a95aa71a82cef11c2e3b6da82cc1c0a00a749c16902b988652bcba21c7e1488b5942d4250bb8e2585df88d68fb1ab22a9491c2e2b6ce76f66e16a66bc5e87563e879830640d6155e0c28f6011a4211f1612f4fce716ef199c716f22ab609db7e6f8fa1e7a1d55541a07d6466c2ca3d514711f421994a8531c549bc2da39da72ca5f2aa6cb8e2690a1e8f97f5f9014bd0847e8e0741b02430591852fcab1c6dbb88538a9bcba8d19866e5910870048b8a2638df2905e753a8e5185797521236372b56d76034a2d8d6699215d6a56e9e2bc73720eb9a27a7f54ab6c5a99af016dfd220b199d4a74ddc6d9698c6db89237a2880012a42143291dd7652ba3ac5c9968cab6c2a3ab7b30ed7a2d022990aea8eadecc75d94ae8eb172653ad4a16a67bc4af8ce751e2e8b6ced7a2d022990ae94d1325b75dd0ae58d4458f8fe21b9cd01f09021285ad6c86351163e3f886e73407c24084a16b3b219a4559c8fe219fa0c84a3c86e85ad6c858c3c41e1d852f073841751c2b328fae18d4452e90615b9c90210921f2b7a3acd635114ba41856e7240842487ca8e8eb355f0e0572088e999d4709ce1068fb22b55a99a5c23c86eda906158fe21a3ab7b303e0ddb35166628c762bc822112ea04020b6e8215203c061918050f0011184141e5252102bc48674081246460e00511c091608f99dc3102520c5d71140391de93d079131f11de5d529b7b6cfd694f268a4c0a04500c007ed15a6cdf6d6db0dceb9983121a460005ea7dd7742460245c99dd77424601c4c975d77424609ce0a69433f64c219d02049195838618470245823e6770c40a8c3e0ddb35166628c762bc822112eb296c0b66a4d04438df2b6a137845a86dce3deca0d4089752d0b2003966a1f45f3b88449441b295c0ea9e215203c061959860f15d1184141ea352102bc56d461008a2db889fc37a1561828b2d030ae9a0c1313e89a9f48531cce1f186046cb3f013a40063d5012e67c2145f3b87c6183ab2d061069e0250499dbe73aca01cf6975be73aca0e440a7986496ca4cd151163f886db8a6128f21ba0eb3b28270aa9a61925b281004a9061925b288674081246560e18611c091608f99dc3102a30250499dbe73aca4d04438df2b6a137845a86dce3deca0d408974073da5d6f9ceb296d461008a2db889fc37a1561828b2d030ae9a09c2aa6986496ca649370c48e20a7)) else (if j<4 then 0x2eb30385b18f5785c8e2676cd45ba10457a381da676fd456cdce88517b318f5b2e73ed5e1b8a499ca66c1406aa0647ac706184b6082739194d6cc0e1706715514cb797db752ada4b91763e05826e71f0f319c6bb36aaa1d9475d9c5c2ba7a4f41e44c7c47796d4a6dedb3d8071da38975bf6cd45738844ba430082dba0575194b3de5c6c5a6104a9a22b3b02341e1078f0438521d84a3dbc1456cc41709d46f9e74b9176358fb9c802247c24ab4b368e651d767170ae9e93d079131f11de5d529b7b6d734457683608b80923486f1a68eac2c70c5b811418915e93d079131f11de5d529b7b6dce209174bacc5396c63c347a945970768e2e8628ac4a5249c482238871fac4a2eb83ad279c49f0f88215e666edcda4966b12ac4402f4387a232e68622383e36ae2c5a287a83d5d0dac50bd0710d0f1d0f0b9602526f04a4334907a232711f887278b0ae2c5a28ae52473b96db3b1c89c05a992f13adda10d076614256c3cbc5c88ba1d80e0c4a4334919218c729c49626eb8b064d4a1233c0569c07f2f05b2384141eb76615bbc4738c10710d5b8759858ef06acb4751be79d100bd0e6347c24ae685641ae2cd9450f434563c2e5866025263f8f043add5b662f04a4335047a3867113859278b0aa2c5a81290cd241e88c9c47e21c9e2c2b8b168a48d28158db9c08f7d8a81fa14622b803022bad8a2b129492712088e21c7eb128bae18948cf015a70220bc16cb076d5da299856ef17982eae10e3918c56a9e6acb4bc473b9adb2b9491cee5b6cec7227016a66bc43f41435709d299c9e2c07e21ec5ada8b84220839c66edcd27c831ed6749ac41090443d4a2bc74b6e6916e2d71eed3b2679ec340f94a6de6620cbe1dc9e83d6eb1535466db4402f4387a232e68622383e36ad2c5a29fe38d2e885178564186225b9c5d3b0841f092200894143f57c57999be79dc2752cdada8f85a2284e1c0ec37579935ad9db30420f9044c5164e14a2bc79b6ee716e3277ef03b2659d1946793221c7e9d08424089202cca3eb87823358e3d0f21d8521b8f2f03adde79dd4709ce1059e651374e67321c7e2088ea3eccadc613c16c2498f2248021090ba20252641896188863f58c3c56d07bc1d4709ce1068fb2ab363d6c4ba25862e72109022480b328fae18f5b12e89618b9c8424089202cca3eb81dcbe648874dcba2888e20a721e4f4224921f0902116a66970466da906158fe21a3ab7b32428989322993578370ed6f58a8f64458655975a55a2bd4a1e2e7b6ceb3bc609d45a99af11a8af02c820849e2c07e21e636acb4731ba76dc1749100bd6843ae683e3686223b16b8a996a6696e8f21ab6a3683e3f87ea5adec44511889da1b6e40095fa860043faa40a4d59316a669708f21bb6a418563f8868eadecc6696a672357e2db8f6118b1f5a3ab2b1981455848 else (if j<5 then 0x9c88032c7c342b6b26850f8376cd45998a31d8af208844ba430082dba1456cc43739076f9e7709d4bc6341e21b84a3d8521d4b91763d8db9c7c24880226cdae28f215203c061918050f0011184141ea352102bc4af1d90529c3f258ba19887991456cca9699e76a5d44b91763d8db9c6324867226c3aba8d8cde041e3c10e0481e03832f0778eb105a94f1a6271324e58b63a7219ccb18cd0ab2c1a10613c13924132200891f0929cc5b2f08e1f887288ba41c4356d63bb9c2751be79eb8b36514e1363c0619c87f2f05b2384141eb76615bbbd11635172487cba23f88641856b7a3acd2bd458618fb9cec4e0852048a651d79d2ba4105728a66101cf6f9e7a7eb8b368e4b91763615906e7200891f092ae2cda39174b9111f092ba21889615906b8b368e41c4358e14876f06f9e7709d4b36b8a3d11635172487cba23f88641856b7a3acd4b91763e05826e71f0f319c6bb36aca1d456cc43739076f9e7709d4bc6341e21b84a3d8521d4b91763d8db9c7c24880226cdae28f635114ba41856e7240842487cade8eb350710d5b80e0cbc1c2509a66c6b8b06884458d45c921f2e88fe2190615ade8eb358d4458f8fe21b9c921f0902128eadecc41c4358e14876f06f9e7709d4b36b8a3c3e0ddae4f66628c6d284681a51bb1c165dae18cde058e3d0f2078120682ef0778eb301ac4edaa105946798b4b2721acc91a4cfa1ec7aa5734457683608b80923486f1a68eac6c75d8165ce08836e0224d31a46fa3ec7ac593160eb9ca66229d1ae5e8a3e918cde056e146620b81a0c80ef0778eb4f841261b125d924dd2c63a721bcca1c8c8ac688afd734457683608b80923486f1a68eac6c7220bb228935c91d4295365547a39750780e560370eca013ceb9ca66188513a6e1296d7ba57a4dd7c238829b4921f0902128eadecc5e9375f08e20a6d2487c24084a3ab7b317a4dd74238a79b47218c9037288adec0184f04448063490210921f2e8809498623f886418555b6610758ef0795ce79dbeade8eb348674081246460e00511c091608f99dc3102a3558385488223a5e751c2739e5a3ec8ad5fe38d2e8fd178622585641b9c5d7a490200891f0924143f1255f999c2751be79eb8b368e289be5b18fb343f45d2e4105c8e2676cd45ba0a26f96c63ecd0fd174b9041723899db3516e88e07657c38414b60fc57999456cc416b1a963d6c4b91782605b9c6b19ecca1eac289be5b18fb343f45d2e4105c8e2676cd45ba1ce209174bacc5396c63c347a945970768e2e85f5be63d6cb35e34b9173e1f344697515b3b9c788d1630f1078f04356ef06cd45795d47096c63d174b889202e889618b328fae1be8498f5b2cd41d2e45c42529b3bc2341e2e7579048e07699dcf515b36fa155b2cd4b917b9d9b4d0e57d2da871e2402126f950b35e33e697209cc45d else 0x4c5932e4589cc7d3b85f211ce41acc30161a490710d5b84a3dbb9c2751be79eb8b368e3ad4a16a67bc4af8ce751e2e8b6e33781078f0438520784a0cbc1de3ac417093c6f89c4c9394c031)))
def mo503Item (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xcc02c08ac2058115640b022a58160454a02c08a32058111840b02225016043e002c0878c05810f140b021e20160439902c08714058109280b006ac81600d5802c01a96058035280b006a400c0aba7018155340302a89c060551300c0aa21018154400302a864060550c00c0aa0b018154140302a78406054f000c0a9d8018153960302a728060542c80c0a858018150960302a128060510d00c0a218018140c003028164060502c00c092460181244203024880060490580c0920a018123c00302471c06048e300c0905a0181172c03022a1806044e580c0729a0180e4ac0301c864060390c00c071d80180a7340301491806025cb00c04a860180873203010168060202280c040440141554e0282aa98050554d80a0aa9a014154ce0282a89c050551300a0aa21014154360282a868050550c80a0aa18014153ce0282a758050542c00a0a28d0141449a02828930050510d80a0a21a0141441a02828830050510280a0a2040141439a02828730050492300a092210141238c02822a1c050453380a08a270141140e028228180503d0680a07a0c0140f40e0281e8180503ce680a0729a0140e4340281c864050390c00a052460140950c02812818050202200a00a04010159360202b268040562b8080ac56010157ae0202af58040524d8080a49a010147ac0202556c0404aad0080951b01012a34020254100404a23808094460101278e02024f1804046ab80808d5601011a2e02023458040464380808c860100f90e0201f2180403ab3808075660100ea4e0201d4340403a86008074a70100e94c0201d2680403a33808074660100e8ac0201cf9c04039e68080555b0100aab4020154340402a23008053c601009aac02013458040268680804d0c0100990c0201319804022b08080456001008ab20201156004022a58080454a01008a4202011480040228d0080451901008a300201128404022500080444b010087c202010f180401eb000803d5801007a400200f45804006ac00800d4a01001a4202003464040068c00800c4b00c158ae0182b15803055338060aa6600c154420182a880030550c8060aa1800c154160182a82803054f30060a9e100c153c00182a76403054ec0060a9cb00c153940182a18403054258060a84a00c149120182921003052248060a44800c1451a01828a3003051268060a24c00c144320182886003051028060a1d900c143b00182873403050e60060a05900c140b0018248840304905806091e000c117900182299803044f0006089cb00c113940181f1200303d260060746700c0e8cc0181cf3403039e60060724c00c0e4320181c86003038ec806071d800c0e3980181319803025e6006044a100c089160181112c030222500600c4b00c0189401803120020468b80408d160080ea4e0101d434020229080404518 else (if j<2 then 0x7c8704c0f90c0981ea1c1303a2b0260729a04c0e4ac0981556c1302aad0260544604c0a7340981491813026ab02604b9604c0950c0981158413022b00260455904c08ab00981152c13022a50260451904c08a300981141413022458260444604c0851609810a28130212302600d5904c01ab00980352c13006a502600d1804c0193609803268130054202600a0504c014080802b42410056840200ac9b040159340802b15c100562b0200abd7040157ac0802a16410054258200a849040150900802952410052a40200a49b040149340802922410052440200a4850401490808028f5c1004aad8200955a04012a36080254681004a82820095040401288e0802511810049e3820093c60401278a08024f10100482d02009049040120900802411c10048230200904404011aae08023558100468b02008d080401190e080232181004424820088480400f90e0801f2181003e4282007c840400eace0801d5981003a93820075260400ea1a0801d4301003a4d020074670400e7ae0801cf341002aad8200555a0400aa1a0801511810026ab02004d0d04009a18080132181002282020044460400809a08010130100202282004044040019360682b4240d0568401a0aba70341574c0682aa9c0d0555301a0aa21034154400682a82c0d0550501a0a54903414a90068292240d0524401a0a4840341471a06828e240d0514681a0a28c03414512068254240d04a8401a09221034124160682345c0d0468401a08ba70341174c06822e5c0d0455381a08aa603411440068228280d03eab81a07d490340fa2e0681f2240d03e4281a07c840340f72e0681ee340d03dc601a07b890340f51a0681ea300d03d0201a075670340eacc0681d49c0d03a9301a0750d0340ea180681d29c0d03a5301a0550d0340aa18068134580d0268681a04d0c03408ac2068115800d022ac81a0455803408a96068115280d0229081a0451903408942068112800d0224501a03d6003407ab00680f52c0d01ea501a03d18034079400680f22c0d01e4501a00d5903401ab00680352c0d006a501a00d18034017160602ae9c0c055d30180aa21030153c00602a12c0c051c68180a38c0301440806024e680c0482481808ba70301174c06022e580c03dc68180539a0300972c06002e300b056848160ad0802c157920582af200b055d38160aba602c154ce058295240b052a40160a44902c1489005828e340b051c60160a38902c1449a058289300b04a848160950802c12a0a058254100b04a23016093c902c1279005824f180b049e2816093c402c1179005822e9c0b0453301607c4802c0f71a0581e9300b03ab38160756602c0ea1a0581d4300b03a338160746602c0e7ce0581cf980b039e68160550d02c0aa1805814f340b029e6016053c602c09a1a058131980b025e681604b else 0x26c455d0cd88aba09951554332a2aa826545530cca892a19951254132a22982653d5304c94754d9928ea993251523664a2a464c944d4c9928989b32513132647ba26cc8f744c991e98993205d5360ba21ec41740bd9819d50cf033aa19a0674433c0ce8866819310cf0255142e04aa1e5c0950d0b812a1796d9a29231b04564cb608ac986c10e918d8068f61ab8caa3b57195466ae32a0ed5c65419ab8c9c3b57193866ae2a70cd5c51419ab7ca83b56f95066ad32a8ed5a65519ab4c9c3b56993866ad2a70ed2ca8825a59510434a8aa996950e530d2525515a4a4aa23471ac9768e3592cd1c6aa5da38d54b3471aa1768e3542cd1c68859a38b94b3471721668df542cd1a6b25da34d64b3469aa9768d3552cd1a6a85da34b94b3467aa1764ea8740c1ca876d83950ed3071aa1760e3542cc1a6a85d83454ed3068a05a5c1158b2b822b16170455ecae08abd85c1147b2b8228f61703d62cae07a3d85c0357b2b806af61700d1ecae01a3d85b651a8cb2a2a965654552c2ca8725858e558b6b1cab169639552dac72aa5a58e547b6b1ca8f696393a2d2c72725a58d554b6b1aaa9696353a2d2c6a725a58d148b4b1a1d16962946839a7243a134e487406855c198c5ad0e418b509c83165441262ca8820c5950e4187209c430d1438a61a02710a6a550494d4aa0829a953925352a720a6a490494d4920829a9139253522720a67d4e414cf89c824dd4a9a49ba95309355246926aa48c24115a164822b42890455e59208abca24112a144822342c90445e592088bca240f5796481eaf28900d6859201ad0a240357964806af288d952a2917493db22e927b441ca91148393e22906aac5a1b6b192c3656285c6baca2d8d75945a1ae927b635d24f686b7492d8cd441c4199e838a333d0710660c8ed0cc141da1929288a32525110647ca228c8f944412e32a0c0982b26c130564d0260ac5704c158ac0982aa6c130554d0260aa5604c154300982a82813052a48260a54804c1493609829268130522b0260a38d04c1471209828e20130514d8260a28d04c1451809828a2413051440260a25604c1449809828920130510d0260a21904c1440a0982556c1304aad0260951b04c12a340982511c1304a23026093c704c1278c09824e6c13049cd0260924704c1248c0982471813046ab82608d5604c11a2c0982321c130464302608b9604c1150e09822a1813045030260))
def mo503Row8 := packet 0x1380000193040420000064c100d8000192a0402a000064a8100780000190840120000064210018000192804000000006423
def mo503Row9 := packet 0x22e00002804108a000002100c22200000c8230858000021b8420a0000c280107f8000021b841f2000008ea1079800029b0841da00002a401073800029b0841c200000862106d80001882041aa0000086210678000020a841920000a6801061800002190417a000008641000000000000016e000008621058800018820415600006208104d800003188c12a00004a621049000003188c11e00000a423046000003b08c10e00002086c040800020a9040f600000864103a80001902040de00000864103480000212840c60000a6821030000002988c0ba00000840302d000003900c0a8000086e21027000021b88407e000086ec1000000000000007800000a84301b00000a90040600000e6201016800003080c000000000000000000000000000000000000004f0003118a8808a000c6a853
def mo503Row10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x3800021028480200000a4c11fd80002118847ea0000c46211f9000003988c7d800008462100000000000007cc000026401189800002988c61a000006a2117e800002988c5f400000a62317a00001298045dc00004a621175800002988c5d000000a623172800003188c5c400000c62316f800003188c00000000000000000000000005b20000cb04116b000002988c5a600000a403168000002900c59a00000a403000000000000058e00002a401162000002900c58200000a40315d800039288457000000a40315900000a93c855e00000a623156000003188c54c00002a401151800002900c53a00002a40114b80000a90045220000e840113f8000103a384ba0000c840112b80003228844a200002a40112580003a1004000000000000000000000000048a0000c840111f80000a90044720000c8401000000000000044a00008d04110f800032288443200002a40110980000a900441a000104a2110380000a900440200002a4010fd800012a0043ea00002ae810f7800002930439c00000ea430e400000ab9843840000070a10de000013020436c00002a8010d800000a98043540000086210d200003192040000000000000cf0000211b0433600000c6230cc000003a90c0000000000000c9000009a90431800004a6210c3000018a3042e20000628c10b5800028a3842ac00008c62100000000000002a00000846c10a500003141840000000000000a2000018a30427c0000c8a4109c0000324a8426a00000ea4309780003228842520000c8a4100000000000002460000c8a2108e80003228840000000000004158000982321024000e0a6224028003829888ff0000eca6223f58003118a88fbc00080a2623e88002028988f88000e46a223db8003229888f500026e40843cc80013a8b10f14000462ae43bd801018a310ed80004a28c439f803918a810e60002604e843908023010990e24008e04a243818039028b10de800c840a24372801b902890dac006e40a2435b8002bb1888d3800e462a043438023010990ce400c840a2432f8002031888c520000628c20000000000000a84008462a042938018a10410a240062a480400000000000000000000000002708000298b8800000000000000000000000009540008a6c2200000000000008c400e0824c400000000000000000000000001ec800280b1887980008062e21df8002818b88764000a062e21d28002018a88730000e062a21c58003818a886fc0008062a21b88002018a886c80000862a21ab800180928869400080a24219e800200a90866000060e4a2191800203928862c00080e4a21800002329888000000000000142800320139c4e00004826a41318002a103880000000000000000000000000456004e2ca750f000021b13903a200c4e82a40bb802318b9102b800c82ae44 else 0x10a20000a2061425800018120509000000c623422800003188d07e00004a06141e000003188d06c00004026141280000a810503e0000624013b30000121804ec00000c46013ad0000211804ea80000846013a70000131804da00000846213650000211884d8800004c6213588000131884d5600004c62134b0000211884d020000846213360000131884cb800000c62332b0000290184ca200000a64c327000002988cc9600000a623324000002988cc8a00000a623321000002988cc7e00000a62331e000002988cc6c0000a48013118000022884c4000000c62330e800003188cc2e0000a40813088000290204c1600004c0813028000129804bfe0000a40612fc800001a904be60000a48012f68000292004bce00004a8012f2000003188cbc200000c6232ed8000288184bb000000a6232e90000308184b9e00000c6232e6000003188cb9200000c6232e3000003188cb8600000a6232e0000002988cb7a00000c6232dd000003188cb6e00000c6232d88000211804b560000846012d28000211804b3e0000c40612cc8000211804b260000624012c8000003188cb1a00000c6232c5000003188cb0e00000c6232c2000002988cb0200000a6232bf000003188caf600000a6232bc000002900caea000010a232b78000211804ad20000846012b18000311804aba0000846012ab8000311838aa200008460129e0000029884a6c00000a841290800038a804a1800000a621283000002a104a0000000a4c100000000000009f400000a84127a000002a1049dc0000840a126d80002102849aa00000a841267800039280499200000a841261800002930497a00000a84125b800002a1049480000ac84124f0000029884930000084601249000002a1049180000840a1243000002988490000000a4c123d000002a1048e8000084621238800003988c00000000000022e000039a8848ac0000a0841229800003988c000000000000226800039900488e000009021221000010323087a000040c8c21b80000b39048620000c2e61215800002a10484a0000840a120f800002a10483200000a4c1209800028120481a00008460120)
def mo503Row11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xb000028b189e12000e426c277e00002b0989dde000a026c2762800283098800000000000075c000390b189d560000ac26274f0002831889d22000e426c27410012098291cb0000a0c622725800281b089c80000806c4870b0002831889bd800080c6226ef8002031889ba400080c62200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006d30001a130900000000000000000000000001b32000846c220000000000001ada0062840a46af0018a10291a6a0062840a46930009920291a2e0062c4a04677001893a81000000000000066f802118a81000000000000000000000000019a000ae624c46608009a102900000000000000000000000000000000000000659002109a810000000000000651802109ba91928002684ea4000000000000190e000a026c263c0018212b918d20084260a462e80021318a5862006084ae4612000283188982a006084ae460300099202917f40000862c95f60002118b3d7be0000a2c625e8001882b911786000082c625dc00028213a171e00082c4e45b300028b39116b2000082c625a6000020b18967a0008c2e445988000218b2564400086c4e458a000b102bbd612000a084e857e0001209b095a4004862ae4562800028b1894fc0008062c251b8002818b09454000a062c24e30003ab1888000000000000000000000000136e00eac26040000000000001354000eac6224ce8002bb1889320000aec6224c18003ab18892e8004c60ae400000000000012ca0026c4ae44ac0003ab18892580084c6a040000000000000000000000000000000000000123a000a6c484000000000000121e006c40aef47380028213a000000000000000000000000000000000000000000000000001102000a6c48442b80213ab19000000000000000000000000000000000000007fc039200b195f9804ea026c500000000000000000000000007d00212809b15f060c4802a657b3001b10ab95e600a0842c780000000000001da404c8026a5732831201a895c460c480a2656fc82918230adb6a008c4a265000000000000000000000000000000000000000000000000006be028210b195a88084a062ed67e8310298bb4000000000000620031200a99573c04c062aed5ba831020abb55c20408c271a5540282109b15516062ae480b530839021b09548800ae46c255068203ab18953e006ca084eb00000000000013a60840a26c5000000000000000000000000049d82821318951e40480a6c254650128b201ad15a04ac2608b00000000000011200a48c260b00000000000010cc04ae86c3900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x205a0080264c4810000390b188000000000000000000000000202a000480ae800000000000000000000000007f48012098291f7a00062c4e400000000000000000000000007ab80020b13900000000000007a500002b0989e46000a02c6278)
def mo503Rows : Nat → Nat → Nat
  | 8 => fun i => packedAt mo503Row8 (i*50) 50
  | 9 => fun i => packedAt mo503Row9 (i*50) 50
  | 10 => fun i => packedAt mo503Row10 (i*50) 50
  | 11 => fun i => packedAt mo503Row11 (i*50) 50
  | _ => fun _ => 0
def mo503Leaf : Tier.Leaves := (mo503Rows,entryWord mo503Palette 10 mo503Entry mo503Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503G : Chart mo503 mo479K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503E : ∀ c ∈ mo503Q, TestedCube.geometry mo503.mask (targetOf mo503) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo503S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503T : TreeChecked mo503Q mo503F mo503Leaf mo503 := by
  intro k hk
  change k ≤ 13 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 8) 0 8 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 9) 0 58 4 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 10) 0 299 6 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 11) 0 179 6 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 12) 0 17 2 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo503Q mo503F mo503Leaf mo503 13) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo503All : forestCases mo503 := allTree mo503 (by decide) (boundsBefore mo479K) (before_sound mo479K mo479V) mo503G mo503E mo503T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503R : Impossible false (targetOf mo503) 13 (vars 503).toFinset := fromRoot (g:=mo503) (mo503All 13 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503Low : Lower false (varsX 503) (graphGoal 503) 14 := fromImpossible (g:=mo503) (hints:=8858371396) mo503R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo503K := extendKnown mo479K 14 [(509,[49,100,135]),(503,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503V : Known false mo503K := extend_ok (m:=503) mo479V mo503Low (by decide +kernel)
def mo507Y : Array Signals := #[(sR87,sR72),(sR99,sR81),(0,0),(sR103,sR24),(sR109,sR51),(sR17,sR55),(sR15,sR26),(sR16,sR60),(sR18,sR63)]
def mo507C : List ColumnInfo := [(32,0,475,0,11),(0,32,474,1,10),(2,0,505,0,10),(8,0,499,0,10),(128,0,379,0,10),(256,0,251,0,10),(1,0,474,0,9),(16,0,491,0,9),(64,0,443,0,9),(2,128,361,16,8),(16,2,361,128,8),(16,128,361,2,8),(32,2,329,144,7)]
def mo507A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def mo507D10 := packet 0x280000000609c4c4f0308100572ab9054d264954bfffbd6150d10
def mo507D11 := packet 0xec080000006006200cc892074c96251ab398dd7a73e3c0553ac354690d30a2050fffef
def mo507H11 := packet 0x382312d3001d090d49b0000ecdc10a
def mo507D12 := packet 0x6541320ff
def mo507H12 := packet 0x1b445052a0c00b140026c00000009180000315a1000b2e00002e1baf102040000264209517c40058202
def mo507L : Nat → Packing
  | 10 => (5,2,4,131075,18,6,1029,mo507D10)
  | 11 => (7,1,4,131073,16,7,1037,mo507D11)
  | 12 => (1,0,4,65537,0,0,1030,mo507D12)
  | _ => emptyPacking
def mo507I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 2 11 4 10 3 3 mo507H11
  | 12 => lookupWord 4 31 5 10 3 3 mo507H12
  | _ => fun _ => none
def mo507 : Forest := ⟨1531,12,fun i => mo507Y[i]?.getD (0,0),mo507C,mo507A,mo507L,mo507I⟩
def mo507S : List SparseRegion := [
(subcube 32 0,rm38,rm39),
(subcube 0 32,rm55,rm56),
(subcube 2 0,rm57,rm58),
(subcube 8 0,rm50,rm51),
(subcube 128 0,rm59,rm60),
(subcube 256 0,rm61,rm62),
(subcube 1 0,rm63,rm56),
(subcube 16 0,[33,65,72,130,264,320],[11,42,98,137,168,224,259,290,385,416]),
(subcube 64 0,[17,18,33,130,144,264],[11,42,56,137,168,259,290,304,385,416]),
(subcube 2 128,[144,161,193,200,392,448],rm64),
(subcube 16 2,[35,67,74,130,266,322],[11,42,98,259,290]),
(subcube 16 128,[130,161,193,200,392,448],rm64),
(subcube 32 2,[18,67,74,130,266,322],[11,66,259])]
def mo507Q := mo507S.map expandRegion
def mo507F (_ : Nat) : Option CrossCheck.Corners := none
def mo507Palette : Array Nat := #[0,11,17,18,33,42,56,65,72,98,112,130,137,144,168,224,259,264,290,304,320,385,416]
def mo507Entry := packet 0x39487c93204e936beab4cd69fca190943e0bec77b33644e119b02788eae6b57d5a3ca38e963203fc18b4b54edd4170074a70ecc9a529bb6c8db82e9cec1874315870c3c42cd76de4a8b5bb1de1c695164c2c77f3a5604ebd0e9287c17d8ef66766905499bc406080f1ddcb6a2487aaf2070a284f1d9dcaa9dd66e60
def mo507Item := packet 0xa45cfb2348b932429133e68d2267cd0a44af923443acf8e88759f1510e9262a12afb1d4255323a287d9d4c50fb3a88a1f3351143e45a1ab929e3357233866ae13a8ed5a66f1dab2cdc3b4959d8468e569acd1c9ea59a3938cb2c73b49a58e75834b1cde969639b8ad0280b4da050159b40a02aa141404ecd028084c60500f9b40a01ea681403d2b028074da0500e92c0a01c958140292302804cc60500950c0a00d218140192302802cc6044169b40882d258110566d0220acc504413b34088275681104e0302209b0504412b2c088213181103e6d02207c960440a90c088133180d059f401a0b2a90341551e06826fa40d04d5401a093e80341274406824aa00d048d101a07da90340fad20681f3a40d03e7401a079910340eb460681d58c0d03a7181a074e20340e7a00681ca440d026a701a04b90034093200680cf440d0194881a03290034057a00680aa400b059f48160abcf02c137d005824fa40b049d181607da802c0f9520581f03c0b03ad1816075a202c0e9460581cf440b0260701604b9102c067a20580cf400b015e881009bda0201348c04024f5808049cb010092860201230c0382cfa007039e80080b49601016744020265180403dc8008074da0100598c0181f3a40303e54806074a3
def mo507Row10 := packet 0xac614000084a2622600080a2620c00060c482
def mo507Row11 := packet 0xea00ae4c26600000000000ba00ae4c6268a004eac6265a00ea4c2660000000000000000000000
def mo507Rows : Nat → Nat → Nat
  | 10 => fun i => packedAt mo507Row10 (i*44) 44
  | 11 => fun i => packedAt mo507Row11 (i*44) 44
  | _ => fun _ => 0
def mo507Leaf : Tier.Leaves := (mo507Rows,entryWord mo507Palette 7 mo507Entry mo507Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507G : Chart mo507 mo503K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507E : ∀ c ∈ mo507Q, TestedCube.geometry mo507.mask (targetOf mo507) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo507S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507T : TreeChecked mo507Q mo507F mo507Leaf mo507 := by
  intro k hk
  change k ≤ 12 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo507Q mo507F mo507Leaf mo507 10) 0 5 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo507Q mo507F mo507Leaf mo507 11) 0 7 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo507Q mo507F mo507Leaf mo507 12) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo507All : forestCases mo507 := allTree mo507 (by decide) (boundsBefore mo503K) (before_sound mo503K mo503V) mo507G mo507E mo507T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507R : Impossible false (targetOf mo507) 12 (vars 507).toFinset := fromRoot (g:=mo507) (mo507All 12 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507Low : Lower false (varsX 507) (graphGoal 507) 13 := fromImpossible (g:=mo507) (hints:=13153361988) mo507R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo507K := extendKnown mo503K 13 [(510,[32,116,134]),(507,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507V : Known false mo507K := extend_ok (m:=507) mo503V mo507Low (by decide +kernel)
def mo511Y : Array Signals := #[(sR91,sR74),(sR45,sR82),(sR53,sR90),(sR33,sR32),(sR92,sR49),(sR41,sR40),(sR50,sR48),(sR47,sR46),(sR52,sR44)]
def mo511C : List ColumnInfo := [(2,0,509,0,14),(8,0,503,0,14),(1,0,510,0,13),(4,0,507,0,13),(32,0,479,0,13),(16,0,495,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(18,0,493,0,11),(72,0,439,0,11),(130,0,381,0,11),(264,0,247,0,11),(1,32,474,4,10),(3,0,508,0,10),(4,32,474,1,10),(6,0,505,0,10),(9,0,502,0,10),(12,0,499,0,10),(16,2,365,128,10),(17,0,494,0,10),(64,8,183,256,10),(128,2,365,16,10),(132,0,379,0,10),(5,32,474,0,9),(144,2,365,0,9),(320,8,183,0,9)]
def mo511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def mo511D9 := packet 0x41000d9ae06481bda33b5556b719b2251745c1c12517458970
def mo511D10 := packet 0xfc048000000000000000000000000000000000000240000000000000002140d1eb7a2e3f83abea0e9e8de0e642af0be18842200f878365a2c960ae562a950a652289409e4e26930964a2401c0c050200c040100001925ebb11b6054e46533194e36530d94436530b94b2e333194c166b8198cc5630d58435630b58b2d63054ebb342ec9c9020b8504e0c8a4120b108a8408cc64b81929062b3156905fdabf3aecef7f8ddbb76dddb376bddab73ddcef56fd5b756bcfeaf6dbdae9fb6c8945d1706c4945d17025174589706c894589706c494589706d9a225170619745c120
def mo511H10 := packet 0x1100000010a000
def mo511D11 := packet 0x7fc9450000000000000000000000000009fe00480000000000000000000000000000000000000000000000000000bf9f20151fc0bc00557f8584140fe004800007ffc7c41600000000000000000000017ef260000000000000000000000000000000000000000000000000000000000000000000000000000be58128000000000000000001f2c0943e604a00010e27681d6e8b1c2a341815a8d325a2baae2e4f954511d0ce1c3d24d91a78cd24ad5e64cb4e67531c2e3c7a3f51e0d1f0855e189f11e1fc3785f09e0fc1781f01dffbf77def1ddfbb775ee9dcfb9771ee1dbfb776ded9dafb5769ed1d9fb3765ec9d8fb1761ec1d7fad6560a393b26e4cc9011c2304508810c210410800fc1f03a672ce19bb3666acd199b32662cc197b2e65acb195b2a652ca193b2664ac9191b22642c818fb1e63ac718db1a632c618bb1662ac5188a1041e83906a0c41682904a0840a408008001630ccfb002fa403035010344102c407b5007b440e2c410300102400a3710a3310a36d0a30d0a10d0a30b0a2cb07b31092ed0a3050bb610b330eb30ceb10ceb30aeb2caeb304f33319330d9310d9330b932cb933058037541b7143b6d512ed443674536545b635130d73129712ed7334d3330d3310d2f3313330f332ed2eb2cd42ecb592ab4350943309432c9430c9410c94308942c88bb509430e942ec9592a973747734c772ec773687714877308772e8772c87736c5732c5730c5710c57308572c840b6a2c3002cb500136a0dac4063500cb0006b31082ed082eb09b6109a4107330e8aece8aeaeaa40ed331833659192a9294894aec7512a73ae864b6c5512a56b0856ae84236582b6390aec722e85ffaff57f7ffbdfdafdd7dfbef5f6ffb77dabebdf3ff9d77fbbfbdefeeff6ffb7dd6fe7f73f77fdbfddfe6fef7f5b7fdbeedef3ff9fdcfde3feffb7fbbfd5fdef7f76fbb6ddaedff5feafecffc945d1705d1625c094589705d1425c1a225170684945c0955d12061970481745c12058970481425c120619911d18664074
def mo511H11 := packet 0x33d842710694008a34800015fe415000009615afdad31ebafbb38da2ce40000000000000001ebc600040f2003e363480080aeb2fd1061d5704
def mo511D12 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xf6c76bf6b76af6a769f69768f68767f67766f66765f65764f64763f63762f62761f61760f6075ff5f75ef5e75df5d75cf5c75bf5b75af5a759f59758f58757f57756f56755f55754f54753f53752f52751f51750f5074df4d74b34ab4a349b49348b48347b47346b4634394314294073ff3f73ef3e73df3d73cf3c73bf3b73af3a739f3973783703683603583503293213193113092e52dd2d52cd2c52bd2b52ad2a529d29528d28527d27526d26525d25524d24523d23522d2251fb1f31eb1e31db1d31cb1c319f19718f18717f17716f16715f15714f14713f13712f12711f11710f1070ff0e40c50b20aa08c08407c07406c047023000e353ce153ce32bce349ce2c9ce2a9ce2e1ce241ce309be2c9be3531e1531e32b1e3491e3091e2a91e3411e2e11e2411e3319e30f9e2ed9e3099e2c99e2a99e3259e2e59e3317e32d7e30d7e10d7e3097e2c97e3313e30d3e10d3e30b3e2cb3e3053e3316e30d6e10d6e30b6e2cb6e3056e3535e32d5e2ed5e3495e1295e3095e2e95e2c95e34d4e30d4e10d4e3094e2c94e30c9e10c9e32c8e30c8e10c8e3088e2c887b53c7953c7b5057b4a57b0a57aca57b4457ac457b4057b0057ac057a4057b2c07b0c4790c47b0c1790c17b0a17aca17b0417ac417b0d27aed27b0b27acb27b0927b5317953143491c9530cb4f0cb2f0cb0f0cb4d0caed0cb4b0cb2b0cb0b0caeb0cacb0cb250cac50cb010cae10ca4107aecf7ac8f7b0ce790ce7b08e7ac8e7b0ed7b08dc2eccc308cc2c8cc30cbc10cbc308bc2c8b7949a7b09a7ac9a7aa9a7ae5aa3518a3318a30d8a34b8a30b8a2cb8a3498a3098a2c98a2a98a3458a3258a3317a32d7a30d7a10d7a3097a2c977b317a30f7a2ed7435137b313434d3a2ed3a2eb343453a3316a30d6a10d6a30b6a2cb6a3096a2c96a30567b316a30f6a2ed6b2ed5a2e95434d4cb094cae94cb50acb0cacb4aacb0aacacaacb44acac4acb0c9c90c9cb089cac89c3086c0e86c2c86c12a8db507db307db0e7db4c7db2c7db0c7d90c7daec7d9487db087dae87dac870153c5350551505534a5530a55344553045534055300552405510c552ca552c4552c05532c05b0c4590c45b0045ac0462ca36300362c03624036b0c2690c26aca26b0026ac026a40273501734c1730c1710c1730a172ca1734417304172c4103501034417300172c017240101531830f0aaed04b3188ac980b513134d31b4b3234732b45333433912968aed592e945b2863b5079aec7b92a79ae87d2c47d2847fffffeffafeffdffdefbffaff7ff7ef6ff3feefdffdfedfddf7ddfdbfd7fbffbfebfdbfbbf7bdfbbfaff9ff5d9846197466170619705d9705d5705d17058970509702517065d6461d64611646615465d5465954615545d55459140551405d1205c12025520658746547464c74644746407461874 else 0x27fb0bb60026004fe681c08092000017c783429248000000000000001fc278f93cb80000000000000000000000000000000000007d6234032480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f96bc824005f3712194000000000000000000000fe126280920000279e0023800000000000000000000000000009ea184600000000005fe4182490000000013aeea808e00000000000000000000000000000000000000000000000027188918248000000000000007987021480000000000000000000000000000000000000005f7d8259fe2208b6609002e5dc027000000000171ea023af81110238e315a047474a655a97cc564d4b8a8e4ec495182b425351897217022c0f43e4948c5731a059603285634fc33a52a8abaa874c1a8219736d8fa3ac616ac2e36be02a99e1aacaa4a9ca94a8ca84a7ca74a6ca64a5ca54a4ca44a3ca34a2ca24a1ca14a0ca049fc9f49ec9e49dc9d49cc9c49bc9b49ac9a499c99498c98497c97496c96495c95494c94493c93492c8f78ef8c18b98b188387b87386b86385b85381a81280a8027fa7f27ea7e27da7d27ca7c27ba7b27aa7a279a79278a75f75774f74773f73772f72771f71770f7076ff6f76ef6e76df6d76c)
def mo511H12 := packet 0x10b305a051f060000000f3d911f848001e662c5082c001e4d0005138c28e370000000000f041130000000000606800106c846234c84e836000000397000112d40cf83e05d6048359174000000e2780034a723cc8fa020001054103b88223b9b400060e4001a1d5dc1858000c5e00062d3849c6141d3873800000c2ad6ac7514339d2f106423629413d9024c6000526216bc85f0c00010a0001c050000000001c3490d30f4000000e2bf06283fa5b421a8adc8a0000001948001e6cfa00000000000712e910000524000641d89016ba32c028001e350007c8f8940000005018000000000000000046a000517c001fa9f238000000e090000000001387ec474d0001803e2ce8cac0200000000034d0000000099e82a40221f000007642f0000000000720b248041442000000198a0a00000000000000000932192e570000f18ae9aa7400020700a8000c3f000341644400003008e0d60000000596000121ea0b800000000062b0000001c302000800c60820004800c42c70400cb0de880106002000001080
def mo511D13 := packet 0xbdd2871290000de7b68860096017b2924e01580005612dc454000000000000000000000000003f8da2909240000003fddd613804f88510470093b1e08c0000007e7288c0a8fbf18c0a0000000000000cc909400000000003fc893b3e856000173f2c00537d404cbd7f0008c07afdc1183fc3c9dc02adf0630518e67604d3c28c30522ff4a676052799d809ef873f300297fe34045f8c09693e82647a0633b091e018fc58808cf4018a02bde8830fe28208c3fd00023514252c95011840a269826486251322ec51cd40348c70d2e79a88499a818b1690046e52a8b3312b8438c871e171e0c36b6c4d81af352aa1518a21422734de9ad33a634be96d2ba5349e92d23a4347e8a712e21c3b831041f6be578cef9db3ae70ed8dadb53696d0d9db33636c4d85b035f6bcd612ba564a393b25245e804ef9c23365c8a99292183cc6c8c515e2803f06b0b811011000a65bd2ede995f4c87a61b5309a98614430a65e530f299594c24a5d25325298774c33a219d2ece98474b23a662d30f6996b4c35a21ad2ed6985b4bada596d1296984b4ba5a592d2a96992b4b15a50ad30ca88654c2aa5955308a96454aa2a60952c4a94254ca1a610d2e8687434b2156582b2a15900acbc86122b30d5976acb37615baead598acbb565d6b2e9616450aa27254cae0419602ca8264c1b2211901fffff7effbfdfeffdfebfb7deefdbf611745c1645514048074
def mo511H13 := packet 0x103700000000106ba018829f0bc00000003041508ef55500480005f04d0aa216e071800000005818c50b826a151540882d286d6833fc0b2033504d15384100007c5c58052096c31a02d0001030a8276cb1619c000288100a7b5f00938e49b89461a7881b73f1105e076c28e015aa8760edd339c459e69a96fdb4f37d00d66169f32314918b12044815d81600cb21480002655fc94d9bfabdbc03d80bc030212c216bf010001822081c5078f0a1823ef6b000010f622e000048ae15bc00012445016e1e6c3c0618da46b13a8bfc4178a11419040f703cd8f68115611584d48fff9169a3e7553ea6000000000007848c1f60002c6bb01bddbe0000000180d1156637d837800001caa011819c04761c5032b075d2a49841402b8256068106d8150835529600018081c0f80000000c26050990fd81d3c3b00002b05000000024338000419bc1300000084a9480001c01002489546217127b031c17d43b5804b87a20e39b67b4c60591072227e420a85d7883c1c005fb815109f72e800042037103236584b642440b9c37800058bb7c8de0a900f70da31388383581089b51a1634bd80b42e20f97b5ea08e034b8550a65d340892518e40a3413d8b350110182e695286c16d80fd081a07f55bfe2b728180ba218ce11381b8000014ce1d6c6eb83cc0fb43fb66380000000000152610a220ac0003c0c8000918a316ec0600000cbd0087a7de823e0a40001e7bb08db0eff97d07e3ac66172c0c3962885e29fde002a1360420000e3ddc2fe86500004a2b94bd8f491d0841f00d203a008cc304d53587e21dd22d5802c0bd30b0900d4088086a5f530b0667da6984e64400461a0c930e621a6e53260300004135c48e86bedf0000147d4cf831a9641b4757883000121888082cad310f5135d449495401fc0b800e6af90825434647c00b7e181a3bc46c2832b9f5a405801803e9421cac544030d52d4801c9867865d54fcd1fa03a381408ba19a0a12f3040001603b044e029712a5233156b6f6c15f9ac480eb8660159c1922563d01a12623c9a7b6469f003638487cd0aa402fa10304808b20000c04fc28bccbd13d42c061580990000e232c4b906ca1895b5006608f521cd83900003061a1ce8b25878b043214b5b7800000000001fab5424f0a0f4c481b800068db0501001703086a020021052400270e260c5b0821ac091f05000b0101f7046e081f889101031809000501eb00b819160905014d0a1f0a0003291275010a04040710001612190301020309030917345b110b040300023f014f0034011200140b050e
def mo511D14 := packet 0x9803bef401cfde019f30075c00e00314084840a4471641033cd6622cc08a8e0862dc96910c48c5401845d074591545c140483ff
def mo511H14 := packet 0x1e1c88b000253200062370de820000051000326a0000000000c6a0008d98108001623dcd8805527a1d5d91eeb02aa47b1640924055b58de010f42c0b36020002015a8b211368e07a000a95843006d4ba8494217d7e640b107adf58400000008cc0000125525c4c0000003445281b7600064c1f17036000085000045a0000001b12c220000000001e0bb4530f30f847809a0006aeec16000bd228bc001ab1714a060000f3990ba89a14a00000048e00000000000001e62000000189c000b85118781c00000000000000000002048000c1b3143dc481bc7600018d8003865da55d60001c3200c81740c400164100000000014b96108003069fc7a24800000022a0000003c1c63fc12c12b428000000000255c000200442400072f00000024100000004c1000090b0002110e0133e0000ec245139dc8bba6fc572be122aefc00000040d0002f432136c90000000c39702f72800183a0000000000000d018000001cb2c9e107f49051cb0792a820810040472053800021551b714100100e0080440800421022cf
def mo511D15 := packet 0xc41009ff
def mo511H15 := packet 0x34d008df14a24d963b090025e0007000012d9c8000000cd001c2002280015030000001c7000000144d14850
def mo511L : Nat → Packing
  | 9 => (3,6,5,196610,33,5,1024,mo511D9)
  | 10 => (32,5,5,1179655,83,9,1039,mo511D10)
  | 11 => (109,4,5,3080205,100,11,1069,mo511D11)
  | 12 => (264,3,5,1900573,85,12,1087,mo511D12)
  | 13 => (75,2,5,720904,67,11,1078,mo511D13)
  | 14 => (8,1,5,65537,0,8,1041,mo511D14)
  | 15 => (1,0,5,0,0,0,0,mo511D15)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 11 0 6 2 0 mo511H10
  | 11 => lookupWord 8 47 4 9 5 0 mo511H11
  | 12 => lookupWord 34 223 6 13 7 2 mo511H12
  | 13 => lookupWord 97 443 8 15 9 2 mo511H13
  | 14 => lookupWord 35 223 6 13 7 2 mo511H14
  | 15 => lookupWord 5 37 3 9 3 2 mo511H15
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,15,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
def mo511S : List SparseRegion := [
(subcube 2 0,[17,33,36,65,72,132,144,260,264,320],[13,28,56,84,112,137,168,224,304,385,416]),
(subcube 8 0,[17,18,33,36,65,130,132,144,260,320],[7,70,84,98,112,224,259,290,304,385,416]),
(subcube 1 0,[18,36,72,130,132,144,260,264,320],[14,28,42,56,70,84,98,112,168,224,290,304,416]),
(subcube 4 0,[17,18,33,65,72,130,144,264,320],[11,42,56,98,112,137,168,224,259,290,304,385,416]),
(subcube 32 0,[17,18,65,72,130,132,144,260,264,320],[15,28,70,84,137,192,259,272,385]),
(subcube 16 0,[33,36,65,72,130,132,260,264,320],[15,42,70,98,137,168,224,259,290,385,416]),
(subcube 64 0,[17,18,33,36,130,132,144,260,264],[15,28,42,56,137,168,259,290,304,385,416]),
(subcube 128 0,[17,18,33,36,65,72,260,264,320],[15,28,42,56,70,84,98,112,259,290,304]),
(subcube 256 0,[17,18,33,36,65,72,130,132,144],[15,28,42,56,70,84,98,112,137,168,224]),
(subcube 0 2,[18,35,38,67,74,130,262,266,322],rm65),
(subcube 18 0,[33,36,65,72,132,260,264,320],[13,68,137,168,224,385,416]),
(subcube 72 0,rm44,rm45),
(subcube 130 0,[17,33,36,65,72,260,264,320],[13,28,56,84,112,257,304]),
(subcube 264 0,rm46,rm47),
(subcube 1 32,[36,50,104,162,176,296,352],rm56),
(subcube 3 0,[36,72,132,144,260,264,320],[28,56,84,112,168,224,304,416]),
(subcube 4 32,rm55,rm56),
(subcube 6 0,rm57,rm58),
(subcube 9 0,rm48,rm49),
(subcube 12 0,rm50,rm51),
(subcube 16 2,[35,38,67,74,130,262,266,322],rm65),
(subcube 17 0,[36,72,130,132,260,264,320],[14,42,70,98,168,224,290,416]),
(subcube 64 8,[25,26,41,44,138,140,152,264],rm66),
(subcube 128 2,[18,35,38,67,74,262,266,322],rm65),
(subcube 132 0,rm59,rm60),
(subcube 5 32,[50,104,162,176,296,352],rm56),
(subcube 144 2,[35,38,67,74,262,266,322],rm65),
(subcube 320 8,[25,26,41,44,138,140,152],rm66)]
def mo511Q := mo511S.map expandRegion
def mo511X := packet 0xc12130038210c00d0000001de00257d055ea415096bd697bd30674b000c900000000003781c07a510011e0030b000de000178469cd15cd001dee79ded015cc2f9c516cc0001b00000f78000014e001070020673c009705800256d265c0031ca7ac9003c6000000001c0001700000001890000013000b805e0011ce5000d240000000160000029a002423480f00000a2a540000065752d780030b886240026d174669e000000024fe5dc365f9df27db001df4580057a9a0000100823178a1014000042102452
def mo511Z : Array Nat := #[332864,348180,660327,680807,696980,3848917,5259584,5931828,5931892,5931895,6140793,6161684,6177088,6196180,6207648,6236035,6236595,7177889,7303510,7307606,10140357,10140389,10466634,10466730,13469313,13469345,13469409,15028244,15356564,15381188,15381236,15565456,15565552]
def mo511F (h : Nat) := ((lookupWord 22 149 5 10 6 0 mo511X h).map fun a => corners [17,18,33,36,65,72,130,132,144,260,264,320] [15,28,42,56,70,84,98,112,137,168,224,259,290,304,385,416] (mo511Z[a.1]?.getD 0))
def mo511Palette : Array Nat := #[0,15,17,18,28,33,36,42,56,65,70,72,84,98,112,130,132,137,144,168,224,259,260,264,290,304,320,385,416]
def mo511Entry (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0xaada98410774c5c1445b94edc78fe782d0c72074d5ed303a59d2b296f4220c53348174c22d352c0931908423c65d357b4c6b0454e48b20ae78544b86a0fd3b18ca717ca34ec2735d302108f1974d5ed308985c84256e2115d31501317493ba21012b2804d38ba20d8574c0b431c81d357b4cd8b86e7a8945a3d1fc73d697f63a098079edcb90dc78fe7861a235981986e007532b5d1e912c028fb2e425ad42cbd6e539705138fdc79fdc78fe7a7f44e2c54d46c757f63a098079edcb90dc78fe7a778c0ec13c18bcc0c018e531f8fdc79fdc78fe7b71e3f9ed8b86e7b71e3f9e9de303b04f062f303006394c7e3f71e7e8945a3d1fc73b9d7f63a098079edcb90dc78fe7861a22e881986e007d81aff3d115b9e3d472891cc7fb9d7b642018279fe4372dc78fe7a7f44e2c54d46c757f63a098079edcb90dc78fe7b62e1b9e9f5068ad5351b1b5f98c82200e7b72e428945a3d1fc73b957f63a098079edcb90dc78fe7861a22e681986e007d81aff3d115b9771e3f9edc78fe7b62e1b9e06949e424d96b4a6f949e424d96b4e06949e424d96b4ac0f9ee3df15bb06a86acd2703e7b8cda78ce507532b5d1e912c0371e3f9edc78fe6b71e339edaf8fe5f0fcc34e0a626c6dd15734edc78fe6b60e279adaf8ce5d0a6377432e49bda7d41a2b54d46c6d7e632088039adcb8d9f5068ac2506b1b5f98c82200e7b72e4367e1f9ada78ce5371e3f9edc78fe6b71e339edc78ce69be527909365ad39be527909365ad3a4191692a5d1f0c68fa5731c425b851495634e719f16e1f26f9cee7f90c0eada8a5b5c144d3df1719f26e38fc139f6f949e424d96b4e525be8ca79e424e018ee968d10474e0480fb483f5bb8fa32acd0d896338f4c663d792a67f8896a4dd3da3866cd3ea48d0178705d96ecedd0905a062b4c31b6378dcb40c4638c8c678b4a8c8ff445256ee3e8dab6910fc1cd0d5a4a16e07b69e3f94da78ce536ce339808276bc8d3a12f907006bdc2c3cef39de303b04705ef303006394c7e3371e6ea24daa64417ed38515104353b67e1f9ed9f87e6a539f1307d151b5f1fab9f7761e3d57517cec4db6ead5afacfa69986c56f9cecf8c93a4752039be376eda78ce5371e3f9ec0f9ee3c0c1078f8be76bcb62e1b9ea25168f47f1cf58719f182601e7b72e4371e3f9e18688d5e0677f801d4cad747a44b00dc78fe7b71e3f9e9ea333bc4f062d6799c07adb5e3f71e7f71e3f9ed8b86e7b71e3f9e9ea333bc4f062d6799c07adb5e3f71e7e8945a3d1fc73b9d7f63a098079edcb90dc78fe7861a22e881986e007d81aff3d115b9f71e3f9edc78fe7b62e1b9e9f5068ac2506b505f98c82200e7b72e4303e7b8fc0f9ee3d896338f4c663d79be1cf903ecf6ced8a4638f8c678caf93e073fd4754ba771e3f9e79918e3a319e34162918e3e319e32b else (if j<2 then 0xe9fd138b15351b1d5fd8e82601e7b72e4371e3f9e2a8868f48e470731fc9e2fae783a1663a018257b6424e96ea2a9b495255851170c177bdc762e1b9ea25168f47f1cee55fd8e82601e6b72e40613d07423ee661e0263e0691891bfccb4875ba29178f9c86eb525fd8e82601e6b6ee363e4768a6e9c8d497b642018279be376ea25168f46e166e55fcb97fdf6e6b68e22864585e2808eb9e05804a263b6ae538c45a89471f87d6e61dcb818057e6b61e165d99a54324e9cf5be739b87cb90e7f71dc78fe6a8945a3d1fc73b957f63a098079adcb9018688b9a0661b801f606bfcf4456e58f51ca24731fee55ed9080609e7f8ddcb6de339adb78ce6b60e139a6f949e424d96b4e6f949e424d96b4e7c9b85c14473d597b9b7c139f6fd4aa528ee424d4825a47a459074ec4331a8aad939f26e34e5b94e5c144e3f04e7dbe527909365ad383f5bb8fa32acd0d2a67f8896a4dd3e8c8ff445256ee3e8dab6910fc1cd0d5a4a16e07b69e3f94da78ce507532b5d1e912c02a6aca4e6c59fd394e10d404ab9eda388d9f87e6b69e3394575e25807b19eed248ad29899ce6dcd115d789601ec67bb4922b4a626739b73441313a11a0f60777a329ba8eaed133ab6ea4b2e5075199ce56e0795a4a38fda7951313a11a0f60792a329ba8eaed133ab6d5d789601ec67bb4922b4a626739b7344575e25807b19eed248ad29899ce6dcd113d7713f25881dfacfac6d1a9739b7b4f4f5dc4fc96206fe3a90246901ce6ded3d3c4fb7daa2cfce53c4fafd340eace53d7713f25881dfacfac6d1a9739b7b4f4e84c69a8ca6f7683d817e604ceb44b704705d70511cd565ee6df71e7dbd52a56a8f9092e689667197e4fd1f2ace9a841d2f4d0dfbf2b5aa2b1b3f18d3b39ade354344f062d803006394c7e3f71e7c344dc3076775a329ba8eaed133ac4f6be3f97428dddd21c8dafbd9f87e6b69e3f94739be561497cd71725bbdcb906e545ad6a8e7e4d9ce5a9c66293f4ec633aacaa696d585274f719f1739bee7b72e42a0aaea67bdc6d284d5116d53b64e279ea9ab2939ce6fb4e5396e56149e7b72e42ada8a5b5c144d3df1719f26e38fdc79fa8aad401f17134e595415b94ddb38fe624d4042a64f4f516254894e5fa2bbdd0630b1ca3a9490645b2d1fa4e98cc710ab65b5c144d39be739f1719f26e38fdc79fa8aad939f26e34e5b94e5c144e3f71e7d22896b25c2a6561495396ed3d930a9f2739be719f19f5064c22bc6e088017e63372e7b8f9f5068ad5351b1b5f98c82200e7b72e42a6aca4e6c59fd394e10d404ab9eda388a36ad901d566f435b81e56928e3f69e54e16445eba3922cebdbbc80e03722261721095b504502c5404c5d24ee88404ab8013186e887a17b502d36f2060d2db608985c84256e2115d31501317493ba21012b2804d38ba20d8574ca8 else 0x519d6bb394a0284a815e5788d99685d1db2a4bcbc0691bc8139f31d3f0f789725a0a6266f0250d41ec67ce712d11685d1e22a4bcbc0832308125b3ad3f175a174788a92f2f020c8c20496ceb4fc5d685d1e22a4bcbc0832308125b3ad3f175a1747889929af020cd619c7bceb44c49b971d45ad6a8e7a5a9c66293f4ec633a4e84c69aa1b338283e1a83628ceb4fc5d64559e0a4a97dfc8139c691bf4fcc71077152592d1a977f2508725881ce717d3d9a70d29a7290e527140e4a8ff39c4b4459156772a5b477f20c8c20496ceb4fc5d64559dc4051abfc832308125b3ad3f1759156772a5b477f20c8c20496ceb4fc5d3a131a6a329be460f605f98133ad1312aa6d0941c86eb395396e56149e7b72e41565915220496e02a8ad6a5b473ad3f176853828498ba0b128d777e63f6734407d29e55565915220496e02a8ad6a5b473ad3f1797666950c93a73d6f9ce6e1f2e439fdc5ca5577fa96b1d39ca5577fa96b1d39e072f4e59156dfdca5577fa96b1d39a14e2e87e4b0d0e7e15b1e61a06dfdca5577fa96b1d39ca5577fa96b1d39e072d6455a97a4b7f1bc69d3b10cc64f98aa3aba729aea9adb3ac625b949445c34e7c5c66f9ce6e1f2e439fdc65b93a5251170d3dbe739b87cb90e7f71781cb59156a5e92dfc6f1a74ec4331781cb59156a5e92dfc6f1a74ec4331781cb59156a5e92dfc6f1a74ec43316b4464ea94a3b918544b7f9fbd3b10cc5e072d6455a97a4b7f1bc69d1710cc6921a5e917331558494e56361a89e022918ae4a6e8c3fa3fa54f9041d0c2f44a3e4275199cc5490996e9c15a4a38fcb32368845170ad2eae75e5fb2c04bc3343cc13a131ada3a94dda0d2fdfb7fb4fcc710781cb59156a5e92dfc6f1a74ec4331781cb59156a2e82dfc6516f4ec932e72de05588c20f80ac6cfad6a8d3b18ce9cb781565906f1a780a5e92d3b10cc5cb7815623083e02b1b3eb5aa34ec633a72de05588c20f0036119368d0d3b18ce956591cb20c8ce02a5b46a8ad74fceb184e84c69a8ca6f5f83d817e604ceb44c4964559e0aa2b5dfc81258832334fceb18dc78fe79cb7815623083e02b1b3eb5aa34ec633adc78fe79ca5577fa96b1d39ca556ff404d8d39e072d6455a97a4b7f1bc69d3b10cc767e1f9eda78fe50aa21a892f9161fc731dc8eb8e0e85990826015fd8ea9ab2a8a4ed39585254e5bb72e7b8f6ad38b187eb921661e07836a572f4f59156dfe8945a3d1fc73b9d7f63a098079edcb90dc78fe78aa21a892f9161fc731dc8eb9e0e85990826015fd8ea9ab2a8a4ed29585254e5bb03e7b8f2a60d06c42d2c495296f4e05f23ee88098fe3c61a22e881986e007d81aff3d115b9e8fb2e425ad42c956e539705138fdc79f49225ac970a99585254e5bb4f6503d7c9ce6f9c67c67f44d308b31d826015fd8edcb9ee3f71e3f9)) else (if j<5 then (if j<4 then 0x99db27299a4f46e5c1e09fbe0eb0d8d0454d914c4a22138ca58456c5dc861f862e70eae2bd20e859176428a826015fd8ec89d257d6b5514752d69a9ab2a8a4ed31585254e5bb72e7b8f83a164758e8fa018257b643227495f5a547551425ae4e96ea2a9b4c5255851170e439fdc5a90baa613eb2731bc711efd31350c970561495396ea1d094c23ac82088017e63372e7b8f11414a8197aac3f710470634c1253949c405384d512c81791c45ae82e0772f89ee1362e7e9aaf685ab26e6f5f0e3cfd9a8f796a7429024330abc69665c9d3ca1685d34c0eef5b868945819b45c5ad6a8ac6cfe7a3d4727398a4f96a716b04517139b9e1a83e1512f18d3b282a60d71419d344953d454e23c27ee86017cbe2a2ab6a6105c4d31705116e53b71e3f9ea8aada99ef0774c5c1445b94edc78fe784f06170511cd5656c50f71e7dbd52a38a8f909350f96a718ee4fd330acdaa0aaea60fdc4d304d5104053b62e1b9ea64fc2c4acc656a57dd251d49a8b9096e4ed36b3a26bfb3d1550d4ce7a5d8f6659c51b224878a883b8414115d2d313912728172e7c88862aa3d2391c1cc7f26cb5b9e168398e806085e98896e4eab6b0d35bc730160e390e676c6a42ea984fac9cc6f1c47bf4c4d4325c1585254e5ba87425308eb20822005f98cdcb9ee3d685d1e2264bcbb8692306725b33d1b165a17476c992f2ee1a46f19ce7cc746c3d64559dca42d1dfc692306725b33d1b16aea54999f26e33c240793a4c9e3f71e7ce13045eb9b832cebbbbc71e03687897279492216ee2588125087c5f39d39de59eef19cd4d0e8645961341523a8d8a72a5bfc6238883250871ec811718b4e414b9c4b8560483739c534b789720ec92216ee1ec8125087c5339d29de59eef19cd4d0d2866f9540e3fd12bd9be6a2bc97bb8901d8d73138fda79520883ce9675ceee20883ce9675ceee4a19be55038ff4468538ba1f92c34368538ba1f92c3434a19be55038ff449aa75aec972beee1686a310d5e2395d95e25c9682f0a9bb89421c9620739b7b4f5a1747889929aee1a4d619c7bccf44b705f199a64eab9e08e18421b89e166913987a28836e3789725a174796ef23087cf739b7b4f7897279492216ee2588125087b7b39d39e25c9682f0a9bb89421c9620739b7b4f2cc7e170687a4ba2b4a6266e361e077ec4b2c0a77e5dc1bd647837f398d433867cc2dad11685d1db264a6bb8693186733b31d12da789725a0bc2a6f02508725881ce6ded3d3a131a6a86cce0a0f86a0d8a33ad3ede99a5daeac0cf05a1a8c435788e576599a5daeac0cf05a1a8c435788e576599a5daeac0cf05a1a8c435788e57655c9e25d07b19eef248ad29899ce6dcd11e25c9682f0a9bb89421c9620739b7b4f4e4496b08222ee38362883e1ad3f38b764e96ea2a9b4e4a8154a028e2395d96509c9997 else 0x25087c3737d29eb6d8476e13300c4e51702e7d26002c7aab853e24f3fa4d9c65ac3737d29e16d1655040955ddd6cf01e640552a94a8f90934fe96a713e24fd2b0ec9c9f1e05c209e924885298a9b9d7c6020f12e1529e0d6dd4c515b9e7a71968fe93737c374bb2aac9c65aa9250b42b2cdf4aa54f97b5b6c38040200d01df26e38fc139f599725a0a62a6ee2508733881cdf0dd2e6f99132931ea88e1180e0bde0e188a0f12e1529e0d5c9665d00ebbc92214a62a737c374b008464ea94a8f918544b5e60fd2b0ece1485a805b2aace3cfe9367196b0dcdf4ab2aac9c65aa9250b42b2cdf4aa54f97b5b6c38040940d075f26e38fc139f008464ea94a8f918544b5e60fd2b0ece1665c968298a9bb89421cce20737c374baf66f522945aa9ba86caab38f9aa753e0fe93671969665c83b5a2ee3388125087c3737d29665c968298a9bb89421cce20737c374b76d50588a62a6eb398d4338cfc9b0dd2c141145c21492b9d7983e1512f0ed2b37785b45954102557775b3c07990154aa52a3e424d3fa5a9c4f893f4ac3b2776d50588a62a6eb398d4338cfc9b0dd2c30009d984c32dd694a8eacb2b0ed2b37198e45c8835989421cce206ef17cbd20892214a62a5327a93a00b9112e1529e0dcdf0dd2d665c968298a9bb89421cce20737c374baf8804eaca132a3abaa1b339161e0712e0f86a0d8a164559dc7837f20c8c20496ceb4fc5e1d91d3a88c4c9325882e6dde18781c4b83e1a8362859156771e0bfc832308125b3ad3f17a01146e6d171eb5aa2b1b3f9e8b58c9ce6293e5a9c5950f9924977386a0f8544bc634acdde16d1655040955ddd6cf6ce65bf52aaea8f909367396a7198a4fd3b18ce9dc54964b46a5dfc9421c9620739c5f4f771525911a406ff2508725881ce717d3ecaab2cfac6a4aa67296f28d262e3c9e770b080940413c187c5c6dc706df07827c14270451608221492b9d805f09d5d60f8544b71c1970d4fdecf1aa2b1b3f08d2728b2aacb3aafa92a79ca5bcd3498b8f079d7dc200801038059f17136cc1b7ab2aacb3eb1a92a99ca5bcd3498b8f279dc2c20080104f061f171b71c1b7c9ca6693d1b9707827ef83ac363411536453128884e2df6115b1772187e18b9c3ab52ef6115b8f96947547551425af2187e1863a018257b64266976bab02d41d480324e9e439fdc6b3a26bfb3d1550d4ce7a5d8f6659c51b224878a883b54141140ac1d39126e0172e7c886b0d63d2391c1cc7f26cb5b9dfc2d98e806085e9889111190e96b6404020160e390e676c60d2d0b50d8e41813eb702235b60db31ce58de3a43a8742530ae3205f90b8239fe4372ace89afecf455435339e9763d9967146c8921e2a20ee10504574b4c4e449ca05cb9f22218aa8f48e470731fc9b2d6e785a0e63a018217a6225b93aadac34d6f1cc05838e43) else (if j<6 then 0xb90e7f7172dac77df11120c84b4e5593958d6e1207d1e62a1d7003d51632af78f51cd705eb9f796b045939f196dbe739b87cb4e4e4495b949561445c23d4705ea26e7806095ed90e439fdc5940f6a66e2b2719f1739bed3924895445396e561499fd138b27bc757f63a098079edcb906503da89beab5f1719f26e34e492255256e53970511309b22c9ff1d6397f6417be3f71e7caa21a892f9161b8591dcb8b8e0e858c07fdf65fcb9a9ab2a8a4ed39404a94e10f68e7b87268ae17873b208e280af25ee77e8b18058e289825da8dab640a47435b81e56928e3f69e5523899d19fd135f5894c1469b31d8357f63a01acaa696e4eab6a2d3db87c5bee7370e2dac116a67cab2739be719f1d393912570561495396ea251617a3db9e098057f63b72e7b8f1b0b34e4921248222ca82d2e77f4b712e0f8660a8813f0e53d6bf7eaa2b4a7ac2ceb48c546c2cd39248492088b2a0b4b9dfd2dc4b83e1982a204fc394f5afbf8d0368ff4333ad2315721ba561497b971735bddcb906dd45b0a9ee7e4f97e719666892f39c5748af29d9a24b95e60b0e9fc5748a92507b5b6ce9495616e539705138fdc79f6b99d5012a7b8526c19eda3886dd45b0a9ee7e4f97e719666892f39c57487895da91c8b2dd4665e770b390f1600995a4a16e07abb956c199eec354c323476da78fe51a76593b49dec139aa66363e15b7516c2a7b9f93e5f9c6599a24bce715d2255aedbba8de8b2a51af29de3e5e99e4f9c6599a24b575e2581d7bb492214b42a339c57487895d941c29c9b67b5ba723390f160539445c14956267978b2aeeec320e81c87ce7f90dc84705d70511cd565ee6df71e7dbd52a56a8f9092e689667197e4fd1f2ace9ae675404a9ee149b268368e21b7516d1a979f93e629c65a9ce4dce717d3eac02c310ced0a98d2382d3ca0010082f0ae34b61084c1854b8dcc810a37b748db71bedd46655a4a1c909dd667369e55bb52a9ba339093d049c50392a3fce712d11685d1db2a4bcbb8691bc8139f31d3f0f59de4bbc872074f2cc7e4e485124a92f0821b6e761e078560d2fe0f7f964558377737f204e720c6fd3f38c45685d1db2a4bcbb8691bc8139f31d3f0f59de4bbc872074f59de4bc4872074f39850cc07076b3d1a468cc57359eef1a692cc55558f8018688b920661b804a99fe225a9374f879e5cf4e1186e618c5cd4ce2886ef198e45c8835989421cce206ef17cbd20892214a62a5327a93a00b9112e1529e0dcdf0dd2e6f99132931ea88e1180e0bde0e188a0f12e1529e0d5c9665d00ebbc92214a62a737c374bb2aac9c65aa9250b42b2cdf4aa54f97b5b6c38040940d075f26e38fc139fb2aac9c65aa9250b42b2cdf4aa54f97b5b6c38040204101df26e38fc139faf66f522945aa9ba86caab38f9aa753e0fe93671969665c83b5a2ee33881 else 0x6b99d5012a7b8526c9a0da38866929b46a5e5a4f98a7196a7393739c5f4f6b99d5012a7b8526c9a0da3886dd45b46a5e7e4f98a7196a7393739c5f4f6b99d5012a7b8526c9a0da3886dd45b46a5e7e4f98a7196a7393739c5f4f87e18470b98f5f67fd7b302e67908a2e0591b89e2fa66976bab033c16871324e8e239fd9e7299a4f46e5c1e09fbe0eb0d8d0454d914c4a22138ca58456c5dc861f862e70ead4bbdd46655a4a1c909dd667369e55bb52a9ba3390905044790392a3fccb12d11d46655a4a1c909dd667369e55bb52a9ba339093d049c50392a3fce712d11e25ca5079e72675ae665d4ce5685d0434a8154a0289aa75aeec1bb85a1a8c435788e576538c649bc75af4901d8d7312ef2ec5d1cc8e280af25ec96951d45f5379dc275199e2b69e55d46655a4a1c909dd667369e55bb52a9ba339093d049c50392a3fce712d11ce6f958525f35c5c96ef70e41b9516b5aa39d9367396a7198a4fd3b18ceabe2013ab284ca8eaea86cce458781c4b83e1a8362859156771e0dfc832308125b3ad3f17876474ea231324c9620b8937661e0712e0f86a0d8a164559dc782ff20c8c20496ceb4fc5df26e170511cf565ee6df6fe75bf52a94a3b8b935209691e91641d3b10cc5ae675404a9ee149b268368e21b7516d1a979d93e629c65a9ce4dce717d3dd46655a4a1c909dd667369e55bb52a9ba338b93d049c50392a3fce712d1139126b25c2a6561495396ed3dac115f2739be719f1a25161563db9e098057f63b72e7b8f6b045a99f2ac9ce6f9c67c74e4e4495c1585254e5ba8945a838f6e7826015fd8edcb9ee3c862aa3d2391c1cc7f278beb9e168398e806095ed9096e4eab6b0d3dbe739b87c)))
def mo511Item (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x2002c1b208058361840b06c300160cd2402c1968c058327180b061030160c10702c1540c05828e900b051908160a32002c14618058284840b03a928160752402c0ca40058194300b03266816064cc02c0c088058113940b022720160446502c0164a05802c4c0b0058901600b050241cabe04839578090729a0120e3b40241c74804838d78090719a0120e32d0241c64204838c3409071860120e29f0241c53c04836cb40906d960120db210241b64004833b9009067620120cd4602419a680483349009065da0120cb460241965804832a1c09065430120c6de0241870c04828e9009051908120a30d02413dde04827bb80904e8b01209b960241362c0481d4900903290812045160240872c04803b8406071da80c0e3b40181c74803038cd0060719680c0e3240181c64203038a78060711700c0e12e0181b72603036e140606d9a00c0db240181b62603036c4806065a380c0cb460181966803032a1c060654300c0c3870181870c03030c1c060618300c0ab060181474803028c90060519080c0a3200181442e03028858060508b80c0a1160181362e03026c580604d1200c099240181162c0301ac1c060358300c043170180862c02839990050730f80a0e61e0141cabe02839578050727780a0e4ee0141c8de028391b8050711700a0cf2401419dc802833b14050676200a0ce0701419c0c0283351c05066a300a0c71f01418e3c02831b78050632300a0a73401414de802829b4c050536900a0a67401414cc80282935c050526b00a0a457014148ac028288580504f9700a09eef01413ddc028279b80503b9a00a077250140ee480281dbd00503b7200a076d30140ed8a0281d9d0050378f00a06ede0140dc8c02819cb4050339200a067210140ce4002819c34050338600a066f40140cdda02819bb0050337080a066e00140ae3c02811cb8050237700a0446401404ddc02803c8005007760060e61f00c1cc3c01838ed403071da0060e3a500c1c6e801838cd4030719a0060e32d00c1c64201838c8003071868060e30c00c1c56801838ab403071468060e28c00c1c45c018387bc03070f70060e12e00c1c0dc018381b403070308060de4b00c1bc16018378280306dc98060db7400c1b6a601836d480306da50060db2d00c1b65801836c840306d900060daad00c1b55801836a840306d500060da9300c1b524018361840306c300060cbb400c14cea018299d0030531a0060a32100c1464001828a8403051500060a29300c1442e0182885803050eb0060a05600c13c5e018278b80304dab80609b5600c1352c01822d580303b3a0060660d00c0cc180181814c030058980600aa000c0152601039b2c02072370040e12e00818dbe01031b78020537a8040a6f4008148ac010284580204f7780409eee0080cdea01019bb40203370804026ef else 0xc71f05818e3c0b03191c160632302c0c3070581860c0b02b918160539a02c0a6f405814da60b029b48160533a02c0a664058146480b027cbc1604f9702c09eee0580ee680b01dc901603b6982c076c50580de3c0b01b91c160372302c067340580cda60b011cb8160139702c00e650481ca6a090394d012072770240e46f0481c8dc09038ed412071da0240e3350481c66809038cb412071868240e22f0481c45c090384b81206f858240df0a0481bcd80903792c1206e9a0240dd130481ba24090374281206dda8240db930481b71609036e101206d968240db2c04819d96090334d4120669a0240cbb404818dbe09031b78120578f8240ad1e04814e6a09029cd0120537a8240a6f404814da609029b48120533a8240a674048149ae09029358120522b8240a4560481442e09028858120508b8240a11604813e5e09027cb81204f7782409eee04813cde090279b81204e8b82409d160481372e09026e581204d8b02408d160481172e0901dcd41203b9a024076f50480eda60901d9d012033968240670d0480ce1809019bd41203370824066d30480cce8090199b412033360240664d0480ca400901943412032860240472f04808e5c09011bbc12023370240451704808a2c09010e5c12021cb024026ef04804ddc090099b8120079682400f2104801dc2090039b4100729a8200e5340401c9de080393b810072378200e46e0401c61a080384b810070370200dd340401ba26080374481006d890200db050401b608080334d010066920200a4d7040149ac08029158100502b02009d1704013a2c080234581003a920200605204008a2e08011458100227201e0e6cb03c1cd940783952c0f0729a81e0e53403c1c9de078393b80f0723701e0e37503c1c6e8078387bc0f070f701e0df0b03c1be140783782c0f06e9a01e0dd1303c1ba240783742c0f06da981e0cecb03c19c0e078338180f066a581e0cd4603c19a8a078334d00f0539a81e0a73403c14dea07829b4c0f0536901e0a63403c14ae80782954c0f052a901e0a54b03c149ae078293580f0522b01e0a1d703c143ac07827cbc0f04f9701e09e2f03c13c5c078275b80f04e8b81e09d1603c136ae07826d580f0468b01e0773403c0eda60781db480f03aa981e0755203c0ce6807819cb40f0338681e0670c03c0cdda07819bb00f0337081e066c503c0cc6a078198b40f032b681e0656c03c0caa6078195480f032a201e0652103c0c69807811cb80f0228b81e0451603c04e5c078098bc0f0079681e00f2103c01e4007803b840b072778160e3a402c1c6be05838d780b071908160e30d02c1c618058388900b070ef0160e12e02c1c242058384340b070860160e06d02c1c0c2058374480b06dc28160db2d02c1b64805836c840b06d828160da2402c1b25a058364b00b06c908160d9) else (if j<3 then 0x79e62578f3cc48f1e78d91e3ceeb23c79a62478f346caf1e68d91e377312bc6ee36578ddc6c8f1ba9895e3753123c6ea36578dd46c8f1b37895e366f123c689e2578b38d8ebd7274bd7ae4e972efca4f55df949e8bbf184d577dd23aacbba4d3597749a4b2edc84d65db9092c5b611358b6c2249d6594b53acb29626f3a6d74de74dac9bce955926e6d45a4dcda8a48d8150a91b02a10c9df185993be30a3277c51664ef8a28c9de585993bcb0a327745145d537c4cbaa6f8916cce6cd2d99cd985b339534b6672a6160ce44d2c19c89851e77814a3cef020e1cc31f1c39863c37f338946fe67120df4cb651be996c837d1cd9469db9a28d3b62841a43954834858a9065de7028cbbce0413f19d8c25b024481a073320340e61f0681cc3c0d0395781a071d28340e3a40681c6be0d038d781a071908340e30d0681c53c0d037c281a06f368340de6c0681bcca0d0379901a06f258340de450681bc880d03744c1a06e858340dba40681b7160d036e141a06dc20340db210681b60a0d033c941a067920340cee406819d8a0d03381c1a067030340cd4706819a8c0d0334901a065a38340cb460681950e0d032a181a0638f8340c71e06818dbe0d03191c1a063230340c51f06818a3c0d030e1c1a061c30340c30706815c8e0d02b9181a055c30340a664068147480d028c841a05190034077250680ee480d01db141a03a92834075240680de3e0d01bc781a0372383406e460680da3e0d01b4781a035c383406b860680ce480d019c841a033868340670c0680cdc20d0199341a03290034065130680ca1a0d015c781a0128b83400f2d06801e420d003c801a0077083400e6506801a420d002c941a0058983400b120680160a0d002c10170736582e0e6ca05c1ccc80b83987c170730f02e0e55f05c1c8960b839128170711202e0e06105c1c0be0b837c2c1706f3682e0de6405c1bc960b8379141706f2202e0dccb05c1b0c00b833c90170677682e0cee505c19dc80b833b2c170676282e0cec405c19c0e0b83381817066a302e0cce405c198ca0b833190170662582e0cc4505c190c80b83211c170642302e0c71f05c18e3c0b83191c170632302e0c4de05c15c8c0b829990170526b02e0a46105c148a60b8291481703b9202e076c505c0e88a0b81bc7c170378f02e06e4705c0dc8c0b819c84170338682e0670c05c0cdc80b819b84170336282e0646405c0c8a60b819148170322282e0644405c0c0ca0b81814c170302902e0604505c0c0880b811394170079682e00f2105c01dc20b039b2c160736502c0e6640581cc3e0b03957c16072af02c0e3240581c53c0b037c2c1606f8502c0de640581bc8a0b0379101606d8982c0db1205819e4a0b033c90160677202c0cec505819d880b03381c160670302c0cd4705819a8c0b032a1c160654302c0 else 0xd5e74e2fabce9c5b579d36beaf3a6d6d5e74c2fabce985b578d36beaf1a6d6d5e34aadaba29c5f574532beae8a656d4b6ccc1a83394b750672966973e52fd2e7ca5da5cf8ebb4b9f1b7e973e36ed2e7c55fa5cf8abb4b8f1576968e3afd2d1c75da5938cbb4b27157e964e2aed199c75ba3338eb345dd39068bba713d1774e25a2edd94f45dbb295f549f17bea93e2d7d523b5ef067276de0ce4ecbc19c8db783391b2f066e36de0cdc6cbc03c8d975d393d6eba727a5d74e475bae9c8e975d387d6eba70fa5d74dc74bae9b0e975d328d6eba651a5d6ee235baddc46975bb28d6eb7651a5d6ce474bad9c26b75b384d2eb6703add6ce074b999c3d967ec3586cb9f197d973e32eb2e7c55d62f19b36c5e336658bc654db178ca992d6d94b65a66f29cb4cde529599ccc32b33998256653294ac1dd6093f19e0f27e33c1a4fc6763c9f8cec693f19a0f27e3341a4fc666349f5cec793eb9d8d27b73c1e4f6e78349edcd0793db9a0d25b0244e4b6048948cca3a19199474122ef3cb245de782c8bbcf049168cd9921e3997e43c732f4878e39f90f1c73d21e38c7e43c718f4878e21e90dbccbf21b7997a436f1cfc86de39e90dbc63d21ab8c7e17db23642f9a07582d8122501e76a9603c718fc078e31e80f1c23f01e3847a036f18f406ce2a57dd14aaefb339885f6673103eccdd607d83cac8fb079585f60f2b03ec1dd617d83bac0f3328d85e6651b03c))
def mo511Row9 := packet 0x1800000a84300300000a2984000000006841
def mo511Row10 := packet 0x58000003a90c15a000010a4305380000b390414800000a84304a000002a10c00000000000004700001c02041100000a4081042800002a10c10400000a843039000003298c0de00000a843036000002a10c09e00000a8430248000188204086000008621020000002a10c07a00000a84301d000002a10c05400000ea43013800003a90c04200000a8e100d800029498400000000000000a80000a2984024000012ca3007800003298c12e0006e84a203a80032a09880be000ca826202900018a128805a000c06282
def mo511Row11 := packet 0x1a7800020980469200002c60119a000020980464200002c60118600000b18045f800000e82317c800003a08c5e600004c82116f00002098045b000002c60116a800003a90c58a00000ea43000000000000057e0000920a115c800039028455200000ea4314c800003a90c512000010c63143000003b18c50600000ea43140000003a90c4c600000ea4312e80002082844ae00000a821123800003a90c46e00000ea4311a000003a90c42e00000ca63108800021028441600000a841104000003298c40a00000ca63101000003298c3f80001068210fb000051a0843e00000e68210f6800004318c3ce00014e621000000000000000000000000000000000000000000000000000f2000004318c3c200000ca6300000000000003b60000c60a10ec000003a98c3aa00000ca630e9000003298c39e00000ea630e6000004180c38c00002a6010e1800003290c38000000ca430de800003290c0000000000000db80000b290433400000ca430cb800003290c32800000ea430c8800003290c31c00000ca430c5800003210c30a0000c24010bf80003090042a80000c240109f80000b100427200002cb21099800030810423200002d081089800010308420600000c823080000003208c1f4000050ec107a00000a14041ae00000c823059800003208c6c8000280ae81aa8001a0b39067400e682c04193800183a908624008e60a2417f8002920b885c800e682c041640002429388558000e2c4a214e0004c293085180004ec28213980013b0a084cc00082a4e21250002092b0847400122a4c21138002820b0843400084a6c200000000000003540010284a20ce80040a12882b400004a3020a2802881399023e4ce9230b708300010320881ce0004ea26206d000402988816c0010c26a200000000000000000000000000b3803010ba18186010c68eb6
def mo511Row12 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x8002030c093e8000e42d024f4000401baa53b8001006ea94e8000401baa538600008c3224db0002030c093520008430c24ce800409baa531e000c26af44c1000280ba092ea000a0e2824b4000280ba092b6000a02e824a7000280ba09282000a02e8249a00031a0b8924e001042e8248d000280a30921a000a0c28248000029b0a091e6000a02c82473000280b2091b2000a02c82466000390b20917e000e2c702459000030ba0914600a4826c444b000030ba091120000870c24268003020c1d050000286ec240e0003020c1d020000c083074020003020c1cfee000e483023f58003020c1cfb80102c04a43db8002924088f54000e429023cf0003020c1cf24000c083073c28000320c08ef20000c83073b60000320c08ebe0000c83023a9000030a408e8a000e4308239c000300a388e500000c83023868003020c1cdb600a482c043670002931c08d3e0082a506434300040b9b08cb200144c6e20000000000000c52000a4c6e20000000000000c3400a40ce643068004131b88c00001046ce22f98002931b88bcc000a4ce622ec80012b1b88b980000870c22de0002931b88b46000a46ce22b480020b9c880000000000002a200020c3188a5c00122a6e20000000000000a3600008c3022870000230c08a020004e30c227a00030b9a889ce0004e30c226d0000230c0899a00008c30226000002b0c089660000ac30224d00002b0c0891a000e42d0223400002a30888b600080e6a2227800138a32400000000000020d80001a938881c00060ea4220080018293887e800006e4a21f3800183a9080000000000001ec0018128b1076600060e4a21c480030a93886f800060a4e200000000000006de00060e4a2862829300a3960ca00ae4c28582403902b0a16060002c8e70680c000b239c19ff60e6a0c8257f180439b2099f96010e682c67d702941b0a15f2c002c8e7067b603902b0a15e74002c8e706781839a832095d88010e682c6746802b930a15cc60e4a02c85723039280b215c520a6e48c25708802b9a0b19bbe002c6eb066e1021429b095b54002c6eb066c9000b1bac180000000000006bb12c3098229ab20c2604ea569ea901c20b29a40082064ea56820183092bc59d0a506082ca6658208193a94000000000000657928309c22992402c60ae4563a80b1813a958b0060c2ae4561d8180a3929583ee42c0906a601031a92389578200d0682e65c4a941820b296d8082064ea55a781830ab9155c00c0a4e2855290492030bed436084e0a30541a8040a1bb18f88008e2c70637502920b4994d5c0a4832e6533480a312b994c72084632ea500000000000000000000000000000000000000aec010c682e600000000000008ea00ae682c6214003a91831878001006c4a61cb001a8a31140000000000000000000000000000000000000 else 0x8710000280a061640000a02818560000280a0614c00002e08185000003882861340000e20c184a000029030611c00010628184400002012861040000e40a157e800028208559a0000a08215638000318a055680000e2a01557000038a8055500000c628155100002920855380000a482154b0000318a0510600000c82143e80000320850ee000082c0e43880000320850d60000a482143280003930050be00000c82142c8000032084e6a000010c63392800004318ce3e00000c82138c8000032084e14000010c63383800004318cd96000010c6334c8000290304d2600000ca41333000004318ccac000010c6331b000004318cb92000010c632db0000290304b6000000ca412d0000004318cb3a000010c632cd000004318cb280001068212c7000041a084ac60001068212ae80001c20840000000000002ab8000418a040000000000002a8800020c184a82000010c630000000000000a760001060c1295800004318ca50000010c63256800003388494e00000ce21226000004318c0000000000002230000143004886000010c63220000004318e1d0000a02e8285c000280ba09f12000a0e2827af8004120b89ea400106e8227968004120b89e40000a0e28277b0002838a09dd2000a0e28276e0002923889d6e000a0e2827550001423889d00000a0e2827020003038a09bee000c0e28200000000000017e60082a46c45f300020c31897b2000830c625da00020c318974a004f062845a1000280ba0966a000a02e82594000300ba096360008106c25880001283421606000a0e822569800283a089574000a106c2544800201ba894f800080c302537800200b48948a00080d02251c0002030c0941c000802d2250)
def mo511Row13 := packet 0x2a18010c6e28600000000000029e8010c6e286a6e00431b8a18000000000000a5f812a01c314000000000000a519b0b9202aa91600d06e28600000000000028e600d06e286a2b038a81c31687200a4f06c5a1080341b8a1a812010c682e69f6041300ba1679e104c02e859db80341a0b9a73e010c6e2869c380341b8a1a6d4028a4d0659a6820a9341966600a42870c50000000000002628820c6a50a97b820a91c3165b4082e4c705000000000000257a082e506c500000000000025400a482d06500000000000025060a48306c59338390a31c46494082a4d0650000000000000000000000000916829030ba164200a40c2e858fc00431b8a1a3c0008e306c68e400431b8a1a3560e2a10c650000000000002326010c6e2868bb04182b8a162b20e2a06d058a080341a0b9a252010c6e286000000000000221a028e50c1087a80341b8a1800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def mo511Rows : Nat → Nat → Nat
  | 9 => fun i => packedAt mo511Row9 (i*50) 50
  | 10 => fun i => packedAt mo511Row10 (i*50) 50
  | 11 => fun i => packedAt mo511Row11 (i*50) 50
  | 12 => fun i => packedAt mo511Row12 (i*50) 50
  | 13 => fun i => packedAt mo511Row13 (i*50) 50
  | _ => fun _ => 0
def mo511Leaf : Tier.Leaves := (mo511Rows,entryWord mo511Palette 10 mo511Entry mo511Item)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511G : Chart mo511 mo507K := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511E : ∀ c ∈ mo511Q, TestedCube.geometry mo511.mask (targetOf mo511) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := sparseAll (cs:=mo511S) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511T : TreeChecked mo511Q mo511F mo511Leaf mo511 := by
  intro k hk
  change k ≤ 15 at hk
  interval_cases k
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 9) 0 3 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 10) 0 32 3 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 11) 0 109 5 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 12) 0 264 6 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 13) 0 75 4 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 14) 0 8 1 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
  · have q : pieces (treeCheck mo511Q mo511F mo511Leaf mo511 15) 0 1 0 := by
      simp only [pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact fromZero q i hi
theorem mo511All : forestCases mo511 := allTree mo511 (by decide) (boundsBefore mo507K) (before_sound mo507K mo507V) mo511G mo511E mo511T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511R : Impossible false (targetOf mo511) 15 (vars 511).toFinset := fromRoot (g:=mo511) (mo511All 15 (by decide)) (idx:=0) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem finalMono : Impossible false graph 15 inputs.toFinset := by
  have tg : targetOf mo511 = graph := by decide +kernel
  have vs : vars 511 = inputs := by decide +kernel
  rw [←tg,←vs]
  exact mo511R

end PEqualNP.Outside.L_meta_11028

theorem PEqualNP.Outside.L_meta_11028 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  apply PEqualNP.Outside.L_meta_11028.finishWhenMonotone
  exact PEqualNP.Outside.L_meta_11028.finalMono
