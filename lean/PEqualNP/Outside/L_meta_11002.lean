import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_11002_aux
-- Checked eight-vertex certificate from L_meta_8403. Long zero runs in its
-- packed natural-number tables are written as shifts.
def joinBits (high width low : Nat) : Nat := (high <<< width) + low

namespace Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
end Basis1868


namespace Conflict1868
open Basis1868

abbrev I := Fin 414
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def D (p n : I) (a : Sig) : Prop := P a p ≠ N a n
def op (d x y : Bool) : Bool := if d then x || y else x && y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  by_contra! hn
  apply hd
  unfold P N
  rw [bop,bop]
  exact congrArg₂ (op d) (not_ne_iff.mp hn.1) (not_ne_iff.mp hn.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_neg {p n a} (hv : Valid a) : D p n (neg a) ↔ D p n a := by
  unfold D P N
  rw [bit_neg _ _ hv,bit_neg _ _ hv]
  cases bit true p a <;> cases bit false n a <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pair_sep {k t S} (hl : Live k t S) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,P,N,bit,target,testBit_top,p.isLt]
  | unary ha _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨_, Finset.mem_insert_self _ _, (d_neg ha.1).mp h⟩
    · exact ⟨_, Finset.mem_insert_of_mem hc, h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_unique_keep {p n a c U} (h : Unique p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Unique p n (insert (neg a) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · exact (hna (h _ (Finset.mem_insert_self _ _) ((d_neg hv).mp hd)).symm).elim
  · exact h _ (Finset.mem_insert_of_mem hu) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_keep {p n a c U} (h : Mark p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Mark p n (insert (neg a) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,neg_unique_keep hm hna hv⟩,q,neg_unique_keep hq hna hv⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_move {p n a U} (h : Mark p n (insert a U) a)
    (ha : a ∉ U) (hv : Valid a) : Mark p n (insert (neg a) U) (neg a) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a U := Finset.subset_insert _ _
  exact ⟨(d_neg hv).mpr hd,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mix : ∀ (d ap an bp bn al ar : Bool), ap ≠ an →
    op d ap bp ≠ op d al bp → op d ar bn ≠ op d an bn →
    bp = bn ∧ op d ap bp ≠ op d an bn := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U))
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : P b p = N b m := not_ne_iff.mp (fun h => hab (hm _ hb h).symm)
  have bq : P b q = N b n := not_ne_iff.mp (fun h => hab (hq _ hb h).symm)
  have zm := unique_diff tail (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  change bit true p (bin d a b) ≠ bit false m (bin d a b) at zm
  change bit true q (bin d a b) ≠ bit false n (bin d a b) at zq
  rw [bop,bop] at zm zq
  change op d (P a p) (P b p) ≠ op d (N a m) (N b m) at zm
  change op d (P a q) (P b q) ≠ op d (N a n) (N b n) at zq
  rw [← bm] at zm
  rw [bq] at zq
  have hh := mix _ _ _ _ _ _ _ hd zm zq
  refine ⟨fun h => h hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unary_col {k U a} (hv : Valid a) (fresh : neg a ∉ insert a U)
    (col : Colored (insert (neg a) U) k) :
    ∃ l, Colored (insert a U) l ∧ l + (insert a U).card ≤ k + (insert (neg a) U).card := by
  let R := ({a} : Finset Sig) ∩ U
  let f (x : Sig) := if x = a then neg a else x
  have mem (x) (hx : x ∈ insert a U) (_ : x ∉ R) : f x ∈ insert (neg a) U := by
    by_cases e : x = a
    · simp [f,e]
    · simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left e)
  have keep (x p n) (hxr : x ∉ R) (mx : Mark p n (insert a U) x) :
      Mark p n (insert (neg a) U) (f x) := by
    by_cases e : x = a
    · subst x
      have ha : a ∉ U := by simpa [R] using hxr
      simpa [f] using neg_mark_move mx ha hv
    · simpa [f,e] using neg_mark_keep mx e hv
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy hxr hyr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n hxr mx,keep y p n hyr my⟩
    by_cases ex : x = a <;> by_cases ey : y = a
    · exact (hxy (ex.trans ey.symm)).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : neg a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> simp [R,ha,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
theorem live_colored {k t S} (l : Live k t S) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary ha hf _ ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := unary_col ha.1 hf hk
    exact ⟨u,hu,by omega⟩
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail hk
    exact ⟨u,hu,by omega⟩

end Conflict1868

namespace Grid1868
open Basis1868

abbrev Ix := Fin 256
def coord (side : Bool) (i : Nat) := if side then i / 16 * 16 else i % 16
def hop (n mask x : Nat) : Nat := (x ||| ((x <<< n) &&& (mask <<< n))) ||| ((x >>> n) &&& mask)
def safe (s : Bool) (n mask : Nat) : Prop :=
  ∀ i : Ix, (((mask <<< n).testBit i.val = true → n ≤ i.val ∧ coord s (i.val-n) = coord s i.val) ∧
    (mask.testBit i.val = true → i.val+n < 256 ∧ coord s (i.val+n) = coord s i.val))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
instance (s n m) : Decidable (safe s n m) := by unfold safe; infer_instance

def m4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def m5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def m6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m7 : Nat := 0xffffffffffffffffffffffffffffffff
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 16 m4 x))))
end Grid1868

namespace Check1868
open Basis1868
open Grid1868 Conflict1868

abbrev Signs := List (Sig × Nat)

end Check1868


namespace ColorSearch1868
open Basis1868
open Conflict1868 Check1868

def paint (n : Nat) : Signs → (Nat → Nat) → Bool
  | [], _ => true
  | x::xs, bins =>
    (List.range n).any fun i => ((bins i &&& x.2) == 0) &&
      paint n xs (fun j => if i=j then bins j ||| x.2 else bins j)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma paint_ok {n xs} (bins : Nat → Nat) (f : Sig → Nat) (nd : (xs.map Prod.fst).Nodup)
    (bd : ∀ x ∈ xs, f x.1 < n) (ok : ∀ x ∈ xs, bins (f x.1) &&& x.2 = 0)
    (sep : ∀ x ∈ xs, ∀ y ∈ xs, x.1 ≠ y.1 → f x.1 = f y.1 → x.2 &&& y.2 = 0) :
    paint n xs bins = true := by
  induction xs generalizing bins with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hn,hnd⟩ := List.nodup_cons.mp nd
    apply List.any_eq_true.mpr
    refine ⟨f x.1,List.mem_range.mpr (bd _ (by simp)),Bool.and_eq_true_iff.mpr ⟨by
      simp only [beq_iff_eq]; exact ok _ (by simp),?_⟩⟩
    apply ih _ hnd (fun a ha => bd a (List.mem_cons_of_mem _ ha)) _ (fun a ha b hb =>
      sep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    intro y hy
    have hy' := List.mem_cons_of_mem x hy
    by_cases e : f x.1 = f y.1
    · have ne : x.1 ≠ y.1 := fun eq => hn (List.mem_map.mpr ⟨y,hy,eq.symm⟩)
      simp [e,Nat.and_or_distrib_right,ok y hy',sep x (List.mem_cons_self ..) y hy' ne e]
    · simpa [e] using ok y hy'

end ColorSearch1868

namespace Free1868
open Basis1868
open Conflict1868

def flip (s : Bool) (a : Sig) := if s then neg a else a
def sign (a : Sig) := bit true 0 a
def can (a : Sig) := flip (sign a) a

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg2 (a : Sig) : neg (neg a) = a := by
  obtain ⟨u,v⟩ := a
  simp [neg,bnot,Nat.xor_assoc]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip2 (s a) : flip s (flip s a) = a := by cases s <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipFalse (a) : flip false a = a := rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma vf {a} (s) (h : Valid a) : Valid (flip s a) := by cases s <;> first | exact h | exact valid_neg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sign_neg {a} (h : Valid a) : sign (neg a) = !sign a := bit_neg true 0 h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_neg {a} (v : Valid a) : can (neg a) = can a := by
  unfold can
  rw [sign_neg v]
  cases sign a <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_flip {a} (s) (v : Valid a) : can (flip s a) = can a := by
  cases s with
  | false => rfl
  | true => exact can_neg v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can2 {a} (v : Valid a) : can (can a) = can a := can_flip _ v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma recover (a) : flip (sign a) (can a) = a := flip2 _ _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_zero : can zero = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_one : can one = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipProper (s) {a} (ha : proper a) : proper (flip s a) := by
  cases s
  · exact ha
  · refine ⟨valid_neg ha.1,?_,?_⟩
    · intro h
      exact ha.2.2 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.1))
    · intro h
      exact ha.2.1 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.2))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canProper {a} (h : proper a) : proper (can a) := flipProper _ h

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sameClass {a b} (h : can a = can b) : a = b ∨ a = neg b := by
  have ha := recover a
  rw [h] at ha
  unfold can at ha
  cases ea : sign a <;> cases eb : sign b <;> simp [ea,eb,flip,neg2] at ha <;> aesop

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_neg_self (d : Bool) {a} (h : Valid a) :
    bin d a (neg a) = (if d then one else zero) := by
  have op {x : Nat} (hx : Valid1 x) :
      x &&& bnot x = 0 ∧ x ||| bnot x = top := by
    constructor <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      simp only [Nat.testBit_and,Nat.testBit_or,testBit_bnot hx,testBit_top,Nat.zero_testBit] <;>
      by_cases hj : j < 414
    all_goals first | (rw [hx j (by omega)] <;> simp [hj]) | (cases x.testBit j <;> simp [hj])
  cases d
  · exact Prod.ext (op h.1).1 (op h.2).1
  · exact Prod.ext (op h.1).2 (op h.2).2

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma distinctClass {d a b} (ha : proper a) (hab : a ≠ b) (hg : proper (bin d a b)) :
    can a ≠ can b := by
  intro h
  rcases sameClass h with e | e
  · exact hab e
  · have eb : b = neg a := by rw [e,neg2]
    rw [eb,bin_neg_self _ ha.1] at hg
    cases d
    · exact hg.2.1 rfl
    · exact hg.2.2 rfl

def blend (d s t : Bool) (a b : Sig) := can (bin d (flip s a) (flip t b))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive BL : Nat → Finset Sig → Prop where
  | stop : BL 0 {can target}
  | step {k U a b d s t} (ha : proper a) (hb : proper b)
      (ac : can a = a) (bc : can b = b) (hab : a ≠ b)
      (fresh : blend d s t a b ∉ insert a (insert b U))
      (tail : BL k (insert (blend d s t a b) U)) : BL (k+1) (insert a (insert b U))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma compress {k t S} (l : Live k t S) :
    ∃ j T, j+t ≤ k ∧ BL j T ∧ T ⊆ S.image can := by
  induction l with
  | stop => exact ⟨0,_,by omega,BL.stop,by simp⟩
  | @unary k t U a ha _ _ ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    refine ⟨j,T,by omega,h,?_⟩
    simpa only [Finset.image_insert,can_neg ha.1] using sub
  | @binary k t U a b d ha hb hab _ tail ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    let g := bin d a b
    let z := can g
    let w := insert (can a) (insert (can b) (U.image can))
    have hsource : (insert a (insert b U)).image can = w := by simp [w]
    rw [hsource]
    have hs : T ⊆ insert z (U.image can) := by simpa [g,z] using sub
    by_cases need : z ∈ T ∧ z ∉ w
    · have hu : T.erase z ⊆ U.image can := by
        intro c hc
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hc))).resolve_left (Finset.ne_of_mem_erase hc)
      have hp : proper g := live_proper tail _ (Finset.mem_insert_self ..)
      have nz := distinctClass ha hab hp
      have id : blend d (sign a) (sign b) (can a) (can b) = z := by
        simp [blend,recover,z,g]
      have out : BL j (insert (blend d (sign a) (sign b) (can a) (can b)) (T.erase z)) := by
        rw [id,Finset.insert_erase need.1]; exact h
      have fresh : blend d (sign a) (sign b) (can a) (can b) ∉ insert (can a) (insert (can b) (T.erase z)) := by
        rw [id]
        intro zz
        apply need.2
        simp only [Finset.mem_insert] at zz ⊢
        simp only [w,Finset.mem_insert]
        exact zz.imp_right (fun e => e.imp_right (fun h => hu h))
      refine ⟨j+1,_,by omega,BL.step (canProper ha) (canProper hb) (can2 ha.1) (can2 hb.1) nz fresh out,?_⟩
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hu)
    · refine ⟨j,T,by omega,h,?_⟩
      intro c hc
      rcases Finset.mem_insert.mp (hs hc) with rfl | hU
      · exact Classical.byContradiction (fun hn => need ⟨hc,hn⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU)


set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.forms {k S} (l : BL k S) : ∀ a ∈ S, proper a ∧ can a = a := by
  induction l with
  | stop => simpa using And.intro (canProper target_proper) (can2 valid_target)
  | step ha hb ca cb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha,ca⟩,⟨hb,cb⟩,fun a h => ih _ (Finset.mem_insert_of_mem h)⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_ne {a} (hv : Valid a) : neg a ≠ a := by
  intro h
  have eq := sign_neg hv
  rw [h] at eq
  cases e : sign a <;> simp [e] at eq

def Present (n : Nat) (S : Finset Sig) := ∃ t, Live (n+t) t S

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma insertFlip {n a U} (s : Bool) (ha : proper a)
    (hf : s = true → neg a ∉ insert a U) (h : Present n (insert (flip s a) U)) :
    Present n (insert a U) := by
  cases s
  · exact h
  · obtain ⟨t,hl⟩ := h
    exact ⟨t+1,by simpa [Nat.add_assoc] using Live.unary ha (hf rfl) hl⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.expand {j S} (l : BL j S) : Present j S := by
  induction l with
  | stop =>
    have eq : can target = neg target := by decide +kernel
    rw [eq]
    have hf : neg (neg target) ∉ insert (neg target) (∅ : Finset Sig) := by
      rw [neg2]; simp [Ne.symm (neg_ne valid_target)]
    have t : Live 0 0 (insert (neg (neg target)) ∅) := by rw [neg2]; exact Live.stop
    exact ⟨1,Live.unary (flipProper true target_proper) hf t⟩
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    let x := flip s a
    let y := flip t b
    let g := bin d x y
    let z := can g
    change z ∉ insert a (insert b U) at fresh
    change Present k (insert z U) at ih
    have cx : can x = a := (can_flip s ha.1).trans ca
    have cy : can y = b := (can_flip t hb.1).trans cb
    have vg : Valid g := valid_bin (vf _ ha.1) (vf _ hb.1)
    have zu : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have canonU (c) (hc : c ∈ U) : can c = c := (tail.forms c (Finset.mem_insert_of_mem hc)).2
    have gz : proper z := (tail.forms _ (Finset.mem_insert_self ..)).1
    have hg : proper g := recover g ▸ flipProper (sign g) gz
    have go := insertFlip (sign g) hg (by
      intro act h
      rcases Finset.mem_insert.mp h with gg | inu
      · exact neg_ne vg gg
      · have zz : z = neg g := by change flip (sign g) g = _; rw [act]; rfl
        exact zu (zz ▸ inu)) ih
    have xy : x ≠ y := fun eq => ne (cx.symm.trans ((congrArg can eq).trans cy))
    have gfresh : g ∉ insert x (insert y U) := by
      intro h
      rcases Finset.mem_insert.mp h with hh | h
      · have za : z = a := (congrArg can hh).trans cx
        exact fresh (Finset.mem_insert.mpr (Or.inl za))
      rcases Finset.mem_insert.mp h with hh | inu
      · have zb : z = b := (congrArg can hh).trans cy
        exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl zb)))
      · apply zu
        change can g ∈ U
        rwa [canonU g inu]
    obtain ⟨negCount,live⟩ := go
    have go2 : Present (k+1) (insert x (insert y U)) := by
      refine ⟨negCount,?_⟩
      convert Live.binary (flipProper s ha) (flipProper t hb) xy gfresh live using 1 <;> omega
    have nap : neg a ∉ U := by
      intro hh
      have eq := canonU (neg a) hh
      rw [can_neg ha.1,ca] at eq
      exact neg_ne ha.1 eq.symm
    have nbp : neg b ∉ U := by
      intro hh
      have eq := canonU (neg b) hh
      rw [can_neg hb.1,cb] at eq
      exact neg_ne hb.1 eq.symm
    have xa := insertFlip s ha (U := insert y U) (fun _ hh => by
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact neg_ne ha.1 eq
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact ne (ca.symm.trans ((can_neg ha.1).symm.trans ((congrArg can eq).trans cy)))
      · exact nap hh) go2
    rw [Finset.insert_comm] at xa
    rw [Finset.insert_comm]
    apply insertFlip t hb _ xa
    intro act hh
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact neg_ne hb.1 eq
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact ne ((cb.symm.trans ((can_neg hb.1).symm.trans ((congrArg can eq).trans ca))).symm)
    · exact nbp hh

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma freeColors {k S} (h : BL k S) : ∃ n, Colored S n ∧ n+S.card ≤ k+2 := by
  obtain ⟨t,hl⟩ := h.expand
  obtain ⟨n,c,b⟩ := live_colored hl
  exact ⟨n,c,by omega⟩

end Free1868

namespace FreeSearch1868
open Basis1868
open Conflict1868 Check1868 Free1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma negFlip (u : Bool) (a : Sig) : neg (flip u a) = flip (!u) a := by
  cases u <;> simp [PEqualNP.Outside.L_meta_11002_aux.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 414 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 414 <;> simp [e]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipBlend {a b} (ha : Valid a) (hb : Valid b) (d s t : Bool) :
    ∃ u v, blend false u v a b = blend d s t a b := by
  cases d
  · exact ⟨s,t,rfl⟩
  · refine ⟨!s,!t,?_⟩
    unfold blend
    rw [← negFlip,← negFlip,← deM (vf s ha) (vf t hb),can_neg (valid_bin (vf s ha) (vf t hb))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_symm (d s t a b) : blend d s t a b = blend d t s b a := by unfold blend; rw [bin_comm]

def keep (a b : Sig) (u v : Bool) (c : Sig) := (c != a || u) && (c != b || v)
def next (v : List Sig) (a b z : Sig) (l r : Bool) := z :: v.filter (keep a b l r)
def oneB (v : List Sig) (go : List Sig → Bool) (a b : Sig) (s t : Bool) :=
  let z := blend false s t a b
  z != zero && !(v.contains z) &&
  ([false,true].any fun l => [false,true].any fun r => go (next v a b z l r))
def pairB (v : List Sig) (go : List Sig → Bool) (a b : Sig) :=
  [false,true].any fun s => [false,true].any fun t => oneB v go a b s t

def baseTest (v : List Sig) := v == [can target]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tailState {a b z : Sig} {U : Finset Sig} {v : List Sig} (nd : v.Nodup)
    (rep : v.toFinset = insert a (insert b U)) (fresh : z ∉ insert a (insert b U)) :
    let w := next v a b z (decide (a ∈ U)) (decide (b ∈ U))
    w.Nodup ∧ w.toFinset = insert z U := by
  classical
  dsimp only
  have ff : (v.filter (keep a b (decide (a ∈ U)) (decide (b ∈ U)))).toFinset = U := by
    ext c
    simp only [List.mem_toFinset,List.mem_filter,keep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne]
    have mem : c ∈ v ↔ c = a ∨ c = b ∨ c ∈ U := by rw [← List.mem_toFinset,rep]; simp
    rw [mem]
    by_cases ea : c = a <;> by_cases eb : c = b <;> simp_all
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun h => fresh (rep ▸ List.mem_toFinset.mpr (List.mem_of_mem_filter h)),nd.filter _⟩
  · simpa only [next,List.toFinset_cons,ff]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma anyBool {f : Bool → Bool} (a) (h : f a = true) : [false,true].any f = true :=
  List.any_eq_true.mpr ⟨a,by cases a <;> simp,h⟩

end FreeSearch1868

namespace Part1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868

end Part1868

namespace Full1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868

end Full1868

namespace Cuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma oneStep {k S} (l : BL k S) (m : Nat) (hm : k ≤ m+1) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) (go : List Sig → Bool)
    (hyp : ∀ w, w.Nodup → ∀ j ≤ m, BL j w.toFinset → go w = true) :
    (baseTest v || scanPairs (pairB v go) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr; right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v go x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      exact hyp _ nw j (by omega) (pw ▸ tail)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])



def excluded (k : Nat) (v : List Sig) := ∀ n ≤ k, ¬ BL n v.toFinset
end Cuts1868

namespace FastCuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868 Cuts1868

end FastCuts1868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Board1868
open Basis1868
def mult : List (Sig × Nat) → Sig
  | [] => zero
  | o::l => let (atLeastOne,atLeastTwo) := mult l
            (atLeastOne ||| o.2,atLeastTwo ||| (atLeastOne &&& o.2))
end Board1868
namespace LinearWide1868
open Basis1868 Board1868
end LinearWide1868
namespace Linear1868
def Linear (f : Nat → Nat) := f 0 = 0 ∧ ∀ x y, f (x ||| y) = f x ||| f y
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linId : Linear id := ⟨rfl,fun _ _ => rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linAnd (mask : Nat) : Linear (fun x => x &&& mask) :=
  ⟨by simp,fun _ _ => Nat.and_or_distrib_right ..⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linLeft (n : Nat) : Linear (fun x => x <<< n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_shiftLeft,Nat.testBit_or]
    by_cases e : n ≤ j <;> simp [e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linRight (n : Nat) : Linear (fun x => x >>> n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp [Nat.testBit_shiftRight,Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOr {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ||| g x) :=
  ⟨by simp [hf.1,hg.1],fun x y => by dsimp only; rw [hf.2,hg.2]; ac_rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linComp {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f (g x)) :=
  ⟨by dsimp only; rw [hg.1,hf.1],fun _ _ => by dsimp only; rw [hg.2,hf.2]⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma trunc_succ (x n : Nat) : x % 2^(n+1) = (x % 2^n) ||| (if x.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_or]
  cases e : x.testBit n <;> by_cases h : j=n <;> by_cases lt : j<n <;>
    simp_all [Nat.testBit_two_pow, show (j < n+1) ↔ j<n ∨ j=n by omega] <;> omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma imagesTrunc {f : Nat→Nat} (hl : Linear f) (x j) (n : Nat) :
    (f (x % 2^n)).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  induction n with
  | zero => simp [Nat.mod_one,hl.1]
  | succ n ih =>
    rw [trunc_succ,hl.2,Nat.testBit_or,Bool.or_eq_true,ih]
    by_cases bit : x.testBit n = true
    · simp only [bit,↓reduceIte]
      constructor
      · rintro (⟨i,hi,hb,hv⟩|h)
        · exact ⟨i,by omega,hb,hv⟩
        · exact ⟨n,by omega,bit,h⟩
      · rintro ⟨i,hi,hb,hv⟩
        by_cases e : i=n
        · exact Or.inr (e ▸ hv)
        · exact Or.inl ⟨i,by omega,hb,hv⟩
    · simp only [bit,↓reduceIte,hl.1,Nat.zero_testBit,Bool.false_eq_true,or_false]
      constructor
      · rintro ⟨i,hi,hb,hv⟩; exact ⟨i,by omega,hb,hv⟩
      · rintro ⟨i,hi,hb,hv⟩
        have ne : i ≠ n := fun e => bit (e ▸ hb)
        exact ⟨i,by omega,hb,hv⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma images {f : Nat→Nat} (hl : Linear f) {x n} (lim : x < 2^n) (j) :
    (f x).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  simpa [Nat.mod_eq_of_lt lim] using imagesTrunc hl x j n
end Linear1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma validBound {x} (h : Valid1 x) : x < 2^414 := by
  have eq : x % 2^414 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 414
    · simp [hj]
    · simp [hj,h j (by omega)]
  rw [← eq]
  exact Nat.mod_lt _ (by decide)
def Sub (x y : Nat) := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linMono {f} (h : Linear f) {x y} (s : Sub x y) : Sub (f x) (f y) := by
  have e : x ||| y = y := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
    cases hx : x.testBit i <;> simp [hx,s i]
  intro i hi
  have e' := congrArg (fun w : Nat => w.testBit i) (h.2 x y)
  simp [e,Nat.testBit_or,hi] at e'
  exact e'
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
abbrev Ix := Fin 26496
abbrev I := Fin 414
def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_11002_aux.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
abbrev Sign := Sig × Nat
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiOne {v : List Sign} {a} (ha : a ∈ v) (i) (hit : a.2.testBit i = true) :
    (mult v).1.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).1 ||| z.2).testBit i = true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl|hh
    · exact Or.inr hit
    · exact Or.inl (ih hh)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiTwo {v : List Sign} {a b} (ha : a∈v) (hb : b∈v) (ne : a ≠ b) (i)
    (x : a.2.testBit i = true) (y : b.2.testBit i = true) : (mult v).2.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).2 ||| ((mult l).1 &&& z.2)).testBit i = true
    rw [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ha with ea|hal
    · subst a
      rcases List.mem_cons.mp hb with eb|hbl
      · exact (ne eb.symm).elim
      · exact Or.inr ⟨multiOne hbl i y,x⟩
    · rcases List.mem_cons.mp hb with eb|hbl
      · subst b
        exact Or.inr ⟨multiOne hal i x,y⟩
      · exact Or.inl (ih hal hbl)

def U (d : Bool) (p n : I) (v : List Sig) (a : Sig) := ∀ c ∈ v, DS d p n c → c=a
def M (d : Bool) (p n : I) (v : List Sig) (a : Sig) :=
  DS d p n a ∧ (∃ j,U d p j v a) ∧ ∃ j,U d j n v a
end WProof1868
namespace Guard3400
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open WProof1868 LinearWide1868
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
open PEqualNP.Outside.L_meta_11002_aux.ColorSearch1868 (paint paint_ok)

end Guard3400
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Check2516
def costly (g : Gate) : Bool := match g.op with | .not => false | _ => true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gateTag {w : List Sig} (hw : ∀ a∈w, Valid a) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ (∃ a∈w, proper a ∧ gv w g=neg a) ∨
      ((if costly g then 1 else 0)=1 ∧ ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g=bin d a b) := by
  by_cases h : costly g=true
  · rcases gate_rep hw g legal with a|a|a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨by simp [h],a⟩)
  · obtain ⟨o,l⟩ := g
    cases o <;> try simp [costly] at h
    have nt (a : Sig) (v : Valid a) (r : represented w a) :
        represented w (neg a) ∨ ∃ a'∈w, proper a' ∧ neg a=neg a' := by
      rcases operand_cases v r with rfl|rfl|⟨mem,hp⟩
      · exact Or.inl (Or.inr (fun hp => hp.2.2 neg_laws.1))
      · exact Or.inl (Or.inr (fun hp => hp.2.1 neg_laws.2))
      · exact Or.inr ⟨a,mem,hp,rfl⟩
    cases l with
    | nil => exact (nt zero valid_zero (Or.inr (fun h => h.2.1 rfl))).imp_right Or.inl
    | cons i l => exact (nt (w.getD i zero) (valid_getD hw i) (get_rep w i)).imp_right Or.inl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pullTag (c : Nat) {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ (∃ a ∈ w, proper a ∧ z=neg a) ∨ (c=1 ∧ ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k+t'+c ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨hc,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tagExtract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.countP costly + t ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pullTag (if costly g then 1 else 0) ht (gateTag hw g (legal g (by simp))) hs
    exact ⟨l,u,T,by cases he : costly g <;> simp [he] at hl ⊢ <;> omega,hu,hT⟩
end Check2516
namespace Check2516
open Basis1868 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
end Check2516
namespace Basis1868
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindexLoop_testBit (f : Fin 414 → Fin 414) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 414 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 414
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 414 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 414 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 414
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 414 → Fin 414) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)

end Basis1868
namespace Sym1868
open Basis1868
def Good (H J : SigHom) (a : Sig) := Valid a ∧ J.fn (H.fn a) = a
variable {H J : SigHom}
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodNeg {a} (h : Good H J a) : Good H J (neg a) :=
  ⟨valid_neg h.1,by rw [H.hneg h.1,J.hneg (H.valid a),h.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBin {a b} (ha : Good H J a) (hb : Good H J b) {d} : Good H J (bin d a b) :=
  ⟨valid_bin ha.1 hb.1,by rw [H.hbin,J.hbin,ha.2,hb.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inj {a b} (ha : Good H J a) (hb : Good H J b) (e : H.fn a = H.fn b) : a=b := by
  rw [← ha.2,← hb.2,e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma properH {a} (ga : Good H J a) (ha : proper a) : proper (H.fn a) :=
  ⟨H.valid a,fun e => ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero)),
    fun e => ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))⟩
end Sym1868
namespace Moves3400
open Basis1868
open Free1868 Sym1868 Cuts1868
def SignFixed (H : SigHom) := ∀ a, sign (H.fn a)=sign a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip_map (H : SigHom) (s : Bool) {a : Sig} (ha : Valid a) :
    H.fn (flip s a)=flip s (H.fn a) := by cases s <;> first | rfl | exact H.hneg ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_map {H : SigHom} (fix : SignFixed H) {a : Sig} (ha : Valid a) :
    H.fn (can a)=can (H.fn a) := by unfold can; rw [fix a,flip_map H _ ha]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_map {H : SigHom} (fix : SignFixed H) {a b : Sig} (ha : Valid a) (hb : Valid b) (d s t) :
    H.fn (blend d s t a b)=blend d s t (H.fn a) (H.fn b) := by
  unfold blend
  rw [can_map fix (valid_bin (vf s ha) (vf t hb)),H.hbin,flip_map H _ ha,flip_map H _ hb]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodFlip {H J : SigHom} {a} (h : Good H J a) (s : Bool) : Good H J (flip s a) := by
  cases s <;> first | exact h | exact goodNeg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBlend {H J : SigHom} {a b} (ha : Good H J a) (hb : Good H J b) (d s t) :
    Good H J (blend d s t a b) := goodFlip (goodBin (goodFlip ha s) (goodFlip hb t)) _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mapBL {H J : SigHom} (fix : SignFixed H) {k S} (l : BL k S) (hs : ∀ a∈S,Good H J a) :
    BL k (S.image H.fn) := by
  induction l with
  | stop => simpa only [Finset.image_singleton,can_map fix target_proper.1,H.htarget] using (BL.stop : BL 0 {can target})
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    have ga := hs a (Finset.mem_insert_self ..)
    have gb := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have gu (x) (h : x∈U) : Good H J x := hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have gz := goodBlend ga gb d s t
    have ez := blend_map fix ha.1 hb.1 d s t
    have ht := ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,ez] at ht
    rw [Finset.image_insert,Finset.image_insert]
    apply BL.step (properH ga ha) (properH gb hb) _ _ (fun e => ne (inj ga gb e)) _ ht
    · rw [← can_map fix ha.1,ca]
    · rw [← can_map fix hb.1,cb]
    · rw [← ez,← Finset.image_insert,← Finset.image_insert]
      intro h
      obtain ⟨x,hx,xe⟩ := Finset.mem_image.mp h
      exact fresh (inj (hs x hx) gz xe ▸ hx)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fixed (p n : Fin 414 → Fin 414) (z : p 0=0) : SignFixed (pairHom p n) := by
  intro a
  change (reindex p a.1).testBit 0=a.1.testBit 0
  rw [reindex_testBit]
  simp [z]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma move {v w : List Sig} {k : Nat} (H J : SigHom) (fix : SignFixed H)
    (equal : (v.map H.fn).toFinset=w.toFinset)
    (inverse : v.all (fun a => decide (J.fn (H.fn a)=a))=true)
    (old : excluded k w) : excluded k v := by
  intro m hm l
  have h := mapBL (J:=J) fix l (fun a ha => ⟨(l.forms a ha).1.1,
    of_decide_eq_true (List.all_eq_true.mp inverse a (List.mem_toFinset.mp ha))⟩)
  have eq : v.toFinset.image H.fn=(v.map H.fn).toFinset := by
    ext x; simp
  rw [eq,equal] at h
  exact old _ hm h
end Moves3400
namespace Mono1868
open Basis1868

abbrev I := Fin 414
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def pos (x y : Bool) : Prop := x = true ∧ y = false
def D (p n : I) (a : Sig) : Prop := pos (P a p) (N a n)
def op (d x y : Bool) : Bool := if d then x || y else x && y

lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
lemma bor : ∀ (d ap an bp bn : Bool), pos (op d ap bp) (op d an bn) → pos ap an ∨ pos bp bn := by
  unfold pos; decide +kernel
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  unfold D P N at hd
  rw [bop,bop] at hd
  exact bor _ _ _ _ _ hd
lemma pair_sep {k t S} (hl : Live k t S) (ht : t = 0) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,pos,P,N,bit,target,testBit_top,p.isLt]
  | unary => omega
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (ht : t=0) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h ht p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

lemma mix : ∀ (d ap an bp bn al ar bm bq : Bool), pos ap an →
    ¬ pos bp bm → ¬ pos bq bn →
    pos (op d ap bp) (op d al bm) → pos (op d ar bq) (op d an bn) →
    ¬ pos bp bn ∧ pos (op d ap bp) (op d an bn) := by unfold pos; decide +kernel

lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U)) (ht : t = 0)
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : ¬ pos (P b p) (N b m) := fun h => hab (hm _ hb h).symm
  have bq : ¬ pos (P b q) (N b n) := fun h => hab (hq _ hb h).symm
  have zm := unique_diff tail ht (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail ht (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  unfold D P N at zm zq
  rw [bop,bop] at zm zq
  have hh := mix _ _ _ _ _ _ _ _ _ hd bm bq zm zq
  refine ⟨hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (ht : t=0) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ht ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail ht mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

theorem live_colored {k t S} (l : Live k t S) (ht : t=0) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary => omega
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih ht
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail ht hk
    exact ⟨u,hu,by omega⟩

end Mono1868
end PEqualNP.Outside.L_meta_11002_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_11002_aux
def edge : (Fin 8→Bool)→Bool := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7))
end PEqualNP.Outside.L_meta_11002_aux
namespace PEqualNP.Outside.L_meta_11002_aux
section
open Basis1868 Free1868
namespace Projection8403
def unaryRep (w : List Sig) (z : Sig) := ∃ a∈w,proper a ∧ z=neg a
def binRep (w : List Sig) (z : Sig) := ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b
lemma pullBudget {w : List Sig} {z : Sig} {k t S} {cost : Nat} (h : Live k t S)
    (hz : represented w z ∨ unaryRep w z ∨ (0 < cost ∧ binRep w z)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k + t' + cost ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨positive,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def Can (cost : Nat) (base : Finset Sig) := ∃ k t T,k≤cost+t ∧ Live k t T ∧ T⊆base
lemma mono {m n a b} (h : Can m a) (budget : m≤n) (sub : a⊆b) : Can n b := by
  obtain ⟨u,t,T,cap,run,incl⟩:=h;exact ⟨u,t,T,by omega,run,incl.trans sub⟩
lemma rewind {q basis z cost} (step : represented basis.toList z ∨ unaryRep basis.toList z ∨
      0<cost ∧ binRep basis.toList z) (tail : Can q (insert z basis)) : Can (q+cost) basis := by
  obtain ⟨k,t,T,le,h,sub⟩:=tail
  have avail : ∀a∈T,a∈basis.toList++[z] := by
    intro a ha;rcases Finset.mem_insert.mp (sub ha) with rfl|hm
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr hm)
  obtain ⟨k',t',T',cap,live,old⟩:=pullBudget h step avail
  exact ⟨k',t',T',by omega,live,fun a ha=>Finset.mem_toList.mp (old a ha)⟩
lemma negStep {basis : Finset Sig} {a : Sig} (va : Valid a) (ha : a∈basis) :
    represented basis.toList (neg a) ∨ unaryRep basis.toList (neg a) ∨ 0<0 ∧ binRep basis.toList (neg a) := by
  by_cases p : proper a
  · exact Or.inr (Or.inl ⟨a,Finset.mem_toList.mpr ha,p,rfl⟩)
  · rcases operand_cases va (Or.inr p : represented [] a) with rfl|rfl|⟨bad,_⟩
    · rw [neg_laws.1];exact Or.inl (Or.inr (fun p=>p.2.2 rfl))
    · rw [neg_laws.2];exact Or.inl (Or.inr (fun p=>p.2.1 rfl))
    · cases bad
lemma binaryStep {basis : Finset Sig} {a b : Sig} (d) (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis) :
    represented basis.toList (bin d a b) ∨ unaryRep basis.toList (bin d a b) ∨ 0<1 ∧ binRep basis.toList (bin d a b) := by
  rcases bin_rep d va vb (Or.inl (Finset.mem_toList.mpr ha)) (Or.inl (Finset.mem_toList.mpr hb)) with r|u|v
  · exact Or.inl r
  · exact Or.inr (Or.inl u)
  · exact Or.inr (Or.inr ⟨by decide,v⟩)
def constant (a : Sig) := a=zero ∨ a=one
instance (a : Sig) : Decidable (constant a) := by unfold constant;infer_instance
def mass (H : SigHom) (s : Finset Sig) := (s.filter (fun a=>constant (H.fn a))).card
lemma constant_neg {a : Sig} (va : Valid a) : constant (neg a) ↔ constant a := by
  constructor
  · rintro (e|e)
    · right;simpa only [neg2,neg_laws.1] using (show neg (neg a)=neg zero from congrArg neg e)
    · left;simpa only [neg2,neg_laws.2] using congrArg neg e
  · rintro (rfl|rfl)
    · right;exact neg_laws.1
    · left;exact neg_laws.2
lemma constResult {a b : Sig} (va : Valid a) (vb : Valid b) (d : Bool) (c : constant a ∨ constant b) :
    constant (bin d a b) ∨ bin d a b=a ∨ bin d a b=b := by
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws va
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws vb
  rcases c with (rfl|rfl)|(rfl|rfl) <;> cases d <;> simp_all [constant,bin_comm]
lemma bothResult {a b : Sig} (va : Valid a) (vb : Valid b) (d) (ca : constant a) (cb : constant b) :
    constant (bin d a b) := by
  rcases constResult va vb d (Or.inl ca) with h|h|h
  · exact h
  · simpa only [h] using ca
  · simpa only [h] using cb
lemma constFree {basis : Finset Sig} {a b : Sig} (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis)
    (d) (c : constant a ∨ constant b) : represented basis.toList (bin d a b) := by
  rcases constResult va vb d c with (h|h)|h|h
  · exact Or.inr (fun p=>p.2.1 h)
  · exact Or.inr (fun p=>p.2.2 h)
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr ha
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr hb
end Projection8403
end
section
open Basis1868 Free1868
namespace Projection8403
lemma massInsert (H : SigHom) (a : Sig) (U : Finset Sig) :
    mass H (insert a U) = mass H U + (if a∉U ∧ constant (H.fn a) then 1 else 0) := by
  classical
  by_cases mem : a∈U
  · simp [mem,Finset.insert_eq_of_mem mem]
  · by_cases c : constant (H.fn a)
    · simp [mass,Finset.filter_insert,mem,c,Finset.card_insert_of_notMem]
    · simp [mass,Finset.filter_insert,mem,c]
lemma pushNeg {H : SigHom} {q : Nat} {U : Finset Sig} {a : Sig} (va : Valid a)
    (tail : Can q ((insert (neg a) U).image H.fn)) : Can q ((insert a U).image H.fn) := by
  let pool:=(insert a U).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have sub : (insert (neg a) U).image H.fn⊆insert (neg (H.fn a)) pool := by
    rw [Finset.image_insert,H.hneg va]
    exact Finset.insert_subset_insert _ (Finset.image_mono _ (Finset.subset_insert ..))
  simpa only [Nat.add_zero,pool] using rewind (negStep (H.valid a) ha) (mono tail (Nat.le_refl _) sub)
lemma pushBin {H : SigHom} {q : Nat} {U : Finset Sig} {a b : Sig} (d : Bool) (tail : Can q ((insert (bin d a b) U).image H.fn)) :
    Can (q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1)) ((insert a (insert b U)).image H.fn) := by
  let pool:=(insert a (insert b U)).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have hb : H.fn b∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have sub : (insert (bin d a b) U).image H.fn ⊆ insert (bin d (H.fn a) (H.fn b)) pool := by
    rw [Finset.image_insert,H.hbin]
    apply Finset.insert_subset_insert
    exact Finset.image_mono _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
  by_cases c : constant (H.fn a) ∨ constant (H.fn b)
  · rw [ite_eq_left c]
    apply rewind (Or.inl (constFree (H.valid a) (H.valid b) ha hb d c))
    exact mono tail (Nat.le_refl _) sub
  · rw [ite_eq_right c]
    exact rewind (binaryStep d (H.valid a) (H.valid b) ha hb) (mono tail (Nat.le_refl _) sub)
lemma massNeg {H : SigHom} {U : Finset Sig} {a : Sig} (va : Valid a) (fresh : neg a∉insert a U) :
    mass H (insert a U)≤mass H (insert (neg a) U) := by
  have hz : neg a∉U:=fun zn=>fresh (Finset.mem_insert_of_mem zn)
  rw [massInsert,massInsert,H.hneg va]
  simp only [hz,not_false_eq_true,true_and,constant_neg (H.valid a)]
  by_cases c : constant (H.fn a) <;> by_cases t : a∈U <;> simp [c,t]
lemma massBin {H : SigHom} {U : Finset Sig} {a b : Sig} (d : Bool) (ab : a≠b) (fresh : bin d a b∉insert a (insert b U)) :
    mass H (insert a (insert b U)) + (if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1) ≤
      mass H (insert (bin d a b) U)+1 := by
  have hz : bin d a b∉U:=fun z=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem z))
  rw [massInsert,massInsert,massInsert,H.hbin]
  by_cases ca : constant (H.fn a) <;> by_cases cb : constant (H.fn b)
  all_goals by_cases aa : a∈U <;> by_cases bb : b∈U
  all_goals simp only [Finset.mem_insert,ab,false_or,ca,cb,aa,bb,hz,not_true_eq_false,not_false_eq_true,
    and_false,false_and,true_and,and_true,ite_false,ite_true,or_false,false_or,true_or,or_true,Nat.add_zero]
  all_goals try omega
  all_goals try (have z:=bothResult (H.valid a) (H.valid b) d ca cb; rw [ite_eq_left z]; omega)
  all_goals try (split <;> omega)
  all_goals
    have z := bothResult (H.valid a) (H.valid b) d ca cb
    simp only [z,ite_true]
    omega
theorem projected {k t S} (h : Live k t S) (H : SigHom) :
    ∃ q,q+mass H S+t≤k ∧ Can q (S.image H.fn) := by
  induction h with
  | stop =>
    have nc : ¬constant target:=by rintro (e|e);exact target_proper.2.1 e;exact target_proper.2.2 e
    refine ⟨0,by simp [mass,H.htarget,nc],0,0,{target},by omega,Live.stop,?_⟩
    simp [H.htarget]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massNeg (H:=H) ha.1 hf
    exact ⟨q,by omega,pushNeg ha.1 prog⟩
  | @binary k t U a b d ha hb ab hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massBin (H:=H) d ab hf
    exact ⟨q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1),by omega,pushBin d prog⟩
theorem projectedBL {n S} (run : BL n S) (H : SigHom) :
    ∃k T,k+mass H S≤n ∧ BL k T ∧ T⊆(S.image H.fn).image can := by
  obtain ⟨t,live⟩:=run.expand
  obtain ⟨q,lim,m,u,T,cap,h,sub⟩:=projected live H
  obtain ⟨j,V,size,ok,ss⟩:=compress h
  exact ⟨j,V,by omega,ok,ss.trans (Finset.image_mono _ sub)⟩
end Projection8403
end
section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Check2516 Free1868 FreeSearch1868 Cuts1868
open Projection8403 PEqualNP.Outside.L_meta_11002_aux
namespace Exact8403
def raw8 : List Sig := [(0x2aaaaaaaaaaaaaaaaaaaaabdd5555555555eaaedb6db5ef7baaaaaaaaaaaaaaaaaaaaaaaaaaaabdd5555555555eaaedb6db5ef7b,0x4002040804002040804002040804002040804002040804002040804002040804002040804002040804002040804002040804002),(0xcccccccccccccccccccccd6e6666666666b3376db6deb5adccccccccccccccccccccccccccccd6e6666666666b3376db6deb5ad,0x924489000924489000924489000924489000924489000924489000924489000924489000924489000924489000924489000924),(0x30f0f0f0f0f0f0f0f0f0f0e7787878787873c3b8e38e739cef0f0f0f0f0f0f0f0f0f0f0f0f0f0e7787878787873c3b8e38e739ce,0x292489122a92489122a92489122a92489122a92489122a92489122a92489122a92489122a92489122a92489122a92489122a9248),(0xff00ff00ff00ff00ff00f87f807f807f83fc3f03f07c1f0ff00ff00ff00ff00ff00ff00ff00f87f807f807f83fc3f03f07c1f0,0x31c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70e00331c70),(0xffff0000ffff0000ffff007fff80007ffc003ffc007fe00ffff0000ffff0000ffff0000ffff007fff80007ffc003ffc007fe00,0x1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f8001c3c1f80),(0x3f00000000ffffffff0000007fffffff8000003fffff80000ffffffff00000000ffffffff0000007fffffff8000003fffff80000,0x3e0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe0000003fe000),(0x3fffffffff000000000000007fffffffffffffc0000000000ffffffffffffffff000000000000007fffffffffffffc0000000000,0x1fc0000001fc0000001fc0000001fc0000001fc0000001fc0000001fc0000001fc0000001fc0000001fc0000001fc00000),(0x3fffffffffffffffffffffff8000000000000000000000000ffffffffffffffffffffffffffffff8000000000000000000000000,0xfe0000000fe0000000fe0000000fe0000000fe0000000fe0000000fe0000000fe0000000fe0000000fe0000000fe0000000)]
def pos8 : Array Nat := #[3,5,6,7,9,11,13,14,15,17,19,21,22,23,25,27,29,30,31,34,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,61,62,63,67,69,70,71,72,73,74,75,76,77,78,79,81,83,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,131,133,134,135,137,139,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255]
def neg8 : Array Nat := #[0,1,2,4,8,10,12,16,18,20,24,26,28,32,33,36,40,44,48,52,56,60,64,65,66,68,80,82,84,128,129,130,132,136,138,140]
def sample8 (s : Bool) (i : Fin 414) : Fin 8 → Bool :=
  let xs:=if s then pos8 else neg8
  fun j=>(xs.getD (i.val % xs.size) 0).testBit j.val
lemma vals : ∀a∈raw8,Valid a := by
  have h : raw8.all (fun x=>decide (x.1≤top ∧ x.2≤top))=true := by decide +kernel
  intro a ha
  have k:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top k.1,valid1_of_le_top k.2⟩
set_option maxHeartbeats 0 in
lemma good8 : ∀(s : Bool) (i : Fin 414), edge (sample8 s i)=s ∧ List.ofFn (sample8 s i)=raw8.map (bit s i) := by decide +kernel
lemma output8 {C : Circuit} (fan : FanInTwo C) (spec : ∀x, C.eval (List.ofFn x)=edge x) :
    target∈execute C.gates raw8 := by
  let w:=execute C.gates raw8
  have hwv:=execute_valid C.gates raw8 vals
  have hp (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero)=s := by
    rw [←b_read]
    change ((execute C.gates raw8).map _).getD C.output false=s
    rw [execute_bits _ _ _ _ vals (fun g hg=>(fan g hg).1)]
    have h:=spec (sample8 s i)
    rw [(good8 s i).1,(good8 s i).2] at h
    exact h
  have hvout:=valid_getD hwv C.output
  have et : w.getD C.output zero=target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq;intro j
      rw [target,testBit_top]
      by_cases hi : j<414
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)];simp [hi]
    · apply Nat.eq_of_testBit_eq;intro j
      by_cases hi : j<414
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)];exact (Nat.zero_testBit j).symm
  have rep:=get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun h=>h target_proper)
def necessary (v : List Sig) := ∀a∈v,∃p n : Fin 414,∀b∈v,bit true p b≠bit false n b → b=a
lemma allNeeded {k t S} {v : List Sig} (h : Live k t S) (sub : S⊆v.toFinset) (need : necessary v) : S=v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨p,n,uniq⟩:=need a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_11002_aux.Conflict1868.pair_sep h p n
  exact uniq b (List.mem_toFinset.mp (sub hb)) sep ▸ hb
def necessaryAt (v : List Sig) (pn : List (Nat×Nat)) :=
  (v.zip pn).all fun (a,p,n) => v.all fun b=>bit true (Fin.ofNat 414 p) b == bit false (Fin.ofNat 414 n) b || b==a
lemma needFrom {v : List Sig} {pn : List (Nat×Nat)} (len : v.length≤pn.length) (ok : necessaryAt v pn=true) : necessary v := by
  intro a ha
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ha
  have hp : i<pn.length:=by omega
  have hz : (a,pn[i])∈v.zip pn := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp;omega,by simp [eq]⟩
  have h:=List.all_eq_true.mp ok _ hz
  refine ⟨Fin.ofNat 414 pn[i].1,Fin.ofNat 414 pn[i].2,?_⟩
  intro b hb no
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp h _ hb) with e|e
  · exact False.elim (no (beq_iff_eq.mp e))
  · exact beq_iff_eq.mp e
end Exact8403
end
section
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Cuts1868
open Linear1868
namespace QuickQ

abbrev Move := Bool × Nat × Nat
def update (op : Move) (x : Nat) :=
  (if op.1 then x ||| (x <<< op.2.1) else x ||| (x >>> op.2.1)) &&& op.2.2
def sweep : List Move → Nat → Nat
  | [],x => x
  | h::t,x => sweep t (update h x)
theorem linUpdate (op : Move) : Linear (update op) := by
  rcases op with ⟨b,m,n⟩
  cases b
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x >>> m)) (linAnd n) (linOr linId (linRight m))
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x <<< m)) (linAnd n) (linOr linId (linLeft m))
theorem linSweep (xs : List Move) : Linear (sweep xs) := by
  induction xs with
  | nil => exact linId
  | cons h t ih => exact linComp (f:=sweep t) (g:=update h) ih (linUpdate h)

structure Chart where
  h : Nat
  w : Nat
  spreadP : List Move
  spreadN : List Move
  fillP : List Move
  fillN : List Move

def area (c : Chart) := c.h*c.w
def roof (c : Chart) := 2^(area c)-1
def lanes (c : Chart) := (roof c)/(2^c.w-1)
def row (c : Chart) (i : Nat) := (2^c.w-1) <<< (c.w*i)
def col (c : Chart) (i : Nat) := lanes c <<< i
def positive (c : Chart) (i : Fin (area c)) : Fin 414 := Fin.ofNat 414 (i.val/c.w)
def negative (c : Chart) (i : Fin (area c)) : Fin 414 := Fin.ofNat 414 (i.val % c.w)
def good (c : Chart) :=
  (∀i : Fin 414, sweep c.spreadP (2^i.val) = if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 414, sweep c.spreadN (2^i.val) = if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c), (row c (positive c i).val).testBit i.val=true ∧
      (col c (negative c i).val).testBit i.val=true) ∧
  (∀(i : Fin (area c)) (p : Fin c.h), (row c p.val).testBit i.val=true → (positive c i).val=p.val) ∧
  (∀(i : Fin (area c)) (n : Fin c.w), (col c n.val).testBit i.val=true → (negative c i).val=n.val) ∧
  (∀i : Fin (area c), (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀r : Fin c.h, sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val = 0) ∧
  (∀n : Fin c.w, sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val = 0)
theorem roofBit (c : Chart) (i : Nat) : (roof c).testBit i=decide (i<area c) := by
  simp [roof,Nat.testBit_two_pow_sub_one]
theorem locate {f : Nat→Nat} {mask top x i : Nat} (lin : Linear f) (hm : mask.testBit i=true)
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_11002_aux.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_11002_aux.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_11002_aux.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_11002_aux.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.1 ⟨j,hj⟩] at x
    by_cases e : j<c.h
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(positive c i).isLt,x,?_⟩
    rw [h.1 (positive c i), ite_eq_left (h.2.2.2.2.2.1 i).1]
    exact (h.2.2.1 i).1
theorem nbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadN a).testBit i.val = a.testBit (negative c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_11002_aux.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.2.1 ⟨j,hj⟩] at x
    by_cases e : j<c.w
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(negative c i).isLt,x,?_⟩
    rw [h.2.1 (negative c i),ite_eq_left (h.2.2.2.2.2.1 i).2]
    exact (h.2.2.1 i).2
end QuickQ
end
section
open Basis1868
namespace QuickQ
def compactGood (c : Chart) :=
  (∀i : Fin 414,sweep c.spreadP (2^i.val)=if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 414,sweep c.spreadN (2^i.val)=if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c),(row c (positive c i).val).testBit i.val=true ∧ (col c (negative c i).val).testBit i.val=true ∧
      (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀p q : Fin c.h,p≠q → row c p.val &&& row c q.val=0) ∧
  (∀p q : Fin c.w,p≠q → col c p.val &&& col c q.val=0) ∧
  (∀r : Fin c.h,sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val=0) ∧
  (∀n : Fin c.w,sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val=0)
theorem goodOfCompact {c : Chart} (h : compactGood c) : good c := by
  obtain ⟨sp,sn,sel,rows,cols,fp,fn⟩:=h
  refine ⟨sp,sn,fun i=>⟨(sel i).1,(sel i).2.1⟩,?_,?_,fun i=>(sel i).2.2,fp,fn⟩
  · intro i p hp
    let q : Fin c.h:=⟨(positive c i).val,(sel i).2.2.1⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (rows q p (fun eq=>ne (congrArg Fin.val eq)))
    change (row c (positive c i).val &&& row c p.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).1,hp,Nat.zero_testBit] at bad
    contradiction
  · intro i n hn
    let q : Fin c.w:=⟨(negative c i).val,(sel i).2.2.2⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (cols q n (fun eq=>ne (congrArg Fin.val eq)))
    change (col c (negative c i).val &&& col c n.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).2.1,hn,Nat.zero_testBit] at bad
    contradiction
end QuickQ
end
section
namespace QuickQ
def roof1024 : Nat := 2^1024-1
def ch64x16 : Chart := ⟨64,16,[(false,0,0xffffffffffffffff),(true,480,(joinBits 0xffffffff 512 0xffffffff)),(true,240,(joinBits (joinBits 0xffff 256 0xffff) 512 (joinBits 0xffff 256 0xffff))),(true,120,(joinBits (joinBits (joinBits 0xff 128 0xff) 256 (joinBits 0xff 128 0xff)) 512 (joinBits (joinBits 0xff 128 0xff) 256 (joinBits 0xff 128 0xff)))),(true,60,0xf000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f),(true,30,0x300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003),(true,15,0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001),(true,1,roof1024),(true,2,roof1024),(true,4,roof1024),(true,8,roof1024)],[(false,0,0xffff),(true,16,roof1024),(true,32,roof1024),(true,64,roof1024),(true,128,roof1024),(true,256,roof1024),(true,512,roof1024)],[(false,1,roof1024),(false,2,roof1024),(false,4,roof1024),(false,8,roof1024),(false,0,0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001),(true,1,roof1024),(true,2,roof1024),(true,4,roof1024),(true,8,roof1024)],[(false,16,roof1024),(false,32,roof1024),(false,64,roof1024),(false,128,roof1024),(false,256,roof1024),(false,512,roof1024),(false,0,0xffff),(true,16,roof1024),(true,32,roof1024),(true,64,roof1024),(true,128,roof1024),(true,256,roof1024),(true,512,roof1024)]⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem good_ch64x16 : good ch64x16 := by apply goodOfCompact;unfold compactGood;decide +kernel
end QuickQ
end
section
namespace QuickQ
def roof2048 : Nat := 2^2048-1
def ch64x32 : Chart := ⟨64,32,[(false,0,0xffffffffffffffff),(true,992,(joinBits 0xffffffff 1024 0xffffffff)),(true,496,(joinBits (joinBits 0xffff 512 0xffff) 1024 (joinBits 0xffff 512 0xffff))),(true,248,(joinBits (joinBits (joinBits 0xff 256 0xff) 512 (joinBits 0xff 256 0xff)) 1024 (joinBits (joinBits 0xff 256 0xff) 512 (joinBits 0xff 256 0xff)))),(true,124,(joinBits (joinBits (joinBits (joinBits 15 128 15) 256 (joinBits 15 128 15)) 512 (joinBits (joinBits 15 128 15) 256 (joinBits 15 128 15))) 1024 (joinBits (joinBits (joinBits 15 128 15) 256 (joinBits 15 128 15)) 512 (joinBits (joinBits 15 128 15) 256 (joinBits 15 128 15))))),(true,62,0x30000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003),(true,31,0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001),(true,1,roof2048),(true,2,roof2048),(true,4,roof2048),(true,8,roof2048),(true,16,roof2048)],[(false,0,0xffffffff),(true,32,roof2048),(true,64,roof2048),(true,128,roof2048),(true,256,roof2048),(true,512,roof2048),(true,1024,roof2048)],[(false,1,roof2048),(false,2,roof2048),(false,4,roof2048),(false,8,roof2048),(false,16,roof2048),(false,0,0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001),(true,1,roof2048),(true,2,roof2048),(true,4,roof2048),(true,8,roof2048),(true,16,roof2048)],[(false,32,roof2048),(false,64,roof2048),(false,128,roof2048),(false,256,roof2048),(false,512,roof2048),(false,1024,roof2048),(false,0,0xffffffff),(true,32,roof2048),(true,64,roof2048),(true,128,roof2048),(true,256,roof2048),(true,512,roof2048),(true,1024,roof2048)]⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem good_ch64x32 : good ch64x32 := by apply goodOfCompact;unfold compactGood;decide +kernel
end QuickQ
end
section
namespace QuickQ
def roof256 : Nat := 2^256-1
def ch16x16 : Chart := ⟨16,16,[(false,0,0xffff),(true,120,0xff000000000000000000000000000000ff),(true,60,0xf000000000000000f000000000000000f000000000000000f),(true,30,0x300000003000000030000000300000003000000030000000300000003),(true,15,0x1000100010001000100010001000100010001000100010001000100010001),(true,1,roof256),(true,2,roof256),(true,4,roof256),(true,8,roof256)],[(false,0,0xffff),(true,16,roof256),(true,32,roof256),(true,64,roof256),(true,128,roof256)],[(false,1,roof256),(false,2,roof256),(false,4,roof256),(false,8,roof256),(false,0,0x1000100010001000100010001000100010001000100010001000100010001),(true,1,roof256),(true,2,roof256),(true,4,roof256),(true,8,roof256)],[(false,16,roof256),(false,32,roof256),(false,64,roof256),(false,128,roof256),(false,0,0xffff),(true,16,roof256),(true,32,roof256),(true,64,roof256),(true,128,roof256)]⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem good_ch16x16 : good ch16x16 := by apply goodOfCompact;unfold compactGood;decide +kernel
end QuickQ
end
section
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open PEqualNP.Outside.L_meta_11002_aux.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
open PEqualNP.Outside.L_meta_11002_aux.ColorSearch1868 (paint paint_ok)
namespace QuickQ
def diff (c : Chart) (d : Bool) (a : Sig) : Sig × Nat :=
  let p:=sweep c.spreadP a.1
  let n:=sweep c.spreadN a.2
  (a,if d then p ^^^ n else p &&& (roof c ^^^ n))
def signs (c : Chart) (d : Bool) (v : List Sig) := v.map (diff c d)
def once (s : List (Sig × Nat)) := let t:=mult s;t.1 ^^^ t.2
def hit (c : Chart) (sn : Nat) (z : Sig × Nat) := z.2 &&& sn &&& roof c
def marked (c : Chart) (sn : Nat) (z : Sig × Nat) : Sig × Nat :=
  let u:=hit c sn z
  (z.1,z.2 &&& sweep c.fillP u &&& sweep c.fillN u &&& roof c)
def entries (c : Chart) (d : Bool) (v : List Sig) := let s:=signs c d v;let one:=once s;s.map (marked c one)
def test (c : Chart) (d : Bool) (colors : Nat) (v : List Sig) :=
  let s:=signs c d v
  let counts:=mult s
  (counts.1 &&& roof c)==roof c && paint colors (s.map (marked c (counts.1 ^^^ counts.2))) (fun _=>0)
theorem diffBit {c : Chart} (good : good c) (d : Bool) {a : Sig} (val : Valid a) (i : Fin (area c)) :
    (diff c d a).2.testBit i.val=true ↔ DS d (positive c i) (negative c i) a := by
  have rt : (roof c).testBit i.val=true:=by rw [roofBit];exact decide_eq_true i.isLt
  cases d
  · change Nat.testBit (sweep c.spreadP a.1 &&& (roof c ^^^ sweep c.spreadN a.2)) i.val=true ↔ a.1.testBit (positive c i).val=true ∧ a.2.testBit (negative c i).val=false
    simp [Nat.testBit_and,Nat.testBit_xor,pbit good val.1,nbit good val.2,rt]
  · change Nat.testBit (sweep c.spreadP a.1 ^^^ sweep c.spreadN a.2) i.val=true ↔ a.1.testBit (positive c i).val≠a.2.testBit (negative c i).val
    simp [Nat.testBit_xor,pbit good val.1,nbit good val.2]
theorem hitBound (c : Chart) (sn : Nat) (a : Sig × Nat) : Sub (hit c sn a) (roof c) := by
  intro i hi;simp only [hit,Nat.testBit_and,Bool.and_eq_true] at hi;exact hi.2
theorem uniq {c : Chart} (good : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (hit c (once (signs c d v)) (diff c d a)).testBit i.val=true) :
    U d (positive c i) (negative c i) v a := by
  intro b hb db
  by_contra neq
  have h1 : diff c d a ∈ signs c d v:=List.mem_map_of_mem ha
  have h2 : diff c d b ∈ signs c d v:=List.mem_map_of_mem hb
  have ne : diff c d a ≠ diff c d b:=fun e=>neq (congrArg Prod.fst e).symm
  simp only [hit,Nat.testBit_and,Bool.and_eq_true,once,Nat.testBit_xor] at h
  have first:=multiOne h1 i.val h.1.1
  have second:=multiTwo h1 h2 ne i.val h.1.1 ((diffBit good d (va b hb) i).2 db)
  simp [first,second] at h
theorem entryMark {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (marked c (once (signs c d v)) (diff c d a)).2.testBit i.val=true) :
    M d (positive c i) (negative c i) v a := by
  let u:=hit c (once (signs c d v)) (diff c d a)
  simp only [marked,Nat.testBit_and,Bool.and_eq_true] at h
  let p : Fin c.h:=⟨(positive c i).val,(hg.2.2.2.2.2.1 i).1⟩
  let n : Fin c.w:=⟨(negative c i).val,(hg.2.2.2.2.2.1 i).2⟩
  have rp:=locate (linSweep _) (hg.2.2.1 i).1 (hg.2.2.2.2.2.2.1 p) (hitBound c (once (signs c d v)) (diff c d a)) h.1.1.2
  have rn:=locate (linSweep _) (hg.2.2.1 i).2 (hg.2.2.2.2.2.2.2 n) (hitBound c (once (signs c d v)) (diff c d a)) h.1.2
  refine ⟨(diffBit hg d (va a ha) i).1 h.1.1.1,?_,?_⟩
  · obtain ⟨j,hj,hp⟩:=rp
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : positive c j'=positive c i:=Fin.ext (hg.2.2.2.1 j' p hp)
    exact ⟨negative c j',eq ▸ uniq hg va ha j' hj⟩
  · obtain ⟨j,hj,hn⟩:=rn
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : negative c j'=negative c i:=Fin.ext (hg.2.2.2.2.1 j' n hn)
    exact ⟨positive c j',eq ▸ uniq hg va ha j' hj⟩
theorem entryIds (c d v) : (entries c d v).map Prod.fst=v := by
  simp [entries,signs,marked,diff,Function.comp_def]
theorem hasEntry {c d v a} (ha : a∈entries c d v) : a.1∈v := by
  rw [←entryIds c d v];exact List.mem_map_of_mem ha
theorem overlap {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a)
    {x y} (hx : x∈entries c d v) (hy : y∈entries c d v) (non : x.2 &&& y.2≠0) :
    ∃p n,M d p n v x.1 ∧ M d p n v y.1 := by
  obtain ⟨zx,ax,rfl⟩:=List.mem_map.mp hx
  obtain ⟨zy,ay,rfl⟩:=List.mem_map.mp hy
  obtain ⟨ax',av,rfl⟩:=List.mem_map.mp ax
  obtain ⟨ay',bv,rfl⟩:=List.mem_map.mp ay
  obtain ⟨j,h⟩:=Nat.exists_testBit_of_ne_zero non
  rw [Nat.testBit_and,Bool.and_eq_true] at h
  have u:=h.1
  simp only [marked,Nat.testBit_and,Bool.and_eq_true,roofBit] at u
  let i : Fin (area c):=⟨j,of_decide_eq_true u.2⟩
  exact ⟨positive c i,negative c i,entryMark hg va av i h.1,entryMark hg va bv i h.2⟩

theorem testSigned {c : Chart} (hg : good c) {k m v} (hm : m≤k) (nd : v.Nodup) (h : BL m v.toFinset) :
    test c true (k+2-v.length) v=true := by
  obtain ⟨t,l⟩:=h.expand
  have val : ∀a∈v,Valid a:=fun a ha=>(h.forms _ (List.mem_toFinset.mpr ha)).1.1
  obtain ⟨n,⟨f,bd,ok⟩,le⟩:=freeColors h
  have sz : v.toFinset.card=v.length:=List.toFinset_card_of_nodup nd
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_and,roofBit]
    by_cases hi : i<area c
    · let z : Fin (area c):=⟨i,hi⟩
      obtain ⟨a,ha,hit⟩:=pair_sep l (positive c z) (negative c z)
      have av:=List.mem_toFinset.mp ha
      have hit':=multiOne (List.mem_map_of_mem (f:=diff c true) av) i ((diffBit hg true (val a av) z).2 hit)
      simpa [hi,signs] using hit'
    · simp [hi]
  · change paint (k+2-v.length) (entries c true v) _ =true
    apply paint_ok _ f
    · rwa [entryIds]
    · intro a ha;have := bd _ (List.mem_toFinset.mpr (hasEntry ha));omega
    · simp
    · intro a ha b hb ne eq
      by_contra non
      obtain ⟨p,q,x,y⟩:=overlap hg val ha hb non
      apply ok _ (List.mem_toFinset.mpr (hasEntry ha)) _ (List.mem_toFinset.mpr (hasEntry hb)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_11002_aux.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_11002_aux.Conflict1868.Unique] using y⟩
end QuickQ
end
section
open Basis1868
open Free1868 FreeSearch1868 Cuts1868
namespace QuickQ

def incl (v w : List Sig) : Bool := v.length == w.length && v.all w.contains
theorem inclEq {v w : List Sig} (nd : v.Nodup) (h : incl v w=true) : v.toFinset=w.toFinset := by
  obtain ⟨card,mem⟩:=Bool.and_eq_true_iff.mp h
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp mem _ (List.mem_toFinset.mp ha)))
  · rw [List.toFinset_card_of_nodup nd,beq_iff_eq.mp card]
    exact List.toFinset_card_le _
end QuickQ
end
section
open Basis1868
open Free1868 FreeSearch1868 Cuts1868
namespace QuickQ

def wireKey (a : Sig) :=
  let x := a.1 % 1000000007
  let y := a.2 % 1000000009
  (x*x+193*x*y+479*y*y+139*x+197*y) % 1099511627689
def key (xs : List Sig) := xs.foldl (fun r a=>r+wireKey a) 0
end QuickQ
end
section
open Basis1868 Free1868 Projection8403
namespace Tape8403
def close (v : List Sig) : Finset Sig := insert zero (insert one (v.toFinset ∪ v.toFinset.image neg))
theorem memClose {v : List Sig} {a : Sig} (ha : a∈v) : a∈close v := by
  simp only [close,Finset.mem_insert,Finset.mem_union,List.mem_toFinset]
  exact Or.inr (Or.inr (Or.inl ha))
theorem negClose {v : List Sig} {a : Sig} (ha : a∈close v) : neg a∈close v := by
  simp only [close,Finset.mem_insert,Finset.mem_union,Finset.mem_image,List.mem_toFinset] at *
  rcases ha with rfl|rfl|av|⟨b,hb,rfl⟩
  · exact Or.inr (Or.inl neg_laws.1)
  · exact Or.inl neg_laws.2
  · exact Or.inr (Or.inr (Or.inr ⟨a,av,rfl⟩))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [neg2] using hb)))
theorem flipClose {v : List Sig} {a : Sig} (ha : a∈close v) (s) : flip s a∈close v := by
  cases s
  · exact ha
  · exact negClose ha
theorem close_cons (z : Sig) (v : List Sig) : close (z::v)=insert (neg z) (insert z (close v)) := by
  ext x
  simp [close,or_assoc,or_left_comm,or_comm]
def op (code : Nat) (w : List Sig) : Sig :=
  let a:=w.getD (code/1024) zero
  let b:=w.getD (code/16 % 64) zero
  flip (code.testBit 3) (bin (code.testBit 2) (flip (code.testBit 1) a) (flip (code.testBit 0) b))
theorem memRead (w : List Sig) (i : Nat) : w.getD i zero∈close w := by
  by_cases h : i<w.length
  · exact memClose (by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h])
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)];simp [close]
theorem op_valid {w : List Sig} (va : ∀a∈w,Valid a) (code) : Valid (op code w) :=
  vf _ (valid_bin (vf _ (valid_getD va _)) (vf _ (valid_getD va _)))
theorem freeFlip {V : Finset Sig} {a : Sig} (va : Valid a) (ha : a∈V) {q} (s : Bool)
    (endCap : Can q (insert (flip s a) V)) : Can q V := by
  cases s
  · simpa only [flipFalse,Finset.insert_eq_of_mem ha] using endCap
  · simpa only [Nat.add_zero] using rewind (negStep va ha) endCap
theorem dropBoth {V : Finset Sig} {a : Sig} (va : Valid a) {q}
    (endCap : Can q (insert (neg a) (insert a V))) : Can q (insert a V) := by
  simpa only [Nat.add_zero] using rewind (negStep va (Finset.mem_insert_self ..)) endCap
theorem step {w : List Sig} (va : ∀a∈w,Valid a) {q} (code)
    (tail : Can q (close (op code w::w))) :
    Can (q+if op code w∈close w then 0 else 1) (close w) := by
  rw [close_cons] at tail
  by_cases hz : op code w∈close w
  · simpa only [ite_eq_left hz,Nat.add_zero,Finset.insert_eq_of_mem hz,Finset.insert_eq_of_mem (negClose hz)] using tail
  · rw [ite_eq_right hz]
    let a:=flip (code.testBit 1) (w.getD (code/1024) zero)
    let b:=flip (code.testBit 0) (w.getD (code/16 % 64) zero)
    let c:=bin (code.testBit 2) a b
    have av : Valid a:=vf _ (valid_getD va _)
    have bv : Valid b:=vf _ (valid_getD va _)
    have cv : Valid c:=valid_bin av bv
    have ca:=dropBoth (op_valid va code) tail
    have cg : Can q (insert c (close w)) := by
      apply freeFlip cv (Finset.mem_insert_self c (close w)) (code.testBit 3)
      apply mono ca (Nat.le_refl _)
      exact Finset.insert_subset_insert _ (Finset.subset_insert ..)
    exact rewind (binaryStep (code.testBit 2) av bv (flipClose (memRead w _) _) (flipClose (memRead w _) _)) cg
def eval : List Nat → List Sig → Nat×List Sig
  | [],v=>(0,v)
  | c::cs,v=>
    let z:=op c v
    let out:=eval cs (z::v)
    ((if z∈close v then 0 else 1)+out.1,out.2)
theorem rewindTape {qs : List Nat} {v : List Sig} (va : ∀a∈v,Valid a) {q}
    (tail : Can q (close (eval qs v).2)) : Can (q+(eval qs v).1) (close v) := by
  induction qs generalizing v with
  | nil => simpa [eval] using tail
  | cons x xs ih =>
    have va' : ∀a∈op x v::v,Valid a := List.forall_mem_cons.mpr ⟨op_valid va x,va⟩
    have p:=step va x (ih va' tail)
    simpa only [eval,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using p
theorem eqFlip (H : SigHom) {a : Sig} (va : Valid a) (s : Bool) : H.fn (flip s a)=flip s (H.fn a) := by
  cases s
  · rfl
  · exact H.hneg va
theorem eqRead (H : SigHom) (v : List Sig) (i : Nat) : H.fn (v.getD i zero)=(v.map H.fn).getD i zero := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : v[i]? with
  | none => exact H.hzero
  | some a => rfl
theorem eqOp (H : SigHom) {v : List Sig} (va : ∀a∈v,Valid a) (code) :
    H.fn (op code v)=op code (v.map H.fn) := by
  unfold op
  rw [eqFlip H (valid_bin (vf _ (valid_getD va _)) (vf _ (valid_getD va _))),H.hbin,
      eqFlip H (valid_getD va _),eqFlip H (valid_getD va _),eqRead,eqRead]
theorem eqTape (H : SigHom) (cs : List Nat) {v : List Sig} (va : ∀a∈v,Valid a) :
    (eval cs v).2.map H.fn=(eval cs (v.map H.fn)).2 := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    have va' := List.forall_mem_cons.mpr ⟨op_valid va c,va⟩
    simp only [eval,←eqOp H va,←List.map_cons]
    exact ih va'
end Tape8403
end
section
open Basis1868 Free1868 Cuts1868
open Projection8403 Exact8403 Tape8403
namespace Leaf8403
def pick (idx : List Nat) (v : List Sig) := idx.map (fun i=>v.getD i zero)
def dead (v : List Sig) := v.countP (fun a=>decide (constant a))
def rank (lb : Nat) (raw : List Sig) := ∀q,Can q (close raw) → lb≤q
def check (budget lb : Nat) (raw : List Sig) (cs idx : List Nat) :=
  let out:=Tape8403.eval cs raw
  decide (budget+out.1 < lb+dead (pick idx out.2))
theorem eqPick (H : SigHom) (idx : List Nat) (v : List Sig) :
    (pick idx v).map H.fn=pick idx (v.map H.fn) := by
  simp only [pick,List.map_map,Function.comp_def,eqRead]
theorem pick_close (idx : List Nat) (v : List Sig) : (pick idx v).toFinset⊆close v := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact memRead v i
theorem massEq (H : SigHom) {v : List Sig} (nd : v.Nodup) : mass H v.toFinset=dead (v.map H.fn) := by
  induction v with
  | nil => simp [mass,dead]
  | cons a v ih =>
    obtain ⟨fresh,nd⟩:=List.nodup_cons.mp nd
    rw [List.toFinset_cons,massInsert,ih nd]
    have fresh' : a∉v.toFinset:=by simpa using fresh
    simp only [fresh',not_false_eq_true,true_and,List.map_cons,dead,List.countP_cons]
    by_cases hc : constant (H.fn a) <;> simp [hc]
theorem checked {H : SigHom} {full raw : List Sig} (same : full.map H.fn=raw) (va : ∀a∈full,Valid a)
    {lb budget : Nat} (lower : rank lb raw) {cs idx : List Nat} (ok : check budget lb raw cs idx=true)
    {k t : Nat} (h : Live k t (pick idx (Tape8403.eval cs full).2).toFinset)
    (nd : (pick idx (Tape8403.eval cs full).2).Nodup) : budget+t<k := by
  let big:=(Tape8403.eval cs full).2
  let small:=Tape8403.eval cs raw
  have ev : big.map H.fn=small.2:=by change (Tape8403.eval cs full).2.map H.fn=(Tape8403.eval cs raw).2;rw [←same];exact eqTape H cs va
  have eq : (pick idx big).map H.fn=pick idx small.2 := by rw [eqPick,ev]
  have vraw : ∀a∈raw,Valid a := by
    rw [←same]
    intro a ha
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
    exact H.valid x
  obtain ⟨q,lim,prog⟩:=projected h H
  have used : (pick idx big).toFinset.image H.fn⊆close small.2 := by
    intro a ha
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    have mem:=List.mem_map_of_mem (f:=H.fn) (List.mem_toFinset.mp hx)
    rw [eq] at mem
    exact pick_close idx small.2 (List.mem_toFinset.mpr mem)
  have possible:=mono prog (Nat.le_refl _) used
  have cap:=lower _ (rewindTape vraw possible)
  have massEq':=massEq H nd
  change mass H (pick idx big).toFinset=dead ((pick idx big).map H.fn) at massEq'
  rw [eq] at massEq'
  change q+mass H (pick idx big).toFinset+t≤k at lim
  rw [massEq'] at lim
  have tested : budget+small.1<lb+dead (pick idx small.2):=of_decide_eq_true ok
  change lb≤q+small.1 at cap
  omega
theorem signed {H : SigHom} {full raw : List Sig} (same : full.map H.fn=raw) (va : ∀a∈full,Valid a)
    {lb budget : Nat} (lower : rank lb raw) {cs idx : List Nat} (ok : check budget lb raw cs idx=true)
    (nd : (pick idx (Tape8403.eval cs full).2).Nodup) : excluded budget (pick idx (Tape8403.eval cs full).2) := by
  intro k cap live
  obtain ⟨t,exp⟩:=live.expand
  have bad:=checked same va lower ok exp nd
  omega
theorem subset_can_close {v : List Sig} (va : ∀a∈v,Valid a) : (close v).image can⊆insert zero (v.map can).toFinset := by
  intro a ha
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
  simp only [close,Finset.mem_insert,Finset.mem_union,Finset.mem_image,List.mem_toFinset] at hb
  rcases hb with rfl|rfl|bv|⟨w,hw,rfl⟩
  · exact can_zero ▸ Finset.mem_insert_self ..
  · exact can_one ▸ Finset.mem_insert_self ..
  · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem bv))
  · rw [can_neg (va _ hw)]
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hw))
theorem known {k : Nat} {base raw : List Sig} (e : excluded k base) (ns : necessary base) (va : ∀a∈raw,Valid a)
    (sub : (raw.map can).toFinset⊆insert zero base.toFinset) : rank (k+1) raw := by
  intro q h
  obtain ⟨m,t,S,fee,run,contains⟩:=h
  obtain ⟨j,T,lim,bl,ss⟩:=compress run
  have incl : T⊆base.toFinset := by
    intro x hx
    have nz := (bl.forms x hx).1.2.1
    have h:=subset_can_close va ((ss.trans (Finset.image_mono _ contains)) hx)
    exact (Finset.mem_insert.mp (sub ((Finset.mem_insert.mp h).resolve_left nz))).resolve_left nz
  obtain ⟨u,pl⟩:=bl.expand
  rw [allNeeded pl incl ns] at bl
  by_contra! hh
  exact e j (by omega) bl
end Leaf8403
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open Projection8403 Tape8403 Leaf8403 QuickQ
namespace TableLeafQ
abbrev Desc := List Nat × List Nat
def body (full : List Sig) (d : Desc) := pick d.2 (Tape8403.eval d.1 full).2
structure Minor (full : List Sig) where
  raw : List Sig
  lb : Nat
  h : ∃H : SigHom,full.map H.fn=raw ∧ rank lb raw
end TableLeafQ
end
section
open Basis1868 Projection8403 Tape8403
namespace Mono8403
def possible (n : Nat) (V : Finset Sig) := ∃k U,k≤n ∧ Live k 0 U ∧ U⊆V
def closed (v : List Sig) := insert zero (insert one v.toFinset)
lemma widen {k l : Nat} {U V : Finset Sig} (h : possible k U) (le : k≤l) (ss : U⊆V) : possible l V := by
  obtain ⟨j,S,c,l',s⟩:=h;exact ⟨j,S,c.trans le,l',s.trans ss⟩
lemma free {q U a} (rep : represented U.toList a) (out : possible q (insert a U)) : possible q U := by
  obtain ⟨k,S,le,l,ss⟩:=out
  refine ⟨k,S,le,l,?_⟩
  intro w hw
  rcases Finset.mem_insert.mp (ss hw) with rfl|hv
  · exact Finset.mem_toList.mp (rep.resolve_right (fun ht=>ht (live_proper l _ hw)))
  · exact hv
lemma pay {q U a b} (d : Bool) (va : Valid a) (vb : Valid b) (ha : a∈U) (hb : b∈U)
    (out : possible q (insert (bin d a b) U)) : possible (q+1) U := by
  let z:=bin d a b
  by_cases already : z∈U
  · exact widen out (by omega) (Finset.insert_subset already (Finset.Subset.refl _))
  obtain ⟨k,S,le,l,ss⟩:=out
  by_cases used : z∈S
  · have properZ := live_proper l z used
    have noConst : ¬(constant a ∨ constant b) := by
      intro hc
      rcases constResult va vb d hc with (h|h)|h|h
      · exact properZ.2.1 h
      · exact properZ.2.2 h
      · exact already (by simpa only [z,h] using ha)
      · exact already (by simpa only [z,h] using hb)
    have pa : proper a:=⟨va,fun eq=>noConst (Or.inl (Or.inl eq)),fun eq=>noConst (Or.inl (Or.inr eq))⟩
    have pb : proper b:=⟨vb,fun eq=>noConst (Or.inr (Or.inl eq)),fun eq=>noConst (Or.inr (Or.inr eq))⟩
    have ab : a≠b := by
      intro e;subst b
      obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws va
      cases d
      · exact already (by simpa only [z,aa] using ha)
      · exact already (by simpa only [z,aa'] using ha)
    let T:=S.erase z
    have drop : T⊆U := by
      intro y hy
      exact (Finset.mem_insert.mp (ss (Finset.mem_erase.mp hy).2)).resolve_left (Finset.mem_erase.mp hy).1
    have fresh : z∉insert a (insert b T) := fun hz=>already ((Finset.insert_subset ha (Finset.insert_subset hb drop)) hz)
    have tail : Live k 0 (insert z T) := by simpa [T,Finset.insert_erase used] using l
    exact ⟨k+1,_,by omega,Live.binary pa pb ab fresh tail,Finset.insert_subset ha (Finset.insert_subset hb drop)⟩
  · exact ⟨k,S,by omega,l,fun x hx=>(Finset.mem_insert.mp (ss hx)).resolve_left (fun e=>used (by simpa only [z,←e] using hx))⟩
theorem projected {k t S} (h : Live k t S) (ht : t=0) (H : SigHom) :
    ∃q,q+mass H S≤k ∧ possible q (S.image H.fn) := by
  induction h with
  | stop =>
    have nc : ¬constant target:=by rintro (e|e);exact target_proper.2.1 e;exact target_proper.2.2 e
    exact ⟨0,by simp [mass,H.htarget,nc],0,{target},by omega,Live.stop,by simp [H.htarget]⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab fresh tail ih =>
    obtain ⟨q,cap,can⟩:=ih ht
    let big:=(insert a (insert b U)).image H.fn
    have ax : H.fn a∈big:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
    have bx : H.fn b∈big:=Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have sub : (insert (bin d a b) U).image H.fn ⊆ insert (bin d (H.fn a) (H.fn b)) big := by
      rw [Finset.image_insert,H.hbin]
      exact Finset.insert_subset_insert _ (Finset.image_mono _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..)))
    have en:=widen can (Nat.le_refl _) sub
    have budget:=massBin (H:=H) d ab fresh
    by_cases c : constant (H.fn a) ∨ constant (H.fn b)
    · rw [ite_eq_left c] at budget
      exact ⟨q,by omega,free (constFree (H.valid a) (H.valid b) ax bx d c) en⟩
    · rw [ite_eq_right c] at budget
      exact ⟨q+1,by omega,pay d (H.valid a) (H.valid b) ax bx en⟩
end Mono8403
end
section
open Basis1868 Projection8403 Tape8403 Leaf8403 Exact8403
namespace Mono8403
def gate (code : Nat) (v : List Sig) :=
  bin (code.testBit 2) (v.getD (code/1024) zero) (v.getD (code/16 % 64) zero)
def process : List Nat→List Sig→Nat×List Sig
  | [],v=>(0,v)
  | c::cs,v=>
    let z:=gate c v
    let result:=process cs (z::v)
    ((if z∈closed v then 0 else 1)+result.1,result.2)
def level (m : Nat) (v : List Sig) := ∀q,possible q (closed v) → m≤q
def rejects (k : Nat) (v : List Sig) := ∀j≤k,¬Live j 0 v.toFinset
theorem gate_valid {v : List Sig} (va : ∀a∈v,Valid a) (c) : Valid (gate c v) := valid_bin (valid_getD va _) (valid_getD va _)
theorem read_closed (w : List Sig) (i : Nat) : w.getD i zero∈closed w := by
  by_cases h : i<w.length
  · simp [closed,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)];simp [closed]
theorem closed_cons (z : Sig) (v : List Sig) : closed (z::v)=insert z (closed v) := by ext y;simp [closed,or_left_comm]
theorem back {cs : List Nat} {v : List Sig} (va : ∀a∈v,Valid a) {q}
    (tail : possible q (closed (process cs v).2)) : possible (q+(process cs v).1) (closed v) := by
  induction cs generalizing v with
  | nil => simpa [process] using tail
  | cons x xs ih =>
    have va' : ∀a∈gate x v::v,Valid a:=List.forall_mem_cons.mpr ⟨gate_valid va x,va⟩
    have p:=ih va' tail
    rw [closed_cons] at p
    by_cases h : gate x v∈closed v
    · simpa only [process,ite_eq_left h,Nat.zero_add,Finset.insert_eq_of_mem h] using p
    · have z:=pay (x.testBit 2) (valid_getD va _) (valid_getD va _) (read_closed v (x/1024)) (read_closed v (x/16 % 64)) p
      simpa only [process,ite_eq_right h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using z
theorem process_map (H : SigHom) (cs : List Nat) (v : List Sig) :
    (process cs v).2.map H.fn=(process cs (v.map H.fn)).2 := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    have e : H.fn (gate c v)=gate c (v.map H.fn):=by unfold gate;rw [H.hbin,eqRead,eqRead]
    simp only [process,←e,←List.map_cons]
    exact ih _
def checkCut (k lb : Nat) (raw : List Sig) (cs idx : List Nat) :=
  let out:=process cs raw
  decide (k+out.1 < lb+dead (pick idx out.2))
theorem checked0 {H : SigHom} {full raw : List Sig} (same : full.map H.fn=raw) (va : ∀a∈full,Valid a)
    {lb k : Nat} (lower : level lb raw) {cs idx : List Nat} (ok : checkCut k lb raw cs idx=true)
    (nd : (pick idx (process cs full).2).Nodup) : rejects k (pick idx (process cs full).2) := by
  intro j cap live
  let big:=(process cs full).2
  let small:=process cs raw
  have ev : big.map H.fn=small.2:=by change (process cs full).2.map H.fn=(process cs raw).2;rw [←same];exact process_map H cs full
  have eq : (pick idx big).map H.fn=pick idx small.2 := by rw [eqPick,ev]
  have vraw : ∀a∈raw,Valid a := by
    rw [←same];intro a ha;obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha;exact H.valid x
  obtain ⟨q,lim,prog⟩:=projected live rfl H
  have used : (pick idx big).toFinset.image H.fn⊆closed small.2 := by
    intro a ha
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    have mem:=List.mem_map_of_mem (f:=H.fn) (List.mem_toFinset.mp hx)
    rw [eq] at mem
    obtain ⟨i,hi,hit⟩:=List.mem_map.mp mem
    rw [←hit]
    exact read_closed _ _
  have prior:=lower _ (back vraw (widen prog (Nat.le_refl _) used))
  have size:=massEq H nd
  change mass H (pick idx big).toFinset=dead ((pick idx big).map H.fn) at size
  rw [eq] at size
  change q+mass H (pick idx big).toFinset≤j at lim
  rw [size] at lim
  have tested : k+small.1<lb+dead (pick idx small.2):=of_decide_eq_true ok
  change lb≤q+small.1 at prior
  omega
theorem level_of_rank {m raw} (r : rank m raw) : level m raw := by
  intro q h
  obtain ⟨k,S,cap,l,sub⟩:=h
  apply r q
  refine ⟨k,0,S,by omega,l,sub.trans ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact Finset.mem_insert_self ..
  · rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    · exact memClose (List.mem_toFinset.mp hx)
theorem known0 {k : Nat} {base raw : List Sig} (e : rejects k base) (ns : necessary base)
    (sub : raw.toFinset⊆closed base) : level (k+1) raw := by
  intro q h
  obtain ⟨j,S,cap,l,ss⟩:=h
  have incl : S⊆base.toFinset := by
    intro x hx
    have p:=live_proper l x hx
    have v:=ss hx
    have q0 : x∉({zero,one}:Finset Sig):=by simpa using And.intro p.2.1 p.2.2
    rcases Finset.mem_insert.mp v with z|v
    · exact False.elim (p.2.1 z)
    · rcases Finset.mem_insert.mp v with z|v
      · exact False.elim (p.2.2 z)
      · have j0:=sub v
        rcases Finset.mem_insert.mp j0 with z|j0
        · exact False.elim (p.2.1 z)
        · rcases Finset.mem_insert.mp j0 with z|j0
          · exact False.elim (p.2.2 z)
          · simpa using j0
  rw [allNeeded l incl ns] at l
  by_contra! small
  exact e j (by omega) l
end Mono8403
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open PEqualNP.Outside.L_meta_11002_aux.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
open PEqualNP.Outside.L_meta_11002_aux.ColorSearch1868 (paint paint_ok)
namespace QuickQ
theorem testMono {c : Chart} (hg : good c) {k m v} (hm : m≤k) (nd : v.Nodup) (h : Live m 0 v.toFinset) :
    test c false (k+2-v.length) v=true := by
  have val : ∀a∈v,Valid a:=fun a ha=>(live_proper h _ (List.mem_toFinset.mpr ha)).1
  obtain ⟨n,⟨f,bd,ok⟩,le⟩:=PEqualNP.Outside.L_meta_11002_aux.Mono1868.live_colored h rfl
  have sz : v.toFinset.card=v.length:=List.toFinset_card_of_nodup nd
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_and,roofBit]
    by_cases hi : i<area c
    · let z : Fin (area c):=⟨i,hi⟩
      obtain ⟨a,ha,hit⟩:=PEqualNP.Outside.L_meta_11002_aux.Mono1868.pair_sep h rfl (positive c z) (negative c z)
      have av:=List.mem_toFinset.mp ha
      have hit':=multiOne (List.mem_map_of_mem (f:=diff c false) av) i ((diffBit hg false (val a av) z).2 hit)
      simpa [hi,signs] using hit'
    · simp [hi]
  · change paint (k+2-v.length) (entries c false v) _ =true
    apply paint_ok _ f
    · rwa [entryIds]
    · intro a ha;have := bd _ (List.mem_toFinset.mpr (hasEntry ha));omega
    · simp
    · intro a ha b hb ne eq
      by_contra non
      obtain ⟨p,q,x,y⟩:=overlap hg val ha hb non
      apply ok _ (List.mem_toFinset.mpr (hasEntry ha)) _ (List.mem_toFinset.mpr (hasEntry hb)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,PEqualNP.Outside.L_meta_11002_aux.Mono1868.Mark,PEqualNP.Outside.L_meta_11002_aux.Mono1868.Unique,PEqualNP.Outside.L_meta_11002_aux.Mono1868.D,PEqualNP.Outside.L_meta_11002_aux.Mono1868.pos,PEqualNP.Outside.L_meta_11002_aux.Mono1868.P,PEqualNP.Outside.L_meta_11002_aux.Mono1868.N,bit] using x,by simpa [DS,M,U,PEqualNP.Outside.L_meta_11002_aux.Mono1868.Mark,PEqualNP.Outside.L_meta_11002_aux.Mono1868.Unique,PEqualNP.Outside.L_meta_11002_aux.Mono1868.D,PEqualNP.Outside.L_meta_11002_aux.Mono1868.pos,PEqualNP.Outside.L_meta_11002_aux.Mono1868.P,PEqualNP.Outside.L_meta_11002_aux.Mono1868.N,bit] using y⟩
end QuickQ

namespace Mono8403
def choice (go : List Sig→Bool) (v : List Sig) (a b : Sig) := [false,true].any fun d=>
  let z:=bin d a b
  z != zero && z != one && !(v.contains z) &&
    ([false,true].any fun u=>[false,true].any fun t=>go (next v a b z u t))
theorem oneStep0 {k S} (l : Live k 0 S) (m : Nat) (hm : k≤m+1) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset=S) (go : List Sig→Bool)
    (hyp : ∀w,w.Nodup → ∀j≤m,Live j 0 w.toFinset → go w=true) :
    (v==[target] || scanPairs (choice go v) v)=true := by
  cases l with
  | stop =>
    have hv : v=[target]:=List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v
    simp
  | @binary j _ U a b d ha hb ab fresh tail =>
    let z:=bin d a b
    have va : a∈v:=List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b∈v:=List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (eq : bin d x y=z) (eS : v.toFinset=insert x (insert y U)) : choice go v x y=true := by
      apply anyBool d
      have prop:=live_proper tail z (Finset.mem_insert_self ..)
      have nv : z∉v:=fun h=>fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z)=true:=by simpa using nv
      simp only [eq,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨⟨prop.2.1,prop.2.2⟩,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z∉insert x (insert y U):=fun hh=>nv (List.mem_toFinset.mp (eS ▸ hh))
      obtain ⟨nw,pw⟩:=tailState nd eS fr
      exact hyp _ nw j (by omega) (pw ▸ tail)
    apply Bool.or_eq_true_iff.mpr
    right
    apply scanPairs_complete _ va vb ab
    · exact yes a b rfl rep
    · exact yes b a (bin_comm ..) (by rwa [Finset.insert_comm b a])
end Mono8403
end
section
open Basis1868 Free1868 Cuts1868
open Projection8403 Tape8403 Leaf8403 TableLeafQ QuickQ
namespace Cheap8403
def seen (v : List Sig) (z : Sig) := z==zero || z==one || v.contains z || v.contains (neg z)
theorem seen_ok (v : List Sig) (z : Sig) : seen v z=true ↔ z∈close v := by
  simp only [seen,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem,close,Finset.mem_insert,Finset.mem_union,Finset.mem_image,List.mem_toFinset]
  constructor
  · rintro (((h|h)|h)|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨neg z,h,neg2 z⟩))
  · rintro (h|h|h|⟨y,hy,rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (by simpa only [neg2] using hy)
def run : List Nat→List Sig→Nat×List Sig
  | [],v=>(0,v)
  | c::cs,v=>
    let z:=op c v
    let r:=run cs (z::v)
    ((if seen v z then 0 else 1)+r.1,r.2)
theorem run_eq (cs : List Nat) (v : List Sig) : run cs v=Tape8403.eval cs v := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih => simp only [run,ih,Tape8403.eval,seen_ok]
def testMinor (budget lb : Nat) (raw : List Sig) (d : Desc) :=
  let r:=run d.1 raw
  decide (budget+r.1<lb+dead (pick d.2 r.2))
theorem testMinor_ok (budget lb : Nat) (raw : List Sig) (d : Desc) :
    testMinor budget lb raw d=Leaf8403.check budget lb raw d.1 d.2 := by simp only [testMinor,Leaf8403.check,run_eq]
end Cheap8403
end
section
namespace Deck8403
def getWord (n bits i : Nat) := (n >>> (bits*i)) % 2^bits
end Deck8403
end
section
open Basis1868
open Mono8403
namespace MonoWord8403
structure Slice (full : List Sig) where
  raw : List Sig
  lb : Nat
  sound : ∃H : SigHom,full.map H.fn=raw ∧ level lb raw
end MonoWord8403
end
section
open Basis1868 Leaf8403 TableLeafQ Mono8403
namespace MonoDeck8403
def fromDesc (full : List Sig) (d : Desc) :=
  pick d.2 (process d.1 full).2
end MonoDeck8403
end
section
open Basis1868 Free1868 Cuts1868 Sym1868 Moves3400
open Tape8403 Leaf8403 TableLeafQ
namespace RotateQ
structure Rot (full : List Sig) where
  raw : List Sig
  H : SigHom
  J : SigHom
  fwd : full.map H.fn=raw
  bwd : raw.map J.fn=full
def goodList (H J : SigHom) (v : List Sig) := ∀a∈v,J.fn (H.fn a)=a
theorem goodMap {H J : SigHom} {v w : List Sig} (eq : v.map H.fn=w) (back : w.map J.fn=v) : goodList H J v := by
  subst w
  induction v with
  | nil => simp [goodList]
  | cons a v ih =>
    simp only [List.map_cons,List.cons.injEq] at back
    exact List.forall_mem_cons.mpr ⟨back.1,ih back.2⟩
theorem signedBody (H : SigHom) {v : List Sig} (va : ∀a∈v,Valid a) (d : Desc) : (body v d).map H.fn=body (v.map H.fn) d := by
  simp only [body,eqPick,eqTape H _ va]
theorem monoBody (H : SigHom) (v : List Sig) (d : Desc) : (MonoDeck8403.fromDesc v d).map H.fn=MonoDeck8403.fromDesc (v.map H.fn) d := by
  simp only [MonoDeck8403.fromDesc,eqPick,Mono8403.process_map]
lemma vr {full : List Sig} (r : Rot full) : ∀a∈r.raw,Valid a := by
  rw [←r.fwd]
  intro a ha;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha;exact r.H.valid b
theorem doS {v : List Sig} (va : ∀a∈v,Valid a) (r : Rot v) (f : SignFixed r.J) (d : Desc) {k}
    (h : excluded k (body v d)) : excluded k (body r.raw d) := by
  have j : (body r.raw d).map r.J.fn=body v d:=by rw [signedBody r.J (vr r),r.bwd]
  have i : (body v d).map r.H.fn=body r.raw d:=by rw [signedBody r.H va,r.fwd]
  apply move r.J r.H f (by rw [j]) _ h
  exact List.all_eq_true.mpr (fun a ha=>decide_eq_true (goodMap j i a ha))
theorem mapLive {H J : SigHom} {k t S} (l : Live k t S) (good : ∀a∈S,Good H J a) : Live k t (S.image H.fn) := by
  induction l with
  | stop => simpa only [Finset.image_singleton,H.htarget] using Live.stop
  | @unary k t U a ha fresh tail ih =>
    have ga:=good a (Finset.mem_insert_self ..)
    have gz:=goodNeg ga
    have gu (x) (hx : x∈U) := good x (Finset.mem_insert_of_mem hx)
    have hh:=ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,H.hneg ha.1] at hh
    rw [Finset.image_insert]
    apply Live.unary (properH ga ha) _ hh
    rw [←H.hneg ha.1,←Finset.image_insert]
    intro mem
    obtain ⟨u,hu,eu⟩:=Finset.mem_image.mp mem
    exact fresh (inj (good _ hu) gz eu ▸ hu)
  | @binary k t U a b d ha hb ab fresh tail ih =>
    have ga:=good a (Finset.mem_insert_self ..)
    have gb:=good b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have gz:=goodBin (d:=d) ga gb
    have gu (x) (hx : x∈U) := good x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have hh:=ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,H.hbin] at hh
    rw [Finset.image_insert,Finset.image_insert]
    apply Live.binary (properH ga ha) (properH gb hb) (fun e=>ab (inj ga gb e)) _ hh
    rw [←H.hbin,←Finset.image_insert,←Finset.image_insert]
    intro mem
    obtain ⟨u,hu,eu⟩:=Finset.mem_image.mp mem
    exact fresh (inj (good _ hu) gz eu ▸ hu)
theorem doM {v : List Sig} (r : Rot v) (d : Desc) {k} (h : Mono8403.rejects k (MonoDeck8403.fromDesc v d)) :
    Mono8403.rejects k (MonoDeck8403.fromDesc r.raw d) := by
  have j : (MonoDeck8403.fromDesc r.raw d).map r.J.fn=MonoDeck8403.fromDesc v d:=by rw [monoBody,r.bwd]
  have i : (MonoDeck8403.fromDesc v d).map r.H.fn=MonoDeck8403.fromDesc r.raw d:=by rw [monoBody,r.fwd]
  intro n cap l
  have run:=mapLive (H:=r.J) (J:=r.H) l (fun a ha=>⟨(live_proper l _ ha).1,goodMap j i a (List.mem_toFinset.mp ha)⟩)
  apply h n cap
  have eq : (MonoDeck8403.fromDesc r.raw d).toFinset.image r.J.fn=(MonoDeck8403.fromDesc v d).toFinset := by
    rw [←j];ext y;simp
  rwa [eq] at run
end RotateQ
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open Projection8403 Tape8403 Leaf8403 TableLeafQ QuickQ
namespace OrbitQ

structure Rows where
  count : Nat
  desc : Nat→Desc
  kinds : Nat
  refs : Nat
  keys : Nat
  indices : Nat
  indexWidth : Nat
def getWord := Deck8403.getWord
def label (r : Rows) (i : Nat) := getWord r.kinds 5 i
def keyAt (r : Rows) (i : Nat) := getWord r.keys 23 i
def idx (r : Rows) (i : Nat) := getWord r.indices r.indexWidth i
def compact (n depth code : Nat) : Desc :=
  let cs:=(List.range depth).map fun i=>
    let c:=getWord code 12 i
    (c/256)*1024+(c/16 % 16)*16+c % 16
  let mask:=code >>> (12*depth)
  (cs,(List.range (n+depth)).filter mask.testBit)
def table (n depth cnt width codes kinds refs keys ids bits : Nat) : Rows :=
  ⟨cnt,fun i=>compact n depth (getWord codes width i),kinds,refs,keys,ids,bits⟩
def empty : Rows := ⟨0,fun _=>([],[]),0,0,0,0,0⟩
def search (t : Rows) (h : Nat) : Nat→Nat→Nat→Nat
  | 0,l,_=>l
  | n+1,l,r=>if l≥r then l else
    let m:=(l+r)/2
    if keyAt t m<h then search t h n (m+1) r else search t h n l m
open RotateQ
def all (full : List Sig) (k : Nat) (old : Rows) := ∀i : Fin old.count,
    let v:=body full (old.desc i.val)
    v.Nodup → excluded k v
def matchCode {full : List Sig} (R : Nat→Rot full) (old : Rows) (v : List Sig) :=
  let h:=key v % 8388607
  let i:=search old h (old.refs.log2+2) 0 old.refs
  let ref:=idx old i
  i<old.refs && ref/8<old.count && incl v (body (R (ref % 8)).raw (old.desc (ref/8)))
theorem matchFalse {full : List Sig} {k : Nat} {old : Rows} {v : List Sig} (R : Nat→Rot full) (va : ∀a∈full,Valid a) (fr : ∀r,PEqualNP.Outside.L_meta_11002_aux.Moves3400.SignFixed (R r).J) (prior : all full k old)
    (nd : v.Nodup) (h : ∃j≤k,BL j v.toFinset) : matchCode R old v=false := by
  obtain ⟨j,hj,run⟩:=h
  apply Bool.eq_false_iff.mpr
  intro yes
  let i:=search old (key v % 8388607) (old.refs.log2+2) 0 old.refs
  let ref:=idx old i
  let r:=R (ref % 8)
  let d:=old.desc (ref/8)
  let w:=body r.raw d
  have inc : (i<old.refs && ref/8<old.count && incl v w)=true:=yes
  obtain ⟨ok,yes⟩:=Bool.and_eq_true_iff.mp inc
  have bound : ref/8<old.count:=of_decide_eq_true (Bool.and_eq_true_iff.mp ok).2
  have eql:=inclEq nd yes
  have size:=beq_iff_eq.mp (Bool.and_eq_true_iff.mp yes).1
  have nw : w.Nodup:=by
    change (↑w : Multiset Sig).Nodup
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    change w.toFinset.card=w.length
    rw [←eql,List.toFinset_card_of_nodup nd,size]
  have dir : (body full d).map r.H.fn=w:=by rw [signedBody r.H va d,r.fwd]
  have orig : (body full d).Nodup:=List.Nodup.of_map r.H.fn (dir ▸ nw)
  exact doS va r (fr _) d (prior ⟨ref/8,bound⟩ orig) j hj (eql ▸ run)
def guardFlat {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  v.length≤k+1 && test c true (k+2-v.length) v && !matchCode R old v
def nextFlat {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  !(baseTest v || scanPairs (pairB v (guardFlat R c k old)) v)
theorem next_ok {full : List Sig} {c : Chart} (hg : good c) (R : Nat→Rot full) (va : ∀a∈full,Valid a) (fr : ∀r,PEqualNP.Outside.L_meta_11002_aux.Moves3400.SignFixed (R r).J) {k : Nat} {old : Rows} {v : List Sig}
    (pr : all full k old) (nd : v.Nodup) (no : nextFlat R c k old v=true) : excluded (k+1) v := by
  intro n hn live
  have yes:=oneStep live k hn v nd rfl (guardFlat R c k old) (by
    intro w dw j jk h
    obtain ⟨t,lh⟩:=h.expand
    have lim:=live_size lh
    rw [List.toFinset_card_of_nodup dw] at lim
    simp only [guardFlat,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨by omega,testSigned hg jk dw h⟩,by rw [matchFalse R va fr pr dw ⟨j,jk,h⟩];rfl⟩)
  change !(baseTest v || scanPairs (pairB v (guardFlat R c k old)) v)=true at no
  rw [yes] at no
  contradiction
def assess {full : List Sig} (R : Nat→Rot full) (c : Chart) (old : Rows) (m : Minor full) (kind k : Nat) (d : Desc) :=
  let v:=body full d
  if kind=0 then nextFlat R c (k-1) old v
  else Cheap8403.testMinor k m.lb m.raw d
def checkAt {full : List Sig} (R : Nat→Rot full) (c : Chart) (old : Rows)
    (m : Minor full) (ms : Array (Minor full)) (k : Nat) (tab : Rows) (i : Nat) :=
  let kind:=label tab i
  assess R c old (ms.getD (kind-1) m) kind k (tab.desc i)
theorem finish {full : List Sig} {c : Chart} (hg : good c) (va : ∀a∈full,Valid a) (R : Nat→Rot full) (fr : ∀r,PEqualNP.Outside.L_meta_11002_aux.Moves3400.SignFixed (R r).J)
    {k : Nat} {old : Rows} (pr : all full k old) (m : Minor full) (ms : Array (Minor full))
    (tab : Rows) (h : ∀i : Fin tab.count,checkAt R c old m ms (k+1) tab i=true) : all full (k+1) tab := by
  intro i
  change (body full (tab.desc i.val)).Nodup → _
  intro nd
  have ok:=h i
  let kind:=label tab i.val
  let minor:=ms.getD (kind-1) m
  change assess R c old minor kind (k+1) (tab.desc i.val)=true at ok
  by_cases z : kind=0
  · exact next_ok hg R va fr pr nd (by simpa only [assess,z,ite_true,Nat.add_sub_cancel] using ok)
  · simp only [assess,ite_eq_right z,Cheap8403.testMinor_ok] at ok
    obtain ⟨H,eq,lb⟩:=minor.h
    exact signed eq va lb ok nd

namespace Mono
open Mono8403
open MonoDeck8403 (fromDesc)
open MonoWord8403 (Slice)
def all (full : List Sig) (k : Nat) (old : Rows) := ∀i : Fin old.count,
    let v:=fromDesc full (old.desc i.val)
    v.Nodup → rejects k v
def matchCode {full : List Sig} (R : Nat→Rot full) (old : Rows) (v : List Sig) :=
  let h:=key v % 8388607
  let i:=search old h (old.refs.log2+2) 0 old.refs
  let ref:=idx old i
  i<old.refs && ref/8<old.count && incl v (fromDesc (R (ref % 8)).raw (old.desc (ref/8)))
theorem matchFalse {full : List Sig} {k : Nat} {old : Rows} {v : List Sig} (R : Nat→Rot full)  (prior : all full k old)
    (nd : v.Nodup) (h : ∃j≤k,Live j 0 v.toFinset) : matchCode R old v=false := by
  obtain ⟨j,hj,run⟩:=h
  apply Bool.eq_false_iff.mpr
  intro yes
  let i:=search old (key v % 8388607) (old.refs.log2+2) 0 old.refs
  let ref:=idx old i
  let r:=R (ref % 8)
  let d:=old.desc (ref/8)
  let w:=fromDesc r.raw d
  have inc : (i<old.refs && ref/8<old.count && incl v w)=true:=yes
  obtain ⟨ok,yes⟩:=Bool.and_eq_true_iff.mp inc
  have bound : ref/8<old.count:=of_decide_eq_true (Bool.and_eq_true_iff.mp ok).2
  have eql:=inclEq nd yes
  have size:=beq_iff_eq.mp (Bool.and_eq_true_iff.mp yes).1
  have nw : w.Nodup:=by
    change (↑w : Multiset Sig).Nodup
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    change w.toFinset.card=w.length
    rw [←eql,List.toFinset_card_of_nodup nd,size]
  have dir : (fromDesc full d).map r.H.fn=w:=by rw [monoBody r.H full d,r.fwd]
  have orig : (fromDesc full d).Nodup:=List.Nodup.of_map r.H.fn (dir ▸ nw)
  exact doM r d (prior ⟨ref/8,bound⟩ orig) j hj (eql ▸ run)
def guardFlat {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  v.length≤k+1 && test c false (k+2-v.length) v && !matchCode R old v
def nextFlat {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  !(v==[target] || scanPairs (choice (guardFlat R c k old) v) v)
theorem next_ok {full : List Sig} {c : Chart} (hg : good c) (R : Nat→Rot full)  {k : Nat} {old : Rows} {v : List Sig}
    (pr : all full k old) (nd : v.Nodup) (no : nextFlat R c k old v=true) : rejects (k+1) v := by
  intro n hn live
  have yes:=oneStep0 live k hn v nd rfl (guardFlat R c k old) (by
    intro w dw j jk h
    have lim:=live_size h
    rw [List.toFinset_card_of_nodup dw] at lim
    simp only [guardFlat,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨by omega,testMono hg jk dw h⟩,by rw [matchFalse R pr dw ⟨j,jk,h⟩];rfl⟩)
  change !(v==[target] || scanPairs (choice (guardFlat R c k old) v) v)=true at no
  rw [yes] at no
  contradiction
def assess {full : List Sig} (R : Nat→Rot full) (c : Chart) (old : Rows) (m : Slice full) (kind k : Nat) (d : Desc) :=
  let v:=fromDesc full d
  if kind=0 then nextFlat R c (k-1) old v
  else checkCut k m.lb m.raw d.1 d.2
def checkAt {full : List Sig} (R : Nat→Rot full) (c : Chart) (old : Rows)
    (m : Slice full) (ms : Array (Slice full)) (k : Nat) (tab : Rows) (i : Nat) :=
  let kind:=label tab i
  assess R c old (ms.getD (kind-1) m) kind k (tab.desc i)
theorem finish {full : List Sig} {c : Chart} (hg : good c) (va : ∀a∈full,Valid a) (R : Nat→Rot full)
    {k : Nat} {old : Rows} (pr : all full k old) (m : Slice full) (ms : Array (Slice full))
    (tab : Rows) (h : ∀i : Fin tab.count,checkAt R c old m ms (k+1) tab i=true) : all full (k+1) tab := by
  intro i
  change (fromDesc full (tab.desc i.val)).Nodup → _
  intro nd
  have ok:=h i
  let kind:=label tab i.val
  let minor:=ms.getD (kind-1) m
  change assess R c old minor kind (k+1) (tab.desc i.val)=true at ok
  by_cases z : kind=0
  · exact next_ok hg R pr nd (by simpa only [fromDesc,assess,z,ite_true,Nat.add_sub_cancel] using ok)
  · simp only [assess,ite_eq_right z] at ok
    obtain ⟨H,eq,lb⟩:=minor.sound
    exact checked0 eq va lb ok nd
end Mono
end OrbitQ
end
section
namespace SpanQ
abbrev Block (P : Nat→Prop) (start n : Nat) := ∀i : Fin n,P (start+i.val)
theorem glue {P : Nat→Prop} {start a b : Nat} (x : Block P start a) (y : Block P (start+a) b) : Block P start (a+b) := by
  intro i
  by_cases h : i.val<a
  · exact x ⟨i.val,h⟩
  · have e:=y ⟨i.val-a,by omega⟩
    change P (start+a+(i.val-a)) at e
    rwa [show start+a+(i.val-a)=start+i.val by omega] at e
end SpanQ
end
section
open Basis1868 Projection8403 Mono8403
namespace Dominance8403
def below (a b : Sig) := (∀i,a.1.testBit i=true → b.1.testBit i=true) ∧
  (∀i,b.2.testBit i=true → a.2.testBit i=true)
lemma belowBin {a b c e : Sig} (s : Bool) (ac : below a c) (be : below b e) : below (bin s a b) (bin s c e) := by
  obtain ⟨p,n⟩:=ac
  obtain ⟨q,m⟩:=be
  cases s
  · constructor
    · intro i h
      simp [bin,Nat.testBit_and] at h ⊢
      exact ⟨p i h.1,q i h.2⟩
    · intro i h
      simp [bin,Nat.testBit_and] at h ⊢
      exact ⟨n i h.1,m i h.2⟩
  · constructor
    · intro i h
      simp [bin,Nat.testBit_or] at h ⊢
      exact h.imp (p i) (q i)
    · intro i h
      simp [bin,Nat.testBit_or] at h ⊢
      exact h.imp (n i) (m i)
lemma atTop {b : Sig} (va : Valid b) (h : below target b) : b=target := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i<414
    · have yes : top.testBit i=true:=by
        have e : top=2^414-1:=by decide
        rw [e,Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hi
      exact (h.1 i yes).trans yes.symm
    · exact (va.1 i (by omega)).trans (target_proper.1.1 i (by omega)).symm
  · apply Nat.eq_of_testBit_eq
    intro i
    cases e : b.2.testBit i with
    | false => simp [target]
    | true => exact (h.2 i e).symm
def amount (f : Sig→Sig) (U : Finset Sig) := (U.filter (fun a=>constant (f a))).card
lemma insertAmount (f : Sig→Sig) (a : Sig) (U : Finset Sig) :
    amount f (insert a U)=amount f U+(if a∉U ∧ constant (f a) then 1 else 0) := by
  classical
  by_cases h : a∈U
  · simp [h,Finset.insert_eq_of_mem h]
  · by_cases c : constant (f a)
    · simp [amount,Finset.filter_insert,h,c,Finset.card_insert_of_notMem]
    · simp [amount,Finset.filter_insert,h,c]
lemma congrAmount {f g : Sig→Sig} {U : Finset Sig} (h : ∀a∈U,f a=g a) : amount f U=amount g U := by
  unfold amount
  congr 1
  ext a
  simp only [Finset.mem_filter]
  exact and_congr_right (fun ha=>by rw [h a ha])
lemma gateBudget {f g : Sig→Sig} {U : Finset Sig} {a b} (d : Bool)
    (va : Valid (f a)) (vb : Valid (f b)) (ab : a≠b) (fresh : bin d a b∉insert a (insert b U))
    (old : ∀c∈U,g c=f c) (eq : g (bin d a b)=bin d (f a) (f b)) :
    amount f (insert a (insert b U))+(if constant (f a) ∨ constant (f b) then 0 else 1)≤amount g (insert (bin d a b) U)+1 := by
  have hz : bin d a b∉U:=fun z=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem z))
  rw [insertAmount,insertAmount,insertAmount,eq,congrAmount old]
  by_cases ca : constant (f a) <;> by_cases cb : constant (f b)
  all_goals by_cases aa : a∈U <;> by_cases bb : b∈U
  all_goals simp only [Finset.mem_insert,ab,false_or,ca,cb,aa,bb,hz,not_true_eq_false,not_false_eq_true,
    and_false,false_and,true_and,and_true,ite_false,ite_true,or_false,false_or,true_or,or_true,Nat.add_zero]
  all_goals try omega
  all_goals try (have z:=bothResult va vb d ca cb;rw [ite_eq_left z];omega)
  all_goals try (split <;> omega)
  all_goals have z:=bothResult va vb d ca cb;simp only [z,ite_true];omega
theorem simulate {k t S} (l : Live k t S) (ht : t=0) (H : SigHom) (f : Sig→Sig)
    (ok : ∀a∈S,Valid (f a) ∧ below (H.fn a) (f a)) : ∃q,q+amount f S≤k ∧ possible q (S.image f) := by
  classical
  induction l generalizing f with
  | stop =>
    have vx:=ok target (Finset.mem_singleton_self _)
    have eq:=atTop vx.1 (by simpa only [H.htarget] using vx.2)
    have nc : ¬constant target:=by rintro (h|h);exact target_proper.2.1 h;exact target_proper.2.2 h
    exact ⟨0,by simp [amount,eq,nc],0,{target},by omega,Live.stop,by simp [eq]⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab fresh tail ih =>
    let S:=insert a (insert b U)
    let z:=bin d a b
    let g:=Function.update f z (bin d (f a) (f b))
    have vz : g z=bin d (f a) (f b):=Function.update_self ..
    have old (c) (hc : c∈U) : g c=f c:=by
      apply Function.update_of_ne
      rintro rfl
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
    have ax:=ok a (Finset.mem_insert_self ..)
    have bx:=ok b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have newOk : ∀c∈insert z U,Valid (g c) ∧ below (H.fn c) (g c) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl|hc
      · rw [vz,H.hbin]
        exact ⟨valid_bin ax.1 bx.1,belowBin d ax.2 bx.2⟩
      · rw [old c hc]
        exact ok c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
    obtain ⟨q,cap,run⟩:=ih ht g newOk
    have sub : (insert z U).image g⊆insert (bin d (f a) (f b)) (S.image f) := by
      rw [Finset.image_insert,vz,Finset.image_congr old]
      exact Finset.insert_subset_insert _ (Finset.image_mono _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..)))
    have run':=widen run (Nat.le_refl _) sub
    have lim:=gateBudget d ax.1 bx.1 ab fresh old vz
    have am : f a∈S.image f:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
    have bm : f b∈S.image f:=Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    by_cases c : constant (f a) ∨ constant (f b)
    · rw [ite_eq_left c] at lim
      exact ⟨q,by omega,free (constFree ax.1 bx.1 am bm d c) run'⟩
    · rw [ite_eq_right c] at lim
      exact ⟨q+1,by omega,pay d ax.1 bx.1 am bm run'⟩
end Dominance8403
end
section
open Basis1868 Leaf8403 Projection8403 Mono8403 Dominance8403
namespace Fit8403
abbrev Pair := Sig×Sig
def rowMask (p : Bool) (r : Nat) : List Pair→Nat
  | []=>top
  | (a,b)::tail=>
    let m:=rowMask p r tail
    if p then (if a.1.testBit r then b.1 &&& m else m)
    else (if a.2.testBit r then m else bnot b.2 &&& m)
def gather (p : Bool) (w : List Pair) : List Nat→Nat
  | []=>0
  | r::rs=>rowMask p r w ||| gather p w rs
lemma gatherBit (p w rs i) (h : (gather p w rs).testBit i=true) : ∃r∈rs,(rowMask p r w).testBit i=true := by
  induction rs with
  | nil =>simp [gather] at h
  | cons r rs ih =>
    rw [gather,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨r,List.mem_cons_self ..,h⟩
    · obtain ⟨s,hs,b⟩:=ih h
      exact ⟨s,List.mem_cons_of_mem _ hs,b⟩
lemma topBit {i : Nat} (h : i<414) : top.testBit i=true := by
  have e : top=2^414-1:=by decide
  rw [e,Nat.testBit_two_pow_sub_one];exact decide_eq_true h
lemma rowsP {w : List Pair} {r i : Nat} (h : (rowMask true r w).testBit i=true) :
    ∀q∈w,q.1.1.testBit r=true → q.2.1.testBit i=true := by
  induction w with
  | nil => simp
  | cons x w ih =>
    obtain ⟨a,b⟩:=x
    by_cases ar : a.1.testBit r=true
    · simp [rowMask,ar,Nat.testBit_and] at h
      exact List.forall_mem_cons.mpr ⟨fun _=>h.1,ih h.2⟩
    · simp [rowMask,ar] at h
      exact List.forall_mem_cons.mpr ⟨fun e=>False.elim (ar e),ih h⟩
lemma rowsN {w : List Pair} {r i : Nat} (hi : i<414) (h : (rowMask false r w).testBit i=true) :
    ∀q∈w,q.2.2.testBit i=true → q.1.2.testBit r=true := by
  induction w with
  | nil => simp
  | cons x w ih =>
    obtain ⟨a,b⟩:=x
    by_cases ar : a.2.testBit r=true
    · simp [rowMask,ar] at h
      exact List.forall_mem_cons.mpr ⟨fun _=>ar,ih h⟩
    · simp [rowMask,ar,Nat.testBit_and,bnot,Nat.testBit_xor,topBit hi] at h
      exact List.forall_mem_cons.mpr ⟨fun e=>by simp_all,ih h.2⟩
def covered (p : Bool) (w : List Pair) := gather p w (List.range 16)==top
theorem fitted {w : List Pair} (va : ∀x∈w,Valid x.2) (a : covered true w=true) (b : covered false w=true) :
    ∃H : SigHom,∀x∈w,below (H.fn x.1) x.2 := by
  have chooseRow (p : Bool) (ok : covered p w=true) (i : Fin 414) :
      ∃r : Fin 414,(rowMask p r w).testBit i=true := by
    obtain ⟨r,hr,hit⟩:=gatherBit p w (List.range 16) i.val ((beq_iff_eq.mp ok).symm ▸ topBit i.isLt)
    have lt:=List.mem_range.mp hr
    exact ⟨⟨r,by omega⟩,hit⟩
  choose x xp using chooseRow true a
  choose y yp using chooseRow false b
  refine ⟨pairHom x y,?_⟩
  intro z hz
  constructor
  · intro j hj
    change (reindex x z.1.1).testBit j=true at hj
    rw [reindex_testBit] at hj
    split at hj
    next h=>exact rowsP (xp ⟨j,h⟩) z hz hj
    next =>contradiction
  · intro j hj
    change (reindex y z.1.2).testBit j=true
    rw [reindex_testBit]
    split
    next h=>exact rowsN h (yp ⟨j,h⟩) z hz hj
    next h=>simp [(va z hz).2 j (by omega)] at hj
structure Basis where
  root : List Sig
  lb : Nat
  va : ∀a∈root,Valid a
  low : level lb root
def select (b : Basis) (ix : Nat) := if ix=14 then one else b.root.getD ix zero
lemma selMem (b : Basis) (ix : Nat) : select b ix∈closed b.root := by
  unfold select
  split
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  · exact read_closed _ _
lemma selVal (b : Basis) (ix : Nat) : Valid (select b ix) := by
  unfold select
  split
  · exact valid_one
  · exact valid_getD b.va _
def pin (b : Basis) (code : Nat) (v : List Sig) (a : Sig) :=
  select b (OrbitQ.getWord code 4 (v.idxOf a))
def pairs (b : Basis) (code : Nat) (v : List Sig) := v.map (fun a=>(a,pin b code v a))
def verify (b : Basis) (code k : Nat) (v : List Sig) :=
  let w:=pairs b code v
  k<b.lb+dead (w.map Prod.snd) && covered true w && covered false w
lemma amountEq (f : Sig→Sig) {v : List Sig} (nd : v.Nodup) : amount f v.toFinset=dead (v.map f) := by
  induction v with
  | nil => simp [amount,dead]
  | cons a v ih =>
    obtain ⟨fresh,nd⟩:=List.nodup_cons.mp nd
    rw [List.toFinset_cons,insertAmount,ih nd]
    have fresh' : a∉v.toFinset:=by simpa using fresh
    simp only [fresh',not_false_eq_true,true_and,List.map_cons,dead,List.countP_cons]
    by_cases hc : constant (f a) <;> simp [hc]
theorem checked {b : Basis} {code k v} (nd : v.Nodup) (ok : verify b code k v=true) : rejects k v := by
  let f:=pin b code v
  let w:=pairs b code v
  have go : (k<b.lb+dead (w.map Prod.snd) && covered true w && covered false w)=true:=ok
  obtain ⟨first,n⟩:=Bool.and_eq_true_iff.mp go
  obtain ⟨lim,p⟩:=Bool.and_eq_true_iff.mp first
  have cost:=of_decide_eq_true lim
  have valW : ∀z∈w,Valid z.2:=by
    rintro z hz
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hz
    exact selVal b _
  obtain ⟨H,h⟩:=fitted valW p n
  intro j cap live
  have sim (a) (ha : a∈v.toFinset) : Valid (f a) ∧ below (H.fn a) (f a) :=
    ⟨selVal b _,h (a,f a) (List.mem_map_of_mem (f:=fun x=>(x,f x)) (List.mem_toFinset.mp ha))⟩
  obtain ⟨q,save,can⟩:=simulate live rfl H f sim
  have sub : v.toFinset.image f⊆closed b.root:=by
    intro a ha;obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp ha;exact selMem b _
  have lower:=b.low q (widen can (Nat.le_refl _) sub)
  have eq : amount f v.toFinset=dead (w.map Prod.snd) := by
    simpa only [w,pairs,List.map_map,Function.comp_def,f] using (amountEq f nd)
  rw [eq] at save
  omega
end Fit8403
end
section
open Basis1868 Free1868 Cuts1868
open Mono8403 QuickQ RotateQ OrbitQ
open MonoWord8403 (Slice)
namespace FitOrbitQ
def seen0 (v : List Sig) (z : Sig) := z==zero || z==one || v.contains z
theorem seenEq (v : List Sig) (z : Sig) : seen0 v z=true ↔ z∈closed v := by
  simp [seen0,closed,or_assoc]
def cheap : List Nat→List Sig→Nat×List Sig
  | [],v=>(0,v)
  | c::cs,v=>
    let z:=gate c v
    let a:=cheap cs (z::v)
    ((if seen0 v z then 0 else 1)+a.1,a.2)
lemma cheapEq (cs : List Nat) (v : List Sig) : cheap cs v=process cs v := by
  induction cs generalizing v with
  | nil=>rfl
  | cons c cs ih=>simp only [cheap,process,ih,seenEq]
def cut (k lb : Nat) (w : List Sig) (d : TableLeafQ.Desc) :=
  let a:=cheap d.1 w
  decide (k+a.1<lb+Leaf8403.dead (Leaf8403.pick d.2 a.2))
def checkAt {full : List Sig} (R : Nat→Rot full) (c : Chart) (old : Rows)
    (sl : Nat→Slice full) (basis : Nat→Fit8403.Basis) (k : Nat) (tab : Rows) (more : Nat→Nat) (i : Nat) :=
  let kind:=label tab i
  let d:=tab.desc i
  if kind=0 then Mono.nextFlat R c (k-1) old (MonoDeck8403.fromDesc full d)
  else if kind=31 then
    let v:=more i
    Fit8403.verify (basis (v % 16)) (v/16) k (MonoDeck8403.fromDesc full d)
  else
    let a:=sl (kind-1)
    cut k a.lb a.raw d
theorem finish {full : List Sig} {c : Chart} (hg : good c) (va : ∀a∈full,Valid a)
    (R : Nat→Rot full) {k old} (pr : Mono.all full k old)
    (sl : Nat→Slice full) (basis : Nat→Fit8403.Basis) (tab : Rows) (more : Nat→Nat)
    (ok : ∀i : Fin tab.count,checkAt R c old sl basis (k+1) tab more i=true) :
    Mono.all full (k+1) tab := by
  intro i
  change (MonoDeck8403.fromDesc full (tab.desc i.val)).Nodup → _
  intro nd
  let d:=tab.desc i.val
  have h:=ok i
  by_cases zero : label tab i.val=0
  · exact Mono.next_ok hg R pr nd (by simpa only [checkAt,zero,ite_true,Nat.add_sub_cancel] using h)
  · by_cases fit : label tab i.val=31
    · exact Fit8403.checked nd (by simpa only [checkAt,zero,fit,ite_false,ite_true,Nat.reduceEqDiff] using h)
    · obtain ⟨H,eq,lb⟩:=(sl (label tab i.val-1)).sound
      exact checked0 eq va lb (by simpa only [checkAt,zero,fit,ite_false,cut,cheapEq,checkCut] using h) nd
end FitOrbitQ
end
section
open Basis1868 Free1868 Cuts1868 Moves3400
open Projection8403 QuickQ RotateQ OrbitQ TableLeafQ Exact8403 Leaf8403
namespace CoreCheck8403
theorem up {full : List Sig} {c : Chart} (hg : good c) (va : ∀a∈full,Valid a) (R : Nat→Rot full)
    (fr : ∀i,SignFixed (R i).J) {k old} (pr : all full k old) (tab : Rows)
    (h : ∀i : Fin tab.count,nextFlat R c k old (body full (tab.desc i))=true) : all full (k+1) tab := by
  intro i
  change (body full (tab.desc i.val)).Nodup → _
  intro nd
  exact next_ok hg R va fr pr nd (h i)
theorem rechart {v w : List Sig} (H : SigHom) {k : Nat} (low : rank (k+1) w)
    (sub : v.toFinset.image H.fn⊆Tape8403.close w) : excluded k v := by
  intro j cap h
  obtain ⟨t,l⟩:=h.expand
  obtain ⟨q,lim,out⟩:=projected l H
  have lb:=low q (Projection8403.mono out (Nat.le_refl _) sub)
  omega
end CoreCheck8403
end
end PEqualNP.Outside.L_meta_11002_aux
namespace PEqualNP.Outside.L_meta_11002_aux
section
open Basis1868
open ColorSearch1868 FreeSearch1868 Cuts1868
open QuickQ
namespace PaintQ
abbrev Item:=Sig×Nat
def onePaint : List Item→Nat→Bool
  | [],_=>true
  | x::xs,a=>(a &&& x.2)==0 && onePaint xs (a ||| x.2)
def twoPaint : List Item→Nat→Nat→Bool
  | [],_,_=>true
  | x::xs,a,b=>((a &&& x.2)==0 && twoPaint xs (a ||| x.2) b) ||
        ((b &&& x.2)==0 && twoPaint xs a (b ||| x.2))
lemma oneEq (xs : List Item) (f : Nat→Nat) : paint 1 xs f=onePaint xs (f 0) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 1=[0] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      onePaint,ite_true]
lemma twoEq (xs : List Item) (f : Nat→Nat) : paint 2 xs f=twoPaint xs (f 0) (f 1) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 2=[0,1] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      twoPaint,ite_true,Nat.reduceEqDiff,ite_false]
def color (n : Nat) (w : List Item) := if n=1 then onePaint w 0 else if n=2 then twoPaint w 0 0 else paint n w (fun _=>0)
lemma colorEq (n : Nat) (w : List Item) : color n w=paint n w (fun _=>0) := by
  unfold color
  split
  next h=>subst n;exact (oneEq w (fun _=>0)).symm
  next=>split
        next h=>subst n;exact (twoEq w (fun _=>0)).symm
        next=>rfl
def shade (c : Chart) (once : Nat) (x : Item) : Item :=
  let h:=hit c once x
  if h=0 then (x.1,0) else (x.1,x.2 &&& sweep c.fillP h &&& sweep c.fillN h &&& roof c)
lemma shadeEq (c : Chart) (once : Nat) (x : Item) : shade c once x=marked c once x := by
  simp only [shade,marked]
  split
  next h=>rw [h,(linSweep _).1];simp
  next=>rfl
def testRows (c : Chart) (k : Nat) (s : List Item) :=
  let g:=PEqualNP.Outside.L_meta_11002_aux.Board1868.mult s
  (g.1 &&& roof c)==roof c && color k (s.map (shade c (g.1 ^^^ g.2)))
lemma rowsMap (c d k v) : testRows c k (v.map (diff c d))=test c d k v := by
  simp only [testRows,test,signs,colorEq,funext (shadeEq _ _)]
end PaintQ
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open QuickQ OrbitQ Mono8403 RotateQ PaintQ
namespace PackQ
def pass (c : Chart) (k : Nat) (hit : List Sig→Bool) (v : List Item) :=
  v.length≤k+1 && testRows c (k+2-v.length) v && !(hit (v.map Prod.fst))
def plain (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) :=
  v.length≤k+1 && test c d (k+2-v.length) v && !(hit v)
lemma passMap (c d k hit v) : pass c k hit (v.map (diff c d))=plain c d k hit v := by
  simp only [pass,plain,List.length_map,rowsMap,List.map_map]
  have id : Prod.fst ∘ diff c d=id:=rfl
  rw [id,List.map_id]
def selected (a b : Sig) (l r : Bool) (v : List Item) := v.filter fun x=>keep a b l r x.1
lemma selectMap (c d a b l r) (v : List Sig) :
    selected a b l r (v.map (diff c d))=(v.filter (keep a b l r)).map (diff c d) := by
  simp only [selected,List.filter_map]
  rfl
def choices (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (w : List Item) (a b z : Sig) :=
  let val:=diff c d z
  [false,true].any fun l=>[false,true].any fun r=>pass c k hit (val::selected a b l r w)
lemma choicesMap (c d k hit v a b z) : choices c d k hit (v.map (diff c d)) a b z=
    [false,true].any (fun l=>[false,true].any fun r=>plain c d k hit (next v a b z l r)) := by
  simp only [choices,selectMap,next,← List.map_cons,passMap]
def forkS (c : Chart) (k : Nat) (hit : List Sig→Bool) (ws : List Item) (v : List Sig) (a b : Item) :=
  [false,true].any fun s=>[false,true].any fun t=>
    let z:=blend false s t a.1 b.1
    z != zero && !(v.contains z) && choices c true k hit ws a.1 b.1 z
def forkM (c : Chart) (k : Nat) (hit : List Sig→Bool) (ws : List Item) (v : List Sig) (a b : Item) :=
  [false,true].any fun d=>
    let z:=bin d a.1 b.1
    z != zero && z != one && !(v.contains z) && choices c false k hit ws a.1 b.1 z
lemma forkSMap (c k hit v a b) :
    forkS c k hit (v.map (diff c true)) v (diff c true a) (diff c true b)=pairB v (plain c true k hit) a b := by
  simp only [forkS,pairB,oneB,choicesMap];rfl
lemma forkMMap (c k hit v a b) :
    forkM c k hit (v.map (diff c false)) v (diff c false a) (diff c false b)=choice (plain c false k hit) v a b := by
  simp only [forkM,choice,choicesMap];rfl
lemma scanMap {α β : Type} (f : α→β) (u : β→β→Bool) (g : α→α→Bool)
    (all : ∀a b,u (f a) (f b)=g a b) (v : List α) :
    scanPairs u (v.map f)=scanPairs g v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [scanPairs,List.any_map,Function.comp_def,all,ih]
def nodeS {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (diff c true)
  !(baseTest v || scanPairs (forkS c k (matchCode R old) ws v) ws)
def nodeM {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (diff c false)
  !(v==[target] || scanPairs (forkM c k (Mono.matchCode R old) ws v) ws)
lemma nodeSEq {full} (R : Nat→Rot full) (c k old v) : nodeS R c k old v=nextFlat R c k old v := by
  simp only [nodeS,nextFlat,scanMap _ _ _ (forkSMap _ _ _ _)]
  rfl
lemma nodeMEq {full} (R : Nat→Rot full) (c k old v) : nodeM R c k old v=Mono.nextFlat R c k old v := by
  simp only [nodeM,Mono.nextFlat,scanMap _ _ _ (forkMMap _ _ _ _)]
  rfl
end PackQ
end
section
open Basis1868 PaintQ
namespace SlimTwo8403
def two : List Item→Nat→Nat→Bool
  | [],_,_=>true
  | x::xs,a,b=>((a &&& x.2)==0 && two xs (a ||| x.2) b) ||
        (a != b && (b &&& x.2)==0 && two xs a (b ||| x.2))
lemma swap (w : List Item) (a b : Nat) : twoPaint w a b=twoPaint w b a := by
  induction w generalizing a b with
  | nil=>rfl
  | cons x xs ih=>
    rw [twoPaint,twoPaint,ih (a ||| x.2) b,ih a (b ||| x.2),Bool.or_comm]
lemma eqTwo (w : List Item) (a b : Nat) : two w a b=twoPaint w a b := by
  induction w generalizing a b with
  | nil=>rfl
  | cons x xs ih=>
    by_cases h : a=b
    · subst b
      rw [two,twoPaint]
      simp only [bne_self_eq_false,Bool.false_and,Bool.or_false,ih]
      rw [swap xs a (a ||| x.2),Bool.or_self]
    · rw [two,twoPaint]
      simp only [bne_iff_ne.mpr h,Bool.true_and,ih]
end SlimTwo8403
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open QuickQ OrbitQ Mono8403 RotateQ PaintQ PackQ
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
namespace GroupQ
def passes (c : Chart) (lookup : List Sig→Bool) (colors len : Nat) (rest : List Item) (g : Sig) (a : Item) :=
  let cover:=g.1 ||| a.2
  (cover &&& roof c)==roof c &&
    let one:=cover ^^^ (g.2 ||| (g.1 &&& a.2))
    color colors (shade c one a::rest.map (shade c one)) && !lookup (a.1::rest.map Prod.fst)
def arrangements (c : Chart) (k : Nat) (lookup : List Sig→Bool) (ws : List Item) (a b : Sig) (zs : List Item) :=
  [false,true].any fun l=>[false,true].any fun r=>
    let rest:=selected a b l r ws
    let m:=rest.length+1
    m≤k+1 && zs.any (passes c lookup (k+2-m) m rest (mult rest))
lemma swapOrder {α β : Type} (xs : List α) (ys : List β) (p : α→β→Bool) :
    (xs.any fun x=>ys.any (p x))=(ys.any fun y=>xs.any (fun x=>p x y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨x,hx,y,hy,h⟩ <;> exact ⟨y,hy,x,hx,h⟩
lemma passHead (c k lookup rest a) : pass c k lookup (a::rest)=
    (rest.length+1≤k+1 && passes c lookup (k+2-(rest.length+1)) (rest.length+1) rest (mult rest) a) := by
  simp only [pass,testRows,passes,List.length_cons,List.map_cons,mult,Bool.and_assoc]
lemma arrangements_eq (c d k lookup ws a b) (zs : List Sig) :
    arrangements c k lookup ws a b (zs.map (diff c d))=
    zs.any (choices c d k lookup ws a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [arrangements,choices,List.any_eq_true,List.any_map,Function.comp_apply,
    passHead,Bool.and_eq_true,List.mem_map,exists_exists_and_eq_and]
  constructor
  · rintro ⟨l,hl,r,hr,bnd,z,hz,h⟩
    exact ⟨z,hz,l,hl,r,hr,bnd,h⟩
  · rintro ⟨z,hz,l,hl,r,hr,bnd,h⟩
    exact ⟨l,hl,r,hr,bnd,z,hz,h⟩
def generators (d : Bool) (a b : Sig) : List Sig :=
  if d then [false,true].flatMap (fun s=>[false,true].map (fun t=>blend false s t a b))
  else [bin false a b,bin true a b]
def fresh (d : Bool) (v : List Sig) (z : Sig) := z != zero && (d || z != one) && !(v.contains z)
def fork (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) (ws : List Item) (a b : Item) :=
  let zs:=(generators d a.1 b.1).filter (fresh d v)
  arrangements c k hit ws a.1 b.1 (zs.map (diff c d))
lemma forkSEQ (c k hit v ws a b) : fork c true k hit v ws a b=forkS c k hit ws v a b := by
  simp only [fork,arrangements_eq,generators,ite_true,forkS,List.any_filter,List.any_flatMap,List.any_map,
    Function.comp_def,fresh,Bool.true_or,Bool.and_true,Bool.and_assoc]
lemma forkMEQ (c k hit v ws a b) : fork c false k hit v ws a b=forkM c k hit ws v a b := by
  simp only [fork,arrangements_eq,generators,Bool.false_eq_true,ite_false,forkM,List.any_filter,List.any_cons,List.any_nil,
    Bool.or_false,fresh,Bool.false_or,Bool.and_assoc]
def nodeS {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (diff c true)
  !(baseTest v || scanPairs (fork c true k (matchCode R old) v ws) ws)
def nodeM {full : List Sig} (R : Nat→Rot full) (c : Chart) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (diff c false)
  !(v==[target] || scanPairs (fork c false k (Mono.matchCode R old) v ws) ws)
lemma nodeSEq {full} (R : Nat→Rot full) (c k old v) : nodeS R c k old v=nextFlat R c k old v := by
  let ws:=v.map (diff c true)
  have e : fork c true k (matchCode R old) v ws=forkS c k (matchCode R old) ws v:=by
    funext a b;exact forkSEQ c k _ v ws a b
  rw [←PackQ.nodeSEq R c k old v]
  change _=_
  simpa only [nodeS,PackQ.nodeS,ws] using congrArg (fun f=>!(baseTest v || scanPairs f ws)) e
lemma nodeMEq {full} (R : Nat→Rot full) (c k old v) : nodeM R c k old v=Mono.nextFlat R c k old v := by
  let ws:=v.map (diff c false)
  have e : fork c false k (Mono.matchCode R old) v ws=forkM c k (Mono.matchCode R old) ws v:=by
    funext a b;exact forkMEQ c k _ v ws a b
  rw [←PackQ.nodeMEq R c k old v]
  change _=_
  simpa only [nodeM,PackQ.nodeM,ws] using congrArg (fun f=>!(v==[target] || scanPairs f ws)) e
end GroupQ
end
section
open Basis1868 Free1868 FreeSearch1868 Cuts1868
open QuickQ OrbitQ Mono8403 RotateQ PaintQ PackQ
open PEqualNP.Outside.L_meta_11002_aux.Board1868 (mult)
namespace ShapeQ
structure Shape where
  cap : Nat
  pr : Nat→Nat
  nr : Nat→Nat
  rows : Nat→Nat
  cols : Nat→Nat
def ofChart (c : Chart) : Shape:=⟨roof c,sweep c.spreadP,sweep c.spreadN,sweep c.fillP,sweep c.fillN⟩
def sep (g : Shape) (d : Bool) (a : Sig) : Item :=
  let p:=g.pr a.1
  let n:=g.nr a.2
  (a,if d then p ^^^ n else p &&& (g.cap ^^^ n))
def mark (g : Shape) (key : Nat) (a : Item) : Item :=
  let u:=a.2 &&& key &&& g.cap
  if u=0 then (a.1,0) else (a.1,a.2 &&& g.rows u &&& g.cols u &&& g.cap)
def paint (n : Nat) (w : List Item) :=
  if n=1 then onePaint w 0 else if n=2 then SlimTwo8403.two w 0 0 else PEqualNP.Outside.L_meta_11002_aux.ColorSearch1868.paint n w (fun _=>0)
lemma paintEq (n w) : paint n w=color n w:=by simp only [paint,color,SlimTwo8403.eqTwo]
def passes (g : Shape) (lookup : List Sig→Bool) (colors : Nat) (rest : List Item) (agg : Sig) (z : Item) :=
  let cover:=agg.1 ||| z.2
  (cover &&& g.cap)==g.cap &&
    let one:=cover ^^^ (agg.2 ||| (agg.1 &&& z.2))
    paint colors (mark g one z::rest.map (mark g one)) && !lookup (z.1::rest.map Prod.fst)
lemma passesEq (c k lookup a z r len) : passes (ofChart c) lookup k r a z=GroupQ.passes c lookup k len r a z := by
  simp only [passes,GroupQ.passes,paintEq];rfl
def arrangements (g : Shape) (k : Nat) (lookup : List Sig→Bool) (ws : List Item) (a b : Sig) (zs : List Item) :=
  [false,true].any fun l=>[false,true].any fun r=>
    let rest:=selected a b l r ws
    let m:=rest.length+1
    m≤k+1 && zs.any (passes g lookup (k+2-m) rest (mult rest))
def fork (g : Shape) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) (ws : List Item) (a b : Item) :=
  let zs:=(GroupQ.generators d a.1 b.1).filter (GroupQ.fresh d v)
  arrangements g k hit ws a.1 b.1 (zs.map (sep g d))
lemma forkEq (c d k hit v ws a b) : fork (ofChart c) d k hit v ws a b=GroupQ.fork c d k hit v ws a b := by
  simp only [fork,GroupQ.fork,arrangements,GroupQ.arrangements]
  congr 1
  funext l
  congr 1
  funext r
  let rs:=selected a.1 b.1 l r ws
  let z:=((GroupQ.generators d a.1 b.1).filter (GroupQ.fresh d v)).map (diff c d)
  have h : passes (ofChart c) hit (k+2-(rs.length+1)) rs (mult rs)=GroupQ.passes c hit (k+2-(rs.length+1)) (rs.length+1) rs (mult rs):=by
    funext x; exact passesEq ..
  exact congrArg (fun u=>decide (rs.length+1≤k+1) && z.any u) h
def nodeS {full : List Sig} (R : Nat→Rot full) (g : Shape) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (sep g true)
  !(baseTest v || scanPairs (fork g true k (matchCode R old) v ws) ws)
def nodeM {full : List Sig} (R : Nat→Rot full) (g : Shape) (k : Nat) (old : Rows) (v : List Sig) :=
  let ws:=v.map (sep g false)
  !(v==[target] || scanPairs (fork g false k (Mono.matchCode R old) v ws) ws)
lemma nodeSEq {full} (R : Nat→Rot full) (c k old v) : nodeS R (ofChart c) k old v=nextFlat R c k old v := by
  rw [←GroupQ.nodeSEq R c k old v]
  let ws:=v.map (diff c true)
  have e : fork (ofChart c) true k (matchCode R old) v ws=GroupQ.fork c true k (matchCode R old) v ws:=by
    funext a b;exact forkEq ..
  exact congrArg (fun f=>!(baseTest v || scanPairs f ws)) e
lemma nodeMEq {full} (R : Nat→Rot full) (c k old v) : nodeM R (ofChart c) k old v=Mono.nextFlat R c k old v := by
  rw [←GroupQ.nodeMEq R c k old v]
  let ws:=v.map (diff c false)
  have e : fork (ofChart c) false k (Mono.matchCode R old) v ws=GroupQ.fork c false k (Mono.matchCode R old) v ws:=by
    funext a b;exact forkEq ..
  exact congrArg (fun f=>!(v==[target] || scanPairs f ws)) e
end ShapeQ
end
section
open QuickQ ShapeQ
namespace UnrollQ
def s64_320 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch64x32.spreadP.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 992)) &&& (ch64x32.spreadP.getD 1 (false,0,0)).2.2
  let v:=(v ||| (v <<< 496)) &&& (ch64x32.spreadP.getD 2 (false,0,0)).2.2
  let v:=(v ||| (v <<< 248)) &&& (ch64x32.spreadP.getD 3 (false,0,0)).2.2
  let v:=(v ||| (v <<< 124)) &&& (ch64x32.spreadP.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 62)) &&& (ch64x32.spreadP.getD 5 (false,0,0)).2.2
  let v:=(v ||| (v <<< 31)) &&& (ch64x32.spreadP.getD 6 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof2048
  let v:=(v ||| (v <<< 2)) &&& roof2048
  let v:=(v ||| (v <<< 4)) &&& roof2048
  let v:=(v ||| (v <<< 8)) &&& roof2048
  let v:=(v ||| (v <<< 16)) &&& roof2048
  v
def s64_321 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch64x32.spreadN.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 32)) &&& roof2048
  let v:=(v ||| (v <<< 64)) &&& roof2048
  let v:=(v ||| (v <<< 128)) &&& roof2048
  let v:=(v ||| (v <<< 256)) &&& roof2048
  let v:=(v ||| (v <<< 512)) &&& roof2048
  let v:=(v ||| (v <<< 1024)) &&& roof2048
  v
def s64_322 (v : Nat) :=
  let v:=(v ||| (v >>> 1)) &&& roof2048
  let v:=(v ||| (v >>> 2)) &&& roof2048
  let v:=(v ||| (v >>> 4)) &&& roof2048
  let v:=(v ||| (v >>> 8)) &&& roof2048
  let v:=(v ||| (v >>> 16)) &&& roof2048
  let v:=(v ||| (v >>> 0)) &&& (ch64x32.fillP.getD 5 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof2048
  let v:=(v ||| (v <<< 2)) &&& roof2048
  let v:=(v ||| (v <<< 4)) &&& roof2048
  let v:=(v ||| (v <<< 8)) &&& roof2048
  let v:=(v ||| (v <<< 16)) &&& roof2048
  v
def s64_323 (v : Nat) :=
  let v:=(v ||| (v >>> 32)) &&& roof2048
  let v:=(v ||| (v >>> 64)) &&& roof2048
  let v:=(v ||| (v >>> 128)) &&& roof2048
  let v:=(v ||| (v >>> 256)) &&& roof2048
  let v:=(v ||| (v >>> 512)) &&& roof2048
  let v:=(v ||| (v >>> 1024)) &&& roof2048
  let v:=(v ||| (v >>> 0)) &&& (ch64x32.fillN.getD 6 (false,0,0)).2.2
  let v:=(v ||| (v <<< 32)) &&& roof2048
  let v:=(v ||| (v <<< 64)) &&& roof2048
  let v:=(v ||| (v <<< 128)) &&& roof2048
  let v:=(v ||| (v <<< 256)) &&& roof2048
  let v:=(v ||| (v <<< 512)) &&& roof2048
  let v:=(v ||| (v <<< 1024)) &&& roof2048
  v
def s64_32 : Shape := ⟨roof2048,s64_320,s64_321,s64_322,s64_323⟩
set_option maxRecDepth 8192 in
lemma s64_32eq : s64_32=ofChart ch64x32:=rfl
def s64_160 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch64x16.spreadP.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 480)) &&& (ch64x16.spreadP.getD 1 (false,0,0)).2.2
  let v:=(v ||| (v <<< 240)) &&& (ch64x16.spreadP.getD 2 (false,0,0)).2.2
  let v:=(v ||| (v <<< 120)) &&& (ch64x16.spreadP.getD 3 (false,0,0)).2.2
  let v:=(v ||| (v <<< 60)) &&& (ch64x16.spreadP.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 30)) &&& (ch64x16.spreadP.getD 5 (false,0,0)).2.2
  let v:=(v ||| (v <<< 15)) &&& (ch64x16.spreadP.getD 6 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof1024
  let v:=(v ||| (v <<< 2)) &&& roof1024
  let v:=(v ||| (v <<< 4)) &&& roof1024
  let v:=(v ||| (v <<< 8)) &&& roof1024
  v
def s64_161 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch64x16.spreadN.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 16)) &&& roof1024
  let v:=(v ||| (v <<< 32)) &&& roof1024
  let v:=(v ||| (v <<< 64)) &&& roof1024
  let v:=(v ||| (v <<< 128)) &&& roof1024
  let v:=(v ||| (v <<< 256)) &&& roof1024
  let v:=(v ||| (v <<< 512)) &&& roof1024
  v
def s64_162 (v : Nat) :=
  let v:=(v ||| (v >>> 1)) &&& roof1024
  let v:=(v ||| (v >>> 2)) &&& roof1024
  let v:=(v ||| (v >>> 4)) &&& roof1024
  let v:=(v ||| (v >>> 8)) &&& roof1024
  let v:=(v ||| (v >>> 0)) &&& (ch64x16.fillP.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof1024
  let v:=(v ||| (v <<< 2)) &&& roof1024
  let v:=(v ||| (v <<< 4)) &&& roof1024
  let v:=(v ||| (v <<< 8)) &&& roof1024
  v
def s64_163 (v : Nat) :=
  let v:=(v ||| (v >>> 16)) &&& roof1024
  let v:=(v ||| (v >>> 32)) &&& roof1024
  let v:=(v ||| (v >>> 64)) &&& roof1024
  let v:=(v ||| (v >>> 128)) &&& roof1024
  let v:=(v ||| (v >>> 256)) &&& roof1024
  let v:=(v ||| (v >>> 512)) &&& roof1024
  let v:=(v ||| (v >>> 0)) &&& (ch64x16.fillN.getD 6 (false,0,0)).2.2
  let v:=(v ||| (v <<< 16)) &&& roof1024
  let v:=(v ||| (v <<< 32)) &&& roof1024
  let v:=(v ||| (v <<< 64)) &&& roof1024
  let v:=(v ||| (v <<< 128)) &&& roof1024
  let v:=(v ||| (v <<< 256)) &&& roof1024
  let v:=(v ||| (v <<< 512)) &&& roof1024
  v
def s64_16 : Shape := ⟨roof1024,s64_160,s64_161,s64_162,s64_163⟩
set_option maxRecDepth 8192 in
lemma s64_16eq : s64_16=ofChart ch64x16:=rfl
def s16_160 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch16x16.spreadP.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 120)) &&& (ch16x16.spreadP.getD 1 (false,0,0)).2.2
  let v:=(v ||| (v <<< 60)) &&& (ch16x16.spreadP.getD 2 (false,0,0)).2.2
  let v:=(v ||| (v <<< 30)) &&& (ch16x16.spreadP.getD 3 (false,0,0)).2.2
  let v:=(v ||| (v <<< 15)) &&& (ch16x16.spreadP.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof256
  let v:=(v ||| (v <<< 2)) &&& roof256
  let v:=(v ||| (v <<< 4)) &&& roof256
  let v:=(v ||| (v <<< 8)) &&& roof256
  v
def s16_161 (v : Nat) :=
  let v:=(v ||| (v >>> 0)) &&& (ch16x16.spreadN.getD 0 (false,0,0)).2.2
  let v:=(v ||| (v <<< 16)) &&& roof256
  let v:=(v ||| (v <<< 32)) &&& roof256
  let v:=(v ||| (v <<< 64)) &&& roof256
  let v:=(v ||| (v <<< 128)) &&& roof256
  v
def s16_162 (v : Nat) :=
  let v:=(v ||| (v >>> 1)) &&& roof256
  let v:=(v ||| (v >>> 2)) &&& roof256
  let v:=(v ||| (v >>> 4)) &&& roof256
  let v:=(v ||| (v >>> 8)) &&& roof256
  let v:=(v ||| (v >>> 0)) &&& (ch16x16.fillP.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 1)) &&& roof256
  let v:=(v ||| (v <<< 2)) &&& roof256
  let v:=(v ||| (v <<< 4)) &&& roof256
  let v:=(v ||| (v <<< 8)) &&& roof256
  v
def s16_163 (v : Nat) :=
  let v:=(v ||| (v >>> 16)) &&& roof256
  let v:=(v ||| (v >>> 32)) &&& roof256
  let v:=(v ||| (v >>> 64)) &&& roof256
  let v:=(v ||| (v >>> 128)) &&& roof256
  let v:=(v ||| (v >>> 0)) &&& (ch16x16.fillN.getD 4 (false,0,0)).2.2
  let v:=(v ||| (v <<< 16)) &&& roof256
  let v:=(v ||| (v <<< 32)) &&& roof256
  let v:=(v ||| (v <<< 64)) &&& roof256
  let v:=(v ||| (v <<< 128)) &&& roof256
  v
def s16_16 : Shape := ⟨roof256,s16_160,s16_161,s16_162,s16_163⟩
set_option maxRecDepth 8192 in
lemma s16_16eq : s16_16=ofChart ch16x16:=rfl
end UnrollQ
end
section
open Basis1868 Free1868 Cuts1868
open OrbitQ QuickQ TableLeafQ Leaf8403 RotateQ Mono8403 ShapeQ
namespace FrontQ
def testS {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : Minor full) (ms : Array (Minor full)) (k : Nat) (tab : Rows) (i : Nat) := if label tab i=0 then ShapeQ.nodeS R UnrollQ.s64_32 (k-1) prev (body full (tab.desc i)) else OrbitQ.checkAt R ch64x32 prev m ms k tab i
lemma eqS {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : Minor full) (ms : Array (Minor full)) (k : Nat) (tab : Rows) (i : Nat) : testS R prev m ms k tab i=OrbitQ.checkAt R ch64x32 prev m ms k tab i:=by
  unfold testS
  split
  next h=>simp only [UnrollQ.s64_32eq,ShapeQ.nodeSEq,OrbitQ.checkAt,OrbitQ.assess,h,ite_true]
  next=>rfl
def testM {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : MonoWord8403.Slice full) (ms : Array (MonoWord8403.Slice full)) (k : Nat) (tab : Rows) (i : Nat) := if label tab i=0 then ShapeQ.nodeM R UnrollQ.s16_16 (k-1) prev (MonoDeck8403.fromDesc full (tab.desc i)) else OrbitQ.Mono.checkAt R ch16x16 prev m ms k tab i
lemma eqM {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : MonoWord8403.Slice full) (ms : Array (MonoWord8403.Slice full)) (k : Nat) (tab : Rows) (i : Nat) : testM R prev m ms k tab i=OrbitQ.Mono.checkAt R ch16x16 prev m ms k tab i:=by
  unfold testM
  split
  next h=>simp only [UnrollQ.s16_16eq,ShapeQ.nodeMEq,OrbitQ.Mono.checkAt,OrbitQ.Mono.assess,h,ite_true]
  next=>rfl
def testF {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : Nat→MonoWord8403.Slice full) (ms : Nat→Fit8403.Basis) (k : Nat) (tab : Rows) (more : Nat→Nat) (i : Nat) := if label tab i=0 then ShapeQ.nodeM R UnrollQ.s16_16 (k-1) prev (MonoDeck8403.fromDesc full (tab.desc i)) else FitOrbitQ.checkAt R ch16x16 prev m ms k tab more i
lemma eqF {full : List Sig} (R : Nat→Rot full) (prev : Rows) (m : Nat→MonoWord8403.Slice full) (ms : Nat→Fit8403.Basis) (k : Nat) (tab : Rows) (more : Nat→Nat) (i : Nat) : testF R prev m ms k tab more i=FitOrbitQ.checkAt R ch16x16 prev m ms k tab more i:=by
  unfold testF
  split
  next h=>simp only [UnrollQ.s16_16eq,ShapeQ.nodeMEq,FitOrbitQ.checkAt,h,ite_true]
  next=>rfl
end FrontQ
end
section
open Basis1868
namespace SmallHom8403
def make (p pBits n nBits : Nat) := pairHom
  (fun i=>Fin.ofNat 414 (OrbitQ.getWord pBits 8 (i.val % p)))
  (fun i=>Fin.ofNat 414 (OrbitQ.getWord nBits 8 (i.val % n)))
theorem validImage (H : SigHom) {v w : List Sig} (eq : v.map H.fn=w) : ∀a∈w,Valid a := by
  rw [←eq]
  intro a ha;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha;exact H.valid b
end SmallHom8403
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin5
def full : List Sig := [(0x2aaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0aaaaaaaaaa0,0x1f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f55),(0x2660a6666666660a6666666660a6666666660a6666666660a6666666660a6666666660a6666666660a6666666660a6666666660a,0x35333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f5333f533),(0x1e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e661e1e1e01e66,0x330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330ff330f),(0x201e001fe01e01e001fe01e01e001fe01e01e001fe01e01e001fe01e01e001fe01e01e001fe01e01e001fe01e01e001fe01e01e0,0x30ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ff),(0x2001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e0001ffe001e,0xffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0fff),(0x1fffe0000001fffe0000001fffe0000001fffe0000001fffe0000001fffe0000001fffe0000001fffe0000001fffe0000001fffe,0x3fff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,8),(5,12),(17,16),(1,1),(5,2),(17,4)]) (by decide) (by decide +kernel)
end Origin5
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin5
namespace OrbCore5
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 44))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 20))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b28272a2926252423201f22211e1d100f0c0b0e0d0a09080706051c1b18171a191615141312110402030100 8 (i.val % 44))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xf0e0d0c131211100b090a080706030205040100 8 (i.val % 20))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2a2b29282627251c1a1b191816171524222321201e1f1d14121311100e0f0d0c0a0b09040302010807060500 8 (i.val % 44))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131112100b0a09080f0e0d0c0705060403010200 8 (i.val % 20))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x282b272a262925100c0f0b0e0a0d092420231f221e211d080607051c181b171a161915040203011413121100 8 (i.val % 44))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xf0d0e0c0b090a08131211100703060205010400 8 (i.val % 20))
def H3 := pairHom p3 n3
def p4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2a28262b2927251c1a18161b191715100e0c0a0f0d0b09040302012422201e23211f1d141213110806070500 8 (i.val % 44))
def n4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xb0a0908131112100f0d0e0c0705030106040200 8 (i.val % 20))
def H4 := pairHom p4 n4
def p5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x282a262b272925100c0e0a0f0b0d091c181a161b171915040203012420221e231f211d080607051412131100 8 (i.val % 44))
def n5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xb090a080f0d0e0c131112100703050106020400 8 (i.val % 20))
def H5 := pairHom p5 n5
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 1 zero,full.getD 0 zero,full.getD 2 zero,full.getD 4 zero,full.getD 3 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 1 zero,full.getD 2 zero,full.getD 0 zero,full.getD 4 zero,full.getD 5 zero,full.getD 3 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H4,by decide +kernel,by decide +kernel⟩
def raw4 := [full.getD 2 zero,full.getD 0 zero,full.getD 1 zero,full.getD 5 zero,full.getD 3 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot4 : Rot full := ⟨raw4,H4,H3,by decide +kernel,by decide +kernel⟩
def raw5 := [full.getD 2 zero,full.getD 1 zero,full.getD 0 zero,full.getD 5 zero,full.getD 4 zero,full.getD 3 zero]
set_option maxRecDepth 8192 in
def rot5 : Rot full := ⟨raw5,H5,H5,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else if i=2 then rot2 else if i=3 then rot3 else if i=4 then rot4 else if i=5 then rot5 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t4 := table 6 3 0 1 0x0 0x0 0 0x0 0x0 1
def t5 := table 6 2 4 32 0xf3522302eb53f302f905d302f506231f 0x0 8 0xed700fc3e1262ec15b459a45361ce9d7a0ccbb32056e80 0x443148a419 5
def t6 := table 6 1 3 19 0x1f4c0bd98fff43f 0x0 12 0xf83629de91e394d66f2721dbfe7a1731d55dd8b4ba7515692ff69cecccbe34e0b89f1 0x901416b2881ad30 5
def t7 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore5
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin5
namespace OrbCore5
abbrev q5 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 4 t4 (TableLeafQ.body full (t5.desc i))=true
set_option maxRecDepth 8192 in
theorem b5a0 : SpanQ.Block q5 0 4 := by decide +kernel
theorem ready5 : OrbitQ.all full 5 t5 := by
  have prev : OrbitQ.all full 4 t4:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot prev t5
  have g : SpanQ.Block q5 0 4 := b5a0
  intro i
  simpa only [q5,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 3 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready5 t6
  have g : SpanQ.Block q6 0 3 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 7 full := by
  have eq : TableLeafQ.body full (t7.desc 0)=full := by decide +kernel
  have h:=ready7 ⟨0,by decide⟩
  change (TableLeafQ.body full (t7.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore5
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core5
def st33 : List Sig := [(0x15550555555555505555555555055555555550555555555505555555555055555555550555555555505555555555055555555550,0x1f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f5555f55),(0xccfacccccccccfacccccccccfacccccccccfacccccccccfacccccccccfacccccccccfacccccccccfacccccccccfacccccccccfa,0xaccc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0accc0acc),(0x3f0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0ccf0f0f0ff0cc,0xcf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf00ccf0),(0x300f000ff00f00f000ff00f00f000ff00f00f000ff00f00f000ff00f00f000ff00f00f000ff00f00f000ff00f00f000ff00f00f0,0x30ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ffff0ff),(0xfff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0ffff000fff0,0x30000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f000),(0x30000fffffff0000fffffff0000fffffff0000fffffff0000fffffff0000fffffff0000fffffff0000fffffff0000fffffff0000,0xf0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002b 8 (i.val % 44))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 20))
def proj := pairHom pIndex nIndex
theorem e33 : excluded 7 st33 := by
  let w:=Origin5.full
  have low : rank 8 w := known OrbCore5.bound Origin5.needed Origin5.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core5
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin6
def full : List Sig := [(0x2aa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480aaaaaaa55480,0x37bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bd),(0x26633224666666633224666666633224666666633224666666633224666666633224666666633224666666633224666666633224,0x3d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b),(0x1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f1921e1e1e10f192,0x2ce7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7ece7),(0x1f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e01fe01f00f8e,0x3c1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1ffc1f),(0x3ff0007e0001fff0007e0001fff0007e0001fff0007e0001fff0007e0001fff0007e0001fff0007e0001fff0007e0001fff0007e,0x23ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ffe3ff),(0xffffe0000000ffffe0000000ffffe0000000ffffe0000000ffffe0000000ffffe0000000ffffe0000000ffffe0000000ffffe,0x1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff1fff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(12,10),(7,2),(21,3)]) (by decide) (by decide +kernel)
end Origin6
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin6
namespace OrbCore6
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 48))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xf0e0d0c0b0a09080706050403020100 8 (i.val % 16))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2f2c2b2e2d2a29282724232625222113120f0e11100d0c0b0a080709201f1c1b1e1d1a19181714161506040503010200 8 (i.val % 48))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xc0b0a0f0e0d09070806050402030100 8 (i.val % 16))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t5 := table 6 3 0 1 0x0 0x0 0 0x0 0x0 1
def t6 := table 6 2 2 32 0xf502f54bdd04f54b 0x0 3 0xec8c9135a8d13e45c 0x809 4
def t7 := table 6 1 10 19 0x3faa5ff542fea9ffd08bfa097f432fe85ffd0fffa0fff31f 0x0 18 0x3d58967aaf24f3bbbddb60d33fab1659ad6aa8a073ab70270ed8ca41c187d28ee2fb21a86cf2f87c75bbfe2a04d18c86da8f503a 0x24280222038308449100c10415241899 7
def t8 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore6
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin6
namespace OrbCore6
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 2 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  have prev : OrbitQ.all full 5 t5:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot prev t6
  have g : SpanQ.Block q6 0 2 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 10 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 10 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 7 t7 (TableLeafQ.body full (t8.desc i))=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 1 := by decide +kernel
theorem ready8 : OrbitQ.all full 8 t8 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready7 t8
  have g : SpanQ.Block q8 0 1 := b8a0
  intro i
  simpa only [q8,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 8 full := by
  have eq : TableLeafQ.body full (t8.desc 0)=full := by decide +kernel
  have h:=ready8 ⟨0,by decide⟩
  change (TableLeafQ.body full (t8.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore6
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core6
def st21 : List Sig := [(0x1552aa4055555552aa4055555552aa4055555552aa4055555552aa4055555552aa4055555552aa4055555552aa4055555552aa40,0x37bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bdb7bd),(0x33319912333333319912333333319912333333319912333333319912333333319912333333319912333333319912333333319912,0x3d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b7d6b),(0x30f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736f0f0f0f78736,0x13181318131813181318131813181318131813181318131813181318131813181318131813181318131813181318131813181318),(0x3f07f838ff00ff07f838ff00ff07f838ff00ff07f838ff00ff07f838ff00ff07f838ff00ff07f838ff00ff07f838ff00ff07f838,0x3e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e0),(0x7ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0ffff0007ffc0,0x1c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c001c00),(0x3ff80000fffffff80000fffffff80000fffffff80000fffffff80000fffffff80000fffffff80000fffffff80000fffffff80000,0x2000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002f 8 (i.val % 48))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xf0e0d0c0b0a09080706050403020100 8 (i.val % 16))
def proj := pairHom pIndex nIndex
theorem e21 : excluded 8 st21 := by
  let w:=Origin6.full
  have low : rank 9 w := known OrbCore6.bound Origin6.needed Origin6.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core6
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin9
def full : List Sig := [(0x15555554aa00aaaaaaa550055555552a802aaaaaa954015555554aa00aaaaaaa550055555552a802aaaaaa954015555554aa00,0x1bf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7ed),(0x50ccccccc6628666666633143333333198a19999998cc50ccccccc6628666666633143333333198a19999998cc50ccccccc6628,0x36adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b),(0x1343c3c3c21e9a1e1e1e10f4d0f0f0f087a6878787843d343c3c3c21e9a1e1e1e10f4d0f0f0f087a6878787843d343c3c3c21e9a,0xe63f1cc7e398fc731f8e63f1cc7e398fc731f8e63f1cc7e398fc731f8e63f1cc7e398fc731f8e63f1cc7e398fc731f8e63f1cc7),(0x30c03fc03e018601fe01f00c300ff00f8061807f807c030c03fc03e018601fe01f00c300ff00f8061807f807c030c03fc03e0186,0x3e1fffc3fff87fff0fffe1fffc3fff87fff0fffe1fffc3fff87fff0fffe1fffc3fff87fff0fffe1fffc3fff87fff0fffe1fffc3f),(0xfc0003ffe007e0001fff003f0000fff801f80007ffc00fc0003ffe007e0001fff003f0000fff801f80007ffc00fc0003ffe007e,0x1fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ffe07ffc0fff81fff03ff),(0x3fc0000001fffe0000000ffff00000007fff80000003fffc0000001fffe0000000ffff00000007fff80000003fffc0000001fffe,0x3fff8ffff1fffe3fffc7fff8ffff1fffe3fffc7fff8ffff1fffe3fffc7fff8ffff1fffe3fffc7fff8ffff1fffe3fffc7fff8ffff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(18,16),(3,1),(9,6),(18,3)]) (by decide) (by decide +kernel)
end Origin9
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin9
namespace OrbCore9
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 45))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1211100f0e0d0c0b0a09080706050403020100 8 (i.val % 19))
def H0 := pairHom p0 n0
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t4 := table 6 3 0 1 0x0 0x0 0 0x0 0x0 1
def t5 := table 6 2 2 32 0xaf54142fed04d522 0x0 2 0x3787836844fb 0x8 4
def t6 := table 6 1 7 19 0x1dd48bba17f732ffe87ffd0c7fa98ff53f 0x0 7 0x1b61b67467dd570a9192115ad38e195e71681364b 0x30a00810608 6
def t7 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore9
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin9
namespace OrbCore9
abbrev q5 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 4 t4 (TableLeafQ.body full (t5.desc i))=true
set_option maxRecDepth 8192 in
theorem b5a0 : SpanQ.Block q5 0 2 := by decide +kernel
theorem ready5 : OrbitQ.all full 5 t5 := by
  have prev : OrbitQ.all full 4 t4:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot prev t5
  have g : SpanQ.Block q5 0 2 := b5a0
  intro i
  simpa only [q5,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 7 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready5 t6
  have g : SpanQ.Block q6 0 7 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 7 full := by
  have eq : TableLeafQ.body full (t7.desc 0)=full := by decide +kernel
  have h:=ready7 ⟨0,by decide⟩
  change (TableLeafQ.body full (t7.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore9
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core9
def st9 : List Sig := [(0x200aaaaaaa550055555552a802aaaaaa954015555554aa00aaaaaaa550055555552a802aaaaaa954015555554aa00aaaaaaa5500,0x1bf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7edb6fdb6dfb6dbf6db7ed),(0x228666666633143333333198a19999998cc50ccccccc6628666666633143333333198a19999998cc50ccccccc662866666663314,0x36adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b6dab6db56db6adb6d5b),(0x165e1e1e1ef0b2f0f0f0f78597878787bc2cbc3c3c3de165e1e1e1ef0b2f0f0f0f78597878787bc2cbc3c3c3de165e1e1e1ef0b2,0x319c0e3381c67038ce0719c0e3381c67038ce0719c0e3381c67038ce0719c0e3381c67038ce0719c0e3381c67038ce0719c0e338),(0x279fe01fe0ff3cff00ff07f9e7f807f83fcf3fc03fc1fe79fe01fe0ff3cff00ff07f9e7f807f83fcf3fc03fc1fe79fe01fe0ff3c,0x1e0003c00078000f0001e0003c00078000f0001e0003c00078000f0001e0003c00078000f0001e0003c00078000f0001e0003c0),(0x381fffe000ffc0ffff0007fe07fff8003ff03fffc001ff81fffe000ffc0ffff0007fe07fff8003ff03fffc001ff81fffe000ffc0,0x3e000fc001f8003f0007e000fc001f8003f0007e000fc001f8003f0007e000fc001f8003f0007e000fc001f8003f0007e000fc00),(0x1fffffff0000fffffff80007ffffffc0003ffffffe0001fffffff0000fffffff80007ffffffc0003ffffffe0001fffffff0000,0x70000e0001c0003800070000e0001c0003800070000e0001c0003800070000e0001c0003800070000e0001c0003800070000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002c 8 (i.val % 45))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1211100f0e0d0c0b0a09080706050403020100 8 (i.val % 19))
def proj := pairHom pIndex nIndex
theorem e9 : excluded 7 st9 := by
  let w:=Origin9.full
  have low : rank 8 w := known OrbCore9.bound Origin9.needed Origin9.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core9
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin10
def full : List Sig := [(0x2aaaaaa95400aaaaaaa55002aaaaaa95400aaaaaaa55002aaaaaa95400aaaaaaa55002aaaaaa95400aaaaaaa55002aaaaaa95400,0x2f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bd),(0x19999998cd246666666334919999998cd246666666334919999998cd246666666334919999998cd246666666334919999998cd24,0x1ad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b),(0x78787843c921e1e1e10f24878787843c921e1e1e10f24878787843c921e1e1e10f24878787843c921e1e1e10f24878787843c92,0x39ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7e739f9ce7),(0x7f807c038e01fe01f00e3807f807c038e01fe01f00e3807f807c038e01fe01f00e3807f807c038e01fe01f00e3807f807c038e,0x3fc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1fff07ffc1f),(0x7ffc007e0001fff001f80007ffc007e0001fff001f80007ffc007e0001fff001f80007ffc007e0001fff001f80007ffc007e,0x383ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ffe0fff83ff),(0x3fffe0000000ffff80000003fffe0000000ffff80000003fffe0000000ffff80000003fffe0000000ffff80000003fffe,0x7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff1fffc7fff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(10,10),(10,5),(19,3)]) (by decide) (by decide +kernel)
end Origin10
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin10
namespace OrbCore10
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 46))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x11100f0e0d0c0b0a09080706050403020100 8 (i.val % 18))
def H0 := pairHom p0 n0
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t6 := table 6 1 0 1 0x0 0x0 0 0x0 0x0 1
def t7 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore10
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin10
namespace OrbCore10
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  have prev : OrbitQ.all full 6 t6:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot prev t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 7 full := by
  have eq : TableLeafQ.body full (t7.desc 0)=full := by decide +kernel
  have h:=ready7 ⟨0,by decide⟩
  change (TableLeafQ.body full (t7.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore10
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core10
def st0 : List Sig := [(0x15555554aa0055555552a8015555554aa0055555552a8015555554aa0055555552a8015555554aa0055555552a8015555554aa00,0x2f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bdbdef6f7bd),(0xccccccc6692333333319a48ccccccc6692333333319a48ccccccc6692333333319a48ccccccc6692333333319a48ccccccc6692,0x1ad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b6b5adad6b),(0x3c3c3c3de1b6f0f0f0f786dbc3c3c3de1b6f0f0f0f786dbc3c3c3de1b6f0f0f0f786dbc3c3c3de1b6f0f0f0f786dbc3c3c3de1b6,0x631818c60631818c60631818c60631818c60631818c60631818c60631818c60631818c60631818c60631818c60631818c606318),(0x3fc03fc1fe38ff00ff07f8e3fc03fc1fe38ff00ff07f8e3fc03fc1fe38ff00ff07f8e3fc03fc1fe38ff00ff07f8e3fc03fc1fe38,0x3e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e000f8003e0),(0x3fffc001ffc0ffff0007ff03fffc001ffc0ffff0007ff03fffc001ffc0ffff0007ff03fffc001ffc0ffff0007ff03fffc001ffc0,0x7c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c001f0007c00),(0x3ffffffe0000fffffff80003ffffffe0000fffffff80003ffffffe0000fffffff80003ffffffe0000fffffff80003ffffffe0000,0x38000e00038000e00038000e00038000e00038000e00038000e00038000e00038000e00038000e00038000e00038000e00038000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002d 8 (i.val % 46))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x11100f0e0d0c0b0a09080706050403020100 8 (i.val % 18))
def proj := pairHom pIndex nIndex
theorem e0 : excluded 7 st0 := by
  let w:=Origin10.full
  have low : rank 8 w := known OrbCore10.bound Origin10.needed Origin10.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core10
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin14
def full : List Sig := [(0x2aa8555542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550,0x36b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d),(0x26183330c199860ccc30666183330c199860ccc30666183330c199860ccc30666183330c199860ccc30666183330c199860ccc30,0x2dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedb),(0x21850f0c28786143c30a1e1850f0c28786143c30a1e1850f0c28786143c30a1e1850f0c28786143c30a1e1850f0c28786143c30a,0x23fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7),(0x1f8300fc1807e0c03f0601f8300fc1807e0c03f0601f8300fc1807e0c03f0601f8300fc1807e0c03f0601f8300fc1807e0c03f06,0x1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3f),(0x7f0003f8001fc000fe0007f0003f8001fc000fe0007f0003f8001fc000fe0007f0003f8001fc000fe0007f0003f8001fc000fe,0x3f9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff3fe7fcff9ff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(4,6),(4,3),(8,2)]) (by decide) (by decide +kernel)
end Origin14
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin14
namespace OrbCore14
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x14131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 21))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa09080706050403020100 8 (i.val % 11))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1413120d0c0b0a11100f0e09080706050402030100 8 (i.val % 21))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa09050403080706020100 8 (i.val % 11))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t4 := table 5 2 0 1 0x0 0x0 0 0x0 0x0 1
def t5 := table 5 1 2 18 0xfd08bf42f 0x0 4 0xb9fc6ec97c994a8bf0a0467 0x8901 4
def t6 := table 5 0 1 5 0x1f 0x0 0 0x0 0x0 1
end OrbCore14
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin14
namespace OrbCore14
abbrev q5 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 4 t4 (TableLeafQ.body full (t5.desc i))=true
set_option maxRecDepth 8192 in
theorem b5a0 : SpanQ.Block q5 0 2 := by decide +kernel
theorem ready5 : OrbitQ.all full 5 t5 := by
  have prev : OrbitQ.all full 4 t4:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot prev t5
  have g : SpanQ.Block q5 0 2 := b5a0
  intro i
  simpa only [q5,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 1 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready5 t6
  have g : SpanQ.Block q6 0 1 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 6 full := by
  have eq : TableLeafQ.body full (t6.desc 0)=full := by decide +kernel
  have h:=ready6 ⟨0,by decide⟩
  change (TableLeafQ.body full (t6.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore14
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core14
def st4 : List Sig := [(0x15542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550aaaa8555542aaaa155550aaaa8,0x36b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d6dadb5b6b6d),(0x330c199860ccc30666183330c199860ccc30666183330c199860ccc30666183330c199860ccc30666183330c199860ccc3066618,0x2dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedb),(0xf3d7879ebc3cf5e1e7af0f3d7879ebc3cf5e1e7af0f3d7879ebc3cf5e1e7af0f3d7879ebc3cf5e1e7af0f3d7879ebc3cf5e1e7a,0x1c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c038),(0x303e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07c,0x201c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0),(0x3fc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80,0x600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a0908070605040302010014 8 (i.val % 21))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa09080706050403020100 8 (i.val % 11))
def proj := pairHom pIndex nIndex
theorem e4 : excluded 6 st4 := by
  let w:=Origin14.full
  have low : rank 7 w := known OrbCore14.bound Origin14.needed Origin14.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core14
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin24
def full : List Sig := [(0x155128aaaaaa8aa89455555545544a2aaaaaa2aa251555555155128aaaaaa8aa89455555545544a2aaaaaa2aa251555555155128,0x1bbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeedd),(0xcc8846666664664423333332332211999999199108cccccc8cc8846666664664423333332332211999999199108cccccc8cc884,0x3f777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfb),(0x3c4621e1e1e21e2310f0f0f10f11887878788788c43c3c3c43c4621e1e1e21e2310f0f0f10f11887878788788c43c3c3c43c462,0x36eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7),(0x3c1e01fe01e01e0f00ff00f00f07807f80780783c03fc03c03c1e01fe01e01e0f00ff00f00f07807f80780783c03fc03c03c1e,0x31ffe3ffc7ff8fff1ffe3ffc7ff8fff1ffe3ffc7ff8fff1ffe3ffc7ff8fff1ffe3ffc7ff8fff1ffe3ffc7ff8fff1ffe3ffc7ff8f),(0x3fe0001ffe001ff0000fff000ff80007ff8007fc0003ffc003fe0001ffe001ff0000fff000ff80007ff8007fc0003ffc003fe,0xffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87f),(0x3ffffe0000001fffff0000000fffff80000007ffffc0000003ffffe0000001fffff0000000fffff80000007ffffc0000003ffffe,0x3fe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff0ffe1ffc3ff87ff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(5,2),(14,4),(26,4)]) (by decide) (by decide +kernel)
end Origin24
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin24
namespace OrbCore24
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 49))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xe0d0c0b0a09080706050403020100 8 (i.val % 15))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x302f2e2d2c2b2a29282726252423221514131211100f0e0d0c0b0a21201f1e1d1c1b1a1918171609080706050403020100 8 (i.val % 49))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa0908070e0d0c0b06050403020100 8 (i.val % 15))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2d2f2b302c2e2a2925272328242622211d1f1b201c1e1a191617181511130f1410120e0d0a0b0c09060708050401020300 8 (i.val % 49))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xc0d0e0b08090a0705060401020300 8 (i.val % 15))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2d2f2b302c2e2a29252723282426221511130f1410120e0d0a0b0c211d1f1b201c1e1a1916171809060708050401020300 8 (i.val % 49))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x8090a070c0d0e0b05060401020300 8 (i.val % 15))
def H3 := pairHom p3 n3
def p4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x21291915090d042f1f271713070b023020281814080c032e1e26122d1d251611060a012b1b230f2c1c2410052a1a220e00 8 (i.val % 49))
def n4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xe060a030c0508010d09020b040700 8 (i.val % 15))
def H4 := pairHom p4 n4
def p5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x15290d210919042f13270b1f0717023014280c200818032e12261e2d11250a1d0616012b0f231b2c10241c052a0e221a00 8 (i.val % 49))
def n5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa060e0308050c01090d0207040b00 8 (i.val % 15))
def H5 := pairHom p5 n5
def p6 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x21291915090d042f1f271713070b022d1d251611060a012b1b230f3020281814080c032e1e26122c1c2410052a1a220e00 8 (i.val % 49))
def n6 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xc0508010e060a030d09020b040700 8 (i.val % 15))
def H6 := pairHom p6 n6
def p7 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x15290d210919042f13270b1f0717022d11250a1d0616012b0f231b3014280c200818032e12261e2c10241c052a0e221a00 8 (i.val % 49))
def n7 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x8050c010a060e03090d0207040b00 8 (i.val % 15))
def H7 := pairHom p7 n7
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 2 zero,full.getD 1 zero,full.getD 0 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 2 zero,full.getD 1 zero,full.getD 0 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H3,by decide +kernel,by decide +kernel⟩
def raw4 := [full.getD 4 zero,full.getD 3 zero,full.getD 5 zero,full.getD 1 zero,full.getD 0 zero,full.getD 2 zero]
set_option maxRecDepth 8192 in
def rot4 : Rot full := ⟨raw4,H4,H4,by decide +kernel,by decide +kernel⟩
def raw5 := [full.getD 4 zero,full.getD 3 zero,full.getD 5 zero,full.getD 1 zero,full.getD 2 zero,full.getD 0 zero]
set_option maxRecDepth 8192 in
def rot5 : Rot full := ⟨raw5,H5,H6,by decide +kernel,by decide +kernel⟩
def raw6 := [full.getD 5 zero,full.getD 3 zero,full.getD 4 zero,full.getD 1 zero,full.getD 0 zero,full.getD 2 zero]
set_option maxRecDepth 8192 in
def rot6 : Rot full := ⟨raw6,H6,H5,by decide +kernel,by decide +kernel⟩
def raw7 := [full.getD 5 zero,full.getD 3 zero,full.getD 4 zero,full.getD 1 zero,full.getD 2 zero,full.getD 0 zero]
set_option maxRecDepth 8192 in
def rot7 : Rot full := ⟨raw7,H7,H7,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else if i=2 then rot2 else if i=3 then rot3 else if i=4 then rot4 else if i=5 then rot5 else if i=6 then rot6 else if i=7 then rot7 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t4 := table 6 5 0 1 0x0 0x0 0 0x0 0x0 1
def t5 := table 6 4 2 55 0x3d8b7bb7b2d8817b16f76f65b10f 0x0 6 0x3b49bd4e02847bf67a7b3468a620b132363 0x6e84c 4
def t6 := table 6 3 9 45 0x1c313f31f20bedb2881d887f6d97c0ec43fb6ca207e217db65f03f10bde82fb2d8816f417d96c43cfeedecb62047f76f65b10f 0x0 22 0x3ca5af771becd2c5699f0806ef20b5a47dea0286f39ce126f262cddccf988824e2a0796a1b2a4a5a84609ea8a848c94cee118e8c20dcfe254a983919a02817e 0x1ca90830b1060e101e5021a14381874000c5098 7
def t7 := table 6 2 35 32 0xeb31f20bf901131bf901f31bf502120bf502f20bed03d302ed03b302ed03210fed03b10fed03110bed03f10bdd04120bdd04f20bdd04110bdd04f10bbd05120bbd05f20bbd05110bbd05f10bfd04d102fd04f10bfd02d312ff652102ff65f102ff65b102ff541102ff542102ff65210fff65f10fff65b10fff54110fff54210fff54f10fff54110bff54f10b 0x0 76 0xfd7345f530fbe3e0cfbfe9df2888de40fabbd1c9f62487ec48e3d0f863a117173b7e5dc19039ed98731695661d40ca3f7190db471bf82e201f8c19c1d75e79ec3676580d5caa253f4d12fa8ac77d0490f9f852d3cef9269c714cdead955e7725e832432d2c6e191867aef083dedfdda7bf99a77ece16f39865da2b33affaa74159ae72165caf7bb6cba96a4dc2ca0ad590b8731d4c061c2cebf4ef5255eb227b6e42e03c83b274f973f1ea7f23cbc4e76372ce2e411bf185340ca06647a4c32ce9760082e5ad85a10a0a71ba937ad820bcfc395b8059085074127 0x44904e088161a0a811400045004843e22021120249040814103c0e0c8f9d1001b36122d0602408c6033418bc612c04040005806010a84c8b9310c70019025678428383813110a00c1e2e0c839180d0b8a03c125910e 9
def t8 := table 6 1 17 19 0x7f20bfe41ffd00bfa07ff40bfe625fcc7ff98dff301fe605fcc3ff985ff202fe203fc40bf887ff10b 0x0 60 0xfef1c7f137ffc81f5760ebce87bcfc84a438ad926fcbdedc5657b5630f6570f6a24b3d384b5a04a2b15cc161ea2ec243e979eb2edcd8eda5821b18fa95e235a9aa96d333bba3d12b4636de522e6ca13318d1368e6c23dbe51036e8386ccbc8ca124d89f4dad83a65936e6ae131548526a708a84d3b569a36e501e119d9a2037f1e86e7960c818317958a2da18c57a74c9a846134e9e25c1f64b711c64fe98a12f812ec8220e40c3fc32808f0e 0x26850804861340c14421c6b2c63061062323a777138701a3e24267c46080069580a73362a300e8404756a44183c1672202e1278224076745c601e28 8
def t9 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore24
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin24
namespace OrbCore24
abbrev q5 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 4 t4 (TableLeafQ.body full (t5.desc i))=true
set_option maxRecDepth 8192 in
theorem b5a0 : SpanQ.Block q5 0 2 := by decide +kernel
theorem ready5 : OrbitQ.all full 5 t5 := by
  have prev : OrbitQ.all full 4 t4:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot prev t5
  have g : SpanQ.Block q5 0 2 := b5a0
  intro i
  simpa only [q5,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 9 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready5 t6
  have g : SpanQ.Block q6 0 9 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b7a16 : SpanQ.Block q7 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b7a32 : SpanQ.Block q7 32 3 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 35 := (SpanQ.glue b7a0 (SpanQ.glue b7a16 b7a32))
  intro i
  simpa only [q7,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 7 t7 (TableLeafQ.body full (t8.desc i))=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a16 : SpanQ.Block q8 16 1 := by decide +kernel
theorem ready8 : OrbitQ.all full 8 t8 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready7 t8
  have g : SpanQ.Block q8 0 17 := (SpanQ.glue b8a0 b8a16)
  intro i
  simpa only [q8,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 8 t8 (TableLeafQ.body full (t9.desc i))=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 1 := by decide +kernel
theorem ready9 : OrbitQ.all full 9 t9 := by
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot ready8 t9
  have g : SpanQ.Block q9 0 1 := b9a0
  intro i
  simpa only [q9,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 9 full := by
  have eq : TableLeafQ.body full (t9.desc 0)=full := by decide +kernel
  have h:=ready9 ⟨0,by decide⟩
  change (TableLeafQ.body full (t9.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore24
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403six
def st281 : List Sig := [(0xaa89455555545544a2aaaaaa2aa251555555155128aaaaaa8aa89455555545544a2aaaaaa2aa251555555155128aaaaaa8aa894,0x1bbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeeddddbbbb7776eeedd),(0x664423333332332211999999199108cccccc8cc8846666664664423333332332211999999199108cccccc8cc884666666466442,0x3f777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfbbbf777eeefdddfb),(0x1e1dcef0f0f0ef0ee7787878778773bc3c3c3bc3b9de1e1e1de1dcef0f0f0ef0ee7787878778773bc3c3c3bc3b9de1e1e1de1dce,0x9111222244448889111222244448889111222244448889111222244448889111222244448889111222244448889111222244448),(0x1fe1f0ff00ff0ff0f87f807f87f87c3fc03fc3fc3e1fe01fe1fe1f0ff00ff0ff0f87f807f87f87c3fc03fc3fc3e1fe01fe1fe1f0,0xe001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c00380070),(0x1ffe00ffff000fff007fff8007ff803fffc003ffc01fffe001ffe00ffff000fff007fff8007ff803fffc003ffc01fffe001ffe00,0x3001e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c00780),(0x200000fffffff000007ffffff800003ffffffc00001ffffffe00000fffffff000007ffffff800003ffffffc00001ffffffe00000,0x1e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c007800f001e003c007800)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010030 8 (i.val % 49))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xe0d0c0b0a09080706050403020100 8 (i.val % 15))
def proj := pairHom pIndex nIndex
theorem e281 : excluded 9 st281 := by
  let w:=Origin24.full
  have low : rank 10 w := known OrbCore24.bound Origin24.needed Origin24.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403six
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin34
def full : List Sig := [(0x155555428a00aaaaaa145005555550a2802aaaaa85140155555428a00aaaaaa145005555550a2802aaaaa85140155555428a00,0x3dfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfd),(0xa8cccccd1a6546666668d32a33333346995199999a34ca8cccccd1a6546666668d32a33333346995199999a34ca8cccccd1a654,0x2b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab),(0x2643c3c3c861321e1e1e430990f0f0f2184c87878790c2643c3c3c861321e1e1e430990f0f0f2184c87878790c2643c3c3c86132,0x3f339fe673fcce7f99cff339fe673fcce7f99cff339fe673fcce7f99cff339fe673fcce7f99cff339fe673fcce7f99cff339fe67),(0x21c03fc0381f0e01fe01c0f8700ff00e07c3807f80703e1c03fc0381f0e01fe01c0f8700ff00e07c3807f80703e1c03fc0381f0e,0x270ffce1ff9c3ff387fe70ffce1ff9c3ff387fe70ffce1ff9c3ff387fe70ffce1ff9c3ff387fe70ffce1ff9c3ff387fe70ffce1f),(0x1fc0003ff800fe0001ffc007f0000ffe003f80007ff001fc0003ff800fe0001ffc007f0000ffe003f80007ff001fc0003ff800fe,0x20fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1ff),(0x3fc0000007fffe0000003ffff0000001ffff8000000ffffc0000007fffe0000003ffff0000001ffff8000000ffffc0000007fffe,0x1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff07ffe0fffc1fff83fff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(4,1),(9,3),(22,5)]) (by decide) (by decide +kernel)
end Origin34
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin34
namespace OrbCore34
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 45))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1211100f0e0d0c0b0a09080706050403020100 8 (i.val % 19))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2c2b2a252423222928272621201f1e1211100f0c0b0a090e0d081d1c1b1a151419181716130706030205040100 8 (i.val % 45))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xd0c0b0a091211100f0e080704030605020100 8 (i.val % 19))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t5 := table 6 2 0 1 0x0 0x0 0 0x0 0x0 1
def t6 := table 6 1 2 19 0x3d90ffb101 0x0 3 0x1fc0a9b370f9902051 0x980 4
def t7 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore34
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin34
namespace OrbCore34
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 2 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  have prev : OrbitQ.all full 5 t5:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot prev t6
  have g : SpanQ.Block q6 0 2 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 7 full := by
  have eq : TableLeafQ.body full (t7.desc 0)=full := by decide +kernel
  have h:=ready7 ⟨0,by decide⟩
  change (TableLeafQ.body full (t7.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore34
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core34
def st3 : List Sig := [(0x200aaaaaa145005555550a2802aaaaa85140155555428a00aaaaaa145005555550a2802aaaaa85140155555428a00aaaaaa14500,0x3dfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfdef7fbdeff7bdfef7bfd),(0x2546666668d32a33333346995199999a34ca8cccccd1a6546666668d32a33333346995199999a34ca8cccccd1a6546666668d32a,0x2b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab5ad56b5aad6b55ad6ab),(0x2cde1e1e1bcf66f0f0f0de7b37878786f3d9bc3c3c379ecde1e1e1bcf66f0f0f0de7b37878786f3d9bc3c3c379ecde1e1e1bcf66,0xcc60198c03318066300cc60198c03318066300cc60198c03318066300cc60198c03318066300cc60198c03318066300cc60198),(0xf1fe01fe3f078ff00ff1f83c7f807f8fc1e3fc03fc7e0f1fe01fe3f078ff00ff1f83c7f807f8fc1e3fc03fc7e0f1fe01fe3f078,0x18f0031e0063c00c78018f0031e0063c00c78018f0031e0063c00c78018f0031e0063c00c78018f0031e0063c00c78018f0031e0),(0x301fffe003ff80ffff001ffc07fff800ffe03fffc007ff01fffe003ff80ffff001ffc07fff800ffe03fffc007ff01fffe003ff80,0x1f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e00),(0x1ffffffc0000ffffffe00007ffffff00003ffffff80001ffffffc0000ffffffe00007ffffff00003ffffff80001ffffffc0000,0x20007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f0003e0007c000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002c 8 (i.val % 45))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1211100f0e0d0c0b0a09080706050403020100 8 (i.val % 19))
def proj := pairHom pIndex nIndex
theorem e3 : excluded 7 st3 := by
  let w:=Origin34.full
  have low : rank 8 w := known OrbCore34.bound Origin34.needed Origin34.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core34
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin38
def full : List Sig := [(0x2a48555242aa92155490aaa48555242aa92155490aaa48555242aa92155490aaa48555242aa92155490aaa48555242aa92155490,0x1edbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbd),(0x262233311199888ccc446662233311199888ccc446662233311199888ccc446662233311199888ccc446662233311199888ccc44,0x35beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb),(0x21190f08c8784643c2321e1190f08c8784643c2321e1190f08c8784643c2321e1190f08c8784643c2321e1190f08c8784643c232,0x33f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67),(0x1f0700f83807c1c03e0e01f0700f83807c1c03e0e01f0700f83807c1c03e0e01f0700f83807c1c03e0e01f0700f83807c1c03e0e,0xff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1f),(0xff0007f8003fc001fe000ff0007f8003fc001fe000ff0007f8003fc001fe000ff0007f8003fc001fe000ff0007f8003fc001fe,0x3f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(4,2),(10,3)]) (by decide) (by decide +kernel)
end Origin38
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin38
namespace OrbCore38
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x14131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 21))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa09080706050403020100 8 (i.val % 11))
def H0 := pairHom p0 n0
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t5 := table 5 1 0 1 0x0 0x0 0 0x0 0x0 1
def t6 := table 5 0 1 5 0x1f 0x0 0 0x0 0x0 1
end OrbCore38
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin38
namespace OrbCore38
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_16 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 1 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  have prev : OrbitQ.all full 5 t5:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x16 valid_full rot fixedRot prev t6
  have g : SpanQ.Block q6 0 1 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_16eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 6 full := by
  have eq : TableLeafQ.body full (t6.desc 0)=full := by decide +kernel
  have h:=ready6 ⟨0,by decide⟩
  change (TableLeafQ.body full (t6.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore38
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core38
def st0 : List Sig := [(0x15242aa92155490aaa48555242aa92155490aaa48555242aa92155490aaa48555242aa92155490aaa48555242aa92155490aaa48,0x1edbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbdb7b6f6dedbd),(0x3311199888ccc446662233311199888ccc446662233311199888ccc446662233311199888ccc446662233311199888ccc4466622,0x35beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fadf5beb),(0xf73787b9bc3dcde1ee6f0f73787b9bc3dcde1ee6f0f73787b9bc3dcde1ee6f0f73787b9bc3dcde1ee6f0f73787b9bc3dcde1ee6,0xc0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c098),(0x307c7f83e3fc1f1fe0f8ff07c7f83e3fc1f1fe0f8ff07c7f83e3fc1f1fe0f8ff07c7f83e3fc1f1fe0f8ff07c7f83e3fc1f1fe0f8,0x300e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),(0x3f807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a0908070605040302010014 8 (i.val % 21))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xa09080706050403020100 8 (i.val % 11))
def proj := pairHom pIndex nIndex
theorem e0 : excluded 6 st0 := by
  let w:=Origin38.full
  have low : rank 7 w := known OrbCore38.bound Origin38.needed Origin38.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core38
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Origin96
def full : List Sig := [(0x2108aaaa8442108aaaa8442108aaaa8442108aaaa8442108aaaa8442108aaaa8442108aaaa8442108aaaa8442108aaaa8442108,0x3ffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffd),(0x294a4666652294a4666652294a4666652294a4666652294a4666652294a4666652294a4666652294a4666652294a4666652294a4,0x36dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76db),(0x18c621e1e3118c621e1e3118c621e1e3118c621e1e3118c621e1e3118c621e1e3118c621e1e3118c621e1e3118c621e1e3118c62,0x2db76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb76edb7),(0x7c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e01fe0f07c1e,0x238f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f1e38f),(0x3fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe0001ff003fe,0x207ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07ffe07f),(0x3fffe000000ffffe000000ffffe000000ffffe000000ffffe000000ffffe000000ffffe000000ffffe000000ffffe000000ffffe,0x1fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff01fff)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needed : necessary full:=needFrom (pn:=[(1,2),(1,1),(2,1),(5,1),(10,1),(29,7)]) (by decide) (by decide +kernel)
end Origin96
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ Origin96
namespace OrbCore96
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 44))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 20))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2b28272a2926252423201f22211e1d1c1b191a1817161415131210110f0e0d0b0c0a09080607050403010200 8 (i.val % 44))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1213110f100e0d0b0c0a08090705060402030100 8 (i.val % 20))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t4 := table 6 3 0 1 0x0 0x0 0 0x0 0x0 1
def t5 := table 6 2 3 32 0xd721f31fdd020301dd02d301 0x0 5 0x70180cd5b1917e48ee51283c90bb9 0x880029 5
def t6 := table 6 1 4 19 0xde63fbcc07f880ff10f 0x0 7 0x1950f8b027c95ac0e79a7f66cae248a620788ddbd 0x430106528 5
def t7 := table 6 0 1 6 0x3f 0x0 0 0x0 0x0 1
end OrbCore96
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ Origin96
namespace OrbCore96
abbrev q5 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 4 t4 (TableLeafQ.body full (t5.desc i))=true
set_option maxRecDepth 8192 in
theorem b5a0 : SpanQ.Block q5 0 3 := by decide +kernel
theorem ready5 : OrbitQ.all full 5 t5 := by
  have prev : OrbitQ.all full 4 t4:=by intro i;exact Fin.elim0 i
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot prev t5
  have g : SpanQ.Block q5 0 3 := b5a0
  intro i
  simpa only [q5,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q6 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 5 t5 (TableLeafQ.body full (t6.desc i))=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 4 := by decide +kernel
theorem ready6 : OrbitQ.all full 6 t6 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready5 t6
  have g : SpanQ.Block q6 0 4 := b6a0
  intro i
  simpa only [q6,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := ShapeQ.nodeS rot UnrollQ.s64_32 6 t6 (TableLeafQ.body full (t7.desc i))=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  apply CoreCheck8403.up good_ch64x32 valid_full rot fixedRot ready6 t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,UnrollQ.s64_32eq,ShapeQ.nodeSEq,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 7 full := by
  have eq : TableLeafQ.body full (t7.desc 0)=full := by decide +kernel
  have h:=ready7 ⟨0,by decide⟩
  change (TableLeafQ.body full (t7.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCore96
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403
namespace Proof8403core96
def st13 : List Sig := [(0x21084555542210845555422108455554221084555542210845555422108455554221084555542210845555422108455554221084,0x3ffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffdfbffd),(0x14a5233332914a5233332914a5233332914a5233332914a5233332914a5233332914a5233332914a5233332914a5233332914a52,0x36dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76dbb76db),(0x339cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739cef0f0e7739ce,0x12489124891248912489124891248912489124891248912489124891248912489124891248912489124891248912489124891248),(0x3c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0ff00f87c1f0,0x1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70e1c70),(0x3fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00ffff007fe00,0x1f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f8001f80),(0xffffff80000ffffff80000ffffff80000ffffff80000ffffff80000ffffff80000ffffff80000ffffff80000ffffff80000,0x2000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000)]
def pIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002b 8 (i.val % 44))
def nIndex (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 20))
def proj := pairHom pIndex nIndex
theorem e13 : excluded 7 st13 := by
  let w:=Origin96.full
  have low : rank 8 w := known OrbCore96.bound Origin96.needed Origin96.valid_full (by decide +kernel)
  apply CoreCheck8403.rechart proj low
  decide +kernel
end Proof8403core96
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403 Mono8403 Fit8403
namespace FitRoots8403
def v5 : List Sig := [neg (Proof8403core5.st33.getD 0 zero),Proof8403core5.st33.getD 1 zero,Proof8403core5.st33.getD 2 zero,neg (Proof8403core5.st33.getD 3 zero),Proof8403core5.st33.getD 4 zero,Proof8403core5.st33.getD 5 zero]
lemma valid_v5 : ∀a∈v5,Valid a := by
  have h : v5.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n5 : necessary Proof8403core5.st33:=needFrom (pn:=[(0,8),(4,12),(16,16),(0,1),(4,2),(16,4)]) (by decide) (by decide +kernel)
def base5 : Basis := ⟨v5,8,valid_v5,level_of_rank (known Proof8403core5.e33 n5 valid_v5 (by decide +kernel))⟩
def v6 : List Sig := [neg (Proof8403core6.st21.getD 0 zero),neg (Proof8403core6.st21.getD 1 zero),Proof8403core6.st21.getD 2 zero,Proof8403core6.st21.getD 3 zero,Proof8403core6.st21.getD 4 zero,Proof8403core6.st21.getD 5 zero]
lemma valid_v6 : ∀a∈v6,Valid a := by
  have h : v6.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
def base6 : Basis := ⟨v6,9,valid_v6,level_of_rank (known Proof8403core6.e21 n6 valid_v6 (by decide +kernel))⟩
def v9 : List Sig := [neg (Proof8403core9.st9.getD 0 zero),neg (Proof8403core9.st9.getD 1 zero),Proof8403core9.st9.getD 2 zero,Proof8403core9.st9.getD 3 zero,Proof8403core9.st9.getD 4 zero,Proof8403core9.st9.getD 5 zero]
lemma valid_v9 : ∀a∈v9,Valid a := by
  have h : v9.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n9 : necessary Proof8403core9.st9:=needFrom (pn:=[(0,2),(0,1),(17,16),(2,1),(8,6),(17,3)]) (by decide) (by decide +kernel)
def base9 : Basis := ⟨v9,8,valid_v9,level_of_rank (known Proof8403core9.e9 n9 valid_v9 (by decide +kernel))⟩
def v10 : List Sig := [neg (Proof8403core10.st0.getD 0 zero),neg (Proof8403core10.st0.getD 1 zero),Proof8403core10.st0.getD 2 zero,Proof8403core10.st0.getD 3 zero,Proof8403core10.st0.getD 4 zero,Proof8403core10.st0.getD 5 zero]
lemma valid_v10 : ∀a∈v10,Valid a := by
  have h : v10.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n10 : necessary Proof8403core10.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(9,10),(9,5),(18,3)]) (by decide) (by decide +kernel)
def base10 : Basis := ⟨v10,8,valid_v10,level_of_rank (known Proof8403core10.e0 n10 valid_v10 (by decide +kernel))⟩
def v14 : List Sig := [neg (Proof8403core14.st4.getD 0 zero),neg (Proof8403core14.st4.getD 1 zero),Proof8403core14.st4.getD 2 zero,Proof8403core14.st4.getD 3 zero,Proof8403core14.st4.getD 4 zero]
lemma valid_v14 : ∀a∈v14,Valid a := by
  have h : v14.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n14 : necessary Proof8403core14.st4:=needFrom (pn:=[(0,2),(0,1),(3,6),(3,3),(7,2)]) (by decide) (by decide +kernel)
def base14 : Basis := ⟨v14,7,valid_v14,level_of_rank (known Proof8403core14.e4 n14 valid_v14 (by decide +kernel))⟩
def v24 : List Sig := [neg (Proof8403six.st281.getD 0 zero),neg (Proof8403six.st281.getD 1 zero),Proof8403six.st281.getD 2 zero,Proof8403six.st281.getD 3 zero,Proof8403six.st281.getD 4 zero,Proof8403six.st281.getD 5 zero]
lemma valid_v24 : ∀a∈v24,Valid a := by
  have h : v24.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n24 : necessary Proof8403six.st281:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,2),(13,4),(25,4)]) (by decide) (by decide +kernel)
def base24 : Basis := ⟨v24,10,valid_v24,level_of_rank (known Proof8403six.e281 n24 valid_v24 (by decide +kernel))⟩
def v34 : List Sig := [neg (Proof8403core34.st3.getD 0 zero),neg (Proof8403core34.st3.getD 1 zero),Proof8403core34.st3.getD 2 zero,Proof8403core34.st3.getD 3 zero,Proof8403core34.st3.getD 4 zero,Proof8403core34.st3.getD 5 zero]
lemma valid_v34 : ∀a∈v34,Valid a := by
  have h : v34.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
def base34 : Basis := ⟨v34,8,valid_v34,level_of_rank (known Proof8403core34.e3 n34 valid_v34 (by decide +kernel))⟩
def v38 : List Sig := [neg (Proof8403core38.st0.getD 0 zero),neg (Proof8403core38.st0.getD 1 zero),Proof8403core38.st0.getD 2 zero,Proof8403core38.st0.getD 3 zero,Proof8403core38.st0.getD 4 zero]
lemma valid_v38 : ∀a∈v38,Valid a := by
  have h : v38.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n38 : necessary Proof8403core38.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,2),(9,3)]) (by decide) (by decide +kernel)
def base38 : Basis := ⟨v38,7,valid_v38,level_of_rank (known Proof8403core38.e0 n38 valid_v38 (by decide +kernel))⟩
def v96 : List Sig := [neg (Proof8403core96.st13.getD 0 zero),neg (Proof8403core96.st13.getD 1 zero),Proof8403core96.st13.getD 2 zero,Proof8403core96.st13.getD 3 zero,Proof8403core96.st13.getD 4 zero,Proof8403core96.st13.getD 5 zero]
lemma valid_v96 : ∀a∈v96,Valid a := by
  have h : v96.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma n96 : necessary Proof8403core96.st13:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,1),(9,1),(28,7)]) (by decide) (by decide +kernel)
def base96 : Basis := ⟨v96,8,valid_v96,level_of_rank (known Proof8403core96.e13 n96 valid_v96 (by decide +kernel))⟩
def small (i : Nat) := #[base5,base6,base9,base10,base14,base24,base34,base38,base96].getD i base5
end FitRoots8403
end
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD1Data
def full : List Sig := [(0x2aaaaaeaaaab5fffc183aaaaaaaaaaaaaaeaaaab5fffc183aaaaaaaaaaaaaaeaaaab5fffc183aaaaaaaaaaaaaaeaaaab5fffc183,0x4925555492004925555492004925555492004925555492004925555492004925555492004925555492004925555492004925555),(0xcccccf333339aaf4081ccccccccccccccf333339aaf4081ccccccccccccccf333339aaf4081ccccccccccccccf333339aaf4081,0x2924aaaa924aa924aaaa924aa924aaaa924aa924aaaa924aa924aaaa924aa924aaaa924aa924aaaa924aa924aaaa924aa924aaaa),(0x30f0f0bc3c3decca0204f0f0f0f0f0f0f0bc3c3decca0204f0f0f0f0f0f0f0bc3c3decca0204f0f0f0f0f0f0f0bc3c3decca0204,0xe383cf3e00cce383cf3e00cce383cf3e00cce383cf3e00cce383cf3e00cce383cf3e00cce383cf3e00cce383cf3e00cce383cf3),(0x3f00ff3fc03e0f0c0810ff00ff00ff00ff3fc03e0f0c0810ff00ff00ff00ff3fc03e0f0c0810ff00ff00ff00ff3fc03e0f0c0810,0xfc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf038f0fc0f3cf),(0x3fff003fffc00ff0952affff0000ffff003fffc00ff0952affff0000ffff003fffc00ff0952affff0000ffff003fffc00ff0952a,0x30002082000ff0002082000ff0002082000ff0002082000ff0002082000ff0002082000ff0002082000ff0002082000ff0002082),(0x3ffffff000264cffffffff0000003ffffff000264cffffffff0000003ffffff000264cffffffff0000003ffffff000264c,0xc30c03f00000c30c03f00000c30c03f00000c30c03f00000c30c03f00000c30c03f00000c30c03f00000c30c03f00000c30c),(0x3fffffc0000000003870ffffffffffffffc0000000003870ffffffffffffffc0000000003870ffffffffffffffc0000000003870,0xc30fc0000000c30fc0000000c30fc0000000c30fc0000000c30fc0000000c30fc0000000c30fc0000000c30fc0000000c30)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(2,36),(4,42),(1,17),(2,19),(4,22)]) (by decide) (by decide +kernel)
lemma need9 : necessary Proof8403core9.st9:=needFrom (pn:=[(0,2),(0,1),(17,16),(2,1),(8,6),(17,3)]) (by decide) (by decide +kernel)
def raw17 : List Sig :=
  let w:=Proof8403core9.st9
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 5 zero,w.getD 4 zero]
def h17 := SmallHom8403.make 45 0x676665646362616057565554535251062d2c2b2a29282703201f1e021c47464544434241053736171615011100 19 0x26252405042d2c2b2a1f1e1d1c151413121110
set_option maxRecDepth 8192 in
lemma image17 : full.map h17.fn=raw17 := by decide +kernel
def m17 : Slice full := ⟨raw17,8,h17,image17,level_of_rank (known Proof8403core9.e9 need9 (SmallHom8403.validImage h17 image17) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m17]
end MonoD1Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD1Data
namespace OrbM1
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x6f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251064f4e4d4c4b4a494847464544434241053f3e3d3c3b3a390437363534333231302f2e2d2c2b2a292827032524232221201f1e021c1b1a1918171615011312110001000605040302010006050403020100 8 (i.val % 112))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x5042d2c2b2a030227262524012221201f1e1d1c1b001918171615141312111003020100050403020100050403020100 8 (i.val % 48))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x6f6e6d6c676665646b6a6968636261605f5e5d5c575655545b5a595853525106353433322d2c2b2a31302f2e2928270325242322201f1e02211c4f4e4d4c474645444b4a4948434241053f3e3d3c373b3a3904361b1a1716191815011311120001000603020504010006030205040100 8 (i.val % 112))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x3022726252405042d2c2b2a01221f1e21201d1c1b001915141318171612111005040100030205040100030205040100 8 (i.val % 48))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 4 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1].getD i rot0
def t6 := table 7 2 0 1 0x0 0x0 0 0x0 0x0 1
def t7 := table 7 1 2 20 0xf7424ef534 0x21 4 0x9e01712e4055b6f971186c0 0x1809 4
def t8 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbM1
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD1Data
namespace OrbM1
abbrev q7 (i : Nat) := FrontQ.testM rot t6 m17 ms 7 t7 i=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 2 := by decide +kernel
theorem ready7 : OrbitQ.Mono.all full 7 t7 := by
  have prev : OrbitQ.Mono.all full 6 t6:=by intro i;exact Fin.elim0 i
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot prev m17 ms t7
  have g : SpanQ.Block q7 0 2 := b7a0
  intro i
  simpa only [q7,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := FrontQ.testM rot t7 m17 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 1 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready7 m17 ms t8
  have g : SpanQ.Block q8 0 1 := b8a0
  intro i
  simpa only [q8,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 8 full := by
  have eq : MonoDeck8403.fromDesc full (t8.desc 0)=full := by decide +kernel
  have h:=ready8 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t8.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbM1
end
namespace MonoD1Data
theorem bound : Mono8403.rejects 8 full := OrbM1.bound
end MonoD1Data
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD2Data
def full : List Sig := [(0x2af55555d7fff0707aaaaaaaaaaaaaaf55555d7fff0707aaaaaaaaaaaaaaf55555d7fff0707aaaaaaaaaaaaaaf55555d7fff0707,0x25555108040255551080402555510804025555108040255551080402555510804025555108040255551080402555510804025555),(0xcb9999966ad50101ccccccccccccccb9999966ad50101ccccccccccccccb9999966ad50101ccccccccccccccb9999966ad50101,0xaaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaaa52a954aaaa),(0x30de1e1e7b3660a0af0f0f0f0f0f0f0de1e1e7b3660a0af0f0f0f0f0f0f0de1e1e7b3660a0af0f0f0f0f0f0f0de1e1e7b3660a0a,0x28a2c03319828a2c03319828a2c03319828a2c03319828a2c03319828a2c03319828a2c03319828a2c03319828a2c03319828a2),(0x3f1fe01f83c782424ff00ff00ff00ff1fe01f83c782424ff00ff00ff00ff1fe01f83c782424ff00ff00ff00ff1fe01f83c782424,0xa28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a063c1e0a28a),(0x1fffe003f805050ffff0000ffff001fffe003f805050ffff0000ffff001fffe003f805050ffff0000ffff001fffe003f805050,0x30c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3003fe0030c3),(0x1ffffffc0009898ffffffff0000001ffffffc0009898ffffffff0000001ffffffc0009898ffffffff0000001ffffffc0009898,0xc30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c07c0000c30c),(0x3fe0000000000e0e0ffffffffffffffe0000000000e0e0ffffffffffffffe0000000000e0e0ffffffffffffffe0000000000e0e0,0xc30f8000000c30f8000000c30f8000000c30f8000000c30f8000000c30f8000000c30f8000000c30f8000000c30f8000000c30)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(2,17),(4,34),(3,19),(5,21)]) (by decide) (by decide +kernel)
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
def raw6 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h6 := SmallHom8403.make 48 0x71706d6c6968656461605d5c5958550751504d4c4948450641403d053a363532312e2d2a0426252320031c1a18150201 16 0x2a0427250222201e1c00191715131110
set_option maxRecDepth 8192 in
lemma image6 : full.map h6.fn=raw6 := by decide +kernel
def m6 : Slice full := ⟨raw6,9,h6,image6,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h6 image6) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m6]
end MonoD2Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD2Data
namespace OrbM2
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565507535251504f4e4d4c4b4a494847464506434241403f3e3d053b3a393837363534333231302f2e2d2c2b2a04282726252423222120031e1d1c1b1a1918171615140212010007060504030201000706050403020100 8 (i.val % 116))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x52a290427032524022201201f1e1d1c1b001918171615141312111003020100050403020100050403020100 8 (i.val % 44))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x737271706b6a69686f6e6d6c67666564636261605b5a59585f5e5d5c5756550738373635302f2e2d343332312c2b2a04282726252221200324231e535251504b4a49484f4e4d4c47464506434241403b3a3f3e3d05391d1c19181b1a171615120114020007040306050102000704030605010200 8 (i.val % 116))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x325240222052a29042701201d1c1f1e1b001918171413161512111005040100030205040100030205040100 8 (i.val % 44))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 4 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1].getD i rot0
def t7 := table 7 2 0 1 0x0 0x0 0 0x0 0x0 1
def t8 := table 7 1 7 20 0xfb214fb100ff654ff650ff544ff534ff424 0x42108421 11 0x1faa7e39be8d638ae39d5e8f2c1dcd4839728708445ec1a477a783b33e029cb9 0x11c10008a18c49801 6
def t9 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbM2
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD2Data
namespace OrbM2
abbrev q8 (i : Nat) := FrontQ.testM rot t7 m6 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 7 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  have prev : OrbitQ.Mono.all full 7 t7:=by intro i;exact Fin.elim0 i
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot prev m6 ms t8
  have g : SpanQ.Block q8 0 7 := b8a0
  intro i
  simpa only [q8,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testM rot t8 m6 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 1 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready8 m6 ms t9
  have g : SpanQ.Block q9 0 1 := b9a0
  intro i
  simpa only [q9,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 9 full := by
  have eq : MonoDeck8403.fromDesc full (t9.desc 0)=full := by decide +kernel
  have h:=ready9 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t9.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbM2
end
namespace MonoD2Data
theorem bound : Mono8403.rejects 9 full := OrbM2.bound
end MonoD2Data
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD4Data
def full : List Sig := [(0x1555d6db7f0e07aaaaaaaaaaaaaaf55555d6db7f0e07aaaaaaaaaaaaaaf55555d6db7f0e07aaaaaaaaaaaaaaf55555d6db7f0e07,0x152a108402952a108402952a108402952a108402952a108402952a108402952a108402952a108402952a108402952a108402952a),(0x1999676dd51209ccccccccccccccb99999676dd51209ccccccccccccccb99999676dd51209ccccccccccccccb99999676dd51209,0x28d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1a5015468d1),(0x1e1e7b8e662412f0f0f0f0f0f0f0de1e1e7b8e662412f0f0f0f0f0f0f0de1e1e7b8e662412f0f0f0f0f0f0f0de1e1e7b8e662412,0x22c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5c0299862c5),(0x201f83f0788844ff00ff00ff00ff1fe01f83f0788844ff00ff00ff00ff1fe01f83f0788844ff00ff00ff00ff1fe01f83f0788844,0xa950631e04a950631e04a950631e04a950631e04a950631e04a950631e04a950631e04a950631e04a950631e04a950631e04a95),(0x3fe003ff8050a8ffff0000ffff001fffe003ff8050a8ffff0000ffff001fffe003ff8050a8ffff0000ffff001fffe003ff8050a8,0x306003e008306003e008306003e008306003e008306003e008306003e008306003e008306003e008306003e008306003e008306),(0x3ffffc00006130ffffffff0000001ffffffc00006130ffffffff0000001ffffffc00006130ffffffff0000001ffffffc00006130,0xc1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c1807c0000c18),(0x81c0ffffffffffffffe0000000000081c0ffffffffffffffe0000000000081c0ffffffffffffffe0000000000081c0,0x3060f800003060f800003060f800003060f800003060f800003060f800003060f800003060f800003060f800003060f800003060)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(2,17),(3,18),(4,19),(6,21)]) (by decide) (by decide +kernel)
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
lemma need14 : necessary Proof8403core14.st4:=needFrom (pn:=[(0,2),(0,1),(3,6),(3,3),(7,2)]) (by decide) (by decide +kernel)
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
lemma need38 : necessary Proof8403core38.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,2),(9,3)]) (by decide) (by decide +kernel)
def raw6 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h6 := SmallHom8403.make 48 0x757471706d6c6968656461605d5c5908555451504d4c4907454441063e3a39363532312e052a292724041f1c19150201 16 0x26052321031e021c1b01191715131110
set_option maxRecDepth 8192 in
lemma image6 : full.map h6.fn=raw6 := by decide +kernel
def m6 : Slice full := ⟨raw6,9,h6,image6,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h6 image6) (by decide +kernel))⟩
def raw12 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,w.getD 5 zero]
def h12 := SmallHom8403.make 48 0x737271706b6a6968535251504b4a4907636261605b5a5908434241063d38373635302f2e051e1d1c1803282722140200 16 0x2505231c0119042120031e1615121110
set_option maxRecDepth 8192 in
lemma image12 : full.map h12.fn=raw12 := by decide +kernel
def m12 : Slice full := ⟨raw12,9,h12,image12,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h12 image12) (by decide +kernel))⟩
def raw14 : List Sig :=
  let w:=Proof8403core14.st4
  [neg (w.getD 0 zero),zero,zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero]
def h14 := SmallHom8403.make 21 0x717069686160590851504907410636352e05271c02 11 0x52321031e1c0119151110
set_option maxRecDepth 8192 in
lemma image14 : full.map h14.fn=raw14 := by decide +kernel
def m14 : Slice full := ⟨raw14,7,h14,image14,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h14 image14) (by decide +kernel))⟩
def raw20 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 4 zero,w.getD 5 zero,w.getD 3 zero]
def h20 := SmallHom8403.make 48 0x6f6e6d6c6b6a696834333231302f2e055f5e5d5c5b5a590826252404224f4e4d4c4b4a49071b1a1918033f3e3d120100 16 0x20031e1b011906262505231413121110
set_option maxRecDepth 8192 in
lemma image20 : full.map h20.fn=raw20 := by decide +kernel
def m20 : Slice full := ⟨raw20,9,h20,image20,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h20 image20) (by decide +kernel))⟩
def raw22 : List Sig :=
  let w:=Proof8403core14.st4
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 4 zero,w.getD 3 zero]
def h22 := SmallHom8403.make 21 0x6d6c69685d5c590832312e0524044d4c49073e1901 11 0x31e2605231b0119131110
set_option maxRecDepth 8192 in
lemma image22 : full.map h22.fn=raw22 := by decide +kernel
def m22 : Slice full := ⟨raw22,7,h22,image22,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h22 image22) (by decide +kernel))⟩
def raw28 : List Sig :=
  let w:=Proof8403core14.st4
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,zero,w.getD 4 zero,w.getD 2 zero,w.getD 3 zero]
def h28 := SmallHom8403.make 21 0x6b6a69684b4a4907302f2e0518035b5a59083d2200 11 0x11925052320031e121110
set_option maxRecDepth 8192 in
lemma image28 : full.map h28.fn=raw28 := by decide +kernel
def m28 : Slice full := ⟨raw28,7,h28,image28,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h28 image28) (by decide +kernel))⟩
def raw36 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero,w.getD 5 zero]
def h36 := SmallHom8403.make 45 0x67666564636261605f5e5d5c5b5a590847464544434241063f3e3d2c2b2a292827262524042216151402120100 19 0x626250523042120031e001716151413121110
set_option maxRecDepth 8192 in
lemma image36 : full.map h36.fn=raw36 := by decide +kernel
def m36 : Slice full := ⟨raw36,8,h36,image36,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h36 image36) (by decide +kernel))⟩
def raw38 : List Sig :=
  let w:=Proof8403core38.st0
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 4 zero]
def h38 := SmallHom8403.make 21 0x656461605d5c5908454441063e2a29272404150201 11 0x26052321031e1715131110
set_option maxRecDepth 8192 in
lemma image38 : full.map h38.fn=raw38 := by decide +kernel
def m38 : Slice full := ⟨raw38,7,h38,image38,level_of_rank (known Proof8403core38.e0 need38 (SmallHom8403.validImage h38 image38) (by decide +kernel))⟩
def raw68 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),w.getD 2 zero,neg (w.getD 1 zero),w.getD 3 zero,w.getD 4 zero,zero,w.getD 5 zero]
def h68 := SmallHom8403.make 45 0x57565352555451504f4e4b4a4d4c490747464342454441063f3d3e21201e1d1f1c1b1a18031916141502120001 19 0x625260523021c1b0119001617151412131110
set_option maxRecDepth 8192 in
lemma image68 : full.map h68.fn=raw68 := by decide +kernel
def m68 : Slice full := ⟨raw68,8,h68,image68,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h68 image68) (by decide +kernel))⟩
def raw76 : List Sig :=
  let w:=Proof8403core38.st0
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero]
def h76 := SmallHom8403.make 21 0x535251504b4a4907434241063d1e1d1c1803140200 11 0x2505231c01191615121110
set_option maxRecDepth 8192 in
lemma image76 : full.map h76.fn=raw76 := by decide +kernel
def m76 : Slice full := ⟨raw76,7,h76,image76,level_of_rank (known Proof8403core38.e0 need38 (SmallHom8403.validImage h76 image76) (by decide +kernel))⟩
def raw132 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),w.getD 2 zero,w.getD 3 zero,neg (w.getD 1 zero),w.getD 4 zero,w.getD 5 zero,zero]
def h132 := SmallHom8403.make 45 0x3c3b34333a3932313837302f36352e052c2b26252a29240428222721201b1a1f191e1d18031c16121501140002 19 0x42021031e021b1c0119001417131612151110
set_option maxRecDepth 8192 in
lemma image132 : full.map h132.fn=raw132 := by decide +kernel
def m132 : Slice full := ⟨raw132,8,h132,image132,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h132 image132) (by decide +kernel))⟩
def raw148 : List Sig :=
  let w:=Proof8403core38.st0
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 4 zero,zero]
def h148 := SmallHom8403.make 21 0x34333231302f2e0526252404221b1a191803120100 11 0x20031e1b01191413121110
set_option maxRecDepth 8192 in
lemma image148 : full.map h148.fn=raw148 := by decide +kernel
def m148 : Slice full := ⟨raw148,7,h148,image148,level_of_rank (known Proof8403core38.e0 need38 (SmallHom8403.validImage h148 image148) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m6,m12,m14,m20,m22,m28,m36,m38,m68,m76,m132,m148]
end MonoD4Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD4Data
namespace OrbFitM4
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x77767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a590857565554535251504f4e4d4c4b4a490747464544434241063f3e3d3c3b3a393837363534333231302f2e052c2b2a292827262524042221201f1e1d1c1b1a1918031615140212010006050403020100080706050403020100 8 (i.val % 120))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x626250523042120031e021c1b011900171615141312111001000605040302010006050403020100 8 (i.val % 40))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x777675746f6e6d6c737271706b6a6968676665645f5e5d5c636261605b5a59083c3b3a393433323138373635302f2e052c2b2a2926252404282722575655544f4e4d4c535251504b4a4907474645443f3e434241063d21201f1b1a191e1d1c18031615120114020004070603010200080504070603010200 8 (i.val % 120))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x42120031e0626250523021b1c011900171413161512111001000403060502010004030605020100 8 (i.val % 40))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x77767372757471706f6e6b6a6d6c696857565352555451504f4e4b4a4d4c490767666362656461605f5e5b5a5d5c590847464342454441063f3d3e3c3b38373a3936353433302f32312e0521201e1d1f1c1b1a1803192c2b282a292726252224041614150212000106050304020001070806050304020001 8 (i.val % 120))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x625260523021c1b0119042120031e00161715141213111003000605020104030006050201040300 8 (i.val % 40))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x77766f6e75746d6c73726b6a717069683c3b34333a3932313837302f36352e0567665f5e65645d5c63625b5a616059082c2b26252a29240428222757564f4e55544d4c53524b4a5150490721201b1a1f191e1d18031c47463f45443e43423d41061612150114000204070306010002050804070306010002 8 (i.val % 120))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x42021031e021b1c0119062625052300141713161215111005000403020106050004030201060500 8 (i.val % 40))
def H3 := pairHom p3 n3
def p4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x777673726f6e6b6a757471706d6c6968575653524f4e4b4a555451504d4c49073c3b38373433302f3a39363532312e0521201e1d1b1a18031f1c19676663625f5e5b5a656461605d5c5908474643423f3d454441063e2c2b282625222a292724041614120015020103080604000201070503080604000201 8 (i.val % 120))
def n4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x21c1b01190625260523042021031e00161412171513111003000201060504030002010605040300 8 (i.val % 40))
def H4 := pairHom p4 n4
def p5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x77766f6e73726b6a75746d6c717069683c3b34333837302f3a39323136352e0557564f4e53524b4a55544d4c5150490721201b1a1e1d18031f191c67665f5e63625b5a65645d5c616059082c2b262528222a2924042747463f43423d45443e41061612140015010203080406000102050703080406000102 8 (i.val % 120))
def n5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x21b1c0119042021031e062526052300141612171315111005000201040306050002010403060500 8 (i.val % 40))
def H5 := pairHom p5 n5
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 4 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 0 zero,full.getD 2 zero,full.getD 3 zero,full.getD 1 zero,full.getD 5 zero,full.getD 6 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H4,by decide +kernel,by decide +kernel⟩
def raw4 := [full.getD 0 zero,full.getD 3 zero,full.getD 1 zero,full.getD 2 zero,full.getD 6 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot4 : Rot full := ⟨raw4,H4,H3,by decide +kernel,by decide +kernel⟩
def raw5 := [full.getD 0 zero,full.getD 3 zero,full.getD 2 zero,full.getD 1 zero,full.getD 6 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot5 : Rot full := ⟨raw5,H5,H5,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1,rot2,rot3,rot4,rot5].getD i rot0
def t5 := table 7 6 0 1 0x0 0x0 0 0x0 0x0 1
def extra5 (i : Nat) := getWord 0x0 1 i
def t6 := table 7 5 1 72 0x933120874734534214 0x0 1 0x13d5e8 0x0 0
def extra6 (i : Nat) := getWord 0x0 0 i
def t7 := table 7 4 14 59 0x3d1baa01002210a7e387402004421493f0e8e68a68429a741c20d14d0853ca82a438010202793120844324104f26240c88648209e64041cd14d08536a83a4380102026d3120734524404fa22090e00408096e42002114d0851ba83001203a2a04f5020734654424 0x2002100010001f 15 0x1c797072c0185a11ceb1fbb7397fbe654b7b8c46d70943ea23d151e56e20f6132be1ba5412a09a509903a89 0xe3018b00345050820109320430 7
def extra7 (i : Nat) := getWord 0x42130536 31 i
def t8 := table 7 3 121 46 0x3f1024060404fce190051503f3834014540fd40901c1513f3764014540fcd950051503f3644014540f3e111c90853cf740724214f3c0c14d0853cf834534214f3dcd14d0853cf630534214f3e110c90413cf644324104dbdcd1491011ef864724214fa40c0191013eb084024540fac150091503e9010624414fac110091503e9010724214fae1d0091503eb874020404fae1c0081013eb864024540fae140091503eb844024540fac041c90853eb834054214fac481c90853ed034070544fb40c0051513eb764024540fadd90081013eb754024540fadd50081013eb120624414fac041891053eb130624404fadcd0150853eb724024540fad950091503eb644024540fb40c0051093eb644020404fad890091503ed034760404fad510091503eb520024540fb4181c908535f844534404d7dd114d10135f764534214d7d081951093d9044070424f640414d0853db844010424f6e110150853dd010734424f6c5014d1013db644074214f6c4814d0853db010534214f6d910110853dd044760414f74111d81013df844634404f7e1114d1013dd084534214f741c14d0853dd044760104eee190111503bb834044540ef41501c1513bb764044540eec541911013bb150644104eed910111503bb6240445401fe1d1d515127f8746544249fdcd19510917f874754544de40414d101379010654424de41901c15137b010654424dec0414d10137d010654424df4191d810537d060764404df4191d810137d064760104bec5c1951092fb170644424bf41c01d1091fb0500745407ec0d01d1501fb0540745407ec0901d1501fb0640745407ee1401d1501fb8340745407f4200111511fb7640745407ed9501d1501fb6440745407ed8901d1501fb5340745407ed4801d1501fb434074540fe40d01d1503f9010764424fe4041951093f9010624424fe41901c1513fb764044214fe4190191003f9064034400 0x1f3a00939c020800100000fa1084092001c8a100600250902101024e7020e0511000005f0fc1f1006100000001403a009210e70000010be21081f0014a0110001c88024e73a0884005ff80e2 186 0x3ffd607f2987fe5215f99897f0ae77ded3ffaa0b9f2de63e576afc55bff7aef9e727efc595c788b91ef168bdbe237b6433f6495dea173fce0b5794dbdf29187e3404bc670e78a4cbf097fbe115ddbfd41b7a7c86e6801d86723b0abe7403dae644cbcaf0a193966f1f82adf4b34be622b7c0fbef4217dd9e02ba7b67741aa2dffa4db810bb5a2c768e692cfe3ed9bd15b2c8bb6515c6c8824587f57af6ad55e8e4ab234ad5627ca920ab51431a954f051bce0a31f753f717a7434e4d43bc96f6db2b12424aa3947672c8c87b3139bda21d28443373882c891024c61557dc22095840e3503f80a0686e40ac6d80205eff97b5f530dbdad5c79db40f1e341e2970bc0c97754386ea0b5dd34ae3a2fa8740ebce80f81cdd26b99be3729b88e41bd9bf3d137c47e6d76e6daa7b1b5005b694216ba6eacffde19fc1bb226ea63f4a8c74f358c8bcb146d660f4c8bfea91713ddaded875a8e26a92ddd462a4270c424c6f2e9651351e385a383e746b34a8cb451146da22360444404a87edbd0d0bfa1929b420b04831319060b5a094453ee8d877da3ce50c11b973736bd446d0518cf3a119ae8732fbae651cb4c01e717cbbf2eeaa65dcf68b69e71625772b7050562c08a7be214cbd8288d924fab3c9c3f193658126b52848ad2c8622e90a4932038183974ec6f3ce0cb67e196106323828640a78b76ad15bd64230fc84604508397d0ef28c199d9021a7d03f80e03a356017f080283b80153a 0x5ead84d095e6a44803b0528d8c21ace82887c03a24e30611a4c01e526208702788a05aa02c8721e19a1e8d41d53c09248938d01e9370c018b28e42386a448ce3206a0d4d0cc8cc368561b45c9988800bb83881a0204635a5e0d0d8140b45e35c2f004599885e0922a058052e2d2048401ae2b004378eeb3a2a3487b532b08ece4a983a2d0ba2f86219220a10e02a8c6359895f868438868a0e60906f0581a8b0605d054080601b8961480a1106e47098030dc2bac42d386088b0040f01d84c009061081e3736c4034a2506c240849427a8e09ebb23e0509c19d2459074e905a0aa2e1f5403a8ee060 10
def extra8 (i : Nat) := getWord (joinBits (joinBits (joinBits 0x4f521306 612 0x453120f1) 1548 0xf4513026000000000435120f4100000000054f310226) 2160 (joinBits (joinBits 0xf4123056 180 0x4523100f6) 1008 (0x4f5213036f45123056 <<< 108))) 36 i
def t9 := table 7 2 157 33 0x1f9014540fd80a2a07ed851013f6a28209f5024540fa8102027dc091503eec48829f7020404fbb9210a7dd480853ee648209ef734424f7a9a10a7bcc41093ba088a81df044540dfbaa2a26fd9510937ea68809bf5244047e83a2a03fc1d1503fa0c0829fd030414fe80820a7f4101503fa040a81fd060400fe83a2a07f4111503fa048a81fd014540fe8382a07f41d1513fa0e0a89fd040544fe83220a7f4081513fa020a89fd070424fe8202127f4081093fa020849fd064404fe8302027f40c1013fa040809fd074214fe83810a7f4150853fa0a0429fd040214fe80810a7f41d1093fa0c0849fd044214fe8320827f4180413fa0a8209fd050104ff83a2a27fc1c1513fe080a89ff024544ff8102a27fc041513fe028a89ff044544ffbaa2a27fdd01513fee40a89ff074540ff8222a07fc051503feea8a81ff740540ffb2a2a07fd501513fe0e0849ff064424ff8222127fc101093fe040849ff010424ff8122127fc1d1093fe0c0849ff014424ffbb22127fdd81093feea8849ff750424ffba02127fdcd1093fee60849ff720424ffb2a2127fd941093fec88849ff640424ffb182127fd891093fec40849ff544424ffaa02127fd4c1513fea60849ff764414ffbb020a7fd951053fec88829ff624414ffa9a20a7fd481513fea40849ff060404ffbb22027fdd81013feca8809ff650404ffb222027fd8d1013fec48809ff534404ffa922027fdd91003feca8801ff644400ffb122007fd4d1003fe860849ff420544ffa102127fd041513fe820a81ff410424ffbaa10a7fdd40853fee48429ff654214ffb2810a7fd510853fea68429ff320544ff9902127fcc41093fa068209fd030104ffbb20827fdd80413feca8209ff644104ffb120827fd4d0413fe420a89ff210424 0x483e0fa400007e0008090001f0250241027001004ffe4f87ff207e0f883f1fd041fd5ffffe8000800fc00010294a4e4493e00103f00140028072084101c041002020840020014043f0000707c0047cff41c8421084020204004210be2003e00fc21 260 0xff9ff1fda29ffa7297f3852fdb7f3fb6a1ff622bfe31a6fbd8a7f6784fec2bf7d3f86f9e069f371dbe660bfbec67f7a757ec3307d6b8cfab58cf35ae7e55d5bc3591f80b18eeee01ddaadfbb16e7735b6ed4a55d89edfaa93b752834e9735fd2b127a523174223ce825d1cfb28b9e4ff737212e4fb81c66a5b89c0671059be1e2cfbbf593771f36ec422dcb04fb7ab6b6d2be6d9f2edac4f1b1b617629786c02d8d7f219aec6e35b445eb15bcd5e445aac28754cee699a4ed2dd29a097bf40b50678008cee6c39bd9932f3c765a836cb4a8b9207f3086af608bb8c015fd7ed372f43645e668dbcb93375b21eeb45add21a0b9eb89735142e2513d9cf5fb32b5766061eca2b8d92bf6b22be15dc486ba36fd743fbacf55959c6daaf454d49c6ba7b61b4e938e9922352fe4ba5effb48932a8f3b951e3c9a36d47451162861c6d058f8a0130b4025c2800c44f0d359d200934d19e66ac8cbb8f9976e012eb17651aa5c9b816930ae1258d5648b4bc8f1368c786116534a2c0b5c580f787410f0d1b0e0f446c1c39681f30702713e04dcbc07b447eeeaaf846d9ef1d6bd9d7c797252f0aefddebc4badf6575b234e878f9c7d9b38dfd46f7024dcea01b6a1736a71c6d3b40d9a6a1ae37ab5773b6abfc4d52d31a950d34ffd869f9e8d03a9d9d0d1336dde66b662cc37fd9701fb2556463da9ac5767d8a4293119c45f3984bd54757970b2f0c435bebdab756ad6e6ecadcb085a861cb0c9a95dc212b8ba5566a84abbbd1526f3a962bb521114a29b2142dfc27a3094bc5088f89051e676a2d75545545e870a7902b562002583c482277d8d0ea4fe9d11ac39ef8a7296b4dcf889b66d43613846a379cd040d9967f031f4e2601e8cbf2d01775532e6e3c5c7cb4b263c958c892b01b6553034a5284940bf82670de48c7948e9fb91bb6d22c12a454da089577108bfa1fd9083defb0790330edadf1b54a033ef60636490b816613261c2558f0461928697bb0caef8190a8c2aa5b83f9780791c80f12d01cd4702a8a804e9b0066ce803239003a30 0x770681e8038428de0a44100542282c388252ba245018920e013c118690424001301d09815c458936a009420b4901e134311092fa10e0da51622c4c2a83001c88a3b26949c0b0088282d60492306a05b008ab0900da1b1880122f20a92d8191248f8429280121702f8034c658431a132c72341593a0ea1643601a082260320814400e4448662c60e6210651168f04a8930e60109d88a04423c4523312e16d3709847e0910682e4300dc4607d4bc1553d86212c014b522d20800c92a8100c1200716a2b4014340870a287a4b23204d0909d25805c650138150dc539300068ee47c168880ee8b0a8921134255178324e41d02ba2e08e26413c4b0588ed0b81210a1f00b03d02681e00a860cc10086a7e04299c1018928826881080039104c88310541e006084224dfc040952a40e04e04501c0042004a0b88be1a8430a62449588403a88e47036026c88a151411e812050308465c0b79540ec06104143b3620c49a51044890203 11
def extra9 (i : Nat) := getWord (joinBits (joinBits (joinBits (joinBits 0x45f231e06000000000000453120f1 596 (joinBits 0x45312f0e 360 0x34012f5e)) 804 0x345f120e10f451230f600000000000f451230e600000000000f451230f60f451230f6) 1560 (joinBits (joinBits (joinBits 0x4351f20f1000000000004f52130f6 196 0x345012fe000000000000345012fe) 364 0x4f52130e600000000000345012fe0045f2310e60f451230f60f451230e6) 800 (joinBits 0x4f521305f6 520 0x45f23103f6))) 3080 (joinBits (joinBits 0x4351f205f1 1280 0x45f23100f6) 1600 (joinBits (joinBits 0x345012f5e 244 0xf451230f4600000000004f52130f26) 1120 (joinBits (joinBits 0xf451230e6 160 0x45f2310e56) 200 (0x45f2310e36 <<< 80))))) 40 i
def t10 := table 7 1 12 20 0xff544ff540ff424ff420ff414ff410ff404ff400ff214ff210ff104ff100 0x20041f00801 42 0x3e8f99f0a663d4f335a9bbdf3ec98e08630b94c8f6a688eccdda54898fa460f142bf9e7ee2f4e5f5c9b9dbb3241ce5271fc91081904aaaf0325ddb423ba296e6a1e26c0580971f432855a8482ea28a2df8e57771999b42c73365895dca0a8893eacf25193245016c7e41b0e87b9195aea27615c42e7486d93b 0xcc874462aa1092043a30adb8592820c05258100088dbc2734550416544b994e25882d0c32 7
def extra10 (i : Nat) := getWord (0x345f120f1 <<< 136) 34 i
def t11 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
def extra11 (i : Nat) := getWord 0x0 0 i
end OrbFitM4
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD4Data
namespace OrbFitM4
abbrev q6 (i : Nat) := FrontQ.testF rot t5 (fun j=>ms.getD j m6) FitRoots8403.small 6 t6 extra6 i=true
set_option maxRecDepth 8192 in
theorem b6a0 : SpanQ.Block q6 0 1 := by decide +kernel
theorem ready6 : OrbitQ.Mono.all full 6 t6 := by
  have prev : OrbitQ.Mono.all full 5 t5:=by intro i;exact Fin.elim0 i
  apply FitOrbitQ.finish good_ch16x16 valid_full rot prev (fun j=>ms.getD j m6) FitRoots8403.small t6 extra6
  have g : SpanQ.Block q6 0 1 := b6a0
  intro i
  simpa only [q6,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q7 (i : Nat) := FrontQ.testF rot t6 (fun j=>ms.getD j m6) FitRoots8403.small 7 t7 extra7 i=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 14 := by decide +kernel
theorem ready7 : OrbitQ.Mono.all full 7 t7 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready6 (fun j=>ms.getD j m6) FitRoots8403.small t7 extra7
  have g : SpanQ.Block q7 0 14 := b7a0
  intro i
  simpa only [q7,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := FrontQ.testF rot t7 (fun j=>ms.getD j m6) FitRoots8403.small 8 t8 extra8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a16 : SpanQ.Block q8 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a32 : SpanQ.Block q8 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a48 : SpanQ.Block q8 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a64 : SpanQ.Block q8 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a80 : SpanQ.Block q8 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a96 : SpanQ.Block q8 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a112 : SpanQ.Block q8 112 9 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready7 (fun j=>ms.getD j m6) FitRoots8403.small t8 extra8
  have g : SpanQ.Block q8 0 121 := (SpanQ.glue (SpanQ.glue (SpanQ.glue b8a0 b8a16) (SpanQ.glue b8a32 b8a48)) (SpanQ.glue (SpanQ.glue b8a64 b8a80) (SpanQ.glue b8a96 b8a112)))
  intro i
  simpa only [q8,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testF rot t8 (fun j=>ms.getD j m6) FitRoots8403.small 9 t9 extra9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a32 : SpanQ.Block q9 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a48 : SpanQ.Block q9 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a64 : SpanQ.Block q9 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a80 : SpanQ.Block q9 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a96 : SpanQ.Block q9 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a112 : SpanQ.Block q9 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a128 : SpanQ.Block q9 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a144 : SpanQ.Block q9 144 13 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready8 (fun j=>ms.getD j m6) FitRoots8403.small t9 extra9
  have g : SpanQ.Block q9 0 157 := (SpanQ.glue (SpanQ.glue (SpanQ.glue b9a0 b9a16) (SpanQ.glue b9a32 (SpanQ.glue b9a48 b9a64))) (SpanQ.glue (SpanQ.glue b9a80 b9a96) (SpanQ.glue b9a112 (SpanQ.glue b9a128 b9a144))))
  intro i
  simpa only [q9,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testF rot t9 (fun j=>ms.getD j m6) FitRoots8403.small 10 t10 extra10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 12 := by decide +kernel
theorem ready10 : OrbitQ.Mono.all full 10 t10 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready9 (fun j=>ms.getD j m6) FitRoots8403.small t10 extra10
  have g : SpanQ.Block q10 0 12 := b10a0
  intro i
  simpa only [q10,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q11 (i : Nat) := FrontQ.testF rot t10 (fun j=>ms.getD j m6) FitRoots8403.small 11 t11 extra11 i=true
set_option maxRecDepth 8192 in
theorem b11a0 : SpanQ.Block q11 0 1 := by decide +kernel
theorem ready11 : OrbitQ.Mono.all full 11 t11 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready10 (fun j=>ms.getD j m6) FitRoots8403.small t11 extra11
  have g : SpanQ.Block q11 0 1 := b11a0
  intro i
  simpa only [q11,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 11 full := by
  have eq : MonoDeck8403.fromDesc full (t11.desc 0)=full := by decide +kernel
  have h:=ready11 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t11.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbFitM4
end
namespace MonoD4Data
theorem bound : Mono8403.rejects 11 full := OrbFitM4.bound
end MonoD4Data
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD8Data
def full : List Sig := [(0x2abddb6bd8b05d55555555555555d5555eedb5ec582eaaaaaaaaaaaaaaeaaaaf76daf62c1755555555555555755557bb6d7b160b,0x8949481081129290210225252042044a4a408408949481081129290210225252042044a4a40840894948108112929021022525),(0xcd6edbd6950ae66666666666666e6666b76deb4a85733333333333333733335bb6f5a542b99999999999999b9999addb7ad2a15,0x9121211201224242240244848448048909089009121211201224242240244848448048909089009121211201224242240244848),(0x30e771ce70603787878787878787787873b8e738301bc3c3c3c3c3c3c3bc3c39dc739c180de1e1e1e1e1e1e1de1e1cee39ce0c06,0x1224a4a245244949448a48929289149125251229224a4a245244949448a48929289149125251229224a4a245244949448a489292),(0xf87e0f848247f807f807f807f87f807c3f07c24123fc03fc03fc03fc3fc03e1f83e12091fe01fe01fe01fe1fe01f0fc1f09048,0x1c06868386380d0d070c701a1a0e18e034341c31c06868386380d0d070c701a1a0e18e034341c31c06868386380d0d070c701a1a),(0x3f007ff0030587fff80007fff8007fff803ff80182c3fffc0003fffc003fffc01ffc00c161fffe0001fffe001fffe00ffe0060b0,0x2000c0c007c00181800f800303001f000606003e000c0c007c00181800f800303001f000606003e000c0c007c00181800f800303),(0x3fff8000020907fffffff80000007fffffc000010483fffffffc0000003fffffe000008241fffffffe0000001ffffff000004120,0x70703f8000e0e07f0001c1c0fe00038381fc00070703f8000e0e07f0001c1c0fe00038381fc00070703f8000e0e07f0001c1c),(0x40e07ffffffffffffff8000000000020703ffffffffffffffc000000000010381ffffffffffffffe0000000000081c0,0x38383c00007070780000e0e0f00001c1c1e000038383c00007070780000e0e0f00001c1c1e000038383c00007070780000e0e0)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(3,17),(4,18),(5,23),(6,20)]) (by decide) (by decide +kernel)
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
lemma need9 : necessary Proof8403core9.st9:=needFrom (pn:=[(0,2),(0,1),(17,16),(2,1),(8,6),(17,3)]) (by decide) (by decide +kernel)
lemma need10 : necessary Proof8403core10.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(9,10),(9,5),(18,3)]) (by decide) (by decide +kernel)
lemma need14 : necessary Proof8403core14.st4:=needFrom (pn:=[(0,2),(0,1),(3,6),(3,3),(7,2)]) (by decide) (by decide +kernel)
lemma need24 : necessary Proof8403six.st281:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,2),(13,4),(25,4)]) (by decide) (by decide +kernel)
lemma need38 : necessary Proof8403core38.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,2),(9,3)]) (by decide) (by decide +kernel)
def raw10 : List Sig :=
  let w:=Proof8403core10.st0
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h10 := SmallHom8403.make 46 0x767572716e6d6a69666562615e5d5a08565552514e4d4a07464542063e3a39363532312e052a2825211e1b160301 18 0x7052304201f021c011a1900171614131110
set_option maxRecDepth 8192 in
lemma image10 : full.map h10.fn=raw10 := by decide +kernel
def m10 : Slice full := ⟨raw10,8,h10,image10,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h10 image10) (by decide +kernel))⟩
def raw12 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,w.getD 5 zero]
def h12 := SmallHom8403.make 48 0x747372716c6b6a69545352514c4b4a07646362615c5b5a08444342063d38373635302f2e05201f1e1a04292824150300 16 0x605231a001703201e021c1514121110
set_option maxRecDepth 8192 in
lemma image12 : full.map h12.fn=raw12 := by decide +kernel
def m12 : Slice full := ⟨raw12,9,h12,image12,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h12 image12) (by decide +kernel))⟩
def raw14 : List Sig :=
  let w:=Proof8403core14.st4
  [neg (w.getD 0 zero),zero,zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero]
def h14 := SmallHom8403.make 21 0x72716a6962615a0852514a07420636352e05281e03 11 0x52320021c1a0017141110
set_option maxRecDepth 8192 in
lemma image14 : full.map h14.fn=raw14 := by decide +kernel
def m14 : Slice full := ⟨raw14,7,h14,image14,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h14 image14) (by decide +kernel))⟩
def raw24 : List Sig :=
  let w:=Proof8403six.st281
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h24 := SmallHom8403.make 49 0x706f6e6d6c6b6a69605f5e5d5c5b5a08504f4e4d4c4b4a07403f3e3d34333231302f2e05272625241d1c1b1a0413020100 15 0x70605231f1e021c19001713121110
set_option maxRecDepth 8192 in
lemma image24 : full.map h24.fn=raw24 := by decide +kernel
def m24 : Slice full := ⟨raw24,10,h24,image24,level_of_rank (known Proof8403six.e281 need24 (SmallHom8403.validImage h24 image24) (by decide +kernel))⟩
def raw25 : List Sig :=
  let w:=Proof8403core14.st4
  [zero,neg (w.getD 1 zero),neg (w.getD 0 zero),zero,w.getD 4 zero,w.getD 2 zero,w.getD 3 zero]
def h25 := SmallHom8403.make 21 0x6f6b6d694f4b4d07332f31051c045f5b5d083f2602 11 0x19170607231e1f1c121310
set_option maxRecDepth 8192 in
lemma image25 : full.map h25.fn=raw25 := by decide +kernel
def m25 : Slice full := ⟨raw25,7,h25,image25,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h25 image25) (by decide +kernel))⟩
def raw40 : List Sig :=
  let w:=Proof8403core10.st0
  [w.getD 5 zero,w.getD 3 zero,w.getD 4 zero,w.getD 2 zero,zero,neg (w.getD 1 zero),neg (w.getD 0 zero)]
def h40 := SmallHom8403.make 46 0x682c481860274013662a46165e253e01642944155c243d00622842035a672b47175f263f0265455d63435b610608 18 0x2051104161f071303151e061220141c2310
set_option maxRecDepth 8192 in
lemma image40 : full.map h40.fn=raw40 := by decide +kernel
def m40 : Slice full := ⟨raw40,8,h40,image40,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h40 image40) (by decide +kernel))⟩
def raw72 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 4 zero,w.getD 5 zero,w.getD 3 zero,neg (w.getD 1 zero),w.getD 2 zero,zero,neg (w.getD 0 zero)]
def h72 := SmallHom8403.make 48 0x5823501d4818401354204c1a44153d0057224f1c47173f02531f4b044356214e1b46163e01521e4a4203554d45510706 16 0x15061200051101191607131a17142310
set_option maxRecDepth 8192 in
lemma image72 : full.map h72.fn=raw72 := by decide +kernel
def m72 : Slice full := ⟨raw72,9,h72,image72,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h72 image72) (by decide +kernel))⟩
def raw76 : List Sig :=
  let w:=Proof8403core38.st0
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero]
def h76 := SmallHom8403.make 21 0x545352514c4b4a07444342063d201f1e1a04150300 11 0x605231a00171514121110
set_option maxRecDepth 8192 in
lemma image76 : full.map h76.fn=raw76 := by decide +kernel
def m76 : Slice full := ⟨raw76,7,h76,image76,level_of_rank (known Proof8403core38.e0 need38 (SmallHom8403.validImage h76 image76) (by decide +kernel))⟩
def raw104 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 4 zero,w.getD 2 zero,w.getD 3 zero,neg (w.getD 1 zero),zero,zero,neg (w.getD 0 zero)]
def h104 := SmallHom8403.make 21 0x4818401346163e0144153d00420347173f02454306 11 0x511160713150612142310
set_option maxRecDepth 8192 in
lemma image104 : full.map h104.fn=raw104 := by decide +kernel
def m104 : Slice full := ⟨raw104,7,h104,image104,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h104 image104) (by decide +kernel))⟩
def raw136 : List Sig :=
  let w:=Proof8403core9.st9
  [w.getD 5 zero,w.getD 3 zero,w.getD 4 zero,w.getD 2 zero,neg (w.getD 0 zero),neg (w.getD 1 zero),zero]
def h136 := SmallHom8403.make 45 0x3c2c231834271d133a2a211632251b013829201530241a0036281e032e3b2b221733261c023931371f2f043505 19 0x200110401161f191303151e12201a141c1710
set_option maxRecDepth 8192 in
lemma image136 : full.map h136.fn=raw136 := by decide +kernel
def m136 : Slice full := ⟨raw136,8,h136,image136,level_of_rank (known Proof8403core9.e9 need9 (SmallHom8403.validImage h136 image136) (by decide +kernel))⟩
def raw152 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,zero,neg (w.getD 1 zero),neg (w.getD 0 zero),zero]
def h152 := SmallHom8403.make 21 0x341d2713331c2602301a24002f04321b2501312e05 11 0x1e12191f13000211171c10
set_option maxRecDepth 8192 in
lemma image152 : full.map h152.fn=raw152 := by decide +kernel
def m152 : Slice full := ⟨raw152,7,h152,image152,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h152 image152) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m10,m12,m14,m24,m25,m40,m72,m76,m104,m136,m152]
end MonoD8Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD8Data
namespace OrbFitM8
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x7877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a085857565554535251504f4e4d4c4b4a074847464544434206403f3e3d3c3b3a393837363534333231302f2e052c2b2a292827262524232221201f1e1d1c1b1a0418171615031302010006050403020100080706050403020100 8 (i.val % 121))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x70605230403201f1e021c011a1900171615141312111007060504030201000706050403020100 8 (i.val % 39))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x783c682c5823481870346027501d4013763a662a562146166e325e254e1b3e0174386429542044156c305c244c1a3d0072366228521e42036a2e5a4a773b672b572247176f335f264f1c3f0275396555456d315d4d733763531f436b2f5b4b0471356151066905080703020406050807010003020406050807 8 (i.val % 121))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x20005110401161f19071303151e0612201a141c17231002000504010703060200050401070306 8 (i.val % 39))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 6 zero,full.getD 4 zero,full.getD 5 zero,full.getD 3 zero,full.getD 1 zero,full.getD 2 zero,full.getD 0 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1].getD i rot0
def t6 := table 7 5 0 1 0x0 0x0 0 0x0 0x0 1
def extra6 (i : Nat) := getWord 0x0 1 i
def t7 := table 7 4 5 59 0x5b5080864034100aea1010c80882013d42002101504027a84043202a0805f1024070754100 0x0 5 0x7d4dc6e04dcd30958a007778697a3 0x18408020 6
def extra7 (i : Nat) := getWord 0x0 0 i
def t8 := table 7 3 62 46 0xfc40901c1413f1010614404fc4090140413f1024070404f340c14d08536f734534414dbe0d14910136f734524404f640418d1093d9010534214f641101c1093d9040074104f64100190413db834030104f6e1d00c0413db864030104f6dd900c0413db734030104f6e1c00d0403db834034100f6e1d00d0403db864034100f6dd900d0403db760034100f6dd500d0403db734034100f6d9500d0403b9050074104eec1d0110403bb064044100eee1c0110403bb834044100eee1d0110403bb864044100eedd90110403bb760044100eedcd011040379010534414de40414d10137b070054100dec2101504037b074054100de40414910137b054054100dee1c01504037b834054100dee1d01504037b864054100dedd901504037b760054100dedd501504037b734054100ded950150402f9010634504bee0d0190402fd0707541007edcd01d0403f9100624424fe40414d1053f9010724404fe4041891013f9064020404 0xe7ffc60000e3fffe3000033840001c81210a53840001c2211c00f90e10000720482080201001f 64 0xfff443f8e6a7b5822f4f6e7e98115c6521f78599eec270d9c1b3b2c2fb64b54ebe36bd4bcdd9717872bc4a5fb225a703d14a4e8e8402fcfbc098f6def1cda0e326364587e186efcd0d4209f68fcbc69a976eddce8b829c9b053911677157d4e127e9b48bb3641f969c1b2d140c19f9d1b1a60b5ec41cbd84c179965aeb3e55c8d949a0bdd2f477a51c784286d07c3b6cea60b9b1c1534fab0689198b070f9463a321b514411798806648906fc120b4c237908306d8045fb9 0xa0221c188282e02130c82c3417080101a078547a271b1003639070a84625168e03c12108ac761301818183c1717c60241981028190c01c0a37160d4520d00874443a1b040122f058 9
def extra8 (i : Nat) := getWord (joinBits (joinBits 0x3e468a63c4090d48 316 0x1e2046a8410d4483c421a890788) 1712 (joinBits 0xa843e066 664 0x53421f043)) 35 i
def t9 := table 7 2 180 33 0xfc80a2087edc51413f6028821fb714404fdb0a2027ecc50413f6a28209f7324104fba120827b40d1043da060209ef434424f7b9a2127bd8d1093de620849ef534214f799010a7bd0d0813de620409ef324204f781a2087bc0c0413da068201ef034100ee822208774101813ba088201df040604ef82220877c1104037a0a8201bf534414dfa9a2026fd5110137ea48809bf054100be8320805fd8d1412fec88a097f0641007e83a0803fdd11811fe0e8201fd040410fe8182087f4111043fa088a49fd040524fe8102927f4041493fa088c09fd030604fe8203027f41c1413fa0a0a09fd044504fe8202827f40c1413fa080829fd030414fe82220a7f41c1093fa0c0849fd044424fe8202127f4041093fa068821fd020424fe8382027f4181013fa088809fd040404fe8182027f41d0853fa0e0429fd064214fe83010a7f4150853fa0a0429fd040214fe83a1027f41c0813fa0c8409fd060204fe8281027f4110813fa080409fd044214fe82a1027f41d0413fa0e0209fd064104fe8300827f4150413fa028821fd050104fe8220827f4100413fa068209fd030104fe8380807f4180403fa0a0201fd040100fe8180807f4081813fa0e8201fd020504fe8320807f4081013fa020829fd054100ff8382127fc181093fa088201fd020204fe80810a7fdd81093feec0429ff760204ffb9210a7fdc90813fee28a49ff714424ffbb21027fd950853feca8409ff650424ffb2810a7fd940813fec88849ff644214ffb221027fd891093fec48429ff624204ffb9a2827fd851093fea88849ff544214ffaa21027fd8d1053fea68829ff714414ffb0a20a7fc1c1013fe0c0809ff734404ffb1a2027fd4d1013feec0809ff744404ffb922027fd941013fec88809ff624404ffaa22027fd491013feec0209ff724104ffbb20827fdd50413feca8209ff650104ffb220827fd890413fea88209fd034100ff83a0807fc190403fe0a8201ff760100ffb920807fdd90403feea8201ff654100ffb280807fd910403fec48201ff544100 0xc007c1f203e4000401105f300010100430400010010008101024110841a08227d242088227ce427c63f9c8417c7f3fc64fffe7f9084f83e03fc1f213e209c2417c1f07fe0f9c8319ce71fc000000739c842007f000842000007ce0000e401c80200e00000720083084270800039024 231 0x1ff8c9bf7cc97edfb8fd932bf95c2ff1f0efe38e4fc5955f7dba3eaae3fbddb5f71d8fedddb7d50d9f8fe66f125a1df4367bd7fe776bd6ecfa39d434bfa6f9a746f08e7a115c7c4438e58df1c11ce366c1c666e3882877103b6e1857bbb5c8b743276e5eeadcaf75b8df577198dedf548db49d1b5a1eb68d97ec96a9d3c0c3a5462b46915e7ca53cf73b59c161f37a906616e0cb76fd95ea8f1dd29637534c5a9e58969570f98f60e85ec1c7a3837f1afbf355ed422bcaf3175f006e9aae5ced00b9564f71db12e15025c228db728956dde86db0bc5a7a04b4826766eb96cbc4a594955b1a63961c8aac256357a279aa1bbf542932a57945493aca86e055007fea004453dcc7a7987b499ed293307d1e35fa21b5943367682500502ce3a00aff3f7cf27679c4da62e9b38e333346e5c37b4a7a2c932e2322a0ca436ce47b6f78ec0c91c4c5e34b06c62de98c2ee115839e2996744d59f885a1f0f932e1f06043d64787004d0dd4ba1b0cac2b27c8526ab066092073ebc048d2806f24fd30a9f90813f1f117dbffcfb405df5ecd3d8fbd7afb44f3e061e7b92bbe7c875c5b6e7bb15cc0b3b849fa6febcada45d9a318bb4196f620532bd739d7ad302f1eaa5d15aab9b585721ac2de7605b553eb3ac2967118abe751561520ac222956c51a8cb41500c449e8ded39724a6e3014db2c69498512720ba48713489e74911b0521bafa3e83946a7e489479d11541a133ba41bac67cff58f4edd1dfb363be2a076dceced5fd1d96ac3a9066742e9ce70679c2569382e066f9f08ce86c98ae292f0bd65beeacae7d01594e229e8cc518c449b28913209d2575e2492fec8c6db8fc17a1f6dd23e953c76e818e0ccc195e3e2e6b40561208a6e6c13011623e3b8420c6865805088bde0f97cc1de5a833d900539ac09d5c812d2a0153f8 0x941ac108041381c0330a4062170290110341941a94b07c0fc580ae12c2102a0a10f418c838b32001304e8042f60500682e15a2242517314c0085500f0541645889913c0203b07706a0541c1410ce0583500c116234089832020ecd485d0e218c460ab0900803200e11466c1615b07409c37878212208430611402b01192f0a60e42a8013221f80d81714e63c1e0330a00642298302c418220460cc568c00b223a04c5902c1201c4d3157070088489600ac5a4439980bc1c80719211c1a0d40450b00148c0b033e4705988512a094d18560460d81b8553284141a04f134238a700b02407c1587f0c41680313a2d4534a10510f82283c8260760a05894d10441cd28a70920c0101af006184be89f03c0404083d0da1d00501324a288370880b047ca005f05a600968142f024c5512412e11c3a8430d80c84a0182521a0438 11
def extra9 (i : Nat) := getWord (joinBits (joinBits (joinBits (joinBits (joinBits 0x14d087c38c000000000054321f0e2 120 0x21a890788) 348 0x5342f0e13) 1328 0x3c4090d7c8) 1440 (joinBits (joinBits (joinBits 0x3c4090d7c8 272 0x10d47c83c400000000000000000001e20486be4) 352 0x150c843f880000000000543210fe20000000000150c843f88) 504 (joinBits 0xa6843e1c63c4090d7c8788121af100000000001e20486be4 232 0xa6843e1c60000000000788121af9))) 3472 (joinBits (joinBits (joinBits (joinBits 0x10d47c8384000000000001f2345f3 116 0x788121af1) 548 0x14d087c3cc000000000053421f0f3000000000014d087c3cc29a10f879800000000003e468a7e6) 896 (joinBits 0x14d087c394c 544 0x53421f0e33)) 1716 (0x7c8d157cc <<< 1324))) 39 i
def t10 := table 7 1 24 20 0xff324ff320ff524ff520ff424ff420ff210ff200ff214ff204ff604ff600ff504ff500ff414ff410ff404ff400ff314ff310ff304ff300ff104ff100 0x21007008420001f01c0007c8421000 42 0x3f6e5f7db8b3ec6805c5d9037d6216fa25cdbfae5b3244351f5de80cdbcc2ad591b71f22331e007c2bf8fb5702b42cd0e5d77179a051593f76de710ae4dc24b9b5abd2c89f236ef84179f17e330eef81b5d8d23b2de9e61e5ecc0a2997e6c925462047c49083c00cfa6769c121f20a7d23ee1487a06505fdfb 0x5038487980592111609188392918b93181289978511930582040a8b17101b098a068900900081089b870 8
def extra10 (i : Nat) := getWord (joinBits 0xf12345f1 384 (0xf12345f1 <<< 192)) 32 i
def t11 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
def extra11 (i : Nat) := getWord 0x0 0 i
end OrbFitM8
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD8Data
namespace OrbFitM8
abbrev q7 (i : Nat) := FrontQ.testF rot t6 (fun j=>ms.getD j m10) FitRoots8403.small 7 t7 extra7 i=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 5 := by decide +kernel
theorem ready7 : OrbitQ.Mono.all full 7 t7 := by
  have prev : OrbitQ.Mono.all full 6 t6:=by intro i;exact Fin.elim0 i
  apply FitOrbitQ.finish good_ch16x16 valid_full rot prev (fun j=>ms.getD j m10) FitRoots8403.small t7 extra7
  have g : SpanQ.Block q7 0 5 := b7a0
  intro i
  simpa only [q7,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := FrontQ.testF rot t7 (fun j=>ms.getD j m10) FitRoots8403.small 8 t8 extra8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a16 : SpanQ.Block q8 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a32 : SpanQ.Block q8 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b8a48 : SpanQ.Block q8 48 14 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready7 (fun j=>ms.getD j m10) FitRoots8403.small t8 extra8
  have g : SpanQ.Block q8 0 62 := (SpanQ.glue (SpanQ.glue b8a0 b8a16) (SpanQ.glue b8a32 b8a48))
  intro i
  simpa only [q8,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testF rot t8 (fun j=>ms.getD j m10) FitRoots8403.small 9 t9 extra9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a32 : SpanQ.Block q9 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a48 : SpanQ.Block q9 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a64 : SpanQ.Block q9 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a80 : SpanQ.Block q9 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a96 : SpanQ.Block q9 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a112 : SpanQ.Block q9 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a128 : SpanQ.Block q9 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a144 : SpanQ.Block q9 144 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a160 : SpanQ.Block q9 160 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a176 : SpanQ.Block q9 176 4 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready8 (fun j=>ms.getD j m10) FitRoots8403.small t9 extra9
  have g : SpanQ.Block q9 0 180 := (SpanQ.glue (SpanQ.glue (SpanQ.glue b9a0 (SpanQ.glue b9a16 b9a32)) (SpanQ.glue b9a48 (SpanQ.glue b9a64 b9a80))) (SpanQ.glue (SpanQ.glue b9a96 (SpanQ.glue b9a112 b9a128)) (SpanQ.glue b9a144 (SpanQ.glue b9a160 b9a176))))
  intro i
  simpa only [q9,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testF rot t9 (fun j=>ms.getD j m10) FitRoots8403.small 10 t10 extra10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a16 : SpanQ.Block q10 16 8 := by decide +kernel
theorem ready10 : OrbitQ.Mono.all full 10 t10 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready9 (fun j=>ms.getD j m10) FitRoots8403.small t10 extra10
  have g : SpanQ.Block q10 0 24 := (SpanQ.glue b10a0 b10a16)
  intro i
  simpa only [q10,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q11 (i : Nat) := FrontQ.testF rot t10 (fun j=>ms.getD j m10) FitRoots8403.small 11 t11 extra11 i=true
set_option maxRecDepth 8192 in
theorem b11a0 : SpanQ.Block q11 0 1 := by decide +kernel
theorem ready11 : OrbitQ.Mono.all full 11 t11 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready10 (fun j=>ms.getD j m10) FitRoots8403.small t11 extra11
  have g : SpanQ.Block q11 0 1 := b11a0
  intro i
  simpa only [q11,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 11 full := by
  have eq : MonoDeck8403.fromDesc full (t11.desc 0)=full := by decide +kernel
  have h:=ready11 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t11.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbFitM8
end
namespace MonoD8Data
theorem bound : Mono8403.rejects 11 full := OrbFitM8.bound
end MonoD8Data
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD32Data
def full : List Sig := [(0x1d55eaaef7bd8d8dd555555555555eeaaf5577bdec6c6eaaaaaaaaaaaaf7557aabbdef636375555555555557baabd55def7b1b1b,0x112120204002242404080044848081000890901020011212020400224240408004484808100089090102001121202040022424),(0x2e66b3375ad68282e666666666666b733599bad6b414173333333333335b99accdd6b5a0a0b999999999999adccd666eb5ad0505,0x9224a4a4489244949489124892929122491252522449224a4a4489244949489124892929122491252522449224a4a4489244949),(0x37873c3b9ce7030378787878787873bc39e1dce738181bc3c3c3c3c3c39de1cf0ee739c0c0de1e1e1e1e1e1cef0e787739ce0606,0x1244949489124892929122491252522449224a4a4489244949489124892929122491252522449224a4a448924494948912489292),(0x7f83fc3e0f814147f807f807f807c3fc1fe1f07c0a0a3fc03fc03fc03e1fe0ff0f83e05051fe01fe01fe01f0ff07f87c1f02828,0x23861e1f001c70c3c3e0038e18787c0071c30f0f800e3861e1f001c70c3c3e0038e18787c0071c30f0f800e3861e1f001c70c3c3),(0x7ffc003ff0028287fff80007fff803ffe001ff8014143fffc0003fffc01fff000ffc00a0a1fffe0001fffe00fff8007fe005050,0x3c00d8d80e1f801b1b01c3f0036360387e006c6c070fc00d8d80e1f801b1b01c3f0036360387e006c6c070fc00d8d80e1f801b1b),(0x7fffffc000050507fffffff8000003fffffe000028283fffffffc000001ffffff000014141fffffffe000000ffffff80000a0a0,0xe0e00fe0001c1c01fc000383803f8000707007f0000e0e00fe0001c1c01fc000383803f8000707007f0000e0e00fe0001c1c),(0x38000000000060607fffffffffffffc000000000030303fffffffffffffe000000000018181ffffffffffffff00000000000c0c0,0x70707f00000e0e0fe00001c1c1fc000038383f8000070707f00000e0e0fe00001c1c1fc000038383f8000070707f00000e0e0)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(3,17),(4,17),(5,20),(6,23)]) (by decide) (by decide +kernel)
lemma need10 : necessary Proof8403core10.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(9,10),(9,5),(18,3)]) (by decide) (by decide +kernel)
lemma need14 : necessary Proof8403core14.st4:=needFrom (pn:=[(0,2),(0,1),(3,6),(3,3),(7,2)]) (by decide) (by decide +kernel)
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
lemma need38 : necessary Proof8403core38.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,2),(9,3)]) (by decide) (by decide +kernel)
lemma need96 : necessary Proof8403core96.st13:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,1),(9,1),(28,7)]) (by decide) (by decide +kernel)
def raw34 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h34 := SmallHom8403.make 45 0x72716e6d6a69666562615e5d5a59560752514e4d4a49460642403d39383534312f2c2b280524201e1b04160301 19 0x728270524042120021d011a19171614131110
set_option maxRecDepth 8192 in
lemma image34 : full.map h34.fn=raw34 := by decide +kernel
def m34 : Slice full := ⟨raw34,8,h34,image34,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h34 image34) (by decide +kernel))⟩
def raw36 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h36 := SmallHom8403.make 45 0x706f6e6d68676665605f5e5d58575607504f4e4d4847460641403c37363534302f2a292805231f1e1a04150300 19 0x62826052403211f021d001a18171514121110
set_option maxRecDepth 8192 in
lemma image36 : full.map h36.fn=raw36 := by decide +kernel
def m36 : Slice full := ⟨raw36,8,h36,image36,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h36 image36) (by decide +kernel))⟩
def raw38 : List Sig :=
  let w:=Proof8403core38.st0
  [neg (w.getD 0 zero),zero,zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero]
def h38 := SmallHom8403.make 21 0x6e6d66655e5d56074e4d46064035342f28051e0403 11 0x28052421021d1a17141110
set_option maxRecDepth 8192 in
lemma image38 : full.map h38.fn=raw38 := by decide +kernel
def m38 : Slice full := ⟨raw38,7,h38,image38,level_of_rank (known Proof8403core38.e0 need38 (SmallHom8403.validImage h38 image38) (by decide +kernel))⟩
def raw40 : List Sig :=
  let w:=Proof8403core10.st0
  [w.getD 5 zero,w.getD 3 zero,w.getD 4 zero,zero,w.getD 2 zero,neg (w.getD 1 zero),neg (w.getD 0 zero)]
def h40 := SmallHom8403.make 46 0x6c334c1d5c263f136a314a1b5a243d016830481a58233c00662f4604566b324b1c5b253e02694959674757650607 18 0x20511041920271303181f261221171d2410
set_option maxRecDepth 8192 in
lemma image40 : full.map h40.fn=raw40 := by decide +kernel
def m40 : Slice full := ⟨raw40,8,h40,image40,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h40 image40) (by decide +kernel))⟩
def raw48 : List Sig :=
  let w:=Proof8403core10.st0
  [w.getD 5 zero,w.getD 3 zero,w.getD 4 zero,w.getD 2 zero,zero,neg (w.getD 0 zero),neg (w.getD 1 zero)]
def h48 := SmallHom8403.make 46 0x64442e185c3f261362422c165a3d240160412a15583c23005e4028035663432d175b3e2502612b595f29575d0507 18 0x5021107162720130615261f122814241d10
set_option maxRecDepth 8192 in
lemma image48 : full.map h48.fn=raw48 := by decide +kernel
def m48 : Slice full := ⟨raw48,8,h48,image48,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h48 image48) (by decide +kernel))⟩
def raw96 : List Sig :=
  let w:=Proof8403core96.st13
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,zero,w.getD 5 zero]
def h96 := SmallHom8403.make 44 0x54535251504f4e4d4c4b4a494847460644434241403f3e3d3c2221201f1e1d1c1b1a04181716150313020100 20 0x706282726052401001a19181716151413121110
set_option maxRecDepth 8192 in
lemma image96 : full.map h96.fn=raw96 := by decide +kernel
def m96 : Slice full := ⟨raw96,8,h96,image96,level_of_rank (known Proof8403core96.e13 need96 (SmallHom8403.validImage h96 image96) (by decide +kernel))⟩
def raw104 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 4 zero,w.getD 2 zero,w.getD 3 zero,zero,neg (w.getD 1 zero),zero,neg (w.getD 0 zero)]
def h104 := SmallHom8403.make 21 0x4c1d3f134a1b3d01481a3c0046044b1c3e02494706 11 0x511192713182612172410
set_option maxRecDepth 8192 in
lemma image104 : full.map h104.fn=raw104 := by decide +kernel
def m104 : Slice full := ⟨raw104,7,h104,image104,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h104 image104) (by decide +kernel))⟩
def raw160 : List Sig :=
  let w:=Proof8403core96.st13
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,w.getD 5 zero,zero]
def h160 := SmallHom8403.make 44 0x3b3a3938373635342e2d2c2b2a292805333231302f262524232221201f1e18171615031d1c1b1a0413020100 20 0x40321201f021d01001a16151419181713121110
set_option maxRecDepth 8192 in
lemma image160 : full.map h160.fn=raw160 := by decide +kernel
def m160 : Slice full := ⟨raw160,8,h160,image160,level_of_rank (known Proof8403core96.e13 need96 (SmallHom8403.validImage h160 image160) (by decide +kernel))⟩
def raw176 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 4 zero,w.getD 2 zero,w.getD 3 zero,neg (w.getD 1 zero),zero,neg (w.getD 0 zero),zero]
def h176 := SmallHom8403.make 21 0x2e1826132c1624012a15230028032d1725022b2905 11 0x211162013151f12141d10
set_option maxRecDepth 8192 in
lemma image176 : full.map h176.fn=raw176 := by decide +kernel
def m176 : Slice full := ⟨raw176,7,h176,image176,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h176 image176) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m34,m36,m38,m40,m48,m96,m104,m160,m176]
end MonoD32Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD32Data
namespace OrbM32
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x74737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857560754535251504f4e4d4c4b4a494847460644434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292805262524232221201f1e1d1c1b1a0418171615031302010007060504030201000706050403020100 8 (i.val % 117))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x7062827260524040321201f021d01001a1918171615141312111007060504030201000706050403020100 8 (i.val % 43))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x74737271706f6e6d64636261605f5e5d6c6b6a69686766655c5b5a59585756073b3a3938373635342e2d2c2b2a292805333231302f2625242354535251504f4e4d44434241404c4b4a49484746063f3e3d3c2221201f1e18171615031d1c1b1a041302010007050603040201000705060304020100 8 (i.val % 117))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x40321201f021d0706282726052401001a1615141918171312111004030207060501000403020706050100 8 (i.val % 43))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x7473706f72716e6d6c6b68676a6966656463605f62615e5d5c5b58575a5956075453504f52514e4d4c4b48474a49460644434142403f3e3c3d3b3a373639383534333230312f2e2d2a292c2b28052625232422211f201e1d1c1a1b0418171516031302000107060504030200010706050403020001 8 (i.val % 117))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x60728262705240304211f20021d00011a1819171516141213111006070503040200010607050304020001 8 (i.val % 43))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x7473706f72716e6d6463605f62615e5d6c6b68676a6966655c5b58575a5956073b3a3736393835342e2d2a292c2b2805333230312f262523245453504f52514e4d44434142404c4b48474a4946063f3e3c3d22211f201e18171516031d1c1a1b041302000107050603040200010705060304020001 8 (i.val % 117))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x304211f20021d0607282627052400011a1516141819171213111003040206070500010304020607050001 8 (i.val % 43))
def H3 := pairHom p3 n3
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 4 zero,full.getD 3 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 4 zero,full.getD 3 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H3,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1,rot2,rot3].getD i rot0
def t6 := table 7 4 0 1 0x0 0x0 0 0x0 0x0 1
def t7 := table 7 3 4 46 0xf2c501090413d9044010314af41c1d10c5379064010314 0x180e0 4 0xdf572f4c439d927788b5bfb 0x6110 5
def t8 := table 7 2 12 33 0xfb99018a7dd090413da060209dd040504efba218a77d900c53be868629df4243047e8382a27f4150c53fa068629fd010314 0x100670186048060 17 0x6fe799c8a3938a4a96f72eadc3cd7aa86db37316e2b04729109a512b989b83493082c990231242a0642eb605491d0458bd 0x288088051704ac0830ed8482141ca0 7
def t9 := table 7 1 20 20 0xff654ff650ff540ff534ff514ff510ff504ff500ff434ff430ff310ff300ff210ff544ff530ff304ff314ff214ff104ff100 0x20c70180601484100c000c01 42 0x3c84057767cee8f4d1cfe6478dbf271545dd7116ba84b6b4adc45f3866bcf2bd794322eec95d856e5afbe995ab086b2c3c55a1b7a9f96b3628ea6b31bc7c78185d39d04e8f9fc6933f238775fb16b5498546b432824474eb55e878ee4daa6e983fe92ac694461bc05e53b8b51d815b36426c824415e2809024 0x181029607a4920211b715078614108681a98697948190272583181704a30897b73884b283880900a40 8
def t10 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbM32
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD32Data
namespace OrbM32
abbrev q7 (i : Nat) := FrontQ.testM rot t6 m34 ms 7 t7 i=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 4 := by decide +kernel
theorem ready7 : OrbitQ.Mono.all full 7 t7 := by
  have prev : OrbitQ.Mono.all full 6 t6:=by intro i;exact Fin.elim0 i
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot prev m34 ms t7
  have g : SpanQ.Block q7 0 4 := b7a0
  intro i
  simpa only [q7,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := FrontQ.testM rot t7 m34 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 12 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready7 m34 ms t8
  have g : SpanQ.Block q8 0 12 := b8a0
  intro i
  simpa only [q8,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testM rot t8 m34 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 4 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready8 m34 ms t9
  have g : SpanQ.Block q9 0 20 := (SpanQ.glue b9a0 b9a16)
  intro i
  simpa only [q9,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testM rot t9 m34 ms 10 t10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 1 := by decide +kernel
theorem ready10 : OrbitQ.Mono.all full 10 t10 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready9 m34 ms t10
  have g : SpanQ.Block q10 0 1 := b10a0
  intro i
  simpa only [q10,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 10 full := by
  have eq : MonoDeck8403.fromDesc full (t10.desc 0)=full := by decide +kernel
  have h:=ready10 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t10.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbM32
end
namespace MonoD32Data
theorem bound : Mono8403.rejects 10 full := OrbM32.bound
end MonoD32Data
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD64Data
def full : List Sig := [(0x2bddb6db6bdef636375555555555557bb6db6d7bdec6c6eaaaaaaaaaaaaf76db6daf7bd8d8dd555555555555eedb6db5ef7b1b1b,0x1140804002a28a040200151450201000a8a28100800545140804002a28a040200151450201000a8a28100800545140804002a28a),(0xd6edb6dbd6b5a4a4b999999999999addb6db7ad6b494973333333333335bb6db6f5ad69292e666666666666b76db6deb5ad2525,0xa29000924145148004920a28a40024905145200124828a29000924145148004920a28a40024905145200124828a290009241451),(0xe771c71ce739c0c0de1e1e1e1e1e1cee38e39ce738181bc3c3c3c3c3c39dc71c739ce7030378787878787873b8e38e739ce0606,0x24922a924849249154924249248aa492124924552490924922a924849249154924249248aa492124924552490924922a92484924),(0xf87e07e0f83e01011fe01fe01fe01f0fc0fc1f07c02023fc03fc03fc03e1f81f83e0f804047f807f807f807c3f03f07c1f00808,0x2ebc331c705d75e198e382ebaf0cc71c175d786638e0baebc331c705d75e198e382ebaf0cc71c175d786638e0baebc331c705d75),(0x3007ff800ffc00a0a1fffe0001fffe00fff001ff8014143fffc0003fffc01ffe003ff0028287fff80007fff803ffc007fe005050,0x28a03c1f80514501e0fc028a280f07e0145140783f00a28a03c1f80514501e0fc028a280f07e0145140783f00a28a03c1f805145),(0x7fffff000014141fffffffe000000fffffe000028283fffffffc000001fffffc000050507fffffff8000003fffff80000a0a0,0x30c03fe000618601ff00030c300ff8001861807fc000c30c03fe000618601ff00030c300ff8001861807fc000c30c03fe0006186),(0x3ff800000000018181ffffffffffffff000000000030303fffffffffffffe000000000060607fffffffffffffc0000000000c0c0,0x71fc000008e38fe00000471c7f00000238e3f8000011c71fc000008e38fe00000471c7f00000238e3f8000011c71fc000008e38)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(3,17),(4,17),(5,18),(6,23)]) (by decide) (by decide +kernel)
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
def raw72 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 4 zero,w.getD 5 zero,w.getD 3 zero,zero,neg (w.getD 1 zero),w.getD 2 zero,neg (w.getD 0 zero)]
def h72 := SmallHom8403.make 48 0x6a335a274a1d3d1366305624461a3a0069325926491c3c02652f55054568315825481b3b01642e544404675747630706 16 0x182812010311231f192913221d172610
set_option maxRecDepth 8192 in
lemma image72 : full.map h72.fn=raw72 := by decide +kernel
def m72 : Slice full := ⟨raw72,9,h72,image72,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h72 image72) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m72]
end MonoD64Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD64Data
namespace OrbM64
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x7271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554075251504f4e4d4c4b4a494847464544064241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524052221201f1e1d1c1b1a0418171615031302010007060504030201000706050403020100 8 (i.val % 115))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x5042a292803260224232221201f011d1c001a1918171615141312111003020100050403020100050403020100 8 (i.val % 45))
def H0 := pairHom p0 n0
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0].getD i rot0
def t7 := table 7 2 0 1 0x0 0x0 0 0x0 0x0 1
def t8 := table 7 1 13 20 0xef434ef324ef314ef300ff524ff504ff424ff414ff214ff204ff104ff100ff314 0x1084210842108421 13 0x7d0bcef3f539c6791b7e83bee6554b93471697ec9e66013768ac61e3a277f6982f7c281adc0 0x60816042890e0c206002810 7
def t9 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbM64
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD64Data
namespace OrbM64
abbrev q8 (i : Nat) := FrontQ.testM rot t7 m72 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 13 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  have prev : OrbitQ.Mono.all full 7 t7:=by intro i;exact Fin.elim0 i
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot prev m72 ms t8
  have g : SpanQ.Block q8 0 13 := b8a0
  intro i
  simpa only [q8,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testM rot t8 m72 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 1 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply OrbitQ.Mono.finish good_ch16x16 valid_full rot ready8 m72 ms t9
  have g : SpanQ.Block q9 0 1 := b9a0
  intro i
  simpa only [q9,FrontQ.eqM,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 9 full := by
  have eq : MonoDeck8403.fromDesc full (t9.desc 0)=full := by decide +kernel
  have h:=ready9 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t9.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbM64
end
namespace MonoD64Data
theorem bound : Mono8403.rejects 9 full := OrbM64.bound
end MonoD64Data
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403 Mono8403 Fit8403
namespace FitRoots8403
def base1 : Basis := ⟨MonoD1Data.full,9,MonoD1Data.valid_full,known0 MonoD1Data.bound MonoD1Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def base2 : Basis := ⟨MonoD2Data.full,10,MonoD2Data.valid_full,known0 MonoD2Data.bound MonoD2Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def base4 : Basis := ⟨MonoD4Data.full,12,MonoD4Data.valid_full,known0 MonoD4Data.bound MonoD4Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def base8 : Basis := ⟨MonoD8Data.full,12,MonoD8Data.valid_full,known0 MonoD8Data.bound MonoD8Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def base32 : Basis := ⟨MonoD32Data.full,11,MonoD32Data.valid_full,known0 MonoD32Data.bound MonoD32Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def base64 : Basis := ⟨MonoD64Data.full,10,MonoD64Data.valid_full,known0 MonoD64Data.bound MonoD64Data.fullNeed (fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))⟩
def all (i : Nat) := #[base5,base6,base9,base10,base14,base24,base34,base38,base96,base1,base2,base4,base8,base32,base64].getD i base5
end FitRoots8403
end
section
open Basis1868 Free1868 Cuts1868
open Exact8403 Leaf8403 QuickQ
open Mono8403 MonoWord8403
namespace MonoD0Data
def full : List Sig := [(0x2aaaaaaaaaaaaabdd5555555555eaaedb6db5ef7bd81baaaaaaaaaaaaaaaaaaaaaaaaaaaabdd5555555555eaaedb6db5ef7bd81b,0x40804002944a040804002944a040804002944a040804002944a040804002944a040804002944a040804002944a040804002944a),(0xcccccccccccccd6e6666666666b3376db6deb5ad2825ccccccccccccccccccccccccccccd6e6666666666b3376db6deb5ad2825,0x8900092422914890009242291489000924229148900092422914890009242291489000924229148900092422914890009242291),(0x30f0f0f0f0f0f0e7787878787873c3b8e38e739ce3006f0f0f0f0f0f0f0f0f0f0f0f0f0f0e7787878787873c3b8e38e739ce3006,0x1122a924849249122a924849249122a924849249122a924849249122a924849249122a924849249122a924849249122a92484924),(0xff00ff00ff00f87f807f807f83fc3f03f07c1f04048ff00ff00ff00ff00ff00ff00ff00f87f807f807f83fc3f03f07c1f04048,0x200331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85),(0xffff0000ffff007fff80007ffc003ffc007fe008110ffff0000ffff0000ffff0000ffff007fff80007ffc003ffc007fe008110,0x1c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a35),(0xffffffff0000007fffffff8000003fffff8000002a0ffffffff00000000ffffffff0000007fffffff8000003fffff8000002a0,0x3fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c06),(0x3f000000000000007fffffffffffffc000000000004c0ffffffffffffffff000000000000007fffffffffffffc000000000004c0,0x1fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc000007038),(0x3fffffffffffffff80000000000000000000000000700ffffffffffffffffffffffffffffff80000000000000000000000000700,0x3e000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma fullNeed : necessary full:=needFrom (pn:=[(0,18),(0,17),(1,17),(3,17),(4,17),(5,18),(6,20),(8,23)]) (by decide) (by decide +kernel)
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
lemma need9 : necessary Proof8403core9.st9:=needFrom (pn:=[(0,2),(0,1),(17,16),(2,1),(8,6),(17,3)]) (by decide) (by decide +kernel)
lemma need10 : necessary Proof8403core10.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(9,10),(9,5),(18,3)]) (by decide) (by decide +kernel)
lemma need14 : necessary Proof8403core14.st4:=needFrom (pn:=[(0,2),(0,1),(3,6),(3,3),(7,2)]) (by decide) (by decide +kernel)
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
lemma need96 : necessary Proof8403core96.st13:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,1),(9,1),(28,7)]) (by decide) (by decide +kernel)
def raw1 : List Sig :=
  let w:=MonoD1Data.full
  [zero,w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero,w.getD 6 zero]
def h1 := SmallHom8403.make 112 0xeae8e6e4e2e0dedcdad8d6d4d2d0cecccac8c6c4c2c0bebcbab8b6b4b2b0ae0aaaa8a6a4a2a09e9c9a98969492908e098a88868482807e087a75716f6d6b69676563615f5d5b59575507514f4d4b49444240063c3835322f2c292605211c170205020a0908070605020a090807060502 48 0x80731302f2d05042a2928260224232221201f1d1c001a19181716151413121005040200080705040200080705040200
set_option maxRecDepth 8192 in
lemma image1 : full.map h1.fn=raw1 := by decide +kernel
def m1 : Slice full := ⟨raw1,9,h1,image1,known0 MonoD1Data.bound MonoD1Data.fullNeed (by decide +kernel)⟩
def raw2 : List Sig :=
  let w:=MonoD2Data.full
  [w.getD 0 zero,zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero,w.getD 6 zero]
def h2 := SmallHom8403.make 116 0xe9e8e5e4e1e0dddcd9d8d5d4d1d0cdccc9c8c5c4c1c0bdbcb9b8b5b4b1b0ad0aa9a8a5a4a1a09d9c9998959491908d098988858481807d08797774706f6c6b68676463605f5c5b58575407504f4c4b484643423f063b3734312e2b2825201e1b041603010a090807060403010a09080706040301 44 0x83130062d052a2903260224232221201f011d1c1a1917161413111005030201080605030201080605030201
set_option maxRecDepth 8192 in
lemma image2 : full.map h2.fn=raw2 := by decide +kernel
def m2 : Slice full := ⟨raw2,10,h2,image2,known0 MonoD2Data.bound MonoD2Data.fullNeed (by decide +kernel)⟩
def raw4 : List Sig :=
  let w:=MonoD4Data.full
  [w.getD 0 zero,w.getD 1 zero,zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero,w.getD 6 zero]
def h4 := SmallHom8403.make 120 0xe7e6e5e4dfdedddcd7d6d5d4cfcecdccc7c6c5c4bfbebdbcb7b6b5b4afaead0aa7a6a5a49f9e9d9c979695948f8e8d09878685847f7e7d087877736e6d6c6b666564635e5d5c5b565554074e4d4c4b474641403f063a363534302f2e2a292824051f1e1a04150300080706050403000a0908070605040300 40 0x7312f062d042a280326242220011d001a1817151412111001000706040324010007060403240100
set_option maxRecDepth 8192 in
lemma image4 : full.map h4.fn=raw4 := by decide +kernel
def m4 : Slice full := ⟨raw4,12,h4,image4,known0 MonoD4Data.bound MonoD4Data.fullNeed (by decide +kernel)⟩
def raw6 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 0 zero),zero,zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h6 := SmallHom8403.make 48 0xe5e4dddcd5d4cdccc5c4bdbcb5b4ad0aa5a49d9c95948d0985847d08776c6b64635c5b54074c4b463f06342e281e0403 16 0x31062d2a0326242220011d1a17141110
set_option maxRecDepth 8192 in
lemma image6 : full.map h6.fn=raw6 := by decide +kernel
def m6 : Slice full := ⟨raw6,9,h6,image6,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h6 image6) (by decide +kernel))⟩
def raw8 : List Sig :=
  let w:=MonoD8Data.full
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero,w.getD 6 zero]
def h8 := SmallHom8403.make 121 0xe3e2e1e0dfdedddcd3d2d1d0cfcecdccc3c2c1c0bfbebdbcb3b2b1b0afaead0aa3a2a1a09f9e9d9c939291908f8e8d09838281807f7e7d08767574736a696867666564635a595857565554074a494847463d3c3b3a333231302f2e27262524051d1c1b1a0413020100080705040201000a0908070504020100 39 0x302f062d05042a2928032623221f011d19181713121110302f060504032301302f060504032301
set_option maxRecDepth 8192 in
lemma image8 : full.map h8.fn=raw8 := by decide +kernel
def m8 : Slice full := ⟨raw8,12,h8,image8,known0 MonoD8Data.bound MonoD8Data.fullNeed (by decide +kernel)⟩
def raw9 : List Sig :=
  let w:=Proof8403core9.st9
  [zero,neg (w.getD 0 zero),neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h9 := SmallHom8403.make 45 0xe2e0dedcd2d0ceccc2c0bebcb2b0ae0aa2a09e9c92908e0982807e08756967656359575507493c322f26051c02 19 0x302f2d05042a29282623221f1d191817131210
set_option maxRecDepth 8192 in
lemma image9 : full.map h9.fn=raw9 := by decide +kernel
def m9 : Slice full := ⟨raw9,8,h9,image9,level_of_rank (known Proof8403core9.e9 need9 (SmallHom8403.validImage h9 image9) (by decide +kernel))⟩
def raw10 : List Sig :=
  let w:=Proof8403core10.st0
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h10 := SmallHom8403.make 46 0xe1e0dddcd1d0cdccc1c0bdbcb1b0ad0aa1a09d9c91908d0981807d0874686764635857540748463b312e251b0401 18 0x30062d052a29032623221f011d1917131110
set_option maxRecDepth 8192 in
lemma image10 : full.map h10.fn=raw10 := by decide +kernel
def m10 : Slice full := ⟨raw10,8,h10,image10,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h10 image10) (by decide +kernel))⟩
def raw16 : List Sig :=
  let w:=MonoD8Data.full
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero,w.getD 6 zero,w.getD 5 zero]
def h16 := SmallHom8403.make 121 0xdbdad9d8d7d6d5d4d3d2d1d0cfcecdccbbbab9b8b7b6b5b4b3b2b1b0afaead0a6261605f5e5d5c5b5a595857565554074544434241403f063d3c3b3a9b9a999897969594939291908f8e8d097b7a797877767574732d2c2b2a29282726252405181716150313020100060905030201000a0706090503020100 39 0x29280326080731302f062d21201f011d1615141312111029280308070621012928030807062101
set_option maxRecDepth 8192 in
lemma image16 : full.map h16.fn=raw16 := by decide +kernel
def m16 : Slice full := ⟨raw16,12,h16,image16,known0 MonoD8Data.bound MonoD8Data.fullNeed (by decide +kernel)⟩
def raw17 : List Sig :=
  let w:=Proof8403core9.st9
  [zero,neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 5 zero,w.getD 4 zero]
def h17 := SmallHom8403.make 45 0xdad8d6d4d2d0ceccbab8b6b4b2b0ae0a615f5d5b59575507444240063c9a98969492908e097a752c2926051702 19 0x292826080731302f2d21201f1d161514131210
set_option maxRecDepth 8192 in
lemma image17 : full.map h17.fn=raw17 := by decide +kernel
def m17 : Slice full := ⟨raw17,8,h17,image17,level_of_rank (known Proof8403core9.e9 need9 (SmallHom8403.validImage h17 image17) (by decide +kernel))⟩
def raw18 : List Sig :=
  let w:=Proof8403core10.st0
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 5 zero,w.getD 4 zero]
def h18 := SmallHom8403.make 46 0xd9d8d5d4d1d0cdccb9b8b5b4b1b0ad0a605f5c5b5857540743423f063b9998959491908d097977742b2825160301 18 0x290326083130062d21201f011d1614131110
set_option maxRecDepth 8192 in
lemma image18 : full.map h18.fn=raw18 := by decide +kernel
def m18 : Slice full := ⟨raw18,8,h18,image18,level_of_rank (known Proof8403core10.e0 need10 (SmallHom8403.validImage h18 image18) (by decide +kernel))⟩
def raw32 : List Sig :=
  let w:=MonoD32Data.full
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,zero,w.getD 5 zero,w.getD 6 zero]
def h32 := SmallHom8403.make 117 0xcbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaead0a8b8a898887868584838281807f7e7d087b7a797877767574735251504f4e4d4c4b4a494847464544434241403f063d3c3b3a2221201f1e1d1c1b1a041817161503130201000a080604030201000a08060403020100 43 0x80731302f062d05042a292803261c001a191817161514131211100807060504031c000807060504031c00
set_option maxRecDepth 8192 in
lemma image32 : full.map h32.fn=raw32 := by decide +kernel
def m32 : Slice full := ⟨raw32,11,h32,image32,known0 MonoD32Data.bound MonoD32Data.fullNeed (by decide +kernel)⟩
def raw34 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero,w.getD 5 zero]
def h34 := SmallHom8403.make 45 0xc9c8c5c4c1c0bdbcb9b8b5b4b1b0ad0a8988858481807d08797774504f4c4b484643423f063b201e1b04160301 19 0x83130062d052a2903261c1a19171614131110
set_option maxRecDepth 8192 in
lemma image34 : full.map h34.fn=raw34 := by decide +kernel
def m34 : Slice full := ⟨raw34,8,h34,image34,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h34 image34) (by decide +kernel))⟩
def raw64 : List Sig :=
  let w:=MonoD64Data.full
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero,zero,w.getD 6 zero]
def h64 := SmallHom8403.make 115 0xabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d098b8a898887868584838281807f7e7d087b7a79787776757473393837363534333231302f2e2d2c2b2a292827262524052221201f1e1d1c1b1a0418171615031302010009080504030201000908050403020100 45 0x80731302f062d0224232221201f011d1c001a1918171615141312111006020100080706020100080706020100
set_option maxRecDepth 8192 in
lemma image64 : full.map h64.fn=raw64 := by decide +kernel
def m64 : Slice full := ⟨raw64,10,h64,image64,known0 MonoD64Data.bound MonoD64Data.fullNeed (by decide +kernel)⟩
def raw68 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),w.getD 2 zero,zero,neg (w.getD 1 zero),w.getD 3 zero,w.getD 4 zero,zero,w.getD 5 zero]
def h68 := SmallHom8403.make 45 0xa7a69f9ea5a49d9c97968f8e95948d0987867f7e85847d087873773635302f342e2a292405281f1a1e04150003 19 0x72f31062d242220011d00181a171512141110
set_option maxRecDepth 8192 in
lemma image68 : full.map h68.fn=raw68 := by decide +kernel
def m68 : Slice full := ⟨raw68,8,h68,image68,level_of_rank (known Proof8403core34.e3 need34 (SmallHom8403.validImage h68 image68) (by decide +kernel))⟩
def raw72 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 4 zero,w.getD 5 zero,w.getD 3 zero,zero,neg (w.getD 1 zero),w.getD 2 zero,zero,neg (w.getD 0 zero)]
def h72 := SmallHom8403.make 48 0xa3339327831d76139f308f247f1a7300a2329226821c75029e2f8e057ea1319125811b74019d2e8d7d04a090809c0908 16 0x182f12010611231f193013221d172d10
set_option maxRecDepth 8192 in
lemma image72 : full.map h72.fn=raw72 := by decide +kernel
def m72 : Slice full := ⟨raw72,9,h72,image72,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h72 image72) (by decide +kernel))⟩
def raw96 : List Sig :=
  let w:=Proof8403core96.st13
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,zero,zero,w.getD 5 zero]
def h96 := SmallHom8403.make 44 0x8b8a898887868584838281807f7e7d087b7a797877767574732221201f1e1d1c1b1a04181716150313020100 20 0x80731302f062d1c001a19181716151413121110
set_option maxRecDepth 8192 in
lemma image96 : full.map h96.fn=raw96 := by decide +kernel
def m96 : Slice full := ⟨raw96,8,h96,image96,level_of_rank (known Proof8403core96.e13 need96 (SmallHom8403.validImage h96 image96) (by decide +kernel))⟩
def raw104 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 4 zero,w.getD 2 zero,w.getD 3 zero,zero,neg (w.getD 1 zero),zero,zero,neg (w.getD 0 zero)]
def h104 := SmallHom8403.make 21 0x831d7613811b74017f1a73007d04821c7502807e08 11 0x611193013182f12172d10
set_option maxRecDepth 8192 in
lemma image104 : full.map h104.fn=raw104 := by decide +kernel
def m104 : Slice full := ⟨raw104,7,h104,image104,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h104 image104) (by decide +kernel))⟩
def raw128 : List Sig :=
  let w:=MonoD64Data.full
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,w.getD 5 zero,w.getD 6 zero,zero]
def h128 := SmallHom8403.make 115 0x7271706f6e6d6c6b6261605f5e5d5c5b6a696867666564635a595857565554075251504f4e4d4c4b4544434241403f064a494847463d3c3b3a3938373635342d2c2b2a2928333231302f2e27262524052221201f1e18171615031d1c1b1a041302010007060503040201000706050304020100 45 0x5042a292803260224212023221f011d1c001a1615141918171312111003020100050403020100050403020100
set_option maxRecDepth 8192 in
lemma image128 : full.map h128.fn=raw128 := by decide +kernel
def m128 : Slice full := ⟨raw128,10,h128,image128,known0 MonoD64Data.bound MonoD64Data.fullNeed (by decide +kernel)⟩
def raw144 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 4 zero,w.getD 5 zero,w.getD 3 zero,neg (w.getD 1 zero),zero,w.getD 2 zero,neg (w.getD 0 zero),zero]
def h144 := SmallHom8403.make 48 0x622d5a2745183d135e2a562441153a00612c592644173c025d29550540602b582543163b015c28543f035f57425b0706 16 0x152812010311211f162913201d142610
set_option maxRecDepth 8192 in
lemma image144 : full.map h144.fn=raw144 := by decide +kernel
def m144 : Slice full := ⟨raw144,9,h144,image144,level_of_rank (known Proof8403core6.e21 need6 (SmallHom8403.validImage h144 image144) (by decide +kernel))⟩
def raw160 : List Sig :=
  let w:=Proof8403core96.st13
  [neg (w.getD 0 zero),neg (w.getD 1 zero),w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,zero,w.getD 5 zero,zero]
def h160 := SmallHom8403.make 44 0x5251504f4e4d4c4b4544434241403f064a494847463d3c3b3a2221201f1e18171615031d1c1b1a0413020100 20 0x5042a292803261c001a16151419181713121110
set_option maxRecDepth 8192 in
lemma image160 : full.map h160.fn=raw160 := by decide +kernel
def m160 : Slice full := ⟨raw160,8,h160,image160,level_of_rank (known Proof8403core96.e13 need96 (SmallHom8403.validImage h160 image160) (by decide +kernel))⟩
def raw176 : List Sig :=
  let w:=Proof8403core14.st4
  [w.getD 4 zero,w.getD 2 zero,w.getD 3 zero,neg (w.getD 1 zero),zero,zero,neg (w.getD 0 zero),zero]
def h176 := SmallHom8403.make 21 0x45183d1343163b0141153a003f0344173c02424006 11 0x311162913152812142610
set_option maxRecDepth 8192 in
lemma image176 : full.map h176.fn=raw176 := by decide +kernel
def m176 : Slice full := ⟨raw176,7,h176,image176,level_of_rank (known Proof8403core14.e4 need14 (SmallHom8403.validImage h176 image176) (by decide +kernel))⟩
def ms : Array (Slice full) := #[m1,m2,m4,m6,m8,m9,m10,m16,m17,m18,m32,m34,m64,m68,m72,m96,m104,m128,m144,m160,m176]
end MonoD0Data
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ MonoD0Data
namespace OrbFitM0
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaead0aabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d098b8a898887868584838281807f7e7d087b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554075251504f4e4d4c4b4a494847464544434241403f063d3c3b3a393837363534333231302f2e2d2c2b2a292827262524052221201f1e1d1c1b1a0418171615031302010004030201000a09080706050403020100 8 (i.val % 236))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x80731302f062d05042a292803260224232221201f011d1c001a1918171615141312111006050403020100080706050403020100 8 (i.val % 52))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xebeae9e8e7e6e5e4dbdad9d8d7d6d5d4e3e2e1e0dfdedddcd3d2d1d0cfcecdcccbcac9c8c7c6c5c4bbbab9b8b7b6b5b4c3c2c1c0bfbebdbcb3b2b1b0afaead0a7271706f6e6d6c6b6261605f5e5d5c5b6a696867666564635a595857565554075251504f4e4d4c4b4544434241403f064a494847463d3c3b3aabaaa9a8a7a6a5a49b9a999897969594a3a2a1a09f9e9d9c939291908f8e8d098b8a8988878685847b7a797877838281807f7e7d08767574733938373635342d2c2b2a2928333231302f2e27262524052221201f1e18171615031d1c1b1a041302010003040201000a07060908050304020100 8 (i.val % 236))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x5042a29280326080731302f062d0224212023221f011d1c001a1615141918171312111003080706020100050403080706020100 8 (i.val % 52))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero,full.getD 7 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 4 zero,full.getD 3 zero,full.getD 5 zero,full.getD 7 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := #[rot0,rot1].getD i rot0
def t7 := table 8 6 0 1 0x0 0x0 0 0x0 0x0 1
def extra7 (i : Nat) := getWord 0x0 1 i
def t8 := table 8 5 12 73 0xf3283a5480220102820dbcd82a525d1d904136d20c80800480c8ec1b65094a90044020504db484a05043a01a0807394212a401500814135ca0e9520020c48a09ae9074040024064760d7284a54802a0102826ba42502821d0110403dc22095200a8040a09be10101a4084064100 0xc00ffffffffff 16 0xede7c7b8c4db71747e68befba8aad520aa69241a5013947cf1fcf3877dd8d3736b58e640cd0c4bc1d284e49463a8 0xb101c28626508940608590022848 7
def extra8 (i : Nat) := getWord 0xf042453110f13454210f23451410f23451410f23454110f23454110f1234541f04234511 36 i
def t9 := table 8 4 156 60 0xf8d054030614104f4d064030614104dcfa448246245043cfa44924724604fa5050034014760fa3250024870104f6b534054870104f6d064980614104deb034074870104deb534074870104ded084980614104fe1020024870504fe1020024870104f95050024024760f93250034870104f97250934724104f97250834624104f5b044054870104f5b544054870104f5b7440548701049df8548247245149df954834624504dd7120834624504dd7254834624504ddb864034870504ddd010834624504ddd0a4834624504ddb544074870104ddb6440748701043dfa54934724604fd1020034870514fd1020034870104fd9044090724504fd9044090764104f33250054870104f3b250054870104f35060824034100db3250074870104db7250974764104dbb864044870504dbb250074870104db7a84874034100db7864874034100bb7250984764104bb7250874724104bb7a94874034100bb7974984034100bb7944874034100fb1020044870104fb3250074870104fb3a94044020504fb3a90044020504fb3150934074104fb50a0874034100fb5074874034100fb50a0824034100e75070924044100e73260064020604d75060824064100d77184874044100d77a84874044100d77874974044100d7b854054870514d7b854054870504d7b084054870504d7b874054870504d7d064980624504b75060024074100b77a94874044100b77974984044100b779448740441007771a4984044100777a94974044100777a44974044100f71100824044100f731a4084044100f73174094044100f73130094044100f731a4074044100f73194074044100f73174074044100f73130074044100f75090094044100f75090074044100f75104974044100f75064980010514f75090974044100f75090924044100f750a0874044100f75074874044100f750a0824044100f75060824064100f73154094044100f73154074044100f73a94054020504f73a90054020504f73254054870504f75064980020504f73144094044100f73144074044100f79064090724104f79064090764104af5070924074100ef32a0064020604ef90740907641041f72749848646541f7a841947646141ff6549848646541ff5409848646541ff5309848646541ff5449848646541ff5349848646541ff6449848646541ffa949747641049f71949840641009f7a948740641009f79749840641009f79440840641009f7944874064100df1020074870514df1020074870504df1100874064100df31a4084064100df50a0084064100df5104874064100df5074084064100df3164084064100df3154034064760df3154024064760df3164024064760df3144024064760df5054024064760df5040024064760df5030034064760df5084980010514df3024074870504df50a0874064100df5074874064100df50a0824064100df3a94010624504df3a90010624504df3944010624504df3254074870504df5084980020504df9010984624504df9064074870504df9084090764104df90840907641003f7a44974074100bf1010834074504bf1094090074100bf1100874074100bf5100924074100bf3a44010724604ff1014980020504ff1100924074100 0x18c6000c0b90c631bc6818d832afe328d72f806328c65180a318102f8c001fd1f414a0020637a00502040008bf4141f417ffffffffa3e518fff180a50011f023e518c6328000408529081f120a31940307ff2fa3fff8860f941f17c4bf881f 178 0x3ffd487e2832fb4985f687bbebd9c7d38e0f9a543ee9ce7d8138facef4f18277e14d87be579f737e3ed4c05da5133b32a4f5ff07eb0f37d59617a8cb07430f4e809abceb01b96baf725d40de48cdba85b374592ecdafdd8d9cfb087035a6026ac1acd29bfda481833b0dfe6ccdaccc091935a872568964671fc755d78decab1b90462ff5fc41e2f804ce6f6e605ec5c8bd697d7928c2f1e0fdd3570b65055688f36b93bd568856aba94b5716b2a6138d47d18a85b45507d7a9f74d52c1b1a3ded941531e7d4c9cf24d09bc9c735dd666613a4c848f97d73b264c36408a347cddb8cbab317de522989fc3db628718310e1a9a1a110433326853c570966f611061c18a1f81a0c1010a15ffdfabfd1027c1a76f66655eb9db3c1f4276a20cebcd95d2006b9ca72722648e1c25d94dcb323d10646170c6edd9883e2b04da45fac70b5c26d5e033ab9fe0566c1ea763a549b1c28e20b5016949c7f4d181a122d729453e8685c96909c2721236641e4e483b3650506d9f4f863e6bc47b6d2cf2dc69de4213ab304756158e9c1e1cf23a3830266ecc4cdc8929a9c46351f1669d784d01c4998b0532e0dc5cf050b78c516862a2c0804504b0c957af91ccde22d1963f6b647b5540f5dc51e4e70372e786a0aa8d37ef160b402bfb0054b6e8a109412e5621883742d3cc055c760a9260134710234f384376804b0b60783bc04d31808424 0x2203c0510fe0041492821a028a285b0c00883f9930660901c8380e60744588c0a64681d1670da5604802e0be1f83d0210b21582a07b00405c0d1860bc10c3a17505e110478820d809ccc0230a62642006a1285c44b03001c1a034865106078100250080b03709b08c0200305f25a0581810301e2044685c0201dc0901510e0c82903602818c140311120f0bc83d2c80e84d1800c21d82804c03e1f00c8550180242c9110920dc2683c07a0703788504c11c038720841382508a0300a81a8832900144d0950da210310570e825c330941325684902b06802c38029000244371322565f41380a0262382083f07c0ec2e84f09606c358 11
def extra9 (i : Nat) := getWord (joinBits (joinBits (joinBits (joinBits 0x1243554e1 240 0xf5f3420018) 920 (joinBits 0x4561230fb 280 0xf0142453f10000000000f0142453f1)) 1400 (joinBits (joinBits 0x543210fe52 160 0x543210f3e2) 440 0xf123454f10f123454f10f123454e10f12345f410f123454f10f123454f1f0143452f100000000000f123454f1)) 2600 (joinBits (joinBits (joinBits 0xf123454010f123454f1 320 0xf0123454f1) 800 (joinBits 0xf23450e13 680 0xf0423451f1)) 1280 (joinBits (joinBits 0xf0423451f1f042345f110000000000f0423451f10000000000f0423451f1f042345101f0423451f1 160 0x56341200fd) 440 (joinBits 0xf042345f110000000000054231f06a 240 (joinBits 0xf1423450f1 120 0xf5f3412008))))) 40 i
def t10 := table 8 3 1015 47 0x1f9d0d1850413f381830a0827e7534614104fae280c28209edc542051813db82838a2826f7744714504deeec8e28a09bddd51c514137bc123122826f7744614104deeea8c28209bddcd1850412fbc2240a3025f7864814604bef0a9028c097de491c91812fbc2238a2825f7864714504bef0a8e28a097de0d1c51412fba923923027f1024070504fe2020c28209fcd510051d83f9aa000a3b07f3040014760fe7088028ec1fce100051d83f9ba000a3b07f3744014760fe6860028ec1fcd080051d83f982200a3b07f3074014760fe60e0028ec1fcc150051d83f982800a3b07f3034014760fe6060028ec1fc4090201813f98120403027f3434014760fe6848028ec1fce610051d83f9cc000a3b07f3874014760fe70e0028ec1fce190051d83f9c3000a3b07f3854014760fe70a0028ec1fce0d0051d83f9c1800a3b07f3820014760fe6ea0028ec1fcdcc0051d83f98b240a3027f3010714504fea021028c09fddd12051813f9c9203a2827f3154714504fe6ea8028ec1fd40921c1453fbc9238a28a7f5010714504fe6020c28209fd4251c51413fa8124382827f3724074104fee0490e0a09fde511c51413fbba238a2827f7934714504feee68e28a09fcdc80051d83f9b2a00a3b07f3650014760fe6a68028ec1fcd4c0051d83f9a9200a3b07f3520014760fea020c28209fd40921c0413fba1243a0827f7024870104fee8490e0209fdd091d90413fba123920827f5044614104fef088c28209fde611850413fbcc030a0827f7874614104fef0c8c28209fde151850413fbc1a30a0827f7754614104fea0490e0201bbdd11c9145377c1a3122825ef844824614bdf268ec8c297be4d1c91812f7c2239228a5ef874724514bdf048e48a297bd4d1d91852f7a9a3923027e9034070514fd6a88048ec1fad500091d83f58200123b07eb844024760fd7080048ec1fadd00091d83f5ba20123b07eb430024760fd6840048ec1fac110091d83f581a04030a7eb074024760fd60e0048ec1fac150091d83f58280123b07eb020024760fd2068100c29fac090091d83f5a1a0123b07eb424024760fd7308048ec1fae600091d83f58b241230a7eb934074514fd70e8048ec1fae1c0091d83f5c320123b07eb860024760fd70a8048ec1fae140091d83f580839228a7eb154724514fda021048c29fbc502091853f789041230a7ef544824614fdee89048c29fbd0c2091853f7a1041230a7ef010824614fde869048c29fbd092091853f5c180123b07eb820024760fd6ea0048ec1fadcc0091d83f5c120123b07eb754024760fda020e48a29fb40d21c1453f684a39228a7ef010724514fde280e48a29fbc101c91453f781039228a7ef120724514fdea88e48a29fbe511c91453f7ba239228a7ef644724514fde860e48a29fbd081c91453f7a1a39228a7ef424724514fdf268e48a29fbe491c91453f681a4382827ef034870504fdf268e48a09fbdcd1c91413f5b900123b07eb654024760fd6ca0048ec1fbd8d2091813f7b1a39228a7eb534024760fd6a680e8209fbd4d2091853f7a9a39228a7ef534724504fd6a60048ec1fad490091d83f5a900123b07ed034870104fde8690e8209fbc0d21c0413f7a1a4380827ef434764104fde868e48209fbe4d1c90413f681830a0827ef834624104fdec68ec8209fbd8d1c90413f7a9a43a0827ef534870104fdea68ec8209fbd4d1c90413f681a4380807ef320824614fde640e48a29fbcc81c90413ec82003a0827db054034760fb60a0068ec1f6c2000d1d83ed83a01a3b07db070034760fb6060068ec1f6c0800d1d83ed84201a3b07db034034760fb6048068ec1f6c1001d0413ed8a043a0827db984034760fb62810e0209f6e6000d1d83ed8a03b20827db874034760fb70e0068ec1f6e1900d1d83edc3001a3b07db854034760fb70a0068ec1f74100051853ed8a03920827db834034760fb7060068ec1f6e0800d1d83edba801a3b07db730034760fba080048c09f6c501c50413edc1201a3b07db754034760fb6280c48209f741121c1453ee8220102827dd040024504fb6280c28209f741121c1413ef8224382827db720034760fb6ca8068ec1f6d9400d1d83eda9a01a3b07db530034760fb6a48068ec1f6d4800d1d83ee8224380827df140874104fbe2810e0209f7c1121c0413ef8a03b20827df140724104fb6108068201f6c2000d0403ed83801a0807db054034100fb60a0068201f6c0d00d0403ed81801a0807db024034100fb6040068201f6e6100d0403edcc001a0807db874034100fb70e0068201f6e1900d0403edc3001a0807db854034100fb70a0068201f6e0d00d0403edc1801a0807db820034100fb6ea0068201f6dcc00d0403ed83a01a0807db824034100fb6ea8068201f6dcd00d0403edb9201a0807db720034100fb6ca8068201f6d9400d0403eda9a01a0807db530034100fb6a48068201f6d4800d0403ed99201a0807dd044870100fbe2890e8201f7c511d90403ed99001a0805bf150724604f720a0108c09ee41401d1413dc82803a0827bb094044100f76120088201eec210110403dd8400220807bb070044100f760c8088201eec180110403dd8200220807bb030044100f76040088201eee510110403ddca00220807bb844044100f77080088201eedd00110403dd83a0220807bb744044100f76c88088201eed900110403dda180220807bb420044100f76080088ec1eec110111d83ddca20223b07bb940044760f77088088ec1eee100111d83ddba00223b07bb744044760f76c88088ec1eed900111d83dda180223b07bb420044760f76120088ec1eec200111d83dd83a0223b07bb070044760f760c8088ec1eec180111d83dd8180223b07bb020044760f76068088ec1eec090111d83dd8280423027bb050074104f762a0108c09eec540091813dd8a80103027bb044044100f76868088201eed0d0111d83dda120220807bb424044760f77308088201eee610111d83dd8a843a3027bb980044100f77300088ec1eee5d0110403ddcba0223b07bb150864604f772e0088201eee5c0111d83ddcb20220807bb964044760f772c0088201eee580111d83dd84a0223b07bb934044100f77268088ec1eec542091813ddc980220807bb930044760f77240088201eee480111d83ddc3a0220807bb874044760f762a0ec8c09eee1c0110403ddc380223b07bb864044100f770c8088ec1eee180110403ddc300223b07bb084044760f7a0a0028c29eee0d0110403ddc1a0223b07bb150724604f77060088201eee0c0111d83ddc100220807bb820044760f76ec0088201eedd80111d83ddb980220807bb730044760f77248088201eee490111d83dd8a840a3027bd050084604f7a0a00c8c09ef4140091813ddc120220807bb824044760f7e2a1048c09eec1401d1413dd8a80323027bb764044100f76ec8088ec1eedcd0110403de82a43828a7bd050714514f7e0a0e28a29ef41401d1413de82a0102827bb724044100f7a0a90e0a09ef4141c51413df82a4382827bb720044100f76e40088ec1eed8d0110403ddb1a0223b07bb630044100f76c60088ec1eed890110403ddb120223b07bb620044100f76c40088ec1eec0d0110403dd8120220807bb324044100f7a0a90e0209ef4141c50413df82a4380827bb320044100f7a0a90e0201ef4141c50403df8aa43a0807bf154764100efa0c8040c09df4180211813bf8b23b20800ff9848646549fe2e0ec8c293fe5d1d918527fbaa43a32a4ff7547646145ff3090c8ca9be41c02118537d8420320806fb080064100df60a00c8201bec1001904037d8100320806f9010624504df6a880c8201bed5001904037dc220320806fb840064100df6e800c8201bec1501904037dba20320806fb430064100df68400c8201bec1c02118537daa20323b06fb540064760df60800c8ec1bec110191d837dc220323b06fb840064760df6e800c8ec1bedd10191d837da180323b06fb420064760df60a00c8ec1bec0c0191d837d8100323b06fb054064760df60680c8ec1bec090191d837c83a04032a6fb074080654df68680c8201bed0d0191d837da120320806fb424064760df73080c8201bee610191d837dcc00320806fb980064760df62c90c8ca9bec5c1d918537dc3a0320806fd010864654dfea890c8ca9bfd0c21919537fa1043232a6ff434864654dfe8490c8ca9bee1c01904037dc380323b06fb864064100df70c80c8ec1bee1801904037dc300323b06fb854064100df70a80c8ec1bee1401904037dc280323b06fd070084614df70680c8201bee0d0191d837dc180320806fb830064760df70400c8201bee080191d837dba80320806fb750064760df6e600c8201bedcc0191d837d8220320806fb824064100df70480c8ec1bec0c01904037dbaa0320806fb754064760df6ea80e8a09bec0d01904037e83a43828a6ff744874514dfee890e0a29bfdd11c914537fba238a28a6fb144624504dfa088c48a09bec0901904037e82a3122826fd070874504dfa0e90e0a09bfdd121d14137f83843a2826ff744870504dfe0e90e0a09bfdd11c914137fbb23922826ff754874504dfeea90e0a09bfdd51c914137f8403122826ff010624504dff088c48a09bfe6118914137fcc03122826ff864624504dff068c48a09bfc6018914137db900320806fb720064760df6ca80c8201bed950191d837db280320806fb650064760df6a680c8201bed4d0191d837fa9a43232a6fb530064100df6a600c8ec1bed4901904037da920323b06fb520064100df6a400c8ec1becc901904037e83a4380826ff074870104dff2e8ec8209bfdd51d904137d9900320806fd074870100dfe2e90e8201bfc5d1d904037fcba3b20806ff7547641003ff2e90e8ca87fe5521d1952fc8083b230a5fb094074100bf61200e82017ec1c01d0402fd83003a0805fb050074100bf60800e82017ec0801d0402fc8083923025fb074074100bf60c80e82017ed5101d0402fdaa003a0805fb054074100bf72880e82017ee5001d0402fdc2203a0805fb840074100bf6e800e82017edd101d0402fdb2203a0805fb640074100bf68600e82017ed0801d0402fc84204032a5fb844074104bf60600e82017ec1101d0402fda1a03a0805fb424074100bf73080e82017ec0421d1952fd8b243a32a5fb980074100bf72e80e82017ee5c01d0402fdcb203a0805fb960074100bf72a80e82017ee5401d0402fdc9a03a0805fb930074100bf72400e82017ec041d91852fdc3a03a0805fb194764614bfa0210e8ca97fd5121d1952ffba243a32a5ff644874654bfe8610e8ca97fd0821d1952ffa1a43a32a5ff424874654bf70e00e82017ee1901d0402fdc320423025fb860074100bf70a80e82017ee1401d0402fe8083b230a5fb034074100bfa088ec8c297ec511c91812ffc2241230a5ff140764614bfe240ec8c297fd511d91852ffca23b230a5ff744764614bfec88ec8c297fd0c1d91852ffa103b230a5ff434764614bfe848ec8c297fe4d1d91852fdc1803a0805fb820074100bf6ec00e82017edd401d0402fdb9803a0805fb924074100bfa088e48c097ec0901d0402fe8323923025fd054724604bfa1010c8c097fe112091812ffc324123025ff854824604bff288e48c097fdd11c91812ffc9a3923025fb834074504bf6ec80e82017edd501d0402fdb9a03a0805ff844724514bff0e8e48a297fe111c51452ffc3238a28a5ff834714514bfa108040a097edc901d0402ffc3a43a2825ff864874504bff088e48a097fe1d1c91412fdb9003a0805fb654074100bf6ca00e82017ed8d01d0402ffb1a43a32a5ff634764614bf6c600e82017ed8901d0402fdb1003a0805fb534074100bfea690e8ca97fd4d1d91852fda9803a0805fb524074100bfea48ec8c297ed4801d0402fd99203a0805ff984764104bff0c90e82097fe1d1c90412fd99003a0805ff184874100bfe308ec82017fe611d90402ffc3243a0805ff8347641007ff289048c08ffe5d2091811ff8ca3b20807f9010864614ff20210c8c09fe4041d91813fc82a04230a7f9050084614ff2088108c29fe4100211853fc83804230a7f9010824604ff20a8108c09fe4110211813fc8200423027f9070084604ff20a0108c09fe42401d1413fc83003a2827f9054074504ff20800e8a09fe41101d1413fc82803a2827f9094074514ff20210e8a29fe42401c1453fc80838a28a7f9024070504ff2108100c29fe4041d90413fc8083b230a7f9034070514ff21280e8a09fe40421d1413fc80843a0827f9090070504ff2020e48a09fe4041890413fc80830a0827f9094074104ff21200e8209fe41c01d0413fc83203a0827f9060074104ff20a80e8209fe41101d0413fc82803a0827f9040074104ff21200e0209fe40d01c0413fc8120380827f9084064104ff20210e8201fe4041d90403fc8180423027f9020084614ff21280e8201fe42401d0403fc83803a0807f9060074100ff20a00e8201fe41001d0403fc81003a0807fb020074100ff2108040c09fe40c01d1413fc8420320807f9080064100ff20a00c8201fe4100190403fc8100320807fb084064100ff20c80e8a09fe41901d0403fdaa20320807f9040064760ff20880c8ec1fe4100091d83fc82000a3b07f9054074100ff72880e8201fee110190403fd82a0320807f9054064100ff6e880e8201fed9101d0403fc8280323b07f9030064760ff20400c8ec1fe4150191d83fc8220123b07f9080084610ff20290e0a29fe41c0091d83fc82a0123b07f9050024760ff2040048ec1fee110091d83fd81a04030a7f9034080614ff2088028ec1fe40521c1413fc83800a3b07f9054014760ff20a0028ec1fe40521c0413fc81800a3b07f9080064760ff2100108c01fed510211853fc80a41230a7f9014874654ff2108100ca9fed510191d83fd8220323b07fb744064760ff68600c8ec1fed080191d83fd8120323b07f9014724514ff2029028c09fe4210201813fdc2200a3b07f9024080604ff6048100c09fe4051c50413fd81803a0807fb190020604ff20600e8201fe41101d0403fda1a03a0807fb434064760ff68480e8201fed090191d83fd8a043a28a7fb140874614ff62810e8209fee610041853fdcc200828a7fb984064100ff62810e8c09fec5021d1413fd8aa43a0807fb984024760ff7308028ec1fee610081813fdcc000828a7fb980064100ff7300048ec1fec0521c1413fd80a4380827fb980014760ff62810c8c29fee5d0041853fd8a04323027fb974020604ff6289048c29fec502091853fdc9a00830a7fb934074100ff62c9048c29fec552091853fd8a04123027fb934074514ff62c9048c09fee4d01d0413fdc9a0103027fb140764614ff6280ec8209fee1d0041853fdc3a0320807fb164764100ff6280ec8c09fec551d90403fdc3a0123b07fb874014760ff70e8040c09fe4210191803fdc380123b07fb870014760ff70c80c8201fee190091d83fdc3200a3b07fb854064100ff70a8028ec1fee140190403fe82003230a7fd040084614ff6020e48a29fec041c91413fd8a039228a7fb144724514ffa080028c29fec041c90413fd8aa3920827fb140724104ffa040108c29ff4080191853fdc1a00828a7fb834064100ff62c8e48a29fec551c91453fe82243230a7fb140724604ff6280e48a09ff4042091853fdc1a00a3b07fb834020604ff20680e8201fe4110190403fdc9203a0807fb824064100ffa0a9048c09fec551c51453fdc120123b07ff744824604ff20480e8201fec5121d1413fd8a24382827fb144724504ff6e880e8a09fee4d01d1413fc80a38a2827fb154724504ff70680c8209fe4051850413fdcc20102827fb980020504ff7068040a09fe40c0190403fdbaa0320807fb754024760ff6ea8028ec1fedcd01d0403ffca238a28a7f9034064100ffa1200e8a09ff40421d1413fe8083922827fd084020504ffa0e0e48a09ff4111c91413fe8400122827fb724074100ff6e480c8201ff4191c91413fe82a3922827fd044870504ffa0e10e8a09ff41521c1413fe8483922827fd034870504ffa128e48a09ff41d21c1413fe83a3922827fd090714504ffa0e0e28a09ffe511c91413fc8120320807fb654064100ff6c680e8201fed4d01d0403fda9a0320807fb534084614ff6a680c8ec1fed4901d0403fda920320807fb520064100ff66480e8201ff41521c0413fe8483920827fd074870104ffa120ec8209ff4191d90413fe84838a0827fb144874100ff6288ec8201ff40521d0403fd99003a0807fd014764100ffa0e90e0201ff4241d90403fe8323b20807fd090714100 0xc05194a3414032806828068280ab594a318c6318c60594a0ffe431ca4d5a1052b5ad2ad0bf8fe52800b5fc1f90c605aca5294a55807218c631800b41405f8c030006b014ab2946318c6318e40594bff80639491f6ad0829565f8fe518c6018dad2ada5583eb18fec28c6818c630001202d652a105294a5294a01c863183e0420a5297e21086528c0b7386000c7218c6d5a10528c6d6b4ab18da5180031824b294a5294031c8632116528c63183e05a105288412ac802880b294a52945f10865294a037ccb4206528c6318c034206318c6318c6342063295eb421ef7bca5294a318c63048bf282455ad08420a2914520c80d2ad6842105289a51342d4216b048a52940d294a840805294000164b5a10842108414a201645f944202040580a5ffc0c28c3f29463194631fca518c6318c632c205003f218c6304bf242c1028c631ad6842105294a01344d0b4a55ac60688a52880318c63180ab00d6390d052958c1800807d6b294a5294a5294a5288120145f1080559560fad05187e0414a518c6318d0818d6310c6302d1f02d08294420ac1f5946818c635a1082956218c63f946340c63180414156018105f8d0518c004144358d00001681ad652a10842105294a52944040042101021805ffaca518d7f28c6b2fd0518cbffb7ebffd6bfffedfad7ffad0828ca36ffff10bffffd6828c21fffec28d6c420a318c6518ca51a0b08146dfaca5f8e5f181652ffeb697eb5946318e0bffc7f97c5f10c6318c631ffe018cb297fff94a521fc7f18fe24147f400431fd68195adfad6b42105294635fc631fca3ffd82414631fda210c00295a3f8c631fd65fac0012ca52886bfffe058fe05a0a3597e0fad7f58d65414a5294a5114000200318842ffd1f 1294 0x3ff99c7fea46ff88d7fe818bfc56fff4fdcfe6b0bfca5b3f6fcc7ed96ffda185f9d88bf21137e3c96fbe3a5f72eb7edc237db2a6fb54c7f69d6fecc937d8d50fb1139f566efea426fd4816fa7be9f4a1afe8e427d11d5fa0287f33c6fe4ac7fc8c80f9005ff0d70fe152c7c0a0af80881eef31bdc5557b7193f6c399ec84b7d867b7ada69f4e247e921bfd20a8fa3724f44647e79a07cee44f9d385f34369e6435bca77bf94941f28c8de46263c8b4df90694f2038fe3f3afc761f78deb8f1a473e2ca67c5948789a51f112e5e1ab8fc356a784a46f04e41e03a6fbf078f7dce7efa6abdeae8bbd51d779666ef1483dd990fb9eb2772719ee4ce9dc0f63b80e476ff21ed94bddb0e03b613876bf5ded4e45da3bbfb44daf67974ecbab1d930ebae128f5a553eafef3d5c3ebab571f564e2eab2d7d54aefa9f8a753ed4ea5c71d4ad5ba906cf4d3e2e97f95d2dc8ba531f745897e89f25d137eba0d81f3f80ae7ae8dceefbf9d545f399d6e728cfcde0ff9a758f33e46e66f7fcc1dab97f5c72e4c4e59835ca9f1b9489b72908be4adffc813a38feaaf1eed9e3aa61c74fdf8e8e7f1cad6e3751fc66e938b668712985e20eebc41ca38731d70d14de16185c2903b84749f08399e1022fc1a38383170f04995e0246dc03da78008befaa15df362dbdf6bf7b8b76f4beede2151bc29f778521ef07b7de0da3bb834775e206eb4b2dd56c3b9f4b373c6dee6918dc96a3b88f2370f476dde84db54a1b6a4276c9556d8dffdb068bb57dfb6ac98ecde26d9a7dbb30f576570c6c9b63d93247b2617b62fb3ec3348d8226bb0323f602d16bf835d78545aeee875d37deb96f3d72159ae33975c34ceb790bd64abbabaf47575556adb80d59be5aaf813540e26a78d1d4d45da93453520256a19d2d42c9ba79f434e02be99438d2e341a5c53f4b59a6960a0d26627a40b934814068a047d135cda21a1343985e85386d09871a0cbc34107e67c1d3cf4bb39e3aff3c423e740f4ce7ac39c9a7738d52e718f6ce19759bc583368dae699d4cd071399efab33575666048ccb0c3994bbb32956e646b8cc8c8f98c5632d3ca659d8acad3f994bf13294d36502c0c9b0ef935a8724e92e48787c909579205df236e6645a7dc841e38ff9431e61fe3b30ac74a698d7d4b197c162fff5c5a4eb8b34ef1333ae2623bc4a2d78939b311f25e234a4c4692388c9a7113ae6204bfc3b5bf8742db0e848618f1ac3063b860a6b0bbed61649dc2aec7854f130a912e14067c2643d843ba30825460dff3c1af03828ecf047fb6063d7c0736580e23b01bda602b9ec00a6b7fa17efc9c7df8b77bee0877d9e3ef97c0df2229be21b37c081ef6d655ec6c1bd76ed79ce3ef293dde51f7bc6f01780f06edd6ddd99debaa677753bd2ea57ddd1f50b9ef2973d51ee51eadc9fe2b9048971b506e2465dc48b8b88d2770e3f2e166b5c0f3fb7fb956fc97ede42f5bc74eb7826b6e9ef2daf02db42feb65d276c99c6d9174db161cb5707b6a6fbad3b19da6fcfb4d14b696b72d22415a4170b47b1568f29ed1931da2f19b44bd767f9facfce659f600b3d651677fc6ccca0599657b2c2db64179ec6f00d8da7bb198b7632cd2c603858b2a3b13817608ab6bff71d7e921afcf515f5a82be904d7c98baf61175e671ebc6bbd78169aefe095cf50eb9e50573a35ae4e8b5c36deb791456e25eadc37f5b038eb5e12d6b3cfad51255a4a56b3fcdd64d97ac023f57abcaaf07d55a76eab134355f626aae73554247aa538f5422eea6a4354b005a94f89526252a4b86548f75a8a28d50e062a1a73d41f5ea7d7e74f974a9e815538090a6d4474d305a99e4ad3354da62ac14c45e6987f452e004a57e154ad83a93330523d7ba418c947d6428f28b51e173a3841f46f3568c6e9518883a3069345852e8794ed0ddb4a1b0e7434fce8655750c665a173cb42a3868391a50473fa0715140345e802cfcfee599fb2bd3e5c527bd94cf73649ec7b33d0a167932e4ec2349d244f39b8667343e4e3d6b9c78bb38ba26713e4ce23799c2879381b067018c4ddbcb9b9f9f37216a6d0f74d8a6b9ad247349b5e685784cee2999a7a532b212655c5ccab649954bd329cc665312cc3eba98752b300426600394bc7279757492e89965d003cb94799696532b28b255867ca82e194fa3d29dd0e5339aca45af943aaf280c224f1ef49a8dd932c8f255fbe498854921fd91eefd23a1c646e9248dc119141c922108e43c76c876899098f9211bb241fcbc8214c903f9f206c6240d4ac811469015dd20103a401dc47eb428f3f011e43023c566c7879c8ed6f91d486e3a0924740298e41331c5c0e38781c6cff48d41f51a1c3a33e88c678ca8ce45919c41633253c643858c8341186c5e3074845d9a98b7b8116c9c62d6c54579fc89dc5d136c62265e1c4bd2a897761127e4e243e9c46d0388d1571142221f9be43eb008727f50e1a9a1c1bf437cdc86f81b0d79261a68d434d0b866e7d0bf3de1760c42dd5a859ce70a615612cdec251de8481ff0900de119d3c2203184226308044e0f4f1c1c7878374e306aea608726c0fbfe81b8350309ca0237dc035bd80620300818e00e4a40117c7fe9feff7989fdc1b3f8f777f1d94fdfef5fae913f57e87e9592fba25df71a03ee3217d7d0efa9fb1f49343e819e7d0116f9a05df323dbe5ad97ca364f91515f06a3be03d17b42e8f66655ec960bd627f7ac1f6f47969e8b72bd03d679b5a2f32929e4a0dbc915f78b7fcf0fac9e1eeb3c2fdf782546ef3dd9de4ce3ba4b877364aee504ddb3fa3b61997695a4ed1749d922ebb190d761a52eb6e35d61fb3ac18274eee8e9c83dd3636b9f50173c8cce76a41cec5d39d85773ab50e74dc1ce37b39a325734238e67b2dcb52eb94ca3728caee50dddc8dd839175871e544e3572dc69e9b8bf4471722ce2ddf5c58deb8985e70d87ee17b4dc25f1382ce77019ece02921c0435b803c86fcbd6df1d7dbdce8b76ca06ec3badd66f9ba2e1b72a4b6e4cf8dc59c1b71e2b6dadc6d983adb0469b5e8836b34c6d42a0d7df65af63e35d5f86b878ed6ac71ad2f1357b836af2cad5db59a905534e46a696726d23269a3fe8347f8268eb22d1c08da2da0b43951683048d03e11a068a33d4466760a8cd86599991333320366525acc962196f21b2ae08655314ca4dcd94817328ae764ea3cc953b19247fb234926407c4c7e3958f648b1e0f163b764c6cc158d11331708a624372c42fe1874703072e2609720c0c66980c29aff4d05f9768bee5957d7fbaf9c265f2450bd80ed7a8312f4d665e94cebd091979d32af21475e3e42bc69fd78b13af133b5e1c8cbc38057680daeb3b05d4a50ba938174f53ae97115cdf28b8c6b1717af2e0ac15c052eb7bf696e1b02da7285b2060b5c26d6a3caad389c5a45ecb42ef9673ef2ce79959cba2b3414d62e602c003657befaaf488d5a3b6ab2b41563ef2abb9a1565d22abf10553dd2aa6d8d542c22a5edc54b644a93fc55028229b85e53522aa62f054c42aa9723652d3eca586a54afe7a940d6526c70a4a0754790528a913510da8a1c059433c1a85e7b50b3eea0e5c941988a8271b5040d6a036a1403792801fb4ff30a9fd4353f6b627e6474f9acc9dcc913b7d9a75de14e65489cc0a939356a6fc904dd4009b561536182269bf94d1b889a36d53411b26747d4ce652999d19333252642ca4c2a0a9825d93029d25d12a4b4a04964a312b77fa56b924ac1b6955cb5259a7a491834922989233f9241be2475ef489b9c90d0552082223e6ca47bcbe8f6b491eb5c23d404479c7a8ec5811d15aa39a784710668da6111ab7ca354ce46515e8c586d189db22f68c45dd028b0f8115cf0a28a5444c0fa8931e50f88421d32d438e58866ff10cd86a192be42ceec855db90ab7d214de642885084a8b5091fa211cd0422ccc835f4905fe2a0ab2541200e81f8a5017829ff6903f7ed27ecea0fd5749f98e23f0f487ddb14fab249f523f3e1bf67c0850f7b5d1ef0d93dda187adedcf51451e90d13cedde79afe4f32591e4d2a3c4d32783ec0efda89ded4e3ae5a0759b1cead281d37c43a668a746220e81591cd71839a8ac72e4fce5c601c8ebb390f2671dbd4e33841c64d938c102709270e01bd1bf5ec37e0106fa680df01b9bbd813713cc6d4d88d9e699b3bed3651706c1978d7d771af2a035ce746b347cd37021a550234a718693274d23021a31c4346386683c54cbb199951f432a3b264fae8c8dae19187b322fac6403f4c7a6698ef3d31d8a2626bc0c3fbb986fd030d52c61688cc25a4183c522fdc385fa4f8bdc4f97b29a2f1f025df9ccbaf0b975d6c2ea9305d178cb9c2a9731f82e3fea5c3ca8b7f6016fcbc2dc0c85b687cb629496c1332d7d28599044b21e7162cf82c4cf657d428aeacb95ce242b897e56e7c4ad6cf95aca52b440a566100a8f6014f2a129e4ba52c1bca4e049497a328e1305094bca0c799418cf27f1da4ecb409cf8f1382fb26f6ac4d375099eb41303dc26051c4be4809742b12d66f259a024b050895855129bfb2523b64a17f0942fd12534e24913248a210908fb9205e523fef647d5a88d5ab918bbb22de2e457a408ad649132f121de5c43bc3886f0b10d4d2219c0042c8a8854fb105ef320738240a6e47ef658fca1a1f2c9a3e1a247811c8eb60b1d237e3a3214736208e69641cbafa395c806efc10dd2b51b507c36466c6c1340d41e41a68d234c048695690d1ce019ee2a3363b8667a00c98f218b81c3112c4621820befff17bcfe2f2fa85cad50b874216e23c2d9ad459d3b0b18dc161eb42c395c576530ae59d159fa22afa4855e950a9645151fd22a021851a3389e0b813bafc271f0c4d26e899b2812d2042570204852289077e11966222bb5044d650873b7109b96208be84081e07f9510f55b61ea6fc3c9a8078c380f00fe1c61743859606b2d50cea921852c0306a40600ba0bfd8817c6b42f4e285ca300b8a7017016c2ded305ab230b2878163c3c2c21e85581e09f0fe12bd802461c844dbc084d6210337c1fcc803ea0607ce080ec65c1d8a983a0f2073ff00e5dc41c280034cc10672dc0cc914198e18318fa062e360bf38c1744382e59705c7700abbec144e08259cd0491cc08f73c0e37c01b0dc030d6205dd400bacb0170b602d4520585c009e05013a220269d004b64409298011bb401c1620361ec0661d00ab9f0126b401f0e402b2b0042ce 0x7e1cc17b860e76a03901c4306114242854c4382391c007d826a36e0c400343462ea04b0c3045e2980c3050047403a0b087fc360335175935c7960e600406242562e417f8c7c7e8233018847c0a23271b290685164b92be044c5f23bc14c890c34a0fa07780782200541a90e986cc35517b0c38c201250710b305483df02b8a9417e3b11159e7c28822408501146ee2fd16881b00c2098076860c86a4ca17a8e847e417806a16b044e3cc0d812082620713b408c466a4eb1508b987e84aa28e89c42303d51930cac4101670ee0c680123de29c95881b07991f9857c0783911118e1c5da04008c8888fc439a0eb08ecf0c70d0660044ea801217383107602590d9913400437c0a784585ea47b2e39a780223e5109084c0b40a3187066c5fc13318415ec39047f0a60c800664a10ed8c3c8323da3950c64bda3c520181b0f6a2dd2960c7c8f432c197084475865a11418fc5d80df04d835cbea3931e408146e80e31628b8060270c28786bc33a19805b8efc06825013d0bdc22a6d706b0f740ba24928002ec2b202e0440fb85442ac0da03b02d03370490ecc12011e36181fcf7c2e90e900bc6040c11a285d0f2c3c02249b582642d832e82ac78416a0a088242f210900d8b6844e4141038dd47e017e064064c6503880d79edcfb60a5090089871e6232740e246522d33c391a40c440f0148a3079046a0208dc072e7780e8075c7a833b0a80b80afa33919d091022e04210c87601081340560860ab81731bf06885602bc159022c0dc25134a082c0284e118d8934fc03a531a992c65061e1659880fd65f23c198681b015a1b61dc0a363293568e940c80c5139012c1702ef1658a387161a91c707f46060d51e006ac64a3da1b78cf407633a3780c0424042616c01483ca0f91180d6c68e2040070a8c4440a91c30364d2a3971e90fa0e9c3c10351e5492a20e0e2852c16c07316c8c702dc0bd2df819c8480f81cd90587c21e31ad01102461b30f398a06b874603f14e082a3c91f1870c1861cf0f58b846ce1970888f2872c4631128ec877e4bc1540b884802d726a0ea840c19a0161774c4200b1ac1e105a010e17588a4c6e0fb13a03400b01fd2af0dbca9c2c107b886482e2e81bd12f85ce6ae0358bb836a03203291f002a79c0030f0cd8c00c1f312f41681710378b6c8ce0cb03e8150e003a21da0fa4e2c0cf13006c8e6c6c91bc83d819467615c0ee4cbe5b201009a466c16f0248850f825f13f39bd0db25e71100d707060482ab8190a3a44c1468414588124278894c6f62a70d407fcb6a5fc1e2062803015024d0af81f805016e06085241d114287906f41e91c89c2c2ac48d1ae8ee83823e41a8886049a36503c0708206080069819461e05b04f8134a6c3af12602044020f217907880d077201b0284f503c62f315084822031670b78c560131b985603ca60f1ad97a851e0560de8e9c68232c2319b340f04ce1b4856c46412f157899054c1dc30a80b445809306104f03421450b906384aa2e519081b431e1fc31c969841425b03b051c52e2960f719986d45661e804f87461de0a50bc8f8a01329b86b869436119a03703162dd15c8f4885620d0b58a7074e6c01588a1c21a2bf17d86c4d6a2cd2141a6c24c3c6060137876c3cd1e117a4fe238516f0d74d143903690b68cc41b108e0f1c89004e1e78f6cc702751de9b7cc8e21709d81542d83710f807982d22140450dac58e38e3a9842c8684ba0478adc7283bb3e210f81c00d90e30b50b8046d36e17a07de1991d483fc4fc26110b0b3c2767ea17e0d104ee0b209c8d340e83630968df44761b918f17d0e7e36d33508001685d506115b439407a30106dc5c63f60f21cf032c2781d58f9806034b1d6011c15e44b32a0d8856833011506903180222de0bd053a1700cf82c475c28618881f4c522fa13608b40543e9135841c0bc1cd07982b4002376012810cb800350f907b4b7e76c05e158c30205318b848cc842930fc870cb6e78a12486b46787d10108cbc20c12704187d04fa1da1250db41fa1eb31e8d5830822e2638d9c9fc08718482b84ac0c92fb165044276e3c212243d06651dc0acc23c2ab0460a4463005c0b005d034e20c1dc82441e03f229481881600c52f78eec0be1e02e38b0c8e03592f8199c2242d41b59cb42740861a78d906f26ea3869714b761c81a000cc7a62d50bb0e3002038f161067030e3662a4075030a2c81368c405103dc0d000b0396037072891460a28b0e606e03e669f13186340527380598c80cde322128807039c27b12409309a42aa04f936c36c2820530aa43f40c00a68584c964ee182039c22829004e01d41ba2361398c18e903d61af05947da70a00f81e40f60e411a04e8e1025e13f81a00860941400040a8a6bb0c9048820438d0bd0cf863c3a01c808f00940461801c643e20b50a30cc468c4040e8971007c74206883682421751a18c40f6e20c2db12b8fa271319983345a627902c82e43e61520ec8198efa4f413407a8e2a3491af86541482952fa9854eae0070540e98ba60a014d06785985e01ac8d3027a2f33b215247b01511e6913c7b21be20003a41d41771f38a1050c5df2f087bcde60970fd89382c80a71e18ec08ee3eb0dd06f85b63060d500e07ae3c70bf950c32239e01c80fc5be3a40858e4820812a0bf8b2816070711f002816642804f0fb063a0660271dc491a5ec15d0af404e323104183ce48169234986c17449d1bf82647da3121cc07f83ee07632c0320c5c12e18a0eb460a4af0630f3873a26e0229cc85f03f509204a02600d13230e909440230aa077432013f1651d6049e156138095c23425213e02a86c015d1418ad803a35001e8a246164221ef0038f2a3e80aa84201ea25d32e04043f01b43ee98d466e6e830f1bc421811a30e845470221f0648ef44be3821ca1e6c54028108797ecbbe08e00281802701800e48 13
def extra10 (i : Nat) := getWord (joinBits (joinBits (joinBits (joinBits (joinBits 0xf0251354f100f6534210e 1320 (joinBits 0x6f5432100e000000000000f102f43e52 396 0x10ff2345e300000000000045f23f1e06)) 3300 (joinBits (joinBits 0xf025135f41 1232 0xf0142354f100f6534201e) 792 (joinBits 0xf653420e1e 484 0x6f5432011e00000000000564231065fa))) 5808 (joinBits (joinBits (joinBits 0x1f24354e1 176 0x564231046fa) 1584 0x56423100fa) 3344 (joinBits 0xf014235f41 2992 0xf0142453f1))) 9856 (joinBits (joinBits (joinBits 0xf014245f31 440 0x654310f2e9) 2376 0xf123454f1) 5940 (joinBits (joinBits 0xf12345f41 836 (joinBits 0xff24350e12005634120fd 264 0x56231f04a)) 1540 (joinBits 0x10f2345ef3 1100 (joinBits 0xf6342105e 352 0xf0423451f1))))) 22572 (joinBits (joinBits (joinBits (joinBits 0x563412002fd 1628 (joinBits 0xf042345f11 660 (joinBits 0xf1423450f1 264 0x54231f06a))) 2552 (joinBits (joinBits 0xf1423450f1 528 0x1ff23450e3) 924 0x4f231f055f6)) 5500 (joinBits (joinBits 0x65432100fe 2288 0xf5f34120f806f543210fe) 2332 (joinBits (joinBits (joinBits 0xf0142345f1 264 0xf6534210fe) 528 0xf6534210ee056f34120fd00000000000010f42345f1000000000000f65342106e056f34120fd) 1232 (joinBits (joinBits 0x201f3546ec056f34120fd0f6534210fe00000000000010f42345f1 176 0x10ff2345e30f6534210fe) 748 (joinBits 0xf65342101e0f65342100e0f6534210ee 264 0x201f35464c056f341200d010ff2345e30f6534210fe))))) 9944 (joinBits (joinBits (joinBits (joinBits 0x564231f06a0564231f0fa0f102f435e2 1140 0x34501f2fe) 796 (joinBits (joinBits 0x564231f0fa 132 0xf65342101e) 484 (joinBits 0x45f23f10e60564231f0fa 176 0x10ff2345e3))) 2596 (joinBits (joinBits 0x10ff2345e30f65342106e000000000000f65342100e00000000000045f23f10e600000000000f0142345ff1 484 0xf0142345f01f0142345f01) 1364 (joinBits (joinBits 0xf0142345f01f0142345ff1f01423451f1 352 0xf5f341200f800000000000f0142345f11) 616 (joinBits (joinBits 0x564231f0f5a 220 0xf6534210e1e) 264 0x10f42345f01)))) 5016 (joinBits (joinBits (joinBits 0x10f42345f01 924 (joinBits (joinBits 0x45f231f05f6 176 0x6f54321011e) 176 0x564231f06fa564231f06fa)) 1188 (joinBits 0x6f54321011e 836 (joinBits 0x6f5432100e 352 (joinBits 0xf102f435e32 132 0x4f521f30e36)))) 2596 (joinBits (joinBits (joinBits 0xf5f341200f856f341200fd10f423455f1 176 0x56f341200fd) 440 0xf5f341200f80000000000010ff23455e3) 1364 (joinBits 0xf5f341200f8 1232 0xf0142345f11f0142345ff100000000000f0142345ff1)))))) 44 i
def t11 := table 8 2 547 34 0x3f9014760fec051d83fb814604fedc51413fb414604fecc50413fb614104fd4091d83f7024760fde091853f7724514fdd091853f7324104fdd090413ed030104fb40d1d83ef034760fbc0c0413ed034100fbc0d0403dd044100f74111d83dd040604f7c111d83df040604f7c1104037d064100df4191d837f064760dfe1919537f644654dfd8d14537f634504dfd9114137f624504dfc190402fd074100bfe1d1952ff754764bfdcd1852ff764614bfdcd1812ff754604bfdd11812ff724604bfc1d0403fd070514ff4101453fd030514ff40d1453fd070104ff4181853fd050614ff4101853fd034614ff40c1853fd060104ff4110413fd040104ff40d0413fd030104ff41c0403fd060100ff4100403fd030100ff4041853fd074100ff4041453fd064100ff4151853fd044514ff4111853fd034764ff40c1d93fd030760ff40d1d83fd034654ff40c1953fd030604ff40c1413fd044100ff4181d93fd044764ff4101d93fd020764ff4041d93fd060760ff4101d83fd080610ff4201803fd044760ff4201853fd024760ff4211853fd084654ff4191d83fd080654ff4151953fd050654ff4111953fd040654ff41d1453fd020654ff4041953fd034604ff4211813fd014760ff4201813fd060604ff4151813fd050604ff4111813fd074104ff4081813fd040604ffd0d1d93ff430764ffc0d1d93ff030764ffdcd1d93ff730764ffd8c1d93ff634764ffcc81d93ff310764ffc181d93ff044764ffc101d93ff020764ffc041d93ff024764ffc191d93ff014764ffcc91d93ff314764ffd0d1d83ff430760ffc0c1d83ff034760ffdcd1d83ff730760ffd8c1d83ff634760ffcc81d83ff310760ffc181d83ff040760ffc081d83ff010760ffc111d83ff024760ffc191d83ff014760ffcc91d83ff314760ffe1d1d83ff434654ffd0c1953ff034654ffc0c1953ff834654ffe0c1953ff734654ffdcc1953ff630654ffd8d1953ff534654ffd4c1953ff320654ffcc41953ff084654ffc201953ff054654ffc141953ff044654ffc101953ff024654ffc081953ff010654ffcc91953ff314654ffe1d1953ff870654ffe191953ff860654ffe151953ff850654ffe111953ff840654ffdd81d93ff760760ffdd81953ff754764ffdd51d83ff754654ffdd41d93ff750760ffdd41953ff744764ffdd11d83ff744654ffdd01d93ff740760ffdd01953ff060614ffc141853ff040614ffc0d1853ff030614ffc041853ff054614ffd0d1853ff430614ffc111853ff834614ffe0c1853ff734614ffdcc1853ff630614ffd8d1853ff534614ffd4c1853ff320614ffcc41853ff080614ffc211853ff064614ffc051853ff324614ffcc51853ff874614ffe1c1853ff864614ffe181853ff854614ffe141853ff844614ffe101853ff824614ffdd91853ff760614ffdd51853ff750614ffdd11853ff740614ffe1d1843ff870610ffe191843ff824610ffdd91843ff724610ffe1d1803ff870600ffe191803ff824600ffdd91803ff724600ffd941953ff650614ffd901d93ff640760ffd901953ff640614ffd881d93ff620760ffd881953ff620614ffe051803ff434604ffd0c1813ff030604ffe0d1813ff830604ffdcd1813ff730604ffd8c1813ff634604ffd4d1813ff530604ffcc81813ff310604ffc0d1813ff084604ffc201813ff060604ffc151813ff050604ffc111813ff024604ffc081813ff040604ffcc91813ff314604ffe1d1813ff870604ffe191813ff860604ffe151813ff850604ffe111813ff840604ffe091813ff820604ffdd91813ff760604ffdd51813ff750604ffdd11813ff740604ffdc91813ff720604ffdc51803ff650604ffd901813ff620604ffe051813fd034504ffc051953ff064604ff41d1413fd070504ff4111413fd040504ff4190413fd020504ffd951953ff654614ffd951813ff644764ffd911d83ff644654ffd911853ff644604ffc1c1453ff040514ffc0c1453ff034514ffc041453ff434514ffd0c1453ff044514ffdcd1453ff730514ffd8c1453ff634514ffcc81453ff310514ffc1d1453ff324514ffcc51453ff874514ffe1c1453ff764514ffdd81453ff754514ffdd41453ff744514ffdd01453ff724514ffdc81453ff710514ffd901453ff620514ffdc51453ff014514ffd911453ff434504ffd0c1413ff734504ffdcc1413ff630504ffc0c1413ff634504ffcc81413ff310504ffcc91413ff314504ffe1d1413ff870504ffdd91413ff760504ffdd51413ff750504ffdd11413ff740504ffdc91413ff720504ffdc41413ff640504ffd881413ff714504ffc0d1413ff074504ffc1c1413ff044504ffc101413ff024504ffc081413ff644504ffd891413ff610764ffd841d83ff610654ffd841853ff610604ffd841453ff610504ffd511d93ff544760ffd511953ff544614ffd511813ff544514ffd511413ff540764ffd501d83ff540654ffd501853ff540604ffd501453ff540504ffd491953ff524614ffd491813ff520654ffd481853ff520604ffd451953ff514614ffd451813ff510654ffd441853ff510604ffd091d93ff424760ffd091953ff424614ffd091813ff424514ffd091413ff420764ffd081d83ff420654ffd081853ff420604ffd081453ff420504ffd051d93ff414760ffd051953ff414614ffd051813ff414514ffd051413ff410764ffd041d83ff410654ffd041853ff410604ffd041453ff410504ffc1c0413ff060104ffc110413ff040104ffc0d0413ff030104ffd0d0413ff430104ffdcd0413ff730104ffd8c0413ff634104ffcc80413ff310104ffc1d0413ff324104ffcc50413ff874104ffe1c0413ff764104ffdd80413ff754104ffdd40413ff744104ffdd00413ff724104ffdc80413ff710104ffd900413ff620104ffdc50413ff064104ffd910413ff624104ffd850413ff610104ffd510413ff540104ffd090413ff420104ffd050413ff410104ff40d0403ff070100ffc180403ff040100ffc0c0403ff074100ffc190403ff434100ffd0c0403ff734100ffdcc0403ff630100ffd8d0403ff320100ffcc40403ff044100ffcc90403ff314100ffe1d0403ff870100ffdd90403ff760100ffdd50403ff750100ffdd10403ff740100ffdc90403ff720100ffdc40403ff640100ffd880403ff714100ffd910403ff624100ffd850403ff610100ffd510403ff540100ffd090403ff420100ffd050403ff410100ffc850403ff034100 0x240014600480028ca30486010005914400480518ca010008180682805f28c7f5a0a31aca518c4b28fe0f810528c6318c63195652ffeb2b5a5f801f07d08297fff8c00fad08283e52946318c6318d652ffffffc632946318c6318d65948b294863914a318c6318c6840c7f821052fe1018c0d5ad082956b5a10842105294a52ad0518fe8294a318c631a1031fc0000c6068168414a002d08295adf89ad6b7ff6b508294a55ad6bf94a318c6318d0818c60fad082800518c0d02d082941f02d082940d6a0ab00fe007ca5ffd08414a52958518d852946318c63f8c6002d68414a017cab07ca528c6318c6318c005ad082941ff9560183e5280055ad6b5ad6b294a5294a5294a5295084210842108420a5294a5294a5294a5294a5294a5294a5297eb294632946318c63f8c6000168414a017cab07ca002ca5294a5189651884528c6318c6518c1f02d0829442095602880b294a529443 722 0x3fddc0ff917cfeb007fd0c4ff40f97e57b9fc316df85e1bf0421fdfee6fb517df615afebbeefd5986fa914ff47213e754efcba1ff965e7f1fdcfe35347c151ff7d275efa27fdd936fb8d36f7170fee11b3dafb47b484ef67153ecc797d911cfa8584f4bd3de9541bd193ffa2dfbf431d9e817d3ce8eaf9a610f2a857e4a077c834af90112f201bfe3c0cbc28bff81c80efc275df6ebfbb45d773d64ee5d2ddcb1ebb81ec76fbd5ec77a3d8c043b1602f61c56ebff23d5cb4fa958bf517d4ea148dd422dfa77b6f4e1c7e9a28fd33a7ba6606f45d77e78dd9cf1b9f9d00373816ce6e7cfcd19d799d60726985e484f5c876b38c9347120a3e1ef07c286338422c705b52e08d8fc0e4e77be9cef587cde939bbd03e778521eedfbddd81ffba236b7186aedc007db3649b4c22b6917e6d1103d8f1e9b1010b6189aebf8dfd7d6a3af421f5deccebb00bd72de7ab6e0352f956a4b5cd479a1a831bf4ff70e9f172d3dfe5a7824f4c624e97aebd1f861a2f89b4584c6840d5d073ada0b1233e84ae799ebcea4eb9cd89738b8fe71546ce13239c23af36cdae69a23cd2bbd96882b2b47ae566c4ca96a994412f26c3be40b36c7f3e98ed66b19f34e327a4c587e389bad3133a8e20373c3c6038734c30d9f5e19102c2cd1583012b04f12605ed8c0261d802f4eff44e5fe85fbf59cd7e7d62fc5bbdf8469be02e37b699af552ede9bf0bd023b7935eaf16bc5e2847bc4a1b73ed7ae6c47dccb01b83a69705496e07d35c01dab7b1cb6ed3e6da0855b2671b64cd36b2306d63115a7633b4890567a852cca3059573ab2ac2364343ac6ba658a9f0b14c0f617bc6c1528d79d88aee7ad5a06eab32add640fdac798d57ba66ae32fd56d61aabfa7545052a84a954fbc9a9e83153abaaa670654caaea92e19523a429ee34d3a123a6bb254d3e8298e7152ede9a5b5d94ad1c2904ebd1fc49a3dff3476cc68e74cd1c1a9a2d773453bde8a524d0f6b2a1c3b143512a850d8502792a03ac13dc632794d5cf168c9df5533a8a0674a79ce8e529caaf93801526e7244db3079a461534774667145cc864f98f18331c3866264fcc48489874ed2ecc0a5d6f64ba4da96fe3b2db1665b497cb65219684932cc58658d414b162a95160729ef9e528c2ca4828948d6b282f224f25ec9e31892bd91248d0245eacc8995490975920f046416da48287a8f20e11c9e8638fbe471eca8dc6791b77663652446bcba8d219f1a0d06317bd45f7468bd205174c622d30dc52da789783312c2a62005f434deb869a350d342e1a02ec32e7785a9650adae21531d42971484d56309748e0bd22c11c7481a3b102be46039b9c0711f8073f500a3fa00db83f9caf7f3026fe3689fc525bf7cbd7e846ef9f751f33b13e59d47c074af7f605ef592bdd4bb7b5e9cf543adea1133d169779ee2cf3a2d9e09ee3c101b781426f01365dfe42bbf74b779da2ef38a5d8d253aed68757470eab2a9d4e3cba269c73e496e7b585cf23339d229736b7ae5e9ddcad22b94ca37295fce4cdd9c6555b8c56270d970e092a1be4a6b7c75f6f65e8dd9e8db6f723692536d0c16da0a65b3d8236750b6bed68d6ccf9ad7f0b5ae046b2d84d45001a7c69b4eb4569a7fad21f19a34ecb46363681a28cdfd9d9bc87336f7b66d700cda8059ae39b32ec96552f6c9a0699036531b304624372c3b6c98628ab0b787605788bfa1ed7ed5dafc7735f4284be69297af23af1a7f5e2c9abb28a5756e92ea1fe5ce8b2b848c56ef84adceaa5b8238b6ad056bfc22d75205ad388b5733d6a340ad22395a2658b30b8d650e0ac943358bcbcb1245d61dc4ac0ba557ef58af7df55e24aab8aca56f648ad10095a0802b36745662eaaa9f4154ab6aa6e4054acf6a938ed5185ea9f8e953b424a4e5c54980aa90dfc51357ca263d54308ba85836508eaea08ce540644280ade50034e9fbce93eac427b5c14eefaa9dbecd3b6eaa769454e97b49cf93135abba64aec4c6eb297defd2f92125e3294bab36946a1928aa6250c5149da5a930051242672472dd48b09690a59d1f6cea3e86347d0c08f2aad1de8c238fa346c1a88cea991968c232a3f45a7488a77090e24521855b429be084aad50917021155242021683d4150579e9fea093fbca87f3538fe35a9f9ecb3f26187e3150f62ce1e9eb63ce52e79988cf04a31df2213ae5a075a0d4eab159d412a3a5e0a74a72ce71e89cdc5d39130271e9d0e3d069c5f5f386c3a70d254e13839c249c38476c7058a0e05229bdf2a37770a6d7260da6c59acc0b35229069efa4d21969a3fa9342770682894d031519d588338e9a661eccc97c298b0cb31513e61d06cbd3c59745e32e2c225c02f8b586c162e9d2c3b8a577f28aeee015cce12b8b9a56c8d0acfe215598a2a36b8541c50a7cc314e8dd29c8d252d214a5837949e00291de6521c98a2a71945475289b5a50d058a16509426812779c64ea6b49cf8f139c1f26ff304c9e30989de12a1fb2528da49ec54936c3924ef62482d0480be08f503914494226e0c44ac6c88fe4911d89221ff6442b2485603105c4d204f1e3cbd907954b0ef39c1db3503b0e647581f8e58481c957438d25870e040e0e7a1bcbb837236c6e3598d89af1adc12354b606a3948d30121a17c833f95866f878cba6119554c3263c86347a0c4b26189632309100610758bf8211716f22d99485a73d0b3a2f166c3e2c78c0585238aedbf15a2182b1ad051a338a3353138de22706dc4d48689a5581345282419a8460bb88771610e19821372c4209d0801730f8a661e8ac83cb7b8769b60e251c1bd35435a87865f2e0cba5c1536102a2840534290a447a11df3022fcc043f7708303e1043d4203a003ea0607c3ae0dbb8c1921582c13d056b62091f480fba1013b76026bd8049b7c055cf8048c9 0x1ba08903d804a0bb10f8338abc1cb0e5014c0180f301801009be15f038160c3b80940748860a0a161038930c20013b2e900bc22a1c00b103102c853c2cb93481726001059190aca5510d592341d011725702c02e40fc30403b42b661b0d003f494403f0450570b581b600e85e417a48b056836c05e51105301003cc03407d80f0934056020913492e54002392ecb1c1f70bb802c1b00372f681d407c5b905f050c3ca03102f883400847a0ec02581d611000f85f40ac4200bf06c441e1d4014877402415703f835c1804ec09f82d003c17a05990582c606c0f5068c3ae00207281681c24790b983f028e0fd0a407f09d42070470740a5c1bd28202fc43c1440fc04c834a05225501b08b218d06003e01785b50c500088e81c40d8030499a4370d680702ea0640c9015434c0240c3008c96e57b07a02f8be81e92e3035010c0ab0ff877c1de1e806c81cc3a01e525a168c9aa4da100873029e098234912031614500d05b80d459404007e81ee195105088441c1a80d4868840415805891b414840403405643c419301500d43c6164023802414e1a702d859413c1eb09e817003616f05980b88a20f0081877089404b01215f00f609d0fd85500ce09f30b07bc4080f10d082dc07a10707a82844281900c787809f411302481043e205b2e084f80580942590170b680e70a803e414e4212c08050acc1460f1966c10e0c70cd16bc02e1ae20708681bc11d0fe83202f005d2f8108c30a03602e80b0ba454b0e594d401a11904f87b816200f2929720b1001109982d409e21306a17b033804e269847014014e015102c8440dd0c0076c440069032905cad60e32cf02a00d420b08c03281961990e387a424860c05482788a00bd10486241181d602286740064c903b83041b81d30a5066c84e003030815c0501af29d07f833000f051148c04217f01702541c00330d9881805601009481d83781962230578c2e0a02db8690c1c5aa230057c96c10a00c05b009e426267015cc1a4a309105243644190b6847801c5210a9015038a1760ff166801021d048047c33e0d0094076435c1f304d133ca3402826b0498a0415603f0294b7611b0df886009861901f94ec3181272fa1048ad021c09e01ac0f012000081081b2597057823c21c10f01c87243480da2d58070ad8591027080482052b26283b82da49708580e01480130ad03c826e03a27201600d646502991888780a504982848c6462029078014c5e825910d489a12a231849832c155063073c00c0820f08054ace1de021142424e1aa097854c1384d0251901430806f09607c03aa0850a684b40e402d2fa88541c45d10a100b440a08109b038430e11608f139802815d10184301c41bd01d01301985c804882fc98e51f20001b800a5b803e876812417100a85800140c200894e8c1243b00b15a820c1fc01116081722152ac133c2b261f22188443ea53000613ec9fc0132b482e03ec0440e790e48f80ba2e1001c1121f32c8135436403209884b09781f209a0634bf217006885d025a50809c81982982120ad82d499a09c0e1879c2b814106110f4c441ce07a94e042010107f87900aa48808a0264a1a0830b0926013603b22f121013216227187f4b7c070070117807c07105602e81980260e68 13
def extra11 (i : Nat) := getWord (joinBits (joinBits (joinBits (joinBits (joinBits (joinBits 0x6f543210fe 176 0xf6534210fe) 748 0x564231f0fa000000000000564231f0fa) 1760 (joinBits (joinBits 0xf6534210fe0f6534210fe 264 0xf6534210fe) 704 (joinBits 0x201f3546ec000000000000f6534210fe 484 (joinBits 0xf6534210ee056f34120fd0f6534210fe 176 0xf6534210fe)))) 2772 (joinBits (joinBits 0x564231f0fa 836 0xf65342106fef65342106fe10ff2345ee3f01f23450e110ff2345ee3) 1672 0xf102f435ee2)) 4972 (joinBits (joinBits 0xf102f435ee2 2112 (joinBits 0x564231f06fa 660 0x6f5432101fe)) 2596 (joinBits (joinBits 0xf6534210f5e 308 0xf6534210f5ef6534210f1e) 1276 (joinBits 0xf6534210f0e 704 0x6f5432100fe)))) 11572 (joinBits (joinBits (joinBits (joinBits 0x6f5432100fe 792 (joinBits 0xf102f435ee2 132 0x6f543210fe)) 1184 (joinBits 0x45612f30eb0564231f0fa 1008 0x34501f2fee)) 2028 (joinBits (joinBits 0x56f341202fd 176 0x45312ff03e1) 1276 (joinBits 0x56f341200fd56f341200fd 264 0x56f341200fd))) 6732 (joinBits (joinBits (joinBits 0x564231f00fa 616 0x45f23f10ee6) 748 (joinBits 0x564231f00fa 176 0x45f23f10ee6)) 2376 (0xf0142345ff1 <<< 1056)))) 44 i
def t12 := table 8 1 36 21 0xff9927fcc83fec49ff620ffa907fd493fe421ff200ff90a7fc813feec9ff760ffb2a7fd943fec89ff640ffb1a7fd8c3fec29ff610ffb007fd4c3fea21ff604ffa9a7fd453fea09ff500ffa1a7fd0c3fe629ff310ff9827fcc03fe209ff100 0x2946318c6318c0002d082941ff95602800b294a529400 56 0xf8e82fe67f03c7232f23492dda211b6a4275b4d9694d80c722f38d60030c2b46177dac02a397cc78ae7817dc517cb65d27634512c6605578169a693954700128201fd031329b188d2a576e4b479491048901667104c2e1552d4001d77bd422e3ef19c7573b6dae9639c8ac1c3797b4962f42465e2c4eb82f156f25d2b1f7955c672a74c54d264e91df061a1bf227def0460088884cb0da7421615602808403de51 0x8c6222d010121b11980a8400b838440d0794416610b90c860f1004030190712024410814c0c15228500a5505044ac612614c8e0c0e02c085e0f8483a16010 9
def extra12 (i : Nat) := getWord (0x56f34120fdade68241fa <<< 584) 39 i
def t13 := table 8 0 1 8 0xff 0x0 0 0x0 0x0 1
def extra13 (i : Nat) := getWord 0x0 0 i
end OrbFitM0
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ MonoD0Data
namespace OrbFitM0
abbrev q8 (i : Nat) := FrontQ.testF rot t7 (fun j=>ms.getD j m1) FitRoots8403.all 8 t8 extra8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 12 := by decide +kernel
theorem ready8 : OrbitQ.Mono.all full 8 t8 := by
  have prev : OrbitQ.Mono.all full 7 t7:=by intro i;exact Fin.elim0 i
  apply FitOrbitQ.finish good_ch16x16 valid_full rot prev (fun j=>ms.getD j m1) FitRoots8403.all t8 extra8
  have g : SpanQ.Block q8 0 12 := b8a0
  intro i
  simpa only [q8,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testF rot t8 (fun j=>ms.getD j m1) FitRoots8403.all 9 t9 extra9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a32 : SpanQ.Block q9 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a48 : SpanQ.Block q9 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a64 : SpanQ.Block q9 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a80 : SpanQ.Block q9 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a96 : SpanQ.Block q9 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a112 : SpanQ.Block q9 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a128 : SpanQ.Block q9 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a144 : SpanQ.Block q9 144 12 := by decide +kernel
theorem ready9 : OrbitQ.Mono.all full 9 t9 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready8 (fun j=>ms.getD j m1) FitRoots8403.all t9 extra9
  have g : SpanQ.Block q9 0 156 := (SpanQ.glue (SpanQ.glue (SpanQ.glue b9a0 b9a16) (SpanQ.glue b9a32 (SpanQ.glue b9a48 b9a64))) (SpanQ.glue (SpanQ.glue b9a80 b9a96) (SpanQ.glue b9a112 (SpanQ.glue b9a128 b9a144))))
  intro i
  simpa only [q9,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testF rot t9 (fun j=>ms.getD j m1) FitRoots8403.all 10 t10 extra10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a16 : SpanQ.Block q10 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a32 : SpanQ.Block q10 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a48 : SpanQ.Block q10 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a64 : SpanQ.Block q10 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a80 : SpanQ.Block q10 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a96 : SpanQ.Block q10 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a112 : SpanQ.Block q10 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a128 : SpanQ.Block q10 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a144 : SpanQ.Block q10 144 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a160 : SpanQ.Block q10 160 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a176 : SpanQ.Block q10 176 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a192 : SpanQ.Block q10 192 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a208 : SpanQ.Block q10 208 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a224 : SpanQ.Block q10 224 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a240 : SpanQ.Block q10 240 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a256 : SpanQ.Block q10 256 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a272 : SpanQ.Block q10 272 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a288 : SpanQ.Block q10 288 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a304 : SpanQ.Block q10 304 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a320 : SpanQ.Block q10 320 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a336 : SpanQ.Block q10 336 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a352 : SpanQ.Block q10 352 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a368 : SpanQ.Block q10 368 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a384 : SpanQ.Block q10 384 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a400 : SpanQ.Block q10 400 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a416 : SpanQ.Block q10 416 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a432 : SpanQ.Block q10 432 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a448 : SpanQ.Block q10 448 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a464 : SpanQ.Block q10 464 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a480 : SpanQ.Block q10 480 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a496 : SpanQ.Block q10 496 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a512 : SpanQ.Block q10 512 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a528 : SpanQ.Block q10 528 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a544 : SpanQ.Block q10 544 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a560 : SpanQ.Block q10 560 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a576 : SpanQ.Block q10 576 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a592 : SpanQ.Block q10 592 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a608 : SpanQ.Block q10 608 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a624 : SpanQ.Block q10 624 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a640 : SpanQ.Block q10 640 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a656 : SpanQ.Block q10 656 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a672 : SpanQ.Block q10 672 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a688 : SpanQ.Block q10 688 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a704 : SpanQ.Block q10 704 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a720 : SpanQ.Block q10 720 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a736 : SpanQ.Block q10 736 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a752 : SpanQ.Block q10 752 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a768 : SpanQ.Block q10 768 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a784 : SpanQ.Block q10 784 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a800 : SpanQ.Block q10 800 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a816 : SpanQ.Block q10 816 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a832 : SpanQ.Block q10 832 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a848 : SpanQ.Block q10 848 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a864 : SpanQ.Block q10 864 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a880 : SpanQ.Block q10 880 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a896 : SpanQ.Block q10 896 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a912 : SpanQ.Block q10 912 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a928 : SpanQ.Block q10 928 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a944 : SpanQ.Block q10 944 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a960 : SpanQ.Block q10 960 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a976 : SpanQ.Block q10 976 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a992 : SpanQ.Block q10 992 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a1008 : SpanQ.Block q10 1008 7 := by decide +kernel
theorem ready10 : OrbitQ.Mono.all full 10 t10 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready9 (fun j=>ms.getD j m1) FitRoots8403.all t10 extra10
  have g : SpanQ.Block q10 0 1015 := (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a0 b10a16) (SpanQ.glue b10a32 b10a48)) (SpanQ.glue (SpanQ.glue b10a64 b10a80) (SpanQ.glue b10a96 b10a112))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a128 b10a144) (SpanQ.glue b10a160 b10a176)) (SpanQ.glue (SpanQ.glue b10a192 b10a208) (SpanQ.glue b10a224 b10a240)))) (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a256 b10a272) (SpanQ.glue b10a288 b10a304)) (SpanQ.glue (SpanQ.glue b10a320 b10a336) (SpanQ.glue b10a352 b10a368))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a384 b10a400) (SpanQ.glue b10a416 b10a432)) (SpanQ.glue (SpanQ.glue b10a448 b10a464) (SpanQ.glue b10a480 b10a496))))) (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a512 b10a528) (SpanQ.glue b10a544 b10a560)) (SpanQ.glue (SpanQ.glue b10a576 b10a592) (SpanQ.glue b10a608 b10a624))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a640 b10a656) (SpanQ.glue b10a672 b10a688)) (SpanQ.glue (SpanQ.glue b10a704 b10a720) (SpanQ.glue b10a736 b10a752)))) (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a768 b10a784) (SpanQ.glue b10a800 b10a816)) (SpanQ.glue (SpanQ.glue b10a832 b10a848) (SpanQ.glue b10a864 b10a880))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a896 b10a912) (SpanQ.glue b10a928 b10a944)) (SpanQ.glue (SpanQ.glue b10a960 b10a976) (SpanQ.glue b10a992 b10a1008))))))
  intro i
  simpa only [q10,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q11 (i : Nat) := FrontQ.testF rot t10 (fun j=>ms.getD j m1) FitRoots8403.all 11 t11 extra11 i=true
set_option maxRecDepth 8192 in
theorem b11a0 : SpanQ.Block q11 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a16 : SpanQ.Block q11 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a32 : SpanQ.Block q11 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a48 : SpanQ.Block q11 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a64 : SpanQ.Block q11 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a80 : SpanQ.Block q11 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a96 : SpanQ.Block q11 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a112 : SpanQ.Block q11 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a128 : SpanQ.Block q11 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a144 : SpanQ.Block q11 144 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a160 : SpanQ.Block q11 160 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a176 : SpanQ.Block q11 176 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a192 : SpanQ.Block q11 192 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a208 : SpanQ.Block q11 208 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a224 : SpanQ.Block q11 224 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a240 : SpanQ.Block q11 240 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a256 : SpanQ.Block q11 256 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a272 : SpanQ.Block q11 272 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a288 : SpanQ.Block q11 288 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a304 : SpanQ.Block q11 304 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a320 : SpanQ.Block q11 320 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a336 : SpanQ.Block q11 336 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a352 : SpanQ.Block q11 352 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a368 : SpanQ.Block q11 368 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a384 : SpanQ.Block q11 384 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a400 : SpanQ.Block q11 400 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a416 : SpanQ.Block q11 416 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a432 : SpanQ.Block q11 432 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a448 : SpanQ.Block q11 448 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a464 : SpanQ.Block q11 464 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a480 : SpanQ.Block q11 480 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a496 : SpanQ.Block q11 496 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a512 : SpanQ.Block q11 512 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a528 : SpanQ.Block q11 528 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a544 : SpanQ.Block q11 544 3 := by decide +kernel
theorem ready11 : OrbitQ.Mono.all full 11 t11 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready10 (fun j=>ms.getD j m1) FitRoots8403.all t11 extra11
  have g : SpanQ.Block q11 0 547 := (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b11a0 b11a16) (SpanQ.glue b11a32 b11a48)) (SpanQ.glue (SpanQ.glue b11a64 b11a80) (SpanQ.glue b11a96 b11a112))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b11a128 b11a144) (SpanQ.glue b11a160 b11a176)) (SpanQ.glue (SpanQ.glue b11a192 b11a208) (SpanQ.glue b11a224 (SpanQ.glue b11a240 b11a256))))) (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b11a272 b11a288) (SpanQ.glue b11a304 b11a320)) (SpanQ.glue (SpanQ.glue b11a336 b11a352) (SpanQ.glue b11a368 (SpanQ.glue b11a384 b11a400)))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b11a416 b11a432) (SpanQ.glue b11a448 b11a464)) (SpanQ.glue (SpanQ.glue b11a480 b11a496) (SpanQ.glue b11a512 (SpanQ.glue b11a528 b11a544))))))
  intro i
  simpa only [q11,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q12 (i : Nat) := FrontQ.testF rot t11 (fun j=>ms.getD j m1) FitRoots8403.all 12 t12 extra12 i=true
set_option maxRecDepth 8192 in
theorem b12a0 : SpanQ.Block q12 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b12a16 : SpanQ.Block q12 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b12a32 : SpanQ.Block q12 32 4 := by decide +kernel
theorem ready12 : OrbitQ.Mono.all full 12 t12 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready11 (fun j=>ms.getD j m1) FitRoots8403.all t12 extra12
  have g : SpanQ.Block q12 0 36 := (SpanQ.glue b12a0 (SpanQ.glue b12a16 b12a32))
  intro i
  simpa only [q12,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q13 (i : Nat) := FrontQ.testF rot t12 (fun j=>ms.getD j m1) FitRoots8403.all 13 t13 extra13 i=true
set_option maxRecDepth 8192 in
theorem b13a0 : SpanQ.Block q13 0 1 := by decide +kernel
theorem ready13 : OrbitQ.Mono.all full 13 t13 := by
  apply FitOrbitQ.finish good_ch16x16 valid_full rot ready12 (fun j=>ms.getD j m1) FitRoots8403.all t13 extra13
  have g : SpanQ.Block q13 0 1 := b13a0
  intro i
  simpa only [q13,FrontQ.eqF,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : rejects 13 full := by
  have eq : MonoDeck8403.fromDesc full (t13.desc 0)=full := by decide +kernel
  have h:=ready13 ⟨0,by decide⟩
  change (MonoDeck8403.fromDesc full (t13.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbFitM0
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403 TableLeafQ QuickQ
namespace SoftS4
def full : List Sig := [(0x254a890120110b2fd0bc0f7abc654a890120110b2fd0bc0f7abc654a890120110b2fd0bc0f7abc654a890120110b2fd0bc0f7abc,0x38ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8ffdff8),(0x2cd9a4a090ca803d64ebddd1ca2cd9a4a090ca803d64ebddd1ca2cd9a4a090ca803d64ebddd1ca2cd9a4a090ca803d64ebddd1ca,0x3fb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bfb768bf),(0x1c38639482117a40dbcf60fcce1c38639482117a40dbcf60fcce1c38639482117a40dbcf60fcce1c38639482117a40dbcf60fcce,0x17ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57ee6b57),(0x3f81070758165879e31f8ef8803f81070758165879e31f8ef8803f81070758165879e31f8ef8803f81070758165879e31f8ef88,0x27d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7d6f2e7),(0x3ff80ff3f37d3339d21458d892fff80ff3f37d3339d21458d892fff80ff3f37d3339d21458d892fff80ff3f37d3339d21458d892,0x29004829004829004829004829004829004829004829004829004829004829004829004829004829004829004829004829004829),(0x3ffff003fcdb7a6784a304b6a8fffff003fcdb7a6784a304b6a8fffff003fcdb7a6784a304b6a8fffff003fcdb7a6784a304b6a8,0x14040154040154040154040154040154040154040154040154040154040154040154040154040154040154040154040154040154),(0x3ffffffc00d5c98e50c9eb600cfffffffc00d5c98e50c9eb600cfffffffc00d5c98e50c9eb600cfffffffc00d5c98e50c9eb600c,0x2021282021282021282021282021282021282021282021282021282021282021282021282021282021282021282021282021282)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needFull : necessary full:=needFrom (pn:=[(0,10),(4,3),(5,8),(1,0),(4,10),(3,17),(2,19)]) (by decide) (by decide +kernel)
lemma need5 : necessary Proof8403core5.st33:=needFrom (pn:=[(0,8),(4,12),(16,16),(0,1),(4,2),(16,4)]) (by decide) (by decide +kernel)
def raw5 : List Sig :=
  let w:=Proof8403core5.st33
  [one,w.getD 0 zero,neg (w.getD 1 zero),neg (w.getD 2 zero),neg (w.getD 3 zero),w.getD 4 zero,w.getD 5 zero]
def h5 := SmallHom8403.make 44 0x66653c62605e385b5957331f292a0d03532b50263013240e1110021b482d310c452827070512091d041a1c0b 20 0xc07091108040612030b050e0a1013150f141617
set_option maxRecDepth 8192 in
lemma image5 : full.map h5.fn=raw5 :=by decide +kernel
def m5 : Minor full := ⟨raw5,8,h5,image5,known Proof8403core5.e33 need5 (SmallHom8403.validImage h5 image5) (by decide +kernel)⟩
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
def raw6 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 0 zero,one,w.getD 1 zero,neg (w.getD 2 zero),w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h6 := SmallHom8403.make 48 0x3e6563625f5e5c5b5857551f3f2a1803522b4f264d13160e37101e1b173b2d470c44280f07391219221d2c0114250608 16 0x70111040212030b05000e1015140d17
set_option maxRecDepth 8192 in
lemma image6 : full.map h6.fn=raw6 :=by decide +kernel
def m6 : Minor full := ⟨raw6,9,h6,image6,known Proof8403core6.e21 need6 (SmallHom8403.validImage h6 image6) (by decide +kernel)⟩
def raw12 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 0 zero,w.getD 1 zero,one,neg (w.getD 2 zero),w.getD 4 zero,w.getD 3 zero,w.getD 5 zero]
def h12 := SmallHom8403.make 48 0x643c63625d385c5b51504f264c24160e5633551f360d18034a021e1b153431470c35270f07411a01210b2e190a200623 16 0x901110b000e08040602121315160d17
set_option maxRecDepth 8192 in
lemma image12 : full.map h12.fn=raw12 :=by decide +kernel
def m12 : Minor full := ⟨raw12,9,h12,image12,known Proof8403core6.e21 need6 (SmallHom8403.validImage h12 image12) (by decide +kernel)⟩
def raw20 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 0 zero,w.getD 1 zero,neg (w.getD 2 zero),one,w.getD 4 zero,w.getD 5 zero,w.getD 3 zero]
def h20 := SmallHom8403.make 48 0x61605f5e5d385c5b4645442835270f0754293f2a360d18034209221d0a4e304d134c24160e401c14210b2f1715320823 16 0x6021205000e0c070901110f14160d17
set_option maxRecDepth 8192 in
lemma image20 : full.map h20.fn=raw20 :=by decide +kernel
def m20 : Minor full := ⟨raw20,9,h20,image20,known Proof8403core6.e21 need6 (SmallHom8403.validImage h20 image20) (by decide +kernel)⟩
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
def raw36 : List Sig :=
  let w:=Proof8403core34.st3
  [w.getD 0 zero,w.getD 1 zero,neg (w.getD 2 zero),neg (w.getD 3 zero),zero,w.getD 4 zero,w.getD 5 zero]
def h36 := SmallHom8403.make 45 0x5a5958575633551f54293f2a360d18034b1137104a021e1b2f1715430539122e194209221d0a00252006320823 19 0xc0709011108040602120a1013150f14160d17
set_option maxRecDepth 8192 in
lemma image36 : full.map h36.fn=raw36 :=by decide +kernel
def m36 : Minor full := ⟨raw36,8,h36,image36,known Proof8403core34.e3 need34 (SmallHom8403.validImage h36 image36) (by decide +kernel)⟩
def raw68 : List Sig :=
  let w:=Proof8403core34.st3
  [w.getD 0 zero,neg (w.getD 2 zero),w.getD 1 zero,neg (w.getD 3 zero),w.getD 4 zero,zero,w.getD 5 zero]
def h68 := SmallHom8403.make 45 0x3a535150522b4f264e304c244d13160e4b114a0237101e1b2f15173d04411a2c01401c210b1400202506322308 19 0xc09070111030b05000e0a1310150f16140d17
set_option maxRecDepth 8192 in
lemma image68 : full.map h68.fn=raw68 :=by decide +kernel
def m68 : Minor full := ⟨raw68,8,h68,image68,known Proof8403core34.e3 need34 (SmallHom8403.validImage h68 image68) (by decide +kernel)⟩
def raw132 : List Sig :=
  let w:=Proof8403core34.st3
  [w.getD 0 zero,neg (w.getD 2 zero),neg (w.getD 3 zero),w.getD 1 zero,w.getD 4 zero,w.getD 5 zero,zero]
def h132 := SmallHom8403.make 45 0x494846453b2d442834313527470c0f07430542093912221d2e0a193d04401c2c14411a210b0100322508202306 19 0x80604021203050b000e0a0f10141316150d17
set_option maxRecDepth 8192 in
lemma image132 : full.map h132.fn=raw132 :=by decide +kernel
def m132 : Minor full := ⟨raw132,8,h132,image132,known Proof8403core34.e3 need34 (SmallHom8403.validImage h132 image132) (by decide +kernel)⟩
def ms : Array (Minor full) := #[m5,m6,m12,m20,m36,m68,m132]
end SoftS4
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ SoftS4
namespace OrbCut4
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x67666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 104))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x17161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 24))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x676665615f5e643c63625d5c5b5a595857543f56483b46454434473543423a534d51504f4b4a4041553e3d605249373839364c4e292030312e2f2b2c2d1f332624282527231e21322a221b1a1d1c1718190f0a010c10051216070d130b1502060e08110403091400 8 (i.val % 104))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x171614150f111210130e0d08050a060c04090b0703010200 8 (i.val % 24))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x67663c3e636261605d385f5c5b3a535150524f4e595658575554363f4b374948474645353d4039424c644365345a415e4a4d443b2b322d292f2c312e33243027281f202a08212225261e0b091b1201161518170a0d1a11020f03130c1d141c23070604050e101900 8 (i.val % 104))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x17141516100e11130f120d0c040a07030905060b08000102 8 (i.val % 24))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x6766603e5f5e643c5d38635c5b494846453b4434595458573f56365543393a534d51504c3d41374a35614b654e5a406242474f522d202b332e2c302f29273124262a321f06211e2528220b021d10140f0a1819150d1c050916030c131b011a230e08041107121700 8 (i.val % 104))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x17151416100e120f13110d08070a0403060b09050c000201 8 (i.val % 24))
def H3 := pairHom p3 n3
def p4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x67663c615d383e6563625f5c5b3a5351504e4c5248344645353b47443d405a59365857554b3742394f64436056494a5e414d3f543025292d2c2f332e31262b1f2a272028081e223224211b120b091516010f14190c02041a1807130d1d171006032311050e1c0a00 8 (i.val % 104))
def n4 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x171416150f110e1310120d03060a050c0b07040908010002 8 (i.val % 24))
def H4 := pairHom p4 n4
def p5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x676660645d383e655f5e635c5b4948464534353b534e51504c524d4f3d415a593658573f43394a3744614b3c543a4262404755563125332b2c2e292f30282d2a1f24322606221e2027211d100b020a0f141601171309041c180e0c0d1b19120803230511071a1500 8 (i.val % 104))
def n5 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1715161413120e0f10110d03090a0b08050407060c020001 8 (i.val % 24))
def H5 := pairHom p5 n5
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 3 zero,full.getD 2 zero,full.getD 4 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 5 zero,full.getD 4 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 0 zero,full.getD 2 zero,full.getD 3 zero,full.getD 1 zero,full.getD 5 zero,full.getD 6 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H4,by decide +kernel,by decide +kernel⟩
def raw4 := [full.getD 0 zero,full.getD 3 zero,full.getD 1 zero,full.getD 2 zero,full.getD 6 zero,full.getD 4 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot4 : Rot full := ⟨raw4,H4,H3,by decide +kernel,by decide +kernel⟩
def raw5 := [full.getD 0 zero,full.getD 3 zero,full.getD 2 zero,full.getD 1 zero,full.getD 6 zero,full.getD 5 zero,full.getD 4 zero]
set_option maxRecDepth 8192 in
def rot5 : Rot full := ⟨raw5,H5,H5,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else if i=2 then rot2 else if i=3 then rot3 else if i=4 then rot4 else if i=5 then rot5 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t6 := table 7 4 0 1 0x0 0x0 0 0x0 0x0 1
def t7 := table 7 3 1 43 0x7f874754544 0x0 1 0x4632c 0x0 0
def t8 := table 7 2 13 33 0x1fb61b40dfa811206fd40ad0377eea4a89bf754544dfa982a26fd4f5513fa0e2a89fd06b40dffb8daa27fdd91037fe822a89ff41f544 0x1008a018c0008084 20 0xd90613a47b6efe0b2dbf795b3654d590df2b0563cf818d95434b0dd6020e242baaf1672d60ed6ca1537451a1aaa94185fa4be4788d89a85cf45 0x1142558418603028e003a84a2421c040c32 7
def t9 := table 7 1 22 20 0xff41bff41dff411ff410ff541ff544ff540ff42bff420ff42dff421ff40bff400ff40dff401ff212ff21fff21bff101ff102ff10fff10b 0x42108c028c63184a00884210842 84 0xee1a6fdb07cba7ad8f4c4ece7bc69ceaa97863c17083fddf5bd7ba4ceb72a44ea02a8d3f5e3a236eb32175e477f0c7d7798cc85ae8c60d9c883b2a67762b9a2be7b6d6b881aa7145510f5a8d7d1d0ca68a10af141ae5275804cd19e599fd41331bc256e7a4a39388fd6271d6dbe2107d436ff381e89b028f3e038313f75f27cbb6aec4f15993cf32852c64c618c8cac5912cfafa7d55c6d16b3a3c966752ac98955918f6ac94954ed61a7b9114e6a649c09d11f8c2a3524e46662c810db8fc9e69da137399fa4717194d99ee1a266025ccbc47570c80de40ea0481a908825fbf83b04c06305d0be4701752d8286be0165af 0x818da01a5429316004890021708058685b983c5a10aa6b2b4c426a6d59831c92713a90698c75205d338b63a252721802659a7b380879443534a4619474ac0c6c5c4a8a6462129c48a88823734014285030320a78 8
def t10 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbCut4
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ SoftS4
namespace OrbCut4
abbrev q7 (i : Nat) := FrontQ.testS rot t6 m5 ms 7 t7 i=true
set_option maxRecDepth 8192 in
theorem b7a0 : SpanQ.Block q7 0 1 := by decide +kernel
theorem ready7 : OrbitQ.all full 7 t7 := by
  have prev : OrbitQ.all full 6 t6:=by intro i;exact Fin.elim0 i
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot prev m5 ms t7
  have g : SpanQ.Block q7 0 1 := b7a0
  intro i
  simpa only [q7,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q8 (i : Nat) := FrontQ.testS rot t7 m5 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 13 := by decide +kernel
theorem ready8 : OrbitQ.all full 8 t8 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready7 m5 ms t8
  have g : SpanQ.Block q8 0 13 := b8a0
  intro i
  simpa only [q8,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testS rot t8 m5 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 6 := by decide +kernel
theorem ready9 : OrbitQ.all full 9 t9 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready8 m5 ms t9
  have g : SpanQ.Block q9 0 22 := (SpanQ.glue b9a0 b9a16)
  intro i
  simpa only [q9,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testS rot t9 m5 ms 10 t10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 1 := by decide +kernel
theorem ready10 : OrbitQ.all full 10 t10 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready9 m5 ms t10
  have g : SpanQ.Block q10 0 1 := b10a0
  intro i
  simpa only [q10,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 10 full := by
  have eq : TableLeafQ.body full (t10.desc 0)=full := by decide +kernel
  have h:=ready10 ⟨0,by decide⟩
  change (TableLeafQ.body full (t10.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCut4
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403 TableLeafQ QuickQ
namespace SoftS32
def full : List Sig := [(0x3c2a9ddbbddffbfd5dce264043e154eeddeeffdfeaee7132021f0aa776ef77feff5773899010f8553bb77bbff7fabb9c4c8087c2,0x6000100c00020180004030000806000100c00020180004030000806000100c00020180004030000806000100c0002018000403),(0x1420d08120907e26f4d7a724fea10684090483f137a6bd3927f508342048241f89bd35e9c93fa841a1024120fc4de9af4e49fd42,0x16fbcf9adf79f35bef3e6b7de7cd6fbcf9adf79f35bef3e6b7de7cd6fbcf9adf79f35bef3e6b7de7cd6fbcf9adf79f35bef3e6b7),(0x2ce3c99311880809bf69cf4133671e4c988c40404dfb4e7a099b38f264c46202026fda73d04cd9c79326231010137ed39e8266ce,0x297efaf52fdf5ea5fbebd4bf7d7a97efaf52fdf5ea5fbebd4bf7d7a97efaf52fdf5ea5fbebd4bf7d7a97efaf52fdf5ea5fbebd4b),(0x3b603870f804a9516e1424ddf3db01c387c0254a8b70a126ef9ed80e1c3e012a545b8509377cf6c070e1f00952a2dc2849bbe7b6,0x337f9c3e6ff387cdfe70f9bfce1f37f9c3e6ff387cdfe70f9bfce1f37f9c3e6ff387cdfe70f9bfce1f37f9c3e6ff387cdfe70f9b),(0x3dc007f0087da0a291aab6eae1ee003f8043ed05148d55b7570f7001fc021f6828a46aadbab87b800fe010fb414523556dd5c3dc,0x2f7f631defec63bdfd8c77bfb18ef7f631defec63bdfd8c77bfb18ef7f631defec63bdfd8c77bfb18ef7f631defec63bdfd8c77b),(0x1aeffff007fc6f33f2308d28a4d77fff803fe3799f9184694526bbfffc01ff1bccfc8c234a2935dfffe00ff8de67e4611a5149ae,0x3042082e084105c10820b8210417042082e084105c10820b8210417042082e084105c10820b8210417042082e084105c10820b82),(0x254ffffff8007da2a63b6407b92a7fffffc003ed1531db203dc953fffffe001f68a98ed901ee4a9ffffff000fb454c76c80f7254,0xf280201e500403ca00807940100f280201e500403ca00807940100f280201e500403ca00807940100f280201e500403ca008079)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needFull : necessary full:=needFrom (pn:=[(1,17),(0,2),(0,12),(3,8),(1,1),(2,3),(2,8)]) (by decide) (by decide +kernel)
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
def raw34 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),one,w.getD 1 zero,neg (w.getD 2 zero),neg (w.getD 3 zero),w.getD 4 zero,w.getD 5 zero]
def h34 := SmallHom8403.make 45 0x3f3b605f5d253c2e363258303e101b0e3d0c51214e132b0d22061e3a0b48192f0145162d20083327230a281a0f 19 0x50f0400190711090117020d10150e14160a1a
set_option maxRecDepth 8192 in
lemma image34 : full.map h34.fn=raw34 :=by decide +kernel
def m34 : Minor full := ⟨raw34,8,h34,image34,known Proof8403core34.e3 need34 (SmallHom8403.validImage h34 image34) (by decide +kernel)⟩
def raw36 : List Sig :=
  let w:=Proof8403core34.st3
  [neg (w.getD 0 zero),w.getD 1 zero,one,neg (w.getD 2 zero),neg (w.getD 3 zero),w.getD 4 zero,w.getD 5 zero]
def h36 := SmallHom8403.make 45 0x6261605f5c2a3c2e5926583055021b0e521f51214d112b0d240609491c4819310144032d200734272c0a291a17 19 0x60f0300190b110801170c0d12151314180a1a
set_option maxRecDepth 8192 in
lemma image36 : full.map h36.fn=raw36 :=by decide +kernel
def m36 : Minor full := ⟨raw36,8,h36,image36,known Proof8403core34.e3 need34 (SmallHom8403.validImage h36 image36) (by decide +kernel)⟩
lemma need10 : necessary Proof8403core10.st0:=needFrom (pn:=[(0,2),(0,1),(1,1),(9,10),(9,5),(18,3)]) (by decide) (by decide +kernel)
def raw40 : List Sig :=
  let w:=Proof8403core10.st0
  [w.getD 5 zero,neg (w.getD 3 zero),neg (w.getD 4 zero),one,neg (w.getD 2 zero),neg (w.getD 1 zero),neg (w.getD 0 zero)]
def h40 := SmallHom8403.make 46 0x3935503757434c405d2f4e233e081e0f5c314d2c550709173c012b0a1b5e054f15561404182513102a11022e0d0e 18 0x1000a07100904160b12080318111517191a
set_option maxRecDepth 8192 in
lemma image40 : full.map h40.fn=raw40 :=by decide +kernel
def m40 : Minor full := ⟨raw40,8,h40,image40,known Proof8403core10.e0 need10 (SmallHom8403.validImage h40 image40) (by decide +kernel)⟩
def raw48 : List Sig :=
  let w:=Proof8403core10.st0
  [w.getD 5 zero,neg (w.getD 3 zero),neg (w.getD 4 zero),neg (w.getD 2 zero),one,neg (w.getD 0 zero),neg (w.getD 1 zero)]
def h48 := SmallHom8403.make 46 0x5b384741574c4340362245283e1e080f592444295509071758062d1a1b5a12461d5604141832161026030230200e 18 0x10a050e04091606130308180f1419171a
set_option maxRecDepth 8192 in
lemma image48 : full.map h48.fn=raw48 :=by decide +kernel
def m48 : Minor full := ⟨raw48,8,h48,image48,known Proof8403core10.e0 need10 (SmallHom8403.validImage h48 image48) (by decide +kernel)⟩
def ms : Array (Minor full) := #[m34,m36,m40,m48]
end SoftS32
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ SoftS32
namespace OrbCut32
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x64636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 101))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 27))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x64636261605f5a3659395e5c3c5756554b4a4948474645444354535251504f4e4d4c4237403f3e3a583b3d5b35415d38343325242e22302b292d262c23272a3231282f190d1c08151f1b0a211817131d04160503100f0e200b0c1a071e0901121411020600 8 (i.val % 101))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1a17181916141512130f0e11100d0c060a0403050b070908020001 8 (i.val % 27))
def H1 := pairHom p1 n1
def p2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x64633f3b605f5e5c5d5b5a365857563e54533d51504f4d4e4c4b4a3a4847464445434241406255523c614939383759353334262f30312e2d232b25282927322a222c2421200c091d0b1b1a19180f03151411121302170e0d1f1c0a1e070806050416100100 8 (i.val % 101))
def n2 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1a1916171815140e1011120f130d02070a08090b050603040c0100 8 (i.val % 27))
def H2 := pairHom p2 n2
def p3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x64633f3b605f5a5936395e5d3c57563e4b4a3a48474644454354533d51504f4d4e4c4237406255495861525b35415c3833342a222e24302b282d32232c2725262f2931190d0b07150c1b0a21180f111d0403051602170e201c1f1a08091e01121413100600 8 (i.val % 101))
def n3 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x1a171619181415100e0f1311120d02050a030406070b08090c0001 8 (i.val % 27))
def H3 := pairHom p3 n3
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 4 zero,full.getD 3 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def raw2 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot2 : Rot full := ⟨raw2,H2,H2,by decide +kernel,by decide +kernel⟩
def raw3 := [full.getD 0 zero,full.getD 2 zero,full.getD 1 zero,full.getD 4 zero,full.getD 3 zero,full.getD 6 zero,full.getD 5 zero]
set_option maxRecDepth 8192 in
def rot3 : Rot full := ⟨raw3,H3,H3,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else if i=2 then rot2 else if i=3 then rot3 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t7 := table 7 2 0 1 0x0 0x0 0 0x0 0x0 1
def t8 := table 7 1 5 20 0xff31fff300ff30eff100ff10e 0x118c21 12 0xe263e9bb55db749bc6017cbbe501d54a02239da8c4a9417a68f0c4466159d6a869dc7 0x2121846280242364a 6
def t9 := table 7 0 1 7 0x7f 0x0 0 0x0 0x0 1
end OrbCut32
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ SoftS32
namespace OrbCut32
abbrev q8 (i : Nat) := FrontQ.testS rot t7 m34 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 5 := by decide +kernel
theorem ready8 : OrbitQ.all full 8 t8 := by
  have prev : OrbitQ.all full 7 t7:=by intro i;exact Fin.elim0 i
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot prev m34 ms t8
  have g : SpanQ.Block q8 0 5 := b8a0
  intro i
  simpa only [q8,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testS rot t8 m34 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 1 := by decide +kernel
theorem ready9 : OrbitQ.all full 9 t9 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready8 m34 ms t9
  have g : SpanQ.Block q9 0 1 := b9a0
  intro i
  simpa only [q9,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 9 full := by
  have eq : TableLeafQ.body full (t9.desc 0)=full := by decide +kernel
  have h:=ready9 ⟨0,by decide⟩
  change (TableLeafQ.body full (t9.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbCut32
end
section
open Basis1868 Free1868 Cuts1868 Exact8403 Leaf8403 TableLeafQ QuickQ
namespace FullSignedR8403
def full : List Sig := [(0x15554a8a24aa925080a90aa880822040093fffd7e8f57b1e655555555554a8a24aa925080a90aa880822040093fffd7e8f57b1e6,0x3eff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8fffffeff8),(0x333326591266490a5464a6645450920a0cdd2ddb5f4edda1c333333333326591266490a5464a6645450920a0cdd2ddb5f4edda1c,0x3fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87ff7d7fe87),(0x30f0e1c771e1c739cfe39e1dcdce76d95ccca396c1891a2b4f0f0f0f0f0e1c771e1c739cfe39e1dcdce76d95ccca396c1891a2b4,0x22e80207522e80207522e80207522e80207522e80207522e80207522e80207522e80207522e80207522e80207522e80207522e80),(0xff01f87e01f83e0dfc1fe1f1f7871e6e5b8587b46420926ff00ff00ff01f87e01f83e0dfc1fe1f1f7871e6e5b8587b46420926,0x260b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0485a660b0),(0xfffe007ffe003ff1ffe001fe07f81f80fd31c9e060c61c0ffff0000fffe007ffe003ff1ffe001fe07f81f80fd31c9e060c61c0,0x382188831f82188831f82188831f82188831f82188831f82188831f82188831f82188831f82188831f82188831f82188831f8218),(0x3f0000007fffffc001fffffe0007ffe00179d4505a008911effffffff0000007fffffc001fffffe0007ffe00179d4505a008911e,0x36004040576004040576004040576004040576004040576004040576004040576004040576004040576004040576004040576004),(0x3fffffff8000000001fffffffff80000092708fb689e30088ffffffffffffff8000000001fffffffff80000092708fb689e30088,0x8a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a020008a4a),(0x3ffffffffffffffffe000000000000000a1e2f00037259c64fffffffffffffffffffffffe000000000000000a1e2f00037259c64,0x5a10108005a10108005a10108005a10108005a10108005a10108005a10108005a10108005a10108005a10108005a10108005a1)]
lemma valid_full : ∀a∈full,Valid a := by
  have h : full.all (fun a=>decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha
  have p:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
lemma needFull : necessary full:=needFrom (pn:=[(0,27),(0,12),(4,2),(11,0),(6,8),(1,21),(3,2),(2,13)]) (by decide) (by decide +kernel)
def raw4 : List Sig :=
  let w:=SoftS4.full
  [w.getD 0 zero,w.getD 1 zero,zero,neg (w.getD 2 zero),neg (w.getD 3 zero),w.getD 4 zero,w.getD 5 zero,w.getD 6 zero]
def h4 := SmallHom8403.make 104 0xd7d6d4cfcdccc7c6c5c4bfbdbcb7b6b5b4b0aea99e9d989796918f8b86817877716c6b6a61594f4ca8d554ce769f60be85a36572af4139903d5d345338a735693c95458a00584943ad801601123027150b1d0a202e24191a030c182a3229111e1f0e21082f061346 24 0x201b2322131d1c1f151e0c051004080317060e0f12010002
set_option maxRecDepth 8192 in
lemma image4 : full.map h4.fn=raw4 :=by decide +kernel
def m4 : Minor full := ⟨raw4,11,h4,image4,known OrbCut4.bound SoftS4.needFull (SmallHom8403.validImage h4 image4) (by decide +kernel)⟩
lemma need6 : necessary Proof8403core6.st21:=needFrom (pn:=[(0,2),(0,1),(1,1),(11,10),(6,2),(20,3)]) (by decide) (by decide +kernel)
def raw6 : List Sig :=
  let w:=Proof8403core6.st21
  [w.getD 0 zero,one,zero,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h6 := SmallHom8403.make 48 0xd5d4cdccc5c4bdbcb5b4aeada8a7152f9d3896958f2e1d0c851a80120b7634712a6a69031f6024275816531320450e1e 16 0x17001c0f011d12100e021e1f23220c20
set_option maxRecDepth 8192 in
lemma image6 : full.map h6.fn=raw6 :=by decide +kernel
def m6 : Minor full := ⟨raw6,9,h6,image6,known Proof8403core6.e21 need6 (SmallHom8403.validImage h6 image6) (by decide +kernel)⟩
lemma need9 : necessary Proof8403core9.st9:=needFrom (pn:=[(0,2),(0,1),(17,16),(2,1),(8,6),(17,3)]) (by decide) (by decide +kernel)
def raw17 : List Sig :=
  let w:=Proof8403core9.st9
  [one,w.getD 0 zero,neg (w.getD 1 zero),w.getD 2 zero,zero,w.getD 3 zero,w.getD 5 zero,w.getD 4 zero]
def h17 := SmallHom8403.make 45 0xcac8c6c4c2c0bebcab3f35a7a510182f6f6d6b6967283c1f5b2511161b9302902e8d0f8a0c052d33014a322614 19 0xb061d0705170a081c0d0e161e1a1522211b20
set_option maxRecDepth 8192 in
lemma image17 : full.map h17.fn=raw17 :=by decide +kernel
def m17 : Minor full := ⟨raw17,8,h17,image17,known Proof8403core9.e9 need9 (SmallHom8403.validImage h17 image17) (by decide +kernel)⟩
lemma need24 : necessary Proof8403six.st281:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,2),(13,4),(25,4)]) (by decide) (by decide +kernel)
def raw24 : List Sig :=
  let w:=Proof8403six.st281
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,zero,zero,w.getD 3 zero,w.getD 4 zero,w.getD 5 zero]
def h24 := SmallHom8403.make 49 0xc3c2c1c0bfbebdbca6a5a410a318152f8e8d8c0f8b8a1d0c7d2d1c0a68676628653c031f571b17294b4a04493240140900 15 0xa08001c0b06011d16021e211b0c20
set_option maxRecDepth 8192 in
lemma image24 : full.map h24.fn=raw24 :=by decide +kernel
def m24 : Minor full := ⟨raw24,10,h24,image24,known Proof8403six.e281 need24 (SmallHom8403.validImage h24 image24) (by decide +kernel)⟩
def raw32 : List Sig :=
  let w:=SoftS32.full
  [neg (w.getD 0 zero),w.getD 1 zero,neg (w.getD 2 zero),neg (w.getD 3 zero),neg (w.getD 4 zero),zero,w.getD 5 zero,w.getD 6 zero]
def h32 := SmallHom8403.make 101 0xbbbab7b6b5b4b2b1b0acaba9a8a6a5a389888685848382817d646361605c5b5a5957484240b9a487aeb862b37f44aa5f46473f5da75ead584380af413e4535363d3b7e1a16191c2621151e241400250d1b31050610092f122c2b0e0a17290b072d11182723 27 0x201c1b1d21232215130f19171a1f04030c0b060905070a08180100
set_option maxRecDepth 8192 in
lemma image32 : full.map h32.fn=raw32 :=by decide +kernel
def m32 : Minor full := ⟨raw32,10,h32,image32,known OrbCut32.bound SoftS32.needFull (SmallHom8403.validImage h32 image32) (by decide +kernel)⟩
lemma need34 : necessary Proof8403core34.st3:=needFrom (pn:=[(0,2),(0,1),(1,1),(3,1),(8,3),(21,5)]) (by decide) (by decide +kernel)
def raw34 : List Sig :=
  let w:=Proof8403core34.st3
  [w.getD 0 zero,one,neg (w.getD 1 zero),w.getD 2 zero,w.getD 3 zero,zero,w.getD 4 zero,w.getD 5 zero]
def h34 := SmallHom8403.make 45 0xb9b8b5b4b136aeadaa3fa8a7a410152f872c851a823180127e0b1c622b60245e275a2558161747453b0e3e1e09 19 0x7170a001c090f0b011d181f19231a22210c20
set_option maxRecDepth 8192 in
lemma image34 : full.map h34.fn=raw34 :=by decide +kernel
def m34 : Minor full := ⟨raw34,8,h34,image34,known Proof8403core34.e3 need34 (SmallHom8403.validImage h34 image34) (by decide +kernel)⟩
def raw72 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 4 zero),neg (w.getD 5 zero),w.getD 3 zero,zero,neg (w.getD 1 zero),w.getD 2 zero,zero,neg (w.getD 0 zero)]
def h72 := SmallHom8403.make 48 0x9c528e4b84447d40984f8b4981430a009b518d4a830d2d1497308a32069a508c04823b1c0996131d800e990f31950c12 16 0x13081b02000c1416190a21101e231c20
set_option maxRecDepth 8192 in
lemma image72 : full.map h72.fn=raw72 :=by decide +kernel
def m72 : Minor full := ⟨raw72,9,h72,image72,known Proof8403core6.e21 need6 (SmallHom8403.validImage h72 image72) (by decide +kernel)⟩
lemma need96 : necessary Proof8403core96.st13:=needFrom (pn:=[(0,2),(0,1),(1,1),(4,1),(9,1),(28,7)]) (by decide) (by decide +kernel)
def raw96 : List Sig :=
  let w:=Proof8403core96.st13
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 3 zero,w.getD 4 zero,zero,zero,w.getD 5 zero]
def h96 := SmallHom8403.make 44 0x8988872c8619851a84838231810680127f057e3d0b7d2d1c0a4823474645440d3b430e42263e411e40140900 20 0x705170a08001c18041f1913231a1522211b0c20
set_option maxRecDepth 8192 in
lemma image96 : full.map h96.fn=raw96 :=by decide +kernel
def m96 : Minor full := ⟨raw96,8,h96,image96,known Proof8403core96.e13 need96 (SmallHom8403.validImage h96 image96) (by decide +kernel)⟩
def raw144 : List Sig :=
  let w:=Proof8403core6.st21
  [neg (w.getD 4 zero),neg (w.getD 5 zero),w.getD 3 zero,neg (w.getD 1 zero),zero,w.getD 2 zero,neg (w.getD 0 zero),zero]
def h144 := SmallHom8403.make 48 0x704e684b5c4257406c4c6549594129006f33674a5b261b146b013c32116e4d66045a3e17096a2003581e6d2825691f16 16 0x15061b02010c0d161a0b210e1e221d20
set_option maxRecDepth 8192 in
lemma image144 : full.map h144.fn=raw144 :=by decide +kernel
def m144 : Minor full := ⟨raw144,9,h144,image144,known Proof8403core6.e21 need6 (SmallHom8403.validImage h144 image144) (by decide +kernel)⟩
def raw160 : List Sig :=
  let w:=Proof8403core96.st13
  [w.getD 0 zero,w.getD 1 zero,w.getD 2 zero,w.getD 4 zero,w.getD 3 zero,zero,w.getD 5 zero,zero]
def h160 := SmallHom8403.make 44 0x6463622b612160245c5b5a25591158165f075e5d27571b1729482347464542263e411e440d3b430e40140900 20 0x9030f0b06011d18041f1a1522191323211b0c20
set_option maxRecDepth 8192 in
lemma image160 : full.map h160.fn=raw160 :=by decide +kernel
def m160 : Minor full := ⟨raw160,8,h160,image160,known Proof8403core96.e13 need96 (SmallHom8403.validImage h160 image160) (by decide +kernel)⟩
def ms : Array (Minor full) := #[m4,m6,m17,m24,m32,m34,m72,m96,m144,m160]
end FullSignedR8403
end
section
open Basis1868 Free1868 Cuts1868 Moves3400 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 RotateQ OrbitQ FullSignedR8403
namespace OrbBoth0
def p0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 220))
def n0 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 8 (i.val % 36))
def H0 := pairHom p0 n0
def p1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0xdbdad9d8d7d6d5d4cbcac9c8c7c6c5c4d3d2d1d0cfcecdccc3c2c1c0bfbebdbcbbbab9b8b7b6b5b4acabaaa935a8a7b3b2b1b0aeada6a5a4a37c7b7a787776706f6e6d6c6b6a69757473723971686766653c64636261605c5b5a59585f5e57a2a1a0379f9e9d949392918f9c9b9a99989796958e8d8c8b89888786857f7e3d84838281807d565554534e334d4c52504f4b4a49484746454241444340363b5d8a3e3a9034793faf38513225012f2a1b2b2c2e0a0f0b0d311a230219130c0e03172d2421181c12151420160610281e261f27290908051107041d223000 8 (i.val % 220))
def n1 (i : Fin 414) := Fin.ofNat 414 (OrbitQ.getWord 0x222321201f1e1c1d1b191a180f16130d1512110e1710140c0a0b07060908030405020001 8 (i.val % 36))
def H1 := pairHom p1 n1
def raw0 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 3 zero,full.getD 4 zero,full.getD 5 zero,full.getD 6 zero,full.getD 7 zero]
set_option maxRecDepth 8192 in
def rot0 : Rot full := ⟨raw0,H0,H0,by decide +kernel,by decide +kernel⟩
def raw1 := [full.getD 0 zero,full.getD 1 zero,full.getD 2 zero,full.getD 4 zero,full.getD 3 zero,full.getD 5 zero,full.getD 7 zero,full.getD 6 zero]
set_option maxRecDepth 8192 in
def rot1 : Rot full := ⟨raw1,H1,H1,by decide +kernel,by decide +kernel⟩
def rot (i : Nat) := if i=1 then rot1 else rot0
lemma fixedRot (i : Nat) : SignFixed (rot i).J := by
  unfold rot
  repeat' split
  all_goals exact fixed _ _ (by decide +kernel)
def t7 := table 8 5 0 1 0x0 0x0 0 0x0 0x0 1
def t8 := table 8 4 7 60 0x5dfa9497462d10ff7106e01b72d50def107e01b82d60d1ff53d9848646541ff53b9848646541ffa949747641011ffa9497476410f 0x8400 7 0x1f0e7bb16c3cb9313e22d96432674c4abab08bb77 0x8620a10c00 6
def t9 := table 8 3 111 47 0x1f9d0b58b443ff3a15b16887fe762b62d10ffcec5ac5a21fbde0ad8b5437f880dc0eb06ff101b71d50dfe2036c3a21ffd40fdc6d437fbcc230e880ff762b764101feec5aec8203fdd0b61d043ffba15c3a087ff798461b10ffef308c3a21ffdd8ae1d043ffbb15bb2087ff762d87410ffeec5aec821ff3c52d8b443fe78a1316887eef74472d51ddde2f6e5aa3bbbe0f58b543777819316a86eef32286451dddf2e4c5a21fbbe5d18b443ef7c20b96a8edef82072d51dfd203705ac3bfa406dcb5477f480db16887fed03f71b51dfda044e5aa3bfb416d8b443ff682f316887fef43d87410ffde8770e821ffbdcee1d043ff7cc2316887fef86462d10ffdec7aec821ff6412c1f843fec82103f087fd904b06e10ffb20840dc21ff6dcf40ec43fed8a143a087fdb14276410ffb202207621ff7e6100ec43fef8a143a087fb905001b61df720bc036c3bee416c239837dc829047306fb901104b60df720b60fca1bee41481f9437dc82883a080fb9050074101f720b60fc21fee41481f843fddc9e825b06fbb92b04b60df77060096c1bef417806d877ddc10825b06fbd05271d51df76e56096c1a3fe6121919517fcc0c3228eaff98486451ddf20f611cc3bbe41c82398777c80db16a86ef9010864654df20230c8a3bbec5ae1914777d8b743228eeff42d864654dfe8570c8ca9bf41f9c6d4777d8cdb16a86efd07087450ddfee890e8a1bbfe6118b54377fa95c3228eeff52d86451ddff2e8ec8203bfe5d1d9043efc808bb230edf901b72d60dbf20210e8ca97fd0b61d1952ffa15c3a32a5fb18072d50bbff308ec82037fe1c61d043effcc23b2087bfb19082d60bff203705ac1bfe41d0049877fc809396a85ff907e01b61dff2036e5aa1bfec585d90407fd8b23b2080ffb13d874101 0x424200e528004204200108420021100a228027394a00108108804200200882108024000840100401003380e41812000047110810800508084000a22842701c090000001082 121 0x7dcaf9fa30c1f08fffdc64679cdd2f3359de22ebbc3e52775b11ebd039d30e2ba5f69f3a1e8e680b5be89df753a06e87a7d92143b21b775e6ea6aea01d5b25faa626b4f66b699c3dd134739e80933bdcee65677c872418e750719bbf608399bfba977ed2e2f28bfdcfadeb83ab57062c6df5ba5a8ca5b468f9689c42cf679d93327b1fef3633ce2b8ddcd56031a9c8f5531752a44e6d379b2a39b3b43233a85b9fcfb4fd9b0bb1360542578f9488da990b77b1f27663c0e44743318db89f16b78a23ba5c435b787f76f0dd2661752cc209f983fb4f062416085c5bdd8797b7488e46cadc293a38001a6be140d48c6da5fffb25c015a4682b2b5a55ce06a9dc6551274c9b89853605525998d49c73c89e02d11eff21235540e8bc7a7480f2fd11e576e3be6fa7531dcdc3a39b2ed9328a7856e508aaf6e93b7bd275c604778688bee48f9ca91e734c3c16fc68b798c59ac0b62c015756410d9001eda1 0x248b02f8b2168d8120380407e238aa2a07a328642b04e338d00b0521b8dc088b61981a2588a0482e27876330b4018c23189c1a802298b80a04a03016051302200825194208ba2187c1002a1b18866092690622803432072288ac6f0561500e1601c0f044130ae351503103a240841a09a0c8743000a350360506c108243485e20012518000608c080da098d6010600596a5703e078701e0 10
def t10 := table 8 2 521 34 0x3fb81b60bfedc4182ffb81b60dfee075837fb71060dfedc4582ffb71160dfedc6d42ffb71d50bfed84142ffb71b50dfedc75437fb61050dfed84542ffb61150dfed06d82ffb41b60dfed07582ffb41d60dfecc74407fb31b101fed86c407fb61d101fed46c407fb51d101fec848407fb31d10ffecc6c43ffb61b10ffed87443ffb51b10ffed47443ffb21210ffec86c407fb21b10ffde0ad877f782d61dfddc81877f772161dfdd8ad877f772b51dfddcb5477f762051dfdd885477f742b61dfdd0b5877f721251dfdc848407f732d10ffdccac43ff762b10ffdd8b443ff742b10ffdd0b443ff721110ffdc86c43fed03b10ffb40c843fef03b10ffbc0c843fdd04b60df74109837df04b60df7c1098377f862654dfe1919537f761654dfdd819537f641654dfd9119537f63451ddfd8c54777f86251ddfe1914777f62b51ddfd8854777f61051ddfd84142f7f63450ddfd8c54377f64150ddfd9114377f62050ddfd8b54377f61b50ddfd845436ff761764bfe1c9952ff874654bfdd89952ff760654bfdd45d92ff754764bfdc81952ff73161dbfdcd1876ff76161dbfdd91876ff72b61dbfdc85876ff71061dbfdc4182eff73160dbfdcd1836ff75160dbfdd51836ff74160dbfdd11836ff72060dbfdcb5836ff71b60dbfdc45835ff8727647fe1c1d93fd08061dff4209877fd06b61dff4141877fd05b61dff4179877fd05261dff4101877fd04b61dff4139877fd04261dff40c1877fd03b61dff40f9877fd03261dff4189877fd01b61dff420182ffd08260bff414182ffd05b60bff417982ffd05260bff410182ffd04b60bff413982ffd04260bff40c182ffd03b60bff40f982ffd03260bff408582ffd06060bff418982ffd08060dff4209837fd05060dff416d837fd05e60dff4149837fd04060dff4139837fd03060dff40ed837fd03e60dff40c9837fd02b60dff412d837fd04260dff422d837fd06260dff41b982ffd06060dff41ad837fd06061dff422d877fd08e60bff41c8407fd02b60bff41d0407fd070101ff4188407fd064101ff4180407fd042101ff4104407fd044101ff4100407fd032101ff40d0407fd030101ff4189d93fd042764ff4105d93fd044764ff4101d93fd032764ff40c5d93fd034764ff40c1d93fd02b764ff4081d93fd08e61dff4085d93fd08b60bff4041d93fd08e60dff4045d93fd082654ff4205953fd084654ff4201953fd052654ff4145953fd054654ff4141953fd042654ff4105953fd044654ff4101953fd032654ff40c5953fd034654ff40c1953fd02b654ff4081953fd021654ff4041953fd011654ff41c1477fd07b51dff41f9477fd07251dff4101477fd04251dff40c1477fd03251dff412d477fd04e51dff40ed477fd03e51dff406d477fd07050bff41ed42ffd07e50bff41c942ffd04050bff412d42ffd04e50bff410942ffd03050bff40c942ffd03b50bff40f942ffd02150bff40ad42ffd07050dff41ed437fd07e50dff41c9437fd04050dff412d437fd04e50dff4109437fd03050dff40c9437fd061764ff4181d93fd03b50dff40f9437fd02b50dff41c043ffd071101ff40bd82ffd02160dff41ec43ffd02260dff4049877fd07e10fff41c843ffd06010fff4184407fd02f50bff4085437fd06b10fff4089437fd01251dff41b843ffd06210fff410043ffd04b10fff413843ffd04210fff40c043ffd03e10fff40c4407fd071764ffd8c9d93ff432764ffd0d1d93ff320764ffccb5d93ff310764ffcc75d93ff634764ffcc85d93ff32b764ffcc45d93ff31b764ff41c5953fd061654ffd8c9953ff532654ffd4d1953ff432654ffd0d1953ff320654ffccb5953ff310654ffcc75953ff634654ffcc85953ff32b654ffcc45953ff31b654ff41ed877fd02261dffc0ed877ff03261dffc06d877ff01261dffe0c9877ff83461dffdcc5877ff73061dffd8c9877ff53261dffd4d1877ff43261dffd0d1877ff32061dffccb5877ff31061dffcc75877ff63461dffcc85877ff32b61dffcc45877ff31b61dffe0ad877ff82d61dffdc81877ff72161dffe0b582fff72060bff41ed837ff71061dffdc4182ffd01260dffe0d1837ff73160dffd8d1837ff82d60dffe06d837ff72060dff41f982fff71161dffdc45837fd01160bffd8add93ff62b654ffd8ad877fd06b51dff4089477ff73151dffdcd1477ff43151dffd0d1477ff31d51dffcc6d477ff87151dffe1d1477ff87051dffdd85477ff76451dffdd49477ff75151dffdd51477ff74251dffdd05477ff74451dffdd01477ff72051dffdcb5477ff71b51dffdc41477ff71d51dffdc45477ff64251dffd911477ff07050bffc1f942fff87150bffe1d142fff87050bffdd8942fff76150bffdd9142fff76050bffdd4542fff75450bffdd0542fff74450bffdc8142fff72d50bffdc4142fff71d50bffd90542fff64450bffd88142fff62d50bff41ad437ff61050bff4049437ff07b50dffc1c9437ff73150dffdcd1437ff63450dffd8c5437ff87150dffe1d1437ff87050dffdd89437ff76150dffdd91437ff76050dffdd45437ff75450dffdd05437ff74450dffdc81437ff72d50dffdc6d437ff71150dffd905437ff64450dffd881437ff62d50dffd86d437fd06e50bffd845437fd01150bffd505477ff54451dffd4ad953ff52b61dffd4b5953ff52d61dffd46d953ff51b61dffd475953ff51d61dffd0add93ff42b654ffd0ad877ff42051dffd0b5d93ff42d654ffd0b5877ff42d51dffd06dd93ff41b654ffd06d877ff41b51dffd041477ff41d764ffd075953ff41d61dffd075477ff41151dffe1c4407ff874101ffe1c0407ff762101ffdd84407ff764101ffdd80407ff751101ffdd50407ff741101ffdd10407ff720101ffdcb4407ff641101ffd910407ff620101ffd8b4407fd02210fffc849d93ff212654ffc849877fd01210fff40ec43ffd03210fffe1c443fff87410fffe1c043fff76210fffdd8443fff76410fffdd8043fff75110fffdd5043fff74110fffdd1043fff72010fffdcb443fff64110fffd91043fff62010fffd8b443ffd02d101ffc86dd93ff21b654ffc86d877fd01b101 0x33800739c602800529484210211808410420010821084038842014a4208410880420c40080202008501ca520425008a5284252140329ce0294843842700847384242108700ce73a52021084210840842128129210842108408421114a94908421081084222100501405000e201ca0290842042129084204210880010c000250049084210842042108902420e601c8408484084c7180e4210810842211c0039084204202842238c02000003946010006014842102109c210842108421084a5084210842108421084420840008421084210842108421084421080739ce70842019ce739c45114a1084210a407294842108420840380e529c6901ca529484210e038ca5294a5280e10842901ca529484210e019ca5294a52948421084210842108421084210842108421120394e02908420845214421084208520394e029084208452144210842 683 0x1febfe3fcd15ff7bd4fe1827fb4fa3f4c50fe8fd7facfb1f5608fea833fd34c8f9abe9f2f163e3e84fb81e2f6e9fbed07ffd5cfefa90c1f4b101e89b2fd0fb579f2c2f37319e6e41bcb28ef960a4f28513e48a73c7d79789a39f10169e05767bd702f77aa1ed4785da17e7b10c0f60d44ec0533d7f59baf7b1f5e6f2eb7af5d53de7aa688754028e9a6bfd3054ba5c2373fd94e7f205cf25af9d668737b40e6c47dccf12f98a137301c6e5fe3fcbc4bf95294f28247e4a7a1c94bf78e80f71b38ee363a7c65f7f8c1def13aa6e2604dc40f8f87e9df0e650e18f5bc166138233a701991e01439bf6eb37ed67efbb92deeb57bd4e2378d35eec0a0dd0677b7a3df6e64dedc2fadb7475b6314f69bbf6cff52d9c72bb1f9db62b80ebb18dd6bb0dad15f357164eabf53d57287aabbb754cfbea6451d4a4b5a5c78b4b85ce96929d2b17fa303c3446c4685565cf2fad9dc9073ad3fe7421dce49f39bf3a334fe5667640cc4043985eaf30affe5b915cb603f9606532bc4ae577caca1bab931b5725c8f64aab5c950d391eed32024863f7e3c76ebf8dfa8b1b1a5632630c613878b5f2f16303e21abfc36ae186843b0b153e1607bc25a0182c3cf0534de08824c0d435818e170187a602b83bfc2857f752efeabcdfcccebf7dbd7eb3cefb78edf5b2fbea7e37d41cafa3965f077bbe053b7b84aef49a55e813dbd0119788156f04c3dda287bb1ec3759702ea125dd1d7eba088f7409d2e6be5dcd297b98f07722556e3ee4dc68e3b8bf7d70fda2e16d75b54a3b54fb16a3502d44325a855ab4d079698c8ecd4dc59891db2e64565811ec9d9958f70db0fdcf60e072c1a4ad824f7afa6475e1bcabba2fd75bb7ae58fd5c2c7eb441dd66f40acac87578c5ea9e9d551a4aa9cdf9534fa2a49e85484d2a903415144e6a141753f0f8a7be1d4f316e9e54bd39da3a6daf34cf2ee96b84d2724da4cc9b4827ee8fe9151db84a30a9345b5d686b08d07a13a0cff14168d682944d0510fa0720940cbd280a82cfe4449fa8df3f1ede7df58cf6ce39e7f1539eada71dcace38789c47a13773ca6d222cd96f89ae895351fda69db34cf19a98ff33313d52623f6cc3da698313b3019825f26bcbd7839775ed2dc8d25aee94b5bf79597d52b099e55b2ccaa57295282d2a37b24f56849899292d39b256da64717d48ba4b912e9120f80641048c7fbae8fba331f3e0a3afa6c713958e0ce51be25235fd6469d928d291f1a279233fa84672fb8c4b4f17250a2dcfc45a3f38a77a7144b9627709c4646188b4a10fe8b61ebebc3b30d86dbf70d079a193fac2b1b8855c170a88fa1187f4217b5832f5b04cf7a08edac101f681be1b02491202430c00a657ff8aafea9d9fab5bbee9567daf54fa43bdf4406be536b7bc9e4f6e20dec3adbd67f27aa274f4b27de951ebcfb9378c67af0e30de17e7bbb700773090ec8c59d64ccba749d745336e82171cfee439b1907262bee3b9cdc1213b812cf6fb6a2df5abdbc80b376fa26ed4aedd7ebdb98873725276e1138dbbe69b5b10b6acde6d1606d9fcb9b3bc53662216c847ed6c2a5ad7bb353f2f695590d25c49a49ee344ea667e820cf85119c6adb32c2b66415acc4f21969923240e46439c4c847918ff8d31f4ca62dd66c58f4989aa4b0f4eb61db2cc385e586c723098a860c8a4c0f0418192d2fa8775ed05abc75cd7696c2ea6ea5b9c50b6dbc56d65e2da4a85afb42b5ae8169d94acf845583746af43795b940ab6dd1565198ac81755770d2acf79551e10a94ddd5278a2a2d2653b8caa72bbd4e39729a07752f862a585f149feea8fdaa5190b4a2a705454d2a88e35510b56a1d6d14112fa7fae74fe5049ef26d3c29fa77fa94ef1a29ddc0537e7f26cdb14d4b9298e0b92d62025a4914b3c5692cf05243b1a459004896de90d33d1b3ad2351d3460b148bacc9169c322cf0f455f1c8895890a66d2093d4412346817628fe4499fbe383f41a67e0e60f92531f18d23df1e47bbfacf643f9e2dd43c2af077d6a4ee8f79d9e083aadc075287ce91cc1d000939b1c8732fece5e8e9c7662382ea86f8708dcf1f1b70fa36c5266bdd24d799899fff133b0ca669834cd12d1997ce3324ec65d464ca7fe994a5a328a78650eecc927899230931f9ba63498cc4337987358306472607240bfccf97efb92faef05f3ac4bd9a396fd592df5aa5bdcf0b6af116d2d42d6f0e5abba4b472e1681272c5c0c56f6dcad9fe95b1c82a1576537778a698b94bd39297a0452908ca4928946459282a424fd5509f3c893d9df2740a64e6d809aecd934c0d2680f84b879496c6892a15224eed449cef09273392367e2462fa47660c8debe91972523207245b164862e39093f420940040f00c7ea640f95cc1f171a3d2148797638e66871c369037b4f46e9be8dabef1afcd235ce4c690690d089519ca8e330ed06275d0c065816637e2ca94058b0c0a967514d2d02989a452acc0a4f971458982844604e8f8095d9712629e249dac4860788f22a11cbbc236568465b80870a710bac220c3703dc178763570ebd8a1bbb14369ab86ca850d799a19e784334f986657d0cbaea195d242f54305e22d0b69ec169f982be3d855c740a75ca146aa02868f0504aa09946212935424e3e04933608887e10b0d020fd003e822079e020f39401e30683c2ca0730180d93041aff50350ee0627660c40dc1678c82ad3f04603808a21c107c281fbce03e606074088072d900b799014f1c021c3403e23005f1a 0x3420af05194b027c09723810348b64250ed03f430e0e325402b49fc1a401a1424a984f7018829082a00a00e061821a4202cc86a814c0732f205ac29616208d85340780020a007ec3b80770ad01c4b581fe04a91f4888153272137c2ac5490d581e83760cc05385a018809603e10fc1104870f4026829817f012923433a1230ad11b0a7e1240b6082026e1d40d613e80c814f0331818aaa42d090008818001221b02148640940bc06d01ce0f602c85d00f21b7225055c3d6204031940025007200184680d807b084148838405108e12049ea0110a801d4afc1ef0e8866091250e26e056012e1182c7001801802f047026090c4eb0eb84241640782e40228b6e16e0cf842c39e02a24806f02f20b906481843180a406b85142f41a604911000d404b09d85c01781de0af00dc16a07f20482280ec19204082e83e418b02b16441dc1820ee83380ec5c609e8040bc40cb014852c9f04a907d86a436a11929481d03be01e0d3809023458902a144405c12921a01940340880b480002b207f07312440d206d25505580dc104046127824e5d50a986c81ca09f010830418a0680b286e829419c029134c3980ec02b92e00721c70c5023cb940630141490a0e5fa0dc15a822e58d02d83780c845526c86c08e850d06104d81b604602f0124b8006f2f683c40c049b08c813428c14d23e060c1e60710210140bd200e103814802c13a00d854423e1f608515041160b10b8841c20c1310a18484ba000808b06942de0ea09081b89c620005e81743c6066022820840410a0ff815821845008186f415a05f0ae94d43e810f08f0164a8403c28704503e002603c967833415424a8780a7808b20592c010045c25282f816e1202fc07642c81bf0e203c810642001e81380fc12624b12841240860cd86200b407800c0538ace0670ae06b432a0092b901689d46012e681ac0764730198210c004300f504480b00822e993a41e019603105201940f80ef9494a6002320083440185e0038072c36c04c02085d80a254e07303fc9901c900b83501400cd02480400704b4069002894412603b94589da52500984b40424c700a95dc2aa0e805184042201f70a2001cbe20582c080d4344138094123c2a81330c987b837c15b10083bc36202423006140aa0da044868021648410180481c217501403e4044432205839026800703785b41ba0ae0ec00501a005321580e81c410c0e083d02c01180a900b4a0400e2cb82142f80ff0fe858c0900eb28e007ca2a5af0cc011c3f811506c03f89261f90c003b0b500bf03a84c811c5ce00892703601e609587d405e4990f6021c95604308288180ca4050cb94bc0ba60501501b416c00f04692cc3b61c30bd808c2cc01f007958405803326180989aa12e070045c1f659401d874818c00d02e00641da1ad2dc06402e61ae08e849c3c21d30ff120009e15f014915c0a613904180fcbce12a00207cc3fa40825601f41f80f72a381c8b6450804e80741300bb0f281f8b1e1d42c2056caba1c5089846c86e57d01386e41ac0cf0eb00b88701b302a023004e5a301f0 13
def t11 := table 8 1 70 21 0x3fec45ff621ffb127fd883fea45ff322ff990ffcc93fe641ff210ff90effc803fe41bff524ffa907fd487fe423ff21bff900ffc82ffeec3ff764ffbb07fd94bfeca3ff654ffb287fd90bfec83ff644ffb207fd8cbfec63ff634ffb187fd86ffec21ff61dffb08ffd82ffec01ff60dffb00ffd4cbfea63ff534ffa987fd46ffea21ff51dffa88ffd42ffea01ff50dffa80ffd0c7fe869ff430ff98dffcc43fe63bff311ff985ffcc03fe61bff301ff880ffc40bfe21fff10b 0x210842108421084210842108520394e02908421084208e0100e0390a4288a0280a029084210842108400802 112 0xfc0667f1ecabdc0f17960a4f29133dccd97b87b476ec87eb87e7ced41f97d32f175a1e2604dbeb49f6d52fece76cd63399aace4f4b494e919facdd9099ad11735011e5e413caac3b81e7b300c18dfff2fbeb65f793b12d6642d9981ab136115f89b6b9b92d6d1d6ad7ae9561a02a749a53df0ea73b474d7f3299e5dd1f431a3c7d346152684a6a4e279198c02b2d6fde4f82749a138928929239bf6444efc798c78defd50a42c212fc94104e481dcf50029a9f4319be736a79ee4cf134e1cd2f8b9169370afcedcab75a8af6b4c11e67e820c903918ff8d2fe5ff5a5e6ab2b1f163e0aab7e90559a1ea71cb94b58628fdaa51538293137524249a2c9223d4d8c745d34e6c809b9ba52b1c1852f4e492733921c6f23b3063e45d8648fa8c173b17969e27022445be3087eb30f20441d378c33aab06120a0bc45a15bd501c176816b20 0x6e0d03a018881d00844852219164c82c03910511141b01e1f17e1214615010101805c844058365298602858221425315e000625e9240c14c0d8680b83e57008038480c060060525693e2117a0a01c558821594e140701988a4c938010220517c141344b93a4807e588420303c4e18a07012571841682a1283c0984e5001a190585d80a519801a8021e054431 10
def t12 := table 8 0 1 8 0xff 0x0 0 0x0 0x0 1
end OrbBoth0
end
section
open Basis1868 Free1868 Cuts1868 QuickQ Leaf8403 TableLeafQ Exact8403
open Mono8403 OrbitQ FullSignedR8403
namespace OrbBoth0
abbrev q8 (i : Nat) := FrontQ.testS rot t7 m4 ms 8 t8 i=true
set_option maxRecDepth 8192 in
theorem b8a0 : SpanQ.Block q8 0 7 := by decide +kernel
theorem ready8 : OrbitQ.all full 8 t8 := by
  have prev : OrbitQ.all full 7 t7:=by intro i;exact Fin.elim0 i
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot prev m4 ms t8
  have g : SpanQ.Block q8 0 7 := b8a0
  intro i
  simpa only [q8,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q9 (i : Nat) := FrontQ.testS rot t8 m4 ms 9 t9 i=true
set_option maxRecDepth 8192 in
theorem b9a0 : SpanQ.Block q9 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a16 : SpanQ.Block q9 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a32 : SpanQ.Block q9 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a48 : SpanQ.Block q9 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a64 : SpanQ.Block q9 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a80 : SpanQ.Block q9 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b9a96 : SpanQ.Block q9 96 15 := by decide +kernel
theorem ready9 : OrbitQ.all full 9 t9 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready8 m4 ms t9
  have g : SpanQ.Block q9 0 111 := (SpanQ.glue (SpanQ.glue b9a0 (SpanQ.glue b9a16 b9a32)) (SpanQ.glue (SpanQ.glue b9a48 b9a64) (SpanQ.glue b9a80 b9a96)))
  intro i
  simpa only [q9,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q10 (i : Nat) := FrontQ.testS rot t9 m4 ms 10 t10 i=true
set_option maxRecDepth 8192 in
theorem b10a0 : SpanQ.Block q10 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a16 : SpanQ.Block q10 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a32 : SpanQ.Block q10 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a48 : SpanQ.Block q10 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a64 : SpanQ.Block q10 64 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a80 : SpanQ.Block q10 80 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a96 : SpanQ.Block q10 96 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a112 : SpanQ.Block q10 112 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a128 : SpanQ.Block q10 128 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a144 : SpanQ.Block q10 144 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a160 : SpanQ.Block q10 160 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a176 : SpanQ.Block q10 176 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a192 : SpanQ.Block q10 192 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a208 : SpanQ.Block q10 208 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a224 : SpanQ.Block q10 224 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a240 : SpanQ.Block q10 240 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a256 : SpanQ.Block q10 256 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a272 : SpanQ.Block q10 272 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a288 : SpanQ.Block q10 288 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a304 : SpanQ.Block q10 304 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a320 : SpanQ.Block q10 320 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a336 : SpanQ.Block q10 336 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a352 : SpanQ.Block q10 352 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a368 : SpanQ.Block q10 368 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a384 : SpanQ.Block q10 384 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a400 : SpanQ.Block q10 400 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a416 : SpanQ.Block q10 416 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a432 : SpanQ.Block q10 432 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a448 : SpanQ.Block q10 448 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a464 : SpanQ.Block q10 464 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a480 : SpanQ.Block q10 480 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a496 : SpanQ.Block q10 496 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b10a512 : SpanQ.Block q10 512 9 := by decide +kernel
theorem ready10 : OrbitQ.all full 10 t10 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready9 m4 ms t10
  have g : SpanQ.Block q10 0 521 := (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a0 b10a16) (SpanQ.glue b10a32 b10a48)) (SpanQ.glue (SpanQ.glue b10a64 b10a80) (SpanQ.glue b10a96 b10a112))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a128 b10a144) (SpanQ.glue b10a160 b10a176)) (SpanQ.glue (SpanQ.glue b10a192 b10a208) (SpanQ.glue b10a224 b10a240)))) (SpanQ.glue (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a256 b10a272) (SpanQ.glue b10a288 b10a304)) (SpanQ.glue (SpanQ.glue b10a320 b10a336) (SpanQ.glue b10a352 b10a368))) (SpanQ.glue (SpanQ.glue (SpanQ.glue b10a384 b10a400) (SpanQ.glue b10a416 b10a432)) (SpanQ.glue (SpanQ.glue b10a448 b10a464) (SpanQ.glue b10a480 (SpanQ.glue b10a496 b10a512))))))
  intro i
  simpa only [q10,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q11 (i : Nat) := FrontQ.testS rot t10 m4 ms 11 t11 i=true
set_option maxRecDepth 8192 in
theorem b11a0 : SpanQ.Block q11 0 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a16 : SpanQ.Block q11 16 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a32 : SpanQ.Block q11 32 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a48 : SpanQ.Block q11 48 16 := by decide +kernel
set_option maxRecDepth 8192 in
theorem b11a64 : SpanQ.Block q11 64 6 := by decide +kernel
theorem ready11 : OrbitQ.all full 11 t11 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready10 m4 ms t11
  have g : SpanQ.Block q11 0 70 := (SpanQ.glue (SpanQ.glue b11a0 b11a16) (SpanQ.glue b11a32 (SpanQ.glue b11a48 b11a64)))
  intro i
  simpa only [q11,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
abbrev q12 (i : Nat) := FrontQ.testS rot t11 m4 ms 12 t12 i=true
set_option maxRecDepth 8192 in
theorem b12a0 : SpanQ.Block q12 0 1 := by decide +kernel
theorem ready12 : OrbitQ.all full 12 t12 := by
  apply OrbitQ.finish good_ch64x32 valid_full rot fixedRot ready11 m4 ms t12
  have g : SpanQ.Block q12 0 1 := b12a0
  intro i
  simpa only [q12,FrontQ.eqS,Nat.zero_add] using (g ⟨i.val,i.isLt⟩)
theorem bound : excluded 12 full := by
  have eq : TableLeafQ.body full (t12.desc 0)=full := by decide +kernel
  have h:=ready12 ⟨0,by decide⟩
  change (TableLeafQ.body full (t12.desc 0)).Nodup → _ at h
  rw [eq] at h
  exact h (by decide +kernel)
end OrbBoth0
end
section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_11002_aux
open Basis1868 Free1868 Check2516 Cuts1868
open Exact8403 Projection8403
namespace BridgeR8403
def monoRaw : List Sig :=[(0x2aaaaaaaaaaaaabdd5555555555eaaedb6db5ef7bd81baaaaaaaaaaaaaaaaaaaaaaaaaaaabdd5555555555eaaedb6db5ef7bd81b,0x40804002944a040804002944a040804002944a040804002944a040804002944a040804002944a040804002944a040804002944a),(0xcccccccccccccd6e6666666666b3376db6deb5ad2825ccccccccccccccccccccccccccccd6e6666666666b3376db6deb5ad2825,0x8900092422914890009242291489000924229148900092422914890009242291489000924229148900092422914890009242291),(0x30f0f0f0f0f0f0e7787878787873c3b8e38e739ce3006f0f0f0f0f0f0f0f0f0f0f0f0f0f0e7787878787873c3b8e38e739ce3006,0x1122a924849249122a924849249122a924849249122a924849249122a924849249122a924849249122a924849249122a92484924),(0xff00ff00ff00f87f807f807f83fc3f03f07c1f04048ff00ff00ff00ff00ff00ff00ff00f87f807f807f83fc3f03f07c1f04048,0x200331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85e00331c700b85),(0xffff0000ffff007fff80007ffc003ffc007fe008110ffff0000ffff0000ffff0000ffff007fff80007ffc003ffc007fe008110,0x1c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a3501c3c1f806a35),(0xffffffff0000007fffffff8000003fffff8000002a0ffffffff00000000ffffffff0000007fffffff8000003fffff8000002a0,0x3fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c060003fe0000c06),(0x3f000000000000007fffffffffffffc000000000004c0ffffffffffffffff000000000000007fffffffffffffc000000000004c0,0x1fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc00000703801fc000007038),(0x3fffffffffffffff80000000000000000000000000700ffffffffffffffffffffffffffffff80000000000000000000000000700,0x3e000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0fe000000081c0)]
lemma monoNeed : necessary monoRaw:=needFrom (pn:=[(0,18),(0,17),(1,17),(3,17),(4,17),(5,18),(6,20),(8,23)]) (by decide) (by decide +kernel)
lemma signedNeed : necessary FullSignedR8403.full:=needFrom (pn:=[(0,27),(0,12),(4,2),(11,0),(6,8),(1,21),(3,2),(2,13)]) (by decide) (by decide +kernel)
def pS : Array Nat := #[0,25,136,68,21,106,110,57,37,1,99,103,124,12,9,128,160,48,108,30,2,157,46,43,158,118,116,44,100,125,4,67,24,61,87,17,59,50,7,54,71,42,83,63,120,101,132,156,31,112,19,28,91,166,176,152,148,85,39,11,69,104,6,168,3,5,8,10,13,14,15,16,18,20,22,23,26,27,29,32,33,34,35,36,38,40,41,45,47,49,51,52,53,55,56,58,60,62,64,65,66,70,72,73,74,75,76,77,78,79,80,81,82,84,86,88,89,90,92,93,94,95,96,97,98,102,105,107,109,111,113,114,115,117,119,121,122,123,126,127,129,130,131,133,134,135,137,138,139,140,141,142,143,144,145,146,147,149,150,151,153,154,155,159,161,162,163,164,165,167,169,170,171,172,173,174,175,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219]
def nS : Array Nat := #[30,23,14,27,11,34,24,35,31,28,32,25,1,17,16,26,18,21,20,8,19,5,15,33,12,9,6,2,29,22,13,10,0,3,4,7]
def hS := pairHom (fun i=>Fin.ofNat 414 (pS.getD (i.val % pS.size) 0)) (fun i=>Fin.ofNat 414 (nS.getD (i.val % nS.size) 0))
set_option maxRecDepth 8192 in
lemma sigSub : (raw8.toFinset.image hS.fn).image can⊆FullSignedR8403.full.toFinset := by decide +kernel
def pM : Array Nat := #[0,1,2,4,9,19,46,67,108,124,156,0,1,2,4,9,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219]
def nM : Array Nat := #[11,14,21,23,27,28,30,34,35,11,14,21,23,27,28,30,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
def hM := pairHom (fun i=>Fin.ofNat 414 (pM.getD (i.val % pM.size) 0)) (fun i=>Fin.ofNat 414 (nM.getD (i.val % nM.size) 0))
set_option maxRecDepth 8192 in
lemma monoSub : raw8.toFinset.image hM.fn⊆monoRaw.toFinset := by decide +kernel

theorem binary13 {C : Circuit} (fan : FanInTwo C) (sp : ∀x,C.eval (List.ofFn x)=edge x)
    (signed : excluded 12 FullSignedR8403.full) : 13≤C.gates.countP costly := by
  obtain ⟨k,t,S,cap,h,sub⟩:=tagExtract C.gates raw8 vals fan (output8 fan sp)
  obtain ⟨q,fee,m,u,T,fee',hl,ss⟩:=Projection8403.projected h hS
  obtain ⟨j,U,size,b,ub⟩:=compress hl
  have raw : S⊆raw8.toFinset:=fun x hx=>List.mem_toFinset.mpr (sub x hx)
  have incl:=((ub.trans (Finset.image_mono _ ss)).trans (Finset.image_mono _ (Finset.image_mono _ raw))).trans sigSub
  obtain ⟨v,phys⟩:=b.expand
  rw [allNeeded phys incl signedNeed] at b
  by_contra! small
  exact signed j (by omega) b
theorem pureRun (gs : List Gate) (w : List Sig) (valid : ∀a∈w,Valid a)
    (good : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (out : target∈execute gs w) : Mono8403.possible gs.length (Mono8403.closed w) := by
  induction gs generalizing w with
  | nil =>
    refine ⟨0,{target},by rfl,Live.stop,?_⟩
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr out)))
  | cons g gs ih =>
    have va : ∀a∈w++[gv w g],Valid a:=by
      intro a ha
      rcases List.mem_append.mp ha with old|z
      · exact valid a old
      · exact List.mem_singleton.mp z ▸ gv_valid valid g
    have h:=ih _ va (fun g hg=>good g (List.mem_cons_of_mem _ hg)) out
    have eq : Mono8403.closed (w++[gv w g])=insert (gv w g) (Mono8403.closed w):=by
      ext y;simp [Mono8403.closed,or_assoc,or_left_comm,or_comm]
    rw [eq] at h
    have useOld (mem : gv w g∈Mono8403.closed w) : Mono8403.possible (g::gs).length (Mono8403.closed w) :=
      Mono8403.widen h (by simp) (Finset.insert_subset mem (Finset.Subset.refl _))
    obtain ⟨oplim,len⟩:=good g (List.mem_cons_self ..)
    obtain ⟨op,ins⟩:=g
    change op=.and ∨ op=.or at oplim
    change ins.length≤2 at len
    cases ins with
    | nil =>
      rcases oplim with rfl|rfl <;> apply useOld <;> simp [gv,Mono8403.closed]
    | cons i ins =>
      cases ins with
      | nil =>
        obtain ⟨and1,or0,rest⟩:=bin_laws (valid_getD valid i)
        rcases oplim with rfl|rfl <;> apply useOld <;>
          simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,and1,or0] using Mono8403.read_closed w i
      | cons j tail =>
        cases tail with
        | cons a tail => simp at len
        | nil =>
          obtain ⟨and1,or0,rest⟩:=bin_laws (valid_getD valid j)
          rcases oplim with rfl|rfl
          · exact Mono8403.pay false (valid_getD valid i) (valid_getD valid j) (Mono8403.read_closed w i) (Mono8403.read_closed w j)
                (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,and1] using h)
          · exact Mono8403.pay true (valid_getD valid i) (valid_getD valid j) (Mono8403.read_closed w i) (Mono8403.read_closed w j)
                (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,or0] using h)
theorem main (sg : excluded 12 FullSignedR8403.full) (mono : Mono8403.rejects 13 monoRaw) :
    ∀t,HasCircuitSize 8 edge t →14≤t := by
  rintro t ⟨C,fan,le,sp⟩
  by_contra! sm
  have b:=binary13 fan sp sg
  change C.gates.length≤t at le
  have cnt:=List.countP_le_length (p:=costly) (l:=C.gates)
  have eq : C.gates.countP costly=C.gates.length:=by omega
  have allc:=List.countP_eq_length.mp eq
  have good (g : Gate) (mem : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    have h:=fan g mem
    have co:=allc g mem
    refine ⟨?_,h.2⟩
    rcases (show g.op=.and ∨ g.op=.or ∨ g.op=.not from h.1) with op|op|op
    · exact Or.inl op
    · exact Or.inr op
    · simp [costly,op] at co
  obtain ⟨k,S,cap,phy,sub⟩:=pureRun C.gates raw8 vals good (output8 fan sp)
  have ss : S⊆raw8.toFinset:=by
    intro a ha
    have proper:=live_proper phy a ha
    exact (Finset.mem_insert.mp ((Finset.mem_insert.mp (sub ha)).resolve_left proper.2.1)).resolve_left proper.2.2
  obtain ⟨q,save,j,T,fee,run,sub'⟩:=Mono8403.projected phy rfl hM
  have incl:=sub'.trans ((Finset.image_mono _ ss).trans monoSub)
  rw [allNeeded run incl monoNeed] at run
  exact mono j (by omega) run
end BridgeR8403
end
end PEqualNP.Outside.L_meta_11002_aux
open PEqualNP.Outside.L_meta_11002_aux
namespace PEqualNP.Outside.L_meta_11002_aux
theorem eight_lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 14 ≤ t := by
  apply BridgeR8403.main OrbBoth0.bound
  have eq : BridgeR8403.monoRaw=MonoD0Data.full:=by decide +kernel
  rw [eq]
  exact OrbFitM0.bound

-- Pinning an essential input saves a gate, by the restriction argument of L_meta_4109.
namespace Restriction
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi

theorem one_drop (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin n)
    (b : Bool)
    (hess : ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hnc : ¬ ∃ c, ∀ y : Fin n → Bool, C.eval (List.ofFn (Function.update y i b)) = c) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (Function.update y i b)) := by
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  have hev : ∀ x, C.eval x = (run C.gates x).getD C.output false := fun _ => rfl
  have hout : C.output < n + C.gates.length := by
    by_contra hcon
    obtain ⟨x, y, -, hxy⟩ := hess
    apply hxy
    rw [hev, hev, List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
  let X : (Fin n → Bool) → List Bool := fun y => List.ofFn (Function.update y i b)
  have hXl : ∀ y, (X y).length = n := fun y => by simp [X]
  have hXi : ∀ y, (X y).getD i false = b := by
    intro y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  have hXk : ∀ (k : ℕ), k < n → k ≠ i → ∀ y, (X y).getD k false = (List.ofFn y).getD k false := by
    intro k hk hki y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_ofFn, List.getElem_ofFn]
    exact Function.update_of_ne (fun hc => hki (congrArg Fin.val hc)) _ _
  have hinw : ∀ k < n, ∀ y, (C.wires (X y)).getD k false = (X y).getD k false := by
    intro k hk y
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k =>
          if k < n + j then (C.wires (X y)).getD k false else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have hoi : C.output ≠ i := by
    intro h
    apply hnc
    refine ⟨b, fun y => ?_⟩
    rw [hev, h, run_input _ _ _ (by simp)]
    exact hXi y
  have hread : ∃ g ∈ C.gates, (i : ℕ) ∈ rds g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy, hne⟩ := hess
    apply hne
    rw [hev, hev]
    refine indep i C.gates (fun g hg => (hops g hg).1) hcon _ _ (by simp) (fun k hk => ?_) _ hoi
    by_cases h : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_ofFn, List.getElem_ofFn]
      exact hxy _ fun hc => hk (congrArg Fin.val hc)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  obtain ⟨D, S, d1, -, -, d4, d5, d6⟩ := circuit n n C X hops hXl (fun k hk => by
      by_cases h : k = i
      · exact Or.inl ⟨b, fun y => by rw [h]; exact hXi y⟩
      · exact Or.inr ⟨k, hk, hXk k hk h⟩) hrec hinw hout hnc
  refine ⟨D, fun g hg => ?_, ?_, fun y => d6 y⟩
  · obtain ⟨h1, h2⟩ := d1 g hg
    exact ⟨by simpa using h1, h2⟩
  · have hdrop : Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
      obtain ⟨hop, hlen⟩ := hops _ hg
      have hv := hrec j hj
      have hii : ∀ y, (if (i : ℕ) < n + j then (C.wires (X y)).getD (i : ℕ) false else false) = b := by
        intro y
        rw [if_pos (by have := i.2; omega), hinw i i.2, hXi]
      generalize hI : C.gates[j].inputs = I at *
      generalize hO : C.gates[j].op = o at *
      have two : ∀ c : ℕ, (∀ y, (C.wires (X y)).getD (n + j) false =
          (b && if c < n + j then (C.wires (X y)).getD c false else false)) ∨
          (∀ y, (C.wires (X y)).getD (n + j) false =
          (b || if c < n + j then (C.wires (X y)).getD c false else false)) →
          Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
        intro c hc
        by_cases hcl : c < n + j
        · simp only [hcl, if_true] at hc
          rcases hc with hc | hc <;> cases b
          · exact Or.inl ⟨false, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inl ⟨true, fun y => by simp only; rw [hc y]; rfl⟩
        · simp only [hcl, if_false] at hc
          rcases hc with hc | hc
          · exact Or.inl ⟨b && false, fun y => hc y⟩
          · exact Or.inl ⟨b || false, fun y => hc y⟩
      match I, hlen with
      | [], _ =>
        exfalso
        simp only [rds, hO, hI] at hgi
        rcases hop with rfl | rfl | rfl <;> simp at hgi
      | [a], _ =>
        have hai : a = i := by
          simp only [rds, hO, hI] at hgi
          rcases hop with rfl | rfl | rfl
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
        subst hai
        refine Or.inl ⟨o.eval [b], fun y => ?_⟩
        simp only
        rw [hv y, List.map_singleton, hii y]
      | [a, c], _ =>
        rcases hop with rfl | rfl | rfl
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.and_comm]
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.or_comm]
        · have hai : (i : ℕ) = a := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          subst hai
          refine Or.inl ⟨!b, fun y => ?_⟩
          simp only
          rw [hv y, List.map_cons, hii y]
          rfl
    have hsub : S ⊆ (Finset.range C.gates.length).erase j := by
      intro k hk
      obtain ⟨h1, h2⟩ := d5 k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 h1⟩
      rintro rfl
      exact h2 hdrop
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range] at h1
    change D.gates.length + 1 ≤ C.gates.length
    omega

end Restriction

-- Size-preserving input relabelling from L_meta_9258.
namespace Projection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end Projection

end PEqualNP.Outside.L_meta_11002_aux

-- Deleting vertex 4 leaves the eight-vertex function after a permutation.
theorem PEqualNP.Outside.L_meta_11002 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 15 ≤ t := by
  intro t hc
  let f := (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8))
  obtain ⟨C, fan, size, computes⟩ := hc
  change ∀ x, C.eval (List.ofFn x) = f x at computes
  have essential : ∃ x y : Fin 9 → Bool, (∀ j, j ≠ 4 → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    refine ⟨fun i => decide (i = 8), fun i => decide (i = 4 ∨ i = 8), ?_, ?_⟩
    · intro j hj
      simp [hj]
    · rw [computes, computes]
      decide +kernel
  have nonconst : ¬ ∃ c, ∀ y : Fin 9 → Bool,
      C.eval (List.ofFn (Function.update y 4 false)) = c := by
    rintro ⟨c, fixed⟩
    have allOff := fixed (fun _ => false)
    have allOn := fixed (fun _ => true)
    rw [computes] at allOff allOn
    have different : f (Function.update (fun _ => false) 4 false) ≠
        f (Function.update (fun _ => true) 4 false) := by decide +kernel
    exact different (allOff.trans allOn.symm)
  obtain ⟨D, valid, saved, evalD⟩ :=
    Restriction.one_drop 9 C fan 4 false essential nonconst
  have pinned : PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x => f (Function.update x 4 false)) D.size :=
    ⟨D, valid, le_rfl, fun x => (evalD x).trans (computes _)⟩
  let π : Fin 9 → Fin 8 := ![5, 3, 2, 4, 0, 6, 1, 7, 0]
  have same : (fun y : Fin 8 → Bool => f (Function.update (y ∘ π) 4 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext y
    revert y
    decide +kernel
  have mapped := Projection.relabel_size π (fun x => f (Function.update x 4 false)) D.size pinned
  rw [same] at mapped
  have floor := eight_lower D.size mapped
  omega
