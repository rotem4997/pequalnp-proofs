import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10472
namespace Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := Nat × Nat
def top : Nat := 0xffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def Valid1 (x : Nat) : Prop := ∀ j, 16 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 8 * 2 ^ 8 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 16) := by
  rw [top_eq_pow]; exact pow_add_testBit 8 8 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 16 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 16
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 16 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 16 by omega]
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
  have hlt : x < 2 ^ 8 * 2 ^ 8 := by
    have hp : 0 < 2 ^ 8 * 2 ^ 8 := by decide
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
    by_cases hj : j < 16 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 16 <;> simp [hj]
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
def bit (side : Bool) (i : Fin 16) (a : Sig) : Bool :=
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

abbrev I := Fin 16
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
      by_cases hj : j < 16
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
  cases u <;> simp [PEqualNP.Outside.L_meta_10472.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 16 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 16 <;> simp [e]

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
lemma validBound {x} (h : Valid1 x) : x < 2^16 := by
  have eq : x % 2^16 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 16
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
abbrev I := Fin 16
def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_10472.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_10472.Board1868 (mult)
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
open PEqualNP.Outside.L_meta_10472.Board1868 (mult)
open PEqualNP.Outside.L_meta_10472.ColorSearch1868 (paint paint_ok)

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
def reindexLoop (f : Fin 16 → Fin 16) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 16 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 16 → Fin 16) (x : Nat) : Nat := reindexLoop f x 16
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindexLoop_testBit (f : Fin 16 → Fin 16) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 16 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 16
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
            have hj414 : j < 16 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 16 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 16
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 16 → Fin 16) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 16 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 16 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 16 → Fin 16) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 16 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 16 → Fin 16) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 16 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 16 → Fin 16) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 16 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 16 → Fin 16) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 16
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 16 → Fin 16) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 16 → Fin 16) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 16
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
def pairHom (fp fn : Fin 16 → Fin 16) : SigHom where
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
lemma fixed (p n : Fin 16 → Fin 16) (z : p 0=0) : SignFixed (pairHom p n) := by
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

abbrev I := Fin 16
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
end PEqualNP.Outside.L_meta_10472
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_10472
def edge (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
end PEqualNP.Outside.L_meta_10472
namespace PEqualNP.Outside.L_meta_10472
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
open Projection8403 PEqualNP.Outside.L_meta_10472
namespace Exact8403
def raw8 : List Sig := [(551, 4098), (32768, 0), (16864, 384), (12572, 352), (43410, 50264), (3161, 40980), (32256, 1536)]
def pos8 : Array Nat := #[33, 17, 9, 40, 56, 5, 36, 20, 28, 65, 96, 112, 72, 88, 68, 18]
def neg8 : Array Nat := #[0, 1, 32, 16, 48, 8, 24, 4, 12, 64, 80]
def sample8 (s : Bool) (i : Fin 16) : Fin 7 → Bool :=
  let xs:=if s then pos8 else neg8
  fun j=>(xs.getD (i.val % xs.size) 0).testBit j.val
lemma vals : ∀a∈raw8,Valid a := by
  have h : raw8.all (fun x=>decide (x.1≤top ∧ x.2≤top))=true := by decide +kernel
  intro a ha
  have k:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top k.1,valid1_of_le_top k.2⟩
set_option maxHeartbeats 0 in
lemma good8 : ∀(s : Bool) (i : Fin 16), edge (sample8 s i)=s ∧ List.ofFn (sample8 s i)=raw8.map (bit s i) := by decide +kernel
lemma output8 {C : Circuit} (fan : FanInTwo C) (spec : ∀x, C.eval (List.ofFn x)=edge x) :
    target∈execute C.gates raw8 := by
  let w:=execute C.gates raw8
  have hwv:=execute_valid C.gates raw8 vals
  have hp (s : Bool) (i : Fin 16) : bit s i (w.getD C.output zero)=s := by
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
      by_cases hi : j<16
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)];simp [hi]
    · apply Nat.eq_of_testBit_eq;intro j
      by_cases hi : j<16
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)];exact (Nat.zero_testBit j).symm
  have rep:=get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun h=>h target_proper)
def necessary (v : List Sig) := ∀a∈v,∃p n : Fin 16,∀b∈v,bit true p b≠bit false n b → b=a
lemma allNeeded {k t S} {v : List Sig} (h : Live k t S) (sub : S⊆v.toFinset) (need : necessary v) : S=v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨p,n,uniq⟩:=need a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_10472.Conflict1868.pair_sep h p n
  exact uniq b (List.mem_toFinset.mp (sub hb)) sep ▸ hb
def necessaryAt (v : List Sig) (pn : List (Nat×Nat)) :=
  (v.zip pn).all fun (a,p,n) => v.all fun b=>bit true (Fin.ofNat 16 p) b == bit false (Fin.ofNat 16 n) b || b==a
lemma needFrom {v : List Sig} {pn : List (Nat×Nat)} (len : v.length≤pn.length) (ok : necessaryAt v pn=true) : necessary v := by
  intro a ha
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ha
  have hp : i<pn.length:=by omega
  have hz : (a,pn[i])∈v.zip pn := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp;omega,by simp [eq]⟩
  have h:=List.all_eq_true.mp ok _ hz
  refine ⟨Fin.ofNat 16 pn[i].1,Fin.ofNat 16 pn[i].2,?_⟩
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
def positive (c : Chart) (i : Fin (area c)) : Fin 16 := Fin.ofNat 16 (i.val/c.w)
def negative (c : Chart) (i : Fin (area c)) : Fin 16 := Fin.ofNat 16 (i.val % c.w)
def good (c : Chart) :=
  (∀i : Fin 16, sweep c.spreadP (2^i.val) = if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 16, sweep c.spreadN (2^i.val) = if i.val<c.w then col c i.val else 0) ∧
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
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_10472.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_10472.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_10472.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10472.WProof1868.validBound va)]
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
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10472.WProof1868.validBound va)]
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
  (∀i : Fin 16,sweep c.spreadP (2^i.val)=if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 16,sweep c.spreadN (2^i.val)=if i.val<c.w then col c i.val else 0) ∧
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
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open PEqualNP.Outside.L_meta_10472.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_10472.Board1868 (mult)
open PEqualNP.Outside.L_meta_10472.ColorSearch1868 (paint paint_ok)
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
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10472.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10472.Conflict1868.Unique] using y⟩
end QuickQ
end

open Basis1868 Free1868 FreeSearch1868 Cuts1868 Check2516 Exact8403
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def chart : QuickQ.Chart := ⟨16,16,[(false, 0, 0xffff), (true, 120, 0xff000000000000000000000000000000ff), (true, 60, 0xf000000000000000f000000000000000f000000000000000f), (true, 30, 0x300000003000000030000000300000003000000030000000300000003), (true, 15, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma chart_valid : QuickQ.good chart := by
  apply QuickQ.goodOfCompact
  unfold QuickQ.compactGood
  decide +kernel

def minorRaw : List Sig := [(0x7dd8, 0xeffd), (0x73a6, 0x5feb), (0x2992, 0xc458), (0x311c, 0x160), (0x41e0, 0x180), (0x7e00, 0x600)]
def omitLeaf : SigHom := pairHom (fun i => Fin.ofNat 16 (i.val % 15)) id
lemma need_full : necessary raw8 :=
  needFrom (pn := [(0, 2), (15, 3), (5, 1), (2, 1), (1, 1), (0, 1), (9, 1)]) (by decide) (by decide +kernel)
lemma need_minor : necessary minorRaw :=
  needFrom (pn := [(0, 2), (0, 1), (1, 1), (2, 1), (5, 1), (9, 1)]) (by decide) (by decide +kernel)
lemma minorImage : (raw8.toFinset.image omitLeaf.fn).image can ⊆ insert zero minorRaw.toFinset := by
  decide +kernel
lemma massLeaf : 1 ≤ Projection8403.mass omitLeaf raw8.toFinset := by
  decide +kernel
lemma minorND : minorRaw.Nodup := by decide

def word0 : Sig := (0x24, 0x19a3)
def word1 : Sig := (0x192, 0xc058)
def word2 : Sig := (0x1a6, 0x59eb)
def word3 : Sig := (0x1d8, 0xe9fd)
def word4 : Sig := (0x1da, 0xe9fd)
def word5 : Sig := (0x1dc, 0xe9fd)
def word6 : Sig := (0x1f8, 0xe9fd)
def word7 : Sig := (0x1fe, 0xf9ff)
def word8 : Sig := (0x200, 0x0)
def word9 : Sig := (0x202, 0x5e0b)
def word10 : Sig := (0x226, 0x1002)
def word11 : Sig := (0xc00, 0x0)
def word12 : Sig := (0xc00, 0xee1d)
def word13 : Sig := (0xc58, 0xa014)
def word14 : Sig := (0xdd8, 0xe9fd)
def word15 : Sig := (0x2182, 0x4448)
def word16 : Sig := (0x2992, 0xc458)
def word17 : Sig := (0x2b92, 0xc458)
def word18 : Sig := (0x2dda, 0xe45c)
def word19 : Sig := (0x301c, 0x60)
def word20 : Sig := (0x311c, 0x160)
def word21 : Sig := (0x31d8, 0xe9fd)
def word22 : Sig := (0x31dc, 0xe9fd)
def word23 : Sig := (0x3206, 0x5e6b)
def word24 : Sig := (0x331c, 0x160)
def word25 : Sig := (0x3c18, 0xee7d)
def word26 : Sig := (0x3d1c, 0x160)
def word27 : Sig := (0x3d9a, 0xee7d)
def word28 : Sig := (0x3e00, 0x600)
def word29 : Sig := (0x3e1e, 0xfe7f)
def word30 : Sig := (0x3f92, 0xc658)
def word31 : Sig := (0x41d8, 0xe9fd)
def word32 : Sig := (0x41e0, 0x180)
def word33 : Sig := (0x41f8, 0xe9fd)
def word34 : Sig := (0x42a2, 0x5e8b)
def word35 : Sig := (0x43e0, 0x180)
def word36 : Sig := (0x4cc0, 0xee9d)
def word37 : Sig := (0x4de0, 0x180)
def word38 : Sig := (0x4e00, 0x600)
def word39 : Sig := (0x4ee2, 0xfe9f)
def word40 : Sig := (0x5224, 0x1ba3)
def word41 : Sig := (0x522c, 0x1ba3)
def word42 : Sig := (0x5264, 0x1ba3)
def word43 : Sig := (0x5448, 0x2ba5)
def word44 : Sig := (0x5600, 0x200)
def word45 : Sig := (0x5624, 0x1ba3)
def word46 : Sig := (0x566c, 0x3ba7)
def word47 : Sig := (0x6f92, 0xc658)
def word48 : Sig := (0x7180, 0x4fe9)
def word49 : Sig := (0x7182, 0x4fe9)
def word50 : Sig := (0x7184, 0x4fe9)
def word51 : Sig := (0x7198, 0x4fe9)
def word52 : Sig := (0x719c, 0x4fe9)
def word53 : Sig := (0x71a0, 0x4fe9)
def word54 : Sig := (0x71a6, 0x5feb)
def word55 : Sig := (0x71c0, 0x4fe9)
def word56 : Sig := (0x71d8, 0xeffd)
def word57 : Sig := (0x71e0, 0x4fe9)
def word58 : Sig := (0x71fc, 0x1e0)
def word59 : Sig := (0x7200, 0x600)
def word60 : Sig := (0x7224, 0x1fa3)
def word61 : Sig := (0x7226, 0x1602)
def word62 : Sig := (0x7380, 0x4fe9)
def word63 : Sig := (0x7382, 0x4648)
def word64 : Sig := (0x73a6, 0x5feb)
def word65 : Sig := (0x73be, 0x5feb)
def word66 : Sig := (0x73e6, 0x5feb)
def word67 : Sig := (0x7b92, 0xc658)
def word68 : Sig := (0x7bb6, 0xdffb)
def word69 : Sig := (0x7c00, 0x600)
def word70 : Sig := (0x7d80, 0x4fe9)
def word71 : Sig := (0x7d92, 0xc658)
def word72 : Sig := (0x7dd8, 0xeffd)
def word73 : Sig := (0x7dda, 0xeffd)
def word74 : Sig := (0x7ddc, 0xeffd)
def word75 : Sig := (0x7df8, 0xeffd)
def word76 : Sig := (0x7e00, 0x600)
def word77 : Sig := (0x7e24, 0x1fa3)
def word78 : Sig := (0x7e26, 0x1602)
def word79 : Sig := (0x7f1c, 0x760)
def word80 : Sig := (0x7f80, 0x4fe9)
def word81 : Sig := (0x7f82, 0x4648)
def word82 : Sig := (0x7f92, 0xc658)
def word83 : Sig := (0x7fa6, 0x5feb)
def word84 : Sig := (0x7fd8, 0xeffd)
def word85 : Sig := (0x7fe0, 0x780)
def word86 : Sig := (0x7ffc, 0x7e0)
def word87 : Sig := (0x7ffe, 0xffff)

def bucket1_0 : List (List Sig) := []

def bucket1_1 : List (List Sig) := []

def bucket1_2 : List (List Sig) := []

def bucket1_3 : List (List Sig) := []

def bucket1_4 : List (List Sig) := []

def bucket1_5 : List (List Sig) := []

def bucket1_6 : List (List Sig) := []

def bucket1_7 : List (List Sig) := []

def bucket1_8 : List (List Sig) := []

def bucket1_9 : List (List Sig) := []

def bucket1_10 : List (List Sig) := []

def bucket1_11 : List (List Sig) := []

def bucket1_12 : List (List Sig) := []

def bucket1_13 : List (List Sig) := []

def bucket1_14 : List (List Sig) := []

def bucket1_15 : List (List Sig) := []

def bucket1_16 : List (List Sig) := []

def bucketTier1 : List (List (List Sig)) := [bucket1_0, bucket1_1, bucket1_2, bucket1_3, bucket1_4, bucket1_5, bucket1_6, bucket1_7, bucket1_8, bucket1_9, bucket1_10, bucket1_11, bucket1_12, bucket1_13, bucket1_14, bucket1_15, bucket1_16]

def bucket2_0 : List (List Sig) := []

def bucket2_1 : List (List Sig) := []

def bucket2_2 : List (List Sig) := []

def bucket2_3 : List (List Sig) := []

def bucket2_4 : List (List Sig) := []

def bucket2_5 : List (List Sig) := []

def bucket2_6 : List (List Sig) := []

def bucket2_7 : List (List Sig) := []

def bucket2_8 : List (List Sig) := []

def bucket2_9 : List (List Sig) := []

def bucket2_10 : List (List Sig) := []

def bucket2_11 : List (List Sig) := []

def bucket2_12 : List (List Sig) := []

def bucket2_13 : List (List Sig) := []

def bucket2_14 : List (List Sig) := []

def bucket2_15 : List (List Sig) := []

def bucket2_16 : List (List Sig) := []

def bucketTier2 : List (List (List Sig)) := [bucket2_0, bucket2_1, bucket2_2, bucket2_3, bucket2_4, bucket2_5, bucket2_6, bucket2_7, bucket2_8, bucket2_9, bucket2_10, bucket2_11, bucket2_12, bucket2_13, bucket2_14, bucket2_15, bucket2_16]

def bucket3_0 : List (List Sig) := []

def bucket3_1 : List (List Sig) := []

def bucket3_2 : List (List Sig) := []

def bucket3_3 : List (List Sig) := []

def bucket3_4 : List (List Sig) := []

def bucket3_5 : List (List Sig) := []

def bucket3_6 : List (List Sig) := []

def bucket3_7 : List (List Sig) := []

def bucket3_8 : List (List Sig) := []

def bucket3_9 : List (List Sig) := []

def bucket3_10 : List (List Sig) := []

def bucket3_11 : List (List Sig) := []

def bucket3_12 : List (List Sig) := []

def bucket3_13 : List (List Sig) := []

def bucket3_14 : List (List Sig) := []

def bucket3_15 : List (List Sig) := []

def bucket3_16 : List (List Sig) := []

def bucketTier3 : List (List (List Sig)) := [bucket3_0, bucket3_1, bucket3_2, bucket3_3, bucket3_4, bucket3_5, bucket3_6, bucket3_7, bucket3_8, bucket3_9, bucket3_10, bucket3_11, bucket3_12, bucket3_13, bucket3_14, bucket3_15, bucket3_16]

def bucket4_0 : List (List Sig) := []

def bucket4_1 : List (List Sig) := []

def bucket4_2 : List (List Sig) := []

def bucket4_3 : List (List Sig) := []

def bucket4_4 : List (List Sig) := []

def bucket4_5 : List (List Sig) := []

def bucket4_6 : List (List Sig) := []

def bucket4_7 : List (List Sig) := []

def bucket4_8 : List (List Sig) := []

def bucket4_9 : List (List Sig) := []

def bucket4_10 : List (List Sig) := []

def bucket4_11 : List (List Sig) := []

def bucket4_12 : List (List Sig) := []

def bucket4_13 : List (List Sig) := []

def bucket4_14 : List (List Sig) := []

def bucket4_15 : List (List Sig) := []

def bucket4_16 : List (List Sig) := []

def bucketTier4 : List (List (List Sig)) := [bucket4_0, bucket4_1, bucket4_2, bucket4_3, bucket4_4, bucket4_5, bucket4_6, bucket4_7, bucket4_8, bucket4_9, bucket4_10, bucket4_11, bucket4_12, bucket4_13, bucket4_14, bucket4_15, bucket4_16]

def bucket5_0 : List (List Sig) := []

def bucket5_1 : List (List Sig) := [[word3, word16, word20, word23, word48, word85]]

def bucket5_2 : List (List Sig) := [[word2, word3, word16, word32, word48, word58],
    [word9, word12, word16, word32, word48, word76]]

def bucket5_3 : List (List Sig) := []

def bucket5_4 : List (List Sig) := [[word9, word16, word25, word48, word58, word76]]

def bucket5_5 : List (List Sig) := []

def bucket5_6 : List (List Sig) := []

def bucket5_7 : List (List Sig) := [[word3, word16, word25, word58, word64, word79]]

def bucket5_8 : List (List Sig) := [[word2, word3, word16, word20, word32, word53],
    [word2, word6, word16, word20, word32, word48]]

def bucket5_9 : List (List Sig) := [[word2, word3, word16, word20, word23, word25],
    [word16, word25, word34, word48, word58, word76]]

def bucket5_10 : List (List Sig) := [[word3, word12, word16, word32, word64, word86]]

def bucket5_11 : List (List Sig) := []

def bucket5_12 : List (List Sig) := [[word3, word16, word25, word58, word64, word86]]

def bucket5_13 : List (List Sig) := [[word2, word3, word16, word20, word32, word49],
    [word2, word4, word16, word20, word32, word48]]

def bucket5_14 : List (List Sig) := []

def bucket5_15 : List (List Sig) := []

def bucket5_16 : List (List Sig) := [[word2, word16, word20, word25, word48, word85]]

def bucketTier5 : List (List (List Sig)) := [bucket5_0, bucket5_1, bucket5_2, bucket5_3, bucket5_4, bucket5_5, bucket5_6, bucket5_7, bucket5_8, bucket5_9, bucket5_10, bucket5_11, bucket5_12, bucket5_13, bucket5_14, bucket5_15, bucket5_16]

def bucket6_0 : List (List Sig) := [[word3, word16, word32, word58, word64, word72, word79],
    [word3, word20, word32, word48, word64, word82],
    [word9, word16, word25, word58, word64, word72, word76],
    [word12, word16, word32, word48, word58, word64, word76],
    [word16, word20, word25, word32, word34, word48, word76],
    [word23, word58, word64, word72, word76, word82]]

def bucket6_1 : List (List Sig) := [[word2, word16, word20, word32, word56, word72],
    [word3, word16, word23, word58, word64, word72, word76],
    [word16, word20, word23, word25, word36, word64, word76],
    [word16, word23, word32, word34, word36, word72, word76],
    [word16, word25, word58, word64, word72, word76, word79],
    [word16, word32, word34, word36, word48, word76],
    [word20, word32, word36, word40, word48, word76]]

def bucket6_2 : List (List Sig) := [[word2, word3, word16, word20, word23, word32, word72],
    [word2, word3, word16, word20, word32, word48],
    [word2, word16, word20, word32, word48, word75, word76],
    [word2, word16, word20, word32, word53, word72, word76],
    [word2, word16, word23, word58, word72, word76],
    [word16, word20, word25, word48, word58, word64, word76],
    [word16, word32, word34, word48, word58, word72, word76]]

def bucket6_3 : List (List Sig) := [[word2, word16, word20, word23, word25, word72, word76],
    [word3, word16, word20, word32, word49, word64, word76],
    [word4, word16, word20, word32, word48, word64, word76],
    [word16, word20, word23, word25, word48, word76],
    [word16, word23, word36, word58, word64, word72, word76]]

def bucket6_4 : List (List Sig) := [[word2, word3, word16, word20, word32, word64, word75],
    [word2, word6, word16, word20, word32, word64, word72],
    [word3, word16, word20, word32, word36, word64, word85],
    [word12, word16, word32, word64, word72, word76, word86]]

def bucket6_5 : List (List Sig) := [[word3, word16, word20, word32, word48, word64, word85],
    [word3, word16, word32, word58, word64, word72, word86],
    [word16, word20, word25, word36, word64, word76, word85],
    [word16, word23, word48, word58, word72, word76],
    [word16, word25, word34, word58, word64, word72, word76],
    [word23, word40, word58, word72, word76]]

def bucket6_6 : List (List Sig) := [[word16, word20, word25, word48, word64, word76, word85],
    [word16, word25, word58, word64, word72, word76, word86],
    [word16, word32, word36, word64, word72, word79, word85]]

def bucket6_7 : List (List Sig) := [[word2, word16, word20, word32, word48, word73, word76],
    [word2, word16, word20, word32, word49, word72, word76],
    [word16, word36, word58, word64, word72, word76, word85]]

def bucket6_8 : List (List Sig) := [[word3, word16, word32, word36, word58, word64, word76],
    [word3, word20, word32, word64, word72, word81],
    [word16, word25, word32, word36, word64, word76, word79],
    [word16, word48, word58, word64, word72, word76, word85],
    [word20, word23, word40, word58, word72, word76],
    [word40, word58, word64, word72, word76, word85]]

def bucket6_9 : List (List Sig) := [[word2, word3, word16, word20, word32, word64, word73],
    [word2, word4, word16, word20, word32, word64, word72],
    [word2, word16, word20, word32, word48, word72, word85],
    [word3, word16, word20, word25, word64, word85],
    [word3, word16, word32, word48, word58, word64, word76],
    [word12, word16, word23, word58, word64, word72, word76],
    [word16, word20, word23, word25, word34, word72, word76]]

def bucket6_10 : List (List Sig) := [[word3, word20, word32, word63, word64, word72],
    [word58, word64, word72, word82, word85]]

def bucket6_11 : List (List Sig) := [[word2, word16, word20, word25, word32, word48, word76],
    [word2, word16, word20, word32, word43, word48, word76],
    [word2, word16, word20, word37, word72],
    [word2, word16, word26, word32, word72],
    [word2, word16, word58, word64, word72, word85],
    [word3, word16, word58, word64, word72, word85],
    [word16, word32, word36, word48, word58, word64, word76]]

def bucket6_12 : List (List Sig) := [[word2, word16, word20, word25, word64, word72, word85],
    [word16, word20, word23, word48, word72, word76, word85],
    [word16, word25, word32, word34, word36, word64, word76],
    [word20, word23, word40, word72, word76, word85]]

def bucket6_13 : List (List Sig) := [[word2, word3, word16, word20, word25, word32, word64],
    [word2, word3, word16, word20, word32, word43, word64],
    [word2, word16, word32, word48, word58, word72, word76],
    [word3, word16, word20, word23, word32, word48, word76],
    [word3, word16, word25, word58, word64, word76],
    [word12, word16, word58, word64, word72, word76, word85],
    [word20, word23, word64, word72, word82, word85],
    [word20, word32, word48, word72, word76, word77],
    [word20, word58, word64, word72, word82, word85]]

def bucket6_14 : List (List Sig) := [[word3, word12, word16, word32, word58, word64, word76],
    [word3, word16, word20, word23, word64, word72, word85],
    [word9, word16, word32, word48, word58, word72, word76],
    [word16, word20, word25, word64, word72, word79, word85]]

def bucket6_15 : List (List Sig) := [[word2, word3, word16, word32, word58, word64, word72],
    [word2, word16, word20, word23, word72, word85],
    [word2, word16, word20, word32, word56],
    [word3, word16, word20, word25, word32, word64, word79],
    [word3, word16, word20, word32, word53, word64, word76],
    [word6, word16, word20, word32, word48, word64, word76],
    [word9, word12, word16, word32, word64, word72, word76],
    [word16, word20, word23, word32, word36, word48, word76],
    [word20, word32, word48, word60, word72, word76]]

def bucket6_16 : List (List Sig) := [[word2, word16, word25, word58, word64, word72, word76],
    [word3, word16, word20, word23, word25, word64, word76],
    [word3, word16, word20, word25, word58, word64, word76],
    [word3, word16, word32, word36, word64, word79],
    [word3, word20, word32, word36, word64, word82],
    [word3, word20, word32, word40, word48, word76],
    [word16, word25, word48, word58, word64, word76]]

def bucketTier6 : List (List (List Sig)) := [bucket6_0, bucket6_1, bucket6_2, bucket6_3, bucket6_4, bucket6_5, bucket6_6, bucket6_7, bucket6_8, bucket6_9, bucket6_10, bucket6_11, bucket6_12, bucket6_13, bucket6_14, bucket6_15, bucket6_16]

def bucket7_0 : List (List Sig) := [[word1, word20, word32, word48, word64, word72, word76],
    [word3, word16, word20, word32, word64, word72, word79],
    [word3, word16, word20, word32, word64, word73, word76],
    [word4, word16, word20, word32, word64, word72, word76],
    [word16, word20, word29, word64, word72, word76],
    [word20, word32, word64, word67, word72, word76]]

def bucket7_1 : List (List Sig) := [[word16, word19, word32, word48, word64, word72, word76],
    [word16, word20, word23, word58, word64, word72, word76],
    [word16, word20, word31, word32, word64, word72, word76],
    [word16, word20, word32, word64, word72, word76, word80],
    [word16, word20, word37, word64, word72, word76],
    [word16, word26, word32, word64, word72, word76],
    [word18, word20, word32, word64, word72, word76],
    [word19, word32, word40, word64, word72, word76],
    [word20, word32, word63, word64, word72, word76],
    [word20, word32, word64, word72, word82, word85]]

def bucket7_2 : List (List Sig) := [[word2, word16, word20, word32, word64, word72, word85],
    [word3, word16, word20, word32, word64, word72, word85],
    [word16, word20, word32, word34, word48, word72, word76],
    [word16, word58, word64, word72, word76, word85],
    [word20, word32, word41, word64, word72, word76],
    [word20, word32, word47, word64, word72, word76]]

def bucket7_3 : List (List Sig) := [[word2, word16, word20, word32, word64, word72, word73, word76],
    [word16, word20, word22, word32, word64, word72, word76],
    [word16, word20, word25, word64, word72, word76, word85],
    [word16, word20, word32, word48, word64, word73, word76],
    [word16, word20, word32, word48, word64, word76, word84],
    [word16, word20, word32, word49, word64, word72, word76],
    [word16, word20, word32, word62, word64, word72, word76]]

def bucket7_4 : List (List Sig) := [[word3, word16, word20, word25, word32, word64, word76],
    [word3, word16, word20, word32, word43, word64, word76],
    [word14, word16, word20, word32, word64, word72, word76],
    [word16, word20, word32, word48, word66, word72, word76],
    [word16, word20, word32, word55, word64, word72, word76],
    [word16, word20, word32, word64, word72, word79, word85],
    [word20, word32, word40, word66, word72, word76],
    [word20, word32, word42, word64, word72, word76]]

def bucket7_5 : List (List Sig) := [[word16, word20, word23, word64, word72, word76, word85],
    [word16, word20, word32, word48, word65, word72, word76],
    [word16, word20, word32, word51, word64, word72, word76],
    [word16, word20, word32, word56, word64, word76],
    [word16, word20, word58, word64, word72, word76, word85],
    [word20, word32, word64, word72, word76, word82],
    [word32, word58, word64, word72, word76, word82]]

def bucket7_6 : List (List Sig) := [[word2, word16, word32, word58, word64, word72, word76],
    [word3, word16, word20, word32, word64, word72, word76],
    [word3, word16, word32, word58, word64, word72, word76],
    [word16, word20, word25, word32, word36, word64, word76],
    [word20, word27, word32, word64, word72, word76],
    [word20, word32, word64, word72, word76, word77]]

def bucket7_7 : List (List Sig) := [[word2, word16, word20, word25, word32, word64, word72, word76],
    [word2, word16, word20, word32, word43, word64, word72, word76],
    [word3, word15, word20, word32, word64, word72, word76],
    [word9, word16, word20, word32, word64, word72, word76],
    [word9, word16, word32, word58, word64, word72, word76],
    [word13, word20, word32, word40, word72, word76],
    [word16, word20, word25, word32, word48, word64, word76],
    [word16, word20, word32, word33, word64, word72, word76],
    [word16, word20, word32, word43, word48, word64, word76],
    [word16, word20, word32, word48, word72, word76, word83],
    [word16, word20, word32, word64, word70, word72, word76],
    [word20, word32, word46, word64, word72, word76]]

def bucket7_8 : List (List Sig) := [[word3, word16, word20, word32, word36, word64, word76],
    [word3, word16, word20, word32, word59, word64, word72],
    [word3, word20, word32, word64, word72, word76, word82],
    [word16, word20, word32, word56, word64, word72, word76],
    [word16, word32, word36, word58, word64, word72, word76],
    [word16, word32, word58, word64, word72, word76, word79],
    [word20, word23, word32, word64, word72, word76, word82],
    [word20, word32, word58, word64, word72, word76, word82],
    [word20, word32, word60, word64, word72, word76]]

def bucket7_9 : List (List Sig) := [[word3, word16, word20, word23, word32, word64, word72, word76],
    [word3, word16, word20, word32, word48, word64, word76],
    [word3, word16, word20, word32, word58, word64, word72, word76],
    [word16, word20, word25, word32, word64, word72, word76, word79],
    [word16, word20, word32, word48, word64, word72, word76],
    [word16, word20, word32, word54, word72, word76],
    [word16, word32, word48, word58, word64, word72, word76],
    [word20, word32, word40, word64, word72, word76],
    [word32, word40, word58, word64, word72, word76]]

def bucket7_10 : List (List Sig) := [[word2, word16, word20, word23, word32, word72, word76],
    [word15, word20, word32, word48, word64, word72, word76],
    [word16, word20, word32, word52, word64, word72, word76],
    [word16, word20, word32, word57, word64, word72, word76],
    [word16, word32, word36, word64, word72, word76, word79],
    [word16, word32, word39, word64, word72, word76],
    [word20, word28, word32, word64, word72, word82],
    [word20, word30, word32, word64, word72, word76],
    [word20, word32, word36, word64, word72, word76, word82]]

def bucket7_11 : List (List Sig) := [[word2, word11, word16, word20, word32, word72],
    [word3, word16, word20, word28, word32, word64, word72],
    [word3, word16, word20, word32, word64, word74, word76],
    [word5, word16, word20, word32, word64, word72, word76],
    [word7, word16, word20, word32, word64, word72],
    [word16, word20, word23, word32, word36, word64, word72, word76],
    [word16, word20, word32, word36, word48, word64, word76],
    [word20, word32, word48, word64, word72, word76, word82],
    [word20, word32, word64, word69, word72, word82],
    [word20, word32, word64, word71, word72, word76]]

def bucket7_12 : List (List Sig) := [[word0, word20, word32, word64, word72, word76],
    [word3, word16, word20, word32, word64, word75, word76],
    [word3, word20, word32, word40, word64, word72, word76],
    [word6, word16, word20, word32, word64, word72, word76],
    [word16, word20, word32, word48, word58, word64, word72, word76],
    [word16, word32, word34, word58, word64, word72, word76],
    [word20, word32, word40, word58, word64, word72, word76]]

def bucket7_13 : List (List Sig) := [[word2, word16, word20, word32, word48, word72, word76],
    [word3, word10, word16, word20, word32, word64, word76],
    [word16, word20, word23, word32, word48, word72, word76],
    [word16, word20, word25, word32, word34, word64, word72, word76],
    [word16, word20, word32, word64, word72, word76, word78],
    [word16, word20, word32, word64, word72, word76, word86],
    [word16, word25, word58, word64, word72, word76],
    [word16, word32, word58, word64, word72, word76, word86],
    [word20, word23, word32, word40, word72, word76]]

def bucket7_14 : List (List Sig) := [[word1, word3, word20, word32, word64, word72, word76],
    [word3, word16, word20, word32, word38, word64, word72],
    [word3, word20, word32, word64, word72, word82],
    [word12, word16, word20, word32, word64, word72, word76],
    [word12, word16, word32, word58, word64, word72, word76],
    [word16, word20, word32, word48, word64, word74, word76],
    [word16, word20, word32, word50, word64, word72, word76],
    [word16, word20, word35, word64, word72, word76],
    [word16, word24, word32, word64, word72, word76],
    [word16, word32, word34, word36, word64, word72, word76],
    [word17, word20, word32, word64, word72, word76],
    [word19, word32, word64, word72, word76, word82],
    [word20, word32, word36, word40, word64, word72, word76],
    [word20, word32, word45, word64, word72, word76]]

def bucket7_15 : List (List Sig) := [[word2, word3, word16, word20, word32, word64, word72],
    [word2, word16, word20, word32, word64, word72, word75, word76],
    [word3, word16, word19, word32, word64, word72, word76],
    [word16, word20, word21, word32, word64, word72, word76],
    [word16, word20, word32, word36, word64, word72, word76, word85],
    [word16, word20, word32, word48, word64, word75, word76],
    [word16, word20, word32, word53, word64, word72, word76],
    [word16, word20, word32, word61, word64, word72, word76],
    [word16, word23, word58, word64, word72, word76],
    [word20, word32, word40, word48, word64, word72, word76]]

def bucket7_16 : List (List Sig) := [[word16, word20, word23, word25, word64, word72, word76],
    [word16, word20, word23, word32, word34, word72, word76],
    [word16, word20, word25, word58, word64, word72, word76],
    [word16, word20, word32, word48, word64, word72, word76, word85],
    [word20, word32, word40, word48, word72, word76],
    [word20, word32, word40, word64, word72, word76, word85],
    [word20, word32, word64, word72, word76, word81]]

def bucketTier7 : List (List (List Sig)) := [bucket7_0, bucket7_1, bucket7_2, bucket7_3, bucket7_4, bucket7_5, bucket7_6, bucket7_7, bucket7_8, bucket7_9, bucket7_10, bucket7_11, bucket7_12, bucket7_13, bucket7_14, bucket7_15, bucket7_16]

def bucket8_0 : List (List Sig) := [[word13, word16, word20, word32, word64, word72, word76],
    [word16, word20, word32, word64, word72, word73, word76],
    [word16, word20, word32, word64, word72, word76, word83],
    [word16, word20, word32, word64, word72, word76, word84]]

def bucket8_1 : List (List Sig) := [[word11, word16, word20, word32, word64, word72, word76],
    [word16, word20, word32, word64, word68, word72, word76],
    [word16, word20, word32, word64, word72, word76, word82]]

def bucket8_2 : List (List Sig) := [[word16, word20, word28, word32, word64, word72, word76]]

def bucket8_3 : List (List Sig) := [[word16, word20, word32, word64, word69, word72, word76],
    [word16, word32, word58, word64, word72, word76]]

def bucket8_4 : List (List Sig) := [[word15, word20, word32, word64, word72, word76],
    [word16, word20, word25, word32, word64, word72, word76],
    [word16, word20, word32, word43, word64, word72, word76]]

def bucket8_5 : List (List Sig) := [[word16, word20, word32, word38, word64, word72, word76],
    [word16, word20, word32, word40, word64, word72, word76],
    [word16, word20, word32, word44, word64, word72, word76],
    [word20, word32, word64, word72, word76, word82]]

def bucket8_6 : List (List Sig) := [[word2, word16, word20, word32, word64, word72, word76],
    [word3, word16, word20, word32, word64, word72, word76],
    [word16, word20, word23, word32, word64, word72, word76],
    [word16, word20, word32, word58, word64, word72, word76]]

def bucket8_7 : List (List Sig) := []

def bucket8_8 : List (List Sig) := [[word16, word20, word32, word36, word64, word72, word76],
    [word16, word20, word32, word64, word72, word76, word79]]

def bucket8_9 : List (List Sig) := [[word16, word20, word32, word48, word64, word72, word76],
    [word20, word32, word40, word64, word72, word76]]

def bucket8_10 : List (List Sig) := [[word16, word20, word32, word64, word72, word76, word85]]

def bucket8_11 : List (List Sig) := [[word1, word20, word32, word64, word72, word76],
    [word16, word20, word32, word64, word72, word74, word76]]

def bucket8_12 : List (List Sig) := [[word16, word19, word32, word64, word72, word76],
    [word16, word20, word32, word34, word64, word72, word76],
    [word16, word20, word32, word64, word72, word75, word76]]

def bucket8_13 : List (List Sig) := [[word10, word16, word20, word32, word64, word72, word76]]

def bucket8_14 : List (List Sig) := [[word8, word16, word20, word32, word64, word72, word76],
    [word16, word20, word32, word64, word66, word72, word76]]

def bucket8_15 : List (List Sig) := [[word16, word20, word32, word64, word65, word72, word76]]

def bucket8_16 : List (List Sig) := [[word16, word20, word32, word59, word64, word72, word76],
    [word16, word20, word32, word64, word72, word76, word87]]

def bucketTier8 : List (List (List Sig)) := [bucket8_0, bucket8_1, bucket8_2, bucket8_3, bucket8_4, bucket8_5, bucket8_6, bucket8_7, bucket8_8, bucket8_9, bucket8_10, bucket8_11, bucket8_12, bucket8_13, bucket8_14, bucket8_15, bucket8_16]

def bucket9_0 : List (List Sig) := []

def bucket9_1 : List (List Sig) := []

def bucket9_2 : List (List Sig) := []

def bucket9_3 : List (List Sig) := [[word16, word20, word32, word64, word72, word76]]

def bucket9_4 : List (List Sig) := []

def bucket9_5 : List (List Sig) := []

def bucket9_6 : List (List Sig) := []

def bucket9_7 : List (List Sig) := []

def bucket9_8 : List (List Sig) := []

def bucket9_9 : List (List Sig) := []

def bucket9_10 : List (List Sig) := []

def bucket9_11 : List (List Sig) := []

def bucket9_12 : List (List Sig) := []

def bucket9_13 : List (List Sig) := []

def bucket9_14 : List (List Sig) := []

def bucket9_15 : List (List Sig) := []

def bucket9_16 : List (List Sig) := []

def bucketTier9 : List (List (List Sig)) := [bucket9_0, bucket9_1, bucket9_2, bucket9_3, bucket9_4, bucket9_5, bucket9_6, bucket9_7, bucket9_8, bucket9_9, bucket9_10, bucket9_11, bucket9_12, bucket9_13, bucket9_14, bucket9_15, bucket9_16]

def buckets : ℕ → List (List (List Sig))
  | 1 => bucketTier1
  | 2 => bucketTier2
  | 3 => bucketTier3
  | 4 => bucketTier4
  | 5 => bucketTier5
  | 6 => bucketTier6
  | 7 => bucketTier7
  | 8 => bucketTier8
  | 9 => bucketTier9
  | _ => []


def tiers (n : ℕ) : List (List Sig) := (buckets n).flatten

def hashBucket (w : List Sig) : Nat :=
  (w.foldl (fun s a => s + a.1 * 31 + a.2 * 11) 0) % 17

def bucketHas (w : List Sig) : List (List (List Sig)) → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b.contains w
  | _ :: bs, i + 1 => bucketHas w bs i

lemma bucketHas_sound (w : List Sig) (v : List (List (List Sig))) (i : Nat)
    (h : bucketHas w v i = true) : w ∈ v.flatten := by
  induction v generalizing i with
  | nil => simp [bucketHas] at h
  | cons b v ih =>
    cases i with
    | zero =>
      have mem : w ∈ b := List.contains_iff_mem.mp (by simpa [bucketHas] using h)
      exact List.mem_flatten.mpr ⟨b, by simp, mem⟩
    | succ i =>
      have mem : w ∈ v.flatten := ih i (by simpa [bucketHas] using h)
      obtain ⟨bs, hs, hw⟩ := List.mem_flatten.mp mem
      exact List.mem_flatten.mpr ⟨bs, by simp [hs], hw⟩

def tierHas (n : Nat) (w : List Sig) : Bool := bucketHas w (buckets n) (hashBucket w)

lemma tierHas_sound {n : Nat} {w : List Sig} (h : tierHas n w = true) : w ∈ tiers n :=
  bucketHas_sound w _ _ h

def sigKey (s : Sig) := s.1 * 2^16 + s.2

def insertSignal (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b :: bs => if sigKey a ≤ sigKey b then a :: b :: bs else b :: insertSignal a bs

def sortSignals : List Sig → List Sig
  | [] => []
  | a :: bs => insertSignal a (sortSignals bs)

lemma insertSignalPerm (a : Sig) (w : List Sig) : (insertSignal a w).Perm (a :: w) := by
  induction w with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : sigKey a ≤ sigKey b
    · simp [insertSignal, h]
    · exact (by simpa [insertSignal, h] using (List.Perm.cons b ih).trans (.swap a b bs))

lemma sortPerm (l : List Sig) : (sortSignals l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertSignalPerm a (sortSignals bs)).trans (.cons a ih)

lemma sortFinset (l : List Sig) : (sortSignals l).toFinset = l.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (sortPerm l).mem_iff (a := a)

lemma liveCard {n : ℕ} {S : Finset Sig} (live : BL n S) : S.card ≤ n + 1 := by
  induction live with
  | stop => simp
  | @step k U a b d s t ha hb ca cb hab fresh tail ih =>
    have hr : blend d s t a b ∉ U := by
      intro mem
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    rw [Finset.card_insert_of_notMem hr] at ih
    have ha := Finset.card_insert_le (s := insert b U) (a := a)
    have hb := Finset.card_insert_le (s := U) (a := b)
    omega

def absent (n : ℕ) (w : List Sig) : Bool :=
  decide (w.length ≤ n + 1) && QuickQ.test chart true (n + 2 - w.length) w &&
    !tierHas n (sortSignals w)


section
open QuickQ ColorSearch1868 FreeSearch1868 Cuts1868
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
  let g:=PEqualNP.Outside.L_meta_10472.Board1868.mult s
  (g.1 &&& roof c)==roof c && color k (s.map (shade c (g.1 ^^^ g.2)))
lemma rowsMap (c d k v) : testRows c k (v.map (diff c d))=test c d k v := by
  simp only [testRows,test,signs,colorEq,funext (shadeEq _ _)]
end PaintQ

open PaintQ
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
lemma forkSMap (c k hit v a b) :
    forkS c k hit (v.map (diff c true)) v (diff c true a) (diff c true b)=pairB v (plain c true k hit) a b := by
  simp only [forkS,pairB,oneB,choicesMap];rfl
lemma scanMap {α β : Type} (f : α→β) (u : β→β→Bool) (g : α→α→Bool)
    (all : ∀a b,u (f a) (f b)=g a b) (v : List α) :
    scanPairs u (v.map f)=scanPairs g v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [scanPairs,List.any_map,Function.comp_def,all,ih]
end PackQ

open PackQ
open Board1868 (mult)
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
end GroupQ

end


def rowFast (n : ℕ) (v : List Sig) : Bool :=
  let ws := v.map (QuickQ.diff chart true)
  !(baseTest v || scanPairs (GroupQ.fork chart true n (fun w => tierHas n (sortSignals w)) v ws) ws)

lemma rowFast_eq (n : ℕ) (v : List Sig) :
    rowFast n v = !(baseTest v || scanPairs (pairB v (absent n)) v) := by
  let ws := v.map (QuickQ.diff chart true)
  let code := fun w => tierHas n (sortSignals w)
  have e : GroupQ.fork chart true n code v ws = PackQ.forkS chart n code ws v := by
    funext a b
    exact GroupQ.forkSEQ chart n code v ws a b
  unfold rowFast
  change (!(baseTest v || scanPairs (GroupQ.fork chart true n code v ws) ws)) = _
  rw [e]
  rw [show ws = v.map (QuickQ.diff chart true) from rfl]
  rw [PackQ.scanMap _ _ _ (PackQ.forkSMap _ _ _ _)]
  rfl

def checkRows (n : ℕ) (rs : List (List Sig)) := rs.all (rowFast n)

def checkTier (n : ℕ) := checkRows n (tiers (n+1))

def verified (n : ℕ) := ∀ v ∈ tiers n, v.Nodup → ∀ k ≤ n, ¬ BL k v.toFinset

lemma verificationStart : verified 0 := by simp [verified, tiers, buckets]

lemma verificationStep {n} (previous : verified n) (checked : checkTier n = true) :
    verified (n+1) := by
  intro v vr nd k lim live
  have hnext : ∀ w : List Sig, w.Nodup → ∀ j ≤ n, BL j w.toFinset → absent n w = true := by
    intro w wn j bound hw
    have notFound : sortSignals w ∉ tiers n := by
      intro mem
      have equiv : (sortSignals w).toFinset = w.toFinset := sortFinset w
      exact previous _ mem ((sortPerm w).nodup_iff.mpr wn) j bound (equiv.symm ▸ hw)
    have length : w.length ≤ n + 1 := by
      have card := liveCard hw
      rw [List.toFinset_card_of_nodup wn] at card
      omega
    have miss : tierHas n (sortSignals w) = false := by
      cases hit : tierHas n (sortSignals w) with
      | false => rfl
      | true => exact (notFound (tierHas_sound hit)).elim
    simpa [absent, length, QuickQ.testSigned chart_valid bound wn hw] using miss
  have reach := oneStep live n lim v nd rfl (absent n) hnext
  have fast : rowFast n v = true := List.all_eq_true.mp checked v vr
  have fail := (rowFast_eq n v).symm.trans fast
  change !(baseTest v || scanPairs (pairB v (absent n)) v) = true at fail
  simp [reach] at fail

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma level1 : checkTier 0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma level2 : checkTier 1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma level3 : checkTier 2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_0 : checkRows 3 bucket4_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_1 : checkRows 3 bucket4_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_2 : checkRows 3 bucket4_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_3 : checkRows 3 bucket4_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_4 : checkRows 3 bucket4_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_5 : checkRows 3 bucket4_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_6 : checkRows 3 bucket4_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_7 : checkRows 3 bucket4_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_8 : checkRows 3 bucket4_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_9 : checkRows 3 bucket4_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_10 : checkRows 3 bucket4_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_11 : checkRows 3 bucket4_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_12 : checkRows 3 bucket4_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_13 : checkRows 3 bucket4_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_14 : checkRows 3 bucket4_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_15 : checkRows 3 bucket4_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part4_16 : checkRows 3 bucket4_16 = true := by decide +kernel
lemma level4 : checkTier 3 = true := by
  have h : bucketTier4.all (checkRows 3) = true := by
    simp only [bucketTier4, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part4_0, part4_1, part4_2, part4_3, part4_4, part4_5, part4_6, part4_7, part4_8, part4_9, part4_10, part4_11, part4_12, part4_13, part4_14, part4_15, part4_16] 
  change checkRows 3 bucketTier4.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_0 : checkRows 4 bucket5_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_1 : checkRows 4 bucket5_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_2 : checkRows 4 bucket5_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_3 : checkRows 4 bucket5_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_4 : checkRows 4 bucket5_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_5 : checkRows 4 bucket5_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_6 : checkRows 4 bucket5_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_7 : checkRows 4 bucket5_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_8 : checkRows 4 bucket5_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_9 : checkRows 4 bucket5_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_10 : checkRows 4 bucket5_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_11 : checkRows 4 bucket5_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_12 : checkRows 4 bucket5_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_13 : checkRows 4 bucket5_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_14 : checkRows 4 bucket5_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_15 : checkRows 4 bucket5_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part5_16 : checkRows 4 bucket5_16 = true := by decide +kernel
lemma level5 : checkTier 4 = true := by
  have h : bucketTier5.all (checkRows 4) = true := by
    simp only [bucketTier5, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part5_0, part5_1, part5_2, part5_3, part5_4, part5_5, part5_6, part5_7, part5_8, part5_9, part5_10, part5_11, part5_12, part5_13, part5_14, part5_15, part5_16] 
  change checkRows 4 bucketTier5.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_0 : checkRows 5 bucket6_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_1 : checkRows 5 bucket6_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_2 : checkRows 5 bucket6_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_3 : checkRows 5 bucket6_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_4 : checkRows 5 bucket6_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_5 : checkRows 5 bucket6_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_6 : checkRows 5 bucket6_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_7 : checkRows 5 bucket6_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_8 : checkRows 5 bucket6_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_9 : checkRows 5 bucket6_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_10 : checkRows 5 bucket6_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_11 : checkRows 5 bucket6_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_12 : checkRows 5 bucket6_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_13 : checkRows 5 bucket6_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_14 : checkRows 5 bucket6_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_15 : checkRows 5 bucket6_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part6_16 : checkRows 5 bucket6_16 = true := by decide +kernel
lemma level6 : checkTier 5 = true := by
  have h : bucketTier6.all (checkRows 5) = true := by
    simp only [bucketTier6, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part6_0, part6_1, part6_2, part6_3, part6_4, part6_5, part6_6, part6_7, part6_8, part6_9, part6_10, part6_11, part6_12, part6_13, part6_14, part6_15, part6_16] 
  change checkRows 5 bucketTier6.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_0 : checkRows 6 bucket7_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_1 : checkRows 6 bucket7_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_2 : checkRows 6 bucket7_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_3 : checkRows 6 bucket7_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_4 : checkRows 6 bucket7_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_5 : checkRows 6 bucket7_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_6 : checkRows 6 bucket7_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_7 : checkRows 6 bucket7_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_8 : checkRows 6 bucket7_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_9 : checkRows 6 bucket7_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_10 : checkRows 6 bucket7_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_11 : checkRows 6 bucket7_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_12 : checkRows 6 bucket7_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_13 : checkRows 6 bucket7_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_14 : checkRows 6 bucket7_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_15 : checkRows 6 bucket7_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part7_16 : checkRows 6 bucket7_16 = true := by decide +kernel
lemma level7 : checkTier 6 = true := by
  have h : bucketTier7.all (checkRows 6) = true := by
    simp only [bucketTier7, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part7_0, part7_1, part7_2, part7_3, part7_4, part7_5, part7_6, part7_7, part7_8, part7_9, part7_10, part7_11, part7_12, part7_13, part7_14, part7_15, part7_16] 
  change checkRows 6 bucketTier7.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_0 : checkRows 7 bucket8_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_1 : checkRows 7 bucket8_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_2 : checkRows 7 bucket8_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_3 : checkRows 7 bucket8_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_4 : checkRows 7 bucket8_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_5 : checkRows 7 bucket8_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_6 : checkRows 7 bucket8_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_7 : checkRows 7 bucket8_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_8 : checkRows 7 bucket8_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_9 : checkRows 7 bucket8_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_10 : checkRows 7 bucket8_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_11 : checkRows 7 bucket8_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_12 : checkRows 7 bucket8_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_13 : checkRows 7 bucket8_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_14 : checkRows 7 bucket8_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_15 : checkRows 7 bucket8_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part8_16 : checkRows 7 bucket8_16 = true := by decide +kernel
lemma level8 : checkTier 7 = true := by
  have h : bucketTier8.all (checkRows 7) = true := by
    simp only [bucketTier8, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part8_0, part8_1, part8_2, part8_3, part8_4, part8_5, part8_6, part8_7, part8_8, part8_9, part8_10, part8_11, part8_12, part8_13, part8_14, part8_15, part8_16] 
  change checkRows 7 bucketTier8.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_0 : checkRows 8 bucket9_0 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_1 : checkRows 8 bucket9_1 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_2 : checkRows 8 bucket9_2 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_3 : checkRows 8 bucket9_3 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_4 : checkRows 8 bucket9_4 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_5 : checkRows 8 bucket9_5 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_6 : checkRows 8 bucket9_6 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_7 : checkRows 8 bucket9_7 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_8 : checkRows 8 bucket9_8 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_9 : checkRows 8 bucket9_9 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_10 : checkRows 8 bucket9_10 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_11 : checkRows 8 bucket9_11 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_12 : checkRows 8 bucket9_12 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_13 : checkRows 8 bucket9_13 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_14 : checkRows 8 bucket9_14 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_15 : checkRows 8 bucket9_15 = true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma part9_16 : checkRows 8 bucket9_16 = true := by decide +kernel
lemma level9 : checkTier 8 = true := by
  have h : bucketTier9.all (checkRows 8) = true := by
    simp only [bucketTier9, List.all_cons, List.all_nil, Bool.and_self, Bool.true_and, part9_0, part9_1, part9_2, part9_3, part9_4, part9_5, part9_6, part9_7, part9_8, part9_9, part9_10, part9_11, part9_12, part9_13, part9_14, part9_15, part9_16] 
  change checkRows 8 bucketTier9.flatten = true
  unfold checkRows at h ⊢
  rw [List.all_flatten]
  exact h
lemma tables_checked : verified 9 :=
  verificationStep (verificationStep (verificationStep (verificationStep (verificationStep (verificationStep (verificationStep (verificationStep (verificationStep (verificationStart) level1) level2) level3) level4) level5) level6) level7) level8) level9

lemma minorChecked {k} (lim : k ≤ 9) : ¬ BL k minorRaw.toFinset := by
  intro live
  have sortedPresent : sortSignals minorRaw ∈ tiers 9 := by decide +kernel
  have e := sortFinset minorRaw
  exact tables_checked _ sortedPresent ((sortPerm minorRaw).nodup_iff.mpr minorND)
    k lim (e.symm ▸ live)

lemma binary_lower (C : Circuit) (legal : FanInTwo C)
    (spec : ∀x, C.eval (List.ofFn x) = edge x) : 11 ≤ C.gates.countP costly := by
  obtain ⟨k,t,S,cap,run,sub⟩ := tagExtract C.gates raw8 vals legal (output8 legal spec)
  have e : S = raw8.toFinset := allNeeded run
    (fun a ha => List.mem_toFinset.mpr (sub a ha)) need_full
  obtain ⟨q,le,j,r,T,cap',h,ss⟩ := Projection8403.projected run omitLeaf
  obtain ⟨a,V,le',pv,sv⟩ := compress h
  have incl : V ⊆ insert zero minorRaw.toFinset :=
    (sv.trans (Finset.image_mono _ ss)).trans (e.symm ▸ minorImage)
  have incl' : V ⊆ minorRaw.toFinset := by
    intro b hb
    exact (Finset.mem_insert.mp (incl hb)).resolve_left (pv.forms b hb).1.2.1
  obtain ⟨z,zrun⟩ := pv.expand
  have eq := allNeeded zrun incl' need_minor
  by_contra! small
  have nine : a ≤ 9 := by
    rw [e] at le
    have m := massLeaf
    omega
  exact minorChecked nine (eq ▸ pv)

def witness : Circuit :=
  ⟨[⟨.or, [4, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [7, 13]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 16]⟩], 18⟩
lemma witness_fan : ∀g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma witness_eval (x : Fin 7 → Bool) : witness.eval (List.ofFn x) = edge x := by
  revert x
  decide +kernel

def flatEdges : List ℕ := [0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6]
def tableEdge (x : Fin 7 → Bool) : Bool := decide (∃ i < flatEdges.length / 2,
  (List.ofFn x).getD (flatEdges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (flatEdges.getD (2*i+1) 0) false = true)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma table_match : ∀x, tableEdge x = edge x := by decide +kernel
lemma replacement (gs : List Gate) (o : ℕ)
    (legal : FanInTwo (⟨gs,o⟩ : Circuit))
    (spec : ∀x, (⟨gs,o⟩ : Circuit).eval (List.ofFn x) = tableEdge x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gs.length ∧ ∀ x, (⟨gates',o'⟩ : Circuit).eval (List.ofFn x) = tableEdge x := by
  by_cases n : ∃ g ∈ gs, g.op = .not
  · have lower := binary_lower ⟨gs,o⟩ legal (fun x => (spec x).trans (table_match x))
    change 11 ≤ gs.countP costly at lower
    have strict : gs.countP costly < gs.length := by
      have le := List.countP_le_length (p := costly) (l := gs)
      by_contra! opp
      have all := List.countP_eq_length.mp (Nat.le_antisymm le opp)
      obtain ⟨g,hg,ho⟩ := n
      simpa [costly,ho] using all g hg
    refine ⟨witness.gates,witness.output,witness_fan,?_ ,?_⟩
    · simpa [witness] using (show 12 ≤ gs.length by omega)
    · intro x
      exact (witness_eval x).trans (table_match x).symm
  · refine ⟨gs,o,?_ ,le_rfl,spec⟩
    intro g hg
    have h := legal g hg
    refine ⟨?_ , h.2⟩
    rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not from h.1) with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (n ⟨g,hg,c⟩).elim

end PEqualNP.Outside.L_meta_10472
theorem PEqualNP.Outside.L_meta_10472 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ spec
  exact PEqualNP.Outside.L_meta_10472.replacement gates o (fun g hg => ⟨show
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)
      from (legal g hg).1, (legal g hg).2⟩) spec
