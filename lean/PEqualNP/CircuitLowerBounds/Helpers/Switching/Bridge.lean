import Mathlib
import PEqualNP.Defs

/-!
# From gate lists to a graded family of Boolean functions

STATUS: a helper. Nothing here is a recorded lemma; it is checked only when a lemma that rests
on it is.

A circuit of our model (a list of AND, OR and NOT gates reading wire indices) on `n` inputs is
described by a list of pairs (grade, function): two entries per wire (the wire's function and
its negation) and the two constants. Grade `0` entries are constants and literals; an entry of
grade `k ≥ 1` is the AND or the OR of a list of entries of smaller grade, as long as the fan-in
bound. The list is closed under negation (de Morgan), the grade of a wire is at most its depth
in the model (NOT gates cost no grade), and the output entry computes the circuit.

Corner cases of the model, all covered: a gate that reads a wire that does not exist yet reads
`false` at depth `0` (here: the constant `false`, grade `0`); a NOT gate reads only its first
input and is `true` on no inputs; an output index out of range gives `false` and depth `0`.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Bridge

open PEqualNP.CircuitLowerBounds

/-- Boolean functions of `n` variables. -/
abbrev BF (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- An entry: a grade and a function. -/
abbrev Entry (n : ℕ) : Type := ℕ × BF n

/-- The negated entry, at the same grade. -/
def negp {n : ℕ} (q : Entry n) : Entry n := (q.1, fun x => !q.2 x)

/-- The entry of a wire that does not exist: the constant `false` at grade `0`. -/
def dflt {n : ℕ} : Entry n := (0, fun _ => false)

/-- Constants and literals. -/
def IsBase {n : ℕ} (f : BF n) : Prop :=
  (∃ b : Bool, f = fun _ => b) ∨ ∃ i : Fin n, f = (fun x => x i) ∨ f = fun x => !x i

/-- The AND of the functions of a list of entries. -/
def allOf {n : ℕ} (l : List (Entry n)) : BF n := fun x => l.all fun q => q.2 x

/-- The OR of the functions of a list of entries. -/
def anyOf {n : ℕ} (l : List (Entry n)) : BF n := fun x => l.any fun q => q.2 x

/-- The entry `p` is well formed relative to the family `S` with fan-in bound `B`: grade `0`
and a constant or literal, or positive grade and the AND or OR of at most `B` entries of `S` of
smaller grade. -/
def Ok {n : ℕ} (B : ℕ) (S : List (Entry n)) (p : Entry n) : Prop :=
  (p.1 = 0 ∧ IsBase p.2) ∨
    (0 < p.1 ∧ ∃ l : List (Entry n), l.length ≤ B ∧ (∀ q ∈ l, q ∈ S ∧ q.1 < p.1) ∧
      (p.2 = allOf l ∨ p.2 = anyOf l))

/-- The family of a list of wire entries: the two constants, then each entry and its negation. -/
def fam {n : ℕ} (W : List (Entry n)) : List (Entry n) :=
  (0, fun _ => false) :: (0, fun _ => true) :: W.flatMap fun p => [p, negp p]

/-- The grade of a new gate over the wire entries `W`. -/
def stepGrade {n : ℕ} (W : List (Entry n)) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => (W.getD i dflt).1).foldr max 0 + 1
  | GateOp.or => (g.inputs.map fun i => (W.getD i dflt).1).foldr max 0 + 1
  | GateOp.not => (match g.inputs with
      | [] => 0
      | i :: _ => (W.getD i dflt).1)
  | _ => 0

/-- The entry of a new gate over the wire entries `W`. -/
def stepW {n : ℕ} (W : List (Entry n)) (g : Gate) : Entry n :=
  (stepGrade W g, fun x => g.op.eval (g.inputs.map fun i => (W.getD i dflt).2 x))

/-- The wire entries after the gates `gs`, from the entries `W`. -/
def buildFrom {n : ℕ} (gs : List Gate) (W : List (Entry n)) : List (Entry n) :=
  gs.foldl (fun W g => W ++ [stepW W g]) W

/-- The entries of the input wires. -/
def inputEntries (n : ℕ) : List (Entry n) := List.ofFn fun i : Fin n => (0, fun x => x i)

/-! ## Small facts -/

theorem negp_negp {n : ℕ} (q : Entry n) : negp (negp q) = q := by
  rcases q with ⟨k, f⟩
  simp [negp]

theorem isBase_neg {n : ℕ} {f : BF n} (h : IsBase f) : IsBase fun x => !f x := by
  rcases h with ⟨b, rfl⟩ | ⟨i, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨i, Or.inr rfl⟩
  · exact Or.inr ⟨i, Or.inl (by funext x; simp)⟩

theorem not_all {α : Type} (l : List α) (f : α → Bool) :
    (!l.all f) = l.any fun a => !f a := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, List.any_cons, Bool.not_and, ih]

theorem not_any {α : Type} (l : List α) (f : α → Bool) :
    (!l.any f) = l.all fun a => !f a := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, List.any_cons, Bool.not_or, ih]

theorem le_foldr_max (l : List ℕ) {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem foldr_max_map_le {α : Type} (l : List α) (f h : α → ℕ) (hl : ∀ a ∈ l, f a ≤ h a) :
    (l.map f).foldr max 0 ≤ (l.map h).foldr max 0 := by
  induction l with
  | nil => exact le_rfl
  | cons a t ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))

theorem ok_mono {n B : ℕ} {S S' : List (Entry n)} (h : ∀ q ∈ S, q ∈ S') {p : Entry n}
    (hp : Ok B S p) : Ok B S' p := by
  rcases hp with hp | ⟨hk, l, hl, hq, hf⟩
  · exact Or.inl hp
  · exact Or.inr ⟨hk, l, hl, fun q hql => ⟨h q (hq q hql).1, (hq q hql).2⟩, hf⟩

theorem mem_fam {n : ℕ} {W : List (Entry n)} {q : Entry n} :
    q ∈ fam W ↔ q = (0, fun _ => false) ∨ q = (0, fun _ => true) ∨
      ∃ p ∈ W, q = p ∨ q = negp p := by
  simp [fam, List.mem_flatMap]

theorem fam_mono {n : ℕ} (W : List (Entry n)) (p : Entry n) :
    ∀ q ∈ fam W, q ∈ fam (W ++ [p]) := by
  intro q hq
  rw [mem_fam] at hq ⊢
  rcases hq with h | h | ⟨r, hr, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨r, by simp [hr], h⟩)

theorem negp_mem_fam {n : ℕ} {W : List (Entry n)} {q : Entry n} (hq : q ∈ fam W) :
    negp q ∈ fam W := by
  rw [mem_fam] at hq ⊢
  rcases hq with rfl | rfl | ⟨r, hr, h | h⟩
  · exact Or.inr (Or.inl (by simp [negp]))
  · exact Or.inl (by simp [negp])
  · exact Or.inr (Or.inr ⟨r, hr, Or.inr (by rw [h])⟩)
  · exact Or.inr (Or.inr ⟨r, hr, Or.inl (by rw [h, negp_negp])⟩)

theorem getD_mem_fam {n : ℕ} (W : List (Entry n)) (i : ℕ) : W.getD i dflt ∈ fam W := by
  rw [mem_fam]
  by_cases h : i < W.length
  · refine Or.inr (Or.inr ⟨W[i], List.getElem_mem h, Or.inl ?_⟩)
    simp [List.getD_eq_getElem?_getD, h]
  · left
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 h), dflt]

theorem length_fam {n : ℕ} (W : List (Entry n)) : (fam W).length = 2 * W.length + 2 := by
  have : (W.flatMap fun p => [p, negp p]).length = 2 * W.length := by
    induction W with
    | nil => rfl
    | cons a t ih => simp [List.flatMap_cons, ih]; omega
  simp [fam, this]

/-! ## The invariant -/

/-- Every wire entry and its negation is well formed relative to the family. -/
def Inv {n : ℕ} (B : ℕ) (W : List (Entry n)) : Prop :=
  ∀ p ∈ W, Ok B (fam W) p ∧ Ok B (fam W) (negp p)

theorem inv_all {n B : ℕ} {W : List (Entry n)} (h : Inv B W) :
    ∀ q ∈ fam W, Ok B (fam W) q := by
  intro q hq
  rw [mem_fam] at hq
  rcases hq with rfl | rfl | ⟨r, hr, h' | h'⟩
  · exact Or.inl ⟨rfl, Or.inl ⟨false, rfl⟩⟩
  · exact Or.inl ⟨rfl, Or.inl ⟨true, rfl⟩⟩
  · rw [h']; exact (h r hr).1
  · rw [h']; exact (h r hr).2

theorem inv_input (n B : ℕ) : Inv B (inputEntries n) := by
  intro p hp
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
  exact ⟨Or.inl ⟨rfl, Or.inr ⟨i, Or.inl rfl⟩⟩, Or.inl ⟨rfl, Or.inr ⟨i, Or.inr rfl⟩⟩⟩

theorem step_ok {n B : ℕ} {W : List (Entry n)} (h : Inv B W) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hB : g.inputs.length ≤ B) :
    Ok B (fam W) (stepW W g) ∧ Ok B (fam W) (negp (stepW W g)) := by
  have hlt : ∀ i ∈ g.inputs,
      (W.getD i dflt).1 < (g.inputs.map fun i => (W.getD i dflt).1).foldr max 0 + 1 :=
    fun i hi => Nat.lt_succ_of_le (le_foldr_max _ (List.mem_map.2 ⟨i, hi, rfl⟩))
  rcases hop with hop | hop | hop
  · have hg : stepGrade W g = (g.inputs.map fun i => (W.getD i dflt).1).foldr max 0 + 1 := by
      simp [stepGrade, hop]
    constructor
    · refine Or.inr ⟨by simp [stepW, hg], g.inputs.map fun i => W.getD i dflt, by simpa using hB,
        ?_, Or.inl ?_⟩
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
        exact ⟨getD_mem_fam W i, by simpa [stepW, hg] using hlt i hi⟩
      · funext x
        simp [stepW, hop, GateOp.eval, allOf, List.all_map, Function.comp_def]
    · refine Or.inr ⟨by simp [stepW, negp, hg], g.inputs.map fun i => negp (W.getD i dflt),
        by simpa using hB, ?_, Or.inr ?_⟩
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
        exact ⟨negp_mem_fam (getD_mem_fam W i), by simpa [stepW, negp, hg] using hlt i hi⟩
      · funext x
        simp [stepW, negp, hop, GateOp.eval, anyOf, List.all_map, List.any_map,
          Function.comp_def, not_all]
  · have hg : stepGrade W g = (g.inputs.map fun i => (W.getD i dflt).1).foldr max 0 + 1 := by
      simp [stepGrade, hop]
    constructor
    · refine Or.inr ⟨by simp [stepW, hg], g.inputs.map fun i => W.getD i dflt, by simpa using hB,
        ?_, Or.inr ?_⟩
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
        exact ⟨getD_mem_fam W i, by simpa [stepW, hg] using hlt i hi⟩
      · funext x
        simp [stepW, hop, GateOp.eval, anyOf, List.any_map, Function.comp_def]
    · refine Or.inr ⟨by simp [stepW, negp, hg], g.inputs.map fun i => negp (W.getD i dflt),
        by simpa using hB, ?_, Or.inl ?_⟩
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
        exact ⟨negp_mem_fam (getD_mem_fam W i), by simpa [stepW, negp, hg] using hlt i hi⟩
      · funext x
        simp [stepW, negp, hop, GateOp.eval, allOf, List.all_map, List.any_map,
          Function.comp_def, not_any]
  · -- a NOT gate: its entry is the constant `true` or the negation of an entry of the family
    have key : stepW W g ∈ fam W := by
      cases hin : g.inputs with
      | nil =>
        have : stepW W g = (0, fun _ => true) := by
          simp [stepW, stepGrade, hop, hin, GateOp.eval]
        rw [this, mem_fam]; exact Or.inr (Or.inl rfl)
      | cons i t =>
        have : stepW W g = negp (W.getD i dflt) := by
          simp [stepW, stepGrade, hop, hin, GateOp.eval, negp]
        rw [this]; exact negp_mem_fam (getD_mem_fam W i)
    exact ⟨inv_all h _ key, inv_all h _ (negp_mem_fam key)⟩

theorem inv_step {n B : ℕ} {W : List (Entry n)} (h : Inv B W) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hB : g.inputs.length ≤ B) : Inv B (W ++ [stepW W g]) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact ⟨ok_mono (fam_mono W _) (h p hp).1, ok_mono (fam_mono W _) (h p hp).2⟩
  · rw [List.mem_singleton] at hp
    subst hp
    exact ⟨ok_mono (fam_mono W _) (step_ok h g hop hB).1,
      ok_mono (fam_mono W _) (step_ok h g hop hB).2⟩

theorem inv_build {n B : ℕ} (gs : List Gate) :
    ∀ W : List (Entry n), Inv B W →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ B) → Inv B (buildFrom gs W) := by
  induction gs with
  | nil => intro W h _; exact h
  | cons g t ih =>
    intro W h hg
    exact ih _ (inv_step h g (hg g (by simp)).1 (hg g (by simp)).2)
      fun g' hg' => hg g' (by simp [hg'])

theorem length_build {n : ℕ} (gs : List Gate) :
    ∀ W : List (Entry n), (buildFrom gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; rfl
  | cons g t ih =>
    intro W
    show (buildFrom t (W ++ [stepW W g])).length = _
    rw [ih]; simp; omega

/-! ## Correctness -/

theorem getD_snd {n : ℕ} (W : List (Entry n)) (x : Fin n → Bool) :
    ∀ i : ℕ, (W.map fun p => p.2 x).getD i false = (W.getD i dflt).2 x := by
  induction W with
  | nil => intro i; simp [dflt]
  | cons a t ih =>
    intro i
    cases i with
    | zero => simp
    | succ j => simpa using ih j

theorem build_wires {n : ℕ} (x : Fin n → Bool) (gs : List Gate) :
    ∀ W : List (Entry n), (buildFrom gs W).map (fun p => p.2 x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun p => p.2 x) := by
  induction gs with
  | nil => intro W; rfl
  | cons g t ih =>
    intro W
    show (buildFrom t (W ++ [stepW W g])).map _ = _
    rw [ih, List.foldl_cons]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, stepW, getD_snd]

/-! ## Grades against depths -/

theorem getD_fst_le {n : ℕ} {W : List (Entry n)} {D : List ℕ}
    (h : List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) W D) :
    ∀ i : ℕ, (W.getD i dflt).1 ≤ D.getD i 0 := by
  induction h with
  | nil => intro i; simp [dflt]
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ j => simpa using ih j

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} {b : β} (hab : R a b) :
    List.Forall₂ R (l ++ [a]) (l' ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons h1 ih

theorem stepGrade_le {n : ℕ} {W : List (Entry n)} {D : List ℕ}
    (h : List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) W D) (g : Gate) :
    stepGrade W g ≤ (g.inputs.map fun i => D.getD i 0).foldr max 0 + 1 := by
  have hm := foldr_max_map_le g.inputs (fun i => (W.getD i dflt).1) (fun i => D.getD i 0)
    fun i _ => getD_fst_le h i
  unfold stepGrade
  split
  · exact Nat.succ_le_succ hm
  · exact Nat.succ_le_succ hm
  · split
    · exact Nat.zero_le _
    · rename_i i t hin
      have h1 : (W.getD i dflt).1 ≤ D.getD i 0 := getD_fst_le h i
      have h2 : D.getD i 0 ≤ (g.inputs.map fun i => D.getD i 0).foldr max 0 :=
        le_foldr_max _ (List.mem_map.2 ⟨i, by simp [hin], rfl⟩)
      omega
  · exact Nat.zero_le _

theorem build_depths {n : ℕ} (gs : List Gate) :
    ∀ (W : List (Entry n)) (D : List ℕ),
      List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) W D →
      List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) (buildFrom gs W)
        (gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]) D) := by
  induction gs with
  | nil => intro W D h; exact h
  | cons g t ih =>
    intro W D h
    exact ih _ _ (forall₂_snoc h (stepGrade_le h g))

theorem input_depths (n : ℕ) :
    List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) (inputEntries n) (List.replicate n 0) := by
  have key : ∀ (W : List (Entry n)) (m : ℕ), W.length = m → (∀ p ∈ W, p.1 = 0) →
      List.Forall₂ (fun (p : Entry n) (d : ℕ) => p.1 ≤ d) W (List.replicate m 0) := by
    intro W
    induction W with
    | nil => intro m hm _; subst hm; exact List.Forall₂.nil
    | cons a t ih =>
      intro m hm h0
      subst hm
      rw [List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons (by simp [h0 a (by simp)]) (ih _ rfl fun p hp => h0 p (by simp [hp]))
  refine key _ _ (by simp [inputEntries]) ?_
  intro p hp
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
  rfl

/-! ## The layered description -/

/-- The layered description of a circuit of AND, OR and NOT gates on `n` inputs with fan-in at
most `B`: a list of at most `2 (n + size) + 2` graded functions, closed under negation, every
entry a constant or literal at grade `0` or the AND or OR of at most `B` entries of smaller
grade, with an output entry of grade at most the depth of the circuit that computes it. -/
theorem layered (C : Circuit) (n B : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ B) :
    ∃ (F : List (Entry n)) (out : Entry n),
      F.length ≤ 2 * (n + C.size) + 2 ∧ out ∈ F ∧ out.1 ≤ C.depth n ∧
      (∀ x : Fin n → Bool, out.2 x = C.eval (List.ofFn x)) ∧
      (∀ q ∈ F, negp q ∈ F) ∧ (∀ q ∈ F, Ok B F q) := by
  refine ⟨fam (buildFrom C.gates (inputEntries n)),
    (buildFrom C.gates (inputEntries n)).getD C.output dflt, ?_, getD_mem_fam _ _, ?_, ?_,
    fun q hq => negp_mem_fam hq, inv_all (inv_build C.gates _ (inv_input n B) hC)⟩
  · rw [length_fam, length_build]
    simp [inputEntries, Circuit.size]
  · exact getD_fst_le (build_depths C.gates _ _ (input_depths n)) C.output
  · intro x
    have h := build_wires x C.gates (inputEntries n)
    have h0 : (inputEntries n).map (fun p => p.2 x) = List.ofFn x := by
      simp [inputEntries, List.map_ofFn, Function.comp_def]
    rw [h0] at h
    show _ = (C.wires (List.ofFn x)).getD C.output false
    unfold Circuit.wires
    rw [← h, getD_snd]

/-- The same output entry on input lists: every list of length `n` is the list of values of
the assignment `i ↦ xs[i]`. -/
theorem ofFn_getD (n : ℕ) (xs : List Bool) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.getD i false) = xs := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h2]

end PEqualNP.CircuitLowerBounds.Switching.Bridge
