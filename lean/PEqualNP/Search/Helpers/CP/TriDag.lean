import PEqualNP.Defs.SearchCP
import Mathlib.Tactic

/-!
# Helpers: from cutting planes refutations to triangle dags

Helper module (proofs only). The falsified set of a cutting planes line is a triangle for
every split of the variables; the falsified set of a clause line is the set of points
falsifying the clause; every rule is sound pointwise. Hence the falsified sets of the lines
of a derivation, in the same order, form a triangle dag (Hrubes and Pudlak 2017; Sokolov
2017). The Boolean axioms have an empty falsified set, entered as a sink of any clause, so
the formula must be nonempty: a refutation forces that, by soundness.
-/

namespace PEqualNP.Search.Helpers.CP

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type}

/-- The falsified set of a line is a triangle for every split: the first player's partial
sum is below the constant minus the second player's partial sum. -/
theorem fals_isTri [Fintype V] (side : V → Bool) (e : CPLine V) :
    IsTri side {a | ¬ CPLine.Holds a e} := by
  refine ⟨fun x => ∑ v, if side v then e.1 v * (if x v then 1 else 0) else 0,
    fun y => e.2 - ∑ v, if side v then 0 else e.1 v * (if y v then 1 else 0), ?_, ?_, ?_⟩
  · intro x y
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : side v <;> simp [mix, h]
  · intro x y
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : side v <;> simp [mix, h]
  · intro x
    have hs : (∑ v, e.1 v * (if x v then 1 else 0))
        = (∑ v, if side v then e.1 v * (if x v then 1 else 0) else 0)
          + ∑ v, if side v then 0 else e.1 v * (if x v then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : side v <;> simp [h]
    simp only [Set.mem_ofPred_eq, CPLine.Holds, not_le]
    rw [hs]
    constructor <;> intro h <;> linarith

/-- The line of a clause holds exactly at the points satisfying the clause. -/
theorem clauseCP_holds_iff [Fintype V] [DecidableEq V] (a : V → Bool) (C : Clause V) :
    CPLine.Holds a (clauseCP C) ↔ ClauseSat a C := by
  have hsum : (∑ v, (∑ l ∈ C, if l.1 = v then (if l.2 then (1 : ℤ) else -1) else 0)
        * (if a v then 1 else 0))
      = ∑ l ∈ C, (if l.2 then (1 : ℤ) else -1) * (if a l.1 then 1 else 0) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.1]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hind : (∑ l ∈ C, (if l.2 then (1 : ℤ) else -1) * (if a l.1 then 1 else 0))
      + (∑ l ∈ C, if l.2 then (0 : ℤ) else 1) = ∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases l with ⟨v, b⟩
    cases b <;> cases a v <;> simp
  have key : CPLine.Holds a (clauseCP C)
      ↔ (1 : ℤ) ≤ ∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0 := by
    unfold CPLine.Holds clauseCP
    dsimp only
    rw [hsum, ← hind]
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    by_contra hne
    have h0 : (∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => by
        have hal : ¬ a l.1 = l.2 := fun hal => hne ⟨l, hl, hal⟩
        simp [hal]
    omega
  · rintro ⟨l, hl, hal⟩
    calc (1 : ℤ) = if a l.1 = l.2 then (1 : ℤ) else 0 := by simp [hal]
      _ ≤ _ := Finset.single_le_sum (f := fun l : Literal V => if a l.1 = l.2 then (1 : ℤ) else 0)
        (fun i _ => by split_ifs <;> norm_num) hl

/-- The falsified set of a clause line is the set of points falsifying the clause. -/
theorem fals_clauseCP [Fintype V] [DecidableEq V] (C : Clause V) :
    {a | ¬ CPLine.Holds a (clauseCP C)} = {a | ¬ ClauseSat a C} := by
  ext a
  simp only [Set.mem_ofPred_eq, clauseCP_holds_iff]

/-- The Boolean axiom `x_v ≥ 0` holds everywhere. -/
theorem holds_boolLo [Fintype V] [DecidableEq V] (a : V → Bool) (v : V) :
    CPLine.Holds a ((fun u => if u = v then 1 else 0, 0) : CPLine V) := by
  unfold CPLine.Holds
  exact Finset.sum_nonneg fun u _ => by dsimp only; split_ifs <;> norm_num

/-- The Boolean axiom `-x_v ≥ -1` holds everywhere. -/
theorem holds_boolHi [Fintype V] [DecidableEq V] (a : V → Bool) (v : V) :
    CPLine.Holds a ((fun u => if u = v then -1 else 0, -1) : CPLine V) := by
  have hs : (∑ u, (if u = v then (-1 : ℤ) else 0) * (if a u then 1 else 0))
      = (-1) * (if a v then 1 else 0) := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ v) h
  unfold CPLine.Holds
  dsimp only
  rw [hs]
  split_ifs <;> norm_num

/-- Addition is sound pointwise. -/
theorem holds_add [Fintype V] {a : V → Bool} {e e' : CPLine V}
    (h : CPLine.Holds a e) (h' : CPLine.Holds a e') :
    CPLine.Holds a ((e.1 + e'.1, e.2 + e'.2) : CPLine V) := by
  unfold CPLine.Holds at *
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  linarith

/-- Multiplication by a natural number (possibly zero) is sound pointwise. -/
theorem holds_mul [Fintype V] {a : V → Bool} {e : CPLine V} (k : ℕ)
    (h : CPLine.Holds a e) :
    CPLine.Holds a (((k : ℤ) • e.1, (k : ℤ) * e.2) : CPLine V) := by
  unfold CPLine.Holds at *
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (Int.natCast_nonneg k)

/-- Division with the constant rounded up is sound pointwise. -/
theorem holds_div [Fintype V] {a : V → Bool} {e : CPLine V} (d : ℕ) (hd : 0 < d)
    (hdiv : ∀ v, (d : ℤ) ∣ e.1 v) (h : CPLine.Holds a e) :
    CPLine.Holds a ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) : CPLine V) := by
  unfold CPLine.Holds at *
  dsimp only
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hs : (d : ℤ) * (∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0))
      = ∑ v, e.1 v * (if a v then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdiv v)]
  have hq : -(∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0)) ≤ (-e.2) / (d : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hd']
    linarith
  linarith

/-- The line `0 ≥ 1` holds nowhere. -/
theorem not_holds_zero_one [Fintype V] (a : V → Bool) :
    ¬ CPLine.Holds a (((0 : V → ℤ), (1 : ℤ)) : CPLine V) := by
  simp [CPLine.Holds]

/-- Soundness of cutting planes: every line of a derivation from `F` holds at every point
satisfying all the clauses of `F`. -/
theorem holds_of_derivation [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {π : List (CPLine V)} (h : IsCPDerivation F π) (a : V → Bool)
    (ha : ∀ C ∈ F, ClauseSat a C) : ∀ f ∈ π, CPLine.Holds a f := by
  induction h with
  | nil => intro f hf; simp at hf
  | ax C _ hC ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact (clauseCP_holds_iff a C).2 (ha C hC)
    · exact ih f hf
  | boolLo v _ ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact holds_boolLo a v
    · exact ih f hf
  | boolHi v _ ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact holds_boolHi a v
    · exact ih f hf
  | add _ he he' ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact holds_add (ih _ he) (ih _ he')
    · exact ih f hf
  | mul k _ he ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact holds_mul k (ih _ he)
    · exact ih f hf
  | div d _ he hd hdiv ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact holds_div d hd hdiv (ih _ he)
    · exact ih f hf

/-- A formula with a cutting planes refutation is nonempty. -/
theorem nonempty_of_refutation [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {π : List (CPLine V)} (h : IsCPRefutation F π) : F.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  exact not_holds_zero_one (fun _ => false)
    (holds_of_derivation h.1 (fun _ => false) (fun C hC => absurd hC (Set.notMem_empty C)) _ h.2)

/-- The falsified sets of the lines of a derivation from a nonempty formula form a triangle
dag, in the same order. -/
theorem triDag_of_derivation [Fintype V] [DecidableEq V] (side : V → Bool)
    {F : Set (Clause V)} (hF : F.Nonempty) {π : List (CPLine V)} (h : IsCPDerivation F π) :
    IsTriDag side F (π.map fun e => {a | ¬ CPLine.Holds a e}) := by
  obtain ⟨C₀, hC₀⟩ := hF
  induction h with
  | nil => exact IsTriDag.nil
  | ax C _ hC ih =>
    rw [List.map_cons]
    exact IsTriDag.sink ih (fals_isTri side _)
      ⟨C, hC, fun a ha hs => ha ((clauseCP_holds_iff a C).2 hs)⟩
  | boolLo v _ ih =>
    rw [List.map_cons]
    exact IsTriDag.sink ih (fals_isTri side _)
      ⟨C₀, hC₀, fun a ha => absurd (holds_boolLo a v) ha⟩
  | boolHi v _ ih =>
    rw [List.map_cons]
    exact IsTriDag.sink ih (fals_isTri side _)
      ⟨C₀, hC₀, fun a ha => absurd (holds_boolHi a v) ha⟩
  | @add π e e' _ he he' ih =>
    rw [List.map_cons]
    refine IsTriDag.split ih (fals_isTri side _) (List.mem_map.2 ⟨e, he, rfl⟩)
      (List.mem_map.2 ⟨e', he', rfl⟩) fun a ha => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact ha (holds_add hn.1 hn.2)
  | @mul π e k _ he ih =>
    rw [List.map_cons]
    refine IsTriDag.split ih (fals_isTri side _) (List.mem_map.2 ⟨e, he, rfl⟩)
      (List.mem_map.2 ⟨e, he, rfl⟩) fun a ha => ?_
    exact Or.inl fun hh => ha (holds_mul k hh)
  | @div π e d _ he hd hdiv ih =>
    rw [List.map_cons]
    refine IsTriDag.split ih (fals_isTri side _) (List.mem_map.2 ⟨e, he, rfl⟩)
      (List.mem_map.2 ⟨e, he, rfl⟩) fun a ha => ?_
    exact Or.inl fun hh => ha (holds_div d hd hdiv hh)

/-- A cutting planes refutation gives a triangle dag solving the search problem, node for
line. -/
theorem triDagFor_of_refutation [Fintype V] [DecidableEq V] (side : V → Bool)
    {F : Set (Clause V)} {π : List (CPLine V)} (h : IsCPRefutation F π) :
    IsTriDagFor side F (π.map fun e => {a | ¬ CPLine.Holds a e}) := by
  refine ⟨triDag_of_derivation side (nonempty_of_refutation h) h.1,
    List.mem_map.2 ⟨_, h.2, ?_⟩⟩
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact not_holds_zero_one a

end PEqualNP.Search.Helpers.CP
