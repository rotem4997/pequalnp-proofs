import PEqualNP.ProofComplexity.Helpers.BitPHP
import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamily
import PEqualNP.ProofComplexity.L043
import PEqualNP.Defs.ProofComplexityGeneral

/-!
# Plan for L-pcx-065 (low F2 degree does not bound the rank of Res(⊕) refutations)

Nothing here is a recorded lemma. This file fixes the definitions and the interface statements
so that the parts of the proof can be written independently, and proves the final assembly
from those statements.

The family. A linear system over the two-element field: equations `i : Fin m`, variables
`j : Fin N`, the support of equation `i` is `G i` for a `BipGraph m N`, the right side is
`c i`. It is lifted by the inner product gadget on two pairs of bits: the variable `j` becomes
the four Boolean variables `(j, 0), (j, 1), (j, 2), (j, 3)` and its value is
`ip2 = (y 0 and y 1) xor (y 2 and y 3)`. Each lifted equation is written as its canonical
CNF: one clause for each assignment of its `4 * |G i|` variables that violates it.

The parts (one statement each, all stated on Boolean assignments, the convention of the
definitions root; `Helpers.fals_vec` is the bridge to the vectors of `Helpers.BitPHP`):

* `StmtClosure`: a line of rank `k` has a set `K` of at most `k` blocks such that every
  assignment falsifying the line can be changed, off the blocks of `K`, into one that still
  falsifies the line and has any prescribed gadget values off `K`. The proof is `exists_good`,
  `exists_pivots` and `exists_perp_inf` of `Helpers.BitPHP` (with `l = 4`), and `ip2_stifled`
  below: fix the three non-pivot bits of every block off `K` so that they force the wanted
  value, then solve for the pivots.
* `StmtFormula`: the lifted formula has width at most `4 * b`, its clauses of equation `i`
  say exactly that equation `i` holds, and a set of equations whose supports cancel and whose
  right sides sum to one gives a polynomial calculus refutation of degree `4 * b`.
* `StmtWidth`: on a boundary expander every Res(⊕) refutation of the lifted formula has a
  line `C` with `δ * s < 3 * linRank C`. Leg target: `StmtClosure → StmtWidth`.
* `StmtRenamePC`, `StmtRenameRank`, `StmtDependency`: renaming the variables keeps polynomial
  calculus refutations and the rank of a line; more equations than variables have a nonempty
  set of supports that cancel.
* `assembly_of` (proved here): these give `Stmt065`, the recorded statement of L-pcx-065.

Changes from the paper plan, with reasons:

1. `StmtWidth` needs `1 ≤ δ` (the paper plan has `δ = 2` in mind). With `δ = 0` it is false:
   one equation with empty support and right side one lifts to the empty clause, the
   refutation is that one line, and it has rank `0`.
2. `StmtWidth` does not assume that the system is unsatisfiable: the proof never uses it (a
   refutation is given), and without it no measure has to be shown to be well defined.
3. The measure is best used through `Covers` (a set of equations one of which is violated by
   every assignment falsifying the line); `mu` is its least size and is defined for the
   record, but the argument of `StmtWidth` only needs: axioms are covered by one equation,
   a weakening is covered by the cover of its premise, a resolvent by the union of the two
   covers, the empty line by no set of at most `s` equations (`1 ≤ δ` is used here), and a
   line covered by a set `W` of at most `s` equations is covered by some `U ⊆ W` with
   `δ * |U| ≤ linRank` (take `U` the union of the subsets of `W` whose unique neighbours all
   lie in the closure; no maximality or size argument is needed, since `U ⊆ W` already has
   at most `s` elements, and unique neighbours of a union are unique neighbours of a part).
4. The closure set of `StmtClosure` is existential, so the notion `Good` of `Helpers.BitPHP`
   does not appear in any interface.
-/

namespace PEqualNP.ProofComplexity.LiftRank

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily

/-! ### Definitions -/

/-- The gadget: the inner product of two pairs of bits over the two-element field. -/
def ip2 (y : Fin 4 → Bool) : Bool := xor (y 0 && y 1) (y 2 && y 3)

/-- The gadget value of block `j` under the assignment `a` of the lifted variables. -/
def gval {N : ℕ} (a : Fin N × Fin 4 → Bool) (j : Fin N) : Bool := ip2 (fun t => a (j, t))

/-- The assignment `a` of the lifted variables satisfies the lifted equation `i`: the number
of blocks `j` of `G i` with gadget value true is odd exactly when `c i` is true. -/
def EqSat {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (a : Fin N × Fin 4 → Bool)
    (i : Fin m) : Prop :=
  LinEqSat (gval a) (G i, c i)

/-- The clause on the variables of the blocks of `G i` that is false exactly at the
assignments that agree with `α` on those variables. -/
def blockClause {m N : ℕ} (G : BipGraph m N) (i : Fin m) (α : Fin N × Fin 4 → Bool) :
    Clause (Fin N × Fin 4) :=
  ((G i) ×ˢ (Finset.univ : Finset (Fin 4))).image (fun v => (v, !α v))

/-- The clauses of the lifted equation `i`: one for each assignment that violates it. -/
def liftEq {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (i : Fin m) :
    Set (Clause (Fin N × Fin 4)) :=
  {C | ∃ α : Fin N × Fin 4 → Bool, ¬ EqSat G c α i ∧ C = blockClause G i α}

/-- The lifted formula: the clauses of all lifted equations. -/
def liftSys {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) : Set (Clause (Fin N × Fin 4)) :=
  {C | ∃ i : Fin m, C ∈ liftEq G c i}

/-- The set `U` of equations covers the line `L`: every assignment that falsifies `L`
violates a lifted equation of `U`. -/
def Covers {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (U : Finset (Fin m))
    (L : LinClause (Fin N × Fin 4)) : Prop :=
  ∀ a : Fin N × Fin 4 → Bool, ¬ LinClauseSat a L → ∃ i ∈ U, ¬ EqSat G c a i

/-- The measure of a line: the least number of equations in a set that covers it (zero when
no set covers it, which cannot happen when the lifted system is unsatisfiable). -/
noncomputable def mu {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool)
    (L : LinClause (Fin N × Fin 4)) : ℕ :=
  sInf {k | ∃ U : Finset (Fin m), U.card = k ∧ Covers G c U L}

/-! ### Interface statements -/

/-- Closure realisation (leg 1). -/
def StmtClosure : Prop :=
  ∀ (N : ℕ) (L : LinClause (Fin N × Fin 4)), ∃ K : Finset (Fin N), K.card ≤ linRank L ∧
    ∀ a : Fin N × Fin 4 → Bool, ¬ LinClauseSat a L → ∀ t : Fin N → Bool,
      ∃ a' : Fin N × Fin 4 → Bool, ¬ LinClauseSat a' L ∧
        (∀ j ∈ K, ∀ u : Fin 4, a' (j, u) = a (j, u)) ∧ ∀ j, j ∉ K → gval a' j = t j

/-- The width of the lifted formula (leg 2). -/
def StmtFormulaWidth : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (b : ℕ), LeftDegLe G b →
    ∀ C ∈ liftSys G c, C.card ≤ 4 * b

/-- The clauses of a lifted equation say that the equation holds (leg 2). -/
def StmtFormulaSem : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (a : Fin N × Fin 4 → Bool) (i : Fin m),
    (∀ C ∈ liftEq G c i, ClauseSat a C) ↔ EqSat G c a i

/-- A set `S` of equations whose supports cancel and whose right sides sum to one gives a
polynomial calculus refutation of the lifted formula in degree `4 * b` (leg 2). -/
def StmtFormulaPC : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (b : ℕ), LeftDegLe G b →
    ∀ S : Finset (Fin m), (∀ j : Fin N, Even (S.filter (fun i => j ∈ G i)).card) →
      Odd (S.filter (fun i => c i = true)).card →
      PCRefutable (cnfSystem (liftSys G c)) (4 * b)

/-- Leg 2. -/
def StmtFormula : Prop := StmtFormulaWidth ∧ StmtFormulaSem ∧ StmtFormulaPC

/-- Every Res(⊕) refutation of the lifted formula on a boundary expander has a line of large
rank. Leg 3 proves `StmtClosure → StmtWidth`. -/
def StmtWidth : Prop :=
  ∀ (m N : ℕ) (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ), IsBdryExpander G s δ →
    3 ≤ s → 1 ≤ δ → ∀ π : List (LinClause (Fin N × Fin 4)), IsLinRefutation (liftSys G c) π →
      ∃ C ∈ π, δ * s < 3 * linRank C

/-- Renaming the variables keeps polynomial calculus refutations (leg 4). -/
def StmtRenamePC : Prop :=
  ∀ (V W : Type) [DecidableEq V] [DecidableEq W] (e : V ≃ W) (F : Set (Clause V)) (d : ℕ),
    PCRefutable (cnfSystem F) d → PCRefutable (cnfSystem (ren e '' F)) d

/-- Pulling a line back along a renaming does not raise its rank (leg 4). -/
def StmtRenameRank : Prop :=
  ∀ (V W : Type) [DecidableEq V] [DecidableEq W] (e : V ≃ W) (L : LinClause W),
    linRank (backLin e L) ≤ linRank L

/-- More equations than variables: some nonempty set of supports cancels (leg 4). -/
def StmtDependency : Prop :=
  ∀ (n : ℕ) (G : BipGraph (n + 1) n), ∃ S : Finset (Fin (n + 1)), S.Nonempty ∧
    ∀ j : Fin n, Even (S.filter (fun i => j ∈ G i)).card

/-- The recorded statement of L-pcx-065, verbatim. -/
def Stmt065 : Prop :=
  ∃ w d c : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)), (∀ C ∈ F, C.card ≤ w) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) d ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → ∃ C ∈ π, n ≤ c * PEqualNP.ProofComplexity.linRank C

/-- The assembly (leg 4, proved below as `assembly_of`). -/
def StmtAssembly : Prop :=
  StmtFormula → StmtWidth → StmtRenamePC → StmtRenameRank → StmtDependency → Stmt065

/-! ### Small facts -/

/-- The gadget is 1-stifled: for every position `p` and every wanted value `t`, the other
three bits can be set so that the gadget has value `t` whatever the bit at `p` is. -/
theorem ip2_stifled (p : Fin 4) (t : Bool) :
    ∃ y : Fin 4 → Bool, ∀ z : Fin 4 → Bool, (∀ q, q ≠ p → z q = y q) → ip2 z = t := by
  have key : ∀ (y : Fin 4 → Bool), (∀ r : Bool, ip2 (Function.update y p r) = t) →
      ∀ z : Fin 4 → Bool, (∀ q, q ≠ p → z q = y q) → ip2 z = t := by
    intro y hy z hz
    have : z = Function.update y p (z p) := by
      funext q
      by_cases hq : q = p
      · subst hq; simp
      · rw [Function.update_of_ne hq]; exact hz q hq
    rw [this]
    exact hy _
  fin_cases p <;> cases t
  · exact ⟨![false, false, false, false], key _ (by decide)⟩
  · exact ⟨![false, false, true, true], key _ (by decide)⟩
  · exact ⟨![false, false, false, false], key _ (by decide)⟩
  · exact ⟨![false, false, true, true], key _ (by decide)⟩
  · exact ⟨![false, false, false, false], key _ (by decide)⟩
  · exact ⟨![true, true, false, false], key _ (by decide)⟩
  · exact ⟨![false, false, false, false], key _ (by decide)⟩
  · exact ⟨![true, true, false, false], key _ (by decide)⟩

/-- The gadget is onto. -/
theorem ip2_surj (t : Bool) : ∃ y : Fin 4 → Bool, ip2 y = t := by
  obtain ⟨y, hy⟩ := ip2_stifled 0 t
  exact ⟨y, hy y (fun _ _ => rfl)⟩

/-- The width of the lifted formula. -/
theorem formula_width : StmtFormulaWidth := by
  rintro m N G c b hb C ⟨i, α, -, rfl⟩
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  exact Nat.mul_le_mul_left 4 (hb i)

/-- The clauses of a lifted equation say that the equation holds. -/
theorem formula_sem : StmtFormulaSem := by
  intro m N G c a i
  constructor
  · intro h
    by_contra hn
    obtain ⟨l, hl, hal⟩ := h _ ⟨a, hn, rfl⟩
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hl
    simp at hal
  · rintro h C ⟨α, hα, rfl⟩
    by_contra hn
    apply hα
    have hag : ∀ v ∈ (G i) ×ˢ (Finset.univ : Finset (Fin 4)), a v = α v := by
      intro v hv
      by_contra hne
      refine hn ⟨(v, !α v), Finset.mem_image_of_mem _ hv, ?_⟩
      revert hne
      cases a v <;> cases α v <;> simp
    have hg : ∀ j ∈ G i, gval α j = gval a j := by
      intro j hj
      unfold gval
      congr 1
      funext u
      exact (hag (j, u) (Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩)).symm
    unfold EqSat LinEqSat at h ⊢
    rw [Finset.filter_congr (fun j hj => by rw [hg j hj])]
    exact h

theorem toZ_inj : ∀ b b' : Bool, toZ b = toZ b' → b = b' := by decide

/-- Closure realisation, from the good sets and pivots of `Helpers.BitPHP` and the stifling
of the gadget. -/
theorem closure : StmtClosure := by
  classical
  intro N L
  obtain ⟨K, hG, hK⟩ := exists_good (formSpan L)
  refine ⟨K, by rw [linRank_eq]; exact hK, ?_⟩
  obtain ⟨zf, hzf⟩ := exists_pivots (by norm_num : 0 < 4) N (formSpan L) K (by omega) hG
  intro a ha t
  choose st hst using fun j : Fin N => ip2_stifled (zf j) (t j)
  obtain ⟨y, hy⟩ : ∃ y : Fin N × Fin 4 → Bool,
      y = fun v => if v.1 ∈ K then a v else st v.1 v.2 := ⟨_, rfl⟩
  obtain ⟨w, hwU, hwN⟩ := exists_perp_inf (formSpan L) (vanishPivots K zf) (vec y - vec a) (by
    intro g hg
    have hgs := hzf g hg.1 hg.2
    unfold dotProduct
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 ∈ K
    · simp [hy, vec, hv]
    · rw [hgs v hv, zero_mul])
  have hy' : ∀ v : Fin N × Fin 4, v.1 ∈ K ∨ v.2 ≠ zf v.1 → (vec a + w) v = vec y v := by
    intro v hv
    have hmem : Pi.single v (1 : ZMod 2) ∈ vanishPivots K zf := by
      intro i hi
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      rcases hv with h | h
      · exact hi h
      · exact h rfl
    have := hwN _ hmem
    rw [single_one_dotProduct, single_one_dotProduct] at this
    simp [this]
  have hfals : Fals L (vec a + w) := fals_add ((fals_vec a L).2 ha) hwU
  obtain ⟨a', ha'⟩ := vec_surj (vec a + w)
  have hval : ∀ v : Fin N × Fin 4, v.1 ∈ K ∨ v.2 ≠ zf v.1 → a' v = y v := by
    intro v hv
    apply toZ_inj
    have h1 := hy' v hv
    rw [← ha'] at h1
    exact h1
  refine ⟨a', ?_, ?_, ?_⟩
  · rw [← fals_vec, ha']
    exact hfals
  · intro j hj u
    rw [hval (j, u) (Or.inl hj), hy]
    simp [hj]
  · intro j hj
    refine hst j _ fun q hq => ?_
    rw [hval (j, q) (Or.inr hq), hy]
    simp [hj]

/-! ### The assembly -/

/-- The arithmetic of the assembly. -/
theorem assembly_arith (n₁ s₀ r : ℕ) (hs : 0 < s₀) (h3 : 3 * s₀ ≤ n₁)
    (hr : 2 * (n₁ / s₀) < 3 * r) : n₁ * 4 ≤ 12 * s₀ * r := by
  have h1 : n₁ < s₀ * (n₁ / s₀ + 1) := Nat.lt_mul_div_succ n₁ hs
  have h2 : 3 ≤ n₁ / s₀ := (Nat.le_div_iff_mul_le hs).mpr h3
  have h4 : s₀ * (2 * (n₁ / s₀) + 1) ≤ s₀ * (3 * r) := Nat.mul_le_mul_left _ hr
  have h5 : s₀ * 1 ≤ s₀ * (n₁ / s₀) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- L-pcx-065 from the interface statements and the expanders of L-pcx-043. -/
theorem assembly_of : StmtAssembly := by
  classical
  rintro ⟨hWidth, -, hPC⟩ hRank hRenPC hRenRank hDep
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  refine ⟨4 * b, 4 * b, 12 * s₀, fun N => ?_⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max N (max n₀ (3 * s₀)) := ⟨_, rfl⟩
  have hN : N ≤ n₁ := hn₁ ▸ le_max_left _ _
  have hn0 : n₀ ≤ n₁ := hn₁ ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hn3 : 3 * s₀ ≤ n₁ := hn₁ ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨G, hLd, -, hE⟩ := hG n₁ hn0
  obtain ⟨S, ⟨i₀, hi₀⟩, hS⟩ := hDep n₁ G
  obtain ⟨c, hc⟩ : ∃ c : Fin (n₁ + 1) → Bool, c = fun i => decide (i = i₀) := ⟨_, rfl⟩
  have hodd : Odd (S.filter (fun i => c i = true)).card := by
    have : S.filter (fun i => c i = true) = {i₀} := by
      ext i
      simp only [hc, Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hi₀, h⟩⟩
    rw [this, Finset.card_singleton]
    exact odd_one
  obtain ⟨e, -⟩ : ∃ e : Fin n₁ × Fin 4 ≃ Fin (n₁ * 4), e = finProdFinEquiv := ⟨_, rfl⟩
  have hfin : (ren e '' liftSys G c).Finite := Set.toFinite _
  refine ⟨n₁ * 4, by omega, hfin.toFinset, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨C0, hC0, rfl⟩ := hfin.mem_toFinset.mp hC
    exact le_trans Finset.card_image_le (hWidth _ _ G c b hLd C0 hC0)
  · rw [Set.Finite.coe_toFinset]
    exact hRenPC _ _ e _ _ (hPC _ _ G c b hLd S hS hodd)
  · intro π hπ
    rw [Set.Finite.coe_toFinset] at hπ
    have href := back_refutation e (liftSys G c) π hπ
    have h3 : 3 ≤ n₁ / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr hn3
    obtain ⟨C', hC', hbig⟩ := hRank _ _ G c (n₁ / s₀) 2 hE h3 (by norm_num) _ href
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    refine ⟨C, hC, ?_⟩
    have hle := hRenRank _ _ e C
    have := assembly_arith n₁ s₀ (linRank (backLin e C)) hs₀ hn3 hbig
    calc n₁ * 4 ≤ 12 * s₀ * linRank (backLin e C) := this
      _ ≤ 12 * s₀ * linRank C := Nat.mul_le_mul_left _ hle

end PEqualNP.ProofComplexity.LiftRank
