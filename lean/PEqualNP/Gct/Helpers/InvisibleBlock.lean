import Mathlib
import PEqualNP.Gct.Helpers.ProdSigmaChain

/-! Helper for L-gct-098 (Lemma I), proofs only. A space `W` of `P × m` matrices on which every
column-set injective sum vanishes. Three steps.

1. Echelon by last nonzero column: `Wc W n` is the part of `W` vanishing on the columns `≥ n`, and
   `S W j` is the space of the columns `j` of `Wc W (j+1)`. Rank-nullity telescopes to
   `finrank W = ∑ j, finrank (S W j)`.
2. The injective sums vanish on families with column `y` taken from `S W y`: replace the columns
   of an element of `W` by prescribed ones, one column at a time, using a lift and additivity of
   the injective sum in one column.
3. Moebius without set partitions: if the diagonal sums of a family vanish on every nonempty
   proper subset, the injective sum is a nonzero constant times the full diagonal sum. Induction
   through `Option`, the constant getting multiplied by `-(card α)`. -/

namespace PEqualNP.Gct.Helpers.InvisibleBlock

open Module Finset

variable {P m : ℕ}

/-! ### Step 3: Moebius -/

/-- The injective sum of a family of vectors. -/
noncomputable def injSum {α : Type*} [Fintype α] [DecidableEq α] (u : α → Fin P → ℂ) : ℂ :=
  ∑ f : α ↪ Fin P, ∏ a, u a (f a)

/-- The diagonal sum of a family over a set of indices. -/
def diagSum {α : Type*} (B : Finset α) (u : α → Fin P → ℂ) : ℂ :=
  ∑ i, ∏ a ∈ B, u a i

/-- The Moebius statement for an index type. -/
def Moeb (P : ℕ) (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  Nonempty α → ∃ c : ℂ, c ≠ 0 ∧ ∀ u : α → Fin P → ℂ,
    (∀ B : Finset α, B.Nonempty → B ≠ univ → diagSum B u = 0) → injSum u = c * diagSum univ u

theorem moeb_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (h : Moeb P α) : Moeb P β := by
  intro hβ
  obtain ⟨c, hc, hu⟩ := h (hβ.map e.symm)
  refine ⟨c, hc, fun u hB => ?_⟩
  have hI : injSum (fun a => u (e a)) = injSum u := by
    unfold injSum
    refine Fintype.sum_equiv (Equiv.embeddingCongr e (Equiv.refl _)) _ _ fun g => ?_
    refine Fintype.prod_equiv e _ _ fun a => ?_
    simp [Equiv.embeddingCongr_apply]
  have hD : ∀ B : Finset α, diagSum B (fun a => u (e a)) = diagSum (B.map e.toEmbedding) u := by
    intro B
    unfold diagSum
    simp [Finset.prod_map]
  have := hu (fun a => u (e a)) (fun B hBn hBu => by
    rw [hD]
    refine hB _ (hBn.map) fun hcon => hBu ?_
    rw [← Finset.map_univ_equiv e] at hcon
    exact Finset.map_injective _ hcon)
  rw [hI, hD, Finset.map_univ_equiv] at this
  exact this

theorem exists_not_mem {α : Type*} [Fintype α] {B : Finset α} (h : B ≠ univ) : ∃ b, b ∉ B := by
  by_contra hc
  push_neg at hc
  exact h (eq_univ_iff_forall.2 hc)

/-- The sum over the complement of the range of an embedding. -/
theorem sum_compl_range {α : Type*} [Fintype α] (g : α ↪ Fin P) (φ : Fin P → ℂ)
    [Fintype ↥(Set.range g)ᶜ] :
    ∑ i : ↥(Set.range g)ᶜ, φ i = ∑ i, φ i - ∑ a, φ (g a) := by
  classical
  have h1 := Finset.sum_compl_add_sum (univ.map g) φ
  rw [Finset.sum_map] at h1
  have h2 : ∑ i ∈ (univ.map g)ᶜ, φ i = ∑ i : ↥(Set.range g)ᶜ, φ i :=
    Finset.sum_subtype _ (fun x => by simp) φ
  rw [← h2, eq_sub_iff_add_eq]
  exact h1

/-- The merged family: the factor of index `z` multiplied by the vector of `none`. -/
def merge {α : Type*} [DecidableEq α] (u : Option α → Fin P → ℂ) (z : α) : α → Fin P → ℂ :=
  fun a i => u (some a) i * if a = z then u none i else 1

theorem prod_merge {α : Type*} [DecidableEq α] (u : Option α → Fin P → ℂ) (z : α)
    (B : Finset α) (i : Fin P) :
    ∏ a ∈ B, merge u z a i = (∏ a ∈ B, u (some a) i) * if z ∈ B then u none i else 1 := by
  unfold merge
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']

/-- The recursion of the injective sum through `Option`. -/
theorem injSum_option {α : Type*} [Fintype α] [DecidableEq α] (u : Option α → Fin P → ℂ) :
    injSum u = diagSum {none} u * injSum (fun a => u (some a))
      - ∑ z, injSum (merge u z) := by
  classical
  unfold injSum diagSum
  rw [Fintype.sum_equiv (Function.Embedding.optionEmbeddingEquiv α (Fin P)) _
    (fun p => u none p.2 * ∏ a, u (some a) (p.1 a)) (fun f => by
      rw [Fintype.prod_option]; rfl)]
  rw [Fintype.sum_sigma]
  simp only [Finset.prod_singleton]
  have hz : ∀ z : α, ∑ g : α ↪ Fin P, ∏ a, merge u z a (g a)
      = ∑ g : α ↪ Fin P, (∏ a, u (some a) (g a)) * u none (g z) := by
    intro z
    refine Fintype.sum_congr _ _ fun g => ?_
    unfold merge
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ z (fun a => u none (g a))]
    simp
  simp only [hz]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Fintype.sum_congr _ _ fun g => ?_
  rw [← Finset.sum_mul, sum_compl_range g (u none), sub_mul, ← Finset.mul_sum]
  ring

theorem moeb_option {α : Type*} [Fintype α] [DecidableEq α] (h : Moeb P α) :
    Moeb P (Option α) := by
  intro _
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨1, one_ne_zero, fun u _ => ?_⟩
    rw [injSum_option]
    have h1 : injSum (P := P) (fun a : α => u (some a)) = 1 := by
      unfold injSum
      rw [Fintype.sum_eq_single (Function.Embedding.ofIsEmpty) (fun g hg =>
        absurd (Function.Embedding.ext fun a => isEmptyElim a) hg)]
      simp
    have h2 : ({none} : Finset (Option α)) = univ := by
      ext o; cases o with
      | none => exact ⟨fun _ => mem_univ _, fun _ => mem_singleton_self _⟩
      | some a => exact isEmptyElim a
    simp [h1, h2]
  · obtain ⟨c, hc, hu⟩ := h hα
    obtain ⟨a0⟩ := hα
    refine ⟨-(Fintype.card α : ℂ) * c, ?_, fun u hB => ?_⟩
    · have : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨a0⟩).ne'
      exact mul_ne_zero (neg_ne_zero.2 this) hc
    rw [injSum_option]
    have h0 : diagSum {none} u = 0 :=
      hB {none} (singleton_nonempty _) fun hcon => by
        have : some a0 ∈ ({none} : Finset (Option α)) := hcon ▸ mem_univ _
        simp at this
    have hfull : ∀ z, diagSum univ (merge u z) = diagSum univ u := by
      intro z
      unfold diagSum
      refine Fintype.sum_congr _ _ fun i => ?_
      rw [prod_merge, Fintype.prod_option, if_pos (mem_univ z), mul_comm]
    have hm : ∀ z, injSum (merge u z) = c * diagSum univ u := by
      intro z
      rw [← hfull z]
      refine hu _ fun B hBn hBu => ?_
      obtain ⟨b, hb⟩ := exists_not_mem hBu
      by_cases hzB : z ∈ B
      · have hnone : none ∉ B.map Function.Embedding.some := by simp
        have heq : diagSum B (merge u z) = diagSum (insert none (B.map Function.Embedding.some)) u := by
          unfold diagSum
          refine Fintype.sum_congr _ _ fun i => ?_
          rw [prod_merge, if_pos hzB, Finset.prod_insert hnone, Finset.prod_map, mul_comm]
          rfl
        rw [heq]
        refine hB _ (insert_nonempty _ _) fun hcon => ?_
        have : some b ∈ insert none (B.map Function.Embedding.some) := hcon ▸ mem_univ _
        simp [hb] at this
      · have heq : diagSum B (merge u z) = diagSum (B.map Function.Embedding.some) u := by
          unfold diagSum
          refine Fintype.sum_congr _ _ fun i => ?_
          rw [prod_merge, if_neg hzB, Finset.prod_map, mul_one]
          rfl
        rw [heq]
        refine hB _ hBn.map fun hcon => ?_
        have : (none : Option α) ∈ B.map Function.Embedding.some := hcon ▸ mem_univ _
        simp at this
    simp only [h0, zero_mul, zero_sub, hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

theorem moeb_fin (n : ℕ) : Moeb P (Fin n) := by
  induction n with
  | zero => intro h; exact isEmptyElim (h.some)
  | succ n ih => exact moeb_equiv (finSuccEquiv n).symm (moeb_option ih)

theorem moeb (α : Type*) [Fintype α] [DecidableEq α] : Moeb P α :=
  moeb_equiv (Fintype.equivFin α).symm (moeb_fin _)

/-- Injective sums vanishing for families from subspaces give vanishing diagonal sums. -/
theorem diag_of_inj (V : Fin m → Submodule ℂ (Fin P → ℂ))
    (hinj : ∀ Y : Finset (Fin m), Y.Nonempty → ∀ s : Fin m → Fin P → ℂ, (∀ y ∈ Y, s y ∈ V y) →
      ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, s y (f y) = 0) :
    ∀ A : Finset (Fin m), A.Nonempty → ∀ s : Fin m → Fin P → ℂ, (∀ j ∈ A, s j ∈ V j) →
      ∑ i, ∏ j ∈ A, s j i = 0 := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hA s hs
    obtain ⟨c, hc, hu⟩ := moeb (P := P) (↥A) hA.coe_sort
    have key := hu (fun y => s y) fun B hBn hBu => by
      obtain ⟨b, hb⟩ := exists_not_mem hBu
      unfold diagSum
      have := ih (B.map (Function.Embedding.subtype _)) ?_ hBn.map s ?_
      · simpa [Finset.prod_map] using this
      · rw [Finset.ssubset_iff_of_subset]
        · exact ⟨b, b.2, by simpa using hb⟩
        · intro x hx
          obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
          exact y.2
      · intro j hj
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hj
        exact hs _ y.2
    have h0 : injSum (fun y : ↥A => s y) = 0 := hinj A hA s hs
    rw [h0] at key
    have := (mul_eq_zero.1 key.symm).resolve_left hc
    unfold diagSum at this
    have e : ∀ i, ∏ y : ↥A, s y i = ∏ j ∈ A, s j i := fun i => Finset.prod_coe_sort A (fun j => s j i)
    simp only [← e]
    exact this

/-! ### Step 1: echelon by last nonzero column -/

variable (W : Submodule ℂ (Fin P × Fin m → ℂ))

/-- The part of `W` vanishing on the columns of index at least `n`. -/
def Wc (n : ℕ) : Submodule ℂ (Fin P × Fin m → ℂ) where
  carrier := {t | t ∈ W ∧ ∀ (i : Fin P) (y : Fin m), n ≤ (y : ℕ) → t (i, y) = 0}
  add_mem' := fun {a b} ha hb => ⟨W.add_mem ha.1 hb.1, fun i y hy => by
    simp [ha.2 i y hy, hb.2 i y hy]⟩
  zero_mem' := ⟨W.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := fun c t ht => ⟨W.smul_mem c ht.1, fun i y hy => by simp [ht.2 i y hy]⟩

/-- Column `j` of a matrix. -/
def col (j : Fin m) : (Fin P × Fin m → ℂ) →ₗ[ℂ] (Fin P → ℂ) where
  toFun t i := t (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The space of the last nonzero columns in position `j`. -/
def S (j : Fin m) : Submodule ℂ (Fin P → ℂ) :=
  LinearMap.range (col j ∘ₗ (Wc W ((j : ℕ) + 1)).subtype)

theorem finrank_Wc_succ (n : ℕ) (h : n < m) :
    finrank ℂ ↥(Wc W (n + 1)) = finrank ℂ ↥(S W ⟨n, h⟩) + finrank ℂ ↥(Wc W n) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (col ⟨n, h⟩ ∘ₗ (Wc W (n + 1)).subtype)
  have hle : Wc W n ≤ Wc W (n + 1) := fun t ht => ⟨ht.1, fun i y hy => ht.2 i y (by omega)⟩
  have hker : LinearMap.ker (col ⟨n, h⟩ ∘ₗ (Wc W (n + 1)).subtype)
      = (Wc W n).comap (Wc W (n + 1)).subtype := by
    ext ⟨t, ht⟩
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Submodule.mem_comap]
    constructor
    · intro h0
      refine ⟨ht.1, fun i y hy => ?_⟩
      rcases Nat.lt_or_ge n (y : ℕ) with hlt | hge
      · exact ht.2 i y hlt
      · have hy' : y = ⟨n, h⟩ := Fin.ext (by simp; omega)
        subst hy'
        exact congr_fun h0 i
    · intro h0
      funext i
      exact h0.2 i ⟨n, h⟩ le_rfl
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hrn
  change _ = finrank ℂ ↥(LinearMap.range (col ⟨n, h⟩ ∘ₗ (Wc W (n + 1)).subtype)) + _
  omega

theorem finrank_eq_sum : finrank ℂ ↥W = ∑ j, finrank ℂ ↥(S W j) := by
  let g : ℕ → ℕ := fun n => if h : n < m then finrank ℂ ↥(S W ⟨n, h⟩) else 0
  have hg : ∑ j : Fin m, finrank ℂ ↥(S W j) = ∑ n ∈ range m, g n := by
    rw [← Fin.sum_univ_eq_sum_range g m]
    refine Fintype.sum_congr _ _ fun j => ?_
    simp [g, j.isLt]
  have key : ∀ n ≤ m, finrank ℂ ↥(Wc W n) = ∑ k ∈ range n, g k := by
    intro n
    induction n with
    | zero =>
      intro _
      have : Wc W 0 = ⊥ := by
        rw [eq_bot_iff]
        intro t ht
        rw [Submodule.mem_bot]
        funext ⟨i, y⟩
        exact ht.2 i y (Nat.zero_le _)
      simp [this]
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, ← ih (by omega), finrank_Wc_succ W n (by omega)]
      simp [g, show n < m by omega, add_comm]
  have hWm : Wc W m = W := by
    ext t
    exact ⟨fun h => h.1, fun h => ⟨h, fun i y hy => absurd y.isLt (by omega)⟩⟩
  rw [hg, ← key m le_rfl, hWm]

/-! ### Step 2: the injective sums on families from the spaces `S W j` -/

/-- The injective sum over a set of columns of a family of columns. -/
noncomputable def colSum (Y : Finset (Fin m)) (g : Fin m → Fin P → ℂ) : ℂ :=
  ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, g y (f y)

theorem colSum_congr (Y : Finset (Fin m)) (g g' : Fin m → Fin P → ℂ)
    (h : ∀ y ∈ Y, g y = g' y) : colSum Y g = colSum Y g' := by
  unfold colSum
  refine Fintype.sum_congr _ _ fun f => Fintype.prod_congr _ _ fun y => ?_
  rw [h y y.2]

theorem colSum_add (Y : Finset (Fin m)) (c : Fin m) (hc : c ∈ Y) (g1 g2 g3 : Fin m → Fin P → ℂ)
    (hoff : ∀ y, y ≠ c → g1 y = g2 y ∧ g1 y = g3 y) (hon : g1 c = g2 c + g3 c) :
    colSum Y g1 = colSum Y g2 + colSum Y g3 := by
  classical
  unfold colSum
  rw [← Finset.sum_add_distrib]
  refine Fintype.sum_congr _ _ fun f => ?_
  rw [Fintype.prod_eq_mul_prod_compl (⟨c, hc⟩ : ↥Y), Fintype.prod_eq_mul_prod_compl (⟨c, hc⟩ : ↥Y),
    Fintype.prod_eq_mul_prod_compl (⟨c, hc⟩ : ↥Y)]
  have e2 : ∏ y ∈ ({(⟨c, hc⟩ : ↥Y)}ᶜ : Finset ↥Y), g1 y (f y)
      = ∏ y ∈ ({(⟨c, hc⟩ : ↥Y)}ᶜ : Finset ↥Y), g2 y (f y) :=
    Finset.prod_congr rfl fun y hy => by
      have : (y : Fin m) ≠ c := fun h => by
        simp only [Finset.mem_compl, Finset.mem_singleton] at hy
        exact hy (Subtype.ext h)
      rw [(hoff y this).1]
  have e3 : ∏ y ∈ ({(⟨c, hc⟩ : ↥Y)}ᶜ : Finset ↥Y), g1 y (f y)
      = ∏ y ∈ ({(⟨c, hc⟩ : ↥Y)}ᶜ : Finset ↥Y), g3 y (f y) :=
    Finset.prod_congr rfl fun y hy => by
      have : (y : Fin m) ≠ c := fun h => by
        simp only [Finset.mem_compl, Finset.mem_singleton] at hy
        exact hy (Subtype.ext h)
      rw [(hoff y this).2]
  rw [← e2, ← e3]
  simp only [hon, Pi.add_apply]
  ring

/-- Columns below `n` from `s`, the others from `t`. -/
def mix (s : Fin m → Fin P → ℂ) (t : Fin P × Fin m → ℂ) (n : ℕ) : Fin m → Fin P → ℂ :=
  fun y i => if (y : ℕ) < n then s y i else t (i, y)

theorem inj_on_S
    (hW : ∀ t ∈ W, ∀ Y : Finset (Fin m), Y.Nonempty →
      ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, t (f y, (y : Fin m)) = 0)
    (Y : Finset (Fin m)) (hY : Y.Nonempty) (s : Fin m → Fin P → ℂ)
    (hs : ∀ y ∈ Y, s y ∈ S W y) :
    ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, s y (f y) = 0 := by
  have key : ∀ n ≤ m, ∀ t ∈ W, colSum Y (mix s t n) = 0 := by
    intro n
    induction n with
    | zero =>
      intro _ t ht
      have := hW t ht Y hY
      unfold colSum mix
      simpa using this
    | succ n ih =>
      intro hn t ht
      have hnm : n < m := by omega
      by_cases hcY : (⟨n, hnm⟩ : Fin m) ∈ Y
      · obtain ⟨⟨tc, htc⟩, hcol⟩ := hs _ hcY
        have htc2 : ∀ (i : Fin P) (y : Fin m), n + 1 ≤ (y : ℕ) → tc (i, y) = 0 := htc.2
        have h1 := ih (by omega) (t + tc) (W.add_mem ht htc.1)
        have h2 := ih (by omega) t ht
        rw [colSum_add Y ⟨n, hnm⟩ hcY _ (mix s t n) (mix s t (n + 1)) ?_ ?_, h2, zero_add]
          at h1
        · exact h1
        · intro y hy
          have hy' : (y : ℕ) ≠ n := fun h => hy (Fin.ext h)
          unfold mix
          refine ⟨?_, ?_⟩ <;> funext i
          · by_cases hlt : (y : ℕ) < n
            · simp [hlt]
            · have : tc (i, y) = 0 := htc2 i y (by omega)
              simp [hlt, this]
          · by_cases hlt : (y : ℕ) < n
            · simp [hlt, show (y : ℕ) < n + 1 by omega]
            · have : tc (i, y) = 0 := htc2 i y (by omega)
              simp [hlt, this, show ¬ (y : ℕ) < n + 1 by omega]
        · funext i
          unfold mix
          have := congr_fun hcol i
          simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
          simp [← this, col]
      · rw [← ih (by omega) t ht]
        refine colSum_congr Y _ _ fun y hy => ?_
        have hy' : (y : ℕ) ≠ n := fun h => hcY (by
          have : y = ⟨n, hnm⟩ := Fin.ext h
          exact this ▸ hy)
        unfold mix
        funext i
        by_cases hlt : (y : ℕ) < n
        · simp [hlt, show (y : ℕ) < n + 1 by omega]
        · simp [hlt, show ¬ (y : ℕ) < n + 1 by omega]
  have := key m le_rfl 0 W.zero_mem
  unfold colSum mix at this
  simpa using this

/-- Lemma I. -/
theorem lemmaI (W : Submodule ℂ (Fin P × Fin m → ℂ))
    (hW : ∀ t ∈ W, ∀ Y : Finset (Fin m), Y.Nonempty →
      ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, t (f y, (y : Fin m)) = 0) :
    finrank ℂ ↥W ≤ P - 1 := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · have := Submodule.finrank_le W
    simpa using this
  · have hdiag := diag_of_inj (S W) (inj_on_S W hW)
    have hc := PEqualNP.Gct.Helpers.ProdSigmaChain.chain P m hP (S W) hdiag
    have hle := Submodule.finrank_le (Submodule.span ℂ
        {v : Fin P → ℂ | ∃ (A : Finset (Fin m)) (t : Fin m → (Fin P → ℂ)),
          (∀ i ∈ A, t i ∈ S W i) ∧ v = ∏ i ∈ A, t i})
    rw [Module.finrank_fin_fun] at hle
    rw [finrank_eq_sum W]
    omega

end PEqualNP.Gct.Helpers.InvisibleBlock
