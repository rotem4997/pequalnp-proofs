import PEqualNP.ProofComplexity.Helpers.LiftQuadDefs

/-! Small facts, the round and the assembly for L-pcx-072, on the definitions and interface
statements of `LiftQuadDefs`. -/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily PEqualNP.ProofComplexity.LiftRank

/-! ### Definitions -/


/-! ### Small facts -/

theorem fval_empty {N : ℕ} (β : Fin N → Bool) (a : Fin N × Fin 4 → Bool) :
    fval ∅ β a = gval a := by
  funext j
  simp [fval]

/-- The empty line implies only the trivial equation. -/
theorem impSpace_empty {V : Type} [Fintype V] [DecidableEq V] :
    impSpace (∅ : LinClause V) = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  rintro ⟨g, e⟩ hp
  have hall : ∀ a : V → Bool, g ⬝ᵥ vec a = e := fun a =>
    (mem_impSpace _ _).1 hp a (by rintro ⟨q, hq, -⟩; simp at hq)
  have he : e = 0 := by
    have hv : vec (fun _ : V => false) = 0 := by
      funext v
      simp [vec, Helpers.toZ]
    have := hall (fun _ => false)
    rw [hv, dotProduct_zero] at this
    exact this.symm
  have hg : g = 0 := by
    funext w
    have hv : vec (fun v => decide (v = w)) = Pi.single w 1 := by
      funext v
      by_cases hvw : v = w
      · subst hvw; simp [vec, Helpers.toZ]
      · simp [vec, Helpers.toZ, hvw]
    have := hall (fun v => decide (v = w))
    rw [hv, dotProduct_single, mul_one, he] at this
    simpa using this
  simp [he, hg]

/-- The rank of a line is at most the dimension of the space of equations it implies: the
forms of the line are the first components of elements of `impSpace`. -/
theorem rank_space {V : Type} [Fintype V] [DecidableEq V] (L : LinClause V) :
    linRank L ≤ Module.finrank (ZMod 2) (impSpace L) := by
  classical
  have hle : formSpan L ≤ (impSpace L).map (LinearMap.fst (ZMod 2) (V → ZMod 2) (ZMod 2)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨(ind q.1, Helpers.toZ (!q.2)), ?_, rfl⟩
    rw [SetLike.mem_coe, mem_impSpace]
    intro a ha
    have hn : ¬ LinEqSat a q := fun hs => ha ⟨q, Finset.mem_coe.mp hq, hs⟩
    rw [linEqSat_iff] at hn
    show ind q.1 ⬝ᵥ vec a = Helpers.toZ (!q.2)
    obtain ⟨f, b⟩ := q
    revert hn
    generalize ind f ⬝ᵥ vec a = z
    have key : ∀ (b : Bool) (z : ZMod 2), ¬ z = Helpers.toZ b → z = Helpers.toZ (!b) := by
      decide
    exact key b z
  rw [linRank_eq]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

/-- Local consistency with nothing frozen, on a boundary expander. -/
theorem good_init {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ)
    (β : Fin N → Bool) (hG : IsBdryExpander G s δ) (hδ : 1 ≤ δ) : Good G c s ∅ β := by
  intro U hU
  obtain ⟨x, -, hx⟩ := peel G c ∅ U (fun _ => false) (by
    intro T hT hK i hi
    exfalso
    have h1 := hG T ((Finset.card_le_card hT).trans hU)
    rw [Finset.subset_empty.mp hK, Finset.card_empty] at h1
    have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨i, hi⟩
    have := Nat.mul_le_mul hδ hpos
    omega) U le_rfl
  exact ⟨x, by simp, hx⟩

theorem linEqSat_false {V : Type} (a : V → Bool) (f : Finset V) :
    LinEqSat a (f, false) ↔ ¬ LinEqSat a (f, true) := by
  unfold LinEqSat
  simp

/-- A Res(⊕) derivation from the lifted formula is a generalised derivation with nothing
frozen. -/
theorem gderiv_of_lin {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (β : Fin N → Bool)
    {π : List (LinClause (Fin N × Fin 4))}
    (h : IsLinDerivation ((fun C => linOfClause C) '' liftSys G c) π) : GDeriv G c ∅ β π := by
  classical
  induction h with
  | nil => exact .nil
  | @ax π C _ hC ih =>
    obtain ⟨i, hi⟩ := covers_axiom G c hC
    refine .ax ih ⟨i, fun a ha => ?_⟩
    obtain ⟨i', hi', h'⟩ := hi a ha
    exact ⟨i', hi', by rw [fval_empty]; exact h'⟩
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    refine .res ih hC hD ⟨f, fun a ha => ⟨fun hf hCa => ?_, fun hf hDa => ?_⟩⟩
    · obtain ⟨q, hq, hs⟩ := hCa
      by_cases hqe : q = (f, false)
      · subst hqe
        exact (linEqSat_false a f).1 hs hf
      · exact ha ⟨q, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hqe, hq⟩), hs⟩
    · obtain ⟨q, hq, hs⟩ := hDa
      by_cases hqe : q = (f, true)
      · subst hqe
        exact hf hs
      · exact ha ⟨q, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hqe, hq⟩), hs⟩
  | @weak π C D _ hC hw ih => exact .weak ih hC hw

/-! ### One round and the induction -/

section Round

variable (hC : StmtChain) (hS : StmtStep) (hP : StmtPath) (hSub : StmtSubst)
  (hGs : StmtGoodStep)
include hC hS hP hSub hGs

/-- One round: if `3 * (r + |K₀|) ≤ δ * s` and `1 ≤ r`, a generalised refutation gives one
for a locally consistent frozen system with at most one more block, shorter by `r`. -/
theorem round {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ)
    (hE : IsBdryExpander G s δ) (hs : 3 ≤ s) (hδ : 1 ≤ δ) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (hgood : Good G c s K₀ β) (r : ℕ) (hr : 1 ≤ r)
    (hrs : 3 * (r + K₀.card) ≤ δ * s) (π : List (LinClause (Fin N × Fin 4)))
    (hπ : GRef G c K₀ β π) :
    ∃ (K₁ : Finset (Fin N)) (β₁ : Fin N → Bool) (π' : List (LinClause (Fin N × Fin 4))),
      K₁.card ≤ K₀.card + 1 ∧ Good G c s K₁ β₁ ∧ GRef G c K₁ β₁ π' ∧
        π'.length + r ≤ π.length := by
  classical
  obtain ⟨path, hsub, hhead, hchain, z, hlast, hzf, hrank⟩ :=
    hP m N G c K₀ β s δ hE hs hδ hgood π hπ
  have hrk : r ≤ Module.finrank (ZMod 2) (impSpace z) :=
    le_trans (by omega : r ≤ linRank z) (rank_space z)
  obtain ⟨⟨g, e⟩, hvz, hv0, l', hl'sub, hl'len, hl'⟩ :=
    hC ((Fin N × Fin 4 → ZMod 2) × ZMod 2) (LinClause (Fin N × Fin 4)) impSpace path ∅ z r
      hhead impSpace_empty hlast (hchain.imp fun A B h => hS _ A B h) hr hrk
  have hg : g ≠ 0 := by
    rintro rfl
    obtain ⟨a0, ha0⟩ := hzf
    have h0 : (0 : Fin N × Fin 4 → ZMod 2) ⬝ᵥ vec a0 = e := (mem_impSpace _ _).1 hvz a0 ha0
    rw [zero_dotProduct] at h0
    exact hv0 (by rw [← h0]; rfl)
  obtain ⟨⟨j, u⟩, hw⟩ : ∃ w, g w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (funext hn)
  have key1 : ∀ t : ZMod 2, (if t = 1 then (1 : ZMod 2) else 0) = t := by decide
  have key2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
  have key3 : ∀ t : ZMod 2, t = Helpers.toZ (decide (t = 1)) := by decide
  obtain ⟨f, hf⟩ : ∃ f : Finset (Fin N × Fin 4), f = Finset.univ.filter (fun v => g v = 1) :=
    ⟨_, rfl⟩
  have hind : ind f = g := by
    funext v
    simp only [ind, hf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key1 (g v)
  have hwf : (j, u) ∈ f := by
    simp only [hf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key2 _ hw
  have himp : ∀ A ∈ l', Imp A (f, decide (e = 1)) := by
    intro A hA x hx
    rw [linEqSat_iff]
    show ind f ⬝ᵥ vec x = Helpers.toZ (decide (e = 1))
    have h1 : g ⬝ᵥ vec x = e := (mem_impSpace _ _).1 (hl' A hA) x hx
    rw [hind, h1]
    exact key3 e
  obtain ⟨b, hbK, hgood'⟩ := hGs m N G c s δ K₀ β j hE hδ (by omega) hgood
  obtain ⟨π', hd, hemp, hcount⟩ :=
    hSub m N G c K₀ β j u f (decide (e = 1)) b hwf hbK π hπ.1
  refine ⟨insert j K₀, Function.update β j b, π', Finset.card_insert_le _ _, hgood',
    ⟨hd, hemp hπ.2⟩, ?_⟩
  have := hcount l' (hl'sub.trans hsub) himp
  omega

/-- The induction: `T * (T + 1) ≤ 2 * length` whenever `3 * (T + |K₀|) ≤ δ * s`. -/
theorem quad_bound {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ)
    (hE : IsBdryExpander G s δ) (hs : 3 ≤ s) (hδ : 1 ≤ δ) :
    ∀ (T : ℕ) (K₀ : Finset (Fin N)) (β : Fin N → Bool) (π : List (LinClause (Fin N × Fin 4))),
      Good G c s K₀ β → 3 * (T + K₀.card) ≤ δ * s → GRef G c K₀ β π →
        T * (T + 1) ≤ 2 * π.length := by
  intro T
  induction T with
  | zero => intro _ _ _ _ _ _; simp
  | succ T ih =>
    intro K₀ β π hgood hT hπ
    obtain ⟨K₁, β₁, π', hK₁, hgood', hπ', hlen⟩ :=
      round hC hS hP hSub hGs G c s δ hE hs hδ K₀ β hgood (T + 1) (by omega) hT π hπ
    have h := ih K₁ β₁ π' hgood' (by omega) hπ'
    nlinarith

end Round

/-! ### The assembly -/

/-- The arithmetic of the assembly. -/
theorem assembly_arith (n₁ s₀ L : ℕ) (hs : 0 < s₀) (h3 : 3 * s₀ ≤ n₁)
    (hT : (2 * (n₁ / s₀) / 3) * (2 * (n₁ / s₀) / 3 + 1) ≤ 2 * L) :
    (n₁ * 4) ^ 2 ≤ 576 * s₀ ^ 2 * L := by
  obtain ⟨q, hq⟩ : ∃ q, q = n₁ / s₀ := ⟨_, rfl⟩
  rw [← hq] at hT
  have h1 : n₁ < s₀ * (q + 1) := hq ▸ Nat.lt_mul_div_succ n₁ hs
  have h2 : 3 ≤ q := hq ▸ (Nat.le_div_iff_mul_le hs).mpr h3
  obtain ⟨T, hTd⟩ : ∃ T, T = 2 * q / 3 := ⟨_, rfl⟩
  rw [← hTd] at hT
  have hA : q ≤ 3 * T := by omega
  have hB : 2 * q ≤ 3 * (T + 1) := by omega
  have hC' : q * (2 * q) ≤ (3 * T) * (3 * (T + 1)) := Nat.mul_le_mul hA hB
  have hq9 : q * q ≤ 9 * L := by nlinarith
  have hn : n₁ ≤ 2 * s₀ * q := by nlinarith
  have hn2 : n₁ * n₁ ≤ (2 * s₀ * q) * (2 * s₀ * q) := Nat.mul_le_mul hn hn
  have hs2 : s₀ * s₀ * (q * q) ≤ s₀ * s₀ * (9 * L) := Nat.mul_le_mul_left _ hq9
  nlinarith

/-- L-pcx-072 from the interface statements and the expanders of L-pcx-043. -/
theorem assembly_of : StmtAssemblyQuad := by
  classical
  intro hC hS hP hSub hGs
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  refine ⟨4 * b, 4 * b, 576 * s₀ ^ 2, fun N => ?_⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max N (max n₀ (3 * s₀)) := ⟨_, rfl⟩
  have hN : N ≤ n₁ := hn₁ ▸ le_max_left _ _
  have hn0 : n₀ ≤ n₁ := hn₁ ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hn3 : 3 * s₀ ≤ n₁ := hn₁ ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨G, hLd, -, hE⟩ := hG n₁ hn0
  obtain ⟨S, ⟨i₀, hi₀⟩, hS'⟩ := dependency n₁ G
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
  · intro C hC'
    obtain ⟨C0, hC0, rfl⟩ := hfin.mem_toFinset.mp hC'
    exact le_trans Finset.card_image_le (formula_width _ _ G c b hLd C0 hC0)
  · rw [Set.Finite.coe_toFinset]
    exact rename_pc _ _ e _ _ (formula_pc _ _ G c b hLd S hS' hodd)
  · intro π hπ
    rw [Set.Finite.coe_toFinset] at hπ
    have href := back_refutation e (liftSys G c) π hπ
    have h3 : 3 ≤ n₁ / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr hn3
    have hgr : GRef G c ∅ (fun _ => false) (π.map (backLin e)) :=
      ⟨gderiv_of_lin G c _ href.1, href.2⟩
    have hq := quad_bound hC hS hP hSub hGs G c (n₁ / s₀) 2 hE h3 (by norm_num)
      (2 * (n₁ / s₀) / 3) ∅ (fun _ => false) _ (good_init G c _ 2 _ hE (by norm_num))
      (by rw [Finset.card_empty]; omega) hgr
    rw [List.length_map] at hq
    exact assembly_arith n₁ s₀ π.length hs₀ hn3 hq

end PEqualNP.ProofComplexity.LiftQuad
