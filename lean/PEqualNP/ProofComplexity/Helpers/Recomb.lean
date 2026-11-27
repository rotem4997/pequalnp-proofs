import PEqualNP.ProofComplexity.Helpers.BitPHP

/-!
# Helpers: recombination at a hyperplane, rank form (L-pcx-075)

* Composition of derivations (`deriv_append`): a derivation from `B` whose axioms are axioms of
  `A` or lines of an earlier derivation from `A` continues that derivation.
* Inserting one equation into every line is a homomorphism of derivations (`insert_derivation`).
* Mapping every line through a map of equations that comes from a map of points and sends the
  two equations `f = 0`, `f = 1` to two opposite equations maps derivations to derivations, one
  extra weakening line per resolution (`map_derivation`).
* The affine substitution onto the hyperplane `{f0 = c}` along a point `v0 ∈ f0`: `hypEq`,
  `hypLin`, `hypPt`, with the facts (i) satisfaction transfer `hypLin_sat`, (ii) the forms of the
  image miss `v0` (`hypLin_forms`), (iii) rank does not grow (`linRank_hypLin_le`) and drops by
  one on a line holding an equation with form `f0` (`linRank_hypLin_lt`), (iv)
  `hypEq_self`.
* The recombination theorem `recomb`.
-/

namespace PEqualNP.ProofComplexity.Recomb

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

/-! ### Composition of derivations -/

/-- Composition: `π` is a derivation from `B`, and every clause of `B` is a clause of `A` or a
line of the derivation `π0` from `A`. Then `π ++ π0` (newest first) is a derivation from `A`. -/
theorem deriv_append {V : Type} [DecidableEq V] {A B : Set (LinClause V)}
    {π0 π : List (LinClause V)} (h0 : IsLinDerivation A π0) (h : IsLinDerivation B π)
    (hB : ∀ C ∈ B, C ∈ A ∨ C ∈ π0) : IsLinDerivation A (π ++ π0) := by
  induction h with
  | nil => simpa using h0
  | @ax π C _ hC ih =>
    rcases hB C hC with hA | h0C
    · exact IsLinDerivation.ax ih hA
    · exact IsLinDerivation.weak ih (List.mem_append_right _ h0C) (fun _ ha => ha)
  | @res π C D R _ hC hD hR ih =>
    exact IsLinDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR
  | @weak π C D _ hC hw ih =>
    exact IsLinDerivation.weak ih (List.mem_append_left _ hC) hw

/-- Weakening by inclusion. -/
theorem weak_of_subset {V : Type} {C D : LinClause V} (h : C ⊆ D) :
    ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  rintro a ⟨q, hq, hs⟩
  exact ⟨q, h hq, hs⟩

/-! ### Inserting one equation into every line -/

theorem insert_resolvent {V : Type} [DecidableEq V] {C D R : LinClause V} (q : LinEq V)
    (h : IsLinResolvent C D R) : IsLinResolvent (insert q C) (insert q D) (insert q R) := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  refine ⟨f, Finset.mem_insert_of_mem hC, Finset.mem_insert_of_mem hD, ?_⟩
  have hne : ((f, false) : LinEq V) ≠ (f, true) := by simp
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · by_cases hx : x = (f, false)
      · exact Or.inr ⟨hx ▸ hne, Or.inl rfl⟩
      · exact Or.inl ⟨hx, Or.inl rfl⟩
    · exact Or.inl ⟨h1, Or.inr h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  · rintro (⟨h1, rfl | h2⟩ | ⟨h1, rfl | h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem insert_weak {V : Type} [DecidableEq V] {C D : LinClause V} (q : LinEq V)
    (hw : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D) :
    ∀ a : V → Bool, LinClauseSat a (insert q C) → LinClauseSat a (insert q D) := by
  rintro a ⟨e, he, hs⟩
  rcases Finset.mem_insert.mp he with rfl | he
  · exact ⟨e, Finset.mem_insert_self _ _, hs⟩
  · obtain ⟨e', he', hs'⟩ := hw a ⟨e, he, hs⟩
    exact ⟨e', Finset.mem_insert_of_mem he', hs'⟩

/-- Inserting the equation `q` into every line maps a derivation from `B` to a derivation from
the clauses of `B` with `q` inserted, line for line. -/
theorem insert_derivation {V : Type} [DecidableEq V] (q : LinEq V) {B : Set (LinClause V)}
    {π : List (LinClause V)} (h : IsLinDerivation B π) :
    IsLinDerivation ((fun C => insert q C) '' B) (π.map (fun C => insert q C)) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | ax _ hC ih => exact IsLinDerivation.ax ih ⟨_, hC, rfl⟩
  | res _ hC hD hR ih =>
    exact IsLinDerivation.res ih (List.mem_map.2 ⟨_, hC, rfl⟩) (List.mem_map.2 ⟨_, hD, rfl⟩)
      (insert_resolvent q hR)
  | weak _ hC hw ih =>
    exact IsLinDerivation.weak ih (List.mem_map.2 ⟨_, hC, rfl⟩) (insert_weak q hw)

/-! ### Mapping lines through a map of equations -/

theorem erase_image_subset {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β)
    (C : Finset α) (q0 : α) : (C.image g).erase (g q0) ⊆ (C.erase q0).image g := by
  intro x hx
  obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨?_, hq⟩, rfl⟩
  rintro rfl
  exact hne rfl

theorem image_sat {V : Type} [DecidableEq V] (g : LinEq V → LinEq V)
    (P : (V → Bool) → (V → Bool)) (hP : ∀ a q, LinEqSat a (g q) ↔ LinEqSat (P a) q)
    (a : V → Bool) (C : LinClause V) : LinClauseSat a (C.image g) ↔ LinClauseSat (P a) C := by
  constructor
  · rintro ⟨q', hq', hs⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    exact ⟨q, hq, (hP a q).mp hs⟩
  · rintro ⟨q, hq, hs⟩
    exact ⟨g q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, (hP a q).mpr hs⟩

/-- Line-by-line simulation through a map of equations `g` that comes from the map of points
`P` and sends `f = 0`, `f = 1` to two opposite equations. Each line of the new derivation is
contained in the image of a line of the old one. -/
theorem map_derivation {V : Type} [DecidableEq V] (g : LinEq V → LinEq V)
    (P : (V → Bool) → (V → Bool)) (hP : ∀ a q, LinEqSat a (g q) ↔ LinEqSat (P a) q)
    (hg : ∀ f : Finset V, ∃ h : Finset V, ∃ β : Bool, g (f, false) = (h, β) ∧ g (f, true) = (h, !β))
    {B : Set (LinClause V)} {π : List (LinClause V)} (hπ : IsLinDerivation B π) :
    ∃ π' : List (LinClause V), IsLinDerivation ((fun C => C.image g) '' B) π' ∧
      (∀ L ∈ π, L.image g ∈ π') ∧ ∀ L' ∈ π', ∃ L ∈ π, L' ⊆ L.image g := by
  induction hπ with
  | nil => exact ⟨[], IsLinDerivation.nil, by simp, by simp⟩
  | @ax π C _ hC ih =>
    obtain ⟨π', hd, hmem, hsub⟩ := ih
    refine ⟨C.image g :: π', IsLinDerivation.ax hd ⟨C, hC, rfl⟩, ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem L hL)
    · intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact ⟨C, List.mem_cons_self, subset_refl _⟩
      · obtain ⟨L, hL, h⟩ := hsub L' hL'
        exact ⟨L, List.mem_cons_of_mem _ hL, h⟩
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨π', hd, hmem, hsub⟩ := ih
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    obtain ⟨h, β, e0, e1⟩ := hg f
    have h0 : (h, β) ∈ C.image g := e0 ▸ Finset.mem_image_of_mem _ hfC
    have h1 : (h, !β) ∈ D.image g := e1 ▸ Finset.mem_image_of_mem _ hfD
    have hs : (C.image g).erase (h, β) ∪ (D.image g).erase (h, !β) ⊆
        (C.erase (f, false) ∪ D.erase (f, true)).image g := by
      rw [Finset.image_union, ← e0, ← e1]
      exact Finset.union_subset_union (erase_image_subset _ _ _)
        (erase_image_subset _ _ _)
    -- the resolvent of the two image lines, in the order given by `β`
    obtain ⟨Rl, hRl, hRlsub⟩ : ∃ Rl, IsLinDerivation ((fun C => C.image g) '' B) (Rl :: π') ∧
        Rl ⊆ (C.erase (f, false) ∪ D.erase (f, true)).image g := by
      cases β with
      | false => exact ⟨_, IsLinDerivation.res hd (hmem C hC) (hmem D hD) ⟨h, h0, h1, rfl⟩, hs⟩
      | true =>
        refine ⟨_, IsLinDerivation.res hd (hmem D hD) (hmem C hC) ⟨h, h1, h0, rfl⟩, ?_⟩
        rw [Finset.union_comm]
        exact hs
    refine ⟨(C.erase (f, false) ∪ D.erase (f, true)).image g :: Rl :: π',
      IsLinDerivation.weak hRl List.mem_cons_self (weak_of_subset hRlsub), ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem L hL))
    · intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact ⟨_, List.mem_cons_self, subset_refl _⟩
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact ⟨_, List.mem_cons_self, hRlsub⟩
      · obtain ⟨L, hL, h⟩ := hsub L' hL'
        exact ⟨L, List.mem_cons_of_mem _ hL, h⟩
  | @weak π C D _ hC hw ih =>
    obtain ⟨π', hd, hmem, hsub⟩ := ih
    refine ⟨D.image g :: π', IsLinDerivation.weak hd (hmem C hC) (fun a ha => ?_), ?_, ?_⟩
    · rw [image_sat g P hP] at ha ⊢
      exact hw _ ha
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem L hL)
    · intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact ⟨D, List.mem_cons_self, subset_refl _⟩
      · obtain ⟨L, hL, h⟩ := hsub L' hL'
        exact ⟨L, List.mem_cons_of_mem _ hL, h⟩

/-! ### The substitution onto a hyperplane -/

/-- Substitution onto the hyperplane `{f0 = c}` along `v0`: an equation `h = b` with `v0 ∈ h`
becomes `h + f0 = b + c`; the others are kept. -/
def hypEq {V : Type} [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool) (q : LinEq V) :
    LinEq V :=
  if v0 ∈ q.1 then (symmDiff q.1 f0, xor q.2 c) else q

/-- `hypEq` applied to every equation of a line. -/
def hypLin {V : Type} [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool) (C : LinClause V) :
    LinClause V :=
  C.image (hypEq f0 v0 c)

/-- The point map: flip `v0` when the parity of `f0` is not `c`. It lands in `{f0 = c}`. -/
def hypPt {V : Type} [Fintype V] [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool)
    (a : V → Bool) : V → Bool :=
  Function.update a v0 (if ind f0 ⬝ᵥ vec a = toZ c then a v0 else !a v0)

theorem ind_symmDiff {V : Type} [DecidableEq V] (s t : Finset V) :
    ind (symmDiff s t) = ind s + ind t := by
  funext v
  simp only [ind, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp [hs, ht]; decide

theorem toZ_xor (b c : Bool) : toZ (xor b c) = toZ b + toZ c := by
  cases b <;> cases c <;> decide

theorem vec_update {V : Type} [DecidableEq V] (a : V → Bool) (v0 : V) (b : Bool) :
    vec (Function.update a v0 b) = Function.update (vec a) v0 (toZ b) := by
  funext v
  by_cases h : v = v0
  · subst h; simp [vec]
  · simp [vec, h]

theorem dot_update {V : Type} [Fintype V] [DecidableEq V] (u x : V → ZMod 2) (v0 : V)
    (y : ZMod 2) : u ⬝ᵥ Function.update x v0 y = u ⬝ᵥ x + u v0 * (y - x v0) := by
  have : Function.update x v0 y = x + Pi.single v0 (y - x v0) := by
    funext v
    by_cases h : v = v0
    · subst h; simp
    · simp [h]
  rw [this, dotProduct_add, dotProduct_single]

/-- Fact (i), one equation. -/
theorem hypEq_sat {V : Type} [Fintype V] [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool) (a : V → Bool) (q : LinEq V) :
    LinEqSat a (hypEq f0 v0 c q) ↔ LinEqSat (hypPt f0 v0 c a) q := by
  rw [linEqSat_iff, linEqSat_iff]
  set δ : ZMod 2 := toZ (if ind f0 ⬝ᵥ vec a = toZ c then a v0 else !a v0) - toZ (a v0) with hδ
  have hdot : ∀ s : Finset V, ind s ⬝ᵥ vec (hypPt f0 v0 c a) =
      ind s ⬝ᵥ vec a + ind s v0 * δ := by
    intro s
    rw [hypPt, vec_update, dot_update]
    rfl
  have hf : toZ c = ind f0 ⬝ᵥ vec a + δ := by
    rw [hδ]
    by_cases h : ind f0 ⬝ᵥ vec a = toZ c
    · rw [if_pos h, h]; ring
    · rw [if_neg h]
      have key : ∀ x : ZMod 2, ∀ b c : Bool, x ≠ toZ c → toZ c = x + (toZ (!b) - toZ b) := by
        decide
      exact key _ _ _ h
  rw [hdot]
  unfold hypEq
  by_cases hq : v0 ∈ q.1
  · rw [if_pos hq]
    simp only [ind_symmDiff, toZ_xor, add_dotProduct, hf]
    have h1 : ind q.1 v0 = 1 := by simp [ind, hq]
    rw [h1, one_mul]
    have key : ∀ X Y Z d : ZMod 2, X + Y = Z + (Y + d) ↔ X + d = Z := by decide
    exact key _ _ _ _
  · rw [if_neg hq]
    have h0 : ind q.1 v0 = 0 := by simp [ind, hq]
    rw [h0, zero_mul, add_zero]

/-- Fact (i): satisfaction transfer for lines. -/
theorem hypLin_sat {V : Type} [Fintype V] [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool) (a : V → Bool) (C : LinClause V) :
    LinClauseSat a (hypLin f0 v0 c C) ↔ LinClauseSat (hypPt f0 v0 c a) C :=
  image_sat _ _ (hypEq_sat f0 v0 c) a C

/-- `hypEq` sends `f = 0` and `f = 1` to two opposite equations. -/
theorem hypEq_pair {V : Type} [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool)
    (f : Finset V) : ∃ h : Finset V, ∃ β : Bool,
      hypEq f0 v0 c (f, false) = (h, β) ∧ hypEq f0 v0 c (f, true) = (h, !β) := by
  by_cases hf : v0 ∈ f
  · exact ⟨symmDiff f f0, c, by simp [hypEq, hf], by simp [hypEq, hf]⟩
  · exact ⟨f, false, by simp [hypEq, hf], by simp [hypEq, hf]⟩

/-- The point map is the identity on `{f0 = c}`. -/
theorem hypPt_eq_self {V : Type} [Fintype V] [DecidableEq V] {f0 : Finset V} {v0 : V}
    {c : Bool} {a : V → Bool} (h : ind f0 ⬝ᵥ vec a = toZ c) : hypPt f0 v0 c a = a := by
  simp [hypPt, h]

/-- Fact (ii): the forms of `hypLin` miss `v0`. -/
theorem hypLin_forms {V : Type} [DecidableEq V] {f0 : Finset V} {v0 : V} (hv0 : v0 ∈ f0)
    (c : Bool) (C : LinClause V) : ∀ q ∈ hypLin f0 v0 c C, v0 ∉ q.1 := by
  intro q hq
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hq
  unfold hypEq
  by_cases h : v0 ∈ q.1
  · rw [if_pos h]
    simp [Finset.mem_symmDiff, h, hv0]
  · rw [if_neg h]; exact h

/-- Fact (iv). -/
theorem hypEq_self {V : Type} [DecidableEq V] {f0 : Finset V} {v0 : V} (hv0 : v0 ∈ f0)
    (c b : Bool) : hypEq f0 v0 c (f0, b) = (∅, xor b c) := by
  simp [hypEq, hv0]

/-- On forms, `hypEq` is the linear map `x ↦ x + x(v0) f0`. -/
def hypMap {V : Type} [DecidableEq V] (f0 : Finset V) (v0 : V) :
    (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun x := x + x v0 • ind f0
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

theorem ind_hypEq {V : Type} [DecidableEq V] {f0 : Finset V} {v0 : V} (c : Bool)
    (q : LinEq V) : ind (hypEq f0 v0 c q).1 = hypMap f0 v0 (ind q.1) := by
  show _ = ind q.1 + ind q.1 v0 • ind f0
  unfold hypEq
  by_cases h : v0 ∈ q.1
  · rw [if_pos h, ind_symmDiff]
    simp [ind, h]
  · rw [if_neg h]
    simp [ind, h]

theorem formSpan_hypLin {V : Type} [DecidableEq V] (f0 : Finset V) (v0 : V) (c : Bool)
    (C : LinClause V) : formSpan (hypLin f0 v0 c C) = (formSpan C).map (hypMap f0 v0) := by
  unfold formSpan
  rw [Submodule.map_span]
  congr 1
  rw [hypLin, Finset.coe_image, Set.image_image, Set.image_image]
  exact Set.image_congr fun q _ => ind_hypEq c q

/-- Rank is monotone under inclusion. -/
theorem linRank_mono {V : Type} [Fintype V] [DecidableEq V] {C D : LinClause V} (h : C ⊆ D) :
    linRank C ≤ linRank D := by
  rw [linRank_eq, linRank_eq]
  apply Submodule.finrank_mono
  unfold formSpan
  exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 h))

/-- Inserting one equation raises the rank by at most one. -/
theorem linRank_insert_le {V : Type} [Fintype V] [DecidableEq V] (q : LinEq V)
    (C : LinClause V) : linRank (insert q C) ≤ linRank C + 1 := by
  rw [linRank_eq, linRank_eq, formSpan_insert, sup_comm]
  by_cases h : ind q.1 ∈ formSpan C
  · rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 h)]
    omega
  · rw [Submodule.finrank_sup_span_singleton h]

/-- Fact (iii), weak form. -/
theorem linRank_hypLin_le {V : Type} [Fintype V] [DecidableEq V] (f0 : Finset V) (v0 : V)
    (c : Bool) (C : LinClause V) : linRank (hypLin f0 v0 c C) ≤ linRank C := by
  rw [linRank_eq, linRank_eq, formSpan_hypLin]
  exact Submodule.finrank_map_le _ _

/-- A linear map that kills a nonzero vector of `S` lowers the dimension of `S`. -/
theorem finrank_map_lt_of_ker {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (M : W →ₗ[K] W) (S : Submodule K W) {x : W} (hx : x ∈ S)
    (hx0 : x ≠ 0) (hM : M x = 0) : Module.finrank K (S.map M) + 1 ≤ Module.finrank K S := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (M.domRestrict S)
  rw [LinearMap.range_domRestrict] at hrn
  have hk : (⟨x, hx⟩ : S) ∈ LinearMap.ker (M.domRestrict S) := by
    rw [LinearMap.mem_ker]
    exact hM
  have hpos : 0 < Module.finrank K (LinearMap.ker (M.domRestrict S)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.2
    refine ⟨⟨⟨x, hx⟩, hk⟩, fun h => hx0 ?_⟩
    have := congrArg (fun y : LinearMap.ker (M.domRestrict S) => ((y : S) : W)) h
    simpa using this
  omega

/-- Fact (iii), strict form: on a line holding an equation with form `f0` the rank drops. -/
theorem linRank_hypLin_lt {V : Type} [Fintype V] [DecidableEq V] {f0 : Finset V} {v0 : V}
    (hv0 : v0 ∈ f0) (c : Bool) {C : LinClause V} {b : Bool} (hC : (f0, b) ∈ C) :
    linRank (hypLin f0 v0 c C) + 1 ≤ linRank C := by
  rw [linRank_eq, linRank_eq, formSpan_hypLin]
  have h1 : ind f0 v0 = 1 := by simp [ind, hv0]
  refine finrank_map_lt_of_ker (hypMap f0 v0) (formSpan C) (ind_mem_formSpan hC) ?_ ?_
  · intro h
    have := congrFun h v0
    rw [h1] at this
    exact one_ne_zero this
  · show ind f0 + ind f0 v0 • ind f0 = 0
    rw [h1, one_smul]
    funext v
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize ind f0 v = z
    revert z
    decide

/-! ### Recombination -/

/-- The bridge for one axiom `C`: from `C` and the unit line `{(f0, !c0)}`, at rank at most
`w + 1`, a derivation of the image of `insert (f0, c0) C` under the substitution. -/
theorem bridge_step {V : Type} [Fintype V] [DecidableEq V] {A : Set (LinClause V)}
    {f0 : Finset V} {v0 : V} (hv0 : v0 ∈ f0) {c0 : Bool} {w k : ℕ}
    (hw : ∀ C ∈ A, linRank C ≤ w) (hk : w + 1 ≤ k) {π : List (LinClause V)}
    (hπ : IsLinDerivation A π) (hu : ({(f0, !c0)} : LinClause V) ∈ π) {C : LinClause V}
    (hC : C ∈ A) :
    ∃ ρ : List (LinClause V), IsLinDerivation A (ρ ++ π) ∧
      hypLin f0 v0 (!c0) (insert (f0, c0) C) ∈ ρ ∧ ∀ L ∈ ρ, linRank L ≤ k := by
  have hXr : linRank (hypLin f0 v0 (!c0) (insert (f0, c0) C)) ≤ w := by
    have h1 := linRank_hypLin_lt hv0 (!c0) (Finset.mem_insert_self (f0, c0) C)
    have h2 := linRank_insert_le (f0, c0) C
    have h3 := hw C hC
    omega
  set X := hypLin f0 v0 (!c0) (insert (f0, c0) C) with hX
  have hX0r : linRank (insert (f0, c0) X) ≤ k := by
    have := linRank_insert_le (f0, c0) X; omega
  have hX1r : linRank (insert (f0, !c0) X) ≤ k := by
    have := linRank_insert_le (f0, !c0) X; omega
  have hCr : linRank C ≤ k := by have := hw C hC; omega
  -- X with `f0 = c0` is a weakening of `C`
  have hw0 : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a (insert (f0, c0) X) := by
    intro a ha
    by_cases hs : LinEqSat a (f0, c0)
    · exact ⟨_, Finset.mem_insert_self _ _, hs⟩
    · have hpt : ind f0 ⬝ᵥ vec a = toZ (!c0) := by
        rw [linEqSat_iff] at hs
        have key : ∀ x : ZMod 2, ∀ b : Bool, x ≠ toZ b → x = toZ (!b) := by decide
        exact key _ _ hs
      have : LinClauseSat a X := by
        rw [hX, hypLin_sat, hypPt_eq_self hpt]
        exact weak_of_subset (Finset.subset_insert _ _) a ha
      exact weak_of_subset (Finset.subset_insert _ _) a this
  have hw1 : ∀ a : V → Bool, LinClauseSat a {(f0, !c0)} → LinClauseSat a (insert (f0, !c0) X) :=
    weak_of_subset (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
  have hd0 : IsLinDerivation A (insert (f0, !c0) X :: insert (f0, c0) X :: C :: π) :=
    IsLinDerivation.weak (IsLinDerivation.weak (IsLinDerivation.ax hπ hC) List.mem_cons_self hw0)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)) hw1
  have hR : ∀ R : LinClause V, R ⊆ X →
      IsLinDerivation A (R :: insert (f0, !c0) X :: insert (f0, c0) X :: C :: π) →
      ∃ ρ : List (LinClause V), IsLinDerivation A (ρ ++ π) ∧ X ∈ ρ ∧ ∀ L ∈ ρ, linRank L ≤ k := by
    intro R hRX hd
    refine ⟨[X, R, insert (f0, !c0) X, insert (f0, c0) X, C],
      IsLinDerivation.weak hd List.mem_cons_self (weak_of_subset hRX), by simp, ?_⟩
    intro L hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl
    · exact le_trans hXr (by omega)
    · exact le_trans (linRank_mono hRX) (le_trans hXr (by omega))
    · exact hX1r
    · exact hX0r
    · exact hCr
  cases c0 with
  | false =>
    exact hR _ (Finset.union_subset (Finset.erase_insert_subset _ _)
      (Finset.erase_insert_subset _ _))
      (IsLinDerivation.res hd0 (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
        ⟨f0, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, rfl⟩)
  | true =>
    exact hR _ (Finset.union_subset (Finset.erase_insert_subset _ _)
      (Finset.erase_insert_subset _ _))
      (IsLinDerivation.res hd0 List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
        ⟨f0, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, rfl⟩)

/-- The bridges for a list of axioms. -/
theorem bridges {V : Type} [Fintype V] [DecidableEq V] {A : Set (LinClause V)}
    {f0 : Finset V} {v0 : V} (hv0 : v0 ∈ f0) {c0 : Bool} {w k : ℕ}
    (hw : ∀ C ∈ A, linRank C ≤ w) (hk : w + 1 ≤ k) {π : List (LinClause V)}
    (hπ : IsLinDerivation A π) (hu : ({(f0, !c0)} : LinClause V) ∈ π) :
    ∀ l : List (LinClause V), (∀ C ∈ l, C ∈ A) →
      ∃ ρ : List (LinClause V), IsLinDerivation A (ρ ++ π) ∧
        (∀ C ∈ l, hypLin f0 v0 (!c0) (insert (f0, c0) C) ∈ ρ) ∧ ∀ L ∈ ρ, linRank L ≤ k
  | [], _ => ⟨[], by simpa using hπ, by simp, by simp⟩
  | C :: l, hl => by
    obtain ⟨ρ, hd, hmem, hr⟩ := bridges hv0 hw hk hπ hu l (fun C hC => hl C (List.mem_cons_of_mem _ hC))
    obtain ⟨ρ', hd', hmem', hr'⟩ := bridge_step hv0 hw hk hd
      (List.mem_append_right _ hu) (hl C List.mem_cons_self)
    refine ⟨ρ' ++ ρ, by simpa using hd', ?_, ?_⟩
    · intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · exact List.mem_append_left _ hmem'
      · exact List.mem_append_right _ (hmem E hE)
    · intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · exact hr' L hL
      · exact hr L hL

/-- Recombination at a hyperplane, rank form. -/
theorem recomb {V : Type} [Fintype V] [DecidableEq V] (A : Set (LinClause V)) (w k : ℕ)
    (f0 : Finset V) (c0 : Bool) (hf0 : f0.Nonempty) (hw : ∀ C ∈ A, linRank C ≤ w)
    (hk : w + 1 ≤ k)
    (hA : ∃ π : List (LinClause V), IsLinDerivation A π ∧
      ({(f0, !c0)} : LinClause V) ∈ π ∧ ∀ L ∈ π, linRank L ≤ k)
    (hB : ∃ π : List (LinClause V), IsLinDerivation ((fun C => insert (f0, c0) C) '' A) π ∧
      ({(f0, c0)} : LinClause V) ∈ π ∧ ∀ L ∈ π, (f0, c0) ∈ L ∧ linRank L ≤ k + 1) :
    ∃ π : List (LinClause V), IsLinDerivation A π ∧ (∅ : LinClause V) ∈ π ∧
      ∀ L ∈ π, linRank L ≤ k := by
  classical
  obtain ⟨v0, hv0⟩ := hf0
  obtain ⟨πA, hdA, hu, hrA⟩ := hA
  obtain ⟨πB, hdB, hfin, hrB⟩ := hB
  have hfinA : A.Finite := Set.toFinite A
  obtain ⟨ρ, hdρ, hmemρ, hrρ⟩ := bridges hv0 hw hk hdA hu hfinA.toFinset.toList
    (fun C hC => hfinA.mem_toFinset.1 (Finset.mem_toList.1 hC))
  obtain ⟨π', hd', hmem', hsub'⟩ := map_derivation (hypEq f0 v0 (!c0)) (hypPt f0 v0 (!c0))
    (hypEq_sat f0 v0 (!c0)) (hypEq_pair f0 v0 (!c0)) hdB
  have happ : IsLinDerivation A (π' ++ (ρ ++ πA)) := by
    refine deriv_append hdρ hd' ?_
    rintro _ ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    exact Or.inr (List.mem_append_left _
      (hmemρ C (Finset.mem_toList.2 (hfinA.mem_toFinset.2 hC))))
  have hlast : ({(f0, c0)} : LinClause V).image (hypEq f0 v0 (!c0)) ∈ π' :=
    hmem' _ hfin
  refine ⟨∅ :: (π' ++ (ρ ++ πA)), IsLinDerivation.weak happ (List.mem_append_left _ hlast) ?_,
    List.mem_cons_self, ?_⟩
  · intro a ha
    exfalso
    rw [Finset.image_singleton, hypEq_self hv0] at ha
    obtain ⟨q, hq, hs⟩ := ha
    rw [Finset.mem_singleton] at hq
    subst hq
    cases c0 <;> simp [LinEqSat] at hs
  · intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · rw [linRank_eq, formSpan, Finset.coe_empty, Set.image_empty, Submodule.span_empty,
        finrank_bot]
      exact Nat.zero_le _
    rcases List.mem_append.mp hL with hL | hL
    · obtain ⟨L0, hL0, hsub⟩ := hsub' L hL
      obtain ⟨hc, hr⟩ := hrB L0 hL0
      have h1 := linRank_mono hsub
      have h2 := linRank_hypLin_lt hv0 (!c0) hc
      unfold hypLin at h2
      omega
    rcases List.mem_append.mp hL with hL | hL
    · exact hrρ L hL
    · exact hrA L hL

end PEqualNP.ProofComplexity.Recomb
