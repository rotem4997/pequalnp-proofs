import PEqualNP.ProofComplexity.Helpers.LiftQuadDefs

/-!
# Leg C of L-pcx-072: substitution and pruning (`StmtSubst`)

Conjecture until the checker accepts it.

The substitution `σ` fixes the three bits of block `j` other than `u` to constants that force
gadget value `b` (`ip2_stifled`) and sets bit `(j, u)` to the affine form that makes `f = a`
false. On vectors over the two-element field it is an affine map `x ↦ lin x + kk`, so the image
of an equation is again an equation (`sEq`, obtained by duality), with
`LinEqSat y (sEq q) ↔ LinEqSat (σ y) q`.

The pruning (`prune_deriv`) is stated for any map of assignments with such an equation image
that turns the frozen gadget values of one system into those of another: keep the images of the
entries whose image is falsifiable. A resolvent with a deleted premise becomes a weakening of
the image of the other premise.
-/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily PEqualNP.ProofComplexity.LiftRank

open Classical in
/-- The images of the entries of `π` whose image is falsifiable, in order. -/
noncomputable def prune {V : Type} (sE : LinEq V → LinEq V) [DecidableEq V]
    (π : List (LinClause V)) : List (LinClause V) :=
  (π.filter (fun L => decide (Falsifiable (L.image sE)))).map (fun L => L.image sE)

theorem prune_cons_pos {V : Type} [DecidableEq V] (sE : LinEq V → LinEq V)
    (L : LinClause V) (π : List (LinClause V)) (h : Falsifiable (L.image sE)) :
    prune sE (L :: π) = L.image sE :: prune sE π := by
  classical
  unfold prune
  rw [List.filter_cons_of_pos (by simpa using h)]
  rfl

theorem prune_cons_neg {V : Type} [DecidableEq V] (sE : LinEq V → LinEq V)
    (L : LinClause V) (π : List (LinClause V)) (h : ¬ Falsifiable (L.image sE)) :
    prune sE (L :: π) = prune sE π := by
  classical
  unfold prune
  rw [List.filter_cons_of_neg (by simpa using h)]

theorem mem_prune {V : Type} [DecidableEq V] (sE : LinEq V → LinEq V)
    {L : LinClause V} {π : List (LinClause V)} (hL : L ∈ π) (h : Falsifiable (L.image sE)) :
    L.image sE ∈ prune sE π := by
  classical
  unfold prune
  exact List.mem_map.2 ⟨L, List.mem_filter.2 ⟨hL, by simpa using h⟩, rfl⟩

/-- The count: every entry of the sublist is deleted. -/
theorem prune_length {V : Type} [DecidableEq V] (sE : LinEq V → LinEq V)
    {l' π : List (LinClause V)} (hl : l'.Sublist π)
    (hd : ∀ L ∈ l', ¬ Falsifiable (L.image sE)) :
    (prune sE π).length + l'.length ≤ π.length := by
  induction hl with
  | slnil => simp [prune]
  | @cons l₁ l₂ x _ ih =>
    by_cases hx : Falsifiable (x.image sE)
    · rw [prune_cons_pos sE x l₂ hx, List.length_cons, List.length_cons]
      have := ih hd
      omega
    · rw [prune_cons_neg sE x l₂ hx, List.length_cons]
      have := ih hd
      omega
  | @cons_cons l₁ l₂ x _ ih =>
    have hx : ¬ Falsifiable (x.image sE) := hd x (List.mem_cons_self ..)
    rw [prune_cons_neg sE x l₂ hx, List.length_cons, List.length_cons]
    have := ih (fun L hL => hd L (List.mem_cons_of_mem _ hL))
    omega

theorem sat_image {V : Type} [DecidableEq V] {σ : (V → Bool) → (V → Bool)}
    {sE : LinEq V → LinEq V} (hE : ∀ y q, LinEqSat y (sE q) ↔ LinEqSat (σ y) q)
    (y : V → Bool) (L : LinClause V) :
    LinClauseSat y (L.image sE) ↔ LinClauseSat (σ y) L := by
  unfold LinClauseSat
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨q₀, hq₀, (hE y q₀).1 hs⟩
  · rintro ⟨q₀, hq₀, hs⟩
    exact ⟨sE q₀, Finset.mem_image_of_mem _ hq₀, (hE y q₀).2 hs⟩

theorem linEqSat_false_iff {V : Type} (y : V → Bool) (g : Finset V) :
    LinEqSat y (g, false) ↔ ¬ LinEqSat y (g, true) := by
  unfold LinEqSat
  simp

/-- The pruned image of a generalised derivation is a generalised derivation. -/
theorem prune_deriv {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (K₀ K₁ : Finset (Fin N))
    (β β₁ : Fin N → Bool) (σ : (Fin N × Fin 4 → Bool) → (Fin N × Fin 4 → Bool))
    (sE : LinEq (Fin N × Fin 4) → LinEq (Fin N × Fin 4))
    (hE : ∀ y q, LinEqSat y (sE q) ↔ LinEqSat (σ y) q)
    (hf : ∀ y, fval K₀ β (σ y) = fval K₁ β₁ y) :
    ∀ π, GDeriv G c K₀ β π → GDeriv G c K₁ β₁ (prune sE π) := by
  intro π hπ
  induction hπ with
  | nil => simpa [prune] using GDeriv.nil
  | @ax π L _ hL ih =>
    by_cases hF : Falsifiable (L.image sE)
    · rw [prune_cons_pos sE L π hF]
      obtain ⟨i, hi⟩ := hL
      refine GDeriv.ax ih ⟨i, fun y hy => ?_⟩
      have := hi (σ y) (fun h => hy ((sat_image hE y L).2 h))
      rwa [hf] at this
    · rwa [prune_cons_neg sE L π hF]
  | @res π C D R _ hC hD hR ih =>
    by_cases hF : Falsifiable (R.image sE)
    · rw [prune_cons_pos sE R π hF]
      obtain ⟨g, hg⟩ := hR
      set q := sE (g, true) with hqdef
      have key : ∀ y, ¬ LinClauseSat y (R.image sE) →
          (LinEqSat y q → ¬ LinClauseSat y (C.image sE)) ∧
            (¬ LinEqSat y q → ¬ LinClauseSat y (D.image sE)) := by
        intro y hy
        have h := hg (σ y) (fun h => hy ((sat_image hE y R).2 h))
        rw [hqdef, hE, sat_image hE, sat_image hE]
        exact h
      by_cases hCf : Falsifiable (C.image sE)
      · by_cases hDf : Falsifiable (D.image sE)
        · obtain ⟨g', e'⟩ := q
          cases e'
          · refine GDeriv.res ih (mem_prune sE hD hDf) (mem_prune sE hC hCf) ⟨g', fun y hy => ?_⟩
            have hk := key y hy
            rw [linEqSat_false_iff, not_not] at hk
            exact ⟨hk.2, hk.1⟩
          · exact GDeriv.res ih (mem_prune sE hC hCf) (mem_prune sE hD hDf) ⟨g', key⟩
        · -- the image of `D` is deleted: the image of `R` weakens the image of `C`
          have hw : ∀ y, LinClauseSat y (C.image sE) → LinClauseSat y (R.image sE) := by
            intro y hy
            by_contra hn
            by_cases hq : LinEqSat y q
            · exact (key y hn).1 hq hy
            · exact hDf ⟨y, (key y hn).2 hq⟩
          exact GDeriv.weak ih (mem_prune sE hC hCf) hw
      · have hw : ∀ y, LinClauseSat y (D.image sE) → LinClauseSat y (R.image sE) := by
          intro y hy
          by_contra hn
          by_cases hq : LinEqSat y q
          · exact hCf ⟨y, (key y hn).1 hq⟩
          · exact (key y hn).2 hq hy
        have hDf : Falsifiable (D.image sE) := by
          obtain ⟨y, hy⟩ := hF
          exact ⟨y, fun h => hy (hw y h)⟩
        exact GDeriv.weak ih (mem_prune sE hD hDf) hw
    · rwa [prune_cons_neg sE R π hF]
  | @weak π C D _ hC himp ih =>
    by_cases hF : Falsifiable (D.image sE)
    · rw [prune_cons_pos sE D π hF]
      have hw : ∀ y, LinClauseSat y (C.image sE) → LinClauseSat y (D.image sE) := fun y h =>
        (sat_image hE y D).2 (himp _ ((sat_image hE y C).1 h))
      have hCf : Falsifiable (C.image sE) := by
        obtain ⟨y, hy⟩ := hF
        exact ⟨y, fun h => hy (hw y h)⟩
      exact GDeriv.weak ih (mem_prune sE hC hCf) hw
    · rwa [prune_cons_neg sE D π hF]

/-! ### The substitution -/

section Subst

variable {N : ℕ} (j : Fin N) (u : Fin 4) (f : Finset (Fin N × Fin 4)) (a : Bool)
  (st : Fin 4 → Bool)

/-- Clear block `j`. -/
def clr (x : Fin N × Fin 4 → ZMod 2) : Fin N × Fin 4 → ZMod 2 :=
  fun v => if v.1 = j then 0 else x v

/-- The linear part of the substitution. -/
def lin : (Fin N × Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin N × Fin 4 → ZMod 2) where
  toFun x := clr j x + (ind f ⬝ᵥ clr j x) • Pi.single (j, u) 1
  map_add' x y := by
    have : clr j (x + y) = clr j x + clr j y := by
      funext v; simp only [clr, Pi.add_apply]; split_ifs <;> simp
    rw [this, dotProduct_add, add_smul]
    abel
  map_smul' r x := by
    have : clr j (r • x) = r • clr j x := by
      funext v; simp only [clr, Pi.smul_apply]; split_ifs <;> simp
    rw [this, dotProduct_smul, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

/-- The constants of block `j` (bit `u` cleared). -/
def kc : Fin N × Fin 4 → ZMod 2 :=
  fun v => if v.1 = j then (if v.2 = u then 0 else toZ (st v.2)) else 0

/-- The constant part of the substitution. -/
def kk : Fin N × Fin 4 → ZMod 2 :=
  kc j u st + (toZ (!a) + ind f ⬝ᵥ kc j u st) • Pi.single (j, u) 1

/-- The substitution on vectors. -/
def sx (x : Fin N × Fin 4 → ZMod 2) : Fin N × Fin 4 → ZMod 2 :=
  lin j u f x + kk j u f a st

/-- The substitution on assignments. -/
def sig (y : Fin N × Fin 4 → Bool) : Fin N × Fin 4 → Bool :=
  fun v => decide (sx j u f a st (vec y) v = 1)

theorem toZ_decide (z : ZMod 2) : toZ (decide (z = 1)) = z := by
  revert z; decide

theorem vec_sig (y : Fin N × Fin 4 → Bool) : vec (sig j u f a st y) = sx j u f a st (vec y) := by
  funext v
  simp only [vec, sig, toZ_decide]

theorem sig_out (y : Fin N × Fin 4 → Bool) (v : Fin N × Fin 4) (hv : v.1 ≠ j) :
    sig j u f a st y v = y v := by
  have h : sx j u f a st (vec y) v = toZ (y v) := by
    have hne : v ≠ (j, u) := fun h => hv (by rw [h])
    simp [sx, lin, kk, kc, clr, hv, hne, vec]
  simp only [sig, h]
  cases y v <;> decide

theorem sig_blk (y : Fin N × Fin 4 → Bool) (t : Fin 4) (ht : t ≠ u) :
    sig j u f a st y (j, t) = st t := by
  have h : sx j u f a st (vec y) (j, t) = toZ (st t) := by
    have hne : (j, t) ≠ (j, u) := fun h => ht (by simpa using h)
    simp [sx, lin, kk, kc, clr, ht, hne]
  simp only [sig, h]
  cases st t <;> decide

theorem two_eq_zero' (t : ZMod 2) : t + t = 0 := by
  revert t; decide

/-- The substituted assignment falsifies `f = a`. -/
theorem sig_not_sat (hju : (j, u) ∈ f) (y : Fin N × Fin 4 → Bool) :
    ¬ LinEqSat (sig j u f a st y) (f, a) := by
  rw [linEqSat_iff, vec_sig]
  have h1 : ind f (j, u) = 1 := by simp [ind, hju]
  have : ind f ⬝ᵥ sx j u f a st (vec y) = toZ (!a) := by
    simp only [sx, lin, kk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_add, dotProduct_smul,
      dotProduct_single, h1, smul_eq_mul, mul_one]
    generalize ind f ⬝ᵥ clr j (vec y) = s
    generalize ind f ⬝ᵥ kc j u st = t
    have : s + s * 1 + (t + (toZ (!a) + t) * 1) = toZ (!a) + (s + s) + (t + t) := by ring
    rw [mul_one, mul_one] at this
    rw [this, two_eq_zero', two_eq_zero', add_zero, add_zero]
  rw [this]
  show ¬ toZ (!a) = toZ a
  cases a <;> decide

/-- The functional `x ↦ ind g · lin x`. -/
def phi (g : Finset (Fin N × Fin 4)) : (Fin N × Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ind g ⬝ᵥ lin j u f x
  map_add' x y := by rw [map_add, dotProduct_add]
  map_smul' r x := by rw [map_smul, dotProduct_smul, RingHom.id_apply]

/-- The image of an equation under the substitution. -/
noncomputable def sEq (q : LinEq (Fin N × Fin 4)) : LinEq (Fin N × Fin 4) :=
  (Finset.univ.filter (fun v => Classical.choose (dual_vec (phi j u f q.1)) v = 1),
    decide (toZ q.2 - ind q.1 ⬝ᵥ kk j u f a st = 1))

theorem ind_filter_one {V : Type} [Fintype V] [DecidableEq V] (w : V → ZMod 2) :
    ind (Finset.univ.filter (fun v => w v = 1)) = w := by
  funext v
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  generalize w v = z
  revert z; decide

theorem sEq_sat (y : Fin N × Fin 4 → Bool) (q : LinEq (Fin N × Fin 4)) :
    LinEqSat y (sEq j u f a st q) ↔ LinEqSat (sig j u f a st y) q := by
  rw [linEqSat_iff, linEqSat_iff, vec_sig]
  simp only [sEq, ind_filter_one, toZ_decide]
  have hw := Classical.choose_spec (dual_vec (phi j u f q.1)) (vec y)
  have hφ : phi j u f q.1 (vec y) = ind q.1 ⬝ᵥ lin j u f (vec y) := rfl
  rw [hφ] at hw
  rw [dotProduct_comm, ← hw, sx, dotProduct_add]
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [← h]; ring

end Subst

theorem fval_sig {N : ℕ} (K₀ : Finset (Fin N)) (β : Fin N → Bool) (j : Fin N) (u : Fin 4)
    (f : Finset (Fin N × Fin 4)) (a b : Bool) (st : Fin 4 → Bool)
    (hst : ∀ z : Fin 4 → Bool, (∀ q, q ≠ u → z q = st q) → ip2 z = b)
    (hb : j ∈ K₀ → b = β j) (y : Fin N × Fin 4 → Bool) :
    fval K₀ β (sig j u f a st y) = fval (insert j K₀) (Function.update β j b) y := by
  funext i
  unfold fval
  by_cases hij : i = j
  · subst hij
    simp only [Finset.mem_insert_self, ↓reduceIte, Function.update_self]
    by_cases hi : i ∈ K₀
    · simp only [hi, ↓reduceIte, hb hi]
    · simp only [hi, ↓reduceIte]
      exact hst _ (fun t ht => sig_blk i u f a st y t ht)
  · simp only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij]
    split_ifs
    · rfl
    · unfold gval
      congr 1
      funext t
      exact sig_out j u f a st y (i, t) hij

/-- Leg C of L-pcx-072. -/
theorem subst : StmtSubst := by
  intro m N G c K₀ β j u f a b hju hb π hπ
  obtain ⟨st, hst⟩ := ip2_stifled u b
  let sE := sEq j u f a st
  have hE : ∀ y q, LinEqSat y (sE q) ↔ LinEqSat (sig j u f a st y) q :=
    fun y q => sEq_sat j u f a st y q
  refine ⟨prune sE π, prune_deriv G c K₀ (insert j K₀) β (Function.update β j b)
    (sig j u f a st) sE hE (fval_sig K₀ β j u f a b st hst hb) π hπ, ?_, ?_⟩
  · intro h0
    have hF : Falsifiable ((∅ : LinClause (Fin N × Fin 4)).image sE) :=
      ⟨fun _ => false, by simp [LinClauseSat]⟩
    have := mem_prune sE h0 hF
    simpa using this
  · intro l' hl hI
    refine prune_length sE hl (fun L hL => ?_)
    rintro ⟨y, hy⟩
    have h1 : ¬ LinClauseSat (sig j u f a st y) L := fun h => hy ((sat_image hE y L).2 h)
    exact sig_not_sat j u f a st hju y (hI L hL _ h1)

end PEqualNP.ProofComplexity.LiftQuad
