import Mathlib
import PEqualNP.Defs

-- The matching correspondence adapts the project's Rung RowSystem Matching and Bridge proofs.
-- The block argument splits each contributing matching into its two diagonal parts.
namespace PEqualNP.Outside.L_gct_204

open Finset

variable {a b : ℕ}

def IsMatch (M : Finset (Fin a × Fin b)) : Prop :=
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

noncomputable def matchings (rows : Finset (Fin a)) (cols : Finset (Fin b)) (s : ℕ) :
    Finset (Finset (Fin a × Fin b)) := by
  classical
  exact ((rows ×ˢ cols).powersetCard s).filter IsMatch

noncomputable def mpOn {R : Type*} [CommRing R] (rows : Finset (Fin a)) (cols : Finset (Fin b)) (s : ℕ)
    (W : Fin a × Fin b → R) : R :=
  ∑ M ∈ matchings rows cols s, ∏ e ∈ M, W e

lemma mem_matchings {rows : Finset (Fin a)} {cols : Finset (Fin b)} {s : ℕ}
    {M : Finset (Fin a × Fin b)} :
    M ∈ matchings rows cols s ↔ (M ⊆ rows ×ˢ cols ∧ M.card = s) ∧ IsMatch M := by
  simp [matchings, mem_powersetCard]

noncomputable def sumSubperm {R : Type} [CommRing R] {a b : ℕ} (r : ℕ)
    (X : Matrix (Fin a) (Fin b) R) : R :=
  ∑ S : {S : Finset (Fin a) // S.card = r}, ∑ T : {T : Finset (Fin b) // T.card = r},
    Matrix.permanent
      (Matrix.of fun i j : Fin r => X (S.1.orderEmbOfFin S.2 i) (T.1.orderEmbOfFin T.2 j))

noncomputable def edge {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : Finset (Fin a × Fin b) :=
  univ.image fun k : Fin s => (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k)

lemma edge_fun_injective {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) :
    Function.Injective fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
  intro k k' h
  exact (x.2.1.1.orderEmbOfFin x.2.1.2).injective (congrArg Prod.snd h)

lemma edge_image_snd {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.snd = x.2.1.1 := by
  unfold edge
  rw [Finset.image_image]
  exact Finset.image_orderEmbOfFin_univ x.2.1.1 x.2.1.2

lemma edge_image_fst {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.fst = x.1.1 := by
  unfold edge
  rw [Finset.image_image]
  have : (Prod.fst ∘ fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k))
      = (x.1.1.orderEmbOfFin x.1.2) ∘ x.2.2 := rfl
  rw [this, ← Finset.image_image, Finset.image_univ_equiv]
  exact Finset.image_orderEmbOfFin_univ x.1.1 x.1.2

lemma sumSubperm_eq_mpOn {R : Type} [CommRing R] (s : ℕ) (Z : Matrix (Fin a) (Fin b) R) :
    sumSubperm s Z = mpOn univ univ s (fun e => Z e.1 e.2) := by
  have h1 : sumSubperm s Z = ∑ x : ({S : Finset (Fin a) // S.card = s} ×
      {T : Finset (Fin b) // T.card = s} × Equiv.Perm (Fin s)),
      ∏ k, Z (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k)) (x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
    simp only [sumSubperm, Matrix.permanent, Fintype.sum_prod_type, Matrix.of_apply]
  rw [h1]
  unfold mpOn
  refine Finset.sum_bij (fun x _ => edge x) ?_ ?_ ?_ ?_
  · intro x _
    rw [mem_matchings]
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · unfold edge
      rw [Finset.card_image_of_injective _ (edge_fun_injective x)]
      simp
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' :=
        x.2.2.injective ((x.1.1.orderEmbOfFin x.1.2).injective h)
      rw [this]
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' := (x.2.1.1.orderEmbOfFin x.2.1.2).injective h
      rw [this]
  · intro x _ x' _ h
    have hS : x.1.1 = x'.1.1 := by rw [← edge_image_fst x, ← edge_image_fst x', h]
    have hT : x.2.1.1 = x'.2.1.1 := by rw [← edge_image_snd x, ← edge_image_snd x', h]
    obtain ⟨⟨S, hS1⟩, ⟨T, hT1⟩, σ⟩ := x
    obtain ⟨⟨S', hS1'⟩, ⟨T', hT1'⟩, σ'⟩ := x'
    simp only at hS hT
    subst hS
    subst hT
    have hσ : σ = σ' := by
      ext k
      have hk : (S.orderEmbOfFin hS1 (σ k), T.orderEmbOfFin hT1 k) ∈
          edge (⟨⟨S, hS1'⟩, ⟨T, hT1'⟩, σ'⟩ :
            {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin b) // T.card = s} ×
              Equiv.Perm (Fin s)) := by
        rw [← h]
        exact mem_image.mpr ⟨k, mem_univ _, rfl⟩
      obtain ⟨k', _, hk'⟩ := mem_image.mp hk
      simp only [Prod.mk.injEq] at hk'
      have hkk : k' = k := (T.orderEmbOfFin hT1).injective hk'.2
      rw [hkk] at hk'
      have := (S.orderEmbOfFin hS1).injective hk'.1
      rw [this]
    rw [hσ]
  · intro M hM
    rw [mem_matchings] at hM
    obtain ⟨⟨_, hcard⟩, hm1, hm2⟩ := hM
    have hS : (M.image Prod.fst).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm1 e he e' he' h
    have hT : (M.image Prod.snd).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm2 e he e' he' h
    have hex : ∀ k : Fin s, ∃ e ∈ M, e.2 = (M.image Prod.snd).orderEmbOfFin hT k := by
      intro k
      have := Finset.orderEmbOfFin_mem (M.image Prod.snd) hT k
      obtain ⟨e, he, he2⟩ := mem_image.mp this
      exact ⟨e, he, he2⟩
    choose g hgM hg2 using hex
    have hginj : Function.Injective g := by
      intro k k' h
      have : (M.image Prod.snd).orderEmbOfFin hT k = (M.image Prod.snd).orderEmbOfFin hT k' := by
        rw [← hg2 k, ← hg2 k', h]
      exact ((M.image Prod.snd).orderEmbOfFin hT).injective this
    let φ : Fin s → Fin s := fun k =>
      ((M.image Prod.fst).orderIsoOfFin hS).symm ⟨(g k).1, mem_image_of_mem _ (hgM k)⟩
    have hφ : ∀ k, (M.image Prod.fst).orderEmbOfFin hS (φ k) = (g k).1 := by
      intro k
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [φ]
    have hφinj : Function.Injective φ := by
      intro k k' h
      have h1 : (g k).1 = (g k').1 := by rw [← hφ k, ← hφ k', h]
      exact hginj (hm1 _ (hgM k) _ (hgM k') h1)
    refine ⟨⟨⟨M.image Prod.fst, hS⟩, ⟨M.image Prod.snd, hT⟩,
      Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)⟩, mem_univ _, ?_⟩
    have himg : (univ.image g) = M := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨k, _, rfl⟩ := mem_image.mp he
        exact hgM k
      · rw [Finset.card_image_of_injective _ hginj, hcard]
        simp
    refine Eq.trans ?_ himg
    unfold edge
    refine Finset.image_congr fun k _ => ?_
    simp only [Equiv.ofBijective_apply]
    rw [hφ k, ← hg2 k]
  · intro x _
    unfold edge
    rw [Finset.prod_image]
    intro k _ k' _ h
    exact edge_fun_injective x h

noncomputable def desk {a b : ℕ} (k : ℕ) (W : Fin a × Fin b → ℂ) : ℂ :=
  ∑ R : Finset (Fin a), ∑ C : Finset (Fin b),
    if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun i j => W (R.orderEmbOfFin h.1 i, C.orderEmbOfFin h.2 j))
    else 0

lemma sum_when {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f : ∀ x, p x → ℂ) :
    (∑ x, if h : p x then f x h else 0) = ∑ x : {x // p x}, f x x.2 := by
  have hp (x : {x // p x}) : (if h : p x.val then f x.val h else 0) = f x.val x.property :=
    dite_eq_left x.property
  have hn (x : {x // ¬ p x}) : (if h : p x.val then f x.val h else 0) = 0 :=
    dite_eq_right x.property
  simpa only [hp, hn, Finset.sum_const_zero, add_zero] using
    (Fintype.sum_subtype_add_sum_subtype p (fun x => if h : p x then f x h else 0)).symm

lemma sum_when₂ {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] (q : β → Prop) [DecidablePred q]
    (f : ∀ x y, p x → q y → ℂ) :
    (∑ x, ∑ y, if h : p x ∧ q y then f x y h.1 h.2 else 0) =
      ∑ x : {x // p x}, ∑ y : {y // q y}, f x y x.2 y.2 := by
  calc
    _ = ∑ x, if hx : p x then (∑ y, if hy : q y then f x y hx hy else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : p x
      · rw [dite_eq_left hx]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : q y <;> simp [hx, hy]
      · simp [hx]
    _ = ∑ x : {x // p x}, ∑ y, if hy : q y then f x y x.2 hy else 0 :=
      sum_when p _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_when q _

lemma desk_eq_mp {a b : ℕ} (k : ℕ) (W : Fin a × Fin b → ℂ) :
    desk k W = mpOn Finset.univ Finset.univ k W := by
  have h := sumSubperm_eq_mpOn k (Matrix.of fun (i : Fin a) (j : Fin b) => W (i,j))
  change sumSubperm k _ = mpOn _ _ k W at h
  apply Eq.trans _ h
  unfold desk sumSubperm
  exact sum_when₂ (fun R : Finset (Fin a) => R.card = k)
    (fun C : Finset (Fin b) => C.card = k)
    (fun R C hR hC => Matrix.permanent (Matrix.of fun i j => W (R.orderEmbOfFin hR i, C.orderEmbOfFin hC j)))

end PEqualNP.Outside.L_gct_204

namespace PEqualNP.Outside.L_gct_204

open Finset

def leftEmb (r s : ℕ) {p q : ℕ} : Fin p × Fin q ↪ Fin (p+r) × Fin (q+s) :=
  (Fin.castAddEmb r).prodMap (Fin.castAddEmb s)

def rightEmb (p q : ℕ) {r s : ℕ} : Fin r × Fin s ↪ Fin (p+r) × Fin (q+s) :=
  (Fin.natAddEmb p).prodMap (Fin.natAddEmb q)

def join {p q r s : ℕ} (A : Finset (Fin p × Fin q)) (B : Finset (Fin r × Fin s)) :=
  A.map (leftEmb r s) ∪ B.map (rightEmb p q)

theorem blockIndex_ne {p r : ℕ} (x : Fin p) (y : Fin r) : Fin.castAdd r x ≠ Fin.natAdd p y := by
  intro he
  have hv := congrArg Fin.val he
  change x.val = p + y.val at hv
  omega

theorem emb_disj {p q r s : ℕ} (A : Finset (Fin p × Fin q)) (B : Finset (Fin r × Fin s)) :
    Disjoint (A.map (leftEmb r s)) (B.map (rightEmb p q)) := by
  rw [Finset.disjoint_left]
  intro w ha hb
  obtain ⟨a,_,rfl⟩ := mem_map.mp ha
  obtain ⟨b,_,he⟩ := mem_map.mp hb
  exact blockIndex_ne a.1 b.1 (congrArg Prod.fst he.symm)

private theorem match_map_prod {p q a b : ℕ} (f : Fin p ↪ Fin a) (g : Fin q ↪ Fin b)
    (A : Finset (Fin p × Fin q)) : IsMatch (A.map (f.prodMap g)) ↔ IsMatch A := by
  constructor
  · intro h
    constructor
    · intro x hx y hy eq
      apply (f.prodMap g).injective
      exact h.1 _ (mem_map.mpr ⟨x,hx,rfl⟩) _ (mem_map.mpr ⟨y,hy,rfl⟩) (congrArg f eq)
    · intro x hx y hy eq
      apply (f.prodMap g).injective
      exact h.2 _ (mem_map.mpr ⟨x,hx,rfl⟩) _ (mem_map.mpr ⟨y,hy,rfl⟩) (congrArg g eq)
  · intro h
    constructor
    · intro _ hx _ hy eq
      obtain ⟨x,hxa,rfl⟩ := mem_map.mp hx
      obtain ⟨y,hya,rfl⟩ := mem_map.mp hy
      exact congrArg (f.prodMap g) (h.1 x hxa y hya (f.injective eq))
    · intro _ hx _ hy eq
      obtain ⟨x,hxa,rfl⟩ := mem_map.mp hx
      obtain ⟨y,hya,rfl⟩ := mem_map.mp hy
      exact congrArg (f.prodMap g) (h.2 x hxa y hya (g.injective eq))

private theorem match_union {p q : ℕ} (U V : Finset (Fin p × Fin q))
    (cross : ∀ x ∈ U, ∀ y ∈ V, x.1 ≠ y.1 ∧ x.2 ≠ y.2) :
    IsMatch (U ∪ V) ↔ IsMatch U ∧ IsMatch V := by
  constructor
  · intro h
    have sub {W : Finset (Fin p × Fin q)} (hW : W ⊆ U ∪ V) : IsMatch W :=
      ⟨fun a ha b hb => h.1 a (hW ha) b (hW hb), fun a ha b hb => h.2 a (hW ha) b (hW hb)⟩
    exact ⟨sub Finset.subset_union_left, sub Finset.subset_union_right⟩
  · rintro ⟨hU,hV⟩
    constructor <;> intro x hx y hy eq <;>
      rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy <;>
      first
      | exact hU.1 x hx y hy eq
      | exact hV.1 x hx y hy eq
      | exact hU.2 x hx y hy eq
      | exact hV.2 x hx y hy eq
      | exact ((cross x hx y hy).1 eq).elim
      | exact ((cross y hy x hx).1 eq.symm).elim
      | exact ((cross x hx y hy).2 eq).elim
      | exact ((cross y hy x hx).2 eq.symm).elim

theorem join_match_iff {p q r s : ℕ} (A : Finset (Fin p × Fin q)) (B : Finset (Fin r × Fin s)) :
    IsMatch (join A B) ↔ IsMatch A ∧ IsMatch B := by
  unfold join
  rw [match_union]
  · exact and_congr (match_map_prod _ _ _) (match_map_prod _ _ _)
  · intro x hx y hy
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    obtain ⟨b,_,rfl⟩ := mem_map.mp hy
    exact ⟨blockIndex_ne a.1 b.1, blockIndex_ne a.2 b.2⟩

theorem supported_of_ne {p q r s : ℕ} {t1 : Fin p × Fin q → ℂ} {t2 : Fin r × Fin s → ℂ}
    {T : Fin (p+r) × Fin (q+s) → ℂ}
    (hT : ∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a,b)) 0 0
      (Matrix.of fun a b => t2 (a,b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2))
    (e : Fin (p+r) × Fin (q+s)) (h : T e ≠ 0) :
    (∃ a, leftEmb r s a = e) ∨ ∃ b, rightEmb p q b = e := by
  obtain ⟨i,j⟩ := e
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rename_i i j
    exact Or.inl ⟨(i,j),rfl⟩
  · simp [hT] at h
  · simp [hT] at h
  · rename_i i j
    exact Or.inr ⟨(i,j),rfl⟩

end PEqualNP.Outside.L_gct_204

namespace PEqualNP.Outside.L_gct_204

open Finset
variable {p q r s : ℕ}

private def pullEdge {α β : Type*} [Fintype α] [DecidableEq β] (f : α ↪ β) (M : Finset β) :
    Finset α := univ.filter fun a => f a ∈ M

private lemma separated (a : Fin p × Fin q) (b : Fin r × Fin s) :
    leftEmb r s a ≠ rightEmb p q b := by
  intro h
  have hval := congrArg (fun z : Fin (p+r) × Fin (q+s) => z.1.val) h
  change a.1.val = p + b.1.val at hval
  have := a.1.isLt
  omega

private lemma pullJoin (A : Finset (Fin p × Fin q)) (B : Finset (Fin r × Fin s)) :
    pullEdge (leftEmb r s) (join A B) = A ∧ pullEdge (rightEmb p q) (join A B) = B := by
  constructor
  · ext a
    have hh : leftEmb r s a ∉ B.map (rightEmb p q) := by
      rintro h
      obtain ⟨b,_,e⟩ := mem_map.mp h
      exact separated a b e.symm
    simp only [pullEdge, mem_filter, mem_univ, true_and, join, mem_union, hh, mem_map', or_false]
  · ext b
    have hh : rightEmb p q b ∉ A.map (leftEmb r s) := by
      rintro h
      obtain ⟨a,_,e⟩ := mem_map.mp h
      exact separated a b e
    simp only [pullEdge, mem_filter, mem_univ, true_and, join, mem_union, hh, mem_map', false_or]

private lemma joinPull (M : Finset (Fin (p+r) × Fin (q+s)))
    (hd : ∀ e ∈ M, (∃ a, leftEmb r s a = e) ∨ ∃ b, rightEmb p q b = e) :
    join (pullEdge (leftEmb r s) M) (pullEdge (rightEmb p q) M) = M := by
  ext e
  constructor
  · intro h
    rcases mem_union.mp h with h | h
    · obtain ⟨a,ha,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp ha).2
    · obtain ⟨b,hb,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp hb).2
  · intro h
    rcases hd e h with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact mem_union_left _ (mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _,h⟩))
    · exact mem_union_right _ (mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _,h⟩))

private theorem size_join (A : Finset (Fin p × Fin q)) (B : Finset (Fin r × Fin s)) :
    (join A B).card = A.card + B.card := by
  simp [join, card_union_of_disjoint (emb_disj A B)]

private lemma memFull {m n k : ℕ} {M : Finset (Fin m × Fin n)} :
    M ∈ matchings univ univ k ↔ M.card = k ∧ IsMatch M := by
  simp [mem_matchings]

private theorem conv_core (t1 : Fin p × Fin q → ℂ) (t2 : Fin r × Fin s → ℂ)
    (T : Fin (p+r) × Fin (q+s) → ℂ)
    (hleft : ∀ a, T (leftEmb r s a) = t1 a) (hright : ∀ b, T (rightEmb p q b) = t2 b)
    (hsupp : ∀ e, T e ≠ 0 → (∃ a, leftEmb r s a = e) ∨ ∃ b, rightEmb p q b = e)
    (k : ℕ) :
    mpOn univ univ k T = ∑ a ∈ range (k+1), mpOn univ univ a t1 * mpOn univ univ (k-a) t2 := by
  classical
  let F := fun a : ℕ => (matchings (univ : Finset (Fin p)) (univ : Finset (Fin q)) a) ×ˢ
    (matchings (univ : Finset (Fin r)) (univ : Finset (Fin s)) (k-a))
  let w1 := fun A : Finset (Fin p × Fin q) => ∏ e ∈ A, t1 e
  let w2 := fun B : Finset (Fin r × Fin s) => ∏ e ∈ B, t2 e
  have weight (A B) : (∏ e ∈ join A B, T e) = w1 A * w2 B := by
    rw [join, prod_union (emb_disj A B), prod_map, prod_map]
    simp [w1,w2,hleft,hright]
  symm
  calc
    _ = ∑ z ∈ (range (k+1)).sigma F, w1 z.2.1 * w2 z.2.2 := by
      rw [sum_sigma]
      apply sum_congr rfl
      intro a _
      rw [Finset.sum_product]
      simpa [mpOn,w1,w2,Finset.sum_mul,Finset.mul_sum] using
        (Finset.sum_comm (s := matchings univ univ (k-a)) (t := matchings univ univ a)
          (f := fun B A => w1 A * w2 B))
    _ = _ := by
      unfold mpOn
      apply sum_bij_ne_zero (fun z _ _ => join z.2.1 z.2.2)
      · rintro ⟨a,A,B⟩ hz _
        obtain ⟨ha,hab⟩ := mem_sigma.mp hz
        obtain ⟨hA,hB⟩ := mem_product.mp hab
        obtain ⟨hca,hma⟩ := memFull.mp hA
        obtain ⟨hcb,hmb⟩ := memFull.mp hB
        exact memFull.mpr ⟨by rw [size_join,hca,hcb]; have := mem_range.mp ha; omega,
          (join_match_iff A B).mpr ⟨hma,hmb⟩⟩
      · rintro ⟨a,A,B⟩ ha _ ⟨b,C,D⟩ hb _ he
        have eA : A = C := (pullJoin A B).1.symm.trans
          ((congrArg (pullEdge (leftEmb r s)) he).trans (pullJoin C D).1)
        have eB : B = D := (pullJoin A B).2.symm.trans
          ((congrArg (pullEdge (rightEmb p q)) he).trans (pullJoin C D).2)
        have hca := (memFull.mp (mem_product.mp (mem_sigma.mp ha).2).1).1
        have hcb := (memFull.mp (mem_product.mp (mem_sigma.mp hb).2).1).1
        change A.card = a at hca
        change C.card = b at hcb
        subst C
        subst D
        have : a = b := hca.symm.trans hcb
        exact congrArg (fun z : ℕ => Sigma.mk (β := fun _ : ℕ => _) z (A,B)) this
      · intro M hm hn
        have hd := joinPull M (fun e he => hsupp e (fun h => hn (prod_eq_zero he h)))
        let A := pullEdge (leftEmb r s) M
        let B := pullEdge (rightEmb p q) M
        change join A B = M at hd
        obtain ⟨hc,hm'⟩ := memFull.mp hm
        rw [← hd] at hc hm'
        rw [size_join] at hc
        obtain ⟨hmA,hmB⟩ := (join_match_iff A B).mp hm'
        refine ⟨⟨A.card,(A,B)⟩, mem_sigma.mpr ⟨mem_range.mpr (by change A.card < k+1; omega), ?_⟩, ?_, hd⟩
        · exact mem_product.mpr ⟨memFull.mpr ⟨rfl,hmA⟩,memFull.mpr ⟨by change B.card = k-A.card; omega,hmB⟩⟩
        · change w1 A * w2 B ≠ 0
          rwa [← weight, hd]
      · rintro ⟨a,A,B⟩ _ _
        exact (weight A B).symm

theorem mp_blocks (t1 : Fin p × Fin q → ℂ) (t2 : Fin r × Fin s → ℂ)
    (T : Fin (p+r) × Fin (q+s) → ℂ)
    (hT : ∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a,b)) 0 0
      (Matrix.of fun a b => t2 (a,b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2))
    (k : ℕ) :
    mpOn univ univ k T = ∑ a ∈ range (k+1), mpOn univ univ a t1 * mpOn univ univ (k-a) t2 := by
  refine conv_core t1 t2 T ?_ ?_ (supported_of_ne hT) k
  · intro a
    rw [hT]
    change Matrix.fromBlocks _ _ _ _ (finSumFinEquiv.symm (Fin.castAdd r a.1))
      (finSumFinEquiv.symm (Fin.castAdd s a.2)) = _
    simp
  · intro b
    rw [hT]
    change Matrix.fromBlocks _ _ _ _ (finSumFinEquiv.symm (Fin.natAdd p b.1))
      (finSumFinEquiv.symm (Fin.natAdd q b.2)) = _
    simp

end PEqualNP.Outside.L_gct_204

namespace PEqualNP.Outside.L_gct_204

open Finset

private theorem mpOn_above_dimensions {p q : ℕ} (k : ℕ) (A : Fin p × Fin q → ℂ)
    (h : min p q < k) : mpOn univ univ k A = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro M hM
  obtain ⟨⟨_, hcard⟩, hrow, hcol⟩ := mem_matchings.mp hM
  have hp : M.card ≤ p := by
    rw [← Finset.card_image_of_injOn (f := Prod.fst) hrow]
    simpa using Finset.card_le_univ (M.image Prod.fst)
  have hq : M.card ≤ q := by
    rw [← Finset.card_image_of_injOn (f := Prod.snd) hcol]
    simpa using Finset.card_le_univ (M.image Prod.snd)
  omega

lemma positive_matching_sum_eq_zero {p q : ℕ} (A : Fin p × Fin q → ℂ)
    (hA : ∀ k : ℕ, 1 ≤ k → k ≤ min p q → desk k A = 0)
    (k : ℕ) (hk : 0 < k) : mpOn univ univ k A = 0 := by
  by_cases hbound : k ≤ min p q
  · exact (desk_eq_mp k A).symm.trans (hA k hk hbound)
  · exact mpOn_above_dimensions k A (Nat.lt_of_not_ge hbound)

end PEqualNP.Outside.L_gct_204

open PEqualNP.Outside.L_gct_204 in
theorem PEqualNP.Outside.L_gct_204 : ∀ p1 q1 p2 q2 : ℕ, ∀ L1 : Submodule ℂ (Fin p1 × Fin q1 → ℂ), ∀ L2 : Submodule ℂ (Fin p2 × Fin q2 → ℂ), (∀ t ∈ L1, ∀ k : ℕ, 1 ≤ k → k ≤ min p1 q1 → (∑ R : Finset (Fin p1), ∑ C : Finset (Fin q1), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → (∀ t ∈ L2, ∀ k : ℕ, 1 ≤ k → k ≤ min p2 q2 → (∑ R : Finset (Fin p2), ∑ C : Finset (Fin q2), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → ∀ t1 ∈ L1, ∀ t2 ∈ L2, ∀ T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ, (∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0 (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2)) → ∀ k : ℕ, 1 ≤ k → k ≤ min (p1 + p2) (q1 + q2) → (∑ R : Finset (Fin (p1 + p2)), ∑ C : Finset (Fin (q1 + q2)), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => T (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0 := by
  intro p1 q1 p2 q2 L1 L2 hL1 hL2 t1 ht1 t2 ht2 T hT k hk _
  change desk k T = 0
  rw [desk_eq_mp, mp_blocks t1 t2 T hT]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hpos : 0 < a
  · rw [positive_matching_sum_eq_zero t1 (hL1 t1 ht1) a hpos, zero_mul]
  · have hb : 0 < k - a := by omega
    rw [positive_matching_sum_eq_zero t2 (hL2 t2 ht2) (k - a) hb, mul_zero]
