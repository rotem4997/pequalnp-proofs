import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8325_aux

open Finset

def enc (n : ℕ) (k : Fin 3) (u : Fin n) : Fin (3 * n) := finProdFinEquiv (k, u)

theorem enc_inj {n : ℕ} {k k' : Fin 3} {u u' : Fin n} :
    enc n k u = enc n k' u' ↔ k = k' ∧ u = u' := by
  unfold enc
  rw [finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem enc_surj {n : ℕ} (a : Fin (3 * n)) : ∃ k u, a = enc n k u :=
  ⟨(finProdFinEquiv.symm a).1, (finProdFinEquiv.symm a).2, by
    unfold enc
    rw [Prod.mk.eta, Equiv.apply_symm_apply]⟩

theorem natAdd_inj' {m k : ℕ} {a b : Fin k} : Fin.natAdd m a = Fin.natAdd m b ↔ a = b := by
  simp [Fin.ext_iff]

theorem succ_ne : ∀ k : Fin 3, k + 1 ≠ k := by decide
theorem pred_ne : ∀ k : Fin 3, k - 1 ≠ k := by decide
theorem two_ne : ∀ k k' : Fin 3, k + 1 = k' → k = k' + 1 → False := by decide

theorem fin3_a : ∀ i j p q : Fin 3, i ≠ j → p ≠ q → (p = i ∨ i = p + 1) → (p = j ∨ j = p + 1) →
    (q = i ∨ i = q + 1) → (q = j ∨ j = q + 1) → False := by decide

theorem fin3_b : ∀ i j p q : Fin 3, i ≠ j → p ≠ q → (p = i ∨ p = i + 1) → (p = j ∨ p = j + 1) →
    (q = i ∨ q = i + 1) → (q = j ∨ q = j + 1) → False := by decide

variable {n : ℕ} (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))

def L1 : Finset (Fin n) := univ.filter (fun u => ∀ v, (u, v) ∈ E → v = σ u)

def R1 : Finset (Fin n) :=
  univ.filter (fun v => (∀ u, (u, v) ∈ E → u = σ.symm v) ∧ σ.symm v ∉ L1 E σ)

def A : Finset (Fin (3 * n) × Fin (3 * n)) :=
  (univ ×ˢ E).image (fun p : Fin 3 × (Fin n × Fin n) => (enc n p.1 p.2.1, enc n p.1 p.2.2))

def B : Finset (Fin (3 * n) × Fin (3 * n)) :=
  (univ ×ˢ L1 E σ).image (fun p : Fin 3 × Fin n => (enc n (p.1 + 1) p.2, enc n p.1 (σ p.2)))

def C : Finset (Fin (3 * n) × Fin (3 * n)) :=
  (univ ×ˢ R1 E σ).image (fun p : Fin 3 × Fin n => (enc n p.1 (σ.symm p.2), enc n (p.1 + 1) p.2))

def F : Finset (Fin (3 * n) × Fin (3 * n)) := A E ∪ B E σ ∪ C E σ

theorem hL1 {u v : Fin n} (hu : u ∈ L1 E σ) (h : (u, v) ∈ E) : v = σ u := by
  simp only [L1, mem_filter, mem_univ, true_and] at hu
  exact hu v h

theorem hR1 {u v : Fin n} (hv : v ∈ R1 E σ) (h : (u, v) ∈ E) : u = σ.symm v := by
  simp only [R1, mem_filter, mem_univ, true_and] at hv
  exact hv.1 u h

theorem hR1' {v : Fin n} (hv : v ∈ R1 E σ) : σ.symm v ∉ L1 E σ := by
  simp only [R1, mem_filter, mem_univ, true_and] at hv
  exact hv.2

theorem mem_F (i j : Fin 3) (u v : Fin n) : (enc n i u, enc n j v) ∈ F E σ ↔
    ((u, v) ∈ E ∧ j = i) ∨ (i = j + 1 ∧ u ∈ L1 E σ ∧ v = σ u) ∨
      (j = i + 1 ∧ v ∈ R1 E σ ∧ u = σ.symm v) := by
  simp only [F, A, B, C, mem_union, mem_image, mem_product, mem_univ, true_and, Prod.mk.injEq,
    enc_inj, Prod.exists]
  constructor
  · rintro ((⟨k, a, b, hab, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ | ⟨k, a, ha, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩) |
      ⟨k, b, hb, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)
    · exact Or.inl ⟨hab, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, hb, rfl⟩)
  · rintro (⟨huv, rfl⟩ | ⟨rfl, hu, rfl⟩ | ⟨rfl, hv, rfl⟩)
    · exact Or.inl (Or.inl ⟨_, _, _, huv, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)
    · exact Or.inl (Or.inr ⟨_, _, hu, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)
    · exact Or.inr ⟨_, _, hv, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem edge (hσ : ∀ u, (u, σ u) ∈ E) {i j : Fin 3} {u v : Fin n}
    (h : (enc n i u, enc n j v) ∈ F E σ) : (u, v) ∈ E := by
  rw [mem_F] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact h
  · exact hσ u
  · simpa using hσ (σ.symm v)

theorem c4 (hC4 : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hσ : ∀ u, (u, σ u) ∈ E) :
    ∀ a b c d : Fin (3 * n), a ≠ b → c ≠ d →
      ¬((a, c) ∈ F E σ ∧ (a, d) ∈ F E σ ∧ (b, c) ∈ F E σ ∧ (b, d) ∈ F E σ) := by
  intro a b c d hab hcd ⟨h1, h2, h3, h4⟩
  obtain ⟨i, u, rfl⟩ := enc_surj a
  obtain ⟨j, w, rfl⟩ := enc_surj b
  obtain ⟨p, v, rfl⟩ := enc_surj c
  obtain ⟨q, z, rfl⟩ := enc_surj d
  have e1 := edge E σ hσ h1
  have e2 := edge E σ hσ h2
  have e3 := edge E σ hσ h3
  have e4 := edge E σ hσ h4
  rw [mem_F] at h1 h2 h3 h4
  have hab' : ¬(i = j ∧ u = w) := fun h => hab (enc_inj.mpr h)
  have hcd' : ¬(p = q ∧ v = z) := fun h => hcd (enc_inj.mpr h)
  by_cases huw : u = w
  · subst huw
    have hij : i ≠ j := fun h => hab' ⟨h, rfl⟩
    by_cases hu : u ∈ L1 E σ
    · have hvz : v = z := (hL1 E σ hu e1).trans (hL1 E σ hu e2).symm
      have hpq : p ≠ q := fun h => hcd' ⟨h, hvz⟩
      have k : ∀ {i p : Fin 3} {x : Fin n}, (((u, x) ∈ E ∧ p = i) ∨
          (i = p + 1 ∧ u ∈ L1 E σ ∧ x = σ u) ∨ (p = i + 1 ∧ x ∈ R1 E σ ∧ u = σ.symm x)) →
          (p = i ∨ i = p + 1) := by
        intro i p x h
        rcases h with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨-, hx, hux⟩
        · exact Or.inl h
        · exact Or.inr h
        · rw [hux] at hu
          exact absurd hu (hR1' E σ hx)
      exact fin3_a i j p q hij hpq (k h1) (k h3) (k h2) (k h4)
    · have k : ∀ {i p : Fin 3} {x : Fin n}, (((u, x) ∈ E ∧ p = i) ∨
          (i = p + 1 ∧ u ∈ L1 E σ ∧ x = σ u) ∨ (p = i + 1 ∧ x ∈ R1 E σ ∧ u = σ.symm x)) →
          (p = i ∨ (p = i + 1 ∧ u = σ.symm x)) := by
        intro i p x h
        rcases h with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h, -, hux⟩
        · exact Or.inl h
        · exact absurd h hu
        · exact Or.inr ⟨h, hux⟩
      have k1 := k h1
      have k2 := k h2
      have k3 := k h3
      have k4 := k h4
      have hv : u = σ.symm v := by
        rcases k1 with h | ⟨-, hv⟩
        · rcases k3 with h' | ⟨-, hv⟩
          · exact absurd (h.symm.trans h') hij
          · exact hv
        · exact hv
      have hz : u = σ.symm z := by
        rcases k2 with h | ⟨-, hz⟩
        · rcases k4 with h' | ⟨-, hz⟩
          · exact absurd (h.symm.trans h') hij
          · exact hz
        · exact hz
      have hvz : v = z := σ.symm.injective (hv.symm.trans hz)
      have hpq : p ≠ q := fun h => hcd' ⟨h, hvz⟩
      exact fin3_b i j p q hij hpq (k1.imp id And.left) (k3.imp id And.left)
        (k2.imp id And.left) (k4.imp id And.left)
  · have hvz : v = z := by
      by_contra hvz
      exact hC4 u w v z huw hvz ⟨e1, e2, e3, e4⟩
    have hpq : p ≠ q := fun h => hcd' ⟨h, hvz⟩
    rw [← hvz] at h2 h4 e2 e4
    by_cases hv : v ∈ R1 E σ
    · exact huw ((hR1 E σ hv e1).trans (hR1 E σ hv e3).symm)
    · have k : ∀ {i p : Fin 3} {x : Fin n}, (((x, v) ∈ E ∧ p = i) ∨
          (i = p + 1 ∧ x ∈ L1 E σ ∧ v = σ x) ∨ (p = i + 1 ∧ v ∈ R1 E σ ∧ x = σ.symm v)) →
          (p = i ∨ v = σ x) := by
        intro i p x h
        rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hv
      have hu : v = σ u := by
        rcases k h1 with h | h
        · rcases k h2 with h' | h'
          · exact absurd (h.trans h'.symm) hpq
          · exact h'
        · exact h
      have hw : v = σ w := by
        rcases k h3 with h | h
        · rcases k h4 with h' | h'
          · exact absurd (h.trans h'.symm) hpq
          · exact h'
        · exact h
      exact huw (σ.injective (hu.symm.trans hw))

def sig : Equiv.Perm (Fin (3 * n)) :=
  (finProdFinEquiv.symm.trans ((Equiv.refl (Fin 3)).prodCongr σ)).trans finProdFinEquiv

theorem sig_enc (k : Fin 3) (u : Fin n) : sig σ (enc n k u) = enc n k (σ u) := by
  simp [sig, enc]

theorem matchF (hσ : ∀ u, (u, σ u) ∈ E) : ∀ a : Fin (3 * n), (a, sig σ a) ∈ F E σ := by
  intro a
  obtain ⟨k, u, rfl⟩ := enc_surj a
  rw [sig_enc, mem_F]
  exact Or.inl ⟨hσ u, rfl⟩

theorem degL (hσ : ∀ u, (u, σ u) ∈ E) :
    ∀ a : Fin (3 * n), ∃ b : Fin (3 * n), b ≠ sig σ a ∧ (a, b) ∈ F E σ := by
  intro a
  obtain ⟨k, u, rfl⟩ := enc_surj a
  rw [sig_enc]
  by_cases hu : u ∈ L1 E σ
  · refine ⟨enc n (k - 1) (σ u), ?_, ?_⟩
    · rw [Ne, enc_inj]
      exact fun h => pred_ne k h.1
    · rw [mem_F]
      exact Or.inr (Or.inl ⟨by simp, hu, rfl⟩)
  · simp only [L1, mem_filter, mem_univ, true_and] at hu
    push_neg at hu
    obtain ⟨v, hv, hne⟩ := hu
    refine ⟨enc n k v, ?_, ?_⟩
    · rw [Ne, enc_inj]
      exact fun h => hne h.2
    · rw [mem_F]
      exact Or.inl ⟨hv, rfl⟩

theorem degR (hσ : ∀ u, (u, σ u) ∈ E) :
    ∀ b : Fin (3 * n), ∃ a : Fin (3 * n), sig σ a ≠ b ∧ (a, b) ∈ F E σ := by
  intro b
  obtain ⟨k, v, rfl⟩ := enc_surj b
  by_cases hex : ∃ u, (u, v) ∈ E ∧ u ≠ σ.symm v
  · obtain ⟨u, hu, hne⟩ := hex
    refine ⟨enc n k u, ?_, ?_⟩
    · rw [sig_enc, Ne, enc_inj]
      intro h
      apply hne
      rw [← h.2]
      simp
    · rw [mem_F]
      exact Or.inl ⟨hu, rfl⟩
  · push_neg at hex
    by_cases hL : σ.symm v ∈ L1 E σ
    · refine ⟨enc n (k + 1) (σ.symm v), ?_, ?_⟩
      · rw [sig_enc, Ne, enc_inj]
        exact fun h => succ_ne k h.1
      · rw [mem_F]
        exact Or.inr (Or.inl ⟨rfl, hL, by simp⟩)
    · have hR : v ∈ R1 E σ := by
        simp only [R1, mem_filter, mem_univ, true_and]
        exact ⟨hex, hL⟩
      refine ⟨enc n (k - 1) (σ.symm v), ?_, ?_⟩
      · rw [sig_enc, Ne, enc_inj]
        exact fun h => pred_ne k h.1
      · rw [mem_F]
        exact Or.inr (Or.inr ⟨by simp, hR, rfl⟩)

theorem card_F : (F E σ).card = 3 * E.card + 3 * ((L1 E σ).card + (R1 E σ).card) := by
  have dAB : Disjoint (A E) (B E σ) := by
    rw [Finset.disjoint_left]
    intro x hA hB
    simp only [A, B, mem_image, mem_product, mem_univ, true_and, Prod.exists] at hA hB
    obtain ⟨k, a, b, -, rfl⟩ := hA
    obtain ⟨k', c, -, h⟩ := hB
    rw [Prod.mk.injEq, enc_inj, enc_inj] at h
    exact succ_ne k' (h.1.1.trans h.2.1.symm)
  have dAC : Disjoint (A E) (C E σ) := by
    rw [Finset.disjoint_left]
    intro x hA hC
    simp only [A, C, mem_image, mem_product, mem_univ, true_and, Prod.exists] at hA hC
    obtain ⟨k, a, b, -, rfl⟩ := hA
    obtain ⟨k', c, -, h⟩ := hC
    rw [Prod.mk.injEq, enc_inj, enc_inj] at h
    exact succ_ne k' (h.2.1.trans h.1.1.symm)
  have dBC : Disjoint (B E σ) (C E σ) := by
    rw [Finset.disjoint_left]
    intro x hB hC
    simp only [B, C, mem_image, mem_product, mem_univ, true_and, Prod.exists] at hB hC
    obtain ⟨k, a, -, rfl⟩ := hB
    obtain ⟨k', c, -, h⟩ := hC
    rw [Prod.mk.injEq, enc_inj, enc_inj] at h
    exact two_ne k k' h.1.1.symm h.2.1.symm
  have cA : (A E).card = 3 * E.card := by
    unfold A
    rw [card_image_of_injective, card_product, card_univ, Fintype.card_fin]
    rintro ⟨k, a, b⟩ ⟨k', a', b'⟩ h
    simp only [Prod.mk.injEq, enc_inj] at h
    obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := h
    rfl
  have cB : (B E σ).card = 3 * (L1 E σ).card := by
    unfold B
    rw [card_image_of_injective, card_product, card_univ, Fintype.card_fin]
    rintro ⟨k, a⟩ ⟨k', a'⟩ h
    simp only [Prod.mk.injEq, enc_inj] at h
    obtain ⟨⟨-, rfl⟩, rfl, -⟩ := h
    rfl
  have cC : (C E σ).card = 3 * (R1 E σ).card := by
    unfold C
    rw [card_image_of_injective, card_product, card_univ, Fintype.card_fin]
    rintro ⟨k, a⟩ ⟨k', a'⟩ h
    simp only [Prod.mk.injEq, enc_inj] at h
    obtain ⟨⟨rfl, -⟩, -, rfl⟩ := h
    rfl
  unfold F
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨dAC, dBC⟩), card_union_of_disjoint dAB,
    cA, cB, cC]
  ring

def X11 (n : ℕ) (k : Fin 3) : Fin (n + n) → Fin (3 * n + 3 * n) :=
  Fin.addCases (fun u => Fin.castAdd (3 * n) (enc n k u)) (fun v => Fin.natAdd (3 * n) (enc n k v))

def X12 (k : Fin 3) : Fin (n + n) → Fin (3 * n + 3 * n) :=
  Fin.addCases (fun u => Fin.castAdd (3 * n) (enc n (if u ∈ L1 E σ then k + 1 else k) u))
    (fun v => Fin.natAdd (3 * n) (enc n (if v ∈ R1 E σ then k + 1 else k) v))

theorem card_diff : Fintype.card {p : Fin 3 × Fin (n + n) // X11 n p.1 p.2 ≠ X12 E σ p.1 p.2} =
    3 * ((L1 E σ).card + (R1 E σ).card) := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ k : Fin 3, (∑ w : Fin (n + n), if X11 n k w ≠ X12 E σ k w then 1 else 0) =
      (L1 E σ).card + (R1 E σ).card := by
    intro k
    rw [Fin.sum_univ_add]
    have hl : ∀ u : Fin n,
        (if X11 n k (Fin.castAdd n u) ≠ X12 E σ k (Fin.castAdd n u) then 1 else 0) =
        if u ∈ L1 E σ then 1 else 0 := by
      intro u
      by_cases hu : u ∈ L1 E σ <;>
        simp [X11, X12, hu, Fin.castAdd_inj, enc_inj, (succ_ne k).symm]
    have hr : ∀ v : Fin n,
        (if X11 n k (Fin.natAdd n v) ≠ X12 E σ k (Fin.natAdd n v) then 1 else 0) =
        if v ∈ R1 E σ then 1 else 0 := by
      intro v
      simp only [X11, X12, Fin.addCases_right]
      by_cases hv : v ∈ R1 E σ <;>
        simp [hv, natAdd_inj', enc_inj, (succ_ne k).symm]
    simp only [hl, hr, Finset.sum_boole]
    simp
  simp only [h, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem card_main : (F E σ).card = 3 * E.card +
    Fintype.card {p : Fin 3 × Fin (n + n) // X11 n p.1 p.2 ≠ X12 E σ p.1 p.2} := by
  rw [card_F, card_diff]

theorem idxL (k : Fin 3) (u : Fin n) : (if u ∈ L1 E σ then k + 1 else k) = k ∨
    ((if u ∈ L1 E σ then k + 1 else k) = k + 1 ∧ u ∈ L1 E σ) := by
  split_ifs with h
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl rfl

theorem idxR (k : Fin 3) (v : Fin n) : (if v ∈ R1 E σ then k + 1 else k) = k ∨
    ((if v ∈ R1 E σ then k + 1 else k) = k + 1 ∧ v ∈ R1 E σ) := by
  split_ifs with h
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl rfl

theorem func (hσ : ∀ u, (u, σ u) ∈ E) (y : Fin (3 * n + 3 * n) → Bool) :
    (∃ a b : Fin (3 * n), (a, b) ∈ F E σ ∧ y (Fin.castAdd (3 * n) a) = true ∧
      y (Fin.natAdd (3 * n) b) = true) ↔
    ∃ k : Fin 3, ∃ u v : Fin n, (u, v) ∈ E ∧
      (y (X11 n k (Fin.castAdd n u)) || y (X12 E σ k (Fin.castAdd n u))) = true ∧
      (y (X11 n k (Fin.natAdd n v)) || y (X12 E σ k (Fin.natAdd n v))) = true := by
  constructor
  · rintro ⟨a, b, hF, ha, hb⟩
    obtain ⟨i, u, rfl⟩ := enc_surj a
    obtain ⟨j, v, rfl⟩ := enc_surj b
    rw [mem_F] at hF
    rcases hF with ⟨huv, hji⟩ | ⟨hij, hu, hv⟩ | ⟨hji, hv, hu⟩
    · refine ⟨i, u, v, huv, ?_, ?_⟩
      · simp only [X11, Fin.addCases_left, ha, Bool.true_or]
      · rw [hji] at hb
        simp only [X11, Fin.addCases_right, hb, Bool.true_or]
    · refine ⟨j, u, v, ?_, ?_, ?_⟩
      · rw [hv]
        exact hσ u
      · simp only [X12, Fin.addCases_left, if_pos hu, ← hij, ha, Bool.or_true]
      · simp only [X11, Fin.addCases_right, hb, Bool.true_or]
    · refine ⟨i, u, v, ?_, ?_, ?_⟩
      · rw [hu]
        simpa using hσ (σ.symm v)
      · simp only [X11, Fin.addCases_left, ha, Bool.true_or]
      · simp only [X12, Fin.addCases_right, if_pos hv, ← hji, hb, Bool.or_true]
  · rintro ⟨k, u, v, huv, hl, hr⟩
    have key : ∀ i j : Fin 3, (i = k ∨ (i = k + 1 ∧ u ∈ L1 E σ)) →
        (j = k ∨ (j = k + 1 ∧ v ∈ R1 E σ)) → (enc n i u, enc n j v) ∈ F E σ := by
      intro i j hi hj
      rw [mem_F]
      rcases hi with rfl | ⟨rfl, hu⟩ <;> rcases hj with rfl | ⟨rfl, hv⟩
      · exact Or.inl ⟨huv, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hv, hR1 E σ hv huv⟩)
      · exact Or.inr (Or.inl ⟨rfl, hu, hL1 E σ hu huv⟩)
      · exact Or.inl ⟨huv, rfl⟩
    simp only [X11, X12, Fin.addCases_left, Fin.addCases_right, Bool.or_eq_true] at hl hr
    rcases hl with hl | hl <;> rcases hr with hr | hr
    · exact ⟨_, _, key _ _ (Or.inl rfl) (Or.inl rfl), hl, hr⟩
    · exact ⟨_, _, key _ _ (Or.inl rfl) (idxR E σ k v), hl, hr⟩
    · exact ⟨_, _, key _ _ (idxL E σ k u) (Or.inl rfl), hl, hr⟩
    · exact ⟨_, _, key _ _ (idxL E σ k u) (idxR E σ k v), hl, hr⟩

end PEqualNP.Outside.L_meta_8325_aux

theorem PEqualNP.Outside.L_meta_8325 : have x1 : (x1 : ℕ) → Finset (Fin x1 × Fin x1) → (Fin (x1 + x1) → Bool) → Bool := fun (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Fin (x1 + x1) → Bool) => Decidable.decide (∃ (x4 : Fin x1) (x5 : Fin x1), (x4, x5) ∈ x2 ∧ x3 (Fin.castAdd x1 x4) = Bool.true ∧ x3 (Fin.natAdd x1 x5) = Bool.true); have x2 : (x2 : ℕ) → Finset (Fin x2 × Fin x2) → Prop := fun (x2 : ℕ) (x3 : Finset (Fin x2 × Fin x2)) => ∀ (x4 x5 x6 x7 : Fin x2), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x3 ∧ (x4, x7) ∈ x3 ∧ (x5, x6) ∈ x3 ∧ (x5, x7) ∈ x3); ∀ (x3 : ℕ) (x4 : Finset (Fin x3 × Fin x3)) (x5 : Equiv.Perm (Fin x3)),   x2 x3 x4 →     (∀ (x7 : Fin x3), (x7, x5 x7) ∈ x4) →       have x8 : ℕ := (3 : ℕ) * x3;       ∃ (x9 : Finset (Fin x8 × Fin x8)) (x10 : Equiv.Perm (Fin x8)) (x11 : Fin (3 : ℕ) → Fin (x3 + x3) → Fin (x8 + x8)) (x12 : Fin (3 : ℕ) → Fin (x3 + x3) → Fin (x8 + x8)), x2 x8 x9 ∧ (∀ (x13 : Fin x8), (x13, x10 x13) ∈ x9) ∧ ((∀ (x13 : Fin x8), ∃ (x14 : Fin x8), x14 ≠ x10 x13 ∧ (x13, x14) ∈ x9) ∧ ∀ (x13 : Fin x8), ∃ (x14 : Fin x8), x10 x14 ≠ x13 ∧ (x14, x13) ∈ x9) ∧ x9.card = (3 : ℕ) * x4.card + Fintype.card { x13 : Fin (3 : ℕ) × Fin (x3 + x3) // x11 x13.1 x13.2 ≠ x12 x13.1 x13.2 } ∧ ∀ (x13 : Fin (x8 + x8) → Bool), x1 x8 x9 x13 = Decidable.decide (∃ (x14 : Fin (3 : ℕ)), (x1 x3 x4 fun (x15 : Fin (x3 + x3)) => x13 (x11 x14 x15) || x13 (x12 x14 x15)) = Bool.true) := by
  intro x1 x2 n E σ hC4 hσ x8
  refine ⟨L_meta_8325_aux.F E σ, L_meta_8325_aux.sig σ, L_meta_8325_aux.X11 n,
    L_meta_8325_aux.X12 E σ, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact L_meta_8325_aux.c4 E σ hC4 hσ
  · exact L_meta_8325_aux.matchF E σ hσ
  · exact L_meta_8325_aux.degL E σ hσ
  · exact L_meta_8325_aux.degR E σ hσ
  · exact L_meta_8325_aux.card_main E σ
  · intro y
    simp only [x1, decide_eq_true_eq]
    exact decide_eq_decide.mpr (L_meta_8325_aux.func E σ hσ y)
