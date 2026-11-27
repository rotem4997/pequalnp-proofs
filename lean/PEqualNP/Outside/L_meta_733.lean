import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_733 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
  (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
  ∀ I : Set (Fin n),
    ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  intro n G X hb I
  constructor
  · rintro ⟨hind, hdom⟩
    refine ⟨{v | v ∈ I ∧ v ∉ X}, fun b hb' => hb'.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro h
        by_contra hyB
        have hyI : y ∉ I := fun hI => hyB ⟨hI, hy⟩
        obtain ⟨u, hu, hyu⟩ := hdom y hyI
        obtain ⟨b, hbB, hub⟩ := h u hyu
        exact hind u hu b hbB.1 hub
      · intro hyB x hyx
        exact ⟨y, hyB, hyx.symm⟩
    · intro v
      constructor
      · intro hv
        by_cases hx : v ∈ X
        · exact Or.inr ⟨hx, fun b hbB => hind v hv b hbB.1⟩
        · exact Or.inl ⟨hv, hx⟩
      · rintro (hv | ⟨hx, hno⟩)
        · exact hv.1
        · by_contra hvI
          obtain ⟨u, hu, hvu⟩ := hdom v hvI
          have hux : u ∉ X := (hb v u hvu).mp hx
          exact hno u ⟨hu, hux⟩ hvu
  · rintro ⟨B, hBX, hsat, hI⟩
    constructor
    · intro u hu v hv huv
      rcases (hI u).mp hu with hu1 | ⟨hux, hun⟩
      · rcases (hI v).mp hv with hv1 | ⟨hvx, hvn⟩
        · exact hBX u hu1 ((hb u v huv).mpr (hBX v hv1))
        · exact hvn u hu1 huv.symm
      · rcases (hI v).mp hv with hv1 | ⟨hvx, hvn⟩
        · exact hun v hv1 huv
        · exact (hb u v huv).mp hux hvx
    · intro v hv
      by_cases hx : v ∈ X
      · by_contra hno
        refine hv ((hI v).mpr (Or.inr ⟨hx, fun b hbB hvb => hno ⟨b, (hI b).mpr (Or.inl hbB), hvb⟩⟩))
      · have hvB : v ∉ B := fun h => hv ((hI v).mpr (Or.inl h))
        have h1 : ¬ ∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b := fun h => hvB ((hsat v hx).mp h)
        push_neg at h1
        obtain ⟨x, hvx, hxno⟩ := h1
        have hxX : x ∈ X := by
          by_contra hxn
          exact hx ((hb v x hvx).mpr hxn)
        exact ⟨x, (hI x).mpr (Or.inr ⟨hxX, fun b hbB => hxno b hbB⟩), hvx⟩
