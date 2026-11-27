import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_731

theorem twoK {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop) (c : G.Coloring (Fin 3))
    (hd : ∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) :
    ∃ K : Set (Fin n), (∀ u ∈ K, c u ≠ 2) ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v) ∧
      ∀ v, c v ≠ 2 → v ∉ K → ∃ k ∈ K, D v k := by
  classical
  let side (j : Fin 3) (T : Set (Fin n)) : Set (Fin n) := {v | c v = j ∧ ∀ t ∈ T, ¬ D v t}
  have flip (j) {S T} (hst : S ⊆ T) : side j T ⊆ side j S :=
    fun _ hv => ⟨hv.1, fun u hu => hv.2 u (hst hu)⟩
  let f : Set (Fin n) →o Set (Fin n) := ⟨fun T => side 0 (side 1 T), fun _ _ h => flip 0 (flip 1 h)⟩
  let X := f.lfp
  let Y := side 1 X
  have hx (v) : v ∈ X ↔ c v = 0 ∧ ∀ w ∈ Y, ¬ D v w := by
    change v ∈ X ↔ v ∈ f X
    rw [f.map_lfp]
  have hy (v) : v ∈ Y ↔ c v = 1 ∧ ∀ w ∈ X, ¬ D v w := Iff.rfl
  refine ⟨X ∪ Y, ?_, ?_, ?_⟩
  · rintro u (ha|hb)
    · rw [((hx u).mp ha).1]
      decide
    · rw [((hy u).mp hb).1]
      decide
  · rintro u (hu|hu) v (hv|hv) adj
    · exact c.valid adj (((hx u).mp hu).1.trans ((hx v).mp hv).1.symm)
    · exact ((hd u v).mp adj).elim (((hx u).mp hu).2 v hv) (((hy v).mp hv).2 u hu)
    · exact ((hd u v).mp adj).elim (((hy u).mp hu).2 v hv) (((hx v).mp hv).2 u hu)
    · exact c.valid adj (((hy u).mp hu).1.trans ((hy v).mp hv).1.symm)
  · intro v hc hv
    by_contra! h
    apply hv
    rcases (by decide : ∀ i : Fin 3, i ≠ 2 → i = 0 ∨ i = 1) (c v) hc with h0|h1
    · exact Or.inl ((hx v).mpr ⟨h0, fun w hw => h w (Or.inr hw)⟩)
    · exact Or.inr ((hy v).mpr ⟨h1, fun w hw => h w (Or.inl hw)⟩)

end PEqualNP.Outside.L_meta_731

open PEqualNP.Outside.L_meta_731 in
theorem PEqualNP.Outside.L_meta_731 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop),
  G.Colorable 3 → (∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
  ∃ I : Set (Fin n),
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
    n ≤ {v : Fin n | v ∈ I ∧ ∃ w, D v w}.ncard + {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}.ncard
      + G.indepNum := by
  rintro n G D ⟨c⟩ hd _
  classical
  obtain ⟨K, _, hind, hab⟩ := twoK G D c hd
  let I := K ∪ {v | c v = 2 ∧ ∀ u ∈ K, ¬ G.Adj v u}
  have sub : K ⊆ I := Set.subset_union_left
  have independent : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    rintro u (hu|hu) v (hv|hv) he
    · exact hind u hu v hv he
    · exact hv.2 u hu he.symm
    · exact hu.2 v hv he
    · exact c.valid he (hu.1.trans hv.1.symm)
  have ab (v) (hv : v ∉ I) (hc : c v ≠ 2) : ∃ w ∈ I, D v w := by
    obtain ⟨w,hw,h⟩ := hab v hc (fun hk => hv (sub hk))
    exact ⟨w,sub hw,h⟩
  refine ⟨I, independent, ?_, ?_⟩
  · intro v hv
    by_cases hc : c v = 2
    · by_contra! h
      exact hv (Or.inr ⟨hc, fun k hk => h k (sub hk)⟩)
    · obtain ⟨u,hu,h⟩ := ab v hv hc
      exact ⟨u,hu,(hd v u).mpr (Or.inl h)⟩
  · let A := {v : Fin n | v ∈ I ∧ ∃ w, D v w}
    let B := {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}
    let W := (A ∪ B)ᶜ
    have out {v} (h : v ∈ W) (hv : v ∉ I) : c v = 2 := by
      by_contra hc
      exact h (Or.inr ⟨hv,ab v hv hc⟩)
    have bad {u v} (hu : u ∈ W) (hv : v ∈ W) (h : D u v) : False := by
      by_cases hi : u ∈ I
      · exact hu (Or.inl ⟨hi,v,h⟩)
      by_cases hj : v ∈ I
      · exact hu (Or.inr ⟨hi,v,hj,h⟩)
      exact c.valid ((hd u v).mpr (Or.inl h)) ((out hu hi).trans (out hv hj).symm)
    have hW : G.IsIndepSet W := by
      intro u hu v hv _ h
      rcases (hd u v).mp h with huv|hvu
      · exact bad hu hv huv
      · exact bad hv hu hvu
    have hcard : W.ncard ≤ G.indepNum := by
      rw [Set.ncard_eq_toFinset_card']
      apply SimpleGraph.IsIndepSet.card_le_indepNum
      simpa using hW
    have hp : (A ∪ B).ncard + W.ncard = n := by
      simpa [W] using Set.ncard_add_ncard_compl (A ∪ B)
    have := Set.ncard_union_le A B
    change n ≤ A.ncard + B.ncard + G.indepNum
    omega
