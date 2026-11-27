import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2268_483
    (lower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
      G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ i j, G.Adj i j → i ∉ A) →
      (∃ i j, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s →
        A.card + G.edgeSet.ncard + ((Finset.univ : Finset (Fin n)) \ A).card / 2 ≤ s + 1)
    (upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
      (∃ i j, G.Adj i j) →
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      PEqualNP.MetaComplexity.HasCircuitSize n f (A.card + G.edgeSet.ncard + T.card - 1)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hcolor hdegree hgirth hA hedge hf s hs
  have hbound := lower n G A f hcolor hdegree hgirth hA hedge hf s hs
  obtain ⟨color⟩ := hcolor
  let active : Finset (Fin n) := Finset.univ \ A
  let side (c : Fin 2) := active.filter (fun i => color i = c)
  have memSide (i : Fin n) (c : Fin 2) : i ∈ side c ↔ i ∉ A ∧ color i = c := by
    simp [side, active]
  have part : (side 0).card + (side 1).card = active.card := by
    have eq : active.filter (fun i => color i ≠ 0) = side 1 := by
      ext i
      simp only [side, Finset.mem_filter]
      have colors : color i = 0 ∨ color i = 1 := by
        have h := (color i).isLt
        rcases (show (color i).val = 0 ∨ (color i).val = 1 by omega) with h₀ | h₁
        · exact Or.inl (Fin.ext h₀)
        · exact Or.inr (Fin.ext h₁)
      rcases colors with hc | hc <;> simp [hc]
    rw [← eq]
    exact Finset.card_filter_add_card_filter_not (s := active) (fun i => color i = 0)
  let c : Fin 2 := if (side 0).card ≤ (side 1).card then 0 else 1
  let T := side c
  have half : T.card ≤ active.card / 2 := by
    dsimp only [T, c]
    split <;> omega
  have independent {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T) : ¬ G.Adj i j :=
    fun h => color.valid h (((memSide i c).mp hi).2.trans ((memSide j c).mp hj).2.symm)
  have cover (i j : Fin n) (h : G.Adj i j) : i ∈ T ∨ j ∈ T := by
    have hi := hA i j h
    have hj := hA j i h.symm
    have different : (color i).val ≠ (color j).val := fun e => color.valid h (Fin.ext e)
    have hiBound := (color i).isLt
    have hjBound := (color j).isLt
    have hcBound := c.isLt
    rcases (show (color i).val = c.val ∨ (color j).val = c.val by omega) with e | e
    · exact Or.inl ((memSide i c).mpr ⟨hi, Fin.ext e⟩)
    · exact Or.inr ((memSide j c).mpr ⟨hj, Fin.ext e⟩)
  obtain ⟨i, j, hij⟩ := hedge
  have outside : ∃ b : Fin n, b ∉ T ∧ b ∉ A := by
    rcases cover i j hij with hi | hj
    · exact ⟨j, fun hj => independent hi hj hij, hA j i hij.symm⟩
    · exact ⟨i, fun hi => independent hi hj hij, hA i j hij⟩
  obtain ⟨b, hbT, hbA⟩ := outside
  let N := G.neighborFinset b
  have nsize : N.card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ← G.ncard_neighborSet]
    exact hdegree b hbA
  have subset : N ⊆ T := by
    intro w hw
    have hbw : G.Adj b w := by simpa [N] using hw
    exact (cover b w hbw).resolve_left hbT
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
  have one := Finset.card_erase_add_one hu
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (N.erase u).card by omega)
  have two := Finset.card_erase_add_one hv
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < ((N.erase u).erase v).card by omega)
  have hvu := (Finset.mem_erase.mp hv).1
  have huT := subset hu
  have hvT := subset (Finset.mem_of_mem_erase hv)
  have huA := ((memSide u c).mp huT).1
  have hvA := ((memSide v c).mp hvT).1
  have huv := independent huT hvT
  let K := G.deleteIncidenceSet u
  let H := K.deleteIncidenceSet v
  have degrees (z : Fin n) (hz : z ∉ A) : G.degree z = 3 := by
    rw [← G.ncard_neighborSet]
    exact hdegree z hz
  have neighbors : K.neighborSet v = G.neighborSet v := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, K, SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · exact And.left
    · intro hvz
      exact ⟨hvz, hvu, fun e => huv (e ▸ hvz.symm)⟩
  have hKdegree : K.degree v = 3 := by
    rw [← K.ncard_neighborSet, neighbors, G.ncard_neighborSet]
    exact degrees v hvA
  have hKedges : K.edgeSet.ncard = G.edgeSet.ncard - 3 := by
    simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, degrees u huA]
      using G.card_edgeFinset_deleteIncidenceSet u
  have hHedges : H.edgeSet.ncard = K.edgeSet.ncard - 3 := by
    simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hKdegree]
      using K.card_edgeFinset_deleteIncidenceSet v
  have bw : G.Adj b w := by
    simpa [N] using Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
  have bnu : b ≠ u := fun e => hbT (e.symm ▸ huT)
  have bnv : b ≠ v := fun e => hbT (e.symm ▸ hvT)
  have edgeH : ∃ i j, H.Adj i j := by
    exact ⟨b, w, SimpleGraph.deleteIncidenceSet_adj.mpr
      ⟨SimpleGraph.deleteIncidenceSet_adj.mpr
        ⟨bw, bnu, (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1⟩,
        bnv, (Finset.mem_erase.mp hw).1⟩⟩
  have edgePos : 0 < H.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    obtain ⟨i', j', h⟩ := edgeH
    exact Finset.card_pos.mpr ⟨s(i', j'), by simpa using h⟩
  let S := (T.erase u).erase v
  have hS : S.card + 2 = T.card := by
    have h₁ := Finset.card_erase_add_one huT
    have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hvu, hvT⟩)
    dsimp [S]
    omega
  have coverH (i j : Fin n) (h : H.Adj i j) : i ∈ S ∨ j ∈ S := by
    obtain ⟨hK, hiv, hjv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    obtain ⟨hG, hiu, hju⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hK
    rcases cover i j hG with hi | hj
    · exact Or.inl (Finset.mem_erase.mpr ⟨hiv, Finset.mem_erase.mpr ⟨hiu, hi⟩⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hjv, Finset.mem_erase.mpr ⟨hju, hj⟩⟩)
  let g := fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)
  have hg (x : Fin n → Bool) : g x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true := by
    rw [show g x = f (Function.update (Function.update x u false) v false) from rfl, hf]
    have saved (i : Fin n) (hiu : i ≠ u) (hiv : i ≠ v) :
        Function.update (Function.update x u false) v false i = x i := by
      rw [Function.update_of_ne hiv, Function.update_of_ne hiu]
    have live (i : Fin n) (h : Function.update (Function.update x u false) v false i = true) :
        i ≠ u ∧ i ≠ v := by
      constructor
      · rintro rfl
        simp [Function.update_of_ne hvu.symm] at h
      · rintro rfl
        simp at h
    apply or_congr
    · constructor
      · rintro ⟨a, ha, h⟩
        obtain ⟨hau, hav⟩ := live a h
        exact ⟨a, ha, (saved a hau hav).symm.trans h⟩
      · rintro ⟨a, ha, h⟩
        exact ⟨a, ha, (saved a (fun e => huA (e ▸ ha)) (fun e => hvA (e ▸ ha))).trans h⟩
    · constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        obtain ⟨hiu, hiv⟩ := live i hi
        obtain ⟨hju, hjv⟩ := live j hj
        refine ⟨i, j, ?_, (saved i hiu hiv).symm.trans hi, (saved j hju hjv).symm.trans hj⟩
        exact SimpleGraph.deleteIncidenceSet_adj.mpr
          ⟨SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hij, hiu, hju⟩, hiv, hjv⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        obtain ⟨hk, hiv, hjv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hij
        obtain ⟨hG, hiu, hju⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hk
        exact ⟨i, j, hG, (saved i hiu hiv).trans hi, (saved j hju hjv).trans hj⟩
  refine ⟨u, v, huA, hvA, hvu.symm, huv, A.card + H.edgeSet.ncard + S.card - 1, ?_, ?_⟩
  · change A.card + G.edgeSet.ncard + active.card / 2 ≤ s + 1 at hbound
    omega
  · exact upper n H A S g edgeH coverH hg
