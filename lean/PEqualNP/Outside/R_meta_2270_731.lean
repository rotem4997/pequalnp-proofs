import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_2270_731
    (strip : ∀ (n : ℕ) (z : Fin n) (g : (Fin n → Bool) → Bool) (s : ℕ),
      (∀ x, g (Function.update x z false) = g x) →
      (∃ x y, g x ≠ g y) →
      HasCircuitSize n (fun x => x z || g x) s →
      ∃ t, t + 1 ≤ s ∧ HasCircuitSize n g t)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (g : (Fin n → Bool) → Bool),
      ¬ G.Colorable 2 →
      (∀ z, (∃ w, G.Adj z w) → (G.neighborSet z).ncard = 3) →
      (∀ (z : Fin n) (w : G.Walk z z), w.IsCycle → 7 ≤ w.length) →
      (∃ u v, G.Adj u v) →
      (∀ x, g x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ s, (∀ T : Finset (Fin n),
        (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → s + 1 < G.edgeSet.ncard + T.card) →
      HasCircuitSize n g s →
      ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ s ∧
        HasCircuitSize n (fun x => g (Function.update (Function.update x u false) v false)) t)
    (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (s : ℕ),
      (A.Nonempty ∨ ∃ u v, G.Adj u v) →
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      s + 1 = A.card + G.edgeSet.ncard + T.card →
      (∀ x, f x = true ↔ (∃ z ∈ A, x z = true) ∨
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      HasCircuitSize n f s) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hnon hdeg hgirth hiso hedge hsem s hs
  let graph : (Fin n → Bool) → Prop := fun x =>
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  let edge : (Fin n → Bool) → Bool := fun x => decide (graph x)
  let withOr : Finset (Fin n) → (Fin n → Bool) → Bool := fun S x =>
    decide ((∃ z ∈ S, x z = true) ∨ graph x)
  have f_eq : f = withOr A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa [withOr, graph] using hsem x
  have graph_update (z : Fin n) (hz : z ∈ A) (x : Fin n → Bool) :
      graph (Function.update x z false) ↔ graph x := by
    have same {u v : Fin n} (h : G.Adj u v) :
        Function.update x z false u = x u ∧ Function.update x z false v = x v := by
      have hu : u ≠ z := fun e => hiso u v h (e ▸ hz)
      have hv : v ≠ z := fun e => hiso v u h.symm (e ▸ hz)
      simp [Function.update_of_ne hu, Function.update_of_ne hv]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨u, v, huv, (same huv).1 ▸ hu, (same huv).2 ▸ hv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨u, v, huv, (same huv).1.trans hu, (same huv).2.trans hv⟩
  have withOr_update (S : Finset (Fin n)) (z : Fin n) (hz : z ∈ A) (hzS : z ∉ S)
      (x : Fin n → Bool) : withOr S (Function.update x z false) = withOr S x := by
    have hsingle : (∃ a ∈ S, Function.update x z false a = true) ↔ ∃ a ∈ S, x a = true := by
      constructor <;> rintro ⟨a, ha, hval⟩ <;> refine ⟨a, ha, ?_⟩
      all_goals
        have hne : a ≠ z := fun e => hzS (e ▸ ha)
        simpa [Function.update_of_ne hne] using hval
    simp only [withOr, hsingle, graph_update z hz x]
  obtain ⟨u0, v0, he0⟩ := hedge
  have withOr_nonconst (S : Finset (Fin n)) : ∃ x y, withOr S x ≠ withOr S y := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    simp [withOr, graph, show ∃ u v, G.Adj u v from ⟨u0, v0, he0⟩]
  have stripFinset (S : Finset (Fin n)) (hSA : S ⊆ A) (b : ℕ)
      (hc : HasCircuitSize n (withOr S) b) :
      ∃ a, a + S.card ≤ b ∧ HasCircuitSize n edge a := by
    induction S using Finset.induction_on generalizing b with
    | empty => exact ⟨b, by simp, by simpa [withOr, edge] using hc⟩
    | @insert z S hz ih =>
      have hjoin : withOr (insert z S) = fun x => x z || withOr S x := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp only [withOr, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_insert]
        simp only [or_and_right, exists_or, exists_eq_left, or_assoc]
      rw [hjoin] at hc
      have hzA : z ∈ A := hSA (Finset.mem_insert_self _ _)
      obtain ⟨c, hcb, hc⟩ := strip n z (withOr S) b
        (withOr_update S z hzA hz) (withOr_nonconst S) hc
      obtain ⟨a, hac, ha⟩ := ih (fun x hx => hSA (Finset.mem_insert_of_mem hx)) c hc
      refine ⟨a, ?_, ha⟩
      rw [Finset.card_insert_of_notMem hz]
      omega
  have hc : HasCircuitSize n (withOr A) s := f_eq ▸ hs
  obtain ⟨s0, hs0, hc0⟩ := stripFinset A Finset.Subset.rfl s hc
  have pairBound : ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ s0 ∧
      HasCircuitSize n (fun x => edge (Function.update (Function.update x u false) v false)) t := by
    by_cases large : ∃ T : Finset (Fin n),
        (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeSet.ncard + T.card ≤ s0 + 1
    · obtain ⟨T, covers, fits⟩ := large
      have inside : ∃ u v, G.Adj u v ∧ u ∈ T ∧ v ∈ T := by
        by_contra! independent
        apply hnon
        refine ⟨SimpleGraph.Coloring.mk (fun w => if w ∈ T then (0 : Fin 2) else 1) ?_⟩
        intro u v huv
        rcases covers u v huv with hu | hv
        · have hv : v ∉ T := independent u v huv hu
          simp [hu, hv]
        · have hu : u ∉ T := fun hu => independent u v huv hu hv
          simp [hu, hv]
      obtain ⟨u, v, huv, huT, hvT⟩ := inside
      let J := G.deleteIncidenceSet u
      let K := J.deleteIncidenceSet v
      let T' := (T.erase u).erase v
      have keep {a b : Fin n} :
          K.Adj a b ↔ G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧ a ≠ v ∧ b ≠ v := by
        simp only [K, J, SimpleGraph.deleteIncidenceSet_adj]
        tauto
      have coverCut : ∀ a b, K.Adj a b → a ∈ T' ∨ b ∈ T' := by
        intro a b h
        obtain ⟨hab, hau, hbu, hav, hbv⟩ := keep.mp h
        rcases covers a b hab with ha | hb
        · exact Or.inl (Finset.mem_erase.mpr ⟨hav, Finset.mem_erase.mpr ⟨hau, ha⟩⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, Finset.mem_erase.mpr ⟨hbu, hb⟩⟩)
      have cardCover : T'.card + 2 = T.card := by
        have h1 := Finset.card_erase_add_one huT
        have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv.symm.ne, hvT⟩)
        dsimp only [T']
        omega
      have degree (a b : Fin n) (h : G.Adj a b) : G.degree a = 3 := by
        simpa only [SimpleGraph.ncard_neighborSet] using hdeg a (hiso a b h)
      have neigh (a : Fin n) (ha : a ≠ u) : J.neighborFinset a = (G.neighborFinset a).erase u := by
        ext b
        simp [J, SimpleGraph.deleteIncidenceSet_adj, ha, and_comm]
      have degreeV : J.degree v = 2 := by
        rw [← J.card_neighborFinset_eq_degree, neigh v huv.symm.ne]
        have h := Finset.card_erase_add_one (G.mem_neighborFinset v u |>.mpr huv.symm)
        rw [G.card_neighborFinset_eq_degree, degree v u huv.symm] at h
        omega
      have degree_le (L : SimpleGraph (Fin n)) [DecidableRel L.Adj] (w : Fin n) :
          L.degree w ≤ L.edgeFinset.card := by
        rw [← L.card_incidenceFinset_eq_degree]
        exact Finset.card_le_card (L.incidenceFinset_subset w)
      have card_eq (L : SimpleGraph (Fin n)) [DecidableRel L.Adj] :
          L.edgeFinset.card = L.edgeSet.ncard := by
        rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
      have cardEdges : K.edgeSet.ncard + 5 = G.edgeSet.ncard := by
        have h1 : J.edgeFinset.card = G.edgeFinset.card - 3 := by
          dsimp only [J]
          rw [G.card_edgeFinset_deleteIncidenceSet, degree u v huv]
        have h2 : K.edgeFinset.card = J.edgeFinset.card - 2 := by
          dsimp only [K]
          rw [J.card_edgeFinset_deleteIncidenceSet, degreeV]
        have h3 := degree_le J v
        rw [degreeV, h1] at h3
        rw [← card_eq K, ← card_eq G]
        omega
      have hedgeK : ∃ a b, K.Adj a b := by
        have hns : ¬ G.neighborFinset u ⊆ ({v} : Finset (Fin n)) := by
          intro h
          have hh := Finset.card_le_card h
          rw [G.card_neighborFinset_eq_degree, degree u v huv, Finset.card_singleton] at hh
          omega
        obtain ⟨a, ha, hnv⟩ := Finset.not_subset.mp hns
        have hua : G.Adj u a := by simpa using ha
        have hns : ¬ G.neighborFinset a ⊆ ({u, v} : Finset (Fin n)) := by
          intro h
          have hh := Finset.card_le_card h
          rw [G.card_neighborFinset_eq_degree, degree a u hua.symm,
            Finset.card_insert_of_notMem (by simpa using huv.ne), Finset.card_singleton] at hh
          omega
        obtain ⟨b, hb, hbn⟩ := Finset.not_subset.mp hns
        have hab : G.Adj a b := by simpa using hb
        have hbne : b ≠ u ∧ b ≠ v := by simpa using hbn
        exact ⟨a, b, keep.mpr ⟨hab, hua.symm.ne, hbne.1, by simpa using hnv, hbne.2⟩⟩
      have positive : 0 < K.edgeSet.ncard := by
        rw [← card_eq K]
        apply Finset.card_pos.mpr
        obtain ⟨a, b, hab⟩ := hedgeK
        exact ⟨s(a,b), by simpa using hab⟩
      let b := K.edgeSet.ncard + T'.card - 1
      have eqBudget : b + 1 = K.edgeSet.ncard + T'.card := by dsimp [b]; omega
      refine ⟨u, v, huv, b, by omega, ?_⟩
      apply star n K ∅ T' _ b (Or.inr hedgeK) coverCut
      · simpa using eqBudget
      · intro x
        have hup (z : Fin n) :
            Function.update (Function.update x u false) v false z = true ↔
              z ≠ u ∧ z ≠ v ∧ x z = true := by
          by_cases huz : z = u
          · subst z; simp [huv.ne]
          · by_cases hvz : z = v
            · subst z; simp
            · simp [huz, hvz]
        simp only [edge, graph, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
          false_or, keep, hup]
        constructor
        · rintro ⟨a, b, hab, ⟨hau, hav, ha⟩, hbu, hbv, hb⟩
          exact ⟨a, b, ⟨hab, hau, hbu, hav, hbv⟩, ha, hb⟩
        · rintro ⟨a, b, ⟨hab, hau, hbu, hav, hbv⟩, ha, hb⟩
          exact ⟨a, b, hab, ⟨hau, hav, ha⟩, hbu, hbv, hb⟩
    · apply core n G edge hnon
        (fun z hz => hdeg z (by obtain ⟨w, hw⟩ := hz; exact hiso z w hw))
        hgirth ⟨u0, v0, he0⟩ (fun x => by simp [edge, graph]) s0 _ hc0
      intro T hcover
      exact Nat.lt_of_not_ge (fun h => large ⟨T, hcover, h⟩)
  obtain ⟨u, v, huv, t0, ht0, hcut⟩ := pairBound
  have hu : u ∉ A := hiso u v huv
  have hv : v ∉ A := hiso v u huv.symm
  let cut (x : Fin n → Bool) := Function.update (Function.update x u false) v false
  let cutEdge : (Fin n → Bool) → Bool := fun x => edge (cut x)
  have hcut : HasCircuitSize n cutEdge t0 := hcut
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wire_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have appendOr (g : (Fin n → Bool) → Bool) (z : Fin n) (j : ℕ)
      (hc : HasCircuitSize n g j) :
      HasCircuitSize n (fun x => x z || g x) (j + 1) := by
    obtain ⟨C, hC, hsize, hval⟩ := hc
    have hlen (x : Fin n → Bool) : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      change (C.gates.foldl step (List.ofFn x)).length = _
      simp [wire_length]
    have hread (x : Fin n → Bool) : (C.wires (List.ofFn x)).getD z false = x z := by
      have stable (gs : List Gate) (w : List Bool) (hi : z.val < w.length) :
          (gs.foldl step w).getD z false = w.getD z false := by
        induction gs generalizing w with
        | nil => rfl
        | cons a gs ih =>
          rw [List.foldl_cons, ih _ (by simp [step]; omega)]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      change (C.gates.foldl step (List.ofFn x)).getD z false = x z
      rw [stable _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, z.isLt]
    let tail : Gate := ⟨.or, [z.val, C.output]⟩
    refine ⟨⟨C.gates ++ [tail], n + C.gates.length⟩, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hh | hh
      · exact hC w hh
      · obtain rfl := List.mem_singleton.mp hh
        simp [tail]
    · change C.gates.length ≤ j at hsize
      change (C.gates ++ [tail]).length ≤ j + 1
      rw [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hsize 1
    · intro x
      change ((C.gates ++ [tail]).foldl step (List.ofFn x)).getD (n + C.gates.length) false = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hlen x]
      change ((C.wires (List.ofFn x)) ++ [_]).getD (C.wires (List.ofFn x)).length false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]
      change ([((C.wires (List.ofFn x)).getD z false), C.eval (List.ofFn x)].any id) = _
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hread x, hval x]
  let cutOr (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
    decide (∃ z ∈ S, x z = true) || cutEdge x
  have addFinset (S : Finset (Fin n)) : HasCircuitSize n (cutOr S) (t0 + S.card) := by
    induction S using Finset.induction_on with
    | empty => simpa [cutOr] using hcut
    | @insert z S hz ih =>
      have heq : cutOr (insert z S) = fun x => x z || cutOr S x := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp only [cutOr, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_insert]
        simp only [or_and_right, exists_or, exists_eq_left, or_assoc]
      rw [heq, Finset.card_insert_of_notMem hz, ← Nat.add_assoc]
      exact appendOr (cutOr S) z _ ih
  have htarget : (fun x => f (cut x)) = cutOr A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    have hs : (∃ z ∈ A, cut x z = true) ↔ ∃ z ∈ A, x z = true := by
      constructor <;> rintro ⟨z, hz, hval⟩ <;> refine ⟨z, hz, ?_⟩
      all_goals
        have hzu : z ≠ u := fun h => hu (h ▸ hz)
        have hzv : z ≠ v := fun h => hv (h ▸ hz)
        simpa [cut, Function.update_of_ne hzu, Function.update_of_ne hzv] using hval
    simp only [f_eq, withOr, cutOr, cutEdge, edge, decide_eq_true_eq, Bool.or_eq_true, hs]
  refine ⟨u, v, hu, hv, huv, t0 + A.card, by omega, ?_⟩
  change HasCircuitSize n (fun x => f (cut x)) _
  rw [htarget]
  exact addFinset A
