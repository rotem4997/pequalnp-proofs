import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Deleting a pendant edge and its neighbour saves two gates, or three
-- when that neighbour has another incident edge. This handles degrees
-- one and two completely. The residual cost question only involves
-- non-star graphs in which every leaf is attached to a hub.
theorem PEqualNP.Outside.R_meta_4480_51
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
    circuitFun n C (fun _ => false) = false →
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C)
    (pendant : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
    let hit := fun (v : Fin (n+m)) (e : Fin n × Fin m) => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
    let val := fun (S : Finset (Fin n × Fin m)) (x : Fin (n+m) → Bool) => decide (∃ e ∈ S, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
    Monotone2 C → circuitFun (n+m) C = val E →
    ∀ u v : Fin (n+m), u ≠ v → (E.filter (hit u)).card = 1 →
      (∃ e ∈ E, hit u e ∧ hit v e) →
      let S := E.filter fun e => ¬ hit v e
      S.Nonempty → ∃ D : Circuit, Monotone2 D ∧ circuitFun (n+m) D = val S ∧
        D.size + min 3 ((E.filter (hit v)).card + 1) ≤ C.size)
    (hubs : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
    let hit := fun (v : Fin (n+m)) (e : Fin n × Fin m) => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
    let val := fun (S : Finset (Fin n × Fin m)) (x : Fin (n+m) → Bool) => decide (∃ e ∈ S, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
    (∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) →
    IsAO2 (n+m) C → circuitFun (n+m) C = val E → (∃ u, (E.filter (hit u)).card = 1) →
    (∀ u v, u ≠ v → (E.filter (hit u)).card = 1 → (∃ e ∈ E, hit u e ∧ hit v e) → 3 ≤ (E.filter (hit v)).card) →
    (∀ v, (E.filter fun e => ¬ hit v e).Nonempty) →
    ∃ v, (E.filter (hit v)).Nonempty ∧ ∃ D : Circuit, Monotone2 D ∧
      circuitFun (n+m) D = val (E.filter fun e => ¬ hit v e) ∧
      D.size + (E.filter (hit v)).card + 1 ≤ C.size) :
∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →     x6 x3 x4 →       (∃ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card = (1 : ℕ)) →         ∃ (x10 : Fin (x1 + x2)),           have x11 : Finset (Fin x1 × Fin x2) := {x11 ∈ x3 | ¬x5 x10 x11};           x11.card < x3.card ∧ (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x6 x11 x12 ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size) := by
  classical
  intro n m E C hit computes c4 hc hleaf
  let val := fun (S : Finset (Fin n × Fin m)) (x : Fin (n+m) → Bool) => decide (∃ e ∈ S, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
  have fc : circuitFun (n+m) C = val E := funext hc.2
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hc.1.1 g hg,
      (hc.1.2.2 g hg).le⟩
  have nonempty : E.Nonempty := by
    obtain ⟨u, h⟩ := hleaf
    obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (E.filter (hit u)).card by omega)
    exact ⟨e, (Finset.mem_filter.mp he).1⟩
  by_cases hstar : ∃ v, ¬ (E.filter fun e => ¬ hit v e).Nonempty
  · obtain ⟨v, hv⟩ := hstar
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hv
    exact ⟨v, by simpa [hempty] using Finset.card_pos.mpr nonempty, Or.inl hempty⟩
  push Not at hstar
  have finish (v : Fin (n+m)) (hv : (E.filter (hit v)).Nonempty)
      (D : Circuit) (hm : Monotone2 D)
      (hf : circuitFun (n+m) D = val (E.filter fun e => ¬ hit v e))
      (sz : D.size + (E.filter (hit v)).card + 1 ≤ C.size) :
      let R := E.filter fun e => ¬ hit v e
      R.card < E.card ∧ (R = ∅ ∨ ∃ B, computes R B ∧ B.size + (E.card - R.card) + 1 ≤ C.size) := by
    have split := Finset.card_filter_add_card_filter_not (s := E) (p := hit v)
    have pos := Finset.card_pos.mpr hv
    have hz : circuitFun (n+m) D (fun _ => false) = false := by rw [hf]; simp [val]
    obtain ⟨B, bm, bs, bf⟩ := normalize _ _ hm hz
    exact ⟨by omega, Or.inr ⟨B, ⟨bm, fun x => congrFun (bf.trans hf) x⟩, by omega⟩⟩
  by_cases ex : ∃ u v, u ≠ v ∧ (E.filter (hit u)).card = 1 ∧
      (∃ e ∈ E, hit u e ∧ hit v e) ∧ (E.filter (hit v)).card < 3
  · obtain ⟨u,v,ne,leaf,adj,small⟩ := ex
    obtain ⟨D, hm, hf, hs⟩ := pendant n m E C mono fc u v ne leaf adj (hstar v)
    have deg : min 3 ((E.filter (hit v)).card + 1) = (E.filter (hit v)).card + 1 := by omega
    change D.size + min 3 ((E.filter (hit v)).card + 1) ≤ C.size at hs
    rw [deg] at hs
    obtain ⟨e, he, _, hv⟩ := adj
    exact ⟨v, finish v ⟨e, Finset.mem_filter.mpr ⟨he,hv⟩⟩ D hm hf (by omega)⟩
  · have large : ∀ u v, u ≠ v → (E.filter (hit u)).card = 1 →
        (∃ e ∈ E, hit u e ∧ hit v e) → 3 ≤ (E.filter (hit v)).card := by
      intro u v n h a
      exact Nat.le_of_not_gt (fun lt => ex ⟨u,v,n,h,a,lt⟩)
    obtain ⟨v,hv,D,hm,hf,hs⟩ := hubs n m E C c4 hc.1 fc hleaf large hstar
    exact ⟨v, finish v hv D hm hf hs⟩
