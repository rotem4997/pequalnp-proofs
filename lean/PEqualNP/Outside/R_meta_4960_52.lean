import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4960_52
    (block : ∀ (n m : ℕ) (G M : Finset (Fin n × Fin m)) (B : Circuit),
      let edge := fun (e : Fin n × Fin m) (w : Fin (n+m)) => decide (w = Fin.castAdd m e.1 ∨ w = Fin.natAdd n e.2)
      let hit := fun e => circuitFun (n+m) B (edge e) = true
      (∀ a b : Fin n, ∀ u v : Fin m, a ≠ b → u ≠ v → ¬ ((a,u) ∈ G ∧ (a,v) ∈ G ∧ (b,u) ∈ G ∧ (b,v) ∈ G)) → M ⊆ G → (∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b) → (∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) →
      (∃ os as' : List (ℕ × ℕ), B.gates = os.map (fun p => ⟨.or,[p.1,p.2]⟩) ++ as'.map (fun p => ⟨.and,[p.1,p.2]⟩)) →
      (∀ x, circuitFun (n+m) B x = true → (fun x : Fin (n+m) → Bool => decide (∃ e ∈ G, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) x = true) →
      (G.filter hit).card + (M.filter hit).card ≤ B.size + 1)
    (cover : ∃ K : ℕ, ∀ (n m : ℕ) (G : Finset (Fin n × Fin m)) (C : Circuit),
      let edge := fun (e : Fin n × Fin m) (w : Fin (n+m)) => decide (w = Fin.castAdd m e.1 ∨ w = Fin.natAdd n e.2)
      (∀ a b : Fin n, ∀ u v : Fin m, a ≠ b → u ≠ v → ¬ ((a,u) ∈ G ∧ (a,v) ∈ G ∧ (b,u) ∈ G ∧ (b,v) ∈ G)) → IsAO2 (n+m) C → circuitFun (n+m) C = (fun x : Fin (n+m) → Bool => decide (∃ e ∈ G, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) →
      ∃ (d k : ℕ) (B : Fin k → Circuit), 0 < d ∧
        (∀ i, (∃ os as' : List (ℕ × ℕ), (B i).gates = os.map (fun p => ⟨.or,[p.1,p.2]⟩) ++ as'.map (fun p => ⟨.and,[p.1,p.2]⟩)) ∧ (∀ x, circuitFun (n+m) (B i) x = true → circuitFun (n+m) C x = true)) ∧
        (∀ e ∈ G, d ≤ ∑ i : Fin k, if circuitFun (n+m) (B i) (edge e) = true then 1 else 0) ∧
        ∑ i, ((B i).size + 1) ≤ d * (C.size + 1 + K * (n+m+1).sqrt)) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) → PEqualNP.TopForm.IsAO2 (x2 + x3) x6 → (∀ (x9 : Fin (x2 + x3) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3), (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) → x5 ⊆ x4 → (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) → (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) → x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨K,build⟩ := cover
  refine ⟨K,?_⟩
  intro n m G M C sq ao computes sub left right
  let edge := fun (e : Fin n × Fin m) (w : Fin (n+m)) => decide (w = Fin.castAdd m e.1 ∨ w = Fin.natAdd n e.2)
  have correct : circuitFun (n+m) C = (fun x : Fin (n+m) → Bool => decide (∃ e ∈ G, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) := by
    funext x
    rw [computes]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,l,h,hp,hl⟩; exact ⟨(p,l),h,hp,hl⟩
    · rintro ⟨⟨p,l⟩,h,hp,hl⟩; exact ⟨p,l,h,hp,hl⟩
  obtain ⟨d,k,B,hd,form,many,paid⟩ := build n m G C sq ao correct
  let accepts (e : Fin n × Fin m) (i : Fin k) := circuitFun (n+m) (B i) (edge e) = true
  have rows (i : Fin k) :
      (G.filter (fun e => accepts e i)).card + (M.filter (fun e => accepts e i)).card ≤ (B i).size+1 :=
    block n m G M (B i) sq sub left right (form i).1
      (fun x h => correct ▸ (form i).2 x h)
  have tally (S : Finset (Fin n × Fin m)) (incl : S ⊆ G) :
      d * S.card ≤ ∑ i : Fin k, (S.filter (fun e => accepts e i)).card := by
    calc
      d * S.card = ∑ _e ∈ S, d := by simp [Nat.mul_comm]
      _ ≤ ∑ e ∈ S, (Finset.univ.filter (accepts e)).card :=
        Finset.sum_le_sum (fun e he => by simpa only [accepts,Finset.card_filter] using many e (incl he))
      _ = ∑ i : Fin k, (S.filter (fun e => accepts e i)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
  have counts := Nat.add_le_add (tally G (Finset.Subset.refl _)) (tally M sub)
  rw [← Nat.mul_add, ← Finset.sum_add_distrib] at counts
  exact Nat.le_of_mul_le_mul_left ((counts.trans (Finset.sum_le_sum (fun i _ => rows i))).trans paid) hd
