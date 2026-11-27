import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.HeptadCover

-- If adding one input makes a wire true, either it reaches that wire through
-- enabled gates or it reaches both operands of a conjunction in a true cone.
theorem PEqualNP.Outside.R_meta_4021_47
    (trace : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (x y : Fin n → Bool) (r : Fin n),
      (∀ i, x i = false → y i = true → i = r) →
      let v := wireValue C n
      let step (u w : ℕ) := ∃ j g q, w = n + j ∧ C.gates[j]? = some g ∧
        (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧ (g.op = .or ∨ g.op = .and ∧ v x q = true)
      let live (u w : ℕ) := ∃ j, w = n + j ∧ u ∈ (gateAt C j).inputs ∧ v y w = true
      ∀ w, v x w = false → v y w = true → Relation.ReflTransGen step r.val w ∨
        ∃ j a b, C.gates[j]? = some ⟨.and,[a,b]⟩ ∧ v y (n+j) = true ∧
          v x a = false ∧ v x b = false ∧ Relation.ReflTransGen step r.val a ∧
          Relation.ReflTransGen step r.val b ∧ Relation.ReflTransGen live (n+j) w)
    (bound : ∀ (C : Circuit), let n := 26
      C.size ≤ 64 → IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      let v := wireValue C n
      (∀ x, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      0 < andPairs n C →
      (∃ j < C.size, (gateAt C j).op = .and ∧ ¬ PEqualNP.CircuitMoves.WireBelowOutput n C (n+j)) →
      let s (b : Bool) : Fin n := if b then 0 else 13
      let x (b : Bool) (i : Fin n) := decide (i = s b)
      let step (b : Bool) (u w : ℕ) := n ≤ w ∧ ∃ q, let g := gateAt C (w-n)
        g.inputs.Perm [u,q] ∧ (g.op = .or ∨ v (x b) q = true)
      (∀ b : Bool, ∃ j a c, C.gates[j]? = some ⟨.and,[a,c]⟩ ∧
        (∀ t ∈ [a,c], v (x b) t = false ∧ Relation.ReflTransGen (step b) (s (!b)).val t) ∧
        Relation.ReflTransGen (fun u w => n ≤ w ∧ u ∈ (gateAt C (w-n)).inputs ∧
          v (fun i => x true i || x false i) w = true) (n+j) C.output) → False) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output := by
  dsimp only
  intro C hC
  obtain ⟨hsize, hmodel, hdistinct, hcomputes, hpairs, hdirty⟩ := hC
  let s (b : Bool) : Fin 26 := if b then 0 else 13
  let x (b : Bool) (i : Fin 26) := decide (i = s b)
  let y (i : Fin 26) := decide (i = 0 ∨ i = 13)
  let step (b : Bool) (u w : ℕ) := ∃ j g q, w = 26+j ∧ C.gates[j]? = some g ∧
    (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧
    (g.op = .or ∨ g.op = .and ∧ wireValue C 26 (x b) q = true)
  change Relation.ReflTransGen (step true) 13 C.output ∨
    Relation.ReflTransGen (step false) 0 C.output
  by_contra hn
  have hbad (b : Bool) : ¬ Relation.ReflTransGen (step b) (s (!b)).val C.output := by
    cases b
    · exact fun h => hn (Or.inr h)
    · exact fun h => hn (Or.inl h)
  have hfalse (b : Bool) : wireValue C 26 (x b) C.output = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨p, l, _, hp, hl⟩ := (hcomputes (x b)).mp hv
    cases b
    · have hp' : ∀ p : Fin 13, x false (Fin.castAdd 13 p) = false := by decide
      rw [hp'] at hp
      cases hp
    · have hl' : ∀ l : Fin 13, x true (Fin.natAdd 13 l) = false := by decide
      rw [hl'] at hl
      cases hl
  have htrue : wireValue C 26 y C.output = true :=
    (hcomputes y).mpr ⟨0, 0, by decide, by decide, by decide⟩
  have hchange (b : Bool) : ∀ i, x b i = false → y i = true → i = s (!b) := by
    cases b <;> decide
  have hcomputes' : ∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true := by
    intro z
    have hinc : ∀ p l : Fin 13, p - l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l := by decide
    rw [hcomputes]
    simp only [hinc]
  have hdirty' : ∃ j < C.size, (gateAt C j).op = .and ∧
      ¬ PEqualNP.CircuitMoves.WireBelowOutput 26 C (26+j) := by
    obtain ⟨j, hj, hop, z, hz, ho⟩ := hdirty
    refine ⟨j, hj, hop, fun h => ?_⟩
    have h' := h z hz
    rw [ho] at h'
    cases h'
  apply bound C hsize hmodel hdistinct hcomputes' hpairs hdirty'
  intro b
  rcases trace 26 C hmodel (x b) y (s (!b)) (hchange b) C.output (hfalse b) htrue with h | h
  · exact False.elim (hbad b h)
  · obtain ⟨j, a, c, hj, _, ha, hc, hpa, hpc, hlive⟩ := h
    have hs (u w : ℕ) (hsu : step b u w) :
        26 ≤ w ∧ ∃ q, let g := gateAt C (w-26)
          g.inputs.Perm [u,q] ∧ (g.op = .or ∨ wireValue C 26 (x b) q = true) := by
      obtain ⟨k, g, q, rfl, hg, hargs, hop⟩ := hsu
      have hk : k < C.gates.length := by
        by_contra! h
        rw [List.getElem?_eq_none h] at hg
        cases hg
      have he : gateAt C k = g := (List.getD_eq_getElem _ _ hk).trans
        (Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hg))
      refine ⟨by omega, q, ?_⟩
      dsimp only
      rw [show 26+k-26 = k by omega, he]
      refine ⟨?_, hop.imp_right And.right⟩
      rcases hargs with h | h
      · simpa only [h] using List.Perm.refl [u,q]
      · simpa only [h] using List.Perm.swap u q []
    refine ⟨j, a, c, hj, ?_, Relation.ReflTransGen.mono ?_ _ _ hlive⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨ha, Relation.ReflTransGen.mono hs _ _ hpa⟩
      · exact ⟨hc, Relation.ReflTransGen.mono hs _ _ hpc⟩
    · intro u w h
      obtain ⟨k, rfl, hm, hv⟩ := h
      have hpair : (fun i => x true i || x false i) = y := by
        funext i
        revert i
        decide
      rw [show 26+k-26 = k by omega]
      exact ⟨by omega, hm, hpair ▸ hv⟩
