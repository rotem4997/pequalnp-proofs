import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadTwo (wval fpl)
open PEqualNP.EdgeOwnership (pairInput)

theorem PEqualNP.Outside.R_meta_4021_487
    (locate : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (z : Fin n) (out : ℕ),
      let flipped := Function.update x z true
      let active (u v : ℕ) := ∃ (j : ℕ) (g : Gate) (w : ℕ),
        v = n + j ∧ C.gates[j]? = some g ∧ (g.inputs = [u, w] ∨ g.inputs = [w, u]) ∧
        (g.op = .or ∨ g.op = .and ∧ wval C x w = true)
      PEqualNP.TopForm.IsAO2 n C → wval C flipped out = true → wval C x out = false →
      Relation.ReflTransGen active z.val out ∨ ∃ j < C.gates.length,
        (gateAt C j).op = .and ∧
        (∀ u ∈ (gateAt C j).inputs, wval C flipped u = true ∧ wval C x u = false) ∧
        Relation.ReflTransGen active (n + j) out)
    (collision_case :
      let one (a : Fin 26) (i : Fin 26) := decide (i = a)
      let active (C : Circuit) (a : Fin 26) (u v : ℕ) := ∃ (j : ℕ) (g : Gate) (w : ℕ),
        v = 26 + j ∧ C.gates[j]? = some g ∧ (g.inputs = [u, w] ∨ g.inputs = [w, u]) ∧
        (g.op = .or ∨ g.op = .and ∧ wval C (one a) w = true)
      let collision (C : Circuit) (a : Fin 26) (j : ℕ) :=
        (gateAt C j).op = .and ∧
        (∀ u ∈ (gateAt C j).inputs,
          wval C (pairInput (0 : Fin 26) 13) u = true ∧ wval C (one a) u = false) ∧
        Relation.ReflTransGen (active C a) (26 + j) C.output
      ∀ (C : Circuit), C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        circuitFun 26 C = fpl 13 (fun p l => p ∈ PEqualNP.HeptadCover.singerLines3 l) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ j, (gateAt C j).op = .and ∧
          ∃ y : Fin 26 → Bool, wval C y (26 + j) = true ∧ circuitFun 26 C y = false) →
        (∃ j, collision C 0 j) → (∃ j, collision C 13 j) →
        Relation.ReflTransGen (active C 0) 13 C.output ∨
        Relation.ReflTransGen (active C 13) 0 C.output) :
have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output := by
  dsimp only
  intro C hC
  obtain ⟨hsize, hshape, hnodup, heval, hnested, hdirty⟩ := hC
  let one (a : Fin 26) (i : Fin 26) := decide (i = a)
  let pair := pairInput (0 : Fin 26) 13
  have hot : wval C pair C.output = true := by
    change C.eval (List.ofFn pair) = true
    exact (heval pair).2 ⟨0, 0, by decide, by decide, by decide⟩
  have cold (a : Fin 26) : wval C (one a) C.output = false := by
    change C.eval (List.ofFn (one a)) = false
    cases h : C.eval (List.ofFn (one a))
    · rfl
    · exfalso
      obtain ⟨p, l, _, hp, hl⟩ := (heval (one a)).1 h
      have hp' : Fin.castAdd 13 p = a := of_decide_eq_true hp
      have hl' : Fin.natAdd 13 l = a := of_decide_eq_true hl
      have hz := congrArg Fin.val (hp'.trans hl'.symm)
      change p.val = 13 + l.val at hz
      have hpv := p.isLt
      omega
  have flipLeft : Function.update (one 0) (13 : Fin 26) true = pair := by
    funext i
    change Function.update (one 0) (13 : Fin 26) true i = decide (i = 0 ∨ i = 13)
    by_cases hi : i = (13 : Fin 26) <;> simp [one, hi]
  have flipRight : Function.update (one 13) (0 : Fin 26) true = pair := by
    funext i
    change Function.update (one 13) (0 : Fin 26) true i = decide (i = 0 ∨ i = 13)
    by_cases hi : i = (0 : Fin 26) <;> simp [one, hi]
  have hleft := locate 26 C (one 0) 13 C.output hshape (by rw [flipLeft]; exact hot) (cold 0)
  have hright := locate 26 C (one 13) 0 C.output hshape (by rw [flipRight]; exact hot) (cold 13)
  rcases hleft with hp | ⟨j, _, hjo, hjv, hjr⟩
  · exact Or.inl hp
  rcases hright with hp | ⟨k, _, hko, hkv, hkr⟩
  · exact Or.inr hp
  have hsinger : ∀ p l : Fin 13,
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide
  have hf : circuitFun 26 C = fpl 13 (fun p l => p ∈ PEqualNP.HeptadCover.singerLines3 l) := by
    funext y
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn y) = true ↔ decide (∃ p l : Fin 13,
      p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ y (Fin.castAdd 13 p) = true ∧
      y (Fin.natAdd 13 l) = true) = true
    simpa only [decide_eq_true_eq, ← hsinger] using heval y
  obtain ⟨m, _, hmo, y, hyv, hyo⟩ := hdirty
  exact collision_case C hsize hshape hnodup hf hnested ⟨m, hmo, y, hyv, hyo⟩
    ⟨j, hjo, by simpa only [flipLeft] using hjv, hjr⟩
    ⟨k, hko, by simpa only [flipRight] using hkv, hkr⟩
