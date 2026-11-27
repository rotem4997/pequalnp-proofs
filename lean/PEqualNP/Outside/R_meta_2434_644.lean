import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.NotPremium

-- A set of gates may be switched off together when it preserves all the
-- edge inputs surviving a single bad gate. The first child compacts the
-- resulting constant gates. The second compares lost edges with the
-- cardinality of a simultaneous switch-off, using only edge observations.
theorem PEqualNP.Outside.R_meta_2434_644
    (compact : ∀ (n : ℕ) (C : Circuit) (S : Finset ℕ), Monotone2 C →
      S ⊆ Finset.range C.size → (∀ j ∈ S, gateAt C j = constGate false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + S.card ≤ C.size ∧ circuitFun n D = circuitFun n C)
    (charge : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      let hits := fun C : Circuit => G.edgeFinset.filter fun e => circuitFun n C (fun v => decide (v ∈ e)) = true
      ∀ C : Circuit, Monotone2 C → circuitFun n C ≤ graphFun G ∅ →
      (∀ B : Circuit, Monotone2 B → circuitFun n B ≤ graphFun G ∅ →
        B.size < C.size → (hits B).card < (hits C).card) →
      let bad := fun j : ℕ => (gateAt C j).op = GateOp.and ∧
        ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      (∃ j, bad j) →
      let masked := fun S : Finset ℕ => Circuit.mk
        (C.gates.mapIdx fun i g => if i ∈ S then constGate false else g) C.output
      ∃ j, bad j ∧ ∃ S : Finset ℕ, j ∈ S ∧ S ⊆ Finset.range C.size ∧
        hits (masked S) = hits (masked {j}) ∧
        (hits C).card ≤ (hits (masked S)).card + k * S.card) :
    ∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →         have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x7 x8 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ x8 = Bool.true;         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x8 fun (x10 : Fin x2) => Decidable.decide (x10 ∈ x9)) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x11 : Fin x2) (x12 : Fin x2), ¬x3.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x9 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true;         ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → x7 x10 → (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 → x7 x13 → x13.size < x10.size → (x8 x13).card < (x8 x10).card) → (∃ (x14 : ℕ), x9 x10 x14) → ∃ (x15 : ℕ), x9 x10 x15 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ x7 x16 ∧ x16.size < x10.size ∧ x8 x16 = x8 { gates := PEqualNP.NotPremium.replaceByConst x10.gates x15 Bool.false, output := x10.output : PEqualNP.CircuitLowerBounds.Circuit } ∧ (x8 x10).card ≤ (x8 x16).card + x1 * (x10.size - x16.size) := by
  obtain ⟨k, price⟩ := charge
  refine ⟨k, ?_⟩
  intro n G inst hd hg safe hits bad C hm hs record dirty
  have safe_iff (B : Circuit) : safe B ↔ circuitFun n B ≤ graphFun G ∅ := by
    change (∀ x, circuitFun n B x = true → graphFun G ∅ x = true) ↔ _
    exact ⟨fun h x => Bool.le_iff_imp.mpr (h x), fun h x => Bool.le_iff_imp.mp (h x)⟩
  obtain ⟨j, hj, S, hjS, hS, same, bound⟩ := price n G hd hg C hm
    ((safe_iff C).mp hs) (fun B hB sb => record B hB ((safe_iff B).mpr sb)) dirty
  let gs := C.gates.mapIdx fun i g => if i ∈ S then constGate false else g
  let M : Circuit := ⟨gs, C.output⟩
  have len : gs.length = C.gates.length := by simp [gs]
  have atGate (i : ℕ) (hi : i < C.gates.length) :
      gs[i]'(len ▸ hi) = if i ∈ S then constGate false else C.gates[i] := by simp [gs]
  have mono : Monotone2 M := by
    intro g hgmem
    change g ∈ gs at hgmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hgmem
    have hlt : i < C.gates.length := len ▸ hi
    rw [atGate i hlt]
    split
    · exact ⟨Or.inr rfl, by decide⟩
    · exact hm _ (List.getElem_mem hlt)
  have consts (i : ℕ) (hi : i ∈ S) : gateAt M i = constGate false := by
    have hlt : i < C.gates.length := Finset.mem_range.mp (hS hi)
    change gs.getD i _ = _
    rw [List.getD_eq_getElem _ _ (by omega), atGate i hlt, ite_eq_left hi]
  have sub : circuitFun n M ≤ circuitFun n C := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have step_le (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
        (a b : List Bool) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
        g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
      rcases hop with e | e <;> rw [e]
      · change (_ : List Bool).all id = true → (_ : List Bool).all id = true
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        exact fun ha i hi => h i (ha i hi)
      · change (_ : List Bool).any id = true → (_ : List Bool).any id = true
        simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        rintro ⟨i, hi, ha⟩
        exact ⟨i, hi, h i ha⟩
    have run (ls : List Gate) (hls : ∀ g ∈ ls, g.op = GateOp.and ∨ g.op = GateOp.or)
        (off : ℕ → Bool) (a b : List Bool) (hlen : a.length = b.length)
        (h : ∀ i, a.getD i false = true → b.getD i false = true) :
        ∀ i, ((ls.mapIdx fun i g => if off i then constGate false else g).foldl step a).getD i false = true →
          (ls.foldl step b).getD i false = true := by
      induction ls generalizing off a b with
      | nil => exact h
      | cons g ls ih =>
        rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons]
        apply ih (fun g' hg' => hls g' (List.mem_cons_of_mem _ hg')) (fun i => off (i+1))
        · simp [step, hlen]
        · intro i
          by_cases hlt : i < a.length
          · simpa only [step, List.getD_append _ _ _ _ hlt,
              List.getD_append _ _ _ _ (hlen ▸ hlt)] using h i
          · by_cases heq : i = a.length
            · subst i
              simp only [step, List.getD_eq_getElem?_getD, List.getElem?_concat_length,
                Option.getD_some]
              rw [hlen, List.getElem?_concat_length]
              split
              · intro hf
                cases hf
              · exact step_le g (hls g (by simp)) a b h
            · have ha : (step a (if off 0 then constGate false else g)).length ≤ i := by simp [step]; omega
              rw [List.getD_eq_default _ _ ha]
              intro hf
              cases hf
    intro x
    apply Bool.le_iff_imp.mpr
    change (gs.foldl step (List.ofFn x)).getD C.output false = true →
      (C.gates.foldl step (List.ofFn x)).getD C.output false = true
    simpa only [gs, decide_eq_true_eq] using
      run C.gates (fun g hg' => (hm g hg').1) (fun i => decide (i ∈ S)) (List.ofFn x) (List.ofFn x)
        rfl (fun _ => id) C.output
  have msize : M.size = C.size := len
  obtain ⟨D, hD, saved, funEq⟩ := compact n M S mono (msize ▸ hS) consts
  have single : (C.gates.mapIdx fun i g => if i ∈ ({j} : Finset ℕ) then constGate false else g) =
      replaceByConst C.gates j false := by
    change _ = C.gates.set j (constGate false)
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp [List.getElem_set, eq_comm]
  have hitsEq : hits D = hits M := by
    change G.edgeFinset.filter _ = G.edgeFinset.filter _
    simp only [funEq]
  change hits M = hits ⟨_, C.output⟩ at same
  rw [single] at same
  change (hits C).card ≤ (hits M).card + k * S.card at bound
  have small : D.size + S.card ≤ C.size := msize ▸ saved
  have pos := Finset.card_pos.mpr (show S.Nonempty from ⟨j, hjS⟩)
  refine ⟨j, hj, D, hD, (safe_iff D).mpr ?_, by omega, hitsEq.trans same, ?_⟩
  · rw [funEq]
    exact sub.trans ((safe_iff C).mp hs)
  · rw [hitsEq]
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (by omega)) _)
