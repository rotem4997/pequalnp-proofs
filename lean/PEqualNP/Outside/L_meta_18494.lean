import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18494

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def Related (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem step {a b : List Bool} (h : Related a b) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) :
    Related (advance a g) (advance b g) := by
  rcases h with ⟨hlen, hmono⟩
  have evalMono :
      g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hop with hop | hop
    · simpa only [hop, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true] using
        (fun (had : ∀ i ∈ g.inputs, a.getD i false = true) i hi =>
          hmono i (had i hi))
    · simp only [hop, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
      rintro ⟨i, hi, had⟩
      exact ⟨i, hi, hmono i had⟩
  refine ⟨by simp [advance, hlen], ?_⟩
  intro i
  by_cases hm : i < a.length
  · rw [advance, advance, List.getD_append _ _ _ _ hm,
      List.getD_append _ _ _ _ (by omega)]
    exact hmono i
  · rw [advance, advance, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← hlen]
    cases i - a.length with
    | zero => simpa only [List.getD_cons_zero] using evalMono
    | succ j => simp

private theorem run (gs : List Gate) (a b : List Bool) (h : Related a b)
    (good : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    Related (gs.foldl advance a) (gs.foldl advance b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hg := good g (List.mem_cons_self)
    exact ih _ _ (step h g hg) (fun q hq => good q (List.mem_cons_of_mem _ hq))


private def Below (x y : Fin 10 → Bool) : Prop := ∀ j, x j = true → y j = true

private instance (x y : Fin 10 → Bool) : Decidable (Below x y) := by
  unfold Below
  infer_instance

private theorem evalMono (C : Circuit) (hC : Monotone2 C) {x y : Fin 10 → Bool}
    (hle : Below x y) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have init : Related (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro k
    by_cases h : k < 10
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
      simp only [List.getElem_ofFn]
      exact hle ⟨k, h⟩
    · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt h)]
      simp
  exact (run C.gates _ _ init (fun g hg => by simpa using (hC g hg).1)).2 C.output

private def update (mask : ℕ) (b : Bool) (i : Fin 10) : Bool :=
  Function.update (fun j : Fin 10 => mask.testBit j.val) 0 (mask.testBit 0 && b) i

private def positives : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]

private def negatives : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

private def graph (x8 : Fin 10 → Bool) : Bool := x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem positiveCertificate :
    ∀ x : Fin 10 → Bool, x 0 = false → graph x = true →
      ∃ m ∈ positives, ∀ b, Below (update m b) x := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem negativeCertificate :
    ∀ x : Fin 10 → Bool, x 0 = false → graph x = false →
      ∃ m ∈ negatives, ∀ b, Below x (update m b) := by
  decide +kernel

end PEqualNP.Outside.L_meta_18494

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18494 in
theorem PEqualNP.Outside.L_meta_18494 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ → Bool), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) (0 : Fin (10 : ℕ)) (x4.testBit (0 : ℕ) && x2 x4))) = Bool.true) → (∀ x5 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) (0 : Fin (10 : ℕ)) (x5.testBit (0 : ℕ) && x2 x5))) = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x6 (0 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn x6) = (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by

  intro C f mono pos neg x hzero
  change C.eval (List.ofFn x) = graph x
  cases h : graph x with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨m, hm, hle⟩ := negativeCertificate x hzero h
    have htrue := evalMono C mono (hle (f m)) yes
    exact Bool.noConfusion (htrue.symm.trans (neg m hm))
  | true =>
    obtain ⟨m, hm, hle⟩ := positiveCertificate x hzero h
    exact evalMono C mono (hle (f m)) (pos m hm)
