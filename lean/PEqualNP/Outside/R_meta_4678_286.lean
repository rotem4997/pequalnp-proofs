import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each block contains all thirteen simultaneous cyclic shifts of one test.
-- The first four blocks are flags. The other eighteen are quadrangles.
-- One instruction uses seven bits for each operand and one bit for the gate.
-- All candidates have exactly 62 instructions, with the output in wire 90.
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_4678_286
    (samples : let pairs : List ℕ := [8796160139265, 2251799889182721, 215506917523485, 1548117546631239, 1477749337260115, 1267743973179493, 439814119817351, 423325471899843, 1442578117984531, 1408496491315497, 1200703561302353]
    let row := fun (r : Fin 286) => List.ofFn (fun j : Fin 26 =>
      ((pairs.getD (r.val / 26) 0) / 2 ^ (26 * (r.val / 13 % 2))).testBit
        (13 * (j.val / 13) + (j.val % 13 + 13 - r.val % 13) % 13))
    let D : Finset (Fin 13) := {0,1,3,9}
    ∀ r, let x := row r
      if r.val < 52 then ∃ p l : Fin 13, p-l ∈ D ∧
        x = List.ofFn (fun i => decide (i=p)) ++ List.ofFn (fun i => decide (i=l))
      else let Q := Finset.univ.filter (fun i : Fin 13 => x.getD i.val false)
           Q.card=4 ∧ (∀ l, (Q.filter fun i => i-l ∈ D).card ≤ 2) ∧
             x = List.ofFn (fun i : Fin 13 => decide (i∈Q)) ++
               List.ofFn (fun l : Fin 13 => decide (∀ i ∈ Q, i-l ∉ D)))
    (compile : let step := fun (w : List Bool) (t : Fin 32768) =>
      let a := w.getD (t.val % 128) false
      let b := w.getD (t.val / 128 % 128) false
      w ++ [if t.val < 16384 then a && b else a || b]
    ∀ C : Circuit, Monotone2 C → C.size ≤ 62 →
    (∀ i : Fin C.gates.length, ∀ j ∈ (C.gates.get i).inputs, j < 27+i.val) →
    ∃ p : List (Fin 32768), p.length = 62 ∧ ∀ x : List Bool, x.length = 27 →
       (p.foldl step (false :: true :: x)).getD 90 false = C.eval x)
    (exclude : let pairs : List ℕ := [8796160139265, 2251799889182721, 215506917523485, 1548117546631239, 1477749337260115, 1267743973179493, 439814119817351, 423325471899843, 1442578117984531, 1408496491315497, 1200703561302353]
    let row := fun (r : Fin 286) => List.ofFn (fun j : Fin 26 =>
      ((pairs.getD (r.val / 26) 0) / 2 ^ (26 * (r.val / 13 % 2))).testBit
        (13 * (j.val / 13) + (j.val % 13 + 13 - r.val % 13) % 13))
    let step := fun (w : List Bool) (t : Fin 32768) =>
      let a := w.getD (t.val % 128) false
      let b := w.getD (t.val / 128 % 128) false
      w ++ [if t.val < 16384 then a && b else a || b]
    ∀ s ∈ ([[],[0],[13],[0,1],[0,2],[0,13],[0,14],[0,15],[0,17],[0,20],[13,14],[13,15]] : List (List ℕ)), ∀ p : List (Fin 32768), p.length = 62 →
    ∃ r, let x := row r
         (p.foldl step (false :: true :: (x ++ [s.any fun j => x.getD j false]))).getD 90 false
           ≠ decide (r.val < 52)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size := by
  dsimp only
  intro C s hs mono ordered passes
  by_contra! small
  have bound : C.size ≤ 62 := by omega
  let pairs : List ℕ := [8796160139265, 2251799889182721, 215506917523485, 1548117546631239, 1477749337260115, 1267743973179493, 439814119817351, 423325471899843, 1442578117984531, 1408496491315497, 1200703561302353]
  let row := fun (r : Fin 286) => List.ofFn (fun j : Fin 26 =>
    ((pairs.getD (r.val / 26) 0) / 2 ^ (26 * (r.val / 13 % 2))).testBit
      (13 * (j.val / 13) + (j.val % 13 + 13 - r.val % 13) % 13))
  obtain ⟨p, hp, simulates⟩ := compile C mono bound ordered
  obtain ⟨r, mismatch⟩ := exclude s hs p hp
  let x := row r
  have hx : x.length = 26 := List.length_ofFn
  have eq := simulates (x ++ [s.any fun j => x.getD j false]) (by simp [hx])
  change _ ≠ decide (r.val < 52) at mismatch
  rw [eq] at mismatch
  have test := samples r
  by_cases hr : r.val < 52
  · rw [ite_eq_left hr] at test
    obtain ⟨a,b,inc,hab⟩ := test
    have e := passes.1 a b inc
    apply mismatch
    rw [decide_eq_true hr, show x = _ from hab]
    exact e
  · rw [ite_eq_right hr] at test
    obtain ⟨card,cap,hq⟩ := test
    have e := passes.2 _ card cap
    apply mismatch
    rw [decide_eq_false hr, show x = _ from hq]
    exact e
