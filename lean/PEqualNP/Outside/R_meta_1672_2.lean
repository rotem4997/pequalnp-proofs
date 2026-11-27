import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split at the first gate that reads the forced conjunction.
-- An unused forced wire leaves a fourteen-gate search on the nine actual inputs.
theorem PEqualNP.Outside.R_meta_1672_2 :
  (∀ (tail : Circuit), tail.size ≤ 14 → FanInTwo tail →
    tail.output ≤ 24 → tail.output ≠ 9 →
    (∀ g ∈ tail.gates, ∀ i ∈ g.inputs, i ≤ 24 ∧ i ≠ 9) →
    ∃ x : Fin 9 → Bool, tail.eval (List.ofFn x ++ [x 4 && x 6]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (before after : List Gate) (pins : List ℕ) (out : ℕ),
    before.length + after.length ≤ 13 →
    (∀ g ∈ before, 9 ∉ g.inputs) → 9 ∈ pins →
    let tail : Circuit := ⟨before ++ ⟨.and, pins⟩ :: after, out⟩
    FanInTwo tail → out ≤ 24 → out ≠ 9 →
    (∀ g ∈ tail.gates, ∀ i ∈ g.inputs, i ≤ 24) →
    ∃ x : Fin 9 → Bool, tail.eval (List.ofFn x ++ [x 4 && x 6]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (before after : List Gate) (pins : List ℕ) (out : ℕ),
    before.length + after.length ≤ 13 →
    (∀ g ∈ before, 9 ∉ g.inputs) → 9 ∈ pins →
    let tail : Circuit := ⟨before ++ ⟨.or, pins⟩ :: after, out⟩
    FanInTwo tail → out ≤ 24 → out ≠ 9 →
    (∀ g ∈ tail.gates, ∀ i ∈ g.inputs, i ≤ 24) →
    ∃ x : Fin 9 → Bool, tail.eval (List.ofFn x ++ [x 4 && x 6]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (before after : List Gate) (pins : List ℕ) (out : ℕ),
    before.length + after.length ≤ 13 →
    (∀ g ∈ before, 9 ∉ g.inputs) → 9 ∈ pins →
    let tail : Circuit := ⟨before ++ ⟨.not, pins⟩ :: after, out⟩
    FanInTwo tail → out ≤ 24 → out ≠ 9 →
    (∀ g ∈ tail.gates, ∀ i ∈ g.inputs, i ≤ 24) →
    ∃ x : Fin 9 → Bool, tail.eval (List.ofFn x ++ [x 4 && x 6]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro noRead andRead orRead notRead circuit fan first correct
  by_contra sizeFailure
  have limit : circuit.size ≤ 15 := by omega
  let target (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let input (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 && x 6]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      obtain ⟨extra, heq, hlength⟩ := ih (step w g)
      refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: extra, ?_, by simp [hlength]⟩
      change run gs (step w g) = _
      rw [heq]
      simp [step, List.append_assoc]
  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    obtain ⟨extra, heq, hlength⟩ := extend gs w
    simp [heq, hlength]
  let clip (i : ℕ) := min i 24
  have readClip (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
      w.getD (clip i) false = w.getD i false := by
    change w.getD (min i 24) false = _
    by_cases hi : i ≤ 24
    · rw [min_eq_left hi]
    rw [min_eq_right (by omega : 24 ≤ i), List.getD_eq_default _ false hw,
      List.getD_eq_default _ false (by omega : w.length ≤ i)]
  let norm (g : Gate) : Gate := ⟨g.op, g.inputs.map clip⟩
  have runNorm (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 24) :
      run (gs.map norm) w = run gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change run (gs.map norm) (step w (norm g)) = run gs (step w g)
      have sw : step w (norm g) = step w g := by
        simp only [step, norm, List.map_map, Function.comp_def, readClip w (by omega)]
      rw [sw]
      apply ih
      simpa only [step, List.length_cons, List.length_append, List.length_singleton, List.length_nil, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm 1] using hw
  have locate (gs : List Gate) (hits : ∃ g ∈ gs, 9 ∈ g.inputs) :
      ∃ (before : List Gate) (g : Gate) (after : List Gate),
        gs = before ++ g :: after ∧
        (∀ e ∈ before, 9 ∉ e.inputs) ∧ 9 ∈ g.inputs := by
    induction gs with
    | nil => simp at hits
    | cons g gs ih =>
      by_cases hg : 9 ∈ g.inputs
      · exact ⟨[], g, gs, rfl, by simp, hg⟩
      · obtain ⟨before, mid, after, heq, beforeClean, midHit⟩ :=
          ih (by simpa [hg] using hits)
        refine ⟨g :: before, mid, after, ?_, ?_, midHit⟩
        · rw [List.cons_append, heq]
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hg
          · exact beforeClean e he
  obtain ⟨gs, out⟩ := circuit
  cases gs with
  | nil =>
    have hf := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at hf
    rw [List.getD_eq_default _ false (by simp)] at hf
    contradiction
  | cons g rest =>
    have tailLimit : rest.length ≤ 14 := by
      change (g :: rest).length ≤ 15 at limit
      simp only [List.length_cons] at limit
      omega
    have firstValue (x : Fin 9 → Bool) :
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 && x 6) := by
      let value := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      obtain ⟨extra, heq, _⟩ := extend rest (List.ofFn x ++ [value])
      have h := first x
      change (run rest (List.ofFn x ++ [value])).getD 9 false = _ at h
      rw [heq, List.getD_append _ _ false 9 (by simp),
        List.getD_append_right _ _ false 9 (by simp)] at h
      change value = (x 4 && x 6)
      exact h
    let tail : Circuit := ⟨rest.map norm, clip out⟩
    have tailSmall : tail.size ≤ 14 := by
      change (rest.map norm).length ≤ 14
      rwa [List.length_map]
    have tailFan : FanInTwo tail := by
      intro a ha
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ha
      have h := fan old (List.mem_cons_of_mem _ hold)
      exact ⟨h.1, by simpa [norm] using h.2⟩
    have indices : ∀ g ∈ tail.gates, ∀ i ∈ g.inputs, i ≤ 24 := by
      intro a ha i hi
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact min_le_right j 24
    have computes (x : Fin 9 → Bool) : tail.eval (input x) = target x := by
      have h := congrFun correct x
      change (run rest (List.ofFn x ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD out false =
        target x at h
      rw [firstValue] at h
      change (run rest (input x)).getD out false = _ at h
      have bound : (input x).length + rest.length ≤ 24 := by
        simp [input]
        omega
      change (run (rest.map norm) (input x)).getD (clip out) false = _
      rw [runNorm rest _ bound, readClip _ (by rwa [runLength])]
      exact h
    have outBound : tail.output ≤ 24 := min_le_right out 24
    have outNotNine : tail.output ≠ 9 := by
      intro heq
      let x (i : Fin 9) := decide (i = 4 ∨ i = 6)
      have hx : target x = false := by decide
      obtain ⟨extra, r, _⟩ := extend tail.gates (input x)
      have hout := computes x
      change (run tail.gates (input x)).getD tail.output false = target x at hout
      rw [r, heq, hx, List.getD_append _ _ false 9 (by simp [input]),
        show (input x).getD 9 false = true by decide] at hout
      contradiction
    suffices wrong : ∃ x, tail.eval (input x) ≠ target x by
      obtain ⟨x, hx⟩ := wrong
      exact hx (computes x)
    by_cases hit : ∃ gate ∈ tail.gates, 9 ∈ gate.inputs
    · obtain ⟨before, mid, after, parts, hc, hm⟩ := locate tail.gates hit
      have hlen : before.length + after.length ≤ 13 := by
        change tail.gates.length ≤ 14 at tailSmall
        simp only [parts, List.length_append, List.length_cons] at tailSmall
        omega
      have onlyOp : mid.op = .and ∨ mid.op = .or ∨ mid.op = .not := by
        have h := (tailFan mid (by simp [parts])).1
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
      have same : tail = ⟨before ++ mid :: after, tail.output⟩ := by
        rcases tail with ⟨gates, out⟩
        rw [←parts]
      obtain ⟨midOp, pins⟩ := mid
      rw [same]
      rcases onlyOp with rfl | rfl | rfl
      · exact andRead before after pins _ hlen hc hm (same ▸ tailFan) outBound outNotNine (same ▸ indices)
      · exact orRead before after pins _ hlen hc hm (same ▸ tailFan) outBound outNotNine (same ▸ indices)
      · exact notRead before after pins _ hlen hc hm (same ▸ tailFan) outBound outNotNine (same ▸ indices)
    · apply noRead tail tailSmall tailFan outBound outNotNine
      intro gate hg i hi
      refine ⟨indices gate hg i hi, ?_⟩
      intro hi9
      subst i
      exact hit ⟨gate, hg, hi⟩
