import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1924_2
    (empty : ∀ (pin : Fin 11) (D : Circuit), FanInTwo D → D.size ≤ 13 →
      D.output ≤ 24 → (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [!(w.getD pin.val false)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (andCase : ∀ (pins : List (Fin 11)) (P D : Circuit), pins.length ≤ 2 →
      Monotone2 P → FanInTwo D → P.size + D.size ≤ 12 → P.output ≤ 24 → D.output ≤ 24 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := P.wires (w ++ [GateOp.and.eval (pins.map fun i => w.getD i.val false)])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (orCase : ∀ (pins : List (Fin 11)) (P D : Circuit), pins.length ≤ 2 →
      Monotone2 P → FanInTwo D → P.size + D.size ≤ 12 → P.output ≤ 24 → D.output ≤ 24 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := P.wires (w ++ [GateOp.or.eval (pins.map fun i => w.getD i.val false)])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := x1.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]);           x2.eval (x6 ++ [!x6.getD x1.output Bool.false]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size + x2.size := by
  intro P D hP hD computes
  by_contra! small
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let clip := fun (g : Gate) => { g with inputs := g.inputs.map (min 24) }
  let clipped := fun (C : Circuit) => Circuit.mk (C.gates.map clip) (min 24 C.output)
  have readClip (w : List Bool) (n i : ℕ) (h : w.length ≤ n) :
      w.getD (min n i) false = w.getD i false := by
    by_cases hi : i ≤ n
    · rw [min_eq_right hi]
    · rw [min_eq_left (by omega), List.getD_eq_default _ _ h,
          List.getD_eq_default _ _ (by omega)]
  have foldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldClip (gs : List Gate) (w : List Bool) (h : w.length + gs.length ≤ 24) :
      (gs.map clip).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hw : w.length ≤ 24 := by omega
      have stepEq : step w (clip g) = step w g := by
        simp only [step, clip, List.map_map, Function.comp_def]
        apply congrArg (fun v => w ++ [g.op.eval v])
        exact List.map_congr_left fun i _ => readClip w 24 i hw
      rw [stepEq]
      apply ih
      dsimp [step]
      simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega
  have clipWires (C : Circuit) (w : List Bool) (h : w.length + C.size ≤ 24) :
      (clipped C).wires w = C.wires w := by
    change (C.gates.map clip).foldl step w = C.gates.foldl step w
    exact foldClip C.gates w h
  have clipEval (C : Circuit) (w : List Bool) (h : w.length + C.size ≤ 24) :
      (clipped C).eval w = C.eval w := by
    change ((clipped C).wires w).getD (min 24 C.output) false = (C.wires w).getD C.output false
    rw [clipWires C w h]
    apply readClip
    rw [show (C.wires w).length = w.length + C.size from foldLen C.gates w]
    exact h
  have gateEq (C : Circuit) : (clipped C).size = C.size := by
    change (C.gates.map clip).length = C.gates.length
    exact List.length_map clip
  have clipMono (C : Circuit) (hc : Monotone2 C) : Monotone2 (clipped C) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [clip] using hc g' hg'
  have clipFan (C : Circuit) (hc : FanInTwo C) : FanInTwo (clipped C) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [clip] using hc g' hg'
  have bounded (C : Circuit) (g : Gate) (hg : g ∈ (clipped C).gates) (i : ℕ)
      (hi : i ∈ g.inputs) : i ≤ 24 := by
    obtain ⟨g', _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact Nat.min_le_left _ _
  have original (x : Fin 9 → Bool) :
      let w := List.ofFn x ++ [x 0 || x 4]
      let v := (clipped P).wires w
      (clipped D).eval (v ++ [!(v.getD (clipped P).output false)]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    dsimp only
    let w := List.ofFn x ++ [x 0 || x 4]
    have wl : w.length = 10 := by simp [w]
    have hw : w.length + P.size ≤ 24 := by omega
    have hv : (P.wires w).length = w.length + P.size := foldLen P.gates w
    change (clipped D).eval ((clipped P).wires w ++
      [!((clipped P).wires w).getD (min 24 P.output) false]) = _
    have hv24 : (P.wires w).length ≤ 24 := by omega
    rw [clipWires P w hw, readClip _ _ _ hv24, clipEval]
    · exact computes x
    · simp only [List.length_append, List.length_singleton, hv]
      omega
  have psmall : (clipped P).size + (clipped D).size ≤ 13 := by
    rw [gateEq, gateEq]
    omega
  have hpout : (clipped P).output ≤ 24 := Nat.min_le_left _ _
  have hdout : (clipped D).output ≤ 24 := Nat.min_le_left _ _
  have hp := clipMono P hP
  have hd := clipFan D hD
  have hb := bounded D
  generalize hP' : clipped P = P' at original psmall hpout hp
  have bp : ∀ g ∈ P'.gates, ∀ i ∈ g.inputs, i ≤ 24 := by
    rw [← hP']
    exact bounded P
  rcases P' with ⟨gs, out⟩
  cases gs with
  | nil =>
    let pin : Fin 11 := ⟨min 10 out, by omega⟩
    have sizeD : (clipped D).size ≤ 13 := by
      change 0 + (clipped D).size ≤ 13 at psmall
      simpa only [Nat.zero_add] using psmall
    obtain ⟨x, hx⟩ := empty pin (clipped D) hd sizeD hdout hb
    apply hx
    have hh := original x
    dsimp only [Circuit.wires, List.foldl_nil] at hh ⊢
    have hr : (List.ofFn x ++ [x 0 || x 4]).getD pin.val false =
        (List.ofFn x ++ [x 0 || x 4]).getD out false := by
      exact readClip _ 10 out (by simp)
    rwa [hr]
  | cons g gs =>
    let Q : Circuit := ⟨gs, out⟩
    let pins : List (Fin 11) := g.inputs.map fun i => ⟨min 10 i, by omega⟩
    have hg := hp g (by simp)
    have hlen : pins.length ≤ 2 := by simpa [pins] using hg.2
    have hQ : Monotone2 Q := fun a ha => hp a (List.mem_cons_of_mem _ ha)
    have hsize : Q.size + (clipped D).size ≤ 12 := by
      change gs.length + 1 + (clipped D).size ≤ 13 at psmall
      change gs.length + (clipped D).size ≤ 12
      omega
    have boundAll : ∀ a ∈ Q.gates ++ (clipped D).gates, ∀ i ∈ a.inputs, i ≤ 24 := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact bp a (List.mem_cons_of_mem _ ha)
      · exact hb a ha
    have hpins (w : List Bool) (h : w.length ≤ 10) :
        pins.map (fun i => w.getD i.val false) = g.inputs.map (fun i => w.getD i false) := by
      simp only [pins, List.map_map, Function.comp_def]
      exact List.map_congr_left fun i _ => readClip w 10 i h
    have hOp : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
    have hresult (op : GateOp) (hop : g.op = op) (x : Fin 9 → Bool) :
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := Q.wires (w ++ [op.eval (pins.map fun i => w.getD i.val false)])
        (clipped D).eval (v ++ [!(v.getD Q.output false)]) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      dsimp only
      rw [hpins _ (by simp), ← hop]
      exact original x
    rcases hOp with ha | ho
    · obtain ⟨x, hx⟩ := andCase pins Q (clipped D) hlen hQ hd hsize hpout hdout boundAll
      exact hx (hresult GateOp.and ha x)
    · obtain ⟨x, hx⟩ := orCase pins Q (clipped D) hlen hQ hd hsize hpout hdout boundAll
      exact hx (hresult GateOp.or ho x)
