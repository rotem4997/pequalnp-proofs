import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4785_642
    (bits : ∀ (n : ℕ) (C : Circuit) (xs : List ℕ), Monotone2 C →
      let ws := C.gates.foldl (fun w g => w ++ [if g.op.eval [true,false] = true then (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a ||| b) 0
        else (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a &&& b) (2^n-1)]) xs
      ∀ j : ℕ, j < n → (ws.getD C.output 0).testBit j = C.eval (xs.map (fun a => a.testBit j)))
    (finite : let seed : List ℕ := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
      let E := fun u v : ℕ => (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
      let run := fun (C : Circuit) (xs : List ℕ) =>
      (C.gates.foldl (fun w g => w ++ [if g.op.eval [true,false] = true then (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a ||| b) 0
        else (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a &&& b) (2^58-1)]) xs).getD C.output 0
      ∀ (C : Circuit) (r : Fin 14), r = 7 ∨ r = 9 → C.size ≤ 25 → Monotone2 C →
        C.output ≤ 40 → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 40) →
        (∀ g ∈ C.gates, g.op = .and →
          (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
          ∀ a b, g.inputs = [a,b] → a < 14 → b < 14 → a ≠ b → E a b ∨ E b a) →
        ∃ j : Fin 58,
          (run C (seed ++ [seed.getD 0 0 ||| seed.getD r.val 0])).testBit j.val ≠
            (2097151 : ℕ).testBit j.val) :
  have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD x1 (0 : ℕ)).testBit x2 = Bool.true; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), x1 ↑x3 ↑x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)) => PEqualNP.MetaComplexity.Monotone2 x4 ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 x5]]) = Bool.true ↔ x2 x6); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x6 ∈ x5.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → ((14 : ℕ) ∈ x6.inputs → ∀ x10 ∈ x6.inputs, (14 : ℕ) ≤ x10) ∧ ∀ (x9 x10 : ℕ), x6.inputs = [x9, x10] → x9 < (14 : ℕ) → x10 < (14 : ℕ) → x9 ≠ x10 → x1 x9 x10 ∨ x1 x10 x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)), x7 = (7 : Fin (14 : ℕ)) ∨ x7 = (9 : Fin (14 : ℕ)) → x4 x6 x7 → x5 x6 → (26 : ℕ) ≤ x6.size := by
  have clamp : ∀ (n k : ℕ) (C : Circuit), C.size ≤ k → ∀ x : List Bool, x.length = n →
      ({ C with
        gates := C.gates.map (fun g => { g with inputs := g.inputs.map (fun i => min i (n+k)) }),
        output := min C.output (n+k) } : Circuit).eval x = C.eval x := by
    intro n k C hC x hx
    let clampGate (b : ℕ) (g : Gate) : Gate :=
      { g with inputs := g.inputs.map (fun i => min i b) }
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have getD_default (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
        w.getD i false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
      rfl
    have getD_clamp (w : List Bool) (b i : ℕ) (h : w.length ≤ b) :
        w.getD (min i b) false = w.getD i false := by
      by_cases hi : i ≤ b
      · rw [Nat.min_eq_left hi]
      · have hbi : b ≤ i := by omega
        rw [Nat.min_eq_right hbi, getD_default w b h,
          getD_default w i (Nat.le_trans h hbi)]
    have step_clamp (w : List Bool) (b : ℕ) (g : Gate) (h : w.length ≤ b) :
        step w (clampGate b g) = step w g := by
      have hr : (g.inputs.map (fun i => min i b)).map (fun i => w.getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro i hi
        exact getD_clamp w b i h
      unfold step clampGate
      dsimp only
      rw [hr]
    have fold_length (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp [step, Nat.add_comm, Nat.add_left_comm]
    have fold_clamp (gs : List Gate) (w : List Bool) (b : ℕ)
        (h : w.length + gs.length ≤ b) :
        (gs.map (clampGate b)).foldl step w = gs.foldl step w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [step_clamp w b g (by simp only [List.length_cons] at h; omega)]
        apply ih
        simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hbound : x.length + C.gates.length ≤ n + k := by
      have hlen : C.gates.length ≤ k := hC
      rw [hx]
      exact Nat.add_le_add_left hlen n
    change ((C.gates.map (clampGate (n+k))).foldl step x).getD
      (min C.output (n+k)) false = (C.gates.foldl step x).getD C.output false
    rw [fold_clamp C.gates x (n+k) hbound]
    apply getD_clamp
    rw [fold_length]
    exact hbound
  dsimp only
  intro C r hr hOK hP
  by_contra hn
  have small : C.size ≤ 25 := by omega
  let E := fun u v : ℕ => (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u 0).testBit v = true
  let F := fun x : Fin 14 → Bool => ∃ u v : Fin 14, E u.val v.val ∧ x u = true ∧ x v = true
  let B := fun x : Fin 14 → Bool =>
    (F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
    (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))
  let seed : List ℕ := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  let run := fun (C : Circuit) (xs : List ℕ) =>
      (C.gates.foldl (fun w g => w ++ [if g.op.eval [true,false] = true then (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a ||| b) 0
        else (g.inputs.map (fun i => w.getD i 0)).foldr (fun a b => a &&& b) (2^58-1)]) xs).getD C.output 0
  change Monotone2 C ∧ (∀ x, B x →
    (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x)) at hOK
  change (∀ g ∈ C.gates, g.op = .and →
    (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
    ∀ a b, g.inputs = [a,b] → a < 14 → b < 14 → a ≠ b → E a b ∨ E b a) at hP
  let D : Circuit := { C with
    gates := C.gates.map (fun g => { g with inputs := g.inputs.map (fun i => min i 40) }),
    output := min C.output 40 }
  have dsize : D.size = C.size := by
    change D.gates.length = C.gates.length
    simp only [D,List.length_map]
  have dmono : Monotone2 D := by
    intro g hg
    change g ∈ C.gates.map _ at hg
    obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hlen⟩ := hOK.1 g hmem
    exact ⟨hop, by simpa using hlen⟩
  have dbound : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 40 := by
    intro g hg i hi
    change g ∈ C.gates.map _ at hg
    obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
    exact Nat.min_le_right _ _
  have dP : ∀ g ∈ D.gates, g.op = .and →
      (14 ∈ g.inputs → ∀ i ∈ g.inputs, 14 ≤ i) ∧
      ∀ a b, g.inputs = [a,b] → a < 14 → b < 14 → a ≠ b → E a b ∨ E b a := by
    intro g hg hop
    change g ∈ C.gates.map _ at hg
    obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp hg
    have old := hP g hmem hop
    constructor
    · intro h14 i hi
      obtain ⟨a,ha,he⟩ := List.mem_map.mp h14
      have ae : a = 14 := by omega
      have ha14 : 14 ∈ g.inputs := ae ▸ ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
      have hb14 := old.1 ha14 b hb
      omega
    · intro a b hab ha hb hne
      have original : g.inputs = [a,b] := by
        cases hs : g.inputs with
        | nil => simp [hs] at hab
        | cons u rest =>
          cases rest with
          | nil => simp [hs] at hab
          | cons v rest =>
            cases rest with
            | nil =>
              simp only [hs,List.map_cons,List.map_nil,List.cons.injEq] at hab
              have ue : u = a := by have := hab.1; omega
              have ve : v = b := by have := hab.2.1; omega
              simpa only [ue,ve] using hs
            | cons w rest => simp [hs] at hab
      exact old.2 a b original ha hb hne
  have evalD (x : List Bool) (hx : x.length = 15) : D.eval x = C.eval x := by
    simpa [D] using clamp 15 25 C small x hx
  obtain ⟨j,hj⟩ := finite D r hr (by simpa [dsize] using small) dmono
    (show D.output ≤ 40 from Nat.min_le_right _ _) dbound dP
  change (run D (seed ++ [seed.getD 0 0 ||| seed.getD r.val 0])).testBit j.val ≠
    (2097151 : ℕ).testBit j.val at hj
  have rows : ∀ j : Fin 58,
      let x := fun i : Fin 14 => (seed.getD i.val 0).testBit j.val
      B x ∧ (F x ↔ (2097151 : ℕ).testBit j.val = true) := by
    decide +kernel
  have inputrows : ∀ (r : Fin 14) (j : Fin 58),
      (seed ++ [seed.getD 0 0 ||| seed.getD r.val 0]).map (fun a => a.testBit j.val) =
      List.ofFn (fun i : Fin 14 => (seed.getD i.val 0).testBit j.val) ++
        [GateOp.or.eval [(seed.getD 0 0).testBit j.val,(seed.getD r.val 0).testBit j.val]] := by
    decide +kernel
  let x := fun i : Fin 14 => (seed.getD i.val 0).testBit j.val
  have target : C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) =
      (2097151 : ℕ).testBit j.val := by
    apply Bool.eq_iff_iff.mpr
    exact (hOK.2 x (rows j).1).trans (rows j).2
  apply hj
  calc
    (run D (seed ++ [seed.getD 0 0 ||| seed.getD r.val 0])).testBit j.val =
        D.eval ((seed ++ [seed.getD 0 0 ||| seed.getD r.val 0]).map (fun a => a.testBit j.val)) :=
      bits 58 D _ dmono j.val j.isLt
    _ = D.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) := by rw [inputrows]; rfl
    _ = C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) := evalD _ (by simp)
    _ = (2097151 : ℕ).testBit j.val := target
