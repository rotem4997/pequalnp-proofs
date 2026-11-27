import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2768_315
    (andCase : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) → gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      a ≤ 24 → b ≤ 24 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (orCase : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) → gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      a ≤ 24 → b ≤ 24 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false || w.getD b false) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C dataC countC computes
  rcases dataC with ⟨lengthC, outputC, headC, shape⟩
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have nonempty : C.gates ≠ [] := by
    intro h
    simp [h] at lengthC
  let last := C.gates.getLast nonempty
  have lastEq : C.gates[14]'(by omega) = last := by
    simpa [last, lengthC] using
      (List.getElem_length_sub_one_eq_getLast (l := C.gates) (by omega))
  obtain ⟨first, tail, gatesEq⟩ := List.exists_cons_of_ne_nil nonempty
  have firstEq : first = (⟨.or, [0, 3]⟩ : Gate) := by
    simpa [gatesEq] using headC
  subst first
  have tailLength : tail.length = 14 := by
    simp [gatesEq] at lengthC
    omega
  let gs := tail.dropLast
  have lastTail : tail.getLast (by intro h; simp [h] at tailLength) = last := by
    simp only [last, gatesEq]
    cases tail with
    | nil => simp at tailLength
    | cons g t => rfl
  have gates : C.gates = (⟨.or, [0, 3]⟩ : Gate) :: (gs ++ [last]) := by
    conv_lhs => rw [gatesEq]
    congr 1
    simpa [gs, lastTail] using
      (List.dropLast_concat_getLast (l := tail) (by intro h; simp [h] at tailLength)).symm
  have gsLength : gs.length = 13 := by simp [gs, tailLength]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldLength (l : List Gate) (w : List Bool) :
      (l.foldl step w).length = w.length + l.length := by
    induction l generalizing w with
    | nil => simp
    | cons g l ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let D : Circuit := ⟨gs, 0⟩
  have val (x : Fin 9 → Bool) :
      circuitFun 9 C x = last.op.eval (last.inputs.map fun i => (D.wires (start x)).getD i false) := by
    have headVal : step (List.ofFn x) ⟨.or, [0, 3]⟩ = start x := by
      simp [start, step, andEval, orEval, notEval]
    have wireLen : (gs.foldl step (start x)).length = 23 := by
      simp [foldLength, gsLength, start]
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
    rw [gates, outputC, List.foldl_cons, headVal, List.foldl_append]
    change ((gs.foldl step (start x)) ++ [_]).getD 23 false = _
    rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq wireLen), wireLen]
    rfl
  have fan : FanInTwo D := by
    intro g mem
    have inC : g ∈ C.gates := by
      rw [gates]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ mem)
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp inC
    specialize shape i hi
    rw [eq] at shape
    dsimp only at shape
    rcases shape with h | ⟨a, _, h⟩ | ⟨a, b, _, _, _, h | h⟩ <;> rw [h] <;> simp
  have countSum : gs.countP (fun g => g.op.eval [false]) +
      (if last.op.eval [false] then 1 else 0) = 1 := by
    simpa [gates, andEval, orEval, notEval] using countC
  have few : gs.countP (fun g => g.op.eval [false]) ≤ 1 := by omega
  have monotoneFold (l : List Gate)
      (good : ∀ g ∈ l, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (u v : List Bool) (len : u.length = v.length)
      (ord : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (l.foldl step u).getD i false = true → (l.foldl step v).getD i false = true := by
    induction l generalizing u v with
    | nil => exact ord
    | cons g l ih =>
      have tailGood : ∀ a ∈ l, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
        fun a ha => good a (List.mem_cons_of_mem g ha)
      have evalOrd :
          g.op.eval (g.inputs.map fun i => u.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
        have gop : g.op = .and ∨ g.op = .or := by
          simpa using good g (by simp)
        rcases gop with h | h
        · simp only [h, andEval, orEval, notEval, List.all_eq_true, List.mem_map, id_eq]
          intro hu b hm
          rcases hm with ⟨i, hi, he⟩
          exact he ▸ ord i (hu _ ⟨i, hi, rfl⟩)
        · simp only [h, andEval, orEval, notEval, List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b, ⟨i, hi, he⟩, hb⟩
          exact ⟨true, ⟨i, hi, ord i (he.trans hb)⟩, rfl⟩
      simp only [List.foldl_cons]
      apply ih tailGood (step u g) (step v g) (by simp [step, len])
      intro i
      by_cases hi : i < u.length
      · simpa only [step, List.getD_append _ _ _ _ hi,
          List.getD_append _ _ _ _ (len ▸ hi)] using ord i
      · have hu : u.length ≤ i := by omega
        have hv : v.length ≤ i := by omega
        simp only [step, List.getD_append_right _ _ _ _ hu, List.getD_append_right _ _ _ _ hv, ← len]
        cases e : i - u.length with
        | zero => simpa using evalOrd
        | succ k => simp
  have falseOut : circuitFun 9 C (fun _ => false) = false := by
    rw [computes]
    rfl
  have trueOut : circuitFun 9 C (fun _ => true) = true := by
    rw [computes]
    rfl
  have shapeLast := shape 14 (by omega)
  dsimp only at shapeLast
  rw [lastEq] at shapeLast
  rcases shapeLast with h | ⟨a, _, h⟩ | ⟨a, b, ha, hb, _, h | h⟩
  · rw [val, h] at falseOut
    contradiction
  · have zero : gs.countP (fun g => g.op.eval [false]) = 0 := by
      rw [h] at countSum
      change gs.countP (fun g => g.op.eval [false]) + 1 = 1 at countSum
      omega
    have good : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
      intro g hg
      have opt : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        simpa using (fan g hg).1
      have hn := List.countP_eq_zero.mp zero g hg
      rcases opt with ha | ho | hnot
      · simp [ha]
      · simp [ho]
      · simp [hnot, andEval, orEval, notEval] at hn
    have startOrd (i : Nat) :
        (start (fun _ => false)).getD i false = true →
        (start (fun _ => true)).getD i false = true := by
      intro e
      have hlen : (start (fun _ => false)).length = 10 := by simp [start]
      by_cases hi : i < (start (fun _ => false)).length
      · have hm : ∀ b : Bool, start (fun _ => b) = List.replicate 10 b := by decide
        rw [hm] at e
        rw [List.getD_replicate false (show i < 10 by omega)] at e
        contradiction
      · rw [List.getD_eq_default _ _ (by omega)] at e
        contradiction
    have mono := monotoneFold gs good (start (fun _ => false)) (start (fun _ => true))
      (by simp [start]) startOrd a
    rw [val, h] at falseOut trueOut
    change (!((D.wires (start (fun _ => false))).getD a false)) = false at falseOut
    change (!((D.wires (start (fun _ => true))).getD a false)) = true at trueOut
    have low : (D.wires (start (fun _ => false))).getD a false = true := by simpa using falseOut
    have contra := mono low
    change (D.wires (start (fun _ => true))).getD a false = true at contra
    rw [contra] at trueOut
    contradiction
  · have ha' : a ≤ 24 := by rcases ha with ha | ha <;> omega
    have hb' : b ≤ 24 := by rcases hb with hb | hb <;> omega
    obtain ⟨x, hx⟩ := andCase gs a b gsLength fan few ha' hb'
    apply hx
    have e := congrFun computes x
    rw [val, h] at e
    simpa [andEval, orEval, notEval, D, start] using e
  · have ha' : a ≤ 24 := by rcases ha with ha | ha <;> omega
    have hb' : b ≤ 24 := by rcases hb with hb | hb <;> omega
    obtain ⟨x, hx⟩ := orCase gs a b gsLength fan few ha' hb'
    apply hx
    have e := congrFun computes x
    rw [val, h] at e
    simpa [andEval, orEval, notEval, D, start] using e
