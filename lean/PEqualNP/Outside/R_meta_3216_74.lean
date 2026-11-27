import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3216_74
    (normalize : ∀ (C : Circuit), FanInTwo C →
    (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
    12 + (C.gates.filter (fun g => [0,9].any g.inputs.contains)).length = C.size →
    let f := fun y : Fin 8 → Bool => C.eval (false :: List.ofFn y ++ [true])
    (∃ x y, f x ≠ f y) → ¬ HasCircuitSize 8 f 11 →
    ∃ S : Set ℕ, C.output ∈ S ∧ 0 ∉ S ∧ 9 ∉ S ∧
      ∀ (p : List Gate) (g : Gate) (t : List Gate), C.gates = p ++ g :: t →
        if [0,9].any g.inputs.contains then
          10+p.length ∈ S → ∃ k ∈ S,
            (g.op = .or ∧ (g.inputs = [0,k] ∨ g.inputs = [k,0])) ∨
            (g.op = .and ∧ (g.inputs = [9,k] ∨ g.inputs = [k,9]))
        else 10+p.length ∈ S ∧ ∀ k ∈ g.inputs, k ∈ S)
    (lower : ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => ([1,10,19,5,14,23,38,47,60] : List ℕ).any
    (fun e => y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8)))) 11)
    (residual : ∀ (C : Circuit) (S : Set ℕ), FanInTwo C → C.size = 14 →
    (C.gates.filter (fun g => [0,9].any g.inputs.contains)).length = 2 →
    (C.gates.filter (fun g => !([0,9].any g.inputs.contains) && g.inputs.contains 4)).length ≤ 1 →
    (C.output ∈ S ∧ 0 ∉ S ∧ 9 ∉ S ∧
      ∀ (p : List Gate) (g : Gate) (t : List Gate), C.gates = p ++ g :: t →
        if [0,9].any g.inputs.contains then
          10+p.length ∈ S → ∃ k ∈ S,
            (g.op = .or ∧ (g.inputs = [0,k] ∨ g.inputs = [k,0])) ∨
            (g.op = .and ∧ (g.inputs = [9,k] ∨ g.inputs = [k,9]))
        else 10+p.length ∈ S ∧ ∀ k ∈ g.inputs, k ∈ S) →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10)))) x) :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (∀ (x15 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x15 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x16 : ℕ) => x15 (Fin.ofNat (8 : ℕ) (x16 / (8 : ℕ))) && x15 (Fin.ofNat (8 : ℕ) (x16 % (8 : ℕ)))) → ∃ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x16 ++ [Bool.false]) ≠ (x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ)) || x16 (4 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (2 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (6 : Fin (8 : ℕ)) || x16 (2 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)) || x16 (5 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ))) := by
  intro P Q R a b o
  let C : Circuit := ⟨P ++ a :: (Q ++ b :: R),o⟩
  change FanInTwo C → _
  intro fan len _ norm clean few hits lowEval
  let rd := fun g : Gate => [0,9].any g.inputs.contains
  have marked (g : Gate) (hg : g ∈ [a,b]) : rd g = true := by
    rcases hits g hg with h | h <;> simp [rd,h]
  have ha := marked a (by simp)
  have hb := marked b (by simp)
  have sz : C.size = 14 := by
    change (P ++ a :: (Q ++ b :: R)).length = 14
    simp only [List.length_append,List.length_cons]
    omega
  have unm (g : Gate) (hg : g ∈ P ++ Q ++ R) : rd g = false := by
    obtain ⟨h0,h9⟩ := clean g hg
    simp [rd,h0,h9]
  have z (L : List Gate) (inc : ∀ g ∈ L, g ∈ P ++ Q ++ R) : L.filter rd = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro g hg
    simp [unm g (inc g hg)]
  have zp := z P (by intro g h; simp [h])
  have zq := z Q (by intro g h; simp [h])
  have zr := z R (by intro g h; simp [h])
  have nr : (C.gates.filter rd).length = 2 := by simp [C,List.filter_append,ha,hb,zp,zq,zr]
  let sparse := fun g : Gate => !rd g && g.inputs.contains 4
  have sf (L : List Gate) (inc : ∀ g ∈ L, g ∈ P ++ Q ++ R) :
      L.filter sparse = L.filter (fun g => g.inputs.contains 4) := by
    exact List.filter_congr (by intro g hg; simp [sparse,unm g (inc g hg)])
  have sp := sf P (by intro g h; simp [h])
  have sq := sf Q (by intro g h; simp [h])
  have sr := sf R (by intro g h; simp [h])
  have noneA : sparse a = false := by simp [sparse,ha]
  have noneB : sparse b = false := by simp [sparse,hb]
  have filterBound : (C.gates.filter sparse).length ≤ 1 := by
    have eq : (C.gates.filter sparse).length = ((P ++ Q ++ R).filter (fun g => g.inputs.contains 4)).length := by
      simp [C,List.filter_append,noneA,noneB,sp,sq,sr]
    exact eq.trans_le few
  let f : (Fin 8 → Bool) → Bool := (fun y : Fin 8 → Bool => ([1,10,19,5,14,23,38,47,60] : List ℕ).any
    (fun e => y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))))
  let G : (Fin 9 → Bool) → Bool := (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10))))
  have hl (y : Fin 8 → Bool) : C.eval (false :: List.ofFn y ++ [true]) = f y := lowEval y
  have hn : ∃ y z : Fin 8 → Bool, C.eval (false :: List.ofFn y ++ [true]) ≠
      C.eval (false :: List.ofFn z ++ [true]) := by
    refine ⟨fun _ => true,fun _ => false,?_⟩
    rw [hl,hl]
    decide +kernel
  have hardC : ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool =>
      C.eval (false :: List.ofFn y ++ [true])) 11 := by
    rw [show (fun y : Fin 8 → Bool => C.eval (false :: List.ofFn y ++ [true])) = f from funext hl]
    exact lower
  obtain ⟨S,hs⟩ := normalize C fan (fun g hg => (norm g hg).1)
    (show 12 + (C.gates.filter rd).length = C.size by omega) hn hardC
  obtain ⟨x,hx⟩ := residual C S fan sz nr filterBound hs
  by_contra! high
  apply hx
  change C.eval (List.ofFn x ++ [!x 0]) = G x
  let y := Fin.tail x
  have eta : Fin.cons (x 0) y = x := Fin.cons_self_tail x
  have rows : List.ofFn x = x 0 :: List.ofFn y := by
    conv_lhs => rw [← eta, List.ofFn_succ]
    simp [y,Fin.cons_succ]
  rw [rows]
  have table0 : ∀ u : Fin 8 → Bool, f u = G (Fin.cons false u) := by decide +kernel
  have table1 : ∀ u : Fin 8 → Bool, (u 0 || u 3 || u 4 || u 1 && u 2 || u 1 && u 6 ||
      u 2 && u 7 || u 5 && u 7) = G (Fin.cons true u) := by decide +kernel
  cases h : x 0
  · change C.eval (false :: List.ofFn y ++ [true]) = G x
    calc
      _ = G (Fin.cons false y) := (hl y).trans (table0 y)
      _ = G x := congrArg G (by simpa only [h] using eta)
  · change C.eval (true :: List.ofFn y ++ [false]) = G x
    calc
      _ = G (Fin.cons true y) := (high y).trans (table1 y)
      _ = G x := congrArg G (by simpa only [h] using eta)
