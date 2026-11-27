import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5152_801
  (canon : ∀ (C : Circuit) (s : Bool) (k : ℕ),
    let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let rd := fun (w : ℕ) (g : Gate) => w ∈ g.inputs ∧ (g.op = .not → g.inputs.head? = some w)
    let cap := fun (D : Circuit) => ∀ (v : Fin 10) (S : Finset ℕ),
      (∀ j ∈ S, ∃ g : Gate, D.gates[j]? = some g ∧ rd v.val g) → S.card ≤ k
    let special := fun (D : Circuit) (j : ℕ) => ∀ (i : ℕ) (g : Gate),
      D.gates[i]? = some g → rd 0 g → i = j ∧
        (g.op = .not ∨ ∀ w ∈ g.inputs, w < 10 → w = 0)
    FanInTwo C → C.size ≤ 18 → cap C →
    (∀ x, (if s then !circuitFun 10 C x else circuitFun 10 C x) = F x) →
    ∃ (D : Circuit) (j : ℕ), FanInTwo D ∧ D.size ≤ C.size ∧ cap D ∧
      circuitFun 10 D = circuitFun 10 C ∧ special D j)
  (core : ∀ (C : Circuit) (s : Bool) (j : ℕ),
    let k := if s then 3 else 2
    let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let rd := fun (w : ℕ) (g : Gate) => w ∈ g.inputs ∧ (g.op = .not → g.inputs.head? = some w)
    let cap := fun (D : Circuit) => ∀ (v : Fin 10) (S : Finset ℕ),
      (∀ j ∈ S, ∃ g : Gate, D.gates[j]? = some g ∧ rd v.val g) → S.card ≤ k
    let special := fun (D : Circuit) (j : ℕ) => ∀ (i : ℕ) (g : Gate),
      D.gates[i]? = some g → rd 0 g → i = j ∧
        (g.op = .not ∨ ∀ w ∈ g.inputs, w < 10 → w = 0)
    FanInTwo C → C.size ≤ 18 → cap C → special C j →
    ∃ x, (if s then !circuitFun 10 C x else circuitFun 10 C x) ≠ F x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         (∀ (x8 : Fin (10 : ℕ)) (x9 : Finset ℕ), (∀ x10 ∈ x9, ∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), (x1 :: x2.gates)[x10]? = Option.some x12 ∧ ↑x8 ∈ x12.inputs ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.not → x12.inputs.head? = Option.some ↑x8)) → x9.card ≤ if x4 = Bool.true then (3 : ℕ) else (2 : ℕ)) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11 := by
  intro g E u s hg hE hs cap
  let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  let C : Circuit := ⟨g :: E.gates,u⟩
  let k : ℕ := if s then 3 else 2
  have fan : FanInTwo C := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | he
    · exact hg _ (List.mem_singleton_self _)
    · exact hE _ he
  have size : C.size ≤ 18 := by
    change (g :: E.gates).length ≤ 18
    change E.gates.length ≤ 17 at hs
    rw [List.length_cons]
    omega
  have target (x : Fin 10 → Bool) : F x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    simp only [F, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  change ∃ x : Fin 10 → Bool, (if s then !circuitFun 10 C x else circuitFun 10 C x) ≠ _
  by_contra! h
  have computes (x : Fin 10 → Bool) : (if s then !circuitFun 10 C x else circuitFun 10 C x) = F x := by
    rw [target]; exact h x
  obtain ⟨D,j,hD,hz,capD,eqD,atZero⟩ := canon C s k fan size cap computes
  obtain ⟨x,bad⟩ := core D s j hD (hz.trans size) capD atZero
  exact bad (eqD ▸ computes x)
