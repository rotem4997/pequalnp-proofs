import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3022_42
    (hoist : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates = pre ++ g :: post → PEqualNP.MetaComplexity.FanInTwo C →
      (∀ i ∈ g.inputs, i < 9) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧
        PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C ∧
        ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
    (firstAnd : ∀ a b : Fin 9, a ≠ b → ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (remaining : ∀ args : List (Fin 11), args.length ≤ 2 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ a b : Fin 9, a ≠ b → g.inputs ≠ [a.val,b.val]) →
      ∃ x : Fin 9 → Bool,
        C.eval ((List.ofFn x ++ [x 0 || x 2]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.or.eval (args.map fun i =>
            (List.ofFn x ++ [x 0 || x 2]).getD i.val false)]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro args arity C fan small
  by_cases noRaw : ∀ g ∈ C.gates, g.op = GateOp.and →
      ∀ a b : Fin 9, a ≠ b → g.inputs ≠ [a.val,b.val]
  · exact remaining args arity C fan small noRaw
  push Not at noRaw
  obtain ⟨g,hg,hop,a,b,ne,hab⟩ := noRaw
  by_contra! correct
  let g0 : Gate := ⟨.or,[0,2]⟩
  let g1 : Gate := ⟨.or,args.map Fin.val⟩
  let T : Circuit := ⟨g0::g1::C.gates,C.output⟩
  have tfan : FanInTwo T := by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · subst q;simp [g0]
    rcases List.mem_cons.mp hq with he | hq
    · subst q;simpa [g1] using arity
    · exact fan q hq
  have first (x : Fin 9 → Bool) :
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
    change (x 0 || (x 2 || false)) = _
    simp
  have computes : circuitFun 9 T = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    change C.eval ((List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]) ++
      [g1.op.eval (g1.inputs.map fun i => (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false)]) = _
    rw [first]
    simpa only [g1,List.map_map,Function.comp_def] using Classical.not_not.mp (correct x)
  obtain ⟨pre,post,hshape⟩ := List.mem_iff_append.mp hg
  have tshape : T.gates = (g0::g1::pre) ++ g :: post := by simp only [T,hshape,List.cons_append]
  obtain ⟨D,dfan,dsz,dfun,dwire⟩ := hoist T (g0::g1::pre) post g tshape tfan (by
    intro i hi
    simp only [hab,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact a.isLt
    · exact b.isLt)
  have dfirst (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x a && x b) := by
    rw [dwire]
    rw [hop,hab]
    change ((List.ofFn x).getD a.val false && ((List.ofFn x).getD b.val false && true)) = _
    simp only [List.getD,List.getElem?_ofFn,a.isLt,b.isLt,Bool.and_true]
    simp
  have bound := firstAnd a b ne D dfan dfirst (dfun.trans computes)
  have tsz : T.size = C.size + 2 := by rfl
  omega
