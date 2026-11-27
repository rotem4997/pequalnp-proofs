import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.PathPair607

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Table := BitVec 9
private def sample (j : Fin 9) (i : Fin 4) : Bool :=
  ([3, 5, 6, 9, 10, 11, 12, 13, 14] : List Nat)[j.val]!.testBit i.val

private def readTable (j : Fin 9) (t : Table) : Bool := t.getLsbD j.val
private theorem read_zero (j : Fin 9) : readTable j 0 = false := BitVec.getLsbD_zero
private theorem read_not (j : Fin 9) (t : Table) : readTable j (~~~t) = !(readTable j t) := by
  simp [readTable, j.isLt]
private def inputs : List Table := [171, 309, 454, 504]
private theorem inputTables (j : Fin 9) : List.ofFn (sample j) = inputs.map (readTable j) := by
  fin_cases j <;> decide
private theorem table_ext (a b : Table) (h : ∀ j, readTable j a = readTable j b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i,hi⟩

private theorem getD_table (x : Fin 9) (ws : List Table) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

private def gateTable (ws : List Table) (g : Gate) : Table :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateTable (x : Fin 9) (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireTables (gs : List Gate) (ws : List Table) : List Table :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

private theorem read_wireTables (x : Fin 9) (gs : List Gate) (ws : List Table)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private theorem wires_match (C : Circuit) (h : FanInTwo C) (j : Fin 9) (o : ℕ) :
    (C.wires (List.ofFn (sample j))).getD o false =
    readTable j ((wireTables C.gates inputs).getD o 0) := by
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (sample j))).getD o false = _
  rw [inputTables, read_wireTables j C.gates inputs h, getD_table]

private def pathA (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
private def pathB (x : Fin 4 → Bool) : Bool := (x 1 && x 3) || (x 3 && x 0) || (x 0 && x 2)
private def F : Table := 485
private def G : Table := 442
private lemma sampleA (j : Fin 9) : pathA (sample j) = readTable j F := by fin_cases j <;> decide
private lemma sampleB (j : Fin 9) : pathB (sample j) = readTable j G := by fin_cases j <;> decide

private lemma tables_present (C : Circuit) (h : FanInTwo C) (o p : Nat)
    (computed : ∀ x, (C.wires (List.ofFn x)).getD o false = pathA x ∧
      (C.wires (List.ofFn x)).getD p false = pathB x) :
    (wireTables C.gates inputs).getD o 0 = F ∧ (wireTables C.gates inputs).getD p 0 = G :=
  ⟨table_ext _ _ (fun j => (wires_match C h j o).symm.trans ((computed _).1.trans (sampleA j))),
   table_ext _ _ (fun j => (wires_match C h j p).symm.trans ((computed _).2.trans (sampleB j)))⟩

private def eight : Circuit :=
  ⟨[⟨.or,[0,2]⟩,⟨.and,[4,1]⟩,⟨.and,[2,3]⟩,⟨.or,[5,6]⟩,
    ⟨.or,[1,0]⟩,⟨.and,[8,3]⟩,⟨.and,[0,2]⟩,⟨.or,[9,10]⟩], 11⟩

private lemma upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∃ o p : Nat,
    ∀ x, (C.wires (List.ofFn x)).getD o false = pathA x ∧
      (C.wires (List.ofFn x)).getD p false = pathB x := by
  refine ⟨eight, ?_, by decide, 7, 11, ?_⟩
  · intro g hg
    simp only [eight, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl), by decide⟩
  · intro x
    rw [show List.ofFn x = [x 0,x 1,x 2,x 3] from rfl]
    unfold pathA pathB
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

end PEqualNP.Outside.PathPair607

namespace PEqualNP.Outside.PathPair607.Search
-- Each bit records a circuit value on one of the nine sampled assignments.
private abbrev A : Nat := 485
private abbrev B : Nat := 442
private def bit (v : Nat) := 1 <<< v
-- The lookup tables mark the partners of each wire that give one of the target outputs.
-- The finite calculation below checks their entries against conjunction and disjunction.
private def va : Nat → Nat
  | 0 => 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 1 => 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 4 => 0x22000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 5 => 0x33000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 32 => 0x20000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 33 => 0x30000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 36 => 0x22000000220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 37 => 0x33000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 64 => 0x20000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 65 => 0x30000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 68 => 0x22000000000000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 69 => 0x33000000000000003300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 96 => 0x20000000200000002000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 97 => 0x30000000300000003000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 100 => 0x22000000220000002200000022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 101 => 0x33000000330000003300000033000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 128 => 0x20000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 129 => 0x30000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 132 => 0x22000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 133 => 0x33000000000000000000000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 160 => 0x20000000200000000000000000000000200000002000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 161 => 0x30000000300000000000000000000000300000003000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 164 => 0x22000000220000000000000000000000220000002200000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 165 => 0x33000000330000000000000000000000330000003300000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 192 => 0x20000000000000002000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000
  | 193 => 0x30000000000000003000000000000000300000000000000030000000000000000000000000000000000000000000000000000000000000000000000000
  | 196 => 0x22000000000000002200000000000000220000000000000022000000000000000000000000000000000000000000000000000000000000000000000000
  | 197 => 0x33000000000000003300000000000000330000000000000033000000000000000000000000000000000000000000000000000000000000000000000000
  | 224 => 0x20000000200000002000000020000000200000002000000020000000200000000000000000000000000000000000000000000000000000000000000000
  | 225 => 0x30000000300000003000000030000000300000003000000030000000300000000000000000000000000000000000000000000000000000000000000000
  | 228 => 0x22000000220000002200000022000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000000000
  | 229 => 0x33000000330000003300000033000000330000003300000033000000330000000000000000000000000000000000000000000000000000000000000000
  | 256 => 0x20000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000
  | 257 => 0x30000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000
  | 260 => 0x22000000000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000
  | 261 => 0x33000000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000000000000000000000000000
  | 288 => 0x20000000200000000000000000000000000000000000000000000000000000002000000020000000000000000000000000000000000000000000000000
  | 289 => 0x30000000300000000000000000000000000000000000000000000000000000003000000030000000000000000000000000000000000000000000000000
  | 292 => 0x22000000220000000000000000000000000000000000000000000000000000002200000022000000000000000000000000000000000000000000000000
  | 293 => 0x33000000330000000000000000000000000000000000000000000000000000003300000033000000000000000000000000000000000000000000000000
  | 320 => 0x20000000000000002000000000000000000000000000000000000000000000002000000000000000200000000000000000000000000000000000000000
  | 321 => 0x30000000000000003000000000000000000000000000000000000000000000003000000000000000300000000000000000000000000000000000000000
  | 324 => 0x22000000000000002200000000000000000000000000000000000000000000002200000000000000220000000000000000000000000000000000000000
  | 325 => 0x33000000000000003300000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000
  | 352 => 0x20000000200000002000000020000000000000000000000000000000000000002000000020000000200000002000000000000000000000000000000000
  | 353 => 0x30000000300000003000000030000000000000000000000000000000000000003000000030000000300000003000000000000000000000000000000000
  | 356 => 0x22000000220000002200000022000000000000000000000000000000000000002200000022000000220000002200000000000000000000000000000000
  | 357 => 0x33000000330000003300000033000000000000000000000000000000000000003300000033000000330000003300000000000000000000000000000000
  | 384 => 0x20000000000000000000000000000000200000000000000000000000000000002000000000000000000000000000000020000000000000000000000000
  | 385 => 0x30000000000000000000000000000000300000000000000000000000000000003000000000000000000000000000000030000000000000000000000000
  | 388 => 0x22000000000000000000000000000000220000000000000000000000000000002200000000000000000000000000000022000000000000000000000000
  | 389 => 0x33000000000000000000000000000000330000000000000000000000000000003300000000000000000000000000000033000000000000000000000000
  | 416 => 0x20000000200000000000000000000000200000002000000000000000000000002000000020000000000000000000000020000000200000000000000000
  | 417 => 0x30000000300000000000000000000000300000003000000000000000000000003000000030000000000000000000000030000000300000000000000000
  | 420 => 0x22000000220000000000000000000000220000002200000000000000000000002200000022000000000000000000000022000000220000000000000000
  | 421 => 0x33000000330000000000000000000000330000003300000000000000000000003300000033000000000000000000000033000000330000000000000000
  | 448 => 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000
  | 449 => 0x30000000000000003000000000000000300000000000000030000000000000003000000000000000300000000000000030000000000000003000000000
  | 452 => 0x22000000000000002200000000000000220000000000000022000000000000002200000000000000220000000000000022000000000000002200000000
  | 453 => 0x33000000000000003300000000000000330000000000000033000000000000003300000000000000330000000000000033000000000000003300000000
  | 480 => 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020
  | 481 => 0x30000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030
  | 484 => 0x22000000220000002200000022000000220000002200000022000000220000002200000022000000220000002200000022000000220000002200000022
  | 485 => 0xa0a0a0b3000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033
  | 487 => 0x20202020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 493 => 0xa000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 495 => 0x200020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 501 => 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 503 => 0x2020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 509 => 0xa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 511 => 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0
private def vb : Nat → Nat
  | 0 => 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 2 => 0x500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 8 => 0x404000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 10 => 0x505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 16 => 0x400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 18 => 0x500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 24 => 0x404040400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 26 => 0x505050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 32 => 0x400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 34 => 0x500000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 40 => 0x404000004040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 42 => 0x505000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 48 => 0x400040004000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 50 => 0x500050005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 56 => 0x404040404040404000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 58 => 0x505050505050505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 128 => 0x400000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 130 => 0x500000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 136 => 0x404000000000000000000000000000004040000000000000000000000000000000000000000000000000000000000000000000000000000
  | 138 => 0x505000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000
  | 144 => 0x400040000000000000000000000000004000400000000000000000000000000000000000000000000000000000000000000000000000000
  | 146 => 0x500050000000000000000000000000005000500000000000000000000000000000000000000000000000000000000000000000000000000
  | 152 => 0x404040400000000000000000000000004040404000000000000000000000000000000000000000000000000000000000000000000000000
  | 154 => 0x505050500000000000000000000000005050505000000000000000000000000000000000000000000000000000000000000000000000000
  | 160 => 0x400000004000000000000000000000004000000040000000000000000000000000000000000000000000000000000000000000000000000
  | 162 => 0x500000005000000000000000000000005000000050000000000000000000000000000000000000000000000000000000000000000000000
  | 168 => 0x404000004040000000000000000000004040000040400000000000000000000000000000000000000000000000000000000000000000000
  | 170 => 0x505000005050000000000000000000005050000050500000000000000000000000000000000000000000000000000000000000000000000
  | 176 => 0x400040004000400000000000000000004000400040004000000000000000000000000000000000000000000000000000000000000000000
  | 178 => 0x500050005000500000000000000000005000500050005000000000000000000000000000000000000000000000000000000000000000000
  | 184 => 0x404040404040404000000000000000004040404040404040000000000000000000000000000000000000000000000000000000000000000
  | 186 => 0x505050505050505000000000000000005050505050505050000000000000000000000000000000000000000000000000000000000000000
  | 256 => 0x400000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000
  | 258 => 0x500000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000
  | 264 => 0x404000000000000000000000000000000000000000000000000000000000000040400000000000000000000000000000000000000000000
  | 266 => 0x505000000000000000000000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000
  | 272 => 0x400040000000000000000000000000000000000000000000000000000000000040004000000000000000000000000000000000000000000
  | 274 => 0x500050000000000000000000000000000000000000000000000000000000000050005000000000000000000000000000000000000000000
  | 280 => 0x404040400000000000000000000000000000000000000000000000000000000040404040000000000000000000000000000000000000000
  | 282 => 0x505050500000000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000
  | 288 => 0x400000004000000000000000000000000000000000000000000000000000000040000000400000000000000000000000000000000000000
  | 290 => 0x500000005000000000000000000000000000000000000000000000000000000050000000500000000000000000000000000000000000000
  | 296 => 0x404000004040000000000000000000000000000000000000000000000000000040400000404000000000000000000000000000000000000
  | 298 => 0x505000005050000000000000000000000000000000000000000000000000000050500000505000000000000000000000000000000000000
  | 304 => 0x400040004000400000000000000000000000000000000000000000000000000040004000400040000000000000000000000000000000000
  | 306 => 0x500050005000500000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000
  | 312 => 0x404040404040404000000000000000000000000000000000000000000000000040404040404040400000000000000000000000000000000
  | 314 => 0x505050505050505000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000
  | 384 => 0x400000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000400000000000000
  | 386 => 0x500000000000000000000000000000005000000000000000000000000000000050000000000000000000000000000000500000000000000
  | 392 => 0x404000000000000000000000000000004040000000000000000000000000000040400000000000000000000000000000404000000000000
  | 394 => 0x505000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000505000000000000
  | 400 => 0x400040000000000000000000000000004000400000000000000000000000000040004000000000000000000000000000400040000000000
  | 402 => 0x500050000000000000000000000000005000500000000000000000000000000050005000000000000000000000000000500050000000000
  | 408 => 0x404040400000000000000000000000004040404000000000000000000000000040404040000000000000000000000000404040400000000
  | 410 => 0x505050500000000000000000000000005050505000000000000000000000000050505050000000000000000000000000505050500000000
  | 416 => 0x400000004000000000000000000000004000000040000000000000000000000040000000400000000000000000000000400000004000000
  | 418 => 0x500000005000000000000000000000005000000050000000000000000000000050000000500000000000000000000000500000005000000
  | 424 => 0x404000004040000000000000000000004040000040400000000000000000000040400000404000000000000000000000404000004040000
  | 426 => 0x505000005050000000000000000000005050000050500000000000000000000050500000505000000000000000000000505000005050000
  | 432 => 0x400040004000400000000000000000004000400040004000000000000000000040004000400040000000000000000000400040004000400
  | 434 => 0x500050005000500000000000000000005000500050005000000000000000000050005000500050000000000000000000500050005000500
  | 440 => 0x404040404040404000000000000000004040404040404040000000000000000040404040404040400000000000000000404040404040404
  | 442 => 0xcc00000000000000cd05050505050505000000000000000005050505050505050000000000000000050505050505050500000000000000000505050505050505
  | 443 => 0x44000000000000004400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 446 => 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 447 => 0x4000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 506 => 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 507 => 0x4400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 510 => 0xc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 511 => 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0

private def grow (L : List Nat) (v : Nat) (p : Nat) : Nat :=
  L.foldl (fun acc w => acc ||| bit (w &&& v) ||| bit (w ||| v)) (p ||| bit v ||| bit (511 ^^^ v))
private def base := [171,309,454,504]
private def gen : List Nat → List Nat
  | [] => []
  | v :: vs => (511 ^^^ v) :: ((vs.flatMap (fun w => [v &&& w,v ||| w])) ++ gen vs)
private def choices (L : List Nat) := (gen L).eraseDups.filter (fun v => v != 0 && v != 511 && !L.contains v)
private def pbase : Nat := (gen base ++ base ++ [0,511]).foldl (fun a v => a ||| bit v) 0
private def abase := base.foldl (fun a v => a ||| va v) (bit A ||| bit (511 ^^^ A))
private def bbase := base.foldl (fun a v => a ||| vb v) (bit B ||| bit (511 ^^^ B))
private def single (L : List Nat) (v : Nat) (p n t : Nat) (fn : Nat → Nat) : Bool :=
  let pp := grow L v p
  pp.testBit t || pp &&& (n ||| fn v) != 0
-- In the last three slots, two missing outputs leave room for at most one auxiliary wire.
private def finish (L : List Nat) (p a b : Nat) : Bool :=
  if L.contains A then
    p.testBit B || p &&& b != 0 || (choices L).any (fun v => single L v p b B vb)
  else if L.contains B then
    p.testBit A || p &&& a != 0 || (choices L).any (fun v => single L v p a A va)
  else
    p &&& a &&& b != 0 ||
    (p.testBit A && (p.testBit B || (grow L A p) &&& b != 0)) ||
    (p.testBit B && (p.testBit A || (grow L B p) &&& a != 0))
private def reach : Nat → List Nat → Nat → Nat → Nat → Bool
  | 0,L,p,a,b => finish L p a b
  | k+1,L,p,a,b => reach k L p a b || (choices L).any (fun v =>
     reach k (v :: L) (grow L v p) (a ||| va v) (b ||| vb v))
private def after (vals : List Nat) (k : Nat) : Bool :=
  let (L,p,a,b) := vals.foldl (fun (st : List Nat × Nat × Nat × Nat) v =>
    let (l,p,a,b) := st
    (v::l,grow l v p,a ||| va v,b ||| vb v)) (base,pbase,abase,bbase)
  reach k L p a b

private def Have (L : List Nat) (t : Nat) : Prop := t = 0 ∨ t = 511 ∨ t ∈ L
private def Can (L : List Nat) (t : Nat) : Prop := Have L t ∨ t ∈ gen L
private def Touch (L : List Nat) (t v : Nat) : Prop :=
  v = t ∨ (511 ^^^ v) = t ∨ ∃ w ∈ L, (v &&& w) = t ∨ (v ||| w) = t
private def Safe (L : List Nat) (p a b : Nat) : Prop :=
  (∀ t, Can L t → p.testBit t = true) ∧
  (∀ v < 512, Touch L A v → a.testBit v = true) ∧
  (∀ v < 512, Touch L B v → b.testBit v = true)
private def Valid : Nat → List Nat → Prop
  | 0,L => A ∈ L ∧ B ∈ L
  | n+1,L => Valid n L ∨ ∃ v ∈ choices L, v < 512 ∧ Valid n (v::L)
private def mRelevant (t w : Nat) : Bool := w &&& t == t || w ||| t == t

private def mEntry (t row w v : Nat) : Bool :=
  !((v &&& w == t) || (v ||| w == t)) || row.testBit v

private def mRow (t : Nat) (f : Nat → Nat) (w : Nat) : Bool :=
  !mRelevant t w || (List.range 512).all (mEntry t (f w) w)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem mTable :
    (List.range 512).all (fun w => mRow A va w && mRow B vb w) = true := by decide +kernel

private theorem mRow_sound {t w v : Nat} {f : Nat → Nat} (hr : mRow t f w = true)
    (hv : v < 512) (hh : v &&& w = t ∨ v ||| w = t) : (f w).testBit v = true := by
  have rel : mRelevant t w = true := by
    unfold mRelevant
    rcases hh with h | h
    · apply Bool.or_eq_true .. |>.mpr
      left
      apply beq_iff_eq.mpr
      rw [← h, Nat.and_comm v w, ← Nat.and_assoc, Nat.and_self]
    · apply Bool.or_eq_true .. |>.mpr
      right
      apply beq_iff_eq.mpr
      rw [← h, Nat.or_comm v w, ← Nat.or_assoc, Nat.or_self]
  have allOk : (List.range 512).all (mEntry t (f w) w) = true := by
    simpa [mRow, rel] using hr
  have pairOk := List.all_eq_true.mp allOk v (List.mem_range.mpr hv)
  rcases hh with h | h <;> simpa [mEntry, h] using pairOk

private theorem mRows {w : Nat} (hw : w < 512) : mRow A va w = true ∧ mRow B vb w = true := by
  have h := List.all_eq_true.mp mTable w (List.mem_range.mpr hw)
  simpa using h

private theorem mBit (v i : Nat) : (bit v).testBit i = true ↔ i = v := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow, eq_comm]

private theorem mFold (L : List Nat) (f : Nat → Nat) (p i : Nat) :
    (L.foldl (fun acc w => acc ||| f w) p).testBit i = true ↔
      p.testBit i = true ∨ ∃ w ∈ L, (f w).testBit i = true := by
  induction L generalizing p with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or]
    simp [or_assoc]

private theorem mGrow (L : List Nat) (v p i : Nat) :
    (grow L v p).testBit i = true ↔ p.testBit i = true ∨ i = v ∨ i = 511 ^^^ v ∨
      ∃ w ∈ L, i = w &&& v ∨ i = w ||| v := by
  unfold grow
  simp_rw [Nat.or_assoc]
  rw [mFold]
  simp [Nat.testBit_or, mBit, or_assoc]

private theorem mTouchInit {L : List Nat} {f : Nat → Nat} {t i : Nat} (hv : i < 512)
    (hr : ∀ w ∈ L, mRow t f w = true) (ht : Touch L t i) :
    (L.foldl (fun b w => b ||| f w) (bit t ||| bit (511 ^^^ t))).testBit i = true := by
  rw [mFold, Nat.testBit_or, Bool.or_eq_true, mBit, mBit]
  rcases ht with h | h | ⟨w, hw, hh⟩
  · exact Or.inl (Or.inl h)
  · left
    right
    rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · exact Or.inr ⟨w, hw, mRow_sound (hr w hw) hv hh⟩

private theorem mTouchCons {L : List Nat} {f : Nat → Nat} {t w i z : Nat}
    (hr : mRow t f w = true) (hv : i < 512)
    (ho : Touch L t i → z.testBit i = true) (ht : Touch (w :: L) t i) :
    (z ||| f w).testBit i = true := by
  rw [Nat.testBit_or, Bool.or_eq_true]
  rcases ht with h | h | ⟨x, hx, hh⟩
  · exact Or.inl (ho (Or.inl h))
  · exact Or.inl (ho (Or.inr (Or.inl h)))
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inr (mRow_sound hr hv hh)
    · exact Or.inl (ho (Or.inr (Or.inr ⟨x, hx, hh⟩)))

private theorem safe_base : Safe base pbase abase bbase := by
  have hb : ∀ w ∈ base, w < 512 := by simp [base]
  refine ⟨?_, fun i hi ht => mTouchInit hi (fun w hw => (mRows (hb w hw)).1) ht,
      fun i hi ht => mTouchInit hi (fun w hw => (mRows (hb w hw)).2) ht⟩
  intro i hi
  apply (mFold _ bit _ _).mpr
  right
  refine ⟨i, ?_, (mBit i i).mpr rfl⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hi with (h | h | h) | h <;> tauto

private theorem safe_add {L : List Nat} {p a b v : Nat} (hs : Safe L p a b) (hv : v < 512)
    (_hb : ∀ w ∈ L, w < 512) : Safe (v :: L) (grow L v p) (a ||| va v) (b ||| vb v) := by
  refine ⟨?_, fun i hi ht => mTouchCons (mRows hv).1 hi (hs.2.1 i hi) ht,
      fun i hi ht => mTouchCons (mRows hv).2 hi (hs.2.2 i hi) ht⟩
  intro i hi
  apply (mGrow L v p i).mpr
  rcases hi with (h | h | h) | h
  · exact Or.inl (hs.1 i (Or.inl (Or.inl h)))
  · exact Or.inl (hs.1 i (Or.inl (Or.inr (Or.inl h))))
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hs.1 i (Or.inl (Or.inr (Or.inr h))))
  · simp only [gen, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
        or_false] at h
    rcases h with h | ⟨w, hw, hh⟩ | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨w, hw,
          by simpa [Nat.and_comm, Nat.or_comm] using hh⟩))
    · exact Or.inl (hs.1 i (Or.inr h))

private lemma selected {L : List Nat} {v : Nat} (h : v ∈ choices L) : Can L v := by
  exact Or.inr (List.mem_eraseDups.mp (List.mem_filter.mp h).1)

private lemma held {L : List Nat} {v : Nat} (h : v ∈ L) : Can L v :=
  Or.inl (Or.inr (Or.inr h))

private lemma oldCan {L : List Nat} {t : Nat} (v : Nat) (h : Can L t) : Can (v::L) t := by
  rcases h with (h | h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact held (List.mem_cons_of_mem _ h)
  · exact Or.inr (by simp [gen, h])

private lemma splitCan {L : List Nat} {v t : Nat} (h : Can (v::L) t) :
    Can L t ∨ Touch L t v := by
  rcases h with (h | h | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl (held h)
  · simp only [gen, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false] at h
    rcases h with h | ⟨w, hw, hh | hh⟩ | h
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr ⟨w,hw,Or.inl hh.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨w,hw,Or.inr hh.symm⟩))
    · exact Or.inl (Or.inr h)

private lemma noTouch {L : List Nat} {a b i j : Nat}
    (hn : a ≠ b) (hc : (511 ^^^ a) ≠ b)
    (hai : a.testBit i = false) (hbi : b.testBit i = true)
    (haj : a.testBit j = true) (hbj : b.testBit j = false) : ¬ Touch L b a := by
  rintro (h | h | ⟨w, _, h | h⟩)
  · exact hn h
  · exact hc h
  · have q := congrArg (fun z : Nat => z.testBit i) h
    simp [Nat.testBit_and,hai,hbi] at q
  · have q := congrArg (fun z : Nat => z.testBit j) h
    simp [Nat.testBit_or,haj,hbj] at q

private lemma dropA {L : List Nat} (h : Can (A::L) B) : Can L B :=
  (splitCan h).resolve_right (noTouch (i:=1) (j:=0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide))
private lemma dropB {L : List Nat} (h : Can (B::L) A) : Can L A :=
  (splitCan h).resolve_right (noTouch (i:=0) (j:=1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide))

private lemma validOne {L : List Nat} (h : Valid 1 L) :
    (A ∈ L ∧ Can L B) ∨ (B ∈ L ∧ Can L A) := by
  rcases h with ⟨ha,hb⟩ | ⟨v,hv,_,ha,hb⟩
  · exact Or.inl ⟨ha, held hb⟩
  · rcases List.mem_cons.mp ha with ha | ha
    · subst v
      exact Or.inr ⟨(List.mem_cons.mp hb).resolve_left (by decide), selected hv⟩
    · rcases List.mem_cons.mp hb with hb | hb
      · exact Or.inl ⟨ha,hb.symm ▸ selected hv⟩
      · exact Or.inl ⟨ha,held hb⟩

private def Near (L : List Nat) (t : Nat) : Prop :=
  Can L t ∨ ∃ v ∈ choices L, v < 512 ∧ Can (v::L) t

private lemma nearTwo {L : List Nat} (h : Valid 2 L) : Near L A ∧ Near L B := by
  have both {W : List Nat} (q : Valid 1 W) : Can W A ∧ Can W B := by
    rcases validOne q with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact ⟨held ha,hb⟩
    · exact ⟨ha,held hb⟩
  rcases h with h | ⟨v,hv,hlt,h⟩
  · exact ⟨Or.inl (both h).1,Or.inl (both h).2⟩
  · exact ⟨Or.inr ⟨v,hv,hlt,(both h).1⟩,Or.inr ⟨v,hv,hlt,(both h).2⟩⟩

private lemma freshTwo {L : List Nat} (ha : A ∉ L) (hb : B ∉ L) (h : Valid 2 L) :
    Can L A ∧ Can L B := by
  rcases h with h | ⟨v,hv,_,h⟩
  · rcases validOne h with h | h
    · exact (ha h.1).elim
    · exact (hb h.1).elim
  · rcases validOne h with ⟨hh,hg⟩ | ⟨hh,hg⟩
    · obtain rfl := (List.mem_cons.mp hh).resolve_right ha
      exact ⟨selected hv,dropA hg⟩
    · obtain rfl := (List.mem_cons.mp hh).resolve_right hb
      exact ⟨dropB hg,selected hv⟩

private lemma intersect {p n v : Nat} (hp : p.testBit v = true) (hn : n.testBit v = true) :
    p &&& n ≠ 0 := by
  intro q
  have h := congrArg (fun z : Nat => z.testBit v) q
  simp [Nat.testBit_and,hp,hn] at h

private lemma near_mask {L : List Nat} {t p n : Nat} (hp : ∀ w, Can L w → p.testBit w = true)
    (hn : ∀ w < 512, Touch L t w → n.testBit w = true) (h : Near L t) :
    Can L t ∨ p &&& n ≠ 0 := by
  rcases h with h | ⟨v,hv,hlt,h⟩
  · exact Or.inl h
  · rcases splitCan h with h | h
    · exact Or.inl h
    · exact Or.inr (intersect (hp v (selected hv)) (hn v hlt h))

private lemma near_bool {L : List Nat} {t p n : Nat} (hp : ∀ w, Can L w → p.testBit w = true)
    (hn : ∀ w < 512, Touch L t w → n.testBit w = true) (h : Near L t) :
    (p.testBit t || p &&& n != 0) = true := by
  rcases near_mask hp hn h with h | h
  · simp [hp t h]
  · simp [h]

private def StateExtension := ∀ {L : List Nat} {p a b v : Nat},
  Safe L p a b → v < 512 → (∀ w ∈ L, w < 512) →
    Safe (v::L) (grow L v p) (a ||| va v) (b ||| vb v)

private lemma finishProof (exts : StateExtension) {L : List Nat} {p a b : Nat}
    (hl : ∀ w ∈ L, w < 512) (safe : Safe L p a b) (h : Valid 3 L) :
    finish L p a b = true := by
  by_cases ha : A ∈ L
  · simp only [finish, List.contains_iff_mem.mpr ha, ite_true, Bool.or_eq_true,
      bne_iff_ne, List.any_eq_true]
    rcases h with h | ⟨v,hv,hlt,h⟩
    · exact Or.inl (by simpa only [Bool.or_eq_true,bne_iff_ne] using (near_bool safe.1 safe.2.2 (nearTwo h).2))
    · have hs := exts safe hlt hl
      exact Or.inr ⟨v,hv,near_bool hs.1 hs.2.2 (nearTwo h).2⟩
  by_cases hb : B ∈ L
  · simp only [finish, show L.contains A = false by simpa using ha, Bool.false_eq_true, ite_false,
      List.contains_iff_mem.mpr hb, ite_true, Bool.or_eq_true,bne_iff_ne,List.any_eq_true]
    rcases h with h | ⟨v,hv,hlt,h⟩
    · exact Or.inl (by simpa only [Bool.or_eq_true,bne_iff_ne] using (near_bool safe.1 safe.2.1 (nearTwo h).1))
    · have hs := exts safe hlt hl
      exact Or.inr ⟨v,hv,near_bool hs.1 hs.2.1 (nearTwo h).1⟩
  simp only [finish, show L.contains A = false by simpa using ha, show L.contains B = false by simpa using hb,
    Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne]
  have both (x : Can L A) (y : Can L B) :
      p.testBit A = true ∧ (p.testBit B = true ∨ grow L A p &&& b ≠ 0) :=
    ⟨safe.1 _ x,Or.inl (safe.1 _ y)⟩
  rcases h with h | ⟨v,hv,hlt,h⟩
  · obtain ⟨x,y⟩ := freshTwo ha hb h
    exact Or.inl (Or.inr (both x y))
  have hs := exts safe hlt hl
  by_cases hA : v = A
  · subst v
    rcases near_mask hs.1 hs.2.2 (nearTwo h).2 with h | z
    · exact Or.inl (Or.inr (both (selected hv) (dropA h)))
    · exact Or.inl (Or.inr ⟨safe.1 _ (selected hv), Or.inr (by
        simpa only [show vb A = 0 from by decide, Nat.or_zero] using z)⟩)
  by_cases hB : v = B
  · subst v
    rcases near_mask hs.1 hs.2.1 (nearTwo h).1 with h | z
    · exact Or.inl (Or.inr (both (dropB h) (selected hv)))
    · exact Or.inr ⟨safe.1 _ (selected hv),Or.inr (by
        simpa only [show va B = 0 from by decide, Nat.or_zero] using z)⟩
  have hh := freshTwo (by simp [Ne.symm hA, ha]) (by simp [Ne.symm hB, hb]) h
  rcases splitCan hh.1 with x | x <;> rcases splitCan hh.2 with y | y
  · exact Or.inl (Or.inr (both x y))
  · have hsA := exts (v := A) safe (by decide) hl
    exact Or.inl (Or.inr ⟨safe.1 _ x, Or.inr (intersect (hsA.1 _ (oldCan A (selected hv)))
      (safe.2.2 v hlt y))⟩)
  · have hsB := exts (v := B) safe (by decide) hl
    exact Or.inr ⟨safe.1 _ y, Or.inr (intersect (hsB.1 _ (oldCan B (selected hv)))
      (safe.2.1 v hlt x))⟩
  · exact Or.inl (Or.inl (intersect (by simp [Nat.testBit_and,safe.1 _ (selected hv), safe.2.1 v hlt x])
      (safe.2.2 v hlt y)))

private lemma reachProof (exts : StateExtension) {L : List Nat} {p a b : Nat} (n : Nat)
    (hl : ∀ w ∈ L, w < 512) (safe : Safe L p a b) (h : Valid (n+3) L) :
    reach n L p a b = true := by
  induction n generalizing L p a b with
  | zero => exact finishProof exts hl safe h
  | succ n ih =>
    rw [reach, Bool.or_eq_true]
    rcases h with h | ⟨v,hv,hlt,h⟩
    · exact Or.inl (ih hl safe h)
    · refine Or.inr (List.any_eq_true.mpr ⟨v,hv,ih ?_ (exts safe hlt hl) h⟩)
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hlt
      · exact hl _ hw

private theorem kernel_step (k : Nat) (l : List Nat) (p a b : Nat)
    (h : reach k l p a b = false)
    (hs : (choices l).any (fun v => reach k (v :: l) (grow l v p) (a ||| va v) (b ||| vb v)) = false) :
    reach (k+1) l p a b = false := by rw [reach, h, hs]; rfl

private theorem kernel_cons {v : Nat} {vs : List Nat} {f : Nat → Bool}
    (hv : f v = false) (hs : vs.any f = false) : (v :: vs).any f = false := by
  simp [List.any_cons, hv, hs]


set_option maxHeartbeats 40000000 in
private theorem branch : after [] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340 : after [340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33 : after [33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447 : after [447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130 : after [130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495 : after [495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168 : after [168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507 : after [507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202 : after [202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260 : after [260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503 : after [503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304 : after [304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509 : after [509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57 : after [57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448 : after [448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510 : after [510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7 : after [7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_276 : after [340, 276] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_373 : after [340, 373] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_324 : after [340, 324] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_470 : after [340, 470] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_336 : after [340, 336] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_508 : after [340, 508] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_33 : after [340, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_447 : after [340, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_130 : after [340, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_495 : after [340, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_168 : after [340, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_507 : after [340, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_202 : after [340, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_260 : after [340, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_503 : after [340, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_304 : after [340, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_509 : after [340, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_57 : after [340, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_448 : after [340, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_510 : after [340, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_340_7 : after [340, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_478 : after [33, 478] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_487 : after [33, 487] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_32 : after [33, 32] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_505 : after [33, 505] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_340 : after [33, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_447 : after [33, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_130 : after [33, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_495 : after [33, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_168 : after [33, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_507 : after [33, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_202 : after [33, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_260 : after [33, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_503 : after [33, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_304 : after [33, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_509 : after [33, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_57 : after [33, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_448 : after [33, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_510 : after [33, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_33_7 : after [33, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_64 : after [447, 64] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_390 : after [447, 390] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_440 : after [447, 440] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_340 : after [447, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_33 : after [447, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_130 : after [447, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_495 : after [447, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_168 : after [447, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_507 : after [447, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_202 : after [447, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_260 : after [447, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_503 : after [447, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_304 : after [447, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_509 : after [447, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_57 : after [447, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_448 : after [447, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_510 : after [447, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_447_7 : after [447, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_381 : after [130, 381] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_439 : after [130, 439] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_128 : after [130, 128] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_506 : after [130, 506] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_340 : after [130, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_33 : after [130, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_447 : after [130, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_495 : after [130, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_168 : after [130, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_507 : after [130, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_202 : after [130, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_260 : after [130, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_503 : after [130, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_304 : after [130, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_509 : after [130, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_57 : after [130, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_448 : after [130, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_510 : after [130, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_130_7 : after [130, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_16 : after [495, 16] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_293 : after [495, 293] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_488 : after [495, 488] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_340 : after [495, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_33 : after [495, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_447 : after [495, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_130 : after [495, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_168 : after [495, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_507 : after [495, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_202 : after [495, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_260 : after [495, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_503 : after [495, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_304 : after [495, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_509 : after [495, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_57 : after [495, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_448 : after [495, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_510 : after [495, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_495_7 : after [495, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_343 : after [168, 343] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_32 : after [168, 32] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_445 : after [168, 445] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_128 : after [168, 128] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_494 : after [168, 494] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_340 : after [168, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_33 : after [168, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_447 : after [168, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_130 : after [168, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_495 : after [168, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_507 : after [168, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_202 : after [168, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_260 : after [168, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_503 : after [168, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_304 : after [168, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_509 : after [168, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_57 : after [168, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_448 : after [168, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_510 : after [168, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_168_7 : after [168, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_4 : after [507, 4] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_305 : after [507, 305] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_450 : after [507, 450] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_340 : after [507, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_33 : after [507, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_447 : after [507, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_130 : after [507, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_495 : after [507, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_168 : after [507, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_202 : after [507, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_260 : after [507, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_503 : after [507, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_304 : after [507, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_509 : after [507, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_57 : after [507, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_448 : after [507, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_510 : after [507, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_507_7 : after [507, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_138 : after [202, 138] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_235 : after [202, 235] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_194 : after [202, 194] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_462 : after [202, 462] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_200 : after [202, 200] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_506 : after [202, 506] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_340 : after [202, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_33 : after [202, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_447 : after [202, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_130 : after [202, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_495 : after [202, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_168 : after [202, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_507 : after [202, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_260 : after [202, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_503 : after [202, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_304 : after [202, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_509 : after [202, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_57 : after [202, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_448 : after [202, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_510 : after [202, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_202_7 : after [202, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_251 : after [260, 251] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_431 : after [260, 431] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_256 : after [260, 256] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_508 : after [260, 508] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_340 : after [260, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_33 : after [260, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_447 : after [260, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_130 : after [260, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_495 : after [260, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_168 : after [260, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_507 : after [260, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_202 : after [260, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_503 : after [260, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_304 : after [260, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_509 : after [260, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_57 : after [260, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_448 : after [260, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_510 : after [260, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_260_7 : after [260, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_8 : after [503, 8] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_163 : after [503, 163] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_496 : after [503, 496] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_340 : after [503, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_33 : after [503, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_447 : after [503, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_130 : after [503, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_495 : after [503, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_168 : after [503, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_507 : after [503, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_202 : after [503, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_260 : after [503, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_304 : after [503, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_509 : after [503, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_57 : after [503, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_448 : after [503, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_510 : after [503, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_503_7 : after [503, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_207 : after [304, 207] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_32 : after [304, 32] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_443 : after [304, 443] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_256 : after [304, 256] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_502 : after [304, 502] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_340 : after [304, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_33 : after [304, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_447 : after [304, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_130 : after [304, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_495 : after [304, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_168 : after [304, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_507 : after [304, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_202 : after [304, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_260 : after [304, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_503 : after [304, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_509 : after [304, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_57 : after [304, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_448 : after [304, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_510 : after [304, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_304_7 : after [304, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_2 : after [509, 2] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_169 : after [509, 169] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_452 : after [509, 452] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_340 : after [509, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_33 : after [509, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_447 : after [509, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_130 : after [509, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_495 : after [509, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_168 : after [509, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_507 : after [509, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_202 : after [509, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_260 : after [509, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_503 : after [509, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_304 : after [509, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_57 : after [509, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_448 : after [509, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_510 : after [509, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_509_7 : after [509, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_41 : after [57, 41] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_187 : after [57, 187] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_49 : after [57, 49] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_317 : after [57, 317] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_56 : after [57, 56] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_505 : after [57, 505] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_340 : after [57, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_33 : after [57, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_447 : after [57, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_130 : after [57, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_495 : after [57, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_168 : after [57, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_507 : after [57, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_202 : after [57, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_260 : after [57, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_503 : after [57, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_304 : after [57, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_509 : after [57, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_448 : after [57, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_510 : after [57, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_57_7 : after [57, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_63 : after [448, 63] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_128 : after [448, 128] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_491 : after [448, 491] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_256 : after [448, 256] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_501 : after [448, 501] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_340 : after [448, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_33 : after [448, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_447 : after [448, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_130 : after [448, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_495 : after [448, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_168 : after [448, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_507 : after [448, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_202 : after [448, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_260 : after [448, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_503 : after [448, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_304 : after [448, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_509 : after [448, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_57 : after [448, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_510 : after [448, 510] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_448_7 : after [448, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_1 : after [510, 1] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_170 : after [510, 170] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_308 : after [510, 308] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_340 : after [510, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_33 : after [510, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_447 : after [510, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_130 : after [510, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_495 : after [510, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_168 : after [510, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_507 : after [510, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_202 : after [510, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_260 : after [510, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_503 : after [510, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_304 : after [510, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_509 : after [510, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_57 : after [510, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_448 : after [510, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_510_7 : after [510, 7] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_3 : after [7, 3] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_175 : after [7, 175] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_5 : after [7, 5] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_311 : after [7, 311] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_6 : after [7, 6] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_455 : after [7, 455] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_340 : after [7, 340] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_33 : after [7, 33] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_447 : after [7, 447] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_130 : after [7, 130] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_495 : after [7, 495] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_168 : after [7, 168] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_507 : after [7, 507] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_202 : after [7, 202] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_260 : after [7, 260] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_503 : after [7, 503] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_304 : after [7, 304] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_509 : after [7, 509] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_57 : after [7, 57] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_448 : after [7, 448] 2 = false := by decide +kernel
set_option maxHeartbeats 40000000 in
private theorem branch_7_510 : after [7, 510] 2 = false := by decide +kernel

set_option maxHeartbeats 40000000 in
private theorem branch3 : after [] 3 = false := by
  change reach 3 base pbase abase bbase = false
  apply kernel_step 2
  · exact branch
  · have h : choices base = [340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_340 (
      kernel_cons branch_33 (
      kernel_cons branch_447 (
      kernel_cons branch_130 (
      kernel_cons branch_495 (
      kernel_cons branch_168 (
      kernel_cons branch_507 (
      kernel_cons branch_202 (
      kernel_cons branch_260 (
      kernel_cons branch_503 (
      kernel_cons branch_304 (
      kernel_cons branch_509 (
      kernel_cons branch_57 (
      kernel_cons branch_448 (
      kernel_cons branch_510 (
      kernel_cons branch_7 (rfl))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_340 : after [340] 3 = false := by
  change reach 3 (340 :: base) (grow base 340 pbase) (abase ||| va 340) (bbase ||| vb 340) = false
  apply kernel_step 2
  · exact branch_340
  · have h : choices (340 :: base) = [276, 373, 324, 470, 336, 508, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_340_276 (
      kernel_cons branch_340_373 (
      kernel_cons branch_340_324 (
      kernel_cons branch_340_470 (
      kernel_cons branch_340_336 (
      kernel_cons branch_340_508 (
      kernel_cons branch_340_33 (
      kernel_cons branch_340_447 (
      kernel_cons branch_340_130 (
      kernel_cons branch_340_495 (
      kernel_cons branch_340_168 (
      kernel_cons branch_340_507 (
      kernel_cons branch_340_202 (
      kernel_cons branch_340_260 (
      kernel_cons branch_340_503 (
      kernel_cons branch_340_304 (
      kernel_cons branch_340_509 (
      kernel_cons branch_340_57 (
      kernel_cons branch_340_448 (
      kernel_cons branch_340_510 (
      kernel_cons branch_340_7 (rfl)))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_33 : after [33] 3 = false := by
  change reach 3 (33 :: base) (grow base 33 pbase) (abase ||| va 33) (bbase ||| vb 33) = false
  apply kernel_step 2
  · exact branch_33
  · have h : choices (33 :: base) = [478, 487, 32, 505, 340, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_33_478 (
      kernel_cons branch_33_487 (
      kernel_cons branch_33_32 (
      kernel_cons branch_33_505 (
      kernel_cons branch_33_340 (
      kernel_cons branch_33_447 (
      kernel_cons branch_33_130 (
      kernel_cons branch_33_495 (
      kernel_cons branch_33_168 (
      kernel_cons branch_33_507 (
      kernel_cons branch_33_202 (
      kernel_cons branch_33_260 (
      kernel_cons branch_33_503 (
      kernel_cons branch_33_304 (
      kernel_cons branch_33_509 (
      kernel_cons branch_33_57 (
      kernel_cons branch_33_448 (
      kernel_cons branch_33_510 (
      kernel_cons branch_33_7 (rfl)))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_447 : after [447] 3 = false := by
  change reach 3 (447 :: base) (grow base 447 pbase) (abase ||| va 447) (bbase ||| vb 447) = false
  apply kernel_step 2
  · exact branch_447
  · have h : choices (447 :: base) = [64, 390, 440, 340, 33, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_447_64 (
      kernel_cons branch_447_390 (
      kernel_cons branch_447_440 (
      kernel_cons branch_447_340 (
      kernel_cons branch_447_33 (
      kernel_cons branch_447_130 (
      kernel_cons branch_447_495 (
      kernel_cons branch_447_168 (
      kernel_cons branch_447_507 (
      kernel_cons branch_447_202 (
      kernel_cons branch_447_260 (
      kernel_cons branch_447_503 (
      kernel_cons branch_447_304 (
      kernel_cons branch_447_509 (
      kernel_cons branch_447_57 (
      kernel_cons branch_447_448 (
      kernel_cons branch_447_510 (
      kernel_cons branch_447_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_130 : after [130] 3 = false := by
  change reach 3 (130 :: base) (grow base 130 pbase) (abase ||| va 130) (bbase ||| vb 130) = false
  apply kernel_step 2
  · exact branch_130
  · have h : choices (130 :: base) = [381, 439, 128, 506, 340, 33, 447, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_130_381 (
      kernel_cons branch_130_439 (
      kernel_cons branch_130_128 (
      kernel_cons branch_130_506 (
      kernel_cons branch_130_340 (
      kernel_cons branch_130_33 (
      kernel_cons branch_130_447 (
      kernel_cons branch_130_495 (
      kernel_cons branch_130_168 (
      kernel_cons branch_130_507 (
      kernel_cons branch_130_202 (
      kernel_cons branch_130_260 (
      kernel_cons branch_130_503 (
      kernel_cons branch_130_304 (
      kernel_cons branch_130_509 (
      kernel_cons branch_130_57 (
      kernel_cons branch_130_448 (
      kernel_cons branch_130_510 (
      kernel_cons branch_130_7 (rfl)))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_495 : after [495] 3 = false := by
  change reach 3 (495 :: base) (grow base 495 pbase) (abase ||| va 495) (bbase ||| vb 495) = false
  apply kernel_step 2
  · exact branch_495
  · have h : choices (495 :: base) = [16, 293, 488, 340, 33, 447, 130, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_495_16 (
      kernel_cons branch_495_293 (
      kernel_cons branch_495_488 (
      kernel_cons branch_495_340 (
      kernel_cons branch_495_33 (
      kernel_cons branch_495_447 (
      kernel_cons branch_495_130 (
      kernel_cons branch_495_168 (
      kernel_cons branch_495_507 (
      kernel_cons branch_495_202 (
      kernel_cons branch_495_260 (
      kernel_cons branch_495_503 (
      kernel_cons branch_495_304 (
      kernel_cons branch_495_509 (
      kernel_cons branch_495_57 (
      kernel_cons branch_495_448 (
      kernel_cons branch_495_510 (
      kernel_cons branch_495_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_168 : after [168] 3 = false := by
  change reach 3 (168 :: base) (grow base 168 pbase) (abase ||| va 168) (bbase ||| vb 168) = false
  apply kernel_step 2
  · exact branch_168
  · have h : choices (168 :: base) = [343, 32, 445, 128, 494, 340, 33, 447, 130, 495, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_168_343 (
      kernel_cons branch_168_32 (
      kernel_cons branch_168_445 (
      kernel_cons branch_168_128 (
      kernel_cons branch_168_494 (
      kernel_cons branch_168_340 (
      kernel_cons branch_168_33 (
      kernel_cons branch_168_447 (
      kernel_cons branch_168_130 (
      kernel_cons branch_168_495 (
      kernel_cons branch_168_507 (
      kernel_cons branch_168_202 (
      kernel_cons branch_168_260 (
      kernel_cons branch_168_503 (
      kernel_cons branch_168_304 (
      kernel_cons branch_168_509 (
      kernel_cons branch_168_57 (
      kernel_cons branch_168_448 (
      kernel_cons branch_168_510 (
      kernel_cons branch_168_7 (rfl))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_507 : after [507] 3 = false := by
  change reach 3 (507 :: base) (grow base 507 pbase) (abase ||| va 507) (bbase ||| vb 507) = false
  apply kernel_step 2
  · exact branch_507
  · have h : choices (507 :: base) = [4, 305, 450, 340, 33, 447, 130, 495, 168, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_507_4 (
      kernel_cons branch_507_305 (
      kernel_cons branch_507_450 (
      kernel_cons branch_507_340 (
      kernel_cons branch_507_33 (
      kernel_cons branch_507_447 (
      kernel_cons branch_507_130 (
      kernel_cons branch_507_495 (
      kernel_cons branch_507_168 (
      kernel_cons branch_507_202 (
      kernel_cons branch_507_260 (
      kernel_cons branch_507_503 (
      kernel_cons branch_507_304 (
      kernel_cons branch_507_509 (
      kernel_cons branch_507_57 (
      kernel_cons branch_507_448 (
      kernel_cons branch_507_510 (
      kernel_cons branch_507_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_202 : after [202] 3 = false := by
  change reach 3 (202 :: base) (grow base 202 pbase) (abase ||| va 202) (bbase ||| vb 202) = false
  apply kernel_step 2
  · exact branch_202
  · have h : choices (202 :: base) = [138, 235, 194, 462, 200, 506, 340, 33, 447, 130, 495, 168, 507, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_202_138 (
      kernel_cons branch_202_235 (
      kernel_cons branch_202_194 (
      kernel_cons branch_202_462 (
      kernel_cons branch_202_200 (
      kernel_cons branch_202_506 (
      kernel_cons branch_202_340 (
      kernel_cons branch_202_33 (
      kernel_cons branch_202_447 (
      kernel_cons branch_202_130 (
      kernel_cons branch_202_495 (
      kernel_cons branch_202_168 (
      kernel_cons branch_202_507 (
      kernel_cons branch_202_260 (
      kernel_cons branch_202_503 (
      kernel_cons branch_202_304 (
      kernel_cons branch_202_509 (
      kernel_cons branch_202_57 (
      kernel_cons branch_202_448 (
      kernel_cons branch_202_510 (
      kernel_cons branch_202_7 (rfl)))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_260 : after [260] 3 = false := by
  change reach 3 (260 :: base) (grow base 260 pbase) (abase ||| va 260) (bbase ||| vb 260) = false
  apply kernel_step 2
  · exact branch_260
  · have h : choices (260 :: base) = [251, 431, 256, 508, 340, 33, 447, 130, 495, 168, 507, 202, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_260_251 (
      kernel_cons branch_260_431 (
      kernel_cons branch_260_256 (
      kernel_cons branch_260_508 (
      kernel_cons branch_260_340 (
      kernel_cons branch_260_33 (
      kernel_cons branch_260_447 (
      kernel_cons branch_260_130 (
      kernel_cons branch_260_495 (
      kernel_cons branch_260_168 (
      kernel_cons branch_260_507 (
      kernel_cons branch_260_202 (
      kernel_cons branch_260_503 (
      kernel_cons branch_260_304 (
      kernel_cons branch_260_509 (
      kernel_cons branch_260_57 (
      kernel_cons branch_260_448 (
      kernel_cons branch_260_510 (
      kernel_cons branch_260_7 (rfl)))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_503 : after [503] 3 = false := by
  change reach 3 (503 :: base) (grow base 503 pbase) (abase ||| va 503) (bbase ||| vb 503) = false
  apply kernel_step 2
  · exact branch_503
  · have h : choices (503 :: base) = [8, 163, 496, 340, 33, 447, 130, 495, 168, 507, 202, 260, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_503_8 (
      kernel_cons branch_503_163 (
      kernel_cons branch_503_496 (
      kernel_cons branch_503_340 (
      kernel_cons branch_503_33 (
      kernel_cons branch_503_447 (
      kernel_cons branch_503_130 (
      kernel_cons branch_503_495 (
      kernel_cons branch_503_168 (
      kernel_cons branch_503_507 (
      kernel_cons branch_503_202 (
      kernel_cons branch_503_260 (
      kernel_cons branch_503_304 (
      kernel_cons branch_503_509 (
      kernel_cons branch_503_57 (
      kernel_cons branch_503_448 (
      kernel_cons branch_503_510 (
      kernel_cons branch_503_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_304 : after [304] 3 = false := by
  change reach 3 (304 :: base) (grow base 304 pbase) (abase ||| va 304) (bbase ||| vb 304) = false
  apply kernel_step 2
  · exact branch_304
  · have h : choices (304 :: base) = [207, 32, 443, 256, 502, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_304_207 (
      kernel_cons branch_304_32 (
      kernel_cons branch_304_443 (
      kernel_cons branch_304_256 (
      kernel_cons branch_304_502 (
      kernel_cons branch_304_340 (
      kernel_cons branch_304_33 (
      kernel_cons branch_304_447 (
      kernel_cons branch_304_130 (
      kernel_cons branch_304_495 (
      kernel_cons branch_304_168 (
      kernel_cons branch_304_507 (
      kernel_cons branch_304_202 (
      kernel_cons branch_304_260 (
      kernel_cons branch_304_503 (
      kernel_cons branch_304_509 (
      kernel_cons branch_304_57 (
      kernel_cons branch_304_448 (
      kernel_cons branch_304_510 (
      kernel_cons branch_304_7 (rfl))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_509 : after [509] 3 = false := by
  change reach 3 (509 :: base) (grow base 509 pbase) (abase ||| va 509) (bbase ||| vb 509) = false
  apply kernel_step 2
  · exact branch_509
  · have h : choices (509 :: base) = [2, 169, 452, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_509_2 (
      kernel_cons branch_509_169 (
      kernel_cons branch_509_452 (
      kernel_cons branch_509_340 (
      kernel_cons branch_509_33 (
      kernel_cons branch_509_447 (
      kernel_cons branch_509_130 (
      kernel_cons branch_509_495 (
      kernel_cons branch_509_168 (
      kernel_cons branch_509_507 (
      kernel_cons branch_509_202 (
      kernel_cons branch_509_260 (
      kernel_cons branch_509_503 (
      kernel_cons branch_509_304 (
      kernel_cons branch_509_57 (
      kernel_cons branch_509_448 (
      kernel_cons branch_509_510 (
      kernel_cons branch_509_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_57 : after [57] 3 = false := by
  change reach 3 (57 :: base) (grow base 57 pbase) (abase ||| va 57) (bbase ||| vb 57) = false
  apply kernel_step 2
  · exact branch_57
  · have h : choices (57 :: base) = [41, 187, 49, 317, 56, 505, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_57_41 (
      kernel_cons branch_57_187 (
      kernel_cons branch_57_49 (
      kernel_cons branch_57_317 (
      kernel_cons branch_57_56 (
      kernel_cons branch_57_505 (
      kernel_cons branch_57_340 (
      kernel_cons branch_57_33 (
      kernel_cons branch_57_447 (
      kernel_cons branch_57_130 (
      kernel_cons branch_57_495 (
      kernel_cons branch_57_168 (
      kernel_cons branch_57_507 (
      kernel_cons branch_57_202 (
      kernel_cons branch_57_260 (
      kernel_cons branch_57_503 (
      kernel_cons branch_57_304 (
      kernel_cons branch_57_509 (
      kernel_cons branch_57_448 (
      kernel_cons branch_57_510 (
      kernel_cons branch_57_7 (rfl)))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_448 : after [448] 3 = false := by
  change reach 3 (448 :: base) (grow base 448 pbase) (abase ||| va 448) (bbase ||| vb 448) = false
  apply kernel_step 2
  · exact branch_448
  · have h : choices (448 :: base) = [63, 128, 491, 256, 501, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_448_63 (
      kernel_cons branch_448_128 (
      kernel_cons branch_448_491 (
      kernel_cons branch_448_256 (
      kernel_cons branch_448_501 (
      kernel_cons branch_448_340 (
      kernel_cons branch_448_33 (
      kernel_cons branch_448_447 (
      kernel_cons branch_448_130 (
      kernel_cons branch_448_495 (
      kernel_cons branch_448_168 (
      kernel_cons branch_448_507 (
      kernel_cons branch_448_202 (
      kernel_cons branch_448_260 (
      kernel_cons branch_448_503 (
      kernel_cons branch_448_304 (
      kernel_cons branch_448_509 (
      kernel_cons branch_448_57 (
      kernel_cons branch_448_510 (
      kernel_cons branch_448_7 (rfl))))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_510 : after [510] 3 = false := by
  change reach 3 (510 :: base) (grow base 510 pbase) (abase ||| va 510) (bbase ||| vb 510) = false
  apply kernel_step 2
  · exact branch_510
  · have h : choices (510 :: base) = [1, 170, 308, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch_510_1 (
      kernel_cons branch_510_170 (
      kernel_cons branch_510_308 (
      kernel_cons branch_510_340 (
      kernel_cons branch_510_33 (
      kernel_cons branch_510_447 (
      kernel_cons branch_510_130 (
      kernel_cons branch_510_495 (
      kernel_cons branch_510_168 (
      kernel_cons branch_510_507 (
      kernel_cons branch_510_202 (
      kernel_cons branch_510_260 (
      kernel_cons branch_510_503 (
      kernel_cons branch_510_304 (
      kernel_cons branch_510_509 (
      kernel_cons branch_510_57 (
      kernel_cons branch_510_448 (
      kernel_cons branch_510_7 (rfl))))))))))))))))))

set_option maxHeartbeats 40000000 in
private theorem branch3_7 : after [7] 3 = false := by
  change reach 3 (7 :: base) (grow base 7 pbase) (abase ||| va 7) (bbase ||| vb 7) = false
  apply kernel_step 2
  · exact branch_7
  · have h : choices (7 :: base) = [3, 175, 5, 311, 6, 455, 340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510] := by decide +kernel
    rw [h]
    exact kernel_cons branch_7_3 (
      kernel_cons branch_7_175 (
      kernel_cons branch_7_5 (
      kernel_cons branch_7_311 (
      kernel_cons branch_7_6 (
      kernel_cons branch_7_455 (
      kernel_cons branch_7_340 (
      kernel_cons branch_7_33 (
      kernel_cons branch_7_447 (
      kernel_cons branch_7_130 (
      kernel_cons branch_7_495 (
      kernel_cons branch_7_168 (
      kernel_cons branch_7_507 (
      kernel_cons branch_7_202 (
      kernel_cons branch_7_260 (
      kernel_cons branch_7_503 (
      kernel_cons branch_7_304 (
      kernel_cons branch_7_509 (
      kernel_cons branch_7_57 (
      kernel_cons branch_7_448 (
      kernel_cons branch_7_510 (rfl)))))))))))))))))))))

theorem kernel_zero : reach 4 base pbase abase bbase = false := by
  apply kernel_step 3
  · exact branch3
  · have h : choices base = [340, 33, 447, 130, 495, 168, 507, 202, 260, 503, 304, 509, 57, 448, 510, 7] := by decide +kernel
    rw [h]
    exact kernel_cons branch3_340 (
      kernel_cons branch3_33 (
      kernel_cons branch3_447 (
      kernel_cons branch3_130 (
      kernel_cons branch3_495 (
      kernel_cons branch3_168 (
      kernel_cons branch3_507 (
      kernel_cons branch3_202 (
      kernel_cons branch3_260 (
      kernel_cons branch3_503 (
      kernel_cons branch3_304 (
      kernel_cons branch3_509 (
      kernel_cons branch3_57 (
      kernel_cons branch3_448 (
      kernel_cons branch3_510 (
      kernel_cons branch3_7 (rfl))))))))))))))))


end PEqualNP.Outside.PathPair607.Search

namespace PEqualNP.Outside.PathPair607

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.PathPair607.Search

private lemma generated_not {L : List Nat} {x : Nat} (hx : x ∈ L) :
    (511 ^^^ x) ∈ gen L := by
  induction L with
  | nil => simp at hx
  | cons z zs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih hx))

private lemma generated_with_head {L : List Nat} (x : Nat) {y : Nat} (hy : y ∈ L) :
    (x &&& y) ∈ gen (x :: L) ∧ (x ||| y) ∈ gen (x :: L) := by
  constructor
  all_goals
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨y, hy, by simp⟩

private lemma generated_pair {L : List Nat} {x y : Nat} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) :
    (x &&& y) ∈ gen L ∧ (x ||| y) ∈ gen L := by
  induction L with
  | nil => simp at hx
  | cons z zs ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact generated_with_head x ((List.mem_cons.mp hy).resolve_left hne.symm)
    · rcases List.mem_cons.mp hy with rfl | hyt
      · simpa only [Nat.and_comm x y, Nat.or_comm x y] using generated_with_head (L := zs) y hxt
      · obtain ⟨ha, hb⟩ := ih hxt hyt
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ ha),
          List.mem_cons_of_mem _ (List.mem_append_right _ hb)⟩

private lemma table_have_cases {L : List Nat} {x : Table} (hx : Have L x.toNat) :
    x = 0#9 ∨ x = BitVec.allOnes 9 ∨ x.toNat ∈ L := by
  rcases hx with hx | hx | hx
  · exact Or.inl (BitVec.eq_of_toNat_eq hx)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq hx))
  · exact Or.inr (Or.inr hx)

private lemma table_can_not {L : List Nat} {x : Table} (hx : Have L x.toNat) :
    Can L (~~~x).toNat := by
  rcases table_have_cases hx with rfl | rfl | h
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inl rfl)
  · apply Or.inr
    have he : (~~~x).toNat = 511 ^^^ x.toNat := by
      change (~~~x).toNat = ((BitVec.allOnes 9) ^^^ x).toNat
      rw [BitVec.allOnes_xor]
    rw [he]
    exact generated_not h

private lemma table_can_pair {L : List Nat} {x y : Table} (hx : Have L x.toNat)
    (hy : Have L y.toNat) : Can L (x &&& y).toNat ∧ Can L (x ||| y).toNat := by
  rcases table_have_cases hx with rfl | rfl | hx'
  · rw [BitVec.zero_and, BitVec.zero_or]
    exact ⟨Or.inl hx, Or.inl hy⟩
  · rw [BitVec.allOnes_and, BitVec.allOnes_or]
    exact ⟨Or.inl hy, Or.inl hx⟩
  rcases table_have_cases hy with rfl | rfl | hy'
  · rw [BitVec.and_zero, BitVec.or_zero]
    exact ⟨Or.inl hy, Or.inl hx⟩
  · rw [BitVec.and_allOnes, BitVec.or_allOnes]
    exact ⟨Or.inl hx, Or.inl hy⟩
  rw [BitVec.toNat_and, BitVec.toNat_or]
  by_cases he : x.toNat = y.toNat
  · rw [he, Nat.and_self, Nat.or_self]
    exact ⟨Or.inl hy, Or.inl hy⟩
  · obtain ⟨ha, hb⟩ := generated_pair hx' hy' he
    exact ⟨Or.inr ha, Or.inr hb⟩

private lemma table_have_getD {ws : List Table} {L : List Nat}
    (hs : ∀ t ∈ ws, Have L t.toNat) (i : Nat) : Have L (ws.getD i 0).toNat := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hs _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

private lemma gate_table_can {ws : List Table} {L : List Nat} {g : Gate}
    (hs : ∀ t ∈ ws, Have L t.toNat) :
    Can L (gateTable ws g).toNat := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    match ins with
    | [] => exact Or.inl (Or.inr (Or.inl rfl))
    | [i] => exact Or.inl (table_have_getD hs i)
    | i :: j :: _ => exact (table_can_pair (table_have_getD hs i) (table_have_getD hs j)).1
  | or =>
    match ins with
    | [] => exact Or.inl (Or.inl rfl)
    | [i] => exact Or.inl (table_have_getD hs i)
    | i :: j :: _ => exact (table_can_pair (table_have_getD hs i) (table_have_getD hs j)).2
  | not =>
    cases ins with
    | nil => exact Or.inl (Or.inr (Or.inl rfl))
    | cons i _ => exact table_can_not (table_have_getD hs i)
  | mod _ => exact Or.inl (Or.inl rfl)
  | maj => exact Or.inl (Or.inl rfl)

private lemma available_or_choice {L : List Nat} {v : Nat} (h : Can L v) :
    Have L v ∨ v ∈ choices L := by
  by_cases hh : Have L v
  · exact Or.inl hh
  · obtain ⟨hz, ho, hm⟩ : v ≠ 0 ∧ v ≠ 511 ∧ v ∉ L := by simpa [Have] using hh
    apply Or.inr
    simpa [choices, hz, ho, hm] using h.resolve_left hh

private lemma table_have_cons {L : List Nat} {t : Nat} (v : Nat) (h : Have L t) :
    Have (v :: L) t := by
  rcases h with hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (List.mem_cons_of_mem v hh))

private lemma evaluated_tables_valid (gs : List Gate) (ws : List Table) (L : List Nat)
    (hs : ∀ t ∈ ws, Have L t.toNat) (o p : Nat)
    (ha : (wireTables gs ws).getD o 0 = F) (hb : (wireTables gs ws).getD p 0 = G) :
    Valid gs.length L := by
  induction gs generalizing ws L with
  | nil =>
    change ws.getD o 0 = F at ha
    change ws.getD p 0 = G at hb
    have af := table_have_getD hs o
    have bg := table_have_getD hs p
    rw [ha] at af
    rw [hb] at bg
    change (485 = 0 ∨ 485 = 511 ∨ 485 ∈ L) at af
    change (442 = 0 ∨ 442 = 511 ∨ 442 ∈ L) at bg
    exact ⟨by simpa using af, by simpa using bg⟩
  | cons g gs ih =>
    let v := gateTable ws g
    change (wireTables gs (ws ++ [v])).getD o 0 = F at ha
    change (wireTables gs (ws ++ [v])).getD p 0 = G at hb
    rcases available_or_choice (gate_table_can (g := g) hs) with hv | hv
    · apply Or.inl
      apply ih (ws ++ [v]) L _ ha hb
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hs t ht
      · obtain rfl := List.mem_singleton.mp ht
        exact hv
    · apply Or.inr
      refine ⟨v.toNat, hv, v.isLt, ih (ws ++ [v]) (v.toNat :: L) ?_ ha hb⟩
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact table_have_cons _ (hs t ht)
      · obtain rfl := List.mem_singleton.mp ht
        exact Or.inr (Or.inr List.mem_cons_self)

private lemma valid_at_larger_budget {m n : Nat} {L : List Nat}
    (h : Valid m L) (hmn : m ≤ n) : Valid n L := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact Or.inl ih

private lemma circuit_valid (C : Circuit) (h : FanInTwo C) (hs : C.size ≤ 7) (o p : Nat)
    (computed : ∀ x, (C.wires (List.ofFn x)).getD o false = pathA x ∧
      (C.wires (List.ofFn x)).getD p false = pathB x) :
    PEqualNP.Outside.PathPair607.Search.Valid 7 PEqualNP.Outside.PathPair607.Search.base := by
  obtain ⟨ha, hb⟩ := tables_present C h o p computed
  apply valid_at_larger_budget (m := C.gates.length) _ hs
  apply evaluated_tables_valid C.gates inputs base _ o p ha hb
  intro t ht
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact Or.inr (Or.inr (by decide))

end PEqualNP.Outside.PathPair607

namespace PEqualNP.Outside

theorem L_meta_607 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∃ o1 o2 : ℕ, ∀ x : Fin 4 → Bool,
        (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) ∧
        (C.wires (List.ofFn x)).getD o2 false = ((x 1 && x 3) || (x 3 && x 0) || (x 0 && x 2))) ∧
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∃ o1 o2 : ℕ, ∀ x : Fin 4 → Bool,
        (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) ∧
        (C.wires (List.ofFn x)).getD o2 false = ((x 1 && x 3) || (x 3 && x 0) || (x 0 && x 2))) := by
  refine ⟨PathPair607.upper, ?_⟩
  rintro ⟨C, hf, hs, o, p, h⟩
  have valid := PathPair607.circuit_valid C hf hs o p h
  have found := PathPair607.Search.reachProof (@PathPair607.Search.safe_add) (L := PathPair607.Search.base) (p := PathPair607.Search.pbase) (a := PathPair607.Search.abase) (b := PathPair607.Search.bbase) 4
    (by
      intro w hw
      simp only [PathPair607.Search.base, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> decide)
    PathPair607.Search.safe_base valid
  exact Bool.false_ne_true (PathPair607.Search.kernel_zero.symm.trans found)

end PEqualNP.Outside
