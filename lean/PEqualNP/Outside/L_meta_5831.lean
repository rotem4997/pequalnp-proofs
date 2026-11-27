import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5831_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def clamp (w : ℕ) : Fin 25 :=
  if h : w < 24 then ⟨w, by omega⟩ else ⟨24, by omega⟩

private theorem getD_ge_false :
    ∀ (ws : List Bool) (i : ℕ), ws.length ≤ i → ws.getD i false = false
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: ws, i + 1, h => getD_ge_false ws i (by simpa using h)

private theorem getD_clamp (ws : List Bool) (hlen : ws.length ≤ 24) (w : ℕ) :
    ws.getD (clamp w).val false = ws.getD w false := by
  unfold clamp
  by_cases hw : w < 24
  · simp [hw]
  · simp only [hw, ↓reduceDIte]
    rw [getD_ge_false ws 24 hlen, getD_ge_false ws w (by omega)]

private def opCode : GateOp → Fin 3
  | GateOp.and => 0
  | GateOp.or => 1
  | _ => 2

private theorem decode_opCode (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (if opCode op = (0 : Fin 3) then GateOp.and
     else if opCode op = (1 : Fin 3) then GateOp.or
     else GateOp.not) = op := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl <;> rfl

private def inPair : List ℕ → Option (Fin 25) × Option (Fin 25)
  | [] => (none, none)
  | [a] => (some (clamp a), none)
  | a :: b :: _ => (some (clamp a), some (clamp b))

private theorem map_inPair (ins : List ℕ) (hins : ins.length ≤ 2)
    (ws : List Bool) (hlen : ws.length ≤ 24) :
    (List.map Fin.val ((inPair ins).1.toList ++ (inPair ins).2.toList)).map
      (fun i => ws.getD i false) =
    ins.map (fun i => ws.getD i false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rfl
  · change [ws.getD (clamp a).val false] = [ws.getD a false]
    rw [getD_clamp ws hlen a]
  · change [ws.getD (clamp a).val false, ws.getD (clamp b).val false] =
      [ws.getD a false, ws.getD b false]
    rw [getD_clamp ws hlen a, getD_clamp ws hlen b]
  · simp at hins

private def encGate (g : Gate) : Gate :=
  { op := if opCode g.op = (0 : Fin 3) then GateOp.and
          else if opCode g.op = (1 : Fin 3) then GateOp.or
          else GateOp.not
    inputs := List.map Fin.val ((inPair g.inputs).1.toList ++ (inPair g.inputs).2.toList) }

private theorem ofFn_encGate :
    ∀ gs : List Gate,
      List.ofFn (fun k : Fin gs.length => encGate (gs.get k)) = gs.map encGate
  | [] => by simp
  | g :: rest => by
    rw [List.ofFn_succ, List.map_cons, ← ofFn_encGate rest]
    rfl

private theorem foldl_wires_len :
    ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).length =
        ws.length + gs.length
  | [], ws => by simp
  | g :: rest, ws => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_wires_len rest]
    simp only [List.length_append, List.length_singleton]
    omega

private theorem foldl_encGate :
    ∀ (gs : List Gate)
      (_hfan : ∀ g ∈ gs,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (ws : List Bool),
      ws.length + gs.length ≤ 24 →
      (gs.map encGate).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws =
      gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws
  | [], _, _, _ => rfl
  | g :: rest, hfan, ws, hlen => by
    simp only [List.map_cons, List.foldl_cons, List.length_cons] at hlen ⊢
    have hg := hfan g (List.mem_cons.mpr (Or.inl rfl))
    have hws : ws.length ≤ 24 := by omega
    have heval :
        (encGate g).op.eval ((encGate g).inputs.map fun i => ws.getD i false) =
        g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      unfold encGate
      dsimp only
      rw [decode_opCode g.op hg.1, map_inPair g.inputs hg.2 ws hws]
    rw [heval]
    apply foldl_encGate rest (fun g' hg' => hfan g' (List.mem_cons.mpr (Or.inr hg')))
    simp only [List.length_append, List.length_singleton]
    omega

theorem main :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (15 : ℕ) →
      ∃ (x4 : Fin (16 : ℕ)) (x5 : Fin ↑x4 → Fin (3 : ℕ))
        (x6 : Fin ↑x4 → Option (Fin (25 : ℕ)) × Option (Fin (25 : ℕ)))
        (x7 : Fin (25 : ℕ)),
        have x8 : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := List.ofFn fun (x8 : Fin ↑x4) =>
              { op := if x5 x8 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and
                      else if x5 x8 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or
                      else PEqualNP.CircuitLowerBounds.GateOp.not,
                inputs := List.map Fin.val ((x6 x8).1.toList ++ (x6 x8).2.toList) :
                  PEqualNP.CircuitLowerBounds.Gate },
            output := ↑x7 : PEqualNP.CircuitLowerBounds.Circuit };
        (∀ (x9 : Fin (9 : ℕ) → Bool), x8.wires (List.ofFn x9) = x1.wires (List.ofFn x9)) ∧
          PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 =
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro x1 hfan hsize
  have hlen_lt : x1.gates.length < 16 := by
    unfold Circuit.size at hsize
    omega
  refine ⟨⟨x1.gates.length, hlen_lt⟩,
    fun k => opCode (x1.gates.get k).op,
    fun k => inPair (x1.gates.get k).inputs,
    clamp x1.output, ?_⟩
  have hwires : ∀ x9 : Fin 9 → Bool,
      ({ gates := List.ofFn (fun k : Fin x1.gates.length => encGate (x1.gates.get k)),
         output := (clamp x1.output).val } : Circuit).wires (List.ofFn x9) =
      x1.wires (List.ofFn x9) := by
    intro x9
    unfold Circuit.wires
    dsimp only
    rw [ofFn_encGate x1.gates]
    apply foldl_encGate x1.gates hfan (List.ofFn x9)
    rw [List.length_ofFn]
    omega
  refine ⟨hwires, ?_⟩
  funext x9
  change (({ gates := List.ofFn (fun k : Fin x1.gates.length => encGate (x1.gates.get k)),
             output := (clamp x1.output).val } : Circuit).wires (List.ofFn x9)).getD
          (clamp x1.output).val false =
    (x1.wires (List.ofFn x9)).getD x1.output false
  rw [hwires x9]
  have hw_len : (x1.wires (List.ofFn x9)).length ≤ 24 := by
    unfold Circuit.wires
    rw [foldl_wires_len, List.length_ofFn]
    omega
  exact getD_clamp (x1.wires (List.ofFn x9)) hw_len x1.output

end PEqualNP.Outside.L_meta_5831_aux

theorem PEqualNP.Outside.L_meta_5831 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (15 : ℕ) →       ∃ (x4 : Fin (16 : ℕ)) (x5 : Fin ↑x4 → Fin (3 : ℕ)) (x6 : Fin ↑x4 → Option (Fin (25 : ℕ)) × Option (Fin (25 : ℕ))) (x7 : Fin (25 : ℕ)),         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x8 : Fin ↑x4) => { op := if x5 x8 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x5 x8 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := List.map Fin.val ((x6 x8).1.toList ++ (x6 x8).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x7 : PEqualNP.CircuitLowerBounds.Circuit };         (∀ (x9 : Fin (9 : ℕ) → Bool), x8.wires (List.ofFn x9) = x1.wires (List.ofFn x9)) ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 :=
  PEqualNP.Outside.L_meta_5831_aux.main
