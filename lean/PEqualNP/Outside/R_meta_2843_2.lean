import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_2843_2
    (h2537 : ∀ (x1 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ))) x1 → (13 : ℕ) ≤ x1)
    (h2832 : ¬PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x1 : Fin (7 : ℕ) → Bool) => x1 (0 : Fin (7 : ℕ)) && x1 (1 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (2 : Fin (7 : ℕ)) || x1 (0 : Fin (7 : ℕ)) && x1 (4 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (2 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (3 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (4 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (6 : Fin (7 : ℕ)) && x1 (3 : Fin (7 : ℕ))) (10 : ℕ))
    (hCore : have f : (Fin (9 : ℕ) → Bool) → Bool := fun (x : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (e : Fin (9 : ℕ) × Fin (9 : ℕ)) => x e.1 && x e.2; have rd : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) => g.inputs[(0 : ℕ)]? = Option.some w ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ g.inputs; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (9 : ℕ)), (v = (1 : Fin (9 : ℕ)) ∨ v = (2 : Fin (9 : ℕ)) ∨ v = (3 : Fin (9 : ℕ)) ∨ v = (6 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.FanInTwo C → C.size = (13 : ℕ) → (∀ g ∈ C.gates, ¬rd g (9 : ℕ)) → (∃ (i0 i4 : Fin C.gates.length), i0 ≠ i4 ∧ (C.gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get i4).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ (j : Fin C.gates.length), rd (C.gates.get j) (0 : ℕ) ↔ j = i0) ∧ (∀ (j : Fin C.gates.length), rd (C.gates.get j) (4 : ℕ) ↔ j = i4)) → (∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)), x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) || x v]) = f x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) || x4 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (14 : ℕ) ≤ x1.size := by
  have evalAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have evalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have evalNot : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have sizeEq : ∀ c : Circuit, c.size = c.gates.length := fun _ => rfl
  let wiresFrom : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  let simpNot : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m l =>
    l.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (none, Sum.inl true)
      (fun a _ => Sum.elim (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)) a)
  let simpAnd : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m l =>
    l.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (none, Sum.inl true)
      (fun a t => t.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (none, a)
        (fun b t2 => t2.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ))
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c && d)))
              (fun k => (none, bif c then Sum.inr k else Sum.inl false)) b)
            (fun j => Sum.elim (fun d => (none, bif d then Sum.inr j else Sum.inl false))
              (fun k => if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)) b) a)
          (fun _ _ => (none, Sum.inl false))))
  let simpOr : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m l =>
    l.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (none, Sum.inl false)
      (fun a t => t.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (none, a)
        (fun b t2 => t2.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ))
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c || d)))
              (fun k => (none, bif c then Sum.inl true else Sum.inr k)) b)
            (fun j => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr j))
              (fun k => if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)) b) a)
          (fun _ _ => (none, Sum.inl false))))
  let simplify : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
    op.casesOn (motive := fun _ => Option Gate × (Bool ⊕ ℕ)) (simpAnd m ins) (simpOr m ins)
      (simpNot m ins) (fun _ => (none, Sum.inl false)) (none, Sum.inl false)
  let sval : List Bool → Bool ⊕ ℕ → Bool := fun w s =>
    Sum.elim (fun c => c) (fun j => w.getD j false) s
  let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m s =>
    Sum.elim (fun _ => True) (fun j => j < m) s
  let Ok : Gate → Prop := fun g =>
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let NOk : Gate → Prop := fun g => Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
  let normGate : Gate → Gate := fun g =>
    g.op.casesOn (motive := fun _ => Gate) g g ⟨GateOp.not, g.inputs.take 1⟩ (fun _ => g) g
  let elimStep : ℕ → List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate :=
    fun n acc g =>
      (acc.1 ++ [(simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
        acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
  let elim : ℕ → List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate :=
    fun n gs acc => gs.foldl (elimStep n) acc
  let Inv : ℕ → List Bool → List Bool → List (Bool ⊕ ℕ) × List Gate → Prop := fun n y w acc =>
    acc.1.length = w.length ∧ ∀ i : ℕ,
      svalid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      sval (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false
  let fF : (Fin 9 → Bool) → Bool := fun x =>
    [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
      ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
      ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
      ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
      fun e => x e.1 && x e.2
  let rd : Gate → ℕ → Prop := fun g w =>
    g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
  let inp : Fin 9 → (Fin 9 → Bool) → List Bool := fun v x =>
    List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]
  let g2537 : (Fin 9 → Bool) → Bool := fun x2 =>
    x2 0 && x2 1 || x2 1 && x2 2 || x2 2 && x2 3 || x2 0 && x2 5 || x2 1 && x2 6 ||
      x2 2 && x2 7 || x2 3 && x2 8 || x2 5 && x2 7 || x2 6 && x2 8 || x2 8 && x2 5
  let f2832 : (Fin 7 → Bool) → Bool := fun x1 =>
    x1 0 && x1 1 || x1 1 && x1 2 || x1 0 && x1 4 || x1 1 && x1 5 || x1 2 && x1 6 ||
      x1 3 && x1 5 || x1 4 && x1 6 || x1 6 && x1 3
  let xA : (Fin 9 → Bool) → Fin 9 → Bool := fun y =>
    ![y 0, y 1, y 2, y 3, false, y 5, y 6, y 7, y 8]
  let xB : (Fin 7 → Bool) → Fin 9 → Bool := fun z =>
    ![false, z 0, z 1, z 2, false, z 3, z 4, z 5, z 6]
  let initA : List (Bool ⊕ ℕ) := [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
    Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inr 0, Sum.inr 0]
  let bIdx : Fin 9 → Bool ⊕ ℕ := fun v =>
    if v = 1 then Sum.inr 0 else if v = 2 then Sum.inr 1 else if v = 3 then Sum.inr 2
    else if v = 5 then Sum.inr 3 else if v = 6 then Sum.inr 4 else if v = 7 then Sum.inr 5
    else if v = 8 then Sum.inr 6 else Sum.inl false
  let initB : Fin 9 → List (Bool ⊕ ℕ) := fun v =>
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl false,
      Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inl false, bIdx v]
  let perm : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let permWire : ℕ → ℕ := fun i => if h : i < 9 then (perm ⟨i, h⟩).val else i
  let remapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map permWire⟩
  let remapCircuit : Circuit → Circuit := fun C => ⟨C.gates.map remapGate, permWire C.output⟩
  let vZ : Fin 9 → Bool := ![false, false, false, false, false, false, false, false, false]
  let v12 : Fin 9 → Bool := ![false, true, true, false, false, false, false, false, false]
  let v14 : Fin 9 → Bool := ![false, true, false, false, true, false, false, false, false]
  let v014 : Fin 9 → Bool := ![true, true, false, false, true, false, false, false, false]
  let v03 : Fin 9 → Bool := ![true, false, false, true, false, false, false, false, false]
  let v034 : Fin 9 → Bool := ![true, false, false, true, true, false, false, false, false]
  let v34 : Fin 9 → Bool := ![false, false, false, true, true, false, false, false, false]
  have simplify_ok : ∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    intro op m ins g hg
    clear h2537 h2832 hCore
    cases op <;> simp only [simplify] at hg
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpAnd] at hg
      · split_ifs at hg <;> simp at hg; subst hg; simp [Ok]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpOr] at hg
      · split_ifs at hg <;> simp at hg; subst hg; simp [Ok]
    · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
        simp [simpNot] at hg <;> (subst hg; simp [Ok])
    · simp at hg
    · simp at hg
  have simplify_count : ∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) → ins.length ≤ 2 →
      (op = GateOp.not → ins.length ≤ 1) → (∃ c, Sum.inl c ∈ ins) →
      (simplify op m ins).1 = none := by
    intro op m ins hop hlen hnot hc
    clear h2537 h2832 hCore simplify_ok
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpAnd]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpOr]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
  have simplify_inl_none : ∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (c : Bool),
      (simplify op m ins).2 = Sum.inl c → (simplify op m ins).1 = none := by
    intro op m ins c hc
    clear h2537 h2832 hCore simplify_ok simplify_count
    cases op
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · rfl
      · rfl
      · cases a with
        | inl _ => cases b <;> rfl
        | inr j =>
          cases b with
          | inl _ => rfl
          | inr k => by_cases hjk : j = k <;> simp [simplify, simpAnd, hjk] at hc
      · rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · rfl
      · rfl
      · cases a with
        | inl _ => cases b <;> rfl
        | inr j =>
          cases b with
          | inl _ => rfl
          | inr k => by_cases hjk : j = k <;> simp [simplify, simpOr, hjk] at hc
      · rfl
    · rcases ins with _ | ⟨a, l⟩
      · rfl
      · cases a with
        | inl _ => rfl
        | inr _ => simp only [simplify, simpNot] at hc; cases hc
    · rfl
    · rfl
  have simplify_sound : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
      ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
      (∀ s ∈ ins, svalid w.length s) →
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (sval w)) := by
    intro op hop w ins hlen hv
    clear h2537 h2832 hCore simplify_ok simplify_count simplify_inl_none
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpAnd, svalid, sval, evalAnd]
      · cases a <;> simp_all [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
      · cases a with
        | inl c =>
          cases b with
          | inl e => cases c <;> cases e <;> simp [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
          | inr k => cases c <;> simp_all [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
        | inr j =>
          cases b with
          | inl e => cases e <;> simp_all [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
          | inr k =>
            by_cases hjk : j = k
            · subst hjk
              simp_all [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
            · simp_all [simplify, simpAnd, svalid, sval, wiresFrom, evalAnd]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpOr, svalid, sval, evalOr]
      · cases a <;> simp_all [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
      · cases a with
        | inl c =>
          cases b with
          | inl e => cases c <;> cases e <;> simp [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
          | inr k => cases c <;> simp_all [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
        | inr j =>
          cases b with
          | inl e => cases e <;> simp_all [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
          | inr k =>
            by_cases hjk : j = k
            · subst hjk
              simp_all [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
            · simp_all [simplify, simpOr, svalid, sval, wiresFrom, evalOr]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · simp [simplify, simpNot, svalid, sval, evalNot]
      · cases a <;> simp_all [simplify, simpNot, svalid, sval, wiresFrom, evalNot]
  have simplify_const : ∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      (∀ s ∈ ins, ∃ c, s = Sum.inl c) → ∃ c, (simplify op m ins).2 = Sum.inl c := by
    intro op m ins h
    clear h2537 h2832 hCore simplify_ok simplify_count simplify_inl_none simplify_sound
    have hn : ∀ j, Sum.inr j ∉ ins := by
      intro j hj
      obtain ⟨c, hc⟩ := h _ hj
      cases hc
    cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;>
      (try cases b) <;> simp_all [simplify, simpAnd, simpOr, simpNot]
  have wiresFrom_append : ∀ (gs gs' : List Gate) (w : List Bool),
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    intro gs gs' w
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_prefix : ∀ (gs : List Gate) (w : List Bool),
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp
  have length_wiresFrom : ∀ (gs : List Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]
  have getD_snoc_ne : ∀ {α : Type} (L : List α) (S d : α) (j : ℕ), j ≠ L.length →
      (L ++ [S]).getD j d = L.getD j d := by
    intro α L S d j h
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have getD_snoc_eq : ∀ {α : Type} (L : List α) (S d : α), (L ++ [S]).getD L.length d = S := by
    intro α L S d
    simp
  have normGate_eval : ∀ (g : Gate) (F : ℕ → Bool),
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    intro g F
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp only [normGate]
    cases inputs <;> simp [evalNot]
  have normGate_nok : ∀ g : Gate, Ok g → NOk (normGate g) := by
    intro g h
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hlen⟩ := h
    rcases hop with h | h | h
    · have : op = GateOp.and := h
      subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.or := h
      subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.not := h
      subst this
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
  have rd_iff_norm : ∀ (g : Gate) (w : ℕ), Ok g → (rd g w ↔ w ∈ (normGate g).inputs) := by
    intro g w hg
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, _⟩ := hg
    rcases hop with rfl | rfl | rfl
    · simp only [rd, normGate, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      constructor
      · rintro (h | h)
        · exact List.mem_of_getElem? h
        · exact h
      · exact Or.inr
    · simp only [rd, normGate, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      constructor
      · rintro (h | h)
        · exact List.mem_of_getElem? h
        · exact h
      · exact Or.inr
    · simp only [rd, normGate, ne_eq, not_true_eq_false, false_and, or_false]
      cases inputs with
      | nil => simp
      | cons a tl => simp [eq_comm]
  have wiresFrom_norm : ∀ (gs : List Gate) (w : List Bool),
      wiresFrom (gs.map normGate) w = wiresFrom gs w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
          (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
      have s2 : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [s1, s2, normGate_eval, ih]
  have elim_getD : ∀ (n k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
      (acc : List (Bool ⊕ ℕ) × List Gate),
      k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
    intro n k d gs
    induction gs with
    | nil => intro acc _; rfl
    | cons g gs ih =>
      intro acc hk
      have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
      rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
      exact getD_snoc_ne _ _ _ _ (by omega)
  have toList_length_le : ∀ (o : Option Gate), o.toList.length ≤ 1 := by
    intro o
    cases o <;> simp
  have elim_ok : ∀ (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
    intro n gs
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplify_ok _ _ _ g' (by simpa using h1)
  have valid_mono : ∀ {m m' : ℕ}, m ≤ m' → ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s := by
    intro m m' h s hs
    cases s with
    | inl _ => trivial
    | inr j => exact lt_of_lt_of_le hs h
  have val_append : ∀ (w t : List Bool) (s : Bool ⊕ ℕ), svalid w.length s →
      sval (w ++ t) s = sval w s := by
    intro w t s hs
    cases s with
    | inl _ => rfl
    | inr j => exact List.getD_append _ _ _ _ hs
  have inv_elim : ∀ (n : ℕ) (y : List Bool), y.length = n → ∀ (gs : List Gate)
      (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
    intro n y hy gs
    induction gs with
    | nil => intro w acc _ h; exact h
    | cons g gs ih =>
      intro w acc hok h
      apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨hl, hi⟩ := h
      set w' := wiresFrom acc.2 y with hw'
      have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          rw [lw']; exact (hi a).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro a _
        exact (hi a).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [wiresFrom_append]
      obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
        sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2
  have elim_cons : ∀ (n : ℕ) (g : Gate) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      elim n (g :: gs) acc = elim n gs (elimStep n acc g) := fun _ _ _ _ => rfl
  have elim_append : ∀ (n : ℕ) (pre post : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
    intro n pre post acc
    simp [elim, List.foldl_append]
  have elim_fst_len : ∀ (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      (elim n gs acc).1.length = acc.1.length + gs.length := by
    intro n gs
    induction gs with
    | nil => intro acc; rfl
    | cons g gs ih =>
      intro acc
      rw [elim_cons, ih]
      simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
      omega
  have elim_len_le : ∀ (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
    intro n gs
    induction gs with
    | nil => intro acc; simp [elim]
    | cons g gs ih =>
      intro acc
      rw [elim_cons]
      have h1 := ih (elimStep n acc g)
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [List.length_cons]
      omega
  have elim_split_getD : ∀ (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
      (acc : List (Bool ⊕ ℕ) × List Gate) (a : ℕ) (d : Bool ⊕ ℕ),
      a ≤ acc.1.length + pre.length →
      (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
    intro n pre g post acc a d h
    rw [elim_append, elim_cons, elim_getD n a d post _ (by
      show a < ((elim n pre acc).1 ++ [_]).length
      rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]
  have elim_split_getD_lt : ∀ (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
      (acc : List (Bool ⊕ ℕ) × List Gate) (a : ℕ) (d : Bool ⊕ ℕ),
      a < acc.1.length + pre.length →
      (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
    intro n pre g post acc a d h
    rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
    show ((elim n pre acc).1 ++ [_]).getD a d = _
    exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
  have elim_gate_stat : ∀ (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (p : ℕ)
      (hp : p < gs.length),
      (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) =
        (simplify gs[p].op (n + (elim n (gs.take p) acc).2.length)
          (gs[p].inputs.map fun i => (elim n (gs.take p) acc).1.getD i (Sum.inl false))).2 := by
    intro n gs acc p hp
    have hs : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
      rw [List.getElem_cons_drop]
      exact (List.take_append_drop p gs).symm
    have hlen : (gs.take p).length = p := by simp; omega
    conv_lhs => rw [hs]
    rw [elim_split_getD n (gs.take p) gs[p] (gs.drop (p + 1)) acc _ _ (by omega)]
    show ((elim n (gs.take p) acc).1 ++ [_]).getD (acc.1.length + p) (Sum.inl false) = _
    rw [show acc.1.length + p = (elim n (gs.take p) acc).1.length by rw [elim_fst_len, hlen],
      getD_snoc_eq]
  have elim_count_none : ∀ (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (gs : List Gate) (S : Finset ℕ),
      (∀ p ∈ S, ∃ hp : p < gs.length,
        (simplify gs[p].op (n + (elim n (gs.take p) acc).2.length)
          (gs[p].inputs.map fun i => (elim n (gs.take p) acc).1.getD i (Sum.inl false))).1 = none) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
    intro n acc gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro S hS
      have hE : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hpl, _⟩ := hS p hp
        simp at hpl
      subst hE
      simp [elim]
    | append_singleton gs g ih =>
      intro S hS
      have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
        rw [elim_append]; rfl
      have ih' := ih (S.erase gs.length) (by
        intro p hp
        obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
        obtain ⟨hpl, hnone⟩ := hS p hpS
        have hplt : p < gs.length := by rw [List.length_append, List.length_singleton] at hpl; omega
        have htake : (gs ++ [g]).take p = gs.take p := List.take_append_of_le_length (le_of_lt hplt)
        have hge : (gs ++ [g])[p] = gs[p] := List.getElem_append_left hplt
        rw [htake, hge] at hnone
        exact ⟨hplt, hnone⟩)
      have hgl : (gs ++ [g]).length = gs.length + 1 := by simp
      rw [hstep, hgl]
      by_cases hin : gs.length ∈ S
      · obtain ⟨_, hnone⟩ := hS _ hin
        have htake : (gs ++ [g]).take gs.length = gs := by simp
        have hge : (gs ++ [g])[gs.length]'(by simp) = g := by simp
        rw [htake, hge] at hnone
        have h2 : (elimStep n (elim n gs acc) g).2.length = (elim n gs acc).2.length := by
          show ((elim n gs acc).2 ++ (simplify g.op (n + (elim n gs acc).2.length)
            (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1.toList).length = _
          rw [hnone]; simp
        have hcard := Finset.card_erase_of_mem hin
        have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
        omega
      · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
            (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
          omega
        rw [Finset.erase_eq_of_notMem hin] at ih'
        omega
  have agree_wires : ∀ (good : ℕ → Prop) (gs : List Gate) (w w' : List Bool),
      w.length = w'.length →
      (∀ i, good i → w.getD i false = w'.getD i false) →
      (∀ q (hq : q < gs.length), good (w.length + q) →
        ∀ i ∈ gs[q].inputs, good i ∨ w.length + q ≤ i) →
      ∀ i, good i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
    intro good gs
    induction gs with
    | nil => intro w w' _ h _; exact h
    | cons g gs ih =>
      intro w w' hl h hg
      have e1 : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      have e2 : wiresFrom (g :: gs) w'
          = wiresFrom gs (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := rfl
      rw [e1, e2]
      apply ih
      · simp [hl]
      · intro j hj
        by_cases hjl : j = w.length
        · subst hjl
          have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
              = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
            congr 1
            apply List.map_congr_left
            intro k hk
            rcases hg 0 (by simp) (by simpa using hj) k (by simpa using hk) with hk' | hk'
            · exact h k hk'
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          rw [getD_snoc_eq, hv, hl, getD_snoc_eq]
        · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by rw [← hl]; exact hjl)]
          exact h j hj
      · intro q hq hgood k hk
        have e : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + q
            = w.length + (q + 1) := by simp; omega
        rw [e] at hgood ⊢
        exact hg (q + 1) (by simp; omega) hgood k (by simpa using hk)
  have agree_wires_sym : ∀ (good : ℕ → Prop) (gs : List Gate) (w w' : List Bool),
      w.length = w'.length →
      (∀ i, good i → w.getD i false = w'.getD i false) →
      (∀ q (hq : q < gs.length), good (w.length + q) →
        (∀ i ∈ gs[q].inputs, good i ∨ w.length + q ≤ i) ∨
        ((gs[q].op = GateOp.and ∨ gs[q].op = GateOp.or) ∧
          (gs[q].inputs = [0, 4] ∨ gs[q].inputs = [4, 0]) ∧
          w.getD 0 false = w'.getD 4 false ∧ w.getD 4 false = w'.getD 0 false ∧ 4 < w.length)) →
      ∀ i, good i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
    intro good gs
    induction gs with
    | nil => intro w w' _ h _; exact h
    | cons g gs ih =>
      intro w w' hl h hg
      have e1 : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      have e2 : wiresFrom (g :: gs) w'
          = wiresFrom gs (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := rfl
      rw [e1, e2]
      apply ih
      · simp [hl]
      · intro j hj
        by_cases hjl : j = w.length
        · subst hjl
          have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
              = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
            rcases hg 0 (by simp) (by simpa using hj) with hreg | hsym
            · congr 1
              apply List.map_congr_left
              intro k hk
              rcases hreg k (by simpa using hk) with hk' | hk'
              · exact h k hk'
              · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
            · obtain ⟨hop, hins, hw0, hw4, _⟩ := hsym
              change g.op = GateOp.and ∨ g.op = GateOp.or at hop
              change g.inputs = [0, 4] ∨ g.inputs = [4, 0] at hins
              rcases hop with hop | hop <;> rcases hins with hins | hins
              · rw [hop, hins]; simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw4]; exact Bool.and_comm _ _
              · rw [hop, hins]; simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw4]; exact Bool.and_comm _ _
              · rw [hop, hins]; simp only [evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw4]; exact Bool.or_comm _ _
              · rw [hop, hins]; simp only [evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw4]; exact Bool.or_comm _ _
          rw [getD_snoc_eq, hv, hl, getD_snoc_eq]
        · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by rw [← hl]; exact hjl)]
          exact h j hj
      · intro q hq hgood
        have e : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + q
            = w.length + (q + 1) := by simp; omega
        rw [e] at hgood ⊢
        rcases hg (q + 1) (by simp; omega) hgood with hreg | hsym
        · left
          intro k hk
          exact hreg k (by simpa using hk)
        · right
          obtain ⟨hop, hins, hw0, hw4, h4l⟩ := hsym
          refine ⟨by simpa using hop, by simpa using hins, ?_, ?_, by simp; omega⟩
          · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]; exact hw0
          · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]; exact hw4
  have eval_agree : ∀ (C : Circuit) (good : ℕ → Prop) (n : ℕ) (w w' : List Bool),
      w.length = n → w'.length = n →
      (∀ i, good i → w.getD i false = w'.getD i false) →
      (∀ q (hq : q < C.gates.length), good (n + q) →
        ∀ i ∈ (normGate C.gates[q]).inputs, good i ∨ n + q ≤ i) →
      good C.output → C.eval w = C.eval w' := by
    intro C good n w w' hn hn' h hg ho
    have e1 : C.eval w = (wiresFrom (C.gates.map normGate) w).getD C.output false := by
      rw [wiresFrom_norm]; rfl
    have e2 : C.eval w' = (wiresFrom (C.gates.map normGate) w').getD C.output false := by
      rw [wiresFrom_norm]; rfl
    rw [e1, e2]
    apply agree_wires good _ w w' (hn.trans hn'.symm) h _ _ ho
    intro q hq hgood i hi
    have hq' : q < C.gates.length := by simpa using hq
    rw [hn] at hgood ⊢
    exact hg q hq' hgood i (by simpa using hi)
  have two_mem : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (a b : ℕ), a ∈ l → b ∈ l → a ≠ b →
      ∀ i ∈ l, i = a ∨ i = b := by
    intro l hl a b ha hb hab
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
    · simp at ha
    · simp at ha hb; omega
    · simp at ha hb ⊢; omega
    · simp at hl
  have two_exact : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (a b : ℕ), a ∈ l → b ∈ l → a ≠ b →
      l = [a, b] ∨ l = [b, a] := by
    intro l hl a b ha hb hab
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
    · simp at ha
    · simp at ha hb; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with h | h <;> first | omega | (subst h; simp)
    · simp at hl
  have keyA : ∀ y : Fin 9 → Bool, fF (xA y) = g2537 y := by
    intro y
    simp only [fF, xA, g2537, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_or,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    ac_rfl
  have keyB : ∀ z : Fin 7 → Bool, fF (xB z) = f2832 z := by
    intro z
    simp only [fF, xB, f2832, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_or,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    ac_rfl
  have keyPerm : ∀ x : Fin 9 → Bool, fF (fun i => x (perm i)) = fF x := by
    intro x
    simp only [fF, perm, List.any_cons, List.any_nil, Bool.or_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    ac_rfl
  have perm_inv : ∀ i : Fin 9, perm (perm i) = i := by decide
  have permWire_inv : ∀ i : ℕ, permWire (permWire i) = i := by
    intro i
    by_cases h : i < 9
    · have h1 : permWire i = (perm ⟨i, h⟩).val := dif_pos h
      rw [h1, show permWire (perm ⟨i, h⟩).val = (perm (perm ⟨i, h⟩)).val from dif_pos (perm ⟨i, h⟩).isLt,
        perm_inv]
    · have h1 : permWire i = i := dif_neg h
      rw [h1, h1]
  have permWire_ge9 : ∀ i : ℕ, 9 ≤ i → permWire i = i := by
    intro i hi; exact dif_neg (by omega)
  have inp_len : ∀ (v : Fin 9) (x : Fin 9 → Bool), (inp v x).length = 11 := by
    intro v x; simp [inp]
  have wiresFrom_remap : ∀ (gs : List Gate) (w1 w2 : List Bool),
      w1.length = w2.length → 9 ≤ w1.length →
      (∀ i, w1.getD (permWire i) false = w2.getD i false) →
      ∀ i, (wiresFrom (gs.map remapGate) w1).getD (permWire i) false = (wiresFrom gs w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro w1 w2 _ _ h; exact h
    | cons g gs ih =>
      intro w1 w2 hlen h9 h
      have e1 : wiresFrom ((g :: gs).map remapGate) w1 =
          wiresFrom (gs.map remapGate) (w1 ++ [(remapGate g).op.eval ((remapGate g).inputs.map fun i => w1.getD i false)]) := rfl
      have e2 : wiresFrom (g :: gs) w2 =
          wiresFrom gs (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := rfl
      rw [e1, e2]
      apply ih
      · simp [hlen]
      · simp; omega
      · intro j
        have hgv : (remapGate g).op.eval ((remapGate g).inputs.map fun i => w1.getD i false) =
            g.op.eval (g.inputs.map fun i => w2.getD i false) := by
          change g.op.eval ((g.inputs.map permWire).map fun i => w1.getD i false) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro a _
          exact h a
        by_cases hj : j = w2.length
        · subst hj
          have hp : permWire w2.length = w1.length := by rw [permWire_ge9 _ (by omega), hlen]
          rw [hp, getD_snoc_eq, hgv, getD_snoc_eq]
        · have hpne : permWire j ≠ w1.length := by
            intro heq
            have hinv := congrArg permWire heq
            rw [permWire_inv, permWire_ge9 _ h9, hlen] at hinv
            exact hj hinv
          rw [getD_snoc_ne _ _ _ _ hpne, getD_snoc_ne _ _ _ _ hj]
          exact h j
  have remap_eval : ∀ (C : Circuit) (v : Fin 9) (x : Fin 9 → Bool),
      (remapCircuit C).eval (inp (perm v) x) = C.eval (inp v (fun i => x (perm i))) := by
    intro C v x
    change (wiresFrom (C.gates.map remapGate) (inp (perm v) x)).getD (permWire C.output) false =
      (wiresFrom C.gates (inp v (fun i => x (perm i)))).getD C.output false
    apply wiresFrom_remap C.gates (inp (perm v) x) (inp v (fun i => x (perm i)))
    · simp [inp]
    · simp [inp]
    · intro i
      by_cases h9 : i < 9
      · have hp : permWire i = (perm ⟨i, h9⟩).val := dif_pos h9
        rw [hp]
        have hlt1 : (perm ⟨i, h9⟩).val < 9 := (perm ⟨i, h9⟩).isLt
        rw [List.getD_append _ _ _ _ (by simp [hlt1]), List.getD_append _ _ _ _ (by simp [h9]),
          List.getD_eq_getElem _ _ (by simp [hlt1]), List.getD_eq_getElem _ _ (by simp [h9]),
          List.getElem_ofFn, List.getElem_ofFn]
      · rw [permWire_ge9 i (by omega)]
        by_cases h11 : i < 11
        · interval_cases i
          · simp [inp, perm]
          · simp [inp, perm]
        · rw [List.getD_eq_default _ _ (by simp [inp]; omega),
            List.getD_eq_default _ _ (by simp [inp]; omega)]
  have remap_fan : ∀ (C : Circuit), FanInTwo C → FanInTwo (remapCircuit C) := by
    intro C hfan g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hop, hlen⟩ := hfan g0 hg0
    exact ⟨hop, by simpa [remapGate] using hlen⟩
  have remap_size : ∀ (C : Circuit), (remapCircuit C).size = C.size := by
    intro C
    rw [sizeEq, sizeEq]
    exact List.length_map _
  have invA0 : ∀ (v : Fin 9), (v = 0 ∨ v = 4) → ∀ y : Fin 9 → Bool,
      Inv 9 (List.ofFn y) (inp v (xA y)) (initA, []) := by
    intro v hv y
    refine ⟨by simp [initA, inp], ?_⟩
    intro i
    by_cases h : i < 11
    · rcases hv with rfl | rfl <;>
        (interval_cases i <;> simp [initA, inp, xA, svalid, sval, wiresFrom])
    · rw [List.getD_eq_default _ _ (by simp [initA]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have invB0 : ∀ (v : Fin 9) (z : Fin 7 → Bool),
      Inv 7 (List.ofFn z) (inp v (xB z)) (initB v, []) := by
    intro v z
    refine ⟨by simp [initB, inp], ?_⟩
    intro i
    by_cases h : i < 11
    · interval_cases i
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · simp [initB, inp, xB, svalid, sval, wiresFrom]
      · fin_cases v <;> simp [initB, bIdx, inp, xB, svalid, sval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initB]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have useA : ∀ (v : Fin 9), (v = 0 ∨ v = 4) → ∀ (gs' : List Gate) (out : ℕ), (∀ g ∈ gs', Ok g) →
      (∀ y : Fin 9 → Bool, (wiresFrom gs' (inp v (xA y))).getD out false = g2537 y) →
      13 ≤ (elim 9 gs' (initA, [])).2.length := by
    intro v hv gs' out hok hev
    set acc := elim 9 gs' (initA, []) with hacc
    have hinv : ∀ y : Fin 9 → Bool, Inv 9 (List.ofFn y) (wiresFrom gs' (inp v (xA y))) acc :=
      fun y => inv_elim 9 (List.ofFn y) (by simp) gs' (inp v (xA y)) (initA, []) hok (invA0 v hv y)
    cases hst : acc.1.getD out (Sum.inl false) with
    | inl c =>
      exfalso
      have h0 : g2537 ![false, false, false, false, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have h1 : g2537 ![true, true, false, false, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have hne : g2537 ![false, false, false, false, false, false, false, false, false] ≠
          g2537 ![true, true, false, false, false, false, false, false, false] := by decide
      exact hne (h0.trans h1.symm)
    | inr o =>
      have hfan' : FanInTwo ⟨acc.2, o⟩ := elim_ok 9 gs' (initA, []) (by simp)
      have heval' : ∀ y : Fin 9 → Bool, ({ gates := acc.2, output := o } : Circuit).eval (List.ofFn y) = g2537 y := by
        intro y
        have hs := ((hinv y).2 out).2
        rw [hst] at hs
        exact hs.trans (hev y)
      exact h2537 acc.2.length ⟨⟨acc.2, o⟩, hfan', by rw [sizeEq], heval'⟩
  have useB : ∀ (v : Fin 9) (gs' : List Gate) (out : ℕ), (∀ g ∈ gs', Ok g) →
      (∀ z : Fin 7 → Bool, (wiresFrom gs' (inp v (xB z))).getD out false = f2832 z) →
      11 ≤ (elim 7 gs' (initB v, [])).2.length := by
    intro v gs' out hok hev
    set acc := elim 7 gs' (initB v, []) with hacc
    have hinv : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (wiresFrom gs' (inp v (xB z))) acc :=
      fun z => inv_elim 7 (List.ofFn z) (by simp) gs' (inp v (xB z)) (initB v, []) hok (invB0 v z)
    cases hst : acc.1.getD out (Sum.inl false) with
    | inl c =>
      exfalso
      have h0 : f2832 ![false, false, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have h1 : f2832 ![true, true, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have hne : f2832 ![false, false, false, false, false, false, false] ≠
          f2832 ![true, true, false, false, false, false, false] := by decide
      exact hne (h0.trans h1.symm)
    | inr o =>
      by_contra hlt
      have hle : acc.2.length ≤ 10 := by omega
      have hfan' : FanInTwo ⟨acc.2, o⟩ := elim_ok 7 gs' (initB v, []) (by simp)
      have heval' : ∀ z : Fin 7 → Bool, ({ gates := acc.2, output := o } : Circuit).eval (List.ofFn z) = f2832 z := by
        intro z
        have hs := ((hinv z).2 out).2
        rw [hst] at hs
        exact hs.trans (hev z)
      exact h2832 ⟨⟨acc.2, o⟩, hfan', by rw [sizeEq]; exact hle, heval'⟩
  have pair12 : ∀ (v : Fin 9) (i : ℕ), ¬ (i = 1 ∨ i = 2 ∨ i = 10) →
      (inp v vZ).getD i false = (inp v v12).getD i false := by
    intro v i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | simp [inp, vZ, v12]
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have pair0 : ∀ (v : Fin 9) (i : ℕ), ¬ (i = 0) →
      (inp v v14).getD i false = (inp v v014).getD i false := by
    intro v i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | simp [inp, v14, v014]
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have pair4 : ∀ (v : Fin 9) (i : ℕ), ¬ (i = 4) →
      (inp v v03).getD i false = (inp v v034).getD i false := by
    intro v i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | simp [inp, v03, v034]
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have pair04 : ∀ (v : Fin 9) (i : ℕ), ¬ (i = 0 ∨ i = 4) →
      (inp v v34).getD i false = (inp v v03).getD i false := by
    intro v i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | simp [inp, v34, v03]
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have flip_gen : ∀ (v : Fin 9) (C : Circuit), (∀ x, C.eval (inp v x) = fF x) →
      ∀ (x x' : Fin 9 → Bool) (D : ℕ → Prop),
      (∀ i, ¬ D i → (inp v x).getD i false = (inp v x').getD i false) → fF x ≠ fF x' →
      ∀ (good : ℕ → Prop), (∀ i, good i → ¬ D i) →
      (∀ q (hq : q < C.gates.length), good (11 + q) →
        ∀ i ∈ (normGate C.gates[q]).inputs, good i ∨ 11 + q ≤ i) →
      good C.output → False := by
    intro v C hall x x' D hpair hF good hG hg ho
    have h := eval_agree C good 11 (inp v x) (inp v x') (inp_len v x) (inp_len v x')
      (fun i hi => hpair i (hG i hi)) hg ho
    rw [hall, hall] at h
    exact hF h
  have solveCore : ∀ (C : Circuit) (v : Fin 9),
      (v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 6) →
      FanInTwo C → C.size ≤ 13 → (∀ x : Fin 9 → Bool, C.eval (inp v x) = fF x) → False := by
    intro C v hv hfan hsize hall
    let gs := C.gates.map normGate
    have hglen : gs.length = C.gates.length := List.length_map _
    have normOk : ∀ g ∈ gs, NOk g := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact normGate_nok _ (hfan _ hg0)
    have hok_gs : ∀ g ∈ gs, Ok g := fun g hg => (normOk g hg).1
    have hevB_gs : ∀ z : Fin 7 → Bool, (wiresFrom gs (inp v (xB z))).getD C.output false = f2832 z := by
      intro z
      change (wiresFrom (C.gates.map normGate) (inp v (xB z))).getD C.output false = f2832 z
      rw [wiresFrom_norm]
      exact (hall (xB z)).trans (keyB z)
    have h11B : 11 ≤ (elim 7 gs (initB v, [])).2.length := useB v gs C.output hok_gs hevB_gs
    let accB := elim 7 gs (initB v, [])
    have outc := flip_gen v C hall vZ v12 (fun i => i = 1 ∨ i = 2 ∨ i = 10) (pair12 v) (by decide)
    have flip0 := flip_gen v C hall v14 v014 (fun i => i = 0) (pair0 v) (by decide)
    have flip4 := flip_gen v C hall v03 v034 (fun i => i = 4) (pair4 v) (by decide)
    have hout_ne0 : C.output ≠ 0 := fun ho =>
      outc (fun i => i = 0) (by intro i hi; omega) (by intro q hq h; omega) ho
    have hout_ne4 : C.output ≠ 4 := fun ho =>
      outc (fun i => i = 4) (by intro i hi; omega) (by intro q hq h; omega) ho
    have hread0 : ∃ i0 : Fin C.gates.length, 0 ∈ (normGate C.gates[i0.val]).inputs := by
      by_contra hn
      push_neg at hn
      refine flip0 (fun i => i ≠ 0) (fun i hi => hi) ?_ hout_ne0
      intro q hq _ i hi; left; rintro rfl; exact hn ⟨q, hq⟩ hi
    have hread4 : ∃ i4 : Fin C.gates.length, 4 ∈ (normGate C.gates[i4.val]).inputs := by
      by_contra hn
      push_neg at hn
      refine flip4 (fun i => i ≠ 4) (fun i hi => hi) ?_ hout_ne4
      intro q hq _ i hi; left; rintro rfl; exact hn ⟨q, hq⟩ hi
    have hnoSingle04 : ∀ (good : ℕ → Prop) (p : Fin C.gates.length),
        good C.output →
        (∀ i, good i → i ≠ 0 ∧ i ≠ 4) →
        (∀ q (hq : q < C.gates.length), good (11 + q) → q ≠ p.val →
          ∀ i ∈ (normGate C.gates[q]).inputs, good i ∨ 11 + q ≤ i) →
        (∀ i ∈ (normGate C.gates[p.val]).inputs, good i ∨ i = 0 ∨ i = 4 ∨ 11 + p.val ≤ i) →
        False := by
      intro good p hgo hgn hqother hpall
      by_cases h0p : 0 ∈ (normGate C.gates[p.val]).inputs
      · by_cases h4p : 4 ∈ (normGate C.gates[p.val]).inputs
        · have hnok := normGate_nok _ (hfan _ (List.getElem_mem p.isLt))
          have hnot_not : (normGate C.gates[p.val]).op ≠ GateOp.not := by
            intro hnt
            have hl1 := hnok.2 hnt
            rcases h1 : (normGate C.gates[p.val]).inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
            · rw [h1] at h0p; simp at h0p
            · rw [h1] at h0p h4p; simp at h0p h4p; omega
            · rw [h1] at hl1; simp at hl1
          have hop : (normGate C.gates[p.val]).op = GateOp.and ∨
              (normGate C.gates[p.val]).op = GateOp.or := by
            rcases hnok.1.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hnot_not
          have hins : (normGate C.gates[p.val]).inputs = [0, 4] ∨
              (normGate C.gates[p.val]).inputs = [4, 0] :=
            two_exact _ hnok.1.2 0 4 h0p h4p (by omega)
          have heq : C.eval (inp v v34) = C.eval (inp v v03) := by
            have e1 : C.eval (inp v v34) = (wiresFrom gs (inp v v34)).getD C.output false := by
              rw [show gs = C.gates.map normGate from rfl, wiresFrom_norm]; rfl
            have e2 : C.eval (inp v v03) = (wiresFrom gs (inp v v03)).getD C.output false := by
              rw [show gs = C.gates.map normGate from rfl, wiresFrom_norm]; rfl
            rw [e1, e2]
            apply agree_wires_sym good gs (inp v v34) (inp v v03)
              ((inp_len v v34).trans (inp_len v v03).symm)
              (fun i hi => pair04 v i (by intro hor; rcases hor with rfl | rfl; exact (hgn 0 hi).1 rfl; exact (hgn 4 hi).2 rfl))
              _ C.output hgo
            intro q hq hgood
            have hq' : q < C.gates.length := by omega
            have hgq : gs[q] = normGate C.gates[q] := by simp [gs]
            rw [inp_len] at hgood ⊢
            by_cases hqp : q = p.val
            · right
              rw [hgq]
              have heqp : normGate C.gates[q] = normGate C.gates[p.val] := by simp only [hqp]
              rw [heqp]
              refine ⟨hop, hins, ?_, ?_, by omega⟩
              · simp [inp, v34, v03]
              · simp [inp, v34, v03]
            · left
              rw [hgq]
              exact hqother q hq' hgood hqp
          rw [hall, hall] at heq
          have hne : fF v34 ≠ fF v03 := by decide
          exact hne heq
        · refine flip4 (fun i => good i ∨ i = 0) ?_ ?_ (Or.inl hgo)
          · intro i hi; rcases hi with h | rfl; exact (hgn i h).2; omega
          · intro q hq hgood i hi
            have hgood' : good (11 + q) := by rcases hgood with h | h; exact h; omega
            by_cases hqp : q = p.val
            · subst hqp
              rcases hpall i hi with hg | rfl | rfl | hge
              · exact Or.inl (Or.inl hg)
              · exact Or.inl (Or.inr rfl)
              · exact absurd hi h4p
              · exact Or.inr hge
            · rcases hqother q hq hgood' hqp i hi with hg | hge
              · exact Or.inl (Or.inl hg)
              · exact Or.inr hge
      · refine flip0 (fun i => good i ∨ i = 4) ?_ ?_ (Or.inl hgo)
        · intro i hi; rcases hi with h | rfl; exact (hgn i h).1; omega
        · intro q hq hgood i hi
          have hgood' : good (11 + q) := by rcases hgood with h | h; exact h; omega
          by_cases hqp : q = p.val
          · subst hqp
            rcases hpall i hi with hg | rfl | rfl | hge
            · exact Or.inl (Or.inl hg)
            · exact absurd hi h0p
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr hge
          · rcases hqother q hq hgood' hqp i hi with hg | hge
            · exact Or.inl (Or.inl hg)
            · exact Or.inr hge
    have hnone_of_const_in : ∀ (p : ℕ) (hp : p < gs.length) (a : ℕ),
        a ∈ gs[p].inputs → a < 11 + p →
        (∃ c, accB.1.getD a (Sum.inl false) = Sum.inl c) →
        (simplify gs[p].op (7 + (elim 7 (gs.take p) (initB v, [])).2.length)
          (gs[p].inputs.map fun i => (elim 7 (gs.take p) (initB v, [])).1.getD i (Sum.inl false))).1 = none := by
      intro p hp a ha halt hconst
      obtain ⟨c, hc⟩ := hconst
      have hpre : (elim 7 (gs.take p) (initB v, [])).1.getD a (Sum.inl false) = Sum.inl c := by
        have hs : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
          rw [List.getElem_cons_drop]
          exact (List.take_append_drop p gs).symm
        have h1 := elim_split_getD_lt 7 (gs.take p) gs[p] (gs.drop (p + 1)) (initB v, []) a (Sum.inl false) (by
          rw [List.length_take]; simp [initB]; omega)
        rw [← hs] at h1
        exact h1.symm.trans hc
      have hnok := normOk gs[p] (List.getElem_mem hp)
      exact simplify_count gs[p].op _ _ hnok.1.1 (by simpa using hnok.1.2)
        (fun h => by simpa using hnok.2 h) ⟨c, List.mem_map.2 ⟨a, ha, hpre⟩⟩
    have hB0 : accB.1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [show accB = elim 7 gs (initB v, []) from rfl, elim_getD 7 0 _ _ _ (by simp [initB])]; rfl
    have hB4 : accB.1.getD 4 (Sum.inl false) = Sum.inl false := by
      rw [show accB = elim 7 gs (initB v, []) from rfl, elim_getD 7 4 _ _ _ (by simp [initB])]; rfl
    have hB9 : accB.1.getD 9 (Sum.inl false) = Sum.inl false := by
      rw [show accB = elim 7 gs (initB v, []) from rfl, elim_getD 7 9 _ _ _ (by simp [initB])]; rfl
    have htwo04 : ∃ (j1 j2 : Fin C.gates.length), j1 ≠ j2 ∧
        (0 ∈ (normGate C.gates[j1.val]).inputs ∨ 4 ∈ (normGate C.gates[j1.val]).inputs) ∧
        (0 ∈ (normGate C.gates[j2.val]).inputs ∨ 4 ∈ (normGate C.gates[j2.val]).inputs) := by
      obtain ⟨i0, hi0⟩ := hread0
      obtain ⟨i4, hi4⟩ := hread4
      by_cases hne : i0 ≠ i4
      · exact ⟨i0, i4, hne, Or.inl hi0, Or.inr hi4⟩
      · have heq : i0 = i4 := not_ne_iff.1 hne
        subst heq
        by_contra hno
        push_neg at hno
        have hall_other : ∀ q (hq : q < C.gates.length), q ≠ i0.val →
            0 ∉ (normGate C.gates[q]).inputs ∧ 4 ∉ (normGate C.gates[q]).inputs := by
          intro q hq hqp
          have h1 := hno i0 ⟨q, hq⟩ (fun h => hqp (congrArg Fin.val h).symm) (Or.inl hi0)
          exact h1
        exact hnoSingle04 (fun i => i ≠ 0 ∧ i ≠ 4) i0 ⟨hout_ne0, hout_ne4⟩ (fun _ h => h)
          (fun q hq _ hqp i hi => by
            left
            refine ⟨?_, ?_⟩
            · rintro rfl; exact (hall_other q hq hqp).1 hi
            · rintro rfl; exact (hall_other q hq hqp).2 hi)
          (fun i _ => by
            by_cases h0 : i = 0
            · exact Or.inr (Or.inl h0)
            · by_cases h4 : i = 4
              · exact Or.inr (Or.inr (Or.inl h4))
              · exact Or.inl ⟨h0, h4⟩)
    obtain ⟨j1, j2, hjne, hj1, hj2⟩ := htwo04
    have hnone_j : ∀ (j : Fin C.gates.length),
        (0 ∈ (normGate C.gates[j.val]).inputs ∨ 4 ∈ (normGate C.gates[j.val]).inputs) →
        ∃ hj : j.val < gs.length,
          (simplify gs[j.val].op (7 + (elim 7 (gs.take j.val) (initB v, [])).2.length)
            (gs[j.val].inputs.map fun i => (elim 7 (gs.take j.val) (initB v, [])).1.getD i (Sum.inl false))).1 = none := by
      intro j hj
      have hj' : j.val < gs.length := by omega
      refine ⟨hj', ?_⟩
      have hgj : gs[j.val] = normGate C.gates[j.val] := by simp [gs]
      rcases hj with h0 | h4
      · exact hnone_of_const_in j.val hj' 0 (by rw [hgj]; exact h0) (by omega) ⟨false, hB0⟩
      · exact hnone_of_const_in j.val hj' 4 (by rw [hgj]; exact h4) (by omega) ⟨false, hB4⟩
    have hcard_gen : ∀ S : Finset ℕ,
        (∀ p ∈ S, ∃ hp : p < gs.length,
          (simplify gs[p].op (7 + (elim 7 (gs.take p) (initB v, [])).2.length)
            (gs[p].inputs.map fun i => (elim 7 (gs.take p) (initB v, [])).1.getD i (Sum.inl false))).1 = none) →
        11 + S.card ≤ C.gates.length := by
      intro S hS
      have hcnt := elim_count_none 7 (initB v, []) gs S hS
      simp only [List.length_nil, Nat.zero_add, hglen] at hcnt
      omega
    have hsz_eq : C.size = 13 := by
      have hne_v : j1.val ≠ j2.val := fun h => hjne (Fin.ext h)
      have h2 := hcard_gen ({j1.val, j2.val} : Finset ℕ) (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hnone_j j1 hj1
        · exact hnone_j j2 hj2)
      rw [Finset.card_pair hne_v] at h2
      rw [sizeEq] at hsize ⊢
      omega
    have hclen : C.gates.length = 13 := by rw [← sizeEq]; exact hsz_eq
    have hcard_le2 : ∀ S : Finset ℕ,
        (∀ p ∈ S, ∃ hp : p < gs.length,
          (simplify gs[p].op (7 + (elim 7 (gs.take p) (initB v, [])).2.length)
            (gs[p].inputs.map fun i => (elim 7 (gs.take p) (initB v, [])).1.getD i (Sum.inl false))).1 = none) →
        S.card ≤ 2 := by
      intro S hS
      have := hcard_gen S hS
      omega
    have honly_j12 : ∀ (p : ℕ) (hp : p < gs.length),
        (simplify gs[p].op (7 + (elim 7 (gs.take p) (initB v, [])).2.length)
          (gs[p].inputs.map fun i => (elim 7 (gs.take p) (initB v, [])).1.getD i (Sum.inl false))).1 = none →
        p = j1.val ∨ p = j2.val := by
      intro p hp hnone
      by_contra hnot
      push_neg at hnot
      have hne_v : j1.val ≠ j2.val := fun h => hjne (Fin.ext h)
      have h3 : ({j1.val, j2.val, p} : Finset ℕ).card ≤ 2 := by
        apply hcard_le2
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hnone_j j1 hj1
        · exact hnone_j j2 hj2
        · exact ⟨hp, hnone⟩
      rw [Finset.card_insert_of_notMem (by simp [hne_v, Ne.symm hnot.1]),
        Finset.card_pair (Ne.symm hnot.2)] at h3
      omega
    have hnoConstB : ∀ p (hp : p < C.gates.length) (c : Bool),
        accB.1.getD (11 + p) (Sum.inl false) ≠ Sum.inl c := by
      by_contra hex
      push_neg at hex
      classical
      let K : Finset ℕ := (Finset.range 13).filter fun p =>
        ∃ c : Bool, accB.1.getD (11 + p) (Sum.inl false) = Sum.inl c
      have hKne : K.Nonempty := by
        obtain ⟨p, hp, c, hc⟩ := hex
        exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), c, hc⟩⟩
      let k := K.max' hKne
      have hkmem : k ∈ K := Finset.max'_mem K hKne
      obtain ⟨hkr, ck, hck⟩ := Finset.mem_filter.1 hkmem
      have hklt : k < C.gates.length := by rw [Finset.mem_range] at hkr; omega
      have hkne_out : C.output ≠ 11 + k := by
        intro hout
        have hinv : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (wiresFrom gs (inp v (xB z))) accB :=
          fun z => inv_elim 7 (List.ofFn z) (by simp) gs (inp v (xB z)) (initB v, []) hok_gs (invB0 v z)
        have h0 : f2832 ![false, false, false, false, false, false, false] = ck := by
          rw [← hevB_gs, ← ((hinv _).2 C.output).2, hout, hck]; rfl
        have h1 : f2832 ![true, true, false, false, false, false, false] = ck := by
          rw [← hevB_gs, ← ((hinv _).2 C.output).2, hout, hck]; rfl
        have hne : f2832 ![false, false, false, false, false, false, false] ≠
            f2832 ![true, true, false, false, false, false, false] := by decide
        exact hne (h0.trans h1.symm)
      have hk_is_j : k = j1.val ∨ k = j2.val := by
        have hk' : k < gs.length := by omega
        have hst := elim_gate_stat 7 gs (initB v, []) k hk'
        have hl11 : (initB v, ([] : List Gate)).1.length = 11 := rfl
        rw [hl11] at hst
        have h2 : (simplify gs[k].op (7 + (elim 7 (gs.take k) (initB v, [])).2.length)
            (gs[k].inputs.map fun i => (elim 7 (gs.take k) (initB v, [])).1.getD i (Sum.inl false))).2 = Sum.inl ck := by
          rw [← hst]; exact hck
        exact honly_j12 k hk' (simplify_inl_none _ _ _ ck h2)
      by_cases hused : ∃ m, ∃ hm : m < C.gates.length, k < m ∧ 11 + k ∈ (normGate C.gates[m]).inputs
      · obtain ⟨m, hm, hkm, hmk⟩ := hused
        have hm' : m < gs.length := by omega
        have hgm : gs[m] = normGate C.gates[m] := by simp [gs]
        have hm_none := hnone_of_const_in m hm' (11 + k) (by rw [hgm]; exact hmk) (by omega) ⟨ck, hck⟩
        have hm_j : m = j1.val ∨ m = j2.val := honly_j12 m hm' hm_none
        have hm_04 : 0 ∈ (normGate C.gates[m]).inputs ∨ 4 ∈ (normGate C.gates[m]).inputs := by
          rcases hm_j with rfl | rfl
          · exact hj1
          · exact hj2
        have hst := elim_gate_stat 7 gs (initB v, []) m hm'
        have hl11 : (initB v, ([] : List Gate)).1.length = 11 := rfl
        rw [hl11] at hst
        have hconstm : ∃ cm, accB.1.getD (11 + m) (Sum.inl false) = Sum.inl cm := by
          rw [show accB = elim 7 gs (initB v, []) from rfl, hst]
          apply simplify_const
          intro s hs
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
          rw [hgm] at ha
          have hlen2 := (normGate_nok _ (hfan _ (List.getElem_mem hm))).1.2
          have hpre_k : (elim 7 (gs.take m) (initB v, [])).1.getD (11 + k) (Sum.inl false) = Sum.inl ck := by
            have hs' : gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
              rw [List.getElem_cons_drop]; exact (List.take_append_drop m gs).symm
            have h1 := elim_split_getD_lt 7 (gs.take m) gs[m] (gs.drop (m + 1)) (initB v, []) (11 + k) (Sum.inl false) (by
              rw [List.length_take]; simp [initB]; omega)
            rw [← hs'] at h1
            exact h1.symm.trans hck
          rcases hm_04 with hm0 | hm4
          · rcases two_mem _ hlen2 0 (11 + k) hm0 hmk (by omega) a ha with rfl | rfl
            · rw [elim_getD 7 0 _ _ _ (by simp [initB])]; exact ⟨false, rfl⟩
            · exact ⟨ck, hpre_k⟩
          · rcases two_mem _ hlen2 4 (11 + k) hm4 hmk (by omega) a ha with rfl | rfl
            · rw [elim_getD 7 4 _ _ _ (by simp [initB])]; exact ⟨false, rfl⟩
            · exact ⟨ck, hpre_k⟩
        have hmK : m ∈ K := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hconstm⟩
        have hle := Finset.le_max' K m hmK
        omega
      · push_neg at hused
        let other : Fin C.gates.length := if k = j1.val then j2 else j1
        have h04_sub : ∀ q (hq : q < C.gates.length),
            (0 ∈ (normGate C.gates[q]).inputs ∨ 4 ∈ (normGate C.gates[q]).inputs) →
            q = k ∨ q = other.val := by
          intro q hq hq04
          have hqj := honly_j12 q (by omega) (hnone_j ⟨q, hq⟩ hq04).2
          dsimp only [other]
          split_ifs with h
          · rcases hqj with rfl | rfl; exact Or.inl h.symm; exact Or.inr rfl
          · rcases hk_is_j with hk1 | hk2
            · exact absurd hk1 h
            · rcases hqj with rfl | rfl; exact Or.inr rfl; exact Or.inl hk2.symm
        exact hnoSingle04 (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 11 + k) other
          ⟨hout_ne0, hout_ne4, hkne_out⟩
          (fun _ h => ⟨h.1, h.2.1⟩)
          (fun q hq hgood hqo i hi => by
            have hqk : q ≠ k := by intro h; exact hgood.2.2 (by omega)
            by_cases hi11k : i = 11 + k
            · subst hi11k
              by_cases hkq : k < q
              · exact absurd hi (hused q hq hkq)
              · exact Or.inr (by omega)
            · left
              refine ⟨?_, ?_, hi11k⟩
              · rintro rfl
                rcases h04_sub q hq (Or.inl hi) with h | h
                · exact hqk h
                · exact hqo h
              · rintro rfl
                rcases h04_sub q hq (Or.inr hi) with h | h
                · exact hqk h
                · exact hqo h)
          (fun i hi => by
            by_cases hi0 : i = 0
            · exact Or.inr (Or.inl hi0)
            · by_cases hi4 : i = 4
              · exact Or.inr (Or.inr (Or.inl hi4))
              · by_cases hi11k : i = 11 + k
                · subst hi11k
                  by_cases hko : k < other.val
                  · exact absurd hi (hused other.val other.isLt hko)
                  · exact Or.inr (Or.inr (Or.inr (by omega)))
                · exact Or.inl ⟨hi0, hi4, hi11k⟩)
    have hno_pair_const : ∀ (p : Fin C.gates.length) (a b : ℕ),
        a ≠ b → a ∈ (normGate C.gates[p.val]).inputs → b ∈ (normGate C.gates[p.val]).inputs →
        a < 11 → b < 11 →
        (∃ ca, accB.1.getD a (Sum.inl false) = Sum.inl ca) →
        (∃ cb, accB.1.getD b (Sum.inl false) = Sum.inl cb) → False := by
      intro p a b hab ha hb ha11 hb11 hca hcb
      obtain ⟨ca, hca⟩ := hca
      obtain ⟨cb, hcb⟩ := hcb
      have hp' : p.val < gs.length := by omega
      have hgp : gs[p.val] = normGate C.gates[p.val] := by simp [gs]
      have hst := elim_gate_stat 7 gs (initB v, []) p.val hp'
      have hl11 : (initB v, ([] : List Gate)).1.length = 11 := rfl
      rw [hl11] at hst
      have hconstp : ∃ cp, accB.1.getD (11 + p.val) (Sum.inl false) = Sum.inl cp := by
        rw [show accB = elim 7 gs (initB v, []) from rfl, hst]
        apply simplify_const
        intro s hs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
        rw [hgp] at hu
        have hlen2 := (normGate_nok _ (hfan _ (List.getElem_mem p.isLt))).1.2
        rcases two_mem _ hlen2 a b ha hb hab u hu with rfl | rfl
        · rw [elim_getD 7 u _ _ _ (by simp [initB]; omega)]
          have h1 : (initB v, ([] : List Gate)).1.getD u (Sum.inl false) = Sum.inl ca := by
            rw [← elim_getD 7 u _ gs (initB v, []) (by simp [initB]; omega)]; exact hca
          exact ⟨ca, h1⟩
        · rw [elim_getD 7 u _ _ _ (by simp [initB]; omega)]
          have h1 : (initB v, ([] : List Gate)).1.getD u (Sum.inl false) = Sum.inl cb := by
            rw [← elim_getD 7 u _ gs (initB v, []) (by simp [initB]; omega)]; exact hcb
          exact ⟨cb, h1⟩
      obtain ⟨cp, hcp⟩ := hconstp
      exact hnoConstB p.val p.isLt cp hcp
    obtain ⟨i0, hi0⟩ := hread0
    obtain ⟨i4, hi4⟩ := hread4
    have hne04 : i0 ≠ i4 := by
      intro heq
      subst heq
      exact hno_pair_const i0 0 4 (by omega) hi0 hi4 (by omega) (by omega) ⟨false, hB0⟩ ⟨false, hB4⟩
    have huniq0 : ∀ j : Fin C.gates.length, rd (C.gates.get j) 0 ↔ j = i0 := by
      intro j
      rw [List.get_eq_getElem, rd_iff_norm _ 0 (hfan _ (List.getElem_mem j.isLt))]
      constructor
      · intro hj0
        by_contra hjne
        have hjne4 : j.val ≠ i4.val := by
          intro heq
          have hj4 : 4 ∈ (normGate C.gates[j.val]).inputs := by
            have : j = i4 := Fin.ext heq; subst this; exact hi4
          exact hno_pair_const j 0 4 (by omega) hj0 hj4 (by omega) (by omega) ⟨false, hB0⟩ ⟨false, hB4⟩
        have hne0 : j.val ≠ i0.val := fun h => hjne (Fin.ext h)
        have hne04v : i0.val ≠ i4.val := fun h => hne04 (Fin.ext h)
        have h3 : ({i0.val, i4.val, j.val} : Finset ℕ).card ≤ 2 := by
          apply hcard_le2
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact hnone_j i0 (Or.inl hi0)
          · exact hnone_j i4 (Or.inr hi4)
          · exact hnone_j j (Or.inl hj0)
        rw [Finset.card_insert_of_notMem (by simp [hne04v, Ne.symm hne0]),
          Finset.card_pair (Ne.symm hjne4)] at h3
        omega
      · rintro rfl; exact hi0
    have huniq4 : ∀ j : Fin C.gates.length, rd (C.gates.get j) 4 ↔ j = i4 := by
      intro j
      rw [List.get_eq_getElem, rd_iff_norm _ 4 (hfan _ (List.getElem_mem j.isLt))]
      constructor
      · intro hj4
        by_contra hjne
        have hjne0 : j.val ≠ i0.val := by
          intro heq
          have hj0 : 0 ∈ (normGate C.gates[j.val]).inputs := by
            have : j = i0 := Fin.ext heq; subst this; exact hi0
          exact hno_pair_const j 0 4 (by omega) hj0 hj4 (by omega) (by omega) ⟨false, hB0⟩ ⟨false, hB4⟩
        have hne4 : j.val ≠ i4.val := fun h => hjne (Fin.ext h)
        have hne04v : i0.val ≠ i4.val := fun h => hne04 (Fin.ext h)
        have h3 : ({i0.val, i4.val, j.val} : Finset ℕ).card ≤ 2 := by
          apply hcard_le2
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact hnone_j i0 (Or.inl hi0)
          · exact hnone_j i4 (Or.inr hi4)
          · exact hnone_j j (Or.inr hj4)
        rw [Finset.card_insert_of_notMem (by simp [hne04v, Ne.symm hjne0]),
          Finset.card_pair (Ne.symm hne4)] at h3
        omega
      · rintro rfl; exact hi4
    have hno9 : ∀ g ∈ C.gates, ¬ rd g 9 := by
      intro g hg hrd
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hg
      have h9p : 9 ∈ (normGate C.gates[p]).inputs :=
        (rd_iff_norm _ 9 (hfan _ (List.getElem_mem hp))).1 hrd
      have hp' : p < gs.length := by omega
      have hgp : gs[p] = normGate C.gates[p] := by simp [gs]
      have hnone9 := hnone_of_const_in p hp' 9 (by rw [hgp]; exact h9p) (by omega) ⟨false, hB9⟩
      have hne04v : i0.val ≠ i4.val := fun h => hne04 (Fin.ext h)
      by_cases hp0 : p = i0.val
      · subst hp0
        exact hno_pair_const i0 0 9 (by omega) hi0 h9p (by omega) (by omega) ⟨false, hB0⟩ ⟨false, hB9⟩
      · by_cases hp4 : p = i4.val
        · subst hp4
          exact hno_pair_const i4 4 9 (by omega) hi4 h9p (by omega) (by omega) ⟨false, hB4⟩ ⟨false, hB9⟩
        · have h3 : ({i0.val, i4.val, p} : Finset ℕ).card ≤ 2 := by
            apply hcard_le2
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · exact hnone_j i0 (Or.inl hi0)
            · exact hnone_j i4 (Or.inr hi4)
            · exact ⟨hp', hnone9⟩
          rw [Finset.card_insert_of_notMem (by simp [hne04v, Ne.symm hp0]),
            Finset.card_pair (Ne.symm hp4)] at h3
          omega
    have hop_or : ∀ (p : Fin C.gates.length) (w : ℕ),
        w ∈ (normGate C.gates[p.val]).inputs →
        (elim 7 (gs.take p.val) (initB v, [])).1.getD w (Sum.inl false) = Sum.inl false →
        (C.gates.get p).op = GateOp.or := by
      intro p w hwin hwval
      rw [List.get_eq_getElem]
      have hokp := hfan C.gates[p.val] (List.getElem_mem p.isLt)
      have hp' : p.val < gs.length := by omega
      have hst := elim_gate_stat 7 gs (initB v, []) p.val hp'
      have hl11 : (initB v, ([] : List Gate)).1.length = 11 := rfl
      rw [hl11] at hst
      have hgp : gs[p.val] = normGate C.gates[p.val] := by simp [gs]
      rw [hgp] at hst
      have hmem_false : Sum.inl false ∈ (normGate C.gates[p.val]).inputs.map
          (fun i => (elim 7 (gs.take p.val) (initB v, [])).1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨w, hwin, hwval⟩
      rcases hokp.1 with hop | hop | hop
      · exfalso
        have h1 : C.gates[p.val].op = GateOp.and := hop
        have h2 : (normGate C.gates[p.val]).op = GateOp.and := by
          cases hcg : C.gates[p.val] with
          | mk op ins => rw [hcg] at h1; dsimp only at h1; subst h1; rfl
        have hlen2 : ((normGate C.gates[p.val]).inputs.map
            (fun i => (elim 7 (gs.take p.val) (initB v, [])).1.getD i (Sum.inl false))).length ≤ 2 := by
          simpa using (normGate_nok _ hokp).1.2
        rw [h2] at hst
        set ins := (normGate C.gates[p.val]).inputs.map
          (fun i => (elim 7 (gs.take p.val) (initB v, [])).1.getD i (Sum.inl false)) with hins
        rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp at hmem_false
        · simp only [List.mem_singleton] at hmem_false
          subst hmem_false
          simp only [simplify, simpAnd] at hst
          exact hnoConstB p.val p.isLt false hst
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_false
          rcases hmem_false with rfl | rfl
          · cases b <;> (simp [simplify, simpAnd] at hst; exact hnoConstB p.val p.isLt false hst)
          · cases a <;> (simp [simplify, simpAnd] at hst; exact hnoConstB p.val p.isLt false hst)
        · simp at hlen2
      · exact hop
      · exfalso
        have h1 : C.gates[p.val].op = GateOp.not := hop
        have h2 : (normGate C.gates[p.val]).op = GateOp.not := by
          cases hcg : C.gates[p.val] with
          | mk op ins => rw [hcg] at h1; dsimp only at h1; subst h1; rfl
        have hlen1 : ((normGate C.gates[p.val]).inputs.map
            (fun i => (elim 7 (gs.take p.val) (initB v, [])).1.getD i (Sum.inl false))).length ≤ 1 := by
          simpa using (normGate_nok _ hokp).2 h2
        rw [h2] at hst
        set ins := (normGate C.gates[p.val]).inputs.map
          (fun i => (elim 7 (gs.take p.val) (initB v, [])).1.getD i (Sum.inl false)) with hins
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp at hmem_false
        · simp only [List.mem_singleton] at hmem_false
          subst hmem_false
          simp only [simplify, simpNot, Bool.not_false] at hst
          exact hnoConstB p.val p.isLt true hst
        · simp at hlen1
    have hop0 : (C.gates.get i0).op = GateOp.or :=
      hop_or i0 0 hi0 (by rw [elim_getD 7 0 _ _ _ (by simp [initB])]; rfl)
    have hop4 : (C.gates.get i4).op = GateOp.or :=
      hop_or i4 4 hi4 (by rw [elim_getD 7 4 _ _ _ (by simp [initB])]; rfl)
    exact hCore C v hv hfan hsz_eq hno9 ⟨i0, i4, hne04, hop0, hop4, huniq0, huniq4⟩ hall
  intro C v hfan hall
  by_contra hlt
  have hsize : C.size ≤ 13 := by omega
  have hcase04 : (v = 0 ∨ v = 4) → False := by
    intro hv04
    let gs := C.gates.map normGate
    have hglen : gs.length = C.gates.length := List.length_map _
    have normOk : ∀ g ∈ gs, NOk g := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact normGate_nok _ (hfan _ hg0)
    have hok_gs : ∀ g ∈ gs, Ok g := fun g hg => (normOk g hg).1
    have hevA_gs : ∀ y : Fin 9 → Bool, (wiresFrom gs (inp v (xA y))).getD C.output false = g2537 y := by
      intro y
      change (wiresFrom (C.gates.map normGate) (inp v (xA y))).getD C.output false = g2537 y
      rw [wiresFrom_norm]
      exact (hall (xA y)).trans (keyA y)
    have h13A : 13 ≤ (elim 9 gs (initA, [])).2.length := useA v hv04 gs C.output hok_gs hevA_gs
    have outc := flip_gen v C hall vZ v12 (fun i => i = 1 ∨ i = 2 ∨ i = 10) (pair12 v) (by decide)
    have flip4 := flip_gen v C hall v03 v034 (fun i => i = 4) (pair4 v) (by decide)
    have hout_ne4 : C.output ≠ 4 := fun ho =>
      outc (fun i => i = 4) (by intro i hi; omega) (by intro q hq h; omega) ho
    have hread4 : ∃ i4 : Fin C.gates.length, 4 ∈ (normGate C.gates[i4.val]).inputs := by
      by_contra hn
      push_neg at hn
      refine flip4 (fun i => i ≠ 4) (fun i hi => hi) ?_ hout_ne4
      intro q hq _ i hi; left; rintro rfl; exact hn ⟨q, hq⟩ hi
    obtain ⟨i4, hi4⟩ := hread4
    have h4A : (elim 9 (gs.take i4.val) (initA, [])).1.getD 4 (Sum.inl false) = Sum.inl false := by
      rw [elim_getD 9 4 _ _ _ (by simp [initA])]; rfl
    have hi4' : i4.val < gs.length := by omega
    have hgi4 : gs[i4.val] = normGate C.gates[i4.val] := by simp [gs]
    have hnok4 := normOk gs[i4.val] (List.getElem_mem hi4')
    have hnone4 : (simplify gs[i4.val].op (9 + (elim 9 (gs.take i4.val) (initA, [])).2.length)
        (gs[i4.val].inputs.map fun i => (elim 9 (gs.take i4.val) (initA, [])).1.getD i (Sum.inl false))).1 = none :=
      simplify_count gs[i4.val].op _ _ hnok4.1.1 (by simpa using hnok4.1.2)
        (fun h => by simpa using hnok4.2 h) ⟨false, List.mem_map.2 ⟨4, by rw [hgi4]; exact hi4, h4A⟩⟩
    have hcnt := elim_count_none 9 (initA, []) gs {i4.val} (by
      intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨hi4', hnone4⟩)
    simp only [Finset.card_singleton, List.length_nil, Nat.zero_add, hglen] at hcnt
    rw [sizeEq] at hsize
    omega
  have useSym : (perm v = 1 ∨ perm v = 2 ∨ perm v = 3 ∨ perm v = 6) → False := by
    intro hpv
    apply solveCore (remapCircuit C) (perm v) hpv (remap_fan C hfan) (by rw [remap_size]; exact hsize)
    intro x
    rw [remap_eval, hall]
    exact keyPerm x
  fin_cases v
  · exact hcase04 (Or.inl rfl)
  · exact solveCore C 1 (Or.inl rfl) hfan hsize hall
  · exact solveCore C 2 (Or.inr (Or.inl rfl)) hfan hsize hall
  · exact solveCore C 3 (Or.inr (Or.inr (Or.inl rfl))) hfan hsize hall
  · exact hcase04 (Or.inr rfl)
  · exact useSym (Or.inl rfl)
  · exact solveCore C 6 (Or.inr (Or.inr (Or.inr rfl))) hfan hsize hall
  · exact useSym (Or.inr (Or.inr (Or.inr rfl)))
  · exact useSym (Or.inr (Or.inl rfl))
