import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_3091_1
    (h2496 : ∀ (x1 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => [((0 : Fin (8 : ℕ)), (1 : Fin (8 : ℕ))), ((0 : Fin (8 : ℕ)), (5 : Fin (8 : ℕ))), ((1 : Fin (8 : ℕ)), (2 : Fin (8 : ℕ))), ((1 : Fin (8 : ℕ)), (6 : Fin (8 : ℕ))), ((2 : Fin (8 : ℕ)), (3 : Fin (8 : ℕ))), ((2 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ))), ((4 : Fin (8 : ℕ)), (6 : Fin (8 : ℕ))), ((4 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ))), ((5 : Fin (8 : ℕ)), (7 : Fin (8 : ℕ)))].any fun (x3 : Fin (8 : ℕ) × Fin (8 : ℕ)) => x2 x3.1 && x2 x3.2) x1 → (12 : ℕ) ≤ x1)
    (h3208 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Bool) (x4 : List ℕ) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x6 ∈ x4, x6 < (2 : ℕ) ^ x1) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ x2 → (∀ x9 ∈ x4, x5.eval (List.ofFn fun (x11 : Fin x1) => x9.testBit ↑x11) = x3 x9) → PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc x1 x2 x3 x4))
    (hUnsat : have p : List ℕ := [(515 : ℕ), (6 : ℕ), (524 : ℕ), (536 : ℕ), (529 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (776 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)]; have n : List ℕ := [(554 : ℕ), (50 : ℕ), (581 : ℕ), (616 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (402 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (r : ℕ) => p.contains r) (p ++ n)))
    (hCore : have f : (Fin (9 : ℕ) → Bool) → Bool := fun (x : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (e : ℕ) => x (Fin.ofNat (9 : ℕ) (e / (10 : ℕ))) && x (Fin.ofNat (9 : ℕ) (e % (10 : ℕ))); have isNot : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false] && !g.op.eval [Bool.true]; have rdb : PEqualNP.CircuitLowerBounds.Gate → ℕ → Bool := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) => Decidable.decide (g.inputs[(0 : ℕ)]? = Option.some w) || (!isNot g && g.inputs.contains w); ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size = (14 : ℕ) → (C.output ≤ (24 : ℕ) ∧ ∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ (24 : ℕ)) → (∀ w < (24 : ℕ), w ∈ C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) → (9 : ℕ) + (C.gates.filter isNot).length + ∑ w ∈ Finset.range (24 : ℕ), (List.count w (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) - (1 : ℕ)) ≤ (14 : ℕ) → (1 : ℕ) ≤ (C.gates.filter isNot).length → (2 : ℕ) ≤ List.count (9 : ℕ) (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) → (∀ (i : Fin (9 : ℕ)), ∃ (xs : Fin (9 : ℕ) → Bool), C.eval (List.ofFn xs ++ [xs i]) ≠ f xs) → (C.gates.countP fun g => rdb g (0 : ℕ)) ≤ (2 : ℕ) → (C.gates.countP fun g => rdb g (3 : ℕ)) ≤ (2 : ℕ) → ∃ (xs : Fin (9 : ℕ) → Bool), C.eval (List.ofFn xs ++ [xs (0 : Fin (9 : ℕ)) || xs (3 : Fin (9 : ℕ))]) ≠ f xs) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  classical
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
  let fP : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5
  let rd : Gate → ℕ → Prop := fun g w =>
    g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
  let inp : (Fin 9 → Bool) → List Bool := fun x =>
    List.ofFn x ++ [x 0 || x 3]
  let f2496 : (Fin 8 → Bool) → Bool := fun x2 =>
    [((0 : Fin 8), (1 : Fin 8)), ((0 : Fin 8), (5 : Fin 8)), ((1 : Fin 8), (2 : Fin 8)),
      ((1 : Fin 8), (6 : Fin 8)), ((2 : Fin 8), (3 : Fin 8)), ((2 : Fin 8), (7 : Fin 8)),
      ((4 : Fin 8), (6 : Fin 8)), ((4 : Fin 8), (7 : Fin 8)), ((5 : Fin 8), (7 : Fin 8))].any
      fun e => x2 e.1 && x2 e.2
  let f2832 : (Fin 7 → Bool) → Bool := fun x1 =>
    x1 0 && x1 1 || x1 1 && x1 2 || x1 0 && x1 4 || x1 1 && x1 5 || x1 2 && x1 6 ||
      x1 3 && x1 5 || x1 4 && x1 6 || x1 6 && x1 3
  let xM0 : (Fin 8 → Bool) → Fin 9 → Bool := fun y =>
    ![false, y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7]
  let xM3 : (Fin 8 → Bool) → Fin 9 → Bool := fun y =>
    ![y 2, y 1, y 0, false, y 3, y 7, y 6, y 5, y 4]
  let xM04 : (Fin 7 → Bool) → Fin 9 → Bool := fun z =>
    ![false, z 0, z 1, z 2, false, z 3, z 4, z 5, z 6]
  let xM34 : (Fin 7 → Bool) → Fin 9 → Bool := fun z =>
    ![z 2, z 1, z 0, false, false, z 6, z 5, z 4, z 3]
  let initM0 : List (Bool ⊕ ℕ) :=
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 2]
  let initM3 : List (Bool ⊕ ℕ) :=
    [Sum.inr 2, Sum.inr 1, Sum.inr 0, Sum.inl false, Sum.inr 3, Sum.inr 7, Sum.inr 6, Sum.inr 5, Sum.inr 4, Sum.inr 2]
  let initM04 : List (Bool ⊕ ℕ) :=
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl false, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 2]
  let initM34 : List (Bool ⊕ ℕ) :=
    [Sum.inr 2, Sum.inr 1, Sum.inr 0, Sum.inl false, Sum.inl false, Sum.inr 6, Sum.inr 5, Sum.inr 4, Sum.inr 3, Sum.inr 2]
  let posRows : List ℕ := [515, 6, 524, 536, 529, 545, 66, 132, 776, 160, 320, 288]
  let negRows : List ℕ := [554, 50, 581, 616, 116, 650, 713, 208, 773, 276, 897, 402]
  let allRows : List ℕ := posRows ++ negRows
  have simplify_ok : ∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    intro op m ins g hg
    clear h2496 h3208 hUnsat hCore
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
    clear h2496 h3208 hUnsat hCore simplify_ok
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpAnd]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpOr]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
  have simplify_sound : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
      ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
      (∀ s ∈ ins, svalid w.length s) →
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (sval w)) := by
    intro op hop w ins hlen hv
    clear h2496 h3208 hUnsat hCore simplify_ok simplify_count
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
  have wiresFrom_append : ∀ (gs gs' : List Gate) (w : List Bool),
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    intro gs gs' w; simp [wiresFrom, List.foldl_append]
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
    intro gs w; obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w; rw [ht]; simp [hl]
  have getD_snoc_ne : ∀ {α : Type} (L : List α) (S d : α) (j : ℕ), j ≠ L.length →
      (L ++ [S]).getD j d = L.getD j d := by
    intro α L S d j h
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have getD_snoc_eq : ∀ {α : Type} (L : List α) (S d : α), (L ++ [S]).getD L.length d = S := by
    intro α L S d; simp
  have normGate_eval : ∀ (g : Gate) (F : ℕ → Bool),
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    intro g F; obtain ⟨op, inputs⟩ := g; cases op <;> simp only [normGate]; cases inputs <;> simp [evalNot]
  have normGate_nok : ∀ g : Gate, Ok g → NOk (normGate g) := by
    intro g h; obtain ⟨op, inputs⟩ := g; obtain ⟨hop, hlen⟩ := h
    rcases hop with h | h | h
    · have : op = GateOp.and := h; subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.or := h; subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.not := h; subst this
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
  have rd_iff_norm : ∀ (g : Gate) (w : ℕ), Ok g → (rd g w ↔ w ∈ (normGate g).inputs) := by
    intro g w hg; obtain ⟨op, inputs⟩ := g; obtain ⟨hop, _⟩ := hg
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
    intro o; cases o <;> simp
  have elim_ok : ∀ (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
    intro n gs
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h; apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplify_ok _ _ _ g' (by simpa using h1)
  have valid_mono : ∀ {m m' : ℕ}, m ≤ m' → ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s := by
    intro m m' h s hs; cases s with | inl _ => trivial | inr j => exact lt_of_lt_of_le hs h
  have val_append : ∀ (w t : List Bool) (s : Bool ⊕ ℕ), svalid w.length s →
      sval (w ++ t) s = sval w s := by
    intro w t s hs; cases s with | inl _ => rfl | inr j => exact List.getD_append _ _ _ _ hs
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
        (by intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs; rw [lw']; exact (hi a).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]; apply List.map_congr_left; intro a _; exact (hi a).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by rw [wiresFrom_append]
      obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
        sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq, hl, getD_snoc_eq]; exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, val_append _ _ _ (by rw [lw']; exact (hi i).1)]; exact (hi i).2
  have elim_append : ∀ (n : ℕ) (pre post : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
      elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
    intro n pre post acc; simp [elim, List.foldl_append]
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
        apply Finset.eq_empty_of_forall_notMem; intro p hp; obtain ⟨hpl, _⟩ := hS p hp; simp at hpl
      subst hE; simp [elim]
    | append_singleton gs g ih =>
      intro S hS
      have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by rw [elim_append]; rfl
      have ih' := ih (S.erase gs.length) (by
        intro p hp
        obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
        obtain ⟨hpl, hnone⟩ := hS p hpS
        have hplt : p < gs.length := by rw [List.length_append, List.length_singleton] at hpl; omega
        have htake : (gs ++ [g]).take p = gs.take p := List.take_append_of_le_length (le_of_lt hplt)
        have hge : (gs ++ [g])[p] = gs[p] := List.getElem_append_left hplt
        rw [htake, hge] at hnone; exact ⟨hplt, hnone⟩)
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
        rw [Finset.erase_eq_of_notMem hin] at ih'; omega
  have expand7 : ∀ z : Fin 7 → Bool, z = ![z 0, z 1, z 2, z 3, z 4, z 5, z 6] := by
    intro z; funext i; fin_cases i <;> rfl
  have expand8 : ∀ y : Fin 8 → Bool, y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7] := by
    intro y; funext i; fin_cases i <;> rfl
  have keyM0_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      fP (xM0 ![b0, b1, b2, b3, b4, b5, b6, b7]) = f2496 ![b0, b1, b2, b3, b4, b5, b6, b7] := by decide
  have keyM0 : ∀ y : Fin 8 → Bool, fP (xM0 y) = f2496 y := by
    intro y; rw [expand8 y]; exact keyM0_0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  have keyM3_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      fP (xM3 ![b0, b1, b2, b3, b4, b5, b6, b7]) = f2496 ![b0, b1, b2, b3, b4, b5, b6, b7] := by decide
  have keyM3 : ∀ y : Fin 8 → Bool, fP (xM3 y) = f2496 y := by
    intro y; rw [expand8 y]; exact keyM3_0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  have keyM04_0 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      fP (xM04 ![b0, b1, b2, b3, b4, b5, b6]) = f2832 ![b0, b1, b2, b3, b4, b5, b6] := by decide
  have keyM04 : ∀ z : Fin 7 → Bool, fP (xM04 z) = f2832 z := by
    intro z; rw [expand7 z]; exact keyM04_0 (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)
  have keyM34_0 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      fP (xM34 ![b0, b1, b2, b3, b4, b5, b6]) = f2832 ![b0, b1, b2, b3, b4, b5, b6] := by decide
  have keyM34 : ∀ z : Fin 7 → Bool, fP (xM34 z) = f2832 z := by
    intro z; rw [expand7 z]; exact keyM34_0 (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)
  have inp_len : ∀ x : Fin 9 → Bool, (inp x).length = 10 := by intro x; simp [inp]
  have invM0 : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (inp (xM0 y)) (initM0, []) := by
    intro y; refine ⟨by simp [initM0, inp], ?_⟩; intro i
    by_cases h : i < 10
    · interval_cases i <;> simp [initM0, inp, xM0, svalid, sval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initM0]; omega), List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have invM3 : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (inp (xM3 y)) (initM3, []) := by
    intro y; refine ⟨by simp [initM3, inp], ?_⟩; intro i
    by_cases h : i < 10
    · interval_cases i <;> simp [initM3, inp, xM3, svalid, sval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initM3]; omega), List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have invM04 : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (inp (xM04 z)) (initM04, []) := by
    intro z; refine ⟨by simp [initM04, inp], ?_⟩; intro i
    by_cases h : i < 10
    · interval_cases i <;> simp [initM04, inp, xM04, svalid, sval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initM04]; omega), List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have invM34 : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (inp (xM34 z)) (initM34, []) := by
    intro z; refine ⟨by simp [initM34, inp], ?_⟩; intro i
    by_cases h : i < 10
    · interval_cases i <;> simp [initM34, inp, xM34, svalid, sval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initM34]; omega), List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have use2496 : ∀ (init : List (Bool ⊕ ℕ)) (xM : (Fin 8 → Bool) → Fin 9 → Bool),
      (∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (inp (xM y)) (init, [])) →
      ∀ (gs' : List Gate) (out : ℕ), (∀ g ∈ gs', Ok g) →
      (∀ y : Fin 8 → Bool, (wiresFrom gs' (inp (xM y))).getD out false = f2496 y) →
      12 ≤ (elim 8 gs' (init, [])).2.length := by
    intro init xM hinv0 gs' out hok hev
    set acc := elim 8 gs' (init, []) with hacc
    have hinv : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (wiresFrom gs' (inp (xM y))) acc :=
      fun y => inv_elim 8 (List.ofFn y) (by simp) gs' (inp (xM y)) (init, []) hok (hinv0 y)
    cases hst : acc.1.getD out (Sum.inl false) with
    | inl c =>
      exfalso
      have h0 : f2496 ![false, false, false, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have h1 : f2496 ![true, true, false, false, false, false, false, false] = c := by
        rw [← hev, ← ((hinv _).2 out).2, hst]; rfl
      have hne : f2496 ![false, false, false, false, false, false, false, false] ≠
          f2496 ![true, true, false, false, false, false, false, false] := by decide
      exact hne (h0.trans h1.symm)
    | inr o =>
      have hfan' : FanInTwo ⟨acc.2, o⟩ := elim_ok 8 gs' (init, []) (by simp)
      have heval' : ∀ y : Fin 8 → Bool, ({ gates := acc.2, output := o } : Circuit).eval (List.ofFn y) = f2496 y := by
        intro y
        have hs := ((hinv y).2 out).2
        rw [hst] at hs
        exact hs.trans (hev y)
      exact h2496 acc.2.length ⟨⟨acc.2, o⟩, hfan', by rw [sizeEq], heval'⟩
  have hbound : ∀ r ∈ allRows, r < 2 ^ 10 := by
    have hall : allRows.all (fun r => decide (r < 2 ^ 10)) = true := by decide
    intro r hr; exact of_decide_eq_true (List.all_eq_true.1 hall r hr)
  have hrowBit9 : ∀ r ∈ allRows, r.testBit 9 = (r.testBit 0 || r.testBit 3) := by
    have hall : allRows.all (fun r => decide (r.testBit 9 = (r.testBit 0 || r.testBit 3))) = true := by decide
    intro r hr; exact of_decide_eq_true (List.all_eq_true.1 hall r hr)
  have hrowVal : ∀ r ∈ allRows,
      fP (fun i : Fin 9 => r.testBit i.val) = posRows.contains r := by
    have hall : allRows.all (fun r => decide (fP (fun i : Fin 9 => r.testBit i.val) = posRows.contains r)) = true := by decide
    intro r hr; exact of_decide_eq_true (List.all_eq_true.1 hall r hr)
  dsimp only
  intro C hfan hsz hwf hallin hbud hc9 hnoSingle
  by_contra hnotex
  push_neg at hnotex
  by_cases hnot0 : (List.filter (fun g : Gate => g.op.eval [false] && !g.op.eval [true]) C.gates).length = 0
  · have hmono : Monotone2 C := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hnotg : g.op = GateOp.not := h
        have hpred : (g.op.eval [false] && !g.op.eval [true]) = true := by
          rw [hnotg, evalNot, evalNot]; rfl
        have hmemf : g ∈ List.filter (fun g : Gate => g.op.eval [false] && !g.op.eval [true]) C.gates :=
          List.mem_filter.2 ⟨hg, hpred⟩
        have hpos : 0 < (List.filter (fun g : Gate => g.op.eval [false] && !g.op.eval [true]) C.gates).length :=
          List.length_pos_of_mem hmemf
        omega
    have heval_rows : ∀ r ∈ allRows,
        C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = posRows.contains r := by
      intro r hr
      have hlist : (List.ofFn fun i : Fin 10 => r.testBit i.val) =
          List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 3] := by
        rw [← hrowBit9 r hr]
        simp [List.ofFn_succ]
      rw [hlist]
      exact (hnotex (fun i : Fin 9 => r.testBit i.val)).trans (hrowVal r hr)
    exact hUnsat (h3208 10 14 (fun r => posRows.contains r) allRows C hbound hmono (by omega) heval_rows)
  have hnot1 : 1 ≤ (List.filter (fun g : Gate => g.op.eval [false] && !g.op.eval [true]) C.gates).length := by omega
  let gs := C.gates.map normGate
  have hglen : gs.length = C.gates.length := List.length_map _
  have hclen : C.gates.length = 14 := by rw [← sizeEq]; exact hsz
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg; exact normGate_nok _ (hfan _ hg0)
  have hok_gs : ∀ g ∈ gs, Ok g := fun g hg => (normOk g hg).1
  have hkill_set : ∀ (n : ℕ) (init : List (Bool ⊕ ℕ)), init.length = 10 →
      ∀ (P : Fin C.gates.length → Prop) [DecidablePred P],
      (∀ j : Fin C.gates.length, P j →
        ∃ w < 10, rd (C.gates.get j) w ∧ ∃ c, init.getD w (Sum.inl false) = Sum.inl c) →
      (elim n gs (init, [])).2.length + ((Finset.univ : Finset (Fin C.gates.length)).filter P).card ≤ 14 := by
    intro n init hinitlen P _ hP
    let S : Finset ℕ := ((Finset.univ : Finset (Fin C.gates.length)).filter P).image Fin.val
    have hScard : S.card = ((Finset.univ : Finset (Fin C.gates.length)).filter P).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    rw [← hScard]
    have hcnt := elim_count_none n (init, []) gs S (by
      intro p hp
      obtain ⟨j, hjf, rfl⟩ := Finset.mem_image.1 hp
      have hjP : P j := (Finset.mem_filter.1 hjf).2
      obtain ⟨w, hw10, hrd, c, hcw⟩ := hP j hjP
      have hj' : j.val < gs.length := by omega
      refine ⟨hj', ?_⟩
      have hgj : gs[j.val] = normGate C.gates[j.val] := by simp [gs]
      have hwin : w ∈ gs[j.val].inputs := by
        rw [hgj]
        have hrd' : rd C.gates[j.val] w := by simpa [List.get_eq_getElem] using hrd
        exact (rd_iff_norm _ w (hfan _ (List.getElem_mem j.isLt))).1 hrd'
      have hval : (elim n (gs.take j.val) (init, [])).1.getD w (Sum.inl false) = Sum.inl c := by
        rw [elim_getD n w _ _ _ (by simp [hinitlen]; omega)]
        exact hcw
      have hnok := normOk gs[j.val] (List.getElem_mem hj')
      exact simplify_count gs[j.val].op _ _ hnok.1.1 (by simpa using hnok.1.2)
        (fun h => by simpa using hnok.2 h) ⟨c, List.mem_map.2 ⟨w, hwin, hval⟩⟩)
    simp only [List.length_nil, Nat.zero_add, hglen, hclen] at hcnt
    exact hcnt
  have hcountP_eq : ∀ (p : Gate → Bool),
      C.gates.countP p = ((Finset.univ : Finset (Fin C.gates.length)).filter fun j => p (C.gates.get j) = true).card := by
    intro p
    have h1 : ∀ (l : List Gate), l.countP p = ((Finset.univ : Finset (Fin l.length)).filter fun j => p (l.get j) = true).card := by
      intro l
      induction l with
      | nil => simp
      | cons g tl ih =>
        rw [List.countP_cons, ih]
        have hbij : ((Finset.univ : Finset (Fin (g :: tl).length)).filter fun j => p ((g :: tl).get j) = true).card =
            (if p g = true then 1 else 0) +
              ((Finset.univ : Finset (Fin tl.length)).filter fun j => p (tl.get j) = true).card := by
          have hfin : (Finset.univ : Finset (Fin (g :: tl).length)) =
              insert 0 ((Finset.univ : Finset (Fin tl.length)).map ⟨Fin.succ, Fin.succ_injective _⟩) := by
            ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk, true_and, true_iff]
            exact Fin.cases (Or.inl rfl) (fun y => Or.inr ⟨y, rfl⟩) x
          rw [hfin, Finset.filter_insert]
          have hnot0 : (0 : Fin (g :: tl).length) ∉ ((Finset.univ : Finset (Fin tl.length)).map ⟨Fin.succ, Fin.succ_injective _⟩).filter (fun j => p ((g :: tl).get j) = true) := by
            simp [Fin.succ_ne_zero]
          have hmap : (((Finset.univ : Finset (Fin tl.length)).map ⟨Fin.succ, Fin.succ_injective _⟩).filter fun j => p ((g :: tl).get j) = true).card =
              ((Finset.univ : Finset (Fin tl.length)).filter fun j => p (tl.get j) = true).card := by
            rw [Finset.filter_map, Finset.card_map]
            rfl
          by_cases hpg : p g = true
          · have hpg0 : p ((g :: tl).get 0) = true := hpg
            rw [if_pos hpg0, if_pos hpg, Finset.card_insert_of_notMem hnot0, hmap]
            omega
          · have hpg0 : ¬ p ((g :: tl).get 0) = true := hpg
            rw [if_neg hpg0, if_neg hpg, hmap, Nat.zero_add]
        rw [hbij]
        cases hpg : p g <;> simp [Nat.add_comm]
    exact h1 C.gates
  let rdb : Gate → ℕ → Bool := fun g w =>
    decide (g.inputs[0]? = some w) || (!(g.op.eval [false] && !g.op.eval [true]) && g.inputs.contains w)
  have rdb_iff_rd : ∀ (g : Gate) (w : ℕ), Ok g → (rdb g w = true ↔ rd g w) := by
    intro g w hok
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, _⟩ := hok
    rcases hop with rfl | rfl | rfl
    · simp [rdb, rd, evalAnd]
    · simp [rdb, rd, evalOr]
    · simp [rdb, rd, evalNot]
  have hr0 : (C.gates.countP fun g => rdb g 0) ≤ 2 := by
    rw [hcountP_eq]
    have h12 : 12 ≤ (elim 8 gs (initM0, [])).2.length := use2496 initM0 xM0 invM0 gs C.output hok_gs (by
      intro y
      change (wiresFrom (C.gates.map normGate) (inp (xM0 y))).getD C.output false = f2496 y
      rw [wiresFrom_norm]; exact (hnotex (xM0 y)).trans (keyM0 y))
    have hle := hkill_set 8 initM0 rfl (fun j => rdb (C.gates.get j) 0 = true) (fun j hj =>
      ⟨0, by omega, (rdb_iff_rd _ 0 (hfan _ (List.get_mem _ _))).1 hj, false, rfl⟩)
    omega
  have hr3 : (C.gates.countP fun g => rdb g 3) ≤ 2 := by
    rw [hcountP_eq]
    have h12 : 12 ≤ (elim 8 gs (initM3, [])).2.length := use2496 initM3 xM3 invM3 gs C.output hok_gs (by
      intro y
      change (wiresFrom (C.gates.map normGate) (inp (xM3 y))).getD C.output false = f2496 y
      rw [wiresFrom_norm]; exact (hnotex (xM3 y)).trans (keyM3 y))
    have hle := hkill_set 8 initM3 rfl (fun j => rdb (C.gates.get j) 3 = true) (fun j hj =>
      ⟨3, by omega, (rdb_iff_rd _ 3 (hfan _ (List.get_mem _ _))).1 hj, false, rfl⟩)
    omega
  have hfC_eq : ∀ x : Fin 9 → Bool,
      ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any
        fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = fP x := by
    intro x
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = fP x
    simp only [fP, Bool.or_false]
    ac_rfl
  rw [hsz] at hwf hallin hbud
  have hnoSingle' : ∀ i : Fin 9, ∃ xs : Fin 9 → Bool,
      C.eval (List.ofFn xs ++ [xs i]) ≠
        ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any
          fun e : ℕ => xs (Fin.ofNat 9 (e / 10)) && xs (Fin.ofNat 9 (e % 10))) := by
    intro i
    obtain ⟨xs, hxs⟩ := hnoSingle i
    exact ⟨xs, by rw [hfC_eq xs]; exact hxs⟩
  obtain ⟨xs, hxs⟩ := hCore C hfan hsz hwf hallin hbud hnot1 hc9 hnoSingle' hr0 hr3
  dsimp only at hxs
  rw [hfC_eq xs] at hxs
  exact hxs (hnotex xs)
