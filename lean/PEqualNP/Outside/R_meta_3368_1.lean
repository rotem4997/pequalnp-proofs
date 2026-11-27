import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_3368_1
    (h2537 : ∀ (x1 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ))) x1 → (13 : ℕ) ≤ x1)
    (h2832 : ¬PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x1 : Fin (7 : ℕ) → Bool) => x1 (0 : Fin (7 : ℕ)) && x1 (1 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (2 : Fin (7 : ℕ)) || x1 (0 : Fin (7 : ℕ)) && x1 (4 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (2 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (3 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (4 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (6 : Fin (7 : ℕ)) && x1 (3 : Fin (7 : ℕ))) (10 : ℕ))
    (hCore : have f : (Fin (9 : ℕ) → Bool) → Bool := fun (x : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (e : Fin (9 : ℕ) × Fin (9 : ℕ)) => x e.1 && x e.2; have rd : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) => g.inputs[(0 : ℕ)]? = Option.some w ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ g.inputs; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size = (13 : ℕ) → (∀ g ∈ C.gates, ¬rd g (4 : ℕ)) → (∃ (i0 i9 : Fin C.gates.length), i0 ≠ i9 ∧ (C.gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get i9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ (j : Fin C.gates.length), rd (C.gates.get j) (0 : ℕ) ↔ j = i0) ∧ (∀ (j : Fin C.gates.length), rd (C.gates.get j) (9 : ℕ) ↔ j = i9)) → (∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn (Function.update x (4 : Fin (9 : ℕ)) Bool.false) ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)), x (4 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ))]) = f x) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
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
  let inp : (Fin 9 → Bool) → List Bool := fun x =>
    List.ofFn (Function.update x (4 : Fin 9) false) ++ [x 0 || x 4, x 4 || x 1]
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
    Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inr 0, Sum.inr 1]
  let initB : List (Bool ⊕ ℕ) := [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl false,
    Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inl false, Sum.inr 0]
  let vZ : Fin 9 → Bool := ![false, false, false, false, false, false, false, false, false]
  let v12 : Fin 9 → Bool := ![false, true, true, false, false, false, false, false, false]
  let v45 : Fin 9 → Bool := ![false, false, false, false, true, true, false, false, false]
  let v045 : Fin 9 → Bool := ![true, false, false, false, true, true, false, false, false]
  let v13 : Fin 9 → Bool := ![false, true, false, true, false, false, false, false, false]
  let v134 : Fin 9 → Bool := ![false, true, false, true, true, false, false, false, false]
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
  have simplify_sound : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
      ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
      (∀ s ∈ ins, svalid w.length s) →
      svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (sval w)) := by
    intro op hop w ins hlen hv
    clear h2537 h2832 hCore simplify_ok simplify_count
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
    clear h2537 h2832 hCore simplify_ok simplify_count simplify_sound
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
  have elim_drop_one : ∀ (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
      (acc : List (Bool ⊕ ℕ) × List Gate),
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 = none →
      (elim n (pre ++ g :: post) acc).2.length + 1 ≤ acc.2.length + (pre ++ g :: post).length := by
    intro n pre g post acc hnone
    rw [elim_append, elim_cons]
    have h1 := elim_len_le n post (elimStep n (elim n pre acc) g)
    have h2 : (elimStep n (elim n pre acc) g).2.length = (elim n pre acc).2.length := by
      show ((elim n pre acc).2 ++ (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1.toList).length = _
      rw [hnone]; simp
    have h3 := elim_len_le n pre acc
    simp only [List.length_append, List.length_cons]
    omega
  have elim_count : ∀ (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (gs : List Gate),
      (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
      (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
          ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
        (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
    intro n acc gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ S hS
      have hE : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨g, hg, _⟩ := hS p hp
        simp at hg
      subst hE
      simp [elim]
    | append_singleton gs g ih =>
      intro hok S hS
      have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
        rw [elim_append]; rfl
      have hpre : ∀ (a : ℕ) (d : Bool ⊕ ℕ), a < acc.1.length + gs.length →
          (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
        fun a d h => elim_split_getD_lt n gs g [] acc a d h
      have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
      have ih' := ih hok' (S.erase gs.length) (by
        intro p hp
        obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
        obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
        have hpl : p < gs.length := by
          obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
          rw [List.length_append, List.length_singleton] at h1
          omega
        rw [List.getElem?_append_left hpl] at hg'
        rw [hpre a _ (by omega)] at hc
        exact ⟨g', hg', a, ha, hlt, c, hc⟩)
      have hgl : (gs ++ [g]).length = gs.length + 1 := by simp
      rw [hstep, hgl]
      by_cases hin : gs.length ∈ S
      · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
        have hgg : g' = g := by
          rw [List.getElem?_concat_length] at hg'
          exact (Option.some.inj hg').symm
        subst hgg
        rw [hpre a _ hlt] at hc
        have hnone : (simplify g'.op (n + (elim n gs acc).2.length)
            (g'.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1 = none := by
          have hgok := hok g' (by simp)
          exact simplify_count g'.op _ _ hgok.1.1 (by simpa using hgok.1.2)
            (fun h => by simpa using hgok.2 h) ⟨c, List.mem_map.2 ⟨a, ha, hc⟩⟩
        have h2 : (elimStep n (elim n gs acc) g').2.length = (elim n gs acc).2.length := by
          show ((elim n gs acc).2 ++ (simplify g'.op (n + (elim n gs acc).2.length)
            (g'.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1.toList).length = _
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
  have replace_unused : ∀ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (g' : Gate) (w : List Bool),
      (∀ q (hq : q < gs.length), k < q → w.length + k ∉ gs[q].inputs) →
      ∀ i, i ≠ w.length + k →
        (wiresFrom (gs.take k ++ g' :: gs.drop (k + 1)) w).getD i false = (wiresFrom gs w).getD i false := by
    intro gs k hk g' w hunused
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      rw [List.getElem_cons_drop]
      exact (List.take_append_drop k gs).symm
    have hprelen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take]
      omega
    have heq1 : wiresFrom (gs.take k ++ g' :: gs.drop (k + 1)) w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++ [g'.op.eval (g'.inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have heq2 : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++ [gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit]
      rw [wiresFrom_append]; rfl
    rw [heq1, heq2]
    apply agree_wires (fun i => i ≠ w.length + k) (gs.drop (k + 1))
    · simp
    · intro i hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    · intro q hq _ i hi
      left
      have hq' : k + 1 + q < gs.length := by rw [List.length_drop] at hq; omega
      have hmem : i ∈ gs[k + 1 + q].inputs := by
        have : (gs.drop (k + 1))[q] = gs[k + 1 + q] := List.getElem_drop
        rw [← this]
        exact hi
      intro heq
      subst heq
      exact hunused (k + 1 + q) hq' (by omega) hmem
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
  have two_mem : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (a b : ℕ), a ∈ l → b ∈ l → a ≠ b →
      ∀ i ∈ l, i = a ∨ i = b := by
    intro l hl a b ha hb hab
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
    · simp at ha
    · simp at ha hb; omega
    · simp at ha hb ⊢; omega
    · simp at hl
  have expand7 : ∀ z : Fin 7 → Bool, z = ![z 0, z 1, z 2, z 3, z 4, z 5, z 6] := by
    intro z
    funext i
    fin_cases i <;> rfl
  have expand9 : ∀ z : Fin 9 → Bool, z = ![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7, z 8] := by
    intro z
    funext i
    fin_cases i <;> rfl
  have keyA0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      fF (xA ![b0, b1, b2, b3, b4, b5, b6, b7, b8]) =
        g2537 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
    decide
  have keyA : ∀ y : Fin 9 → Bool, fF (xA y) = g2537 y := by
    intro y
    rw [expand9 y]
    exact keyA0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
  have keyB0 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      fF (xB ![b0, b1, b2, b3, b4, b5, b6]) = f2832 ![b0, b1, b2, b3, b4, b5, b6] := by
    decide
  have keyB : ∀ z : Fin 7 → Bool, fF (xB z) = f2832 z := by
    intro z
    rw [expand7 z]
    exact keyB0 (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)
  have inp_len : ∀ x : Fin 9 → Bool, (inp x).length = 11 := by
    intro x
    simp [inp]
  have pair12 : ∀ i, ¬ (i = 1 ∨ i = 2 ∨ i = 10) → (inp vZ).getD i false = (inp v12).getD i false := by
    intro i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | decide
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have pair0 : ∀ i, ¬ (i = 0) → (inp v45).getD i false = (inp v045).getD i false := by
    intro i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | decide
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have pair9 : ∀ i, ¬ (i = 9) → (inp v13).getD i false = (inp v134).getD i false := by
    intro i hi
    by_cases h : i < 11
    · interval_cases i <;> first | (exfalso; omega) | decide
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
  have flip_gen : ∀ (C : Circuit), (∀ x, C.eval (inp x) = fF x) →
      ∀ (x x' : Fin 9 → Bool) (D : ℕ → Prop),
      (∀ i, ¬ D i → (inp x).getD i false = (inp x').getD i false) → fF x ≠ fF x' →
      ∀ (good : ℕ → Prop), (∀ i, good i → ¬ D i) →
      (∀ q (hq : q < C.gates.length), good (11 + q) →
        ∀ i ∈ (normGate C.gates[q]).inputs, good i ∨ 11 + q ≤ i) →
      good C.output → False := by
    intro C hall x x' D hpair hF good hG hg ho
    have h := eval_agree C good 11 (inp x) (inp x') (inp_len x) (inp_len x')
      (fun i hi => hpair i (hG i hi)) hg ho
    rw [hall, hall] at h
    exact hF h
  have invA0 : ∀ y : Fin 9 → Bool, Inv 9 (List.ofFn y) (inp (xA y)) (initA, []) := by
    intro y
    refine ⟨by simp [initA, inp], ?_⟩
    intro i
    by_cases h : i < 11
    · interval_cases i <;> simp [initA, inp, xA, svalid, sval, wiresFrom, Function.update]
    · rw [List.getD_eq_default _ _ (by simp [initA]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have invB0 : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (inp (xB z)) (initB, []) := by
    intro z
    refine ⟨by simp [initB, inp], ?_⟩
    intro i
    by_cases h : i < 11
    · interval_cases i <;> simp [initB, inp, xB, svalid, sval, wiresFrom, Function.update]
    · rw [List.getD_eq_default _ _ (by simp [initB]; omega),
        List.getD_eq_default _ _ (by rw [inp_len]; omega)]
      exact ⟨trivial, rfl⟩
  have useA : ∀ (gs' : List Gate) (out : ℕ), (∀ g ∈ gs', Ok g) →
      (∀ y : Fin 9 → Bool, (wiresFrom gs' (inp (xA y))).getD out false = g2537 y) →
      13 ≤ (elim 9 gs' (initA, [])).2.length := by
    intro gs' out hok hev
    set acc := elim 9 gs' (initA, []) with hacc
    have hinv : ∀ y : Fin 9 → Bool, Inv 9 (List.ofFn y) (wiresFrom gs' (inp (xA y))) acc :=
      fun y => inv_elim 9 (List.ofFn y) (by simp) gs' (inp (xA y)) (initA, []) hok (invA0 y)
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
  have useB : ∀ (gs' : List Gate) (out : ℕ), (∀ g ∈ gs', Ok g) →
      (∀ z : Fin 7 → Bool, (wiresFrom gs' (inp (xB z))).getD out false = f2832 z) →
      11 ≤ (elim 7 gs' (initB, [])).2.length := by
    intro gs' out hok hev
    set acc := elim 7 gs' (initB, []) with hacc
    have hinv : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (wiresFrom gs' (inp (xB z))) acc :=
      fun z => inv_elim 7 (List.ofFn z) (by simp) gs' (inp (xB z)) (initB, []) hok (invB0 z)
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
      have hfan' : FanInTwo ⟨acc.2, o⟩ := elim_ok 7 gs' (initB, []) (by simp)
      have heval' : ∀ z : Fin 7 → Bool, ({ gates := acc.2, output := o } : Circuit).eval (List.ofFn z) = f2832 z := by
        intro z
        have hs := ((hinv z).2 out).2
        rw [hst] at hs
        exact hs.trans (hev z)
      exact h2832 ⟨⟨acc.2, o⟩, hfan', by rw [sizeEq]; exact hle, heval'⟩
  dsimp only
  intro C hfan hsize hall
  let gs := C.gates.map normGate
  have hglen : gs.length = C.gates.length := List.length_map _
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (hfan _ hg0)
  have hok_gs : ∀ g ∈ gs, Ok g := fun g hg => (normOk g hg).1
  have hevA_gs : ∀ y : Fin 9 → Bool, (wiresFrom gs (inp (xA y))).getD C.output false = g2537 y := by
    intro y
    change (wiresFrom (C.gates.map normGate) (inp (xA y))).getD C.output false = g2537 y
    rw [wiresFrom_norm]
    exact (hall (xA y)).trans (keyA y)
  have hevB_gs : ∀ z : Fin 7 → Bool, (wiresFrom gs (inp (xB z))).getD C.output false = f2832 z := by
    intro z
    change (wiresFrom (C.gates.map normGate) (inp (xB z))).getD C.output false = f2832 z
    rw [wiresFrom_norm]
    exact (hall (xB z)).trans (keyB z)
  have h13A : 13 ≤ (elim 9 gs (initA, [])).2.length := useA gs C.output hok_gs hevA_gs
  have hsz_eq : C.size = 13 := by
    have hle := elim_len_le 9 gs (initA, [])
    simp only [List.length_nil, Nat.zero_add, hglen] at hle
    rw [sizeEq] at hsize ⊢
    omega
  have hclen : C.gates.length = 13 := by rw [← sizeEq]; exact hsz_eq
  have h11B : 11 ≤ (elim 7 gs (initB, [])).2.length := useB gs C.output hok_gs hevB_gs
  have hno_dropA : ∀ p (hp : p < gs.length),
      (simplify gs[p].op (9 + (elim 9 (gs.take p) (initA, [])).2.length)
        (gs[p].inputs.map fun i => (elim 9 (gs.take p) (initA, [])).1.getD i (Sum.inl false))).1 ≠ none := by
    intro p hp hnone
    have hs : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
      rw [List.getElem_cons_drop]
      exact (List.take_append_drop p gs).symm
    have hdrop := elim_drop_one 9 (gs.take p) gs[p] (gs.drop (p + 1)) (initA, []) hnone
    rw [← hs] at hdrop
    simp only [List.length_nil, Nat.zero_add, hglen, hclen] at hdrop
    omega
  have hno4 : ∀ g ∈ C.gates, ¬ rd g 4 := by
    intro g hg hrd
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hg
    have hp' : p < gs.length := by omega
    have hmem : 4 ∈ gs[p].inputs := by
      have : gs[p] = normGate C.gates[p] := by simp [gs]
      rw [this]
      exact (rd_iff_norm _ 4 (hfan _ (List.getElem_mem hp))).1 hrd
    have h4 : (elim 9 (gs.take p) (initA, [])).1.getD 4 (Sum.inl false) = Sum.inl false := by
      rw [elim_getD 9 4 _ _ _ (by simp [initA])]; rfl
    apply hno_dropA p hp'
    have hnok := normOk gs[p] (List.getElem_mem hp')
    exact simplify_count gs[p].op _ _ hnok.1.1 (by simpa using hnok.1.2)
      (fun h => by simpa using hnok.2 h) ⟨false, List.mem_map.2 ⟨4, hmem, h4⟩⟩
  have hno09 : ∀ p (hp : p < C.gates.length),
      ¬ (0 ∈ (normGate C.gates[p]).inputs ∧ 9 ∈ (normGate C.gates[p]).inputs) := by
    intro p hp h09
    have h0 := h09.1
    have h9 := h09.2
    have hp' : p < gs.length := by omega
    have hgp : gs[p] = normGate C.gates[p] := by simp [gs]
    have hnok := normOk gs[p] (List.getElem_mem hp')
    rw [hgp] at hnok
    have hnot_not : (normGate C.gates[p]).op ≠ GateOp.not := by
      intro hnt
      have hl1 := hnok.2 hnt
      rcases h1 : (normGate C.gates[p]).inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rw [h1] at h0; simp at h0
      · rw [h1] at h0 h9; simp at h0 h9; omega
      · rw [h1] at hl1; simp at hl1
    have htwo : (normGate C.gates[p]).inputs = [0, 9] ∨ (normGate C.gates[p]).inputs = [9, 0] := by
      have hl2 := hnok.1.2
      rcases h1 : (normGate C.gates[p]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rw [h1] at h0; simp at h0
      · rw [h1] at h0 h9; simp at h0 h9; omega
      · rw [h1] at h0 h9
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9
        rcases h0 with rfl | rfl <;> rcases h9 with h9 | h9 <;> first | omega | (subst h9; simp)
      · rw [h1] at hl2; simp at hl2
    have h0v : (elim 9 (gs.take p) (initA, [])).1.getD 0 (Sum.inl false) = Sum.inr 0 := by
      rw [elim_getD 9 0 _ _ _ (by simp [initA])]; rfl
    have h9v : (elim 9 (gs.take p) (initA, [])).1.getD 9 (Sum.inl false) = Sum.inr 0 := by
      rw [elim_getD 9 9 _ _ _ (by simp [initA])]; rfl
    apply hno_dropA p hp'
    rw [hgp]
    rcases hnok.1.1 with hop | hop | hop
    · have : (normGate C.gates[p]).op = GateOp.and := hop
      rw [this]
      rcases htwo with hi | hi <;> (rw [hi]; simp only [List.map_cons, List.map_nil, h0v, h9v]; rfl)
    · have : (normGate C.gates[p]).op = GateOp.or := hop
      rw [this]
      rcases htwo with hi | hi <;> (rw [hi]; simp only [List.map_cons, List.map_nil, h0v, h9v]; rfl)
    · exact absurd hop hnot_not
  have hdead : ∀ k (hk : k < C.gates.length), C.output ≠ 11 + k →
      ∃ m, ∃ hm : m < C.gates.length, k < m ∧ 11 + k ∈ (normGate C.gates[m]).inputs := by
    intro k hk hneout
    by_contra hnu
    push_neg at hnu
    have hk' : k < gs.length := by omega
    let gs' := gs.take k ++ ⟨GateOp.and, []⟩ :: gs.drop (k + 1)
    have hok' : ∀ g ∈ gs', Ok g := by
      intro g hg
      simp only [gs', List.mem_append, List.mem_cons] at hg
      rcases hg with h1 | rfl | h1
      · exact hok_gs g (List.mem_of_mem_take h1)
      · exact ⟨Or.inl rfl, by simp⟩
      · exact hok_gs g (List.mem_of_mem_drop h1)
    have hev' : ∀ y : Fin 9 → Bool, (wiresFrom gs' (inp (xA y))).getD C.output false = g2537 y := by
      intro y
      have hrep := replace_unused gs k hk' ⟨GateOp.and, []⟩ (inp (xA y)) (by
        intro q hq hkq
        have hq' : q < C.gates.length := by omega
        rw [inp_len, show gs[q] = normGate C.gates[q] by simp [gs]]
        exact hnu q hq' hkq) C.output (by rw [inp_len]; exact hneout)
      exact hrep.trans (hevA_gs y)
    have hge13 := useA gs' C.output hok' hev'
    have hdrop := elim_drop_one 9 (gs.take k) ⟨GateOp.and, []⟩ (gs.drop (k + 1)) (initA, []) rfl
    have hlen' : gs'.length = 13 := by
      simp only [gs', List.length_append, List.length_cons, List.length_take, List.length_drop]
      omega
    simp only [List.length_nil, Nat.zero_add] at hdrop
    change (elim 9 gs' (initA, [])).2.length + 1 ≤ gs'.length at hdrop
    omega
  have outc := flip_gen C hall vZ v12 (fun i => i = 1 ∨ i = 2 ∨ i = 10) pair12 (by decide)
  have flip0 := flip_gen C hall v45 v045 (fun i => i = 0) pair0 (by decide)
  have flip9 := flip_gen C hall v13 v134 (fun i => i = 9) pair9 (by decide)
  have hread0 : ∃ i0 : Fin C.gates.length, 0 ∈ (normGate C.gates[i0.val]).inputs := by
    by_contra hn
    push_neg at hn
    by_cases ho : C.output = 0
    · exact outc (fun i => i = 0) (by intro i hi; omega) (by intro q hq h; omega) ho
    · refine flip0 (fun i => i ≠ 0) (fun i hi => hi) ?_ ho
      intro q hq _ i hi
      left
      rintro rfl
      exact hn ⟨q, hq⟩ hi
  have hread9 : ∃ i9 : Fin C.gates.length, 9 ∈ (normGate C.gates[i9.val]).inputs := by
    by_contra hn
    push_neg at hn
    by_cases ho : C.output = 9
    · exact outc (fun i => i = 9) (by intro i hi; omega) (by intro q hq h; omega) ho
    · refine flip9 (fun i => i ≠ 9) (fun i hi => hi) ?_ ho
      intro q hq _ i hi
      left
      rintro rfl
      exact hn ⟨q, hq⟩ hi
  obtain ⟨i0, hi0⟩ := hread0
  obtain ⟨i9, hi9⟩ := hread9
  have hne09 : i0 ≠ i9 := by
    intro heq
    subst heq
    exact hno09 i0.val i0.isLt ⟨hi0, hi9⟩
  let accB := elim 7 gs (initB, [])
  have hgget : ∀ q (hq : q < C.gates.length), gs[q]? = some (normGate C.gates[q]) := by
    intro q hq
    simp [gs, hq]
  have hB0 : accB.1.getD 0 (Sum.inl false) = Sum.inl false := by
    rw [show accB = elim 7 gs (initB, []) from rfl, elim_getD 7 0 _ _ _ (by simp [initB])]; rfl
  have hB9 : accB.1.getD 9 (Sum.inl false) = Sum.inl false := by
    rw [show accB = elim 7 gs (initB, []) from rfl, elim_getD 7 9 _ _ _ (by simp [initB])]; rfl
  have hcard_le2 : ∀ S : Finset ℕ,
      (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < 11 + p ∧
        ∃ c, accB.1.getD a (Sum.inl false) = Sum.inl c) → S.card ≤ 2 := by
    intro S hS
    have hcnt := elim_count 7 (initB, []) gs normOk S hS
    simp only [List.length_nil, Nat.zero_add, hglen, hclen] at hcnt
    have h11B' : 11 ≤ accB.2.length := h11B
    change accB.2.length + S.card ≤ 13 at hcnt
    omega
  have hmem_i0 : ∃ g, gs[i0.val]? = some g ∧ ∃ a ∈ g.inputs, a < 11 + i0.val ∧
      ∃ c, accB.1.getD a (Sum.inl false) = Sum.inl c :=
    ⟨normGate C.gates[i0.val], hgget i0.val i0.isLt, 0, hi0, by omega, false, hB0⟩
  have hmem_i9 : ∃ g, gs[i9.val]? = some g ∧ ∃ a ∈ g.inputs, a < 11 + i9.val ∧
      ∃ c, accB.1.getD a (Sum.inl false) = Sum.inl c :=
    ⟨normGate C.gates[i9.val], hgget i9.val i9.isLt, 9, hi9, by omega, false, hB9⟩
  have huniq0 : ∀ j : Fin C.gates.length, rd (C.gates.get j) 0 ↔ j = i0 := by
    intro j
    rw [List.get_eq_getElem, rd_iff_norm _ 0 (hfan _ (List.getElem_mem j.isLt))]
    constructor
    · intro hj0
      by_contra hjne
      have hjne9 : j.val ≠ i9.val := by
        intro heq
        have hj9 : 9 ∈ (normGate C.gates[j.val]).inputs := by
          have : j = i9 := Fin.ext heq
          subst this; exact hi9
        exact hno09 j.val j.isLt ⟨hj0, hj9⟩
      have hne0 : j.val ≠ i0.val := fun h => hjne (Fin.ext h)
      have hne09v : i0.val ≠ i9.val := fun h => hne09 (Fin.ext h)
      have h3 : ({i0.val, i9.val, j.val} : Finset ℕ).card ≤ 2 := by
        apply hcard_le2
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact hmem_i0
        · exact hmem_i9
        · exact ⟨normGate C.gates[j.val], hgget j.val j.isLt, 0, hj0, by omega, false, hB0⟩
      rw [Finset.card_insert_of_notMem (by simp [hne09v, Ne.symm hne0]),
        Finset.card_pair (Ne.symm hjne9)] at h3
      omega
    · rintro rfl; exact hi0
  have huniq9 : ∀ j : Fin C.gates.length, rd (C.gates.get j) 9 ↔ j = i9 := by
    intro j
    rw [List.get_eq_getElem, rd_iff_norm _ 9 (hfan _ (List.getElem_mem j.isLt))]
    constructor
    · intro hj9
      by_contra hjne
      have hjne0 : j.val ≠ i0.val := by
        intro heq
        have hj0 : 0 ∈ (normGate C.gates[j.val]).inputs := by
          have : j = i0 := Fin.ext heq
          subst this; exact hi0
        exact hno09 j.val j.isLt ⟨hj0, hj9⟩
      have hne9 : j.val ≠ i9.val := fun h => hjne (Fin.ext h)
      have hne09v : i0.val ≠ i9.val := fun h => hne09 (Fin.ext h)
      have h3 : ({i0.val, i9.val, j.val} : Finset ℕ).card ≤ 2 := by
        apply hcard_le2
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact hmem_i0
        · exact hmem_i9
        · exact ⟨normGate C.gates[j.val], hgget j.val j.isLt, 9, hj9, by omega, false, hB9⟩
      rw [Finset.card_insert_of_notMem (by simp [hne09v, Ne.symm hjne0]),
        Finset.card_pair (Ne.symm hne9)] at h3
      omega
    · rintro rfl; exact hi9
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
      have hinv : ∀ z : Fin 7 → Bool, Inv 7 (List.ofFn z) (wiresFrom gs (inp (xB z))) accB :=
        fun z => inv_elim 7 (List.ofFn z) (by simp) gs (inp (xB z)) (initB, []) hok_gs (invB0 z)
      have h0 : f2832 ![false, false, false, false, false, false, false] = ck := by
        rw [← hevB_gs, ← ((hinv _).2 C.output).2, hout, hck]; rfl
      have h1 : f2832 ![true, true, false, false, false, false, false] = ck := by
        rw [← hevB_gs, ← ((hinv _).2 C.output).2, hout, hck]; rfl
      have hne : f2832 ![false, false, false, false, false, false, false] ≠
          f2832 ![true, true, false, false, false, false, false] := by decide
      exact hne (h0.trans h1.symm)
    obtain ⟨m, hm, hkm, hmk⟩ := hdead k hklt hkne_out
    have hmn0 : m ≠ i0.val := by
      intro heq
      have hm0 : 0 ∈ (normGate C.gates[m]).inputs := by
        simp only [heq]; exact hi0
      have hm' : m < gs.length := by omega
      have hst := elim_gate_stat 7 gs (initB, []) m hm'
      have hl11 : (initB, ([] : List Gate)).1.length = 11 := rfl
      rw [hl11] at hst
      have hconstm : ∃ cm, accB.1.getD (11 + m) (Sum.inl false) = Sum.inl cm := by
        rw [show accB = elim 7 gs (initB, []) from rfl, hst]
        apply simplify_const
        intro s hs
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
        have hgm : gs[m] = normGate C.gates[m] := by simp [gs]
        rw [hgm] at ha
        have hlen2 := (normGate_nok _ (hfan _ (List.getElem_mem hm))).1.2
        rcases two_mem _ hlen2 0 (11 + k) hm0 hmk (by omega) a ha with rfl | rfl
        · rw [elim_getD 7 0 _ _ _ (by simp [initB])]; exact ⟨false, rfl⟩
        · have hpre : (elim 7 (gs.take m) (initB, [])).1.getD (11 + k) (Sum.inl false) =
              accB.1.getD (11 + k) (Sum.inl false) := by
            have hs' : gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
              rw [List.getElem_cons_drop]
              exact (List.take_append_drop m gs).symm
            conv_rhs => rw [show accB = elim 7 gs (initB, []) from rfl, hs']
            rw [elim_split_getD_lt 7 (gs.take m) gs[m] (gs.drop (m + 1)) (initB, []) (11 + k) _ (by
              rw [List.length_take]; simp [initB]; omega)]
          rw [hpre, hck]; exact ⟨ck, rfl⟩
      have hmK : m ∈ K := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hconstm⟩
      have hle := Finset.le_max' K m hmK
      omega
    have hmn9 : m ≠ i9.val := by
      intro heq
      have hm9 : 9 ∈ (normGate C.gates[m]).inputs := by
        simp only [heq]; exact hi9
      have hm' : m < gs.length := by omega
      have hst := elim_gate_stat 7 gs (initB, []) m hm'
      have hl11 : (initB, ([] : List Gate)).1.length = 11 := rfl
      rw [hl11] at hst
      have hconstm : ∃ cm, accB.1.getD (11 + m) (Sum.inl false) = Sum.inl cm := by
        rw [show accB = elim 7 gs (initB, []) from rfl, hst]
        apply simplify_const
        intro s hs
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
        have hgm : gs[m] = normGate C.gates[m] := by simp [gs]
        rw [hgm] at ha
        have hlen2 := (normGate_nok _ (hfan _ (List.getElem_mem hm))).1.2
        rcases two_mem _ hlen2 9 (11 + k) hm9 hmk (by omega) a ha with rfl | rfl
        · rw [elim_getD 7 9 _ _ _ (by simp [initB])]; exact ⟨false, rfl⟩
        · have hpre : (elim 7 (gs.take m) (initB, [])).1.getD (11 + k) (Sum.inl false) =
              accB.1.getD (11 + k) (Sum.inl false) := by
            have hs' : gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
              rw [List.getElem_cons_drop]
              exact (List.take_append_drop m gs).symm
            conv_rhs => rw [show accB = elim 7 gs (initB, []) from rfl, hs']
            rw [elim_split_getD_lt 7 (gs.take m) gs[m] (gs.drop (m + 1)) (initB, []) (11 + k) _ (by
              rw [List.length_take]; simp [initB]; omega)]
          rw [hpre, hck]; exact ⟨ck, rfl⟩
      have hmK : m ∈ K := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hconstm⟩
      have hle := Finset.le_max' K m hmK
      omega
    have hne09v : i0.val ≠ i9.val := fun h => hne09 (Fin.ext h)
    have h3 : ({i0.val, i9.val, m} : Finset ℕ).card ≤ 2 := by
      apply hcard_le2
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | hp3
      · exact hmem_i0
      · exact hmem_i9
      · rw [hp3]; exact ⟨normGate C.gates[m], hgget m hm, 11 + k, hmk, by omega, ck, hck⟩
    rw [Finset.card_insert_of_notMem (by simp [hne09v, Ne.symm hmn0]),
      Finset.card_pair (Ne.symm hmn9)] at h3
    omega
  have hop_or : ∀ (p : Fin C.gates.length) (w : ℕ),
      w ∈ (normGate C.gates[p.val]).inputs →
      (elim 7 (gs.take p.val) (initB, [])).1.getD w (Sum.inl false) = Sum.inl false →
      (C.gates.get p).op = GateOp.or := by
    intro p w hwin hwval
    rw [List.get_eq_getElem]
    have hokp := hfan C.gates[p.val] (List.getElem_mem p.isLt)
    have hp' : p.val < gs.length := by omega
    have hst := elim_gate_stat 7 gs (initB, []) p.val hp'
    have hl11 : (initB, ([] : List Gate)).1.length = 11 := rfl
    rw [hl11] at hst
    have hgp : gs[p.val] = normGate C.gates[p.val] := by simp [gs]
    rw [hgp] at hst
    have hmem_false : Sum.inl false ∈ (normGate C.gates[p.val]).inputs.map
        (fun i => (elim 7 (gs.take p.val) (initB, [])).1.getD i (Sum.inl false)) :=
      List.mem_map.2 ⟨w, hwin, hwval⟩
    rcases hokp.1 with hop | hop | hop
    · exfalso
      have h1 : C.gates[p.val].op = GateOp.and := hop
      have h2 : (normGate C.gates[p.val]).op = GateOp.and := by
        cases hcg : C.gates[p.val] with
        | mk op ins => rw [hcg] at h1; dsimp only at h1; subst h1; rfl
      have hlen2 : ((normGate C.gates[p.val]).inputs.map
          (fun i => (elim 7 (gs.take p.val) (initB, [])).1.getD i (Sum.inl false))).length ≤ 2 := by
        simpa using (normGate_nok _ hokp).1.2
      rw [h2] at hst
      set ins := (normGate C.gates[p.val]).inputs.map
        (fun i => (elim 7 (gs.take p.val) (initB, [])).1.getD i (Sum.inl false)) with hins
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
          (fun i => (elim 7 (gs.take p.val) (initB, [])).1.getD i (Sum.inl false))).length ≤ 1 := by
        simpa using (normGate_nok _ hokp).2 h2
      rw [h2] at hst
      set ins := (normGate C.gates[p.val]).inputs.map
        (fun i => (elim 7 (gs.take p.val) (initB, [])).1.getD i (Sum.inl false)) with hins
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at hmem_false
      · simp only [List.mem_singleton] at hmem_false
        subst hmem_false
        simp only [simplify, simpNot, Bool.not_false] at hst
        exact hnoConstB p.val p.isLt true hst
      · simp at hlen1
  have hop0 : (C.gates.get i0).op = GateOp.or :=
    hop_or i0 0 hi0 (by rw [elim_getD 7 0 _ _ _ (by simp [initB])]; rfl)
  have hop9 : (C.gates.get i9).op = GateOp.or :=
    hop_or i9 9 hi9 (by rw [elim_getD 7 9 _ _ _ (by simp [initB])]; rfl)
  exact hCore C hfan hsz_eq hno4 ⟨i0, i9, hne09, hop0, hop9, huniq0, huniq9⟩ hall
