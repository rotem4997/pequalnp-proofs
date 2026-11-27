import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The gate elimination argument adapts L-meta-2038 and L-meta-551.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3590_1 :
    (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)) 12) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) → ¬((x2 = 4 ∧ x3 ∈ ([6,7,8] : List (Fin 10))) ∨ (x3 = 4 ∧ x2 ∈ ([2,3] : List (Fin 10)))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size := by
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    clear * - wiresFrom wiresFrom_cons gs₁ gs₂ w
    induction gs₁ generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

  have wiresFrom_length (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    clear * - wiresFrom wiresFrom_cons gs w
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      rw [wiresFrom_cons, ih]
      simp
      omega

  have getD_snoc_lt {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    clear * - α l x d i hi
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    clear * - α l x d i hi
    subst hi
    simp [List.getD]

  have getD_snoc_ne {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    clear * - getD_snoc_lt α l x d i hi
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    clear * - wiresFrom wiresFrom_cons getD_snoc_lt gs w i hi
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [wiresFrom_cons, ih _ (by simp; omega)]
      exact getD_snoc_lt _ _ _ _ hi

  let OkGate (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  let NOkGate (g : Gate) : Prop :=
    OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

  let normGate (g : Gate) : Gate :=
    GateOp.rec (motive := fun _ => Gate) g g ⟨GateOp.not, g.inputs.take 1⟩
      (fun _ => g) g g.op

  have evalAnd (v : List Bool) : GateOp.and.eval v = v.all id := rfl
  have evalOr (v : List Bool) : GateOp.or.eval v = v.any id := rfl
  have evalNot (v : List Bool) : GateOp.not.eval v = !(v.headD false) := rfl

  have normGate_eval (g : Gate) (F : ℕ → Bool) :
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    clear * - normGate evalNot g F
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp only [normGate]
    cases inputs <;> simp [evalNot]

  have normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
    clear * - OkGate NOkGate normGate g h
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hlen⟩ := h
    rcases hop with h | h | h
    · have : op = GateOp.and := h
      subst this
      exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.or := h
      subst this
      exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
    · have : op = GateOp.not := h
      subst this
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
      · simp [normGate]
      · simp [normGate]

  have wiresFrom_norm (gs : List Gate) (w : List Bool) :
      wiresFrom (gs.map normGate) w = wiresFrom gs w := by
    clear * - wiresFrom wiresFrom_cons normGate normGate_eval gs w
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

  let statVal (w : List Bool) (s : Bool ⊕ ℕ) : Bool :=
    Sum.elim id (fun j => w.getD j false) s

  let statValid (m : ℕ) (s : Bool ⊕ ℕ) : Prop :=
    Sum.elim (fun _ => True) (fun j => j < m) s

  let simpNot (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    List.casesOn ins (none, Sum.inl true) (fun a _ =>
      Sum.elim (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)) a)

  let simpAnd (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    List.casesOn ins (none, Sum.inl true) (fun a rest =>
      List.casesOn rest (none, a) (fun b tail =>
        List.casesOn tail
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c && d)))
              (fun j => (none, bif c then Sum.inr j else Sum.inl false)) b)
            (fun i => Sum.elim (fun d => (none, bif d then Sum.inr i else Sum.inl false))
              (fun j => (some ⟨GateOp.and, [i, j]⟩, Sum.inr m)) b) a)
          (fun _ _ => (none, Sum.inl false))))

  let simpOr (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
    List.casesOn ins (none, Sum.inl false) (fun a rest =>
      List.casesOn rest (none, a) (fun b tail =>
        List.casesOn tail
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (c || d)))
              (fun j => (none, bif c then Sum.inl true else Sum.inr j)) b)
            (fun i => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr i))
              (fun j => (some ⟨GateOp.or, [i, j]⟩, Sum.inr m)) b) a)
          (fun _ _ => (none, Sum.inl false))))

  let simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
      Option Gate × (Bool ⊕ ℕ) :=
    GateOp.rec (motive := fun _ => Option Gate × (Bool ⊕ ℕ))
      (simpAnd m ins) (simpOr m ins) (simpNot m ins) (fun _ => (none, Sum.inl false))
      (none, Sum.inl false) op

  have simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
      ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
    clear * - OkGate simpNot simpAnd simpOr simplifyGate op m ins
    intro g hg
    cases op <;> simp only [simplifyGate] at hg
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpAnd] at hg
      subst hg; simp [OkGate]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpOr] at hg
      subst hg; simp [OkGate]
    · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
        simp [simpNot] at hg
      subst hg; simp [OkGate]
    · simp at hg
    · simp at hg

  have simplifyGate_sound (op : GateOp)
      (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
      (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, statValid w.length s) :
      statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
        (simplifyGate op w.length ins).2 ∧
      statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
        (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
    clear * - wiresFrom statVal statValid simpNot simpAnd simpOr simplifyGate evalAnd evalOr evalNot op hop w ins hlen hv
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplifyGate, simpAnd, statValid, statVal, evalAnd]
      · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, wiresFrom]
      · cases a with
        | inl c =>
          cases b with
          | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal]
          | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, wiresFrom]
        | inr i =>
          cases b with
          | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, wiresFrom]
          | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplifyGate, simpOr, statValid, statVal, evalOr]
      · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, wiresFrom]
      · cases a with
        | inl c =>
          cases b with
          | inl d => simp_all [simplifyGate, simpOr, statValid, statVal]
          | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, wiresFrom]
        | inr i =>
          cases b with
          | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, wiresFrom]
          | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · simp [simplifyGate, simpNot, statValid, statVal, evalNot]
      · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, wiresFrom]

  let elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate :=
    let r := simplifyGate g.op (m + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

  let elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
      List (Bool ⊕ ℕ) × List Gate :=
    gs.foldl (elimStep m) acc

  have elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
      (acc : List (Bool ⊕ ℕ) × List Gate) :
      elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

  have toList_opt_len_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
    clear * - α o
    cases o <;> simp

  have elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
    clear * - OkGate simplifyGate_ok elimPass elimPass_cons m gs acc h
    induction gs generalizing acc with
    | nil => exact h
    | cons g gs ih =>
      rw [elimPass_cons]
      apply ih
      intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

  let ElimInv (m : ℕ) (w_in w_old : List Bool)
      (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
    w_in.length = m ∧
    acc.1.length = w_old.length ∧
    ∀ i : ℕ,
      statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

  have elimInv_step (m : ℕ) (w_in w_old : List Bool)
      (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
      (hinv : ElimInv m w_in w_old acc) :
      ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
        (elimStep m acc g) := by
    clear * - wiresFrom wiresFrom_append wiresFrom_length getD_snoc_eq getD_snoc_ne wiresFrom_getD_lt OkGate statVal statValid simplifyGate_sound elimStep ElimInv m w_in w_old acc g hok hinv
    obtain ⟨hwin, hlen, hi⟩ := hinv
    set w_new := wiresFrom acc.2 w_in with hw_new
    have hw_len : w_new.length = m + acc.2.length := by
      rw [hw_new, wiresFrom_length, hwin]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
    have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
      intro s hs
      obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
      rw [hw_len]
      exact (hi idx).1
    have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
    rw [hw_len] at hsound
    refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
    intro i
    simp only [elimStep]
    by_cases hieq : i = acc.1.length
    · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, ← Nat.add_assoc]
        exact hsound.1
      · rw [wiresFrom_append, ← hw_new, hsound.2]
        congr 1
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro idx _
        exact (hi idx).2
    · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
      have hv := (hi i).1
      have hval := (hi i).2
      refine ⟨?_, ?_⟩
      · cases hst : acc.1.getD i (Sum.inl false) with
        | inl c => trivial
        | inr j =>
          rw [hst] at hv
          simp only [statValid, Sum.elim_inr, List.length_append] at hv ⊢
          omega
      · cases hst : acc.1.getD i (Sum.inl false) with
        | inl c =>
          rw [hst] at hval
          exact hval
        | inr j =>
          rw [hst] at hv hval
          simp only [statValid, Sum.elim_inr] at hv
          simp only [statVal, Sum.elim_inr] at hval ⊢
          rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
          exact hval

  have elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
      (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
      (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
      ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
    clear * - wiresFrom wiresFrom_cons OkGate elimPass elimPass_cons ElimInv elimInv_step m w_in gs w_old acc hok hinv
    induction gs generalizing w_old acc with
    | nil => exact hinv
    | cons g gs ih =>
      rw [wiresFrom_cons, elimPass_cons]
      exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

  let touches (g : Gate) : Bool :=
    g.inputs.contains 4

  have simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
      (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
      (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
      (simplifyGate op m ins).1 = none := by
    clear * - simpNot simpAnd simpOr simplifyGate op m ins hop hlen hnot hc
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplifyGate, simpAnd]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplifyGate, simpOr]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

  have elimPass_count (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
      (h : ∀ g ∈ gs, NOkGate g)
      (h4 : acc.1.getD 4 (Sum.inl false) = Sum.inl false)
      (ha : 4 < acc.1.length) :
      (elimPass n gs acc).2.length + gs.countP touches ≤ acc.2.length + gs.length := by
    clear * - getD_snoc_lt NOkGate simplifyGate elimStep elimPass elimPass_cons toList_opt_len_le touches simplifyGate_none_of_const n gs acc h h4 ha
    induction gs generalizing acc with
    | nil => simp [elimPass]
    | cons g gs ih =>
      have h4' : (elimStep n acc g).1.getD 4 (Sum.inl false) = Sum.inl false := by
        unfold elimStep
        rw [getD_snoc_lt _ _ _ _ (by omega), h4]
      have ha' : 4 < (elimStep n acc g).1.length := by simp [elimStep]; omega
      have ht := ih (elimStep n acc g) (fun a hm => h a (List.mem_cons_of_mem _ hm)) h4' ha'
      let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
      let part := simplifyGate g.op (n + acc.2.length) ins
      have hb : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        change (acc.2 ++ part.1.toList).length ≤ _
        rw [List.length_append]
        exact Nat.add_le_add_left (toList_opt_len_le _) _
      rw [elimPass_cons, List.countP_cons, List.length_cons]
      cases he : touches g with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      | true =>
        have hn : part.1 = none := by
          have hg := h g List.mem_cons_self
          apply simplifyGate_none_of_const _ _ _ hg.1.1
          · simpa [ins] using hg.1.2
          · intro hn
            simpa [ins] using hg.2 hn
          · have hi : 4 ∈ g.inputs := by simpa [touches] using he
            exact ⟨false, List.mem_map.mpr ⟨4, hi, h4⟩⟩
        have hd : (elimStep n acc g).2.length = acc.2.length := by
          change (acc.2 ++ part.1.toList).length = _
          simp [hn]
        simp only [↓reduceIte]
        omega

  let fixedInput (q : Fin 8) (x : Fin 8 → Bool) (z : Bool) : List Bool :=
    [x 0, x 1, x 2, x 3, z, x 4, x 5, x 6, x 7, x 0, x q]

  let initial (q : Fin 8) : List (Bool ⊕ ℕ) × List Gate :=
    ([Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
      Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, Sum.inr q.val], [])

  have first_inv (q : Fin 8) (x : Fin 8 → Bool) :
      ElimInv 8 (List.ofFn x) (fixedInput q x false) (initial q) := by
    clear * - wiresFrom_nil statVal statValid ElimInv fixedInput initial q x
    refine ⟨List.length_ofFn, rfl, ?_⟩
    intro i
    by_cases hi : i < 11
    · interval_cases i <;> simp [initial, fixedInput, statValid, statVal, wiresFrom_nil, List.getD]
      · fin_cases q <;> rfl
    · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
        List.getD_eq_default _ _ (by simp [fixedInput]; omega)]
      exact ⟨trivial, rfl⟩

  have remove (C : Circuit) (q : Fin 8) (hfan : FanInTwo C)
      (hcount : 1 ≤ (C.gates.map normGate).countP touches)
      (hfalse : ∃ x : Fin 8 → Bool, C.eval (fixedInput q x false) = false) :
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (fixedInput q x false) := by
    clear * - wiresFrom NOkGate normGate normGate_nok wiresFrom_norm statVal elimPass elimPass_ok elimInv_pass touches elimPass_count fixedInput initial first_inv C q hfan hcount hfalse
    let gs := C.gates.map normGate
    have hnok : ∀ g ∈ gs, NOkGate g := by
      intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact normGate_nok a (hfan a ha)
    let acc := elimPass 8 gs (initial q)
    have hs : acc.2.length + 1 ≤ C.size := by
      have ht := elimPass_count 8 gs (initial q) hnok rfl (by simp [initial])
      change acc.2.length + gs.countP touches ≤ 0 + gs.length at ht
      have hl : gs.length = C.size := List.length_map _
      change 1 ≤ gs.countP touches at hcount
      omega
    have hv (x : Fin 8 → Bool) :
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          C.eval (fixedInput q x false) := by
      have hr := ((elimInv_pass 8 (List.ofFn x) gs (fixedInput q x false) (initial q)
        (fun g hg => (hnok g hg).1) (first_inv q x)).2.2 C.output).2
      show _ = (wiresFrom C.gates (fixedInput q x false)).getD C.output false
      exact hr.trans (congrArg (fun w => w.getD C.output false)
        (wiresFrom_norm C.gates (fixedInput q x false)))
    cases ho : acc.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | false =>
        refine ⟨⟨[], 8⟩, fun _ hg => False.elim (List.not_mem_nil hg), by change 0 + 1 ≤ C.size; omega, ?_⟩
        intro x
        have hx := hv x
        rw [ho] at hx
        rw [← hx]
        change (List.ofFn x).getD 8 false = false
        exact List.getD_eq_default _ _ (by simp)
      | true =>
        obtain ⟨x, hx⟩ := hfalse
        have hh := hv x
        rw [ho, hx] at hh
        contradiction
    | inr i =>
      refine ⟨⟨acc.2, i⟩, elimPass_ok 8 gs _ (by simp [initial]), hs, ?_⟩
      intro x
      have hx := hv x
      rw [ho] at hx
      exact hx

  have unaffected (gs : List Gate) (u v : List Bool) (hsize : u.length = v.length)
      (diff : ∀ k, k ≠ 4 → u.getD k false = v.getD k false)
      (noReads : ∀ g ∈ gs, 4 ∉ g.inputs) (k : ℕ) (hk : k ≠ 4) :
      (wiresFrom gs u).getD k false = (wiresFrom gs v).getD k false := by
    clear * - wiresFrom wiresFrom_cons getD_snoc_eq getD_snoc_ne gs u v hsize diff noReads k hk
    induction gs generalizing u v with
    | nil => exact diff k hk
    | cons g gs ih =>
      have hagree :
          g.inputs.map (fun j => u.getD j false) = g.inputs.map (fun j => v.getD j false) := by
        apply List.map_congr_left
        intro j hj
        exact diff j (fun h => noReads g (by simp) (h ▸ hj))
      rw [wiresFrom_cons, wiresFrom_cons, hagree]
      apply ih
      · simp [hsize]
      · intro j hj
        by_cases hlast : j = u.length
        · rw [getD_snoc_eq _ _ _ _ hlast, getD_snoc_eq _ _ _ _ (hlast.trans hsize)]
        · rw [getD_snoc_ne _ _ _ _ hlast, getD_snoc_ne _ _ _ _ (by simpa [hsize] using hlast)]
          exact diff j hj
      · intro a ha
        exact noReads a (List.mem_cons_of_mem _ ha)

  have fixedInput_same (q : Fin 8) (x : Fin 8 → Bool) (k : ℕ) (hk : k ≠ 4) :
      (fixedInput q x false).getD k false = (fixedInput q x true).getD k false := by
    clear * - fixedInput q x k hk
    by_cases hi : k < 11
    · interval_cases k <;> simp_all [fixedInput, List.getD]
    · rw [List.getD_eq_default _ _ (by simp [fixedInput]; omega),
        List.getD_eq_default _ _ (by simp [fixedInput]; omega)]

  have mustRead (C : Circuit) (q : Fin 8) (x : Fin 8 → Bool)
      (hout : C.output ≠ 4)
      (hne : C.eval (fixedInput q x false) ≠ C.eval (fixedInput q x true)) :
      1 ≤ (C.gates.map normGate).countP touches := by
    clear * - normGate wiresFrom_norm touches fixedInput unaffected fixedInput_same C q x hout hne
    by_contra! h
    have hz : (C.gates.map normGate).countP touches = 0 := by omega
    have hc : ∀ g ∈ C.gates.map normGate, 4 ∉ g.inputs := by
      intro g hg
      have hf := List.countP_eq_zero.mp hz g hg
      simpa [touches] using hf
    have he := unaffected (C.gates.map normGate) (fixedInput q x false) (fixedInput q x true)
      rfl (fixedInput_same q x) hc C.output hout
    rw [wiresFrom_norm, wiresFrom_norm] at he
    exact hne he

  let graph8 (x : Fin 8 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)

  let graph9 (x : Fin 9 → Bool) : Bool :=
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
      (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)

  let insertFour (x : Fin 8 → Bool) (b : Bool) : Fin 9 → Bool :=
    ![x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7]

  let withOrs (a b : Fin 10) (x : Fin 9 → Bool) : List Bool :=
    let w := List.ofFn x ++ [x 0 || x 4]
    w ++ [w.getD a.val false || w.getD b.val false]

  let test (q : Fin 8) : Fin 8 → Bool := fun i => i == 0 || i == q

  have restriction (x : Fin 8 → Bool) : graph9 (insertFour x false) = graph8 x := by
    clear * - graph8 graph9 insertFour x
    simp [graph9, graph8, insertFour, Bool.or_assoc]

  have alias_data (a b : Fin 10)
      (h : (a = 4 ∧ b ∈ ([6, 7, 8] : List (Fin 10))) ∨ (b = 4 ∧ a ∈ ([2, 3] : List (Fin 10)))) :
      ∃ q : Fin 8, (∀ x, withOrs a b (insertFour x false) = fixedInput q x false) ∧
        withOrs a b (insertFour (test q) true) = fixedInput q (test q) true ∧
        graph9 (insertFour (test q) true) = true ∧ graph8 (test q) = false := by
    clear * - fixedInput graph8 graph9 insertFour withOrs test a b h
    rcases h with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · refine ⟨5, ?_, by rfl, by rfl, by rfl⟩
        intro x
        simp [withOrs, insertFour, fixedInput, List.getD]
      · refine ⟨6, ?_, by rfl, by rfl, by rfl⟩
        intro x
        simp [withOrs, insertFour, fixedInput, List.getD]
      · refine ⟨7, ?_, by rfl, by rfl, by rfl⟩
        intro x
        simp [withOrs, insertFour, fixedInput, List.getD]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · refine ⟨2, ?_, by rfl, by rfl, by rfl⟩
        intro x
        simp [withOrs, insertFour, fixedInput, List.getD]
      · refine ⟨3, ?_, by rfl, by rfl, by rfl⟩
        intro x
        simp [withOrs, insertFour, fixedInput, List.getD]

  have alias_cases (hbound : ¬ HasCircuitSize 8 graph8 12)
      (C : Circuit) (a b : Fin 10) (hfan : FanInTwo C)
      (halias : (a = 4 ∧ b ∈ ([6, 7, 8] : List (Fin 10))) ∨
        (b = 4 ∧ a ∈ ([2, 3] : List (Fin 10))))
      (heval : ∀ x : Fin 9 → Bool, C.eval (withOrs a b x) = graph9 x) :
      14 ≤ C.size := by
    clear * - wiresFrom wiresFrom_getD_lt fixedInput remove mustRead graph8 graph9 withOrs test restriction alias_data hbound C a b hfan halias heval
    obtain ⟨q, hinput, hinput', htrue, hfalse⟩ := alias_data a b halias
    have hf (x : Fin 8 → Bool) : C.eval (fixedInput q x false) = graph8 x := by
      rw [← hinput x, heval, restriction]
    have ht : C.eval (fixedInput q (test q) true) = true := by
      rw [← hinput', heval, htrue]
    have hout : C.output ≠ 4 := by
      intro ho
      have he := hf (fun _ => true)
      change (wiresFrom C.gates (fixedInput q (fun _ => true) false)).getD C.output false = _ at he
      rw [ho, wiresFrom_getD_lt _ _ _ (by simp [fixedInput])] at he
      simp [fixedInput, List.getD, graph8] at he
    have hdiff : C.eval (fixedInput q (test q) false) ≠ C.eval (fixedInput q (test q) true) := by
      rw [hf, hfalse, ht]
      decide
    obtain ⟨D, hD, hsize, hdeval⟩ := remove C q hfan (mustRead C q (test q) hout hdiff)
      ⟨test q, (hf _).trans hfalse⟩
    by_contra! h
    exact hbound ⟨D, hD, by omega, fun x => (hdeval x).trans (hf x)⟩

  intro hbound hother C a b hfan hlt h01 h09 heval
  by_cases h : (a = 4 ∧ b ∈ ([6, 7, 8] : List (Fin 10))) ∨ (b = 4 ∧ a ∈ ([2, 3] : List (Fin 10)))
  · exact alias_cases hbound C a b hfan h heval
  · exact hother C a b hfan hlt h01 h09 h heval
