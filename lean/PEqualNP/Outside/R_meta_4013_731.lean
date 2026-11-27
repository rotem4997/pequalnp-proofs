import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4013_731
    (hNine : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (15 : ℕ))
    (hSparse : ∀ (C : Circuit) (σ : Fin 10 → Fin 10), FanInTwo C → C.size ≤ 18 → Function.Surjective σ → (∀ v : Fin 10, v = 0 ∨ v = 2 → (C.gates.filter (fun g => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => (List.ofFn σ).getD i 1 == v))).length ≤ 2) → ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  let F (x : Fin 10 → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let G (y : Fin 9 → Bool) : Bool := y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have length_wiresFrom (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]

  let Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  let normGate (g : Gate) : Gate :=
    GateOp.casesOn (motive := fun _ => Gate) g.op g g ⟨GateOp.not, g.inputs.take 1⟩ (fun _ => g) g
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have size_eq (C : Circuit) : C.size = C.gates.length := rfl

  have normGate_eval (g : Gate) (F : ℕ → Bool) :
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp only [normGate]
    cases inputs <;> simp [evalAnd, evalOr, evalNot]

  let NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

  have normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

  have wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
      wiresFrom (gs.map normGate) w = wiresFrom gs w := by
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
          (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
      have s2 : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [s1, s2, normGate_eval, ih]

  let Stat := Sum Bool ℕ

  have sum_left {α β γ : Type} (f : α → γ) (g : β → γ) (a : α) :
      Sum.elim f g (Sum.inl a) = f a := rfl
  have sum_right {α β γ : Type} (f : α → γ) (g : β → γ) (b : β) :
      Sum.elim f g (Sum.inr b) = g b := rfl
  let statVal (w : List Bool) (s : Stat) : Bool :=
    Sum.elim id (fun j => w.getD j false) s
  let statValid (m : ℕ) (s : Stat) : Prop :=
    Sum.elim (fun _ => True) (fun j => j < m) s

  let simpNot (m : ℕ) (s : List Stat) : Option Gate × Stat :=
    List.casesOn (motive := fun _ => Option Gate × Stat) s (none, Sum.inl true)
      (fun a _ => Sum.elim (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)) a)
  let simpBin (op : GateOp) (f : Bool → Bool → Bool) (e : Bool) (m : ℕ) (s : List Stat) :
      Option Gate × Stat :=
    List.casesOn (motive := fun _ => Option Gate × Stat) s (none, Sum.inl e) (fun a tail =>
      List.casesOn (motive := fun _ => Option Gate × Stat) tail (none, a) (fun b rest =>
        List.casesOn (motive := fun _ => Option Gate × Stat) rest
          (Sum.elim
            (fun c => Sum.elim (fun d => (none, Sum.inl (f c d)))
              (fun j => (none, if c = e then Sum.inr j else Sum.inl c)) b)
            (fun j => Sum.elim (fun c => (none, if c = e then Sum.inr j else Sum.inl c))
              (fun k => (some ⟨op, [j, k]⟩, Sum.inr m)) b) a)
          (fun _ _ => (none, Sum.inl false))))
  let simpAnd := simpBin GateOp.and Bool.and true
  let simpOr := simpBin GateOp.or Bool.or false
  let simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    GateOp.casesOn (motive := fun _ => Option Gate × Stat) op
      (simpAnd m ins) (simpOr m ins) (simpNot m ins) (fun _ => (none, Sum.inl false))
      (none, Sum.inl false)

  have simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    intro g hg
    cases op <;> simp only [simplify] at hg
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpAnd, simpBin, sum_left, sum_right] at hg <;> (subst hg; simp [Ok])
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpOr, simpBin, sum_left, sum_right] at hg <;> (subst hg; simp [Ok])
    · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
        simp [simpNot, sum_left, sum_right] at hg <;> (subst hg; simp [Ok])
    · simp at hg
    · simp at hg

  have simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
      (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
      (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
      (simplify op m ins).1 = none := by
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpAnd, simpBin, sum_left, sum_right]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpOr, simpBin, sum_left, sum_right]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot, sum_left, sum_right]

  have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
      (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, statValid w.length s) :
      statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (statVal w)) := by
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpAnd, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot]
      · cases a <;> simp_all [simplify, simpAnd, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot, wiresFrom]
      · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
          simp_all [simplify, simpAnd, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpOr, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot]
      · cases a <;> simp_all [simplify, simpOr, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot, wiresFrom]
      · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
          simp_all [simplify, simpOr, simpBin, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · simp [simplify, simpNot, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot]
      · cases a <;> simp_all [simplify, simpNot, sum_left, sum_right, statValid, statVal, evalAnd, evalOr, evalNot, wiresFrom]


  let elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
    (acc.1 ++ [(simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
      acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

  let elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
    gs.foldl (elimStep n) acc

  have elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
      elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

  have elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
      (elim n gs acc).1.length = acc.1.length + gs.length := by
    induction gs with
    | nil => intro acc; rfl
    | cons g gs ih =>
      intro acc
      rw [elim_cons, ih]
      simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
      omega

  have elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
      k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
    induction gs with
    | nil => intro acc _; rfl
    | cons g gs ih =>
      intro acc hk
      rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
      exact getD_snoc_ne _ _ _ _ (by omega)

  have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
    cases o <;> simp

  have elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplify_ok _ _ _ g' (by simpa using h1)

  have elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
      (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
    induction gs with
    | nil => intro acc; simp [elim]
    | cons g gs ih =>
      intro acc
      have h1 := ih (elimStep n acc g)
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [elim_cons, List.length_cons]; omega

  have statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s := by
    rintro (c | j) hs
    · trivial
    · exact lt_of_lt_of_le hs h

  have statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s → statVal (w ++ t) s = statVal w s := by
    rintro (c | j) hs
    · rfl
    · exact List.getD_append _ _ _ _ hs

  let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
    acc.1.length = w.length ∧ ∀ i : ℕ,
      statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

  have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
      ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
        Inv n y (wiresFrom gs w) (elim n gs acc) := by
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
      have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro a _
        exact (hi a).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [wiresFrom_append]
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
        statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2
  have elim_count (n : ℕ) (P : ℕ → Bool) (gs : List Gate) :
      ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ i, P i = true → i < acc.1.length ∧ acc.1.getD i (Sum.inl false) = Sum.inl false) →
      (elim n gs acc).2.length + (gs.filter fun g => g.inputs.any P).length ≤ acc.2.length + gs.length := by
    induction gs with
    | nil => intro acc _ _; simp [elim]
    | cons g gs ih =>
      intro acc hok hP
      have hP' : ∀ i, P i = true → i < (elimStep n acc g).1.length ∧
          (elimStep n acc g).1.getD i (Sum.inl false) = Sum.inl false := by
        intro i hi
        obtain ⟨hlt, hval⟩ := hP i hi
        refine ⟨by simp [elimStep]; omega, ?_⟩
        change (acc.1 ++ [_]).getD i (Sum.inl false) = Sum.inl false
        rw [List.getD_append _ _ _ _ hlt, hval]
      have hrest := ih (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hP'
      rw [elim_cons]
      by_cases hread : g.inputs.any P = true
      · obtain ⟨i, himem, hiP⟩ := List.any_eq_true.mp hread
        have hg := hok g List.mem_cons_self
        have hnone : (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
          apply simplify_count
          · exact hg.1.1
          · simpa using hg.1.2
          · intro h; simpa using hg.2 h
          · exact ⟨false, List.mem_map.mpr ⟨i, himem, (hP i hiP).2⟩⟩
        have hlen : (elimStep n acc g).2.length = acc.2.length := by
          simp only [elimStep, hnone, Option.toList_none, List.append_nil]
        simp only [List.filter_cons, hread, ↓reduceIte, List.length_cons]
        omega
      · have hread' : g.inputs.any P = false := Bool.eq_false_iff.mpr hread
        have hlen : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
          omega
        simp only [List.filter_cons, hread', Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
  have normGate_inputs (g : Gate) (hg : Ok g) :
      (normGate g).inputs = (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) := by
    obtain ⟨op, inputs⟩ := g
    rcases hg.1 with h | h | h
    · have : op = GateOp.and := h
      subst this; rfl
    · have : op = GateOp.or := h
      subst this; rfl
    · have : op = GateOp.not := h
      subst this; rfl
  have norm_count (gs : List Gate) (P : ℕ → Bool) (h : ∀ g ∈ gs, Ok g) :
      ((gs.map normGate).filter (fun g => g.inputs.any P)).length =
        (gs.filter (fun g => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any P)).length := by
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro g hg
    dsimp only [Function.comp_apply]
    rw [normGate_inputs g (h g hg)]
  let remap (j : ℕ) : Fin 9 := ([4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD j 0
  let embed (p : Fin 10 → Fin 10) (y : Fin 9 → Bool) (i : Fin 10) : Bool :=
    if (p i).val = 0 then false
    else y (remap ((p i).val - 1))
  let init (p σ : Fin 10 → Fin 10) : List Stat :=
    List.ofFn (fun i : Fin 10 =>
      if (p (σ i)).val = 0 then Sum.inl false
      else Sum.inr (remap ((p (σ i)).val - 1)).val) ++ [Sum.inr 0]
  have ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
      (List.ofFn f).getD i.val d = f i := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have inv_initial (p σ : Fin 10 → Fin 10) (y : Fin 9 → Bool) :
      Inv 9 (List.ofFn y) (List.ofFn (embed p y ∘ σ) ++ [y 0]) (init p σ, []) := by
    refine ⟨by simp [init], ?_⟩
    intro j
    change statValid 9 ((init p σ).getD j (Sum.inl false)) ∧
      statVal (List.ofFn y) ((init p σ).getD j (Sum.inl false)) =
        (List.ofFn (embed p y ∘ σ) ++ [y 0]).getD j false
    by_cases hj : j < 10
    · let i : Fin 10 := ⟨j, hj⟩
      have hs : (init p σ).getD j (Sum.inl false) =
          if (p (σ i)).val = 0 then Sum.inl false else Sum.inr (remap ((p (σ i)).val - 1)).val := by
        dsimp [init]
        rw [List.getD_append _ _ _ _ (by simp; exact hj)]
        exact ofFn_getD _ i _
      have hw : (List.ofFn (embed p y ∘ σ) ++ [y 0]).getD j false = embed p y (σ i) := by
        rw [List.getD_append _ _ _ _ (by simp; exact hj)]
        exact ofFn_getD _ i _
      rw [hs, hw]
      by_cases hp : (p (σ i)).val = 0
      · rw [ite_eq_left hp]
        refine ⟨True.intro, ?_⟩
        dsimp only [statVal, embed]
        rw [ite_eq_left hp]
        rfl
      · have hb : (remap ((p (σ i)).val - 1)).val < 9 := (remap _).isLt
        rw [ite_eq_right hp]
        refine ⟨hb, ?_⟩
        dsimp only [statVal, embed]
        rw [ite_eq_right hp]
        exact ofFn_getD y (remap ((p (σ i)).val - 1)) false
    · by_cases h10 : j = 10
      · subst j
        simp [init, statValid, statVal]
      · have hj11 : 11 ≤ j := by omega
        rw [List.getD_eq_default _ _ (by simpa [init] using hj11),
          List.getD_eq_default _ _ (by simpa using hj11)]
        exact ⟨True.intro, rfl⟩
  let swap : Fin 10 → Fin 10 := ![2,1,0,4,3,7,6,5,9,8]
  have hint_id : ∀ (y : Fin 9 → Bool), (embed id y 0 || embed id y 2) = y 0 := by
    decide +kernel
  have hint_swap : ∀ (y : Fin 9 → Bool), (embed swap y 0 || embed swap y 2) = y 0 := by
    decide +kernel
  have graph_id : ∀ (y : Fin 9 → Bool), F (embed id y) = G y := by
    decide +kernel
  have graph_swap : ∀ (y : Fin 9 → Bool), F (embed swap y) = G y := by
    decide +kernel
  have pin_zero_id : ∀ i : Fin 10, (id i).val = 0 ↔ i = 0 := by
    decide +kernel
  have pin_zero_swap : ∀ i : Fin 10, (swap i).val = 0 ↔ i = 2 := by
    decide +kernel
  intro C σ hFan hSize hSurj
  classical
  by_contra hne
  have hAll : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) = F x := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  have endpoint_bound (v : Fin 10) (hv : v ≠ 1) (p : Fin 10 → Fin 10)
      (hp : ∀ i : Fin 10, (p i).val = 0 ↔ i = v)
      (hhint : ∀ y : Fin 9 → Bool, (embed p y 0 || embed p y 2) = y 0)
      (hgraph : ∀ y : Fin 9 → Bool, F (embed p y) = G y) :
      (C.gates.filter (fun g =>
        (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any
          (fun i => (List.ofFn σ).getD i 1 == v))).length ≤ 2 := by
    let P : ℕ → Bool := fun i => (List.ofFn σ).getD i 1 == v
    let A := elim 9 (C.gates.map normGate) (init p σ, [])
    have hNOK : ∀ g ∈ C.gates.map normGate, NOk g := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact normGate_nok g' (hFan g' hg')
    have hP : ∀ i, P i = true → i < (init p σ).length ∧
        (init p σ).getD i (Sum.inl false) = Sum.inl false := by
      intro i hi
      have heq : (List.ofFn σ).getD i 1 = v := by simpa only [P, beq_iff_eq] using hi
      have hlt : i < 10 := by
        by_contra hn
        have hd : (List.ofFn σ).getD i 1 = 1 := List.getD_eq_default _ _ (by simp; omega)
        exact hv (heq.symm.trans hd)
      have hσ : σ ⟨i, hlt⟩ = v := by
        simpa only [List.getD_eq_getElem (List.ofFn σ) (1 : Fin 10) (by simpa using hlt), List.getElem_ofFn] using heq
      have hpσ : (p (σ ⟨i, hlt⟩)).val = 0 := (hp _).mpr hσ
      refine ⟨by simp [init]; omega, ?_⟩
      dsimp only [init]
      rw [List.getD_append _ _ _ _ (by simpa using hlt)]
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp only [List.getElem_ofFn, hpσ, ↓reduceIte]
    have hbound0 := elim_count 9 P (C.gates.map normGate) (init p σ, []) hNOK hP
    have hcount := norm_count C.gates P hFan
    have hbound : A.2.length +
        (C.gates.filter (fun g =>
          (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any P)).length ≤ C.size := by
      simpa only [A, hcount, List.length_nil, Nat.zero_add, List.length_map,
        size_eq] using hbound0
    have hsem (y : Fin 9 → Bool) :
        statVal (wiresFrom A.2 (List.ofFn y)) (A.1.getD C.output (Sum.inl false)) = G y := by
      have hinv := inv_elim 9 (List.ofFn y) (by simp) (C.gates.map normGate)
        (List.ofFn (embed p y ∘ σ) ++ [y 0]) (init p σ, [])
        (fun g hg => (hNOK g hg).1) (inv_initial p σ y)
      have hval := (hinv.2 C.output).2
      rw [wiresFrom_norm] at hval
      change statVal (wiresFrom A.2 (List.ofFn y)) (A.1.getD C.output (Sum.inl false)) =
        C.eval (List.ofFn (embed p y ∘ σ) ++ [y 0]) at hval
      rw [← hhint y, hAll, hgraph] at hval
      exact hval
    cases hout : A.1.getD C.output (Sum.inl false) with
    | inl c =>
      have h0 := hsem (fun _ => false)
      have h1 := hsem (fun _ => true)
      rw [hout] at h0 h1
      change c = false at h0
      change c = true at h1
      exact (Bool.false_ne_true (h0.symm.trans h1)).elim
    | inr j =>
      let D : Circuit := ⟨A.2, j⟩
      have hD : FanInTwo D := by
        intro g hg
        exact elim_ok 9 (C.gates.map normGate) (init p σ, []) (by simp) g hg
      have hcorrect : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = G y := by
        intro y
        have h := hsem y
        rw [hout] at h
        exact h
      have h16 : 16 ≤ A.2.length := by
        by_contra hsmall
        apply hNine
        refine ⟨D, hD, ?_, hcorrect⟩
        change A.2.length ≤ 15
        omega
      change (C.gates.filter (fun g =>
        (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any P)).length ≤ 2
      omega
  have hsparse : ∀ v : Fin 10, v = 0 ∨ v = 2 →
      (C.gates.filter (fun g =>
        (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any
          (fun i => (List.ofFn σ).getD i 1 == v))).length ≤ 2 := by
    intro v hv
    rcases hv with rfl | rfl
    · exact endpoint_bound 0 (by decide) id pin_zero_id hint_id graph_id
    · exact endpoint_bound 2 (by decide) swap pin_zero_swap hint_swap graph_swap
  obtain ⟨x, hx⟩ := hSparse C σ hFan hSize hSurj hsparse
  exact hx (hAll x)
