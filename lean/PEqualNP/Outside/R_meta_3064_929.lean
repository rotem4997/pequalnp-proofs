import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_3064_929 :
  (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12) →
  (∀ (gs : List Gate) (a b : ℕ), gs.length ≤ 12 → FanInTwo ⟨gs, 0⟩ →
    8 ≤ a → a < b → b < 8 + gs.length →
    ∃ x : Fin 8 → Bool,
      let w := (Circuit.mk gs 0).wires (List.ofFn x)
      (w.getD a false && w.getD b false) ≠ (fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) x) →
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
    obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
    rw [ht]; simp [hl]

  have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
    rw [ht, List.getD_append _ _ _ _ h]

  let Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


  have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp
  let isNot (op : GateOp) : Bool :=
    GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false op

  let normGate (g : Gate) : Gate :=
    if isNot g.op then ⟨GateOp.not, g.inputs.take 1⟩ else g

  have normGate_eval (g : Gate) (F : ℕ → Bool) :
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> try rfl
    cases inputs <;> rfl

  let NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

  have normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hlen⟩ := h
    rcases hop with h | h | h
    · have : op = GateOp.and := h
      subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate, isNot]⟩
    · have : op = GateOp.or := h
      subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate, isNot]⟩
    · have : op = GateOp.not := h
      subst this
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate, isNot]

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

  -- Each old wire has either a constant value or a new wire number.
  let Stat : Type := Bool ⊕ ℕ

  let statVal (w : List Bool) (s : Stat) : Bool :=
    Sum.casesOn s id (fun j => w.getD j false)

  let statValid (m : ℕ) (s : Stat) : Prop :=
    Sum.casesOn s (fun _ => True) (fun j => j < m)

  let simpNot (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    ins.head?.elim (none, Sum.inl true)
      (fun a => Sum.casesOn a (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)))

  let simpAnd (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    List.casesOn ins (none, Sum.inl true) (fun a tail =>
      List.casesOn tail (none, a) (fun b more =>
        List.casesOn more
          (a.elim
            (fun c => Sum.casesOn b (fun d => (none, Sum.inl (c && d)))
                (fun j => (none, bif c then Sum.inr j else Sum.inl false)))
            (fun j => Sum.casesOn b (fun c => (none, bif c then Sum.inr j else Sum.inl false))
                (fun k => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m))))
          (fun _ _ => (none, Sum.inl false))))

  let simpOr (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    List.casesOn ins (none, Sum.inl false) (fun a tail =>
      List.casesOn tail (none, a) (fun b more =>
        List.casesOn more
          (a.elim
            (fun c => Sum.casesOn b (fun d => (none, Sum.inl (c || d)))
                (fun j => (none, bif c then Sum.inl true else Sum.inr j)))
            (fun j => Sum.casesOn b (fun c => (none, bif c then Sum.inl true else Sum.inr j))
                (fun k => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m))))
          (fun _ _ => (none, Sum.inl false))))

  let simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    GateOp.rec (motive := fun _ => Option Gate × Stat)
      (simpAnd m ins) (simpOr m ins) (simpNot m ins)
      (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op

  have gateAnd (ins : List Bool) : GateOp.and.eval ins = ins.all id := rfl
  have gateOr (ins : List Bool) : GateOp.or.eval ins = ins.any id := rfl
  have gateNot (ins : List Bool) : GateOp.not.eval ins = !(ins.headD false) := rfl

  have simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
      ∀ g ∈ (simplify op m ins).1, Ok g := by
    intro g hg
    cases op <;> simp only [simplify] at hg
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpAnd] at hg <;> (subst hg; simp [Ok])
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simpOr] at hg <;> (subst hg; simp [Ok])
    · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
        simp [simpNot] at hg <;> (subst hg; simp [Ok])
    · simp at hg
    · simp at hg

  have simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
      (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
      (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
      (simplify op m ins).1 = none := by
    clear wiresFrom_append wiresFrom_start length_wiresFrom getD_wiresFrom
      getD_snoc_ne getD_snoc_eq normGate_eval normGate_nok wiresFrom_norm simplify_ok
    obtain ⟨c, hc⟩ := hc
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpAnd]
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp_all [simplify, simpOr]
    · have := hnot rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

  have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
      (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, statValid w.length s) :
      statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (statVal w)) := by
    clear wiresFrom_append wiresFrom_start length_wiresFrom getD_wiresFrom
      getD_snoc_ne getD_snoc_eq normGate_eval normGate_nok wiresFrom_norm simplify_ok
    clear simplify_count
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpAnd, statValid, statVal, gateAnd]
      · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, gateAnd, wiresFrom]
      · cases a <;> cases b
        · simp_all [simplify, simpAnd, statValid, statVal, gateAnd, wiresFrom]
        · rename_i c j
          cases c <;> simp_all [simplify, simpAnd, statValid, statVal, gateAnd, wiresFrom]
        · rename_i j c
          cases c <;> simp_all [simplify, simpAnd, statValid, statVal, gateAnd, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, gateAnd, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpOr, statValid, statVal, gateOr]
      · cases a <;> simp_all [simplify, simpOr, statValid, statVal, gateOr, wiresFrom]
      · cases a <;> cases b
        · simp_all [simplify, simpOr, statValid, statVal, gateOr, wiresFrom]
        · rename_i c j
          cases c <;> simp_all [simplify, simpOr, statValid, statVal, gateOr, wiresFrom]
        · rename_i j c
          cases c <;> simp_all [simplify, simpOr, statValid, statVal, gateOr, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, gateOr, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · simp [simplify, simpNot, statValid, statVal, gateNot]
      · cases a <;> simp_all [simplify, simpNot, statValid, statVal, gateNot, wiresFrom]

  let elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
    (acc.1 ++ [(simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
      acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

  let elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
    gs.foldl (elimStep n) acc

  have getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
      (L ++ [S]).getD k d = S := by
    subst h; simp

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

  have statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s := by
    intro s hs
    cases s
    · exact trivial
    · exact lt_of_lt_of_le hs h

  have statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
      statVal (w ++ t) s = statVal w s := by
    intro s hs
    cases s
    · rfl
    · exact List.getD_append _ _ _ _ hs

  let RunInvariant (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
    acc.1.length = w.length ∧ ∀ i : ℕ,
      statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

  have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
      ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → RunInvariant n y w acc →
        RunInvariant n y (wiresFrom gs w) (elim n gs acc) := by
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
      obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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

  have elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
        ≤ acc.2.length + gs.length := by
    induction gs with
    | nil => intro acc _ _ _; simp [elim]
    | cons g gs ih =>
      intro acc hok hk hc
      have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
      rw [h3, List.length_cons, List.countP_cons]
      by_cases hkg : k ∈ g.inputs
      · obtain ⟨c, hc⟩ := hc
        have hnok := hok g List.mem_cons_self
        have hnone : (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
          apply simplify_count
          · exact hnok.1.1
          · simpa using hnok.1.2
          · intro h; simpa using hnok.2 h
          · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
        have h2 : (elimStep n acc g).2.length = acc.2.length := by
          show (acc.2 ++ (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
          rw [hnone]; simp
        simp only [hkg, decide_true, ite_true]
        omega
      · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
          omega
        simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
        omega

  let F9 (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  let F8 (x : Fin 8 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

  have getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
      (List.ofFn f).getD j.val d = f j := by
    simp [List.getD_eq_getElem?_getD]

  have agree_off (v : ℕ) (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ v → w.getD i false = w'.getD i false) → (∀ g ∈ gs, v ∉ (normGate g).inputs) →
      ∀ i, i ≠ v → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
    induction gs with
    | nil => intro w w' _ h _; exact h
    | cons g gs ih =>
      intro w w' hl h hr
      have hg : g.op.eval (g.inputs.map fun i => w.getD i false)
          = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rw [← normGate_eval g, ← normGate_eval g]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact h a (fun e => hr g List.mem_cons_self (e ▸ ha))
      refine ih (w ++ [_]) (w' ++ [_]) (by simp [hl]) ?_
        (fun g' hg' => hr g' (List.mem_cons_of_mem _ hg'))
      intro i hi
      rw [hg]
      by_cases hil : i = w.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega), h i hi]

  let pt (l : List (Fin 9)) : Fin 9 → Bool := fun i => decide (i ∈ l)

  classical
  intro small lastAnd gs pins hlen hfan _ hpins
  by_contra h
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let run (gs : List Gate) (x : Fin 9 → Bool) := wiresFrom gs (seed x)
  have good (x : Fin 9 → Bool) :
      GateOp.and.eval (pins.map (fun i => (run gs x).getD i.val false)) = F9 x := by
    by_contra bad
    exact h ⟨x, bad⟩
  have pos (x : Fin 9 → Bool) (hx : F9 x = true) (p : Fin 24) (hp : p ∈ pins) :
      (run gs x).getD p.val false = true := by
    have hg := good x
    rw [hx] at hg
    change (pins.map (fun i => (run gs x).getD i.val false)).all id = true at hg
    exact List.all_eq_true.mp hg _ (List.mem_map_of_mem hp)
  have noPin (p : Fin 24) (hp : p ∈ pins) : p.val ≠ 4 := by
    intro hp4
    have hg := pos (pt [0,1]) (by decide) p hp
    rw [hp4, show run gs (pt [0,1]) = wiresFrom gs (seed (pt [0,1])) from rfl,
      getD_wiresFrom _ _ _ (by simp [seed])] at hg
    exact (by decide : (seed (pt [0,1])).getD 4 false ≠ true) hg
  -- The seed disjunction stays true on both rows, but the target changes.
  let one := pt [4,0,6]
  let zero := pt [0,6]
  have off (i : ℕ) (hi : i ≠ 4) : (seed one).getD i false = (seed zero).getD i false := by
    by_cases h9 : i = 9
    · subst i
      decide
    change (List.ofFn one ++ [_]).getD i false = (List.ofFn zero ++ [_]).getD i false
    rw [getD_snoc_ne _ _ _ _ (by simpa using h9), getD_snoc_ne _ _ _ _ (by simpa using h9)]
    by_cases hi9 : i < 9
    · let q : Fin 9 := ⟨i,hi9⟩
      change (List.ofFn one).getD q.val false = (List.ofFn zero).getD q.val false
      rw [getD_ofFn', getD_ofFn']
      have h4 : q ≠ 4 := fun e => hi (congrArg Fin.val e)
      simp [one, zero, pt, h4]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi9),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi9)]
  have kept : ∃ g ∈ gs, 4 ∈ (normGate g).inputs := by
    by_contra hn
    have hr (g : Gate) (hg : g ∈ gs) : 4 ∉ (normGate g).inputs := fun hf => hn ⟨g,hg,hf⟩
    have eq : pins.map (fun i => (run gs one).getD i.val false) =
        pins.map (fun i => (run gs zero).getD i.val false) := by
      apply List.map_congr_left
      intro a ha
      exact agree_off 4 gs (seed one) (seed zero) (by simp [seed]) off hr a.val (noPin a ha)
    have he := congrArg (GateOp.and.eval) eq
    rw [good, good] at he
    exact (by decide : F9 one ≠ F9 zero) he
  -- Fix input 4 to false. Wire 9 becomes the surviving input 6.
  let idx : Fin 9 → Fin 8 := ![0,1,2,3,0,4,5,6,7]
  let project (y : Fin 8 → Bool) (i : Fin 9) : Bool := if i = 4 then false else y (idx i)
  have rel (y : Fin 8 → Bool) : F9 (project y) = F8 y := by
    simp [F9, F8, project, idx]
  let begin : List Stat × List Gate :=
    ([Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4,
      Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 5], [])
  let middle := gs.map normGate
  have middleOK (g : Gate) (hg : g ∈ middle) : NOk g := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok q (hfan q hq)
  let done := elim 8 middle begin
  have hpos : 1 ≤ middle.countP (fun g => decide (4 ∈ g.inputs)) := by
    obtain ⟨g,hg,hg'⟩ := kept
    exact List.countP_pos_iff.mpr ⟨normGate g, List.mem_map_of_mem hg, decide_eq_true hg'⟩
  have sizeDone : done.2.length ≤ 12 := by
    have hs := elim_count 8 4 middle begin middleOK (by decide) ⟨false, rfl⟩
    change done.2.length + _ ≤ 0 + middle.length at hs
    have hm : middle.length = gs.length := List.length_map normGate
    have saving := Nat.add_le_add_left hpos done.2.length
    have bound : done.2.length + middle.countP (fun g => decide (4 ∈ g.inputs)) ≤ gs.length := by
      simpa only [hm, Nat.zero_add] using hs
    exact Nat.le_of_succ_le_succ (saving.trans (bound.trans hlen))
  have fanDone : FanInTwo ⟨done.2, 0⟩ := elim_ok 8 middle begin (by simp [begin])
  have init (y : Fin 8 → Bool) : RunInvariant 8 (List.ofFn y) (seed (project y)) begin := by
    refine ⟨by simp [begin, seed], ?_⟩
    intro i
    by_cases hi : i < 10
    · interval_cases i <;> simp [begin, seed, project, idx, statValid, statVal, wiresFrom,
        List.getD_eq_getElem?_getD]
    · have a : begin.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simpa [begin] using Nat.le_of_not_gt hi)
      have b : (seed (project y)).getD i false = false :=
        List.getD_eq_default _ _ (by simpa [seed] using Nat.le_of_not_gt hi)
      rw [a,b]
      exact ⟨trivial, rfl⟩
  have evalDone (y : Fin 8 → Bool) (j : ℕ) :
      statValid (8 + done.2.length) (done.1.getD j (Sum.inl false)) ∧
      statVal (wiresFrom done.2 (List.ofFn y)) (done.1.getD j (Sum.inl false)) =
        (run gs (project y)).getD j false := by
    have hh := inv_elim 8 (List.ofFn y) (by simp) middle _ begin
      (fun g hg => (middleOK g hg).1) (init y)
    exact ⟨(hh.2 j).1, ((hh.2 j).2).trans
      (congrArg (fun w => w.getD j false) (wiresFrom_norm gs (seed (project y))))⟩
  let read (p : Fin 24) := done.1.getD p.val (Sum.inl false)
  let value (y : Fin 8 → Bool) := statVal (wiresFrom done.2 (List.ofFn y))
  have eqTarget (y : Fin 8 → Bool) :
      GateOp.and.eval (pins.map (fun i => value y (read i))) = F8 y := by
    rw [← rel, ← good]
    congr 1
    exact List.map_congr_left (fun a _ => (evalDone y a.val).2)
  have single (p : Stat) (he : ∀ y, value y p = F8 y) : False := by
    cases p with
    | inl c =>
      have hOne := he (fun _ => true)
      have hZero := he (fun _ => false)
      exact (by decide : F8 (fun _ => true) ≠ F8 (fun _ => false)) (hOne.symm.trans hZero)
    | inr a =>
      exact small ⟨⟨done.2,a⟩, fanDone, sizeDone, he⟩
  have lower (j : ℕ) (hs : ∀ y, F8 y = true → value y (Sum.inr j) = true) : 8 ≤ j := by
    by_contra hj
    have hj8 : j < 8 := Nat.lt_of_not_ge hj
    let q : Fin 8 := ⟨j,hj8⟩
    have same (y : Fin 8 → Bool) : value y (Sum.inr j) = y q := by
      change (wiresFrom done.2 (List.ofFn y)).getD j false = y q
      rw [getD_wiresFrom _ _ _ (by simpa using hj8)]
      exact getD_ofFn' 8 y false q
    let a : Fin 8 → Bool := fun i => decide (i.val = 0 ∨ i.val = 1)
    let b : Fin 8 → Bool := fun i => decide (i.val = 2 ∨ i.val = 3)
    by_cases hc : j = 0 ∨ j = 1
    · have e := hs b (by decide)
      rw [same] at e
      rcases hc with h0 | h1
      · simp [b, q, h0] at e
      · simp [b, q, h1] at e
    · have e := hs a (by decide)
      rw [same] at e
      simp [a, q, hc] at e
  -- A lone surviving output uses the size bound; two computed wires use the AND case.
  have closePair (p q : Fin 24)
      (hh : ∀ y, (value y (read p) && value y (read q)) = F8 y) : False := by
    generalize hp : read p = sp at hh
    generalize hq : read q = sq at hh
    cases sp with
    | inl c =>
      cases c
      · have e := hh (fun _ => true)
        change false = F8 (fun _ => true) at e
        exact (by decide : F8 (fun _ => true) ≠ false) e.symm
      · exact single sq (fun y => hh y)
    | inr a =>
      cases sq with
      | inl c =>
        cases c
        · have e := hh (fun _ => true)
          change (value (fun _ => true) (Sum.inr a) && false) = F8 (fun _ => true) at e
          exact (by decide : F8 (fun _ => true) ≠ false) ((Bool.and_false _).symm.trans e).symm
        · exact single (Sum.inr a) (fun y => (Bool.and_true _).symm.trans (hh y))
      | inr b =>
        have va : a < 8 + done.2.length := by
          have e := (evalDone (fun _ => false) p.val).1
          change statValid (8 + done.2.length) (read p) at e
          rw [hp] at e
          exact e
        have vb : b < 8 + done.2.length := by
          have e := (evalDone (fun _ => false) q.val).1
          change statValid (8 + done.2.length) (read q) at e
          rw [hq] at e
          exact e
        have la := lower a (fun y hy => (Bool.and_eq_true_iff.mp ((hh y).trans hy)).1)
        have lb := lower b (fun y hy => (Bool.and_eq_true_iff.mp ((hh y).trans hy)).2)
        rcases lt_trichotomy a b with hab | rfl | hba
        · obtain ⟨y, hy⟩ := lastAnd done.2 a b sizeDone fanDone la hab vb
          exact hy (hh y)
        · exact single (Sum.inr a) (fun y => by simpa only [Bool.and_self] using hh y)
        · obtain ⟨y, hy⟩ := lastAnd done.2 b a sizeDone fanDone lb hba va
          exact hy ((Bool.and_comm _ _).trans (hh y))
  cases pins with
  | nil =>
    have e := eqTarget (fun _ => false)
    change true = F8 (fun _ => false) at e
    exact (by decide : F8 (fun _ => false) ≠ true) e.symm
  | cons p tail =>
    cases tail with
    | nil => exact single (read p) (fun y => by simpa [gateAnd] using eqTarget y)
    | cons q tail =>
      have tailEmpty : tail = [] := by simpa using hpins
      subst tail
      apply closePair p q
      intro y
      simpa [gateAnd] using eqTarget y
