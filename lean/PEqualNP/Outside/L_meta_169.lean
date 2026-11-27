import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation adapted from MetaComplexity/Helpers/Elim.lean.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht, List.append_assoc]
    rfl

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨tail, h, hlen⟩ := wiresFrom_prefix gs w
  simp [h, hlen]

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- A NOT gate reads only its first wire: drop the others. -/
private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
private abbrev Stat := Sum Bool ℕ

private def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
    next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
    saved. -/
private theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
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
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
    and every old wire has a valid status whose value on the new wires is the old value. -/
private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
    input is the constant `b`. -/
private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

private theorem normGate_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) : normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [normGate]

private theorem normGate_read (g : Gate) (n : ℕ)
    (h : g.op = GateOp.not ∧ g.inputs.head? = some n ∨
      g.op ≠ GateOp.not ∧ n ∈ g.inputs) : n ∈ (normGate g).inputs := by
  rcases h with ⟨hop, hhead⟩ | ⟨hop, hmem⟩
  · have htake : g.inputs.take 1 = [n] := by
      rcases h : g.inputs with _ | ⟨a, ins⟩ <;> simp_all
    simp [normGate, hop, htake]
  · simpa only [normGate_of_ne_not g hop] using hmem

private theorem elim_stat_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem elim_read_const (n k : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (hread : k ∈ g.inputs) (b : Bool)
    (hfix : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
    simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
      (fun h => by simpa using hg.2 h) ⟨b, List.mem_map.mpr ⟨k, hread, hfix⟩⟩
  change (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]
  simp

private theorem bad_reader_constant (n m : ℕ) (stats : List Stat) (g : Gate)
    (hg : NOk g) (hread : n ∈ g.inputs) (hfix : stats.getD n (Sum.inl false) = Sum.inl false)
    (hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < stats.length)) :
    ∃ b, (simplify g.op m (g.inputs.map fun i => stats.getD i (Sum.inl false))).2 =
      Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1.1
  have hlen : ins.length ≤ 2 := hg.1.2
  simp only [List.getD_eq_getElem?_getD] at hfix
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpAnd, hfix]⟩
    · have hmem : n = a ∨ n = b := by simpa using hread
      rcases hmem with ha | hb
      · subst a
        refine ⟨false, ?_⟩
        cases hb : stats[b]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, hb]
      · subst b
        refine ⟨false, ?_⟩
        cases ha : stats[a]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, ha]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpOr, hfix]⟩
    · have hout (w : ℕ) (hw : w ∈ [a, b]) :
          stats[w]?.getD (Sum.inl false) = Sum.inl false := by
        by_cases hn : w = n
        · simpa only [hn] using hfix
        · have hnlt : ¬w < stats.length := fun hlt => hbad ⟨rfl, rfl, w, hw, hn, hlt⟩
          exact List.getD_eq_default _ _ (Nat.le_of_not_gt hnlt)
      exact ⟨false, by simp [simplify, simpOr, hout a (by simp), hout b (by simp)]⟩
    · simp at hlen
  · have hone : ins.length ≤ 1 := hg.2 rfl
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨true, by simp [simplify, simpNot, hfix]⟩
    · simp at hone

private theorem wires_agree (gs : List Gate) (bad : ℕ → Prop) (w w' : List Bool)
    (hlen : w.length = w'.length)
    (hw : ∀ i, ¬bad i → w.getD i false = w'.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬bad i) :
    ∀ i, ¬bad i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact hw
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hv : v = v' := by
      dsimp only [v, v']
      congr 1
      exact List.map_congr_left (fun i hi => hw i (hgs g List.mem_cons_self i hi))
    change ∀ i, ¬bad i → (wiresFrom gs (w ++ [v])).getD i false =
      (wiresFrom gs (w' ++ [v'])).getD i false
    apply ih _ _ (by simp [hlen]) _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i hi
    by_cases heq : i = w.length
    · rw [getD_snoc_len _ _ _ _ heq.symm, getD_snoc_len _ _ _ _ (hlen.symm.trans heq.symm), hv]
    · rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

end PEqualNP.Outside.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.Meta169 in
theorem PEqualNP.Outside.L_meta_169 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  classical
  intro n C hmin hdep hnonconst htight j hreads
  by_contra hshape
  let gs := C.gates.map normGate
  let pre := gs.take j.val
  let g := normGate (C.gates.get j)
  let post := gs.drop (j.val + 1)
  let m := n + 1 + j.val
  let start : List Stat × List Gate := (initStats n false, [])
  let before := elim n pre start
  let after := elimStep n before g
  let final := elim n post after
  have hj : j.val < gs.length := by simp [gs]
  have hsplit : gs = pre ++ g :: post := by
    have hs := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons hj] at hs
    simpa [pre, g, post, gs, List.get_eq_getElem] using hs.symm
  have hPreLen : pre.length = j.val := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hSize : C.size = pre.length + 1 + post.length := by
    have hs := congrArg List.length hsplit
    have hg : gs.length = C.size := by simp [gs, Circuit.size]
    simp only [List.length_append, List.length_cons] at hs
    omega
  have hok : ∀ k ∈ gs, NOk k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact normGate_nok _ (hmin.1 _ hk')
  have hg : NOk g := hok g (by rw [hsplit]; simp)
  have hpre : ∀ k ∈ pre, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_left _ hk)
  have hpost : ∀ k ∈ post, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
  have hread : n ∈ g.inputs := normGate_read _ _ hreads
  have hm : before.1.length = m := by
    rw [elim_stat_length]
    simp [start, initStats, m, hPreLen]
  have hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < before.1.length) := by
    intro ⟨hop, hlen, w, hw, hne, hlt⟩
    have hop' : (C.gates.get j).op = GateOp.or := (normGate_op _).symm.trans hop
    have hgn : g = C.gates.get j := normGate_of_ne_not _ (by rw [hop']; simp)
    rw [hgn] at hlen hw
    exact hshape ⟨hop', hlen, by simpa only [hgn] using hread, w, hw, hne, by simpa [hm, m] using hlt⟩
  have hstart : n < start.1.length := by simp [start, initStats]
  have hfix : start.1.getD n (Sum.inl false) = Sum.inl false := by
    simp [start, initStats]
  have hbefore : before.1.getD n (Sum.inl false) = Sum.inl false := by
    exact (elim_getD n n _ pre start hstart).trans hfix
  -- A reader with the wrong shape becomes a constant after fixing the last input.
  obtain ⟨b, hconst⟩ := bad_reader_constant n (n + before.2.length) before.1 g hg hread hbefore hbad
  have hSaved : after.2.length = before.2.length := elim_read_const n n before g hg hread false hbefore
  have hAfterLen : after.1.length = m + 1 := by simp [after, elimStep, hm]
  have hAfterN : after.1.getD n (Sum.inl false) = Sum.inl false := by
    change (before.1 ++ [_]).getD n (Sum.inl false) = Sum.inl false
    rw [getD_snoc_ne _ _ _ _ (by rw [hm]; dsimp [m]; omega), hbefore]
  have hAfterM : after.1.getD m (Sum.inl false) = Sum.inl b := by
    change (before.1 ++ [_]).getD m (Sum.inl false) = Sum.inl b
    rw [getD_snoc_len _ _ _ _ hm, hconst]
  have hFinal : elim n gs start = final := by
    rw [hsplit]
    simp only [elim, List.foldl_append]
    rfl
  have heval (y : Fin n → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn y)) =
        circuitFun (n + 1) C (Fin.snoc y false) := by
    have hv := (inv_elim n (List.ofFn y) (by simp) gs _ start
      (fun k hk => (hok k hk).1) (inv_init n false y)).2 C.output
    rw [hFinal] at hv
    simp only [circuitFun, Circuit.eval, ofFn_snoc]
    change _ = (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false
    rw [← wiresFrom_norm C.gates]
    exact hv.2
  obtain ⟨out, hout⟩ : ∃ out, final.1.getD C.output (Sum.inl false) = Sum.inr out := by
    cases h : final.1.getD C.output (Sum.inl false) with
    | inr out => exact ⟨out, rfl⟩
    | inl c =>
      obtain ⟨y, y', hne⟩ := hnonconst
      exfalso
      apply hne
      rw [← heval y, ← heval y', h]
      rfl
  have hOutN : C.output ≠ n := by
    intro h
    rw [h, elim_getD n n _ post after (by rw [hAfterLen]; dsimp [m]; omega), hAfterN] at hout
    cases hout
  have hOutM : C.output ≠ m := by
    intro h
    rw [h, elim_getD n m _ post after (by omega), hAfterM] at hout
    cases hout
  have hLower : C.size ≤ final.2.length + 1 := by
    apply htight final.2.length
    refine ⟨⟨final.2, out⟩, ?_, le_rfl, ?_⟩
    · have ho := elim_ok n gs start (by simp [start])
      rwa [hFinal] at ho
    · intro y
      have he := heval y
      rw [hout] at he
      exact he
  have hBeforeLen : before.2.length ≤ pre.length := by
    simpa [before, start] using elim_len n pre start
  have hFinalLen : final.2.length ≤ after.2.length + post.length :=
    elim_len n post after
  -- A second reader of either fixed wire would save a second gate.
  have noPre (k : Gate) (hk : k ∈ pre) : n ∉ k.inputs := by
    intro hr
    have h := elim_len_lt n n pre start hpre hstart ⟨false, hfix⟩ ⟨k, hk, hr⟩
    change before.2.length + 1 ≤ 0 + pre.length at h
    omega
  have noPost (k : Gate) (hk : k ∈ post) (i : ℕ) (hi : i ∈ k.inputs) :
      ¬(i = n ∨ i = m) := by
    intro hbadIndex
    rcases hbadIndex with hN | hM
    · subst i
      have h := elim_len_lt n n post after hpost
        (by rw [hAfterLen]; dsimp [m]; omega) ⟨false, hAfterN⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega
    · subst i
      have h := elim_len_lt n m post after hpost
        (by omega) ⟨b, hAfterM⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega
  -- Without a second reader, neither changed wire can affect the output.
  obtain ⟨y, hne⟩ := hdep
  apply hne
  let input (b : Bool) := List.ofFn y ++ [b]
  have hInputLen (b : Bool) : (input b).length = n + 1 := by simp [input]
  let w (b : Bool) := wiresFrom pre (input b)
  have hwLen (b : Bool) : (w b).length = m := by
    simp [w, length_wiresFrom, hInputLen, hPreLen, m]
  have hw : ∀ i, i ≠ n → (w false).getD i false = (w true).getD i false := by
    apply wires_agree pre (fun i => i = n) _ _ (by simp [hInputLen]) _
      (fun k hk i hi he => noPre k hk (he ▸ hi))
    intro i hi
    change (List.ofFn y ++ [false]).getD i false = (List.ofFn y ++ [true]).getD i false
    have hin : i ≠ (List.ofFn y).length := by simpa using hi
    rw [getD_snoc_ne _ _ _ _ hin, getD_snoc_ne _ _ _ _ hin]
  let extended (b : Bool) := w b ++ [g.op.eval (g.inputs.map fun i => (w b).getD i false)]
  have ha : ∀ i, ¬(i = n ∨ i = m) →
      (extended false).getD i false = (extended true).getD i false := by
    intro i hi
    have hin : i ≠ n := fun he => hi (Or.inl he)
    have him : i ≠ m := fun he => hi (Or.inr he)
    dsimp only [extended]
    rw [getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him),
      getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him)]
    exact hw i hin
  have hv := wires_agree post (fun i => i = n ∨ i = m) (extended false) (extended true)
    (by simp [extended, hwLen]) ha noPost C.output (by simp [hOutN, hOutM])
  simp only [circuitFun, Circuit.eval, ofFn_snoc]
  change (wiresFrom C.gates (input false)).getD C.output false =
    (wiresFrom C.gates (input true)).getD C.output false
  have hs : C.gates.map normGate = pre ++ g :: post := hsplit
  simp only [← wiresFrom_norm C.gates, hs, wiresFrom_append]
  exact hv
