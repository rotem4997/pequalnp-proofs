import PEqualNP.Defs

-- Proof developed by Astra (OpenAI Codex) for project participant Stibnit3.
-- The wire relabeling and gate elimination helpers adapt the project proofs.

namespace PEqualNP.MetaComplexity.Astra548Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end PEqualNP.MetaComplexity.Astra548Helpers

namespace PEqualNP.MetaComplexity.Astra548Helpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.MetaComplexity.Astra548Helpers

namespace PEqualNP.MetaComplexity.Astra548Helpers

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

abbrev Stat := Sum Bool Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, (@Sum.inl Bool Nat) true)
  | Sum.inl c :: _ => (none, (@Sum.inl Bool Nat) (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, (@Sum.inr Bool Nat) m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, (@Sum.inl Bool Nat) true)
  | [Sum.inl c] => (none, (@Sum.inl Bool Nat) c)
  | [Sum.inr j] => (none, (@Sum.inr Bool Nat) j)
  | [Sum.inl c, Sum.inl d] => (none, (@Sum.inl Bool Nat) (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then (@Sum.inr Bool Nat) j else (@Sum.inl Bool Nat) false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then (@Sum.inr Bool Nat) j else (@Sum.inl Bool Nat) false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, (@Sum.inr Bool Nat) m)
  | _ => (none, (@Sum.inl Bool Nat) false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, (@Sum.inl Bool Nat) false)
  | [Sum.inl c] => (none, (@Sum.inl Bool Nat) c)
  | [Sum.inr j] => (none, (@Sum.inr Bool Nat) j)
  | [Sum.inl c, Sum.inl d] => (none, (@Sum.inl Bool Nat) (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then (@Sum.inl Bool Nat) true else (@Sum.inr Bool Nat) j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then (@Sum.inl Bool Nat) true else (@Sum.inr Bool Nat) j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, (@Sum.inr Bool Nat) m)
  | _ => (none, (@Sum.inl Bool Nat) false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, (@Sum.inl Bool Nat) false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, (@Sum.inl Bool Nat) c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k ((@Sum.inl Bool Nat) false) = (@Sum.inl Bool Nat) c) →
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
          (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i ((@Sum.inl Bool Nat) false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i ((@Sum.inl Bool Nat) false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    set ins := g.inputs.map fun i => acc.1.getD i ((@Sum.inl Bool Nat) false) with hins
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
    show ((acc.1 ++ [r.2]).getD i ((@Sum.inl Bool Nat) false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i ((@Sum.inl Bool Nat) false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (@Sum.inr Bool Nat) i) ++ [(@Sum.inl Bool Nat) b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (@Sum.inr Bool Nat) i)).length = n := by simp
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

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output ((@Sum.inl Bool Nat) false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output ((@Sum.inl Bool Nat) false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output ((@Sum.inl Bool Nat) false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n ((@Sum.inl Bool Nat) false) = (@Sum.inl Bool Nat) b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Astra548Helpers

namespace Gap548Circuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem plug {m r s : ℕ} (f : (Fin m → Bool) → Bool) (H : (Fin (m+1) → Bool) → Bool)
    (hf : HasCircuitSize m f r) (hh : HasCircuitSize (m+1) H s)
    (live : ∃ x, f x = true) :
    HasCircuitSize m (fun x => H (Fin.snoc x (f x))) (r+s) := by
  obtain ⟨D,okD,szD,evD⟩ := hf
  let M := m + D.gates.length
  have len (x : Fin m → Bool) : (D.wires (List.ofFn x)).length = M := by
    have aux (gs : List Gate) (W : List Bool) :
        (gs.foldl step W).length = W.length + gs.length := by
      induction gs generalizing W with
      | nil => simp
      | cons h t ih => simp [List.foldl,ih,step]; omega
    change (D.gates.foldl step _).length = _
    rw [aux]; simp [M]
  have valid : D.output < M := by
    obtain ⟨x,hx⟩ := live
    by_contra! hx'
    have h := evD x
    unfold Circuit.eval at h
    rw [List.getD_eq_default _ _ (by rw [len]; exact hx'), hx] at h
    contradiction
  let π : Fin (m+1) → Fin M := Fin.snoc (fun i : Fin m => (⟨i.val, by dsimp [M]; omega⟩ : Fin M)) ⟨D.output,valid⟩
  obtain ⟨C,okC,szC,evC⟩ := relabel_size π H s hh
  refine ⟨⟨D.gates ++ C.gates,C.output⟩,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact okD g h
    · exact okC g h
  · change (D.gates++C.gates).length ≤ _
    change D.gates.length ≤ _ at szD
    change C.gates.length ≤ _ at szC
    simp; omega
  · intro x
    let W := D.wires (List.ofFn x)
    let z : Fin M → Bool := fun i => W.getD i.val false
    have ofz : List.ofFn z = W := by
      apply List.ext_getElem <;> simp [z,W,len]
    have hz : z ∘ π = Fin.snoc x (f x) := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [z,π,W,Circuit.eval] using evD x
      · have keep (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
            (gs.foldl step w).getD j false = w.getD j false := by
          induction gs generalizing w with
          | nil => rfl
          | cons h t ih =>
            rw [List.foldl_cons,ih (step w h) (by simp [step]; omega)]
            exact List.getD_append _ _ _ _ hj
        simp only [Function.comp_apply,π,Fin.snoc_castSucc]
        change (D.gates.foldl step (List.ofFn x)).getD j.val false = x j
        rw [keep _ _ _ (by simp)]
        simp [List.getD_eq_getElem]
    have h : C.eval (List.ofFn z) = H (z ∘ π) := evC z
    rw [hz] at h
    change ((D.gates ++ C.gates).foldl step _).getD C.output false = _
    rw [List.foldl_append]
    change (C.gates.foldl step W).getD C.output false = _
    change (C.gates.foldl step (List.ofFn z)).getD C.output false = _ at h
    rw [ofz] at h
    exact h
end Gap548Circuit
namespace Gap548Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem weaken {m s t : ℕ} {f : (Fin m → Bool) → Bool}
    (h : HasCircuitSize m f s) (hle : s ≤ t) : HasCircuitSize m f t := by
  obtain ⟨C, ok, sz, ev⟩ := h
  exact ⟨C,ok,sz.trans hle,ev⟩
theorem input {m : ℕ} (i : Fin m) : HasCircuitSize m (fun x => x i) 0 := by
  refine ⟨⟨[],i.val⟩,by simp [FanInTwo],by simp [Circuit.size],?_⟩
  intro x; simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem addWire {m : ℕ} (a b : Fin m) (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [x a,x b]) 1 := by
  refine ⟨⟨[⟨op,[a,b]⟩],m⟩,?_,by simp [Circuit.size],?_⟩
  · intro g hg; simp at hg; subst g
    obtain rfl|rfl := ho <;> simp
  · intro x
    simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem binary {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true)
    (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [f x,g x]) (s+t+1) := by
  let G : (Fin (m+1) → Bool) → Bool := fun z => g (fun i => z i.castSucc)
  have hG : HasCircuitSize (m+1) G t := relabel_size Fin.castSucc g t hg
  have lG : ∃ x, G x = true := by
    obtain ⟨x,hx⟩ := lg
    exact ⟨Fin.snoc x false, by simpa [G] using hx⟩
  have h1 := addWire (Fin.last m).castSucc (Fin.last (m+1)) op ho
  have h2 := plug G _ hG h1 lG
  have h3 := plug f _ hf h2 lf
  simpa [G,Nat.add_assoc] using h3
end Gap548Circuit
namespace Gap548Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem orSize {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t) :
    HasCircuitSize m (fun x => f x || g x) (s+t+1) := by
  by_cases lf : ∃ x, f x = true
  · by_cases lg : ∃ x, g x = true
    · simpa [GateOp.eval] using binary hf hg lf lg .or (Or.inr rfl)
    · have h x : g x = false := by cases he : g x <;> simp_all
      simpa [h] using weaken hf (show s ≤ s+t+1 by omega)
  · have h x : f x = false := by cases he : f x <;> simp_all
    simpa [h] using weaken hg (show t ≤ s+t+1 by omega)
theorem andLive {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true) :
    HasCircuitSize m (fun x => f x && g x) (s+t+1) := by
  simpa [GateOp.eval] using binary hf hg lf lg .and (Or.inl rfl)
end Gap548Circuit

namespace Gap548
theorem orient {k : ℕ} (K : SimpleGraph (Fin (k+1))) [DecidableRel K.Adj]
    (S : Finset (Fin (k+1))) (cov : ∀ v w, K.Adj v w → v ∈ S ∨ w ∈ S) :
    ∃ owner leaf : (↥K.edgeFinset) → Fin (k+1),
      (∀ e, owner e ∈ S) ∧ ∀ e, s(owner e,leaf e) = e.val := by
  classical
  have h (e : ↥K.edgeFinset) : ∃ u w, u ∈ S ∧ s(u,w) = e.val := by
    obtain ⟨v,hv⟩ := (show ∃ p : Fin (k+1) × Fin (k+1), s(p.1,p.2) = e.val from
      ⟨e.val.out,Sym2.mk_fst_out_snd_out _⟩)
    have hadj : K.Adj v.1 v.2 := by
      apply (K.mem_edgeSet).mp
      rw [hv]; exact K.mem_edgeFinset.mp e.property
    rcases cov _ _ hadj with h|h
    · exact ⟨_,_,h,hv⟩
    · exact ⟨_,_,h,(Sym2.eq_swap ..).trans hv⟩
  choose u w hs he using h
  exact ⟨u,w,hs,he⟩
theorem oriented_edges {k : ℕ} (K : SimpleGraph (Fin (k+1))) [DecidableRel K.Adj]
    (S : Finset (Fin (k+1))) (u w : (↥K.edgeFinset) → Fin (k+1))
    (hs : ∀ e, u e ∈ S) (he : ∀ e, s(u e,w e) = e.val) (b : Fin (k+1) → Bool) :
    (∃ v z, K.Adj v z ∧ b v = true ∧ b z = true) ↔
      ∃ v ∈ S, b v = true ∧ ∃ e, u e = v ∧ b (w e) = true := by
  constructor
  · rintro ⟨v,z,h,hv,hz⟩
    let e : ↥K.edgeFinset := ⟨s(v,z),K.mem_edgeFinset.mpr (K.mem_edgeSet.mpr h)⟩
    have hh : s(u e,w e) = s(v,z) := he e
    obtain ⟨h1,h2⟩|⟨h1,h2⟩ := Sym2.eq_iff.mp hh
    · exact ⟨_,hs e,h1 ▸ hv,e,rfl,h2 ▸ hz⟩
    · exact ⟨_,hs e,h1 ▸ hz,e,rfl,h2 ▸ hv⟩
  · rintro ⟨v,_,hv,e,rfl,hw⟩
    refine ⟨u e,w e,?_,hv,hw⟩
    apply K.mem_edgeSet.mp
    rw [he]; exact K.mem_edgeFinset.mp e.property
end Gap548

namespace Gap548
open PEqualNP.MetaComplexity
def extG {n : ℕ} (g : (Fin n → Bool) → Bool → Bool) (z : Fin (n+1+1) → Bool) :=
  g (fun i => z i.castSucc.castSucc) (z (Fin.last n).castSucc) ||
    (z (Fin.last n).castSucc && z (Fin.last (n+1)))
def baseG {n : ℕ} (g : (Fin n → Bool) → Bool → Bool) (y : Fin (n+1) → Bool) :=
  g (fun i => y i.castSucc) (y (Fin.last n))
theorem specialize {n q : ℕ} {g : (Fin n → Bool) → Bool → Bool}
    (hn : ∃ y y' b b', g y b ≠ g y' b')
    (hz : ∃ y, g y true = false)
    (hc : HasCircuitSize (n+1+1) (extG g) (q+1)) :
    HasCircuitSize (n+1) (baseG g) q := by
  obtain ⟨y0,h0⟩ := hz
  obtain ⟨y1,y2,b1,b2,hn⟩ := hn
  have he (y : Fin (n+1) → Bool) : extG g (Fin.snoc y false) = baseG g y := by
    simp [extG,baseG]
  have H := Astra548Helpers.gate_elim (n+1) (extG g) false q
  have dep : ∃ x : Fin (n+1+1) → Bool,
      extG g (Function.update x (Fin.last (n+1)) (!x (Fin.last (n+1)))) ≠ extG g x := by
    refine ⟨Fin.snoc (Fin.snoc y0 true) false, ?_⟩
    simpa [extG, Function.update_of_ne, Fin.castSucc_ne_last, h0]
  have nonconst : ∃ y y' : Fin (n+1) → Bool,
      extG g (Fin.snoc y false) ≠ extG g (Fin.snoc y' false) := by
    refine ⟨Fin.snoc y1 b1,Fin.snoc y2 b2,?_⟩
    simpa [he, baseG] using hn
  simpa only [he] using H dep nonconst hc
end Gap548
namespace Gap548
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
theorem positive {n q : ℕ} {g : (Fin n → Bool) → Bool → Bool}
    (hn : ∃ y y' b b', g y b ≠ g y' b') (hz : ∃ y, g y true = false)
    (hc : HasCircuitSize (n+1+1) (extG g) q) : 0 < q := by
  by_contra! h
  obtain ⟨⟨gs,o⟩,_,hs,he⟩ := hc
  change gs.length ≤ q at hs
  have eg : gs = [] := List.length_eq_zero_iff.mp (by omega)
  subst gs
  have val (x : Fin (n+1+1) → Bool) :
      (List.ofFn x).getD o false = extG g x := he x
  obtain ⟨y,hy⟩ := hz
  by_cases ho : o = n+1
  · obtain ⟨a,b,i,j,hne⟩ := hn
    have H (z : Fin n → Bool) (v : Bool) := val (Fin.snoc (Fin.snoc z v) false)
    have H' (z : Fin n → Bool) (v : Bool) : false = g z v := by
      have hv := H z v
      rw [ho,List.getD_eq_getElem _ _ (by simp)] at hv
      simp only [List.getElem_ofFn] at hv
      let xx : Fin (n+1+1) → Bool := Fin.snoc (Fin.snoc z v) false
      change xx (Fin.last (n+1)) = _ at hv
      have hx : xx (Fin.last (n+1)) = false := by simp [xx]
      rw [hx] at hv
      simpa only [Fin.snoc_last,extG,Fin.snoc_castSucc,
        Bool.and_false,Bool.or_false] using hv
    exact hne ((H' a i).symm.trans (H' b j))
  · have h1 := val (Fin.snoc (Fin.snoc y true) false)
    have h2 := val (Fin.snoc (Fin.snoc y true) true)
    have ne : o ≠ (List.ofFn (Fin.snoc y true)).length := by simpa only [List.length_ofFn] using ho
    rw [Astra548Helpers.ofFn_snoc, Astra548Helpers.getD_snoc_ne _ _ _ _ ne] at h1 h2
    simp only [extG,Fin.snoc_last,Fin.snoc_castSucc,hy,Bool.false_or,Bool.true_and] at h1 h2
    exact Bool.false_ne_true (h1.symm.trans h2)
end Gap548

namespace Gap548Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
noncomputable def row {A : Type} {m : ℕ} (T : Finset A) (l : A → Fin m) (x : Fin m → Bool) : Bool :=
  @decide (∃ i ∈ T, x (l i) = true) (Classical.propDecidable _)
theorem row_nonempty {A : Type} {m : ℕ} (T : Finset A) (l : A → Fin m) (hne : T.Nonempty) :
    HasCircuitSize m (row T l) (T.card-1) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at hne
  | @insert i t hi ih =>
    by_cases ht : t.Nonempty
    · have h := orSize (input (l i)) (ih ht)
      have hc := Finset.card_pos.mpr ht
      have eq : row (insert i t) l = (fun x => x (l i) || row t l x) := by
        funext x; apply Bool.eq_iff_iff.mpr; simp [row]
      rw [eq,Finset.card_insert_of_notMem hi]
      exact weaken h (by omega)
    · have et := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      have he : row {i} l = (fun x => x (l i)) := by funext x; apply Bool.eq_iff_iff.mpr; simp [row]
      simpa [he] using input (l i)
noncomputable def joined {A : Type} {m : ℕ} (base : (Fin m → Bool) → Bool)
    (I : Finset A) (term : A → (Fin m → Bool) → Bool) (x : Fin m → Bool) :=
  base x || @decide (∃ i ∈ I, term i x = true) (Classical.propDecidable _)
theorem accumulate {A : Type} {m c : ℕ} (I : Finset A) (cost : A → ℕ)
    (term : A → (Fin m → Bool) → Bool)
    (hterm : ∀ i ∈ I, (∀ x, term i x = false) ∨
      ∃ d, HasCircuitSize m (term i) d ∧ d+1 ≤ cost i)
    (base : (Fin m → Bool) → Bool) (hb : HasCircuitSize m base c) :
    HasCircuitSize m (joined base I term) (c+∑ i ∈ I, cost i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have he : joined base ∅ term = base := by funext x; simp [joined]
    simpa [he] using hb
  | @insert i t hi ih =>
    have h := ih (fun j hj => hterm j (Finset.mem_insert_of_mem hj))
    have eq : joined base (insert i t) term = (fun x => joined base t term x || term i x) := by
      funext x; apply Bool.eq_iff_iff.mpr; simp [joined, or_assoc, or_comm, or_left_comm]
    rw [eq, Finset.sum_insert hi]
    rcases hterm i (Finset.mem_insert_self ..) with he|⟨d,hd,hc⟩
    · simpa [he] using weaken h (show c+∑ j ∈ t, cost j ≤ c+(cost i+∑ j ∈ t,cost j) by omega)
    · exact weaken (orSize h hd) (by omega)
end Gap548Circuit

namespace Gap548Circuit
open PEqualNP.MetaComplexity
noncomputable def star {A V : Type} {m : ℕ} (T : V → Finset A) (vwire : V → Fin m)
    (l : A → Fin m) (v : V) (x : Fin m → Bool) := x (vwire v) && row (T v) l x
theorem attachStars {A V : Type} {m c : ℕ} (I : Finset V) (T : V → Finset A)
    (vwire : V → Fin m) (l : A → Fin m) {base : (Fin m → Bool) → Bool}
    (hb : HasCircuitSize m base c) :
    HasCircuitSize m (joined base I (star T vwire l))
      (c + (∑ i ∈ I, (T i).card) + I.card) := by
  classical
  have h := accumulate I (fun i => (T i).card+1) (star T vwire l) (base := base) (hb := hb)
  have hh : ∀ i ∈ I, (∀ x, star T vwire l i x = false) ∨
      ∃ d, HasCircuitSize m (star T vwire l i) d ∧ d+1 ≤ (T i).card+1 := by
    intro i _
    by_cases ht : (T i).Nonempty
    · right
      obtain ⟨a,ha⟩ := ht
      have hl : ∃ x, row (T i) l x = true := ⟨fun _ => true, by simp only [row,decide_eq_true_eq]; exact ⟨a,ha,by trivial⟩⟩
      have H := andLive (input (vwire i)) (row_nonempty _ l ⟨a,ha⟩) ⟨fun _ => true,rfl⟩ hl
      have pos := Finset.card_pos.mpr (show (T i).Nonempty from ⟨a,ha⟩)
      exact ⟨_, H, by omega⟩
    · left
      have h0 := Finset.not_nonempty_iff_eq_empty.mp ht
      intro x; simp [star,row,h0]
  simpa [Finset.sum_add_distrib,Nat.add_assoc] using h hh
theorem finish {a m c : ℕ} (l : Fin a → Fin m) {base : (Fin m → Bool) → Bool}
    (hb : HasCircuitSize m base c) :
    HasCircuitSize m (fun x => base x || decide (∃ i, x (l i) = true)) (c+a) := by
  classical
  have H := accumulate (Finset.univ : Finset (Fin a)) (fun _ => 1) (fun i x => x (l i))
    (fun i _ => Or.inr ⟨0,input (l i),by decide⟩) base hb
  have eq : joined base Finset.univ (fun i x => x (l i)) = (fun x => base x || decide (∃ i, x (l i) = true)) := by
    funext x; apply Bool.eq_iff_iff.mpr; simp [joined]
  simpa [eq] using H
end Gap548Circuit

open Gap548Circuit Gap548 PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_548 : ∀ (n k a : ℕ) (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj] (g : (Fin n → Bool) → Bool → Bool) (S : Finset (Fin (k + 1))) (c q : ℕ), (∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b') → (∃ y : Fin n → Bool, g y false = false) → (∃ y : Fin n → Bool, g y true = false) → (∀ u w : Fin (k + 1), K.Adj u w → u ∈ S ∨ w ∈ S) → (((0 : Fin (k + 1)) ∉ S → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun z : Fin (n + 1) → Bool => g (fun i : Fin n => z i.castSucc) (z (Fin.last n))) c → PEqualNP.MetaComplexity.HasCircuitSize (n + ((k + 1) + a)) (fun x : Fin (n + ((k + 1) + a)) → Bool => g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i)) (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) || decide (∃ u w : Fin (k + 1), K.Adj u w ∧ x (Fin.natAdd n (Fin.castAdd a u)) = true ∧ x (Fin.natAdd n (Fin.castAdd a w)) = true) || decide (∃ i : Fin a, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)) (a + K.edgeFinset.card + c + S.card)) ∧ ((0 : Fin (k + 1)) ∈ S → PEqualNP.MetaComplexity.HasCircuitSize (n + 1 + 1) (fun z : Fin (n + 1 + 1) → Bool => g (fun i : Fin n => z i.castSucc.castSucc) (z (Fin.last n).castSucc) || (z (Fin.last n).castSucc && z (Fin.last (n + 1)))) q → ∀ s : ℕ, s + 2 = a + K.edgeFinset.card + q + S.card → PEqualNP.MetaComplexity.HasCircuitSize (n + ((k + 1) + a)) (fun x : Fin (n + ((k + 1) + a)) → Bool => g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i)) (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) || decide (∃ u w : Fin (k + 1), K.Adj u w ∧ x (Fin.natAdd n (Fin.castAdd a u)) = true ∧ x (Fin.natAdd n (Fin.castAdd a w)) = true) || decide (∃ i : Fin a, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)) s)) := by
  classical
  intro n k a K _ g S c q hn _hz0 hz1 cov
  obtain ⟨u,w,hs,he⟩ := orient K S cov
  let m := n+((k+1)+a)
  let Y (i : Fin n) : Fin m := Fin.castAdd _ i
  let V (i : Fin (k+1)) : Fin m := Fin.natAdd n (Fin.castAdd a i)
  let X (i : Fin a) : Fin m := Fin.natAdd n (Fin.natAdd (k+1) i)
  let B (x : Fin m → Bool) := g (fun i => x (Y i)) (x (V 0))
  let T (v : Fin (k+1)) : Finset (↥K.edgeFinset) := Finset.univ.filter (fun e => u e = v)
  let l (e : ↥K.edgeFinset) := V (w e)
  let t := Gap548Circuit.star T V l
  have hsum : K.edgeFinset.card = ∑ v ∈ S, (T v).card := by
    have h : (↑(Finset.univ : Finset (↥K.edgeFinset)) : Set _).MapsTo u S := fun e _ => hs e
    simpa [T] using Finset.card_eq_sum_card_fiberwise h
  have eq (x : Fin m → Bool) : (∃ i j, K.Adj i j ∧ x (V i) = true ∧ x (V j) = true) ↔ ∃ v ∈ S, t v x = true := by
    simpa [t,Gap548Circuit.star,row,T,l] using oriented_edges K S u w hs he (fun i => x (V i))
  let Z := fun x : Fin m → Bool => B x || decide (∃ i j, K.Adj i j ∧ x (V i) = true ∧ x (V j) = true) || decide (∃ i, x (X i) = true)
  have finalEq : Z = (fun x => joined B S t x || decide (∃ i, x (X i) = true)) := by
    funext x; apply Bool.eq_iff_iff.mpr; simp [Z,joined,eq]
  change (_ → _ → HasCircuitSize m Z _) ∧ (_ → _ → ∀ s, _ → HasCircuitSize m Z s)
  constructor
  · intro _ hc
    let π : Fin (n+1) → Fin m := Fin.snoc Y (V 0)
    have hb : HasCircuitSize m B c := by
      have h := relabel_size π (baseG g) c hc
      have e : (fun x => baseG g (x ∘ π)) = B := by funext x; simp [baseG,B,π]
      rwa [e] at h
    have h := finish X (attachStars S T V l hb)
    rw [finalEq]
    exact weaken h (by omega)
  · intro hS hq s hbound
    let I := S.erase 0
    have hi : I.card + 1 = S.card := Finset.card_erase_add_one hS
    have hed : (∑ v ∈ I, (T v).card) + (T 0).card = K.edgeFinset.card :=
      (Finset.sum_erase_add _ _ hS).trans hsum.symm
    let f (x : Fin m → Bool) := B x || t 0 x
    have joinEq : joined f I t = joined B S t := by
      funext x; apply Bool.eq_iff_iff.mpr
      have es : S = insert 0 I := (Finset.insert_erase hS).symm
      simp [joined,f,es,or_assoc]
    suffices H : ∃ d, HasCircuitSize m f d ∧ d+2 ≤ q+(T 0).card+1 by
      obtain ⟨d,hd,hcost⟩ := H
      have h := finish X (attachStars I T V l hd)
      change HasCircuitSize m (fun x => joined f I t x || decide (∃ i, x (X i) = true)) _ at h
      rw [joinEq,← finalEq] at h
      exact weaken h (by omega)
    by_cases h0 : (T 0).Nonempty
    · let π : Fin (n+1+1) → Fin (m+1) := Fin.snoc
          (Fin.snoc (fun i : Fin n => (Y i).castSucc) (V 0).castSucc) (Fin.last m)
      let A (z : Fin (m+1) → Bool) := extG g (z ∘ π)
      have ha : HasCircuitSize (m+1) A q := relabel_size π (extG g) q hq
      have hl : ∃ x, row (T 0) l x = true := ⟨fun _ => true,by simp only [row,decide_eq_true_eq]; obtain ⟨e,he⟩ := h0; exact ⟨e,he,by trivial⟩⟩
      have h := plug (row (T 0) l) A (row_nonempty (T 0) l h0) ha hl
      have e : (fun x => A (Fin.snoc x (row (T 0) l x))) = f := by
        funext x; simp [A,extG,π,f,B,t,Gap548Circuit.star]
      rw [e] at h
      have pos := Finset.card_pos.mpr h0
      exact ⟨_,h,by omega⟩
    · have pos := positive hn hz1 hq
      obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
      subst q
      have hh := specialize hn hz1 hq
      let π : Fin (n+1) → Fin m := Fin.snoc Y (V 0)
      have h := relabel_size π (baseG g) r hh
      have em : T 0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0
      have e : (fun x => baseG g (x ∘ π)) = f := by
        funext x; simp [f,B,t,Gap548Circuit.star,row,em,π,baseG]
      rw [e] at h
      exact ⟨_,h,by omega⟩
