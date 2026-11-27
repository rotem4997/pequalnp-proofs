import PEqualNP.Defs

-- Circuit normalization and soundness of the barrier checker follow L-meta-927, Apache-2.0.
namespace PEqualNP.Outside.L_meta_9140

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

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

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
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

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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
    · simp [hlt, statValid, statVal, wiresFrom]
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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
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
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
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
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
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
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

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
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 18 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 12 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT : ℕ → ℕ) (S : ℕ → ℕ → List ℕ) (hroot : S cap 0 = xs)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k S NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      rw [← hroot] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)


def six : BFn 6 := fun x => decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true)

def edgeFn : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3)

def sampleRows : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 16, 16, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 3, 5, 17, 33, 3, 6, 10, 18, 5, 6, 12, 10, 12, 3, 5, 6, 10, 11, 12, 13, 17, 18, 25, 33, 41, 17, 18, 21, 22, 28, 25, 26, 28, 33, 3, 5, 6, 10, 12, 17, 18, 33, 35, 38, 42, 50, 37, 38, 44, 41, 42, 44, 49, 50, 3, 5, 6, 10, 12, 17, 18, 33, 53, 54, 60, 3, 5, 6, 10, 12, 17, 18, 33, 57, 58, 60]
def inputWords : List Nat := [0x34668d2468e4bda611f0000000000001ffe00f, 0x49a9364bd349423aaf100000003ffc000000f0, 0x82dc589c859380cd722001ffc1c00038000700, 0xe31060f1061e14f1c40ffe000e0001c1fff800, 0xec1d8302181fe700084ffffff00001fe000000, 0xf01e03ffe0201800008ffffffffffe00000000]

def bankWordChunk (i : Nat) : Nat := (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x8000880000000000000000000000000000000080000000100000000000000000000000000000400040000000000000000000000000000000004000000008000000000000000000000000000000000400000000000000000000000000000000000000000008000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000 else 0xcc180c8181800c322001ffc1c0003800070000a81408c141002a2310000000000000000000008c100c81010008220000000000000000000000881008c101000822000000000000000000000088100881010008220000000000000000000000640c0440c080a611300000000000000000000044080400808084102000000000000000000000200400404000220110000000000000000000) else (if i < 3 then 0x3e07c0007c000fff730000000000001ffffff038070d987000059e60000000ffffe00001ff0030060f1060010f1c40000000e000001fff80003006000061e04f1c4000000000001c1fff80002c0589c858000cd7220000001c0000000070002c05800059380cd722000000000003800070001a03449c340003aa7100000003ffc000000f000cc180c8181808c3220000000000000000000 else (if i < 4 then 0xc018000181fe70008400000000001fe0000000b817000171b4259ee000000000001fe001ff009a134001349423aaf100000000000000000f008a9160ad141420a2b100000003ffc000000f00889120a910142082a0001fff1fffe3e0007f00640c8000c96a5c550600000000001ffffff0f04608c0008c4a5a61170000000000001ffe00f03e07cd987c000fff73000000ffffe01ffffff else 0x100200b420201800008000000fc002000000001002006160201800008000000e3ffe00000000100200246020180000800000000000000000000fe1fc001fdfe7ffff700000000001ffffffff0d21a4001a4c67328d500000000001c7fff8ff0ce19c0019c1e30e3b7000000000003e0007ff0c0d8302181fe700084001fff00001fe0000000c0d83021801e300084001fff000003e000000))) else (if i < 7 then (if i < 6 then 0x124248b424a018c550a000000fc00201ffff0f11a234fde360183aa79000000ffffe000000f01122246162601832859000000e3ffe01fff8ff10e21c0ce1e0080e33b0000001fffe000007ff10620c2460e018a611b0000000000001ffe00f100e03ffe0201800008001fffffffe00000000100e030ee0200800008001fff1fffe00000000100200fde0201800008000000ffffe00000000 else 0x1fefff0effffeffffff001fff1ffffffffffff1fe3fcfdfffffffffff000000fffffffffffff1cef9f0ef9e1eb0e3bf001fff1fffe3e0007ff1c23870278606b0209d00000303ffe060000ff14668d0468e0a90611f000000000000000000f1446890428a0a90410e001fff1c0023e00070f13e27cfde7e018fff7b000000ffffe01ffffff12c258fde5a018cd72a000000ffffe00000700) else (if i < 8 then 0x240481000804a500004000000000000000000020440824008494a41020000000000001ffe00020200420404414a20110000000000001ffe0002004010000000000000000000000000000000020000020000414a00000000000000001ffe00020000020000010000000000000000000000000200000000004040000000000000000000000001fefffffffe1fbfffff001fffffffe3fffffff else (if i < 9 then 0x3006012460201800008000000000000000000030060124202018000080000000000000000000300201206020180000800000000000000000003002012020201800008ffe003e0002000000002c0d83021805e700084001fff000003e000000244489040884a5841060000000000000000000242485004844a5220150000000000000000000240481200804b5a00040000000000001ffe000 else 0x300e032ee0201800008001fff1fffe00000000300e012ce02018000080000000000000000000300601fde0201800008000000ffffe000000003006012460241ca00080000000000001ffe0003006012460241c000080000000000000000000300601246020980000800000000000000000003006012460201880008000000000000000000030060124602018200080000000000000000000)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x342685246864bd2201d00000000000000000003422852068643d2201d0000000000001ffe00f340681246824bd0000c00000000000000000003402812028243d0000cffe003e0003c7fff80f308e112ce1211808228000000000000000000030660d2460e098a611b00000000000000000003046092460a0988410a000000000000000000030260524606018220190000000000000000000 else 0x346e8d2ce8e4bda611f0000000000001ffe00f346e8d2468e5bda611f0000000000001ffe00f34668d2468e4bda611f0000000000001ffe00f34668d2468e4bda611f000000000000000000034668d2468e4bd8611f0000000000001ffe00f34668d2468e4bd2611f0000000000001ffe00f3446892468a4bd8410e00000000000000000003446892428a4bd8410e0000000000001ffe00f) else (if i < 13 then 0x4008024bc000000000000000003ffc000000004008020200000000000000000000000000000040000041000000000000000000000000000000400000000008000000000000000000000000003fe7fd247ffffffffff00000000001ffffffff3cef9f2ef9e5ffae3bf001fff1fffe3fffe7ff37e6fdfdefe4bdfff7f000000ffffe01ffffff34ee9d2ce9e5bdae33f0000000000001ffe00f else (if i < 14 then 0x48090202500942000800000000000000000000480902021009420008000000000000000000004188304983090038a600000000000000000000412024414248003285100000000000000000004108224bc208003084000000003ffc00000000410020410208003084000000000000000000004088124bc101000822000000003ffc000000004028064bc040002201100000003ffc00000000 else 0x49a9364b9349423aaf100000003ffc000000f04989324b93094218ae000000003ffc000000f049212643524842328d100000003ffc000000f049092243120942308c0000000000000000000049012243120842108c0ffe003e3fffc60018f04889120a910942082a00000000000000000000482906025049422209100000000000000000004809024bd009420008000000003ffc00000000))) else (if i < 18 then (if i < 16 then 0x4d21a6431a4c67328d5ffe003e3fffc7fff8ff4c098202181fe70008400000000001fe0000004c018202180c6700084ffe00300001c600000049ed3e4fd3c9c2bebf300000003ffc000000f049ad364fd349423aaf100000003ffc000000f049ad364bd349c23aaf100000003ffc000000f049a9364bd34942baaf100000003ffc000000f049a9364bd349423aaf100000003ffc000000f0 else (if i < 17 then 0x61002061020c1430840ffe000e0001c1fff800610020610208103084000000000000000000005defbf4ffbe9eb3ebff001fff1fffe3e0007ff5beb7efff7e95affffb000000ffffe01ffffff59ab36fff3695a3aaf9000000ffffe000000f059ab366ff3695a3aaf900000003ffc000000f0500a02ffe0201800008000000ffffe000000004fe9fe4bdfdfe7ffff700000003ffdffffffff else 0x6c018302181fe700084ffe00300001fe0000006c018302180c6700084ffe00300001c600000069ad374bd349423aaf100000003ffc000000f069a9366bd34d56baaf100000003ffc01ffe0f069a9366bd349523aaf100000003ffc000000f069a9364bd34d463aaf100000003ffc000000f0680d030210094200080000000000000000000061002061020c14b08400000000000001ffe000)) else (if i < 19 then 0x7002036360201800008ffe003e3ffe000000006dedbf4fdbcde7bebf700000003ffc000000f06dadb74bdb4de73aaf500000003ffc000000f06ccd9b0e998de78c3a600000000000000000006c0d8302180de700084ffffff00001fe0000006c0d8302180de70008400000000000000000006c098302180d6700084ffe00300001c60000006c058302180ce700084ffe00300001c6000000 else (if i < 20 then 0x70ce1b6fe1a1988c32a00000003ffc00000000700e036fe0201800008ffffffffffe00000000700e036fe020180000800000003ffc00000000700e0326602018000080000000000000000000700a036be0201800008ffe003e3ffe000000007006036760201800008ffe003e3ffe0000000070060165602018000080000000000000000000700203ffe0201800008ffe003ffffe00000000 else 0x780f032670295a00088000000000000000000075eebd6debedbdbeb7f0000000000001ffe00f7566ad656aecbdb695f0000000000001ffe00f746e8f6fe8e4bda611f00000003ffc01ffe00f746e8f2668e4bda611f0000000000001ffe00f74668d6568e4bda611f0000000000001ffe00f74668d2468ecbda611f0000000000001ffe00f71062165622818308480000000000000000000))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then 0x79ef3f6ff3e9dabebfb00000003ffc000000f079af376ff36d5e3aaf900000003ffc000000f079af376ff369da3aaf900000003ffc000000f079af376ff3695abaaf900000003ffc000000f079af376ff3695a3aaf900000003ffc000000f079ab376bf3695a3aaf9ffe003e3ffe000000f079ab376bf3695a3aaf900000003ffc000000f07923276372685a328d9ffe003e3ffe000000f0 else 0x7cef9f2ef9edffae3bf0000000000001ffe00f7c6f8f2678edffa619f0000000000001ffe00f7c0f836ff82dff0008c00000003ffc000000007c0f8367782dff0008c00000000000000000007c0f8326782dff0008c00000000000000000007c078326782c7f0008cffe00300001c60000007c038363782c7f0008cffe003e3fffc60000007c038322782c7f0008cffe00300001c6000000) else (if i < 24 then 0x7defbf6ffbedffbebff00000003ffc01ffe0ff7defbf6ffbedffbebff00000003ffc000000f07defbf6ffbedff3ebfffffffffffffffffffff7dafb76ffb6dff3aafd00000003ffc000000f07dabb76bfb6d7f3aafdffe003e3fffc7fff8ff7d6faf677aedffb69df0000000000001ffe00f7d67af677aecffb69dfffe003e3fffc7fff8ff7d23a7637a6c7f328ddffe003e3fffc7fff8ff else (if i < 25 then 0x801c009c80000000000001ffc1c00000000000801c000400138000000001ffc0000038000000801c000000138000000001ffc0000038000000801c000000000000000001ffc000000000000080100090000000000000000000000000000000801000000012000000000000000000000000007fe3ffffffec7ffffffffe003fffffc7ffffff7fe3ff637ffffffffffffe003e3fffffffffff else 0x821c4090041380c1400001ffc000003800000082104090041200c140000000000000000000008210409004120041400fffffffc003fe001f00809c109c81010008220001ffc1c00000000000809c100881138008220001ffc0000038000000805c089c80808084102001ffc1c00000000000805c080400938084102001ffc0000038000000801c009c80138000000001ffc1c00038000000))) else (if i < 28 then (if i < 27 then 0x82d85898859380cd722001ffc1c0003800070082d4589c859280cd722001ffc1c0003800070082d0589c859200cd7220000001c0000000070082985098851300c962000000000000000000008298509885130049620001ffc1c0003800070082544894049280c5502001ffc1c0003800070082544894049280c55020000000000000000000821c409c841200c1400001ffc1c00000000000 else 0x8650c8900c96a5c5506fffffffc003ffffff0f831060f1061210f1c40000000e000001fff80082fc5c9cc5d380ef733001ffc1c0003800070082dc589cc59380cd722001ffc1c0003800070082dc589c859380ed722001ffc1c0003800070082dc589c859380cd722001ffc1c0003800070082dc589c859380cd722000000000000000000082d8589c859300cd722001ffc1c00038000700) else (if i < 29 then 0xa01c010000138000000001ffc00000380000009effdf9efdf3ebcf7bf001fff1fffe3e0007ff93fe7cfde7f398fff7b001ffcffffe39ffffff92de58fde5b398cd72a001ffcffffe3800070092de58bce5b398cd72a001ffc1c00038000700901e00fde0201800008001ffcffffe000000008ffdfc9c9fdfe7ffff7001ffc1c001ffffffff8edddb9e9d93e3cd7a6001fff1c0003e000700 else (if i < 30 then 0xa31060f1061614f1c40ffe000e0001c1fff800a2dc599c859380cd722001ffc1c00038000700a2dc58bc859794ed722001ffc1c00039ffe700a2dc58bc859390cd722001ffc1c00038000700a2dc589c859784cd722001ffc1c00038000700a21040b0041614e14000000000000001ffe000a21040b0041614c1400ffe000e0001c1fff800a21040b0041210c14000000000000000000000 else 0xb01601b4602018000080000000000000000000b01601b420201800008fffffffc00200000000aedddb9e9d97e7cd7a6001fff1c0003e000700ac1d83021817e700084ffffff00001fe000000a6fcdd9ccdd7a5ef737001ffc1c00038000700a6dcd99c8d97a5cd726001ffc1c00038000700a41c81000817a500004001ffc0000038000000a41481000816a500004ffffff00001fe000000)))) else (if i < 36 then (if i < 33 then (if i < 32 then 0xb0be15bce161182a239001ffc1c00000000000b01e03bee0201800008ffffffffffe00000000b01e01bce0201800008001ffc1c00000000000b01e01bca0201800008fffffffc00200000000b01e012460339800008001ffc0000038000000b01e012460201800008001ffc0000000000000b01601fde0201800008ffffffffffe00000000b01601b460201800008fffffffc00200000000 else 0xb2fe5dbce5f398ef73b001ffc1c00038000700b2de59bce5b79ccd72a001ffc1c00038000700b2de59bce5b398ed72a001ffc1c00038000700b2de59bce5b398cd72a001ffc1c00038000700b2de59bca5b398cd72afffffffc00238000700b2de59bca5b398cd72a001ffc1c00038000700b25649b424b298c550afffffffc00238000700b21641b4643218c14080000000000000000000) else (if i < 34 then 0xb676cdb46cf6bde751f0000000000001ffe00fb656c9b42cb6bdc550efffffffc003ffffff0fb47e8dbce8e4bda611f001ffc1c00001ffe00fb47e8d2468f7bda611f001ffc0000039ffe00fb4768db468e4bda611f0000000000001ffe00fb4768d2468f6bda611f0000000000001ffe00fb41e81bce837bd0000c001ffc1c00038000000b41681b42836bd0000cfffffffc003fe000000 else (if i < 35 then 0xbeffdfbefdf7ffcf7bffffffffffffffffffffb7f6fdfdeff6bdfff7ffffffffffffffffffffb6feddbcedf7bdef73f001ffc1c00039ffe70fb6feddbcedf7bdef73f001ffc1c00038000700b6feddbcedf7bdef73f0000000000001ffe00fb6ded9bcedb7bdcd72e001ffc1c00038000700b6ded9bcadb7bdcd72efffffffc003ffffff0fb676cdb46cf6bde751ffffffffc003ffffff0f else 0xc31060d1061a0051c40ffe000e0001c0001800c2dc5adfc59380cd722001ffc1fffc38000700c2dc5a9e859380cd722001ffc1c00038000700c2dc58dd859380cd722001ffc1c00038000700c2dc589c859b80cd722001ffc1c00038000700c01c02dfc0000000000001ffc1fffc00000000c01802db80000000000ffffffffffe00000000bff7fdb43fffffffffffffffffc003ffffffff))) else (if i < 39 then (if i < 37 then 0xc3fc7cddc7db80fff73001ffc1c00038000700c3dc78dd879b80fdf62001ffc1c00038000700c3746cd546da80f7d530000000000000000000c31060f1061a10f1c40ffe000e0001c1fff800c31060d1061e04f1c40ffe000e0001c1fff800c31060d1061a00f1c400000000000000000000c31060d1061a00d1c40ffe000e0001c0001800c31060d1061a0071c40ffe000e0001c0001800 else (if i < 38 then 0xcadd5a9ed59bc2cd7a2001ffc1c00038000700cadd5a9e959bc2cd7a2001ffc1c00038000700c9bd36dfd349423aaf1001ffc1fffc000000f0c9bd364bd35bc23aaf1001ffc03ffc380000f0c9b936dbd349423aaf100000003ffc000000f0c9b9364bd35b423aaf100000003ffc000000f0c81d0202101bc200080001ffc0000038000000c8190202101b4200080ffffff00001fe000000 else 0xcbfd7edfd7dbc2ffff3001ffc1fffc380007f0cbfd7edfd7dbc2ffff300000003ffc000000f0cbdd7adf979bc2fdfe2001ffc1c00038000700cbdd7adf979bc2ddfe2ffffffffffffe001ff0cbb976dbd75b42fbef100000003ffc000000f0cbb976dbd75b427bef1ffffffffffffe001ff0cb9972db971b4259ee0ffffffffffffe001ff0cafd5e9ed5dbc2ef7b3001ffc1c00038000700)) else (if i < 40 then 0xe0100020001e1400000ffe00000001c0000000e0100000001e0400000ffe00000001c0000000e010000000000000000ffe0000000000000000dfffffdffffbeb5ffffffffffffffffe001fffdbfb7efff7fb5affffbfffffffffffffffffffd01a02ffe0201800008ffffffffffe00000000cff9fedb9fdfe7ffff7fffffffffffffffffffcc198202181fe700084ffffff00001fe000000 else (if i < 41 then 0xe01c030200000000000ffffff0000000000000e01c00fd80001000000fffffcfc00000000000e01c0000001f8400000fffffc00001f8000000e01802fbc0001000000ffe000e3ffc00000000e01000f1001e1400000ffe000e0001c0000000e01000f1000414a0000ffe000e000001ffe000e01000f100001000000ffe000e000000000000e0100020001e14a0000ffe00000001c1ffe000 else 0xe2104090041e04c1400ffe00000001c0000000e11020f102081030840ffe000e000000000000e1102041021e0430840ffe00000001c0000000e01c03f300001000000ffffffe000000000000e01c039e80000000000ffffff1c00000000000e01c034bc0000000000ffffff03ffc00000000e01c0302001e0400000ffffff00001c0000000e01c030200138000000ffffff0000038000000)))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then 0xe31060f1061a10f1c400000000000000000000e31060f1061a1051c40ffe000e0001c0001800e31060d1061e04f1c40ffe00000001c0000000e31060d1061e0451c40ffe000e0001c0001800e2dc5b9e859380cd722ffffff1c00038000700e2dc58fd859390cd722fffffcfc00038000700e2dc589c859f84cd722fffffc1c001f8000700e21040f1041210c1400ffe000e000000000000 else 0xe31460f5061e14f1c40ffe000e0001c1fff800e31460f1061e94f1c40ffe000e0001c1fff800e31060f1461e14f1c40ffe000e0001c1fff800e31060f1061e14f1c40ffe000e0001c1fff800e31060f1061e14f1c400000000000001ffe000e31060f1061e14d1c40ffe000e0001c1fff800e31060f1061e1471c40ffe000e0001c1fff800e31060f1061a10f1c40ffe000e000000000000) else (if i < 45 then 0xe31c63f3061e14f1c40ffffffe0001c1fff800e31c60fd861e14f1c40fffffcfc001c1fff800e31c60f1061f94f1c40fffffce0001f9fff800e31862fbc61e14f1c40ffe000e3ffdc1fff800e31862f3061e14f1c40ffe000e0001c1fff800e31860f9861e14f1c40ffe000e0001c1fff800e31860f1061f14f1c40ffe000e0001c1fff800e31461f1061e14f1c40ffe000e0001c1fff800 else (if i < 46 then 0xe3dc78fd879b90fdf62001ffc1c00038000700e3b874f9c75f14fbe71ffe000e0001c1fff800e39c70fd871f14f9e60ffe000e0001c1fff800e39870f9c71f14f9e60ffe000e0001c1fff800e39870f9871f14f9e60ffe000e0001c1fff800e3746cf546de94f7d53ffe000e0001c1fff800e35468f5069e94f5d42ffe000e0001c1fff800e33064f1465e14f3c51ffe000e0001c1fff800 else 0xe770ecf10edeb5f7d57ffe000e0001c1fff80fe754e9f50e9eb5f5d46ffe000e0001c1fff800e734e5f14e5eb5f3c55ffe000e0001c1fff800e714e1f10e1eb5f1c44ffe000e0001c1fff800e41c83020804a500004ffffff0000000000000e4148100081ea500004ffe00000001c0000000e3dc78fd879f94fdf62fffffcfc001f9ffff00e3dc78fd879f94fdf62ffe000e0001c1fff800))) else (if i < 49 then (if i < 48 then 0xeb1962f3561f56f1cc0ffe000e0001c1fff800eb1962f3161f56f1cc0ffe000e0001c1fff800eadd5b9e959bc2cd7a2001ffc1c00038000700e9bd374bd349423aaf1ffffff03ffc000000f0e9b936fbd349523aaf1ffe000e3ffc000000f0e9b9364bd35f463aaf1ffe00003ffdc00000f0e81d030210094200080ffffff0000000000000e8190202101f4600080ffe00000001c0000000 else 0xec118302181e6700084ffe00300001c6000000ebfd7effd7dfd6ffff3fffffcffffdf9fffff0ebb976fbd75f56fbef1ffe000e3ffdc1fff8f0ebb976fbd75b52fbef100000003ffc000000f0eb9972fb971f56f9ee0ffffffffffffffffff0eb9972fb971f56f9ee0ffe000e0001c1fff800eb3966f3565f56f3cd1ffe000e0001c1fff800eb1d63f3161f56f1cc0ffe000e0001c1fff800) else (if i < 50 then 0xec1d8302181fe720084ffffff00001fe000000ec1d8302181fe700084ffffff00001fe000000ec1d8302181fe700084ffe00000001c0000000ec1d8302181fe700084001ffc0000038000000ec1d8302180de700084ffffff0000000000000ec1d8302180c6700084ffffff00001c6000000ec198302181f6700084ffffff00001fe000000ec158302181ee700084ffffff00001fe000000 else (if i < 51 then 0xec1d834bd81fe700084ffffff03ffdfe000000ec1d8343181fe700084ffffff00001fe000000ec1d8322181ff7a0084ffffff00001ffffe000ec1d8322181ff700084ffffff00001fe000000ec1d830a981fe700084ffffff00001fe000000ec1d8306181fe700084ffffff00001fe000000ec1d8302581fe700084ffffff00001fe000000ec1d8302181fe780084ffffff00001fe000000 else 0xec7d8f0658dfe7a6197ffffff00001fe000000ec5d8b9e989fe784186ffffff1c001fe000000ec5d8b06189fe784186ffffff00001fe000000ec3d8702585fe722095ffffff00001fe000000ec1d83ff981ff700084fffffffc001fe000000ec1d83f3181ff700084ffffffe0001fe000000ec1d839e981fe700084ffffff1c001fe000000ec1d8392181fe700084ffffff00001fe000000)))) else (if i < 57 then (if i < 54 then (if i < 53 then 0xed1da3431a1fe7308c4ffffff00001fe000000ecdd9b0e999fe78c3a6ffffff00001fe000000ecdd9b0e999fe70c3a6ffffff1c001fe000700ecbd970ad95fe72a2b5ffffff00001fe000000ec9d939e991fe7082a4ffffff1c001fe000000ec9d930e991fe7082a4ffffff00001fe000000ec9d930ad91fe7082a4ffffff00001fe000000ec9d930a991fe7082a4ffffff00001fe000000 else 0xee1dc39e9c1fe7c1484ffffff1c001fe000000ee1dc3921c1fe7c1484ffffff00001fe000000ee1dc3921c1fe741484fffffffc003fe001f00edbdb74bdb5fe73aaf5ffffff03ffdfe0000f0ed9db34b9b1fe738ae4ffffff00001fe000000ed3da7435a5fe7328d5ffffff00001fe000000ed1da3f31a1ff7308c4ffffffe0001fe000000ed1da3631a1ff7308c4ffffff00001fe000000) else (if i < 55 then 0xeedddb9e9d9fe7cd7a6001ffc1c00038000700eedddb021d9fe7cd7a6ffffff00001fe000700ee9dd39a9d1fe7c96a4ffffff00001fe000000ee9dd39a9d1fe7496a4ffffff1c001fe000700ee5dcb961c9fe7c5586ffffff1c001fe000700ee5dcb961c9fe7c5586ffffff00001fe000000ee1dc3f31c1ff7c1484ffffffe0001fe000000ee1dc3b21c1ff7c1484ffffff00001fe000000 else (if i < 56 then 0xef1de3f31e1ff7f1cc4ffffffe0001fffff800ef1de3f31e1ff7f1cc4ffe000e0001c1fff800ef1de3d31e1fe7f1cc4ffffff00001fe000000ef1de3d31e1fe751cc4ffffffe0001fe001800ef11e3f31e1e77f1cc4ffe003e0001c7fff800eefddf9edddfe7ef7b7ffffff1c001fe000700eedddbff9d9ff7cd7a6fffffffc001fe000700eedddb9e9d9fe7cd7a6ffffff1c001fe000700 else 0xf01200fde0201800008ffe000ffffe00000000effdffdfdfdfe7ffff7ffffff1fffdfe0007f0effdff021fdfe7ffff7ffffff00001ffffffffeff1fcf11fdff7ffff7ffe000e0001ffffffffefddfbff9f9ff7fdfe6fffffffc001ffffff00efddfbdf9f9fe7fdfe6ffffff1c001fe000700efbdf7fbdf5ff7fbef5ffffffe3ffdfffff8f0ef9df3db9f1fe759ee4ffffffffffffe001ff0))) else (if i < 60 then (if i < 58 then 0xf01a03fbe0201800008ffffffffffe00000000f01603f760201800008ffffffffffe00000000f01601f560201800008ffe000e000000000000f01601f5602018000080000000000000000000f01601f520201800008fffffffc00200000000f0160124603e1c00008ffe00000001c0000000f016012460201800008ffe0000000000000000f01203f360201800008ffe003e3ffe00000000 else (if i < 59 then 0xf01e03ffa0201800008ffffffffffe00000000f01e03f760201800008ffffffe000000000000f01e03bee0201800008ffffff1c00000000000f01e03b620201800008fffffffc00200000000f01e036fe0201800008ffffff03ffc00000000f01e036360201800008ffffffe3ffe00000000f01e032660201800008ffffff0000000000000f01e01fde0201800008fffffcfc00000000000 else 0xf01e03ffe0241c00008ffffffffffe00000000f01e03ffe0211800008ffffffffffe00000000f01e03ffe0209800008ffffffffffe00000000f01e03ffe0201880008ffffffffffe00000000f01e03ffe0201820008ffffffffffe00000000f01e03ffe0201800008ffffffffffe00000000f01e03ffe0201800008ffe000e3ffc00000000f01e03ffe0201800008001ffc1fffc00000000)) else (if i < 61 then 0xf05e0b2660b3988410affffff0000038000000f03e07ffe0601822019ffffffffffe00000000f01e03ffe03f9c00008ffffffffffff8000000f01e03ffe03e1c00008fffffffffffc0000000f01e03ffe0339800008ffffffffffe38000000f01e03ffe0321800008ffffffffffe00000000f01e03ffe0281800008ffffffffffe00000000f01e03ffe0241ca0008ffffffffffe01ffe000 else (if i < 62 then 0xf0de1bffe1a1988c32affffffffffe00000000f0de1bffe1a1980c32affffffffffe38000700f0be17ffe161182a239ffffffffffe00000000f09e13ffe1339808228ffffffffffe38000000f09e13ffe1211808228ffffffffffe00000000f07e0fffe0e098a611bffffffffffe00000000f05e0bffe0b3988410affffffffffe38000000f05e0bffe0a0988410affffffffffe00000000 else 0xf21e43ffe43218c1408ffffffffffe00000000f21e43ffe4321841408ffffffffffffe001f00f1be37ffe360183aa79ffffffffffe000000f0f19e33ffe3291838a68ffffffffffe00000000f13e27ffe2681832859ffffffffffe00000000f13625f562681832859ffe000e000000000000f11e23ffe23e1c30848fffffffffffc0000000f11e23ffe2281830848ffffffffffe00000000))))) else (if i < 73 then (if i < 68 then (if i < 65 then (if i < 64 then 0xf2de59fde5b398cd72a001ffc1c00038000700f29e53ffe53318c9628ffffffffffe00000000f29e53ffe5331849628ffffffffffe38000700f25e4bffe4b298c550affffffffffe38000700f25e4bffe4b298c550affffffffffe00000000f25649f564b298c550affe000e000000000000f21e43ffe43e1cc1408fffffffffffc0000000f21e43ffe43398c1408ffffffffffe38000000 else 0xf2fe5fffe5f398ef73bffffffffffe38000700f2de5bffe5bf9ccd72affffffffffff8000700f2de5bffe5b398cd72affffffffffe38000700f2de5bffe5b398cd72a001ffc1fffc38000700f2de5bffe5a018cd72affffffffffe00000700f2de5bbee5b398cd72affffff1c00038000700f2de5bbee5b398cd72a001ffc1c00038000700f2de59fde5b398cd72afffffcfc00038000700) else (if i < 66 then 0xf35669f566be9cf5d4affe000e0001c1fff800f33665f5667e1cf3c59ffe000e0001c1fff800f31e63ffe63e1cf1c48fffffffffffc1fff800f31e63ffe63a18f1c48ffffffffffe00000000f31e63ffe63a1851c48fffffffffffc0001800f31661f5663e1cf1c48ffe000e0001c1fff800f31661f5663a18f1c480000000000000000000f31661f5663a1851c48ffe000e0001c0001800 else (if i < 67 then 0xf3f27cfde7fe1cfff7bffe000fffffc1fffffff3de7bffe7bf9cfdf6affffffffffff9ffff00f3de7bffe7bb98fdf6affffffffffe38000700f3de79fde7bf9cfdf6afffffcfc001f9ffff00f3de79fde7bb98fdf6a001ffc1c00038000700f39e73ffe7201859e68ffffffffffe00001ff0f3766df566fa98f7d5bffe000e000000000000f3726cf566fe1cf7d5bffe000e0001c1fff80f else 0xf45e8bffe8a4bd8410effffffffffe00000000f43e87ffe864bd2201dffffffffffe00000000f41e83ffe83ebd0000cfffffffffffc0000000f41e83ffe837bd0000cffffffffffe38000000f41e83ffe836bd0000cffffffffffffe000000f41e83ffe824bd0000cffffffffffe00000000f41681f5683ebd0000cffe000e0001c0000000f3fe7fffe7e018fff7bffffffffffe01ffffff))) else (if i < 70 then (if i < 69 then 0xf712e1f12e3e3df1c4cffe003e0003c7fff80ff6fedfffedf7bdef73fffffffffffe39ffe70ff6dedbffedb7bdcd72effffffffffe38000700f65ecbffecb6bdc550efffffffffffffffff0ff47e8fffe8e4bda611fffffffffffe01ffe00ff47e8f2668e4bda611fffffff0000001ffe00ff4768df568e4bda611fffe000e000001ffe00ff4768d2468febda611fffe00000001c1ffe00f else 0xf7fefdfdefffbdfff7fffe000e0001c1fff80ff77eefffeefebdf7d5ffffffffffffc1fff80ff776edf56efebdf7d5fffe000e0001c1fff80ff776edf56efebdf7d5f0000000000001ffe00ff756e9f52ebebdf5d4efffffffc003ffffff0ff756e9f52ebebdf5d4effe000e0001c1fff80ff732e5f16e7e3df3c5dffe000e0001c1fff80ff716e1f56e3ebdf1c4cffe000e0001c1fff800) else (if i < 71 then 0xf89f13fff1215a082a8ffffffffffe3e0007f0f83f07fff0695a22099ffffffffffe00000000f83f072670695a22099ffffff0000000000000f81f03fff03f5e00088fffffffffffc0000000f81f03fff03bda00088ffffffffffe38000000f81f03fff03b5a00088ffffffffffffe000000f81f03fff0295a00088ffffffffffe00000000f7fefdfdefffbdfff7ffffffcfc001f9ffff0f else (if i < 72 then 0xf9bf37fff3695a3aaf900000003ffc000000f0f9bf376ff3695a3aaf9ffffff03ffc000000f0f99f33fff3295a18ae8ffffffffffe000000f0f93f27fff2685a328d9ffffffffffe000000f0f91f23fff2295a308c8ffffffffffe00000000f91f23fff2285a108c8fffffffffffc60018f0f8bf17fff1615a0a2b9ffffffffffe000000f0f89f13fff1295a082a8ffffffffffe00000000 else 0xfadf5bfff5bbdacd7aaffffffffffe38000700fadf5bbef5bbdacd7aa001ffc1c00038000700f9ff3ffff3e9dabebfbffffffffffe000000f0f9bf37fff37f5e3aaf9fffffffffffc00000f0f9bf37fff37bda3aaf9ffffffffffe380000f0f9bf37fff3695a3aaf9ffffffffffe000000f0f9bf37fff3695a3aaf9ffe000e3ffc000000f0f9bf37fff3695a3aaf9001ffc1fffc000000f0)))) else (if i < 78 then (if i < 75 then (if i < 74 then 0xfbff7ffff7fbdaffffb001ffc1fffc380007f0fbdf7bfff7bbdaddfeaffffffffffffe001ff0fbbf77fff77f5efbef9fffffffffffc1fff8f0fbbf77fff77f5efbef9ffe000e3ffdc1fff8f0fbbf77fff77b5afbef9ffffffffffe000000f0fbbf77fff77b5afbef900000003ffc000000f0fbbf77fff77b5a7bef9ffffffffffffe001ff0fb9f73fff73b5a59ee8ffffffffffffe001ff0 else 0xfc1f832ef83fff0008cffffff00001fe000000fc1f8326783fff8008cffffff00001fe000000fc1f8326783fff2008cffffff00001fe000000fc1f8326783fff0008cffffff00001fe000000fc1f8326383fff0008cffffff00001fe000000fc1f8322783fff0008cffffff00001fe000000fc1f8322383fff0008cffffffe0003fe000000fbff7ffff7fbdaffffbffffffffffe380007f0) else (if i < 76 then 0xfc1f83bef83fff0008cffffff1c001fe000000fc1f83beb83fff0008cfffffffc003fe000000fc1f83b6783fff0008cfffffffc003fe000000fc1f83b6783fff0008cffffff00001fe000000fc1f83b6383fff0008cfffffffc003fe000000fc1f836ff83fff0008cffffff03ffdfe000000fc1f8367783fff0008cffffff00001fe000000fc1f8363783fff0008cffffffe3ffffe000000 else (if i < 77 then 0xfc1f83fff83fff0008cffffffffffffe000000fc1f83fff83fff0008cfffffffc001fe000000fc1f83fff82dff0008cffffffffffe00000000fc1f83fff82c7f0008cfffffffffffc6000000fc1f83fff821fb0008cffffffffffe3e000000fc1f83f7783fff0008cffffffe0001fe000000fc1f83f7783fff0008cffffff00001fe000000fc1f83f7383fff0008cfffffffc003fe000000 else 0xfc9f932ef93fff082acffffff00001fe000000fc7f8ffff8ffffa619ffffffffffffffffe00ffc7f8f2678ffffa619fffffff00001ffffe00ffc7f8f2678ffffa619fffffff00001fe000000fc5f8bfff8bfff8418effffffffffffe000000fc5f8b2678bfff8418effffff00001fe000000fc3f87fff87fff2209dffffffffffffe000000fc3f8726787fff2209dffffff00001fe000000))) else (if i < 81 then (if i < 79 then 0xfd3fa7f77a7fff328ddffffffe0001fe000000fd3fa7637a7fff328ddffffffe3ffffffff8fffd1fa3fffa3fff308ccffffffffffffe000000fd1fa3677a3fff308ccffffff00001fe000000fcff9ffff9e1fb0e3bfffffffffffe3e0007fffcff9f0ef9ffef0e3bfffffff1fffffe0007fffcbf97bef97fff2a2bdffffff1c001fe000000fc9f93fff93fff082acffffffffffffe000000 else (if i < 80 then 0xfe1fc3fffc3fffc148cffffffffffffe000000fe1fc3b67c3fffc148cffffff00001fe000000fdffbffffbedffbebffffffffffffe01ffe0fffdffbf6ffbffffbebffffffff03ffdffffe0fffdbfb7fffb7fff3aafdffffffffffffe0000f0fdbfb7fffb6dff3aafdffffffffffe000000f0fdbfb76ffb7fff3aafdffffff03ffdfe0000f0fd3fa7fffa6c7f328ddfffffffffffc7fff8ff else 0xfedfdbfffdbfffcd7aeffffff1c001fe000700fedfdbfffdbfffcd7ae001ffc1c00038000700fedfdbbefdbfffcd7aeffffff1c001fe000700fedfdbbefdbfffcd7ae001ffc1c00038000700fedfdbbebdbfffcd7aefffffffc003fe000700fe5fcbf77cbfffc558effffffe0001fe000000fe5fcbb63cbfffc558efffffffc003ffffff0ffe5fcbb63cbfffc558efffffffc003fe000700)) else (if i < 82 then 0xff33e7f37e7e7ff3cddffe003e3fffc7fff8ffff1fe3fffe3ffff1cccffffffffffffffff800ff1fe3f77e3ffff1cccffffffe0001fffff800feffdfbefdffffef7bfffffff1c001ffffe70ffeffdfbefdffffef7bfffffff1c001fe000700fedfdbfffdbfffcd7aeffffffffffffe000700fedfdbfffdbfffcd7aeffffffffffe38000700fedfdbfffdbfffcd7aefffffffc001fe000700 else (if i < 83 then 0xfffffffffffffffffffffe000e3ffdc1fff8fffffffffffffffffffff001ffc1fffc39ffe7ffffdffbffbfbfffddfeefffffffffffffffffffffbbf7fbff7f7f7befdfffffffffffffffffffff9ff3ffff3fff59eecffffffffffffe001ff0ff7feff77efffff7ddfffffffe0001fffff80fff7feff77efffff7ddfffe000e0001c1fff80fff77eff77efefff7ddffffffffffffffffffff else 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007f0)))))))
def bankWord (i : Nat) := fld (bankWordChunk (i / 8)) 152 (i % 8)

def decodeState : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x => bankWord (x &&& 1023) :: decodeState n (x >>> 10)

def level2Chunk (i : Nat) : Nat := 0xa1a2d1e0e2d6dcab3a46841e0e914487838b5b72f0e2c6e0ab3a162c1e0e91368bc38b52e2f0e848b4783a1e2c1e0e3f8b1b83
def level2 (i : Nat) := fld (level2Chunk (i / 12)) 34 (i % 12)

def level3Chunk (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x9b62d368bc499e2c6e07846dd5c2ac5d48b50424878490a2c6e07846e1572ac5d4a15845705d4a15221e05d4a29c34cc5d4a162d4487846dd5c2f05d4a0a2d454784 else 0x8b5b8368be4a155c4cc5d46e1222ac5d4a222d45478499d824dc5d48b18e368ab498a2d368bc49de2d368bf4a155c43c7848b58e4109545f9121e05d49b55c368be4) else (if i < 3 then 0x8b5bf368bc46e15c43cab48b1da708784a162d454784a115c2d87849dd5c368bf4a44da2cc7848b5b72747848b58e448bc4571122d87848b1cc6e0784a4a2d448784 else 0x825b81e05d4769c24cc5d48b5b8454ab4769c243c784a315c368be48b58e368be49422c6e07848b4da2f06e48b4da2d07846e15c454be48b2056e07848b5b8368bc4)) else (if i < 6 then (if i < 5 then 0x8b4da2f09248b58e450784a295c4dcb748b52e1e055498a2d4487848b18e4107849b62d4487848b1b81e04745712e2f05d48b58e368bc49522d368bc4a115c1e05d4 else 0x5f8da2f05d4929b85705d48b4da2ac9248b5b8448784a44da1e05548b5bf4487848b1da6e07849522c3687848b5b71e04748b4da2cc7848b1da6e13348fe2c638da4) else (if i < 7 then 0x8b1ff638784a2a2c6e07848b58e4487849522d448784a15571e05d4570da2f0b648b58e3c8ab4a4a2d368bc499d5c4dcb748b20c6e07848b5121e06e48fdb85710f4 else 0x90a2d6dcbf48458e368bf4769b84cca54a29c343c784a29824dc5d49862c3687846f8da2f05d4)))
def level3 (i : Nat) := fld (level3Chunk (i / 12)) 44 (i % 12)

def level4Chunk (i : Nat) : Nat := (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x6395c368ab29562c769b83687856fd5c4487817562c638da1e04758b1da6e1221e164f6e15c2ac5d58158e5c5331755da6f9b71e05d58b5da638da2f162d6e1041e05d5a315c368781656056e15c43c785 else 0x6e1221e05d11d654570ec1e05d57697e3689517562d638da2fcab5571041f4781755da69d333685d5570da2ac921756689095c368bf58b58e570da2f162d769b71e05d56e15c4487817562d638da2ac3f5) else (if i < 3 then 0x571121e06e17565f570da1e05d59517f36878175668570da2ac5d56395c410b61e158e6115c4105d59955c368b61e158e489041e05d5a155c368ab17559c571041e05d5815b85713317555c368ab2385d5 else (if i < 4 then 0x5f8da1e05d155666570da1e05d59422d638da2fd68a5f8da1e05d56395c410af175667608da1e05d5769b84947817558e5acda2ac5d599d5c4b878175599570da2ac5d58b58e4487817558e570da2b05d5 else 0xa4667368781755da6e17143c7856e15c4107817567b5f8da1e05d597e2d454da1e16675f8da2d87857697e3c87817558e571021e05d56e15c368af175662570da1e05d56815c368ab1755b8570ce2ac5d5))) else (if i < 7 then (if i < 6 then 0x769b7570781755da570da2d89556395c3c8ab17560a639042ac5d58b1da6393336962d815b84547856395c35cab1756628b5153687857698e571372dd6545f8da1e05d5995be3687817562d769b84d85d5 else 0x8b58e41078175671570da1e05d58058e5707817558e5710f4107858b4da274921e15b85710f1e04758b58e368af1756548b5041e05d5829b8368ab1756307698e4d85d5951683687817559d571041e05d5) else (if i < 8 then 0x99d5c4c07817562d7cd8e368bf5a4a2d3687815562c7698e3687859515c448781755da639714d85d5769b84cd221755da6e1714cc5d58b58e368bc1e16828b4da1e05d59a20e368781755b8571071e05d5 else (if i < 9 then 0x9418e571152fd5da6f8da2545d59ed5c368b61e158e47cda2ac5d58b58e368bc15558e5b1041e05d57695c3c8b61e16466395c1e05d5570da2d87815558e571121e05d5a295c368b61e15da708ce1e05d5 else 0x6395c4cd0417562d769b24547856395c374ab17562c769b85707856395c370ab17562d63912368785995b7570781755b8571331744758b58e41c7817562d769b843c78598a2d368bf1e158e5a5041e05d5)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0xa155c3a0781756056395c44c785769b85713617568b571071e05d59298e570da17558e5d0da2ac5d58b5fa639151e1654570da2d8785769b8378781755da6e1221e05d56b95c41078175654488da1e05d5 else 0x8b58e424da1e1592570da2ac5d56395c368af175654571041e05d59062d638da2fd608638da1e05d58b5da6dcbf1e165c5710f3687856e15c3687817158e570ee2ac5d56395f41078175628639121e05d5) else (if i < 13 then 0x63923410781756676ecda1e05d58b20c638da1e16858b5041e05d59515c4bc781756046e15c1e05d5a095c3687817562d769b84cc5d5769b85713343d6426dd5c2fc5d56395c4107817563f6395c43cda5 else (if i < 14 then 0x8298e368ab1756675f8da1e05d58b58e455041e1654828da2ac5d5769b75709517562d8158e4547858b5f2638da2fd58e571041e06058b5b84547811d6896dd5c1e05d599e2d368b61e1652570da1e05d5 else 0x769c36e10f1e1591570da2ac5d5831b8488781756646ecda1e05d56395c41c7817558e575041e05d5769b85710f1e16548b4da1e05d5a155c448781756545710f36878557138410781755da6e1824dc5d5))) else (if i < 18 then (if i < 16 then 0x8b58e410780fd65c570da1e05d56395c410a51e158e5712e2ac5d584d8e570781755da6fdb843c7858b5da639272fd67b9b55c368bf5a2d5c368781756888b4da1e05d59422d639151e1685571371e05d5 else (if i < 17 then 0x6395c498ab1755a2570da2ac5d58b58e3687815d5da6e15c4cc5d59515c4ccda17562d639042fc785571042487817563f6395c3685d58b5da639121e1667604da1e05d5570da2c8781756545a4da1e05d5 else 0x6395c3687817158e580da2ac5d57c98e570da2fd58e5b4da2ac5d599d5c368b61e15da6e15c44c7859515f3687817562d638da2d47858458e368781755da70db84cc5d5a155c4107817555c4108e1e05d5)) else (if i < 19 then 0x95d5c36878175654570da1e05d58b1da6e18e1e168a6e1221e05d56396b4107817562d7698e4d91556395c41095175599571041e05d59b55c368bc1755da6fdb84cc5d599e2d638da2f162d6395c448785 else (if i < 20 then 0x9a22d36878175668571071e05d595d5c36878181654570da1e0605a215c368781756858b4da1e05d590a0e638da2fd58e571051e05d5951233687817566c570da1e05d57698e4ccda2955a0571041e05d5 else 0xa295c368b71e16628b4da1e05550022d638da2f120e638da2ac5d598a0a368781756548a0da1e05d58695c4b8781755da639824dc5d599dbe3687817562d769b84547859b62d368781556548b515368785))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then 0x63957368ab1756676fd0f368785a29b85710f1e164f6e15c1e05d5909b75707817567e570da1e05d56e15c368be17558e570ec2ac5d56e15c4dcab17562c769bd3687859515d3687817560a6e1041e05d5 else 0x96e2d3687817559a570da2ac5d58b5b8454fd1e158e571072fc7857695c4dc941756548b4da2fc7856391f4107817568a571371c85d59515c368a51e162d769aa368bf56dd5c2747817558e571122f05d5) else (if i < 24 then 0xa155c368781755da570f51e05d56397441078175594570da2ac5d59555c36878175683570da1e05d599d5c380781756778b4da1e05d599db75707817562d368921e04756e15c410ab1756428b18e368785 else (if i < 25 then 0x99dbf4ccda1755f76e15c43c785a29b85713317558e5f8da2ac5d59516b36878175654570da2545d56855c410781755a7570da2ac5d58b58e44878155653570da1e05d59a15c36878175685571151e05d5 else 0x63968368ab17562d638da2544759aa0f36878175592571041e05d599e2c638da1e165d570da1e05d58b5cd6e1151e162d8018e4547859ee2d638da2fd6426e1221e05d56fd5c368bc1756428b5b8368bf5))) else (if i < 28 then (if i < 27 then 0x9515c3c8781756676e1221e05d59520a410781755ff6395c1e05d59515c35c78175674570da1e05d56395c4187817562d6e0da2ac5d56395c38c781755b0571041e05d56e15c368bc17562d639042ac5d5 else 0x22c769b81e125b570da1e05d58b5b83687815562d638da2f05d5769bd4ccda17555c368bc1b85d58b58e3c87811d5f76e15c4cc5d5769b843c781a960a639041e05d58b1da639261e162d6fcda1e0555) else (if i < 29 then 0x909b85710f1e155c368b01e05d56395c368b62ad58e488da2ac5d56715c368ab175677570da1e05d56395c368be175651570da1e05d56395c4107b175591571041e05d5769b8338a51e168a8b5b8454785 else (if i < 30 then 0x769b84cc6a17562d368781b85559515c410ab1756426e15c454bf5769b856c7817564b6e15c4cc5d59511f3687817562c7318e36878599d5c368b71e158e571041f05d58697e3687817566d570da1e0595 else 0x9a95c368af1756675f92e1e05d599db85710f1e15ff6395c2947856e15c454ab17568a70cce1e05d595174368781755b8570da2ac5d5570da2d8b31e1654570dd1e05d59515c3707817558e571042ac5d5)))) else (if i < 36 then (if i < 33 then (if i < 32 then 0x6a15c368ab1756426e15c4cc5d599d5c4dc721756428b58e368bf57698e4990f1e166a571041e05d59515c3b8781756426395c41cbf59655c3687817562c769b84dc785a015c3687817558e581041e05d5 else 0x8b58e368ab17558e5710f368ab56395c4108d17558e570da2f05d5a160a4107817558e571072ac5d56395c4108b1756056dd5c1e05d59522d368ab17562d7ed8e4547859515c368bc17559d570da2ac5d5) else (if i < 34 then 0x9520a3687817566a8b4da1e05d5a164f570781755da709221e05d599db85713317561a570da2d87859a15c368bf1e166d571121e05d599e2d639121e162d6e0da1e05957695c4b89517558e571041dc5d5 else (if i < 35 then 0x8b58e3687815568a5712e1e05d59795c3687817558e570da2085d563980368ab175628638da2f05d56e15c390781756548b4da1e055599d5c4d4781755da639334985d59595c3687817562c8158e368785 else 0x6b95c368ab175659570da2947858b1da6e07817558e570da2a45d59ed5c4b8781756675712e2d878590a2d6e1151e1654570da1ec5d55712e1e05d15568a608da1e05d563969368ab17568a8b58e454785))) else (if i < 39 then (if i < 37 then 0x6395c450781756545712e1e05d56395741078175654570da1f05d590a2d368bf24965f571041e05d59815c368781754008b58e4487846395f368ab1756056e1221e05d59422c638da1e1685571042ac5d5 else (if i < 38 then 0xa155c33878175654571261e05d5941b84887817559a571041e05d56395c368ab17555c368bc2485d599e2d6e1151e1654570da2ac5d59bd5c368781755b85710f3dc7858398e41c7817569199cda2d8785 else 0x69d5c4107817558e570da2ac6058058e570b61e158e48cda2ac5d5951603687817560f639041e05d56515c41078175667570da2e87858158e5c50f1e15b8571151e059583d8e368af1755da6dd5c2d8785)) else (if i < 40 then 0x6dd5c1e05d11d58e570da2b85d5570da2cc781755da6e15c4dcb756397d570ab17558e5f9041e05d56395c368ad17558e5bd5c2ac5d59a95c3687817562d63915368ab56e15c4007817565f8b4da1e05d5 else (if i < 41 then 0x8b5da6e1372fd62d638da1e05956395d368ab17558e5a1041e05d59515c36877175609638da1e05d59515c3688d1756668b4da1e05d5769a743cda1e155c4e0da2ac5d59515c3688b1756678b52e1e05d5 else 0x2628b4da1e05d5a5a2d769b81e1685828da1e05d5))))))
def level4 (i : Nat) := fld (level4Chunk (i / 12)) 54 (i % 12)

def level5Chunk (i : Nat) : Nat := (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x8a1da638da1e05d6829b836878174476a29b8571151e05d68b5da638da2545d66e15c368781745569098e570da2005d68b5da664da1e05d67695c368951b85d67598e570da1e05d6a29b8570da1e05d68298e368ab1e05d66395c3c878174476 else (if i < 2 then 0x7698e570d91e05d67698e574da1e05d66395c368ab1740369b667570da1e05d69edb8570da1e05d67998e570da1e05d67c1a7570da1e05d68298e410da1e05d6769b8570f21e05d66395c368ab1740967695c4e0da1e05d682a05638da1e05d6 else 0x909a7570da1e05d676988570da1e05d66395c4dcda2ac5d69ad8e570da1e05d6769b7570921e05d68b5da680da1e05d6951bf570da1e05d68b5da6e0ce1e05d67698e3bcda1e05d66395c37cda2ac5d69698e570da1e05d6769b85710f338786)) else (if i < 4 then 0x7f18e570da1e05d6951b8570da1e05d66398e571041e05d69958e570da1e05d67f98e570da1e05d6769b8571152fc7866395c368aa1e05d68b5da6e15c4547869098e5f8da1e05d69518e571041e05d66395c368781744e68698e570f21e05d6 else (if i < 5 then 0x6395c368781804e69098e5a0da1e05d6a295c368781b85d66395c368781744b66395c3f4da1e05d693d8e570da1e05d60018e368ab1743559398e570da1e05d68bdda638da1e05d699d9a570da1e05d67698e570da2285d67699c570dd1e05d6 else 0x99d5c368b61e06e663985571041e05d699d5c4a4da1e05d67695c3c8781b85d67298e570da1e05d681d8e570da1e05d67698e570da2dc7868b58e368781745569515c368781743166395c3689b1e05d6570da1e06e174556a2a2d638da1e05d6))) else (if i < 9 then (if i < 7 then 0x8318e570da1e05d69ee2d638da1e05d68158e5712e1e05d66391f368781744768158e570da1f05d67698e570da2947868b5da638f21e05d69ed5c368781b85d6769bd488da1e05d6a328a570da1e05d690a2d6e0da1e05d67695c3d0da1e05d6 else (if i < 8 then 0x99d8e5f8da1e05d6769b847cda1e05d6769b1570da1e05d67695c368921e05d66395c368ab2ac5d6001da6395c4dc6056395c410ab1744768bdda638da1e06067695c4b8781743f699da7570da1e05d67ddb8570da1e05d6a618e570da1e05d6 else 0x769b8571333385d6769b9570da1e05d60025f570da1e05d58158e570da2ac5d6769b8571331e05d66395c374781744766395c370781744767698e570da1e05f66e15c368ab1744768b58e454fd3687868f98e570da1e05d68b5da638da2fc786)) else (if i < 10 then 0x2675712e1e05d5769b86395c43c786a15da570da1e05d6769b8570dd1e05d69522d638da1e05d67695c3688e1e05d663974368781744769a15c3687817450699e2d6fcda1e05d69515c368781b85d66395c410da2ac5d68198e570da1e05d6 else (if i < 11 then 0x9515c36878174356769b85d0da1e05d68c58e5f8da1e05d600254571313687859a1da570da1e05d67698e5712b3685d69098e570da2fc5d68158e571261e05d699d8e5a0da1e05d67358e570da1e05d67698e5f92e1e05d69218e570da1e05d6 else 0x6395c410781745166395c410781740868698e5d0da1e05d67698e571371c85d6769aa570da1e05d600262570da1e05d56395c3b8781744767698e570da2585d66395c3ecda1e05d699e2d6e0da1e05d67ed8e570da1e05d66395c368af174516)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x9099c570da1e05d66395c368ab1745d69618e570da1e05d67698e5acda1e05d67698e570da2545d6001b8571041e05d58b5f7638da1e05d676999570da1e05d67dd8e5710f3687866395c4c5041e05d6769a7571261e05d69aa05570da1e05d6 else (if i < 14 then 0x9098e570da2d87869515c368ce1e05d676d8e570da1e05d6769b8570ea1e05d68158e570e11e05d68b5cd639153687869515c368781e05d69098e488da1e05d66e15c368781745966495c368781744766e15c368781745168b5da638da1e0626 else 0x6395c3e4da1e05d6769c36e0ce1e05d66395c504da2ac5d60015c410781743159158e570da1f05d67698e5b8da1e05d6769a0570da1e05d69515c368781743b67698e5dcda1e05d6769b8570ce1e05d699d8e571121e05d68b58e368ab174476)) else (if i < 16 then 0x1da6dd5c1e05d599e2d368781b85d67a98e570da1e05d67adb8570da1e05d6769ac5f8da1e05d69515c368b81e05d69955c368921e05d67d58e570da1e05d67698e5acda1e06066395c439041e05d67a18e570da1f05d68b5da638dd1e05d6 else (if i < 17 then 0x7698e5c0da1e05d69520a368781744766395c404da1e05d66395c368991e05d69515c368781745566395c410781a85d6769a0570da1e060698d8e570da1e05d6769bf6e0ce1e05d6769b86395c4cc5d69018e570da1e05d69515c368781743c6 else 0x8298e36878174476a298e571151e05d6769af570da1e05d66395c368781745560022d639041e05d599d5c368781742067698e570d71e05d699d9c570da1e05d6a158e571041e05d67c1b8570da1e05d6a298e570da1e05d69098e571041e05d6))) else (if i < 21 then (if i < 19 then 0x6395c368bf1e0506a15b8570da1e05d699d8e570da2d87867698e570f21e05d66e15c36878174286909b8570da1e05d67618e570da1e05d68b58e36878174516829da639041e05d67698e571351e05d67698e560da1e05d699d8e488da1e05d6 else (if i < 20 then 0x6b18e570da2ac5d66395c368ab1740b67698e5710a3687866e15c3689d1e05d68b5da368bf2487867ddae570da1e05d699dc3570da1e05d6829da6e0da1e05d67dd8e571333685d6909b8571151e05d67698e43cda1e06a69ed8e570da1e05d6 else 0x99dbf570da1e05d68c58e570da2d87867698e368ce294786815b8571371e05d66395c368b62707860022c7698e36878595254570da1e05d67698e5712e2d87866395c3687b1744766455c368781744767698e5d4da1e05d696dda570da1e05d6)) else (if i < 23 then (if i < 22 then 0x99d8e571041e05d69d58e570da1e05d66395c368981e05d68b5cd638da2fc7867698e5a8da1e05d69095c368bf2485d68c98e570da1e05d60018e571121e05d59518e570da1e05d6001da6396b4dc5d58b5eb638da1e05d67498e570da1e05d6 else 0x9098e571071e05d699db8570da1e05d67698e499221e05d66395c3687817445699dc5570da1e05d688d8e570da2ac5d68b5f0638da1e05d69e654570da1e05d6745b8570da1e05d68a18e368781745568298e571041e05d69099d570da1e05d6) else (if i < 24 then 0x6395c4b87817447699db8571151e05d68b58e36878174286a45da638da2d87869e58e570da1e05d690a2d638da1e05d67695c3688f1e05d66395c3687c1744766395c368781744868158e570ed1e05d695185570da1e05d69098e5710f368786 else 0x769b8570da1f05d692d8e571333685d67699f570da1e05d69515c368ab1744769ed79570da1e05d676989570da1e05d677d8e570da1e05d66395c368ab1743a67dd8e570da1e05d67695c368952485d68b61d638da1e05d673d8e570da1e05d6))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then 0x6395c368ab174476769b8608da1e05d69098e57115368bf67958e570da1e05d68b58e3689d1e05d68b5da6e18e4547867698e47cda1e05d6001da6e1221e05d5769b85712e1e05d67698e56cda1e05d67698b570da1e05d6941b8571371e05d6 else (if i < 27 then 0x769b8570da2ac5d67698e550da1e05d69258e570da1e05d6769ac570da2d87866395c368781744967698e4ccda1a85d66395c4f8da2ac5d663971570da2ac5d67698e571042ac5d66395c368781742e68c5b8570da1e05d69b667570da2fc786 else 0x6395c410e81e05d66395c4107817405676998570da1e05d66395c368a52647867698e570da2e87866395c368da2ac5d69098e570da2305d699d9d570da1e05d66395c498781744768159a570da1e05d67698e570dd1e05d67698e570dc1e05d6)) else (if i < 29 then 0x6395c4e4da2ac5d6639603687817447699e2d638da1e05d66395c368ab1740d699d8e5710f3687869118e570da1e05d6769b8571261e05d699d5c368781b85d68b5d1638da1e05d66395c454da2ac5d67698e570da2987867698e5d0da1e05d6 else (if i < 30 then 0x90a2d7698e368bf67695c3687e1e05d68b1da639373687869098e5a4da1e05d69e98e570da1e05d69515c368781740869b6426395c368bf67699d570da1f05d6769bd570da1e05d60018e570da2bc5d583e05638da1e05d600254571041e05d5 else 0x8b5da638da1f05d68f18e570da1e05d66395c368781745167698e570ee1e05d68de2d638da1e05d692d8e570da1e05d67698e578da1e05d6815a7570da1e05d60018e571041e05d59515c4c4da1e05d66395c368ab19c5d6a3267570da1e05d6))) else (if i < 34 then (if i < 32 then 0x7698e614da2947868158e5f8da1e05d6a59da6e15c1e05d6769b8571372fc5d6909a3570da1e05d6769a05acda1e05d69098e571333685d66395c368781745968b5da6392e1e05d68b5d9638da1e05d68b5da638da1e05668358e570da2ac5d6 else (if i < 33 then 0x7695c368931e05d66395c3688d1744769b58e570da2ac5d676992570da1e05d66395c3688b174476755b8570da1e05d60018e5707f1e05d58c62d638da1e05d67697e368781743f6909ae570da1e05d60018e570b82ac5d571d8e570da1e05d6 else 0x2675f8da1e05d590a2d6395c368bf68b5da639261e05d67ad8e570da1e05d69515c438da1e05d60022d8158e4547858158e5a0da1e05d67998e570dd1e05d68b5da638da2ac5d66395c368771744766395c368ab2185d67698e570da2f05d6)) else (if i < 35 then 0xa1654570da1e05d67698e570f22545d67c18e570da1e05d695242570da1e05d68ed8e570da1e05d678db8570da1e05d69515c368781a85d67698e568da1e05d699d8e5a4da1e05d68b6056e0da1e05d60020a638da2ac5d5769b84dd221e05d6 else (if i < 36 then 0x9520a768da1e05d66395c41078174246001da6e15c43c7857698f570da1e05d675d8e570da1e05d699dbf368ce1e05d699d8e571333685d6a29b8570ce1e05d67698e570da1e05b67698e588da1e05d6002548b4da1e05d56395c368ab1743f6 else 0x829da638da1e05d68b58e570da2ac5d68e1b8570da1e05d66395c368781745368758e570da1e05d67ad8e570da1e0606a158e570da1e05d699dae570da1e05d66395c368781742867698e5a4da1f05d60018e571071e05d59098e570da1e05d6)))) else (if i < 43 then (if i < 40 then (if i < 38 then 0x9098e570da1e06066395c410781740366e15c368971e05d66e15c4dc781744766395c410781740968b5da638da1e05566395c3689f1e05d66395c390da1e05d66395c3689d1e05d681d8e570dd1e05d69a18e570da1e05d66395c368bf2ac5d6 else (if i < 39 then 0x8b5e3638da1e05d66395c3689a1e05d699e54570da1e05d66395c3b078174476951d1570da1e05d690a2d639153687869218e47cda1e05d6769a9570da1e05d67698e570da1ec5d67698e5712a3685d676991570da1e05d66395c4dd041e05d6 else 0x99d5c368781c45d66395c3687811c196769b8570cf1e05d68158e488da1e05d6769c2570da1e05d699d8e570da1e05d68159c570da1e05d69098e570da2fc5067458e570da1e05d68b5da638da2907868b1da638da1e05d69520a570da1e05d6)) else (if i < 41 then 0x8498e570da1e05d68dd8e570da1e05d6769b8570ed1e05d69418e570da2fc5d69b5da6b15c368bf66e15c368781742667695c368781742168b58e570da1e05567695c368b61e03f66395c368781743068158e570da2d87860018e41078174355 else (if i < 42 then 0x6395c368ab1745068c58e570da1e05d68b5da6c8da1e05d66395c43cf736878672d8e570da1e05d67698e608da1e05d66395c3689c1e05d6001da6e15c4cc5d57698e5712e1e05d67658e570da1e05d67ddb8570ce1e05d67698e570da1f05d6 else 0x99e2d639153687869b61a570da1e05d68b5fa638da1e05d699d5c4b8da1e05d66395c368c52ac5d66395c368a71e05d67698e480da1e05d600285571041e05d58b58e368971e05d6951da570da2ac5d699d8e570da1e060697d5c454da1e05d6))) else (if i < 46 then (if i < 44 then 0x6e15c410781744767698e5d0da2545d68b5da6e1371e05d67698e5f8da2d878600267570da2d87856395c3f0da1e05d66395c51cda2ac5d67698e570da2ac5d66e15c3d8da1e05d68158e570da2bc5d66695c368781744766395c410ab1e05d6 else (if i < 45 then 0x99dbf614da1e05d67c18e570da2947867699c5a0da1e05d66395c411041e05d699e28638da1e05d69418e488da1e05d69515c368781740566e15c368ab1e05d68158e571041e05d66395c368a01e05d66395c368c72ac5d69918e570da1e05d6 else 0x815b8571151e05d696d8e570da1e05d66e15c410da1e05d69098e570da29478699d79570da1e05d68798e570da1e05d6815b8570da1e05d691d8e570da1e05d6a45da638da1e05d69e98e570da2545d66515c368781744767698e571261e05d6)) else (if i < 48 then (if i < 47 then 0x9c18e570da1e05d66397e3687817447690a2d638da2fc7869a9da570da1e05d69095c368921e05d600254570da1e05d57698e570da1e85d67698e580da1e05d669d5c368781744766395c4107f1e05d68d98e570da1e05d67698c570da1e05d6 else 0x99d78570da1e05d68b58e3d8da1e05d60018e5710e4105d58b58e368bf2747869095c3688e1e05d6769b85f8da1e05d6769b8338781a85d66395c410781745d6570da274921e05d67558e570da1e05d66395c570da2ac5d66395c400da1e05d6) else (if i < 49 then 0x769b7570da1e05d6941b8570da1e05d68d18e570da1e05d66395c368bc1e05d68159d570da1e05d69a242570da1e05d68b58e41078174476a295c368781c85d67698e570da22c5d67698e490da1e05d67ad8e5acda1e05d66396836878174476 else 0x8b5da63937368bf67698e570da1dc5d68098e570da1e05d68558e570da1e05d68b5da668da1e05d67695c368941e05d67698e5d0f21e05d67698e570da2345d6829cd638da1e05d698a2d768da1e05d68b58e368ab1e05d67258e570da1e05d6)))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then 0x78d8e570da1e05d67ada0570da1e05d68b605638da1e05d68158e570d31e05d66fd8e570da2ac5d68158e5710f36878699d8e570da2947868b5b8368781744766395c505041e05d60022d769b8454785769b85a0da1e05d6a5a2d7698e368786 else (if i < 52 then 0x93d8e570da2ac5d67698e5711d1e05d699d5c4a0da1e05d699e2d638da2fc7867d98e570da1e05d69098e5acda1e05d699d5c368921e05d69098e570da2545d690999570da1e05d68b605639151e05d68b58e410da1e05d687db8570da1e05d6 else 0x8398e368781745066395c368bc174556909a0570da1e05d68e18e570da1e05d6769b4570da1e05d6909b8570ce1e05d67698e571301e05d68b5da69cda1e05d68b5da638da1e05866e18e570da2ac5d68b1da639223687869515c36878174246)) else (if i < 54 then 0x6395c3dcda1e05d682d8e570da1e05d6769b2570da1e05d66395c368ab174316839da638da1e05d67718e570da1e05d69515c36878174096769b85710f1e05d6769bc570da1e05d67a1b8570da1e05d698a2d570da1e05d699d5c3688e1e05d6 else (if i < 55 then 0x6395c410781740b67698e570db1e05d67698e571262947867695c368901e05d69515c4dcda1e05d6a3654570da1e05d67e98e570da1e05d69422d638da1e05d69515c368781740367698e570d51e05d66395c448da1e05d66395c368971e05d6 else 0x6715c368781744767695c368911e05d60026d7695c36895599d8e5acda1e05d699d8e570da2545d66395c368781744d699d99570da1e05d68158e5a4da1e05d67698e5711b1e05d66395c420da1e05d6769b8571371e05d66b18e571041e05d6))) else (if i < 59 then (if i < 57 then 0x769b8554da1e05d66395c368b61e04766395c368ab1b85d68158e571333685d69098e570f21e05d69915c3688e1e05d67698e570ec1e05d663922368781744769515c368c61e05d696d5c438da1e05d6769b3570da1e05d69098e560da1e05d6 else (if i < 58 then 0x769b7570bf1e05d697dda570da1e05d68b5da6390d3687867698e564da1e05d688d8e571041e05d66395c36878174266769b8488da1e05d67a19d570da1e05d60025436878174355815ae570da1e05d699da0570da1e05d699db8570ce1e05d6 else 0x7698e494da1e05d69515c410781744766395c410781743a699dda5712e1e05d6001da6b15c368b6599d5c368781d05d66395c424da1e05d68b5e8638da1e05d66395c368ab1743567698e498ce1e05d6769b8570da2d87860018e57131368ab5)) else (if i < 60 then 0x989da570da1e05d66395c368ab1e05d66395c40cda1e05d66395c4f9041e05d663971571041e05d66395c368781742766395c410781744769520a638da1e05d600285570da1e05d57698e615714dc5d66395c3d8da1e05d69515c368ab1e05d6 else (if i < 61 then 0x869bf570da1e05d68158e570da1e05d6769b8571041e05d66395c368ab1743b66e15c3687817447699d8e570f21e05d69515c410da1e05d66395c368ce2ac5d67699a570da1e05d6a4a678b4da1e05d600268570da1e05d595205570da1e05d6 else 0x98a2d734da1e05d676994570da1e05d68b5da670da1e05d66395c368ab2245d68158e571151e05d69515c368781bc5d66395c410da1e05d66e15c4547817447699d5c368b61e05d66395c3e0da1e05d67bd8e570da1e05d67698e57137454bf6)))) else (if i < 68 then (if i < 65 then (if i < 63 then 0x6395c3e8da1e05d68b5da638da2d87866395c4e5041e05d68b5da639363685d66395c368b82ac5d69098e47cda1e05d69098b570da1e05d683dda638da1e05d67698e570da1e05e6769bb638da1e05d66395c455041e05d67698e5c50f368786 else (if i < 64 then 0x6395c4107819c5d69c1a0570da1e05d68f58e570da1e05d68b5f3638da1e05d66395c368ab1743c67a18e5a4da1e05d6769a7570da1e05d66395c368a81e05d66395c368781744a6869b8570da1e05d67758e570da1e05d69515c4fcda1e05d6 else 0x2545710e3685d56395c368781742568b5da638da2fc6c68b605639153687869098e570dd1e05d68358e571041e05d69515c368781745d68718e570da1e05d67698e5f8da1e05d67698e570da1e05a68298e368ab1744768158e570da1e0606)) else (if i < 66 then 0x9b58e571041e05d67698e570da28c7869098e5d0da1e05d69515c368781741869418e570da1e05d68b5da6e0d11e05d69522d368781744767699e570da1e05d66755c36878174476769a4570da1e05d67e5b8570da1e05d6769b86155c4dc5d6 else (if i < 67 then 0x570da25c8e1e05d68b5da6b18e368bf6769ba570da1e05d68b5da639041e05d69515c504da1e05d68b58e3687817447679d8e570da1e05d67698e5a0da1e05d66395c43cda1e047697d5c3f4da1e05d69418e571151e05d68d58e570da1e05d6 else 0x7698e615261e05d699d8e47cda1e05d66395c41cda1e05d68b5da6e0da1e05d6769b8570d31e05d69518e570da2ac5d6769b85710f3687868b5da634da1e05d67b18e570da1e05d680d8e570da1e05d687d8e570da1e05d674d8e570da1e05d6))) else (if i < 71 then (if i < 69 then 0x9158e570da1e05d68b61a638da1e05d68c1da638d11e05d66398e570da2ac5d676993570da1e05d68695c368781b85d60020a639041e05d58b5da6e1151e05d690d8e570da1e05d66395c3f8da1e05d68b619638da1e05d67a58e570da1e05d6 else (if i < 70 then 0x99d8e5d0da1e05d67698e571121e05d60025b570da1e05d57a18e570da1e05d69e58e570da2ac5d67698e558da1e05d66395c410781743f699d8e570dd1e05d67698e4cd223685d67f58e570da1e05d67698e5c5333685d676996570da1e05d6 else 0x9515c368781740b67998e5a0da1e05d69062d638da1e05d68b5da674da1e05d67698e604da1e05d699d5c368781c85d67698e570d61e05d66395c410bf1e05d68b58e571041e05d663985570da2ac5d67698e570da284786791b8570da1e05d6)) else (if i < 73 then (if i < 72 then 0x6395c368b51e05d68b5da6390f368786a4a67570da1e05d699d5c4b8781b85d67698e5c4d11e05d68158e570d41e05d67698e570da1e45d69a98e570da1e05d663969368781744768158e570da2947866395c36878174576951ac570da1e05d6 else 0x7698e554da1e05d68b1da6395c3687867698e5711c1e05d6a155c410781744766b95c368781744767518e570da1e05d68b605638da2fc7866395c4ccda174476769b85a4da1e05d67b58e570da1e05d6815b1570da1e05d68155c368921e05d6) else (if i < 74 then 0x7698e571371e0606769b8571333685d67698e488da1e05d699d8e570da2f05d68e98e570da1e05d690a0a638da1e05d6989cd570da1e05d67699c570da1e05d68158e5c4ce1e05d6769a7570da294786841da638da1e05d68958e570da1e05d6 else 0xa155c410da1e05d68b5da639374547866395f368781744767698e570da2d87867698e571363685d6769b8570d01e05d695223570da1e05d698a2d638da1e05d68155c3688e1e05d69b5da570da2545d67858e570da1e05d67698e378da1e05d6))))) else (if i < 88 then (if i < 81 then (if i < 78 then (if i < 76 then 0x9515c368781743a66395c368781742a6769b8570e61e05d67e18e570da1e05d68b5e4638da1e05d60018e571042ac5d5769bb3688e1e05d686d8e570da1e05d6a29b8571371e05d67cd8e570da1e05d68b5f2638da1e05d69a59c570da1e05d6 else (if i < 77 then 0x769b8570d11e05d69515c368781744767699d5a4da1e05d6769b85d8da1e05d6769b8570d21e05d6001b8570da2ac5d59fdae570da1e05d66395c4c4da2ac5d6909a9570da1e05d67698e570f31e05d66395c368ab1740867898e570da1e05d6 else 0xa4d8e570da1e05d6769b8571221e05d66395c368781744466395c410c51e05d68158e5acda1e05d68158e570da2545d6769a7368ce1e05d67698e570da2bc5d69515c4f8da1e05d695171570da1e05d681599570da1e05d6951da571041e05d6)) else (if i < 79 then 0x9515c368da1e05d67698d570da1e05d66395c410c71e05d699e0a638da1e05d68b5da6390c3687860015c368ab1743156395c51d041e05d67698e571041e05d66e15c3687817450699d95570da1e05d66395c368781744766395c368811e05d6 else (if i < 80 then 0x7698e584da1e05d68b5da639333685d69515c454da1e05d69a95c368781745167698e5713343cda6002428b58e368bf56395c368831e05d6769b8570da1e05d67999c570da1e05d6a2a6d570da1e05d6815a0570da1e05d6815b8570ce1e05d6 else 0x9515c4e4da1e05d6769b8571151e05d68b5da6b8da1e05d68118e570da1e05d6769ae5710f3687869098e5712e1e05d68658e570da1e05d6769ab570da1e05d69b55c368781745566395c438da2ac5d69098e570da1f05d699e2d638da1e0556))) else (if i < 84 then (if i < 82 then 0x8b6057698e4547868b5cd6e0da1e05d68b600638da1e05d66395c368ab1a85d69515c3687819c5d67698e570eb1e05d66395c368781804768b5da639271e05d69ee6d570da1e05d68698e570da1e05d69b5da570f21e05d66392336878174476 else (if i < 83 then 0x89dda638da1e05d682d8e47cda1e05d66395c368781744f67e58e570da1e05d60018e570da2f05d59520d570da1e05d69098e570da2ac5d6769bc47cda1e05d6769be638da1e05d68b58e454da1e04769fd8e570da1e05d66395c410781740c6 else 0x8158e560da1e05d657138368781744769098e571261e05d68b5da6e1153687866395c571041e05d6829da638da2ac5d600254570b81e05d56395c3689e1e05d699dda5f8da1e05d67c18e571261e05d60022d638da2ac5d5769b8570da1e0606)) else (if i < 86 then (if i < 85 then 0x9522d768da1e05d68b58e368781745068158e570f21e05d66395c410e71e05d697d8e570da1e05d69058e570da1e05d67699d570da1e05d696d5c3d8da1e05d69b654570da1e05d69218e558da1e05d66395c368ab2745d66395c41c78174506 else 0x8b6056395c4547868e58e570da1e05d66fd8e571041e05d68318e488da1e05d6799b8570da1e05d68b5da638da1e05d699d8e5712e1e05d67698e5710f36878699d8e570da1f05d67698e571071e05d6769b8570e51e05d66395d36878174476) else (if i < 87 then 0x769ae571333685d69515c368781743f68298e570da2ac5d699d7e570da1e05d699d8e570da2ac5d69898e570da1e05d67695c368b6248786769a5570da1e05d67698e5710b3687868b5d0638da1e05d68158e571152fc78600254828da1e05d5 else 0x7918e570da1e05d6769a7614da1e05d68b5da638da1e0606769bf6390f3687869418e560da1e05d66e18e571041e05d60022d638da1e05557c98e570da1e05d68c58e5712e1e05d66395c410fd1e05d693d8e571041e05d67c58e570da1e05d6)))) else (if i < 94 then (if i < 91 then (if i < 89 then 0x8b5d6638da1e05d68b58e3687811c3f66395c368a51e0476a2a2d6e0da1e05d60018e570df3685d56e15c3f4da1e05d69515c368bf1e05d67698e5ad371e05d6769c2571261e05d69522d570da1e05d699d8e571261e05d67798e570da1e05d6 else (if i < 90 then 0x769b8570da294786570da248781744769ad9d570da1e05d60025b5710e3685d5769a0571371e05d69098e570da1d85d6769b8570da2dc7869d5a7570da1e05d66395c410781743167218e570da1e05d68a5da638da1e05d66e15c454fd1e05d6 else 0x6395c36878174466769a6570da1e05d68b5da638d91e05d69b6678b4da1e05d6a61b8570da1e05d67698e5a4da1e05d68158e47cda1e05d68b5e6638da1e05d6769b8570d41e05d68b58e368bf1e047691d8e5712e1e05d6769b6570da1e05d6)) else (if i < 92 then 0x769ae570da1e05d66395c368ab174056a155c368781744766395c44878174556769a3570da1e05d67698e571333685d6570da238781744767698e570e01e05d68a9da638da1e05d68b5da6e0da2fc7866395c4e8da1e05d6769b76395c1e05d6 else (if i < 93 then 0x769ac5712e1e05d68cd8e570da1e05d6769b85711e1e05d690a0e638da1e05d66395c410781b85d67b98e570da1e05d6769b85c4ce1e05d60015c3687817418576987570da1e05d68158e570dd1e05d6769b5570da1e05d6a15da571041e05d6 else 0x6395c368b11e05d67698e57cda1e05d6909b8570da2fc5d6735b8570da1e05d68018e570da1e05d6769be368921e05d6921b8570da1e05d600254570da2ac5d58158e5d0da1e05d67698e5711336878699dda570da2d87867698e571271e05d6))) else (if i < 97 then (if i < 95 then 0x7698e570da288786769bf639333685d67d18e570da1e05d67698e5d8da1e05d60018e570da2ac5d56395c41078174356769bf570da2545d6909b8571371e05d69ed8e570da2fc5d60018e571314107858b58e3f4da1e05d6a0667570da1e05d6 else (if i < 96 then 0x7698a570da1e05d66395c368781745066395c368af1e05d68b5da638da2947869515c368c51e05d67698e58cda1e05d6769b8571371c85d6769b8570da2585d66396b368781744766395c368951744767695c368781744366655c36878174476 else 0x99d7e368781b85d67698e570d81e05d66815c368781744766e15c338781744768958e570f21e05d6769b85acda1e05d67698e484da1e05d69318e570da2ac5d6769b8570da2545d69515c51cda1e05d6951da570da1e05d67398e570da1e05d6)) else (if i < 99 then (if i < 98 then 0x769ba570dd1e05d66395c410781743b67698e5a0dd1e05d68698e570da2545d6a29c3570da1e05d66395c410ce1e05d67698e570da1e05d66395c388da1e05d66395c410781e05d683d8e368781745168b5da368921e05d69515c368c71e05d6 else 0x90a2d638da2fc5d68b5cd638da1e05d69222d638da1e05d66395c3fcda1e05d68b5da3688e1e05d69a58e570da1e05d68558e571261e05d68b5da63915344786769ad570da1e05d68518e571041e05d67418e570da1e05d60026a570da1e05d5) else (if i < 100 then 0x8b5fb638da1e05d66395c35c781744766395c410781743c67698e570da1e06066395c3687817452676990570da1e05d66fd5c368781745567698e48cda1e05d66395c410b81e05d67699b570da1e05d699db8571371e05d6a29bf570da1e05d6 else 0x8298e410781744768b5da6a8da1e05d6002628b4da1e05d59edbf570da1e05d68b5da639153687869099a570da1e05d6769b8639221e05d69515c570da1e05d66395c368ab174246769bf570f21e05d6)))))))
def level5 (i : Nat) := fld (level5Chunk (i / 12)) 64 (i % 12)

def level6Chunk (i : Nat) : Nat := (if i < 35 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x99d8e570da1e06e175dda6395c368781b45d78158e570da1e05d0fde227698e570da1e05d79098e570da33878175dda6395c368781742470026d99d5c36878175a426395c368781e05d7001e66395c368781758007695c438da1743160028a6e15c368781759da6e15c504da1e05d7 else 0x8b5da638da1e05d175dda63971571371e05d77698e570da30c78175dda6395c368971e05d77698e5710f36878175c009098e570da19c5d6936426395c36878175dda6395c368781c85d77698e5714036878175e426395c368781743b7891da6395c36878175dda6e15c53cda1e05d7) else (if i < 3 then 0x6b18e570da1e05d11dd8e570da1e05d11c0b799d8e570da1e05d0d5dda6395c368c11e05d79098e570da1e05d069dda6395c36878174097002676395c4c4da1e1a168158e570da1e05d70022d7698e438da175a056395c368bf1e05d78b6056395c36878175dda6fdac570da1e05d7 else 0x18e570da1e05d08da267698e570da1e05d77698e5714236878175e316395c368781b85d70018e570fd368781759da6395c4dcda1e05d7001c56395c368781759da6395c368781740377698e5715136878175e927698e570da1e05d77698e5712e1e06e175e426395c368b81e05d7)) else (if i < 6 then (if i < 5 then 0x88d8e570da1e05d11de676395c368ce1e05d77698e5713436878175c007698e570da29478699d8e570da1e078175e7b9098e570da1e05d77698e570da2ec78175dda6395c368c41e05d77698e5713745478175dda6e1ac570da1e05d78b5da6394136878175dda6e15c368781740b7 else 0x7698e570dd1e05d021e2d7698e368781b05d76395c36878174470e9dda6395c3687c1e05d788dda6e15c36878175c008b5da638da2fc786001da570da248781759da6393147cda1e05d77698e570da1e063175c007698e368781743567698e614da1e06a175e676395c368781743b7) else (if i < 7 then 0x6395c4f8da1e05d11dd8e5c55c36878174477001cd6395c36878175a426398e570da1e05d77698e571041e05d11dc009218e570da1e05d6a2a676395c36878175d8e570da1e05d11c477001da570da238781759da6395c3d8da1e05d77698e5710c36878175e676395c368b81e05d7 else 0x769b85c55c36878175dda6395c528da1e05d7769b8570da1e05d11de2d769ac638da1e05d78b5da638da1e05d02de056395c368c51e05d77698e570da1e05d04ddda6b15c368781b85d77698e570da2ac78175e676395c36878174557769956395c36878175c009098e570da2fc5d6))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x9098e6155c36878175e676395c36878174177815da6395c45478175dda6395c548da1e05d78158e570da31c78175dda6395c468da1e05d77698e5710436878175d8e570da368781744779ee676395c36878175e056395c51cda1e05d7815da6395c36878175dda6e15c4f8da1e05d7 else 0x769b85711536878175e308b5da638da1e05d77698e570da1e05d0b1dda6e15c368da1e05d76395c4e4da1e05d11dc007698e5acda1e05d67698e5f15c36878175c007698e570da2545d67698e570da1e05d151dda6395c368bd1e05d7001da6655c3687817598e5711536878174477) else (if i < 11 then 0x7698e6155c4dcda175dda6395c368781741c7769b8570da1e067175c006395c2e07817447699d8e6395c36878175e0d6395c36878174477001da6815c36878175800769b8570ce1e05d6001da638da1e05d06d98e570da1e0671744778b6237698e36878175c007695c368781742d6 else 0x99d8e570da32078175e2d7698e368781744770018e570da1e05d069800769b8570b81e05d68b5da638da34478175e6d6395c36878174477001da6395c438da175a0d769b8570da1e05d79098e5e55c36878175e507698e570da1e05d78158e5715c36878175dda6395c368781745d7)) else (if i < 14 then (if i < 13 then 0x1da570b81e05d0c59da6395c368781a05d70018e570da1e05d155a426395c368781740877698e5713b36878175c00a298e570da1e05d67698e5714136878175c006395c4c4da1e02469b5da6e15c36878175e6763985570da1e05d78b5da6393e36878175e2d7698e5c4da1e05d7 else 0x1da6395c3c8781759da6397e570da1e05d7769bf570da1e05d0fddda6395c368781ac5d7002426e15c36878175a056fd8e570da1e05d79098e5713136878175dda6395c368781d85d77698e570da1e060175e2d7698e368da1e05d70020a638da1e05d11d9da6395c368d31e05d7) else (if i < 15 then 0x7698e5714f36878175dda6e15c52cda1e05d77698e570da1e05d019c006395c368781741767918e5713e36878175dda6395c368781740176395c36878174470fddda6395c368781743970027b6395c36878175a947698e570da1e05d7881da6395c36878175e2d7698e454da1e05d7 else (if i < 16 then 0x7698e570da1e06c175d8e570da2fc781744778b58e570da1e05d11ddda6e15c368781743f77698e5a15c36878175dda6395c368781740478158e570da1e05d08de2d7698e3687819c5d70015c36878174310a1a056e18e570da1e05d700242570da1e05d0c59e87698e570da1e05d7 else 0x9b62d7698e36878175e056395c520da1e05d77c18e570da1e06a175e056395c36878174317769b8570da2fc78175e2d769b8570da1e05d78698e570da1e05d0fdc008b5da638b81e05d6002546395c36878175a426395c438da1e05d7002676fd5c36878175a2d835da638da1e05d7))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0x7698e570da1e05d0cdd8e570da2e0971e05d7002428b58e368781759da6395c368cd1e05d790a426395c36878175c0099db8570da1e05d699d8e5713136878175e426395c368781a85d7769ac6395c36878175dda6395c368781740b77698e5715036878175e676395c36878174087 else 0x7698e570da29478175c006395c368ab17447688dda6395c36878175dda570da1e06e1743f7a05da6395c36878175dda6395c368781800b77698e570da34078175c007698e47cda1e05d68158e570da1e06e175c0099d5c368781743168c1da6395c36878175c007dd8e570da1e05d6) else (if i < 20 then 0x7698e5715336878175c007698e438da174356001da6395c374781759e07698e570da1e05d78158e570da1e05d0d5c008158e571313687869098e570da33078175dda6395c398da1e05d77698e570da1e05d0bde676395c438da1e05d78ba2d7698e36878175e2d7698e368781743f7 else 0x1da63974368781758006395c368781741967698e570da34478175dda63973570da1e05d76395c368c51e05d11de676395c368781a85d77698e570da34878175e547695c368781744778b5da638da2fc78175dda6395c524da1e05d78b62d7698e36878175dda6395c368781743a7)) else (if i < 23 then (if i < 22 then 0x9d9da6395c36878175d8e570da31c781744777698e5712236878175c0099e2d638da1e05d67698e5713e36878175dda63971570da1e05d76395c51cda1e05d11ddda6395c368781744777698e5713236878175dda6397e368781b85d700267570da1e06e175a679098e570da1e05d7 else 0x8158e570da1e05d0eddda6e15c368c71e05d77698e570da36878175c000018e571041e05d57698e570da20078175e056395c368ce1e05d7769b85714736878175dda769b8570da1e05d78158e570da1e078175dda6395c368781742277698e570da21c78175dda6e15c368c51e05d7) else (if i < 24 then 0xa2a056395c36878175dda6395c3687819c5d70018e570e136878175a056395c368b81e05d7001da6395c4dc5d02d9da6395c368781741d77698e5713936878175dda63966570da1e05d77698e5711536878175dda6e18e571371e05d7869da6395c36878175c006395c36878174516 else (if i < 25 then 0x8b5da638da31478175e676395c368781c05d7769b85715c36878175c007698e570b81e05d67698e5714536878175c007ad8e570da1e05d67698e5714e36878175e6799d8e570da1e05d7835da6395c36878175dda6395c368781740f77698e571261e06a175d8e5715c36878174477 else 0x6fd8e570da1e05d11ddda65d8e570da1e05d7001f06395c36878175a2d7698e51cda1e05d78b5da7698e36878175dda6395c394da1e05d77698e570da1e073175dda70db8570da1e05d70022d7698e368780ed9da6395c368781945d79b5da6395c36878175dda6395c36878174377)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0x7698e570da1e05d0f5db86395c368781744779f5da6395c36878175c006395c3689d1e05d67698e5714b36878175dda6698e570da1e05d7001b8570da1e05d091800829da638da1e05d6769bf6e15c36878175c006395c36878174286002426395c36878175a2d7698e368c71e05d7 else 0x7698e5714336878175dda6395c368b61e06e77698e5712936878175e8e7698e570da1e05d7769b86e15c36878175c00570da1e05d0c42467698e570da1e05d0d1e2e7698e570da1e05d79e1da6395c36878175dda6395c368781743f7791da6395c36878175e056398e570da1e05d7) else (if i < 29 then 0x7698e570da1e05d0a5c007458e570da1e05d68158e6155c36878175dda69d8e570da1e05d77698e570da1e05d045d8e571153f4da1e05d7859da6395c36878175dda6395c368bf1e05d77698e5acda1e05d02ddda6395c4b0da1e05d78b5da6395c36878175d8e570da1e05d11c317 else 0x885da6395c36878175c007698e570da1f05d66395c368781b85d11dc008b58e368781742468b5da6fd8e36878175e426395c368781742477698e570da32478175dda6395c368d41e05d77698e5711036878175dda6815c368781740b7002676395c368781759da6e15c36878174317)) else (if i < 32 then (if i < 31 then 0x6395c36878174470d5e2d769b8638da1e05d77698e5711936878175dda6395c530da1e05d70018e571313687811d9da6e15c368781b85d79098e570da1e05d025dda6395c368cb1e05d7002316395c368781759da6395c478da1e05d77698e5c4da33878175c007698e5712e1e05d6 else 0x9edac6395c36878175e056395c368781745178158e570da1e05d021dda6e15c36878174357001da638b81e05d0d5a8c769b8570da1e05d7001da6e15c4c4da1e19da63969570da1e05d79098e5713736878175c00769ac570da1b85d6001da6395c368ab1759da6395c368781885d7) else (if i < 33 then 0x769da6395c36878175d8e570da33878174477001da57131368780c5a676395c368781742476395c368781e05d11ddda6395c368c51e05d77698e5714636878175c00815b8570da1e05d68158e5713136878175dda6395c368781745078b5da638da1e05d0c5c007698e571261e05d6 else (if i < 34 then 0x769b8570da1e05d0ede676395c36878174097769b8570da33878175c008155c36878174316769b8570da1e078175dda6395c368c71e05d76395c36878174470edc0000254570da1e05d500242638da1e05d0d598e5710e3d8da1e05d7001da570b8238781759da6395c51cda1e05d7 else 0x7698e570da1e05d081dda6718e570da1e05d70022d7698e4c4da1e19da6e15c368b81e05d77698e570da1f05d025dda6395c510da1e05d76395c36878174470f1e676395c4dcda1e05d76395c368b81e05d11de056395c438da1e05d78b5da638da1e06e175e2d769cd638da1e05d7)))))) else (if i < 52 then (if i < 43 then (if i < 39 then (if i < 37 then (if i < 36 then 0x7698e5e95c36878175e6e7698e570da1e05d70022d8158e368781759da6395c570da1e05d77698e570da21078175dda570da2fc921e05d790a056395c36878175e8a769b8570da1e05d78b5da638da1e05d0d5e056395c368781a85d77698e5a0da1e05d021e056395c368781a45d7 else 0x7698e6157136878175dda69d5c368781a85d79b6677695c36878175dda6395c3c8da1e05d77698e570da1e05d131de67698e570da1e05d77698e570f136878175dda63986570da1e05d77698e570da1e05d0f9dda70d8e570da1e05d700267638da1e05d0d580078d8e570da1e05d6) else (if i < 38 then 0x7698e570da2545d0fddda6395c368781740770018e570da1e05d091a2d7698e368781743b7769bf6395c36878175e546395c368781744778b5da638da33878175dda6395c43cda338787001da6395c438b8175a2d7698e368781e05d78b5cd6395c36878175dda7058e570da1e05d7 else 0x99e056395c36878175dda6395c3f4da1e05d7769c56395c36878175e2d7698e368b81e05d70018e570da25c781758009098e5710e3685d6942426395c36878175e426395c368781745d76398e570da1e05d11ddda6395c454da2fc7878b5da6395c454da1e1e978b5da638da1e05d7)) else (if i < 41 then (if i < 40 then 0x9098e5714136878175e2d7698e368781741b763985570da1e05d11ddda6395c3688c1e05d7769b86395c45478175c00769b8571371e05d67698e5955c36878175dda6395c368781742377698e570da1e05d07ddda63964570da1e05d7769b86395c36878175dda6395c368b91e05d7 else 0x7ad8e570da1e05d02ddda6758e570da1e05d77698e5713336878175e676395c368781745d77698e5713d36878175dda6395c4b4da1e05d79b5da6395c368bf1e1dda6715c36878174087769b86155c36878175dda6395c520da1e05d7769c06395c36878175dda6395c36878174317) else (if i < 42 then 0x7698e570dd36878175dda6395c368781b85d7909da6395c368bf175dda7358e570da1e05d7921da6395c36878175dda6395c444da1e05d7769ae570da33878175c007695c394da1e05d67698e570da1e05d0e1dda6395c3c8781743f77698e57133368ce175c0099d8e5710e3685d6 else 0x18e570da2ac78175a426b18e570da1e05d79098e570da1e05d02de7c7698e570da1e05d7a31da6395c36878175c007698e571313687860018e571041e05d11da676395c504da1e05d77698e570da1e05d159dda6395c368ca1e05d70018e570f636878175a2d7698e638da1e05d7))) else (if i < 47 then (if i < 45 then (if i < 44 then 0x2056395c454781759da6655c368c71e05d70018e57104368781759da6e15c368781740878b5da6398536878175c008158e570da1e05d6001b8570da1e05d11da2d7698e570da2fc7876395c4c4da1e05d11dc007699a570da1e05d67698e570da1e05d0d5d8e570da1e05d11c087 else 0x1da69d5c36878175800638da1e05d0d42467698e570da33878175e4288d8e570da1e05d77698e570da1e078175e737698e570da1e05d70015c36878174470c59da6395c368781741277698e570ea36878175dda6e15c4c4da1e05d7861da6395c36878175e997698e570da1e05d7) else (if i < 46 then 0x7698e570da2e078175dda6e15c438da1e05d799dac6395c36878175e676395c368781740b77698e570da1e05d069dda6395c368781d45d7001da6397e36878175a977698e570da1e05d7935da6395c36878175dda719b8570da1e05d76395c438da1e05d11ddda6395c368781743b7 else 0x769ae6395c36878175c008b58e36878174476001da63968368781759da6395c368781743c79098e5713e36878175e4263971570da1e05d7a29da6395c36878175dda6fd8e368ce1e05d79098e570da1e05d11ddda6396b570da1e05d7002506395c3687817598e570da1e06a174477)) else (if i < 49 then (if i < 48 then 0x9098e570da36878175dda6395c534da1e05d70022d769b836878175a2d7698e4c4da1e05d77698e570da1e05d055e056395c36878174247909da6e15c36878175e2d7698e368781740877698e570da1e05d06de0a7698e36878174477769b8570da1e06a175dda6395c36878174557 else 0x1e86395c36878175a426395c3687819c5d70022d768da1e05d0c59da6395c368a41e05d78158e570da1e05d025dda6395c368851e05d79c9da6395c36878175dda6395c368781741779098e5711536878175e6788d8e570da1e05d77698e5d0da1e05d0fde7b7698e570da1e05d7) else (if i < 50 then 0x99d8e5c55c36878175dda6395c368881e05d7769c46395c36878175e676395c368781744779098e5714e36878175e2d7698e438da1e05d790a0d6395c36878175e268158e570da1e05d7951da6395c36878175dda6395c368781985d78158e5713736878175e67769bf570da1e05d7 else (if i < 51 then 0x8b5da638da1e06a175e6d9098e570da1e05d799dda6e15c36878175dda6395c368781c45d70018e5710e3685d0918007698e4c4da1e03567698e5711736878175dda6398e570da1e05d7769b8570da1e05d0b5c009098e570b81e05d68298e570da1e05d11de676395c4f8da1e05d7 else 0x1da6715c368781758009218e571313687867698e6155c36878175df77698e570da1e05d799d8e5711536878175dda6395c3c0da1e05d77698e570da1e05d0d9dda6395c368c81e05d77698e570e936878175c008158e3687817435690a2d7698e36878175e676395c368da1e05d7))))) else (if i < 61 then (if i < 56 then (if i < 54 then (if i < 53 then 0x7698e59d5c36878175e8a6e18e570da1e05d78adda6395c36878175c007698e570da2d87869f6426395c36878175e676395c3687819c5d77698e570da1e05d029dda6395c368c21e05d7001da63922368781759da6395c368ab1744777698e5712e36878175e506395c4dcda1e05d7 else 0x9b6676395c36878175dda63979570da1e05d77698e570da1e05d065e428b58e570da1e05d7816056395c36878175dda6395c458da1e05d79b5d16395c36878175d8e570da1e05d11c057769bf6398536878175c0099d8e570b81e05d69098e570da1e05d0fde678358e570da1e05d7) else (if i < 55 then 0x6395c368bf27478175c006395c368781744767698e5711f36878175e2d7698e5c8da1e05d77a18e570da1e05d025dda6395c498da1e05d785dda6395c36878175c009515c3687817447699e2d7698e36878175dda6e15c3687817442799dda570da1e06e175e426395c368bf1e05d7 else 0x18e570da200781758007698e57131438da6001da6e15c368781759da6395c368951e05d77698e5713136878175c006395c438f63685d67698e570da1e05d145dda6395c368781740877698e570da30078175dda570da2e08e1e05d77698e570da1e05d059c007698e571041e05d6)) else (if i < 58 then (if i < 57 then 0x7698e570e136878175c008158e5710e3685d6942056395c36878175c009b5da570da1e03f60021a6395c36878175a056395c368781745d77698e5e15c36878175e676395c368781743f7001da6e15c454781759da6395c368781905d7a59da6395c36878175dda6395c4dcda2fc5d7 else 0x7698e5713c36878175e676395c368bf1e05d799e2d6395c36878175c007695c368781743167698e60d5c36878175dda7198e570da1e05d77698e570da1e05d105c006395c4e4da1e05d67698e570da1e05d041e676395c50cda1e05d7a3a676395c36878175dda63974570da1e05d7) else (if i < 59 then 0x7c1da6395c36878175c007699d570da1e05d69098e570da1e05d141dda63937488da1e05d77698e5712836878175dda6395c368921e05d77698e570da1e05d161e056395c504da1e05d77698e5710e36878175deb7698e570da1e05d77698e570da1e05d051dda6695c504da1e05d7 else (if i < 60 then 0x1da6395c43cda1e1a6d769ac570da1e05d77698e570da1e05d0a1dda6395c3688e1e05d79098e5714736878175e427698e570da1e05d77998e570da1e05d021d8e570da1e05d11c247a3dda6395c36878175dda6395c368781a85d77698e570da1e069175e426395c368c51e05d7 else 0x7698e570da33078175dda6658e570da1e05d7769b8570da1e05d025d8e57137368781744777698e570da1e05d101d8e570da1e05d11c037769b8570da1e072175d8e570da1e05d11c0977698e570da27478175dda6e15c368781742479098e570da31c78175c008b5da638da1e05d6)))) else (if i < 65 then (if i < 63 then (if i < 62 then 0x769a06395c36878175dda6e18e570ce1e05d7769d16395c36878175e676395c368c51e05d79098e5715c36878175dda6395c434da1e05d77698e570da1e05d0b5dda6e15c4dcda1e05d7815ac6395c36878175e056395c368781740b7001e46395c36878175a056395c540da1e05d7 else 0x1da63969368781759da6395c368781c05d77698e570da33c78175dda63972570da1e05d7001da638da1e062175a676395c368c71e05d70018e36878174470d5a0a7698e570da1e05d70018e570b81e05d091a676395c51cda1e05d799dda6395c36878175c007698e4c51f368786) else (if i < 64 then 0x8c5da6395c36878175c007698e571333685d67dd8e570da33878175e426fd8e570da1e05d77699d570da1e05d025dda6395c3b4da1e05d77698e570da1e074175c00769b8368781743567698e570da1e061175e2d7698e3687817424788e056395c36878175c006395c2e0971e05d6 else 0x8b5da6393736878175e676395c570da1e05d78158e570da1e05d11ddda6397b570da1e05d7909b86395c36878175e928b5da638da1e05d79218e5713136878175c00768da1e05d0d43168b5da638da1e05d025d8e570da2ac78174477a55da6395c36878175c00769ae570da1e05d6)) else (if i < 67 then (if i < 66 then 0x8158e570da36878175e426395c36878174317815da6e15c36878175dda6395c368781740577698e570da294781a9dda6395c36878174427000006395c368ab1755da6395c368b61e05d76395c410da1e05d11de6e99d8e570da1e05d78158e5713e36878175e0563971570da1e05d7 else 0x8158e570da1e067175dda6395c368781740e77698e570da1e05d0adc007698e570da1e05d67698e5711836878175e676fd8e570da1e05d7002547695c36878175a056395c454da1e05d7001da6e15c314781758006395c368781745067698e570da1e05d009d8e570da1e05d0c4287) else (if i < 68 then 0x7698e571371e05d02ddda638da338781a85d799db86395c36878175dda6395c368781743277698e5a4da1e05d025e0d8158e570da1e05d77698e570da1e05d079c006395c438da174476769ac6395c368bf175dda6395c368781740076395c368781745d11dc007698e571312e0786 else (if i < 69 then 0x9b5da570da1e05d0fdde36395c368c51e05d7002426395c4c4da1e1a907698e570da1e05d7001da6395c3687818198e57141368781744779b6056395c36878175c00769b85710e3685d6769b8570da1e05d175c008b5cd638da1e05d6002056395c2e078175a426395c368781b85d7 else 0x1e37698e570da1e05d70022d7698e454da1e1a2d815da638da1e05d79098e570da1e05d0d5e676395c36878174317)))))))
def level6 (i : Nat) := fld (level6Chunk (i / 12)) 74 (i % 12)

def level7Chunk (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x7698e570da1e05d11de237698e570da1e05d7769ac6395c36878175dda6395c368781740b77698e5714136878175c007698e5710e3685d67698e570da1e05d175e057698e570da1e05d7001da638da1e05d0d59da6395c4dcda1e05d77698e570da1e05d025dda6395c36878174247 else 0x7698e570da2fc78175e2d7698e570da1e05d77698e570da1e05d0fdc009098e570da1e05d69b5da6395c36878175c007698e570b81e05d6835da6395c36878175dda6395c3687819c5d77698e5711536878175dda6395c368da1e05d77698e5713e36878175dda63971570da1e05d7) else (if i < 3 then 0x1da6395c4c4da1e19da6395c368781b85d77698e570da1e05d0c5dda6e18e570da1e05d70018e570da1e05d0919da6fd8e570da1e05d77698e5715c36878175dda6395c368c71e05d77698e5714736878175dda7698e570da1e05d77698e570da31478175c0099d8e570da1e05d6 else (if i < 4 then 0x1da6e15c368781759da6395c4c4da1e05d77698e570da1e05d021c006395c368781744767698e6155c36878175dda6398e570da1e05d77698e570da2e078175dda6395c368781743b77698e570da33878175dda6395c368781e05d7002056395c368781759da6395c36878174357 else 0x7698e570da1e05d699dda6395c36878175c008b5da638da1e05d6909da6395c36878175dda6395c368781a85d77698e5710e36878175c007695c36878174316)))
def level7 (i : Nat) := fld (level7Chunk (i / 12)) 74 (i % 12)

def level8Chunk (i : Nat) : Nat := 0x7698e570da1e05d6
def level8 (i : Nat) := fld (level8Chunk (i / 12)) 64 (i % 12)

def number : Nat → Nat
  | 2 => 12
  | 3 => 91
  | 4 => 495
  | 5 => 1210
  | 6 => 833
  | 7 => 55
  | 8 => 1
  | _ => 0

def hashes : Nat → Nat
  | 2 => 0xdb44a59dd5263d5dcab2069fc21dd508b6acb5f2adfa06b4834612355df60cd237bf08a7311d08332d65cfd52476eb57
  | 3 => 0xfe43062efd63cceefbd3fdf2fbb3ff85f63c0f1cf4a95f56ec67d875ea1584c6e9748271e85e1d98e601c632e4a1a7dbdb52de08da8f8f7ed8f2b405d40dfdcfcf8eb422c9984b61c9189720c114ea34c09aba76bfa0851cbd3ae4b8b92ce07eb840a9adb47f6b3cb36782fcad7ac336ac69f63fa7b226e7a419472fa126fdb19c2f35189a56c38a92f5dc538d566df687fd6bf887e3affb864e8c8d8572f7ee8436556281d9fdfc7ed0f77a7de8e5557c035cef7922e5c46aaae38a6a6a821667dde2076668b7126570832b5d6dc8355c1d729f5bd6688359131c825418e177529bb2824ee7682c4e6ef145480ed7da461c326f45fef4b04213477641bd1e5c3f7aa6433ee055133d1a7c403cbaa9273940376838cdbaf830c8a24a2ff349662d9c6291292ea5c0284faace27e7be03260a27fb253cb26f252ffc0b23bbe7c5232bbcbb22da2ca91a018e88171b51740f559c5f0f3d0fe70e19c6790d0c78ef0a5f78680460a53e01117f6d
  | 4 => 0xffb70ca2ff7361e8ff6bde90ff5dbb13fed3e2abfec7d824fea01b3dfe2f7b79fd8b412dfd81d52bfd7b621ffc9b6c55fc9b3a43fc2f8dd1fb51adbafb2eb27dfb091ac0fa1de586fa13ba71f9c67f78f9c4c207f9c05f97f957a3fbf8d6e12cf8c5419cf88540bbf8763709f77aff5ef7325dd3f60b7facf5ec1a34f54515d9f508fca1f443c5e9f3d5c781f37480aaf3137343f2f488faf29d718cf26756a5f164d4c8f13c6b51f071c58df063cc14eedaecf8ee549bc6ee0774aeee054962ec2a8568ec1c5642eac69245e9e3245fe98ce6c5e959019ee92206bbe8bd4dede87c5040e86b9a0fe85e1d98e8298e7de6aa1cc2e60b12eae49eb875e49a8f88e48bd50ee466d2e2e408e3a9e33ba975e25c15bbe244307fe0b4c9f3e0a9cb9ae05d1c6fe0504aa2dfc09a61df6d290edf66fb16df1c04d4de40c1a0ddf72409ddccfffdddb66d21dd10d1a8dccbabeadc73a420dbaa0d89db78c45bdb0e2c5fdb0a598bda47ec98d9bb1c6bd925e1e9d7d35104d7b4e667d5979f42d5685bc9d3b0a9cbd36b25a3d2c56475d2974473d23e0e5ad217be27d1ea44a9d1a57026d161087fd0c576cdd0b68e73d03aed0dd0284153cf8ded43cf5ea40ace856098cd1576a2ccb39835cbcca59ecb1b2abbcb1072c2cadfff44ca9669aaca53371bca4ec2c1c9fa5b67c9dafed5c8fbff1bc81e21e7c7cd6884c7158c41c6d6d50bc633982cc5a2be9ec5409334c35bc5e6c32a5207c31edafbc29d5daac1917773c0a756d7c0410644c00c3636bf6d2ab7beda0d47beb11479be82b0ebbe2f0b22bdb7efb7bd955d30bc25fcafbbbcfd3dbadfca7db9a1ac74b87016d0b76fe3e4b6081bffb591d14eb574e1ecb54ab2efb515e877b4fb1d34b49d6181b47f6b3cb468f4a2b449f02eb41dbd08b3276a2ab3247272b2e41557b0e1d61bb038fe0eafa4155baf57af5daf4fb523ae0e9f35adff70faad47bdf5acdcee4eabe8dc81ab91accfa8caec0da7740b93a75ac075a729051fa6c70bc9a4d0d609a43f11d6a3fda468a31b0852a316ae55a2ce1893a24d8cb8a21b9fdfa20f404da1fa84ffa1ef05b3a1ccd0bea0a96cbe9fcc996b9f895cb69f6ea7a49f63b8a09f5e90959f282e469e3b73629d19f5f79cf3f2089cf3adcf9c2f8e1c9c22e08c9a8c9eb59a5c2ba59a38a79a99e2bc829901514898d8848398cbfcad983b945e980be2ab97f50af5977a24ca96bdad4c969c6d019610bc269588fd82950dd8a094901a6d93e7bd2e9346fd7592fc5df090678a778fd5f2938fc736bd8f710da38ef7f8378e7420068e162e3f8d2358ed8bfb77648ac012148a6e986e8a49cab78690c7c1860b75678492f8948480dc7b8477d0dd8465796c8436556282f7a2068262d4238211a7d881f36aea811c3ee8801315e77fa84a4c7ef2bb717e90620c7e63067b7d2cca877d12593a7cfd7e437ce64fba7cc017147c2d03317bd8d4677bb73aa47b9369fd7b7659cf779fa8917643c77b762eec847454b23d744836b573f4799173e4213873be1742735c6b47716fd70c7153331571409393713c4e0870c28d646f79f56e6f650af06f15bc646efe1b7a6df9d78c6df4aeed6d5aea766d4fb6836cc96fd66cc6304b6c09173a6b99b45d6b36703b6ac3e8386a79906f6961a82f687da62a67b57dcf66e0b0b766bc0a4f66a0104a664cec0b661b6b126503c8fc6501c47064fd737363c1c65a61924dc45ffab9b05f68e7f05f4c9f035f47487e5f19c8195cb4cf025bdcd3425b70f6715ab4df105a6268665a52aad1598880555928e1905921170a586264e3581367af58092eca56fc43af55f9060855430bf454c027a653264b0852e6b48e5258d2f3522280735198834f5193673f51776b9d514c5026513193d950e329d0504d23a04ffa07454f310fff4ef9a8aa4e8d2f0c4d815e104d2f2cdd4cad08ce4c53d2b54bf6f57a4ac4d58048baf2fd48b8e0f848b5a4ee48b061d948687e1a485856a5482601b7471861db46dc06b6459f54844514ded9428a97e941f4c8384129f17840740db3405f72d0404484e9403d16533fd79e333f9c9ca13f6ccce43f69e5ea3f531f803efb98f43e3b37403df7912b3d96a8bd3d5f319c3d5d9bac3d53ba903cdd40953cb183ae3c48b1c03bbbf8b43b548f693b3c64f23ab1540e3a7cd4b93a60062f391b8f9438e5f40e38cc29d23884f57838317cb137d0717b3689b1b936120ce43546e135352a7c3134c1735934524dba342987b63421c71933b5b57e335bdf2e3285db2b3252c3ed2fa797422f62a53c2ec3640e2e6547752cf84ddf2cec58512ccd9f512c9f17c62c8d8f352af0385b2ae3da382a9bf6792a1fd3142a19ef782a0a324629bfad76295f9131294b0bc228437eca277c9d8a275482c426ff4793261dbc1625e509d02536f356252ed91024b8b6ea2292eb2f2188b1ea20fa4a881fa19ca01edd9bc01ea434371dfe08061df388dd1dae76101d8d28f91d8394481d3e9f2a1d1b4b291c4bbde51b47e9c51b1a0b411b08ed611ae9f36f1a1456b919a605681993702a191e356018fb61e018458543181d80e8174c3aad1642beaf15da899a1408164b1402b5e013f469aa13a3bc7d12d1203c126526e411d0ed5011d08db611a80dd3112240d11014eb270f0d17ee0e1c9cc30e0cc8710df3e5bf0d5474680d3d77760d1485d20b9309900aeed4040aa2bf950a9c6a0c08fe8e3905f498f905f0e86a0569e66804fbe11c04ccfa1403b26bfe0294421901d514ff016082bf00781451
  | 5 => 0xffd1235effc1dc23ffb70ca2ff958245ff4aa624ff3206e1ff28667cff0d1cefff04ba5bfeab6f62fe796722fe7241eafe60ae3cfdb7c25bfdb30093fd088604fd03a46afc717ebcfc6f9f34fbf14af3fbc27dc3fbc0d3e6fbb40d44fb8ffe8efb79d674fb32c343fa60eab5fa3fcb78fa04a540fa04015cf9cdbcc7f9a2b839f99b33fbf8d6e12cf86c3fe1f850035ef7bfdbe1f763f967f73710a7f71eb068f6e9309cf6d16aa9f636175bf634bc3bf60d514af6027bc2f5cf9c6bf5cf8cc2f59324fef56fd0fdf53c4be3f4f59bcdf4e90301f4d07a62f4bf397ef49c231ff48cd936f46def80f45488f1f422f6e6f421a3b4f35546eef3231731f2d9a89df2b954d7f1fbd401f1e7f5fef1b193aff1a079f1f14fe7b4f1420d8df0f58eedf0be31d3f07ef7b9f063cc14f0002815efc4fe73efb2127cefae7446ef38d2fdeefd5c31eeeb840eeec5dac6eeaef305ee5d5c05ee394d4fee2cedbdee2cb3b8ee232535ee0774aeedb3fffded9c3364ed5c082ced215921ecb516e4ec7e5710ec29d41dec18ecc1ebd44a45ebc3747eeb79e32aeb6c2d5beb67d376eb3b9366eb2a7584eb241cfdeb1ff410eaeefbadeab9acb8eaa7e14fea6808f2ea1bec47e9fc93a7e9f4f22fe9eaa5f4e97ec866e94ec071e934d82de90a028de8544ff1e7a2d8a2e74e8cd8e6dea741e6d5af2ae6c255d8e6a714b2e699f334e6712297e667a571e640ee41e5fe95afe5a8fa3ce52cbaa3e517bbe4e514383ae4f79824e434c7c4e43256b9e3e38618e3dd35e4e3557a80e33cecc9e31b5e06e2f74569e2f0efe0e2ee8750e2614a3ae1a6aaf2e19bac75e169093ae163dcf0e140954ee0cb6a5fe0a35a03e06b881ce005aa9adfeb3abadf9d1588df9bff9bdf76e39cdf6d290edf50f480df49fc5ddf037568deff465bdec677b0de52afbbde21cf47de213c5fdd9e5811dd6e0a45dd58db44dd17b94bdcd79294dc85eb97dbceac5adb5bc805db0e2c5fdb00b0dedabcde75da7ca891da04c43ed9506373d91ca8fbd8f37c5cd8c372e2d8889c52d7e66d07d7a6c65ed71c5dfdd6c05195d6566f45d61fe094d61b1234d61805abd610c7d6d5e40892d595b15ad589c5e3d52a96e9d5295e57d5203351d509b10cd4efc01cd4baff18d4276d44d3a305ebd3a0f8a6d35a9340d336edc5d31e1458d2d74837d2974473d294897bd25944e3d24b2ad0d23dd616d238254cd1ea44a9d1e0a0ced15d9efed158841bd13c0b69d119c775d0c4afdad083b53cd0806d25d06cc5aed060661cd059e388d0544bdfd01794cbcf86e3accf54d180cf388893ce6ab7a5ce4e75b0ce40a00dcda80b4acd5c3993cd536c6fcd23b9e8ccfa3656cce31115ccdef8e1ccbe5603cca6aab8cc83d536cc78310bcc77673fcc56f758cc4f64a6cc445153cc3c325ccbf62e8dcbcca59ecbc86ad7cbc5f7bccb7fb423cb63da34cb1b00f4caf7acf3caae0f7cca9907c9ca9864beca74c1f6c9b1a5a1c9ad35b0c9320c1bc922c232c8ffbe06c8c60a05c8b851edc855f61cc84561e8c8314febc7d4b31ac7b9002dc76fd1f4c7396fa5c71b04fcc70e4e8bc6f5658ec6e6506dc6d7c3aac6c66accc67f52f4c65bfa87c5d08720c55bbed9c5551274c5409334c4fb734ec4bf313cc460813dc38f5604c3839190c375eecac3570c9cc30710aec2bd5601c2b070e3c29f007bc29d5daac2673e81c2661c34c20b437ec20abeebc1846cdfc14be348c1455343c09adab1c07e1456c02710fcc001cea8bfe7956ebfaa3bd6bf8c53a3bf846f9dbf6804c1bf1313f3bf0c41c2bf07f6e8bef8b367bef57b58bef482dabee849e7be6456afbe54d68dbdf5486cbdf41951bdd7f872bd7458f9bd5c9932bd4590eebcfff784bcfed11bbcf33e4ebcef1561bcb13397bbf8fe8dbbeb0d98bbb2764abb7c89cabb763679bb30d632bb0ed9bdbaf6eb41ba51e0beba2daa25b97bbf52b914295bb911a52fb8ac282db8a4d07bb878cbd6b877d77fb8721f87b85b10bcb84ee215b8444035b81780f1b7c905ccb6d4a588b6a701bfb6319571b5d67e4ab5a84c9fb56e8125b5484f3cb5095435b46ff996b468f4a2b3bee100b3a5fff7b2cd6970b2b7b843b290e79eb2283703b1f92ecdb1f51fc5b19dd39eb0e0fa63b09e3004b039cf9cb0391315b036bfa2afa4e56eafa4155baf8fb1f2af80a17aaf805d30af127140aed56605ae856900ae17aa10ae07a34dadf9701badf22361addcbbafada03a02accc8028acc8c109acae3f0fac90b592abc81900ab95e33eab73f26eab70da5eab563a91ab13e6bfaaebca4caac6e590aac4765eaa929433aa815e97aa68be49aa2da0aaaa1faedfa959acdaa8f8e8eea8e51cf6a8d27c72a8b2cb53a88f72e6a8522950a7b329e3a793e809a714ec6ca6e96af4a6ddb3c6a6bb59e8a6bb3954a6a1a36ba6807c57a67689caa616542aa5fd95d3a5e91d28a5dcbb93a57019f7a50ebfa2a4ea34dba497ac74a451eeb4a43e374aa3ffa4d5a3ab5f8ea39f5a7fa399686da38477b0a3477ec5a31d3052a2cabb1ba2ad65daa25a895ba23df446a2354707a20e95cda2073ec9a19d0c49a12d57c2a125e9b7a122fcc7a0da3a4fa09ca660a0884eeca068210aa028c0cb9fd722019fd66fba9f61d5e39f43f8789f2b5ae49ee583209e9484b19e8d9d5b9e62e0689e4d43ba9e402de39dff89529deef9f79d95190d9d7534cc9ce7a1129cbda7019c9620ae9c85591d9c2f8e1c9be3d67d9be180fa9bd50df49bbd2aa29b8b4e8a9b7c39699b26f4f79af1e3839ae373609a8c9eb599e5d75299b800a29978b68e9948614098958c1d97ecf598977c22129723bb2397004819966cd03f95f2595f959f1eae959ac3629503d81c94d7c99694cc512294a0ab61945956ab944a1033944024d293d60d8293d2427892b9b8f6928c0eae9276f1579270552c924d012b9222580e91f6324d917340de9172e98e9164c9859132676190cf2f3f90c49ca990a3f8959088fdc490703807904e99fd8fc469bd8fbead178f809d1b8ec5262c8e8ec3dd8e6a33eb8e2d17e28e2cac718e123bbe8d168f0c8d162c498d0808838cf0f9b88cab56d48c57b6d88c4774ac8bfe44098bec78e08bba4a118b05f4d18af585288a9a90728a912fdc8a51a18489f29eff89c902db89b4562d89827cb1897d068e896d1f55895b162189087eb088d65c26889ba82088953d1286d9c3d586b6ccd886801919865fe9e5865b4f538641452e863c95e485ea68db85d2d2de85a448af8515da35850c424084cfdacb849e3cf48455ec0583621a8f834e52c582f13efc82b4bae582862a6a827e5896821cac9b8209e819817770d7816d7cb2814bdf0f8084cf678073a642806c5988801b9f2a801a70297fce200e7fc8916c7fa9cfbb7fa84a4c7fa13d7e7f15bdc57f0016f07ee9bf967ed564d07ecebcfc7ec9990d7eb127c07e3cb56c7e3c19487e3bc60f7e14f9597e0886537de735e17ddeb4297daf43927d712b707d5b86897d3b05d97d2961067d255be27d1d6b437ce9d1ee7ce737867cd9a0677c9397af7c7314117beb79017b739cc27b09a6d77ac9588e7ac5e4487ab896b57aac3d267a417e7c79d990917941fc8478279c9877bcd96377b83e79773de77e7734cde37675bf23762eec84762a787075ff59f6756e7bd07569fb967537f144752403fa74b336da743e3ba37420bf9873bdb4c773a4ec937392148d731cf5037309ab3072b1a76c724b87b77237425b721f18e571de5e4b71d9fde671d08e2e717d8a0e71783d6f70dec72e70ba1c1d70b1d5147079bf79706954a570375b576fee25a76fceaaa36f56447d6f49a4a86f26fd886efe1b7a6ee127d46ed102b46ec1b8cb6e94c7c26e654bd26e6541ff6e0e9f8a6df6f7a36df04a086dedc2706d9d58586d57f6c66d313eba6cef61ed6cc6304b6c8519e36c6561656c6413da6c58237e6bfb7f156bec021c6be7ce8c6bcce1456bc1aaa06b3d4c3b6b0f0f2f6a79906f6a472ae26a32e5826a08f55d69dc4ad869650f016943f03368fc3d3168cdfa8868c60c7268b2d4a268a41121684b597e6844acc367f266d0677e0e436721f7aa6710d64a668d439f664d0cc1664c789f662df4ac6595821b654c45b36530e040647897ff6461124264092ebf63ec5ccf637f576e634a8baf63392ab5629e5090621c409961e68c5c61c8860f61c49b0a616f0e10615847f8613a439860942d056053a8935f8b6e245f2e68a45ee54d9a5df0ff1d5dcb15c55db152f55d58c8fe5d50d62d5cca69425c04d51d5bd08c0a5bc8707c5b7574e35b3816735ae313485a8496365a788e155a61e5b659cc458f59ca4aba59c8c96659888055598516d4596c19165965c3c75921170a5920aa355918225158f3b8ad58c83dc65895c6e65878db2a58676dbc586264e35856aedc58058e5057c2251457a15ff35728bf6e56ea4ac45628a62f562503f8561c2657558200a955506d6255430bf45522770554c027a654aad60e5452914453a9fc56524ef5a652228073521b73a5516f01db50f5312a50b8e0e750721cc25048316050202551500b3a994fbea5784f3b09764eb8f33f4eb657b14eb147084e1f7a7b4e06b8ef4dbbda484d8f72d54d8bc1894d881eaf4d401a6f4d2751344d11aa5f4d03ef2a4cf3a7c34cb7d27f4c87d1f74c7aa3414c665de14c52a4654c1580634c0fc3374bf314ff4bf0951a4b9a43614b7768924b49ad794b443b264af657c64ac4d5804a8a51ac4a892b744a559a894a2a92554a06e58f49f11e9e49719562495245f5494eb20048f406a348d722ce48d2deef48b061d94884550948687e1a47dceadf47ce7b4747c8fa7a4796759a476fc461470f85c946fbe00546cfafe446ac105e467930e846623afc465d02bb45e14b3b45500519453f37d4451bdd5c44febd0844e2ef1144b5f1b844905a1143ee3a3643ed1df543e4962443d91f18439e7feb4349890a43078cca4294fd034217c5364133d350412a4523411b300240fb4a6140d4fab540c8c93c40a06cc94090da1c401a135b3fae92133f89c0233f844e8c3f7d914d3f6b58963f531f803f23f2023f0f86943f0126163eff781f3eb911f83e7c69243e4f6eee3e3482b63dc260ad3da6a5863d8e92303d8bec313d51764d3cd31ab23cb80e953c4682753c164c333c088b123bfdc3193bef87cc3bcd77cd3bb88f333bb27ded3bab6c293b930a663b7673583b736d0f3b5f591a3a82533f3a72493b3a2b63a139f636a239eaaa2339df1b6b39d4d8523971206739555f1f3903d3ae388245cb387feeca37cf13b1377c2cdb37657fb6371556de36c29b4136713d39365a6a1436120ce43604338535f7c75f35dd74b5359db58435780e303529e27c349d7911346d2990344cef8f3421c71933a7dc1f33850b42333e2f61330964e932c720f832c6e15932a6ff1c328ff051323ef19c322d9d4d3192a99a318839c130ee4af130a5379c308431f82ff81fcb2fdb59eb2fb2f6352fa84f362f3eacd62ed3627b2ec8e3522ea711da2e61ddf42e3060292e240d792e0202122df4a1712db2b3ca2da1ccd72d9791cd2d7489ad2d691bbd2d21185a2cf84ddf2cabc8f72ca3209e2ca199eb2c9b774c2c7e27132bde47d62bbea86a2ba9f1212b3b3a672b04138a2ae33f692ac4c0f42abaecf42a9295712a8269c02a7a52572a4ed7702a39bf2529cac545295f91312903284328f035782886c3762857092f27d9b63d272bcb6d26ee11c326e7667126e4dea226b1fb3c26180e832604e5c125f08f182548c654240e3f1c23d4149f23c75f2523c403b223ba1a6723b6c69723a0afb1231c4b1522c4527b22c2f7342288c771226bb99822106a4921d6b1c521bdfbbc21a02e642191619021649917210a2ac720cd5c3a20bb64b720912ea4204b33bf203d20192018d4b21fe272631fa19ca01f84eeac1f80c6681f2bb8931f203aa81ed542c81e8bcb2a1e2a26b01de49afc1dde89c41ddc8dbc1d8e63c91d8394481d6964b21d1f0ce61cc28a8f1ca5c19a1c45eec81c15b3091b6a3f1e1b39c9db1aebeea81aa2ea061a8d7ad319cf92f0198094ea1976162c1970c7dd195c86341947176e19465e1a191e356018f65e0b18ea8b6c18c15d441837abe4182d725b182c240c17c7411d17ab868f173e614e171c80a7171a728e16d36b5c16c9b6611642beaf1618b61215ead24f15b3b77515a84069158b7d5d156da13c152b595f15091e0114a2014b14956ea714481fb6141f393713d9d8f013ad96231396b50d12ca6bb212c5d6411264c6a9124babfe122e3d6d1201e02611f8798711e66e94119e2829113a79e71133481f1121ce9410fc5bb110ed23fe10df29ab109e6044109556531076b0bd100d90441009560b100743ef1003111b0ff866d40fcf03bf0f5800a90f5490b90f4d9d210eecff180e5b46230e11c0350d668a0e0d605c960d18759f0cd17dd20cc9e3d70cc5b4ca0cc0ee430c822fc80bf744820b42722d0b0b6e190af0adf40aeada790ae0faa50a9a1c810a3b231e09def96708e191e308d018ed08867abc08850360083dc51b0697f84f064a6a5b063b40b70633253f0633239e0631e2b20625808105f77c1105e6bf9a05d4281005bffdf505ab1449057c0e76057af1f7056f6048054d3cb1052a64bd051b147e048fbd5504739c58045789d60423385803a5aa72038ff5b603209ed0031f6dc302cbebf5027458ed025150cd0215eac201fddf7a01ce183f01b43ec7011ca02c00e7e5ac00bb0ef600b44dd4009804a3
  | 6 => 0xffa9cbc1ff4aa624fed192f4fec06969feb432b3fe61a5c2fe4009bcfdf91451fdd51642fdb7c25bfd9d4c28fd9b0742fc74befefbad5f62fb8ffe8efb6bd49ffa948b99fa658961fa5af28dfa479037fa0fd3abfa01d8c7f9f1e22df980d803f967192ff927e1b5f8cf4242f89fb993f888d4daf8658d3ef8163dfaf78743c4f6e9309cf596ef56f54d552cf48cd936f45592b2f43aff71f422f6e6f40584c2f2e8fb52f2bf50dbf2a3c76cf17ae1b5f1746035f117e603f096ec25f063cc14f00e78a2ef71067bef675ea4ef06a6edeef791cceeec0080ee73b286ee6d3be6ee48df17ee3724f0edae4e9feda1c33dec8fbc62ec48d298ec021bf7eb91a00ceb1ff410ea49eeceea1bec47e9ab5135e93ce9e5e910322fe89e9909e8293d9be82319e6e8225724e7bd9742e7bb7d35e77d4840e6d5af2ae62c9b80e5ef6899e5c8655be591238ee5691159e5157417e4a6a0e7e457d8ede402b8b6e3f36ecde3df5613e3994aaee375f6ade2d684b1e289acc8e263473fe20d45f2e1d40f98e1954f41e08360e6e06c521be06b881ce0311af7e00a0fc1df560d64def22159de87a972ddc13818dd7eea91dcda622adbe47b8adbaec2dfda66e603d958a612d91ca8fbd8c372e2d8b1f602d828376cd802b957d7f24d6fd7e30386d79361cfd7594034d726e74dd6df4810d685c148d6794181d5ff4ca5d5e40892d51cc9d0d4c4d2ddd48b1011d3af1fecd35837f6d325281ed30939bed207e908d1cd446ed17b1ae9d111fc10d102420cd0a72ae5d0329a38d02ac017d01d7ef5d0174610d00462b0cfeb3438cfe4de26cf715df1cf3b3326cefed776ceeef525ce87666bce7a3e1cce6ab7a5ce279589cd9c0993cd8864decd5c3993cd2def5bccc9ad0cccb40637cc458730cc0bf560cbc5f7bccb53b43ecb4495c4ca66c7e4ca4e81ccca08f618ca02bc25c9d83c0fc962b06dc922c232c8bd961ec8b851edc8498901c7fbddbac6eb0a9dc69e3bddc69359dcc65bfa87c626e72cc573b345c52d9c96c4f1d6c5c4f05b7ac4cde215c4a589f4c496bf9ec3f517dcc3d69feac3d3715ec3438186c30753cdc2c128d7c177f997c1473665c10e7a26c09055f2c02c42cdc02710fcc005d270bfbae176bf1c8152bf01754bbef57b58beeec6cebec64ddabea1d3f7bdf5486cbdba5b97bc2db127bbaf62ffbbaae6eabb6a8c07bb098617baa705e3baa6fbe4ba9d500dba167be5ba14a513b912c06fb8dff033b8d035edb839cbccb7daf973b7ba5048b72e43a4b6be779db6b0d6b8b6b0bd90b675c238b65bfb25b64ce604b6499d30b5e5e38ab5c2901eb5977028b53cb21db536cb1eb4f1bdc2b4622037b45412b5b40f8568b3d5fae2b3bee100b3aa762fb2661297b2150189b16c5780b068f111afceba13afb833d5af9a7ba3af10d16dae4fe57eae10e2e7ae0439ccadfe0143adf9701bad780e23ad5557f4ace11c2aacbfcaa6ac3c6e77ac2d7431abf57e7fabbc0f30ab7f050caaf53b11aaebca4caac4765eaa85095daa4b8fdeaa3c7abdaa3c3488aa1cae2fa9b224d7a8f7051da8d27c72a8ae6961a893fa55a7e600dea7d8b51ea7c1a653a780ba62a5ea216fa5e91d28a5d61d5ba564e6faa4fa4615a4d85b0fa4745e7fa39f5a7fa389545ba3430b89a3006626a25a727ca23555bfa201bb89a1ced0ada1b2c621a0215ce4a01f90829fe426d09fd66fba9f5455a69f43f8789ee5bd389e6129869e402de39d95190d9d8031b69d13b7159c9620ae9c2483369bd817699bd50df49bc849d79bb13b0c9ba3bc549b7e900b9b5d2e1e9af1e3839a7a7c569a0693ac99d9f54699b800a298f1effc9863b91c97f8a56697de819c97ba72e697a44acc979d69d49779cefd9773db3a9765ea9f96bbc6159675c7349644495d95d6208e95b94f93958d2e27957ce9c1947384c69342a44191c9624b91150de8910a7847908092f99051fccd9007e1398e6a110f8e60ec908dfcd2788d8b4d608d3180948d162c498c69d0228c21bd0c8c1a9d008bdf91678b9b3ebd8b97ce0c8b4a6c148b27d0898b139fa58ac772b48a51a1848a33de1689cc4f5c896c7e7a888d98ee8883edbb8828d694880995ba87d5552687516026872c323186a7d6de86a103b286314188857683e8851d4dcf84c39e9f848deadb846e2efe8448db498406e4a5839571f3837901308348064a83472cee82d1890a82c8048b828920e1823555ad8217407381f2a445814bdf0f80deb8a180bb0d2a8073a6427fc7610c7f6a1ed67f4698e17f3a00cd7f18fba87e57fb957e3645577de43bda7ddcbe8f7dd4be797dca8f6d7d90a67d7d70c1757d0874757d02442a7c542aae7b64d9a07a631ba67a6037057a2c1dc579edeb457951259f78c1abb8781fd2a97789977f7737399c76bcbfdf76437fd0762eec8475e238fe75d809c4755919177556673c75471d5375122cda74a697ba74367062742993cd73dd5b4e735ee46d731cf503729b930b7280e39d723b5998721f18e571f6293871a57f13715ff35f71014a567071f987705b572b7039f53e6fb3df9a6f546e596ef54f8d6ec1b8cb6e6f53fe6df3a4876dceb71c6db2046f6d704c4d6d2c4f6f6cd56c866cb140716c374e346bec021c6bcc2ffa6b1c3f076a472ae26a21eef669dc4ad869c7c6b7695faa9068d47c116826051b66816b41663c4f11662570b765f027ea6595821b64e4a85964b90a08647897ff6384ae6e6374a1806314967762df48a66279ad486255f0926244f8ea6238e03b61fad96b61d7028a61388cac613685c66130397160c50c77607805dd60759bcd600125ff5f57f6d95ef902bc5edc13645ec974d35e1574e45ddcca165d6a600e5d69ec3d5d50d62d5cfa162d5c6b67af5c08f9515bc8707c5b7dcad259ca4aba598516d458f0383e5870250357a5ba0857a15ff35789df9b577a95b25749223b570faa3c56f4079356c06f385669c25656440a0056278bb35610d3ad54d8ecff54a4282c5414d75d53e4a66053a9fc5652fb89f5529fc04c529ae4eb52827441521530595196825d519331cf510e8ffc50a0eac44feaf79c4ef447864eb112464e624f674dba67a44cfe95704ceb734a4cc8a45c4bf0951a4bcb5bc64b9986ff4b6853994ac4d5804aa373e74a9a08d04a332e5c4a23e47349b16fc349170df048d088a948ba226e48b6248b488be13047d3abc847c8fa7a47afa9ab47a0948a4725888d47163ea44710f19e46f891f246cfafe4468f5505465d02bb46479d424621aed145cbe23745ac7c9f458b998f44f76e5144b9e73e448968f144360de4442e51ca441150b943f97bad43f51a0d43e4962443b61d73437b807d42b42b6542a5f5f9425fb1de420aaafd41b58b3d418b6f38410f8bc34109363a4090da1c40647ff34016412d401479953fe3e6983f89f14b3f6b58963f4fa2ad3edeebb73e5ea4d43d51764d3cfd86933bfc6b3d3bb88f333b280ba63a7ee9be3a72493b39f0e743397b2e48392c63a4391554d938da1db538b547973877825f37d7904037977767375ede803732b7b236d7a08b365d9a6d36484fbc3604338535a51ff635780e3034ce5d4a3473aa8a342511e333c9fabc33b8da8433a2a6ce3391de5f3378ba533342085b3313b45632f23c0432ce8070321ccdb731ef360f31d6dd4d31be2fe4315a47233132012b30cd9ec830ab34b530a36b7c2fb2f6352fa1a8052f853c132f320dcf2ec8e3522ec74d982ebe9f792e621c8c2e61ddf42df800f92de07bfc2dccf3d12d9f2a062d9bcbf82d9791cd2d947f3e2d5e40f92d5464b32d21185a2ca4dc502c1832272bde47d62bce2adc2ba02fb32b20d1202ada02a629e3220a29d40ce9295357622949b7032922cdb028f19e7d2855273028132b512797f7e32777ac0b2769c84d27306929271e5e5326d09847268bc6d1266e3bcf25eb571c25e3f8ae256ac91c246a063c23c403b223a0afb1234f43c622ddb14d2297f85221fec89c21db5c9020921d332078ac3420451ab9203170b82018d4b21ffdd2831fe272631fe1c0be1fddbe2f1f80c6681ecdb6c11ec9975f1e6485541e345c711e30a66b1e13bd261daf09671da1e52f1d3774ea1cbd34661cad64831c9e1a9a1c8c70cb1c7d5baa1c5134ca1bf305c41b5fdc031b48cd381b3458951aae07881a66916d1a32faab1a2b568b19eeff8c198094ea197ecafc196fb5db195c8634195a5dd5194fd03a19465e1a18e8860718e55ff5182d725b1815ed59176594ed17404bd417045ba016a722e915e0720a154d8cb81541471314a2014b13d9d8f013c6bdbe1355076f134652cb134598301320affe1233a14411ef5d0811968bc61121ce941106c3fb10acc91f0fbe17670f686d050e4ec9fd0e092ac40e01a33b0df21bf90dc3d05a0d9ac0800d1c99280cfb76e60cc9e3d70cb888260cb5b2f30bafc9450b7ec8910b7ad6450b569fac0b2fe08d0afb84f50ae4762a0ad0d4b50a8afd7a0a1ca09a0a155a3e0a097f9d09d0aa8f09cb704209acedd90951d6b2090eefb9090410a608f0c91708de944f08af8e3b08aada8d083934540800cd3207fd9b0f0781cc31071044b706f3628d06cbfd2f06a4f6e506676eba063310ab06200cea05def1c1058a1ee8051b147e04f658b404739c5800e1617f00bb0ef600aaf1fc
  | 7 => 0xf6e9309ce3f36ecdd91ca8fbd7e30386d6df4810d30939bed0329a38cbc5f7bccb4495c4ca08f618c8b851edbc2db127b6be779da893fa55a4745e7fa3430b89a25a727c9e402de39c2483369b5d2e1e97f8a5669007e1398b9b3ebd872c323186a103b27fc7610c76bcbfdf7556673c75471d5373dd5b4e6595821b6255f09261fad96b5edc1364598516d456440a005414d75d529ae4eb510e8ffc4cfe95704b68539947afa9ab47a0948a47163ea440647ff3392c63a4391554d92bce2adc2797f7e326d098471c9e1a9a134652cb0cb888260a155a3e058a1ee8
  | 8 => 0xf6e9309c
  | _ => 0

def stateCode : Nat → Nat → Nat
  | 2, i => level2 i
  | 3, i => level3 i
  | 4, i => level4 i
  | 5, i => level5 i
  | 6, i => level6 i
  | 7, i => level7 i
  | 8, i => level8 i
  | _, _ => 0

def state (d i : Nat) : List Nat :=
  let code := stateCode d i
  decodeState (code % 16) (code / 16)

def test (d : Nat) := bar 76 state number (idxGen number hashes) id [] d

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part2_0 : span (test 2) 12 0 = true := by decide +kernel
theorem all2 : span (test 2) 12 0 = true := part2_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_0 : span (test 3) 12 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_12 : span (test 3) 12 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_24 : span (test 3) 12 24 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_36 : span (test 3) 12 36 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_48 : span (test 3) 12 48 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_60 : span (test 3) 12 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_72 : span (test 3) 12 72 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_84 : span (test 3) 7 84 = true := by decide +kernel
theorem all3 : span (test 3) 91 0 = true := (@span_join (test 3) 48 0 43 (@span_join (test 3) 24 0 24 (@span_join (test 3) 12 0 12 part3_0 part3_12) (@span_join (test 3) 12 24 12 part3_24 part3_36)) (@span_join (test 3) 24 48 19 (@span_join (test 3) 12 48 12 part3_48 part3_60) (@span_join (test 3) 12 72 7 part3_72 part3_84)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_0 : span (test 4) 12 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_12 : span (test 4) 12 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_24 : span (test 4) 12 24 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_36 : span (test 4) 12 36 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_48 : span (test 4) 12 48 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_60 : span (test 4) 12 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_72 : span (test 4) 12 72 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_84 : span (test 4) 12 84 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_96 : span (test 4) 12 96 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_108 : span (test 4) 12 108 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_120 : span (test 4) 12 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_132 : span (test 4) 12 132 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_144 : span (test 4) 12 144 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_156 : span (test 4) 12 156 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_168 : span (test 4) 12 168 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_180 : span (test 4) 12 180 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_192 : span (test 4) 12 192 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_204 : span (test 4) 12 204 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_216 : span (test 4) 12 216 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_228 : span (test 4) 12 228 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_240 : span (test 4) 12 240 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_252 : span (test 4) 12 252 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_264 : span (test 4) 12 264 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_276 : span (test 4) 12 276 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_288 : span (test 4) 12 288 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_300 : span (test 4) 12 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_312 : span (test 4) 12 312 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_324 : span (test 4) 12 324 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_336 : span (test 4) 12 336 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_348 : span (test 4) 12 348 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_360 : span (test 4) 12 360 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_372 : span (test 4) 12 372 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_384 : span (test 4) 12 384 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_396 : span (test 4) 12 396 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_408 : span (test 4) 12 408 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_420 : span (test 4) 12 420 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_432 : span (test 4) 12 432 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_444 : span (test 4) 12 444 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_456 : span (test 4) 12 456 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_468 : span (test 4) 12 468 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_480 : span (test 4) 12 480 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_492 : span (test 4) 3 492 = true := by decide +kernel
theorem all4 : span (test 4) 495 0 = true := (@span_join (test 4) 252 0 243 (@span_join (test 4) 120 0 132 (@span_join (test 4) 60 0 60 (@span_join (test 4) 24 0 36 (@span_join (test 4) 12 0 12 part4_0 part4_12) (@span_join (test 4) 12 24 24 part4_24 (@span_join (test 4) 12 36 12 part4_36 part4_48))) (@span_join (test 4) 24 60 36 (@span_join (test 4) 12 60 12 part4_60 part4_72) (@span_join (test 4) 12 84 24 part4_84 (@span_join (test 4) 12 96 12 part4_96 part4_108)))) (@span_join (test 4) 60 120 72 (@span_join (test 4) 24 120 36 (@span_join (test 4) 12 120 12 part4_120 part4_132) (@span_join (test 4) 12 144 24 part4_144 (@span_join (test 4) 12 156 12 part4_156 part4_168))) (@span_join (test 4) 36 180 36 (@span_join (test 4) 12 180 24 part4_180 (@span_join (test 4) 12 192 12 part4_192 part4_204)) (@span_join (test 4) 12 216 24 part4_216 (@span_join (test 4) 12 228 12 part4_228 part4_240))))) (@span_join (test 4) 120 252 123 (@span_join (test 4) 60 252 60 (@span_join (test 4) 24 252 36 (@span_join (test 4) 12 252 12 part4_252 part4_264) (@span_join (test 4) 12 276 24 part4_276 (@span_join (test 4) 12 288 12 part4_288 part4_300))) (@span_join (test 4) 24 312 36 (@span_join (test 4) 12 312 12 part4_312 part4_324) (@span_join (test 4) 12 336 24 part4_336 (@span_join (test 4) 12 348 12 part4_348 part4_360)))) (@span_join (test 4) 60 372 63 (@span_join (test 4) 24 372 36 (@span_join (test 4) 12 372 12 part4_372 part4_384) (@span_join (test 4) 12 396 24 part4_396 (@span_join (test 4) 12 408 12 part4_408 part4_420))) (@span_join (test 4) 36 432 27 (@span_join (test 4) 12 432 24 part4_432 (@span_join (test 4) 12 444 12 part4_444 part4_456)) (@span_join (test 4) 12 468 15 part4_468 (@span_join (test 4) 12 480 3 part4_480 part4_492))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_0 : span (test 5) 12 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_12 : span (test 5) 12 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_24 : span (test 5) 12 24 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_36 : span (test 5) 12 36 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_48 : span (test 5) 12 48 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_60 : span (test 5) 12 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_72 : span (test 5) 12 72 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_84 : span (test 5) 12 84 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_96 : span (test 5) 12 96 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_108 : span (test 5) 12 108 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_120 : span (test 5) 12 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_132 : span (test 5) 12 132 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_144 : span (test 5) 12 144 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_156 : span (test 5) 12 156 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_168 : span (test 5) 12 168 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_180 : span (test 5) 12 180 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_192 : span (test 5) 12 192 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_204 : span (test 5) 12 204 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_216 : span (test 5) 12 216 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_228 : span (test 5) 12 228 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_240 : span (test 5) 12 240 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_252 : span (test 5) 12 252 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_264 : span (test 5) 12 264 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_276 : span (test 5) 12 276 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_288 : span (test 5) 12 288 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_300 : span (test 5) 12 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_312 : span (test 5) 12 312 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_324 : span (test 5) 12 324 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_336 : span (test 5) 12 336 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_348 : span (test 5) 12 348 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_360 : span (test 5) 12 360 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_372 : span (test 5) 12 372 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_384 : span (test 5) 12 384 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_396 : span (test 5) 12 396 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_408 : span (test 5) 12 408 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_420 : span (test 5) 12 420 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_432 : span (test 5) 12 432 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_444 : span (test 5) 12 444 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_456 : span (test 5) 12 456 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_468 : span (test 5) 12 468 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_480 : span (test 5) 12 480 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_492 : span (test 5) 12 492 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_504 : span (test 5) 12 504 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_516 : span (test 5) 12 516 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_528 : span (test 5) 12 528 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_540 : span (test 5) 12 540 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_552 : span (test 5) 12 552 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_564 : span (test 5) 12 564 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_576 : span (test 5) 12 576 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_588 : span (test 5) 12 588 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_600 : span (test 5) 12 600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_612 : span (test 5) 12 612 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_624 : span (test 5) 12 624 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_636 : span (test 5) 12 636 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_648 : span (test 5) 12 648 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_660 : span (test 5) 12 660 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_672 : span (test 5) 12 672 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_684 : span (test 5) 12 684 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_696 : span (test 5) 12 696 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_708 : span (test 5) 12 708 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_720 : span (test 5) 12 720 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_732 : span (test 5) 12 732 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_744 : span (test 5) 12 744 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_756 : span (test 5) 12 756 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_768 : span (test 5) 12 768 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_780 : span (test 5) 12 780 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_792 : span (test 5) 12 792 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_804 : span (test 5) 12 804 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_816 : span (test 5) 12 816 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_828 : span (test 5) 12 828 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_840 : span (test 5) 12 840 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_852 : span (test 5) 12 852 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_864 : span (test 5) 12 864 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_876 : span (test 5) 12 876 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_888 : span (test 5) 12 888 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_900 : span (test 5) 12 900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_912 : span (test 5) 12 912 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_924 : span (test 5) 12 924 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_936 : span (test 5) 12 936 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_948 : span (test 5) 12 948 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_960 : span (test 5) 12 960 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_972 : span (test 5) 12 972 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_984 : span (test 5) 12 984 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_996 : span (test 5) 12 996 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1008 : span (test 5) 12 1008 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1020 : span (test 5) 12 1020 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1032 : span (test 5) 12 1032 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1044 : span (test 5) 12 1044 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1056 : span (test 5) 12 1056 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1068 : span (test 5) 12 1068 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1080 : span (test 5) 12 1080 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1092 : span (test 5) 12 1092 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1104 : span (test 5) 12 1104 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1116 : span (test 5) 12 1116 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1128 : span (test 5) 12 1128 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1140 : span (test 5) 12 1140 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1152 : span (test 5) 12 1152 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1164 : span (test 5) 12 1164 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1176 : span (test 5) 12 1176 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1188 : span (test 5) 12 1188 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1200 : span (test 5) 10 1200 = true := by decide +kernel
theorem all5 : span (test 5) 1210 0 = true := (@span_join (test 5) 600 0 610 (@span_join (test 5) 300 0 300 (@span_join (test 5) 144 0 156 (@span_join (test 5) 72 0 72 (@span_join (test 5) 36 0 36 (@span_join (test 5) 12 0 24 part5_0 (@span_join (test 5) 12 12 12 part5_12 part5_24)) (@span_join (test 5) 12 36 24 part5_36 (@span_join (test 5) 12 48 12 part5_48 part5_60))) (@span_join (test 5) 36 72 36 (@span_join (test 5) 12 72 24 part5_72 (@span_join (test 5) 12 84 12 part5_84 part5_96)) (@span_join (test 5) 12 108 24 part5_108 (@span_join (test 5) 12 120 12 part5_120 part5_132)))) (@span_join (test 5) 72 144 84 (@span_join (test 5) 36 144 36 (@span_join (test 5) 12 144 24 part5_144 (@span_join (test 5) 12 156 12 part5_156 part5_168)) (@span_join (test 5) 12 180 24 part5_180 (@span_join (test 5) 12 192 12 part5_192 part5_204))) (@span_join (test 5) 36 216 48 (@span_join (test 5) 12 216 24 part5_216 (@span_join (test 5) 12 228 12 part5_228 part5_240)) (@span_join (test 5) 24 252 24 (@span_join (test 5) 12 252 12 part5_252 part5_264) (@span_join (test 5) 12 276 12 part5_276 part5_288))))) (@span_join (test 5) 144 300 156 (@span_join (test 5) 72 300 72 (@span_join (test 5) 36 300 36 (@span_join (test 5) 12 300 24 part5_300 (@span_join (test 5) 12 312 12 part5_312 part5_324)) (@span_join (test 5) 12 336 24 part5_336 (@span_join (test 5) 12 348 12 part5_348 part5_360))) (@span_join (test 5) 36 372 36 (@span_join (test 5) 12 372 24 part5_372 (@span_join (test 5) 12 384 12 part5_384 part5_396)) (@span_join (test 5) 12 408 24 part5_408 (@span_join (test 5) 12 420 12 part5_420 part5_432)))) (@span_join (test 5) 72 444 84 (@span_join (test 5) 36 444 36 (@span_join (test 5) 12 444 24 part5_444 (@span_join (test 5) 12 456 12 part5_456 part5_468)) (@span_join (test 5) 12 480 24 part5_480 (@span_join (test 5) 12 492 12 part5_492 part5_504))) (@span_join (test 5) 36 516 48 (@span_join (test 5) 12 516 24 part5_516 (@span_join (test 5) 12 528 12 part5_528 part5_540)) (@span_join (test 5) 24 552 24 (@span_join (test 5) 12 552 12 part5_552 part5_564) (@span_join (test 5) 12 576 12 part5_576 part5_588)))))) (@span_join (test 5) 300 600 310 (@span_join (test 5) 144 600 156 (@span_join (test 5) 72 600 72 (@span_join (test 5) 36 600 36 (@span_join (test 5) 12 600 24 part5_600 (@span_join (test 5) 12 612 12 part5_612 part5_624)) (@span_join (test 5) 12 636 24 part5_636 (@span_join (test 5) 12 648 12 part5_648 part5_660))) (@span_join (test 5) 36 672 36 (@span_join (test 5) 12 672 24 part5_672 (@span_join (test 5) 12 684 12 part5_684 part5_696)) (@span_join (test 5) 12 708 24 part5_708 (@span_join (test 5) 12 720 12 part5_720 part5_732)))) (@span_join (test 5) 72 744 84 (@span_join (test 5) 36 744 36 (@span_join (test 5) 12 744 24 part5_744 (@span_join (test 5) 12 756 12 part5_756 part5_768)) (@span_join (test 5) 12 780 24 part5_780 (@span_join (test 5) 12 792 12 part5_792 part5_804))) (@span_join (test 5) 36 816 48 (@span_join (test 5) 12 816 24 part5_816 (@span_join (test 5) 12 828 12 part5_828 part5_840)) (@span_join (test 5) 24 852 24 (@span_join (test 5) 12 852 12 part5_852 part5_864) (@span_join (test 5) 12 876 12 part5_876 part5_888))))) (@span_join (test 5) 156 900 154 (@span_join (test 5) 72 900 84 (@span_join (test 5) 36 900 36 (@span_join (test 5) 12 900 24 part5_900 (@span_join (test 5) 12 912 12 part5_912 part5_924)) (@span_join (test 5) 12 936 24 part5_936 (@span_join (test 5) 12 948 12 part5_948 part5_960))) (@span_join (test 5) 36 972 48 (@span_join (test 5) 12 972 24 part5_972 (@span_join (test 5) 12 984 12 part5_984 part5_996)) (@span_join (test 5) 24 1008 24 (@span_join (test 5) 12 1008 12 part5_1008 part5_1020) (@span_join (test 5) 12 1032 12 part5_1032 part5_1044)))) (@span_join (test 5) 72 1056 82 (@span_join (test 5) 36 1056 36 (@span_join (test 5) 12 1056 24 part5_1056 (@span_join (test 5) 12 1068 12 part5_1068 part5_1080)) (@span_join (test 5) 12 1092 24 part5_1092 (@span_join (test 5) 12 1104 12 part5_1104 part5_1116))) (@span_join (test 5) 36 1128 46 (@span_join (test 5) 12 1128 24 part5_1128 (@span_join (test 5) 12 1140 12 part5_1140 part5_1152)) (@span_join (test 5) 24 1164 22 (@span_join (test 5) 12 1164 12 part5_1164 part5_1176) (@span_join (test 5) 12 1188 10 part5_1188 part5_1200)))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_0 : span (test 6) 12 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_12 : span (test 6) 12 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_24 : span (test 6) 12 24 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_36 : span (test 6) 12 36 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_48 : span (test 6) 12 48 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_60 : span (test 6) 12 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_72 : span (test 6) 12 72 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_84 : span (test 6) 12 84 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_96 : span (test 6) 12 96 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_108 : span (test 6) 12 108 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_120 : span (test 6) 12 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_132 : span (test 6) 12 132 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_144 : span (test 6) 12 144 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_156 : span (test 6) 12 156 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_168 : span (test 6) 12 168 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_180 : span (test 6) 12 180 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_192 : span (test 6) 12 192 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_204 : span (test 6) 12 204 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_216 : span (test 6) 12 216 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_228 : span (test 6) 12 228 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_240 : span (test 6) 12 240 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_252 : span (test 6) 12 252 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_264 : span (test 6) 12 264 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_276 : span (test 6) 12 276 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_288 : span (test 6) 12 288 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_300 : span (test 6) 12 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_312 : span (test 6) 12 312 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_324 : span (test 6) 12 324 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_336 : span (test 6) 12 336 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_348 : span (test 6) 12 348 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_360 : span (test 6) 12 360 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_372 : span (test 6) 12 372 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_384 : span (test 6) 12 384 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_396 : span (test 6) 12 396 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_408 : span (test 6) 12 408 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_420 : span (test 6) 12 420 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_432 : span (test 6) 12 432 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_444 : span (test 6) 12 444 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_456 : span (test 6) 12 456 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_468 : span (test 6) 12 468 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_480 : span (test 6) 12 480 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_492 : span (test 6) 12 492 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_504 : span (test 6) 12 504 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_516 : span (test 6) 12 516 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_528 : span (test 6) 12 528 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_540 : span (test 6) 12 540 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_552 : span (test 6) 12 552 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_564 : span (test 6) 12 564 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_576 : span (test 6) 12 576 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_588 : span (test 6) 12 588 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_600 : span (test 6) 12 600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_612 : span (test 6) 12 612 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_624 : span (test 6) 12 624 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_636 : span (test 6) 12 636 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_648 : span (test 6) 12 648 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_660 : span (test 6) 12 660 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_672 : span (test 6) 12 672 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_684 : span (test 6) 12 684 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_696 : span (test 6) 12 696 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_708 : span (test 6) 12 708 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_720 : span (test 6) 12 720 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_732 : span (test 6) 12 732 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_744 : span (test 6) 12 744 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_756 : span (test 6) 12 756 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_768 : span (test 6) 12 768 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_780 : span (test 6) 12 780 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_792 : span (test 6) 12 792 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_804 : span (test 6) 12 804 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_816 : span (test 6) 12 816 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_828 : span (test 6) 5 828 = true := by decide +kernel
theorem all6 : span (test 6) 833 0 = true := (@span_join (test 6) 420 0 413 (@span_join (test 6) 204 0 216 (@span_join (test 6) 96 0 108 (@span_join (test 6) 48 0 48 (@span_join (test 6) 24 0 24 (@span_join (test 6) 12 0 12 part6_0 part6_12) (@span_join (test 6) 12 24 12 part6_24 part6_36)) (@span_join (test 6) 24 48 24 (@span_join (test 6) 12 48 12 part6_48 part6_60) (@span_join (test 6) 12 72 12 part6_72 part6_84))) (@span_join (test 6) 48 96 60 (@span_join (test 6) 24 96 24 (@span_join (test 6) 12 96 12 part6_96 part6_108) (@span_join (test 6) 12 120 12 part6_120 part6_132)) (@span_join (test 6) 24 144 36 (@span_join (test 6) 12 144 12 part6_144 part6_156) (@span_join (test 6) 12 168 24 part6_168 (@span_join (test 6) 12 180 12 part6_180 part6_192))))) (@span_join (test 6) 108 204 108 (@span_join (test 6) 48 204 60 (@span_join (test 6) 24 204 24 (@span_join (test 6) 12 204 12 part6_204 part6_216) (@span_join (test 6) 12 228 12 part6_228 part6_240)) (@span_join (test 6) 24 252 36 (@span_join (test 6) 12 252 12 part6_252 part6_264) (@span_join (test 6) 12 276 24 part6_276 (@span_join (test 6) 12 288 12 part6_288 part6_300)))) (@span_join (test 6) 48 312 60 (@span_join (test 6) 24 312 24 (@span_join (test 6) 12 312 12 part6_312 part6_324) (@span_join (test 6) 12 336 12 part6_336 part6_348)) (@span_join (test 6) 24 360 36 (@span_join (test 6) 12 360 12 part6_360 part6_372) (@span_join (test 6) 12 384 24 part6_384 (@span_join (test 6) 12 396 12 part6_396 part6_408)))))) (@span_join (test 6) 204 420 209 (@span_join (test 6) 96 420 108 (@span_join (test 6) 48 420 48 (@span_join (test 6) 24 420 24 (@span_join (test 6) 12 420 12 part6_420 part6_432) (@span_join (test 6) 12 444 12 part6_444 part6_456)) (@span_join (test 6) 24 468 24 (@span_join (test 6) 12 468 12 part6_468 part6_480) (@span_join (test 6) 12 492 12 part6_492 part6_504))) (@span_join (test 6) 48 516 60 (@span_join (test 6) 24 516 24 (@span_join (test 6) 12 516 12 part6_516 part6_528) (@span_join (test 6) 12 540 12 part6_540 part6_552)) (@span_join (test 6) 24 564 36 (@span_join (test 6) 12 564 12 part6_564 part6_576) (@span_join (test 6) 12 588 24 part6_588 (@span_join (test 6) 12 600 12 part6_600 part6_612))))) (@span_join (test 6) 108 624 101 (@span_join (test 6) 48 624 60 (@span_join (test 6) 24 624 24 (@span_join (test 6) 12 624 12 part6_624 part6_636) (@span_join (test 6) 12 648 12 part6_648 part6_660)) (@span_join (test 6) 24 672 36 (@span_join (test 6) 12 672 12 part6_672 part6_684) (@span_join (test 6) 12 696 24 part6_696 (@span_join (test 6) 12 708 12 part6_708 part6_720)))) (@span_join (test 6) 48 732 53 (@span_join (test 6) 24 732 24 (@span_join (test 6) 12 732 12 part6_732 part6_744) (@span_join (test 6) 12 756 12 part6_756 part6_768)) (@span_join (test 6) 24 780 29 (@span_join (test 6) 12 780 12 part6_780 part6_792) (@span_join (test 6) 12 804 17 part6_804 (@span_join (test 6) 12 816 5 part6_816 part6_828)))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_0 : span (test 7) 12 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_12 : span (test 7) 12 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_24 : span (test 7) 12 24 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_36 : span (test 7) 12 36 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_48 : span (test 7) 7 48 = true := by decide +kernel
theorem all7 : span (test 7) 55 0 = true := (@span_join (test 7) 24 0 31 (@span_join (test 7) 12 0 12 part7_0 part7_12) (@span_join (test 7) 12 24 19 part7_24 (@span_join (test 7) 12 36 7 part7_36 part7_48)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part8_0 : span (test 8) 1 0 = true := by decide +kernel
theorem all8 : span (test 8) 1 0 = true := part8_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem lowerFn : ∀ s, HasCircuitSize 6 edgeFn s → 9 ≤ s := by
  refine prove_base 6 76 8 edgeFn sampleRows inputWords [] number hashes state (by decide +kernel)
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) ?_
  intro s hs
  interval_cases s
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => span_ok all2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all8 i (Nat.zero_le i) hi

theorem lower (s : Nat) (h : HasCircuitSize 6 six s) : 9 ≤ s := by
  have heq : six = edgeFn := by decide +kernel
  exact lowerFn s (heq ▸ h)

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [13, 12]⟩], 14⟩

theorem good : ∀ g ∈ witness.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

theorem values : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = six x := by decide +kernel

end PEqualNP.Outside.L_meta_9140

open PEqualNP.Outside.L_meta_9140 in
theorem PEqualNP.Outside.L_meta_9140 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  have h : PEqualNP.MetaComplexity.HasCircuitSize 6 six gates.length := by
    refine ⟨⟨gates, o⟩, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨witness.gates, witness.output, good, ?_, values⟩
  exact lower gates.length h
