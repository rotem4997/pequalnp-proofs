import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12314_aux

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

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
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


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
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
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
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
      · exact absurd hop (hm p g hg)
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

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
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


/-! ## Family 1: a certified frontier search (Run states closed under the moves of `next`) -/

theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr


/-- the table index, written out for six inputs -/
def idx6 (x : Fin 6 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0) + (if x 5 then 2 ^ 5 else 0)

theorem sum_eq (x : Fin 6 → Bool) : (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  rw [Fin.sum_univ_six]; rfl

/-- a function true at the all-false input needs a gate -/
theorem one_le {n : ℕ} (f : BFn n) (hf : f (fun _ => false) = true) :
    ∀ s, HasCircuitSize n f s → 1 ≤ s := by
  intro s hs
  obtain ⟨C, _, hle, hC⟩ := hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exfalso
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hle)
    have h1 := hC (fun _ => false)
    rw [hf] at h1
    have e : C.eval (List.ofFn fun _ : Fin n => false) = false := by
      unfold Circuit.eval Circuit.wires
      rw [hg, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split <;> rfl
    rw [e] at h1
    exact Bool.false_ne_true h1
  · exact hpos

namespace R0

namespace B0

def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := 4294967295
def Y_ : ℕ := 4276676736
def XS_ : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760,0]
def PD_ : List (ℕ × ℕ) := [(1,18093120),(2,17961504),(4,17171976),(8,1441896),(16,5736)]
def PM_ : List (ℕ × ℕ) := [(3,4276676736),(5,4276676736),(6,4276676736),(9,4276676736),(10,4276676736),(12,4276676736),(17,4276676736),(18,4276676736),(20,4276676736),(24,4276676736)]

def G_ : List (List ℕ) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31],[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31],[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31],[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],[0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31],[0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,2,3,6,7,18,19,22,23,10,11,14,15,26,27,30,31],[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31],[0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31],[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31],[0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31],[0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31],[0,1,8,9,16,17,24,25,4,5,12,13,20,21,28,29,2,3,10,11,18,19,26,27,6,7,14,15,22,23,30,31],[0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31],[0,1,16,17,2,3,18,19,8,9,24,25,10,11,26,27,4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31],[0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31],[0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31],[0,1,16,17,8,9,24,25,2,3,18,19,10,11,26,27,4,5,20,21,12,13,28,29,6,7,22,23,14,15,30,31],[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31],[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31],[0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31],[0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31],[0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31],[0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31],[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31],[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31],[0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23,8,10,12,14,9,11,13,15,24,26,28,30,25,27,29,31],[0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15,16,18,20,22,24,26,28,30,17,19,21,23,25,27,29,31],[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31],[0,2,4,6,16,18,20,22,1,3,5,7,17,19,21,23,8,10,12,14,24,26,28,30,9,11,13,15,25,27,29,31],[0,2,4,6,16,18,20,22,8,10,12,14,24,26,28,30,1,3,5,7,17,19,21,23,9,11,13,15,25,27,29,31],[0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15,16,18,24,26,17,19,25,27,20,22,28,30,21,23,29,31],[0,2,8,10,1,3,9,11,16,18,24,26,17,19,25,27,4,6,12,14,5,7,13,15,20,22,28,30,21,23,29,31],[0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15,16,18,24,26,20,22,28,30,17,19,25,27,21,23,29,31],[0,2,8,10,4,6,12,14,16,18,24,26,20,22,28,30,1,3,9,11,5,7,13,15,17,19,25,27,21,23,29,31],[0,2,8,10,16,18,24,26,1,3,9,11,17,19,25,27,4,6,12,14,20,22,28,30,5,7,13,15,21,23,29,31],[0,2,8,10,16,18,24,26,4,6,12,14,20,22,28,30,1,3,9,11,17,19,25,27,5,7,13,15,21,23,29,31],[0,2,16,18,1,3,17,19,4,6,20,22,5,7,21,23,8,10,24,26,9,11,25,27,12,14,28,30,13,15,29,31],[0,2,16,18,1,3,17,19,8,10,24,26,9,11,25,27,4,6,20,22,5,7,21,23,12,14,28,30,13,15,29,31],[0,2,16,18,4,6,20,22,1,3,17,19,5,7,21,23,8,10,24,26,12,14,28,30,9,11,25,27,13,15,29,31],[0,2,16,18,4,6,20,22,8,10,24,26,12,14,28,30,1,3,17,19,5,7,21,23,9,11,25,27,13,15,29,31],[0,2,16,18,8,10,24,26,1,3,17,19,9,11,25,27,4,6,20,22,12,14,28,30,5,7,21,23,13,15,29,31],[0,2,16,18,8,10,24,26,4,6,20,22,12,14,28,30,1,3,17,19,9,11,25,27,5,7,21,23,13,15,29,31],[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31],[0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31],[0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15,16,20,17,21,24,28,25,29,18,22,19,23,26,30,27,31],[0,4,1,5,8,12,9,13,16,20,17,21,24,28,25,29,2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31],[0,4,1,5,16,20,17,21,2,6,3,7,18,22,19,23,8,12,9,13,24,28,25,29,10,14,11,15,26,30,27,31],[0,4,1,5,16,20,17,21,8,12,9,13,24,28,25,29,2,6,3,7,18,22,19,23,10,14,11,15,26,30,27,31],[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,16,20,18,22,17,21,19,23,24,28,26,30,25,29,27,31],[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31],[0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15,16,20,18,22,24,28,26,30,17,21,19,23,25,29,27,31],[0,4,2,6,8,12,10,14,16,20,18,22,24,28,26,30,1,5,3,7,9,13,11,15,17,21,19,23,25,29,27,31],[0,4,2,6,16,20,18,22,1,5,3,7,17,21,19,23,8,12,10,14,24,28,26,30,9,13,11,15,25,29,27,31],[0,4,2,6,16,20,18,22,8,12,10,14,24,28,26,30,1,5,3,7,17,21,19,23,9,13,11,15,25,29,27,31],[0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31],[0,4,8,12,1,5,9,13,16,20,24,28,17,21,25,29,2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31],[0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15,16,20,24,28,18,22,26,30,17,21,25,29,19,23,27,31],[0,4,8,12,2,6,10,14,16,20,24,28,18,22,26,30,1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31],[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31],[0,4,8,12,16,20,24,28,2,6,10,14,18,22,26,30,1,5,9,13,17,21,25,29,3,7,11,15,19,23,27,31],[0,4,16,20,1,5,17,21,2,6,18,22,3,7,19,23,8,12,24,28,9,13,25,29,10,14,26,30,11,15,27,31],[0,4,16,20,1,5,17,21,8,12,24,28,9,13,25,29,2,6,18,22,3,7,19,23,10,14,26,30,11,15,27,31],[0,4,16,20,2,6,18,22,1,5,17,21,3,7,19,23,8,12,24,28,10,14,26,30,9,13,25,29,11,15,27,31],[0,4,16,20,2,6,18,22,8,12,24,28,10,14,26,30,1,5,17,21,3,7,19,23,9,13,25,29,11,15,27,31],[0,4,16,20,8,12,24,28,1,5,17,21,9,13,25,29,2,6,18,22,10,14,26,30,3,7,19,23,11,15,27,31],[0,4,16,20,8,12,24,28,2,6,18,22,10,14,26,30,1,5,17,21,9,13,25,29,3,7,19,23,11,15,27,31],[0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15,16,24,17,25,18,26,19,27,20,28,21,29,22,30,23,31],[0,8,1,9,2,10,3,11,16,24,17,25,18,26,19,27,4,12,5,13,6,14,7,15,20,28,21,29,22,30,23,31],[0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15,16,24,17,25,20,28,21,29,18,26,19,27,22,30,23,31],[0,8,1,9,4,12,5,13,16,24,17,25,20,28,21,29,2,10,3,11,6,14,7,15,18,26,19,27,22,30,23,31],[0,8,1,9,16,24,17,25,2,10,3,11,18,26,19,27,4,12,5,13,20,28,21,29,6,14,7,15,22,30,23,31],[0,8,1,9,16,24,17,25,4,12,5,13,20,28,21,29,2,10,3,11,18,26,19,27,6,14,7,15,22,30,23,31],[0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15,16,24,18,26,17,25,19,27,20,28,22,30,21,29,23,31],[0,8,2,10,1,9,3,11,16,24,18,26,17,25,19,27,4,12,6,14,5,13,7,15,20,28,22,30,21,29,23,31],[0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15,16,24,18,26,20,28,22,30,17,25,19,27,21,29,23,31],[0,8,2,10,4,12,6,14,16,24,18,26,20,28,22,30,1,9,3,11,5,13,7,15,17,25,19,27,21,29,23,31],[0,8,2,10,16,24,18,26,1,9,3,11,17,25,19,27,4,12,6,14,20,28,22,30,5,13,7,15,21,29,23,31],[0,8,2,10,16,24,18,26,4,12,6,14,20,28,22,30,1,9,3,11,17,25,19,27,5,13,7,15,21,29,23,31],[0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15,16,24,20,28,17,25,21,29,18,26,22,30,19,27,23,31],[0,8,4,12,1,9,5,13,16,24,20,28,17,25,21,29,2,10,6,14,3,11,7,15,18,26,22,30,19,27,23,31],[0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15,16,24,20,28,18,26,22,30,17,25,21,29,19,27,23,31],[0,8,4,12,2,10,6,14,16,24,20,28,18,26,22,30,1,9,5,13,3,11,7,15,17,25,21,29,19,27,23,31],[0,8,4,12,16,24,20,28,1,9,5,13,17,25,21,29,2,10,6,14,18,26,22,30,3,11,7,15,19,27,23,31],[0,8,4,12,16,24,20,28,2,10,6,14,18,26,22,30,1,9,5,13,17,25,21,29,3,11,7,15,19,27,23,31],[0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31],[0,8,16,24,1,9,17,25,4,12,20,28,5,13,21,29,2,10,18,26,3,11,19,27,6,14,22,30,7,15,23,31],[0,8,16,24,2,10,18,26,1,9,17,25,3,11,19,27,4,12,20,28,6,14,22,30,5,13,21,29,7,15,23,31],[0,8,16,24,2,10,18,26,4,12,20,28,6,14,22,30,1,9,17,25,3,11,19,27,5,13,21,29,7,15,23,31],[0,8,16,24,4,12,20,28,1,9,17,25,5,13,21,29,2,10,18,26,6,14,22,30,3,11,19,27,7,15,23,31],[0,8,16,24,4,12,20,28,2,10,18,26,6,14,22,30,1,9,17,25,5,13,21,29,3,11,19,27,7,15,23,31],[0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31],[0,16,1,17,2,18,3,19,8,24,9,25,10,26,11,27,4,20,5,21,6,22,7,23,12,28,13,29,14,30,15,31],[0,16,1,17,4,20,5,21,2,18,3,19,6,22,7,23,8,24,9,25,12,28,13,29,10,26,11,27,14,30,15,31],[0,16,1,17,4,20,5,21,8,24,9,25,12,28,13,29,2,18,3,19,6,22,7,23,10,26,11,27,14,30,15,31],[0,16,1,17,8,24,9,25,2,18,3,19,10,26,11,27,4,20,5,21,12,28,13,29,6,22,7,23,14,30,15,31],[0,16,1,17,8,24,9,25,4,20,5,21,12,28,13,29,2,18,3,19,10,26,11,27,6,22,7,23,14,30,15,31],[0,16,2,18,1,17,3,19,4,20,6,22,5,21,7,23,8,24,10,26,9,25,11,27,12,28,14,30,13,29,15,31],[0,16,2,18,1,17,3,19,8,24,10,26,9,25,11,27,4,20,6,22,5,21,7,23,12,28,14,30,13,29,15,31],[0,16,2,18,4,20,6,22,1,17,3,19,5,21,7,23,8,24,10,26,12,28,14,30,9,25,11,27,13,29,15,31],[0,16,2,18,4,20,6,22,8,24,10,26,12,28,14,30,1,17,3,19,5,21,7,23,9,25,11,27,13,29,15,31],[0,16,2,18,8,24,10,26,1,17,3,19,9,25,11,27,4,20,6,22,12,28,14,30,5,21,7,23,13,29,15,31],[0,16,2,18,8,24,10,26,4,20,6,22,12,28,14,30,1,17,3,19,9,25,11,27,5,21,7,23,13,29,15,31],[0,16,4,20,1,17,5,21,2,18,6,22,3,19,7,23,8,24,12,28,9,25,13,29,10,26,14,30,11,27,15,31],[0,16,4,20,1,17,5,21,8,24,12,28,9,25,13,29,2,18,6,22,3,19,7,23,10,26,14,30,11,27,15,31],[0,16,4,20,2,18,6,22,1,17,5,21,3,19,7,23,8,24,12,28,10,26,14,30,9,25,13,29,11,27,15,31],[0,16,4,20,2,18,6,22,8,24,12,28,10,26,14,30,1,17,5,21,3,19,7,23,9,25,13,29,11,27,15,31],[0,16,4,20,8,24,12,28,1,17,5,21,9,25,13,29,2,18,6,22,10,26,14,30,3,19,7,23,11,27,15,31],[0,16,4,20,8,24,12,28,2,18,6,22,10,26,14,30,1,17,5,21,9,25,13,29,3,19,7,23,11,27,15,31],[0,16,8,24,1,17,9,25,2,18,10,26,3,19,11,27,4,20,12,28,5,21,13,29,6,22,14,30,7,23,15,31],[0,16,8,24,1,17,9,25,4,20,12,28,5,21,13,29,2,18,10,26,3,19,11,27,6,22,14,30,7,23,15,31],[0,16,8,24,2,18,10,26,1,17,9,25,3,19,11,27,4,20,12,28,6,22,14,30,5,21,13,29,7,23,15,31],[0,16,8,24,2,18,10,26,4,20,12,28,6,22,14,30,1,17,9,25,3,19,11,27,5,21,13,29,7,23,15,31],[0,16,8,24,4,20,12,28,1,17,9,25,5,21,13,29,2,18,10,26,6,22,14,30,3,19,11,27,7,23,15,31],[0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23,15,31]]

/-- the closed set of failing search states (1233 states, up to 119 symmetries) -/
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,2863311530,4241289216,4293971136] BT.lf) [3,0,2863311530,4241289216,4293971136] BT.lf) [3,2290649224,3772834016,4261473792,4294901760] (BT.nd BT.lf [3,2290649224,3772834016,4261477888,4278059008] BT.lf)) [3,2290649224,3772834016,4261477888,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [3,2290649224,4007718624,4026593280,4294901760] BT.lf) [3,2290649224,4007718624,4034982016,4294901760] BT.lf) [3,2290649224,4007718624,4169726088,4294901760] (BT.nd BT.lf [3,2829625512,3435187392,4194368000,4294901760] BT.lf))) [3,2829625512,3938511552,4227922944,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4205506560,4293962400] BT.lf) [3,2863311530,4241280204,4293980400,4294967040] BT.lf) [3,2863311530,4241288396,4293984240,4294963200] (BT.nd BT.lf [3,2863311530,4241289216,4293971136] BT.lf)) [3,2863311530,4241289216,4293971136,4293984240] (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,4241289216,4293983472,4294954188] BT.lf) [3,2863311530,4241289216,4293984240,4294954188] BT.lf) [3,2863311530,4241292492,4293971136,4294963200] (BT.nd BT.lf [3,2863311530,4241292492,4293980400,4294953984] BT.lf)))) [3,3937069738,4241292492,4293984240,4294950912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,0,2290649224,3772834016,4261477888,4294901760] BT.lf) [4,0,2290649224,4007718624,4026593280,4294901760] BT.lf) [4,0,2863311530,4241280204,4293980400,4294967040] (BT.nd BT.lf [4,0,2863311530,4241289216,4293984240,4294954188] BT.lf)) [4,65535,267390960,2863311530,3435973836] (BT.nd (BT.nd (BT.nd BT.lf [4,65535,2576980377,4042322160,4278255360] BT.lf) [4,8947848,4008636142,4042322160,4278255360,4294901760] BT.lf) [4,11184810,3435973836,4210094320,4278255360,4294901760] (BT.nd BT.lf [4,16776960,2863311530,3435973836,4042322160] BT.lf))) [4,16776960,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,44739242,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,178956970,214748364,4042322160,4278255360,4294901760] BT.lf) [4,178956970,3435973836,4026593280,4293984240,4294901760] (BT.nd BT.lf [4,178956970,3435973836,4042322160,4278255360,4294901760] BT.lf)) [4,178956970,4042322160,4241280204,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,267452400,2863311530,3435973836,4026593280,4294901760] BT.lf) [4,715827882,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2155905152,3941264106,4244438268,4278255360,4294901760] BT.lf))))) [4,2155905152,3941264106,4244438268,4278255360,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290124928,4008636142,4042322160,4287168392,4294901760] BT.lf) [4,2290649216,4008636138,4042322160,4278255360,4294901760] BT.lf) [4,2290649216,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2290649224,2862656160,3435187392,4026593280,4294901760] BT.lf)) [4,2290649224,2863311530,3772834016,4261477888,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,2863311530,4007718624,4026593280,4294901760] BT.lf) [4,2290649224,3772834016,4008636142,4261477888,4294901760] BT.lf) [4,2290649224,3772834016,4042322160,4261477888,4294901760] (BT.nd BT.lf [4,2290649224,3772834016,4261477888,4278124286,4294901760] BT.lf))) [4,2290649224,3772834016,4261477888,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,3772834016,4261477888,4294901760] BT.lf) [4,2290649224,3772834016,4277075694,4278255360,4294901760] BT.lf) [4,2290649224,3772834016,4277206768,4278255360,4294901760] (BT.nd BT.lf [4,2290649224,3772834016,4278124286,4278255360,4294901760] BT.lf)) [4,2290649224,3873892070,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,3941264106,4243651824,4278255360,4294901760] BT.lf) [4,2290649224,4007715040,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4007718624,4008636142,4026593280,4294901760] (BT.nd BT.lf [4,2290649224,4007718624,4026593280,4294901760] BT.lf)))) [4,2290649224,4007718624,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4007718624,4042322160,4287168392,4294901760] BT.lf) [4,2290649224,4008242920,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4008372970,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2290649224,4008373994,4026593280,4293984240,4294901760] BT.lf)) [4,2290649224,4008373994,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4008636128,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4008636138,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4008636142,4026593280,4293984240,4294901760] (BT.nd BT.lf [4,2290649224,4008636142,4034982016,4293984240,4294901760] BT.lf))) [4,2290649224,4008636142,4041269472,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4008636142,4041273568,4278255360,4293787648] BT.lf) [4,2290649224,4008636142,4041273568,4278255360,4294901760] BT.lf) [4,2290649224,4008636142,4042322048,4278255360,4294901760] (BT.nd BT.lf [4,2290649224,4008636142,4042322080,4278255360,4294901760] BT.lf)) [4,2290649224,4008636142,4042322144,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4008636142,4042322160,4278255360,4294901777] (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4278255360,4294934528] BT.lf)))))) [4,2290649224,4008636142,4042322160,4278255360,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4278255360,4294936704] BT.lf) [4,2290649224,4008636142,4042322160,4278255360,4294942720] BT.lf) [4,2290649224,4008636142,4042322160,4278255360,4294959104] (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4286644096,4294934656] BT.lf)) [4,2290649224,4008636142,4042322160,4287137928,4294967040] (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,4008636142,4042322160,4287168256,4294936712] BT.lf) [4,2290649224,4008636159,4042322160,4278255360,4294901760] BT.lf) [4,2290649224,4042322160,4277071598,4278255360,4294901760] (BT.nd BT.lf [4,2290653593,4008636142,4042322160,4278255360,4294901760] BT.lf))) [4,2290657962,4008627404,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2326440618,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2560137368,4008636142,4042322160,4278255360,4294901760] BT.lf) [4,2576980377,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2576980377,4042322160,4278255360,4294901760] BT.lf)) [4,2827520136,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2827520136,4042322160,4277071598,4278255360,4294901760] BT.lf) [4,2827528328,3435973836,4042322160,4277010432,4278255360] BT.lf) [4,2827528328,3435973836,4205509290,4293984240,4294901760] (BT.nd BT.lf [4,2827528328,4008627404,4042322160,4278255360,4294901760] BT.lf)))) [4,2827528328,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2829625480,4008636142,4042322160,4278255360,4294901760] BT.lf) [4,2829625512,3435187392,4210752250,4278255360,4294901760] BT.lf) [4,2829625512,3435973836,4042322160,4261477376,4294901760] (BT.nd BT.lf [4,2829625512,3435973836,4042322160,4261477888,4278059008] BT.lf)) [4,2829625512,3435973836,4042322160,4261477888,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2829625512,3435973836,4076008178,4278255360,4294901760] BT.lf) [4,2829625512,3435973836,4210094320,4278255360,4294901760] BT.lf) [4,2829625512,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [4,2829625512,3435973836,4210752240,4278255360,4294901760] BT.lf))) [4,2829625512,3938511552,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863179944,3435973836,4042322160,4278254592,4294901760] BT.lf) [4,2863179944,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2863179944,3435973836,4210094320,4278255360,4294901760] (BT.nd BT.lf [4,2863180456,3435711688,4042322160,4278255360,4294901760] BT.lf)) [4,2863180456,3435973824,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863180456,3435973836,4042322160,4278255360,4294705152] BT.lf) [4,2863180456,3435973836,4042322160,4278255360,4294836224] (BT.nd BT.lf [4,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [4,2863180456,3435973836,4042322160,4278255360,4294901763] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863180456,3435973836,4042322160,4278451971,4294901760] BT.lf) [4,2863180456,3435973836,4042322160,4289265408,4294901760] BT.lf) [4,2863180456,3435973836,4042322160,4289396480,4294901760] (BT.nd BT.lf [4,2863180458,3435973836,4042322160,4278255360,4294901760] BT.lf)) [4,2863311528,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901761] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901762] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901763] BT.lf))) [4,2863311530,3435973836,4042322160,4278255360,4294901767] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901888] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294934528] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf)) [4,2863311530,3435973836,4042322160,4278320897,4294902017] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4286611584,4294967040] BT.lf) [4,2863311530,3435973836,4042322160,4286643968,4294934656] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4286644096,4294934656] BT.lf)))) [4,2863311530,3435973836,4042322160,4286644096,4294936576] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4286644096,4294936704] BT.lf) [4,2863311530,3435973836,4042322160,4287137792,4294967040] BT.lf) [4,2863311530,3435973836,4042322160,4287137928,4294967040] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168256,4294936576] BT.lf)) [4,2863311530,3435973836,4042322160,4287168256,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168384,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4289243304,4294967040] BT.lf) [4,2863311530,3435973836,4042322160,4289265408,4294944936] (BT.nd BT.lf [4,2863311530,3435973836,4176541936,4287168392,4294936576] BT.lf))) [4,2863311530,3435973836,4205488810,4293980400,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4205506560,4293984240,4294945450] BT.lf) [4,2863311530,3435973836,4205509290,4293984240,4294942720] BT.lf) [4,2863311530,3435973836,4210094320,4289396480,4294945450] (BT.nd BT.lf [4,2863311530,4241280204,4293980400,4294967040] BT.lf)) [4,2863311530,4241289216,4293984240,4294954188] (BT.nd (BT.nd BT.lf [4,2863311530,4241292492,4293984240,4294954188,4294963200] BT.lf) [5,0,16776960,2863311530,3435973836,4042322160] (BT.nd BT.lf [5,0,16776960,2863311530,3435973836,4042322160,4278190080] BT.lf))))))) [5,0,178956970,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,2155905152,3941264106,4244438268,4278255360,4294901760] BT.lf) [5,0,2290649224,3772834016,4278124286,4278255360,4294901760] BT.lf) [5,0,2290649224,4007718624,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,0,2290649224,4008373994,4042322160,4278255360,4294901760] BT.lf)) [5,0,2290649224,4008636142,4026593280,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,0,2290649224,4008636142,4041273568,4278255360,4294901760] BT.lf) [5,0,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,0,2290649224,4008636142,4042322160,4278255360,4294934656] (BT.nd BT.lf [5,0,2576980377,4008636142,4042322160,4278255360,4294901760] BT.lf))) [5,0,2576980377,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,2827528328,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,0,2829625512,3435973836,4042322160,4261477888,4294901760] BT.lf) [5,0,2829625512,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [5,0,2863179944,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,0,2863180456,3435973836,4042322160,4278255360,4294705152] (BT.nd (BT.nd (BT.nd BT.lf [5,0,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,0,2863311528,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,0,2863311530,3435973836,4042322160,4278255360,4294901763] BT.lf)))) [5,0,2863311530,3435973836,4042322160,4278255360,4294934528] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,0,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf) [5,0,2863311530,3435973836,4042322160,4286644096,4294934656] (BT.nd BT.lf [5,0,2863311530,3435973836,4042322160,4287137928,4294967040] BT.lf)) [5,0,2863311530,3435973836,4042322160,4287168256,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [5,3,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,10,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,15,2863311520,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,15,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf))) [5,15,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,2863311530,3435973839,4042322160,4278255360,4294901760] BT.lf) [5,63,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,136,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,170,2863311360,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,170,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd (BT.nd BT.lf [5,170,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,170,2863311615,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,238,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,255,16777215,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,255,252645135,2863311530,3435973836,4278190080] BT.lf) [5,255,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,255,2852170240,3435973836,4042322160,4289396650,4294901760] (BT.nd BT.lf [5,255,2863311496,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,255,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd BT.lf [5,255,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,255,2863311530,3435973836,4042322160,4278190335] BT.lf) [5,255,2863311530,3435973836,4042322160,4278190335,4294967040] (BT.nd BT.lf [5,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,1023,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2730,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,4095,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,4095,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,16383,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,16383,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,16383,2863311530,3435973836,4042322160,4278255360,4294950912] BT.lf) [5,32896,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,34952,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf)))) [5,34952,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,34952,2863311530,3435982574,4042322160,4278255360,4294901760] BT.lf) [5,43176,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,16711935,2863333375,3435973836,4042322160] (BT.nd BT.lf [5,43690,1431633920,2863267840,3435973836,4042322160,4278255360] BT.lf)) [5,43690,1431633920,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [5,43690,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863267840,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863267840,3435973836,4042322160,4278255360,4294945450] (BT.nd BT.lf [5,43690,2863302792,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,43690,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,43690,2863311530,3435921408,4042322160,4278255360,4294954188] BT.lf) [5,43690,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863329006,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,43690,2863333375,3435973836,4042322160,4278255360] BT.lf)) [5,43690,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,43690,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [5,43775,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,60138,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [5,61166,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61166,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,65278,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,65278,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,65535,16711935,252645135,858993459,2863311530] BT.lf)) [5,65535,16711935,252645135,2863311530,3435973836] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,16711935,2290649224,4008636142,4042322160] BT.lf) [5,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [5,65535,268374015,2863311530,3435973836,4293984240] (BT.nd BT.lf [5,65535,2290649224,4008636142,4042322160,4278255360] BT.lf))) [5,65535,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863180456,3435973836,4042322160,4278255360] BT.lf) [5,65535,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,65535,2863267840,3435973836,4042322160,4278255360,4294945450] (BT.nd BT.lf [5,65535,2863311016,3435973836,4042322160,4278255360] BT.lf)) [5,65535,2863311016,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278059008,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)))) [5,65535,2863311530,3435973836,4042322160,4286644096] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4286644096,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042322160,4287168256] BT.lf) [5,65535,2863311530,3435973836,4042322160,4287168256,4294901760] (BT.nd BT.lf [5,262143,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,262143,2863311530,3435973836,4042322160,4278255360,4294705152] (BT.nd (BT.nd (BT.nd BT.lf [5,262143,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,699050,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,996159,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1048575,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf))) [5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,4144959,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,4194303,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,8947848,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,11184810,2852126720,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,11184810,2852170240,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,11184810,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,11184810,2868903935,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,11184810,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,11206570,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,11206655,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,15658734,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,16776960,16777215,2863311530,3435973836,4042322160] BT.lf)) [5,16776960,16777215,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd BT.lf [5,16776960,2863311530,3435973836,4042322160] BT.lf) [5,16776960,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,16776960,2863311530,3435973836,4042322160,4278190080,4278255360] (BT.nd BT.lf [5,16776960,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf))) [5,16776960,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16776960,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,16776960,2863311530,3435973836,4042322160,4294967040] BT.lf) [5,16777215,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,16777215,2852170240,3435973836,4042322160,4289396650,4294901760] BT.lf)) [5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd (BT.nd BT.lf [5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4294967040] (BT.nd BT.lf [5,16777215,2863311530,3435973836,4210094320,4278255360,4294901760] BT.lf)))) [5,67108863,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,178956970,268435455,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,178956970,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,178956970,3435973836,4026531840,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,178956970,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf)) [5,178956970,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,268435455,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,268435455,2863311530,4042322160,4241280204,4278255360,4294901760] (BT.nd BT.lf [5,1073741823,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2147483648,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2147516416,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2147516416,2863311530,3435973836,4042322160,4278255360,4294934528] (BT.nd BT.lf [5,2147516416,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)) [5,2147516416,2863311530,3435973836,4042322160,4286644096,4294901760] (BT.nd (BT.nd BT.lf [5,2155905024,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2155905152,2290649224,4008636142,4042322160,4278255360,4294934656] BT.lf)))))))) [5,2155905152,2290649224,4008636142,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2155905152,2852170240,3435973836,4042322160,4289396650,4294901760] BT.lf) [5,2155905152,2863311360,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2155905152,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934528] (BT.nd (BT.nd (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936576] BT.lf) [5,2155905152,2863311530,3435973836,4042322160,4286644096,4294934656] (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4176541936,4278255360,4294901760] BT.lf))) [5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4177066232,4278255360,4294934656] BT.lf) [5,2155905152,2863311530,3941264106,4244438268,4278255360,4294901760] BT.lf) [5,2155905152,2863311530,3974950124,4210752250,4278255360,4294901760] (BT.nd BT.lf [5,2155905152,3941264106,4244438268,4278255360,4294901760] BT.lf)) [5,2155907208,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2155915946,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2155937791,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,2155937791,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290122880,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,2290124928,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290124928,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290124928,2863311530,3435973836,4042322160,4278255360,4294936704] (BT.nd BT.lf [5,2290124928,2863311530,3435973836,4042322160,4286644096,4294901760] BT.lf)) [5,2290124928,2863311530,3435973836,4042322160,4287168392,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290124928,2863311530,4008505068,4042322160,4278255360,4294901760] BT.lf) [5,2290649216,2863311520,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649216,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf))) [5,2290649224,2290679807,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2576980377,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2576980377,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2694881440,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760] BT.lf)) [5,2290649224,2694881440,3974950124,4210752250,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2728567458,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2829625512,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2862653600,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,2290649224,2862656160,3435187392,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2862656160,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2862656160,3435973836,4042322160,4287168392,4294901760] (BT.nd BT.lf [5,2290649224,2862656160,4008505068,4042322160,4278255360,4294901760] BT.lf)) [5,2290649224,2862656160,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311520,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4034982016,4293984240,4294901760] BT.lf))) [5,2290649224,2863311530,3435973836,4041273568,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322048,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4042322080,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934528] BT.lf)) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294942720] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4286644096,4294934656] BT.lf)))) [5,2290649224,2863311530,3435973836,4042322160,4287137928,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4287168256,4294936712] BT.lf) [5,2290649224,2863311530,3435973887,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435982574,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,3772834016,4244438268,4278255360,4294901760] BT.lf)) [5,2290649224,2863311530,3772834016,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3972852940,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,4007718624,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,4008373994,4042322160,4278255360,4294901760] BT.lf))) [5,2290649224,2863311530,4008505068,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,4008636142,4026593280,4293984240,4294901760] BT.lf) [5,2290649224,2863311530,4008636142,4041273568,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294934656] BT.lf)) [5,2290649224,2863311530,4042322160,4241280204,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863333375,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,3149642683,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,3772834016,3993038336,4042322160,4278255360,4294901760] BT.lf)))))) [5,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,3772834016,4008636142,4177066232,4278255360,4294901760] BT.lf) [5,2290649224,3772834016,4008636142,4210752250,4278255360,4294901760] BT.lf) [5,2290649224,3772834016,4008636142,4278124286,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,3772834016,4042322160,4278124286,4278255360,4294901760] BT.lf)) [5,2290649224,3772834016,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,3907578088,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,3941264106,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,3941264106,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4007718624,4008636142,4042322160,4278255360,4294901760] BT.lf))) [5,2290649224,4007718624,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4007718624,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,4008373994,4042322160,4278255360,4293984240,4294901760] BT.lf) [5,2290649224,4008373994,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf)) [5,2290649224,4008636142,4008640511,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4026593280,4293984240,4294901760] BT.lf) [5,2290649224,4008636142,4034982016,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4037079200,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4041273568,4042322160,4278255360,4294901760] BT.lf)))) [5,2290649224,4008636142,4041273568,4278255360,4293853166,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4041273568,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042321920,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4042326015,4278255360,4294901760] BT.lf)) [5,2290649224,4008636142,4042322160,4059165169,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4092851187,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4160223223,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4169726088,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4176541936,4278255360,4294901760] BT.lf))) [5,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4205509290,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4210096880,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4277075694,4278255360,4294901760] BT.lf)) [5,2290649224,4008636142,4042322160,4277206768,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4278255360,4293980400,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf))))) [5,2290649224,4008636142,4042322160,4278255360,4294508536,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294639610,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4278255360,4294901758,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294901760,4294967280] BT.lf)) [5,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294934656] BT.lf) [5,2290649224,4008636142,4042322160,4278255360,4294936712,4294963440] BT.lf) [5,2290649258,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649343,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2290657448,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290657962,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290657962,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290657962,3435973836,4008640511,4042322160,4278255360,4294901760] BT.lf)) [5,2290662331,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290678008,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2292886186,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,2298478591,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2576980377,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2576980377,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2576980377,2863311530,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2576980377,4008636142,4042322160,4278255360,4294901760] BT.lf)) [5,2576980377,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2827520136,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2827520136,2863311530,4042322160,4241280204,4278255360,4294901760] BT.lf) [5,2827526144,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2827528328,2863311530,3972852940,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2827528328,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2827528328,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2827528328,3435973836,4042322160,4205509290,4278255360,4294901760] (BT.nd BT.lf [5,2827528328,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf)) [5,2827528328,4008636142,4042322160,4241292492,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2827528328,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2829625344,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2829625480,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))) [5,2829625512,2861083272,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,2863311360,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,2863311530,3435187392,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4042322160,4261477888,4294901760] BT.lf)) [5,2829625512,2863311530,3435973836,4042322160,4278254592,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294944768] BT.lf) [5,2829625512,2863311530,3435973836,4176541936,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4210096880,4278255360,4294901760] BT.lf))) [5,2829625512,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,3435973836,4004179626,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,3435973836,4006407884,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [5,2829625512,3435973836,4042322160,4244438268,4261477888,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,3435973836,4042322160,4261477888,4278124286,4294901760] BT.lf) [5,2829625512,3435973836,4042322160,4261477888,4278255360,4294901760] BT.lf) [5,2829625512,3435973836,4042322160,4261477888,4294901760] (BT.nd BT.lf [5,2829625512,3435973836,4042322160,4272619178,4278255360,4294901760] BT.lf)))) [5,2829625512,3435973836,4042322160,4277993212,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [5,2829625512,3435973836,4210096880,4244438268,4278255360,4294901760] BT.lf) [5,2829625512,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,3435973836,4210752250,4278255360,4293984240,4294901760] BT.lf)) [5,2829626026,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2829647100,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2829647871,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863179944,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863179944,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))) [5,2863179944,3435973836,4042322160,4278255360,4291611852,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863179944,3435973836,4042322160,4278255360,4294769916,4294901760] BT.lf) [5,2863179944,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863180456,2863180456,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863180456,2863311530,3435973836,4042322160,4278255360,4294705152] BT.lf)) [5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863180456,3435973836,3974950124,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863180456,3435973836,4008505068,4042322160,4278255360,4294901760] BT.lf))))) [5,2863180456,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4244438268,4278255360,4294705152] BT.lf) [5,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [5,2863180456,3435973836,4042322160,4277993212,4278255360,4294901760] (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf)) [5,2863180456,3435973836,4042322160,4278255360,4294705152] (BT.nd (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4294705152,4294770684] BT.lf) [5,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf) [5,2863180456,3435973836,4042322160,4278255360,4294901758,4294901760] (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294945448] BT.lf) [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf) [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294954188] (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294966524] BT.lf)) [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294967292] (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [5,2863311528,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311528,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)))) [5,2863311528,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311528,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311528,3435973836,4042322160,4278255360,4294901760,4294967292] BT.lf) [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)) [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294950912] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,2863311535,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311598,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2863312895,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,2863320268,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,2863327978,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863333118,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,2863661055,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,2867785454,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2952790015,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [5,2863311530,3435973836,3907578088,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3937053354,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3937058816,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3937069738,4042322160,4278255360,4294950912] BT.lf)) [5,2863311530,3435973836,3937069738,4042322160,4290838464,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3938511552,4042322160,4289396650,4294901760] BT.lf) [5,2863311530,3435973836,3939035848,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3941263872,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,3941264042,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3941264064,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294934656] (BT.nd BT.lf [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294950912] BT.lf)) [5,2863311530,3435973836,3941264106,4243651824,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3941265134,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941269503,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4008372970,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636128,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008636138,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901777] BT.lf)) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294934656] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294942720] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294959104] BT.lf) [5,2863311530,3435973836,4008636159,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4008640254,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4009754623,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4277071598,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4277074602,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4278124202,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278124270,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278124286,4278255360,4294902017] BT.lf))))) [5,2863311530,3435973836,4042322160,4278124543,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901502,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967294] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901763] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901775,4294963440] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901775,4294967280] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901930,4294967040] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4294902015,4294945280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294905855,4294963200] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294934528] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294934656] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294936712] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294945450] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967040] BT.lf)))) [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967168] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967295] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294942880] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963200] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294967280] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294944936,4294967040] BT.lf) [5,2863311530,3435973836,4042322160,4278255615,4294902015] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255615,4294902015,4294967040] BT.lf))) [5,2863311530,3435973836,4042322160,4286644096,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4287137928,4294967040] BT.lf) [5,2863311530,3435973836,4042322160,4287168256,4294936712] BT.lf) [5,2863311530,3435973836,4042322160,4287168392,4294936712,4294967040] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4289374890,4291611852,4294967040] BT.lf)) [6,0,0,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,0,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,15,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,170,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))))) [6,0,255,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,255,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [6,0,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,4095,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,34952,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,0,43690,2863267840,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,43690,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,43690,2863333375,3435973836,4042322160,4278255360] BT.lf) [6,0,43690,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,61166,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,0,65535,16711935,252645135,2863311530,3435973836] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [6,0,65535,2290649224,4008636142,4042322160,4278255360] BT.lf) [6,0,65535,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,65535,2863267840,3435973836,4042322160,4278255360,4294945450] BT.lf)) [6,0,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,1048575,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,11184810,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,16777215,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf)))) [6,0,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,16777215,2863311530,3435973836,4042322160,4294967040] BT.lf) [6,0,268435455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [6,0,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf) [6,0,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf))) [6,0,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [6,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)) [6,0,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,0,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,0,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf))))) [6,0,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760] BT.lf) [6,0,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,0,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [6,0,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf)) [6,0,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,0,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,0,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,0,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,0,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)) [6,0,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,0,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf)) [6,0,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf))) [6,0,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760] BT.lf) [6,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [6,0,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] BT.lf)) [6,0,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd (BT.nd BT.lf [6,0,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] BT.lf) [6,15,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [6,15,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [6,15,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,170,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,170,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,170,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [6,255,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,255,65535,16711935,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd BT.lf [6,255,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,255,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,255,252645135,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,255,252645135,2863311530,3435973836,4278255360,4294901760] BT.lf))) [6,255,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,255,2863311360,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,255,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,255,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,255,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278190080] BT.lf) [6,255,2863311530,3435973836,4042322160,4278190080,4278255360] BT.lf) [6,255,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040] BT.lf)))) [6,255,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4278255615,4294901760] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd (BT.nd (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967210] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4294902015] (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] BT.lf))) [6,4095,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,4095,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,4095,2863311530,3435973836,4042322160,4278255360,4294901760,4294963200] BT.lf) [6,34952,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,34952,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [6,34952,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,34952,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,34952,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,43690,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,43690,52428,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [6,43690,65535,1431655765,3435973836,4042322160,4278255360] BT.lf) [6,43690,65535,2863267840,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,43690,65535,2863267840,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,43690,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,43690,65535,2863333375,3435973836,4042322160,4278255360] BT.lf) [6,43690,65535,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,43690,16711935,2863311530,3435973836,4042322160,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,43690,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,43690,1431699455,2863267840,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,43690,1431699455,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,43690,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,43690,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,2863267840,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,43690,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,2863311530,2863333375,3435973836,4042322160,4278255360] BT.lf) [6,43690,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,43690,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,43690,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,43690,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760] BT.lf) [6,43690,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [6,43690,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))) [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] BT.lf) [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294923605] BT.lf) [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd BT.lf [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188] BT.lf)) [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd BT.lf [6,43690,2863311530,3435973836,4042322160,4278255360,4294945450] BT.lf) [6,43690,2863333375,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,43690,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf))))))) [6,61166,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61166,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,61166,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,61166,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,65535,16711935,2863311530,3435973836,4042322160] BT.lf)) [6,65535,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,16711935,16777215,2863311530,3435973836,4042322160] BT.lf) [6,65535,16711935,252645135,2863311530,3435973836] (BT.nd BT.lf [6,65535,16711935,252645135,2863311530,3435973836,4042322160] BT.lf))) [6,65535,16711935,2290649224,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,16711935,2852170240,2863311530,3435973836,4042322160] BT.lf) [6,65535,16711935,2863311530,2863311530,3435973836,4042322160] BT.lf) [6,65535,16711935,2863311530,2863333375,3435973836,4042322160] (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4008636142,4042322160] BT.lf)) [6,65535,16711935,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160,4278190080] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160,4278255615] BT.lf)))) [6,65535,16711935,2863311530,3435973836,4042322160,4289396650] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160,4294967040] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160,4294967295] BT.lf) [6,65535,16777215,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,268374015,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,268374015,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2155905152,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,2290614272,2863311530,3435973836,4042322160,4278255360] BT.lf))) [6,65535,2290614272,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2290649224,2863311530,4008636142,4042322160,4278255360] (BT.nd BT.lf [6,65535,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2290649224,4008636142,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,65535,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,65535,2290657962,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,65535,2290679807,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2829625512,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360] BT.lf)) [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294945450] BT.lf) [6,65535,2863267840,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf) [6,65535,2863267840,3435973836,4042322160,4278255360,4294945450] (BT.nd BT.lf [6,65535,2863302792,2863311530,3435973836,4042322160,4278255360] BT.lf))) [6,65535,2863302792,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,2863329006,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,2868882175,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,2868882175,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,65535,2863311530,3435973836,3941264106,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4008574976,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4008574976,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,2863311530,3435973836,4008618666,4042322160,4278255360] BT.lf)) [6,65535,2863311530,3435973836,4008618666,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4008640511,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] BT.lf))) [6,65535,2863311530,3435973836,4042322160,4278124286,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] BT.lf)) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294902015] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294936712] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294962926] BT.lf)))))) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294902015] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294945450] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294962926] BT.lf)) [6,65535,2863311530,3435973836,4042322160,4278255360,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255615,4294901760,4294967040] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255615,4294967040] BT.lf) [6,1048575,2863311530,3435973836,4042322160,4278255360,4293918720,4294901760] (BT.nd BT.lf [6,1048575,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf))) [6,1048575,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,11184810,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,11184810,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [6,11184810,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,16777215,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,16777215,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,16777215,2852126720,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,16777215,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,16777215,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,16777215,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,16777215,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf)) [6,16777215,2863311530,3435973836,4042322160,4278255360,4289374890,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf))) [6,16777215,2863311530,3435973836,4042322160,4278255360,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4294967040] BT.lf) [6,268435455,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760] BT.lf) [6,268435455,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,268435455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2147516416,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2147516416,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2155905152,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,2155905152,2281736192,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [6,2155905152,2290649224,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd BT.lf [6,2155905152,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2155905152,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf))) [6,2155905152,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf) [6,2155905152,2863311530,3435973836,4042322160,4278255360,4286644096,4294901760] BT.lf) [6,2155905152,2863311530,3435973836,4042322160,4278255360,4287168392,4294901760] (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] BT.lf)) [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf) [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)))) [6,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290124928,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290124928,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290124928,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [6,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2694881440,2852170240,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2694881440,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf) [6,2290649224,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760] BT.lf) [6,2290649224,2694881440,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760] BT.lf)) [6,2290649224,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2862656160,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [6,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760] BT.lf)))))))) [6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3149642683,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760] BT.lf))) [6,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4034982016,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4160223223,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4169726088,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4176541936,4278255360,4294901760] BT.lf)))) [6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294508536,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] (BT.nd BT.lf [6,2290649224,2863311530,3772834016,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,4008636142,4042322160,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,4008636142,4042322160,4177066232,4278255360,4294901760] BT.lf))))) [6,2290649224,2863311530,4008636142,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,4008636142,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,4008636142,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,4008636142,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760] BT.lf))) [6,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295] BT.lf)) [6,2290657962,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2827528328,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] BT.lf)))) [6,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2829625512,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2829625512,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2829625512,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] BT.lf)) [6,2829625512,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4227922944,4278255360,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf))) [6,2829625512,2863311530,3435973836,4042322160,4278255360,4289265576,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,4042322160,4278255360,4291624908,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,2829625512,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [6,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)))))) [6,2829625512,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,2863180456,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863180456,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd BT.lf [6,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2863180456,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf) [6,2863180456,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf)))) [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf)) [6,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863333375,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863333375,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863333375,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863333375,3435973836,4008640511,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,2863333375,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf) [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294954188] (BT.nd BT.lf [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf)) [6,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,3941264106,3941264106,4042322160,4278255360,4294901760] BT.lf))))) [6,2863311530,3435973836,3941264106,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3941264106,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4289396650,4294901760] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4290838464,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,3941264106,4042322160,4278255360,4291624908,4294901760] BT.lf)) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4293591018,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [6,2863311530,3435973836,4007718624,4008636142,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008373994,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4008640511,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4277075694,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf)))) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294639610,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901758,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967280] (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295] BT.lf)) [6,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278124286,4278124286,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278124286,4278255360,4293853166,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901758,4294901760] BT.lf))) [6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760,4294967295] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf)) [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] BT.lf))))))) [6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188,4294963440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,0,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,0,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,0,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [7,0,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,0,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [7,0,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [7,0,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,0,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,43690,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,0,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,65535,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [7,0,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,0,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [7,0,65535,16711935,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,0,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,65535,2290649224,2863311530,3435973836,4042322160,4278255360] BT.lf)))) [7,0,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,65535,2863267840,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,0,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,65535,2863311530,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [7,0,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [7,0,65535,2863311530,2863333375,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [7,0,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,65535,2863311530,3435973836,4008636142,4042322160,4278255360] BT.lf) [7,0,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,65535,2863311530,3435973836,4042322160,4278255360] BT.lf))) [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] BT.lf) [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf) [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294945450] BT.lf)) [7,0,65535,2863311530,3435973836,4042322160,4278255360,4294967295] (BT.nd (BT.nd BT.lf [7,0,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [7,0,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [7,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [7,0,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,0,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [7,0,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] BT.lf) [7,0,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] (BT.nd BT.lf [7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf))) [7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [7,0,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [7,0,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)) [7,0,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,0,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)))) [7,0,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [7,0,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,0,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf)) [7,0,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,0,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760] BT.lf) [7,0,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760] BT.lf) [7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf))) [7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,0,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [7,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [7,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295] BT.lf)) [7,255,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf) [7,43690,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [7,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [7,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,65535,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,65535,16711935,2863311530,3435973836,4042322160] (BT.nd BT.lf [7,65535,16711935,2863311530,3435973836,4042322160,4278255360] BT.lf)) [7,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,65535,2290649224,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,65535,2863267840,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [7,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,65535,2863311530,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,65535,2863311530,2863333375,3435973836,4042322160,4278255360] BT.lf) [7,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,65535,2863311530,3435973836,4008636142,4042322160,4278255360] BT.lf)) [7,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] (BT.nd BT.lf [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf)))) [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,65535,2863311530,3435973836,4042322160,4278255360,4294945450] BT.lf) [7,65535,2863311530,3435973836,4042322160,4278255360,4294967295] BT.lf) [7,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd BT.lf [7,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [7,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] (BT.nd BT.lf [7,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)) [7,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [7,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf))))) [7,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [7,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [7,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd BT.lf [7,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [7,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf)) [7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295] BT.lf) [7,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [7,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295] BT.lf) [8,0,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,0,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [8,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [8,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [8,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [8,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [8,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf))) [8,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [8,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [8,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [8,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [8,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [9,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [9,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,2863311530,4241289216,4293971136],[]),([3,0,2863311530,4241289216,4293971136],[]),([3,2290649224,3772834016,4261473792,4294901760],[]),([3,2290649224,3772834016,4261477888,4278059008],[]),([3,2290649224,3772834016,4261477888,4294901760],[]),([3,2290649224,4007718624,4026593280,4294901760],[(72,98)]),([3,2290649224,4007718624,4034982016,4294901760],[(72,98)]),([3,2290649224,4007718624,4169726088,4294901760],[(72,98)]),([3,2829625512,3435187392,4194368000,4294901760],[]),([3,2829625512,3938511552,4227922944,4294901760],[(72,95)]),([3,2863311530,3435973836,4205506560,4293962400],[]),([3,2863311530,4241280204,4293980400,4294967040],[]),([3,2863311530,4241288396,4293984240,4294963200],[]),([3,2863311530,4241289216,4293971136],[]),([3,2863311530,4241289216,4293971136,4293984240],[]),([3,2863311530,4241289216,4293983472,4294954188],[]),([3,2863311530,4241289216,4293984240,4294954188],[]),([3,2863311530,4241292492,4293971136,4294963200],[]),([3,2863311530,4241292492,4293980400,4294953984],[]),([3,3937069738,4241292492,4293984240,4294950912],[]),([4,0,2290649224,3772834016,4261477888,4294901760],[]),([4,0,2290649224,4007718624,4026593280,4294901760],[(104,98)]),([4,0,2863311530,4241280204,4293980400,4294967040],[]),([4,0,2863311530,4241289216,4293984240,4294954188],[]),([4,65535,267390960,2863311530,3435973836],[]),([4,65535,2576980377,4042322160,4278255360],[]),([4,8947848,4008636142,4042322160,4278255360,4294901760],[]),([4,11184810,3435973836,4210094320,4278255360,4294901760],[]),([4,16776960,2863311530,3435973836,4042322160],[]),([4,16776960,2863311530,3435973836,4042322160,4278190080],[]),([4,44739242,3435973836,4042322160,4278255360,4294901760],[]),([4,178956970,214748364,4042322160,4278255360,4294901760],[]),([4,178956970,3435973836,4026593280,4293984240,4294901760],[]),([4,178956970,3435973836,4042322160,4278255360,4294901760],[]),([4,178956970,4042322160,4241280204,4278255360,4294901760],[]),([4,267452400,2863311530,3435973836,4026593280,4294901760],[]),([4,715827882,3435973836,4042322160,4278255360,4294901760],[]),([4,2155905152,3941264106,4244438268,4278255360,4294901760],[(96,113),(128,89)]),([4,2155905152,3941264106,4244438268,4278255360,4294934656],[(56,89),(72,89),(96,71),(128,89)]),([4,2290124928,4008636142,4042322160,4287168392,4294901760],[(72,111),(128,65)]),([4,2290649216,4008636138,4042322160,4278255360,4294901760],[]),([4,2290649216,4008636142,4042322160,4278255360,4294901760],[]),([4,2290649224,2862656160,3435187392,4026593280,4294901760],[(56,61),(72,59),(96,7)]),([4,2290649224,2863311530,3772834016,4261477888,4294901760],[]),([4,2290649224,2863311530,4007718624,4026593280,4294901760],[(96,20)]),([4,2290649224,3772834016,4008636142,4261477888,4294901760],[]),([4,2290649224,3772834016,4042322160,4261477888,4294901760],[]),([4,2290649224,3772834016,4261477888,4278124286,4294901760],[]),([4,2290649224,3772834016,4261477888,4278255360,4294901760],[]),([4,2290649224,3772834016,4261477888,4294901760],[]),([4,2290649224,3772834016,4277075694,4278255360,4294901760],[(148,0)]),([4,2290649224,3772834016,4277206768,4278255360,4294901760],[]),([4,2290649224,3772834016,4278124286,4278255360,4294901760],[(148,0)]),([4,2290649224,3873892070,4042322160,4278255360,4294901760],[]),([4,2290649224,3941264106,4243651824,4278255360,4294901760],[(96,97)]),([4,2290649224,4007715040,4042322160,4278255360,4294901760],[]),([4,2290649224,4007718624,4008636142,4026593280,4294901760],[(96,107)]),([4,2290649224,4007718624,4026593280,4294901760],[(72,98),(73,59)]),([4,2290649224,4007718624,4042322160,4278255360,4294901760],[]),([4,2290649224,4007718624,4042322160,4287168392,4294901760],[(72,107)]),([4,2290649224,4008242920,4042322160,4278255360,4294901760],[]),([4,2290649224,4008372970,4042322160,4278255360,4294901760],[]),([4,2290649224,4008373994,4026593280,4293984240,4294901760],[(72,107)]),([4,2290649224,4008373994,4042322160,4278255360,4294901760],[]),([4,2290649224,4008636128,4042322160,4278255360,4294901760],[]),([4,2290649224,4008636138,4042322160,4278255360,4294901760],[]),([4,2290649224,4008636142,4026593280,4293984240,4294901760],[(72,98)]),([4,2290649224,4008636142,4034982016,4293984240,4294901760],[(72,98)]),([4,2290649224,4008636142,4041269472,4278255360,4294901760],[(108,1),(140,3)]),([4,2290649224,4008636142,4041273568,4278255360,4293787648],[(108,1)]),([4,2290649224,4008636142,4041273568,4278255360,4294901760],[(108,1)]),([4,2290649224,4008636142,4042322048,4278255360,4294901760],[]),([4,2290649224,4008636142,4042322080,4278255360,4294901760],[]),([4,2290649224,4008636142,4042322144,4278255360,4294901760],[]),([4,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([4,2290649224,4008636142,4042322160,4278255360,4294901777],[]),([4,2290649224,4008636142,4042322160,4278255360,4294934528],[]),([4,2290649224,4008636142,4042322160,4278255360,4294934656],[(72,93)])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,2290649224,4008636142,4042322160,4278255360,4294936704],[(72,89),(96,65)]),([4,2290649224,4008636142,4042322160,4278255360,4294942720],[]),([4,2290649224,4008636142,4042322160,4278255360,4294959104],[]),([4,2290649224,4008636142,4042322160,4286644096,4294934656],[(72,83)]),([4,2290649224,4008636142,4042322160,4287137928,4294967040],[(56,50),(96,50),(140,2)]),([4,2290649224,4008636142,4042322160,4287168256,4294936712],[(56,63),(128,63)]),([4,2290649224,4008636159,4042322160,4278255360,4294901760],[]),([4,2290649224,4042322160,4277071598,4278255360,4294901760],[]),([4,2290653593,4008636142,4042322160,4278255360,4294901760],[]),([4,2290657962,4008627404,4042322160,4278255360,4294901760],[]),([4,2326440618,3435973836,4042322160,4278255360,4294901760],[]),([4,2560137368,4008636142,4042322160,4278255360,4294901760],[]),([4,2576980377,4008636142,4042322160,4278255360,4294901760],[]),([4,2576980377,4042322160,4278255360,4294901760],[]),([4,2827520136,4008636142,4042322160,4278255360,4294901760],[]),([4,2827520136,4042322160,4277071598,4278255360,4294901760],[]),([4,2827528328,3435973836,4042322160,4277010432,4278255360],[]),([4,2827528328,3435973836,4205509290,4293984240,4294901760],[(56,101)]),([4,2827528328,4008627404,4042322160,4278255360,4294901760],[]),([4,2827528328,4008636142,4042322160,4278255360,4294901760],[]),([4,2829625480,4008636142,4042322160,4278255360,4294901760],[]),([4,2829625512,3435187392,4210752250,4278255360,4294901760],[]),([4,2829625512,3435973836,4042322160,4261477376,4294901760],[(84,29)]),([4,2829625512,3435973836,4042322160,4261477888,4278059008],[(84,29)]),([4,2829625512,3435973836,4042322160,4261477888,4294901760],[(84,29)]),([4,2829625512,3435973836,4076008178,4278255360,4294901760],[]),([4,2829625512,3435973836,4210094320,4278255360,4294901760],[]),([4,2829625512,3435973836,4210096880,4278255360,4294901760],[]),([4,2829625512,3435973836,4210752240,4278255360,4294901760],[]),([4,2829625512,3938511552,4244438268,4278255360,4294901760],[(96,105)]),([4,2863179944,3435973836,4042322160,4278254592,4294901760],[]),([4,2863179944,3435973836,4042322160,4278255360,4294901760],[]),([4,2863179944,3435973836,4210094320,4278255360,4294901760],[]),([4,2863180456,3435711688,4042322160,4278255360,4294901760],[]),([4,2863180456,3435973824,4042322160,4278255360,4294901760],[]),([4,2863180456,3435973836,4042322160,4278255360,4294705152],[]),([4,2863180456,3435973836,4042322160,4278255360,4294836224],[]),([4,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([4,2863180456,3435973836,4042322160,4278255360,4294901763],[]),([4,2863180456,3435973836,4042322160,4278451971,4294901760],[]),([4,2863180456,3435973836,4042322160,4289265408,4294901760],[]),([4,2863180456,3435973836,4042322160,4289396480,4294901760],[]),([4,2863180458,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311528,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901761],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901762],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901763],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901767],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901888],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936704],[]),([4,2863311530,3435973836,4042322160,4278320897,4294902017],[]),([4,2863311530,3435973836,4042322160,4286611584,4294967040],[]),([4,2863311530,3435973836,4042322160,4286643968,4294934656],[]),([4,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([4,2863311530,3435973836,4042322160,4286644096,4294936576],[]),([4,2863311530,3435973836,4042322160,4286644096,4294936704],[]),([4,2863311530,3435973836,4042322160,4287137792,4294967040],[]),([4,2863311530,3435973836,4042322160,4287137928,4294967040],[(56,50)]),([4,2863311530,3435973836,4042322160,4287168256,4294936576],[]),([4,2863311530,3435973836,4042322160,4287168256,4294936712],[(56,63)]),([4,2863311530,3435973836,4042322160,4287168384,4294936712],[(56,59)]),([4,2863311530,3435973836,4042322160,4289243304,4294967040],[]),([4,2863311530,3435973836,4042322160,4289265408,4294944936],[]),([4,2863311530,3435973836,4176541936,4287168392,4294936576],[(56,59)]),([4,2863311530,3435973836,4205488810,4293980400,4294967040],[(72,23)]),([4,2863311530,3435973836,4205506560,4293984240,4294945450],[(128,23)]),([4,2863311530,3435973836,4205509290,4293984240,4294942720],[(72,41)]),([4,2863311530,3435973836,4210094320,4289396480,4294945450],[(128,31)])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,4241280204,4293980400,4294967040],[]),([4,2863311530,4241289216,4293984240,4294954188],[(117,6)]),([4,2863311530,4241292492,4293984240,4294954188,4294963200],[(108,3),(156,17)]),([5,0,16776960,2863311530,3435973836,4042322160],[]),([5,0,16776960,2863311530,3435973836,4042322160,4278190080],[]),([5,0,178956970,3435973836,4042322160,4278255360,4294901760],[]),([5,0,2155905152,3941264106,4244438268,4278255360,4294901760],[(136,113),(176,89)]),([5,0,2290649224,3772834016,4278124286,4278255360,4294901760],[(196,0)]),([5,0,2290649224,4007718624,4042322160,4278255360,4294901760],[]),([5,0,2290649224,4008373994,4042322160,4278255360,4294901760],[]),([5,0,2290649224,4008636142,4026593280,4293984240,4294901760],[(104,98)]),([5,0,2290649224,4008636142,4041273568,4278255360,4294901760],[(148,1)]),([5,0,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,0,2290649224,4008636142,4042322160,4278255360,4294934656],[(104,93)]),([5,0,2576980377,4008636142,4042322160,4278255360,4294901760],[]),([5,0,2576980377,4042322160,4278255360,4294901760],[]),([5,0,2827528328,4008636142,4042322160,4278255360,4294901760],[]),([5,0,2829625512,3435973836,4042322160,4261477888,4294901760],[(116,29)]),([5,0,2829625512,3435973836,4210096880,4278255360,4294901760],[]),([5,0,2863179944,3435973836,4042322160,4278255360,4294901760],[]),([5,0,2863180456,3435973836,4042322160,4278255360,4294705152],[]),([5,0,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([5,0,2863311528,3435973836,4042322160,4278255360,4294901760],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294901763],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294936704],[]),([5,0,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([5,0,2863311530,3435973836,4042322160,4287137928,4294967040],[(80,50)]),([5,0,2863311530,3435973836,4042322160,4287168256,4294936712],[(80,63)]),([5,3,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,32),(72,8),(96,2),(128,0)]),([5,10,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8)]),([5,15,2863311520,3435973836,4042322160,4278255360,4294901760],[(56,32),(72,8),(96,16),(128,10),(168,8)]),([5,15,2863311530,3435973836,4026593280,4293984240,4294901760],[(56,62),(72,60),(96,59)]),([5,15,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,32),(72,8)]),([5,15,2863311530,3435973839,4042322160,4278255360,4294901760],[(56,63),(72,8)]),([5,63,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,32)])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([5,136,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,170,2863311360,3435973836,4042322160,4278255360,4294901760],[(128,21),(168,15)]),([5,170,2863311530,3435973836,4042322160,4278190080,4294967040],[(56,89),(128,89)]),([5,170,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,170,2863311615,3435973836,4042322160,4278255360,4294901760],[]),([5,238,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,255,16777215,2863311530,3435973836,4042322160],[]),([5,255,252645135,2863311530,3435973836,4278190080],[(128,89)]),([5,255,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,255,2852170240,3435973836,4042322160,4289396650,4294901760],[]),([5,255,2863311496,3435973836,4042322160,4278255360,4294901760],[(72,15)]),([5,255,2863311530,3435973836,4042322160,4278190080],[(2,89),(128,89)]),([5,255,2863311530,3435973836,4042322160,4278190080,4294967040],[(128,89)]),([5,255,2863311530,3435973836,4042322160,4278190335],[(2,89),(128,89)]),([5,255,2863311530,3435973836,4042322160,4278190335,4294967040],[(128,89)]),([5,255,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1023,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2730,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,4095,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,4095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16383,2863311530,3435973836,4042322160,4278255360],[(2,31)]),([5,16383,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16383,2863311530,3435973836,4042322160,4278255360,4294950912],[]),([5,32896,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,34952,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,34952,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,34952,2863311530,3435982574,4042322160,4278255360,4294901760],[]),([5,43176,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,16711935,2863333375,3435973836,4042322160],[]),([5,43690,1431633920,2863267840,3435973836,4042322160,4278255360],[(56,31)]),([5,43690,1431633920,3435973836,4042322160,4278255360],[(56,31)]),([5,43690,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,43690,2863267840,3435973836,4042322160,4278255360,4294901760],[(168,17)])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([5,43690,2863267840,3435973836,4042322160,4278255360,4294945450],[(168,17)]),([5,43690,2863302792,3435973836,4042322160,4278255360,4294901760],[(72,17)]),([5,43690,2863311530,3233857728,4244438268,4278255360,4294901760],[(56,29)]),([5,43690,2863311530,3435921408,4042322160,4278255360,4294954188],[(56,41)]),([5,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863333375,3435973836,4042322160,4278255360],[]),([5,43690,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([5,43775,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,60138,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,61166,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,61166,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65278,2863311530,3435973836,4042322160,4278255360],[(2,71)]),([5,65278,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,16711935,252645135,858993459,2863311530],[]),([5,65535,16711935,252645135,2863311530,3435973836],[]),([5,65535,16711935,2290649224,4008636142,4042322160],[]),([5,65535,16711935,2863311530,3435973836,4042322160],[]),([5,65535,268374015,2863311530,3435973836,4293984240],[]),([5,65535,2290649224,4008636142,4042322160,4278255360],[]),([5,65535,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,65535,2863180456,3435973836,4042322160,4278255360],[]),([5,65535,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,2863267840,3435973836,4042322160,4278255360,4294945450],[]),([5,65535,2863311016,3435973836,4042322160,4278255360],[(2,0)]),([5,65535,2863311016,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4278059008,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278255360],[])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,65535,2863311530,3435973836,4042322160,4286644096],[(2,0)]),([5,65535,2863311530,3435973836,4042322160,4286644096,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4287168256],[(2,3)]),([5,65535,2863311530,3435973836,4042322160,4287168256,4294901760],[]),([5,262143,2863311530,3435973836,4042322160,4278255360],[(2,104)]),([5,262143,2863311530,3435973836,4042322160,4278255360,4294705152],[]),([5,262143,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,699050,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,996159,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1048575,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,4144959,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,4194303,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,8947848,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,11184810,2852126720,3435973836,4042322160,4278255360,4294901760],[(80,5)]),([5,11184810,2852170240,3435973836,4042322160,4278255360,4294901760],[(128,11)]),([5,11184810,2863311530,3435973836,4042322160,4278190080,4294967040],[(56,89)]),([5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,11184810,2868903935,3435973836,4042322160,4278255360,4294901760],[]),([5,11184810,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,11206570,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,11206655,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,15658734,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16776960,16777215,2863311530,3435973836,4042322160],[]),([5,16776960,16777215,2863311530,3435973836,4042322160,4278190080],[]),([5,16776960,2863311530,3435973836,4042322160],[(2,89),(6,32),(10,8),(14,2)]),([5,16776960,2863311530,3435973836,4042322160,4278190080],[(129,89)]),([5,16776960,2863311530,3435973836,4042322160,4278190080,4278255360],[(168,89)]),([5,16776960,2863311530,3435973836,4042322160,4278190080,4294967040],[(168,89)]),([5,16776960,2863311530,3435973836,4042322160,4278255360],[]),([5,16776960,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,16776960,2863311530,3435973836,4042322160,4294967040],[(2,89)]),([5,16777215,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,16777215,2852170240,3435973836,4042322160,4289396650,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040],[]),([5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4294967040],[(2,89)]),([5,16777215,2863311530,3435973836,4210094320,4278255360,4294901760],[]),([5,67108863,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,178956970,268435455,3435973836,4042322160,4278255360,4294901760],[]),([5,178956970,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,178956970,3435973836,4026531840,4042322160,4278255360,4294901760],[(72,64)]),([5,178956970,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([5,178956970,3435973836,4042322160,4278255360,4294901760],[]),([5,268435455,2863311530,3435973836,4026593280,4293984240,4294901760],[(76,23)]),([5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760],[(76,23)]),([5,268435455,2863311530,4042322160,4241280204,4278255360,4294901760],[(76,47),(100,23),(132,71),(172,95)]),([5,1073741823,2863311530,3435973836,4042322160,4278255360,4294901760],[(76,23),(100,47),(132,71),(172,95)]),([5,2147483648,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2147516416,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2147516416,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([5,2147516416,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2147516416,2863311530,3435973836,4042322160,4286644096,4294901760],[(56,0),(72,0),(96,0),(128,0),(168,0)]),([5,2155905024,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760],[(128,0),(104,47)]),([5,2155905152,2290649224,4008636142,4042322160,4278255360,4294934656],[(104,47)]),([5,2155905152,2290649224,4008636142,4177066232,4278255360,4294901760],[(60,47),(128,4),(168,2),(80,47),(104,47)]),([5,2155905152,2852170240,3435973836,4042322160,4289396650,4294901760],[(56,11),(72,11),(96,11),(128,11),(168,11)]),([5,2155905152,2863311360,3435973836,4042322160,4278255360,4294901760],[(56,15),(128,21),(168,15)]),([5,2155905152,2863311530,3435973836,4042322160,4278190080,4294967040],[(56,89),(72,89),(96,89),(168,89)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934528],[(128,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936576],[(56,1),(72,1),(96,1)]),([5,2155905152,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([5,2155905152,2863311530,3435973836,4176541936,4278255360,4294901760],[(56,2),(72,2),(96,2),(128,3),(168,1)]),([5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760],[(128,4),(168,2),(80,47)])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,2155905152,2863311530,3435973836,4177066232,4278255360,4294934656],[(56,2),(72,2),(96,2),(128,1),(168,2),(80,47)]),([5,2155905152,2863311530,3941264106,4244438268,4278255360,4294901760],[(128,17),(168,11)]),([5,2155905152,2863311530,3974950124,4210752250,4278255360,4294901760],[(60,23),(128,21),(168,15),(104,23)]),([5,2155905152,3941264106,4244438268,4278255360,4294901760],[(96,113),(98,0),(97,89),(128,89),(129,113)]),([5,2155907208,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2155915946,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2155937791,2863311530,3435973836,4042322160,4278255360],[(2,113)]),([5,2155937791,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290122880,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290124928,2290649224,4008636142,4042322160,4278255360,4294901760],[(96,2),(128,0),(104,1)]),([5,2290124928,2863311530,3435973836,4026593280,4293984240,4294901760],[(56,59),(72,59),(96,3),(128,59),(168,59)]),([5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290124928,2863311530,3435973836,4042322160,4278255360,4294936704],[(96,1)]),([5,2290124928,2863311530,3435973836,4042322160,4286644096,4294901760],[(56,0),(72,0),(96,3),(128,0)]),([5,2290124928,2863311530,3435973836,4042322160,4287168392,4294901760],[(96,3),(168,0)]),([5,2290124928,2863311530,4008505068,4042322160,4278255360,4294901760],[(168,8)]),([5,2290649216,2863311520,3435973836,4042322160,4278255360,4294901760],[(56,8),(72,8),(96,16),(128,10),(168,8),(80,23)]),([5,2290649216,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2290679807,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2576980377,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2576980377,4042322160,4278255360,4294901760],[(6,63)]),([5,2290649224,2694881440,3435973836,4210096880,4278255360,4294901760],[(96,47),(128,49),(80,23)]),([5,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760],[(72,5),(96,5)]),([5,2290649224,2694881440,3974950124,4210752250,4278255360,4294901760],[(60,23)]),([5,2290649224,2728567458,3435973836,4042322160,4278255360,4294901760],[(96,8)]),([5,2290649224,2829625512,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2862653600,3435973836,4042322160,4278255360,4294901760],[(96,8),(80,23)]),([5,2290649224,2862656160,3435187392,4042322160,4278255360,4294901760],[(56,31),(72,7)]),([5,2290649224,2862656160,3435973836,4026593280,4293984240,4294901760],[(56,59),(96,7),(128,59),(80,23)]),([5,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760],[(96,13),(128,7),(80,23)]),([5,2290649224,2862656160,3435973836,4042322160,4287168392,4294901760],[(72,7),(128,7)]),([5,2290649224,2862656160,4008505068,4042322160,4278255360,4294901760],[(80,23)]),([5,2290649224,2862656160,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2863180456,3435973836,4042322160,4278255360,4294901760],[(80,23)]),([5,2290649224,2863311520,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,16),(128,10),(168,8),(80,23)]),([5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760],[(56,59),(72,59),(96,3)])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,2290649224,2863311530,3435973836,4034982016,4293984240,4294901760],[(56,59),(72,59),(96,3)]),([5,2290649224,2863311530,3435973836,4041273568,4278255360,4294901760],[(56,47),(72,47)]),([5,2290649224,2863311530,3435973836,4042322048,4278255360,4294901760],[(56,63),(72,63)]),([5,2290649224,2863311530,3435973836,4042322080,4278255360,4294901760],[(56,50),(72,50)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[(96,2)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936704],[(96,2),(128,0)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294942720],[(56,7),(72,7)]),([5,2290649224,2863311530,3435973836,4042322160,4286644096,4294934656],[(96,1)]),([5,2290649224,2863311530,3435973836,4042322160,4287137928,4294967040],[]),([5,2290649224,2863311530,3435973836,4042322160,4287168256,4294936712],[]),([5,2290649224,2863311530,3435973887,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3435982574,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3772834016,4244438268,4278255360,4294901760],[]),([5,2290649224,2863311530,3772834016,4278124286,4278255360,4294901760],[(196,0)]),([5,2290649224,2863311530,3972852940,4042322160,4278255360,4294901760],[(56,8),(72,8)]),([5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,4007718624,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,4008373994,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,4008505068,4042322160,4278255360,4294901760],[(60,23)]),([5,2290649224,2863311530,4008636142,4026593280,4293984240,4294901760],[(96,20)]),([5,2290649224,2863311530,4008636142,4041273568,4278255360,4294901760],[(148,1)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294934656],[(96,16)]),([5,2290649224,2863311530,4042322160,4241280204,4278255360,4294901760],[(56,63),(96,63)]),([5,2290649224,2863333375,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,3149642683,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,3772834016,3993038336,4042322160,4278255360,4294901760],[(136,1),(156,59)]),([5,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,3772834016,4008636142,4177066232,4278255360,4294901760],[(60,47)]),([5,2290649224,3772834016,4008636142,4210752250,4278255360,4294901760],[]),([5,2290649224,3772834016,4008636142,4278124286,4278255360,4294901760],[(196,0)]),([5,2290649224,3772834016,4042322160,4278124286,4278255360,4294901760],[(196,0)]),([5,2290649224,3772834016,4278124286,4278255360,4294901760],[(148,0),(150,0),(149,0)]),([5,2290649224,3907578088,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,3941264106,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,3941264106,4042322160,4244438268,4278255360,4294901760],[]),([5,2290649224,4007718624,4008636142,4042322160,4278255360,4294901760],[])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,2290649224,4007718624,4042322160,4278255360,4293984240,4294901760],[(116,59)]),([5,2290649224,4007718624,4042322160,4278255360,4294901760],[(74,1),(118,59),(117,83)]),([5,2290649224,4008373994,4042322160,4278255360,4293984240,4294901760],[]),([5,2290649224,4008373994,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4008640511,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4026593280,4293984240,4294901760],[(72,98),(74,3),(73,63),(109,59)]),([5,2290649224,4008636142,4034982016,4042322160,4278255360,4294901760],[(72,63),(96,59),(144,0)]),([5,2290649224,4008636142,4037079200,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4041273568,4042322160,4278255360,4294901760],[(140,1)]),([5,2290649224,4008636142,4041273568,4278255360,4293853166,4294901760],[(108,1)]),([5,2290649224,4008636142,4041273568,4278255360,4294901760],[(108,1),(110,1),(109,1)]),([5,2290649224,4008636142,4042321920,4042322160,4278255360,4294901760],[(72,63)]),([5,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4042326015,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4059165169,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4092851187,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4160223223,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4169726088,4278255360,4294901760],[(56,63),(96,63),(144,3)]),([5,2290649224,4008636142,4042322160,4176541936,4278255360,4294901760],[(128,69),(112,2)]),([5,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760],[(76,47)]),([5,2290649224,4008636142,4042322160,4205509290,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4210096880,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4277075694,4278255360,4294901760],[(140,1),(156,1),(196,3)]),([5,2290649224,4008636142,4042322160,4277206768,4278255360,4294901760],[(148,59),(156,1)]),([5,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760],[(156,1),(196,3)]),([5,2290649224,4008636142,4042322160,4278255360,4293980400,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4294508536,4294901760],[(204,3)]),([5,2290649224,4008636142,4042322160,4278255360,4294639610,4294901760],[(204,3)]),([5,2290649224,4008636142,4042322160,4278255360,4294901758,4294901760],[(204,3)]),([5,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4294901760,4294967280],[]),([5,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295],[])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,2290649224,4008636142,4042322160,4278255360,4294934656],[(72,93),(74,2),(73,59)]),([5,2290649224,4008636142,4042322160,4278255360,4294936712,4294963440],[(72,83),(172,0),(180,0),(148,0)]),([5,2290649258,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290649343,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290657448,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290657962,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2290657962,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,2290657962,3435973836,4008640511,4042322160,4278255360,4294901760],[]),([5,2290662331,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290678008,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2292886186,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2298478591,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2576980377,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2576980377,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([5,2576980377,2863311530,4042322160,4278255360,4294901760],[]),([5,2576980377,4008636142,4042322160,4278255360,4294901760],[]),([5,2576980377,4042322160,4278255360,4294901760],[(2,63),(6,2),(10,0)]),([5,2827520136,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8)]),([5,2827520136,2863311530,4042322160,4241280204,4278255360,4294901760],[(56,63),(96,63)]),([5,2827526144,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,4),(128,3),(168,7)]),([5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8)]),([5,2827528328,2863311530,3972852940,4042322160,4278255360,4294901760],[(56,8),(72,8)]),([5,2827528328,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([5,2827528328,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,2827528328,3435973836,4042322160,4205509290,4278255360,4294901760],[(56,64)]),([5,2827528328,3435973836,4042322160,4277075694,4278255360,4294901760],[]),([5,2827528328,4008636142,4042322160,4241292492,4278255360,4294901760],[]),([5,2827528328,4008636142,4042322160,4278255360,4294901760],[]),([5,2829625344,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,2),(128,17),(168,11)]),([5,2829625480,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8)]),([5,2829625512,2861083272,3435973836,4042322160,4278255360,4294901760],[(72,11),(80,5)]),([5,2829625512,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([5,2829625512,2863311360,3435973836,4042322160,4278255360,4294901760],[(128,21),(168,15),(80,5)])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,2829625512,2863311530,3435187392,4042322160,4278255360,4294901760],[(96,37)]),([5,2829625512,2863311530,3435973836,4042322160,4261477888,4294901760],[(56,71),(116,29)]),([5,2829625512,2863311530,3435973836,4042322160,4278254592,4294901760],[(56,80)]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294944768],[(56,11),(128,0)]),([5,2829625512,2863311530,3435973836,4176541936,4278255360,4294901760],[(56,2)]),([5,2829625512,2863311530,3435973836,4210096880,4278255360,4294901760],[]),([5,2829625512,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2829625512,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([5,2829625512,3435973836,4004179626,4042322160,4278255360,4294901760],[]),([5,2829625512,3435973836,4006407884,4042322160,4278255360,4294901760],[(80,5)]),([5,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,2829625512,3435973836,4042322160,4244438268,4261477888,4294901760],[(84,29)]),([5,2829625512,3435973836,4042322160,4261477888,4278124286,4294901760],[(84,29)]),([5,2829625512,3435973836,4042322160,4261477888,4278255360,4294901760],[(84,29)]),([5,2829625512,3435973836,4042322160,4261477888,4294901760],[(84,29),(86,29),(85,53)]),([5,2829625512,3435973836,4042322160,4272619178,4278255360,4294901760],[(84,29)]),([5,2829625512,3435973836,4042322160,4277993212,4278255360,4294901760],[(84,29),(196,0)]),([5,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760],[(84,29),(196,0)]),([5,2829625512,3435973836,4210096880,4244438268,4278255360,4294901760],[]),([5,2829625512,3435973836,4210096880,4278255360,4294901760],[]),([5,2829625512,3435973836,4210752250,4278255360,4293984240,4294901760],[(132,5),(116,73)]),([5,2829626026,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2829647100,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2829647871,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863179944,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863179944,3435973836,4042322160,4244438268,4278255360,4294901760],[(84,29),(156,79),(196,103)]),([5,2863179944,3435973836,4042322160,4278255360,4291611852,4294901760],[(148,56)]),([5,2863179944,3435973836,4042322160,4278255360,4294769916,4294901760],[(204,0)]),([5,2863179944,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,2863311530,3435973836,4042322160,4278255360,4294705152],[(56,104)]),([5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,3435973836,3974950124,4042322160,4278255360,4294901760],[]),([5,2863180456,3435973836,4008505068,4042322160,4278255360,4294901760],[(60,23)]),([5,2863180456,3435973836,4008636142,4042322160,4278255360,4294901760],[])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863180456,3435973836,4042322160,4244438268,4278255360,4294705152],[(84,29),(156,79)]),([5,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760],[(84,29),(156,79)]),([5,2863180456,3435973836,4042322160,4277993212,4278255360,4294901760],[(156,11),(196,103)]),([5,2863180456,3435973836,4042322160,4278124286,4278255360,4294901760],[(156,11),(196,95)]),([5,2863180456,3435973836,4042322160,4278255360,4294705152],[]),([5,2863180456,3435973836,4042322160,4278255360,4294705152,4294770684],[]),([5,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901758,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294945448],[(132,95)]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294945450],[(132,17)]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294954188],[(140,41)]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294966524],[(196,11)]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294967292],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([5,2863311528,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311528,3435973836,4042322160,4244438268,4278255360,4294901760],[(84,29)]),([5,2863311528,3435973836,4042322160,4278255360,4294770684,4294901760],[(204,104)]),([5,2863311528,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311528,3435973836,4042322160,4278255360,4294901760,4294967292],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294950912],[(48,31),(52,31)]),([5,2863311530,2863311535,3435973836,4042322160,4278255360,4294901760],[(56,32)]),([5,2863311530,2863311598,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863312895,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863320268,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863327978,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863333118,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863661055,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2867785454,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,2952790015,3435973836,4042322160,4278255360,4294901760],[(84,23)]),([5,2863311530,3435973836,3907578088,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3937053354,4042322160,4278255360,4294901760],[(72,32)]),([5,2863311530,3435973836,3937058816,4042322160,4278255360,4294901760],[(72,32),(168,31),(184,31)]),([5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760],[(72,32)]),([5,2863311530,3435973836,3937069738,4042322160,4278255360,4294950912],[(72,31),(76,31)]),([5,2863311530,3435973836,3937069738,4042322160,4290838464,4294901760],[(72,33),(104,21)]),([5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760],[(128,33),(104,15)]),([5,2863311530,3435973836,3938511552,4042322160,4289396650,4294901760],[(76,11),(128,33),(104,17)]),([5,2863311530,3435973836,3939035848,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3941263872,4042322160,4278255360,4294901760],[(72,32),(204,89)]),([5,2863311530,3435973836,3941264042,4042322160,4278255360,4294901760],[(72,32)]),([5,2863311530,3435973836,3941264064,4042322160,4278255360,4294901760],[(76,15),(104,15)]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294934656],[(72,32),(104,11)]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294950912],[(76,31)]),([5,2863311530,3435973836,3941264106,4243651824,4278255360,4294901760],[(84,23)]),([5,2863311530,3435973836,3941265134,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3941269503,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760],[(156,59)]),([5,2863311530,3435973836,4008372970,4042322160,4278255360,4294901760],[(84,23)]),([5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760],[(84,23)]),([5,2863311530,3435973836,4008636128,4042322160,4278255360,4294901760],[(76,8),(84,32)]),([5,2863311530,3435973836,4008636138,4042322160,4278255360,4294901760],[(84,23)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901777],[(76,47),(84,47)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294934656],[]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294942720],[(76,7),(84,7)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294959104],[(76,59),(84,59)]),([5,2863311530,3435973836,4008636159,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4008640254,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4009754623,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4277071598,4278255360,4294901760],[(116,47),(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4277074602,4278255360,4294901760],[(108,27),(116,49),(156,73),(196,95)]),([5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760],[(116,47),(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4278124202,4278255360,4294901760],[(108,26),(116,50),(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4278124270,4278255360,4294901760],[(116,47),(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4278124286,4278255360,4294902017],[(100,71),(108,71),(116,71),(156,71),(196,95)])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4278124543,4278255360,4294901760],[(156,71),(196,95)]),([5,2863311530,3435973836,4042322160,4278255360,4294901502,4294901760],[(156,71),(204,95)]),([5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760],[(204,95)]),([5,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967294],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901763],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901775,4294963440],[(148,65)]),([5,2863311530,3435973836,4042322160,4278255360,4294901775,4294967280],[(172,8),(180,32)]),([5,2863311530,3435973836,4042322160,4278255360,4294901930,4294967040],[(172,15),(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294902015,4294945280],[(132,17)]),([5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294905855,4294963200],[(148,65),(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([5,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294934656],[]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294936712],[]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294945450],[(132,17)]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967040],[(172,15),(180,39),(188,63),(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967168],[(172,15),(180,39),(188,63),(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294934656,4294967295],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936704],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294942880],[(132,3),(172,9)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963200],[(172,20),(180,44),(148,65),(156,89)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(172,9),(180,33),(148,65)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294967280],[(172,8),(180,32)]),([5,2863311530,3435973836,4042322160,4278255360,4294944936,4294967040],[(172,15),(156,89),(204,11)]),([5,2863311530,3435973836,4042322160,4278255615,4294902015],[(156,89)]),([5,2863311530,3435973836,4042322160,4278255615,4294902015,4294967040],[(156,89)]),([5,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([5,2863311530,3435973836,4042322160,4287137928,4294967040],[(56,50),(58,8),(57,32),(133,15),(141,39)])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4287168256,4294936712],[(56,63),(58,8),(57,32)]),([5,2863311530,3435973836,4042322160,4287168392,4294936712,4294967040],[(56,59),(204,0)]),([5,2863311530,3435973836,4042322160,4289374890,4291611852,4294967040],[(56,50),(132,2),(108,26)]),([6,0,0,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([6,0,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,15,2863311530,3435973836,4042322160,4278255360,4294901760],[(80,32),(104,8)]),([6,0,170,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,255,2863311530,3435973836,4042322160,4278190080],[(6,89),(176,89)]),([6,0,255,2863311530,3435973836,4042322160,4278190080,4294967040],[(60,89),(176,89)]),([6,0,255,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,4095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,34952,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,43690,2863267840,3435973836,4042322160,4278255360,4294901760],[(224,17)]),([6,0,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,43690,2863333375,3435973836,4042322160,4278255360],[]),([6,0,43690,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,0,61166,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,65535,16711935,252645135,2863311530,3435973836],[]),([6,0,65535,16711935,2863311530,3435973836,4042322160],[])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,65535,2290649224,4008636142,4042322160,4278255360],[]),([6,0,65535,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([6,0,65535,2863267840,3435973836,4042322160,4278255360,4294945450],[(60,17)]),([6,0,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,1048575,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,11184810,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,16777215,2863311530,3435973836,4042322160,4278190080,4294967040],[(60,89)]),([6,0,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,16777215,2863311530,3435973836,4042322160,4294967040],[(6,89)]),([6,0,268435455,2863311530,3435973836,4042322160,4278255360,4294901760],[(108,23)]),([6,0,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760],[(176,0),(144,47)]),([6,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(176,0)]),([6,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([6,0,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760],[(176,4),(224,2),(112,47)]),([6,0,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,2),(176,0)]),([6,0,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760],[(60,5),(104,5),(136,5)]),([6,0,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760],[(136,13),(176,7),(112,23)]),([6,0,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760],[(60,59),(80,59),(104,59),(136,3)])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[(136,2)]),([6,0,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760],[]),([6,0,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760],[]),([6,0,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760],[(108,47)]),([6,0,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760],[]),([6,0,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760],[(204,1),(252,3)]),([6,0,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760],[]),([6,0,2290649224,4008636142,4042322160,4278255360,4294901760],[(129,1),(169,3)]),([6,0,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295],[]),([6,0,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760],[(104,8)]),([6,0,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760],[(116,29),(252,0)]),([6,0,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760],[(116,29),(204,79)]),([6,0,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760],[])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,2863180456,3435973836,4042322160,4278255360,4294901760],[(97,5),(129,11)]),([6,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760],[(60,32),(104,32)]),([6,0,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760],[(176,33),(144,15)]),([6,0,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([6,0,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760],[(204,59)]),([6,0,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760],[(116,23)]),([6,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,0,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[]),([6,0,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760],[(156,47),(204,71),(252,95)]),([6,0,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(204,71),(252,95)]),([6,0,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760],[(260,95)]),([6,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(73,23),(97,47),(129,71),(169,95)]),([6,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,0,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[(204,89)]),([6,0,2863311530,3435973836,4042322160,4278255360,4294934656],[(73,23),(97,47),(129,71)]),([6,0,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(228,9),(236,33),(196,65)])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(56,62),(72,60),(96,2),(128,0),(168,59)]),([6,15,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(56,32),(58,23),(72,8),(73,23),(77,23),(97,47),(129,71),(169,95)]),([6,15,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280],[(56,64),(72,63),(96,2),(128,0),(236,23)]),([6,170,255,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,170,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,92),(73,23),(97,47),(101,5),(129,71),(169,95)]),([6,170,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(56,89),(128,0),(216,15)]),([6,255,255,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,255,65535,16711935,2863311530,3435973836,4042322160],[]),([6,255,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,255,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,255,252645135,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,2)]),([6,255,252645135,2863311530,3435973836,4278255360,4294901760],[]),([6,255,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,23)]),([6,255,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,11)]),([6,255,2863311360,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,255,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,255,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[]),([6,255,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[])]
noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,2863311530,3435973836,4042322160,4278190080],[(2,89),(128,89),(129,89),(6,29),(10,5)]),([6,255,2863311530,3435973836,4042322160,4278190080,4278255360],[(2,89),(128,89)]),([6,255,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(128,89)]),([6,255,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040],[(128,89),(168,89),(172,89)]),([6,255,2863311530,3435973836,4042322160,4278190080,4294967040],[(2,89),(57,89),(73,91),(77,23),(97,93),(101,47),(128,89),(129,89),(133,89),(169,89),(173,89)]),([6,255,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(128,71)]),([6,255,2863311530,3435973836,4042322160,4278255360,4278255615,4294901760],[(168,71)]),([6,255,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(56,32),(168,11)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(73,23),(77,23),(97,47),(101,47),(129,71),(169,95)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(128,0)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967210],[(56,32),(236,23),(244,47)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,255,2863311530,3435973836,4042322160,4278255360,4294902015],[]),([6,255,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[]),([6,4095,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(96,59)]),([6,4095,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(169,95)]),([6,4095,2863311530,3435973836,4042322160,4278255360,4294901760,4294963200],[]),([6,34952,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([6,34952,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,34952,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,34952,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,34952,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(97,47),(129,71),(133,1),(169,95)]),([6,43690,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,52428,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,23),(96,23)]),([6,43690,65535,16711935,2863311530,3435973836,4042322160],[]),([6,43690,65535,1431655765,3435973836,4042322160,4278255360],[(56,31)]),([6,43690,65535,2863267840,3435973836,4042322160,4278255360],[]),([6,43690,65535,2863267840,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,65535,2863333375,3435973836,4042322160,4278255360],[]),([6,43690,65535,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,0),(72,0)])]
noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([6,43690,16711935,2863311530,3435973836,4042322160,4294901760],[(72,0)]),([6,43690,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,31),(72,32)]),([6,43690,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,1431699455,2863267840,3435973836,4042322160,4278255360,4294901760],[(72,31),(216,31)]),([6,43690,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,31),(72,31)]),([6,43690,1431699455,3435973836,4042322160,4278255360,4294901760],[(168,31)]),([6,43690,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,17),(216,17)]),([6,43690,2863267840,3435973836,4042322160,4278255360,4294901760],[(57,17),(168,17),(169,95)]),([6,43690,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,2863311530,2863333375,3435973836,4042322160,4278255360],[]),([6,43690,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(56,29),(72,29)]),([6,43690,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760],[(56,41),(72,23)]),([6,43690,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(56,23),(72,23)]),([6,43690,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760],[(56,23),(96,23)]),([6,43690,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[(56,23),(96,23)]),([6,43690,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[])]
noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([6,43690,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(56,29),(128,29)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,104),(73,23),(97,47),(101,5),(129,71),(133,11),(169,17)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[(56,95),(168,17)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294923605],[(56,104),(168,31)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(56,17),(216,17)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188],[(56,41),(72,8),(216,3)]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294945450],[(2,31)]),([6,43690,2863333375,3435973836,4042322160,4278255360],[(2,31),(10,7),(14,1)]),([6,43690,2863333375,3435973836,4042322160,4278255360,4294901760],[(169,32)]),([6,61166,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,61166,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,61166,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,61166,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(169,3)]),([6,65535,65535,16711935,2863311530,3435973836,4042322160],[])]
noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,16711935,16777215,2863311530,3435973836,4042322160],[]),([6,65535,16711935,252645135,2863311530,3435973836],[(2,3),(6,1),(14,23)]),([6,65535,16711935,252645135,2863311530,3435973836,4042322160],[]),([6,65535,16711935,2290649224,2863311530,3435973836,4042322160],[]),([6,65535,16711935,2852170240,2863311530,3435973836,4042322160],[]),([6,65535,16711935,2863311530,2863311530,3435973836,4042322160],[]),([6,65535,16711935,2863311530,2863333375,3435973836,4042322160],[]),([6,65535,16711935,2863311530,3435973836,4008636142,4042322160],[]),([6,65535,16711935,2863311530,3435973836,4042322160],[(2,0),(10,29),(14,5)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278190080],[])]
noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,16711935,2863311530,3435973836,4042322160,4278255360],[(2,0)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255615],[]),([6,65535,16711935,2863311530,3435973836,4042322160,4289396650],[]),([6,65535,16711935,2863311530,3435973836,4042322160,4294967040],[]),([6,65535,16711935,2863311530,3435973836,4042322160,4294967295],[]),([6,65535,16777215,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,268374015,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([6,65535,268374015,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2155905152,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2290614272,2863311530,3435973836,4042322160,4278255360],[(2,3),(136,1)]),([6,65535,2290614272,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,1)])]
noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2290649224,2863311530,4008636142,4042322160,4278255360],[]),([6,65535,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([6,65535,2290649224,4008636142,4042322160,4278255360],[(6,59),(10,63),(14,1)]),([6,65535,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,3),(101,47),(129,1),(133,71)]),([6,65535,2290657962,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2290679807,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2829625512,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360],[(2,17)]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294945450],[(72,17)]),([6,65535,2863267840,3435973836,4042322160,4278255360,4294901760,4294945450],[(56,32),(168,17),(172,17)])]
noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863267840,3435973836,4042322160,4278255360,4294945450],[(2,95),(57,17),(61,17),(73,17),(77,23),(97,19),(101,47),(129,21),(133,71),(169,17)]),([6,65535,2863302792,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([6,65535,2863302792,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863329006,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2868882175,3435973836,4042322160,4278255360],[(2,0)]),([6,65535,2863311530,2868882175,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,3941264106,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4008574976,4042322160,4278255360],[(2,95)]),([6,65535,2863311530,3435973836,4008574976,4042322160,4278255360,4294901760],[])]
noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863311530,3435973836,4008618666,4042322160,4278255360],[(2,3)]),([6,65535,2863311530,3435973836,4008618666,4042322160,4278255360,4294901760],[(56,32)]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4008640511,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278124286,4278255360],[(204,71)]),([6,65535,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(204,71)]),([6,65535,2863311530,3435973836,4042322160,4278255360],[(6,31),(10,7),(14,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294902015],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294936712],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(56,32)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294962926],[(244,47),(252,71)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294902015],[(2,95)])]
noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863311530,3435973836,4042322160,4278255360,4294936712],[(2,95)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294945450],[(2,17)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294962926],[(2,3),(196,47),(204,71)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294967295],[]),([6,65535,2863311530,3435973836,4042322160,4278255615,4294901760,4294967040],[(128,0),(220,71),(204,71)]),([6,65535,2863311530,3435973836,4042322160,4278255615,4294967040],[(2,0),(172,71)]),([6,1048575,2863311530,3435973836,4042322160,4278255360,4293918720,4294901760],[(220,95)]),([6,1048575,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(172,59)]),([6,1048575,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(173,95)]),([6,11184810,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,11184810,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(56,89),(128,15)]),([6,11184810,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,92),(73,23),(97,47),(101,5),(129,11),(133,11),(169,17),(173,17),(105,5),(181,0)]),([6,16777215,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,16777215,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,16777215,2852126720,2863311530,3435973836,4042322160,4278255360,4294901760],[(104,5)]),([6,16777215,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[(60,11)])]
noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,16777215,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,16777215,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[]),([6,16777215,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(76,23)]),([6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(172,71),(220,95)]),([6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294967040],[(168,89),(172,71)]),([6,16777215,2863311530,3435973836,4042322160,4278190080,4294967040],[(2,89),(57,89),(73,91),(77,23),(97,93),(101,47),(129,89),(133,89),(169,89)]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(132,71)]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4289374890,4294901760],[(56,32)]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(73,23),(77,23),(97,47),(101,47),(133,71),(173,95)]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4294967040],[(2,89)]),([6,16777215,2863311530,3435973836,4042322160,4294967040],[(2,89),(6,32),(10,8),(14,2)]),([6,268435455,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760],[(76,23),(132,47),(172,71),(220,95),(104,23)]),([6,268435455,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(76,23),(100,59),(132,47),(172,71)]),([6,268435455,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(73,23),(76,23),(78,23),(77,23),(101,47),(133,71),(173,95)]),([6,2147516416,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2147516416,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(73,23),(97,47),(129,71),(169,95)]),([6,2155905152,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2281736192,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,1),(96,1),(128,1),(168,1),(216,1)]),([6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([6,2155905152,2290649224,2863311530,3435973836,4177066232,4278255360,4294901760],[(168,4),(216,2)]),([6,2155905152,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(168,0),(136,5)]),([6,2155905152,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,89),(128,0),(130,0),(129,1),(169,3),(173,0),(104,47),(105,47)]),([6,2155905152,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,11),(72,11),(96,11),(128,11),(168,11),(216,11)]),([6,2155905152,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(60,29),(168,0),(104,29)]),([6,2155905152,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(56,89),(72,89),(96,89),(128,71),(168,113),(216,89)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(56,71),(72,71),(96,71),(128,71),(216,71)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4286644096,4294901760],[(56,71),(72,71),(96,71),(128,0),(168,71),(216,71),(200,0)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4287168392,4294901760],[(56,71),(72,71),(96,71),(128,0),(168,71),(216,71)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(56,11),(72,11),(96,11),(128,0),(168,11),(216,11)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(73,23),(97,47),(128,0),(130,0),(129,71),(169,95),(173,0)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(56,89),(72,89),(96,89),(128,0),(216,89),(236,23),(244,47)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(128,0)])]
noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656],[(2,89),(73,23),(97,47),(129,71)]),([6,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760],[(128,4),(130,0),(129,71),(168,2),(169,95),(80,47),(82,5),(81,29)]),([6,2290124928,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0),(136,1)]),([6,2290124928,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760],[(56,7),(72,7),(96,7),(128,13),(168,7),(216,7)]),([6,2290124928,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(56,59),(72,59),(96,72),(128,48),(168,59),(216,59)]),([6,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(96,2),(98,1),(97,47),(128,0),(129,71),(133,1),(169,95),(173,3)]),([6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2290649224,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([6,2290649224,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,63),(129,1),(133,1),(169,3),(173,3)]),([6,2290649224,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2290649224,2694881440,2852170240,3435973836,4042322160,4278255360,4294901760],[(56,11),(72,5),(128,13),(168,7),(104,11),(176,1),(112,5)]),([6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,5),(96,5),(128,5),(112,5)]),([6,2290649224,2694881440,2863311530,3435973836,4177066232,4278255360,4294901760],[(72,5),(96,5),(128,5),(112,5)]),([6,2290649224,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760],[(72,5),(96,5),(128,5)]),([6,2290649224,2694881440,3435973836,4008636142,4042322160,4278255360,4294901760],[(76,5),(128,47),(80,23),(104,23),(136,23),(112,5)]),([6,2290649224,2694881440,3435973836,4210752250,4278255360,4294901760],[(2,63),(57,5),(61,5),(72,5),(73,5),(96,5),(97,5),(129,7),(133,1),(169,9),(173,3)]),([6,2290649224,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2290649224,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,7),(96,7),(128,13),(168,7)])]
noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,2862656160,3435973836,4042322160,4278255360,4293984240,4294901760],[(56,7),(96,13),(128,7),(168,7),(80,23)]),([6,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760],[(57,7),(96,13),(98,1),(97,7),(128,7),(129,13),(173,3),(80,23),(81,23)]),([6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2290649224,2863311530,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([6,2290649224,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,2290649224,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760],[(56,8),(72,8),(96,8)]),([6,2290649224,2863311530,3149642683,4042322160,4278255360,4294901760],[(10,32)]),([6,2290649224,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760],[(56,47),(72,47),(128,47),(104,23),(136,23)]),([6,2290649224,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(60,23),(104,23)]),([6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(60,23),(104,23)]),([6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(56,59),(72,59),(96,7),(80,59)]),([6,2290649224,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760],[(56,59),(72,59),(96,47),(128,59),(132,47),(80,59)]),([6,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760],[(2,63),(56,59),(57,59),(72,59),(73,61),(96,3),(98,3),(97,59),(101,59),(129,59),(169,63),(173,3),(81,23),(149,23)]),([6,2290649224,2863311530,3435973836,4034982016,4042322160,4278255360,4294901760],[(56,59),(72,59),(96,7),(128,59),(192,0)]),([6,2290649224,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760],[(56,49),(72,49),(96,7),(128,49)]),([6,2290649224,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760],[(56,63),(72,63),(96,47),(132,47)]),([6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(56,47),(72,47),(96,47)]),([6,2290649224,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760],[(56,47),(72,47),(128,47)]),([6,2290649224,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760],[(56,50),(72,50),(96,15),(128,8)]),([6,2290649224,2863311530,3435973836,4042322160,4160223223,4278255360,4294901760],[(56,63),(72,63),(96,89),(148,23)]),([6,2290649224,2863311530,3435973836,4042322160,4169726088,4278255360,4294901760],[(56,7),(72,7),(128,7),(192,3)])]
noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,2863311530,3435973836,4042322160,4176541936,4278255360,4294901760],[(56,47),(72,47),(96,2),(128,47),(168,47),(152,2)]),([6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(56,47),(72,47),(128,47)]),([6,2290649224,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760],[(56,7),(72,7),(128,7)]),([6,2290649224,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760],[(56,49),(72,49),(96,2),(128,47),(168,49)]),([6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(56,5),(72,5),(128,5)]),([6,2290649224,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(204,1),(252,3)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760],[(56,63),(72,63),(96,2),(168,50),(188,23)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(56,59),(72,59),(96,2),(128,0),(168,59),(188,23)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294508536,4294901760],[(56,59),(72,59),(168,59),(188,23),(260,3)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760],[(56,7),(72,7),(168,7),(188,23),(260,3)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(73,23),(97,47),(129,71),(133,1),(169,95),(173,3),(81,23)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280],[(56,63),(72,63),(96,2),(128,0),(216,63),(236,23)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[(2,63),(73,23),(96,2),(98,2),(97,47),(129,71),(133,1),(173,0),(81,23)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(96,1),(220,0),(228,0),(236,24),(196,0)]),([6,2290649224,2863311530,3772834016,4008636142,4042322160,4278255360,4294901760],[(84,5)]),([6,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760],[(101,5),(129,71),(169,95),(81,23),(105,23),(141,11),(181,17)]),([6,2290649224,2863311530,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([6,2290649224,2863311530,4008636142,4042322160,4042322160,4278255360,4294901760],[(108,5)]),([6,2290649224,2863311530,4008636142,4042322160,4177066232,4278255360,4294901760],[(100,5),(108,5)]),([6,2290649224,2863311530,4008636142,4042322160,4210752250,4278255360,4294901760],[])]
noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,2863311530,4008636142,4042322160,4244438268,4278255360,4294901760],[(60,23),(80,23)]),([6,2290649224,2863311530,4008636142,4042322160,4278124286,4278255360,4294901760],[(204,1),(252,3)]),([6,2290649224,2863311530,4008636142,4042322160,4278255360,4293984240,4294901760],[]),([6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(6,32),(109,5),(137,1),(141,11),(177,3),(181,17)]),([6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760,4294967295],[]),([6,2290649224,3772834016,4008636142,4042322160,4278255360,4294901760],[(6,89),(137,1),(141,59),(177,3),(181,65),(189,0),(157,59),(197,65)]),([6,2290649224,4008636142,4008636142,4042322160,4278255360,4294901760],[(6,63),(137,1),(141,1),(177,3),(181,3)]),([6,2290649224,4008636142,4042322160,4042322160,4278255360,4294901760],[(10,2),(149,59),(185,0),(189,65)]),([6,2290649224,4008636142,4042322160,4177066232,4278255360,4294901760],[(76,47),(77,47),(129,63),(169,69),(145,2),(185,4),(14,89),(157,1),(193,0),(197,3)]),([6,2290649224,4008636142,4042322160,4210752250,4278255360,4294901760],[(14,39),(157,1),(193,0),(197,3)]),([6,2290649224,4008636142,4042322160,4278124286,4278255360,4294901760],[(14,89),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,2290649224,4008636142,4042322160,4278255360,4293984240,4294901760],[(74,2),(98,0),(118,59),(117,83),(158,1),(18,3),(205,3)]),([6,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,63),(3,63),(99,1),(103,1),(131,3),(135,3),(6,63),(7,63),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(119,59),(147,0),(151,65),(13,1),(14,0),(15,0),(155,2),(159,89),(17,3)])]
noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,4008636142,4042322160,4278255360,4294901760,4294967295],[(198,1),(206,3)]),([6,2290657962,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[(56,23),(96,23)]),([6,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,112),(73,23),(97,47),(101,5),(129,71),(133,11),(169,17),(173,3),(181,17)]),([6,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,111),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(173,3)]),([6,2827528328,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[(56,31),(72,60),(128,31)]),([6,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,112),(72,8),(73,23),(97,47),(101,5),(129,71),(133,11),(169,95),(173,17),(181,17)]),([6,2829625512,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2829625512,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2829625512,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(56,23),(72,23)]),([6,2829625512,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[(56,23),(96,23)]),([6,2829625512,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2829625512,2863311530,3435973836,4042322160,4227922944,4278255360,4294901760],[(56,79),(128,11),(132,11),(168,79),(180,11),(116,29)]),([6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(56,29),(128,29),(116,29)]),([6,2829625512,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(116,29),(252,0)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(56,71),(128,71),(132,11),(140,11)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4289265576,4294901760],[(56,71),(132,11),(168,71),(140,11)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(56,11),(168,11),(140,11)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4291624908,4294901760],[(56,35),(72,8),(168,35),(80,5),(148,35),(196,5)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(56,31),(168,31),(260,0)])]
noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,92),(73,23),(97,47),(101,5),(129,71),(133,11),(169,95),(173,17),(105,5),(141,11),(181,17)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(56,89),(128,0),(216,89),(204,89)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,2829625512,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760],[(60,23),(108,29)]),([6,2829625512,3435973836,4008636142,4042322160,4278255360,4294901760],[(61,23),(109,53),(137,5),(177,6),(149,71),(189,95)]),([6,2829625512,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760],[(84,29),(252,0)]),([6,2829625512,3435973836,4042322160,4278124286,4278255360,4294901760],[(84,29),(86,29),(85,53),(196,0),(198,0),(197,0)]),([6,2863180456,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(56,29),(128,29),(116,29),(204,79)]),([6,2863180456,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(56,31),(168,31)]),([6,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,104),(73,23),(97,47),(101,5),(129,71),(133,11),(169,95),(173,17),(6,32),(105,5),(109,5),(137,11),(141,11),(181,17)]),([6,2863180456,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760],[(84,29),(156,79)]),([6,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760],[(84,29),(86,29),(85,53),(118,5),(14,15),(156,79),(158,79),(157,79),(197,103)]),([6,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760],[(150,5),(158,11),(18,17),(205,104)]),([6,2863180456,3435973836,4042322160,4278255360,4294901760],[(2,104),(3,104),(75,5),(79,5),(99,11),(103,11),(135,17),(6,8),(7,8),(87,29),(107,1),(111,35),(143,41),(9,5),(10,2),(11,2),(115,7),(119,59),(147,5),(151,65),(13,11),(14,0),(15,0),(155,11),(159,89)]),([6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(48,23),(52,23)])]
noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[(48,23),(52,23)]),([6,2863311530,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[(48,32),(52,32),(72,63)]),([6,2863311530,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[(48,23),(52,23)]),([6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[(48,31),(52,31),(72,60)]),([6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(48,29),(52,29),(116,29)]),([6,2863311530,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(204,71),(252,95)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(48,31),(52,31),(260,104)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(97,5),(101,5),(129,11),(133,11),(169,17),(173,17)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[(77,23),(101,47),(129,32),(169,34),(6,92),(85,23),(105,5),(109,47),(137,11),(141,11),(177,17),(181,17)]),([6,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760,4294967040],[(60,89),(216,32),(228,15),(204,89)]),([6,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[(77,23),(169,32),(6,112),(85,23),(105,5),(109,47),(137,11),(141,71),(177,3),(181,17)]),([6,2863311530,2863333375,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863333375,3435973836,3435986943,4042322160,4278255360,4294901760],[(60,23),(84,23)]),([6,2863311530,2863333375,3435973836,4008636142,4042322160,4278255360,4294901760],[(84,23)]),([6,2863311530,2863333375,3435973836,4008640511,4042322160,4278255360,4294901760],[(84,23)]),([6,2863311530,2863333375,3435973836,4042322160,4244438268,4278255360,4294901760],[(60,29),(116,29)])]
noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(169,32),(6,104),(85,23),(105,5),(109,47),(137,11),(141,71),(181,17)]),([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450],[(56,32),(60,17),(172,17),(216,32),(180,17)]),([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294954188],[(60,41),(188,41)]),([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[(6,92),(85,23),(105,5),(109,47),(141,71),(181,95)]),([6,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760],[(2,32),(57,32),(61,23),(72,32),(73,32),(97,56),(101,47),(129,80),(133,71),(169,32),(173,95),(86,23),(10,104),(113,5),(117,47),(145,11),(149,71),(185,17),(189,95)]),([6,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760],[(78,11),(128,33),(129,79),(82,25),(86,29),(104,15),(106,25),(105,49),(10,99),(113,49),(117,53),(145,79),(149,71),(185,95),(189,95)]),([6,2863311530,3435973836,3941264106,3941264106,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,3941264106,4008636142,4042322160,4278255360,4294901760],[(84,23)]),([6,2863311530,3435973836,3941264106,4042322160,4244438268,4278255360,4294901760],[(76,29),(100,5),(84,29),(108,29),(116,53)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4289396650,4294901760],[(72,32),(76,11),(132,11),(168,32),(180,25),(148,71),(184,11),(196,49)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4290838464,4294901760],[(76,79),(128,33),(172,11),(104,15),(148,71),(184,11)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4291624908,4294901760],[(76,35),(172,1),(140,35),(184,1)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4293591018,4294901760],[(76,11),(180,23),(148,71),(184,11),(196,47),(260,99)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(61,23),(101,47),(129,32),(169,34),(86,23),(10,92),(113,5),(117,47),(145,11),(149,71),(185,17),(189,95)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760,4294967040],[(76,89),(216,32),(232,15),(204,89)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760,4294967295],[]),([6,2863311530,3435973836,4007718624,4008636142,4042322160,4278255360,4294901760],[(204,59)])]
noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760],[(61,23),(78,7),(82,23),(86,31),(10,98),(113,59),(117,47),(145,83),(149,71),(185,95),(189,95),(156,59),(158,59),(157,83)]),([6,2863311530,3435973836,4008373994,4042322160,4278255360,4293984240,4294901760],[(76,59),(172,7),(84,31),(184,7),(156,59)]),([6,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760],[(61,23),(169,32),(84,23),(86,23),(85,23),(10,112),(113,5),(117,47),(145,11),(149,71),(185,17),(189,95)]),([6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4008636142,4008640511,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760],[(76,5),(100,5),(84,5),(140,23),(116,47)]),([6,2863311530,3435973836,4008636142,4042322160,4277075694,4278255360,4294901760],[(116,47),(188,71),(156,47),(204,71),(252,95)]),([6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760],[(116,47),(204,71),(252,95)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760],[(76,59),(84,59),(156,59)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294639610,4294901760],[(76,7),(84,7),(180,23),(260,98)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901758,4294901760],[(260,95)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(61,23),(86,23),(10,63),(117,47),(145,1),(149,71),(185,3),(189,95)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967280],[(76,63),(220,8),(84,63),(228,32)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295],[]),([6,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[(86,23),(10,111),(117,47),(145,1),(149,71),(189,95)]),([6,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760],[(110,23),(116,47),(118,47),(117,47),(14,111),(153,1),(156,71),(158,71),(157,71),(193,3),(196,95),(198,95),(197,95)]),([6,2863311530,3435973836,4042322160,4278124286,4278124286,4278255360,4294901760],[(196,71),(244,95)]),([6,2863311530,3435973836,4042322160,4278124286,4278255360,4293853166,4294901760],[(100,1),(108,1),(116,1),(188,47),(156,71),(244,95),(260,96)])]
noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901758,4294901760],[(156,71),(244,95),(260,95)]),([6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(110,23),(118,47),(14,89),(156,71),(158,71),(157,71),(193,0),(196,95),(198,95),(197,95)]),([6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760,4294967295],[(156,71),(196,95)]),([6,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760],[(142,23),(150,47),(158,71),(18,95),(204,95),(206,95),(205,95)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(13,71),(14,0),(15,0),(155,89),(159,89),(17,95)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(182,23),(190,47),(198,71),(206,95)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295],[]),([6,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[(156,89),(158,89),(157,113),(206,95),(205,89)]),([6,2863311530,3435973836,4042322160,4278255360,4294934656],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,23),(143,41),(9,47),(10,2),(11,2),(115,59),(119,59),(147,47),(151,65),(13,71),(14,0),(15,0),(159,89),(18,71),(19,71)]),([6,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(172,9),(174,9),(173,9),(180,33),(182,33),(181,33),(148,65),(150,65),(149,65),(205,47)]),([6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188,4294963440],[(172,3),(220,9),(140,27),(228,33),(148,51),(188,57),(252,5),(260,29)]),([7,0,0,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,0,65535,2863311530,3435973836,4042322160,4278255360],[])]
noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([7,0,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(169,71),(217,95)]),([7,0,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([7,0,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(217,0),(6,89),(105,23),(109,23),(137,47),(141,47),(177,71),(225,95)]),([7,0,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(60,89),(176,0)]),([7,0,43690,65535,2863311530,3435973836,4042322160,4278255360],[]),([7,0,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,5),(169,11),(6,104),(105,23),(137,47),(141,5),(177,71),(181,11),(225,17)])]
noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,65535,65535,2863311530,3435973836,4042322160,4278255360],[]),([7,0,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,65535,16711935,2863311530,3435973836,4042322160],[(73,0),(129,23),(169,47),(6,0),(14,29),(18,5)]),([7,0,65535,16711935,2863311530,3435973836,4042322160,4278255360],[(6,0)]),([7,0,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[(60,0)]),([7,0,65535,2290649224,2863311530,3435973836,4042322160,4278255360],[]),([7,0,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,65535,2863267840,2863311530,3435973836,4042322160,4278255360],[(6,17)]),([7,0,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(60,17)])]
noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,65535,2863311530,2863311530,3435973836,4042322160,4278255360],[]),([7,0,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,65535,2863311530,2863333375,3435973836,4042322160,4278255360],[]),([7,0,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([7,0,65535,2863311530,3435973836,4008636142,4042322160,4278255360],[]),([7,0,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([7,0,65535,2863311530,3435973836,4042322160,4278255360],[(97,23),(129,47),(169,71),(10,31),(14,7),(18,1)]),([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(169,71),(6,95),(105,23),(109,23),(137,47),(141,47),(177,71),(181,71)]),([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[(60,95)]),([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(60,17),(80,32)])]
noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294945450],[(6,17)]),([7,0,65535,2863311530,3435973836,4042322160,4278255360,4294967295],[]),([7,0,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(60,89),(228,71),(284,95)]),([7,0,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(217,0),(6,89),(105,23),(109,23),(137,47),(141,47),(181,71),(229,95)]),([7,0,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(224,0)]),([7,0,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(217,0),(6,89),(105,23),(137,47),(176,0),(178,0),(177,71),(225,95),(229,0)]),([7,0,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(60,5),(104,5),(136,5),(176,5),(152,5)]),([7,0,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(76,23),(84,23),(144,23)])]
noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(60,59),(80,59),(104,59),(136,7),(112,59)]),([7,0,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(60,47),(80,47),(104,47),(136,47)]),([7,0,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(60,47),(80,47),(104,47),(176,47)]),([7,0,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(60,5),(80,5),(104,5),(176,5)]),([7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(60,59),(80,59),(104,59),(136,2),(176,0),(224,59),(244,23)]),([7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(169,1),(217,3),(6,63),(105,23),(137,47),(177,71),(181,1),(225,95),(229,3),(113,23)]),([7,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([7,0,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(169,1),(217,3),(10,32),(149,5),(185,1),(189,11),(233,3),(237,17)]),([7,0,2290649224,4008636142,4042322160,4278255360,4294901760],[(129,1),(131,1),(169,3),(171,3),(6,63),(7,63),(139,1),(143,1),(179,3),(183,3),(10,63),(11,63),(147,1),(151,1),(187,3),(191,3),(14,2),(15,2),(159,59),(195,0),(199,65),(17,1),(18,0),(19,0),(203,2),(207,89),(21,3)]),([7,0,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(60,29),(80,29),(176,29),(156,29)]),([7,0,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,5),(217,0),(6,92),(105,23),(137,47),(141,5),(177,71),(181,11),(225,95),(229,17),(145,5),(189,11),(237,17)])]
noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([7,0,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(60,23),(64,23),(68,23)]),([7,0,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([7,0,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(60,29),(64,29),(68,29),(156,29)]),([7,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,5),(169,11),(217,17),(6,32),(137,5),(141,5),(177,11),(181,11),(225,17),(229,17)]),([7,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([7,0,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(97,23),(129,47),(169,71),(217,95),(225,32),(10,104),(117,23),(145,5),(149,47),(185,11),(189,71),(237,17)]),([7,0,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(73,23),(129,47),(169,71),(217,95),(85,23),(141,47),(177,32),(225,34),(118,23),(14,92),(153,5),(157,47),(193,11),(197,71),(241,17),(245,95)]),([7,0,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([7,0,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760],[(100,5),(108,5),(140,5),(116,5),(188,23),(156,47)]),([7,0,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760],[(156,47),(260,71),(316,95)]),([7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760],[(100,59),(108,59),(116,59),(204,59)])]
noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(73,23),(129,47),(169,71),(217,95),(85,23),(118,23),(14,63),(157,47),(193,1),(197,71),(241,3),(245,95)]),([7,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295],[]),([7,0,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(73,23),(97,47),(169,71),(217,95),(150,23),(158,47),(18,89),(204,71),(206,71),(205,71),(249,0),(252,95),(254,95),(253,95)]),([7,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(73,23),(75,23),(97,47),(99,47),(129,71),(131,71),(169,95),(171,95),(6,32),(7,32),(107,5),(111,5),(139,11),(143,11),(179,17),(183,17),(9,23),(10,8),(11,8),(115,29),(119,29),(147,35),(151,35),(187,41),(191,41),(13,47),(14,2),(15,2),(155,59),(159,59),(195,65),(199,65),(17,71),(18,0),(19,0),(203,89),(207,89),(21,95)]),([7,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(73,23),(97,47),(129,71),(169,95),(238,23),(246,47),(254,71),(262,95)]),([7,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295],[]),([7,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(73,23),(75,23),(77,23),(79,23),(97,47),(99,47),(101,47),(103,47),(130,0),(129,71),(169,95),(171,0),(6,29),(7,29),(107,5),(111,5),(179,0),(183,0),(9,23),(10,5),(11,5),(115,29),(119,29),(147,23),(151,23),(187,24),(191,24),(13,47),(155,47),(159,47),(195,48),(199,48),(18,0),(19,0),(205,0),(21,0)]),([7,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(2,89),(73,23),(77,23),(97,47),(101,47),(128,0),(130,0),(129,71),(133,89),(169,95),(173,89),(217,89),(221,89),(234,23),(238,23),(242,47),(246,47),(205,0),(262,0)])]
noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([7,43690,65535,2863311530,3435973836,4042322160,4278255360],[(2,31),(97,23),(129,47),(133,5),(169,71),(173,11),(14,7),(18,1)]),([7,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,31),(97,23),(129,47),(133,5),(169,71),(173,11),(137,5),(141,5),(177,11),(181,11)]),([7,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,104),(73,23),(97,47),(99,5),(101,5),(103,5),(129,71),(131,11),(133,11),(135,11),(169,17),(107,5),(111,5),(139,11),(143,11),(10,7),(11,7),(147,1),(151,1),(13,5),(14,1),(15,1),(155,7),(159,7),(195,5),(199,5),(17,11),(203,11),(207,11)]),([7,65535,65535,2863311530,3435973836,4042322160,4278255360],[(97,23),(101,23),(129,47),(133,47),(169,71),(173,71),(10,31),(14,7),(18,1)]),([7,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(101,23),(129,47),(133,47),(169,71),(173,71)]),([7,65535,16711935,2863311530,3435973836,4042322160],[(2,0),(3,0),(99,23),(103,23),(131,47),(135,47),(5,0),(83,0),(87,0),(107,24),(111,24),(139,48),(143,48),(10,29),(11,29),(147,5),(151,5),(13,23),(14,5),(15,5),(155,29),(159,29),(17,47)]),([7,65535,16711935,2863311530,3435973836,4042322160,4278255360],[(2,0),(174,71),(6,71),(85,0),(105,23),(109,24),(137,47),(141,48),(10,31),(14,7),(194,23),(198,23),(18,1),(202,47),(206,47),(22,0)]),([7,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(57,0),(61,0),(73,0),(97,24),(101,23),(129,48),(133,47),(168,0),(169,0),(172,71),(173,71),(217,0),(221,0),(6,71),(85,0),(105,23),(109,24),(137,47),(141,48),(228,95),(229,95)])]
noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([7,65535,2290649224,2863311530,3435973836,4042322160,4278255360],[(6,59),(105,23),(137,47),(177,71),(181,1),(10,31),(113,23),(14,7),(18,1)]),([7,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(97,23),(101,23),(133,47),(169,1),(173,71),(6,59),(105,23),(137,47),(177,71),(181,1),(113,23)]),([7,65535,2863267840,2863311530,3435973836,4042322160,4278255360],[(2,17),(57,17),(73,17),(6,31),(105,23),(137,47),(141,5),(177,71),(181,11),(10,31),(14,8),(18,2),(22,0)]),([7,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(57,17),(61,17),(73,17),(97,17),(101,23),(129,19),(133,47),(169,21),(173,71),(217,17),(221,17),(6,31),(105,23),(137,47),(141,5),(177,71),(181,11)]),([7,65535,2863311530,2863311530,3435973836,4042322160,4278255360],[(6,31),(137,5),(141,5),(177,11),(181,11),(14,7),(18,1)]),([7,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(101,23),(129,5),(133,47),(169,11),(173,71),(6,31),(137,5),(141,5),(177,11),(181,11)]),([7,65535,2863311530,2863333375,3435973836,4042322160,4278255360],[(6,31),(10,104),(117,23),(145,5),(149,47),(185,11),(189,71),(14,7),(18,1)])]
noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([7,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(2,95),(101,23),(129,5),(133,47),(169,11),(173,71),(224,31),(225,31),(10,104),(117,23),(145,5),(149,47),(185,11),(189,71)]),([7,65535,2863311530,3435973836,4008636142,4042322160,4278255360],[(6,31),(85,23),(10,7),(118,23),(14,63),(157,47),(193,1),(197,71),(18,1)]),([7,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(2,95),(73,23),(77,23),(129,47),(133,47),(169,71),(173,71),(85,23),(118,23),(14,63),(157,47),(193,1),(197,71)]),([7,65535,2863311530,3435973836,4042322160,4278255360],[(75,23),(79,23),(99,47),(103,47),(131,71),(135,71),(6,31),(7,31),(107,5),(111,5),(139,11),(143,11),(9,23),(10,7),(11,7),(115,29),(119,29),(147,35),(151,35),(13,47),(14,1),(15,1),(155,59),(159,59),(17,71)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(73,23),(75,23),(77,23),(79,23),(97,47),(99,47),(101,47),(103,47),(129,71),(131,71),(133,71),(135,71),(6,32),(7,31),(107,5),(111,5),(139,11),(143,11),(9,23),(10,8),(11,7),(115,29),(119,29),(147,35),(151,35),(186,23),(187,23),(190,23),(191,23),(13,47),(14,2),(15,1),(155,59),(159,59),(194,47),(195,47),(198,47),(199,47),(17,71),(18,0),(202,71),(203,71),(206,71),(207,71)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[(2,95),(57,95),(73,101),(77,23),(97,107),(101,47),(129,113),(133,71),(169,95),(173,95),(186,23),(190,23),(194,47),(198,47),(202,71),(206,71)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(2,95),(56,32),(58,31),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(169,17),(173,17),(217,17),(238,23),(242,5),(246,47),(250,11),(254,71),(26,31)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(2,95),(73,23),(77,23),(97,47),(101,47),(129,71),(133,71),(238,23),(246,47),(254,71)])]
noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([7,65535,2863311530,3435973836,4042322160,4278255360,4294945450],[(2,17),(58,31),(6,31),(10,8),(190,23),(14,2),(194,5),(198,47),(18,0),(202,11),(206,71),(22,31)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294967295],[(6,31),(10,7),(190,23),(14,1),(198,47),(206,71)]),([7,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(2,89),(57,89),(73,91),(77,23),(97,93),(101,47),(129,89),(133,89),(169,89),(172,71),(174,71),(173,71),(217,89),(220,95),(222,95),(221,95),(146,23),(150,23),(154,47),(158,47),(249,0),(257,0)]),([7,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(73,23),(75,23),(77,23),(79,23),(97,47),(99,47),(101,47),(103,47),(134,71),(133,71),(135,71),(174,95),(173,95),(175,95),(6,32),(7,32),(107,5),(111,5),(179,0),(183,0),(9,23),(10,8),(11,8),(115,29),(119,29),(147,23),(151,23),(187,24),(191,24),(13,47),(14,2),(15,2),(155,47),(159,47),(195,48),(199,48),(18,0),(19,0),(201,0),(21,0)]),([7,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(97,23),(168,0),(170,0),(169,1),(217,3),(221,0),(6,63),(105,23),(137,47),(225,0),(229,0),(113,23)]),([7,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,89),(3,89),(73,23),(75,23),(97,47),(99,47),(128,0),(130,0),(129,71),(169,95),(171,0),(173,0),(175,0),(6,32),(7,32),(107,5),(111,5),(179,0),(183,0),(9,23),(10,8),(11,8),(115,29),(119,29),(147,23),(151,23),(187,24),(191,24),(13,47),(14,2),(15,2),(155,47),(159,47),(195,48),(199,48),(18,0),(19,0),(21,0)]),([7,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(97,23),(169,1),(173,1),(217,3),(221,3),(113,23)])]
noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([7,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(57,5),(61,5),(72,5),(73,5),(96,5),(97,5),(128,5),(129,47),(133,5),(169,7),(173,1),(217,9),(221,3),(6,39),(106,5),(105,23),(177,1),(181,7),(225,3),(229,9),(112,5),(114,5),(145,5),(237,0)]),([7,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(129,5),(169,11),(173,1),(217,17),(221,3),(6,32),(177,1),(181,1),(225,3),(229,3)]),([7,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(2,63),(60,23),(62,23),(73,23),(129,47),(169,71),(173,1),(217,95),(221,3),(6,32),(81,23),(85,23),(104,23),(105,23),(137,23),(177,25),(181,1),(225,27),(229,3),(10,8),(118,23),(149,23),(185,1),(189,25),(233,3),(237,27),(14,63),(193,1),(197,1),(241,3),(245,3)]),([7,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(2,63),(56,59),(57,59),(72,59),(73,61),(96,7),(97,59),(101,59),(129,59),(133,47),(169,83),(173,71),(217,63),(221,3),(80,59),(82,59),(81,61),(110,7),(114,23),(118,31),(14,3),(193,1),(241,3),(245,63),(201,1)]),([7,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(2,63),(56,47),(57,5),(72,47),(73,29),(96,47),(97,47),(101,47),(169,59),(173,1),(217,65),(221,3),(81,23),(114,23),(118,23),(14,2),(241,0),(245,0)]),([7,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(2,63),(56,47),(57,5),(72,47),(73,29),(97,47),(101,47),(128,47),(129,47),(169,47),(173,1),(217,48),(221,3),(81,23),(118,23),(146,23),(150,23),(193,2),(241,4),(18,89),(205,1),(249,0),(253,3)]),([7,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(2,63),(56,5),(57,5),(72,5),(73,23),(97,47),(101,5),(128,5),(129,5),(169,71),(173,1),(217,95),(221,3),(81,23),(109,5),(150,23),(18,39),(205,1),(249,0),(253,3)])]
noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([7,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(2,63),(56,59),(57,7),(72,59),(73,31),(96,2),(98,2),(97,47),(101,47),(128,0),(130,0),(129,71),(133,71),(168,59),(169,59),(217,95),(221,3),(81,23),(186,23),(188,23),(190,23),(189,23),(157,1),(206,1),(22,3),(261,3)]),([7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(3,63),(73,23),(75,23),(97,47),(129,71),(131,1),(133,1),(135,1),(169,95),(171,3),(173,3),(175,3),(6,32),(7,32),(81,23),(139,1),(143,1),(179,3),(183,3),(9,23),(10,8),(11,8),(115,23),(119,23),(147,25),(151,25),(187,27),(191,27),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(2,63),(73,23),(97,47),(129,71),(133,1),(169,95),(173,3),(81,23),(238,23),(254,1),(262,3)]),([7,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(2,63),(3,63),(131,1),(135,1),(171,3),(175,3),(6,32),(7,32),(109,5),(111,5),(137,1),(139,1),(141,11),(143,11),(177,3),(179,3),(181,17),(183,17),(10,63),(11,63),(147,1),(151,1),(187,3),(191,3),(14,2),(15,2),(159,59),(195,0),(199,65),(17,1),(18,0),(19,0),(203,2),(207,89),(21,3)]),([7,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,63),(3,63),(99,1),(103,1),(131,3),(135,3),(6,63),(7,63),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(119,59),(147,0),(151,65),(13,1),(14,0),(15,0),(155,2),(159,89),(17,3)]),([7,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(2,92),(56,29),(73,29),(77,23),(97,53),(101,47),(128,29),(129,29),(169,71),(173,11),(217,95),(221,17),(105,5),(181,11),(229,17),(116,29),(118,29),(117,53),(158,5),(18,15),(249,0),(253,0)]),([7,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,92),(3,92),(73,23),(97,47),(99,5),(101,5),(103,5),(129,71),(133,11),(135,11),(169,95),(171,0),(173,17),(175,17),(6,32),(7,32),(105,5),(107,5),(111,5),(141,11),(143,11),(179,0),(181,17),(183,17),(10,8),(11,8),(119,29),(151,35),(187,0),(191,41),(13,5),(14,2),(15,2),(155,5),(159,59),(195,6),(199,65),(18,0),(19,0),(207,89),(21,0)]),([7,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(129,5),(133,5),(169,11),(173,11),(217,17),(221,17)])]
noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([7,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(2,32),(48,23),(52,23),(73,23),(77,23),(129,23),(133,5),(169,25),(173,11),(217,27),(221,17),(10,8),(149,29),(185,1),(189,35),(233,3),(237,41)]),([7,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(2,32),(133,5),(169,1),(173,11),(217,3),(221,17),(14,63),(157,47),(193,1),(197,71),(241,3),(245,95)]),([7,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(2,32),(48,29),(52,29),(73,23),(77,23),(97,47),(101,47),(129,29),(169,11),(173,11),(217,17),(221,17),(116,29),(118,29),(117,53),(158,5),(18,15),(205,79),(249,0),(253,103)]),([7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(97,5),(99,5),(101,5),(103,5),(129,11),(131,11),(133,11),(135,11),(169,17),(171,17),(173,17),(175,17),(10,8),(11,8),(119,29),(147,1),(151,35),(187,3),(191,41),(13,5),(14,2),(15,2),(155,7),(159,59),(195,9),(199,65),(17,11),(18,0),(19,0),(203,15),(207,89),(21,17)]),([7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(2,32),(97,5),(101,5),(129,11),(133,11),(169,17),(173,17),(246,5),(254,11),(262,17)]),([7,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(99,5),(103,5),(131,11),(135,11),(169,32),(174,17),(175,17),(6,104),(7,104),(85,23),(87,23),(105,5),(107,5),(109,47),(111,47),(137,11),(139,11),(141,71),(143,71),(182,17),(181,17),(183,17),(9,23),(10,8),(11,8),(119,29),(147,1),(151,35),(191,41),(13,47),(14,2),(15,2),(155,7),(159,59),(195,5),(199,65),(17,71),(18,0),(19,0),(203,11),(207,89),(21,95)]),([7,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(2,32),(3,32),(61,23),(99,5),(101,47),(103,5),(129,32),(135,11),(169,34),(171,0),(175,17),(5,23),(6,8),(7,8),(86,23),(87,23),(111,29),(143,35),(179,0),(183,41),(10,92),(11,92),(113,5),(115,5),(117,47),(119,47),(145,11),(149,71),(151,71),(185,17),(187,0),(189,95),(191,95),(13,47),(14,2),(15,2),(155,5),(159,59),(195,6),(199,65),(17,71),(18,0),(19,0),(207,89),(21,95)])]
noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([7,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760],[(61,23),(86,23),(10,63),(149,47),(185,1),(189,71),(233,3),(237,95)]),([7,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760],[(61,23),(76,5),(78,5),(100,5),(102,5),(101,47),(169,32),(217,34),(84,5),(86,23),(140,23),(142,23),(141,23),(10,63),(113,5),(116,47),(118,47),(117,47),(145,5),(149,5),(185,5),(189,71),(233,6),(237,95),(158,47),(18,39),(205,73),(249,0),(253,97)]),([7,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760],[(61,23),(86,23),(142,23),(10,63),(116,47),(118,47),(117,47),(189,71),(233,0),(237,95),(158,47),(18,89),(204,71),(206,71),(205,71),(249,0),(252,95),(254,95),(253,95)]),([7,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760],[(61,23),(76,59),(78,7),(174,7),(84,59),(86,31),(178,23),(182,31),(10,63),(113,59),(117,47),(145,83),(149,71),(185,59),(189,59),(233,59),(237,95),(156,59),(158,59),(157,83),(198,47),(206,71),(22,3),(261,111)]),([7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(2,32),(3,32),(61,23),(103,5),(131,1),(135,11),(171,3),(175,17),(5,23),(6,8),(7,8),(86,23),(87,23),(107,23),(111,29),(139,25),(143,35),(179,27),(183,41),(10,63),(11,63),(117,47),(119,47),(145,1),(147,1),(149,71),(151,71),(185,3),(187,3),(189,95),(191,95),(13,47),(14,2),(15,2),(159,59),(195,0),(199,65),(17,71),(18,0),(19,0),(203,2),(207,89),(21,95)]),([7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760,4294967295],[(61,23),(86,23),(230,23),(10,63),(117,47),(145,1),(149,71),(185,3),(189,95),(246,47),(254,71),(262,95)]),([7,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(2,32),(3,32),(75,5),(79,5),(131,11),(135,11),(171,17),(175,17),(5,23),(6,8),(7,8),(83,29),(87,29),(110,23),(111,23),(139,35),(143,35),(179,41),(183,41),(9,47),(10,2),(11,2),(118,47),(119,47),(147,59),(151,59),(187,65),(191,65),(14,89),(15,89),(156,71),(158,71),(157,71),(159,71),(193,0),(195,0),(196,95),(198,95),(197,95),(199,95),(17,71),(18,0),(19,0),(203,89),(207,89),(21,95)]),([7,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(13,71),(14,0),(15,0),(155,89),(159,89),(17,95)])]
noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([7,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(182,23),(183,23),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(190,47),(191,47),(13,71),(14,0),(15,0),(155,89),(159,89),(198,71),(199,71),(17,95),(206,95),(207,95)]),([7,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295,4294967295],[(182,23),(190,47),(198,71),(206,95)]),([8,0,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(99,23),(129,47),(131,47),(169,71),(171,71),(217,95),(219,95),(10,32),(11,32),(147,5),(151,5),(187,11),(191,11),(235,17),(239,17),(13,23),(14,8),(15,8),(155,29),(159,29),(195,35),(199,35),(243,41),(247,41),(17,47),(18,2),(19,2),(203,59),(207,59),(251,65),(255,65),(21,71),(22,0),(23,0),(259,89),(263,89),(25,95)]),([8,0,65535,2863311530,3435973836,4042322160,4278255360],[(97,23),(99,23),(129,47),(131,47),(169,71),(171,71),(107,23),(111,23),(139,47),(143,47),(179,71),(183,71),(10,31),(11,31),(147,5),(151,5),(187,11),(191,11),(13,23),(14,7),(15,7),(155,29),(159,29),(195,35),(199,35),(17,47),(18,1),(19,1),(203,59),(207,59),(21,71)]),([8,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(99,23),(129,47),(131,47),(169,71),(171,71),(6,95),(105,23),(107,23),(109,23),(111,23),(137,47),(139,47),(141,47),(143,47),(177,71),(179,71),(181,71),(183,71),(10,32),(11,31),(147,5),(151,5),(187,11),(191,11),(13,23),(14,8),(15,7),(155,29),(159,29),(195,35),(199,35),(242,23),(243,23),(246,23),(247,23),(17,47),(18,2),(19,1),(203,59),(207,59),(250,47),(251,47),(254,47),(255,47),(21,71),(22,0),(258,71),(259,71),(262,71),(263,71)]),([8,0,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,23),(99,23),(169,1),(171,1),(217,3),(219,3),(6,63),(7,63),(105,23),(107,23),(137,47),(177,71),(179,1),(181,1),(183,1),(225,95),(227,3),(229,3),(231,3),(10,32),(11,32),(113,23),(187,1),(191,1),(235,3),(239,3),(13,23),(14,8),(15,8),(155,23),(159,23),(195,25),(199,25),(243,27),(247,27),(18,2),(19,2),(251,0),(255,0),(21,1),(22,0),(23,0),(259,2),(263,2),(25,3)])]
noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([8,0,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,5),(131,5),(169,11),(171,11),(217,17),(219,17),(6,32),(7,32),(137,5),(139,5),(141,5),(143,5),(177,11),(179,11),(181,11),(183,11),(225,17),(227,17),(229,17),(231,17),(14,8),(15,8),(159,29),(195,1),(199,35),(243,3),(247,41),(17,5),(18,2),(19,2),(203,7),(207,59),(251,9),(255,65),(21,11),(22,0),(23,0),(259,15),(263,89),(25,17)]),([8,0,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(73,23),(75,23),(129,47),(131,47),(169,71),(171,71),(217,95),(219,95),(6,32),(7,32),(85,23),(143,5),(179,1),(183,11),(227,3),(231,17),(9,23),(10,8),(11,8),(118,23),(119,23),(147,23),(151,29),(187,25),(191,35),(235,27),(239,41),(14,63),(15,63),(157,47),(159,47),(193,1),(195,1),(197,71),(199,71),(241,3),(243,3),(245,95),(247,95),(17,47),(18,2),(19,2),(207,59),(251,0),(255,65),(21,71),(22,0),(23,0),(259,2),(263,89),(25,95)]),([8,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(73,23),(75,23),(97,47),(99,47),(129,71),(131,71),(169,95),(171,95),(6,32),(7,32),(107,5),(111,5),(139,11),(143,11),(179,17),(183,17),(9,23),(10,8),(11,8),(115,29),(119,29),(147,35),(151,35),(187,41),(191,41),(13,47),(14,2),(15,2),(155,59),(159,59),(195,65),(199,65),(17,71),(18,0),(19,0),(203,89),(207,89),(21,95)]),([8,0,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(73,23),(75,23),(97,47),(99,47),(129,71),(131,71),(169,95),(171,95),(6,32),(7,32),(107,5),(111,5),(139,11),(143,11),(179,17),(183,17),(9,23),(10,8),(11,8),(115,29),(119,29),(147,35),(151,35),(187,41),(191,41),(238,23),(239,23),(13,47),(14,2),(15,2),(155,59),(159,59),(195,65),(199,65),(246,47),(247,47),(17,71),(18,0),(19,0),(203,89),(207,89),(254,71),(255,71),(21,95),(262,95),(263,95)]),([8,65535,2863311530,3435973836,4042322160,4278255360],[(75,23),(79,23),(99,47),(103,47),(131,71),(135,71),(6,31),(7,31),(107,5),(111,5),(139,11),(143,11),(9,23),(10,7),(11,7),(115,29),(119,29),(147,35),(151,35),(13,47),(14,1),(15,1),(155,59),(159,59),(17,71)]),([8,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,95),(73,23),(75,23),(77,23),(79,23),(97,47),(99,47),(101,47),(103,47),(129,71),(131,71),(133,71),(135,71),(6,32),(7,31),(107,5),(111,5),(139,11),(143,11),(9,23),(10,8),(11,7),(115,29),(119,29),(147,35),(151,35),(186,23),(187,23),(190,23),(191,23),(13,47),(14,2),(15,1),(155,59),(159,59),(194,47),(195,47),(198,47),(199,47),(17,71),(18,0),(202,71),(203,71),(206,71),(207,71)])]
noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([8,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,63),(3,63),(73,23),(75,23),(97,47),(129,71),(131,1),(133,1),(135,1),(169,95),(171,3),(173,3),(175,3),(6,32),(7,32),(81,23),(139,1),(143,1),(179,3),(183,3),(9,23),(10,8),(11,8),(115,23),(119,23),(147,25),(151,25),(187,27),(191,27),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([8,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(97,5),(99,5),(101,5),(103,5),(129,11),(131,11),(133,11),(135,11),(169,17),(171,17),(173,17),(175,17),(10,8),(11,8),(119,29),(147,1),(151,35),(187,3),(191,41),(13,5),(14,2),(15,2),(155,7),(159,59),(195,9),(199,65),(17,11),(18,0),(19,0),(203,15),(207,89),(21,17)]),([8,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(2,32),(3,32),(61,23),(103,5),(131,1),(135,11),(171,3),(175,17),(5,23),(6,8),(7,8),(86,23),(87,23),(107,23),(111,29),(139,25),(143,35),(179,27),(183,41),(10,63),(11,63),(117,47),(119,47),(145,1),(147,1),(149,71),(151,71),(185,3),(187,3),(189,95),(191,95),(13,47),(14,2),(15,2),(159,59),(195,0),(199,65),(17,71),(18,0),(19,0),(203,2),(207,89),(21,95)]),([8,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(13,71),(14,0),(15,0),(155,89),(159,89),(17,95)]),([8,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(182,23),(183,23),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(190,47),(191,47),(13,71),(14,0),(15,0),(155,89),(159,89),(198,71),(199,71),(17,95),(206,95),(207,95)]),([9,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(73,23),(75,23),(97,47),(99,47),(129,71),(131,71),(169,95),(171,95),(6,32),(7,32),(107,5),(111,5),(139,11),(143,11),(179,17),(183,17),(9,23),(10,8),(11,8),(115,29),(119,29),(147,35),(151,35),(187,41),(191,41),(13,47),(14,2),(15,2),(155,59),(159,59),(195,65),(199,65),(17,71),(18,0),(19,0),(203,89),(207,89),(21,95)]),([9,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,32),(3,32),(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(5,23),(6,8),(7,8),(83,29),(87,29),(107,35),(111,35),(139,41),(143,41),(9,47),(10,2),(11,2),(115,59),(119,59),(147,65),(151,65),(13,71),(14,0),(15,0),(155,89),(159,89),(17,95)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ (K_1 ++ K_2)) ++ ((K_3 ++ K_4) ++ (K_5 ++ K_6))) ++ (((K_7 ++ K_8) ++ (K_9 ++ K_10)) ++ ((K_11 ++ K_12) ++ (K_13 ++ K_14)))) ++ (((K_15 ++ (K_16 ++ K_17)) ++ ((K_18 ++ K_19) ++ (K_20 ++ K_21))) ++ (((K_22 ++ K_23) ++ (K_24 ++ K_25)) ++ ((K_26 ++ K_27) ++ (K_28 ++ K_29))))) ++ ((((K_30 ++ (K_31 ++ K_32)) ++ ((K_33 ++ K_34) ++ (K_35 ++ K_36))) ++ (((K_37 ++ K_38) ++ (K_39 ++ K_40)) ++ ((K_41 ++ K_42) ++ (K_43 ++ K_44)))) ++ (((K_45 ++ (K_46 ++ K_47)) ++ ((K_48 ++ K_49) ++ (K_50 ++ K_51))) ++ (((K_52 ++ K_53) ++ (K_54 ++ K_55)) ++ ((K_56 ++ K_57) ++ (K_58 ++ K_59)))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app (all_app c_3 c_4) (all_app c_5 c_6))) (all_app (all_app (all_app c_7 c_8) (all_app c_9 c_10)) (all_app (all_app c_11 c_12) (all_app c_13 c_14)))) (all_app (all_app (all_app c_15 (all_app c_16 c_17)) (all_app (all_app c_18 c_19) (all_app c_20 c_21))) (all_app (all_app (all_app c_22 c_23) (all_app c_24 c_25)) (all_app (all_app c_26 c_27) (all_app c_28 c_29))))) (all_app (all_app (all_app (all_app c_30 (all_app c_31 c_32)) (all_app (all_app c_33 c_34) (all_app c_35 c_36))) (all_app (all_app (all_app c_37 c_38) (all_app c_39 c_40)) (all_app (all_app c_41 c_42) (all_app c_43 c_44)))) (all_app (all_app (all_app c_45 (all_app c_46 c_47)) (all_app (all_app c_48 c_49) (all_app c_50 c_51))) (all_app (all_app (all_app c_52 c_53) (all_app c_54 c_55)) (all_app (all_app c_56 c_57) (all_app c_58 c_59)))))))

theorem base : ∀ s : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (idx6 (Function.update (x) 5 false))) s → 10 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 9 10 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

end B0

theorem lb : ∀ s : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (idx6 x)) s → 11 ≤ s := by
  intro s h0
  obtain ⟨s1, c1, h1⟩ := one_gate_at 5 _ (5 : Fin 6) false s ⟨pt 6 3, by decide +kernel⟩ ⟨fun _ => false, fun _ => true, by decide +kernel⟩ h0
  have hb2 := B0.base s1 h1
  omega

set_option maxRecDepth 100000 in
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  simp only [sum_eq] at h ⊢
  exact ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [15, 10]⟩], 16⟩, by simp [PEqualNP.MetaComplexity.Monotone2], le_trans (by decide) (lb s h), by decide +kernel⟩

end R0

end PEqualNP.Outside.L_meta_12314_aux

open PEqualNP.Outside.L_meta_12314_aux in
theorem PEqualNP.Outside.L_meta_12314 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  R0.main
