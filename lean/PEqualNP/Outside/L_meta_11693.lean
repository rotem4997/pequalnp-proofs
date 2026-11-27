import Mathlib
import PEqualNP.Defs
-- Restrictions use L-meta-8451. Published base certificates are from L-meta-9148.
namespace PEqualNP.Outside.L_meta_11693.Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
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
end PEqualNP.Outside.L_meta_11693.Pin

namespace PEqualNP.Outside.L_meta_11693.Base0

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


def six : BFn 6 := fun x => decide (∃ i < ([0, 3, 0, 4, 0, 5, 1, 2, 1, 3, 1, 5, 2, 3, 2, 4] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 0, 5, 1, 2, 1, 3, 1, 5, 2, 3, 2, 4] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 0, 5, 1, 2, 1, 3, 1, 5, 2, 3, 2, 4] : List ℕ).getD (2 * i + 1) 0) false = true)

def edgeFn : BFn 6 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

def sampleRows : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 8, 8, 8, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 24, 24, 24, 32, 32, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 9, 17, 33, 6, 10, 34, 6, 7, 9, 10, 11, 12, 17, 19, 20, 33, 34, 35, 6, 12, 20, 6, 7, 9, 10, 12, 13, 17, 20, 21, 33, 34, 37, 9, 10, 12, 17, 20, 6, 9, 10, 12, 17, 19, 20, 22, 26, 33, 34, 50, 25, 26, 28, 33, 34, 6, 9, 10, 12, 17, 20, 33, 34, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 6, 9, 10, 12, 17, 20, 33, 34, 57, 58, 60]
def inputWords : List Nat := [0x2a448a9248c936cc2b5870000000000001ffe3ffc7, 0x50a9142cb6944816726f8000000003ffc00003fff8, 0x8532794903269367c48c800007ff800001fffc0000, 0xe1c3a071c438e07880f11ffe38001c000e00000000, 0xe61c4181e7c3038107002fffc0001ffff000000000, 0xf81ffe0638001c0038024fffffffe0000000000000]

def bankWordChunk (i : Nat) : Nat := (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x8000042248000000000000000003ffc0000000000080000002000000000000000000000000000000000000020000000000000000000000000000000000000000004000000000000000000000000000000000000000000400080000000000000000000000000000000000000020000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000 else (if i < 2 then 0x20180802041246400c80000000000001ffe000000020100802840006624c800000000000000003ffc00020100802040006400c80000000000000000000000000100000000000000000000000000000000000000000080000801244224800000000000001ffe3ffc00000080000001244000800000000000001ffe00000000008000000100000000000000000000000000000000000000200000000000000000000000000000000 else 0x2c000b0c4d960980371300000001ffffe0003ffff0240009040c922cc035830000000000001ffe3ffc701e00078003ce07ec0fd9000000000000fffffffff01c3a071c438e07880f1100038001c000e0000000001c3a0700038e07880f11000380000000e0000000001c00071c438e07880f1100000001c000e000000000122384800249066c08c800007ff800001fffc000000a0002886944016426d8000000003ffc00003fff8)) else (if i < 5 then (if i < 4 then 0x74001d1416ba3e98590300000001c003ffffc00070620018803c70387470ca000000003fff1ffffffff061c4181e7c3038107002001c0001ffff000000000061c418023c3038107002001c00003fff00000000006000181c7c303810700200000001ffff00000000005a001698736c133c4a5800000001ffffe001c00380520014903268367c48c80000000000001fffc00000430590803061307440c800007ff800001fffc0000 else 0x11a3346c1034c832d0a780003fffe0000e001c003810a1142c10144816706f800000000000000003fff81028140c32840806720e8000000003ffc00003fff80e144b82094317810d006001c7ffe00031fffc00070a040a8208c116842b0860000000000001ffe3ffc70942aa520828b468889050003fffe0000ffffc000708408a120808344c285850000000000001ffe3ffc707e001f9c7ffe3ffc7fdb00000001fffffffffffff) else (if i < 6 then 0x1a0c068638c10c803b026001c00063fff00003ffff19e3be7e183cfc7ef8ffd0003fffe0000fffffffff18c1863618186c1838735000380060000e0003ffff18201e0e18041c06780ec00007ffe00001ffffffff181ffe0638001c0038024001ffffe0000000000000181c5e0638001c0038024001c7ffe00000000000001803be0618001c00380240003fffe00000000000001438550c3306090354068001c7ffe3fff0001c0038 else 0x2040801040082048005010000000000000000000002004000000000000000000000000000000000000002000800000000000000000000000000000000000002000000040000000000000000000000000000000001ffffffe3bfffffffffff001ffffe3ffffffffffff1ffc5ffffffffffffffff001c7ffffffffffffffff1fe3bfffdffffffffffff0003fffffffffffffffff1e3c5f8e3bc71f877f0ee001c7ffe3fff1ffffffff))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x28048a020800140028004000000000000000000000261c418063c3038107002001c00003fff0000000002244809040c922c8035030000000000000000000002204088040c112c4030820000000000001ffe000002204008040c102842348200000000000000003ffc02204008040c1028003002000000000000000000000204088104008324c005810000000000001ffe00000204080104088204c2258100000000000000003ffc0 else 0x2a448a9248c934882b50700000000000000003ffc72a448a92484936c8091070000000000001ffe000072a44829248c924882b50700000000000000003ffc72a4482924849248809107ffff8007c003e000000072a048a8248c116802b00600000000000000000000028448a12480834482850500000000000000000000028048a02088014042a48400000000000000003ffc028048a0208001644280840000000000001ffe00000) else (if i < 10 then 0x2a448a9248c936cc2b5870000000000001ffe3ffc72a448a9248c936cc2b1870000000000001ffe3ffc72a448a9248c936cc0b5870000000000001ffe3ffc72a448a9248c936c82b5070000000000001ffe3ffc72a448a9248c936c82b5070000000000000000000002a448a9248c936c80b1070000000000001ffe000072a448a9248c9368c2b5870000000000001ffe3ffc72a448a9248c934cc2b5870000000000001ffe3ffc7 else 0x3be7befe58fdfefefbfff0003fffe0000fffffffff3ae59ebe58dd7ede7b7ff0000000000001ffe3ffff381cde0638001c0038024001c7ffe00000000000002fe48bfbcffff7ffeffdf00000001fffffffffffff2f648bdb4befb7efefdcf0000000000001ffffffc72a649a9a4acd36ce6b5cf0000000000001ffe3ffc72a449a9248c936cc2b5870000000000001ffe3ffc72a448a924ac936cc2b5870000000000001ffe3ffc7)) else (if i < 13 then (if i < 12 then 0x40810020841040100061000000000000000000000040281008a6840006420c8000000003ffc00000000040080000a680000422480000000003ffc00003ffc040080000a680000002000000000003ffc0000000004008000020000000000000000000000000000000004001000000000000000000000000000000000000004000000084000000000000000000000000000000003e7cdf9e7bcf3fcf7f5ef001c7ffe3fff1ffffffff else 0x50091404b680080032020000000003ffc0000000005009140430800804324a000000000000000003ffc0500914043000080030020000000000000000000000461c4180a7c3038107002001c00003fff00000000041c3a0708438e07880f11000380000000e0000000040a1102886144016406d800000000000000000000040890020a690401002610000000003ffc00000000040810020849040142269000000000000000003ffc0) else (if i < 14 then 0x50a9142cb6144816706f800000000000000000000050a9142cb6144816502f8000000003ffc00000003850a9142cb614481250278000000003ffc00000003850a9142cb4944816726f8000000003ffc00003fff850891424b41048103063000000000000000000000050890424b490481032630000000003ffc00003fff850890424b410481010230ffff8007ffffe000000385029140c32040806700e8000000000000000000000 else 0x50a91c2cb6945a56726f8000000003ffc1ffe3fff850a91c2cb6945816726f8000000003ffc00003fff850a9142cb6944a16726f8000000003ffc00003fff850a9142cb6944856726f8000000003ffc00003fff850a9142cb6944816726f8000000003ffc00003fff850a9142cb6944816722f8000000003ffc00003fff850a9142cb6944816526f8000000003ffc00003fff850a9142cb6144816706f8000000003ffc00003fff8)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0x61c3a070c438e07880f11ffe38001c000e0000000060c18030c41860580071100000000000000000000060c18030c418601800711ffe38001c000e000000005ebd5faebfd75f977f6fe001c7ffe3fff1ffffffff59ebbe7ebebcfc7efaffd0003fffe3ffcfffffffff581d5e0638001c0038024001c7ffe0000000000000580bbe0638001c00380240003fffe000000000000057e915fdf7ffebfff7ffb00000001fffffffffffff else 0x6ac58ab2ccd976dc2b7970000000000001ffe3ffc76a4c8a92eec936cc2b587000000003ffc1ffe3ffc76a4c8a9268c936cc2b5870000000000001ffe3ffc76a458a9248c936cc2b5870000000000001ffe3ffc76a448a92ccc936cc2b5870000000000001ffe3ffc7661c4180e7c3038107002fffc0001ffff000000000620c0080e6c1028003002000000003ffc000000000620c0080e4c1008003002fffc0001ffff000000000) else (if i < 18 then 0x780d860638000c0038024ffff8006000000000000072ed94bcf6dd6ade737fb000000003ffc00003fff872ad14acf6d54a96736fa000000003ffc00003fff870e9943cf69c685e727f9000000003ffc00003fff870ad142cb6944816726f8000000003ffc00003fff870a9942cb6944816726f8000000003ffc00003fff870a9142cf6944816726f8000000003ffc00003fff86ae59abacedd76de6b7df0000000000001ffe3ffc7 else 0x7a4d9e9678c93ecc3b5a70000000000001ffe3ffc778ed9e3efe9c7c5e7a7fd000000003ffc00003fff878cd9e36fc187c583873500000000000000000000078ad9e2ebe945c167a6fc000000003ffc00003fff8781dde0638001c0038024fffffffe0000000000000780fbe0638001c0038024fffffffe0000000000000780d9e0638001c0038024000000000000000000000780d8e0638001c0038024ffff80060000000000000)) else (if i < 21 then (if i < 20 then 0x7aed9ebefedd7ede7b7ff000000003ffc1ffe3ffff7aed96befedd6c9e7b7ffffff8007ffffe0003ffff7aed96befedd6c9e7b7ff000000003ffc00003ffff7acd9eb6fcd97edc3b7b70000000000001ffe3ffc77acd8eb6fcd97edc3b7b7ffff8007fffffffe3ffff7acd86b6fcd96c983b737ffff8007ffffe0003ffff7aad9eaefed55e967b6fe000000003ffc00003fff87a6d9e9e7acd3ece7b5ef0000000000001ffe3ffc7 else 0x80127800000012440008000007ff800001ffe0000080127800000010000000000007ff800000000000008010400000000000000000000000000000000000008002200000000000000000000000000000000000008000000100000000000000000000000000000000007fed87ffffffeffffffffffff8007fffffffffffff7efddfbeffdf7f9f7f7fffffffffffffffffffffff7befbefefcfdfcfefbffffffffffffffffffffffff) else (if i < 22 then 0x8410490103021345040800000000000001ffe0000084104101030203010400000000000000000000000081c22071c438e07880f1100000001c000e000000008122304902248066c08c800000000000000000000081127841002090608080000007ff800000000000008102284100209264808800000000000001ffe000008102204100208060808000000000000000000000008032780802041006400c800007ff80000000000000 else 0x8532714903268127c48c800007ff800000001c00008532714903268123c484800007ff800000001c00008532694903269367c48c800007ff800001fffc000085126941012293618480000007ff800001fffc0000851261410322836184800000000000000000000000851261410122812184800ffffffffc003e001c00008430510903060307440c800000000000000000000084127901030213010400000007ff80000000000000))) else (if i < 27 then (if i < 25 then (if i < 24 then 0x8532794903a69367c68c800007ff800001fffc00008532794903269367e48c800007ff800001fffc00008532794903269367c4cc800007ff800001fffc00008532794903269367c48c800007ff800001fffc00008532794903269327c48c800007ff800001fffc00008532794903269167c48c800007ff800001fffc00008532714903268367c48c800007ff800001fffc00008532714903268367c48c8000000000000000000000 else 0xa142a0514028a06880901ffe38001c000e000000009f3e7fcf3be79fe7ff8ee001c7ffe3fff1ffffffff9df3ff7f1b3eff7ffcffd0003fffe0000fffffffff981e7e0638001c0038024001c7ffe000000000000087f279f9c7fff3ffc7fdb00007ff9fffffffffffff861c418123c3038107002001c00003fff00000000086104181c7c303810700200000001ffff0000000008532794903a69367e6cc800007ff800001ffffffc0) else (if i < 26 then 0xa614418141c3038107002fffc0001c003000000000a61441814143038105002fffc0001c003000000000a572f959432eb36fc4dc900007ff800001fffc0000a536794903269367c48c800007ff800001fffc0000a532f94903269367c48c800007ff800001fffc0000a532794943269367c48c800007ff800001fffc0000a1c2a071c438e07880f11ffe38001c000e00000000a142a0514028a06880d01000000000000000000000 else 0xa816fa02080014002800400007ff80000000000000a816ea020800140008004fffffffe0000000000000a776f9d943efb3efc7dcb00007ff800001fffc0000a756e1d143eba3e987d03000000000000000000000a73679c943e793e7c78ca00007ff800001fffc0000a61c418163c3038107002fffc0001ffff000000000a6144181c7c3038107002fffc0001ffff000000000a614418143c3038107002000000000000000000000)) else (if i < 29 then (if i < 28 then 0xad76fb5b4b2eb76fecdcd00007ff800001fffc0000ad36fb4b0b269767ec8cc00007ff800001fffc0000ab66badb4aedb6eeebdcf0000000000001ffe3ffc7ab46aad348e9b6ecabd870000000000001ffe3ffc7aa56fa9248c936cc2b58700007ff800001ffe3ffc7aa54ca9248c936cc2b5870000000000001ffe3ffc7aa46aa9248c936cc2b5870000000000001ffe3ffc7aa448a9348c936cc2b5870000000000001ffe3ffc7 else 0xaf76fbdb4b6fb7efcd9cfffffffffc003ffffc0007af76fbdb4b6fb7efcd9cf00007ff800001fffc0007af56ebd34bebb7edafd870000000000001ffe3ffc7af56ebd349ebb7edafd87ffffffffc003fffffffc7af56ebd3496bb7e98d907ffffffffc003ffffc0007af36fbcb4be797e7ef8ce00007ff800001fffc0000ae74db9b4bcf37cf6f5cf0000000000001ffe3ffc7ae54cb934bcb37cd2f5870000000000001ffe3ffc7) else (if i < 30 then 0xc1c32071c438e07880f11ffe38001c000e00000000c18320618430c07080e10000000000000000000000c18320618430c03080a10ffe38001c000e00000000bff7ffff597ffffffdfffffffffffc003fffffffffbf7effdf7befbfefff9effffffffffffffffffffffb81efe0638001c0038024fffffffe0000000000000aff6ebfbcffff7ffcffdffffffffffffffffffffffaf76fbdb4befb7efefdcf00007ff800001ffffffc7 else 0xc5b379698736d377c4ed800007ff800001fffc0000c53a7949a7a69367c68c800007ff83ffc1fffc0000c53a794923269367c48c800007ff800001fffc0000c533794903269367c48c800007ff800001fffc0000c532794987269367c48c800007ff800001fffc0000c4184101a782030106000000000003ffc000000000c4184101a702010104000fffc0001ffff000000000c1c3a0718438e07880f11ffe38001c000e00000000))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then 0xd0bb7c2cb6945816726f800007ff83ffc00003fff8d0b9542cb6944816726f8000000003ffc00003fff8d0ab342cb6944816726f8000000003ffc00003fff8d0a9142db6944816726f8000000003ffc00003fff8d01b7c04300018003002000007ff80000000000000d01b74043000080010020fffffffe0000000000000c61c4181a7c3038107002fffc0001ffff000000000c6184181e7c3038107002fffc0001ffff000000000 else 0xd5bb7d6db736db77f4ef800007ff800001fffc0000d5bb7d6db736db77d4af8ffffffffffffffffc0038d5bb756db7b6cb77f6ef8000000003ffc00003fff8d5bb756db7b6c937f6ef8ffffffffffffe001ffff8d5bb756db736c933d4a78ffffffffffffe001c0038d53b7d4d33269b67f48e800007ff800001fffc0000d4b9552db7964b17766f8000000003ffc00003fff8d1ab346db6b4c876f2ef8000000003ffc00003fff8) else (if i < 34 then 0xe0000001c400000000000ffe00001c000000000000e00000000000000000000ffe000000000000000000dfbf7fefbff7dfb7ffafefffffffffffffffffffffddfbff7fbf3efd7ffcffdfffffffffffffffffffffd81f7e0638001c0038024fffffffe0000000000000d81bfe0638001c0038024fffffffe0000000000000d7fb75fdf7ffebffd7ffbfffffffffffffffffffffd5bb7d6db7b6db77f6ef800007ff83ffc1fffffff8 else 0xe01e78002000100000000fffc7ff80000000000000e01c4001e400000000000fffc0001c000000000000e01c4000a680000002000fffc00003ffc000000000e01c40002000000000000fffc00000000000000000e013f8000000100000000ffe3fff80000000000000e0080001e680000002000ffe00001fffc000000000e003a001c400000000000ffe38001c000000000000e003a0000000000000000ffe380000000000000000)) else (if i < 37 then (if i < 36 then 0xe1c3a071c438e07880f11000000000000000000000e103a0410020806080800ffe380000000000000000e1022041c420806080800ffe00001c000000000000e083a0208410401000610ffe380000000000000000e0810021c410401000610ffe00001c000000000000e043a0104008204800501ffe380000000000000000e0408011c408204800501ffe00001c000000000000e01fe0002000000000000ffff80000000000000000 else 0xe1c3a871c438f07880f11ffe38001c000e00000000e1c3a071c638e07880f11ffe38001c000e00000000e1c3a071c4b8e07ca2f91ffe38001c000e0003ffc0e1c3a071c4b8e07882f11ffe38001c000e00000000e1c3a071c438e27880f11ffe38001c000e00000000e1c3a071c438e07c80f91ffe38001c000e00000000e1c3a071c438e078a0f11ffe38001c000e00000000e1c3a071c438e07880f11ffe38001c000e00000000) else (if i < 38 then 0xe1dfe071e438e07880f11ffff8001c000e00000000e1d3f871c438f07880f11ffe3fff9c000e00000000e1d3e071c438e07880f11ffe38001c000e00000000e1cba071e6b8e07882f11ffe38001fffce00000000e1cba071e438e07880f11ffe38001c000e00000000e1c7a071c438e07880f11ffe38001c000e00000000e1c3b071c438e07880f11ffe38001c000e00000000e1c3a871c438f27c80f91ffe38001c000fffe00000 else 0xe5327949c7269367c48c8ffe07ff9c0001fffc0000e41c41012302030104000fffc00000000000000000e4104101c702030104000ffe00001c000000000000e3dfe0f1e4f9e2f883f13ffff8001c000e00000000e3c7a0f1c4f9e2f883f13ffe38001c000e00000000e21c408060c1028003002fffc00000000000000000e2040081c4c1028003002ffe00001c000000000000e1e3b079c63ce07ec0fd9ffe38001c000e00000000))) else (if i < 43 then (if i < 41 then (if i < 40 then 0xe6144181c7c3038107002ffe00001c000000000000e5f3f979c73ef37fc4fd9ffe3fff9c000ffffc0000e5f3f979c73ef37fc4fd900007ff800001fffc0000e5f3f179c73ee37fc4fd9ffe38001c000e00000000e5dfe171e73ae37984f11ffff8001c000e00000000e5d3e171c73ae37984f11ffe38001c000e00000000e53e794923269367c48c8fffc7ff800001fffc0000e533f94903269367c48c8ffe3fff800001fffc0000 else 0xe61c4181e7c3038507082fffc0001ffff000000000e61c4181e7c3038127002fffc0001ffff000000000e61c4181e7c3038107402fffc0001ffff000000000e61c4181e7c3038107002fffc0001ffff000000000e61c4181e7c3038107002000000003ffc000000000e61c4181e5c3038107002fffc0001ffff000000000e61c418163c3038107002fffc00000000000000000e61c418023c3038107002fffc00003fff000000000) else (if i < 42 then 0xe61e6181e7c3038107002fffc0001ffff000000000e61d4181e7c3038107002fffc0001ffff000000000e61cc181e7c3038107002fffc0001ffff000000000e61c5181e7c3038107002fffc0001ffff000000000e61c4981e7c313c507082fffc0001ffff1ffe00000e61c4981e7c3138107002fffc0001ffff000000000e61c4181e7c303c107002fffc0001ffff000000000e61c4181e7c3038527482fffc0001ffff00003ffc0 else 0xe6bd51a9e7d74397476dafffc0001ffff000000000e69fe1a1e7d3439107612ffff8001ffff000000000e69d41a1e7d3439107612fffc0001ffff000000000e65fe191e7cb23c907503ffff8001ffff000000000e65cc191e7cb23c907503fffc0001ffff000000000e63c5189e7c70387470cafffc0001ffff000000000e61fe181e7c3038107002ffff8001ffff000000000e61e7981e7c3138107002fffc7ff9ffff000000000)) else (if i < 45 then (if i < 44 then 0xe75ee1d1e7eba3e987d03fffc0001ffff000000000e75ee1d1e7eba3e987903ffff8001ffffe00000000e73e79c9e7e793e7c78cafffc7ff9ffff1fffc0000e73e71c9e7e783e7c78cafffc0001ffff000000000e71fe1c1e7e383e187802ffff8001ffff000000000e71e61c1e7e383e187802fffc0001ffff000000000e6ddc1b1e7db63d907713fffc0001ffff000000000e6ddc1b1e7db639907713ffff8001ffffe00000000 else 0xe7dfe1f1e7fbe3f987f13ffff8001ffffe00000000e7dfe1f1e7fbe3f987f13ffff8001c000e00000000e7dc41f1e7fbe3f987f13fffc0001ffffe00000000e7d7e1f1c7fbe3f987f13ffe38001c000e00000000e7d7e1f1c5fbe3f987f13ffff8001c003e00000000e7d7e1f1c57be3f985f13ffff8001c003e00000000e79f61e1e7f3c3f187e12fffc0001ffff000000000e79f61e1e7f3c3b187a12ffff8001ffffe00000000) else (if i < 46 then 0xe9dfea73ec38f478a8f15ffff8001c000e00000000e9c7aa73cc38f478a8f15ffe38001c000e00000000e81cca022800140028004fffc00000000000000000e807aa020800140028004ffe380000000000000000e7fff9f9e7fff3ffc7fdbfffffff9ffffffffc0000e7fff1f9e7ffe3ffc7fdbffff8001ffffe00000000e7fc41f9e7ffe3ffc7fdbfffc0001fffffffffffffe7e3a1f9c7ffe3ffc7fdbffe38001fffffffffffff else 0xee1feb83efc317812f006ffff8001ffff000000000ee1ccb83efc317812f006fffc0001ffff000000000ebc7aaf3ccf9f6fcabf97ffe38001c000fffe3ffc7ebc7aaf3ccf9f6fcabf970000000000001ffe3ffc7ebc7aaf3ccf9f6f8abf17ffe38001c000e00000000ea5cca9268c936cc2b587fffc000000001ffe3ffc7ea47aa9248c936cc2b587ffe3800000001ffe3ffc7ea448a93ccc936cc2b587ffe00001c0001ffe3ffc7)))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then 0xeff7fbfbcffff7ffeffdfffe3fff9c000fffffffc7efdfebf3effbf7fdaff97ffff8001fffffffe3ffc7efdfebf3effbf7f9aff17ffff8001ffffe00000000efd7ebf3cd7bf7f98df17ffffffffc003ffffc0007ef7efbdbefefb7efefdcffffc7ff9ffff1ffffffc7ef5eebd3efebb7e98f907ffffffffffffffffc0007ee5ccb93efcb37cd2f587fffc0001ffff1ffe3ffc7ee5ccb93efcb37c92f507fffc0001ffff000000000 else 0xf1ebb47df63ce87ef0ff9ffe38001c000e00000000f1dff475f438e878b0f31ffff8001c000e00000000f1cbb475f438e878b0f31ffe38001c000e00000000f0bd542cb6944816726f8fffc00003ffc00003fff8f0abb42cb6944816726f8ffe380003ffc00003fff8f0a9142df6944816726f8ffe00001fffc00003fff8f01d54043000080030020fffc00000000000000000f00bb4043000080030020ffe380000000000000000) else (if i < 50 then 0xf69d45a5f7d34b9117232ffff8007ffffe00000038f63d558df7c70b87770eafffc0001ffff000000000f61ff585f7c30b8137022ffff8001ffff000000000f61d5585f7c30b8137022fffc0001ffff000000000f5fbfd7df7befb7ff6ff9ffe3fff9fffcffffffff8f5fbf57df73ee97bd4f79ffffffffffffe001c0038f1ebb47df6bce87ef2ff9ffe38001fffce0003fff8f1ebb47df6bce87ef2ff9000000003ffc00003fff8 else 0xf7fff5fdf7ffebfff7ffbffff8001ffffe0003fff8f7dff5f5f7fbebf9b7f33ffff8001ffffe00000000f7bf7dedf7f7dbf7f7efafffc7ff9ffff1fffffff8f7bf75edf7f7cbb3d7a7affffffffffffe001c0038f6bd55adf7d74b97776fafffc0001ffff00003fff8f6bd55adf7d74b97776fa000000003ffc00003fff8f6bd55adf7d74b935727afffc0001ffff000000038f69d55a5f7d34b9137632fffc0001ffff000000000)) else (if i < 53 then (if i < 52 then 0xf81ffe0638001c04380a4fffffffe0000000000000f81ffe0638001c0038424fffffffe0000000000000f81ffe0638001c0038024fffffffe0000000000000f81ffe0638001c003802400007ff80000000000000f81fee0638001c0038024fffffffe0000000000000f81dde0638001c0038024fffc00000000000000000f81c5e0638001c0038024fffc7ffe0000000000000f80fbe0638001c0038024ffe380000000000000000 else 0xf81ffe06bc001c0038024fffffffe0000000000000f81ffe0678001c0038024fffffffe0000000000000f81ffe063a001c0038024fffffffe0000000000000f81ffe0638801c043a4a4fffffffe000000003ffc0f81ffe0638801c003a024fffffffe0000000000000f81ffe0638001e44380a4fffffffe00001ffe00000f81ffe0638001e0038024fffffffe0000000000000f81ffe0638001c4038024fffffffe0000000000000) else (if i < 54 then 0xf89ffe27fc105c1038634ffffffffc000000000000f89ffe26bc105c1038634fffffffe0000000000000f85ffe17fc083c4838525ffffffffc000000000000f85ffe1678083c4838525fffffffe0000000000000f83ffe0e3a041c06780ecfffffffe0000000000000f81ffe07fc001c0038024ffffffffc000000000000f81ffe0738001c0038024fffffffe0000000000000f81ffe06be801c003a024fffffffe3ffc000000000 else 0xf95ffe577828bc68b8925ffffffffc000e00000000f93ffe4f3a249c66f88ecfffffffe0000000000000f91ffe47fc209c60b8824ffffffffc000000000000f91ffe4738209c60b8824fffffffe0000000000000f8dffe36fc187c5838735fffffffe0000000000000f8dffe36fc187c1838735ffffffffc000e00000000f8bffe2ebe945c167a6fcfffffffe3ffc00003fff8f8bffe2ebe145c16786fcfffffffe0000000000000))) else (if i < 59 then (if i < 57 then (if i < 56 then 0xf9dffe77fc38fc78b8f35ffff8001c000e00000000f9dffe763838fc78b8f35fffffffe0000e00000000f9cfbe77fc38fc78b8f35ffe38001c000e00000000f9cfae77fc38fc78b8f35ffff8007c000e00000000f9cfa677fc38ec78b8f35ffff8007c000e00000000f99ffe67bc30dc70b8e34fffffffe0000000000000f99ffe67bc30dc30b8a34ffffffffc000e00000000f95ffe577828bc68b8d25fffffffe0000000000000 else 0xfa5ffe9678c93ec83b527fffffffe0000000000000fa1ffe87fcc11e803b026ffffffffc000000000000fa1ffe8678c11e803b026fffffffe0000000000000f9fffe7ffebcfc7efaffdfffffffffffce0003fff8f9fffe7ffe3cfc7ef8ffdffffffffc000e00000000f9fffe7e383cfc7ef8ffdfffffffe0000ffffffffff9e3be7fdc3cfc7ef8ffdffe3ffffc000ffffffffff9dffe77fc38fc78b8f35ffffffffc000e00000000) else (if i < 58 then 0xfc1fff073b021f013c024fffffffe0000000000000fbefbefffefdfefefbfffffe38001fffcfffe3fffffbdffef7fcf9fefcbbfb7ffffffffc000fffe3ffc7fbdffef7fcf9fef8bbf37ffffffffc000e00000000fbcfa6f7fcf9ecf8bbf37ffff8007ffffe0003fffffafffebefedd7ede7b7fffffffffe3ffc1ffe3fffffadffeb6fcd97c983b737ffffffffffffe0003fffffa5ffe9678c93ecc3b5a7fffffffe00001ffe3ffc7 else 0xfdbfff6fbf36dd33fca7cffffffffffffe001c0038fd3fff4f3b269f67fc8ecfffffffe00001fffc0000fd3fff4f3b269f67fc8ec00007ff800001fffc0000fd3fff4f3b269d23fc86cfffffffe00000001c0000fd1fff473b229f61bc824fffffffe0000000000000fd1fff4739229d21bc824ffffffffc003e001c0000fc3fff0f3b061f077c0ecfffffffe0000000000000fc1fff07ff021f013c024ffffffffc000000000000)) else (if i < 61 then (if i < 60 then 0xfe1fff87ffc31f813f026ffffffffffff000000000fe1fff877bc31f813f026fffffffe0000000000000fe1fff8779431f813d026ffffffffc003000000000fe1ddf87ffc31f813f026fffc0001ffff000000000fe1dc787ffc30f813f026ffff8007ffff000000000fdffff7fff3eff7ffcffdffffffffc000ffffc0000fddfff77ff3aff79bcf35ffffffffc000e00000000fdbfff6fbfb6df77feefcfffffffe3ffc1fffffff8 else 0xff5fffd7796bbfe9bd927ffffffffc003ffffc0007ff3fffcfffe79fe7ff8eeffffffffffff1fffc0000fefddfbfffdf7fdf7f7fffffc0001ffff1ffe3fffffeddc7b7ffdb6f993f737ffff8007ffffe0003fffffebfffafffd75f977f6feffffffffffff00003fff8fe5fff97ffcb3fcd3f5a7ffffffffffff1ffe3ffc7fe3fff8e3bc71f877f0eefffffffe3fff1fffffffffe3c5f8fffc71f877f0eefffc7fffffff1ffffffff) else (if i < 62 then 0xfffffffffffffffffffff00007ff83ffc1ffffffffffffffffff7ffffbddb7fffffffffffffffffc003ffffff7ffffffedbbfff7fffffffffffffe001fffffffdffff7fffbfff9bff37ffffffffffffe00000000ffdffff7fffbfff9bff37ffffffffc000e00000000ffdffff7fffbfff9bff37ffff8001ffffe00000000ffdfeff7fdfbfff9bff37fffffffffffffffffffffff7fffdf7befbfefffdeffffffffe00001ffffffc7 else 0xffffffffffffffffffffffffffffffffffffffffff))))))
def bankWord (i : Nat) := fld (bankWordChunk (i / 8)) 168 (i % 8)

def decodeState : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x => bankWord (x &&& 511) :: decodeState n (x >>> 9)

def level4Chunk (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0xe0571787327ae7725645e13d7d5bd5e1cc9ebc0b3af12c4f5e059d789739af02cebc3793d7ad44903a128bc0c4d120e4f5ee756407327ae76cf3e729cd7bd20702f0e6baeb3af10e735 else 0xe059dcabc39ae76cebc441cd765675e1cc9ebc0a2401b8bc5e059d787325ae76c8e05e1cd78167811cc9eb675e254e64f5ced4a40e84faf02cebc399497816782af09ebd5a2481284f5) else (if i < 3 then 0xced9e0e7327af02cf005e13d77b445e25ce6b9db1af0e64f5e059db8bc39af02c2bc3993d73b645e1cc9ebc0b3bdce64f5ced9d788739af02d4bc3993d781675e2309ebbab3af0e64f5 else (if i < 4 then 0xe059d789c39af66cebc3993d7815a6e2f0e6bebb22f0e64f5e05f5787327af02cebc4713d73b939034d3ebc5c9c81789f5ced9e7a7327af0ed4bc3993d7bd645e1cc9eb89a22f12a4f5 else 0xe057d787327af02c0bc3993d767675e1cc9ebd5ded10e64f5d759dee7327af02cedf3993d7815b5e1cc9ebc0b3b4ce64f5dfd11787327af02b5005e13d73b3380af09ebc0a237578735))) else (if i < 7 then (if i < 6 then 0xcee4a40d327ae767cd43993d77b675e1cc9ebccb3af0e64f5d7d9d787327af0313445e271781676a9cc9ebc0a2415784f5e059d789427ae76cebc3793d781675c1cc9ebaba2481d09f5 else 0xded11789427adda41023993d78174a22f0e6bb9b3af0e64f5e051200bc27ae76cef73993d781446e2f0e6bc0b3b8178735ee6f5787327af02cede3993d73b645e27ce6bc0a239578735) else (if i < 8 then 0xced9d789c39af02cecd3993d780d45e1cc9eb9db3bdd0e735e059d787327aec2cebc3993d70b765e1cc9ebbca22f0e64f5ced99787327af0311445e13d7ad76903a0e6b9dba59d78735 else (if i < 9 then 0xe2ce9787327af02cf015e13d781445c1cc9ebc590405784f5e0591787327af0ecebc3993d7815a5e1cc9ebc0b3af10e735eb5ba88e839af032cbc3993d6dd44811cc9ebc0af2f0e64f5 else 0x702cebc4693d7bd92902f09ebbda23a178735ced9e7d0527aef688bc3993d73b64699cc9eb9da24c1d09f5ee481789739aebacebc3993d78167839cc9eb9dc9ccd789f5))))
def level4 (i : Nat) := fld (level4Chunk (i / 12)) 49 (i % 12)

def level5Chunk (i : Nat) : Nat := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0xced1192bc3993db815a5e2a4e64f6ced9288bc3993db3b4499af0e64f6ced1a40bc3993db3b449ec80e64f6d659e40bc3993db3b4493af0e64f6cd51240bc3993db9f4490405784f6ced3640bc3993da8920811cc9e3f6 else (if i < 2 then 0xecd1240bc3993db6967902f0e64f6e3d1240bc3993db3b449036578736e059d78732781db8167902f0e64f6e059d78733093db3b4e902f0e64f6ce51240bc3993dbad44903a0e63f6eb5da40bc3993db3b91902f0e64f6 else 0xcedda40de3993da89205e25d22736e059d78bc3993db81675e1cc9e306cedf640bc3993db3b67902f11c4f6cee4240bc3993db3b6ea22f1284f6e051240bc4e1cdb3b44902f11a4f6c2d117873278fdb9f449d2f0e64f6)) else (if i < 4 then 0xe9d9e40bc3993db81449037ce64f6e059d78732793db3b55902f10e736ced1240dd5e1cdb3b44902f108736cec8182bc3993db81449034ce64f6e059d78733293db3b445e1ccc64f6ced8a88bc3993db3b5a9037178736 else (if i < 5 then 0xced9e40d33993db3b44902f0e64e6e059dc6bc3993db8167742f0e64f6e2d9e40bc3993db3b44902e4e64f6e062688bc3993db5d44903dce64f6ced6a41005e13db3b44902f0e6476e4702cebc3993db3b449e2f0e64f6 else 0xeb5ba88bc3993db3b449d405784f6cede240bc3993db3b44952f0e64f6e059ecebc3993db3b44902f130736d051240bc3993db7d44902f0e64f6cedfecebc3993db3b5b902f0e64f6e059d78ab3993db6744902f0e64f6))) else (if i < 9 then (if i < 7 then 0xced8240bc3993db695a902f0e64f6e2d1240d33993db3b44902f0ec4f6e059d787327909b815a902f0e64f6ced1260bc39949b3b42902f0e64f6ced1246bc3993db3b4477af0e64f6efe7640e05e1cdb6b44902f0e64f6 else (if i < 8 then 0xe770288bc3993db3b6ea2378e64f6ced6240bc3993db3b45902f0e64f6e051240bc4a13da40bc3993c541c6ced1240bc4b13db3b44902f12e736ced1240bc3793db3b675e1ccc44f6ced7e40bc3993d801c0b3a68e64f5 else 0xcee3a40bc3993dbab4490244e64f6ced1240bc39941b3b76902f0e64f6e051178732784db3b44903cce64f6a248178903993db3b67902f1284f6dde7688bc3993db3b67902e0e64f6e059d787327879b3b53902f1184f6)) else (if i < 10 then 0xe651240bc3993db3b6790354e64f6ecd1274bc3993db5f44902f0e64f6ced1240bc39949b3b939034ce64f6a248214bc3993db3b76903a178736ced1240bc4593db8b93902f0e64f6d759e40bc3993db3b4490415784f6 else (if i < 11 then 0x676cebc439cd77b44902f0e64f6ced5a40bc3993db8193b3af0e64f6e05125ebc3993db8144772f0e64f6ced1260bc4f93db3b4490408e64f6ed702cebc3993db3b205e1cc9e3e6d5d1260bc3993db8197a22f0e64f6 else 0xe0702cebc3993db81678a2f0e64f6ced9e5ebc3993db3b67772f0e64f6ced1240bc3893db81445e2cce64f6ced1266bc4693db3b44902dce64f6e05d688bc4f9cdba344902f0e64f6ced1240bc3992db8120682f0e64f6)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xcecfe40bc3993db8179b3af0e64f6ced1240e55e1cdb3b8c902f12e736e051240de3993db3b75b3af13e736ced9640bc3993db3b677b9ccbe4f6cee1688bc3993db5953902f0e64f6a24817873278a98019db22f0e64f5 else (if i < 14 then 0xe051240e05e1cdb81205e1cc9e1c6cedba88bc3993db5744902f0e64f6ced9e40de3993dbab9da2480e64f6ced1240bc4613db3b205e1cc9e1d6ced1276bc3993db81445e2a4e64f6e054e40bc3993db5544902f0e64f6 else 0xced1240dc5e1cdb8144982f0e64f6ced9e40e05e1cdb3b4490328e64f6a2481d4bc3993db3b44903f9784f6ced1240f73993db4344902f0e64f6cec81a6d03993db3b4490335184f6cedba88e85e1cdb3b73a22f0e64f6)) else (if i < 16 then 0xced9d787327849b7344902f0e64f6e05facebc3993db816bb3af0e64f6e05124abc3993db3b8c90408e64f6cec8178823993db5744903a0e64f6ced1240bd3993db3b93902f13e3a6e059d787327835acf205e244e64f6 else (if i < 17 then 0xced9e4abc3993db3b86a22f0e64f6eed1240bc3993db81448eaf0e64f6ced1241005e13db3344902f0e64f6ced4a40bc39949b81675e1ccbe4f6ced1266bc4f9cdb3b67982f0e64f6ced1240e23993db3b44902f0e84f6 else 0xd651240bc3993db3b44902d4e64f6e059d7873278e9b3b8cc2af0e64f6ced1240bc39959b3b445e2b4e64f6ced125abc3993db81675e1cc9e0a6007017873278b173b74a248178736e05118ebc3993dbbf9d90405784f6))) else (if i < 21 then (if i < 19 then 0xced1240f7439cdb8144902f0e64f6efe7674bc3993db594490334e64f6d851240bc3993db89c0b3af0e64f6ee48178913993db8144942f0e64f6e0e76cebc3993dbad44902f1284f6ced9e7d083993db8d44902f0e64f6 else (if i < 20 then 0xe2c8178ae3993db3b4490379284f6e051240cd3993db994499af0e64f6ced9d78733013dbbf44902f12e736da51240bc3993db81445e2a8e64f6ced9e50bc3993db5344902f0e64f6ced9e88f73993db3b88a2481784f6 else 0xcec81a8bc3993db8744982f0e64f6ced1240bc3713db8167882f0e64f6e059d7873278fdb3b44912f0e64f6ced9e40bc3993db4d44902f0e64f6ced1240bc4713da89205e1ccaa4f6e059d789f3993db4f44902f0e64f6)) else (if i < 22 then 0xced1240bc3994db81448f2f0e64f6a248178944893dbd9c0b3af0e64f600702cf035e1cd73b52902f13e4f6e059d78ae3993db3b44902f138736ced1252bc3993db3b87a22f0e64f6ced9e40cd3993db5752902f0e64f6 else (if i < 23 then 0xee67640bc3993dbadc0b3af0e64f6ced1240df3993dbbf4490408e64f6e7d9e40bc3993db3b5e902f0e64f6ced1240bc39925b3b449034ce64f6e059e7cbc3993db8b44902f0e64f6e059d789a3993dba744902f0e64f6 else 0xced9e40bc439cdb8744902f0e64f6a248178933993db3b55903dce64f6cec81a2bc3993db3b96902f0e64f6ced1248bc3993db8167a22f0e64f6ced1240bc4493db8144902f10e736cee4a40d05e13db3b77902f0e64f6))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0xcee26893e8413db3b64902f0e64f6e6f02cebc3993db3b7db72f0e64f6cec81c0d05e1cdb3b5a902f0e64f6ced3e40bc3993db5d675e1ccbe4f6ced1240be3993db8175b3af0e64f6efe1688bc3993db818c902f0e64f6 else (if i < 26 then 0xced0640bc3993db3b44902f0e64a6e059d78733593db819da237178736e054640bc3993db3b44932f0e64f6ced1240bc4a13db81675e298e64f6e054a40bc3993db3b44902f1144f6ced1240b83993db814490405784f6 else 0xcec8178733213db3b44902f13a4f6d751240bc3993db81675e1cc9e206ced9d78873993db3b6790405784f6cc51240bc3993db81449041ce64f6ced1241024b9cdb8167842f0e64f6ced1240fc5e13db3b44903a178946)) else (if i < 28 then 0xe059e1ebc3993db3b4c902f0e64f6cfd1240bc3993da89205e1e8e64f6ced1240d53993db819da2401784f6ced1240e84f835b8155902f0e64f6e062688bc4f93db7144902f0e64f6cec819ebc3993db81449d2f0e64f6 else (if i < 29 then 0xced1240bb3993da8920622f0e64f6ced91d0bc3993db3b85a22f12e736e051266bc3993db3d44902f0e64f6bb48178733293db3b44903d4e64f6ede7640bc3993db815aa22f0e64f6ced2640bc3993db3b679d2f0e64f6 else 0xe064240bc3993db8144902f11a4f60070288dc5e1cd73b20682f0e64f6ced1240bc4c93db4b44902f0e64f6ced9e66bc3993db4744902f0e64f6ced1240bc3a93db3b4497af0e64f6ded11789f3993dbb59db3af0e64f6))) else (if i < 33 then (if i < 31 then 0x70289005e13d75d67a22f0e64f6d751240bc439cdb3b67902f11a4f6ced5e40bc3993db3b92a2481784f6e059d7873278ddb819db3af0e64f6e3d9e40bc3993d8019db3bdce64f5ced1240bc39921801675e1cc9e1e5 else (if i < 32 then 0xe05a288bc3993db3b5390334e64f6d5d1240bc39949bbd20682f0e64f6e851240bc3993db3b679f2cce64f6ced1266d33993db3b76b72f0e64f6cee1689023993db3b53902f0e64f6e2d1266bc3993db3b4490378e64f6 else 0xced1240d34693db8189b3af0e64f6b751178733293db3b449036978736ced1240cc3993da89205e244e64f6e2d1240bc4693db3b449038178736a24817873278adb3b205e1cc9e1c6ced1240d85e1cdb3b448faf0e64f6)) else (if i < 34 then 0xd6d1240bc3993db3b9399af0e64f600702cebc3993d73b47902f0e64f6cee3640bc3993db3b44982f0e64f6e062689085e13db8178902f0e64f6e05fa88bc3993db8189a22f0d64f6a2481d0bc489cdb3b44902f0d84f6 else (if i < 35 then 0xe7d1240e05e1cdb5d55902f0e64f6cdd1240bc3993db3b44902f0e6516cec8184bc3993db3b44902e8e64f6e059d7873278b1b3b675e1ccbe4f6ced1240bc429cdb8144902f12c4f6e051240bc4b9cdb8144902f0de4f6 else 0xe05da40bc3993db5744902f13e4f6ced1240bc419cdb3b6fa22f0e64f6ced1240bc3913db3b67902f12e736cee3e40bc3993db3b4490af0e64f6ced1260e83993db819dad2f0e64f6a248216bc3993db7b445e244e64f6)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0xced9e36bc3993da89205e254e64f6e059e2cbc3993db8b44902f13e736e059d78732e13db81446e2f152736e051240bc39949b3b44902f0e64f6db51240bc3993db3b678e2f0e64f6ced7240bc3993db816781af0e64f6 else (if i < 38 then 0xcec8202bc278e9b3b449032ce64f6e051190bc3993db5d9db3af0e64f6ced9e40bc39949b3b675e1f4e64f6ced1240fd5e13db81675e1cc9e3d6ced1240cd3993db3b6790415784f6e051241023993db3b449034d3e736 else 0xe059e5ebc3993db3b4490405c0bc6ced9d78873997d801c0ad2f0e64f5ced91a0bc3993db3b6790408e64f6cedaa60bc3993dba944902f0e64f6ced1268bc3993db8144902f0e64b6e065ecebc3993db8144802f1524f6)) else (if i < 40 then 0xced9e7cbc3993db3b3a5e1cc9e3a6d951240bc3993db5944902f1184f6ced9e40bc3992dbbd44902f0e64f6e061688bc3993db9f44902f0e64f6e051200bc3993db7b9da22f0e64f6e059e30bc3993db81445e2b0e64f6 else (if i < 41 then 0xcec81a4bc3993db8144902f1184f6ced1240bc3813db3b85b3af0e64f6ced1241006e2f1b3b449d38178736ced4a60bc3993dacf205e1cc9e2a6dd51240bc3993db8167aeaf0e64f6ced1240bc441cdb81675e2cce64f6 else 0xced2a40bc3993db81675e2a4e64f600702cee35e13d76f44902f0e64f6e05d688bc3993db5567902f0e64f6e0511dabc3993db97c0a22f0e64f6ced9e40e55e1cdb3b44902f10e736a248178793993db816ea22f0e64f6))) else (if i < 45 then (if i < 43 then 0xeff02cebc3993db3b6eb3af0e64f6ced5240bc3993db3b6a902f0e64f6d5d9e40bc3993db8144903dce64f6ced1240f43993db8175a23a178736ced11787327851801aeb3af0e64f5ced9e40bc4613db3b679f3a0e64f6 else (if i < 44 then 0xced11e0bc3993db3b75b3ba178736da51240dc5e1cdb3b67972f0e64f6ced0e40bc3993db81675e1cce64f6ced9d787e3993db3b75b3af0e64f6e051240dc5e1cdb3b8c902f0e64f6ced9ddabc3993db3b207caf0e64f6 else 0xced4a40bc3993db8144962f0e64f6ced9e40dc5e1cdb3b4490405784f6ced6640bc3993db3b61902f0e64f6e6e76cebc3993db3b7cb3af0e64f6cedda40bc4a13d801bda22f0e64f5ced9e40f73993db3b40902f0e64f6)) else (if i < 46 then 0xced1241073993db3b677baf0e64f6da51241005e13db81b1b3af0e64f6ced1240e15e1cdba544902f0e64f6ceccd78ae3993db3b675e1ccd64f6ced4640bc3993db3b4490398e64f6e051241005e13db3b96c2af0e64f6 else (if i < 47 then 0xced11787f3993db81675e1cc9e2e6cec81f0bc3993db3b67a22f10e736ced5640bc3993db3b44902f0e64c6e0511b8bc3993db3b44902f0e64d6ced9e41005e13db3b449d2f0e64f6cec81a0bc4f9cda89205e248e64f6 else 0x33b52903a0e64f6ced1240bf3993db3b4495af0e64f6))))))
def level5 (i : Nat) := fld (level5Chunk (i / 12)) 58 (i % 12)

def level6Chunk (i : Nat) : Nat := (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xcec817873278c038f9db951240bc3993dc019da24cd787327b0033b2081af0e62e6ced1240bc3993c24fc0cee2688bc3993df3b44902f0e66627be7689205e1cc9e0870067688e35e13c60d9da248178732d13df8144902f0e64f06be7689205e1cce64f7 else 0xd8e7689205e1cc9ef9dbf59e40bc3993df3b6bb3c81787327be768925902f0e64f7ced1240d75e1cc9ee00e059e40bc3993db3b67902f0e64f06be7689205e1cc9e1f7e051240bc3997c9efe4ced1240bc3993df3b4498481787327be7689205e1cc9e277) else (if i < 3 then 0xe0e7689205e1cc9ef9da24fa41083993dfdb9da2481787327be768920702f0e64f7ced12411d5e1cc9efc0a24817873278e9f8144902f0e64f053e76cf205e1ccbe4f7ceda689205e1cc9ee00ced1240bc4693db3b44902f0e64f08bf833b44902f0e64f7 else (if i < 4 then 0x70313445e1cc9edc0a2481789f3993df3b44902f0e66027be768920792f0e64f7ced1251205e1cc9ef9db3c817873278e9f3b67902f0e64f053f5b3b4490420e64f70067640bc3993c58d9da24818ebc3993df89c0a2481787327be7689205e1cc9e2e7 else 0xe2d1240bc3993c74f9db3c81789f3993df8144902f15c7327be76892062af0e64f7ced1240bc551cc9ef9da248178732d93df814490441787327be7689205e1cc9e077e051240bc3993c7ef9dc551240bc3993df3b4490481787327be7689205e1ccc24f7))) else (if i < 8 then (if i < 6 then 0xe051240bc4d1cc9ef9da2481b6bc3993df3b6790441787327be7689205e1cc9e037f670289205e1cc9ef9da2481a673278e9f3b44902f1787327be7689205e2a0e64f7ced9e40bc3993c7ef9da24817873278c1f3b44902f0e64f22380381449040d78736 else (if i < 7 then 0xced1240bc3993c6af9da24be28bc3993df55449043d787327be7689205e1ccca4f7ced1241015e1cc9ee00ced9e41035e1cdb3b449b481787327b80289204d1cc9e206ced1240cd5e1cc9ef9db3c8178ae3993df81449f481787327be76892061af0e64f7 else 0xced1240bc3993c2afc0a251240bc3993df3b44903a1787327be76cf3e902f0e64f7ced9e40bc4d1cc9efc8ced1240bc3993dfcf9da2481787327b8033b44902f12e736eb70289205e1cc9ef9da248178732793df3b4490479787327bfb33b67902f0e64f7)) else (if i < 9 then 0xced9e89205e1cc9ef9db851240bc3993df3b44902f0e64f1c3e7689205e1cc9e367cee4e40bc3993c74f9da24822ebc3993dfad9db3c81787327be7689205e1cc9e2a7ced1240bc559cc9ef9da2481788f3993df3b449038d787327be7689205e1cc9e0b7 else (if i < 10 then 0xe6f0289205e1cc9ef9da2481787327909f819da22f1527327be7689205e278e64f7d567689205e1cc9efaea248178732f93dc019dbb481787327b67689205e1cc9e2d7e05d689205e1cc9efe9ced1240bc3993df3b4490425787327be7689205e1cc9e1a7 else 0xe051240bc399ac9ee00ced1241023993d801205e1cc9e2e10367689207d2f0e64f7e051240bc531cc9ef9dca51240bc3993dc019da2481347327b676eb67902f0e64f7ced1240bc3993c52fabced1240bc3993df3b44902f1184f1bb8033b44902f0e6526)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0x51240bc3993c54d9db3c8210bc3993df3b44902f1284f1fbe768937902f0e64f700676889a3993c60d9db3c8178a63993df8144902f0e64f103e7689205e21ce64f7ced1240bc469cc9efc0a248210bc3993df3b44902f0e64f0f3e7713449f2f0e64f7 else (if i < 13 then 0x6aa89205e1cc9ed9dc4d1240bc4f93df3b449d481787327bf02892087af0e64f7ced9e40bc3993c40f9da248178b13993dc019dc2d11787327b67689205e1cc9e177ced1240bc3999c9ef9da2481787327861f3b8c902f0e66527be7689205e2c0e64f7 else 0xced1267205e1cc9ee00cedba88bc3993d801c1cec81787327b0035744902f0e64f6cee4e89205e1cc9ef9dad51240bc3993df3b679043d787327b8033b44902f1184f6e4e7689205e1cc9efdaced1240bc3993dc01c0a22f1527327b00288bc3993c602a6)) else (if i < 15 then 0xced1260bc3993c1afc0ced1240bc3993df3b4490451787327be768920862f0e64f70067689207b9cc9ed9da2481787327811c0144902f0e64f0f367689205e204e64f7cee5689205e1cc9efaca24817873278ddf599da2481787327b8033b205e1cc9e2e6 else (if i < 16 then 0xced9e40bc3993c6ef9da2481e2bc3993df3b44902f14e7327be773b67902f0e64f7cede689205e1cc9efb4ced1240bc3993dc019da2481b8bc39b75a89205e1cc9e3f7006757873278c05cd9dc5d1240bc3993df8144902f0e64f1bbe76892074af0e64f7 else 0xced1240bc3993c4af9da24817873278edf3b4490378e64f1fbe76e344902f0e64f7006768920802f09ed9da248178783993dfb19da2481787327be76f344903a178737f1e7689205e1cc9ef9da248178732788df3b449ac81787327b802cf205e1cc9e206))) else (if i < 20 then (if i < 18 then 0xced1240bc3993c1af9da248178732f13df3b4490341787327be7689205e1ece64f7a2481789f489cc9efc5ced1240bc3993df3b68a2481787327b8033b449038d344f6cedb689205e1cc9ee00d651240bc3993dbdf9da2481787327bf031344902f0e64f7 else (if i < 19 then 0xced1240e05e2b8e6e00da51240bc3993db3b7ea2481787327be76d744902f0e64f7ced1240bc3993c5ef9da24817873278cdc01c0a2481787327b6768920762f0e64f7ced1240bc501cc9ef9dc4d9e40bc3993df3b205e2b8e64f1d3f7e89205e1ccca4f7 else 0xced4e89205e1cc9ef9da2481d07327835f3b4490445787327b80381445e1cc9e30600676cf205e1cc9ed9da248178af3993df3b44902f0e64f0dbe7689205e1ccbe4f7cee268920842f09ef9da2481c8bc3993dfbfc8a2481787327bf033b67a22f0e64f7)) else (if i < 21 then 0xced12411c5e1cc9ef9da248178b63993df899da2481787327be7689205e1cc9e1c7e051241035e1cc9ef9da851240bc3993dc019db3af0e64f18367689205e1cc9e3a7ced9e40bc3993c58f9da2481787327829f3b7ba2481787327b802892081af0e6206 else (if i < 22 then 0xced9e41035e1cc9ef9da248236bc3993df3b44902f1187327b8033b449034ce64f6e051241165e1cc9efc0a248178732e13df3b4490359787327b8038b44902f0e64f6005a289205e1cc9ed9da248178732e93df3b44902f0e64f0b38033b2071af09e2e6 else 0xced1241105e1cc9ef9db3c8178732e13df3b44902f0e64f1fbe7689205e25ce64f700702cf445e1cc9ed9da2481b8bc549cdf5d9da2481787327bf233b44902f13e737ced1240bc3e9cc9ef9da2481789f3993df3b44902f0e66a27be7689205e25ce6657))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then 0xf667689205e1cc9ef9da248190bc3993df3b4490319787327b8033b449040d78736ced1240bc399649ef9da248178ae3993df3b67a22f0e65f27be76cf205e1cc9e3d7ced1240bc439ccbef9da2481d0bc398fdf959da2481787327be768920742f13e737 else (if i < 25 then 0xced9e41185e1cc9ef9da248178ac3993df3b4490455787327bf02bb44902f0e64f7ced1241025e1cc9ef9da24fa40bc3993dc019dad481787327b67689205e268e64f7ced1240bc3993c50f9dcbd9e40bc3993df639da2481789f27be768920802f1524f7 else 0xced124102399949ee00ced1240bc4a13dbad9da2481787327be7689205e1cca44f7ced1240bc3993c20f9dc2d1240bc3993df3b4490401787327be76f544902f0e64f7ced1241065e1cc9ef9da9481787327835f3b44903ed787327b8033b4481af0e6306)) else (if i < 27 then 0xda51240bc549cc9ee00d751240bc3993db3b449f481d07327bf0289205e2a4e64f700702892071af09ed44902f0e64f180a9f9f44902f15c7327be768944902f0e64f7ced9ebb205e1cc9ef9da248178733693df3b67902f1667327be7689205e294e64f7 else (if i < 28 then 0xced9e40bc549cc9ee00ced9e40e35e13db8144902f0e67327bf0b3b44902f0e64f7ced1240bc3f1cc9efd6ced1240e83993df3b75a2481787327be76892076af0e64f7e5e7689205e1cc9efa4ced1240bc3993dfbfc0a2481787327be76dd44902f0e64f7 else 0xced1240bc3993c1efcdced1240bc3993df3b7ca2481787327be768920672f0e64f7efe76cf205e1cc9ef9da24e240bc3993df3b55902f0e65f27be76eb44903a178737ced1240bc3993c68f9da9c817873278ddf3b85a22f0e66527be76892e902f0e64f7))) else (if i < 32 then (if i < 30 then 0xced1240f75e1cc9ef9da248178803993df81b1a2481787327be76cf449f2f0e64f7ced1240bc3993c78e00ced125ebc3993db3b44902f1227327be7689205e1ccd64f7ced1240bc531cc9efe8ced1240bc3993df3b67902f0e67327bf5f3b44902f0e64f7 else (if i < 31 then 0xced1241015e2b89ee00e0676cebc3993db3b4499af0e64f1d3f0289205e1cc9e2e7d8e76cf205e1cc9ef9da8c8220bc3993df3b44902f0e64f123e7689205e1cc9e207ced1259205e1cc9ee00cec81a0bc3993db3b44902f0e64f063e768920842f0e64f7 else 0xcedd6cf445e1cc9ee00ced12410371af1b3b449039d787327be771944902f0e64f7ced9e40bc3993c5ce00ced4e40bc3993db3b4498c81787327be7689206e2f0e64f70067689206f1cc9ed9dc9d7640bc3993df3b449043d787327bea33b44902f0e64f7)) else (if i < 33 then 0x67640bc3993c38d9da248178733493df8144902f0e64f03be7689205e1cc9e437d167689205e1cc9ef9da2481d6bc3993df3b48a2481787327be7689205e1ccae4f7e051241205e1cc9ef9da24e978ae3993dfcb9da2481787327be7689205e2349e3a7 else (if i < 34 then 0xefe7727205e1cc9ef9db3c8240bc3993df3b67902f0e66127b8033b204d1cc9e2e6ced4a89205e1cc9ef9da24817873278e5f3b44902f0e64f013e7689205e1cca84f70051240bc489cc9ec00ced1240e05e1cdbcd9da2481787327be76b5205e2a4e64f7 else 0xcee0a89205e1cc9ee00a2481787327881b3b44902f0e65827be7689205e1cc9e377ced12410d5e1cc9ef9dced1240bc3993df3b67902f0e64f03bf0289205e2f0e64f7ced1240bc519cc9efc0a24817873278c1f3b44902f0e66827be76a344902f0e64f7)))) else (if i < 41 then (if i < 38 then (if i < 36 then 0xced1240bc4a1cc9ef9daad1240bc3993df3b44902f0e64f133e76cf205e2f0e64f7ced1240cd3993c6ef9db3c817873278c1f3b44902f0e64f20380001c0b3af0e64f5e051240bc399949ef9da24817873278c9c019da24c1787327b0033abc3993c601c6 else (if i < 37 then 0xcedfe89205e1cc9ef9da2481787327825f8144902f1567327bf7f3b79902f0e64f7ced9e40bc399949efc0a2481c6bc3993df8144903a1787327b8033b675e1ccbe4f6005117873278c040dc8e051240bc3993df3b44902f0f87327bf0289205e1cc9e4f7 else 0xced1240bc4f9cc74f9dc9d1240bc4f93df3b679038d787327be7689205e1cc9e317f767689205e1cc9efc0b3d1240bc3993df3b67903a1787327be771344902f0e64f7e7e7689205e1cc9efc8ced9e40bc3993df3b44902f0e64f233e76cf205e1cc9e4f7)) else (if i < 39 then 0x70289204d1cc9ed9dc051240bc3993dfbfd6a2481787327be7689205e1cc9e007cee1289205e1cc9ef9db3d9e40bc3993df3b4490449787327b8033b44902f0e64f6e051240bc3993c84f9da2481787329035f3b81a2481787327be76892069af0e64f7 else (if i < 40 then 0xced12410e5e1cc9ef9da24e640bc3993df3b44902f1647327b8033b6790268e64f6ced1240bc3993c42f9da2481ecbc3993dc019da22f0e64f18370289205e1cc9e1e7ced1240bc3993c58e00ced1240cd3993db819dbad11787327be7689205e1ccc44f7 else 0xced1240bc4d9cc9ef9da2481787327805f3b4490459787327be7689205e1ccb84f7cedb289205e1cc9ee00ced9e7cbc3993db3b44902f0e64f113e7689205e288e64f7eb6c689205e1cc9ee00e7d1240bc3993db3b449040d787327bf3b3b44902f0e64f7))) else (if i < 44 then (if i < 42 then 0xced1240bc521cc9ee00a2481c6bc27881b3b44902f13e4f06be7689205e1cc9e417e064e89205e1cc9ef9da24817873278f5f3b44902f0e64f22beae89205e1cc9e0d7ed70289205e1cc9ef9dbb4817873278fdf3b4ba2481787327be7689205e1cc9e137 else (if i < 43 then 0xced1240ee5e1cc9ef44902f0e665278fdf3b44902f1687327be7689205e1cc9e057ced1240bc3993c0cf9dcbd1240bc3993dc01c0bad11787327b00381205e1cc9e2e60067689205e21ce6d9da248178a13993df3b4490301787327be7689205e218e64f7 else 0xced1240ff5e1cc9ef9dc9d1241085e13dc019da2482069a39b0033b75b3af0e64f6f0e7689205e1cc9ee00cee3240bc3993db81c0a2481787327be7689208c2f0e64f7e051241145e1cc9ef9da2481787327865f3b93b3c81787327be76892f902f0e64f7)) else (if i < 45 then 0x676892080af09edc0ced9e40bc3993df3b6790451787327be7689208d2f0e64f7f867689205e1cc9efc0bcd1240bc3993df3b5da2481787327be7689205e2cce64f7cee0e89205e1cc9efdfcec8178ae3993df3b75a2481789f39be7689207b9ccbe4f7 else (if i < 46 then 0xced1240bc549cc9ee00ced1240e35e13db3b4490465787327bf8b3b44902f0e64f7ced1240bc3b9cc9ef9dbcd9e40bc3993dc019da8c81787327b676892089af0e64f700676a5205e1cc9ed9da24ca40bc3993df3b4490411787327be76ed44902f0e64f7 else 0xcec81d0d05e1cc9ee00ced5640bc3993db3b6ea22f0e64f1fbe7689206f2f0e64f7ced1240bc3993c1cfdfced1240bc3993dc019da24e9787327b676bb44903a0e64f7))))))
def level6 (i : Nat) := fld (level6Chunk (i / 12)) 67 (i % 12)

def level7Chunk (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xced1240e35e1cc9ef9da2481d0bc3993df919da2481787327be7689205e1cc9e4f7ced1240bc399949ef9da248178bc3993df3b44902f0e64f183e7689205e1cc9e077ced1241205e1cc9ef9da24817873278b9f639da2481787327be7689205e1cce64f7 else 0xced1240bc3993c14e00ced9e40bc3993db3b44902f0e65f27b8038144902f0e64f6ced1240bc3993c1af9dbcd1240bc3993df819da2481787327be7689208a2f0e64f70067640bc3993c5cd9dc9d1240bc3993dc019da2481347327b676cf44902f0e64f7) else (if i < 3 then 0xced1240bc531cc9ef9dbad1240bc3993df3b44a2481787327bf5b3b44902f0e64f7ced127d205e1cc9ef9da2481789a3993dc019da248206bc39b67689205e2b8e64f7ced1241105e1cc9ef9da24817873278fdf3b44902f13e7327be7689205e1cc9e3a7 else (if i < 4 then 0xced7689205e1cc9ef9da248178732e13df3b449040d787327b8033b445e1cc9e3060067689205e1cc9ed9dc4d1240bc3993dc0144902f0e64f10367689205e1cc9e377cee7689205e1cc9ef9da24821ebc3993df3b44902f0e64f103e768920842f0e64f7 else 0x1dfced1240bc3993df3b44902f1527327b8033b449038d784f6)))
def level7 (i : Nat) := fld (level7Chunk (i / 12)) 67 (i % 12)

def level8Chunk (i : Nat) : Nat := 0x33b44902f0e64f6
def level8 (i : Nat) := fld (level8Chunk (i / 12)) 58 (i % 12)

def number : Nat → Nat
  | 4 => 119
  | 5 => 567
  | 6 => 560
  | 7 => 51
  | 8 => 1
  | _ => 0

def hashes : Nat → Nat
  | 4 => 0xfb743a00f73a7d4bf5993b7ff489ff65f2cc9399ef280a8eed1ec33ced0378fdeb4fd111e91ac44ce63d5b1de5012ea0e35362f3de6bc904dc973113dc6362ceda94fc89da4ec89fd5e802c8d3bb5571d0cd7f5eccd8bb48cc5d3efac9ded0b2c313a7bac2668697bf9d56bcbeadd842bd7c7aa2bd09a418bbc70039bba214b6b9bdb873b94bdd66b7e823b5b2ee1ddcb269433db1cbe045af40bd3fad28973aa8632c36a54cd85ea50e25fda234c5029c3797209aa1f4cc97b974ca946c394e93ae4959921e9d238e183d6d8d63d4188c604dde87add65f83f0331e7ecf62857e5dc89c7dbdd28e7d804c4977fac49e767dd40270ccb0796f2da3bf6e3aeb1f6cb8226b6bb15d5c6aa8461c688d3cba681b9121674add1864d55895631496cc60a319a2603fd2455f17c4db5d97806c5d6d75cd5d6117ec5b89af1d591c29b457ef506d51f64e9050e6aafa4fe4fe374c7aa0c44bbccaa7475cf0b6449ee1e8439ed3a5432d9cb94198f2503cb23cb33c082c263aabfacd37e4ca5d370b7e5436be42d435b39ccf3319a0e02e2f82e7298dea74295593aa279af3e826a3211225b3da2023423ca8212daaf41e13d3e61dd0c6d61bbf0d8717d73307179e0f5017938eb61656f05f12667b631074521a0853411602f7a0ee0289fb9c
  | 5 => 0xffe7b1c4ffb45d28ff6a4a48ff504cc1ff36c2bcff04dd1cfe837c73fe6695c0fdcca993fd3e9d62fcfbe4bdfcbeb323fcaf695afc63b4c0fb592b9bfa0ccd26f91876b5f90a517ff8dba7aef8454cc9f8394f84f80bedfbf749e1def6f1f156f6b1cf78f6a26fb3f659ae00f5de8f59f5969fb9f4e2f447f4456bcdf422e8a7f3e2e604f3252ec5f320addef2d7e2a9f2cc9399f1dd04aff1b8f97af1b8f7abf1b284d2f12e92a3f0468220ef71dd81ef66c10cef2ec399eee5dceceec6b0d7edfba782ed9cdd2ded3a01ccec9d7567ec77d9fbec6df0edec4c3e85ec0dc41aebc0c13febbce6d9eb964162eb79dd88eb4fd111eaf00d2ceab407eee9ec8fdfe99aecf0e9757a8ce9311ff6e8c9997ce7ebf9b4e78099bde7683df5e74f90b3e6da0ba2e6a29958e65b968be522be36e4d3c9bce46b179be43a06e4e35db33fe30fb715e298dfc5e28d3ffee20c994ce0e8b759e0e611c3e0b359ace0aae583dfe2bc79dfdb6bbedfbc5765de739546de6892f3de1dc374ddecfdc9dde18004ddc1642adbf6c790db94b4d0dad33a4fdaa5b988da5db13ada4ec89fda4e580ad999a609d9068ef1d8f4409ad8ab5f93d85751d6d841efbdd815abe8d778beecd6bb5e81d6a198add644a1a2d5f7ec7fd5d85fa3d5bb80f6d49f5baad405b094d3864f07d37d6299d30ea709d258dbbbd1c2c2d7d142f2f2d1373e3ad0ea8a9ad039ed0ccfdba90fcf9fe11ccf9e24d8cec45e62ce57e645cca8e37ccbec1e80cb68eee2c9993cf2c89eb341c871830ec7e221afc7d8585cc67612cec66353f3c5439930c5285183c4ad2e9ac44d4b84c43e54a9c3b6532cc3b535bfc3848d58c3426453c3404370c32386b4c296ad86c1ff01f6c1c5de3fc1bb5da5c15dcd51bf81ebd4beadd842be6a04d9bd1cceebbc5a3188bc2a361fba0b7720b9cf9ee1b9cb5f0ab9585372b8d523c9b860b0b4b80481a8b7c2dee6b70f0024b6ca0bc0b68bab8cb68947e5b6002ed7b57f5f1bb5380ef2b4b68d92b46d4d37b46ab591b3d9197cb3c1bc6eb3b80e84b307551fb1fb1c6eb0710001b03c47c0af8fb8c2af734a04ae999732ad299ffaad28973aad2110d6acb1ca8babb84c64aba10254aa430b39aa28fdcba9a2a8d3a95b7883a8632c36a7d0e8d5a750a21da6e180a4a59c08f4a54cd85ea4ef5cada4aa4167a41e9108a3c89bb1a34059eaa2f17321a24b6ab0a232b0b5a0973865a0910fc89fa5e7d29dec09a39dd834689dac58419d88d0499d5366db9d45c8309d2151389c2008649c1d517e9c0172e49b9688659a52f5c29a2ff2939a2e7037989fdf39981d67cb97fef12f979c5bda975fac709671dd63962cdc7a95e52f7495a4a3e99583c5b29577a005955f4c7694a401b79397755793934d03934293409337d38d92de7f0d92d209cd928e134591c1d08190faba72907fa7f89041a8ef9027b77090051aa68fc16b5f8f80757f8f1455738ec5a7e48eafdb688d7b31e78d71f8e18ca775328c5af4df8b6182258b4faa688a92db0389b3f14088fb459d887226ad881ba30687e2c9f387316d9c862c152c84bccb7d81d50ddc8151afce81349925811191c280f589bb807f1807802c51e8800fd1bc7f9286ca7f529bf37f0812857e20d06c7daa2b457d4269187d3f07537ca1515e7c5b875a7b9a4ef679e0ab9d79c2e62778e7f7e077b7060a7767f161773ce0c776ad35cf7688769a74b71e78748bc3ab741473db74069fa673f9f58f739847a47357ba1e72fa68d272aa98fb71771be970dd8a9270d7f9cc6fc1130a6f0b82786ef1eaa66e6a971d6e5f7ea76e2801aa6e13f55e6d9b17a26d5841fb6d4b2a3d6d3b76ae6d16bd6c6d04249b6b8ae4be6b3d89026b3c9f886b3178c86a5b110e6a346bfb6a01cad769c525b068d5a73668cdc6bf6824045767a4499666e4898d65f3dcf565153558649cdff3643f92f8642641cf6422b19263be34df63bd51a363b26b266343c3c562e0e5e362c9594762b4e34962922b2a621cfa26620ff2a9613267ca6063c9325f19a3735ebe671c5e3bbce75d98427d5d6ca99e5d3912c55ce491375c594cce5beaea3f5bac3b125b5d67035ac3b00a59b6c26d59688c335921a86b5916650b58fd600358a362ea57268ad056c4dd005681e278566b3cf6564856a155ddb5165590eac2558ff7a255523861547aa9615404066052f5a6c9528afb2a5255f61150e9ca875003d31f4ff2785c4f6ac0c64f35f4f14e6dd50c4d25d0764cbbba954c7ba9844c00f1424b9e03a74b0561f04ae36d694a48e36b48a9101e4899f02f482cab3d480b9a4847fd872e46ebde90465f6614465a35044655cd21460ea0c244e7fd5f43919dc7433b3679432d9cb942d86eed427a9e55419d743a419ba3b24178ab8741615027413cf3ea40be6e38403df1943f9f37a03f218bc13e2522c73cb23cb33c466c173bc973513b8a71b43b8130ca3b7f60423b0765da3a479c8439ccfe7f39a8e5d439760b0138efe63838400c6137f1e8c337da70d4378ba30c36a5e2fa36a5a8a335a6194f35830051355dbbd334ce3fd434c9a98f343445823368db2532ecbbb232dca7b332b6586b328168793155533e2facf7d52f1374e92e1c1df82e01e4f22b7b38c82b716c8f2b49a5142aaf8f5429740bc1292b7cea28f7317928d3644f28c93be12890182a288597902851c45c283ed7022832ad6126c1e666263082e925bd540125907ac02510833023c8a11d2360336622f61a8922e4dd5122d96f31221e8c3c21e1c0f621a3f80f2154f41020d5b10b200aaf6e1fd121911f38f9931d6aabca1ce6cc471c7ace9a1bf56fc01be75fb41af47f6d1aec58801a76a6181a2e635b196c45311914efb118d9dc6918b278231862ba13185fa38518210c9217dcf894176423cd17090f9416dff15f169f9d4b15a0c04b15196af914fb22cf14e000cf14d01510143fb74813e46be613e03abe1083e4a9104017490f7be29a0f6322c60eea5b380ddb92d00db188310dabba8f0d475ab90d3c65c00c6642df0b0667960afc860c0acae8960a8f928c0a096efe09fced0909c36a5f0827b0c007f94e1407ae3c600751b9de0748a0e40734800407301f5006675c7c053bdd5204fedc7e0476922c047339d50343f8a803103e6902eceb7702e4a56c0292887f015fd11b006606bb
  | 6 => 0xffadc997fe6695c0fe390b39fddeea79fd96a320fd8f7e41fcaf695afbe3e29efa8cf5cafa678366fa2ce826f8ff8b6cf8f873fbf84faca7f6f1f156f6240cdef5de8f59f57f9bbaf53918fef487982bf4456bcdf31c814cf2beb0b4f290bf6af264e8c5f2336937f1dac033f1a56286f15f5a95f124da15f08203f3f0366fb1f02d9ab3eff4388aef2dfc6ceee5dceceec8ea70edfba782ed003ddcece8d06aeca26d44ebed71fcebce8413ebc54329ebc372a1eb502a54ead0f19ee9c8f6c3e96d7b35e933f897e8c9997ce78d51ebe6da0ba2e6d29c33e6aa750be6744178e65a4892e6242709e5e793c8e5dc630ee5b240a3e5916484e4a3cf83e45638efe3f4cd6ee3c9932ee349a78de2c57ad8e26e6ef5e2619242e234fbcce1dc9374e1706a6ee0aae583dfa826b4ded62436de4bd821ddecfdc9dd9aec56db8db773da718f2ed95a01a7d8b958cfd876bfc0d6e3ab0ed697b531d6628b94d5a307b7d4324c4ad405b094d3be6a0dd279934bd25a7c50d24da852d20da5dad185f2c2d0af1bf9d01533f0cffaad73cf9fe11ccf38521fce406154cd53ac09cc4f9975cc18cc13cb29aedbca7275baca2acc0dca27b030c9f8f080c9b05790c8f68a82c8e1ce5ac8210af3c71b7549c6e3afaac6a29d89c631b14cc60f2ea3c51c0082c483c9a7c456324ac3941420c32386b4c21f2f37c204c783c19b3440c0c76c3ac07a5429c037d585bfd53ddbbfa73525bf80d61dbf2e6d97beec548cbeadd842be678637bd6c1c39bc5a3188bbfab96abbdea85abb5c84bfbb3c30c7bb1b06a5bb0db4feba94b1adba077cbeb98af1b5b95e64e1b9122a27b8dc8615b8c3311bb89ad7eeb86bc31fb83d6073b7dc60f0b7afcf1eb76c5683b6bcf9ceb6a3ede6b68bab8cb6002ed7b5944052b57fefb1b5380ef2b5021ceeb3eb394eb3ea6644b3d6c17bb3cfdff8b2a50623b25eb59bb24f7fafb21604f3b1b0e3b4b16ad5beb0b71cb1b070c99cafd6b3bdafcce747af7ad520af734a04ae7fba5cad82afc6ad299ffaace619e0ac88913fab4f633da9ac0766a9a2a8d3a97b250ba95e91b0a91fba12a91c12e0a89dec47a6515550a5dab21da4ef5cada4130da7a3d087e7a34045a9a3233338a30376a2a27c2548a265dc43a24b6ab0a1807c1da171b0d2a0727e599fdb799d9faad3709e14b1049daee01b9d4cfdb99d487cd29ce31f479ce187cb9c659e349c120a4c9bda53c69bc569039aee6f8d9a79dc609a6e511499deff5499b98cf0998e90009984f52d9956928d991bfbb1990dabe097c4ac2197ac50599741752496c5445b969fa8ef962a9db09577a00594dbd6e293c2bbe4939d49809377b96a93539962917120e1912cc9bd91218eb090f76c10906817b68fd97b858fc16b5f8f12d9468e97a7fe8e7fe8688e61d5d88e2592688dff11968dfa70b38d790db88d27bb728c6bd1ca8c3ad9f48bd8c7348bb3c98a8b10864d8afce7038ad2b4778a92db0389da00ba8981392788860221887ae4da8859be4c877a7f7486e5ab1186e2ba9b85a927528518eb4185067cb584f4c67984e36e0e8485802e837fc3ca82002a1f81d2a61e81ca02a6812e9cfe80b31be48081dd2e807f1807807dff70806c70968043598180002e977f05fe387e232fb27e21f72b7cecf5e07c80aaaf7c56ec717b9a4ef67b6ac1e67b12598e7a64eebf79c2e62779b9f76479880d00794e30e5791f2e2078ec2d56780de90a77d6926777094eb776d0b270767ccd5d75b4951e74a47400738455d47384340471a695bc7165caf5714489c9714381e670e367a36f9851ae6ef1eaa66e54998a6d4c015c6d4b55a86c6e48836be2de716bc9ce026b73e8986b66ca706b3d89026a13b1456a086de569c3bd9468d9b32668d5a73668785d06685013d56848940c6839cfd4682c8cb6673a5f7b671df06066c09c72667f16b165f1c8a864b7b6b864aec7f563ec588563ea612863be34df6358ff43622c509c61ea41ba5eabf8395e3cdac25dd3d25c5d6ca99e5d1df1a05c6317bd5bca4b085b52c3855b483ff15ae40ea25aae8e495a6d102f5a58725a59eb6d4b59e6bb3758fda322563259935590eac25531437d551a364e54e7d8c45450ccbf5407ef3253f4afe753ca77c7536ca72f5334cdbd528afb2a524eb05c51787111514126285006c2514f395a684eb305704e578bd64df06aa54d25d0764cf36f224cbbba954c7c7a8e4c641ac84bda9ac94b9e03a74b90885a4abf07594a48e36b49fde0f14899f02f47a3bed4462941d845be575945a35eda4551583f44e7fd5f443b287d442ae63143c6e36f438d8688438416c9433b36794322917140d4a6273febe0ec3fe760b33fc487e33f871b6a3ecbd0ab3d1f2ba93d064e013c6d41a23aaf85643aa776ec3a479c843a142f7939d432af39a84473396a21b23924b63b385fb56a37e2ef5e37b08b263719293036a5e2fa3682c3d336028c0a353db3fc342e95d4338ec0c03323149132b6586b32ad8c91324371fa31fd433b317d3fb330ee21c330c32a6b305646a5305146352fbea4a32fafcdad2f306cc52e64e2d02e30070a2cd9688e2c106bec2b206c352b0b7d052adf29df2aa6e6fb2a5e4e0b2a24be01292c0a4428cf016e28cd1f2b2890182a28489f602791a6252780f32b26cc88fe2646e9ec261830c32582a0522531c02224fe549c24fb30dc24eb561d24e159de24bafb182458863f24087a912353db5f230fc6d422110fa8211c0c3020c77cb920b0458e209ee1da20552ba0201781792005256e1fdc64121f5250dc1edeed6c1ec7790b1e5807c21e3c42cf1cc588bc1b80b1ec1b4741be1affc8c01ab5733919e8e1fe1995dd3c1919b99a18eb56ee18b27823183bc452172bf38f16d7ac70155947bc13f67d8a12d63d8e128e359212610c8a11767a2e110c58811028cb9b0ec4aee70e4e10c30e4da2660df1f3e00ddc54e10dda3a1a0cb9fa1e0c9d5f320c9a5ab00c6642df0b679e4a0a95042809cdb08d0965bacf095a776f0941726708dfdf070827b0c0068c69050688904f06811bc206312f9505d40a060583818c057491e8054cbcd00476922c0460d20c03de916103a748b40211a00601d80baf012a2de3009c8aaa007025950058c9eb
  | 7 => 0xfd8f7e41fa8cf5cafa678366f1dac033e1dc9374dd9aec56d6628b94cf9fe11cc8f68a82bb5c84bfbb1b06a5ba94b1adac88913fa6515550a3d087e7a0727e59990dabe0917120e18f12d9468ad2b47789da00ba85a9275285067cb581ca02a680b31be47f05fe3874a47400738434046ef1eaa66d4b55a868d5a736673a5f7b58fda32253ca77c7536ca72f4e578bd64c7c7a8e3924b63b30c32a6b2b206c352a5e4e0b28cf016e2791a6252531c02220552ba01fdc64121ab573391919b99a1028cb9b09cdb08d0058c9eb
  | 8 => 0xcf9fe11c
  | _ => 0

def stateCode : Nat → Nat → Nat
  | 4, i => level4 i
  | 5, i => level5 i
  | 6, i => level6 i
  | 7, i => level7 i
  | 8, i => level8 i
  | _, _ => 0

def state (d i : Nat) : List Nat :=
  let code := stateCode d i
  decodeState (code % 16) (code / 16)

def test (d : Nat) := bar 84 state number (idxGen number hashes) id [] d

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
theorem part4_108 : span (test 4) 11 108 = true := by decide +kernel
theorem all4 : span (test 4) 119 0 = true := (@span_join (test 4) 60 0 59 (@span_join (test 4) 24 0 36 (@span_join (test 4) 12 0 12 part4_0 part4_12) (@span_join (test 4) 12 24 24 part4_24 (@span_join (test 4) 12 36 12 part4_36 part4_48))) (@span_join (test 4) 24 60 35 (@span_join (test 4) 12 60 12 part4_60 part4_72) (@span_join (test 4) 12 84 23 part4_84 (@span_join (test 4) 12 96 11 part4_96 part4_108))))

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
theorem part5_564 : span (test 5) 3 564 = true := by decide +kernel
theorem all5 : span (test 5) 567 0 = true := (@span_join (test 5) 288 0 279 (@span_join (test 5) 144 0 144 (@span_join (test 5) 72 0 72 (@span_join (test 5) 36 0 36 (@span_join (test 5) 12 0 24 part5_0 (@span_join (test 5) 12 12 12 part5_12 part5_24)) (@span_join (test 5) 12 36 24 part5_36 (@span_join (test 5) 12 48 12 part5_48 part5_60))) (@span_join (test 5) 36 72 36 (@span_join (test 5) 12 72 24 part5_72 (@span_join (test 5) 12 84 12 part5_84 part5_96)) (@span_join (test 5) 12 108 24 part5_108 (@span_join (test 5) 12 120 12 part5_120 part5_132)))) (@span_join (test 5) 72 144 72 (@span_join (test 5) 36 144 36 (@span_join (test 5) 12 144 24 part5_144 (@span_join (test 5) 12 156 12 part5_156 part5_168)) (@span_join (test 5) 12 180 24 part5_180 (@span_join (test 5) 12 192 12 part5_192 part5_204))) (@span_join (test 5) 36 216 36 (@span_join (test 5) 12 216 24 part5_216 (@span_join (test 5) 12 228 12 part5_228 part5_240)) (@span_join (test 5) 12 252 24 part5_252 (@span_join (test 5) 12 264 12 part5_264 part5_276))))) (@span_join (test 5) 144 288 135 (@span_join (test 5) 72 288 72 (@span_join (test 5) 36 288 36 (@span_join (test 5) 12 288 24 part5_288 (@span_join (test 5) 12 300 12 part5_300 part5_312)) (@span_join (test 5) 12 324 24 part5_324 (@span_join (test 5) 12 336 12 part5_336 part5_348))) (@span_join (test 5) 36 360 36 (@span_join (test 5) 12 360 24 part5_360 (@span_join (test 5) 12 372 12 part5_372 part5_384)) (@span_join (test 5) 12 396 24 part5_396 (@span_join (test 5) 12 408 12 part5_408 part5_420)))) (@span_join (test 5) 72 432 63 (@span_join (test 5) 36 432 36 (@span_join (test 5) 12 432 24 part5_432 (@span_join (test 5) 12 444 12 part5_444 part5_456)) (@span_join (test 5) 12 468 24 part5_468 (@span_join (test 5) 12 480 12 part5_480 part5_492))) (@span_join (test 5) 36 504 27 (@span_join (test 5) 12 504 24 part5_504 (@span_join (test 5) 12 516 12 part5_516 part5_528)) (@span_join (test 5) 12 540 15 part5_540 (@span_join (test 5) 12 552 3 part5_552 part5_564))))))

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
theorem part6_552 : span (test 6) 8 552 = true := by decide +kernel
theorem all6 : span (test 6) 560 0 = true := (@span_join (test 6) 276 0 284 (@span_join (test 6) 132 0 144 (@span_join (test 6) 60 0 72 (@span_join (test 6) 24 0 36 (@span_join (test 6) 12 0 12 part6_0 part6_12) (@span_join (test 6) 12 24 24 part6_24 (@span_join (test 6) 12 36 12 part6_36 part6_48))) (@span_join (test 6) 36 60 36 (@span_join (test 6) 12 60 24 part6_60 (@span_join (test 6) 12 72 12 part6_72 part6_84)) (@span_join (test 6) 12 96 24 part6_96 (@span_join (test 6) 12 108 12 part6_108 part6_120)))) (@span_join (test 6) 72 132 72 (@span_join (test 6) 36 132 36 (@span_join (test 6) 12 132 24 part6_132 (@span_join (test 6) 12 144 12 part6_144 part6_156)) (@span_join (test 6) 12 168 24 part6_168 (@span_join (test 6) 12 180 12 part6_180 part6_192))) (@span_join (test 6) 36 204 36 (@span_join (test 6) 12 204 24 part6_204 (@span_join (test 6) 12 216 12 part6_216 part6_228)) (@span_join (test 6) 12 240 24 part6_240 (@span_join (test 6) 12 252 12 part6_252 part6_264))))) (@span_join (test 6) 144 276 140 (@span_join (test 6) 72 276 72 (@span_join (test 6) 36 276 36 (@span_join (test 6) 12 276 24 part6_276 (@span_join (test 6) 12 288 12 part6_288 part6_300)) (@span_join (test 6) 12 312 24 part6_312 (@span_join (test 6) 12 324 12 part6_324 part6_336))) (@span_join (test 6) 36 348 36 (@span_join (test 6) 12 348 24 part6_348 (@span_join (test 6) 12 360 12 part6_360 part6_372)) (@span_join (test 6) 12 384 24 part6_384 (@span_join (test 6) 12 396 12 part6_396 part6_408)))) (@span_join (test 6) 72 420 68 (@span_join (test 6) 36 420 36 (@span_join (test 6) 12 420 24 part6_420 (@span_join (test 6) 12 432 12 part6_432 part6_444)) (@span_join (test 6) 12 456 24 part6_456 (@span_join (test 6) 12 468 12 part6_468 part6_480))) (@span_join (test 6) 36 492 32 (@span_join (test 6) 12 492 24 part6_492 (@span_join (test 6) 12 504 12 part6_504 part6_516)) (@span_join (test 6) 12 528 20 part6_528 (@span_join (test 6) 12 540 8 part6_540 part6_552))))))

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
theorem part7_48 : span (test 7) 3 48 = true := by decide +kernel
theorem all7 : span (test 7) 51 0 = true := (@span_join (test 7) 24 0 27 (@span_join (test 7) 12 0 12 part7_0 part7_12) (@span_join (test 7) 12 24 15 part7_24 (@span_join (test 7) 12 36 3 part7_36 part7_48)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part8_0 : span (test 8) 1 0 = true := by decide +kernel
theorem all8 : span (test 8) 1 0 = true := part8_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem lowerFn : ∀ s, HasCircuitSize 6 edgeFn s → 9 ≤ s := by
  refine prove_base 6 84 8 edgeFn sampleRows inputWords [] number hashes state (by decide +kernel)
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) ?_
  intro s hs
  interval_cases s
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => span_ok all4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all8 i (Nat.zero_le i) hi

theorem lower (s : Nat) (h : HasCircuitSize 6 six s) : 9 ≤ s := by
  have heq : six = edgeFn := by decide +kernel
  exact lowerFn s (heq ▸ h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem exported (s : ℕ) (hc : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) s) : 9 ≤ s := by
  have e : (fun x : Fin 6 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) = six := by
    funext x; revert x; decide +kernel
  rw [e] at hc
  exact lower s hc
end PEqualNP.Outside.L_meta_11693.Base0

namespace PEqualNP.Outside.L_meta_11693
open PEqualNP.MetaComplexity
def restricted0 (x : Fin 7 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 6) || (x 4 && x 5)
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem restricted0_bound (s : ℕ) (h : HasCircuitSize 7 restricted0 s) : 9 ≤ s := by
  let pi : Fin 7 → Fin 6 := ![3,5,4,0,1,2,0]
  have hr := Pin.relabel_size pi restricted0 s h
  have e : (fun x : Fin 6 → Bool => restricted0 (x ∘ pi)) = (fun x => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) := by
    funext x; revert x; decide +kernel
  rw [e] at hr
  exact PEqualNP.Outside.L_meta_11693.Base0.exported s hr

def restricted1 (x : Fin 7 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 5)
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem restricted1_bound (s : ℕ) (h : HasCircuitSize 7 restricted1 s) : 10 ≤ s := by
  obtain ⟨k, hk, hc⟩ := Pin.one_gate_at 6 restricted1 3 false s
    ⟨fun i => decide (i = 6), by decide +kernel⟩
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), by decide +kernel⟩ h
  have e : (fun x => restricted1 (Function.update x 3 false)) = restricted0 := by
    funext x; revert x; decide +kernel
  rw [e] at hc
  have := restricted0_bound k hc
  omega

theorem lower (s : ℕ) (h : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6)) s) : 10 ≤ s := by
  have eq : (fun x : Fin 7 → Bool => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6)) = restricted1 := by funext x; revert x; decide +kernel
  rw [eq] at h
  have := restricted1_bound s h
  omega
end PEqualNP.Outside.L_meta_11693

namespace PEqualNP.Outside.L_meta_11693
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeValue (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def boolValue (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem same_value : ∀ x, edgeValue x = boolValue x := by decide +kernel

-- Each block recognizes a complete multipartite subgraph of the target graph.
def monoCircuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
     ⟨GateOp.or, [4, 6]⟩,
     ⟨GateOp.and, [7, 8]⟩,
     ⟨GateOp.or, [0, 2]⟩,
     ⟨GateOp.or, [10, 4]⟩,
     ⟨GateOp.and, [11, 5]⟩,
     ⟨GateOp.or, [2, 3]⟩,
     ⟨GateOp.and, [13, 6]⟩,
     ⟨GateOp.or, [9, 12]⟩,
     ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ops : ∀ g ∈ monoCircuit.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem computes : ∀ x : Fin 7 → Bool, monoCircuit.eval (List.ofFn x) = boolValue x := by decide +kernel
end PEqualNP.Outside.L_meta_11693

theorem PEqualNP.Outside.L_meta_11693 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _ heval
  have hsize : PEqualNP.MetaComplexity.HasCircuitSize 7 PEqualNP.Outside.L_meta_11693.boolValue gates.length := by
    refine ⟨⟨gates, o⟩, ?_, Nat.le_refl _, ?_⟩
    · intro g hg
      obtain ⟨ha, hb⟩ := hfan g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha, hb⟩
    · intro x
      exact (heval x).trans (PEqualNP.Outside.L_meta_11693.same_value x)
  have h := PEqualNP.Outside.L_meta_11693.lower gates.length hsize
  refine ⟨PEqualNP.Outside.L_meta_11693.monoCircuit.gates, PEqualNP.Outside.L_meta_11693.monoCircuit.output, PEqualNP.Outside.L_meta_11693.ops, ?_, ?_⟩
  · exact h
  · intro x
    exact (PEqualNP.Outside.L_meta_11693.computes x).trans (PEqualNP.Outside.L_meta_11693.same_value x).symm
