import Mathlib
import PEqualNP.Defs

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
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

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

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
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
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
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
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
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
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

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

end Live514

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

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
  induction h with
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

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

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

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
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
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
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
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

end Live514

namespace Live514

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

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
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
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
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

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
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
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
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

end Live514

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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

def rows550 : List ℕ := [73, 9, 73, 73, 226, 178, 226, 202, 9, 178, 226, 9, 18, 101, 9, 101, 136, 138, 69, 97, 50, 33, 20, 146, 8, 98, 144, 202, 73, 37, 37, 33, 178, 18, 5, 178, 5, 16, 8, 194, 228, 66, 73, 162, 2, 132, 34, 50, 20, 138, 2, 18, 74, 33, 37, 65, 192, 128, 138, 224, 144, 192, 33, 16, 18, 69, 146, 196, 20, 130, 66, 34, 73, 9, 73, 73, 228, 180, 228, 101, 9, 180, 228, 9, 20, 202, 9, 202, 33, 37, 74, 200, 148, 136, 18, 52, 1, 196, 48, 101, 73, 138, 138, 136, 180, 20, 10, 180, 10, 16, 1, 100, 226, 68, 73, 164, 4, 34, 132, 148, 18, 37, 4, 20, 69, 136, 138, 72, 96, 32, 37, 224, 48, 96, 136, 16, 20, 74, 52, 98, 18, 36, 68, 132, 105, 13, 89, 77, 234, 182, 230, 234, 137, 242, 242, 17, 22, 103, 25, 117, 152, 26, 77, 105, 51, 35, 84, 147, 40, 99, 208, 154, 193, 45, 13, 161, 186, 26, 21, 154, 133, 17, 12, 195, 204, 3, 67, 163, 3, 6, 38, 35, 80, 140, 6, 17, 70, 129, 161, 129, 129, 129, 152, 208, 80, 208, 112, 129, 24, 76, 134, 134, 49, 6, 193, 3, 201, 11, 89, 75, 229, 182, 230, 229, 41, 244, 244, 24, 22, 206, 25, 218, 49, 21, 75, 201, 156, 140, 82, 60, 129, 204, 112, 53, 104, 139, 11, 168, 181, 21, 26, 53, 42, 24, 3, 108, 99, 12, 76, 172, 12, 6, 134, 140, 80, 35, 6, 24, 70, 40, 168, 40, 40, 40, 49, 112, 80, 112, 208, 40, 17, 67, 38, 38, 152, 6, 104, 12]

def xs550 : List ℕ := [0x30402014b690f419fd083e89eb4f2bce90f00041204401903498f0240e00414f02ce90f, 0x2e001661546044b06aac0014fe8b0ab236f01a004121146044a000e5041eda8b0a9216f0, 0xac0014fe8b0ab236f02e001661546044b06ae5041eda8b0a9216f01a004121146044a000, 0xd083e89eb4f2bce90f030402014b690f419f0240e00414f02ce90f00041204401903498f, 0x117c09002f0cd3de24117c09002f0cd3de24159009802b04d01220159009802b04d01220, 0x4cafe209999c8107f0104040c801a338a6f12c3f0229890c8306f0804860c909e238a670, 0x4278110580164ca6dd4278110580164ca6dd4a299007801a0ca4dd4a299007801a0ca4dd, 0x104040c801a338a6f14cafe209999c8107f0804860c909e238a6702c3f0229890c8306f0]

abbrev f550 : BFn 8 := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7))

theorem rows550_len : rows550.length = 288 := by decide +kernel

theorem enc_inputs550 :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rows550)
      = xs550 := by decide +kernel

theorem enc_goal550 : encL f550 rows550 = goal 144 := by decide +kernel

theorem mask550 : mask 144 = 2 ^ rows550.length - 1 := by decide +kernel

theorem proper_fail550 : ∀ zs ∈ xs550.sublists, zs ≠ xs550 →
    (cov 144 zs &&& lo 144) ≠ lo 144 := by decide +kernel

theorem no_sub550 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 144) (goal 144) s xs550) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xs550 → NatRun (mask 144) (goal 144) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs550
  · subst e; exact noRunFull s hs h
  · exact proper_fail550 zs (List.mem_sublists.2 hz) e (required h)

theorem main550 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 144) (goal 144) s xs550) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7)) s → 11 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f550 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 144) (encL f550 rows550) s' (ws.map fun a => encL a rows550) :=
    Run.map (fun a : BFn 8 => encL a rows550)
      (fun a => by rw [mask550]; exact encL_inv a rows550)
      (fun a b => encL_and a b rows550) (fun a b => encL_or a b rows550) hrun
  rw [enc_goal550] at hr
  refine no_sub550 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs550]
  exact hsub.map _

end Live514

namespace Live514

def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h

end Live514

namespace Live514

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
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
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
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
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end Live514

namespace Live514

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
  induction h with
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
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
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
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end Live514

namespace Live514

def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

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
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end Live514

namespace Live514

def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/4 < N s && (rot (v/2 % 2) zs).isPerm (S s (v/4)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/4 < N s && (rot (v/2 % 2) zs).isPerm (S s (v/4))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end Live514

namespace Live514

def t1 : Nat := 0x600c410f0000000000600c410f00000004001000490f00000004001000490f

def t2 : Nat := 0x1210800914083e0089090800100000000000000000000000000000000000000

def t3 : Nat := 0x400409020000000000b08921620100001000000400000050008800b00901220

def t4 : Nat := 0xb0802009000000000146004a00a00041200000802008002004000146004a000

def t5 : Nat := 0x40002000a0600c00000889088006f000004001006000a0002404020889088206f0

def t6 : Nat := 0x40012108a0f14c83e00899988007f000004001006000a0002404020889088206f0

def t7 : Nat := 0xc801023026f00c0002011000000060800000c80902100670080000210000000000

def t8 : Nat := 0xc801233826f14c83e2099090800160800000c80902100670080000210000000000

def t9 : Nat := 0x100480020026d002001001000044a04840001002800a0004d00a000001000004a000

def t10 : Nat := 0x400801800006f00000400801800006f0000800090900000670000800090900000670

def t11 : Nat := 0x400801a10806f14083e00891908007f0000800090900000670000800090900000670

def t12 : Nat := 0x40c800a32820d14c83e20990900001d08048604900e228a450282f022980080304d0

def t13 : Nat := 0x4020109080101901000408800a238a0010004020000080300800040600000e028a000

def t14 : Nat := 0x2c0000090c810620104000000100108620041000000904800220000000800900100220

def t15 : Nat := 0x400000000208a6d14028000180140006d000080001000208a4500829000180080004d0

def t16 : Nat := 0x400000012108869140abe0089094800700000000000000000000000000000000000000

def t17 : Nat := 0x400000012308a6d140abe00990948007d000080001000208a4500829000180080004d0

def t18 : Nat := 0x7801000004408604007801000004408604000000000000000000000000000000000000

def t19 : Nat := 0x7801000004488695407801008014408604000000000000000000000000000000000000

def t20 : Nat := 0x780100000648a6d54078010180144086d400080001000208a4500829000180080004d0

def t21 : Nat := 0x780100012548869540fbe1089094c08704000000000000000000000000000000000000

def t22 : Nat := 0x781104800640a6d402781101000444a64c40001002800a0004d00a000001000004a000

def t23 : Nat := 0x10400000b0803400410000800240090c804000000000000000000000000000000000000

def t24 : Nat := 0x10400000b290b40955083e808b49090c904000000000000000000000000000000000000

def t25 : Nat := 0x17c01000b0c43c604107809002404d0ce04000000000000000000000000000000000000

def t26 : Nat := 0x17c01000b2f4be6d550fbe909b494d0cfd400080001000208a4500829000180080004d0

def t27 : Nat := 0x200000100000c009d4000000480120ca00d00001004001800008d0200800400100ca00d

def t28 : Nat := 0x2000201406004000a8000009e8002b02000000000000000000000000000000000000000

def t29 : Nat := 0x200020141610c009bc083e09e9092b02100000000000000000000000000000000000000

def t30 : Nat := 0x278010100044c869d4078010480164ca60d00001004001800008d0200800400100ca00d

def t31 : Nat := 0x278110100044006d040781104801640a64048291003800a0004d04a29800380020ca450

def t32 : Nat := 0x30402014a4807410e9000089624623ce80f00041204401903498f0240e00414f02ce90f

def t33 : Nat := 0x30402014b690f409fd083e89eb492b0e904000000000000000000000000000000000000

def t34 : Nat := 0x30402014b690f419fd083e89eb4f2bce90f00041204401903498f0240e00414f02ce90f

def t35 : Nat := 0x37c03014b6d4fc79fd0fbe99eb4f6fcef0f00041204401903498f0240e00414f02ce90f

def t36 : Nat := 0x1000408801a338a0914087e20999988101900040600000e028a000000402000008030080

def t37 : Nat := 0x1040000001211886b140afe008999c810720000000800900100220041000000904800220

def t38 : Nat := 0x10404088018338069140afe2011094010100804820c80982380670083b00210004010000

def t39 : Nat := 0x104040c801a338a6f14cafe209999c8107f0804860c909e238a6702c3f0229890c8306f0

def t40 : Nat := 0x107841c801a778a6f54cffe309999cc187f4804860c909e238a6702c3f0229890c8306f0

def t41 : Nat := 0x110408002f08935820110408002f08935820159009802b04d01220159009802b04d01220

def t42 : Nat := 0x117c09002f0cd3ce04117c09002f0cd3ce04000000000000000000000000000000000000

def t43 : Nat := 0x117c09002f0cd3de24117c09002f0cd3de24159009802b04d01220159009802b04d01220

def t44 : Nat := 0x117c09002f2ddbdeb551ffe908bf9cd3df24159009802b04d01220159009802b04d01220

def t45 : Nat := 0x117c49c82faffbfef55dffeb09bf9cd3dff495d869c92be6f8b6703dbf0ba9ab0cd316f0

def t46 : Nat := 0x134442c94beb3fe7ffdcafea9fbdfebdefff804c72cd49fb3befff2e7fe22d9dfcafefff

def t47 : Nat := 0x1350090064614cc80fc1bfa916aa1c83490412c0e10474f16ce90f65b79e16e21d83598f

def t48 : Nat := 0x137c0b0164654dc80fd1ffe99eaa9eb34f041afbe12574f56de90fe5ffbedeeb9fbb5fff

def t49 : Nat := 0x137c0b016f6cd7de2e917c099eaf0ef3fe24159009802b04d01220159009802b04d01220

def t50 : Nat := 0x137c0b016f6ddfdfbfd1ffe99ebffeffff2f15941b846b1dd35baf17d0e9843ff4fcfb2f

def t51 : Nat := 0x2c00146000000030602c0014600000003060000000000000000000000000000000000000

def t52 : Nat := 0x2d0406604b09031020bc83ecfa3480b01820b5960ff86b05d31220b5d26df83fe4f01220

def t53 : Nat := 0x2e001661406004306aac0014fe8002b03060000000000000000000000000000000000000

def t54 : Nat := 0x2e001661546044b06aac0014fe8b0ab236f01a004121146044a000e5041eda8b0a9216f0

def t55 : Nat := 0x2e00166155614cb0fbec83f4fe9b9ab237f01a004121146044a000e5041eda8b0a9216f0

def t56 : Nat := 0x2e781761546444b66eac7815fe8b0ef2b6f41a004121146044a000e5041eda8b0a9216f0

def t57 : Nat := 0x2f0416614b090310f0fc83fcfeb492b03860fdbf1ffbeb0fd316f0fffbedfbbfe6fcb670

def t58 : Nat := 0x2f0416615f694ff1fffc83fcfebffabeffff1a045325547947e98fe744fede9ffabeffff

def t59 : Nat := 0x2f7c17614b0d4316f0fcfbfdfeb496f0be60fdbf1ffbeb0fd316f0fffbedfbbfe6fcb670

def t60 : Nat := 0x3d7c1d602f0cd3fe643d7c1d602f0cd3fe64159009802b04d01220159009802b04d01220

def t61 : Nat := 0x3e4056e955e37cb6fbecaff6ff9b9eb337f09a4861e91de27ca670ed3f1efb8b0e9316f0

def t62 : Nat := 0x3f7c1f617f6cd7fe6ebd7c1dfeaf0ef3fef41f9049a13f64d4b220f5941fdaab0ed216f0

def t63 : Nat := 0x4083e0089090800100000000000121080091000000000000000000000000000000000000

def t64 : Nat := 0x4083e00891b18801914083e00891b1880191000000000000000000000000000000000000

def t65 : Nat := 0x4278110580164ca6dd4278110580164ca6dd4a299007801a0ca4dd4a299007801a0ca4dd

def t66 : Nat := 0x4278110580764ce7df4278110580764ce7df4a299007801a0ceddf4a299007801a0ceddf

def t67 : Nat := 0x4278110581374ca6dd42fbf10d9096cca7dd4a299007801a0ca4dd4a299007801a0ca4dd

def t68 : Nat := 0x427811058b1e4ea6dd4278110594764ca6df4a2d9207801a0ea4dd4a29d007947a0ca4dd

def t69 : Nat := 0x42781305c0764ca6dfc278119f8016fca6dd4a299007801a0ca4dd4a299007801a0ca4dd

def t70 : Nat := 0x427c1305891e4da7dd5278518d80b67ca6dd4a2d9207801a0fa4dd4a69f00780fa2ca4dd

def t71 : Nat := 0x42fbf10d9096cca7dd4278110581374ca6dd4a299007801a0ca4dd4a299007801a0ca4dd

def t72 : Nat := 0x437c11058b1e4fe6dd52781905a416dceedd4a299007801a0ca4dd4a299007801a0ca4dd

def t73 : Nat := 0x437c1305cb7f4fe7dfd2fbf99fb4f6fcefdf4a2d9207c01b0feddf4a69f00794fa2ceddf

def t74 : Nat := 0x4cafe209999c8107f0104040c801a338a6f12c3f0229890c8306f0804860c909e238a670

def t75 : Nat := 0x4cafe20999bd8907f150c3e0c891b3b8a7f12c3f0229890c8306f0804860c909e238a670

def t76 : Nat := 0x4cafe2099b9c8307f0104040c815e33ca6fb2c3f1229890c8306f0824860c91de23ca670

def t77 : Nat := 0x4cafe2099b9c9317f0104040c805a378b6f12d3f0aa98b0c9316f0904861c909e278a670

def t78 : Nat := 0x4cafe2099d9cc197f0104040c80babbab6f13c3f0329890cc306f0854868c90be2b8b670

def t79 : Nat := 0x4cafe2c9999eb127f01c4042c911a338a6f1ac3f02e9890e9306f0884860e909e238a670

def t80 : Nat := 0x4caff20d999e8127f0124050c901a37ca6f96c3f122b890e8306f08a4860c909e23ca670

def t81 : Nat := 0x4cffe309999cc187f4107841c801a778a6f52c3f0229890c8306f0804860c909e238a670

def t82 : Nat := 0x4dafe2099b9c8347f4104048c825a3b8eef52c3f0229890c8306f0804860c909e238a670

def t83 : Nat := 0x4eafe209d9fc8507fa904040de81a3b8a6f12c3f0229890c8306f0804860c909e238a670

def t84 : Nat := 0x4efff30d999ecda7fd527851cd81b77ca6fd6e3f922f891e8fa6fdca69f0cf89fa3ca6fd

def t85 : Nat := 0x4fafe209dbfd8f47ffd0c3e8deb5f3bcefff2c3f122dc91d834fff8248e0cd1df23cef7f

def t86 : Nat := 0x50c3e0c891b3b8a7f14cafe20999bd8907f1804860c909e238a6702c3f0229890c8306f0

def t87 : Nat := 0x51ffe908bf9cd3df24117c09002f2ddbdeb5159009802b04d01220159009802b04d01220

def t88 : Nat := 0x51ffe908bfbddbdfb551ffe908bfbddbdfb5159009802b04d01220159009802b04d01220

def t89 : Nat := 0x537c1905af1edffefd537c1905af1edffefd5fb99987ab1edcb6fd5fb99987ab1edcb6fd

def t90 : Nat := 0x53ffeb0174f54dc90fd1ffe99eab9fbb4f951afbe12574f56de90fe5ffbedeeb9fbb5fff

def t91 : Nat := 0x5cafea09bd9c91cff4114440c80bab3be6f52c3f0229890c8306f0804860c909e238a670

def t92 : Nat := 0x5cefe209999c9187f0106c40c809afb9a6f12c3f02a9890c9306f0845860c909e6b8a670

def t93 : Nat := 0x5cefe2c999bfb9a7f15cefe2c999bfb9a7f1ac7f62e989eebba6f0ac7f62e989eebba6f0

def t94 : Nat := 0x5dffeb09bf9cd3dff4117c49c82faffbfef53dbf0ba9ab0cd316f095d869c92be6f8b670

def t95 : Nat := 0x5dffeb09bfbddbdff551ffe9c8bfbffbfff53dbf0ba9ab0cd316f095d869c92be6f8b670

def t96 : Nat := 0x6caff669999c8137f03c4054e801a338b6f12c3f0229890c8306f0804860c909e238a670

def t97 : Nat := 0x6e78156580164cb6fd6e78156580164cb6fd4a299007801a0ca4dd4a299007801a0ca4dd

def t98 : Nat := 0x6e781765d4764cb6ffee7815ff8b1efeb6fd5a29d127947a4ca4ddef2d9edf8b1a9eb6fd

def t99 : Nat := 0x6e83f669d4f0c4b16aac0014fe8b2bba36f11a004121146044a000e5041eda8b0a9216f0

def t100 : Nat := 0x6eaff669ddfcc5b7fabc4054fe8babbab6f13e3f43299d6cc7a6f0e54c7edb8beabab6f0

def t101 : Nat := 0x6ffff769db9dc317f0fcfbfdfeb5b7f8bef1fdbf1ffbeb0fd316f0fffbedfbbfe6fcb670

def t102 : Nat := 0xa20014f640632c200bee83b637d05004010ac240f45654f32ce90f6a279636d41907498f

def t103 : Nat := 0xac0014fe8b0ab236f02e001661546044b06ae5041eda8b0a9216f01a004121146044a000

def t104 : Nat := 0xac0014fe8b2bba36f16e83f669d4f0c4b16ae5041eda8b0a9216f01a004121146044a000

def t105 : Nat := 0xac0416ff8b0ab337f03e0056e954e27cb06be5041eda8b0a9316f01a40612114e06ca000

def t106 : Nat := 0xac7815fe8b0ef2b6f42e781761546444b66ee5041eda8b0a9216f01a004121146044a000

def t107 : Nat := 0xad0414fe8b0ab376f43e001e617460d4f86ee5041eda8b0a9216f01a004121146044a000

def t108 : Nat := 0xae0016f740632c20dbee83f6ffd0d224214aea6ff67fd4fb2feddfea6ff67fd4fb2feddf

def t109 : Nat := 0xae0016ffcb6ab636faae0016ffd462f4b06ae5041eda8b0a9216f01a004121146044a000

def t110 : Nat := 0xae0016ffdf6af6b6faae0016ffdf6af6b6faff045ffb9f6ad6b6f0ff045ffb9f6ad6b6f0

def t111 : Nat := 0xaf0416ffcb6bbf77fffe83fefff4f2fcf96fe5041edecb1b935fff1a40e12514f06ce90f

def t112 : Nat := 0xb3501df666637ef80fefbfbf37fe5cc7590ed3c0fdd676f37cf90f7fb79f36f61dc7598f

def t113 : Nat := 0xb37c1df66f6ffffe2fffffbf37ff5cd7df2ed7d0fdd67ff7fcfb2f7fb79fb6ff1dd75baf

def t114 : Nat := 0xbc001cfeaf0ab2fef42f0416615f6847f06ee5041eda8b0a9216f01a004121146044a000

def t115 : Nat := 0xbd87eefa7fe9b35922bd87eefa7fe9b35922b5d66ff87fe5f35b22b5d66ff87fe5f35b22

def t116 : Nat := 0xbf501dfeef6bfefeffefbfbf77fe7cc7f96ef7c4ffdefffbfeffff7fb7df37f67dc7f98f

def t117 : Nat := 0xbf7c1ff76f6f7ffefffffffffffedef7ff6effffffffffffffffffffffffffffffffffff

def t118 : Nat := 0xbf87eefb7fe9bf59bffd87eefefffbbff92fb5d67ffc7ffdf35bafb7d6effc7ff5fffb2f

def t119 : Nat := 0xccafe29f999eb127f0124042c941e33ca6fb2c3f0229890c8306f0804860c909e238a670

def t120 : Nat := 0xd083e89eb4f2bce90f030402014b690f419f0240e00414f02ce90f00041204401903498f

def t121 : Nat := 0xd083e89eb5f3bce99f4387e209dbf98f419f0240e00414f02ce90f00041204401903498f

def t122 : Nat := 0xd0fbe99eb4f6fcef0f037c03014b6d4fc79f0240e00414f02ce90f00041204401903498f

def t123 : Nat := 0xd0fbe99eb4f6fcef9f437c0301cb7d4fc79f0240e00414f02ce90f00041204401903498f

def t124 : Nat := 0xd187e89ebffabfe90f13040a016f699fc99f0240e00414f02ce90f00041204401903498f

def t125 : Nat := 0xd1ffe99eab9fbb4f9553ffeb0174f54dc90fe5ffbedeeb9fbb5fff1afbe12574f56de90f

def t126 : Nat := 0xd1ffe99ebf9ef3ff24137c0b016f6ddfdebf159009802b04d01220159009802b04d01220

def t127 : Nat := 0xd1ffe99ebffeffef0f137c0b016f6ddfcf9f0240e00414f02ce90f00041204401903498f

def t128 : Nat := 0xd1ffe99ebffeffff2f137c0b016f6ddfdfbf17d0e9843ff4fcfb2f15941b846b1dd35baf

def t129 : Nat := 0xd283ea9ff4f2bce90f8304029fcb6bbf619f0240e00414f02ce90f00041204401903498f

def t130 : Nat := 0xd2fbf99fb4f6fcefdf437c1305cb7f4fe7df4a69f00794fa2ceddf4a2d9207c01b0feddf

def t131 : Nat := 0xd387ea9ffffbbfe99fd387ea9ffffbbfe99f0244f20454f92fe98f0244f20454f92fe98f

def t132 : Nat := 0xd3fffb9fffffffefdfd3fffb9fffffffefdf4a6df207d4fb2feddf4a6df207d4fb2feddf

def t133 : Nat := 0xec83f4fe9b9ab237f02e00166155614cb0fbe5041eda8b0a9216f01a004121146044a000

def t134 : Nat := 0xec87f6ff9b9ab337f03e0056e955e37cb0fbe5041eda8b0a9316f01a40612114e06ca000

def t135 : Nat := 0xecabf4fe9b9eb237f02e40166155614cb6fbe5041eda8b0a9216f01a004121146044a000

def t136 : Nat := 0xecaff6ff9b9eb337f03e4056e955e37cb6fbed3f1efb8b0e9316f09a4861e91de27ca670

def t137 : Nat := 0xee83f6ffd0f32c21dbee83f6ffd0f32c21dbea6ff67fd4fb2feddfea6ff67fd4fb2feddf

def t138 : Nat := 0xeefbf7ffd0f76ca7dfeefbf7ffd0f76ca7dfea6ff67fd4fb2feddfea6ff67fd4fb2feddf

def t139 : Nat := 0xefbfbf37fe5cc7590eb3501df666637ef80f7fb79f36f61dc7598fd3c0fdd676f37cf90f

def t140 : Nat := 0xfc83fcfeb4f2bcf96f2f0416614b690f71ff0240e00414f02ce90f00041204401903498f

def t141 : Nat := 0xfc83fcfebf9ab2fff42f0416615f694ff0ffe5041eda8b0a9216f01a004121146044a000

def t142 : Nat := 0xfc83fcfebffabeffff2f0416615f694ff1ffe744fede9ffabeffff1a045325547947e98f

def t143 : Nat := 0xfcfbfdfeb496f0be602f7c17614b0d4316f0fffbedfbbfe6fcb670fdbf1ffbeb0fd316f0

def t144 : Nat := 0xfdffffffbf9ef3fff43f7c5fe97feffffefffdbf1ffbab0ed316f09fd869e93fe6fcb670

def t145 : Nat := 0xff87fefffffbbf79fbff87fefffffbbf79fbffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [] else []) else (if i < 7 then [t34,t39,t43,t54,t122,t133] else [t34,t39,t43,t54,t122,t135]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t34,t39,t54,t65,t103,t126,t131] else [t34,t39,t54,t87,t103,t122]) else (if i < 11 then [t34,t39,t54,t94,t103,t127] else [t34,t39,t54,t103,t126,t130])) else (if i < 14 then (if i < 13 then [t34,t43,t55,t65,t120,t133] else [t34,t43,t55,t74,t103,t122]) else (if i < 15 then [t34,t43,t61,t65,t136,t140] else [t34,t44,t54,t65,t120,t133])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t34,t44,t54,t74,t103,t122] else [t34,t44,t54,t74,t103,t123]) else (if i < 19 then [t34,t45,t54,t94,t103,t122] else [t34,t54,t65,t88,t103,t120])) else (if i < 22 then (if i < 21 then [t2,t34,t43,t54,t65,t120,t133] else [t2,t34,t43,t54,t74,t103,t122]) else (if i < 23 then [t2,t34,t54,t65,t87,t103,t120] else [t2,t35,t43,t54,t74,t103,t120]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t16,t35,t43,t54,t74,t103,t120] else [t18,t34,t39,t43,t54,t120,t133]) else (if i < 27 then [t18,t34,t39,t54,t87,t103,t120] else [t18,t34,t45,t54,t94,t103,t120])) else (if i < 30 then (if i < 29 then [t19,t34,t44,t54,t74,t103,t120] else [t21,t34,t43,t54,t74,t103,t120]) else (if i < 31 then [t25,t34,t39,t54,t94,t103,t120] else [t26,t34,t43,t54,t74,t103,t120]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t29,t43,t54,t65,t74,t103,t120,t131] else [t29,t43,t54,t73,t74,t103,t120]) else (if i < 35 then [t33,t43,t54,t65,t74,t103,t120] else [t34,t39,t42,t54,t74,t103,t120])) else (if i < 38 then (if i < 37 then [t34,t39,t43,t48,t54,t65,t120] else [t34,t39,t43,t53,t65,t120,t136]) else (if i < 39 then [t34,t39,t43,t54,t57,t74,t103] else [t34,t39,t43,t54,t59,t65,t133]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t34,t39,t43,t54,t65,t120,t133] else [t34,t39,t43,t54,t65,t120,t134]) else (if i < 43 then [t34,t39,t43,t54,t65,t120,t141] else [t34,t39,t43,t54,t65,t136,t140])) else (if i < 46 then (if i < 45 then [t34,t39,t43,t54,t71,t120,t133] else [t34,t39,t43,t54,t73,t120,t133]) else (if i < 47 then [t34,t39,t43,t54,t74,t90,t122] else [t34,t39,t43,t54,t74,t103,t122])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t34,t39,t43,t54,t74,t103,t127] else [t34,t39,t43,t54,t74,t106,t122]) else (if i < 51 then [t34,t39,t43,t54,t81,t103,t122] else [t34,t39,t43,t54,t94,t103,t122])) else (if i < 54 then (if i < 53 then [t34,t39,t43,t54,t103,t112,t122] else [t34,t39,t43,t54,t103,t122,t136]) else (if i < 55 then [t34,t39,t43,t54,t115,t120,t133] else [t34,t39,t43,t54,t120,t130,t133]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t34,t39,t43,t56,t74,t103,t122] else [t34,t39,t43,t56,t74,t106,t120]) else (if i < 59 then [t34,t39,t43,t65,t99,t120,t133] else [t34,t39,t43,t65,t120,t125,t133])) else (if i < 62 then (if i < 61 then [t34,t39,t43,t74,t103,t122,t125] else [t34,t39,t54,t59,t65,t87,t103]) else (if i < 63 then [t34,t39,t54,t65,t87,t90,t120] else [t34,t39,t54,t65,t87,t103,t120])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t34,t39,t54,t65,t87,t120,t133] else [t34,t39,t54,t65,t103,t108,t120]) else (if i < 67 then [t34,t39,t54,t65,t103,t120,t126] else [t34,t39,t54,t65,t120,t133,t137])) else (if i < 70 then (if i < 69 then [t34,t39,t54,t71,t87,t103,t120] else [t34,t39,t54,t73,t87,t103,t120]) else (if i < 71 then [t34,t39,t54,t74,t103,t122,t137] else [t34,t39,t54,t87,t103,t115,t120]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t34,t39,t54,t87,t103,t120,t130] else [t34,t39,t54,t94,t103,t128,t130]) else (if i < 75 then [t34,t39,t65,t87,t99,t103,t120] else [t34,t39,t65,t87,t103,t120,t125])) else (if i < 78 then (if i < 77 then [t34,t40,t43,t54,t74,t103,t122] else [t34,t43,t45,t54,t65,t120,t133]) else (if i < 79 then [t34,t43,t45,t54,t74,t103,t122] else [t34,t43,t51,t61,t65,t120,t136])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t34,t43,t54,t61,t65,t120,t133] else [t34,t43,t54,t61,t74,t103,t122]) else (if i < 83 then [t34,t43,t54,t64,t65,t103,t120] else [t34,t43,t54,t65,t74,t104,t121])) else (if i < 86 then (if i < 85 then [t34,t43,t54,t65,t75,t103,t121] else [t34,t43,t54,t65,t86,t120,t133]) else (if i < 87 then [t34,t43,t54,t65,t120,t133,t139] else [t34,t43,t54,t74,t103,t122,t139]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t34,t43,t55,t59,t65,t74,t103] else [t34,t43,t55,t65,t74,t103,t121]) else (if i < 91 then [t34,t43,t61,t65,t74,t103,t140] else [t34,t44,t54,t59,t65,t74,t103])) else (if i < 94 then (if i < 93 then [t34,t44,t54,t65,t74,t103,t121] else [t34,t44,t54,t65,t75,t103,t120]) else (if i < 95 then [t34,t44,t54,t65,t94,t103,t120] else [t34,t44,t54,t65,t95,t103,t120]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t34,t44,t54,t65,t103,t112,t120] else [t34,t44,t54,t65,t103,t120,t136]) else (if i < 99 then [t35,t39,t43,t54,t59,t74,t103] else [t35,t39,t43,t54,t74,t103,t122])) else (if i < 102 then (if i < 101 then [t2,t18,t34,t43,t54,t74,t103,t120] else [t2,t34,t43,t54,t59,t65,t74,t103]) else (if i < 103 then [t2,t34,t43,t54,t63,t65,t103,t120] else [t2,t34,t43,t54,t65,t74,t90,t120]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t2,t34,t43,t54,t65,t74,t103,t120] else [t2,t34,t43,t54,t65,t74,t103,t121]) else (if i < 107 then [t2,t34,t43,t54,t65,t74,t104,t120] else [t2,t34,t43,t54,t65,t75,t103,t120])) else (if i < 110 then (if i < 109 then [t2,t34,t43,t54,t65,t94,t103,t120] else [t2,t34,t43,t54,t65,t103,t112,t120]) else (if i < 111 then [t2,t34,t43,t54,t65,t103,t120,t136] else [t2,t34,t43,t54,t67,t74,t103,t120])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t2,t34,t43,t54,t73,t74,t103,t120] else [t2,t34,t43,t54,t74,t103,t115,t120]) else (if i < 115 then [t2,t34,t43,t54,t74,t103,t120,t130] else [t2,t34,t43,t55,t65,t74,t103,t120])) else (if i < 118 then (if i < 117 then [t2,t34,t43,t65,t74,t103,t120,t125] else [t2,t34,t44,t54,t65,t74,t103,t120]) else (if i < 119 then [t2,t34,t54,t65,t74,t103,t120,t137] else [t2,t43,t54,t65,t74,t103,t120,t143]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t6,t34,t43,t54,t65,t74,t103,t120] else [t8,t34,t43,t54,t65,t74,t103,t120]) else (if i < 123 then [t11,t34,t43,t54,t65,t74,t103,t120] else [t12,t34,t43,t54,t65,t74,t103,t120])) else (if i < 126 then (if i < 125 then [t12,t34,t54,t65,t74,t103,t120,t137] else [t17,t34,t43,t54,t65,t74,t103,t120]) else (if i < 127 then [t17,t34,t43,t54,t73,t74,t103,t120] else [t18,t34,t39,t43,t54,t59,t74,t103]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t18,t34,t39,t43,t54,t74,t90,t120] else [t18,t34,t39,t43,t54,t74,t103,t120]) else (if i < 131 then [t18,t34,t39,t43,t54,t74,t103,t122] else [t18,t34,t39,t43,t54,t74,t106,t120])) else (if i < 134 then (if i < 133 then [t18,t34,t39,t43,t54,t81,t103,t120] else [t18,t34,t39,t43,t54,t94,t103,t120]) else (if i < 135 then [t18,t34,t39,t43,t54,t103,t112,t120] else [t18,t34,t39,t43,t54,t103,t120,t136]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t18,t34,t39,t54,t74,t103,t120,t137] else [t20,t34,t39,t43,t54,t74,t103,t120]) else (if i < 139 then [t20,t34,t43,t45,t54,t74,t103,t120] else [t22,t34,t39,t43,t54,t74,t103,t120])) else (if i < 142 then (if i < 141 then [t24,t34,t43,t54,t65,t74,t103,t120] else [t25,t34,t39,t43,t54,t74,t103,t120]) else (if i < 143 then [t29,t34,t43,t54,t65,t74,t103,t120] else [t30,t34,t39,t43,t54,t74,t103,t120])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t31,t34,t39,t43,t54,t59,t74,t103] else [t31,t34,t39,t43,t54,t74,t103,t120]) else (if i < 147 then [t32,t34,t43,t54,t65,t74,t103,t120] else [t34,t35,t39,t43,t54,t74,t103,t120])) else (if i < 150 then (if i < 149 then [t34,t36,t43,t54,t65,t74,t103,t120] else [t34,t37,t43,t54,t65,t74,t103,t120]) else (if i < 151 then [t34,t38,t43,t54,t65,t74,t103,t120] else [t34,t38,t43,t65,t74,t103,t120,t125]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t34,t39,t41,t43,t54,t74,t103,t120] else [t34,t39,t43,t47,t54,t65,t103,t120]) else (if i < 155 then [t34,t39,t43,t51,t54,t65,t120,t136] else [t34,t39,t43,t52,t54,t74,t103,t120])) else (if i < 158 then (if i < 157 then [t34,t39,t43,t53,t65,t74,t103,t120] else [t34,t39,t43,t54,t59,t65,t74,t90]) else (if i < 159 then [t34,t39,t43,t54,t59,t65,t74,t103] else [t34,t39,t43,t54,t59,t65,t94,t103]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t34,t39,t43,t54,t59,t65,t101,t103] else [t34,t39,t43,t54,t59,t65,t103,t112]) else (if i < 163 then [t34,t39,t43,t54,t59,t65,t103,t136] else [t34,t39,t43,t54,t59,t73,t74,t103])) else (if i < 166 then (if i < 165 then [t34,t39,t43,t54,t59,t74,t103,t115] else [t34,t39,t43,t54,t59,t74,t103,t130]) else (if i < 167 then [t34,t39,t43,t54,t65,t74,t90,t120] else [t34,t39,t43,t54,t65,t74,t103,t120]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t34,t39,t43,t54,t65,t74,t103,t121] else [t34,t39,t43,t54,t65,t74,t103,t122]) else (if i < 171 then [t34,t39,t43,t54,t65,t74,t103,t124] else [t34,t39,t43,t54,t65,t74,t103,t129])) else (if i < 174 then (if i < 173 then [t34,t39,t43,t54,t65,t74,t103,t140] else [t34,t39,t43,t54,t65,t74,t104,t120]) else (if i < 175 then [t34,t39,t43,t54,t65,t74,t105,t120] else [t34,t39,t43,t54,t65,t74,t106,t120])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t34,t39,t43,t54,t65,t74,t107,t120] else [t34,t39,t43,t54,t65,t74,t109,t120]) else (if i < 179 then [t34,t39,t43,t54,t65,t74,t114,t120] else [t34,t39,t43,t54,t65,t74,t120,t133])) else (if i < 182 then (if i < 181 then [t34,t39,t43,t54,t65,t75,t103,t120] else [t34,t39,t43,t54,t65,t76,t103,t120]) else (if i < 183 then [t34,t39,t43,t54,t65,t77,t103,t120] else [t34,t39,t43,t54,t65,t78,t103,t120]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t34,t39,t43,t54,t65,t79,t103,t120] else [t34,t39,t43,t54,t65,t80,t103,t120]) else (if i < 187 then [t34,t39,t43,t54,t65,t81,t103,t120] else [t34,t39,t43,t54,t65,t82,t103,t120])) else (if i < 190 then (if i < 189 then [t34,t39,t43,t54,t65,t83,t103,t120] else [t34,t39,t43,t54,t65,t87,t103,t120]) else (if i < 191 then [t34,t39,t43,t54,t65,t90,t94,t120] else [t34,t39,t43,t54,t65,t90,t112,t120])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t34,t39,t43,t54,t65,t90,t120,t136] else [t34,t39,t43,t54,t65,t91,t103,t120]) else (if i < 195 then [t34,t39,t43,t54,t65,t92,t103,t120] else [t34,t39,t43,t54,t65,t94,t103,t120])) else (if i < 198 then (if i < 197 then [t34,t39,t43,t54,t65,t96,t103,t120] else [t34,t39,t43,t54,t65,t101,t103,t120]) else (if i < 199 then [t34,t39,t43,t54,t65,t102,t103,t120] else [t34,t39,t43,t54,t65,t103,t112,t120]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t34,t39,t43,t54,t65,t103,t113,t120] else [t34,t39,t43,t54,t65,t103,t116,t120]) else (if i < 203 then [t34,t39,t43,t54,t65,t103,t117,t120] else [t34,t39,t43,t54,t65,t103,t119,t120])) else (if i < 206 then (if i < 205 then [t34,t39,t43,t54,t65,t103,t120,t131,t136] else [t34,t39,t43,t54,t65,t103,t120,t133]) else (if i < 207 then [t34,t39,t43,t54,t65,t103,t120,t136] else [t34,t39,t43,t54,t65,t103,t120,t144])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t34,t39,t43,t54,t65,t111,t120,t136] else [t34,t39,t43,t54,t65,t120,t133]) else (if i < 211 then [t34,t39,t43,t54,t65,t120,t136,t142] else [t34,t39,t43,t54,t66,t74,t103,t120])) else (if i < 214 then (if i < 213 then [t34,t39,t43,t54,t67,t74,t103,t120] else [t34,t39,t43,t54,t68,t74,t103,t120]) else (if i < 215 then [t34,t39,t43,t54,t69,t74,t103,t120] else [t34,t39,t43,t54,t70,t74,t103,t120]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t34,t39,t43,t54,t72,t74,t103,t120] else [t34,t39,t43,t54,t73,t74,t90,t120]) else (if i < 219 then [t34,t39,t43,t54,t73,t74,t103,t120] else [t34,t39,t43,t54,t73,t94,t103,t120])) else (if i < 222 then (if i < 221 then [t34,t39,t43,t54,t73,t103,t112,t120] else [t34,t39,t43,t54,t73,t103,t120,t136]) else (if i < 223 then [t34,t39,t43,t54,t74,t90,t115,t120] else [t34,t39,t43,t54,t74,t90,t120,t130]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t34,t39,t43,t54,t74,t97,t103,t120] else [t34,t39,t43,t54,t74,t103,t115,t120]) else (if i < 227 then [t34,t39,t43,t54,t74,t103,t118,t120] else [t34,t39,t43,t54,t74,t103,t120,t132])) else (if i < 230 then (if i < 229 then [t34,t39,t43,t54,t74,t103,t120,t138] else [t34,t39,t43,t54,t74,t103,t120,t145]) else (if i < 231 then [t34,t39,t43,t54,t74,t103,t122] else [t34,t39,t43,t54,t74,t103,t128,t130]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t34,t39,t43,t54,t94,t103,t115,t120] else [t34,t39,t43,t54,t94,t103,t120,t130]) else (if i < 235 then [t34,t39,t43,t54,t103,t112,t115,t120] else [t34,t39,t43,t54,t103,t112,t120,t130])) else (if i < 238 then (if i < 237 then [t34,t39,t43,t54,t103,t115,t120,t136] else [t34,t39,t43,t54,t103,t120,t130,t136]) else (if i < 239 then [t34,t39,t43,t59,t65,t74,t103,t125] else [t34,t39,t43,t65,t74,t90,t120,t125])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t34,t39,t43,t65,t94,t103,t120,t125] else [t34,t39,t43,t65,t103,t112,t120,t125]) else (if i < 243 then [t34,t39,t43,t65,t103,t120,t125,t136] else [t34,t39,t44,t54,t65,t74,t103,t120])) else (if i < 246 then (if i < 245 then [t34,t39,t49,t54,t65,t74,t103,t120] else [t34,t39,t54,t59,t65,t74,t103,t137]) else (if i < 247 then [t34,t39,t54,t60,t65,t74,t103,t120] else [t34,t39,t54,t65,t74,t90,t120,t137]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t34,t39,t54,t65,t74,t103,t120,t137] else [t34,t39,t54,t65,t87,t103,t120]) else (if i < 251 then [t34,t39,t54,t65,t94,t103,t120,t128] else [t34,t39,t54,t65,t94,t103,t120,t137])) else (if i < 254 then (if i < 253 then [t34,t39,t54,t65,t103,t112,t120,t137] else [t34,t39,t54,t65,t103,t120,t136,t137]) else (if i < 255 then [t34,t39,t54,t73,t74,t103,t120,t137] else [t34,t39,t54,t74,t103,t115,t120,t137])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t34,t39,t54,t74,t103,t120,t137,t138] else [t34,t43,t45,t54,t59,t65,t74,t103]) else (if i < 259 then [t34,t43,t45,t54,t65,t94,t103,t120] else [t34,t43,t45,t54,t65,t103,t112,t120])) else (if i < 262 then (if i < 261 then [t34,t43,t45,t54,t65,t103,t120,t136] else [t34,t43,t54,t59,t61,t65,t74,t103]) else (if i < 263 then [t34,t43,t54,t59,t65,t74,t103,t139] else [t34,t43,t54,t61,t65,t103,t112,t120]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t34,t43,t54,t61,t65,t103,t120,t136] else [t34,t43,t54,t65,t103,t112,t120,t139]) else (if i < 267 then [t39,t43,t54,t59,t65,t74,t103,t143] else [t1,t34,t39,t43,t54,t65,t74,t103,t120])) else (if i < 270 then (if i < 269 then [t2,t34,t39,t43,t54,t65,t74,t103,t120] else [t2,t34,t43,t54,t65,t74,t103,t120]) else (if i < 271 then [t3,t34,t39,t43,t54,t65,t74,t103,t120] else [t4,t34,t39,t43,t54,t65,t74,t103,t120])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t5,t34,t39,t43,t54,t65,t74,t103,t120] else [t7,t34,t39,t43,t54,t65,t74,t103,t120]) else (if i < 275 then [t9,t34,t39,t43,t54,t65,t74,t103,t120] else [t10,t34,t39,t43,t54,t65,t74,t103,t120])) else (if i < 278 then (if i < 277 then [t13,t34,t39,t43,t54,t65,t74,t103,t120] else [t14,t34,t39,t43,t54,t65,t74,t103,t120]) else (if i < 279 then [t15,t34,t39,t43,t54,t65,t74,t103,t120] else [t18,t34,t39,t43,t54,t65,t74,t103,t120]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t18,t34,t39,t43,t54,t74,t103,t120] else [t23,t34,t39,t43,t54,t65,t74,t103,t120]) else (if i < 283 then [t27,t34,t39,t43,t54,t65,t74,t103,t120] else [t28,t34,t39,t43,t54,t65,t74,t103,t120])) else (if i < 286 then (if i < 285 then [t34,t34,t39,t43,t54,t65,t74,t103,t120] else [t34,t39,t39,t43,t54,t65,t74,t103,t120]) else (if i < 287 then [t34,t39,t43,t43,t54,t65,t74,t103,t120] else [t34,t39,t43,t45,t54,t65,t74,t103,t120]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t34,t39,t43,t46,t54,t65,t74,t103,t120] else [t34,t39,t43,t50,t54,t65,t74,t103,t120]) else (if i < 291 then [t34,t39,t43,t51,t54,t65,t74,t103,t120] else [t34,t39,t43,t54,t54,t65,t74,t103,t120])) else (if i < 294 then (if i < 293 then [t34,t39,t43,t54,t58,t65,t74,t103,t120] else [t34,t39,t43,t54,t59,t65,t74,t103]) else (if i < 295 then [t34,t39,t43,t54,t59,t65,t74,t103,t120] else [t34,t39,t43,t54,t61,t65,t74,t103,t120]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t34,t39,t43,t54,t62,t65,t74,t103,t120] else [t34,t39,t43,t54,t65,t65,t74,t103,t120]) else (if i < 299 then [t34,t39,t43,t54,t65,t73,t74,t103,t120] else [t34,t39,t43,t54,t65,t74,t84,t103,t120])) else (if i < 302 then (if i < 301 then [t34,t39,t43,t54,t65,t74,t85,t103,t120] else [t34,t39,t43,t54,t65,t74,t89,t103,t120]) else (if i < 303 then [t34,t39,t43,t54,t65,t74,t90,t103,t120] else [t34,t39,t43,t54,t65,t74,t90,t120])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t34,t39,t43,t54,t65,t74,t93,t103,t120] else [t34,t39,t43,t54,t65,t74,t98,t103,t120]) else (if i < 307 then [t34,t39,t43,t54,t65,t74,t100,t103,t120] else [t34,t39,t43,t54,t65,t74,t103,t110,t120])) else (if i < 310 then (if i < 309 then [t34,t39,t43,t54,t65,t74,t103,t111,t120] else [t34,t39,t43,t54,t65,t74,t103,t112,t120]) else (if i < 311 then [t34,t39,t43,t54,t65,t74,t103,t115,t120] else [t34,t39,t43,t54,t65,t74,t103,t120]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t34,t39,t43,t54,t65,t74,t103,t120,t131] else [t34,t39,t43,t54,t65,t74,t103,t120,t137]) else (if i < 315 then [t34,t39,t43,t54,t65,t94,t103,t120] else [t34,t39,t43,t54,t65,t103,t112,t120])) else (if i < 318 then (if i < 317 then [t34,t39,t43,t54,t65,t103,t120,t136] else [t34,t39,t43,t54,t73,t74,t103,t120]) else (if i < 319 then [t34,t39,t43,t54,t74,t103,t115,t120] else [t34,t39,t54,t65,t74,t103,t120,t137])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t34,t39,t43,t54,t65,t74,t103,t120] else []) else []) else []) else []) else []) else [])) else []))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then 0x2106e1c0f045518148701c8ea408de1b8841c1153c118090560bcfa46cae1f05622cfc430ae1582422d0c3f0ae2085622cfc430ae0905622cfc46cae1fc8422cee3f11c1b88422cee465181d482220f9475090907222cfc430ae0905622d1e430ae090561c10e418ae208561090b418ae1f0721c0fc418ae0905622cfc418ae2106e1c1193b9181b8841c0ee465180905622cfc430ae090561c0fc430ae1b88422cee3c118208561c0fc418ae1f0561c0fc418ae1b8841c0ee3c1182106e1c0f03b9181dc421c8ea408dd1ac231c8f647cdd1ac231c8f6408dd2282f1c8ea408dd1ac231c8ea408dd090561c0fc418ae else 0x208771c0ee2ed180905608cfc418ae0bc8222912475091b8771c0ee3c11816c8a1c0ee3f11c090841c0ee3c11809084148e237d181d48222912475091b88a148e237d182286e20cf04551816c771c0ee3f11c0908a1c0ee3c11822c58220f94750921877208fb3fd1c1f07208d0b418ae1f0721c10e418ae1c87c1c1063f0ae2106e1f8f542d182106e15cf542d18208721c0fc418ae090561c11e430ae1b88415d0b3d518158241c1063f0ae090561c097378ae090561090b418ae090561c10e378ae2085608d0b418ae208561090b474ae1f0721c0fc46cae1f0721c0fc430ae090561c097418ae090721c0fc418ae) else (if i < 96 then 0x20884184e237d181b8841c0ee2ed181b8841c1163c1181b8871c1152ed18208561090b390ae16c421c0ee3f11c090561c10e430ae1f0721c0fc430a21f0561c11e430a21f0721c11e418a21b8771c1152ed18090562310b46cae090562310b474ae1b88a15cee3d51820877148e237d1820877184e237d181b877184e237d180dc841c0ee3c118090561c0fc46cae0905608d0b418ae1ac231c8ea47cdd21024148df389181f8771c0ee3f11c1f8421c0ee3f11c090561c11e418ae1b8421c0ee3c1181b88a1c0ee37d1816c841c0ee3f11c1b88420cee3c1181f8771c1153f11c208771c0ee3c1180908a148e237d18 else 0x1dc421c8f647cdd22c58228fb475091f0721c11e418ae1b8841f90b3d5181f07222d0e474ae208721090b474ae1fc841c0ee3f11c2085608cfa474ae1f07222d1e46cae20856108b3418ae2282f1c8eb408dd2388922cfc43102238891c8ea4790c1b88722cee465182087222cfc46cae2288c1c8ea408e41f07222cfc430ae1f07222d1e430ae20856230fc474ae2288c1c8f647ce42088722d164651820856230fa474ae1c87c22d1d478ae2282f1c8f647cdd2106e224f63e91820872230fa474ae1f07222d1e474ae22c58148df4190916c77209123fd1c1f0721c11e430ae1588415cee3d518208841c0ee3c118)) else (if i < 192 then (if i < 160 then 0x1f8421c1143f11c16c871c0ee3f11c1b88720cee37d181b87722cee37d181086e20cdf451181dc6e1c0df3b9181b8771c0ee37d181b88422cee3f9181f07222cfc474ae208562310b474ae21877209123fd1c1c87c22d1d438ae0907222d0e430ae0907222d1e430ae0905622d0e474ae0905622d1e474ae0908922cfc430ae2188a22d1645d1c2188c22cee45d1c22c581ccdf4190922c5823cdf475092287e22cfc4311f0907222d0e46cae0907222d1e46cae20872230fa418ae208721090b418ae218772091247d1c1b8842250b3d9181dc7e1c8f647d061dc6e1f8f542d181b8841f8ee3d51822c582291247509 else 0x16c77209154791c2087722d153c1181f0721090b418a3184571c8ea478de22c58184df419092085622cfc474ae208721c0fc474ae1f0721c0fc474ae0905622cfc474ae1dc8215cf53f11820872108fc474ae208561090e418ae20872108fc418ae20856230fc418ae20856108fc418ae208561090b418e0090560bcfa418ae1f0722310b46ca318c7208d0b418a3090560bd0b46cae1f07208d0b418a31b88415cee3d51816c241c1193f0f01b87720d153c1182188a20d164391c090771491537d182087720d153c1181b87720d1537d182286e218f042d182187720d154391c1b88a20d153c118208771c0ee37d18) else (if i < 224 then 0x20856108b3474ae1dc821c0bb3b918090560bcfc474ae1f07208cfc418ae09056108fc474ae0dc771c0ee2ed181d4822291241909210241c0f03f1181c8841f9143d5181f07208d14418ae1b8841f9143d518208721090b390ae1f07222d0e430ae184571c8ea4090616c7722cee3f11c1602f2291d455092246e184df419191dc421c8f6408dd1f0721090b418ae1847e1c8f647cde184571c8f6478de1f0721090b390a31f072108b3418a31dc421c8ea478dd20877184e23c1181b8421c0ee37d181d482228f041909208771c0ee3d5181dc821c0f03b91816c87185164391c184571c8ea380de1f0721090b474a3 else 0x2288922cfc4751f23889230fa475022388922cfc4311f04c8b2211d3e51e16c720bd193b8eb1dc701c8f647cde2305823cdf4750922c5823cfb475091f0722311e474ae23c7e1c8f647d061f072230fc418ae208721091e474ae208722311e474ae208722310b474e0208721090b474e020872230fc474ae1b884224fa3d91820872230fa474e01f072230fa474a31b88c22cee3f9181b87722cee3c1181b88422d153f91816c8422cee3f11c1b082228b441909090561c0ee418ae09056108b3418ae1f0561c0ee418ae1dc8222cf045518184571c8ea408de20856108b3390ae1dc82184df389182085610917418ae))) else (if i < 384 then (if i < 320 then (if i < 288 then 0x20856230fa418ae208771f9152ed18208771f90b2ed181b884225143d9181b8771f9143d5181608b1cd0637d092087210914474ae20872230fa418e01f072230fa474e01f0722310b474e01f0721090b418e01f072230fa418e016c871c0ee4191c16c771c0ee4191c1f8421c1144191c208771c0ee3ad182288c1c8ea478e41dc421c8f6478dd1f0722310b474a31f072230fa418a3208721090b418e01086e218f042d182088c20d1537d182184220d144791c2188c2391647d1c1b84220d1437d182188c20d164791c2088c20d153c11823c7e230fa4751f23c7e22cfc4311f2188a22d1845d1c1f88422cee3f11c else 0x1587e2291d448f61f07222cfc430f01f07222d1e474f01f07222d1e430f00905622cfc430f020856230fa474f02087223114474ae1b88422514465182087722d15465182088a22d153f9182188c22d164791c2088a22d154651821c6e22cfe451181b8872250b465181b88722d143f9182188c22d144791c1608b23d1d3e5092085623117418ae1dc821c0f0479181dc821f8bb455181dc821f8bb479182087223117474ae20872230fc418ae21c8222d19459182086c229062d1091dc821c0f53b9181dc82184f0389181b8891850637d191dc6e1f8f52cd1820872108b3418ae20872108b3474ae2085623117474ae) else (if i < 352 then 0x1608b23d1d3ed091c8892291d448f62288c1c91947ce42088b2291d3ed191dc8222cf04791820875229062d10921c8222d19479181dc82184f041d181dc821f8bb47d181608c23d1d37d092088b1850637d191dc82184eb3891f2087210914474e02087223114474e02087223115474e02087210915474e0208722311c474e00908a1491537d181b88a22d153f9181b8842250b465182188a22d164391c2187722d154391c2087722d153f918 else 0)) else 0))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x101 else 0x101) else (if i < 7 then 0x291028f0000028f028d028f028f028f028f028d0006020000020a06 else 0x29302950000029501dd029502950295029501dd0006020000020a06))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x299000002970000000303 else 0x1e701e9000001e901e701e901e901e901e901e70006020000020a06) else (if i < 11 then 0x1ef000001ef029b01ed00fb00fb00fb00fb00fb00fb00010603000000000c08 else 0x257029d02a302a5029f0000000002a702a10257025702990257025702570004000004000c00020f09)) else (if i < 14 then (if i < 13 then 0x2a901dd01db01dd01db000001db01db01db01db0005040000000a06 else 0xcd00cb00cb02ab00cb00cb00cb00cb00cb0600000300010a06) else (if i < 15 then 0x26502610263026b020f00000269026302630263026d02630263026300000a04000001000e08 else 0xd901dd01db01dd01db000001db01db01db01db0005040000000a06)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0xcd00cb00cb01df00cb00cb00cb00cb00cb0600000300010a06 else 0xcd00cb00cb01df00cb00cb00cb00cb00cb0600000300010a06) else (if i < 19 then 0x1ef000001ef02ad01ed01eb01eb01eb01eb01eb01eb00010603000000000c08 else 0x1e1000000db00db00db00db00db01e100db00d90005000000040a06)) else (if i < 22 then (if i < 21 then 0x1db01db01db01db01dd01dd01db000001db01db01db01db01db001801db002400d901db01db01db01db01db00080b140005000300010500160c else 0xcb00cd00cb001c00cb01df00cb00cb00cb00cb00cb00cb00cb00cb002800cb00cb00cb00cb00cb00cb140402080901000a0300000300170d) else (if i < 23 then 0xdb00db00d9003401e100db00db00db01e100db00db00db00db00db00db002600db00db00db00db00db0208040a03000f000603080000170d else 0xcb00cd00cb000200cb01df00cb00cb00cb00cb00cb00cb00cb00cb000e00cb00cb00cb00cb00cb00cb140402080901000a0300000300170d))) else (if i < 28 then (if i < 26 then (if i < 25 then 0xcb00cd00cb000600cb01df00cb00cb00cb00cb00cb00cb00cb00cb000e00cb00cb00cb00cb00cb00cb140402080901000a0300000300170d else 0x1e300ff01e301e501e3000001e3001e01dd01e301e301e301e301dd01e301e301e301e301e301e301e3000c10090000030400000501160c) else (if i < 27 then 0x1e9000c01e901e901e701e901e9002a01e701e901e901e901e901e701e901e901e901e901e901e900ff000710090000030400000401160c else 0x1eb01eb01eb01ed00d901eb003001f101eb01eb01eb01eb01ef003201eb01eb01ef01eb01eb01eb01eb01eb01eb111404020001000a0502000001180d)) else (if i < 30 then (if i < 29 then 0x2c000000cd00d100cb00cb01df00cb00cb00d300cb00cb00cb00cb00cb000e00cb00cb00cb00cb00cb00cb08100002050200080200000100170d else 0xcb000001df000000cb000000cb00cb00cb00cb00cb00cd00cb00cb00cb00cb00cb00cb00cb000100090000000300000500130c) else (if i < 31 then 0x1ed01f500fb001001f300fb00fb00fb00fb01ef00fb00fb00fb01ef00fb00fb00fb00fb00fb00fb0e080102000100000502000001160d else 0x47004701f700470047004700cd004700470047020109050400050b07))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x1f9000a000001fb0000000000000706 else 0x11b00e900e901fd01fb00e900e90201020300e900e900e900e900e901ff00e9001600e900e900e900e900e900e90514040c030000080208000300180d) else (if i < 35 then 0x115011b011502050201011d0115011501150115011501ff0115000001150115020701fb0115011501150010000c0006000a00000400150c else 0x11700000021000000210021002100f70021002100cb0021002101ed00210021002100210021000d0c0302050000020201130b)) else (if i < 38 then (if i < 37 then 0x17b000101 else 0x20d0209020d021300000000020d020d020f021501370211020d020d020d020b020d020d020d020d020d020d05030903030100000900000000160d) else (if i < 39 then 0x21000101 else 0x17b000101))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x21b01db00ff021901e300000217017b017b017b017b017b017b017b00050004000500000e08 else 0x21b01db00ff021901e300000217017b017b017b017b017b017b017b00050004000500000e08) else (if i < 43 then 0x1910189017d021f0221021f019100ff01910191021d0191019100ff0191050d010506010600001009 else 0x14101390225013701330105013300200223013b01330227013300e5007f013301330133013302050100080200060c0b08140b)) else (if i < 46 then (if i < 45 then 0x22d022f00ff022901e300000217022b022b022b022b022b022b022b00050004000500000e08 else 0x21701e301dd0217000001e5021702170231021701dd0217021700ff02170217021700090003010503000000110a) else (if i < 47 then 0x21000101 else 0xf7000001ab002100cb02330021002100210021002100210021002100020504000300000e08)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x2100210010002100cb00f7002102330021002100210021011700210021023500210010010c010002060203120a else 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08) else (if i < 51 then 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08 else 0xfd00210021002100cb0021002100f70061002100fb00300021002100ff00ff0021002100210010010902050900030100140b)) else (if i < 54 then (if i < 53 then 0x21000101 else 0x23901ab01ab00fd010b023701ab010101ab023701ab01df0000010701ab01ab01ab01ab000f0002070909000200120a) else (if i < 55 then 0x17b000101 else 0xff000000ff023d017d00ff00ff00d900ff00d900ff023b00ff00ff00ff00ff00ff00ff000f000b030907020200120a))) else (if i < 60 then (if i < 58 then (if i < 57 then 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08 else 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08) else (if i < 59 then 0xf500ff0000023f010d00000023002300d50023002300230023012d00230007030007030101020f09 else 0x17b000101)) else (if i < 62 then (if i < 61 then 0x21000101 else 0xed000101) else (if i < 63 then 0xed000101 else 0x2450241000000db024300ed00ed00ed016500ff00ed00ed00ed00ed00030406000102000e08)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x12d010d00230023023f00d500ff00230023002300f5002300230108030000030800030f09 else 0xed000101) else (if i < 67 then 0x1bd024d00140000000801bd024b0249024701bd01c901bd024d025101bd01bd01bd01bd01bd024f0402040102000209080705140b else 0x17b000101)) else (if i < 70 then (if i < 69 then 0x10d012d000000d500f5002300230023023f00ff002300230023002300030406000102000e08 else 0x245024301e102530245000002450245025500ff01e1024502450245024502450245040c0008000300000000110a) else (if i < 71 then 0x21000101 else 0xed000101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x25900d900ff00ff00ff00d900ff00ff00ff01c900ff00ff00ff00ff00ff025700ff00090206060400000c0c0c130b else 0xfb00dd00dd00ff000000ff025b00fb00fb00fb00fb00fb00fb00fb00040004000002000e08) else (if i < 75 then 0x10d002300230023012d024100ff00f5025d002300230023002300000509000305000e08 else 0xed000101)) else (if i < 78 then (if i < 77 then 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08 else 0x23101dd023101db01db021902190219021900d902190219021902190219021900040006020301000300110a) else (if i < 79 then 0x2101010021025f0021004700210021000000f70021002100cb0021005f003000cd002100210021000e130005010c00070000140b else 0x26302610267002002630261026902630263026d0263026302630263026502630263026b0263020f0263002202630263026302631413000c0c021202000d0a000001011b0f)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x1e5021b01db01e501db0000021b026f021b017d021b021b017d021b021b021b021b021b00090505080000030301120a else 0x27100f700f700d300f700f700f70239027300f7027100f700f700f700f700f700f7100f0104000001030701120a) else (if i < 83 then 0xd5000000cd00d500d5003400d500cd00db00d500d500d500d500d500d900d500d500d500d504000f0100040702040100130b else 0x27702790000027b0275027d002d0277027702770277027702770277000b0604000a0a000e08)) else (if i < 86 then (if i < 85 then 0x1900dd000000cb00d500df002d0019001900190019001900190019000b0604000a0a000e08 else 0x10d00d5000000ff00f5002300230023012d023f0023002300230023000a0006000100000e08) else (if i < 87 then 0x17b000101 else 0x21000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x19000101 else 0x1900dd000000cb00d500df027f0019001900190019001900190019000b0604000a0a000e08) else (if i < 91 then 0x1d500200000028b028301d5028102890285028701d501d5011d01d501d50289026f01d501d501d5070d090001040601000000140b else 0x19000101)) else (if i < 94 then (if i < 93 then 0x1900dd000000cb00d500df002d0019001900190019001900190019000b0604000a0a000e08 else 0x1900dd000000cb00d500df002d0019001900190019001900190019000b0604000a0a000e08) else (if i < 95 then 0xdd00e100cb001900000019001900d700df00e3001900190019001900190b03070003000000080f09 else 0xe30019001900e100cb00e10019001900dd00190019001900d7001900df00190009000c070402070000110a))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x19000101 else 0xe7002d00000000002f00e5002f002d01df002d002d002d002d00d7002d002d002d00d7002d06010300000a0900060600130b) else (if i < 99 then 0x21000101 else 0xf7000000f9002100cb00f50021002100210021002100210021002100020504000300000e08)) else (if i < 102 then (if i < 101 then 0xcb000400cb00d3000c00cb00cb00cb00cb00cf00cb00cb00cb00cb00cb00cb002400cb00cb001a00cd00d100cb00cb00cb00cb00cb00cb00cb001600cb00cb00cb00cb00cb00cb231e1d1c031c11190c19130b0115000e0401000c002615 else 0x110011c000000000019000100000504) else (if i < 103 then 0xd500d500d5000200d900d5000a00d500d500d500d500d500d500d500d700cd00d500d500db00d500d500d500d50000000800cd00d500d500d500f800d500d500d500d500d500d5000c1d1c0005101a00010900000a1b04001418022514 else 0x9e00de000000190000000000000504))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x19000000190019001900d500dd001900df002d00ae0019001900cb001900190019005200190019001900190019001900190019001914010c000f15000d030008090006031b0f else 0x1000019002d001900fc00cb01200019001900190019001900d500dd0019002d00190019001900190019001900df00190019011400190019001900190019001511100e0018001603090714020000022011) else (if i < 107 then 0x190019001900190019001900cb00dd0019002d00d5000500fc00190019001900df0019001900190019001900da009a0019001900190019001904000e170300180019081413020e0401001f11 else 0x19001900190019000500cb001900dd0019002d00d50019010000190019012400df00190019001900190019001901060019001900190019001904000f17110017000305150b09010408001f11)) else (if i < 110 then (if i < 109 then 0x190019001900190019001900cb0019001900dd00e100e1001900d700e30128001900190019001900df0019001900e60019001900190019001902000e17140018001803131109020002001f11 else 0x10a0130000000190000000000000504) else (if i < 111 then 0x2d002d002d002d007100d7002d001500d7002d00cf002d002d002d00e7002d0134002f00e5002d002d002f002d002d00f2002d002d002d002d002d1d000b17110018000203161509020007001f11 else 0x19000000190019001900d500dd00c20019002d0019001900cb001900df0019006200190019001900190019001900190019001900190019150010001016000d050109040106051c0f)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0xdf00df00dd000000df00df00df00df00df00df00df00cb00df00cd00df00df002f00e9002f00df00df00df00df00df00df00df008e00d200df00df00df00df0c000c1a150016000308130200010000112011 else 0x8a00ce000000190000000000000504) else (if i < 115 then 0xdd0000000000d900dd002d00cb00dd00dd00dd00dd00dd00dd00dd00dd00dd00dd00c600dd00dd00dd00dd00dd00dd00dd006600dd00dd00dd00dd00dd0c0d0e091200000015030b0709010100001f11 else 0x19011400620019010600eb00d50019001900dd002d0019001900b200190019001900520019001900df0019009a001900190019001900190019001900cb002d00190019001900190019001900520019001900190019001f1a1e170001001e230619170b0e1f1406001a1712102c17)) else (if i < 118 then (if i < 117 then 0x1900aa0000000303 else 0x19012000c200190124000500d50019001900dd002d0019001900ae00190019001900ae0019001900df001900da001900190019001900190019001900cb002d00190019001900190019001900b20019001900190019001f1a1e170001001e230619170b0e1f1406001a1712102c17) else (if i < 119 then 0x1900be0000000303 else 0xa600190000004e0100000403))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x10001000100ed0021002100210001000f00190052000100190001000100010001000100010000001100010a0300030100150c else 0x2d0000001900190019001900ef0019001900df00d500190019001900190019001900dd00190019110b0007000201070106040104160d) else (if i < 123 then 0x17001700450017004700450017001700f10019001700170019000f001700170017001700000700000200000c0a0a130b else 0x1000100210001002100210001000100d50019000100010019000f000100010001000101000700000f00000c0903130b)) else (if i < 126 then (if i < 125 then 0x1000101 else 0x17001700450017004700450017001700d50019001700170019000f001700170017001701000700000f00000c0903130b) else (if i < 127 then 0x4500f300df004500cd004700450045004500df004500450045004500450045004500450045004500451407000e0204040f0000070003170d else 0x2101380000000303))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0xa20068000000210000000000000504 else 0xf500210021006e005f002100210021006c0009005d0021002100cb00210021002100f7002100210021002100210021002100210000000007180002131400080503000200011c10) else (if i < 131 then 0x6c00cb00210009002100900021002100f500210021002100210021002100210021007800f70021005f00f9002100210021007400210021013c00210021005d00e000210021002100210021006c0021002100210021001d1c1f1526261e162010140c080612200400070212012c17 else 0x210000002100210021002100f700940021005d000900f5002100740021005f0021002100210021009200cb0021002100210021002100210021002118000f1519000a0f0b010b0605020503001f11)) else (if i < 134 then (if i < 133 then 0x2100090021005f002100f5002100210078005d002100210021002100cb002100e200f70021002100210021002100210021002100210c01140700190000000401070015031c0f else 0xff0021002100210021002100f700cb0061002100ff00fd002100ff002100210021007c002100210021002100210021001c005f00fb0021002100ea002100210021141d0015001c051a100b00110702040012002212) else (if i < 135 then 0x10e0080000000210000000000000504 else 0x103005d00f60084005d005d00cf005d005d0105005d005d00fd005d0107005d010b0105005d005d005d0109005d0101005d010b005d005d005d005d130010110e0000000308011819010012001f11))) else (if i < 140 then (if i < 138 then (if i < 137 then 0xca0021000000c80100000403 else 0x210021002100210047010d0021004700210009000d0021002100210021002100210021000300000e0e0304000a01130b) else (if i < 139 then 0xd1002100890021000000210021002100470021004700210021002100210021002100210021010f002100210f0f00000e0505010400010000170d else 0x410000004100410041004101130041004100410021010d01110041005f0009005d004100410041000010000d0b0004000a0a140b)) else (if i < 142 then (if i < 141 then 0x190019001900d500ae001900190019001900dd00cb0019002f0019002f0019011500190019001900df005a00190019001900190019001900000000061b0000011400090016000900011d10 else 0x2100210021002100f700210021002100210117000900f500210070011900210028002100210021002100cb00210021006e0021005f0021002100211700111609000011180b000211010503001f11) else (if i < 143 then 0xdf00dd003400190115011b002f00190019001900d5001900300019011d00190019001900190019011f0019001900d3001900ba0052003500190019001900190e1c0000171804160a0d0b000b00000800022112 else 0x10001000100010001012300010001006e0021004901210001005f0009005d000100010001000012000d0d000600050c140b)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x41000101 else 0x410041004100410127010d0041012500210021000d0041002100410041004100410041000310000c000301000500130b) else (if i < 147 then 0x19000101 else 0x21002100f50009005f00090009005f010b012b006e005f0021002100210009005f00d3005f0129005f005f0021005f0021005f005f0021005f00d3000c005f005f0021005f161a120e1c1008110d1d0e0f11010d000108002413)) else (if i < 150 then (if i < 149 then 0x2d0019000000000019001900190019012f00df012d001900df00190056001900190019001900190019001900191210030005030d0b0200010300170d else 0x2d00000019001900190019001900dd00cb00df00490019001900ae0019001900190019001900190019121001030f010c080003010001160d) else (if i < 151 then 0x12d001900cb001900df00dd013100190019001900190019001900000019001900190019000e0407000300000100120a else 0x19000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x21000101 else 0xf000101) else (if i < 155 then 0x133000001330133013b01330139013d0133013301330133007f01330141005c01050133013300ec01330135013f011a006b013301370133006b013300e5013301330133001f19121116140716000b050602000300012212 else 0x21000101)) else (if i < 158 then (if i < 157 then 0x149014300000143014d0143014b0143014900440151014301430145006d014b014301470143014301430143014f011d01430143014301430c07140006080609000201020001001c0f else 0x101) else (if i < 159 then 0x1000101 else 0x1000101))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x13000101 else 0x101) else (if i < 163 then 0xf000101 else 0x21000101)) else (if i < 166 then (if i < 165 then 0x101 else 0x21000101) else (if i < 167 then 0x1000101 else 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x100210153002300210000001f0021001b0001000100010019001900010001000100010019000100010003001400070c0900020003150c else 0x10001000100010001004100210011002101550023002100010001002100590001000100010019002100210001000100010019005700010001050900181b00120019170c0806030401001f11) else (if i < 171 then 0x2300010021000100210021006b00190001000100010019000100000001000100010001000e0407000300000100120a else 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a)) else (if i < 174 then (if i < 173 then 0xf008b008b007f000f0081005c000f0118000f000f0083000f0085005d006b008700150089000f002d006d000f000f000f0a0e180001040e0001000c060001001b0f else 0x210000000100010021000100010001002100190001002300190003001b0001000100010001001901000c02010f02000c0c04140b) else (if i < 175 then 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x100210001002100010019002100010001002300010019000100010055004100010001000102010a02040f0100090400140b)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x2300010021000100210021008300190001000100010019000100000001000100010001000e0407000300000100120a else 0x100210001014300210001001900210001000f00230001001900010001000f00010001000102000a01030f000d0b0302140b) else (if i < 179 then 0xb00010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x2300990099009900990157004f0157000f004f004f015b0009006301610157004f01570157000000630159015f00390099009900990099015d004f00030b1b000c021900000d04000802021e10)) else (if i < 182 then (if i < 181 then 0x1700000021000100010021000100010021000100190023000100190003000100bd00010001000100000a01000300000d0c0c140b else 0xb00030009000300070009000f001500050003000b0005000300000003000300030003000e0407000300000100120a) else (if i < 183 then 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x2300010047000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x2300010041000100410021000f00310001000100010031000100000001000100010001000e0407000300000100120a) else (if i < 187 then 0x590000000100010021002100010021001900230001000100010019000f000100010001000100000600010e00000a0702130b else 0x230001002100010021002100c100190001000100010019000100000001000100010001000e0407000300000100120a)) else (if i < 190 then (if i < 189 then 0x1002100010021000100190021000f00230001000100190001000f000100010001000101000801030e00000b0202130b else 0x163016300db016d00ed000b0163001800ac01690163016900ed01630163000b0163016300a100ed016300ff0165016b01670163016b00ed0165016300b700db012a0163016301630163001d0610000016020006111600150013001f04002614) else (if i < 191 then 0x1000101 else 0x101)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0xf000101 else 0xb00010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a) else (if i < 195 then 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x21001900010001000b002100010001000b002100190059000100830001000100010001000100010009010c00020603000d0c00150c)) else (if i < 198 then (if i < 197 then 0x2300010171000100210021000f016f000100010001016f000100000001000100010001000e0407000300000100120a else 0x590000001300130021017300130059017500230013001300130175007f001300130013001300000600010e00000a0702130b) else (if i < 199 then 0x1000101 else 0x1000101))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x1000101 else 0x13000101) else (if i < 203 then 0x23000101 else 0x830000006f008b006b000f0015005d0089000f000f002d007f000f000f000f000f000f000f000f0005050900000a0400030101150c)) else (if i < 206 then (if i < 205 then 0xf000f009f007900320179017700000000002d000000000200030a07 else 0x7f017d0050017b007f007f007f007f007f017b0183010501790185017f007f007f00a1007f007f0023007f017b018100a1017b0000007f017b017b00d7017b007f007f00211b1d001d0b1a1000090e070c0000000e2212) else (if i < 207 then 0xf01790000000f005d000f0133000f009f000f0083006b000f0015000f0089002d000f000f007f000f000f120f01000e0600080c00020000170d else 0x1870189007f00a10083003a007f00000179008300830083014100830177008300fd0083018b017d008300d700830083008300830083180e090304000b00030c06010101001b0f)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x9f009f018f0133000f009f00a1009f0179009f0044009f009f006b009f010b009f018d009f009f0089002f009f009f009f009f0018180204110902000002090002001b0f else 0x1400400050019100500088017b0050009c017b0050017b0050008c0000004c00e40108017b01810191017b017b0161017b0191017b0050017901930191017b007f0161019500f0017b007f0193007f019100640112017b00bc017b017b017b017b017b017b00a1007f017b017b017b007f0191017b017b0050017b007f0191017b017b017b017b017b017900a10191017b017b017b017b1800000013000000334800000e4a2649073c4847004645442e434241291f403f253a33301e21390f4d28) else (if i < 211 then 0xf017901790050017901330179000000000179000f000001990179019701070179017900150179017900e70179017901790179030b090403010800000501000002001a0f else 0x19b00210021002100210021000f00df00210021002100df002100000021002100210021000e0407000300000100120a)) else (if i < 214 then (if i < 213 then 0x100010001002100210017002100190023000100010001001900bd000100010001000101000600010f00000d0702130b else 0x10d00210021002100210021000f00df00210021002100df002100000021002100210021000e0407000300000100120a) else (if i < 215 then 0x2300010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a else 0x4f00010021000100210021000f00190001000100010019000100000001000100010001000e0407000300000100120a))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x2300010021000100210021006b00190001000100010019000100000001000100010001000e0407000300000100120a else 0x21000101) else (if i < 219 then 0x2100df002100210021002100210045010d002100df00210021006b0021002100210021002100210009010f00020603000d0200150c else 0x210021019d0021019d017700210021002800df002100210021004500fb002100210021002100df0021002100210021002100170d17000608010100070301011a0e)) else (if i < 222 then (if i < 221 then 0x21000101 else 0x6b019f006b01770000006b01970089006b01a1006b00f3006b0117006b006b01a3006b002f006b0177006b006b006b006b00130c010010010200000a000305190e) else (if i < 223 then 0x101 else 0x21000101))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x100210021000100010001016f01a50001002100010001016f00010001000f00010001000100110f01030100000c0308140b else 0x1000101) else (if i < 227 then 0x21000101 else 0x2100210021002100210045002100ff0000002101a7017700210021002100210021002100210021002100dd003c00210021002116090612000c0800000d010600001a0e)) else (if i < 230 then (if i < 229 then 0xbd0021002100cb0021002100f70021002100210021002100210021002101a900210021002102100a0a030d0400000000140b else 0x21000101) else (if i < 231 then 0x6c01ab006c00800021006c00a0006c00c80021006c010c002100840004006800e8006c005f002100210021002101ad007c000900210048005900210065002100610021002100120021013a006101ab01ab002100f4002100090021002101ab002100210021000901ab00210021005f0009006700210021006c002101ab00090047002100210021002101ab000901ab00210021002100471800000013000000330000000e301f4b073c4a49004847462e4522442943424125403f3a1e26390f4d28 else 0x21000900210021000000210009002101af002101b100210021002100d4002101a70021002100dd006c002100210021002103110805000f0101020001060001190e))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x1000101 else 0x2100210021002e002100ff0000002100ff002100210083002100210021002101a7002100590021002100dd00d400210021002100120a0f010d02000008020b02001a0e) else (if i < 235 then 0x101 else 0x21000101)) else (if i < 238 then (if i < 237 then 0xf000101 else 0xf01010083007f0036003b000f000f0000000f000f01b50177019901af000f0133009f0015000f000f01b3002d000f000f000f000f000a101501060000000503020001011b0f) else (if i < 239 then 0x101 else 0x101)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x1000101 else 0x101) else (if i < 243 then 0xf000101 else 0x190000001900210001000300250017001b001b0021002300010019001f0001001f00010001001700010001002100010019000100190001000100010200120d190000080e03170e080a0507001f11)) else (if i < 246 then (if i < 245 then 0x100210001014300210001001900210001000f00230001001900010001000f00010001000102000a01030f000d0b0302140b else 0x101) else (if i < 247 then 0x1b70009000001b9007d007d01b901bb0049007d01bb007d01bb000d007d007d007d007d00000800010c00000a0502130b else 0x101))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x1000101 else 0x2200a4000b00ac01bd00ac00ac00cc00ed00ac00dc00ed00d000ac000800a80136013200ed01c101bd00ed00ed000b00ed000b00ed00ac000b00ed01c300ed00ed00ed00ed00c400ed00b400ed000b01c3012e011e00ed00ed00ed01c100ed00ed00ed00ed01bd01c700ed00ed00ed000b01bd00ed00ed00ac00ed01bd000b01bf00ed00ed00ed00ed01c7000b01bd00ed00ed00ed01c51800480013000000330000000e4a4948073c474600261f452e4443422941403e253a33301e21390f4d28) else (if i < 251 then 0xb0000000b00d400ac00ff018701cf000b000b00ff000b01c901cd01cb000b019d000b000b00e1000b000b000b000b150b00140f0002000e05060102180d else 0x1000101)) else (if i < 254 then (if i < 253 then 0x101 else 0xf000101) else (if i < 255 then 0x21000101 else 0x101)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x21000101 else 0x1000101) else (if i < 259 then 0x100e10001002100e10001018b001900010059002100210001001c000100210019000100010001000100010001000100010a130004010c00010000000300011a0e else 0x1000101)) else (if i < 262 then (if i < 261 then 0x8901d100890089018b0179002f01b300890089013d0089008900890101008901d3008900890089008900890000008900890010000e000d000a010000000003190e else 0x19000101) else (if i < 263 then 0x101 else 0x19000101))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x150000000001d500150015017d00150015017d00ec00150015001501d3001501d5013901d7009f0015010901a3002f001501d9001500150015001519120000100007000304000009010208001e11 else 0x101) else (if i < 267 then 0x101 else 0xf000d000300010001000100070003001300050005000301bc00150003010c0003000300110003000300030001010c000900030003000b0001000900010003000f0007000300030001000300030003000b1a1b1d18201b13000300032217000f15001615002308062b17)) else (if i < 270 then (if i < 269 then 0x13e000301100001010c00190001000100170001001f000101400001000100010001001900010025001900010001000100210001001900010001000100010001000101c0001b000300190001001b0001000100010124002100010001001000010001002100010001023c00230001001d001700010001001f00010019010c00010001021b3635300a323d00303c3b333a332412010021132e112d2810000f23001d21160e4222 else 0x1800190019002d0019001900310014002d002d0019002d00390019001900190019003c001901b600330037002800000019001900290019002d00050019001900190019000c002d002d0005001900190031002400100019002b000500400005001900190010001900480019000800190019003801a60019002d0019000400190019001000200019001900190019004400270019000501660034002f00190010001900190010004c001c0019001900190005019a0019001000190010002700100019003000350010001902560019002c001900105e665b0000665900006558572e555062624f5f5f5c404f4b2b4c064947462841402400211d033f393b23373635321a1816120e09102a0c6b37) else (if i < 271 then 0x3f0001000100230001010c000100190001014a003d00010001002100010001003b0019000100010001000100010001000100210021000100010001000100010001014c00010001010c0001000100010001000100011d170f1b2316261209200c131b00001d1e07021e1f0c1e2c17 else 0xd000100030003000700030003000300050003010c00030001010c01c4001500030003000b000300030003000300030001000900090041000f000b000500010001014400030003000f0003000100030001000300031d082715241f28130900031c1b000815001616000213002c17)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x23000100000000010c000f000f0021000100010001000100010001000100010001000100010001000100010001000100010021000d0001001700010001002100010043000100010001010c00010001000100130b1f1e1f1700001d1809161914000005100707002916 else 0x100490017000f01500001000f00170017001700170001001700170017000100190001010c0017000100170001004500010045000d0017001700170017004700170001001900170001010c00170017001700150b1b212116000020191a160a1600001f00070d002a16) else (if i < 275 then 0x1000100230001010c00030021000f01540001010c000100010001000100010001000100010001000100010001000100010041000d00310001000100010041000100010031000100010001000100010001000a0b171d281517001d181915181402000111070b002a16 else 0x4b00010000010c00030021000f000100010001000100010001000100010001000100010001000100010001000100010021000d001700010001000100210001004d001700010001010c000100010001000a0b1b1e1f1600001e171b15181400000511070b002916)) else (if i < 278 then (if i < 277 then 0xd000100010001002100010001000100190003012800010001010c01cc001900010001004f00010001000100010001000100210021000100010001000100010001010c00010001000f0001000100010001000100011d082715241f28130900031c1b000815001616000213002c17 else 0xd0001000100010001004b001900030001017a0001002100010001000f0019000100010001000100010001000100210021000100010001000100010001010c00010001010c0001000100010001000100011b130f192116251309000c121b00001c1c07021c1e0c1c2b17) else (if i < 279 then 0x1010c002300010001000f001700030001000100010001000100010001000100210001000100010001000100010021000d0001000100010001002100010051001700010001010c000100010001001d0b00241b131e001e141b151510000005050707002916 else 0x1012e00010019000100030114000100010059000100010001000100210053011600570001000100230041005b00010019002100010001000100110001002100010001000100550001000101580001012c00010001000100010001010c00210001002100010001010c0001000100010001002100210074015a0001000100010001320e32313e0a003c001b302f002d373b3629213332142200242218141c02060015104222))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x2100740021002100590078005d005d005d00630021002100210021000200740021008c005d0021008e0021005d0021006c002100210021007000210067005d0061002100470021008800210009002100be007c007200740021005d0009009000090021002100740061008a00650021002100210021006e005d0208005d0021005f0000002100840021002100090009002100210074002100740047000900210082002100210074008000210021005f00bc0204005f00740021020a0021002100210009007e00210074002100740086007a0021603d280000675d0067655b595664605d5c544453271f4e2751231f4e4d4a1d47454405183f1a3e383a0936353430162f2e120e00100b036b37 else 0x100010001000100010176010c006b0118000100010003002100190023002101d000010001000100010001000100690021000100010001000100010001000100010001013a000100010001000100010130015c000100010019000100010001010c00010001192e202f2c2b0c2c2b1c14291d1b1e16201c120f1c030311001501341b) else (if i < 283 then 0x1900000001000100010023000100010003010c000f00010001000100010001000100110001000100010001000100010001000d0001000100010001000100010001001900010001010c00010001000100240b00231a11170001141f111c101a0005050707002916 else 0x1340023016002400001000100010001000100010001000100010001010c0001019e000f00010001000d0001000100210001000d0001000100190003006d0001011c0001000100010001000101c8000100010021010c00010001002100010001000100190001000100010000262500091a2b002825220017102e000500010000130400000b08361c)) else (if i < 286 then (if i < 285 then 0x23000300210003000101d8002100010019000100010001010c000100010001000100010001000100010001001000010001006b006f00030001010c005f00010001001900530001000100010001000100230d00001e161b001c170e011915061e0810010d002916 else 0x21000d000f000300010001000100010001000100230001000100210001000100010001000100170025000100010021010c000100010001010c0001000100010001000100011a1102120f1b1a030d0401070e10090d0000002413) else (if i < 287 then 0x1001900010001002300010001010c0001002100010001000300730001010c00010001000100010001002100210001000100010071017e0001017c0001007400010019000100010001005300010001000100250025180c130a000100011e000b1f011d0e160c152a16 else 0x23010c0001000100770021002100010001010c000100010001000100010001000100010001007500010001006b000100010001002500010001002100010001002100010001000100940001000100010001000100010003000300170017000100010001017e000100010025000100012b251b33331c000017150b2b0b0d00022e2d2a2c002c1d1d1f010f280000391e))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x1000100010001010c0001000100010001000100010021000d00010079000100010021000100230025000300010021000100010001000100010001000100010001010c00010001000100010001040020221e0012202101151a000c0914030007120a2815 else 0x23010c00030001005300530053007b0053005f00030053005300530035007d005300010001005f003d0035005300010001005300010001020e0053010c007d003500010053000100c400010001025a0053005300ac005f000100010053005300000001232b152d0029000000261200100f07211e2117010d090007191b321a) else (if i < 291 then 0xf00010180000f000f006b0001000101f00122000f000f0087000f000f0085000100150001008b0001007d0001010c000f00d80001000f0001000f000f006d005d000f0120000f000f000d000f006b000f007f02480089010c000f0083008b000f00810017000f000100da000f0182002d000f000f36351f00001b19312722120d2e0536302a2501001731072d2c10142e2a2b003c1f else 0x10c00010001010c0001000f0001002300010001000f0025000f000100010001000100210001000100010021000f0001000100010021000100010001000100010019000101aa0001001900010001002114201f1e0b1d200d13180a130d1409020d03012815)) else (if i < 294 then (if i < 293 then 0x2100210001000f000100010001010c010c0019000100010001000100010001000100010003002100010001000100010023000100010001000100010050008d0001008d0001000100010001000101ba0019000100010001000100251d0900121c0000210b1f0018000100060420001200062e18 else 0xec0000022800e800f800fc00e800f000e800b00100006c010c00e800e800e8000100e800040284027400f40298024400e4028800e818161404030b120f010a090d040c001b0f) else (if i < 295 then 0x1000f000f00010023002100010019000f000100010021000100010001000100010001000100010001004e01040001001900130003004100010184002100b400010001000100010001000100010001000118001a0e1d1c1302182517190004100000170c0112112a16 else 0x23001f000100010001000f000100010001000f0001000100190001000101aa008f0021000100010001010c00210001000100190025001900010021010c0017001900010001000100030001000f00010001000f00010087000f000f00190017001f00010001000100190001000100012b2c3131292a0030001511251a24002f1b01291b070d2b1d241b00150200391e))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x21009e0021010c000100010001000100010085000100010001002501ae009300950001000100210003000100010001000100190001000100910001000f002100010001000100750019000100010001000100010001010c000100000019000100230001251708290011032900271d2b21252601160b081e0f1b16011400321a else 0x570001000f004100010001000100010001001900110001000100230001010c00010001000100010001010c00010001000100010001000100010001000100190001000100012210000019130b001401050002001d00040f122413) else (if i < 299 then 0x10000002300010001000100010001000100010021000101d8000100010001000100010001000100210097004100010001000100640021002100190001001700010001010c00010001010c00210001000100210057001100030001006b00590001000100210001001900010001005700012a33002c2f102f0e00260001192a012b0100000b18290021122800191318391e else 0x10001000f00010001000100010011000100010001000100410099000100010019000100010013000100990001010c000100010001010c00010000000100010001001700190001000100010001000115170e001c1c00000f08121804020c0502001711002815)) else (if i < 302 then (if i < 301 then 0x10001000100030021010c000f00010001000100010001004b00010001010c000100010001000100010001000100170001002100190058000100010003000d0001000100010001009b00000021000100010019000100010001050024101f1a232104001a1a0114131c1a01110e0c080007002e19 else 0x9d0001000100010001000100010001000100010001000100110001010c001900110001000100010001002300410001005700010001010c00010001000100010001000100190000000100010001000116191a001c2000000a0812001505020e02001917002815) else (if i < 303 then 0x10001000100010003000100010001000100230021000100010001000100010001000f0001000100010001001900010021017000ca00010001000100010021000000000001001900130003000f0001000a20020d22191d181a120800190d170800001600142816 else 0x42022c010801ec010c0108010800ce01d4016c010801e80168000101080070024c000c023a02320108022a010800e40236010818160b140913130f01020f0d0404001b0f)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x10001000f000100010021001300170001004f000100010001000100010001000f001f009900010003000100010001010c00010001000100010001010c00010001002100010021000100010001001f0000000100031e001413061e191f120c17070f1c0b04001b00102a16 else 0x25000100010041000100230001001100010001000f0001000100010001000100010001000100010019000100110001000f010c00010001010c000100010001000100010019000100010000000100410001000100091f130327181e181a1102001813161100130500162a16) else (if i < 307 then 0x10001000f000100010013000f00010001004f000f00010001000100010001000100010001000100210001000f0001010c00010001000100010001010c0001001900210001002100010001000100190000009900031e000512191e191b130c131a0f171104130600172a16 else 0x10001000f000f000f000f000f007f010c0001000f000f000f000f000f000f00150041000f010c000d006f000f00890001006b000f0001000f0001000f000f000f0083005d00000001000f002d0075000f0001000b180115130f090027000014041125001f001c0c1b2a16)) else (if i < 310 then (if i < 309 then 0x6f006f006b0001007d00030001006f006f0001000f006f0001006f006f001700810054009f006f006f0001008d006f0001006f01b0006f006f002f00a1006f010c00e0006f0001000f00a5006f010c0001006f006f000100a3006f0065006f00890000006f006f2b2701002d2525201b221a001810201e231c141c091e0d07030500341b else 0xa70047009b000100010001009b00a700010001000f0001000100a900010047004700ab0017009b009b009b009b009b00030031009b009b0001009b009b0031009b009b009b121a0c170f071c1d040a00000d000d070701072413) else (if i < 311 then 0x7d00570057008f000100010057007d0001000100b1000100010023000100af0057001b00170057005700570057005700ad002700570057000100b300570027005700570057121a0c170f071c1d040a00000d000d070701072413 else 0x17c010c0108010c018c010c01f4010c000f010a00010001000f000100010003000100010001007301d8000100e800010012025000010010010c00740001000f010c0001010c0001000f0001000f00010001000100010013000100010041000100010001001700010001017e00010003018e000100010001000300030001000100010053000f0099010c006f000f000100010057000100010025000300010001000100010001001101a80001000f00010003002501da0001009b000101aa00ea00013c005400500050004c004c00365d49000e002a4a245f365e1e5d045c465b175a42592f5733442047153e0728001c0e012d406232))) else (if i < 316 then (if i < 314 then (if i < 313 then 0xb0000000300c2000f0001000900c0000500a5000100030001000100050003000300010001000300090003000900030099007d01a000b5000300250003000b00030007000300010001010c01fc010c000b006f00030003000301a200050001000300030003000300222331001d0309000e262300151f20001a00080003100000090102351c else 0x1000100010001025c00010001000100210090000f00010021000100010001000100010001000300010001020000190001000f0001000100010001000100b7005e0019025e002100010001005c002100000001000100010001001d1e2a0018182100091b25000011070003001d000c00022d18) else (if i < 315 then 0x840214017c017c0083017c01880001017c02100001017c02300001017c0001017c027e017c00a201ac009a02580020025c00010278000b00250041000100010083008300010001000b00830001000b01dc00570168000100010025000100830001000100010011000100010001000100010083000100010001000b0017000102760053009b0083028200a3000100010001000100130001017c0001000100ec0001000b00010001000100010001000100a300010001000100010083000b000b00010001017c000130004b002b615d00420000003e00000026005e000d14486007395f5e215d5c5b3a5a5958005756551a4b545336524a5113231d016534 else 0x1900000021c023400ba018c010c0194018c016c018c018c009b018c018c027c008801e00024028c0294018c028a021800f40260018c17140d13010b121006041002040e001b0f)) else (if i < 318 then (if i < 317 then 0x1b8008c00d8022401a8000f01a80170000f01a80220000f01ac01a8000f01a8007100d40280000f01a801a800aa0028026401b0000d02860238000f000f000f009d000f000d000f000d000d000f000d000f01e4001b00f8000d007900bb000f000f000d000f000d000f000f000f005b008d000d000f000d000f000d000f000d000f01a8007b000f000f029001a0006b0093001d000f000f000f028e000d000f01a8000f00c1000d00bf000d006b00b9000d00c3000d006b006b000f000f000f000d009f003f01a800bd300060002b610000425f5d003e000000260000000d53516007395f5e215d5c5b3a5a5957004856551a4c542336174a1413491d016634 else 0x1e400a401fc006801d8006b01d801e001d800de002101d801ee002101d8002101d8021e003a01d8020e002100300268002101d802160007006100210021002100b5006b002100210007006b0021006301d800c501d40021002100610007006b002100210021002100090021002100210021006b0021002100210007004500210106005f004700c70226006b00210021002100210059002101dc0021002100fc0021000700210021002100210021002100c90021002100210021006b000700070021002101d8002130005f002b605c00420000003e005e00260000000d14485f07395e5d215c4e5b3a5a5958005756551a4c545336524b5013231d016534) else (if i < 319 then 0x3601f4000001ea026c01fa01e801f401f8021001f4021801f4022000d0005701f4010c022201f40034021201f40100010201f4021a17180a08160604130012100e020d011b0f else 0x4a026c0244024e024c02500060026a025002500250026402680270026002500048006202500266024600010250010c0262025018091416160f071401100f0a0502001b0f)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0xbc00b0009000b000c000b000cc00b0005c00920088003a00a0009c002c005a000e00280082007600c8003c00680084000a00d0004a000800b00034007800a600b0001a00b0006400420026009e00520016002a008c005600040060009a00740030008e00180044007c00be006c000000c20094003e0038004600b40014002400b800580062000600b000a40072000c001e00ac0054004c001200860080002000400050006e007e00c4002e00660070001000aa00ca001c00a8009800c6006a00483c005400500050004c004c00365d49000e002a4a245f365e1e5d045c465b175a42592f5733442047153e0728001c0e012d406232 else 0) else 0) else 0) else 0) else 0) else 0)) else 0))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 14
  | 7 => 80
  | 8 => 167
  | 9 => 53
  | 10 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 20
  | 8 => 100
  | 9 => 267
  | 10 => 320
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+16*((h/a+d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with

  | 1 => ws.map (blockWord 72 [1, 0, 3, 2])

  | _ => ws

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 144) (goal 144) s ws) : NatRun (mask 144) (goal 144) s (rotateE g ws) := by
  unfold rotateE

  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 144 stateE nsE actionE sixE rotateE s
end Live514

namespace Live514

theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 1 0 = true := by decide +kernel

theorem z4 : span (Z 4) 1 0 = true := h4y0

theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel

theorem z5 : span (Z 5) 1 0 = true := h5y0

theorem h6y0 : span (Z 6) 10 0 = true := by decide +kernel

theorem h6y1 : span (Z 6) 4 10 = true := by decide +kernel

theorem z6 : span (Z 6) 14 0 = true := (@span_join (Z 6) 10 0 4 h6y0 h6y1)

theorem h7y0 : span (Z 7) 10 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 10 10 = true := by decide +kernel

theorem h7y2 : span (Z 7) 10 20 = true := by decide +kernel

theorem h7y3 : span (Z 7) 10 30 = true := by decide +kernel

theorem h7y4 : span (Z 7) 10 40 = true := by decide +kernel

theorem h7y5 : span (Z 7) 10 50 = true := by decide +kernel

theorem h7y6 : span (Z 7) 10 60 = true := by decide +kernel

theorem h7y7 : span (Z 7) 10 70 = true := by decide +kernel

theorem z7 : span (Z 7) 80 0 = true := (@span_join (Z 7) 40 0 40 (@span_join (Z 7) 20 0 20 (@span_join (Z 7) 10 0 10 h7y0 h7y1) (@span_join (Z 7) 10 20 10 h7y2 h7y3)) (@span_join (Z 7) 20 40 20 (@span_join (Z 7) 10 40 10 h7y4 h7y5) (@span_join (Z 7) 10 60 10 h7y6 h7y7)))

theorem h8y0 : span (Z 8) 10 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 10 10 = true := by decide +kernel

theorem h8y2 : span (Z 8) 10 20 = true := by decide +kernel

theorem h8y3 : span (Z 8) 10 30 = true := by decide +kernel

theorem h8y4 : span (Z 8) 10 40 = true := by decide +kernel

theorem h8y5 : span (Z 8) 10 50 = true := by decide +kernel

theorem h8y6 : span (Z 8) 10 60 = true := by decide +kernel

theorem h8y7 : span (Z 8) 10 70 = true := by decide +kernel

theorem h8y8 : span (Z 8) 10 80 = true := by decide +kernel

theorem h8y9 : span (Z 8) 10 90 = true := by decide +kernel

theorem h8y10 : span (Z 8) 10 100 = true := by decide +kernel

theorem h8y11 : span (Z 8) 10 110 = true := by decide +kernel

theorem h8y12 : span (Z 8) 10 120 = true := by decide +kernel

theorem h8y13 : span (Z 8) 10 130 = true := by decide +kernel

theorem h8y14 : span (Z 8) 10 140 = true := by decide +kernel

theorem h8y15 : span (Z 8) 10 150 = true := by decide +kernel

theorem h8y16 : span (Z 8) 7 160 = true := by decide +kernel

theorem z8 : span (Z 8) 167 0 = true := (@span_join (Z 8) 160 0 7 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 (@span_join (Z 8) 10 0 10 h8y0 h8y1) (@span_join (Z 8) 10 20 10 h8y2 h8y3)) (@span_join (Z 8) 20 40 20 (@span_join (Z 8) 10 40 10 h8y4 h8y5) (@span_join (Z 8) 10 60 10 h8y6 h8y7))) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 (@span_join (Z 8) 10 80 10 h8y8 h8y9) (@span_join (Z 8) 10 100 10 h8y10 h8y11)) (@span_join (Z 8) 20 120 20 (@span_join (Z 8) 10 120 10 h8y12 h8y13) (@span_join (Z 8) 10 140 10 h8y14 h8y15)))) h8y16)

theorem h9y0 : span (Z 9) 10 0 = true := by decide +kernel

theorem h9y1 : span (Z 9) 10 10 = true := by decide +kernel

theorem h9y2 : span (Z 9) 10 20 = true := by decide +kernel

theorem h9y3 : span (Z 9) 10 30 = true := by decide +kernel

theorem h9y4 : span (Z 9) 10 40 = true := by decide +kernel

theorem h9y5 : span (Z 9) 3 50 = true := by decide +kernel

theorem z9 : span (Z 9) 53 0 = true := (@span_join (Z 9) 40 0 13 (@span_join (Z 9) 20 0 20 (@span_join (Z 9) 10 0 10 h9y0 h9y1) (@span_join (Z 9) 10 20 10 h9y2 h9y3)) (@span_join (Z 9) 10 40 3 h9y4 h9y5))

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel

theorem z10 : span (Z 10) 1 0 = true := h10y0

theorem checkedE (s : Nat) (hs : s ≤ 10) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 144) (goal 144) s xs550) : False := by
  have h10 : NatRun (mask 144) (goal 144) 10 xs550 := extend_run h hs
  have p : xs550.Perm (stateE 10 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 10 (by decide) 0 (by decide) (Run.perm p h10)
end Live514

theorem PEqualNP.Outside.L_meta_550 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7)) s → 11 ≤ s := Live514.main550 Live514.noRunFull
