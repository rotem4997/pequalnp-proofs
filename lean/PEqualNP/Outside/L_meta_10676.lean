import Mathlib
import PEqualNP.Defs

-- The core bound is adapted from shuzo, pequalnp-proofs PR 13088.
-- Restriction and relabeling helpers are adapted from
-- Marco Visentini-Scarzanella, pequalnp-proofs PR 3773.
-- These sources are licensed under Apache-2.0.

namespace PEqualNP.Outside.L_meta_10676_aux.Live514
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
end PEqualNP.Outside.L_meta_10676_aux.Live514

namespace PEqualNP.Outside.L_meta_10676_aux.Relabel

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
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end PEqualNP.Outside.L_meta_10676_aux.Relabel

namespace PEqualNP.Outside.L_meta_10676_aux
open PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) ||
  (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) ||
  (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)

def core (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) ||
  (x 5 && x 6) || (x 6 && x 7)

/-- Send the leaf to the final input and its remaining vertices to the core labels. -/
def rename : Fin 9 → Fin 9 := ![7,5,2,3,8,4,1,6,0]
def permuted (x : Fin 9 → Bool) : Bool := target (x ∘ rename)

private theorem cofactor (x : Fin 8 → Bool) : permuted (Fin.snoc x false) = core x := by
  change (x 7 && x 4 || x 5 && x 1 || x 2 && x 1 || x 7 && x 6 ||
    x 5 && x 6 || x 3 && x 6 || false && x 6 || x 2 && x 0 ||
    x 3 && x 0 || x 4 && x 0 || x 1 && x 0) = _
  simp only [Bool.false_and, Bool.or_false, core]
  ac_rfl

theorem lower_of_core (known : ∀ s, HasCircuitSize 8 core s → 13 ≤ s)
    (t : ℕ) (h : HasCircuitSize 9 target t) : 14 ≤ t := by
  by_contra small
  obtain ⟨C, fan, size, eval⟩ := h
  have h13 : HasCircuitSize 9 target 13 := ⟨C, fan, by omega, eval⟩
  have hper : HasCircuitSize 9 permuted (12 + 1) := Relabel.relabel_size rename target 13 h13
  have dep : ∃ x : Fin 9 → Bool,
      permuted (Function.update x (Fin.last 8) (!x (Fin.last 8))) ≠ permuted x :=
    ⟨fun i => decide (i = 6), by decide⟩
  have nc : ∃ x y : Fin 8 → Bool,
      permuted (Fin.snoc x false) ≠ permuted (Fin.snoc y false) :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  have h12 := Live514.gate_elim 8 permuted false 12 dep nc hper
  rw [funext cofactor] at h12
  have contradiction := known 12 h12
  omega

end PEqualNP.Outside.L_meta_10676_aux

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_10676.Core8525
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 256
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 256 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 256 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 256 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 256) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

abbrev ExtraFactory := Nat → Nat → List Decor → Nat → Nat → Option BoundPool
def noFactory : ExtraFactory := fun _ _ _ _ _ => none
def FactorySound (m : Nat) (f : ExtraFactory) := ∀ ops d bank idx paid c,
  f ops d bank idx paid = some c → ValidPool (vars m) (chartGoal m) c
theorem noFactorySound (m : Nat) : FactorySound m noFactory := by
  intro ops d bank idx paid c h
  contradiction

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
  bonus : ExtraFactory
  safe : FactorySound mask bonus

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 256) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  match g.bonus ops d bank idx paid with
  | some c => some c
  | none => (g.cols.read idx).bind fun ci =>
      materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases eb : g.bonus ops depth bank i paid with
  | some c' =>
    rw [eb] at h
    cases h
    exact g.safe _ _ _ _ _ _ eb
  | none =>
      rw [eb] at h
      cases e : g.cols.read i with
      | none => simp [e] at h
      | some ci =>
        simp only [e,Option.bind_some] at h
        apply materialize_sound _ h
        exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def extra3853 (g : Forest) (k tag : Nat) : List (Nat × Nat) :=
  if g.mask=255 && k=10 && tag=5584706113853012463 then [(173,0)] else
  []
def ifUseful3853 {α} (flag : Bool) (xs : List α) : List α :=
  if flag then xs else []
theorem ifUseful3853_mem {α} {flag : Bool} {x : α} {xs : List α} :
    x ∈ ifUseful3853 flag xs → x ∈ xs := by
  cases flag <;> simp [ifUseful3853]

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    rcases List.mem_append.mp (ifUseful3853_mem hx) with h | h
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using h
      obtain ⟨pair,_,v⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) v
    · obtain ⟨pair,_,v⟩ := List.mem_filterMap.mp h
      exact linkedSet_sound g _ names (prior (by omega)) v


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^257*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^257 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 256) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (257*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^257)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 257*(i+1)-257=257*i := by omega
      have ge : ¬257*(i+1)<257 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 256 = (a==BitVec.allOnes 256) := by
  by_cases h : a=BitVec.allOnes 256
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^256-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^256 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (257*i) =
      (f xs[i]==BitVec.allOnes 256) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^257*u+x+(2^257*v+1)=2^257*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^257 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬257*(i+1)+256<257 := by omega
      have di : 257*(i+1)+256-257=257*i+256 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 256 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 256).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 257) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (257*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 257) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 256).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 256 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 256).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 256
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap

def edge8530 : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 6 && x 7)
def sample8530 (r : Row) (i : Fin 8) := bit r (inputs.getD i.val zero)
theorem raw8530 : List.ofFn (fun i : Fin 8 => inputs.getD i.val zero) = vars 255 := by decide +kernel
theorem samples8530 (r : Row) : List.ofFn (sample8530 r) = (vars 255).map (bit r) := by
  rw [←raw8530,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge8530_table : ∀ r : Row, bit r (graphGoal 255) = edge8530 (sample8530 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude8530 (absent : Impossible (graphGoal 255) 12 (vars 255).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8530 t → 13 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 255) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 255)).getD C.output zero = graphGoal 255 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 255)).getD C.output zero) = bit r (graphGoal 255)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples8530,edge8530_table]
    exact correct (sample8530 r)
  have hout := get_rep (execute C.gates (vars 255)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 255, Essential (graphGoal 255) (vars 255) a := by
    have valid : checkEssential (graphGoal 255) (vars 255) (graphPairs 255 1125122049) = true := by decide +kernel
    have ident : (graphPairs 255 1125122049).map Prod.fst = vars 255 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 255).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed7r3 (i : Nat) : Nat := 0x7
def layer7r3 : Packing := (1,0,0,63,0,0,1,packed7r3)
def samples7 : Array (Bits × Bits) := #[(0x3f,0x49),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0x92),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols7 : IndexTree ColumnInfo := (.leaf [])
def levels7 : Nat → Packing
  | 3 => layer7r3
  | _ => emptyPacking
def index7 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g7 : Forest := ⟨7,3,fun j => samples7[j]?.getD (0,0),cols7,#[[]],levels7,index7,noFactory,noFactorySound 7⟩
def packed43r3 (i : Nat) : Nat := 0xf
def layer43r3 : Packing := (1,0,0,63,0,0,1,packed43r3)
def samples43 : Array (Bits × Bits) := #[(0x707ff,0x34129),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9fc1f,0x81c86),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07e0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc96d4),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e318),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols43 : IndexTree ColumnInfo := (.leaf [])
def levels43 : Nat → Packing
  | 3 => layer43r3
  | _ => emptyPacking
def index43 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g43 : Forest := ⟨43,3,fun j => samples43[j]?.getD (0,0),cols43,#[[]],levels43,index43,noFactory,noFactorySound 43⟩
def packed15r4 (i : Nat) : Nat := 0x1f
def layer15r4 : Packing := (1,0,0,63,0,0,1,packed15r4)
def samples15 : Array (Bits × Bits) := #[(0x7e0ff,0x2111),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1f0f,0xa8a46),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ff0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff514a8),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd8cc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols15 : IndexTree ColumnInfo := (.leaf [(8,0,7,0,4)])
def levels15 : Nat → Packing
  | 4 => layer15r4
  | _ => emptyPacking
def index15 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,4,fun j => samples15[j]?.getD (0,0),cols15,#[[]],levels15,index15,noFactory,noFactorySound 15⟩
def packed199r5 (i : Nat) : Nat := 0x3f
def layer199r5 : Packing := (1,0,0,63,0,0,1,packed199r5)
def samples199 : Array (Bits × Bits) := #[(0x3003cf00ffff,0x322145242525),(0xc00cf3ff00ff,0xc4449249484a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff000f3cffff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffff088a28929290),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff03f000000,0x150f03f1c1c1c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffeaf0fc0e0e0e0),(0x0,0x0)]
def cols199 : IndexTree ColumnInfo := (.leaf [(0,64,7,128,5)])
def levels199 : Nat → Packing
  | 5 => layer199r5
  | _ => emptyPacking
def index199 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g199 : Forest := ⟨199,5,fun j => samples199[j]?.getD (0,0),cols199,#[[]],levels199,index199,noFactory,noFactorySound 199⟩
def packed109r4 (i : Nat) : Nat := 0x1f
def layer109r4 : Packing := (1,0,0,63,0,0,1,packed109r4)
def samples109 : Array (Bits × Bits) := #[(0x18040fffff,0x1a4524a555),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff60180e703f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff649a4a5a2a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff801ff39fc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff8088531288),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe003e000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa8e063e30c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000,0x57178c0c30),(0x0,0x0),(0x0,0x0)]
def cols109 : IndexTree ColumnInfo := (.leaf [])
def levels109 : Nat → Packing
  | 4 => layer109r4
  | _ => emptyPacking
def index109 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g109 : Forest := ⟨109,4,fun j => samples109[j]?.getD (0,0),cols109,#[[]],levels109,index109,noFactory,noFactorySound 109⟩
def packed59r4 (i : Nat) : Nat := 0x3f
def layer59r4 : Packing := (1,0,0,63,0,0,1,packed59r4)
def samples59 : Array (Bits × Bits) := #[(0x26707ffff,0x23404929),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffd99fd041f,0x4881d2486),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe1e0607e0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe1c96a6d4),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe007f800,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc097b294),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffb77e0c318),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols59 : IndexTree ColumnInfo := (.leaf [(8,0,51,0,4)])
def levels59 : Nat → Packing
  | 4 => layer59r4
  | _ => emptyPacking
def index59 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g59 : Forest := ⟨59,4,fun j => samples59[j]?.getD (0,0),cols59,#[[]],levels59,index59,noFactory,noFactorySound 59⟩
def packed107r5 (i : Nat) : Nat := 0x202608000902208000020080200803f3b6cc5729487ce19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer107r5 : Packing := (15,1,3,63,0,7,1,packed107r5)
def keys107k6 (i : Nat) : Nat := 0x38a577e9c3a162d05a000000bedd5cb62be410196
def packed107r6 (i : Nat) : Nat := 0x23444bf
def layer107r6 : Packing := (1,0,3,63,0,0,1,packed107r6)
def samples107 : Array (Bits × Bits) := #[(0xc01019c07fff,0xd21488d414a9),(0x100601e7fc07f,0x120e85221e246),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffe007fe7807f80,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe04a167094b14),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff8007ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe470185ce0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0x1b85e18303060),(0x0,0x0),(0x0,0x0)]
def cols107 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,106,0,4),(2,0,105,0,4)]) (.leaf [(8,0,99,0,4),(32,0,75,0,4),(64,0,43,0,4)]))
def levels107 : Nat → Packing
  | 5 => layer107r5
  | 6 => layer107r6
  | _ => emptyPacking
def index107 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 18 4 8 4 0 keys107k6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun j => samples107[j]?.getD (0,0),cols107,#[[]],levels107,index107,noFactory,noFactorySound 107⟩
def packed79r5 (i : Nat) : Nat := 0x204813044100401007cca8794280fd21fd20fd10fe00ee22f611fa00
def layer79r5 : Packing := (7,1,3,63,0,6,1,packed79r5)
def keys79k6 (i : Nat) : Nat := 0x700000009ec571fc000005a
def packed79r6 (i : Nat) : Nat := 0x6a47f
def layer79r6 : Packing := (1,0,3,63,0,0,1,packed79r6)
def samples79 : Array (Bits × Bits) := #[(0x200f3fe03fff,0x240502240891),(0xc033d01fc07f,0xc89254895226),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff003ce01fff80,0xffffffffffffffffffffffffffffffffffffffffffffffffffff1128a912a548),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffe00000,0x141c0f1c3060c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffebe3f0e1c3870),(0x0,0x0),(0x0,0x0)]
def cols79 : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,64,7,8,5),(64,0,15,0,5)]) (.leaf [(2,0,77,0,4),(4,0,75,0,4),(8,64,7,0,4)]))
def levels79 : Nat → Packing
  | 5 => layer79r5
  | 6 => layer79r6
  | _ => emptyPacking
def index79 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 16 0 7 3 0 keys79k6
  | _ => fun _ => none
def g79 : Forest := ⟨79,6,fun j => samples79[j]?.getD (0,0),cols79,#[[]],levels79,index79,noFactory,noFactorySound 79⟩
def packed47r5 (i : Nat) : Nat := 0x3f
def layer47r5 : Packing := (1,0,0,63,0,0,1,packed47r5)
def samples47 : Array (Bits × Bits) := #[(0x26e03f83ff,0x26804a129),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffd93fd07c1f,0x803521486),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffe1c0e07fe0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffe190a84a50),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe00ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc12fb5294),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff7fc0c6318),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols47 : IndexTree ColumnInfo := (.leaf [(8,0,39,0,5)])
def levels47 : Nat → Packing
  | 5 => layer47r5
  | _ => emptyPacking
def index47 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,5,fun j => samples47[j]?.getD (0,0),cols47,#[[]],levels47,index47,noFactory,noFactorySound 47⟩
def packed31r5 (i : Nat) : Nat := 0x3f
def layer31r5 : Packing := (1,0,0,63,0,0,1,packed31r5)
def samples31 : Array (Bits × Bits) := #[(0xe7e7e0ff,0x202111),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff5a1a1f0f,0x14a8a8a46),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff9c1c1ff0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe951514a8),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe01fe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe19fd8cc),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc198cc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols31 : IndexTree ColumnInfo := (.leaf [(8,0,23,0,5)])
def levels31 : Nat → Packing
  | 5 => layer31r5
  | _ => emptyPacking
def index31 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g31 : Forest := ⟨31,5,fun j => samples31[j]?.getD (0,0),cols31,#[[]],levels31,index31,noFactory,noFactorySound 31⟩
def packed222r5 (i : Nat) : Nat := 0x7f
def layer222r5 : Packing := (1,0,0,63,0,0,1,packed222r5)
def samples222 : Array (Bits × Bits) := #[(0x0,0x0),(0x48c00c300f33300ffff,0x48d24c34a5313525555),(0xfffffffffffffffffffffffffffffffffffffffffffff930030c00fc3c00ffff,0xfffffffffffffffffffffffffffffffffffffffffffff9324b0c94ac2ca4aaaa),(0x1c003f000cfcfff3300,0x1c30ff0c6c545c733cc),(0xfffffffffffffffffffffffffffffffffffffffffffffe0003ffff0ff0003c00,0xfffffffffffffffffffffffffffffffffffffffffffffe006d551f0ff0363c3c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffc00000fffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffe147000180aba38c030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0x1eb82aae0f000c000c0),(0x0,0x0)]
def cols222 : IndexTree ColumnInfo := (.leaf [(0,2,216,4,5)])
def levels222 : Nat → Packing
  | 5 => layer222r5
  | _ => emptyPacking
def index222 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g222 : Forest := ⟨222,5,fun j => samples222[j]?.getD (0,0),cols222,#[[]],levels222,index222,noFactory,noFactorySound 222⟩
def packed245r6 (i : Nat) : Nat := 0xe413f
def layer245r6 : Packing := (1,0,2,63,0,0,1,packed245r6)
def samples245 : Array (Bits × Bits) := #[(0x20c0132030301ffffff,0x20d21129103505294a9),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffcb0063c03cc0139c07f,0xfffffffffffffffffffffffffffffffffffffffffffffcb24e2d2acca5296a56),(0x0,0x0),(0xc007cffcf001ce7f80,0xc04a442cf0258c4b14),(0xffffffffffffffffffffffffffffffffffffffffffffff0007f000fffe0f8000,0xffffffffffffffffffffffffffffffffffffffffffffff030ff18855c60fb264),(0xfffffffffffffffffffffffffffffffffffffffffffffffff80000fffff00000,0xd4700030aa39f00c18),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xffffffffffffffffffffffffffffffffffffffffffffff2b85bbc300c0003060),(0x0,0x0)]
def cols245 : IndexTree ColumnInfo := (.leaf [(0,4,240,1,5),(0,32,149,64,5),(4,0,241,0,5),(32,0,213,0,5)])
def levels245 : Nat → Packing
  | 6 => layer245r6
  | _ => emptyPacking
def index245 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g245 : Forest := ⟨245,6,fun j => samples245[j]?.getD (0,0),cols245,#[[]],levels245,index245,noFactory,noFactorySound 245⟩
def packed187r6 (i : Nat) : Nat := 0x90ff
def layer187r6 : Packing := (1,0,2,63,0,0,1,packed187r6)
def samples187 : Array (Bits × Bits) := #[(0x10e0101f26701ffffff,0x10601405023401090a1),(0x33e6013d99ff40407f,0x10e6252488274a4a16),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffe3c7801ce1e01807f80,0xfffffffffffffffffffffffffffffffffffffffffffffe3878ad8e1cb5ae6f5c),(0xffffffffffffffffffffffffffffffffffffffffffffffc07ffe0fe001ff8000,0x2402a0e0fc015c7060c),(0xffffffffffffffffffffffffffffffffffffffffffffffff80000ffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffffef00c80b77d8343468),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffdbfd5f1f000e0383870),(0x0,0x0)]
def cols187 : IndexTree ColumnInfo := (.leaf [(8,0,179,0,5),(2,32,153,0,4),(16,128,43,0,4)])
def levels187 : Nat → Packing
  | 6 => layer187r6
  | _ => emptyPacking
def index187 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun j => samples187[j]?.getD (0,0),cols187,#[[]],levels187,index187,noFactory,noFactorySound 187⟩
def packed243r6 (i : Nat) : Nat := 0x404a08000c100220400820040080100200400c5c03d3a34af29a6a11b96108b05807f54ffa85fd32fea8ff507fa43fd50fea07f4c2fcabbe44ef19fb88bec23fa00
def layer243r6 : Packing := (15,1,4,63,0,8,1,packed243r6)
def keys243k7 (i : Nat) : Nat := 0x6d001a9c630019318e0085700064f2006600e77b880010038
def packed243r7 (i : Nat) : Nat := 0xb87a969bf
def layer243r7 : Packing := (1,0,4,63,0,0,1,packed243r7)
def samples243 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffe0c048406180f9c07fff,0xffffffffffffffffffffffffffffffffffffffffffffe0e2486221c828e424c9),(0xb000f8072009e7fc07f,0xb14039452309218d832),(0x0,0x0),(0x0,0x0),(0xc0071ff9c00e7807f80,0xc0490859c12c70a4b14),(0xfffffffffffffffffffffffffffffffffffffffffffff0007e001fff07ff8000,0xfffffffffffffffffffffffffffffffffffffffffffff020fc2104c305e32244),(0xffffffffffffffffffffffffffffffffffffffffffffffff80001ffff8000000,0xd4700061b1cf80c0c18),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000,0xfffffffffffffffffffffffffffffffffffffffffffff2b86f78606000303060),(0x0,0x0)]
def cols243 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(1,0,242,0,5),(2,0,241,0,5),(16,0,227,0,5)]) (.leaf [(32,0,211,0,5),(64,0,179,0,5),(128,0,115,0,5)])) (.fork 3 (.leaf [(3,0,240,0,4),(17,0,226,0,4),(34,0,209,0,4)]) (.leaf [(96,0,147,0,4),(144,0,99,0,4),(192,0,51,0,4)])))
def levels243 : Nat → Packing
  | 6 => layer243r6
  | 7 => layer243r7
  | _ => emptyPacking
def index243 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 22 4 8 4 0 keys243k7
  | _ => fun _ => none
def g243 : Forest := ⟨243,7,fun j => samples243[j]?.getD (0,0),cols243,#[[]],levels243,index243,noFactory,noFactorySound 243⟩
def packed207r7 (i : Nat) : Nat := 0x7f
def layer207r7 : Packing := (1,0,0,63,0,0,1,packed207r7)
def samples207 : Array (Bits × Bits) := #[(0x1801e78400f3ff00ffff,0x19102284905025242525),(0x460069998033d00ff00ff,0x46222891921254849484a),(0xfffffffffffffffffffffffffffffffffffffffffff980071e6003ce00ffff00,0xfffffffffffffffffffffffffffffffffffffffffff984451462428a90929290),(0xfffffffffffffffffffffffffffffffffffffffffffe0007e07ffc0fff000000,0xfffffffffffffffffffffffffffffffffffffffffffe0607c02b040fc2c0c0c0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffff8007ffff000000000,0xa87800547bf01c1c1c1c),(0xffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000,0xffffffffffffffffffffffffffffffffffffffffffff5787ff838000e0e0e0e0),(0x0,0x0)]
def cols207 : IndexTree ColumnInfo := (.leaf [(128,0,79,0,7)])
def levels207 : Nat → Packing
  | 7 => layer207r7
  | _ => emptyPacking
def index207 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g207 : Forest := ⟨207,7,fun j => samples207[j]?.getD (0,0),cols207,#[[]],levels207,index207,noFactory,noFactorySound 207⟩
def packed119r7 (i : Nat) : Nat := 0x7f
def layer119r7 : Packing := (1,0,0,63,0,0,1,packed119r7)
def samples119 : Array (Bits × Bits) := #[(0x30079e9b803fe03fff,0x32408a099402a50a95),(0x8401a6764ffd01fc07f,0x8440a24202154085022),(0xfffffffffffffffffffffffffffffffffffffffffffff1801c798700e01fff80,0xfffffffffffffffffffffffffffffffffffffffffffff18894518648a912a548),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffe001f81f800ffe00000,0xfffffffffffffffffffffffffffffffffffffffffffffe0c9f01f068fd5a3468),(0xffffffffffffffffffffffffffffffffffffffffffffffffe001ffff00000000,0x1290e001df8e0183060c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000,0xffffffffffffffffffffffffffffffffffffffffffffed6f1ffe00700e1c3870),(0x0,0x0),(0x0,0x0)]
def cols119 : IndexTree ColumnInfo := (.leaf [(16,0,103,0,7)])
def levels119 : Nat → Packing
  | 7 => layer119r7
  | _ => emptyPacking
def index119 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,7,fun j => samples119[j]?.getD (0,0),cols119,#[[]],levels119,index119,noFactory,noFactorySound 119⟩
def packed95r7 (i : Nat) : Nat := 0x7f
def layer95r7 : Packing := (1,0,0,63,0,0,1,packed95r7)
def samples95 : Array (Bits × Bits) := #[(0x3c200f39ff3fe03fff,0x42405001102240891),(0xcd0c033d680d01fc07f,0xc50c89252a454895226),(0xfffffffffffffffffffffffffffffffffffffffffffff0e3003ce700e01fff80,0xfffffffffffffffffffffffffffffffffffffffffffff0a31128a548a912a548),(0xffffffffffffffffffffffffffffffffffffffffffffff03ffc0f800ffe00000,0x150141c0f80cf1c3060c),(0xfffffffffffffffffffffffffffffffffffffffffffffffc0000ffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffff81980ffee0d9b366c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffeafebe3f00700e1c3870),(0x0,0x0),(0x0,0x0)]
def cols95 : IndexTree ColumnInfo := (.leaf [(16,0,79,0,7)])
def levels95 : Nat → Packing
  | 7 => layer95r7
  | _ => emptyPacking
def index95 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g95 : Forest := ⟨95,7,fun j => samples95[j]?.getD (0,0),cols95,#[[]],levels95,index95,noFactory,noFactorySound 95⟩
def packed63r6 (i : Nat) : Nat := 0x7f
def layer63r6 : Packing := (1,0,0,63,0,0,1,packed63r6)
def samples63 : Array (Bits × Bits) := #[(0x4a69b80e7f3f83ff,0x209a000904a129),(0xffffffffffffffffffffffffffffffffffffffffffffffffb5964ff5a0d07c1f,0x108200d4a4521486),(0xffffffffffffffffffffffffffffffffffffffffffffffffc6187039c0e07fe0,0xffffffffffffffffffffffffffffffffffffffffffffffffc618642950a84a50),(0xfffffffffffffffffffffffffffffffffffffffffffffffff81f803e00ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffff81f04be14fb5294),(0xffffffffffffffffffffffffffffffffffffffffffffffffffe0003fff000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffc004bff60a5294),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffef7dff00180c6318),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols63 : IndexTree ColumnInfo := (.leaf [(8,0,55,0,6)])
def levels63 : Nat → Packing
  | 6 => layer63r6
  | _ => emptyPacking
def index63 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,6,fun j => samples63[j]?.getD (0,0),cols63,#[[]],levels63,index63,noFactory,noFactorySound 63⟩
def packed123r7 (i : Nat) : Nat := 0x7f
def layer123r7 : Packing := (1,0,0,63,0,0,1,packed123r7)
def samples123 : Array (Bits × Bits) := #[(0xc00720326701ffffff,0xd201291023501494a9),(0x110064c03d99ff40407f,0x1120e4d0a48887626246),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffe20078ffce1e01807f80,0xffffffffffffffffffffffffffffffffffffffffffffe204a842ce1c258a4b14),(0xfffffffffffffffffffffffffffffffffffffffffffffc007f000fe001ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffc24fe128fc0a5eb2a54),(0xffffffffffffffffffffffffffffffffffffffffffffffff80000ffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffe64700030b77380c0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0x19b857bc3000c0303060),(0x0,0x0),(0x0,0x0)]
def cols123 : IndexTree ColumnInfo := (.leaf [(16,0,107,0,7)])
def levels123 : Nat → Packing
  | 7 => layer123r7
  | _ => emptyPacking
def index123 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g123 : Forest := ⟨123,7,fun j => samples123[j]?.getD (0,0),cols123,#[[]],levels123,index123,noFactory,noFactorySound 123⟩
def packed111r5 (i : Nat) : Nat := 0x4ed7299910
def layer111r5 : Packing := (1,3,3,63,0,0,1,packed111r5)
def keys111k6 (i : Nat) : Nat := 0xa0
def packed111r6 (i : Nat) : Nat := 0x80000000002479848c180bf99910dd95611af59010b758c10bb58810de95600fc84600
def layer111r6 : Packing := (7,2,3,63,0,6,1,packed111r6)
def keys111k7 (i : Nat) : Nat := 0xf8ad4003203705d401
def packed111r7 (i : Nat) : Nat := 0xa8420c321d4c4b5306b2b210828d5311d4c475311c4372a1b1209007f847fa21fc10ff005f957ec23fa00
def layer111r7 : Packing := (7,1,3,63,0,8,1,packed111r7)
def keys111k8 (i : Nat) : Nat := 0x64000007000000a20002b8a0374c
def packed111r8 (i : Nat) : Nat := 0x468897f
def layer111r8 : Packing := (1,0,3,63,0,0,1,packed111r8)
def samples111 : Array (Bits × Bits) := #[(0x6001003d37003ff00ffff,0x648124141328029282929),(0x800600cec9ffd00ff00ff,0x882642484043544454446),(0xffffffffffffffffffffffffffffffffffffffffffb001800f30e00e00ffff00,0xffffffffffffffffffffffffffffffffffffffffffb111888a30c90a90929290),(0xffffffffffffffffffffffffffffffffffffffffffc001fff03f000fff000000,0xffffffffffffffffffffffffffffffffffffffffffc012a0b03e012f16141414),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffe00003ffff000000000,0xffffffffffffffffffffffffffffffffffffffffffd21c00c03bf1c018181818),(0xffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000,0x2de15f0fc00e00e0e0e0e0),(0x0,0x0),(0x0,0x0)]
def cols111 : IndexTree ColumnInfo := (.fork 3 (.leaf [(4,0,107,0,7),(8,0,103,0,7),(32,0,79,0,7)]) (.leaf [(0,64,7,40,6),(64,0,47,0,6),(1,0,110,0,5),(2,0,109,0,5)]))
def levels111 : Nat → Packing
  | 5 => layer111r5
  | 6 => layer111r6
  | 7 => layer111r7
  | 8 => layer111r8
  | _ => emptyPacking
def index111 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 keys111k6
  | 7 => lookupWord 2 11 1 7 3 0 keys111k7
  | 8 => lookupWord 2 16 0 7 3 0 keys111k8
  | _ => fun _ => none
def g111 : Forest := ⟨111,8,fun j => samples111[j]?.getD (0,0),cols111,#[[]],levels111,index111,noFactory,noFactorySound 111⟩
def packed254r7 (i : Nat) : Nat := 0xff
def layer254r7 : Packing := (1,0,0,63,0,0,1,packed254r7)
def samples254 : Array (Bits × Bits) := #[(0x0,0x0),(0x48c0003f30c03c20400ccc03ffffffff,0x48d2400930d29420544c4d492494d555),(0xfffffffffffffffffffffffffffffffa93003324c3003ec58030f00392403fff,0xfffffffffffffffffffffffffffffffa9324b324c3252ac5a930b292926a2aaa),(0xfffffffffffffffffffffffffffffffc1c003c38fc003306003f3ffce3803300,0xfffffffffffffffffffffffffffffffc1c30fc38fc31b3063155171ce3b2b3cc),(0xe0003fc0ffffc3f8003fc000fc003c00,0xe006d5405547c3f80d7fc0d8fc0ebc3c),(0xffffffffffffffffffffffffffffffff00003fff000003ffffc00000ffffc000,0xffffffffffffffffffffffffffffffff0020bff60021034ea1800210db630088),(0xffffffffffffffffffffffffffffffffffffc000000003ffffffffff00000000,0xe1470000000600b14e2ae8e3000c0030),(0xfffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0xffffffffffffffffffffffffffffffff1eb82abfaab83c0030000300003000c0),(0x0,0x0)]
def cols254 : IndexTree ColumnInfo := (.leaf [(4,0,250,0,7)])
def levels254 : Nat → Packing
  | 7 => layer254r7
  | _ => emptyPacking
def index254 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g254 : Forest := ⟨254,7,fun j => samples254[j]?.getD (0,0),cols254,#[[]],levels254,index254,noFactory,noFactorySound 254⟩
def packed191r8 (i : Nat) : Nat := 0xff
def layer191r8 : Packing := (1,0,0,63,0,0,1,packed191r8)
def samples191 : Array (Bits × Bits) := #[(0x1137000803cf4a69b8039ff3fe03fff,0x1013000a004500209a00021042810a1),(0x2c9cc300d33b5964ffd680d01fc07f,0x404c3125121082013529452854a16),(0xffffffffffffffffffffffffffffffffe630e30c00e3cc618700e700e01fff80,0xffffffffffffffffffffffffffffffffe630c30c44a28c618648a548a912a548),(0xfffffffffffffffffffffffffffffffff83f03f000fc0f81f800f800ffe00000,0xfffffffffffffffffffffffffffffffff83e03f056f80f81f05af85cfbd72e5c),(0xffffffffffffffffffffffffffffffffffc003ffff000ffe0000ffff00000000,0x2a40015507000ffc000aff8e0183060c),(0xfffffffffffffffffffffffffffffffffffffc0000000fffffff000000000000,0xfffffffffffffffffffffffffffffffffffbf80064000ef7dfec00680d1a3468),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffff0000000000000000000,0xffffffffffffffffffffffffffffffffd5bffeaaf8fff000007000700e1c3870),(0x0,0x0)]
def cols191 : IndexTree ColumnInfo := (.leaf [(8,0,183,0,8)])
def levels191 : Nat → Packing
  | 8 => layer191r8
  | _ => emptyPacking
def index191 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g191 : Forest := ⟨191,8,fun j => samples191[j]?.getD (0,0),cols191,#[[]],levels191,index191,noFactory,noFactorySound 191⟩
def packed253r8 (i : Nat) : Nat := 0xff
def layer253r8 : Packing := (1,0,0,63,0,0,1,packed253r8)
def samples253 : Array (Bits × Bits) := #[(0x4060009f0203e006003901fffffffff,0x406900850290a006a0095084a1494a9),(0x0,0x0),(0xffffffffffffffffffffffffffffffffe95803313cc027658032601d2740407f,0xffffffffffffffffffffffffffffffffe95927312cd2a56594b26a55256a6a56),(0xfffffffffffffffffffffffffffffffff06003c1cf003986003c7fe639807f80,0xfffffffffffffffffffffffffffffffff06107c18f10b1861094286631a26344),(0x18003fe0fffc1f8003f8007c1ff8000,0x18025520542c1f804bf024781cb0a14),(0xfffffffffffffffffffffffffffffffffe0003fff00001ffffc00007fe000000,0xfffffffffffffffffffffffffffffffffe0187fff01881aeb8c00c47fe323264),(0xfffffffffffffffffffffffffffffffffffffc00000001fffffffff800000000,0x18a380000030051472bd398000c0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffe000000000000000000,0xfffffffffffffffffffffffffffffffffe75c2adfabc3e0018000c0000303060),(0x0,0x0)]
def cols253 : IndexTree ColumnInfo := (.leaf [(4,0,249,0,8)])
def levels253 : Nat → Packing
  | 8 => layer253r8
  | _ => emptyPacking
def index253 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g253 : Forest := ⟨253,8,fun j => samples253[j]?.getD (0,0),cols253,#[[]],levels253,index253,noFactory,noFactorySound 253⟩
def packed247r6 (i : Nat) : Nat := 0x258200000000000185523cc2460c04fc26131501108f8cbd10880215e2995c910042bc130b922008678a217244010e71332e488021d62555c910043b4488b9220087708cd7244010
def layer247r6 : Packing := (9,4,6,63,0,6,1,packed247r6)
def keys247k7 (i : Nat) : Nat := 0x1200f586816400c7b850d3
def packed247r7 (i : Nat) : Nat := 0x160803c6000010582c1058408005041a10217842c085c100000000160800000000000000000000b040e4b2006c005800b0016002c005800b001a0024084810902120424086800d001a0034006082082080000000000000000000000082eeba2c7b06b2a8e94a167f9e66a96e4c8f62e8a22287216842017edf57bde978ddd75dd172dc56fdb96cda460d745955651d384a51a42cfc3b4de33cc02c4a224c841f8781c86c1986016854138481083c0d8300a824078180480c018009fc87845609fc87845509fc874c540ded829dd10bed829dd10dee771c910ded761c910ded751c910ded741c910ded731c910fe4724c510fe87250110ff13150110ff12150110ff13148110dbd655d010ddd655cc10ded655c8109fc87586009fc87546009fc8784600e6e6695622eae6691222f4e558ce22f8e448ce22e766695611eb66691211f56558ce11f96448ce11ee66688a11f665588a11fa64488a11fc63388a119ed829dd109ec8788910fe121481109be885d010cbe665d010d3e555d0109de885cc10cde665cc10d5e555cc10d9e445cc10d9d748cc109ee885c810cee665c810d6e555c810dae445c810dce335c810ced7688810d6d7588810dad7488810dcd7388810bf28844010ef26644010f725544010fb24444010fd23344010fe08244010df17244010fe22244010e7a6695600eba6691200f5a558ce00f9a448ce00eea6688a00f6a5588a00faa4488a00fca3388a00ef26684600f725584600fb24484600fd23384600fe22284600de17244010
def layer247r7 : Packing := (75,3,6,63,0,10,1,packed247r7)
def keys247k8 (i : Nat) : Nat := 0x40b0648e7e07950011159113b129d29407b051b882918acf3a07c1f32970540f5291a536424971b70010cc006b450d01ecf211724000000c2762cf11081928952353da428c2588240f38fa719352fa7a22916f8156ac40040b682fe4de4fbfa50003865c37554af07541d300e2dd00040a000400550006a0903004c170714000a213470444
def packed247r8 (i : Nat) : Nat := (if i < 1 then 0x2d21674b2c58f2c41604af456f2b41584ab454f2a214f4a6c51b28a14049e44eb26c13449844bb24e12548fc477230116489444321410848343f71f80f647a43bf1d60e946e43671ae0d1467432318c0c045d42e31680b0456c2a314a0a244fc26712c090446421710808243fc1f30f607943bc1d70e807243841b70d806a434419b0ca063430c17f0bc05c42cc15f0ac054429413f09a04a423c11308604141fc0f707803a41c40db06a02d413407702a00d405c027010006402400b0003fe99283ff50931ffa8298ffd65487feb2243ff54d21ffa8690ffd61487fea8a43ff50521ffa6290ffd65847fea9c23ff48560ffc22b07fd21543ff08aa1ff4c940ffa62a07fd21503fea1261ff50530ffa42987fe114c3fea0261ff59520ffac8907fd53483fea1a41ff58520ffaa2907fd41483fe98a41ff58120ffaa0907fd40483fe98241ff9dd10ffaec887fd75443feb2a21ff5d110ffac8887fd73443fea9a21ff50d10ffae4887fd62443fea9221ff50910ffa64887fd61443fea8a21ff50510ffa62887fd21443feb0221ff54110ffa80887fd30443fe90221ff59410ffacb007fd64803feb0c01ff54600ffa83007fe11802ff3ba85bf99942f7ac8a17de3350aff3ba65df95532bfae8997be444cbeea9a65fb50932fdacb117ed6488bf6a9c45fb50e22fdc44b0fee22546ff3ba83bf99941fbc66a0fbd42507f7112837f9dd31efcaa98dfd744c7df22263f754d31fba8698fdd324c7f7112637f9dd21dfccc90f7e55486feba243ef91121bfae690fde33487f6a1243fd59611feac908ff553847faa1c23fd58a11feaa508ff542847fa99423fd1c211dfccd08f7e55847df22423f78ce11fdc4508ff561847faa8c23fd50611fea6308ff521847f7112c1fd84560fdc44a87f611542ff3ba81bf99940f7ac8a07bd43503ef19a81ef50940fdc44a07bd41503fb08a817f9dd30efcaa985fd744c3df22261f74c930fdc44987dd314c3fb08a617f9dd20dfccc9077e55482feba241ef91120bfae6907de33483f699241fb48520fec22905fe774437f33221df95510bfae8887be44442feb9a21f78cd10bfae4887ec72443f711221fd4c510fea42887f611443fca0221fe48110dfccc0877e55042feba021ef91010bfae6087de33042feb9021fb88810ff2cb007f964803fca9c01fe50e00ff2c5007f952803fca1401fe4ca00ff0e3007f961803fca8c01fe50600ff263007f921803fd08c01bf99a00efcab007be44803ef19c01fb88a00fec23007f960803fca8401fe50200ff261007f920803fc884019f99a55d7ccd2275e558cfcf22467bb99a22edcab117ae4488be719c45bd99a11eecab08fb644847eb19c23f988a119faec0857d75042deba021775cc10bdae4087f1100437d33401de95600f7489007da33803f511401fc84600 else 0x1d18087c206038104541421b430219106d10303120b0a001428008620028004541420544210c6c1e041840604818c6c142050388741c58317846c5a21c00160c703021b0c08207028104541421a430d0c6910045c4120b08681821a08420510683421a1789060028006001168008201e2414089090221505800d021194380230615021174480210514644a005c4400488182200508587c643181d170e011024280430c66010830780410c610024180440e010c20880420c5e010431640081c18163150508190c8c3060488140d0a3071e081e1180c060580161a001464a80091916001180d060580161a0010d0807038a0c1a0014549800a171462292458443050e0024480090418406090020704038201001e1e0818204203424610058204342c1814045c64004341c100c003064005150c285c4020a170c6100285c4400434301816005868006001070403010d160010c070403024180162200108194216110c14380091200241040010005001400420140050014005001400600142800a001800400181400a0500283060c10c0b060502191900146440919100424643400459002464440042024643400420100c0a04007078104200c022830581041c30285900581041c285c38104343018160060680060010d0804034201801822001080403020c160010717411810601c205a4800434302c201c1814100c080502c80408a01022040301000d1601022040302000c1601022040302010b17130f0b0502540841e19045e40716408e0100208854219902061023401489004e20401000d491445004230302000c4a143d003a304030201400b9902143050e0024480090410004001400500107051014280090818005001800500140050014005001400506002800600180040018040092a2624a898a292628a49892a149852614a852a149852614a85021c01311c908070f9f005040201c3a617c0c3160dca0708a0670310583324201e819170bcac908079c1e14a8526149852a1408601022b5f5a82d2567cb2b58e2c45614aff57a2bb55c4ad35602ac554ca9b5462a154f4a6b5302955494a4351c28a542ca0b50027b53c49d74e6271537c9b34d426753249834be25952bc94749a24b524491748423e51dc8df468230516c8a744e22350fc873432216509483f418209503c8033fe1f94fbc7c33de1e84f347833b81da4ebc7533a61d14e7471b38a1c34dec6ef36a1b34d646ab34c1a24cec66f32a1934c8c62f3141814bfc5eb2f21764b9c5c72e016e4b645ab)
def layer247r8 : Packing := (230,2,6,63,0,13,1,packed247r8)
def keys247k9 (i : Nat) : Nat := 0xc7bfa6587247363461e1e7ad497c0466dc3b6d651b520f8800000000022d000a496d8bb44119a4966105482eaa459ec00005e300090bbc20000009683400006a34be017983d76dcf70f0005cba23055000000a5fa6f000d9c189c748280001b0916c10fc7460b8a49620888600047339936cf24e35f9e0dc000e9f1d5f51052e3f2c3d45d7fe9282b50a0000002c41d7330509f72b4200016958f465baf9e5167000227cb8a5edbc8ce464adb5e08cd64cf139c1553d316b9f38b43bdf92a0812b2e191de857403191a7e000e79414ae20a1d6bd46cc66aed26000b44f4d93eda8c8033dd3656279d87a62cd37b5a00000000000086abbd46e000233b8d43cf0e59bfb359a639d7c7a5c5418c918d5b20281c07d58ed842221415d384f3d1fa01158567711752327c944a6c50d95858ba1ca69433455c0212bf000e1f998c93dc81ab0a791a8252a9d0d0003b600080109540783a9d0bbba2f5900d28500000000000006b720c000000cb57ac54832eae13065b1c295da71235dd7744b3dd6a2c58a8b6cc9d4fe4e1d54e4784701210000060980914006802404198003001124005800c00e000e088840004080020c200040404304281831e05010021000c006018a009c00010201003c182000c11107
def packed247r9 (i : Nat) : Nat := 0x203c014184cc2039980283099c4072f00485153992f0050925318101cb0022289d0604072c00709294080e6088094584d0203981c0249615407110088a273071100709293071b0089e94267101c7402f2454e203860a025492d4078064c4a92227101e011144e6101e00e12526101c8c033284ce206401c7248a9c4070c1404a926280c140080f02549a0c860a5cb4a92203d2220172d2a4879ca40922a42702509908c0942641d0248a92549011808022549940400f2a4cb652aed269ed2e23d43c7fcf39cf367660bc95da8b4b6890f69af2e24b07a8d316223c36852052003fd65ff593fd53ff50ffd62ff54bfd42ff4cbfd61ff547fd41ff4c7fd21ff847fd60ff543fd40ff4c3fd20ff443fc10ff802fe66df957be44f78cfee22fd847fa00
def layer247r9 : Packing := (29,1,6,63,0,11,1,packed247r9)
def keys247k10 (i : Nat) : Nat := 0x132005200278000000000bbc36bc2eb80000000000035b8761006306200003ba8e0b003499000001500000650024afa00003c0003695420f3415a43241
def packed247r10 (i : Nat) : Nat := 0x5131ff
def layer247r10 : Packing := (1,0,6,63,0,0,1,packed247r10)
def samples247 : Array (Bits × Bits) := #[(0x100c004702003c03001e7a6e003ff803ffff,0x100d0843028414034402282688044a211289),(0x2300009cc00cc8400699d93ffd007fc01ff,0x23090004c4848842828908051528144a052),(0xffffffffffffffffffffffffffffe4c0018e3000f3180071e61c00e007fffe00,0xffffffffffffffffffffffffffffe4c2238c3112a3189151461924a9249a4d24),(0x0,0x0),(0x70001f03fff03e0007e07e000fff8000000,0x7003290141b03e0197c07c034f1b0d06834),(0xfffffffffffffffffffffffffffff80001ffc00003ffff8007ffff0000000000,0xfffffffffffffffffffffffffffff80303ff81820129c180077f860c26130984),(0xfffffffffffffffffffffffffffffffffe00000003fffffff800000000000000,0x7543c00001c02d61e7ff8003801c0e07038),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffff8abc16febe0fc00e0000001c00e070381c0),(0x0,0x0)]
def cols247 : IndexTree ColumnInfo := (.fork 18 (.fork 9 (.fork 4 (.leaf [(4,0,243,0,8),(16,0,231,0,8),(32,0,215,0,8),(64,0,183,0,8)]) (.fork 2 (.leaf [(128,0,119,0,8),(0,64,23,160,7)]) (.leaf [(0,128,39,80,7),(1,0,246,0,7),(2,0,245,0,7)]))) (.fork 4 (.leaf [(96,0,151,0,7),(144,0,103,0,7),(0,4,240,3,6),(0,16,102,129,6)]) (.fork 2 (.leaf [(0,32,149,66,6),(16,64,7,160,6)]) (.leaf [(16,128,39,64,6),(32,64,23,128,6),(32,128,7,80,6)])))) (.fork 9 (.fork 4 (.leaf [(48,0,199,0,6),(64,128,39,16,6),(128,64,23,32,6),(192,0,55,0,6)]) (.fork 2 (.leaf [(1,4,240,2,5),(1,16,102,128,5)]) (.leaf [(2,4,240,1,5),(2,32,149,64,5),(5,0,242,0,5)]))) (.fork 4 (.leaf [(6,0,241,0,5),(17,0,230,0,5),(20,0,227,0,5),(34,0,213,0,5)]) (.fork 2 (.leaf [(36,0,211,0,5),(68,0,179,0,5)]) (.leaf [(80,0,39,0,5),(132,0,115,0,5),(160,0,23,0,5)])))))
def levels247 : Nat → Packing
  | 6 => layer247r6
  | 7 => layer247r7
  | 8 => layer247r8
  | 9 => layer247r9
  | 10 => layer247r10
  | _ => emptyPacking
def index247 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 11 0 8 4 0 keys247k7
  | 8 => lookupWord 25 87 6 11 7 0 keys247k8
  | 9 => lookupWord 76 265 7 12 8 0 keys247k9
  | 10 => lookupWord 9 53 2 9 5 0 keys247k10
  | _ => fun _ => none
def g247 : Forest := ⟨247,10,fun j => samples247[j]?.getD (0,0),cols247,#[[]],levels247,index247,noFactory,noFactorySound 247⟩
def packed223r6 (i : Nat) : Nat := 0x7282e506c80b9017282e506c80b9010000008172635445362718120c0600cceaa306382859b5546047050b33b08b18e09967558d811c132cceaa306382839ad546087050733b08b18e098e7358d821c1319f0c8900a12413e191201324827c32440282884f8648804c510
def layer223r6 : Packing := (12,4,5,63,0,8,1,packed223r6)
def keys223k7 (i : Nat) : Nat := 0xd9eb7326d8a100009297aa0070001425701
def packed223r7 (i : Nat) : Nat := 0x8765038c00219900a38765038c00219900a30000000006503c00d900b0030006503c10d900b043a50408169020dc3e08c370f0630dc2e08c370b0630000000dc3c08c370f0230dc2c08c370b023000000020800820000000000000000000b4accb1aa8a2a849fa6096a5493a4890a3c87a007e9f4759b86898c5b9504c91443908408fc378c0288841f8781c86c1986016854138481083c0d8300a824078180480c01800dbd541c1429fd831c1429fd841c132ddd631c132dbd541c1419fd831c1419fd841c131ddd631c1319fd839dd409fd849dd309fe885d130f9d43501309fd849dd209fd839dd20fad5450920fcd634c9209fd849dd109fd839dd10fb55450510fd5634c510dbd7455200ddd7358e009dd831c1429f5811c1429bd841c1329f5811c132e6e6695622f2e5591222ece668ce22f8e448ce229dd831c1419ed821c1419bd841c1319ed821c131e766695611f365591211ed6668ce11f96448ce119f5819dd20be88050920be8804c9209ed829dd10bf08050510bf0804c510e7a6695600f3a5591200eda668ce00f9a448ce00eea6688a00f6a5588a00faa4488a00fca3388a00ef26684600f725584600fb24484600fd23384600
def layer223r7 : Packing := (56,3,5,63,0,10,1,packed223r7)
def keys223k8 (i : Nat) : Nat := 0x1f6b0d9ab38400a50630400fd5106a31100199060006c508c24965881ff4865003b2d09b375ccd783664b5b0e6df4a9c00cbc5c0020b0016aa3c009746c31c00dba443780ab15d308400dac00a5000002646313758c951408c005934208684d700040080
def packed223r8 (i : Nat) : Nat := (if i < 1 then 0x348192408214082105080a40c1604108284072060b020848c4158d1082b1870d205c9060050600414202902c5830020a101c8162c180123105234420a4695223448500c9128495204901460a5801220524009102841800c0050828414008004002801400a00500214223040400d9d00214203440400d9d0021420304a060c8010a10182502c6400a38012280140060030100484004aa4c5294c4aa4c4aa4c4aa444a6444aa444a6444aa444a6444aa444a6444aa1530aa854c2a21510f7df7af7476a763f59f4ff4cf4673c735f2bf25717f06ef5ee86daecd6bfeb26a4e93e82e75667e5a64ce3f635627e1a610602df55eb5e15ccdb85aada459358cd7856ad6455354cd3bd27520d16d0cd064f1cdd4cfcc94b84b1c9d48fc89478471c60c4c445c3bc31c2b42141740d4033dd3d6bc23bbbaaba439338cb66b6034133ab2631530eafdaf72e62dc2d22bdab3a9f295287a7a26925f255240a36a2221820a9fd1e51db1d11ca9c41ba1b39a99a319c99618f98918297c17596f16896215b9551399331179110f90f28da8d40ca0c00b98b30a909f09508b08107706d06305904f04503b03102702081a01380d0068007fe77503feb9a81ff5c940ffa64a07fd71503fe98a81ff9dd30ffae8987fd724c3fea1261ff5c530ffa82987fd404c3feb2a41ff55120ffac6907fd43483feb0241ff54120ffa80907fd30483feb2a21ff55110ffac6887fd43443feb0221ff54110ffa80887fd30443feb2c01ff55200ffac7007fd43803feb0401ff54200ffa81007fd30802fe382c57f1c152bfceea177e5550bdeaa285f78cd42bf8e0a15fe774cb7f332657f5d132f7c88997dd634cafe38265fb59622fdaa9117ed6388bf6a1c457f1c161bf8e0a8dfe77507bf2aa83ef55141fbc66a0dfc70506ff3ba63bf99931bfae898fbe444c7eeb1a637f1c131feacb08ff554847fab1c23fd50e11fdc44b07f611583f7112a1fd84550bfceea077e55503dea1a81f78cd40f7a84a07ee22503dea0a81fd84540bfcee986fe664c2feba261ef91130fba86987dd324c3f711261f74c530fec22985fe774837f33241df95520bfae8907be44482feb9a41f78cd20fda84907ed32482ff3ba21bf99910efcaa885fd74443df222217f5cd10fbc66887f541443fa98a21fe9de00ff2ed007f975803fcb2c01fe5d200ff2a9007f973803fcb1c01fe50e00ff2e5007f962803fca9401fe50a00ff265007f971803fcb0c01fe54600ff283007f9318037f33401df95600bfae9007be44802feb9c01f78ce00bfae5007ee22802feb8c01fd84600ff2c1007f950803fca0401fe4c200ff241007f9108033f334abcf95644dbccd19f9e448cf7733445db95622f5c89117ce3388b7b33423dd95611f6c8908fd6338477d33401de95600f7489007da33803f511401fc84600 else 0x683080400972a12104b1408682080400992a12104c140a1424c3400c325806a40e9201b90840181a3810434502086560410cac0821930d0430c9609a903a4826e421045868e0c00d141801948300329060064c3041929a8c3a43718d201070a8c30c1110634184341043a5061b2051f2438d902c132543820a94c2a4490410e1a1c81b2c12e543820e05524a89041549c4c89038685206ca9014b002490024408e94186c8147c90e3640b00c140e002a530a912400438687206cb00b140e003215492824005527132240e1a1481b2a4052c009240091030d0050d0050900509004305870c1420202021d48012a5230a452a00631514a04400c62829408801182c3860a10181010aa4008c161c30508040508012a52389472c72a254088018e504a8110021c)
def layer223r8 : Packing := (163,2,5,63,0,12,1,packed223r8)
def keys223k9 (i : Nat) : Nat := 0x2601682a08dd29014a00026568d6898000000002546d748be2874f366893519123fa590e114ec1d47e9bc89318c21888688c405c46a468b441963000000280c17cd215f8113648d2d5289b859ad42a115178f4008000003cc59cc82dd3fc7611bd3856859e95c43b1ac8db1e202ba60cad49d171dc005cc8accc0028555d946726c948862238001c230499f40009549a000000324127616c001da4cb34e7dc40038eb025811496db40035e61b11882890a4878673d1c5524692788ff830000a34d609e9ccac14cdfe5f650003851c4362c85b9dde15a7cc36a64002071580000ded04d104a0c00000192659761ce268a80008facc296418786c9c80024ec00083c9fe207d31d592210b9a2b0d000124d17b48150a5a85f19d6c03d0c002001000201044860028002021012702189026610007040018216500194e340036a280a4022420002718840a00592
def packed223r9 (i : Nat) : Nat := 0x1a82894e5146a09725107a0a765a0a25091538a2119553c921294f56928894e56a24895438a2119543c921294f52928894e52a24894ea0a4643e825290fa682a43aaa09907195aa92261c652aa48987195a94a689d2a682a446aa0990fa682a43aaa0992aa488eaa488c0aa9a24d2324c02e2afa9a9da528ba0a799c2691865a14a480f6318a82286c1383607800ff597fd54ff58ffd43ff58bfd52ff50bfd32ff587fd51ff507fd31ff583fd50ff503fd30ff483fd10ff802fe66df957be44f78cfee22fd847fa00
def layer223r9 : Packing := (26,1,5,63,0,10,1,packed223r9)
def keys223k10 (i : Nat) : Nat := 0x44e62072215c00d8c1000000032f408200007d80000568d401489a0039e008708c0000730000000d923012aa85c837200008984
def packed223r10 (i : Nat) : Nat := 0x52511ff
def layer223r10 : Packing := (1,0,5,63,0,0,1,packed223r10)
def samples223 : Array (Bits × Bits) := #[(0x1800004003cf00f080079cfff3ffc00fffff,0x191000488045001092028009102449024491),(0x24600061800d3333430019eb400d003ff003ff,0x24622261912512314324492952454912549126),(0xffffffffffffffffffffffffffc9800186000e3cc38c001e73800e003ffffc00,0xffffffffffffffffffffffffffc9844586224a28c28c489452a48a9224a92a48),(0xe0001f8000fc0fc0fffe07c000fffc0000000,0xe0607f8306f80540560e07c30cfc3b0cc330c),(0xfffffffffffffffffffffffffff00001fffff000fff000007ffff00000000000,0xfffffffffffffffffffffffffff00066aa837000ffe00cc07fc6e01b06c1b06c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffe00000000ffffffff8000000000000000,0xfffffffffffffffffffffffffff0a87800038000abfa8f1f8007001c0701c070),(0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf5781557c0fff00007000003800e0380e0380),(0x0,0x0)]
def cols223 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(2,0,221,0,8),(4,0,219,0,8),(8,0,215,0,8)]) (.leaf [(16,0,207,0,8),(64,0,159,0,8),(128,0,95,0,8),(0,64,23,136,7)])) (.fork 4 (.leaf [(0,128,15,80,7),(6,0,217,0,7),(72,0,151,0,7),(144,0,79,0,7)]) (.leaf [(0,2,216,5,6),(0,4,216,3,6),(1,0,222,0,6),(8,128,7,80,6)]))) (.fork 7 (.fork 3 (.leaf [(16,64,7,136,6),(24,0,199,0,6),(64,128,15,16,6)]) (.leaf [(128,64,23,8,6),(192,0,31,0,6),(1,2,216,4,5),(1,4,216,2,5)])) (.fork 4 (.leaf [(10,0,213,0,5),(12,0,211,0,5),(18,0,205,0,5),(20,0,203,0,5)]) (.leaf [(80,0,15,0,5),(136,0,23,0,5),(80,128,15,0,5),(136,64,23,0,5)]))))
def levels223 : Nat → Packing
  | 6 => layer223r6
  | 7 => layer223r7
  | 8 => layer223r8
  | 9 => layer223r9
  | 10 => layer223r10
  | _ => emptyPacking
def index223 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 16 3 8 4 0 keys223k7
  | 8 => lookupWord 18 69 6 10 6 0 keys223k8
  | 9 => lookupWord 54 189 7 12 8 0 keys223k9
  | 10 => lookupWord 8 48 3 9 5 0 keys223k10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun j => samples223[j]?.getD (0,0),cols223,#[[]],levels223,index223,noFactory,noFactorySound 223⟩
def packed251r6 (i : Nat) : Nat := 0xc23db2443cab0045e65e8854050
def layer251r6 : Packing := (2,4,5,63,0,3,1,packed251r6)
def keys251k7 (i : Nat) : Nat := 0x1dd
def packed251r7 (i : Nat) : Nat := 0xc101049990201928c2040404126a3080021708200001060620580164058811801085c042a306801a4046010d0400217002a2c008381c3045c10106002040010e04380420d04340420106005041410000000000000000000000008200000000000008506141000000000000000000037cdbb60d2b44cbb20c4afcbdaf0b6ad4b3ac0aeaaca7a90a0a6c95a488ea2c87a1082a047b9d8729bc6b9a06698c5f9705694c4d92848914419003e8f43b8e8388dc358d0328c42f8b82c8ac298a026894238882087c1d8701a85c138481083c0d8300a824078180480c018009fd829dd53ded7550932fad5450932fcd53509329fd829dd51fd55354531ded7558921eed6558921fe562545219fd829dd609fc8754560eed62485609fd829dd50ded829dd50bed829dd50dee771c950ded761c950ded741c950ded731c950f6d531c950f6d6254950f6d5250950dec725c550f6c7254550fe87258150f795258150f7951581509fd829dd409fc8754d40fad424c940ebd6458140f795354140fe88254140f795254140fcd424c9309fe885d520ded744c920ded7648520f795354120fe93254120f795154120fe92154120fe562485109fc8795600a7d861c255b3d841c255e3e66956448fd869dd53f1e5591233e6e6695622eae6691222f2e5591222f4e558ce22f8e448ce229bd849dd51e766695611f56558ce11ee66688a11f665588a11fc63388a119dd839dd609ed829dd509ec8788950b7a8854050e7a6654050f3a4454050f5a3354050f688254050d797254050f6a2254050f7211540509f5819dd40bd9831d600bf1811d600e7a6695600eba6691200f3a5591200f5a558ce00f9a448ce00eea6688a00f6a5588a00faa4488a00fca3388a00ef26684600f725584600fd23384600fe22284600
def layer251r7 : Packing := (87,3,5,63,0,10,1,packed251r7)
def keys251k8 (i : Nat) : Nat := 0x154b3a002d2ecc72de73926462476ee68332854c0549abe091f1e29136e2b94793a42001701d791a001b5a88e0e51b8f020ea099ec3f41fb3973cac22b0956e2c7a1c88f6813725800508209a4fad000000000000000034622c00145c058bdd61e60aaa0a63caeb03e2900054e5374ef5000000006536000cc985129a7c00000445f121c13f74232b9af92c200b8b4451060820000c328f68a8912c228138034024110a
def packed251r8 (i : Nat) : Nat := (if i < 1 then 0x4583fea92c1ff50960ffaa2b07fd21583ff3baa1ff5d950ffacaa87fd74543feb22a1ff55150ffae6a87fd53543fea1aa1ff5c950ffac4a87fd52543fea12a1ff4c950ffae2a87fd61543fea8aa1ff4c550ffa42a87fd60543feb2a81ff54d40ffac4a07fd52503fe99281ff58140ffaa0a07fe554c3feaa261ff54930ffa84987fd514c3fe90a61ff54130ffa80987fd76483febaa41ff59520ffcaa907fd74483feb2241ff55120ffae6907fd53483fea1a41ff5c520ffac2907fd51483fe98a41ff58120ffaa0907fd40483fe98241ff59510ffcaa887fd53443feb1221ff54910ffa64887fd60443fea8221ff4c110ffa40887fd65803ff2ac01ff59200ffaa9007fd62803fea9401ff50a00bfceeb2f7c709577f334abdf59655bfceeb26fd65593bf2aac97f9dd54bfaecaa6fe66553bf2aaa9ef59154f7acb227be55912ff3baa7df95553f7c88a9dfe7750efebaa87df95543fbaa6a1fde558cfeeaa4677f9dd62dfacab177e5558bdf222c57f9dd52bfaeca96fe6654bbf2aaa5ef91152fbc66a97ed6254aff3ba857f5d942dfccca15fd7550bbf2aa85ef55142fbc66a17ed5250aff3ba657f5d532efcaa995fd744cbdf22265f754d32fda84997ed6588bf72ac45fb59222fdaa9117ed5388bf6a1c457f9dd61efcaab0fee22586ff3baa37f5d951dfccca8f7e55547ef19aa3fb88951feac2a8dfe774c6febaa63df95531fbaa698fee224c7faa8a637f9dd21bfaec90efe66486febaa43df95521bfae690fde33487f6b1243fd54521feacb08ff655847faa9c23fd58a11feaa508ff532846ff3bac1df95560dfac8b07be445837eb12c1fb88960dfac2b07f611582ff3baa17f5d950dfccca877e55543df222a1df54d50fbc66a87ec72543bea92a1fb88950efaa2a87f611543fcb02a17f5d850dfccc285fd74143df220a17f5cc50fbc66285fd72143f7110a17f5c450fec22285fe77502febb281bf99940bfaeaa077e55503deb2281ef50d40fbc66a07bd42503f711281fe54140bfcee985fd754c3bf2aa617f5d130f7c88987dd324c3f711261f74c530fec22985fe77482febb241bf99920bfaea9077e55482feba241ef91120bfae6907de33483f699241fb48520fec22907f950482ff3ba217f5d910dfccc885fd75443bf2aa217f5cd10fbc66885fd72443f711221fd4c510fea42887f875803fcb2c01fe95600ff2c9007f954803fca9c01fe50e00ff2c5007f952803fca1401fe4ca00ff2c3007f951803fc98c01fe48600dfccd0077e55803df22401f78ce00fdc45007f611803fcb0401fe54200ff281007f930803fc90401fe44200cfccd2aebe669139f2ac89d795633f3c8919eee6688bb72ac45eb91222f9c67116f666847bb2ac23f58ce11fcc4508f79501437d33401de95600f7489007da33803f511401fc84600 else (if i < 2 then 0x870098d0c0848e344800c0103a3800c20e363804468630305060848d001080a38d920022830582a238d1e0029a2a88f2410e363480c005240090830014208b1320c49090048c4188e12009088311c2401080060384802182c5090c1420304050560c001503058282282802828220a3944705045931e2c08651c342a191042146a78e0a08831851183020140c15042101014e2c541083020140a1504204c171c3484c82108080a7122a08460a8e5e4020a3971202008202031c58b01004903978c3822e1c0401210e5e3808020c5e3c618181012090c0c0019028584086032000a16102147084324204505103538b0810c10182004060601418910023058a121018201420042024e5e440086080c00a15003187288e30d4f1a004c170d0640c101018e3c60c06382122c004202031c48b0010c10181122c004304060848b001121438e502851a1d0c8161480c0051828c149002440a106002841420a00518009002801400a005002801400a005140090c00a0200a003001000a8854478a3c3221909e2510c04112785442a23c51e1511e28f08585443010449e1510c041127877e1bdcde46f0b75dba8dca6e036e7b5fda5ecfb671b24d816bbb5b5ac6d596a5f4eba61d2368cb43da0acfb676f373997cbe654f26391dc84e3d71c38b8c5262430eb853c2360cb04b811bfedfa6f8f7acbc1ddbeea9732b84dbbad996aab47d9d2cc164cb1c5876bf75e7ae9d6feb655acacc5612aef563aa7d526a4f513a86d3e69af4c3a57d28a91d47aa33514a861415a00cfb67b33c59d8ce7671337c9b44d5268132c98c4ba25b72ce960ca9a4fb270920485e4151fd8ea471e3751988c245c22ab12c88fc4121ef0ea867c2b6141093831c0ea05b020809c019fd6fbb7c23ddde9cf4178fbc49deeedc75d3ab5cfae7072ab8cdc4ce1970637fdbd6dde6e1b6d9b52d876af3529a6cd2268733cd9b0cb6654b239902c66625b06d81cbec5efaea1736b795af2d45688b30591ac59612ae7569aae1548a8953aa96948c9f34e526d934498e4b9a57d26c914483a3b11b08bd44a221d0bc851414206cfd67de3da9ea0f0c7643a81c9ce266f836e9b24d5c69a33f993cc4c6192f8178cb825b42c595f8a9c52c28f93849a84b225291f08de45421c90b08143da1d88e906f636e1a28ce061e30216c8adc55429d1480a0c4ec26212a892047622e11088504001f30f307643981bf0d906943301840b8057029e14209a84a022810707d03981b20c505c02ac12e08a03b01a40b804f01d80b804200d0007fd65553feaa2a7ff55162ffaeca97fd6554bfeba2a5ff59152ffaa8a97fd7354bfea9aa5ff50d52ffae2a97fd7054bfeb2a85ff54d42ffcaa997fd544cbfea92c3ff59551ffaa6a8ffd62547fea92a3ff4c951ffcaa98ffd524c7feb2a43ff95521ffaa690ffd5 else 0xbc30a24208d0b0803104200c9708bc10920292084585048c100a8c08a86482a428982145223224287002490e046703431324380143282430c4c2262421246222982484450668242302190908c4908a8c0c22384006ca442c2192060b12243141481214111d0d04c17160a30922189241441972d0470884138622420952f1141d1234311b31046888e0a00c985823868a446c48a0a40cf03805c4480c1401d2c0382c3320e01790a05802e445021c6860430c9060890a0890a0890a0319246006884450486104821048810080c083100900240584405840104808748405040101211046006c8406848a085041410421d0421e2421e1821e9010e107890318f1210f12122801218010d8010d8011e0a1058429d08d0508e450829908ac508283020241e18342801800c33a5c318184178e2c304284040639a18282020058b0c14008b0c1cc2815203001162640e922200a2200a1161c185020240a161022018e0e0028c18270c0618c088324106082142030400c8c1418200305400a0050028018a6144618284051ca8c3030582a23971e08214202002c5820862e1e0c90414a5e3c704a0e0c180903a48208b0c1420014341060881d1a68b213c8901800a30518292004881806c6870018008c151c6c8141018e245860028600286002860020e106))
def layer251r8 : Packing := (311,2,5,63,0,13,1,packed251r8)
def keys251k9 (i : Nat) : Nat := 0x73483b3a1143fa9279fd0d604d287209ad112aa30f3b87d8650148b144b0312a1f07c2e757fac976c9c9719dedc03d9c25c0703da4370d2e0ca48b3c1a160cd7213829818dfdcc2000219442766327223b48d10441385bece2ae73c99149800000065e6154001e2769aeba522600020e00000000000156832e1fe4c0000b4000167c0000000000a54a6ef3e8000e16f65f12899512e00041b79eeb0a69100039fe00011b136055ac1a32380005aa82b000326dd09e9f98c1064161136d5a0ba3d9bcf6d98f23148401b679f03a00ba49d46f1c8da3eabd14042f5b549c4054a549ac63700043d0001c3a795fa4e62eae517e42ee65e31072341d186444f75ee206d80cc1d8a000000000072c62cc1f04c40000000d716b500003c4000699c3a80019040000000001906702000246f02b719325ba8f66002fe103a6183bd0d847397fdc1a106530ac907dcd2588eb1d638934c40596d4084ea937e1780018cf696290f60f8a976bf1dbda6a2144b82f84ee035718204b1f2000b73822d4ba209377e47f124689d5bc0eda3b60db296940dcc85600000001e5acc6758002dc4e57d633c682660000005a2814a0005360002d226d44785a9e070802b30f093a3d09a9507c0c853ae370fc16a0e32db312b1bb9bfcb1b5d588d64f328329eb7bc67464a3d71f5a08aa4d7e8021640e14522b19cc590008304c8e479659027502c42328f1801889ddd040d511970802c87b0bcca80a3e2e3570003cfd29e186000259082d6350a580f364100068c656d09494edca6a5a46215453169ebc07d57eab2121e392908020c13040b062c010316010c039d0601100b020107002200080d00000a081d031a0308130600030510064718000600050203090001050218020602000103000008060211062c070211040204070200280600061300010500070c002503010300040000081a
def packed251r9 (i : Nat) : Nat := 0xb098f4e44c2b10af44e34ee8c2c2b903ce2c25b540f30c2c274e44c30abc27103cee0c2b00ce44e2d00ceccaa8c2ae0d03cea0c29c0ce44e30ac426903ce30b09b40f32630b09a40f3a230a68340f38c2c2c4e44c08c2c344f330742b9b44e30b48c2c2bd03cc34252539130d4033a128d0927d03cc31d09b44e2cf0ce4460423513cb0d03c70ce44744e0c70d03c60422d13cb1d2224147d4f01c8360678c316e2ac504949111f839c648b413e2343c0600a81081b02a03c048003fd65ff957fd64ff553fd53ff50ffd62ff54bfd42ff4cbfd61ff547fd31ff487fd60ff543fc50ff503fd30ff483fd10ff802fe66df957be44f78cfee22fd847fa00
def layer251r9 : Packing := (29,1,5,63,0,11,1,packed251r9)
def keys251k10 (i : Nat) : Nat := 0x8800158280195104c9aec6ec8034e00000013000e1a58c5ed00000005094369e8000000053937e000cb5b006bedc00000024200466459190
def packed251r10 (i : Nat) : Nat := 0xa0f1ff
def layer251r10 : Packing := (1,0,5,63,0,0,1,packed251r10)
def samples251 : Array (Bits × Bits) := #[(0x2030010e01007c0c001c803267007fffffff,0x203441060144140d2004a410234804892291),(0xac00033e6004d100193003d99ffd00401ff,0xac28810e6294910c39318a48831d324c866),(0x0,0x0),(0xffffffffffffffffffffffffffffc300063c7800722001e3ffce1e006007fe00,0xffffffffffffffffffffffffffffc30a1e3878a362228aa151ce1ca56a669d4c),(0xc0007c07fff83c001fc000fe0007ff80000,0xc009a402a0b83c04bf8098fc0157170582c),(0xfffffffffffffffffffffffffffff00007ff800003fffe00000fffff80000000,0xfffffffffffffffffffffffffffff00c17ef00c202670c00610b77c60c431188),(0xfffffffffffffffffffffffffffffffff800000003fffffffff0000000000000,0xc50e000000c0198715e8e30001801806030),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffff3af05bfd5f07c038000700000e00e0381c0),(0x0,0x0)]
def cols251 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(2,0,249,0,8),(8,0,243,0,8),(16,0,235,0,8)]) (.leaf [(32,0,219,0,8),(128,0,123,0,8),(1,0,250,0,7),(64,0,187,0,7)])) (.fork 4 (.leaf [(34,0,217,0,7),(144,0,107,0,7),(0,2,216,33,6),(0,16,106,129,6)]) (.leaf [(0,32,153,66,6),(0,128,43,80,6),(1,2,216,32,5),(1,16,106,128,5)]))) (.fork 8 (.fork 4 (.leaf [(3,0,248,0,5),(9,0,242,0,5),(10,0,241,0,5),(17,0,234,0,5)]) (.leaf [(18,0,233,0,5),(24,0,227,0,5),(40,0,211,0,5),(48,0,203,0,5)])) (.fork 4 (.leaf [(64,32,153,2,5),(64,128,43,16,5),(72,0,179,0,5),(96,0,155,0,5)]) (.leaf [(130,0,121,0,5),(136,0,115,0,5),(160,0,91,0,5),(192,0,59,0,5)]))))
def levels251 : Nat → Packing
  | 6 => layer251r6
  | 7 => layer251r7
  | 8 => layer251r8
  | 9 => layer251r9
  | 10 => layer251r10
  | _ => emptyPacking
def index251 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 1 0 keys251k7
  | 8 => lookupWord 29 103 6 11 7 0 keys251k8
  | 9 => lookupWord 103 356 8 13 9 0 keys251k9
  | 10 => lookupWord 9 49 2 9 5 0 keys251k10
  | _ => fun _ => none
def g251 : Forest := ⟨251,10,fun j => samples251[j]?.getD (0,0),cols251,#[[]],levels251,index251,noFactory,noFactorySound 251⟩
def packed239r9 (i : Nat) : Nat := 0xff
def layer239r9 : Packing := (1,0,0,63,0,0,1,packed239r9)
def samples239 : Array (Bits × Bits) := #[(0x403004dc3cf06001003d37003ff00ffff,0x4034204c0450688144141344045444545),(0x8c00b27d330800600cec9ffd00ff00ff,0x8c24101512085062848402952829282a),(0xffffffffffffffffffffffffffffffe93000c38e3cb001800f30e00e00ffff00,0xffffffffffffffffffffffffffffffe93088c30a28b121890a30c90a90929290),(0xfffffffffffffffffffffffffffffff1c000fc0fc0c001fff03f000fff000000,0xfffffffffffffffffffffffffffffff1c0a0f80f80c140aa103e0a0fa2a0a0a0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffe0000fff000fffe00003ffff000000000,0xfffffffffffffffffffffffffffffffe00c0efe000d3820c003bfc20c0c0c0c0),(0xffffffffffffffffffffffffffffffffffff000000ffffffffc0000000000000,0x150f0000002c3d51efc001c01c1c1c1c),(0xffffffffffffffffffffffffffffffffffffffffff0000000000000000000000,0xffffffffffffffffffffffffffffffffeaf0ffffff01c00e00000e00e0e0e0e0),(0x0,0x0)]
def cols239 : IndexTree ColumnInfo := (.leaf [(128,0,111,0,9)])
def levels239 : Nat → Packing
  | 9 => layer239r9
  | _ => emptyPacking
def index239 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g239 : Forest := ⟨239,9,fun j => samples239[j]?.getD (0,0),cols239,#[[]],levels239,index239,noFactory,noFactorySound 239⟩
def packed127r9 (i : Nat) : Nat := 0xff
def layer127r9 : Packing := (1,0,0,63,0,0,1,packed127r9)
def samples127 : Array (Bits × Bits) := #[(0x60001e1003d29a6e0073ff3ff00ffff,0x6480021241400826500029029282929),(0x40800668600ced6593ffad00d00ff00ff,0x40882628642484208086a544544454446),(0xffffffffffffffffffffffffffffffd8b001871800f31861c01ce00e00ffff00,0xffffffffffffffffffffffffffffffd8b111851888a318619214a90a90929290),(0xffffffffffffffffffffffffffffffe0c001f81fff03e07e001f000fff000000,0xffffffffffffffffffffffffffffffe0c012a80a0b03e07c025f014f16141414),(0xffffffffffffffffffffffffffffffff0001ffe00003ff80001ffff000000000,0xffffffffffffffffffffffffffffffff0193ffc0ca03ff001a5ffd60d4d4d4d4),(0xfffffffffffffffffffffffffffffffffffe00000003ffffffe0000000000000,0xffffffffffffffffffffffffffffffe9d21c00000c03bdf7e380018018181818),(0xfffffffffffffffffffffffffffffffffffffffffffc00000000000000000000,0x162de157f5f0fc00001c000e00e0e0e0e0),(0x0,0x0),(0x0,0x0)]
def cols127 : IndexTree ColumnInfo := (.leaf [(16,0,111,0,9)])
def levels127 : Nat → Packing
  | 9 => layer127r9
  | _ => emptyPacking
def index127 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,9,fun j => samples127[j]?.getD (0,0),cols127,#[[]],levels127,index127,noFactory,noFactorySound 127⟩
def packed255r7 (i : Nat) : Nat := 0x32707270727040000000000000000000000000000000000000000000a852a893e9c4ca59269046a290e84409f8f6783a9c8de672f95ca8512712c9045210fc78391b0cc602d1509c48210f06c30150903c18090300c00d17b4ed3120c20c3a4f69da52418418751ed334a4830830e99da768c9061061d53b4cd1920c20c3ac7695a3241841874d6d3b444830830eaada66889061061d65b4ad1120c20c3ae368da2241841874dad3b424830830eb35a56849061061d72b46d0920c20c3ae9689a1241841868bedb94cca900a0d35db32999520141a6db645332a4028316f2e997590805069d6da14cc9510884b9db32a66661010c2fb6a54b0eb20218776cca961d640430f6d9152c3ac808517db7a65855901093bb6f552c8c182127b6deaa5918204295eda532c32e008533db4a65855c010a73b694cb06b80214eb6d299609700428eed9d32c3ac008535db3a658558010a73b674cb08b00210f76ea9960d600429e6d9d32c12c00852f1b8a661158060c7c510d1120a0a219b8999a2241414433d0b2344482828863e1b26a29944010c7c350d15328802147c6e2999dd10042978dc533332200853b1b8a664444010c7c3754cb04880212f86ea99609100438f14cceec12200872e1962598244010e5c5333330488021e389de66609100439d14cc88c1220087aa2669118244010
def layer255r7 : Packing := (52,5,5,63,0,9,1,packed255r7)
def keys255k8 (i : Nat) : Nat := 0x25127cc60000b4c897a071c28c730b7c700290000000024844e9a00342ebedb002e51ba0fda8009a166000193889eea771a1249285cdcadb00758a8b0d82820cb5283357ce69312001c515aa700033cd0803441004cd6000cb060
def packed255r8 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x99442008ff2a197442008ff2a196442008ff2a194442008dfaa99520171c9f9999520171c6fa667761061acf6949061061ae768c9061061aeb6889061061cee64090610618dfaa99520141c9f9999520141ccf6556420141cb79999320141ce75919320141cbb9999220141ceb5919220141b9d6949899a11b3d69c9099a11b9d6949099a1197d69c9099a119dd6949099a1197d69e99592119dd694905c6119dd696995861197d69c90506119bd69890506119dd69490506119f568c90506119f96889050611aed6928884570caf2616450560af568e8884560bbc2816484560bbc2816184560dbca661158060f3c9de1158060fac91211580608bf6a29958060ceea209050540dae9989050540b6e69c9050540bec2814184540a7b68a889dd10abb68a88999108fb68a9961110aeb68a88911109de694905c510aed2a16450510cfca209050510dbc9989050510dec5909050510bdc6949050510bf868890505109de69490505109fa6889050510e1f9de6661410c6fa667761010cafa666661010e2f9de666101087f2a58759010e2f61e6691010e8f9998591010c77a667760c10cb7a666660c10e379de6660c10ce7a664460c10ea799a4460c10e3b9de6660810eab99a4460810cfc6a29944010df868a9944010afc6a29944010bf868a9944010d7ca667744010dbc6589644010dbca666644010f3c9de6644010deca664444010fac99a4444010ef8a658244010ef865d8244010ef86598244010ef82598244010ef85d98244010ef89998244010ef86518244010ef859182440108fd6a29944010aedaa98444010ceda658444010e6d9dd8444010ead9998444010cf5a658344010e759dd8344010eb59998344010ee59118344010cf9a658244010e799dd8244010eb99998244010ee99118244010eec6117044010ef86097044010ef460d6044010ef86096044010ef8609404401097e2a67761a00e3e9dd8621a009eeaa99421a00d6e9dd9421a00bb668c9899a00bb668c9199a0097e69e9959200cee2618459200eae6188691200e7c9dd8120600ebc9998120600eec91181206009de69699586009eeaa99418600d6e9dd9418600bf86889884600ebc6188684600bec6908684600f3c9de6684600fac99a4484600b3e69c9099a00b9e6949099a00af968898846008fb68898846009f668e99582009fa68a994420097eaa997042009beaa99604200d3e9dd9604200d3e65e6604200d5e9dd9504200d9e99995042009eeaa99404200d6e9dd9404200dae9999404200d6e65e4404200dae65a4404200dce6564404200d769dd9304200db69999304200de69119304200d7a9dd9204200dba9999204200dea91192042008be6a299580609f868890505108fc6a29944010cf8a658244010e789dd8244010eb89998244010ee89118244010 else 0x1d5f65d9520141d9f6599520141d6f65d9420141daf6599420141dcf6559420141d6f65d6420141dcf6556420141cf7a219320141cf76199320141cf72199320141de75919320141d7765d9320141db76599320141dd76559320141de76519320141cfba219220141cfb6199220141cfb2199220141deb6919220141deb5919220141d7b65d9220141dbb6599220141ddb6559220141deb6519220141df364d9220141c7f65d8020141cbf6598020141cdf6558020141cf764d8020141cfb649802014197f69c9099a119df6949099a1197f69e99592118ff68098592118ffaa89858570aef69288845708ffaa8985c5608ffaa89850560cef6909850560af768e88845609bf2a564845608ff6a299504608ffaa898585408ff6a68818540cef2608650540b6f69c9050540baf6989050540bcf6949050540be768c9050540beb6889050540ded6454118140cfb29992a2110cfb65d92a2110cfb65992a2110cfb65192a2110afb68a8821910afb68a885d910afb68a889991097f69e99591108ffaa89859110afb68a8859110bed6908650510b7d69c9050510bbd6989050510bdd6949050510bf568c9050510bf968890505109ef692995c110afb68a885c1109f768e9958110afb68a8858110fad59141581108ff6a68818110afb68a8818110ded6514118110afb68a8850110ded6594150110adfaa97661410aef69e9961010aef69a9961010aef69c9661010aefaa97661010aef2a57661010eaf6597661010aef2a666610108ff6a2995901097f69e9959010a7f2a58759010c7fa658759010cdfa658559010af7aa99760c10af7aa99660c10cf765d9660c10af7aa97660c10af76a57660c10e7765d7660c10af7aa99460c10af7aa96460c10af76a56460c10ee76516460c10afbaa97660810afbaa964608108ff6a2995c0109ef692995c010cbfa65865c010cdfa65855c010cefa65845c010e6f69d845c010cf7a65835c010cfba65825c0108ff6a299580109f768e9958010c7fa658758010cdfa658558010cdf65d8558010cefa658458010cef65d8458010eaf6998458010e3f61d6458010e9f6156458010eaf6116458010cf7a658358010cf765d8358010eb75918358010cfba658258010cfb65d8258010ebb5918258010ede6157058010eee6117058010ef660d7058010efa60970580108ff6a29950010c7fa658750010c7f61d9650010cbfa658650010cdfa658550010cdf6598550010cf7a658350010cf76598350010cfba658250010cfb659825001097f69e9959200cef69098592008ff2a56460600cbf6588620600aef6908620600afd68486206009df69699586008ff2a197586008ff2a58458600cef2a194186008ff2a194186008ffaa898506008ff2a19650600aef2a164506009f768e99582008ff2a196502009fb68a) else (if i < 3 then 0x4220904460024180000c808001981020320266b204040110422098a080220c8c182080110c1028d421402350852306460c8c11183028c42128c18146a109460c9019203240648080009242100029142100a4108402914210000181000000000000a080000001810000007002e0040c30386f20586f2040380170028aa384e00614c708c10c298f100001c007800f001e003c007800f001e003c005800e801034008004000000000002801500202801000820800000000000003345f0f824f280000000001041041e0860820820820b042e33004e270982381c8080e33004000000000000000000000000000000000000070010000000380080000000000000e0040e002c00400000000000000000000000000034160378bc3e09bc5e109e9e402f8bc3e09217e2f0c6e7f178617278bc30b8dcfe2f0c2e4ed9ecaec4e88e82e73e6de67e61e52e4ce46e40e3ae2be13e04df5de6dd7dc8db9db3dadda7d8fd89d71d62d53d4dd47d41d3bd35d26d0ed08cf0ce1cc9cc3cbdcb7cb1cabc93c84c75c5dc57c51c4bc45c3fc30c21c12c03bf4beebe8be2bdcbd6bd0bcabc4bb5bafba9ba3b9db97b91b82b73b64b55b46b37b31b2bb25b1fb19b13b0dafeaf8ae9adaacbabcaada9ea8fa80a71a62a53a44a3ea38a29a23a14a0ea089f99f39ed9de9cf9c99ba99999398497e97897296395d95794894293c92d91590f9098fa8e28dc8d68c78b88b28ac8a689789188b87386d8558468378288198137fb7ec7e67ce7bf7b07a179278377d77775f75975373b73571d7176ff6f96f36e46de6d86d26cc6c66c06ba6ab6a569f69969368467e67867266c65d64e6486396216096035f45e55cd5be5a659757f57957356d55e54f5405315225135044f54e64d74c84c24b34ad4a74a149b49548f48948347d47746845945344443e43843242c42642041a41440e4084023fc3f63c33bd3b73b13ab3a539f39939338d38738137236c36636035a35434e3483393213002fa2eb2e52cd2c72c12bb2b52af2a92a329d29729128b28527f27927326d26726125b25524f24924323d23722822221c21621020a1fb1f51ef1e91e31dd1d71d11cb1c51b61b01a119218c18618017a17416e16816215c15615014a14413e13813212c1260ea0c009607504b02a0008ff6a481201649df694905c561aef6829961061aefaa89061061e6f69c9061061eaf6989061061ecf6949061061ee768c9061061eeb6889061061eed68490610618ff6829961061adf6949061061af768c9061061afb6889061061bed6849059141cdf2999520141cdf9999520141cf79999320141cfb9999220141cdf6556120141cf764d6120141cfb6496120141c7fa219720141cbfa219620141d3f65d9620141c7f65d8620141cdfa219520141cdf6199520141cdf2199520141dcf691952014 else 0x8e04003014c86230980680470c104023840000030e093499130c16182c3049a0d881b1020000192c4100e43104c506c408000000145868b640807238826282c572040000000391c413141b002c5720400000005801b0036006c00980100000000000024020000000018307060e0c1c18383048a0c0000000001c0040d202a307060e0c1c1838307060f001d183c00742090c100021820290100030820006404c80c009))
def layer255r8 : Packing := (345,4,5,63,0,12,1,packed255r8)
def keys255k9 (i : Nat) : Nat := 0x4057ce6c7605c5c8997dc242190003402000b47232662de1371e5c92d208c49a5926d80ace5793d39ad86f080007424999f12a34e54052e0000007bd80004a6a3ce930cb62c7575ad5c000000232c4c40000005326bd7c052980000852279ee2000586ac3c496b5d0000567d07995294cea6ce19a06a8783694c10923e21534b6145d1e09b034152ce03c44dece156f8ef0d6d19e5000bc9122003a17121c86095c3b9a70c1b2cbba579d28d86db179b811a9a0e7337e20ca89b21b6ecbc415ca7e2a298ad8613520231c3991e54ec7532225d08a25557315118735000510899051c79c5181922408a523cbf48e000e70286706988696d29a80428acea7e9d6d0a4c181cf2f352430327f29880be000a868ca4000f510004bbc00111a72f000000007a00061ee5ab72018b80034214d755eb95717348259c800185c268404cd50c80b3762e7b3c8532c202a738ce926eea1d327c050836597398c5a3aed07e545322ae2d20762c115f10cf99acfe4e1efdc035942100c07ba194efc23f3e1391c16cfbaec04c8058150711d650a2884105d52089f307131ee0c69b7c6fe8d84d115a10331fb1f912da8ff3016f1110e5812696fe948169cfbf2728c60b0910b38f2ada9072d39b687714e81f000209e8b4ad9d89f2eee080007ac0001e75e9e00013fda1e0006850003e6845104ee9bb817035685d15e54a0000000318cc200071500028ce000c25421cd2683d794355b04b4bf7425351d6ac49627f3cba4ae45a3338b140600006b70cd19beb782680039e1300c7cd871d4712ba816c6144400cc7d0001928c3eeaa800260200019900021e891b0005c8c67a4170001474001cb21836b700004f757209fc181ad3b748003da00b1111fb48415d460100032c01000c0005060d392c1c1109000000030d0219501d31070102030700000c020718060022080006110f06011b055b06090b1d0a05010c020d07000603210102020006090000000600010200020024380101080400053d2d0201005b0003030203000900fb1e19021d04070b00000e02
def packed255r9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xccb90d0077e9dc86802ff328434017f99121a00bfd4caed005fe26176803df13133401ef98799a00f7c48ccd0077e9de66803df30d33401ef97699a00f7d33309005fea6564802ff130b2401ef88659200f7d332c9007ee61164803f730d22401fb88691200fdd334890077e9dd81803df4ccc0c01fba4460600bfccb9030077e9dc81802ff32c40c01efa6620600bfcca103007ee91081802ff532b8c017f8985c600f7d332e3005fea6561802ff130b0c017f99758600efd3bac3007be21961803df4ccb0c01fba4458600ff8b8ac3005fe65c61803bf4ee30c017f99418600fdd220c3005fea6541802ff130a0c017f99650600f7d33283007ee59141803fe102a0c01ff09884600ff8c3c23007fc25a11803fe30d08c01ff08684600ff8bb423007fc99a11803fe30908c01ff16484600efd3bc23007be99a11803f748908c01ff18184600ff8b8c23007fc58611803fe28308c017bd9421a00bfcc810d0073f9de66803df12133401afe66612009fe4c2c9006ef61164803d7ccd224019fe7760600d7f33303006ef91181802ff32040c013fc985c6009fe4c2c3005ef65061802ff32030c013fc9850600dfa4c423006fd61e11803becef08c01bf58684600f7b33423006fd61211803f6c8908c01ff090846009fe4c423006fd60611803df4ccb8401df9715c200ff908ae1005fea6560802ff32eb0401dfa7758200f7d332c1007be59160803f7488b0401ef96158200ff908ac1005fe65c60803bf4ee304017f99418200fdd220c1005fe64460803fe422304017f99650200f7d33281007ee50540803fe422a04017fa9944200bfccba210077e9dd10802ff32c88401efa6644200bfcca221007ee91110803fe28288401ff21144200bfccb8210077e9dc10802ff32c08401efa6604200bfcca021007ee91010802dbb2640ccd4fd9720266b3eca9013347f65c8099a6fb2a404cd1fd97a21649beca900b8cdf6568858677d32c20c39be77610618fecb900a0cbf658805066fb2a402833dd93201419f6c9100a0f3d9de66847d6ccd224233bd94a21709eec9d10b05be24164582df120b0ac16fa9958060e7d3bac0307ae91160183de422b00c17b890505409f6c9510885fc241414423fd32c38212fe9961810c7f3bb0c0863f61e660432fceec2821a7e66614109df4cb080866f9dd8404357cccc20219bd8791010d5ec3488086cf616440427bd32c18219de7760c10d6f33306086e7911830433dceec1021aee6660810dd722304085fca6510043be4ee88021ef26644010fd922220086ed611100437ab0688021be58244010d7cc310d005ee650868039f4ef33401eba6691200df8c0903005ee65061803be4ef08c01ef26684600fd9224230057e65c10802df32c084017799504200bdcca021005f664c10802fd32408401be18244010 else (if i < 2 then 0xb100a0ddf65480506fbb26402837ed9220141dfcc0100a0dfd65c86847becee434237f59421a11bfac810d08dfda6576846fe930bb4237f4905da11f7a4c4cd08fbd24266847becef33423ef57699a11bfa484cd08dfda6564846fe930b2423ef66659211bfa482c908fed21a44847f6ccd224237f59720211efb3b90108dfd65880847deccc404237f59420211fdb2210108f3f9de668467f930b2423ebe6691211f7b332e308dfd24171846fed32b0c237f59758611efb3bac308fbd99961847f6c88b0c237f49058611bfacb28308fbd99941847f6ac8a0c237f49050611cff3b90108ebf998808467fb2840423bbe44202119fec8d10b85f764c815c27f930b0ae1bf49884570dfb44422b87bd99a115c27f93108ae1df571845709fec8d10b05ef650815827f930b8ac13fc9850560f5eb2282b06fd262115837ed1108ac1bf58784560efb3bc22b07bd25a11583deccd08ac1ef56484560fdb22422b04ff26211583deac308ac1ff2115c1609ff4cb08304ffa65811833fceec08c1bbe44604609fecc282306ef611411837eb02a08c1bf58784460efb3bc22306fd61211183f6c89088c1bf58184460f7c48ac0307be50560183df422b00c16fe9958060e7f3bac0306bf61160183d7c88b00c1afd8158060f7b08ac0306ef652885027fb2344281afd8621940d7f444cca06fd604815027f930b0a813fd9818540bdeca0c2a05efa654150377d10a0a81bbd8650540f5f33282a07ed20541503f7120a0a81bf49884540dfb44422a06fd61a11503deccd08a813fc9884540fdaa0c22a07be580605027fb2944221bed92a2110dfac8d10885fb64a884433fd113ba21afd8621910d7f444cc8873f9de664427fd32c2221afe66611109fe4c2c8886efa2244443d7ccd222217f8905c510bfc482c2885fda65414437ed10a0a21ef66650510fdab2282887fc24141442ff120a0a21bf58784510efb3bc22886fd61a11443deccd08a21bf58484510fdb22422887be58060443f6a82a0221cfe7799810dbebb30a086df9998504377d32c2021bbd9761010ddecb308086ef2598404377aecc2021bbe66610109ff4cb08086bf999840433fb0eb2021b7d8559010ddec22c8087af99a440437bb2ec1821bdd9660c10deebb306086f7999830437bb28c1821bdd6460c10df6bb304086fb999820437dac8c1021afd865c010dbec2ae0086ef611700437bb06b8021bed825c010cfec3ac0086df6156004377b08b0021bdd8358010df6c12c00867f61d400435fb0ca0021b7d8550010ddec2280086f760d400437db04a0021ff29944010ff8cba20087fc65910043fe12c88021ff17644010ff933220087fc65110043fe2c8880217f69944010efb3ba20087bd999100437eb0888021fb64444010ff8b8220087fc58110043fe28088021dfa7761a00bf else 0xa0fef65080507f7ac840283fdd9320141ff6c9100a0eff60080506ffd32bb4237fc905da11bfe484cd08dffa65648477f930b24237fc9059211dfebb10108eff998808477fac8404237fc9884570dff44422b85ffa65415837f930a0ac17fc9884560dff44422b06ff61e11583dfac908ac1ffa115c160dfe48b08305ffa65411837fb0f088c1bfd8484460dfecb510a06ff64688502ffb2344281bfe8821940bfec890ca06ffa22665037f90cc0a81bfe8820540dfec3102a06ff21881502ff930b0a81bfe8858540dff440c2a05ff64061503f792ca0a81fbc8650540fdf33282a07ef58541503f7920a0a817fc9884540dff44422a06ff61a115037fd10b0281fbd4158140dff440c0a05ff64460503f7a8230281bfd97a2110dfecb510886ff65288442ffb2f442217fd96a2110bfeca510886ffa2086442ffb2e432217fd9421910bff4caec885ff261764437fd10bb2217fc9899910dff444cc886ff259844437fcccc2221bfc8661110bff4cac8885ff261644437f930b2221bfe8859110ffa4b282887fd21941443feccca0a21ff49050510fdeb2282885ffa65704437fd10b8221dfd715c110bff4cac0886ffa2160442ffb2eb0221bfd8458110f7eb22c0887bf58560443fea82b0221ff97058110dff440c0885ff65c60442ffb2830221bfd8418110ffaa08c0885ffa65404437fd10a02217fd9650110fdea0a80885ffa65760437f92cc2021bfe6661010bff4cac8085ffa6570042ffd32b00217fd9758010dfec22c0087bf59160043ff2e0b00217fe9950010bfecb280085ff65c86802ffb28434017fd9121a00bff4caed005ff261768037fcccc24017fe9959200bfe4c2c9006ff26164803df90cb2401bfd7660600dff33303006ff59181802ffb2e40c017fd9620600dfe43103005ff65081802ffd32b8c017fc985c600dfe4c2e3005ffa6561802ff930b0c01bfc9858600bfecbac3007bf219618037fb08b0c01ff57158600bfecb8c3005ff650618037fb0830c017fd9018600bff4ca83005ff261418037f930a0c017fd9650600fdeb2283007fd205418037fb0f08c01bfd8684600dfec24230077f5c570802ffd32b04017fd9758200f7eb22c1007bf58560803ff2e0b04017fd9650200fdea0a81005ffa6510802ffb2e884017fd9644200bfeca221007fd505108027fb22402ed6fd9020666b7ec8901334ff6448099a7fb23442c93fd90a2164d7f33100b24ff644805927fb21442e3afe6620171bbeca900b8cff642885873fcee402c3afe66201619feca100b0eef9108058777d32c20c3bbd9061061dde4830830cffa65841867fd32c00c39fe7760061ddf2230030cff642885075fb0c43283afe8899941bdf4cac8a0eefa2164507d790cb2283ebe6659141fda48ac8a0ebf9988050777ac8402835fd9720141b7ec)) else (if i < 5 then (if i < 4 then 0x7466accce1991330c65eccba196932cc657cca619353254647cc86190131e463bcc7018d5318c62dcc541899312c622cc3e187530cc611cc20183930345fecbee17d52f6c5e4cbc417712e8c5cfcb9c17192e245bdcb6c16b52d2c59bcb3416612c7c58ecb1a162d2c3c586cb0616052be4575cae015a92b2c560cab815692ac4556caaa154d2a8c54fca9c15352a5c54aca9415212a34544ca86150129f453dca7614e529b4534ca6614c52984529ca5214a1292c523ca42147d28ec51bca32145528a4510ca1c14312854503ca0413e927a44edc9d813a927444e0c9bc1359268c4cac98412ed25cc4b7c96812c925844aec95812a9250449dc93412452434484c90611ed23a446cc8d611a92344467c8cc11912314461c8c2118122f445dc8b8116d22cc451c8a011392264445c87c10d52194430c85610a1213c426c84a108d20fc41dc82e1051209c40cc81010151fec3fbc7f60fe51fbc3f0c7dc0f9d1f2c3e3c7c40f811eec3dbc7b20f4d1e943d0c79a0f2d1e343c4c7840f011dfc3b9c76e0ec51d4c3a0c7340e491c64384c6fa0dd11b9436bc6cc0d791adc354c69c0d211a04339c6680cb91934320c6340c51186c306c6020be117842e8c5c40b6d16a42cdc58e0b0115cc2b3c5640abd155c2aac5520aa1152c2a4c5480a8d15142a0c5400a7d14f429dc5380a6914cc297c52c0a511494290c51e0a351464289c5120a1d142c282c50209fd13dc278c4ee09d913ac274c4e809c9138c26ec4dc09b1135c269c4d009991324262c4c0097912e425ac4b2095912a4253c4a40941127424cc492091d121c240c47e08f511dc238c47008d911ac233c46408c5118422fc45e08b9116422bc44c088d1114221c440085d109c212c422083d106c20bc40807e50f841eec3ce07950f1c1e2c3be07790ee41dbc3b607490e841cec39807290e441c4c38607010dec1bbc37206dd0dac1b4c36606c90d841afc35806ad0d441a7c34c06890d0419bc334065d0cac192c32006390c6418ac312061d0c2c17ec2f205cd0b64165c2be055d0a7c149c28804f109a412dc250048908ec118c224042d08240fdc1ee03c1074c0e4c1be035d068c0cac18802f505bc0b2c15e02a9052c0a0c1360251047c08ac10c020903ec078c0ea01c1035c065c0c2016d02ac050c0960115020403bc06e00c90164027c048007d00d4015c02400350044004c0002ffb2040ac97fe9920164bfec8900b26ff20480592ffd32402e3f7d9520171bfe482e2b0eff5c480586ffd32402c3bfc9061061dff4cb0030eff651801877fb2d44283bfd90a2141bfec8510a0dff241865077fd10432837fd9021941dff444cca0fef24164506ff920b0a83bfc8660141dff33100a0eff58480506ffd3240283bfe8820141efecb900a0fbf658805077fb0c40283bfc8620141fbeca9 else 0xa2a1a027111a99178857829e6a6e2e1a74b97821636089898582381921818d82282082063060820828a1e0060e007801a4078012685901268406462080a30702126e08b801a4049a938236462888e1020820e006022e00a0e0060a407801a407021e0048b002a207801a206881c0240b0018300123068c1e004908b003a305930094323e008961640494164628a06404063059010000000188103938b87822a521e0080818010f060508e2e1e0a7a0189d283018016005801e004201827878b829c7110905040306e208e1e02864471098978b87828c0043c201b8b87829e7e08680101110a80302801000110908e2e1e0250fa0941a30700942a3070212321c00e84106a10b008c2a10700942a107001030010300100908700303009420302123c0200e8012221c02012801c0200a801c0230816802c004921c0049a1c0048e11a161425e2e098645b8b878251a1816e1e09428278b87805a61a180ae1e0169824238b87811e69912c50ae1e0c79c3f14686387805a78685e2e1e0961a178b87825c50ae2e1e0c3199f1428238b87831e712c50ae1e0c79b178b80571e5c5e2e113c7959f8b87824a7e2e1e09310678b87805e61a16e7e2e0149828238b829f8661a0ae2e016e1986b8b821b845a61a6786e2e0e198599e1b8b8386686e2e0e1921f8b87802a5600fc510e7e2e19f8b869f802a5191785e2e1e098685a178b878261a6785e2e1e09865178b8782567e1e08c93878232385e2e1e092178b8782485e2e1e0905d178b8782516a745e2e1e09a9f878132485e2e015919e178b82485e2e08d9e178b82467e2e18b938b862e367e2e18b938b878216467e2e1e085978b878216467e2e1e085979387882b825e4e2e01593938b842c2a50ae1e0e226949b8b8782467e2e1e0929f8b87824e2e1e0259098978b8782567e2e1e0938b8782367e2e1e090978b8782425e2e1e0938780b23e2e1e02590578b80964e2e12b8f9f8b842e4855d0a621414264849d090210941ec83ad07020d941ac832d06220b54144824d044207d40e4817d02a203d4044800cffa1fed3fcc7f3cfde1fb53f5c7e6cfca1f8d3efc7dccfb41f5d3ea47d2cf9e1f313e4c7c4cf861f013ddc7b8cf6c1ecd3d747abcf501e993d247a0cf3a1e6d3ccc796cf281e453c7478ccf141e193c1c782cefe1df53bdc778cef01dd53b94770cede1db13b34762cebe1d753ad4758ceae1d553a9c74fce981d213a2c742ce801cf139d4737ce6c1ccd398c72dce581ca13934724ce421c7938e4719ce2e1c49387470ace101c1138046facdec1bc9377c6eccdd01b9d371c6dfcdbc1b7136c46d5cda01b35364c6c6cd861b0135f46bccd701acd35846accd561a9935246a1cd401a7534e4698cd2c1a51348c68fcd1a1a293434684cd041a0133f467bccf619e533b4675cce619c133) else (if i < 6 then 0x8d983110888261088424208c86411a1082390208e24988248c46111082421919018a63089610a080800806230c282224a069c1824a046c20208060819922a36404988a205858c10a09080040428222001b8820822882810806a28e1910903091b090c4620511081410f0a080a3042118908a48a46852564942a8c20f05083c15110840f05082494103806c8c843068a0820189434988240e289086345030a0e023208888848232084150c2830806020100c70f1f801e004100c04001b883c70a04020100050f1c3c14238b87831e76004180804002b1c3c70f080605e2e1e0c7a21582262e1e0c79914442414100c3f8b878022a1a05801060502010067111c58119e2e1e02311981591898582644678605e4e2e1e01923a02818178b87829e71109040386e2e1e0852580160043c2018178b87831e8030c1600616918030291821438706160d8066419e2e1e0478a9867878b811e5e116e2e0c7958b87831e461e2e0c79385838b1e4c3078018507801e006901e007001809a1000c087021e00690123c089141008f8028504878028507801850400a08e1e2e0a79800017022c0848b002a206881a204170222422c00c00564c00c170226005801060201006711198010603020100050f1f8987831e6451ae2e1e0c7199b801a0870c1080609e1e2e0c71c168020403020100050f1f838b866a41ae2e1e0a719982818169f8b87805a88ae0e2e127489b801a0850d06803c187801c106810e2c184442420100f878b8094905a08a19821030f080605e2e1e0a720442420100c18178b8780a600580108060401e2e00f1f842b8b80149e60a4605e1e2e0a79e801828018280108058c1020018c100281010c10604020100050f1f0c1c3070c10605e2e1e0c79818140804031c4470a06c2c1c047051122158026087878015221e5608588083801c3051106803c304238b87831c3c605a08800602010067111b178b843e4e0450b17938f8789803e7a0860a08702108e2e1e0a70f9a018020a05e2e1e0a79a821c08692105060d8026085820e205e1e2e027960a3850e81003c005090681004c00681002c0040e105e2e02796191220ae0e1678c9429918d8580319870a66056423e2e1e0a1998985809c466056261608a64119f8b87808d9a5110a6485e0e2e19c2815918985819a70a080605e2e1e0a7218010a45e2e1e017982b8781329e50aa2a1a00527119d1a0e266e285e0156799918e1780578a61585e0e2679415918d8980559876685e0e267159856178b819e50ae2e18b679429918d89842d9a70ae2e18b6795146b8b87829e6a6e1e04ca79699178b87809e6a64515e2e0a79a9b8b852e9e50a24a34945e2e0e1a02a928d158b8386711a42345e2e0e19e928d178b805660aa4a3e24be19a99178b87809e61645e2e1e0a79a99158b87829e6a6 else 0x8c78b1c1a225c78918160e304228a241080584c2249425181618406e288648e2050400f61083c10a110f0c5844283c40806850c5844208060a1e1a21186052611168028583431908946420150d8a0e6260524032221209c2a160e3c3870e10885648362961514645a4c3850e145640328930e1c386160d8230805082814208058820162a70428148c30a0808201820a640308131c10905883c201b044160508978420805883c150d0444323891a1090306041a10f05240c3c148c311044410511082018216250820182a0043c4421164610c5816200442288311870c185250a04885081588283840c10f05083c15120d04506a1080d150e84316049516245859210f858e10904e00c201b80303e00f0c201a2e0640b818e20f08c00f8010f088b80108068b8010806800e8010f08c08f801a7043e9046305830a8e1832308160e2056403c01017003e304a3098c1700205c00f8c1a8422308052321c014201a850044323c08c1700243a18a15109300481109300323c0438d001438417003c30311882014908702505c0086c242230523082)))
def layer255r9 : Packing := (630,3,5,63,0,15,1,packed255r9)
def keys255k10 (i : Nat) : Nat := (if i < 1 then 0x4dc00043d3c6823c46550000000486ed910002cc4676800000018d74648000d75c079a918000018850362ac5b00003e0157dfe7141c88b815d00000000412962361f035a884a9c86050001664a94f46b510c193644301cd2f0a5478f083fc8e342e8083d850754d14a5b60230000000f20cdb9b6e01f040769e873ab547379f267000022be47c4ed052d99aa2a3450b0a4177411a9cfa8bcc1584a6de900da1c65637c386872917e5ba606165358c03f916216a665b39d1241862e14ab08909be73719000025a51126c9551bd8b6392c00070df0639855d83f05fcbb859c0000000000000000060eedbdf490528a2205df0000e30d6d0000b0bf455f41fcd57574000534000066fc207180083e6525221c830c8636d7a70596800057e400000031b20000c1002dcdeda98d5e58078de0f03b94f880b0cda78fd99c404e0ad2664fa27cb07e212a109b207c7d01e34aa549b269321517aa6a8604f44d4a9119d480b17a18fb974cf7016083aa4f1e4c27fc15625064fb42c2def293c89dc541cf210a006a276f03c05e58026925159f290e443988611669019de8f92398922e272624164f7034a0b83b419965e86c82f520bf4130dab5da1460250a5f11d8de1495d51ba02093e04c996a85558b9e436053b3388a7b8ff40b643a0ba8001144f8f58250199dd2369d034923e033500d95b0485489c90113da05adb748988b239425c59684cc9a1eacae31d1131d20843976380e5868226ba4bd62c11366751732cdb172e44c35c4a4ac07d00cf30f98121460400002543566fa56a3155c4d305873d594006503ed1eb79be61456a213659b24e540241bb28d1f1a2420ef36e9ccb468d208637ac32000205f97dac8d7745e1238b5243f39bcd2a5e0000f6b59ab0002673571c00057e0000c23307f573893f0003575f531195313a07c28d0000b1b7958c414c8b54ab5fae83580aa7f09f414e800063605522516225c7280003944056c29b1fba09c014044a96064bad0b7006c310002539c4acd9c11bb18085c1dd88084000767ddb1627c861011f43df350cc0b8ce5bc000000000010b400034d92034000443000400005fd78c5cf907b00000001ce0983ca29f539c8ed994a03a7061c8b3f000076781d3b24adb30f0f000f0106003d2e6a000b0e001a0000050200130a0102000008000303000d01141505170011090700011c2f052d0303050100000053260606011804450b0003105807070500050005230a1402000005010001091304341f08000073100000020703020107150500001605043d063001050c04200b0e12000d000140000606020801060001220600170111002202020b0008030100011405001d071d4b006700080307007c070d0b0e1a000128290370000a0800000606010000080f07020304bb000106280b03010d32040627110500 else 0x8268586e2a5373cc766b317f0001a2064e24985278c910001a3a457ae6ff85210a0000000a5369ee64b40e4a3b082a912c052d21f4ca68a00f07183a6a657c64d82fc4d1085dd635386915e123519926a4a2284190200032595445635f877c64939e540548d572c572de2b168000b29607102711ae16bf97c131ac2b26da5c364b12580001e36b55e245906092725508f6960a4f36480cfdc9734b5986b933038e470e471d30a77b9340003c0783ac0ccc8ef465b164dea65204b3e48a50f57275847740000000384220909a8a6f866c67909d93980a2eb6ec6220002135d77756c30158ee000057b175b0750003d8793744ff43d5d2572b0000b5a6e23000047710b0000847518ab5f45f3b0c0000450800000006420001cdfe2c4d1605bc000000113b89b765e115d45b7287951b68ac44d34c000365a445013dd1ae864568c66022453e1908154c1eb030a66eb87a5fed7d6cc865fba3264dae68e8dc609d02781ae24c00057500e2d3a0e166463cbee33ece90001c54e25bc8ac860c5cd6194693949c9700019c20419e6625cc0000000000369881130b40000000c5d41ec835810656b000000037700000002e4772bd41300000006)
def packed255r10 (i : Nat) : Nat := (if i < 1 then 0x3a11082da07180cdff57ea5f727cd1eef7ae1e8178f1ddb763dd587431cab7199c1a6f1db826cbdaea6a5da6768dda0067419a065c1940645d8e062a587961098195f517965d617285be16c85a6164c58395de568157054e54f452d948650e93fc4f4d3aa4dcd34a4c4d2e34a95275491520e47791a045dd14744250d942a507941250123f88fb23dd0f3d3c18ec83a7ce6138e0df33728da1358cd3333f0cbe3238c423048bdb2eacb6d2cbcaf82b20a8a294ca2327b09bc25dc94724788e722a488021408191f887b21dd074b1c6c6dd1ab467d191860f176059a155451e139c4a911c84340fbc3c60e3c3510ca02f80b2029109a0238083c1d8068416a050411103a00bf0258074012c0290003ff20564ffc80593ff20171ffd71587ff20161ffe88507ff61941ffc86507ff99941ffd61507ff60141ffc80507ff5da11ffe66847ff59211ffc815c3ff58570ffe115c3ff20560ffd71583ff50560ffe11583ff5c160ffd41183ff84460ffe88503ff61940ffc86503ff99940ffd81503ff20540ffd61503ff18540ffe11503ff58140ffc60503ffa2110ffd87443ff61910ffc86443ff5d910ffe66443ff61110ffd64443ff5c510ffd61443ff50510ffd70443ff58110ffc60443ff50110ffd76043ff99810ffd64043ff5c010ffd60043ff50010ffc86803ff5da00ffe66803ff59200ffc81803ff5c600ffd61803ff18600ffd41803ff84600ffd70803ff58200ffd40803ff44200bfe885daff20176efc8199bbf20266dfe7799bbf5da66bfc8099affa2164efe66592ff20164fbe66912ffa2171efe665c6ff20171bfe88586ff61d61dfe77587bf99961fbe44587fd5c561bfc80586ff61c61dfe77186ff61061fbe44186ff60061bfe88506ff61941efe66507ef59141bfc80507fd21a11ff576847fd99a11ff564847fd20211dfe77847bf99a11fbe44847fd5c611ff561847fd50611bfc80846ffa2170efe665c37f5c570ff6115c2ffa2160bfd875837f9dd60efe66583bf59160fbe44583bf58560ff611583fe5c160bfd871837f9dc60bfd84183ef91060bfd81183fd84460efd60182ffa2140bfd86503bf99940fbd41503fd84540bfe88442ff61d10dfe77442ff61910efe66442ff61110fbe44443fd50510ff611442ff61c10dfe77042ff61810efe66042ff61010fbe44043fd44010ff987803fe61a00ff886803fe5da00ffa66803fe61200ff964803fe60600ff881803fe5c600ff961803fe18600ff941803fe84600bfd878037f9de00bfd86803bf99a00bfd84803ef91200bfd81803fd84600ff970803fe58200ff860803fe50200ff910803fe04200cfe7799baf99a44bbd841877d9de11ef666847ed91211ef9601827f61c10afd86042df61410bbd84042f760c10bed82043fc44010dfa77803be99a00fba44803fc84600 else (if i < 2 then 0xe04a2a735193051e2b0e2c09ea323c2c4490d1880c2b0e0c5699890c526c587025a4b464c3c28ac38b027aa32688921a3158b0e04b5c64d152e2c380527a62a588921a30d8b061155c64d152e2c380527a632688921a30b8b0e015588c18b0c73730a8f8b0e0373062c97062c26a72c1b062c26a64f8b0e08c6a64f83161106e6145b062c26a6c5870088f2868b8b0e0111e78c23161c02a3cf1f161c098b4c3e2e2c3823999f161c11ccca644058b8b0e0151e91e1a296c18b09aa078a8b87062109e88a9f061c46a60c5b0e0c46a68b813e1c45a6c5870273466612182c5119f161c02aa1414362c3804a7a2362c3813c5985110c17161c09e88d8b0e04f1660d9cc85c58704e284068a3f0e2c11e91e2a2e1c188447a0406c38b047983114c162a8c38b007a84058b8b0e08e2a80b871604d285c18b0a7962a4478b0e04d385c5870279532446170e2c13c6c5870278b3084d121e2c3822d11b161c09e2cc982e1c5813cc911860b870629d305c38b027984880b9f0e2c02a8c587047332c5c5870473330a4a17161c01ccd1182e2c3823cc18b60c584d4c17062c2213cd153e0c584d4c1a29ac5830969c560c5844279a2e04f8b096985250a5b062c26a88c16243c5830ce1b161c09cd199c28a0d8b0e0129e8c5870278d2852228362c3813d18b0e04f1a50a1850fce67161c1485c58704694ce2c18454a20305238b0e08f405c5830888f3080d17161c11e71415291c587007a2305c5870479850910187c5cf8b0e0aa2e2c38139998d468b8b0a7c13c535831612d3088b12199c587050203451f8b0e04f4168d171614f827143f0e2c09e68d1218a0b8b0e0a0505c5870273339ac5870278b30a0a6b161c05a7321b161c1166101888a0b8b0e04f496c5870278b364c58700a95325c587027153a64a8d261c1885502b161c09a51497062c29e64a911e2c38134e992e2c3805279c525c58702799325488f161c02a8158b0e04b28a4d871604f30a4c95223c38315029362c3812cc29361c5813cc99223c5870259c28ac5870273339a8d17161c09e70a10516c18711aa0c888a9b263c587052182e2c3805279cb468b8b0e04f3864a3f0e7c580551192e4c78b0e09cd0a4c97161c09e832292a4469b160c348ac587026945264b8b0e04f38a4c911a5c5870502b161c0965351b161c09e62c9b161c11e63390305c58704f17161c09e54d173e2c38268b8b0e04f299101b3e2c1867158c299c58704e28405cf8b0e09c567c38064a2b205c58704c542e7c5825159f161172e7c58700597161c09e44d9f161c12e2c3813c8973e2c3825af9abb6ae36b48ac46ad3aa72a6ca8f29fea73a997a59e91ba3ae8bba1f683fa0227ca9e4e7479c0a6cb9a36656987e5f696fe588956251a938e4a5919e4378fe63c28e2e3468c062a789de23287b619385 else 0x1b161c0212c79d2e2c3804479b161c11ccca68c86c3831270a3e90c14b60c388d4e58785c5870472340f2d870628e4670b871608e9a6c38b0474c5a60c170c7c580b0fa1362c38239198b260b871608f39bc18b0a78b30888921a3c5870268b506c5870278b362c3823a53330a0b830e28e68cd02a326c5870474b4062d831614a6a71417027c584c9aa0505c09f1612d38a88921a30d8b0614b5068a97160c29cd19a450fc38b0278d38a488f161c1192d058562c3823919d325c5830c7233e2c381347962e28f870262d3a64b8b0e08e4672d8b0e08e9661e282e08f8b096a08a6c5870474b38a8c9b161c11d2d01a2a5c5830c72d445c5870474d30ac98c2e1c5807d065361c49f00f9d364c7871601f3991e17263c587026a45051e6c462c3813d26450588921a3118b0e04d626c3893e01f30a0c14788c587027a45464c170e2c09c7d228444490d185c21b1601f60a8c9b085c58138fa4d464c17161c09e83311243463c4060b8b0e0b0c8f15121e2c3813525a3260b8b0e04f40a1380462c29e2d0284244667161c09a2d428462c3813c59cd094d8b0e04f1683229223118b0618b4964d8b0e04f167c98f161c09854f15288362b062c29e933152c4490d18a118b0e04d6ca8a94406158b0e04f564c78b0))
def layer255r10 : Packing := (201,2,5,63,0,14,1,packed255r10)
def keys255k11 (i : Nat) : Nat := 0x1a94655c2e6ec2c85282e2d50b06cfe8e130200067d6d7f8aa23b894a7cf18df96000068fb3da594992da000583d7aaa3647ec231d1156a98070f554915b669e04d2d88b448813b7f32bd588ac02094e4d95362cb90a0005408f6000c4acbc000401b33312eb3b2104301dcf2916cb417961a94ce026d16ae89d76ec918fda3967743c814a4492434b2c4a4ec6d98e15687e0017640cfa0e000cd3c7371a8cd2792ba8b1338619aa42bf81e2171426fa8578b9809726e74a2600189ea34466d0f2a155e464a62f3400175c070f6ac6e26a64071023fa5200071893a0000000000318248b6386001f8028dcef21062cb01e37e869706ea89ba5f45c4e857548451eb692c002b683b52705372661cc605a562b8400028000030c4e7af9093a7be96001888001028b8df6c20dedc8e593e95437c308c0be3a001c5124c0010ab632f464d5576000000530000390001f67122b44001d2e000140040268c8202040010e1c2801614008120870682180020af438d077009100a9801040812026007040010005065000000000b038741800408001
def packed255r11 (i : Nat) : Nat := 0x15b2208a11e71599e28601a71462228601e71856618a01e71852278608a76671a28601671858628079869e28601661856628601e71462278a086764a9e28601a71858a18079861678a18262a78a180598614a9e28609e28601e41a78a18258a18079059e28609678a1824c92f4b129499234829e06c180541263f0d2288841804207800ffaedff99bfeb27fd71ffac3ff187fea0ffe11ffae1ff583fe307fd40ffa21ff043ff005fe77dfccdef913fb08ffa00
def layer255r11 : Packing := (20,1,5,63,0,10,1,packed255r11)
def keys255k12 (i : Nat) : Nat := 0xf421b160000001c9b30018b920063f0c0000f6000011100000000000000000000003c20080000010f00003546ea800000ad694140020
def packed255r12 (i : Nat) : Nat := 0xe20824ff
def layer255r12 : Packing := (1,0,5,63,0,0,1,packed255r12)
def samples255 : Array (Bits × Bits) := #[(0x1001800044dc002001e780060000784003d29a6e001cfff3ffc00fffff,0x1001a100404c0028402280068800085101400826880011104451044511),(0x24600000b2730c0069984080019a1800ced6593ffeb400d003ff003ff,0x2461220010130c4928904085098a18a2484208051a94a45290a5290a6),(0xffffffa49800198c38c300071e58b00061c6000f31861c0073800e003ffffc00,0xffffffa49844598c30c311251458b1226146244a3186192452a48a9224a92a48),(0xffffffc0e0001e0fc0fc0007e060c0007e07fff03e07e0007c000fffc0000000,0xffffffc0e0507e0f80fc1437c060c142aa02a8703e07c1457c28cfa3a8ca328c),(0x700001ff000fffff8007f00007ff800003ff800007ffff00000000000,0x700066a90005541b8007f0032fff006603ff000357fc6e01b06c1b06c),(0xfffffff800001fffff000000007fffff800000003fffffff8000000000000000,0xfffffff800605ffefe0018200069d383000030403bdf7f86003080c2308c2308),(0xffffffffffffe00000000000007fffffffffffffc00000000000000000000000,0x70a878000000001c000162c3c55fd478fc00000380007001c0701c070),(0xffffffffffffffffffffffffff80000000000000000000000000000000000000,0xfffffff8f578156fffaabe07ff8001c000003800000001c0003800e0380e0380),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.fork 14 (.fork 7 (.fork 3 (.leaf [(4,0,251,0,11),(8,0,247,0,11),(32,0,223,0,11)]) (.leaf [(16,0,239,0,10),(128,0,127,0,10),(2,0,253,0,9),(64,0,191,0,9)])) (.fork 3 (.leaf [(144,0,111,0,9),(0,64,23,168,8),(0,128,47,80,8)]) (.leaf [(1,0,254,0,8),(6,0,249,0,8),(34,0,221,0,8),(48,0,207,0,8)]))) (.fork 7 (.fork 3 (.leaf [(160,0,95,0,8),(0,2,216,37,7),(0,4,248,3,7)]) (.leaf [(0,16,110,129,7),(0,32,157,66,7),(5,0,250,0,7),(8,64,23,160,7)])) (.fork 3 (.leaf [(9,0,246,0,7),(16,64,7,168,7),(16,128,47,64,7)]) (.leaf [(32,64,23,136,7),(64,128,47,16,7),(128,64,23,40,7),(192,0,63,0,7)]))))
def levels255 : Nat → Packing
  | 7 => layer255r7
  | 8 => layer255r8
  | 9 => layer255r9
  | 10 => layer255r10
  | 11 => layer255r11
  | 12 => layer255r12
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 17 62 6 10 6 0 keys255k8
  | 9 => lookupWord 115 391 8 13 9 0 keys255k9
  | 10 => lookupWord 209 717 8 14 10 0 keys255k10
  | 11 => lookupWord 67 228 7 12 8 0 keys255k11
  | 12 => lookupWord 6 46 3 9 5 0 keys255k12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom7 : graphValid g7 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice7k3p0 : block g7 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK7k3 : block g7 3 0 1=true := slice7k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked7 : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0=true)
  · exact (rfl : block g7 1 0 0=true)
  · exact (rfl : block g7 2 0 0=true)
  · exact layerOK7k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 4 :=
  lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) geom7 checked7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps7 : List (Nat × List Nat) := [(7,[])]
def known7 := extendKnown [] 4 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok baseKnown low7 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom43 : graphValid g43 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice43k3p0 : block g43 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK43k3 : block g43 3 0 1=true := slice43k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked43 : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0=true)
  · exact (rfl : block g43 1 0 0=true)
  · exact (rfl : block g43 2 0 0=true)
  · exact layerOK43k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43 : Lower (vars 43) (graphGoal 43) 4 :=
  lower_forest (g:=g43) (i:=0) (hints:=1048577) (before_sound known7 valid7) geom43 checked43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps43 : List (Nat × List Nat) := [(43,[]),(51,[67]),(75,[101,49]),(77,[101,49,33]),(99,[81,97,65,16,48]),(102,[81,97,65,49,16,32]),(105,[97,65,33,48]),(106,[16,96,81,64,49,32]),(147,[117,101,65,49]),(149,[117,101,65,49,33]),(153,[117,101,65,33]),(209,[81,117,16,96,65,33,48]),(216,[113,81,96,65,32]),(226,[80,112,97,64,49,32]),(240,[16,49,115,96,65,32])]
def known43 := extendKnown known7 4 maps43
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43 : Known known43 := extendKnown_ok valid7 low43 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known43) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice15k4p0 : block g15 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK15k4 : block g15 4 0 1=true := slice15k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked15 : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact (rfl : block g15 3 0 0=true)
  · exact layerOK15k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 5 :=
  lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound known43 valid43) geom15 checked15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[67]),(39,[83,67,16])]
def known15 := extendKnown known43 5 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid43 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom199 : graphValid g199 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice199k5p0 : block g199 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK199k5 : block g199 5 0 1=true := slice199k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked199 : checkedTables g199 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g199 0 0 0=true)
  · exact (rfl : block g199 1 0 0=true)
  · exact (rfl : block g199 2 0 0=true)
  · exact (rfl : block g199 3 0 0=true)
  · exact (rfl : block g199 4 0 0=true)
  · exact layerOK199k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low199 : Lower (vars 199) (graphGoal 199) 6 :=
  lower_forest (g:=g199) (i:=0) (hints:=1728053249) (before_sound known15 valid15) geom199 checked199 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps199 : List (Nat × List Nat) := [(199,[])]
def known199 := extendKnown known15 6 maps199
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid199 : Known known199 := extendKnown_ok valid15 low199 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom109 : graphValid g109 (boundsBefore known199) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice109k4p0 : block g109 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK109k4 : block g109 4 0 1=true := slice109k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked109 : checkedTables g109 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0=true)
  · exact (rfl : block g109 1 0 0=true)
  · exact (rfl : block g109 2 0 0=true)
  · exact (rfl : block g109 3 0 0=true)
  · exact layerOK109k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low109 : Lower (vars 109) (graphGoal 109) 5 :=
  lower_forest (g:=g109) (i:=0) (hints:=56623106) (before_sound known199 valid199) geom109 checked109 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps109 : List (Nat × List Nat) := [(109,[]),(110,[83,16]),(115,[101,66,33,49]),(121,[66]),(179,[117,82,98,66,33,16,48]),(203,[117,33]),(205,[117]),(211,[101,117,67,33]),(213,[101,117,67]),(227,[83,115,67,16,32]),(230,[83,115,67,16]),(241,[115,64,32]),(242,[99,80,115,64,32,16])]
def known109 := extendKnown known199 5 maps109
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid109 : Known known109 := extendKnown_ok valid199 low109 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom59 : graphValid g59 (boundsBefore known109) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice59k4p0 : block g59 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK59k4 : block g59 4 0 1=true := slice59k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked59 : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0=true)
  · exact (rfl : block g59 1 0 0=true)
  · exact (rfl : block g59 2 0 0=true)
  · exact (rfl : block g59 3 0 0=true)
  · exact layerOK59k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low59 : Lower (vars 59) (graphGoal 59) 5 :=
  lower_forest (g:=g59) (i:=0) (hints:=1048577) (before_sound known109 valid109) geom59 checked59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps59 : List (Nat × List Nat) := [(59,[]),(91,[101,49]),(155,[117,101,65,49]),(157,[117,101,65,49,33]),(233,[48,116,49,97,33,80]),(234,[116,96,81,32]),(248,[16,84,112,97,32])]
def known59 := extendKnown known109 5 maps59
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid59 : Known known59 := extendKnown_ok valid109 low59 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom107 : graphValid g107 (boundsBefore known59) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice107k5p0 : block g107 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice107k5p5 : block g107 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK107k5 : block g107 5 0 15=true := (@block_merge g107 5 0 5 10 slice107k5p0 slice107k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice107k6p0 : block g107 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK107k6 : block g107 6 0 1=true := slice107k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked107 : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0=true)
  · exact (rfl : block g107 1 0 0=true)
  · exact (rfl : block g107 2 0 0=true)
  · exact (rfl : block g107 3 0 0=true)
  · exact (rfl : block g107 4 0 0=true)
  · exact layerOK107k5
  · exact layerOK107k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low107 : Lower (vars 107) (graphGoal 107) 7 :=
  lower_forest (g:=g107) (i:=0) (hints:=51380225) (before_sound known59 valid59) geom107 checked107 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps107 : List (Nat × List Nat) := [(107,[]),(217,[101,117,49,65,33])]
def known107 := extendKnown known59 7 maps107
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid107 : Known known107 := extendKnown_ok valid59 low107 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom79 : graphValid g79 (boundsBefore known107) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice79k5p0 : block g79 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice79k5p3 : block g79 5 3 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK79k5 : block g79 5 0 7=true := (@block_merge g79 5 0 3 4 slice79k5p0 slice79k5p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice79k6p0 : block g79 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK79k6 : block g79 6 0 1=true := slice79k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked79 : checkedTables g79 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0=true)
  · exact (rfl : block g79 1 0 0=true)
  · exact (rfl : block g79 2 0 0=true)
  · exact (rfl : block g79 3 0 0=true)
  · exact (rfl : block g79 4 0 0=true)
  · exact layerOK79k5
  · exact layerOK79k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low79 : Lower (vars 79) (graphGoal 79) 7 :=
  lower_forest (g:=g79) (i:=0) (hints:=50331649) (before_sound known107 valid107) geom79 checked79 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps79 : List (Nat × List Nat) := [(79,[]),(103,[83,67,16]),(151,[118,67])]
def known79 := extendKnown known107 7 maps79
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid79 : Known known79 := extendKnown_ok valid107 low79 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom47 : graphValid g47 (boundsBefore known79) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice47k5p0 : block g47 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK47k5 : block g47 5 0 1=true := slice47k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked47 : checkedTables g47 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0=true)
  · exact (rfl : block g47 1 0 0=true)
  · exact (rfl : block g47 2 0 0=true)
  · exact (rfl : block g47 3 0 0=true)
  · exact (rfl : block g47 4 0 0=true)
  · exact layerOK47k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 6 :=
  lower_forest (g:=g47) (i:=0) (hints:=1048577) (before_sound known79 valid79) geom47 checked47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(55,[67])]
def known47 := extendKnown known79 6 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid79 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known47) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice31k5p0 : block g31 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK31k5 : block g31 5 0 1=true := slice31k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked31 : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact layerOK31k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 6 :=
  lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound known47 valid47) geom31 checked31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[])]
def known31 := extendKnown known47 6 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid47 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom222 : graphValid g222 (boundsBefore known31) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice222k5p0 : block g222 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK222k5 : block g222 5 0 1=true := slice222k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked222 : checkedTables g222 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0=true)
  · exact (rfl : block g222 1 0 0=true)
  · exact (rfl : block g222 2 0 0=true)
  · exact (rfl : block g222 3 0 0=true)
  · exact (rfl : block g222 4 0 0=true)
  · exact layerOK222k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low222 : Lower (vars 222) (graphGoal 222) 6 :=
  lower_forest (g:=g222) (i:=0) (hints:=1124557088) (before_sound known31 valid31) geom222 checked222 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps222 : List (Nat × List Nat) := [(222,[])]
def known222 := extendKnown known31 6 maps222
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid222 : Known known222 := extendKnown_ok valid31 low222 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom245 : graphValid g245 (boundsBefore known222) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice245k6p0 : block g245 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK245k6 : block g245 6 0 1=true := slice245k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked245 : checkedTables g245 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0=true)
  · exact (rfl : block g245 1 0 0=true)
  · exact (rfl : block g245 2 0 0=true)
  · exact (rfl : block g245 3 0 0=true)
  · exact (rfl : block g245 4 0 0=true)
  · exact (rfl : block g245 5 0 0=true)
  · exact layerOK245k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low245 : Lower (vars 245) (graphGoal 245) 7 :=
  lower_forest (g:=g245) (i:=0) (hints:=1163919362) (before_sound known222 valid222) geom245 checked245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps245 : List (Nat × List Nat) := [(245,[]),(246,[118,84,16])]
def known245 := extendKnown known222 7 maps245
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid245 : Known known245 := extendKnown_ok valid222 low245 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom187 : graphValid g187 (boundsBefore known245) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice187k6p0 : block g187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK187k6 : block g187 6 0 1=true := slice187k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked187 : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0=true)
  · exact (rfl : block g187 1 0 0=true)
  · exact (rfl : block g187 2 0 0=true)
  · exact (rfl : block g187 3 0 0=true)
  · exact (rfl : block g187 4 0 0=true)
  · exact (rfl : block g187 5 0 0=true)
  · exact layerOK187k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low187 : Lower (vars 187) (graphGoal 187) 7 :=
  lower_forest (g:=g187) (i:=0) (hints:=1074790401) (before_sound known245 valid245) geom187 checked187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps187 : List (Nat × List Nat) := [(187,[]),(250,[116,96,81,32])]
def known187 := extendKnown known245 7 maps187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid187 : Known known187 := extendKnown_ok valid245 low187 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom243 : graphValid g243 (boundsBefore known187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice243k6p0 : block g243 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice243k6p6 : block g243 6 6 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK243k6 : block g243 6 0 15=true := (@block_merge g243 6 0 6 9 slice243k6p0 slice243k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice243k7p0 : block g243 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK243k7 : block g243 7 0 1=true := slice243k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked243 : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0=true)
  · exact (rfl : block g243 1 0 0=true)
  · exact (rfl : block g243 2 0 0=true)
  · exact (rfl : block g243 3 0 0=true)
  · exact (rfl : block g243 4 0 0=true)
  · exact (rfl : block g243 5 0 0=true)
  · exact layerOK243k6
  · exact layerOK243k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low243 : Lower (vars 243) (graphGoal 243) 8 :=
  lower_forest (g:=g243) (i:=0) (hints:=1158676481) (before_sound known187 valid187) geom243 checked243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps243 : List (Nat × List Nat) := [(243,[])]
def known243 := extendKnown known187 8 maps243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid243 : Known known243 := extendKnown_ok valid187 low243 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom207 : graphValid g207 (boundsBefore known243) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice207k7p0 : block g207 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK207k7 : block g207 7 0 1=true := slice207k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked207 : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0=true)
  · exact (rfl : block g207 1 0 0=true)
  · exact (rfl : block g207 2 0 0=true)
  · exact (rfl : block g207 3 0 0=true)
  · exact (rfl : block g207 4 0 0=true)
  · exact (rfl : block g207 5 0 0=true)
  · exact (rfl : block g207 6 0 0=true)
  · exact layerOK207k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low207 : Lower (vars 207) (graphGoal 207) 8 :=
  lower_forest (g:=g207) (i:=0) (hints:=1660944385) (before_sound known243 valid243) geom207 checked207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps207 : List (Nat × List Nat) := [(207,[]),(215,[118,67]),(231,[83,67,16])]
def known207 := extendKnown known243 8 maps207
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid207 : Known known207 := extendKnown_ok valid243 low207 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom119 : graphValid g119 (boundsBefore known207) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice119k7p0 : block g119 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK119k7 : block g119 7 0 1=true := slice119k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked119 : checkedTables g119 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0=true)
  · exact (rfl : block g119 1 0 0=true)
  · exact (rfl : block g119 2 0 0=true)
  · exact (rfl : block g119 3 0 0=true)
  · exact (rfl : block g119 4 0 0=true)
  · exact (rfl : block g119 5 0 0=true)
  · exact (rfl : block g119 6 0 0=true)
  · exact layerOK119k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 8 :=
  lower_forest (g:=g119) (i:=0) (hints:=84934657) (before_sound known207 valid207) geom119 checked119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(183,[118,84,16])]
def known119 := extendKnown known207 8 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid207 low119 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom95 : graphValid g95 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice95k7p0 : block g95 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK95k7 : block g95 7 0 1=true := slice95k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked95 : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0=true)
  · exact (rfl : block g95 1 0 0=true)
  · exact (rfl : block g95 2 0 0=true)
  · exact (rfl : block g95 3 0 0=true)
  · exact (rfl : block g95 4 0 0=true)
  · exact (rfl : block g95 5 0 0=true)
  · exact (rfl : block g95 6 0 0=true)
  · exact layerOK95k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low95 : Lower (vars 95) (graphGoal 95) 8 :=
  lower_forest (g:=g95) (i:=0) (hints:=50331649) (before_sound known119 valid119) geom95 checked95 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps95 : List (Nat × List Nat) := [(95,[]),(159,[118,67])]
def known95 := extendKnown known119 8 maps95
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid95 : Known known95 := extendKnown_ok valid119 low95 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom63 : graphValid g63 (boundsBefore known95) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice63k6p0 : block g63 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK63k6 : block g63 6 0 1=true := slice63k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked63 : checkedTables g63 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0=true)
  · exact (rfl : block g63 1 0 0=true)
  · exact (rfl : block g63 2 0 0=true)
  · exact (rfl : block g63 3 0 0=true)
  · exact (rfl : block g63 4 0 0=true)
  · exact (rfl : block g63 5 0 0=true)
  · exact layerOK63k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 7 :=
  lower_forest (g:=g63) (i:=0) (hints:=1048577) (before_sound known95 valid95) geom63 checked63 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[])]
def known63 := extendKnown known95 7 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid95 low63 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom123 : graphValid g123 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice123k7p0 : block g123 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK123k7 : block g123 7 0 1=true := slice123k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked123 : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0=true)
  · exact (rfl : block g123 1 0 0=true)
  · exact (rfl : block g123 2 0 0=true)
  · exact (rfl : block g123 3 0 0=true)
  · exact (rfl : block g123 4 0 0=true)
  · exact (rfl : block g123 5 0 0=true)
  · exact (rfl : block g123 6 0 0=true)
  · exact layerOK123k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low123 : Lower (vars 123) (graphGoal 123) 8 :=
  lower_forest (g:=g123) (i:=0) (hints:=51380225) (before_sound known63 valid63) geom123 checked123 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps123 : List (Nat × List Nat) := [(123,[]),(219,[101,117,49,65]),(221,[101,117,49,65,33]),(235,[48,116,49,97,80]),(249,[64,100,49,113,33,80])]
def known123 := extendKnown known63 8 maps123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid123 : Known known123 := extendKnown_ok valid63 low123 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known123) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k5p0 : block g111 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k5 : block g111 5 0 1=true := slice111k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k6p0 : block g111 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k6p6 : block g111 6 6 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k6 : block g111 6 0 7=true := (@block_merge g111 6 0 6 1 slice111k6p0 slice111k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k7p0 : block g111 7 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k7p3 : block g111 7 3 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k7 : block g111 7 0 7=true := (@block_merge g111 7 0 3 4 slice111k7p0 slice111k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k8p0 : block g111 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k8 : block g111 8 0 1=true := slice111k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked111 : checkedTables g111 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact layerOK111k5
  · exact layerOK111k6
  · exact layerOK111k7
  · exact layerOK111k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 9 :=
  lower_forest (g:=g111) (i:=0) (hints:=51380225) (before_sound known123 valid123) geom111 checked111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(111,[])]
def known111 := extendKnown known123 9 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid123 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom254 : graphValid g254 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice254k7p0 : block g254 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK254k7 : block g254 7 0 1=true := slice254k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked254 : checkedTables g254 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0=true)
  · exact (rfl : block g254 1 0 0=true)
  · exact (rfl : block g254 2 0 0=true)
  · exact (rfl : block g254 3 0 0=true)
  · exact (rfl : block g254 4 0 0=true)
  · exact (rfl : block g254 5 0 0=true)
  · exact (rfl : block g254 6 0 0=true)
  · exact layerOK254k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low254 : Lower (vars 254) (graphGoal 254) 8 :=
  lower_forest (g:=g254) (i:=0) (hints:=1125605664) (before_sound known111 valid111) geom254 checked254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps254 : List (Nat × List Nat) := [(254,[])]
def known254 := extendKnown known111 8 maps254
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid254 : Known known254 := extendKnown_ok valid111 low254 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known254) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice191k8p0 : block g191 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK191k8 : block g191 8 0 1=true := slice191k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked191 : checkedTables g191 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact (rfl : block g191 6 0 0=true)
  · exact (rfl : block g191 7 0 0=true)
  · exact layerOK191k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 9 :=
  lower_forest (g:=g191) (i:=0) (hints:=1074790401) (before_sound known254 valid254) geom191 checked191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[])]
def known191 := extendKnown known254 9 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid254 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom253 : graphValid g253 (boundsBefore known191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice253k8p0 : block g253 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK253k8 : block g253 8 0 1=true := slice253k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked253 : checkedTables g253 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0=true)
  · exact (rfl : block g253 1 0 0=true)
  · exact (rfl : block g253 2 0 0=true)
  · exact (rfl : block g253 3 0 0=true)
  · exact (rfl : block g253 4 0 0=true)
  · exact (rfl : block g253 5 0 0=true)
  · exact (rfl : block g253 6 0 0=true)
  · exact (rfl : block g253 7 0 0=true)
  · exact layerOK253k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low253 : Lower (vars 253) (graphGoal 253) 9 :=
  lower_forest (g:=g253) (i:=0) (hints:=1130364930) (before_sound known191 valid191) geom253 checked253 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps253 : List (Nat × List Nat) := [(253,[])]
def known253 := extendKnown known191 9 maps253
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid253 : Known known253 := extendKnown_ok valid191 low253 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom247 : graphValid g247 (boundsBefore known253) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k6p0 : block g247 6 0 8 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k6p8 : block g247 6 8 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k6 : block g247 6 0 9=true := (@block_merge g247 6 0 8 1 slice247k6p0 slice247k6p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p0 : block g247 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p1 : block g247 7 1 53 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p54 : block g247 7 54 21 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k7 : block g247 7 0 75=true := (@block_merge g247 7 0 54 21 (@block_merge g247 7 0 1 53 slice247k7p0 slice247k7p1) slice247k7p54)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p0 : block g247 8 0 25 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p25 : block g247 8 25 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p89 : block g247 8 89 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p153 : block g247 8 153 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p162 : block g247 8 162 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p226 : block g247 8 226 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k8 : block g247 8 0 230=true := (@block_merge g247 8 0 226 4 (@block_merge g247 8 0 162 64 (@block_merge g247 8 0 153 9 (@block_merge g247 8 0 89 64 (@block_merge g247 8 0 25 64 slice247k8p0 slice247k8p25) slice247k8p89) slice247k8p153) slice247k8p162) slice247k8p226)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k9p0 : block g247 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k9p7 : block g247 9 7 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k9 : block g247 9 0 29=true := (@block_merge g247 9 0 7 22 slice247k9p0 slice247k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k10p0 : block g247 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k10 : block g247 10 0 1=true := slice247k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked247 : checkedTables g247 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0=true)
  · exact (rfl : block g247 1 0 0=true)
  · exact (rfl : block g247 2 0 0=true)
  · exact (rfl : block g247 3 0 0=true)
  · exact (rfl : block g247 4 0 0=true)
  · exact (rfl : block g247 5 0 0=true)
  · exact layerOK247k6
  · exact layerOK247k7
  · exact layerOK247k8
  · exact layerOK247k9
  · exact layerOK247k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low247 : Lower (vars 247) (graphGoal 247) 11 :=
  lower_forest (g:=g247) (i:=0) (hints:=1158676481) (before_sound known253 valid253) geom247 checked247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps247 : List (Nat × List Nat) := [(247,[])]
def known247 := extendKnown known253 11 maps247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid247 : Known known247 := extendKnown_ok valid253 low247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom223 : graphValid g223 (boundsBefore known247) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k6p0 : block g223 6 0 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k6p4 : block g223 6 4 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k6 : block g223 6 0 12=true := (@block_merge g223 6 0 4 8 slice223k6p0 slice223k6p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k7p0 : block g223 7 0 34 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k7p34 : block g223 7 34 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k7 : block g223 7 0 56=true := (@block_merge g223 7 0 34 22 slice223k7p0 slice223k7p34)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p0 : block g223 8 0 18 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p18 : block g223 8 18 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p82 : block g223 8 82 44 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p126 : block g223 8 126 37 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k8 : block g223 8 0 163=true := (@block_merge g223 8 0 126 37 (@block_merge g223 8 0 82 44 (@block_merge g223 8 0 18 64 slice223k8p0 slice223k8p18) slice223k8p82) slice223k8p126)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k9p0 : block g223 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k9p7 : block g223 9 7 19 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k9 : block g223 9 0 26=true := (@block_merge g223 9 0 7 19 slice223k9p0 slice223k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k10p0 : block g223 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k10 : block g223 10 0 1=true := slice223k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked223 : checkedTables g223 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0=true)
  · exact (rfl : block g223 1 0 0=true)
  · exact (rfl : block g223 2 0 0=true)
  · exact (rfl : block g223 3 0 0=true)
  · exact (rfl : block g223 4 0 0=true)
  · exact (rfl : block g223 5 0 0=true)
  · exact layerOK223k6
  · exact layerOK223k7
  · exact layerOK223k8
  · exact layerOK223k9
  · exact layerOK223k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low223 : Lower (vars 223) (graphGoal 223) 11 :=
  lower_forest (g:=g223) (i:=0) (hints:=1124073473) (before_sound known247 valid247) geom223 checked223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps223 : List (Nat × List Nat) := [(223,[])]
def known223 := extendKnown known247 11 maps223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid223 : Known known223 := extendKnown_ok valid247 low223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom251 : graphValid g251 (boundsBefore known223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k6p0 : block g251 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k6p1 : block g251 6 1 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k6 : block g251 6 0 2=true := (@block_merge g251 6 0 1 1 slice251k6p0 slice251k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k7p0 : block g251 7 0 43 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k7p43 : block g251 7 43 44 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k7 : block g251 7 0 87=true := (@block_merge g251 7 0 43 44 slice251k7p0 slice251k7p43)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p0 : block g251 8 0 20 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p20 : block g251 8 20 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p84 : block g251 8 84 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p148 : block g251 8 148 60 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p208 : block g251 8 208 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k8p272 : block g251 8 272 39 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k8 : block g251 8 0 311=true := (@block_merge g251 8 0 272 39 (@block_merge g251 8 0 208 64 (@block_merge g251 8 0 148 60 (@block_merge g251 8 0 84 64 (@block_merge g251 8 0 20 64 slice251k8p0 slice251k8p20) slice251k8p84) slice251k8p148) slice251k8p208) slice251k8p272)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k9p0 : block g251 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k9p7 : block g251 9 7 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k9 : block g251 9 0 29=true := (@block_merge g251 9 0 7 22 slice251k9p0 slice251k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k10p0 : block g251 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k10 : block g251 10 0 1=true := slice251k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked251 : checkedTables g251 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0=true)
  · exact (rfl : block g251 1 0 0=true)
  · exact (rfl : block g251 2 0 0=true)
  · exact (rfl : block g251 3 0 0=true)
  · exact (rfl : block g251 4 0 0=true)
  · exact (rfl : block g251 5 0 0=true)
  · exact layerOK251k6
  · exact layerOK251k7
  · exact layerOK251k8
  · exact layerOK251k9
  · exact layerOK251k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 11 :=
  lower_forest (g:=g251) (i:=0) (hints:=1125122049) (before_sound known223 valid223) geom251 checked251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[])]
def known251 := extendKnown known223 11 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid223 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom239 : graphValid g239 (boundsBefore known251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k9p0 : block g239 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k9 : block g239 9 0 1=true := slice239k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked239 : checkedTables g239 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0=true)
  · exact (rfl : block g239 1 0 0=true)
  · exact (rfl : block g239 2 0 0=true)
  · exact (rfl : block g239 3 0 0=true)
  · exact (rfl : block g239 4 0 0=true)
  · exact (rfl : block g239 5 0 0=true)
  · exact (rfl : block g239 6 0 0=true)
  · exact (rfl : block g239 7 0 0=true)
  · exact (rfl : block g239 8 0 0=true)
  · exact layerOK239k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 10 :=
  lower_forest (g:=g239) (i:=0) (hints:=1661992961) (before_sound known251 valid251) geom239 checked239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps239 : List (Nat × List Nat) := [(239,[])]
def known239 := extendKnown known251 10 maps239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid239 : Known known239 := extendKnown_ok valid251 low239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom127 : graphValid g127 (boundsBefore known239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k9p0 : block g127 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k9 : block g127 9 0 1=true := slice127k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked127 : checkedTables g127 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0=true)
  · exact (rfl : block g127 1 0 0=true)
  · exact (rfl : block g127 2 0 0=true)
  · exact (rfl : block g127 3 0 0=true)
  · exact (rfl : block g127 4 0 0=true)
  · exact (rfl : block g127 5 0 0=true)
  · exact (rfl : block g127 6 0 0=true)
  · exact (rfl : block g127 7 0 0=true)
  · exact (rfl : block g127 8 0 0=true)
  · exact layerOK127k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 10 :=
  lower_forest (g:=g127) (i:=0) (hints:=51380225) (before_sound known239 valid239) geom127 checked127 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[])]
def known127 := extendKnown known239 10 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid239 low127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p0 : block g255 7 0 17 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p17 : block g255 7 17 35 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k7 : block g255 7 0 52=true := (@block_merge g255 7 0 17 35 slice255k7p0 slice255k7p17)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p7 : block g255 8 7 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p71 : block g255 8 71 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p135 : block g255 8 135 19 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p154 : block g255 8 154 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p218 : block g255 8 218 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p282 : block g255 8 282 63 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 345=true := (@block_merge g255 8 0 282 63 (@block_merge g255 8 0 218 64 (@block_merge g255 8 0 154 64 (@block_merge g255 8 0 135 19 (@block_merge g255 8 0 71 64 (@block_merge g255 8 0 7 64 slice255k8p0 slice255k8p7) slice255k8p71) slice255k8p135) slice255k8p154) slice255k8p218) slice255k8p282)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p0 : block g255 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p1 : block g255 9 1 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p65 : block g255 9 65 5 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p70 : block g255 9 70 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p134 : block g255 9 134 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p198 : block g255 9 198 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p262 : block g255 9 262 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p326 : block g255 9 326 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p390 : block g255 9 390 44 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p434 : block g255 9 434 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p498 : block g255 9 498 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p562 : block g255 9 562 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p626 : block g255 9 626 4 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k9 : block g255 9 0 630=true := (@block_merge g255 9 0 626 4 (@block_merge g255 9 0 562 64 (@block_merge g255 9 0 498 64 (@block_merge g255 9 0 434 64 (@block_merge g255 9 0 390 44 (@block_merge g255 9 0 326 64 (@block_merge g255 9 0 262 64 (@block_merge g255 9 0 198 64 (@block_merge g255 9 0 134 64 (@block_merge g255 9 0 70 64 (@block_merge g255 9 0 65 5 (@block_merge g255 9 0 1 64 slice255k9p0 slice255k9p1) slice255k9p65) slice255k9p70) slice255k9p134) slice255k9p198) slice255k9p262) slice255k9p326) slice255k9p390) slice255k9p434) slice255k9p498) slice255k9p562) slice255k9p626)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p0 : block g255 10 0 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p18 : block g255 10 18 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p82 : block g255 10 82 48 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p130 : block g255 10 130 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p194 : block g255 10 194 7 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k10 : block g255 10 0 201=true := (@block_merge g255 10 0 194 7 (@block_merge g255 10 0 130 64 (@block_merge g255 10 0 82 48 (@block_merge g255 10 0 18 64 slice255k10p0 slice255k10p18) slice255k10p82) slice255k10p130) slice255k10p194)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p0 : block g255 11 0 5 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p5 : block g255 11 5 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k11 : block g255 11 0 20=true := (@block_merge g255 11 0 5 15 slice255k11p0 slice255k11p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k12p0 : block g255 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k12 : block g255 12 0 1=true := slice255k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact layerOK255k7
  · exact layerOK255k8
  · exact layerOK255k9
  · exact layerOK255k10
  · exact layerOK255k11
  · exact layerOK255k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 13 :=
  lower_forest (g:=g255) (i:=0) (hints:=1125122049) (before_sound known127 valid127) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known127 13 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid127 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8530 t → 13 ≤ t :=
  conclude8530 (root_index (g:=g255) (before_sound known127 valid127) geom255 checked255 (k:=12) (by decide) (i:=0) (by decide +kernel))

theorem lowerExplicit : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 6 && x 7)) t → 13 ≤ t := PEqualNP.Outside.L_meta_10676.Core8525.exactLower

end PEqualNP.Outside.L_meta_10676.Core8525

theorem PEqualNP.Outside.L_meta_10676 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) t → 14 ≤ t :=
  PEqualNP.Outside.L_meta_10676_aux.lower_of_core
    PEqualNP.Outside.L_meta_10676.Core8525.lowerExplicit
