import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_720

-- Adapted from Mads Anker Nielsen’s subdivided K4 proof and the project circuit lemmas.
open PEqualNP.MetaComplexity

section


namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

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

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

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

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

end

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
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

end PEqualNP.MetaComplexity.Helpers.PermInputs

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.MetaComplexity.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers

end

section


namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not

def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ NotFree C.gates ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem HasMonoSize.has {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ} (h : HasMonoSize n f s) :
    HasCircuitSize n f s := by
  obtain ⟨C, h1, _, h3, h4⟩ := h
  exact ⟨C, h1, h3, h4⟩

theorem HasMonoSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ} (h : HasMonoSize n f s)
    (hs : s ≤ s') : HasMonoSize n f s' := by
  obtain ⟨C, h1, h2, h3, h4⟩ := h
  exact ⟨C, h1, h2, le_trans h3 hs, h4⟩

def MClean (m : ℕ) (gs : List Gate) : Prop := CleanL m gs ∧ NotFree gs

def Computes (m : ℕ) (gs : List Gate) (o : ℕ) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ x : Fin m → Bool, vl gs x o = f x

def LeastIn (Q : List Gate → Prop) (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate)
    (o : ℕ) : Prop :=
  CleanL m gs ∧ Q gs ∧ Computes m gs o f ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → Q gs' → Computes m gs' o' f →
      gs.length ≤ gs'.length

def MLeast (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  LeastIn NotFree m f gs o

theorem MLeast.clean {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (h : MLeast m f gs o) : MClean m gs := ⟨h.1, h.2.1⟩

noncomputable def RdSet (gs : List Gate) (w : ℕ) : Finset ℕ := by
  classical exact (Finset.range gs.length).filter (fun q => Reads gs q w)

theorem mem_rdSet {gs : List Gate} {w q : ℕ} : q ∈ RdSet gs w ↔ Reads gs q w := by
  classical
  unfold RdSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨reads_len h, h⟩⟩

def pt {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun i => decide (i ∈ S)

def Removable (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ) : Prop :=
  ∀ p ∈ S, p < gs.length ∧
    ((∃ j, tgt p = some j ∧ j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j) ∨
      (tgt p = none ∧ o ≠ m + p ∧ (∀ q, Reads gs q (m + p) → q ∈ S) ∧
        ∀ q ∈ S, tgt q ≠ some (m + p)))

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open SimpleGraph

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs
open SimpleGraph

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Loc

open SimpleGraph
open PEqualNP.MetaComplexity.Helpers.Forest

noncomputable def tau {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k}

noncomputable def Phi1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  A.card + G.edgeSet.ncard + tau G

def AFree {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∉ A

structure Run {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop where
  nd : [a', a, s, t, b, b'].Nodup
  ha : ∀ w, G.Adj a w ↔ w = a' ∨ w = s
  hs : ∀ w, G.Adj s w ↔ w = a ∨ w = t
  ht : ∀ w, G.Adj t w ↔ w = s ∨ w = b
  hb : ∀ w, G.Adj b w ↔ w = t ∨ w = b'
  ha' : ∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c
  hb' : ∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c

theorem Run.symm {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Run G b' b t s a a' where
  nd := by
    have := List.nodup_reverse.2 h.nd
    simpa using this
  ha := fun w => (h.hb w).trans Or.comm
  hs := fun w => (h.ht w).trans Or.comm
  ht := fun w => (h.hs w).trans Or.comm
  hb := fun w => (h.ha w).trans Or.comm
  ha' := h.hb'
  hb' := h.ha'

def BoundOf {n : ℕ} (Sz : ((Fin n → Bool) → Bool) → ℕ → Prop) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Prop :=
  ∀ s : ℕ, Sz (F G A) s → Phi1 G A ≤ s + 1

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open SimpleGraph

abbrev Bound {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  BoundOf (HasMonoSize n) G A

def IH {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)), G' ≤ G → AFree G' A' →
    (G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) → Bound G' A'

structure Cex {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) :
    Prop where
  inv : AFree G A
  ih : IH G A
  least : MLeast n (F G A) gs o
  small : gs.length + 2 ≤ Phi1 G A

structure Ctx {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) : Prop where
  cex : Cex G A gs o
  run : Run G a' a s t b b'
  hA : A = ∅

theorem Ctx.symm {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    {a' a s t b b' : Fin n} (h : Ctx G A gs o a' a s t b b') : Ctx G A gs o b' b t s a a' :=
  ⟨h.cex, h.run.symm, h.hA⟩

structure Fan {n : ℕ} (gs : List Gate) (a s t b : Fin n) (qa qs qt qb : ℕ) : Prop where
  fa : RdSet gs a = {qa}
  fs : RdSet gs s = {qs}
  ft : RdSet gs t = {qt}
  fb : RdSet gs b = {qb}

theorem Fan.symm {n : ℕ} {gs : List Gate} {a s t b : Fin n} {qa qs qt qb : ℕ}
    (h : Fan gs a s t b qa qs qt qb) : Fan gs b t s a qb qt qs qa :=
  ⟨h.fb, h.ft, h.fs, h.fa⟩

def ToolLeast : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), (∃ x y : Fin n → Bool, f x ≠ f y) →
    HasMonoSize n f s → ∃ (gs : List Gate) (o : ℕ), MLeast n f gs o ∧ gs.length ≤ s

def ToolOfClean : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ), MClean m gs →
    HasMonoSize m (fun x => vl gs x o) gs.length

def ToolRemoval : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ), CleanL m gs → Removable m gs o P S tgt →
    ∃ (gs' : List Gate) (r : ℕ → ℕ), CleanL m gs' ∧ (NotFree gs → NotFree gs') ∧
      gs'.length + S.card ≤ gs.length ∧ (∀ j, j < m → r j = j) ∧
      ∀ j, j < m + gs.length → (∀ p ∈ S, tgt p = none → j ≠ m + p) →
        r j < m + gs'.length ∧ ∀ x ∈ P, vl gs' x (r j) = vl gs x j

def ToolNoAlias : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) → ∀ p, p < gs.length → ∀ j, j < m + p →
      ¬ ∀ x : Fin m → Bool, vl gs x (m + p) = vl gs x j

def ToolLive : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) →
      o < m + gs.length ∧ ∀ p, p < gs.length → o ≠ m + p → (RdSet gs (m + p)).Nonempty

def ToolProp : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (x x' : Fin m → Bool) (D : Set ℕ) (K : ℕ), CleanL m gs →
    (∀ i : Fin m, (i : ℕ) ∉ D → x i = x' i) →
    (∀ p g, gs[p]? = some g → m + p < K → m + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ vl gs x (m + p) = vl gs x' (m + p)) →
    ∀ j, j < K → j ∉ D → vl gs x j = vl gs x' j

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Loc.Clean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Loc

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    NotFree gs → NotFree acc.2 → NotFree (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem ToolOfClean_proof : ToolOfClean := by
  intro m gs o h
  refine ⟨⟨gs, o⟩, ?_, h.2, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok m gs h.1 g hg).1

def HasMClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ NotFree gs ∧ gs.length ≤ s ∧ Computes n gs o f

theorem mclean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasMonoSize n f s) : HasMClean n f s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := h
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
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · exact elim_mono n C.gates _ hnf (by intro g hg; simp at hg)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem ToolLeast_proof : ToolLeast := by
  classical
  intro n f s hnc h
  have hc := mclean_of n f s hnc h
  have hex : ∃ t, HasMClean n f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hnf, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hnf, hev, ?_⟩, by omega⟩
  intro gs' o' hc' hn' he'
  have := Nat.find_min' hex ⟨gs', o', hc', hn', le_refl _, he'⟩
  omega

theorem relabel_mono {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasMonoSize n h s) : HasMonoSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact hnf g0 hg0
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end PEqualNP.MetaComplexity.Loc.Clean

end

section


namespace PEqualNP.MetaComplexity.Loc.Removal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc

def cnt (S : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if p ∈ S then cnt S p else cnt S p + 1

def rmap (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  if j < m then j
  else if j - m ∈ S then
    match tgt (j - m) with
    | some i => if _h : i < j then rmap m S tgt i else 0
    | none => 0
  else m + cnt S (j - m)
termination_by j

def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

def g0 : Gate := ⟨GateOp.and, []⟩

def build (S : Finset ℕ) (r : ℕ → ℕ) (gs : List Gate) : ℕ → List Gate
  | 0 => []
  | p + 1 => if p ∈ S then build S r gs p else build S r gs p ++ [rg r (gs.getD p g0)]

section
variable (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ)

theorem rmap_lt {j : ℕ} (h : j < m) : rmap m S tgt j = j := by
  rw [rmap]; simp [h]

theorem rmap_keep {p : ℕ} (h : p ∉ S) : rmap m S tgt (m + p) = m + cnt S p := by
  rw [rmap]; simp [h]

theorem rmap_alias {p i : ℕ} (h : p ∈ S) (ht : tgt p = some i) (hi : i < m + p) :
    rmap m S tgt (m + p) = rmap m S tgt i := by
  rw [rmap]; simp [h, ht, hi]

theorem cnt_succ_keep {p : ℕ} (h : p ∉ S) : cnt S (p + 1) = cnt S p + 1 := by
  simp [cnt, h]

theorem cnt_mono {p q : ℕ} (h : p ≤ q) : cnt S p ≤ cnt S q := by
  induction q with
  | zero => simp at h; subst h; exact le_rfl
  | succ q ih =>
    rcases Nat.lt_or_ge p (q + 1) with h' | h'
    · have := ih (by omega)
      simp only [cnt]; split_ifs <;> omega
    · have : p = q + 1 := by omega
      subst this; exact le_rfl

theorem cnt_card (p : ℕ) : cnt S p + ((Finset.range p).filter (· ∈ S)).card = p := by
  induction p with
  | zero => simp [cnt]
  | succ p ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p ∈ S
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      simp only [cnt, if_pos hp]; omega
    · rw [if_neg hp]
      simp only [cnt, if_neg hp]; omega

variable (r : ℕ → ℕ) (gs : List Gate)

theorem len_build (p : ℕ) : (build S r gs p).length = cnt S p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [build, cnt]
    split_ifs <;> simp [ih]

theorem build_prefix (p : ℕ) : ∀ d, ∃ t, build S r gs (p + d) = build S r gs p ++ t := by
  intro d
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    rw [← Nat.add_assoc]
    simp only [build]
    split_ifs
    · exact ⟨t, ht⟩
    · exact ⟨t ++ _, by rw [ht, List.append_assoc]⟩

theorem get_build {p q : ℕ} (hp : p ∉ S) (hq : p < q) :
    (build S r gs q)[cnt S p]? = some (rg r (gs.getD p g0)) := by
  obtain ⟨t, ht⟩ := build_prefix S r gs (p + 1) (q - (p + 1))
  rw [show p + 1 + (q - (p + 1)) = q by omega] at ht
  rw [ht]
  have h1 : build S r gs (p + 1) = build S r gs p ++ [rg r (gs.getD p g0)] := by
    simp [build, hp]
  rw [h1, List.append_assoc, List.getElem?_append_right (by rw [len_build]),
    len_build]
  simp

theorem mem_build (p : ℕ) : ∀ (k : ℕ) (g' : Gate), (build S r gs p)[k]? = some g' →
    ∃ q, q < p ∧ q ∉ S ∧ cnt S q = k ∧ g' = rg r (gs.getD q g0) := by
  induction p with
  | zero => intro k g' h; simp [build] at h
  | succ p ih =>
    intro k g' h
    simp only [build] at h
    split_ifs at h with hp
    · obtain ⟨q, h1, h2, h3, h4⟩ := ih k g' h
      exact ⟨q, by omega, h2, h3, h4⟩
    · by_cases hk : k < (build S r gs p).length
      · rw [List.getElem?_append_left hk] at h
        obtain ⟨q, h1, h2, h3, h4⟩ := ih k g' h
        exact ⟨q, by omega, h2, h3, h4⟩
      · rw [List.getElem?_append_right (by omega)] at h
        have hk' : k - (build S r gs p).length = 0 := by
          by_contra hne
          rw [List.getElem?_eq_none (by simp; omega)] at h
          cases h
        rw [hk'] at h
        simp at h
        refine ⟨p, by omega, hp, ?_, h.symm⟩
        rw [len_build] at hk hk'
        omega

end

def NO (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (j : ℕ) : Prop :=
  ∀ p ∈ S, tgt p = none → j ≠ m + p

section
variable {m : ℕ} {gs : List Gate} {o : ℕ} {P : Set (Fin m → Bool)} {S : Finset ℕ}
  {tgt : ℕ → Option ℕ}

theorem no_tgt (hR : Removable m gs o P S tgt) {p i : ℕ} (hp : p ∈ S) (ht : tgt p = some i) :
    NO m S tgt i := by
  intro q hq hqn heq
  rcases (hR q hq).2 with ⟨j, hj, _⟩ | ⟨_, _, _, hno⟩
  · rw [hqn] at hj; cases hj
  · exact hno p hp (heq ▸ ht)

theorem no_read (hR : Removable m gs o P S tgt) {p : ℕ} (hp : p ∉ S) {g : Gate}
    (hg : gs[p]? = some g) {a : ℕ} (ha : a ∈ g.inputs) : NO m S tgt a := by
  intro q hq hqn heq
  rcases (hR q hq).2 with ⟨j, hj, _⟩ | ⟨_, _, hrd, _⟩
  · rw [hqn] at hj; cases hj
  · exact hp (hrd p ⟨g, hg, heq ▸ ha⟩)

theorem rmap_bound (hR : Removable m gs o P S tgt) :
    ∀ a, NO m S tgt a → ∀ q, a < m + q → rmap m S tgt a < m + cnt S q := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro hno q haq
    by_cases ham : a < m
    · rw [rmap_lt m S tgt ham]; omega
    · obtain ⟨p, rfl⟩ : ∃ p, a = m + p := ⟨a - m, by omega⟩
      by_cases hp : p ∈ S
      · rcases (hR p hp).2 with ⟨i, hi, hil, _⟩ | ⟨hn, _⟩
        · rw [rmap_alias m S tgt hp hi hil]
          exact ih i hil (no_tgt hR hp hi) q (by omega)
        · exact absurd rfl (hno p hp hn)
      · rw [rmap_keep m S tgt hp]
        have h1 := cnt_succ_keep S hp
        have h2 := cnt_mono S (show p + 1 ≤ q by omega)
        omega

theorem getD_eq {gs : List Gate} {p : ℕ} (hp : p < gs.length) :
    gs[p]? = some (gs.getD p g0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

theorem clean_build (hcl : CleanL m gs) (hR : Removable m gs o P S tgt) :
    CleanL m (build S (rmap m S tgt) gs gs.length) := by
  intro k g' hk
  obtain ⟨q, hq, hqS, rfl, rfl⟩ := mem_build S (rmap m S tgt) gs _ k g' hk
  have hg := getD_eq hq
  have hc := hcl q _ hg
  have hb : ∀ a ∈ (gs.getD q g0).inputs, rmap m S tgt a < m + cnt S q := fun a ha =>
    rmap_bound hR a (no_read hR hqS hg ha) q (hc.lt a ha)
  rcases hc with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, _, _, h2⟩
  · refine Or.inl ⟨h1, rmap m S tgt j, hb j (by rw [h2]; simp), ?_⟩
    show (gs.getD q g0).inputs.map _ = _
    rw [h2]; rfl
  · refine Or.inr ⟨h1, rmap m S tgt j, rmap m S tgt k, hb j (by rw [h2]; simp),
      hb k (by rw [h2]; simp), ?_⟩
    show (gs.getD q g0).inputs.map _ = _
    rw [h2]; rfl

theorem val_build (hcl : CleanL m gs) (hR : Removable m gs o P S tgt) :
    ∀ j, j < m + gs.length → NO m S tgt j → ∀ x ∈ P,
      vl (build S (rmap m S tgt) gs gs.length) x (rmap m S tgt j) = vl gs x j := by
  have hcl' := clean_build hcl hR
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjl hno x hx
    by_cases hjm : j < m
    · rw [rmap_lt m S tgt hjm, vl_input _ x j hjm, vl_input _ x j hjm]
    · obtain ⟨p, rfl⟩ : ∃ p, j = m + p := ⟨j - m, by omega⟩
      by_cases hp : p ∈ S
      · rcases (hR p hp).2 with ⟨i, hi, hil, hv⟩ | ⟨hn, _⟩
        · rw [rmap_alias m S tgt hp hi hil, hv x hx]
          exact ih i hil (by omega) (no_tgt hR hp hi) x hx
        · exact absurd rfl (hno p hp hn)
      · have hpl : p < gs.length := by omega
        have hg := getD_eq hpl
        rw [rmap_keep m S tgt hp,
          vl_gate _ hcl' x (cnt S p) _ (get_build S (rmap m S tgt) gs hp hpl),
          vl_gate gs hcl x p _ hg]
        show (gs.getD p g0).op.eval (((gs.getD p g0).inputs.map (rmap m S tgt)).map _) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have hal := (hcl p _ hg).lt a ha
        exact ih a hal (by omega) (no_read hR hp hg ha) x hx

end

theorem ToolRemoval_proof : ToolRemoval := by
  intro m gs o P S tgt hcl hR
  refine ⟨build S (rmap m S tgt) gs gs.length, rmap m S tgt, clean_build hcl hR, ?_, ?_,
    fun j hj => rmap_lt m S tgt hj, ?_⟩
  · intro hnf g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨q, hq, _, _, rfl⟩ := mem_build S (rmap m S tgt) gs _ k g hk
    show (gs.getD q g0).op ≠ _
    exact hnf _ (List.mem_of_getElem? (getD_eq hq))
  · have h1 := cnt_card S gs.length
    have h2 : (Finset.range gs.length).filter (· ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨(hR p h).1, h⟩⟩
    rw [h2] at h1
    rw [len_build]
    omega
  · intro j hj hno
    refine ⟨?_, val_build hcl hR j hj hno⟩
    rw [len_build]
    exact rmap_bound hR j hno gs.length hj

theorem vl_past {m : ℕ} (gs : List Gate) (x : Fin m → Bool) {j : ℕ} (h : m + gs.length ≤ j) :
    vl gs x j = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem out_lt {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hc : Computes m gs o f) (hf : ∃ x y : Fin m → Bool, f x ≠ f y) : o < m + gs.length := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := hf
  apply hxy
  rw [← hc x, ← hc y, vl_past gs x (by omega), vl_past gs y (by omega)]

theorem least_no_drop {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hM : MLeast m f gs o) (hf : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (tgt : ℕ → Option ℕ) (hR : Removable m gs o Set.univ {p} tgt) (ho : o ≠ m + p ∨ tgt p ≠ none) :
    False := by
  obtain ⟨gs', r, hcl', hnf', hlen, _, hv⟩ :=
    ToolRemoval_proof m gs o Set.univ {p} tgt hM.1 hR
  have hol := out_lt hM.2.2.1 hf
  have hno : ∀ q ∈ ({p} : Finset ℕ), tgt q = none → o ≠ m + q := by
    intro q hq hqn
    rw [Finset.mem_singleton] at hq
    subst hq
    rcases ho with h | h
    · exact h
    · exact absurd hqn h
  obtain ⟨_, hv'⟩ := hv o hol hno
  have hle := hM.2.2.2 gs' (r o) hcl' (hnf' hM.2.1) (fun x => by
    rw [hv' x (Set.mem_univ x)]; exact hM.2.2.1 x)
  simp at hlen
  omega

theorem ToolNoAlias_proof : ToolNoAlias := by
  intro m f gs o hM hf p hp j hj heq
  refine least_no_drop hM hf p (fun _ => some j) ?_ (Or.inr (by simp))
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst q
  exact ⟨hp, Or.inl ⟨j, rfl, hj, fun x _ => heq x⟩⟩

theorem ToolLive_proof : ToolLive := by
  intro m f gs o hM hf
  refine ⟨out_lt hM.2.2.1 hf, ?_⟩
  intro p hp hop
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  refine least_no_drop hM hf p (fun _ => none) ?_ (Or.inl hop)
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst q
  refine ⟨hp, Or.inr ⟨rfl, hop, ?_, fun _ _ h => by cases h⟩⟩
  intro q hrd
  have : q ∈ RdSet gs (m + p) := mem_rdSet.2 hrd
  rw [hne] at this
  simp at this

end PEqualNP.MetaComplexity.Loc.Removal

end

section


namespace PEqualNP.MetaComplexity.Loc.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc

theorem ToolProp_proof : ToolProp := by
  intro m gs x x' D K hcl hin hg j hj hjD
  refine agree_B gs hcl x x' (fun j => j ∈ D) K ?_ ?_ j hj hjD
  · intro j hjm hjD
    rw [vl_input gs x j hjm, vl_input gs x' j hjm]
    exact hin ⟨j, hjm⟩ hjD
  · intro p g hp hpK hpD hr _
    rcases hg p g hp hpK hpD with h1 | h1
    · obtain ⟨a, ha, haD⟩ := hr
      exact absurd haD (h1 a ha)
    · exact h1

end PEqualNP.MetaComplexity.Loc.Wires

end

section


namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers

end

section


namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

end PEqualNP.MetaComplexity.Helpers.Readers

end

section


namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

end PEqualNP.MetaComplexity.Helpers.Readers

end

section


theorem PEqualNP.MetaComplexity.L107 : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ), (∃ p : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1), (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → (∀ p q : Fin (n + 1), p ≠ q → (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool, f (Function.update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool, f (Function.update (Function.update x p (!a)) q b) = f (Function.update (Function.update x p a) q (!b)) ∧ f (Function.update (Function.update x p a) q (!b)) = f (Function.update (Function.update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') :=
  PEqualNP.MetaComplexity.Helpers.Readers.fanout_step_3_4

end

section


namespace PEqualNP.MetaComplexity.Helpers.PathSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def G (N k : ℕ) (x : Fin N → Bool) : Bool :=
  decide ((∃ i : Fin N, i.val < k ∧ x i = true) ∨
    (∃ i j : Fin N, k ≤ i.val ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true))

def ext {N : ℕ} (x : Fin N → Bool) (j : ℕ) : Bool := if h : j < N then x ⟨j, h⟩ else false

theorem ext_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ext x i.val = x i := by
  simp [ext]

theorem ext_lt {N : ℕ} {x : Fin N → Bool} {j : ℕ} (h : ext x j = true) : j < N := by
  unfold ext at h
  split at h
  · assumption
  · simp at h

theorem ext_fn {N : ℕ} (Q : ℕ → Bool) (j : ℕ) :
    ext (fun i : Fin N => Q i.val) j = (decide (j < N) && Q j) := by
  unfold ext
  by_cases hj : j < N <;> simp [hj]

theorem ext_update {N : ℕ} (x : Fin N → Bool) (p : Fin N) (b : Bool) (j : ℕ) :
    ext (Function.update x p b) j = if j = p.val then b else ext x j := by
  unfold ext
  by_cases hj : j < N
  · simp [hj, Function.update_apply, Fin.ext_iff]
  · have : j ≠ p.val := by have := p.2; omega
    simp [hj, this]

theorem G_iff (N k : ℕ) (x : Fin N → Bool) : G N k x = true ↔
    ((∃ i, i < k ∧ ext x i = true) ∨ (∃ i, k ≤ i ∧ ext x i = true ∧ ext x (i + 1) = true)) := by
  unfold G
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, j, hi, hij, hx, hy⟩)
    · exact Or.inl ⟨i, hi, by rw [ext_fin]; exact hx⟩
    · refine Or.inr ⟨i, hi, by rw [ext_fin]; exact hx, ?_⟩
      rw [hij, ext_fin]; exact hy
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · have hl := ext_lt hx
      refine Or.inl ⟨⟨i, hl⟩, hi, ?_⟩
      rw [← ext_fin x ⟨i, hl⟩]; exact hx
    · have hl := ext_lt hy
      refine Or.inr ⟨⟨i, by omega⟩, ⟨i + 1, hl⟩, hi, rfl, ?_, ?_⟩
      · rw [← ext_fin x ⟨i, by omega⟩]; exact hx
      · rw [← ext_fin x ⟨i + 1, hl⟩]; exact hy

def del (n k : ℕ) (hk : k < n) : Fin (n + 1) → Fin n :=
  fun i => ⟨if i.val ≤ k then i.val else i.val - 1, by have := i.2; split <;> omega⟩

theorem ext_del (n k : ℕ) (hk : k < n) (y : Fin n → Bool) (b : Bool) (j : ℕ) :
    ext (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ b) j
      = if j = k then b else if j < k then ext y j else ext y (j - 1) := by
  rw [ext_update]
  by_cases hjk : j = k
  · simp [hjk]
  · rw [if_neg hjk, if_neg hjk]
    unfold ext
    by_cases hj : j < n + 1
    · rw [dif_pos hj]
      by_cases hjk' : j < k
      · rw [if_pos hjk', dif_pos (by omega)]
        simp [del, show j ≤ k by omega]
      · rw [if_neg hjk', dif_pos (by omega)]
        simp [del, show ¬ j ≤ k by omega]
    · rw [dif_neg hj, if_neg (by omega), dif_neg (by omega)]

theorem G_del_false (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ false) = G n k y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, hi, hx⟩
    · by_cases hik : i = k
      · rw [if_pos hik] at hx; exact absurd hx (by simp)
      · rw [if_neg hik, if_neg (by omega)] at hx
        rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
        rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · refine Or.inl ⟨i, hi, ?_⟩
      rw [if_neg (by omega), if_pos hi]; exact hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

theorem G_del_true (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ true) = G n (k + 1) y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, by omega, hx⟩
    · by_cases hik : i = k
      · rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inl ⟨k, by omega, ?_⟩
        rwa [show k = i + 1 - 1 by omega]
      · by_cases hik1 : i = k + 1
        · rw [if_neg (by omega), if_neg (by omega)] at hx
          refine Or.inl ⟨k, by omega, ?_⟩
          rwa [show k = i - 1 by omega]
        · rw [if_neg hik, if_neg (by omega)] at hx
          rw [if_neg (by omega), if_neg (by omega)] at hy
          refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
          rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · by_cases hik : i < k
      · refine Or.inl ⟨i, hik, ?_⟩
        rw [if_neg (by omega), if_pos hik]; exact hx
      · have e : i = k := by omega
        subst e
        refine Or.inr ⟨i, le_rfl, by simp, ?_⟩
        rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

theorem G_dep (N k : ℕ) (hd : k + 2 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, G N k (Function.update x p (!x p)) ≠ G N k x := by
  by_cases hp : p.val < k
  · refine ⟨fun _ => false, ?_⟩
    have h1 : G N k (Function.update (fun _ => false) p (!false)) = true := by
      rw [G_iff]
      refine Or.inl ⟨p.val, hp, ?_⟩
      rw [ext_update]; simp
    have h0 : G N k (fun _ => false) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, _, hx⟩ | ⟨i, _, hx, _⟩) <;> simp [ext] at hx
    rw [h1, h0]; simp
  · set q : ℕ := if p.val + 1 < N then p.val + 1 else p.val - 1 with hq
    have hqN : q < N := by rw [hq]; split <;> omega
    have hqk : k ≤ q := by have := p.2; rw [hq]; split <;> omega
    have hpq : p.val ≠ q := by rw [hq]; split <;> omega
    refine ⟨fun i : Fin N => decide (i.val = q), ?_⟩
    have hxp : (fun i : Fin N => decide (i.val = q)) p = false := by simp [hpq]
    rw [hxp]
    have h1 : G N k (Function.update (fun i : Fin N => decide (i.val = q)) p (!false)) = true := by
      rw [G_iff]
      right
      by_cases hc : p.val + 1 < N
      · have hqv : q = p.val + 1 := by rw [hq, if_pos hc]
        refine ⟨p.val, by omega, ?_, ?_⟩
        · rw [ext_update]; simp
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqv, hc]
      · have hqv : q = p.val - 1 := by rw [hq, if_neg hc]
        refine ⟨q, hqk, ?_, ?_⟩
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqN]
        · rw [ext_update, if_pos (by omega)]; rfl
    have h0 : G N k (fun i : Fin N => decide (i.val = q)) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
      · rw [ext_fn (fun j => decide (j = q))] at hx
        simp at hx; omega
      · rw [ext_fn (fun j => decide (j = q))] at hx hy
        simp at hx hy; omega
    rw [h1, h0]; simp

theorem G_lower : ∀ d : ℕ, 2 ≤ d → ∀ k N s : ℕ, N = k + d →
    HasCircuitSize N (G N k) s → N + d / 2 ≤ s + 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd k N s hN h
    by_cases hd4 : d < 4
    · have := dep_lower N (G N k) (G_dep N k (by omega)) s h
      have : d / 2 ≤ 1 := by omega
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hk : k < n := by omega
      set p : Fin (n + 1) := ⟨k, by omega⟩ with hp
      have hdep := G_dep (n + 1) k (by omega) p
      have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
          G (n + 1) k (Function.update x p b) ≠ G (n + 1) k (Function.update y p b) := by
        intro b
        refine ⟨fun _ => false, fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3), ?_⟩
        have h0 : G (n + 1) k (Function.update (fun _ => false) p b) = false := by
          rw [← Bool.not_eq_true, G_iff]
          rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
          · rw [ext_update, if_neg (by simp [hp]; omega)] at hx
            simp [ext] at hx
          · rw [ext_update] at hx hy
            rw [if_neg (by simp [hp]; omega)] at hy
            simp [ext] at hy
        have h1 : G (n + 1) k (Function.update
            (fun i : Fin (n + 1) => decide (i.val = k + 2 ∨ i.val = k + 3)) p b) = true := by
          rw [G_iff]
          refine Or.inr ⟨k + 2, by omega, ?_, ?_⟩
          · rw [ext_update, if_neg (by simp [hp]),
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
          · rw [ext_update, if_neg (by simp [hp]; omega),
              ext_fn (fun j => decide (j = k + 2 ∨ j = k + 3))]
            simp; omega
        rw [h0, h1]; simp
      obtain ⟨b, s', hs, h'⟩ := gate_elim_at n (G (n + 1) k) p s hdep hnc h
      have h'' := relabel_size (del n k hk) _ s' h'
      cases b with
      | false =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p false)) (y ∘ del n k hk)) = G n k := by
          funext y; exact G_del_false n k hk y
        rw [e] at h''
        have := ih (d - 1) (by omega) (by omega) k n s' (by omega) h''
        omega
      | true =>
        have e : (fun y : Fin n → Bool =>
            (fun x => G (n + 1) k (Function.update x p true)) (y ∘ del n k hk)) = G n (k + 1) := by
          funext y; exact G_del_true n k hk y
        rw [e] at h''
        have := ih (d - 2) (by omega) (by omega) (k + 1) n s' (by omega) h''
        omega

def path (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)

theorem path_eq_G (n : ℕ) : path n = G n 0 := by
  funext x
  simp [path, G]

theorem path_lower (n s : ℕ) (h : HasCircuitSize n (path n) s) : n + n / 2 ≤ s + 2 := by
  by_cases hn : n ≤ 1
  · have : n / 2 = 0 := by omega
    omega
  · rw [path_eq_G] at h
    exact G_lower n (by omega) 0 n s (by omega) h

end PEqualNP.MetaComplexity.Helpers.PathSize

end

section


namespace PEqualNP.MetaComplexity.Helpers.CycleSize.PG

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.PathSize

def pathB (w : List Bool) : ℕ → Bool
  | 0 => false
  | 1 => false
  | k + 2 => pathB w (k + 1) || (w.getD k false && w.getD (k + 1) false)

theorem pathB_iff (w : List Bool) : ∀ n : ℕ, pathB w n = true ↔
    ∃ i, i + 1 < n ∧ w.getD i false = true ∧ w.getD (i + 1) false = true
  | 0 => by simp [pathB]
  | 1 => by simp [pathB]
  | k + 2 => by
    rw [pathB, Bool.or_eq_true, pathB_iff w (k + 1), Bool.and_eq_true]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨i, by omega, h1, h2⟩
      · exact ⟨k, by omega, h1, h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      by_cases hik : i = k
      · subst hik; exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨i, by omega, h1, h2⟩

theorem pathB_step (w : List Bool) (n : ℕ) (hn : 1 ≤ n) :
    pathB w (n + 2) = (pathB w n ||
      (w.getD n false && (w.getD (n - 1) false || w.getD (n + 1) false))) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pathB, Nat.add_sub_cancel]
  generalize pathB w (n + 1) = P
  generalize w.getD n false = a
  generalize w.getD (n + 1) false = b
  generalize w.getD (n + 1 + 1) false = c
  cases P <;> cases a <;> cases b <;> cases c <;> rfl

theorem three_gates (v : List Bool) (a b c o : ℕ) (ha : a < v.length) (hb : b < v.length)
    (hc : c < v.length) (ho : o < v.length) :
    (wiresFrom [⟨GateOp.or, [a, c]⟩, ⟨GateOp.and, [b, v.length]⟩,
      ⟨GateOp.or, [o, v.length + 1]⟩] v).getD (v.length + 2) false
      = (v.getD o false || (v.getD b false && (v.getD a false || v.getD c false))) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length →
      (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ ha, A _ _ hb, A _ _ hc, A _ _ ho]

theorem pathGates : ∀ n : ℕ, 2 ≤ n → ∀ m : ℕ, n ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 2 = n + n / 2 ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m → (wiresFrom gs w).getD out false = pathB w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn m hm
    match n, hn, hm, ih with
    | 2, _, hm, _ =>
      refine ⟨[⟨GateOp.and, [0, 1]⟩], m, ?_, rfl, by simp, ?_⟩
      · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
      · intro w hw
        have A : ∀ (t : List Bool) (i : ℕ), i < w.length →
            (w ++ t)[i]?.getD false = w[i]?.getD false := by
          intro t i h; rw [List.getElem?_append_left h]
        subst hw
        simp [wiresFrom, GateOp.eval, pathB, A _ 0 (by omega), A _ 1 (by omega)]
    | 3, _, hm, _ =>
      refine ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, m]⟩], m + 1, ?_, rfl, by simp, ?_⟩
      · intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp [Ok]
      · intro w hw
        have A : ∀ (t : List Bool) (i : ℕ), i < w.length →
            (w ++ t)[i]?.getD false = w[i]?.getD false := by
          intro t i h; rw [List.getElem?_append_left h]
        subst hw
        simp [wiresFrom, GateOp.eval, pathB, A _ 0 (by omega), A _ 1 (by omega),
          A _ 2 (by omega)]
        generalize w[0]?.getD false = a
        generalize w[1]?.getD false = b
        generalize w[2]?.getD false = c
        cases a <;> cases b <;> cases c <;> simp
    | n + 4, _, hm, ih =>
      obtain ⟨gs, out, ok, len, hout, ev⟩ := ih (n + 2) (by omega) (by omega) m (by omega)
      refine ⟨gs ++ [⟨GateOp.or, [n + 1, n + 3]⟩, ⟨GateOp.and, [n + 2, m + gs.length]⟩,
        ⟨GateOp.or, [out, m + gs.length + 1]⟩], m + gs.length + 2, ?_, ?_, by simp; omega, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact ok g hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl <;> simp [Ok]
      · simp only [List.length_append, List.length_cons, List.length_nil]
        have : (n + 4) / 2 = (n + 2) / 2 + 1 := by omega
        omega
      · intro w hw
        rw [wiresFrom_append]
        set v := wiresFrom gs w with hv
        have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
        have e : ∀ i, i < m → v.getD i false = w.getD i false := by
          intro i hi; rw [hv, getD_wiresFrom _ _ _ (by omega)]
        rw [← lv, three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),
          e (n + 1) (by omega), e (n + 2) (by omega), e (n + 3) (by omega), hv, ev w hw,
          pathB_step w (n + 2) (by omega)]
        rfl

theorem getD_ofFn_ext {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = ext x i := by
  unfold ext
  by_cases hi : i < n
  · rw [dif_pos hi]; simp [hi]
  · rw [dif_neg hi, List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.MetaComplexity.Helpers.CycleSize.PG

end

section


namespace PEqualNP.MetaComplexity.Helpers.CycleSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.PathSize
open PEqualNP.MetaComplexity.Helpers.CycleSize.PG

def cyc (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)

theorem succ_mod_eq {i n : ℕ} (h : i < n) : (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  split_ifs with h1
  · rw [h1, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem cyc_iff_ext (n : ℕ) (x : Fin n → Bool) : cyc n x = true ↔
    ∃ i, i < n ∧ ext x i = true ∧ ext x (if i + 1 = n then 0 else i + 1) = true := by
  unfold cyc
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨i.val, i.2, by rw [ext_fin]; exact hi, ?_⟩
    rw [← succ_mod_eq i.2, hij, ext_fin]; exact hj
  · rintro ⟨i, hi, h1, h2⟩
    have hl := ext_lt h2
    refine ⟨⟨i, hi⟩, ⟨_, hl⟩, succ_mod_eq hi, ?_, ?_⟩
    · rw [← ext_fin x ⟨i, hi⟩]; exact h1
    · rw [← ext_fin x ⟨_, hl⟩]; exact h2

def rot (n c : ℕ) (i : Fin n) : Fin n := ⟨(i.val + c) % n, Nat.mod_lt _ (by have := i.2; omega)⟩

theorem cyc_rot_imp (n c : ℕ) (x : Fin n → Bool) (h : cyc n (x ∘ rot n c) = true) :
    cyc n x = true := by
  unfold cyc at h ⊢
  rw [decide_eq_true_iff] at h ⊢
  obtain ⟨i, j, hij, hi, hj⟩ := h
  refine ⟨rot n c i, rot n c j, ?_, hi, hj⟩
  simp only [rot]
  rw [Nat.mod_add_mod, ← hij, Nat.mod_add_mod]
  congr 1; omega

theorem rot_inv (n c : ℕ) (hc : c ≤ n) (i : Fin n) : rot n c (rot n (n - c) i) = i := by
  apply Fin.ext
  simp only [rot]
  rw [Nat.mod_add_mod, show i.val + (n - c) + c = i.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.2]

theorem cyc_rot (n c : ℕ) (hc : c ≤ n) (x : Fin n → Bool) : cyc n (x ∘ rot n c) = cyc n x := by
  rw [Bool.eq_iff_iff]
  refine ⟨cyc_rot_imp n c x, fun h => cyc_rot_imp n (n - c) (x ∘ rot n c) ?_⟩
  have e : (x ∘ rot n c) ∘ rot n (n - c) = x := by
    funext i; simp only [Function.comp_apply, rot_inv n c hc]
  rw [e]; exact h

theorem cyc_eq_path_or (m : ℕ) (hm : 2 ≤ m) (x : Fin (m + 1) → Bool) :
    cyc (m + 1) x = (pathB (List.ofFn x) m ||
      (ext x m && (ext x (m - 1) || ext x 0))) := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, Bool.or_eq_true, pathB_iff, Bool.and_eq_true,
    Bool.or_eq_true]
  simp only [getD_ofFn_ext]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases h3 : i + 1 < m
    · rw [if_neg (by omega)] at h2
      exact Or.inl ⟨i, h3, h1, h2⟩
    · by_cases h4 : i = m
      · subst h4; rw [if_pos rfl] at h2
        exact Or.inr ⟨h1, Or.inr h2⟩
      · rw [if_neg (by omega), show i + 1 = m by omega] at h2
        rw [show i = m - 1 by omega] at h1
        exact Or.inr ⟨h2, Or.inl h1⟩
  · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2 | h2⟩)
    · exact ⟨i, by omega, h1, by rw [if_neg (by omega)]; exact h2⟩
    · exact ⟨m - 1, by omega, h2, by rw [if_neg (by omega), show m - 1 + 1 = m by omega]; exact h1⟩
    · exact ⟨m, by omega, h1, by rw [if_pos rfl]; exact h2⟩

theorem cyc_upper (n s : ℕ) (hn : 3 ≤ n) (h : n + (n + 1) / 2 ≤ s + 1) :
    HasCircuitSize n (cyc n) s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨gs, out, ok, len, hout, ev⟩ := pathGates m (by omega) (m + 1) (by omega)
  refine ⟨⟨gs ++ [⟨GateOp.or, [m - 1, 0]⟩, ⟨GateOp.and, [m, m + 1 + gs.length]⟩,
    ⟨GateOp.or, [out, m + 1 + gs.length + 1]⟩], m + 1 + gs.length + 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ok g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [Ok]
  · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x
    simp only [Circuit.eval, wires_eq]
    rw [wiresFrom_append]
    set w := List.ofFn x with hw
    have hwl : w.length = m + 1 := by simp [hw]
    set v := wiresFrom gs w with hv
    have lv : v.length = m + 1 + gs.length := by rw [hv, length_wiresFrom, hwl]
    have e : ∀ i, i < m + 1 → v.getD i false = w.getD i false := by
      intro i hi; rw [hv, getD_wiresFrom _ _ _ (by omega)]
    rw [← lv, three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      e (m - 1) (by omega), e m (by omega), e 0 (by omega), hv, ev w hwl,
      cyc_eq_path_or m (by omega) x, hw]
    simp only [getD_ofFn_ext]

theorem ext_snoc (m : ℕ) (y : Fin m → Bool) (b : Bool) (j : ℕ) :
    ext (Fin.snoc y b : Fin (m + 1) → Bool) j =
      if j < m then ext y j else if j = m then b else false := by
  unfold ext
  by_cases h1 : j < m
  · rw [dif_pos (by omega), if_pos h1, dif_pos h1]
    simp [Fin.snoc, h1]
  · rw [if_neg h1]
    by_cases h2 : j = m
    · subst h2; rw [dif_pos (by omega), if_pos rfl]
      simp [Fin.snoc]
    · rw [dif_neg (by omega), if_neg h2]

theorem cyc_snoc_false (m : ℕ) (y : Fin m → Bool) :
    cyc (m + 1) (Fin.snoc y false) = path m y := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, path_eq_G, G_iff]
  simp only [ext_snoc]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases a : i + 1 < m
    · simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] at h1 h2
      exact Or.inr ⟨i, Nat.zero_le _, h1, h2⟩
    · by_cases b : i = m
      · subst b; simp at h1
      · simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] at h2
        simp at h2
  · rintro (⟨i, hi, _⟩ | ⟨i, _, h1, h2⟩)
    · omega
    · have := ext_lt h2
      refine ⟨i, by omega, ?_, ?_⟩ <;> simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] <;> assumption

def tauN (m j : ℕ) : ℕ := if j = 0 then 0 else if j + 1 = m then 1 else j + 1

def tau (m : ℕ) (j : Fin m) : Fin m := ⟨tauN m j.val % m, Nat.mod_lt _ (by have := j.2; omega)⟩

theorem ext_tau (m : ℕ) (hm : 2 ≤ m) (z : Fin m → Bool) (j : ℕ) :
    ext (z ∘ tau m) j = if j < m then ext z (tauN m j) else false := by
  unfold ext
  by_cases h1 : j < m
  · have ht : tauN m j < m := by unfold tauN; split_ifs <;> omega
    rw [dif_pos h1, if_pos h1, dif_pos ht]
    simp only [Function.comp_apply, tau, Nat.mod_eq_of_lt ht]
  · rw [dif_neg h1, if_neg h1]

theorem cyc_snoc_true (m : ℕ) (hm : 3 ≤ m) (z : Fin m → Bool) :
    cyc (m + 1) (Fin.snoc (z ∘ tau m) true) = G m 2 z := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, G_iff]
  simp only [ext_snoc, ext_tau m (by omega)]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases h3 : i = m
    · subst h3
      simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h2
      exact Or.inl ⟨0, by omega, h2⟩
    · by_cases h4 : i + 1 = m
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1
        exact Or.inl ⟨1, by omega, h1⟩
      · by_cases h5 : i = 0
        · subst h5
          simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1
          exact Or.inl ⟨0, by omega, h1⟩
        · by_cases h6 : i + 2 = m
          · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h2
            exact Or.inl ⟨1, by omega, h2⟩
          · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1 h2
            exact Or.inr ⟨i + 1, by omega, h1, h2⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h1, h2⟩)
    · by_cases h0 : i = 0
      · subst h0
        refine ⟨m, by omega, ?_, ?_⟩ <;>
          simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] <;> assumption
      · have h1 : i = 1 := by omega
        subst h1
        refine ⟨m - 1, by omega, ?_, ?_⟩
        · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false]; exact h
        · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show m - 1 + 1 = m by omega]
    · have hl := ext_lt h2
      refine ⟨i - 1, by omega, ?_, ?_⟩
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show i - 1 + 1 = i by omega]
        exact h1
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show i - 1 + 1 = i by omega]
        exact h2

theorem cyc_false_lower (m s : ℕ)
    (h : HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y false)) s) :
    m + m / 2 ≤ s + 2 := by
  have e : (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y false)) = path m :=
    funext (cyc_snoc_false m)
  rw [e] at h
  exact path_lower m s h

theorem cyc_true_lower (m s : ℕ) (hm : 4 ≤ m)
    (h : HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y true)) s) :
    m + (m - 2) / 2 ≤ s + 2 := by
  have h' := relabel_size (tau m) _ s h
  have e : (fun x : Fin m → Bool =>
      (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y true)) (x ∘ tau m)) = G m 2 :=
    funext fun z => cyc_snoc_true m (by omega) z
  rw [e] at h'
  exact G_lower (m - 2) (by omega) 2 m s (by omega) h'

def piv (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (i : Fin (m + 1)) : Fin m :=
  ⟨((i.val + (m - v.val)) % (m + 1)) % m, Nat.mod_lt _ hm⟩

theorem restrict_last (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (b : Bool) (s : ℕ)
    (h : HasCircuitSize (m + 1) (fun x => cyc (m + 1) (Function.update x v b)) s) :
    HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y b)) s := by
  have h' := relabel_size (piv m hm v) _ s h
  have e : (fun y : Fin m → Bool =>
      (fun x => cyc (m + 1) (Function.update x v b)) (y ∘ piv m hm v))
      = fun y => cyc (m + 1) (Fin.snoc y b) := by
    funext y
    simp only
    rw [← cyc_rot (m + 1) (v.val + 1) (by omega) (Function.update (y ∘ piv m hm v) v b)]
    congr 1
    funext i
    induction i using Fin.lastCases with
    | last =>
      have hl : rot (m + 1) (v.val + 1) (Fin.last m) = v := by
        apply Fin.ext
        simp only [rot, Fin.val_last]
        rw [show m + (v.val + 1) = v.val + (m + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt v.2]
      simp only [Function.comp_apply, hl, Function.update_self, Fin.snoc_last]
    | cast j =>
      have hj := j.2
      have hv := v.2
      have hne : rot (m + 1) (v.val + 1) j.castSucc ≠ v := by
        intro hc
        have h0 := congrArg Fin.val hc
        simp only [rot, Fin.val_castSucc] at h0
        rcases lt_or_ge (j.val + (v.val + 1)) (m + 1) with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at h0; omega
        · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at h0; omega
      have hp : piv m hm v (rot (m + 1) (v.val + 1) j.castSucc) = j := by
        apply Fin.ext
        simp only [piv, rot, Fin.val_castSucc]
        rw [Nat.mod_add_mod, show j.val + (v.val + 1) + (m - v.val) = j.val + (m + 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val < m + 1), Nat.mod_eq_of_lt hj]
      simp only [Function.comp_apply, Function.update_of_ne hne, hp, Fin.snoc_castSucc]
  rw [e] at h'
  exact h'

theorem arith_false (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h3 : 3 ≤ s) :
    ¬ ((n - 1) + (n - 1) / 2 ≤ (s - 3) + 2) := by
  omega

theorem arith_true (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h4 : 4 ≤ s) :
    ¬ ((n - 1) + (n - 3) / 2 ≤ (s - 4) + 2) := by
  omega

def StmtCycCore : Prop :=
  ∀ n s : ℕ, 5 ≤ n → s + 1 < n + (n + 1) / 2 → HasCircuitSize n (cyc n) s →
    ∃ v : Fin n,
      (3 ≤ s ∧ HasCircuitSize n (fun x => cyc n (Function.update x v false)) (s - 3)) ∨
      (4 ≤ s ∧ HasCircuitSize n (fun x => cyc n (Function.update x v true)) (s - 4))

theorem cyc_exact_of_core (hcore : StmtCycCore) :
    ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + (n + 1) / 2 ≤ s + 1) := by
  intro n s hn
  constructor
  · intro h
    by_contra hlt
    have hs : s + 1 < n + (n + 1) / 2 := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨v, ⟨h3, hc⟩ | ⟨h4, hc⟩⟩ := hcore (m + 1) s hn hs h
    · have := cyc_false_lower m (s - 3) (restrict_last m (by omega) v false (s - 3) hc)
      exact arith_false (m + 1) s hn hs h3 (by simpa using this)
    · have := cyc_true_lower m (s - 4) (by omega) (restrict_last m (by omega) v true (s - 4) hc)
      exact arith_true (m + 1) s hn hs h4 (by omega)
  · exact cyc_upper n s (by omega)

end PEqualNP.MetaComplexity.Helpers.CycleSize

end

section


namespace PEqualNP.MetaComplexity.Helpers.CycleSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PathSize

def Stmt107 : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ), (∃ p : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1), (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → (∀ p q : Fin (n + 1), p ≠ q → (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool, f (Function.update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool, f (Function.update (Function.update x p (!a)) q b) = f (Function.update (Function.update x p a) q (!b)) ∧ f (Function.update (Function.update x p a) q (!b)) = f (Function.update (Function.update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s')

def sc (N i : ℕ) : ℕ := if i + 1 = N then 0 else i + 1

def pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : Fin N → Bool := fun i => decide (P i.val)

theorem cyc_pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    cyc N (pt N P) = true ↔ ∃ i, i < N ∧ P i ∧ P (sc N i) := by
  rw [cyc_iff_ext]
  have e : ∀ j, j < N → ext (pt N P) j = decide (P j) := by
    intro j hj; simp [ext, pt, hj]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hs : sc N i < N := by unfold sc; split_ifs <;> omega
    refine ⟨i, hi, ?_, ?_⟩
    · rw [e i hi] at h1; simpa using h1
    · unfold sc at hs ⊢; rw [e _ hs] at h2; simpa using h2
  · rintro ⟨i, hi, h1, h2⟩
    have hs : sc N i < N := by unfold sc; split_ifs <;> omega
    refine ⟨i, hi, ?_, ?_⟩
    · rw [e i hi]; simpa using h1
    · unfold sc at hs h2; rw [e _ hs]; simpa using h2

theorem cyc_pt_false (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ i, i < N → P i → P (sc N i) → False) : cyc N (pt N P) = false := by
  rw [← Bool.not_eq_true, cyc_pt]
  rintro ⟨i, hi, h1, h2⟩
  exact h i hi h1 h2

theorem upd_pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (p : Fin N) (v : Bool) :
    Function.update (pt N P) p v =
      pt N (fun j => (j = p.val ∧ v = true) ∨ (j ≠ p.val ∧ P j)) := by
  funext i
  by_cases h : i = p
  · subst h; simp [pt]
  · have h' : i.val ≠ p.val := fun e => h (Fin.ext e)
    rw [Function.update_of_ne h]
    simp [pt, h']

theorem cyc_dep (N : ℕ) (hN : 3 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, cyc N (Function.update x p (!x p)) ≠ cyc N x := by
  have hp := p.2
  refine ⟨pt N (fun j => j = sc N p.val), ?_⟩
  have hx : pt N (fun j => j = sc N p.val) p = false := by
    simp only [pt, decide_eq_false_iff_not]; unfold sc; split_ifs <;> omega
  have h1 : cyc N (pt N (fun j => j = sc N p.val)) = false :=
    cyc_pt_false N _ (by intro i hi h1 h2; unfold sc at h1 h2; split_ifs at h1 h2 <;> omega)
  have h2 : cyc N (pt N (fun j => (j = p.val ∧ true = true) ∨
      (j ≠ p.val ∧ j = sc N p.val))) = true := by
    rw [cyc_pt]
    exact ⟨p.val, hp, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨by unfold sc; split_ifs <;> omega, rfl⟩⟩
  rw [hx, upd_pt, Bool.not_false, h1, h2]
  decide

theorem cyc_nonconst (N : ℕ) (hN : 3 ≤ N) (p : Fin N) (b : Bool) :
    ∃ x y : Fin N → Bool,
      cyc N (Function.update x p b) ≠ cyc N (Function.update y p b) := by
  have hp := p.2
  refine ⟨pt N (fun _ => False), pt N (fun j => j = sc N p.val ∨ j = sc N (sc N p.val)), ?_⟩
  have h1 : cyc N (pt N (fun j => (j = p.val ∧ b = true) ∨ (j ≠ p.val ∧ False))) = false :=
    cyc_pt_false N _ (by
      intro i hi h1 h2
      simp only [and_false, or_false] at h1 h2
      have a1 := h1.1
      have a2 := h2.1
      unfold sc at a2; split_ifs at a2 <;> omega)
  have h2 : cyc N (pt N (fun j => (j = p.val ∧ b = true) ∨
      (j ≠ p.val ∧ (j = sc N p.val ∨ j = sc N (sc N p.val))))) = true := by
    rw [cyc_pt]
    refine ⟨sc N p.val, by unfold sc; split_ifs <;> omega, ?_, ?_⟩
    · right; exact ⟨by unfold sc; split_ifs <;> omega, Or.inl rfl⟩
    · right; exact ⟨by unfold sc; split_ifs <;> omega, Or.inr rfl⟩
  rw [upd_pt, upd_pt, h1, h2]
  decide

theorem exists_nbr (N : ℕ) (hN : 5 ≤ N) (p q : ℕ) (hp : p < N) (hq : q < N) (hpq : p ≠ q) :
    ∃ r, r < N ∧ r ≠ p ∧ r ≠ q ∧ (sc N p = r ∨ sc N r = p) ∧ sc N q ≠ r ∧ sc N r ≠ q := by
  by_cases h : q = sc N p ∨ q = sc N (sc N p)
  · refine ⟨if p = 0 then N - 1 else p - 1, ?_⟩
    unfold sc at h ⊢
    split_ifs at h ⊢ <;> omega
  · refine ⟨sc N p, ?_⟩
    unfold sc at h ⊢
    split_ifs at h ⊢ <;> omega

theorem cyc_sens (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) (c : Bool) :
    ∃ x : Fin N → Bool, cyc N (Function.update (Function.update x p true) q c) = true ∧
      cyc N (Function.update (Function.update x p false) q c) = false := by
  have hpq' : p.val ≠ q.val := fun e => hpq (Fin.ext e)
  obtain ⟨r, hr, hrp, hrq, hadj, hn1, hn2⟩ := exists_nbr N hN p.val q.val p.2 q.2 hpq'
  refine ⟨pt N (fun j => j = r), ?_, ?_⟩
  · rw [upd_pt, upd_pt, cyc_pt]
    rcases hadj with h | h
    · refine ⟨p.val, p.2, Or.inr ⟨hpq', Or.inl ⟨rfl, rfl⟩⟩, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩ <;>
        rw [h] <;> assumption
    · refine ⟨r, hr, Or.inr ⟨hrq, Or.inr ⟨hrp, rfl⟩⟩, Or.inr ⟨?_, Or.inl ⟨h, rfl⟩⟩⟩
      rw [h]; exact hpq'
  · rw [upd_pt, upd_pt]
    apply cyc_pt_false
    intro i hi h1 h2
    unfold sc at h2 hn1 hn2
    cases c <;> simp only [Bool.false_eq_true, and_false, false_or, and_true] at h1 h2 <;>
      split_ifs at h2 hn1 hn2 <;> omega

theorem cyc_no_funnel (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) :
    ¬ ∃ a b : Bool, ∀ x : Fin N → Bool,
      cyc N (Function.update (Function.update x p (!a)) q b) =
        cyc N (Function.update (Function.update x p a) q (!b)) ∧
      cyc N (Function.update (Function.update x p a) q (!b)) =
        cyc N (Function.update (Function.update x p (!a)) q (!b)) := by
  rintro ⟨a, b, h⟩
  obtain ⟨x, h1, h2⟩ := cyc_sens N hN p q hpq (!b)
  have e := (h x).2
  cases a
  · rw [Bool.not_false, h1, h2] at e; exact absurd e (by decide)
  · rw [Bool.not_true, h1, h2] at e; exact absurd e (by decide)

theorem size_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize n f s)
    (hst : s ≤ t) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem cyc_core_of_readers (h107 : Stmt107) : StmtCycCore := by
  intro N s hN hs hc
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rcases h107 n (cyc (n + 1)) s ⟨⟨0, by omega⟩, cyc_dep (n + 1) (by omega) _⟩
      (fun p _ b => cyc_nonconst (n + 1) (by omega) p b)
      (fun p q hpq _ _ => cyc_no_funnel (n + 1) hN p q hpq) hc with
    ⟨y, s', hle, hC⟩ | ⟨y, s', hle, hC⟩
  · exact ⟨y, Or.inl ⟨by omega, size_mono hC (by omega)⟩⟩
  · exact ⟨y, Or.inr ⟨by omega, size_mono hC (by omega)⟩⟩

theorem cyc_exact_of_readers (h107 : Stmt107) :
    ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + (n + 1) / 2 ≤ s + 1) :=
  cyc_exact_of_core (cyc_core_of_readers h107)

end PEqualNP.MetaComplexity.Helpers.CycleSize

end

section


theorem PEqualNP.MetaComplexity.L106 : ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔ n + (n + 1) / 2 ≤ s + 1) :=
  PEqualNP.MetaComplexity.Helpers.CycleSize.cyc_exact_of_readers PEqualNP.MetaComplexity.L107

end

section


section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.CircuitLowerBounds

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

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

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

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.CircuitLowerBounds

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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.CircuitLowerBounds

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

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

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

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

end

end PEqualNP.MetaComplexity.L575Proof.Helpers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

end PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs

end PEqualNP.MetaComplexity.L575Proof.Helpers.Forest

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

end

end PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

end PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

end PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

end PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Helpers.TableSearch

open PEqualNP.CircuitLowerBounds

end PEqualNP.MetaComplexity.L575Proof.Helpers.TableSearch

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

end PEqualNP.MetaComplexity.L575Proof.Exchange

end

section

namespace PEqualNP.MetaComplexity.L575Proof.Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.contains k)
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons, List.countP_cons]
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
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
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega

end PEqualNP.MetaComplexity.L575Proof.Exchange

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

section

variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}

end

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

section

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

end

namespace PEqualNP.MetaComplexity.L575Proof.EdgeFn

end PEqualNP.MetaComplexity.L575Proof.EdgeFn

namespace PEqualNP.Outside.Path575

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.L575Proof.Helpers

private theorem positive_of_changes_last {n s : ℕ} (f : (Fin (n+1) → Bool) → Bool) (b : Bool)
    (hd : ∃ x : Fin (n+1) → Bool, f (Function.update x (Fin.last n) (!(x (Fin.last n)))) ≠ f x)
    (hn : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (hs : HasCircuitSize (n+1) f s) : 0 < s := by
  by_contra! hz
  rcases hs with ⟨C, _, hsize, hev⟩
  have glen : C.gates.length ≤ s := hsize
  have hg : C.gates = [] := List.length_eq_zero_iff.mp (by omega)
  have e (x : Fin (n+1) → Bool) : (List.ofFn x).getD C.output false = f x := by
    simpa [Circuit.eval, Circuit.wires, hg] using hev x
  obtain ⟨x, hx⟩ := hd
  by_cases hlt : C.output < n+1
  · let i : Fin (n+1) := ⟨C.output,hlt⟩
    have read (z : Fin (n+1) → Bool) : z i = f z := by
      have hz := e z
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hlt),
        List.getElem_ofFn] at hz
      exact hz
    by_cases hi : i = Fin.last n
    · obtain ⟨u,v,huv⟩ := hn
      apply huv
      rw [←read, ←read, hi, Fin.snoc_last, Fin.snoc_last]
    · apply hx
      rw [←read, ←read, Function.update_of_ne hi]
  · have constant (z : Fin (n+1) → Bool) : false = f z := by
      simpa [List.getD, hlt] using e z
    exact hx ((constant _).symm.trans (constant _))

def terminalFun {n : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n)
    (x : Fin (n+2) → Bool) : Bool :=
  f (fun i => x i.castSucc.castSucc) ||
    (x (Fin.last n).castSucc && (x v.castSucc.castSucc || x (Fin.last (n+1))))

private def terminalRem {n : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n) (b : Bool)
    (x : Fin (n+1) → Bool) : Bool :=
  f (fun i => x i.castSucc) || (x (Fin.last n) && (x v.castSucc || b))

theorem terminal_pair {n s : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n)
    (hn : ∃ u w : Fin n → Bool, f u ≠ f w)
    (h0 : ∃ u : Fin n → Bool, u v = false ∧ f u = false)
    (h1 : ∃ u : Fin n → Bool, u v = true ∧ f u = false)
    (hs : HasCircuitSize (n+2) (terminalFun f v) s) :
    ∃ c, HasCircuitSize n f c ∧ c+3 ≤ s := by
  obtain ⟨x0,hu0,hf0⟩ := h0
  obtain ⟨x1,hu1,hf1⟩ := h1
  have hdep : ∃ x : Fin (n+2) → Bool,
      terminalFun f v (Function.update x (Fin.last (n+1)) (!(x (Fin.last (n+1))))) ≠ terminalFun f v x := by
    refine ⟨Fin.snoc (Fin.snoc x0 true) false,?_⟩
    simp [terminalFun,Function.update_of_ne,Fin.castSucc_ne_last,hu0,hf0]
  have hncb (b : Bool) : ∃ u w : Fin (n+1) → Bool,
      terminalFun f v (Fin.snoc u b) ≠ terminalFun f v (Fin.snoc w b) := by
    obtain ⟨u,w,huw⟩ := hn
    exact ⟨Fin.snoc u false,Fin.snoc w false,by simpa [terminalFun] using huw⟩
  obtain ⟨b,k,hk,hr⟩ := gate_elim_two (n+1) (terminalFun f v) s hdep hncb hs
  have hr' : HasCircuitSize (n+1) (terminalRem f v b) k := by
    change HasCircuitSize (n+1) (fun y => f (fun i => y i.castSucc) || (y (Fin.last n) && (y v.castSucc || b))) k
    simpa [terminalFun] using hr
  have hda : ∃ x : Fin (n+1) → Bool,
      terminalRem f v b (Function.update x (Fin.last n) (!(x (Fin.last n)))) ≠ terminalRem f v b x := by
    refine ⟨Fin.snoc x1 false,?_⟩
    simp [terminalRem,Function.update_of_ne,Fin.castSucc_ne_last,hu1,hf1]
  have hna : ∃ u w : Fin n → Bool,
      terminalRem f v b (Fin.snoc u false) ≠ terminalRem f v b (Fin.snoc w false) := by
    simpa [terminalRem] using hn
  have hpos := positive_of_changes_last (terminalRem f v b) false hda hna hr'
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hfinal := gate_elim n (terminalRem f v b) false c hda hna hr'
  exact ⟨c,by simpa [terminalRem] using hfinal,by omega⟩

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open scoped Classical
open PEqualNP.MetaComplexity.L575Proof.Helpers.Readers PEqualNP.MetaComplexity.L575Proof.EdgeFn

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open PEqualNP.MetaComplexity

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open PEqualNP.MetaComplexity

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open PEqualNP.MetaComplexity

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open PEqualNP.MetaComplexity

end PEqualNP.Outside.Path575

namespace PEqualNP.Outside.Path575

open scoped Classical

end PEqualNP.Outside.Path575

open PEqualNP.Outside.Path575
open PEqualNP.MetaComplexity.L575Proof

end

section


namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem restrictPayTwo {n : ℕ} {gs : List Gate} {o : ℕ} {i : Fin (n + 1)}
    (h : MClean (n + 1) gs)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      vl gs (Function.update x i false) o ≠ vl gs (Function.update y i false) o)
    {p q : ℕ} (hpq : p ≠ q) (hp : RC n gs i false p) (hq : RC n gs i false q) :
    ∃ s, s + 2 ≤ gs.length ∧
      HasMonoSize (n + 1) (fun x => vl gs (Function.update x i false) o) s := by
  classical
  have hcount := elim_count n (statAt n i false, []) gs (clean_nok _ gs h.1) {p, q} (by
    intro r hr
    have hR : RC n gs i false r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    change a < (statAt n i false).length + r
    rw [statAt_length]
    exact (h.1 r g hg).lt a ha)
  have hc2 : ({p, q} : Finset ℕ).card = 2 := by simp [hpq]
  rw [hc2] at hcount
  cases hst : stF n gs i false o with
  | const c =>
    obtain ⟨x, y, hxy⟩ := hnc
    exact False.elim (hxy ((restr_const h.1 (fun _ => rfl) i false c hst x).trans
      (restr_const h.1 (fun _ => rfl) i false c hst y).symm))
  | wire j =>
    have hc : CleanL n (passG n gs i false) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs h.1 g hg).1) (inv_at n i false _) (by intro r g hg; simp at hg)
    have hnf : NotFree (passG n gs i false) :=
      Loc.Clean.elim_mono n gs _ h.2 (by intro g hg; simp at hg)
    refine ⟨(passG n gs i false).length, by simpa [passG] using hcount, ?_⟩
    have e : (fun x : Fin (n + 1) → Bool => vl gs (Function.update x i false) o)
        = fun x => vl (passG n gs i false) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, st_val_wire n gs h.1 i false o j hst]
      rfl
    rw [e]
    exact Loc.Clean.relabel_mono (Fin.succAbove i) _ _
      (Loc.Clean.ToolOfClean_proof n (passG n gs i false) j ⟨hc, hnf⟩)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem wireAllTrue {m : ℕ} {gs : List Gate} (h : MClean m gs) :
    ∀ j, j < m + gs.length → vl gs (fun _ : Fin m => true) j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hinput : j < m
    · rw [vl_input gs _ j hinput]
    · let p := j - m
      have hp : p < gs.length := by dsimp [p]; omega
      have hjp : j = m + p := by dsimp [p]; omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_some_iff.mpr ⟨hp, rfl⟩
      rcases h.1 p g hg with ⟨hop, _⟩ | ⟨hop, a, b, ha, hb, hab⟩
      · exact False.elim (h.2 g (List.mem_of_getElem? hg) hop)
      · rw [hjp, vl_gate gs h.1 _ p g hg, hab]
        have ha' : vl gs (fun _ : Fin m => true) a = true := ih a (by omega) (by omega)
        have hb' : vl gs (fun _ : Fin m => true) b = true := ih b (by omega) (by omega)
        rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha', hb']

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem eliminateMarkedPart {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (A : Set (Fin (n + 1))) (hne : A.Nonempty)
    (hrest : ∀ i ∈ A, ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false))
    (hact : ∀ i ∈ A, ∃ x y : Fin (n + 1) → Bool, (∀ j ∉ A, x j = true) ∧
      (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ x y : Fin (n + 1) → Bool,
      x i = true ∧ y i = false ∧ x j = false ∧ y j = true ∧
      (∀ k, k ≠ i → k ≠ j → x k = y k) ∧ f x ≠ f y)
    (hs : HasMonoSize (n + 1) f s) :
    ∃ i ∈ A, ∃ t, t + 2 ≤ s ∧ HasMonoSize (n + 1) (fun x => f (Function.update x i false)) t := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨x, y, _, hxyEq, hxy⟩ := hact a ha
  have hnc : ∃ x y, f x ≠ f y := ⟨x, y, hxy⟩
  obtain ⟨gs, o, least, hsize⟩ := Loc.Clean.ToolLeast_proof _ _ _ hnc hs
  have clean := least.clean
  have computes (z : Fin (n + 1) → Bool) : vl gs z o = f z := least.2.2.1 z
  have rest (i : Fin (n + 1)) (hi : i ∈ A) :
      ∃ x y, vl gs (Function.update x i false) o ≠ vl gs (Function.update y i false) o := by
    simpa only [computes] using hrest i hi
  have notOutput (i : Fin (n + 1)) (hi : i ∈ A) : o ≠ (i : ℕ) := by
    intro ho
    obtain ⟨u, v, huv⟩ := rest i hi
    apply huv
    rw [ho, vl_input gs _ _ i.isLt, vl_input gs _ _ i.isLt]
    simp
  have readExists : ∃ p, ∃ i ∈ A, Reads gs p i := by
    by_contra! h
    apply hxy
    rw [← computes, ← computes]
    apply Loc.Wires.ToolProp_proof _ gs x y {(a : ℕ)} (o + 1) clean.1
    · intro j hj
      exact hxyEq j (by intro he; subst j; exact hj (by simp))
    · intro p g hp _ _
      exact Or.inl (fun w hw hwa => by
        have he : w = (a : ℕ) := hwa
        exact h p a ha ⟨g, hp, he ▸ hw⟩)
    · omega
    · exact notOutput a ha
  have finish (i : Fin (n + 1)) (hi : i ∈ A) {p q : ℕ}
      (hpq : p ≠ q) (hp : RC n gs i false p) (hq : RC n gs i false q) :
      ∃ i ∈ A, ∃ t, t + 2 ≤ s ∧ HasMonoSize (n + 1) (fun x => f (Function.update x i false)) t := by
    obtain ⟨t, hpay, ht⟩ := restrictPayTwo clean (rest i hi) hpq hp hq
    exact ⟨i, hi, t, by omega, by simpa only [computes] using ht⟩
  by_cases hmult : ∃ i ∈ A, ∃ p q, p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, hi, p, q, hpq, hp, hq⟩ := hmult
    exact finish i hi hpq (rc_input false hp) (rc_input false hq)
  have unique (i : Fin (n + 1)) (hi : i ∈ A) {p q : ℕ}
      (hp : Reads gs p i) (hq : Reads gs q i) : p = q := by
    by_contra h
    exact hmult ⟨i, hi, p, q, h, hp, hq⟩
  let p := Nat.find readExists
  obtain ⟨i, hi, hread⟩ := Nat.find_spec readExists
  have hp0 : ∀ q < p, ∀ j ∈ A, ¬ Reads gs q j := by
    intro q hq j hj hread'
    exact (Nat.not_lt_of_ge (Nat.find_min' readExists ⟨j, hj, hread'⟩)) hq
  obtain ⟨g, hg, hin⟩ := hread
  have hread : Reads gs p i := ⟨g, hg, hin⟩
  have hbinary : ∃ w < n + 1 + p, g.inputs = [(i : ℕ), w] ∨ g.inputs = [w, (i : ℕ)] := by
    rcases clean.1 p g hg with ⟨hop, _⟩ | ⟨_, u, v, hu, hv, hgs⟩
    · exact False.elim (clean.2 g (List.mem_of_getElem? hg) hop)
    · rw [hgs] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with he | he
      · subst u
        exact ⟨v, hv, Or.inl hgs⟩
      · subst v
        exact ⟨u, hu, Or.inr hgs⟩
  obtain ⟨w, hw, hinputs⟩ := hbinary
  have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases clean.1 p g hg with ⟨he, _⟩ | ⟨he, _⟩
    · exact False.elim (clean.2 g (List.mem_of_getElem? hg) he)
    · exact he
  rcases hgop with hand | hor
  · have hst : ∃ c, stF n gs i false (n + 1 + p) = Stat.const c := by
      have h := const_of_read n gs (statAt n i false, []) p g hg
        (clean_nok _ gs clean.1 g (List.mem_of_getElem? hg)) i hin
      have hlt : (i : ℕ) < (statAt n i false, ([] : List Gate)).1.length + p := by
        change (i : ℕ) < (statAt n i false).length + p
        rw [statAt_length]
        omega
      have hfix : fixBit g = false := by simp [fixBit, hand]
      have h' := h hlt (by rw [hfix]; exact stF_self n gs i false)
      simpa [statAt_length, stF] using h'
    obtain ⟨c, hc⟩ := hst
    have ho : o ≠ n + 1 + p := by
      intro ho
      obtain ⟨u, v, huv⟩ := rest i hi
      have he : stF n gs i false o = Stat.const c := ho ▸ hc
      exact huv ((restr_const clean.1 (fun _ => rfl) i false c he u).trans
        (restr_const clean.1 (fun _ => rfl) i false c he v).symm)
    obtain ⟨_, hlive⟩ := Loc.Removal.ToolLive_proof _ _ _ _ least hnc
    obtain ⟨q, hq⟩ := hlive p (reads_len hread) ho
    have hr := mem_rdSet.mp hq
    have hlt := reads_lt clean.1 hr
    exact finish i hi (by omega) (rc_input false hread) (rc_of_reads hr ⟨c, hc⟩)
  · have gateOr (z : Fin (n + 1) → Bool) :
        vl gs z (n + 1 + p) = (z i || vl gs z w) := by
      rw [vl_gate gs clean.1 z p g hg, hor]
      rcases hinputs with h | h <;> simp [h, GateOp.eval, Bool.or_comm, vl_input gs z _ i.isLt]
    by_cases hwA : ∃ j ∈ A, (j : ℕ) = w
    · obtain ⟨j, hj, hjeq⟩ := hwA
      have hreadj : Reads gs p j := ⟨g, hg, by
        rcases hinputs with h | h <;> simp [h, hjeq]⟩
      by_cases hji : j = i
      · subst j
        have hAlias : ∀ z : Fin (n + 1) → Bool, vl gs z (n + 1 + p) = vl gs z i := by
          intro z
          rw [gateOr, ← hjeq] 
          simp [vl_input gs z _ i.isLt]
        exact False.elim (Loc.Removal.ToolNoAlias_proof _ _ _ _ least hnc p
          (reads_len hread) i (by omega) hAlias)
      · obtain ⟨u, v, hui, hvi, huj, hvj, huv, hneq⟩ := hsep i hi j hj (Ne.symm hji)
        apply False.elim
        apply hneq
        rw [← computes, ← computes]
        apply Loc.Wires.ToolProp_proof _ gs u v {(i : ℕ), (j : ℕ)} (o + 1) clean.1
        · intro k hk
          exact huv k (by intro he; subst k; exact hk (by simp))
            (by intro he; subst k; exact hk (by simp))
        · intro q gq hgq _ _
          by_cases hqp : q = p
          · subst q
            exact Or.inr (by rw [gateOr, gateOr, ← hjeq, vl_input gs u _ j.isLt,
              vl_input gs v _ j.isLt]; simp [hui, hvi, huj, hvj])
          · refine Or.inl (fun k hk hkd => ?_)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkd
            rcases hkd with rfl | rfl
            · exact hqp (unique i hi ⟨gq, hgq, hk⟩ hread)
            · exact hqp (unique j hj ⟨gq, hgq, hk⟩ hreadj)
        · omega
        · simp [notOutput i hi, notOutput j hj]
    · obtain ⟨u, v, hu, huv, hneq⟩ := hact i hi
      let D : Set ℕ := {k | ∃ j ∈ A, (j : ℕ) = k}
      have siblingTrue (z : Fin (n + 1) → Bool) (hz : ∀ j ∉ A, z j = true) :
          vl gs z w = true := by
        rw [← wireAllTrue clean w (by have := reads_len hread; omega)]
        apply Loc.Wires.ToolProp_proof _ gs z (fun _ => true) D (n + 1 + p) clean.1
        · intro k hk
          exact hz k (fun hk' => hk ⟨k, hk', rfl⟩)
        · intro q gq hgq hq _
          exact Or.inl (fun k hk hkd => by
            obtain ⟨j, hj, he⟩ := hkd
            exact hp0 q (by omega) j hj ⟨gq, hgq, he ▸ hk⟩)
        · exact hw
        · exact hwA
      have hv : ∀ j ∉ A, v j = true := by
        intro j hj
        rw [← huv j (fun he => hj (he ▸ hi))]
        exact hu j hj
      apply False.elim
      apply hneq
      rw [← computes, ← computes]
      apply Loc.Wires.ToolProp_proof _ gs u v {(i : ℕ)} (o + 1) clean.1
      · intro j hj
        exact huv j (by intro he; subst j; exact hj (by simp))
      · intro q gq hgq _ _
        by_cases hqp : q = p
        · subst q
          exact Or.inr (by rw [gateOr, gateOr, siblingTrue u hu, siblingTrue v hv]; simp)
        · refine Or.inl (fun k hk hkd => ?_)
          have he : k = (i : ℕ) := hkd
          exact hqp (unique i hi ⟨gq, hgq, he ▸ hk⟩ hread)
      · omega
      · exact notOutput i hi

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def spoke (i : Fin 6) : Fin 10 := ⟨i.val + 4, by omega⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def ends : Fin 6 → Fin 10 × Fin 10 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def endOf (i : Fin 6) (v : Fin 10) : Prop := v = (ends i).1 ∨ v = (ends i).2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
instance endOfDecidable (i : Fin 6) (v : Fin 10) : Decidable (endOf i v) :=
  inferInstanceAs (Decidable (v = (ends i).1 ∨ v = (ends i).2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem hubBound : ∀ i : Fin 6, (ends i).1.val < 4 ∧ (ends i).2.val < 4 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem separateEnds : ∀ i j : Fin 6, i ≠ j →
    ∃ v : Fin 10, v.val < 4 ∧ endOf i v ∧ ¬ endOf j v := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem spoke_injective : Function.Injective spoke := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [spoke] at hv
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def active (D : Finset (Fin 6)) : Set (Fin 10) := {v | ∃ i ∉ D, spoke i = v}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def source (D : Finset (Fin 6)) (x : Fin 10 → Bool) : Bool :=
  decide (∃ i : Fin 6, i ∉ D ∧ x (spoke i) = true ∧
    (x (ends i).1 = true ∨ x (ends i).2 = true))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem source_true (D : Finset (Fin 6)) (x : Fin 10 → Bool) :
    source D x = true ↔ ∃ i : Fin 6, i ∉ D ∧ x (spoke i) = true ∧
      ∃ v : Fin 10, endOf i v ∧ x v = true := by
  rw [source, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hsp, hu | hv⟩
    · exact ⟨i, hi, hsp, (ends i).1, Or.inl rfl, hu⟩
    · exact ⟨i, hi, hsp, (ends i).2, Or.inr rfl, hv⟩
  · rintro ⟨i, hi, hsp, v, hv, ht⟩
    rcases hv with hv | hv
    · exact ⟨i, hi, hsp, Or.inl (hv ▸ ht)⟩
    · exact ⟨i, hi, hsp, Or.inr (hv ▸ ht)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem hub_not_active {D : Finset (Fin 6)} {v : Fin 10} (hv : v.val < 4) :
    v ∉ active D := by
  rintro ⟨i, _, hi⟩
  have h := congrArg Fin.val hi
  simp only [spoke] at h
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem end_not_spoke {i j : Fin 6} {v : Fin 10} (hv : endOf i v) : v ≠ spoke j := by
  have hlt : v.val < 4 := by
    rcases hv with hv | hv
    · exact hv.symm ▸ (hubBound i).1
    · exact hv.symm ▸ (hubBound i).2
  intro e
  simp [e, spoke] at hlt

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem restrictSource (D : Finset (Fin 6)) (i : Fin 6) (x : Fin 10 → Bool) :
    source D (Function.update x (spoke i) false) = source (insert i D) x := by
  apply Bool.eq_iff_iff.mpr
  rw [source_true, source_true]
  constructor
  · rintro ⟨j, hj, hsp, v, hv, hbit⟩
    have hji : j ≠ i := by intro h; subst j; simp at hsp
    have hs : spoke j ≠ spoke i := fun h => hji (spoke_injective h)
    exact ⟨j, by simp [hji, hj], by simpa [Function.update_of_ne hs] using hsp,
      v, hv, by simpa [Function.update_of_ne (end_not_spoke hv)] using hbit⟩
  · rintro ⟨j, hj, hsp, v, hv, hbit⟩
    obtain ⟨hji, hj⟩ : j ≠ i ∧ j ∉ D := by simpa using hj
    have hs : spoke j ≠ spoke i := fun h => hji (spoke_injective h)
    exact ⟨j, hj, by simpa [Function.update_of_ne hs] using hsp,
      v, hv, by simpa [Function.update_of_ne (end_not_spoke hv)] using hbit⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem hasRemaining (D : Finset (Fin 6)) (hD : D.card ≤ 2) : ∃ i, i ∉ D := by
  by_contra! h
  have hu : D = Finset.univ := Finset.eq_univ_of_forall h
  simp [hu] at hD

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem sourceZero (D : Finset (Fin 6)) : source D (fun _ => false) = false := by
  apply Bool.eq_false_iff.mpr
  simp [source_true]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem sourceOne (D : Finset (Fin 6)) (hD : D.card ≤ 2) :
    source D (fun _ => true) = true := by
  obtain ⟨i, hi⟩ := hasRemaining D hD
  exact (source_true _ _).mpr ⟨i, hi, rfl, (ends i).1, Or.inl rfl, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem removeSpoke {s : ℕ} (D : Finset (Fin 6)) (hD : D.card ≤ 1)
    (hs : HasMonoSize 10 (source D) s) :
    ∃ i ∉ D, ∃ t, t + 2 ≤ s ∧ HasMonoSize 10 (source (insert i D)) t := by
  classical
  let A := active D
  obtain ⟨i₀, hi₀⟩ := hasRemaining D (by omega)
  have hne : A.Nonempty := ⟨spoke i₀, i₀, hi₀, rfl⟩
  have hrest : ∀ i ∈ A, ∃ x y, source D (Function.update x i false) ≠
      source D (Function.update y i false) := by
    rintro _ ⟨i, _, rfl⟩
    have hc : (insert i D).card ≤ 2 := le_trans (Finset.card_insert_le i D) (by omega)
    exact ⟨fun _ => false, fun _ => true, by
      rw [restrictSource, restrictSource, sourceZero, sourceOne _ hc]
      decide⟩
  have hact : ∀ i ∈ A, ∃ x y : Fin 10 → Bool, (∀ j ∉ A, x j = true) ∧
      (∀ j, j ≠ i → x j = y j) ∧ source D x ≠ source D y := by
    rintro _ ⟨i, hi, rfl⟩
    let x : Fin 10 → Bool := fun j => decide (j ∉ A)
    let y := Function.update x (spoke i) true
    have hzero : source D x = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨j, hj, hsp, _⟩ := (source_true D x).mp htrue
      exact (of_decide_eq_true hsp) ⟨j, hj, rfl⟩
    have hone : source D y = true := by
      have hup : (ends i).1 ∉ A := hub_not_active (hubBound i).1
      have hneq : (ends i).1 ≠ spoke i := end_not_spoke (Or.inl rfl)
      exact (source_true _ _).mpr ⟨i, hi, by simp [y], (ends i).1, Or.inl rfl,
        by simp [x, y, Function.update_of_ne hneq, hup]⟩
    exact ⟨x, y, fun j hj => by simp [x, hj], fun j hj => by simp [y, Function.update_of_ne hj],
      by simp [hzero, hone]⟩
  have hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ x y : Fin 10 → Bool,
      x i = true ∧ y i = false ∧ x j = false ∧ y j = true ∧
      (∀ k, k ≠ i → k ≠ j → x k = y k) ∧ source D x ≠ source D y := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
    have hij' : i ≠ j := fun e => hij (congrArg spoke e)
    obtain ⟨h, hhub, hih, hjh⟩ := separateEnds i j hij'
    have hni : h ≠ spoke i := end_not_spoke hih
    have hnj : h ≠ spoke j := end_not_spoke hih
    let x : Fin 10 → Bool := fun k => decide (k = h ∨ k = spoke i)
    let y : Fin 10 → Bool := fun k => decide (k = h ∨ k = spoke j)
    have hx : source D x = true :=
      (source_true _ _).mpr ⟨i, hi, by simp [x], h, hih, by simp [x]⟩
    have hy : source D y = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨k, _, hs, v, hv, hy⟩ := (source_true D y).mp htrue
      have hhsp : spoke k ≠ h := by
        intro e
        have e' := congrArg Fin.val e
        simp only [spoke] at e'
        omega
      have hkj : k = j := spoke_injective (by simpa [y, hhsp] using hs)
      subst k
      have he : v = h := by simpa [y, end_not_spoke hv] using hy
      exact hjh (he ▸ hv)
    refine ⟨x, y, by simp [x], by simp [y, hni.symm, hij], by simp [x, hnj.symm, hij.symm],
      by simp [y], ?_, by simp [hx, hy]⟩
    intro k hki hkj
    simp [x, y, hki, hkj]
  obtain ⟨v, ⟨i, hi, rfl⟩, t, ht, h⟩ :=
    eliminateMarkedPart A hne hrest hact hsep hs
  have he : (fun x => source D (Function.update x (spoke i) false)) = source (insert i D) :=
    funext (restrictSource D i)
  rw [he] at h
  exact ⟨i, hi, t, ht, h⟩

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def relabelResidual (i j : Fin 6) : Fin 10 → Fin 8 :=
  match (min i.val j.val, max i.val j.val) with
  | (0, 1) => ![7, 2, 4, 0, 0, 0, 6, 3, 1, 5]
  | (0, 2) => ![7, 2, 0, 4, 0, 6, 0, 1, 3, 5]
  | (0, 3) => ![2, 7, 4, 0, 0, 3, 1, 0, 6, 5]
  | (0, 4) => ![2, 7, 0, 4, 0, 1, 3, 6, 0, 5]
  | (0, 5) => ![0, 4, 2, 6, 0, 1, 7, 3, 5, 0]
  | (1, 2) => ![7, 0, 2, 4, 6, 0, 0, 1, 5, 3]
  | (1, 3) => ![2, 4, 7, 0, 3, 0, 1, 0, 5, 6]
  | (1, 4) => ![0, 2, 4, 6, 1, 0, 7, 3, 0, 5]
  | (1, 5) => ![2, 0, 7, 4, 1, 0, 3, 6, 5, 0]
  | (2, 3) => ![0, 2, 6, 4, 1, 7, 0, 0, 3, 5]
  | (2, 4) => ![2, 4, 0, 7, 3, 1, 0, 5, 0, 6]
  | (2, 5) => ![2, 0, 4, 7, 1, 3, 0, 5, 6, 0]
  | (3, 4) => ![0, 7, 2, 4, 6, 1, 5, 0, 0, 3]
  | (3, 5) => ![0, 2, 7, 4, 1, 6, 5, 0, 3, 0]
  | (4, 5) => ![0, 2, 4, 7, 1, 5, 6, 3, 0, 0]
  | _ => fun _ => 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def tailCase (i j : Fin 6) : Bool :=
  decide ((ends i).1 = (ends j).1 ∨ (ends i).1 = (ends j).2 ∨
    (ends i).2 = (ends j).1 ∨ (ends i).2 = (ends j).2)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def modelOriented (tail : Bool) (a b : Fin 8) : Prop :=
  if tail then
    (a.val < 6 ∧ b.val < 6 ∧ (a.val + 1) % 6 = b.val) ∨
      (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 7)
  else
    (a.val + 1) % 8 = b.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
instance modelOrientedDecidable (tail : Bool) (a b : Fin 8) :
    Decidable (modelOriented tail a b) := by
  unfold modelOriented
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def mapped (i j : Fin 6) (a b : Fin 8) : Prop :=
  ∃ k : Fin 6, k ≠ i ∧ k ≠ j ∧ ∃ h : Fin 10, endOf k h ∧
    ((relabelResidual i j (spoke k) = a ∧ relabelResidual i j h = b) ∨
     (relabelResidual i j (spoke k) = b ∧ relabelResidual i j h = a))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
instance mappedDecidable (i j : Fin 6) (a b : Fin 8) :
    Decidable (mapped i j a b) := by
  unfold mapped
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem residualEdges : ∀ i j : Fin 6, i ≠ j → ∀ a b : Fin 8,
    mapped i j a b ↔ modelOriented (tailCase i j) a b ∨ modelOriented (tailCase i j) b a := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def cycleFunction (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def residualModel (tail : Bool) (x : Fin 8 → Bool) : Bool :=
  if tail then PEqualNP.Outside.Path575.terminalFun (cycleFunction 6) (0 : Fin 6) x
  else cycleFunction 8 x

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem residualModel_true (tail : Bool) (x : Fin 8 → Bool) :
    residualModel tail x = true ↔ ∃ a b : Fin 8, modelOriented tail a b ∧ x a = true ∧ x b = true := by
  cases tail
  · simp [residualModel, cycleFunction, modelOriented]
  · simp only [residualModel, ite_true, PEqualNP.Outside.Path575.terminalFun,
      Bool.or_eq_true, Bool.and_eq_true, cycleFunction, decide_eq_true_eq]
    constructor
    · rintro (⟨a, b, hab, ha, hb⟩ | ⟨ha, hb | hb⟩)
      · refine ⟨a.castSucc.castSucc, b.castSucc.castSucc, ?_, ha, hb⟩
        exact Or.inl ⟨a.isLt, b.isLt, hab⟩
      · exact ⟨0, 6, Or.inr (Or.inl ⟨rfl, rfl⟩), hb, ha⟩
      · exact ⟨6, 7, Or.inr (Or.inr ⟨rfl, rfl⟩), ha, hb⟩
    · rintro ⟨a, b, h, ha, hb⟩
      change (a.val < 6 ∧ b.val < 6 ∧ (a.val + 1) % 6 = b.val) ∨
        (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 7) at h
      rcases h with ⟨alt, blt, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨⟨a.val, alt⟩, ⟨b.val, blt⟩, hab, ha, hb⟩
      · exact Or.inr ⟨hb, Or.inl ha⟩
      · exact Or.inr ⟨ha, Or.inr hb⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem residualValue {i j : Fin 6} (hne : i ≠ j) (x : Fin 8 → Bool) :
    source {i, j} (x ∘ relabelResidual i j) = residualModel (tailCase i j) x := by
  apply Bool.eq_iff_iff.mpr
  rw [source_true, residualModel_true]
  constructor
  · rintro ⟨k, hk, hs, h, hh, ht⟩
    have hn : k ≠ i ∧ k ≠ j := by simpa using hk
    have hm : mapped i j (relabelResidual i j (spoke k)) (relabelResidual i j h) :=
      ⟨k, hn.1, hn.2, h, hh, Or.inl ⟨rfl, rfl⟩⟩
    rcases (residualEdges i j hne _ _).mp hm with he | he
    · exact ⟨_, _, he, hs, ht⟩
    · exact ⟨_, _, he, ht, hs⟩
  · rintro ⟨a, b, he, ha, hb⟩
    obtain ⟨k, hi, hj, h, hh, he | he⟩ :=
      (residualEdges i j hne a b).mpr (Or.inl he)
    · exact ⟨k, by simp [hi, hj], by simpa only [Function.comp_apply, he.1] using ha,
        h, hh, by simpa only [Function.comp_apply, he.2] using hb⟩
    · exact ⟨k, by simp [hi, hj], by simpa only [Function.comp_apply, he.1] using hb,
        h, hh, by simpa only [Function.comp_apply, he.2] using ha⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem residualLower {s : ℕ} {tail : Bool} (h : HasCircuitSize 8 (residualModel tail) s) :
    11 ≤ s := by
  cases tail
  · have h' : HasCircuitSize 8 (cycleFunction 8) s := h
    have hs := (PEqualNP.MetaComplexity.L106 8 s (by decide)).mp h'
    norm_num at hs
    omega
  · have h' : HasCircuitSize (6 + 2)
        (PEqualNP.Outside.Path575.terminalFun (cycleFunction 6) (0 : Fin 6)) s := h
    let x : Fin 6 → Bool := fun i => decide (i = 0 ∨ i = 1)
    let y : Fin 6 → Bool := fun _ => false
    let z : Fin 6 → Bool := fun i => decide (i = 0)
    have hx : cycleFunction 6 x = true := by decide
    have hy : cycleFunction 6 y = false := by decide
    have hz : cycleFunction 6 z = false := by decide
    obtain ⟨c, hc, hcs⟩ := PEqualNP.Outside.Path575.terminal_pair (cycleFunction 6) (0 : Fin 6)
      ⟨x, y, by simp [hx, hy]⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩ h'
    have hs := (PEqualNP.MetaComplexity.L106 6 c (by decide)).mp hc
    norm_num at hs
    omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem fullLower {s : ℕ} (h : HasMonoSize 10 (source ∅) s) : 15 ≤ s := by
  obtain ⟨j, -, t, ht, hh⟩ := removeSpoke ∅ (by decide) h
  obtain ⟨i, hi, u, hu, hhu⟩ := removeSpoke {j} (by simp) hh
  have hne : i ≠ j := by simpa using hi
  have hres := Loc.Clean.relabel_mono (relabelResidual i j) _ _ hhu
  have he : (fun x => source {i, j} (x ∘ relabelResidual i j)) = residualModel (tailCase i j) :=
    funext (residualValue hne)
  rw [he] at hres
  have := residualLower hres.has
  omega

end PequalNP583

namespace PequalNP583

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Loc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def postedEdges : List (ℕ × ℕ) :=
  [(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3),
    (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem postedEdgeEquiv : ∀ u v : Fin 10,
    ((u.val, v.val) ∈ postedEdges ∨ (v.val, u.val) ∈ postedEdges) ↔
      ∃ i : Fin 6, (u = spoke i ∧ endOf i v) ∨ (v = spoke i ∧ endOf i u) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem sourceMatches (x : Fin 10 → Bool) :
    source ∅ x = true ↔
      ∃ u v : Fin 10, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  rw [source_true]
  constructor
  · rintro ⟨i, _, hs, v, hv, ht⟩
    rcases (postedEdgeEquiv (spoke i) v).mpr ⟨i, Or.inl ⟨rfl, hv⟩⟩ with he | he
    · exact ⟨spoke i, v, he, hs, ht⟩
    · exact ⟨v, spoke i, he, ht, hs⟩
  · rintro ⟨u, v, he, hu, hv⟩
    obtain ⟨i, ⟨rfl, hend⟩ | ⟨rfl, hend⟩⟩ :=
      (postedEdgeEquiv u v).mp (Or.inl he)
    · exact ⟨i, by simp, hu, v, hend, hv⟩
    · exact ⟨i, by simp, hv, u, hend, hu⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem refutesPosted : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, hfun⟩
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
    exact ⟨by rcases hop' with h | h <;> simp [h], hlen⟩
  have hnf : NotFree C.gates := by
    intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hg).1
    rcases hop with he | he <;> simp [he]
  have exactEval (x : Fin 10 → Bool) : C.eval (List.ofFn x) = source ∅ x :=
    Bool.eq_iff_iff.mpr ((hfun x).trans (sourceMatches x).symm)
  have h := fullLower (s := 14) ⟨C, hfan, hnf, hsize, exactEval⟩
  omega

end PequalNP583


end

end PEqualNP.Outside.L_meta_720

theorem PEqualNP.Outside.L_meta_720 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∃ S : Set ℕ, ((∀ i : ℕ, i < 4 → i ∈ S) ∨ (∀ i : ℕ, 4 ≤ i → i < 10 → i ∈ S)) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j → i ∈ S → 10 + j ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ a b : ℕ, g.inputs = [a, b] → a < 10 + j → b < 10 + j → ¬ (a ∈ S ∧ b ∈ S))) → (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 15 ≤ C.size := by
  intro C hm _ hC
  by_contra! h
  exact PEqualNP.Outside.L_meta_720.PequalNP583.refutesPosted ⟨C, hm, by omega, hC⟩
