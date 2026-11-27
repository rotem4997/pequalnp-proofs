import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9191

namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp
end Maj.Helpers
namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
end Maj.Helpers
namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
abbrev Stat := Sum Bool ℕ
def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
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
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false
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
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (α := Bool) (i : ℕ)) ++ [Sum.inl (β := ℕ) b]
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Sum.inr (α := Bool) (i : ℕ))).length = n := by simp
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
end Maj.Helpers
namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
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
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)
theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]
theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega
theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega
end Maj.Helpers
namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr (α := Bool) (i : ℕ))
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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
  List.ofFn (Fin.insertNth i (Sum.inl b) (fun k : Fin n => Sum.inr (α := Bool) (k : ℕ)) : Fin (n + 1) → Stat)
theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]
theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Sum.inl false) = Sum.inl b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]
theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Sum.inl false) = Sum.inr (k : ℕ) := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]
theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
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
  · show ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Sum.inl false)
theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Sum.inl b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Sum.inl false) = _
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
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
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
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
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
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega
theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj
theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Sum.inl c
theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount
theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Sum.inl c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Sum.inl c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Sum.inl b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Sum.inl (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Sum.inl c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Sum.inl c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Sum.inl c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Sum.inl c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Sum.inl c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩
theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Sum.inl false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Sum.inl false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)
theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Sum.inl c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]
theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Sum.inl c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)
theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]
theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this
theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Sum.inl c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | inl c' => exact absurd hst (hout i b c')
  | inr j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this
theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega
theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega
end Maj.Helpers
namespace Maj.Helpers
open PEqualNP.MetaComplexity
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
theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
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
theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp
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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
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
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
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
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
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
  exact drop_core k pre g post hcl o (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Sum.inl c
theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)
theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Sum.inl c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inl c from h] at h1
  exact h1.symm
theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Sum.inr q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inr q from h] at h1
  exact h1.symm
theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Sum.inr (k : ℕ) := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Sum.inl false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k
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
        (Sum.inl false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]
theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Sum.inl c) : ∃ c, (simplify op t ins).2 = Sum.inl c := by
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
theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Sum.inl c) :
    (simplify g.op t (g.inputs.map F)).2 = Sum.inr t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpOr, hF, hF']
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
theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Sum.inl c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Sum.inr q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩
theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc
theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Sum.inl (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h
theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Sum.inl c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Sum.inl c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Sum.inl c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Sum.inl c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'
theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount
end Maj.Helpers
namespace Maj.Helpers.PermInputs
open PEqualNP.MetaComplexity
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
theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
end Maj.Helpers.PermInputs
namespace Maj.Helpers.Forest
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.PermInputs
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
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
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_9191.Maj.Helpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
end Maj.Helpers.Forest
namespace Maj.Helpers.Readers
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.PermInputs
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
def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    (∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length)

theorem Least.hcl {m f gs o} (L : Least m f gs o) : CleanL m gs := L.1
theorem Least.hev {m f gs o} (L : Least m f gs o) : ∀ x, vl gs x o = f x := L.2.1
theorem Least.hmin {m f gs o} (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o' = f x) → gs.length ≤ gs'.length := L.2.2

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
section ProofScope1
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
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end ProofScope1
theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm
theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Sum.inl c) (x : Fin (n + 1) → Bool) :
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
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | inr j =>
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
section ProofScope2
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS
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
end ProofScope2
end Maj.Helpers.Readers
namespace Maj.Helpers.Readers
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
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
section ProofScope3
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
end ProofScope3
section ProofScope4
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
end ProofScope4
end Maj.Helpers.Readers
namespace Maj.Helpers.Readers
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
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
section ProofScope5
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
end ProofScope5
end Maj.Helpers.Readers
namespace Maj.Helpers.Readers
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
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
theorem noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2
end Maj.Helpers.Readers
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1
def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩
def StmtRD : Prop :=
  ∀ (N : ℕ) (gs : List Gate) (p a : ℕ), CleanL N gs → p < gs.length → a < N + p →
    CleanL N (rdel N p a gs) ∧ (rdel N p a gs).length + 1 = gs.length ∧
    (∀ (x : Fin N → Bool) (w : ℕ), w < N + p → vl (rdel N p a gs) x w = vl gs x w) ∧
    (∀ x : Fin N → Bool, vl gs x (N + p) = vl gs x a →
      ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w)
def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))
def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j
def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))
def StmtXMove : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p p' l q h : ℕ) (g g' : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) → p < p' →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    gs[p']? = some g' → g'.op = GateOp.and → (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    ∃ (gs' : List Gate) (o' : ℕ), Least N F gs' o' ∧
      ∀ t, TailGE N F gs t → TailGE N F gs' (t + 2)
def StmtExch : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o h : ℕ) (T : Finset ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) → (∃ x y : Fin N → Bool, F x ≠ F y) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (N + r)) →
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      gs'.length + T.card ≤ gs.length + 2
def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i
def DeepHyp {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop :=
  (∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)) ∧
  (∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y') ∧
  (∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true) ∧
  (∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true) ∧
  F (fun _ => false) = false

theorem DeepHyp.nc {N F D} (H : @DeepHyp N F D) :
    ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b) := H.1
theorem DeepHyp.nf {N F D} (H : @DeepHyp N F D) :
    ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y' := H.2.1
theorem DeepHyp.win {N F D} (H : @DeepHyp N F D) :
    ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
      ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
        F (Function.update x' y true) = true := H.2.2.1
theorem DeepHyp.mono {N F D} (H : @DeepHyp N F D) :
    ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true := H.2.2.2.1
theorem DeepHyp.zero {N F D} (H : @DeepHyp N F D) : F (fun _ => false) = false := H.2.2.2.2

def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩
def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅
def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)
def Front {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ) : Prop :=
  gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (g.inputs = [l, h] ∨ g.inputs = [h, l]) ∧ y ∈ D ∧ IsLit N gs y l ∧ DFree D gs h
def StmtFront : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p
def StmtWin : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and →
      (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true) ∧ n + 1 ≤ h)
def StmtTwo : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r
def StmtAnd : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ) (g : Gate)
    (y : Fin (n + 1)),
    Least (n + 1) F gs o →
    (∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b)) →
    Dep F y → gs[p]? = some g → g.op = GateOp.and →
    (g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) → IsLit (n + 1) gs y l →
    ph < gs.length → (∀ t, Reads gs t (n + 1 + ph) → t = p) →
    o ≠ n + 1 + p → o ≠ n + 1 + ph →
    (l = (y : ℕ) → Drop F y false 3 gs.length) ∧
    (l ≠ (y : ℕ) → Drop F y true 4 gs.length)
def StmtExt : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)
def StmtML : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')
def StmtLB : Prop :=
  ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
    (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length) →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) →
    (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s →
    A.card + G.edgeSet.ncard + k ≤ s + 1
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega
theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]
theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega
theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]
theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]
theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]
theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega
theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩
theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)
theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]
theorem stmtRD : StmtRD := by
  intro N gs p a hcl hp ha
  exact ⟨rdel_clean N p a gs hcl hp ha, rdel_length N p a gs hp,
    fun x w hw => rdel_prefix N p a gs hcl hp ha x w hw,
    fun x hx w => rdel_all N p a gs hcl hp ha x hx w⟩
theorem TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩
theorem TailGE.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t t' : ℕ}
    (h : TailGE N F gs t) (ht : t' ≤ t) : TailGE N F gs t' :=
  ⟨le_trans ht h.1, fun j h1 h2 => h.2 j (by omega) h2⟩
theorem TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1
theorem TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)
theorem tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx
theorem least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem deepHyp_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩
theorem deepHyp_dep {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  have h0 : F (zeroOn D (fun _ => false)) = false := by
    have : zeroOn D (fun _ : Fin N => false) = fun _ => false := by
      funext i; simp [zeroOn]
    rw [this]; exact hD.zero
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy _ h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp
theorem least_len {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs' : List Gate} {o o' : ℕ}
    (L : Least N F gs o) (L' : Least N F gs' o') : gs.length = gs'.length :=
  le_antisymm (L.hmin gs' o' L'.hcl L'.hev) (L'.hmin gs o L.hcl L.hev)
theorem vl_bin {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) :
    (g.op = GateOp.or → vl gs x (N + p) = (vl gs x l || vl gs x h)) ∧
    (g.op = GateOp.and → vl gs x (N + p) = (vl gs x l && vl gs x h)) := by
  rw [vl_gate gs hcl x p g hg]
  constructor <;> intro hop <;> rw [hop] <;>
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm, Bool.and_comm]
theorem not_tailOK_or {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin (n + 1)} {l h : ℕ}
    (hD : DeepHyp F D) (L : Least (n + 1) F gs o) (hf : Front D gs p g y l h)
    (hop : g.op = GateOp.or) : ¬ TailOK (n + 1) F gs p := by
  obtain ⟨hg, -, hin, hy, hlit, -⟩ := hf
  rintro ⟨g', hg', hop' | ⟨-, hbel⟩⟩
  · rw [hg] at hg'; cases hg'; rw [hop] at hop'; cases hop'
  · rw [hg] at hg'; cases hg'
    have key : ∀ b : Bool, (∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true) → False := by
      intro b hb
      obtain ⟨x, x', hne⟩ := hD.nc y hy b
      have : ∀ z : Fin (n + 1) → Bool, F (Function.update z y b) = true := by
        intro z
        apply hbel
        rw [(vl_bin gs L.hcl _ p l h g hg hin).1 hop, hb _ (by simp)]
        rfl
      exact hne (by rw [this, this])
    rcases hlit with rfl | ⟨pn, rfl, hpn⟩
    · apply key true
      intro x hx
      rw [vl_input gs x y y.isLt]
      simpa using hx
    · apply key false
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]
      simpa using hx
theorem stmtExt (hLift : StmtLift) (hX : StmtXMove) (hFront : StmtFront) (hWin : StmtWin)
    (hTwo : StmtTwo) : StmtExt := by
  classical
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs0, o0, L0, hl0⟩ := exists_least (n + 1) F s hnc hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧
    TailGE (n + 1) F gs t
  have hP0 : P 0 := ⟨gs0, o0, L0, TailGE.zero _ _ _⟩
  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o, L, ht⟩
    exact (least_len L L0) ▸ ht.le
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  refine ⟨gs, o, L, by rw [least_len L L0]; exact hl0, ?_⟩
  by_contra hstop
  push Not at hstop
  obtain ⟨hone, hnoand⟩ := hstop
  obtain ⟨p, g, y, l, h, hf, hop⟩ := hFront n F D gs o hD hne L hone
  have hw := hWin n F D gs o p g y l h hD L hone hf
  obtain ⟨hg, hor, hin, -, -, -⟩ := id hf
  rcases hor with hand | hor
  ·
    obtain ⟨hbel, hhN⟩ := hw.2 hand
    obtain ⟨t, htr, htp⟩ := hnoand p g y l h hf hand hhN hop
    obtain ⟨r, g', q, hrp, hg', hand', hin', -⟩ :=
      hTwo n F D gs o p g y l h hD L hone hf hand ⟨t, htp, htr⟩
    obtain ⟨gs', o', L', ht'⟩ : P (M + 2) := by
      rcases lt_or_gt_of_ne hrp with hlt | hlt
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o r p q l h g' g L hnc hlt hg' hand' hin' hg hand hin hbel
        exact ⟨gs', o', L', ht' M ht⟩
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o p r l q h g g' L hnc hlt hg hand hin hg' hand' hin' hbel
        exact ⟨gs', o', L', ht' M ht⟩
    have := hmax _ ⟨gs', o', L', ht'⟩
    omega
  ·
    have hbel := hw.1 hor
    obtain ⟨L', ht'⟩ := hLift (n + 1) F gs o p l h g L hnc hg hor hin hbel
    have := hmax _ ⟨_, _, L', ht' (not_tailOK_or hD L hf hor) M ht⟩
    omega
theorem stmtML (hAnd : StmtAnd) (hExt : StmtExt) : StmtML := by
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs, o, L, hls, halt⟩ := hExt n F D s hD hne hs
  rcases halt with hone | ⟨p, g, y, l, h, hf, hand, hhN, hop, honly⟩
  · simp only [OneReader, not_and_or] at hone
    push Not at hone
    rcases hone with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · refine ⟨y, hy, ?_⟩
      rcases L.two_readers y (hD.nc y hy) p q hpq hp hq with
        ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
      · exact Or.inl (h3.mono le_rfl hls)
      · exact Or.inl (h4.mono (by omega) hls)
      · exact Or.inr (h4.mono le_rfl hls)
    · refine ⟨y, hy, Or.inl ?_⟩
      exact (L.not_two_readers y (hD.nc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1.mono
        le_rfl hls
  · obtain ⟨hg, -, hin, hy, hlit, hfree⟩ := hf
    refine ⟨y, hy, ?_⟩
    have hrd : Reads gs p h := ⟨g, hg, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hhlt := reads_lt L.hcl hrd
    have hplt := reads_len hrd
    have hdep := deepHyp_dep hD hy
    have hoh : o ≠ h := by
      rintro rfl
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (by
          intro k hk
          have : k ≠ y := fun e => hfree y hy (e ▸ hk)
          simp [Function.update_of_ne this])
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
    have hA := hAnd n F gs o p ph l g y L (hD.nc y hy) hdep hg hand hin hlit (by omega)
      honly hop hoh
    by_cases hl : l = (y : ℕ)
    · exact Or.inl ((hA.1 hl).mono le_rfl hls)
    · exact Or.inr ((hA.2 hl).mono le_rfl hls)
end Maj.EdgeFn
namespace Maj.Helpers.TableSearch
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0
def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]
def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0
def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]
theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]
theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))
def cands (M : ℕ) (S : List ℕ) : List ℕ :=
  M :: 0 :: ((0 :: S).map (fun a => M ^^^ a) ++ (0 :: S) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a &&& b) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a ||| b))
def nub : List ℕ → List ℕ
  | [] => []
  | a :: l => if (nub l).contains a then nub l else a :: nub l
theorem mem_nub (x : ℕ) : ∀ l : List ℕ, x ∈ nub l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · rename_i h
      simp only [List.contains_iff_mem] at h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> [exact (ih.1 h); exact h']
    · simp [ih]
def next (M : ℕ) (S : List ℕ) : List ℕ :=
  nub ((cands M S).filter fun t => !(S.contains t))
def reach (M : ℕ) (good : ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => (0 :: S).any good
  | k + 1, S => (0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])
theorem cands_mono (M : ℕ) (S S' : List ℕ) (h : ∀ x, x ∈ S → x ∈ S') (t : ℕ)
    (ht : t ∈ cands M S) : t ∈ cands M S' := by
  have h0 : ∀ x, x ∈ (0 :: S) → x ∈ (0 :: S') := by
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · simp [hx]
    · exact List.mem_cons_of_mem _ (h x hx)
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at ht
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases ht with ht | ht | ((⟨a, ha, e⟩ | ht) | ⟨a, ha, b, hb, e⟩) | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨a, ?_, e⟩))))
    have := h0 a (by simpa using ha); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ?_))))
    have := h0 t (by simpa using ht); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ?_, b, ?_, e⟩)))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
  · refine Or.inr (Or.inr (Or.inr ⟨a, ?_, b, ?_, e⟩))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
theorem mem_next (M : ℕ) (S : List ℕ) (t : ℕ) : t ∈ next M S ↔ t ∈ cands M S ∧ t ∉ S := by
  simp [next, mem_nub]
theorem any_congr_mem (l l' : List ℕ) (f f' : ℕ → Bool) (hl : ∀ x, x ∈ l ↔ x ∈ l')
    (hf : ∀ x, f x = f' x) : l.any f = l'.any f' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).1 hx, by rw [← hf]; exact e⟩
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).2 hx, by rw [hf]; exact e⟩
theorem reach_congr (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S S' : List ℕ),
    (∀ x, x ∈ S ↔ x ∈ S') → reach M good k S = reach M good k S' := by
  intro k
  induction k with
  | zero =>
    intro S S' h
    simp only [reach]
    exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
  | succ k ih =>
    intro S S' h
    simp only [reach]
    congr 1
    · exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
    · apply any_congr_mem
      · intro x
        rw [mem_next, mem_next]
        exact ⟨fun ⟨a, b⟩ => ⟨cands_mono M S S' (fun y => (h y).1) x a, by rwa [← h]⟩,
          fun ⟨a, b⟩ => ⟨cands_mono M S' S (fun y => (h y).2) x a, by rwa [h]⟩⟩
      · intro t
        exact ih _ _ (by intro x; simp [h])
theorem reach_of_zero (M : ℕ) (good : ℕ → Bool) (S : List ℕ) (h : reach M good 0 S = true) :
    ∀ k, reach M good k S = true := by
  intro k
  cases k with
  | zero => exact h
  | succ k => simp only [reach] at h ⊢; simp [h]
theorem reach_succ (M : ℕ) (good : ℕ → Bool) (k : ℕ) (S : List ℕ) :
    reach M good (k + 1) S
      = ((0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])) := rfl
theorem reach_mono (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S : List ℕ),
    reach M good k S = true → reach M good (k + 1) S = true := by
  intro k
  induction k with
  | zero => intro S h; exact reach_of_zero M good S h 1
  | succ k ih =>
    intro S h
    rw [reach_succ M good k S] at h
    rw [reach_succ M good (k + 1) S]
    simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨t, ht, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, ih _ e⟩
theorem getD_mem_zero (S : List ℕ) (o : ℕ) : S.getD o 0 ∈ (0 :: S) := by
  rw [List.getD_eq_getElem?_getD]
  cases hs : S[o]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hs)
theorem mem_cands_not (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) :
    M ^^^ a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ha)))))
theorem mem_cands_copy (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) : a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))
theorem mem_cands_and (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a &&& b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩))))
theorem mem_cands_or (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a ||| b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩)))
theorem gt_mem (M : ℕ) (S : List ℕ) (g : Gate) (hg : GOk g) :
    gt M g.op (g.inputs.map fun i => S.getD i 0) ∈ cands M S := by
  obtain ⟨hop, hl⟩ := hg
  have hm : ∀ i, S.getD i 0 ∈ (0 :: S) := getD_mem_zero S
  generalize g.inputs = ins at hl ⊢
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp [gt, cands]
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_not M S _ (hm i)
  | [i, j], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_and M S _ _ (hm i) (hm j)
    · exact mem_cands_or M S _ _ (hm i) (hm j)
    · exact mem_cands_not M S _ (hm i)
theorem reach_sound (M : ℕ) (good : ℕ → Bool) : ∀ (gs : List Gate) (k : ℕ) (S : List ℕ)
    (o : ℕ), gs.length ≤ k → (∀ g ∈ gs, GOk g) → good ((tabs M S gs).getD o 0) = true →
    reach M good k S = true := by
  intro gs
  induction gs with
  | nil =>
    intro k S o _ _ hgood
    apply reach_of_zero
    simp only [reach, List.any_eq_true]
    exact ⟨_, getD_mem_zero S o, hgood⟩
  | cons g gs ih =>
    intro k S o hk hok hgood
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hok g (by simp)
    set t := gt M g.op (g.inputs.map fun i => S.getD i 0) with ht
    have h1 : reach M good k' (S ++ [t]) = true :=
      ih k' (S ++ [t]) o (by simpa using hk) (fun g' hg' => hok g' (by simp [hg'])) hgood
    by_cases hin : t ∈ S
    · have e : reach M good k' (S ++ [t]) = reach M good k' S :=
        reach_congr M good k' _ _ (by intro x; simp only [List.mem_append, List.mem_singleton]
                                      constructor
                                      · rintro (h | rfl) <;> assumption
                                      · exact Or.inl)
      exact reach_mono M good k' S (e ▸ h1)
    · simp only [reach, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨t, (mem_next M S t).2 ⟨gt_mem M S g hg, hin⟩, h1⟩
theorem mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))
theorem lower_of_search (n B : ℕ) (f : (Fin n → Bool) → Bool) (T0 : List ℕ) (tgt k : ℕ)
    (htgt : tgt < 2 ^ B)
    (hpt : ∀ p, p < B → ∃ x : Fin n → Bool, List.ofFn x = T0.map (fun t => t.testBit p) ∧
      f x = tgt.testBit p)
    (hsearch : reach (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) k T0 = false) :
    ¬ HasCircuitSize n f k := by
  rintro ⟨C, hC, hsize, hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hgood : (fun t => t % 2 ^ B == tgt) ((tabs (2 ^ B - 1) T0 C.gates).getD C.output 0)
      = true := by
    simp only [beq_iff_eq]
    apply mod_eq_of_testBit B _ tgt htgt
    intro p hp
    obtain ⟨x, hx, hfx⟩ := hpt p hp
    have hM : (2 ^ B - 1).testBit p = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have := hev x
    rw [hfx] at this
    rw [← this, Circuit.eval, Circuit.wires, hx, wires_tabs _ p hM _ _ hok,
      getD_map_testBit]
  have := reach_sound (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) C.gates k T0 C.output hsize hok hgood
  rw [hsearch] at this
  exact absurd this (by decide)
end Maj.Helpers.TableSearch
namespace Maj.Exchange
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def StmtExchange : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ C.size + 2
def StmtTwoReaders : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ 2
def StmtExchangeShape : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ (D : Circuit) (k : ℕ) (σ : ℕ → ℕ) (o : ℕ),
      FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      k + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) = C.size ∧
      D.gates.length = k + 2 ∧ D.output = n + k + 1 ∧
      D.gates[k]? = some ⟨GateOp.not, [h]⟩ ∧
      D.gates[k + 1]? = some ⟨GateOp.or, [o, n + k]⟩ ∧
      StrictMono σ ∧
      (∀ i, i < k → ∃ g gD, C.gates[σ i]? = some g ∧ D.gates[i]? = some gD ∧
        gD.op = g.op ∧
        ¬ (decide (h < n + σ i) &&
          (match g.op with
           | GateOp.not => g.inputs.take 1
           | _ => g.inputs).contains h) = true ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
          (D.wires (List.ofFn x)).getD (n + i) false =
            (C.wires (List.ofFn x)).getD (n + σ i) false)
theorem twoReaders_of_exchange (hE : StmtExchange) : StmtTwoReaders := by
  intro n C h hmin hcov
  obtain ⟨D, hD, hfun, hsize⟩ := hE n C h hmin.1 hcov
  have := hmin.2 D hD hfun
  omega
def nand3C : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
theorem nand3C_hyp :
    FanInTwo nand3C ∧
    (∀ x : Fin 3 → Bool, (nand3C.wires (List.ofFn x)).getD 3 false = false →
      circuitFun 3 nand3C x = true) ∧
    nand3C.gates.zipIdx.countP (fun p => decide (3 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 3) = 1 ∧
    3 ≠ nand3C.output ∧
    (∃ x y : Fin 3 → Bool, circuitFun 3 nand3C x ≠ circuitFun 3 nand3C y) ∧
    (∃ x : Fin 3 → Bool, circuitFun 3 nand3C x ≠ !(nand3C.wires (List.ofFn x)).getD 3 false) := by
  refine ⟨?_, by decide, by decide, by decide, ⟨fun _ => true, fun _ => false, by decide⟩,
    ⟨fun i => decide (i ≠ 2), by decide⟩⟩
  intro g hg
  simp only [nand3C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.TableSearch in
theorem nand3C_minimal : IsMinimalCircuit 3 nand3C := by
  have hlow : ¬ HasCircuitSize 3 (circuitFun 3 nand3C) 2 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 127 2 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 nand3C (fun i => p.testBit i) = Nat.testBit 127 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨nand3C_hyp.1, fun D hD hfun => ?_⟩
  by_contra hlt
  exact hlow ⟨D, hD, by simp [nand3C, Circuit.size] at hlt ⊢; omega,
    fun x => congrFun hfun x⟩
def n4C : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [6]⟩,
    ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [9, 10]⟩], 11⟩
theorem n4C_hyp :
    (∀ x : Fin 5 → Bool, (n4C.wires (List.ofFn x)).getD 4 false = false →
      circuitFun 5 n4C x = true) ∧
    n4C.gates.zipIdx.countP (fun p => decide (4 < 5 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 4) = 2 := by
  refine ⟨?_, by decide⟩
  decide +kernel
def StmtTwoReadersSyntactic : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    (C.gates.filter fun g => g.inputs.contains h).length ≤ 2
def synC : Circuit :=
  ⟨[⟨GateOp.not, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5, 2]⟩], 6⟩
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.TableSearch in
theorem synC_minimal : IsMinimalCircuit 3 synC := by
  have hlow : ¬ HasCircuitSize 3 (circuitFun 3 synC) 3 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 79 3 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 synC (fun i => p.testBit i) = Nat.testBit 79 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨?_, fun D hD hfun => ?_⟩
  · intro g hg
    simp only [synC, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · by_contra hlt
    exact hlow ⟨D, hD, by simp [synC, Circuit.size] at hlt ⊢; omega,
      fun x => congrFun hfun x⟩
theorem not_twoReadersSyntactic : ¬ StmtTwoReadersSyntactic := by
  intro hS
  have := hS 3 synC 2 synC_minimal (by decide)
  revert this
  decide
theorem synC_semantic :
    synC.gates.zipIdx.countP (fun p => decide (2 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 2) = 1 := by
  decide
end Maj.Exchange
namespace Maj.Exchange
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
theorem elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]
theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
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
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega
theorem countP_zipIdx_le (n h : ℕ) (f : Gate → Bool) : ∀ (l : List Gate) (m : ℕ),
    (l.zipIdx m).countP (fun p => decide (h < n + p.2) && f p.1)
      ≤ (l.drop (h + 1 - n - m)).countP f := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    rw [List.zipIdx_cons, List.countP_cons]
    have := ih (m + 1)
    by_cases hd : h + 1 - n - m = 0
    · rw [hd, List.drop_zero, List.countP_cons]
      have e : h + 1 - n - (m + 1) = 0 := by omega
      rw [e, List.drop_zero] at this
      have hlt : h < n + m := by omega
      by_cases hfa : f a = true <;> simp [hlt, hfa] <;> omega
    · obtain ⟨d, hd'⟩ : ∃ d, h + 1 - n - m = d + 1 := ⟨h + 1 - n - m - 1, by omega⟩
      rw [hd', List.drop_succ_cons]
      have e : h + 1 - n - (m + 1) = d := by omega
      rw [e] at this
      have hlt : ¬ h < n + m := by omega
      simp [hlt]
      exact this
theorem eff_eq (g : Gate) :
    (match g.op with
     | GateOp.not => g.inputs.take 1
     | _ => g.inputs) = (normGate g).inputs := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl
def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Sum.inl true else Sum.inr i
theorem startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Sum.inl false) =
      if i < m then (if i = h then Sum.inl true else Sum.inr i) else Sum.inl false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]
theorem inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩
theorem exchange_core (n : ℕ) (C : Circuit) (h : ℕ) (f : Gate → Bool)
    (hf : ∀ g, f g = (normGate g).inputs.contains h) (hC : FanInTwo C)
    (hcov : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) :
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1)
        ≤ C.size + 2 := by
  set r := C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1) with hr
  have hrle : r ≤ (C.gates.drop (h + 1 - n)).countP
      (fun g => (normGate g).inputs.contains h) := by
    have := countP_zipIdx_le n h f C.gates 0
    simp only [Nat.sub_zero] at this
    rw [hr]
    refine le_trans this (le_of_eq ?_)
    apply List.countP_congr
    intro g _
    rw [hf]
  have hrs : r ≤ C.gates.length := by
    refine le_trans hrle (le_trans (List.countP_le_length) ?_)
    simp
  have hconst : (∀ x : Fin n → Bool, circuitFun n C x = true) →
      ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧ D.size + r ≤ C.size + 2 := by
    intro hT
    refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      subst hg; simp
    · funext x
      rw [hT x]
      show (wiresFrom [⟨GateOp.and, []⟩] (List.ofFn x)).getD n false = true
      simp [wiresFrom, GateOp.eval]
    · simp only [Circuit.size, List.length_cons, List.length_nil]
      omega
  by_cases hex : ∃ x0 : Fin n → Bool, (C.wires (List.ofFn x0)).getD h false = true
  swap
  · apply hconst
    intro x
    apply hcov x
    push Not at hex
    simpa using hex x
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < n + C.size := by
    by_contra hlt
    rw [List.getD_eq_default _ _ (by
      rw [wires_eq, length_wiresFrom]; simp [Circuit.size] at hlt ⊢; omega)] at hx0
    cases hx0
  set k := h + 1 - n with hk
  have hks : k ≤ C.gates.length := by simp [Circuit.size] at hhs; omega
  have hhk : h < n + k := by omega
  set gs := C.gates.map normGate with hgs
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre, hgs]; omega
  have hlpost : post.length = C.gates.length - k := by simp [hpost, hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hokpre : ∀ g ∈ pre, Ok g := fun g hg => (hnok g (List.mem_of_mem_take hg)).1
  have hwC : ∀ y : List Bool, C.wires y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop, hgs, wiresFrom_norm]; rfl
  have hyl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := by simp
  have hwh : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false
      = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    rw [hwC, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc := elim n post (startStats (n + pre.length) h, pre) with hacc
  have hinv : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      Inv n (List.ofFn x) (C.wires (List.ofFn x)) acc := by
    intro x hx
    rw [hwC, hacc]
    exact inv_elim n _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_start n h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨t, ht⟩ := elim_prefix n post (startStats (n + pre.length) h, pre)
  rw [← hacc] at ht
  have hcount := elim_count n h post (startStats (n + pre.length) h, pre) hnokpost
    (by simp [startStats]; omega)
    ⟨true, by rw [startStats_getD]; simp [hhk, hlpre]⟩
  rw [← hacc] at hcount
  have hR : post.countP (fun g => g.inputs.contains h)
      = (C.gates.drop k).countP (fun g => (normGate g).inputs.contains h) := by
    rw [hpost, hgs, ← List.map_drop, List.countP_map]; rfl
  have hLk : acc.2.length = k + t.length := by rw [ht]; simp [hlpre]
  have hsize : acc.2.length + r ≤ C.gates.length := by
    change acc.2.length + post.countP (fun g => g.inputs.contains h)
      ≤ pre.length + post.length at hcount
    rw [hlpre, hlpost, hR] at hcount
    omega
  have hwhA : ∀ x : Fin n → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false
      = (C.wires (List.ofFn x)).getD h false := by
    intro x
    rw [ht, wiresFrom_append, hwh,
      getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  have hval : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x))
        = circuitFun n C x := by
    intro x hx
    exact ((hinv x hx).2 C.output).2
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) :=
    ((hinv x0 hx0).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      apply hconst
      intro x
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>
      refine ⟨⟨pre ++ [⟨GateOp.not, [h]⟩], n + k⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hokpre g hg
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
          subst hg; simp
      · funext x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (n + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = n + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (n + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : (C.wires (List.ofFn x)).getD h false = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | inr j =>
    rw [hst] at hvalid
    have hj : j < n + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩], n + L + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact elim_ok n post _ hokpre g hg
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
        rcases hg with rfl | rfl <;> simp
    · funext x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩])
        (List.ofFn x)).getD (n + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = n + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = n + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, n + L].map fun i => W'.getD i false)]).getD
        (n + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (n + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : (C.wires (List.ofFn x)).getD h false = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
      omega
theorem exchange' : StmtExchange := by
  intro n C h hC hcov
  exact exchange_core n C h (fun g => (match g.op with
         | GateOp.not => g.inputs.take 1
         | _ => g.inputs).contains h)
    (fun g => by obtain ⟨op, ins⟩ := g; cases op <;> rfl) hC hcov
theorem twoReaders' : StmtTwoReaders := twoReaders_of_exchange exchange'
end Maj.Exchange
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem exch_startStats_length (m h : ℕ) : (Exchange.startStats m h).length = m := by
  simp [Exchange.startStats]
theorem exch_clean_take (N k : ℕ) (gs : List Gate) (hcl : CleanL N gs) :
    CleanL N (gs.take k) := by
  intro p g hp
  rw [List.getElem?_take] at hp
  by_cases hpk : p < k
  · rw [if_pos hpk] at hp; exact hcl p g hp
  · rw [if_neg hpk] at hp; cases hp
theorem exch_const_reader (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g)
    (hop : g.op = GateOp.or ∨ g.op = GateOp.not) (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Sum.inl false) = Sum.inl true) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') true
  · intro h'; rcases hop with h2 | h2 <;> rw [h2] at h' <;> cases h'
  · intro _; rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst
theorem stmtExch : StmtExch := by
  intro N F gs o h T hcl hev hnc hcov hT
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp
  have hnotT : ¬ ∀ x : Fin N → Bool, F x = true := by
    intro hT'
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = true := by
    by_contra hne
    push Not at hne
    exact hnotT fun x => hcov x (by simpa using hne x)
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < N + gs.length := by
    by_contra hlt
    rw [vl_beyond gs x0 h (by omega)] at hx0
    cases hx0
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc0 : List Stat × List Gate := (Exchange.startStats (N + pre.length) h, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by
    rw [hacc0, exch_startStats_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = true →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx
    rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := Exchange.elim_prefix N post acc0
  rw [← hacc] at htl
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre
  have hsth0 : acc0.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc0, Exchange.startStats_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0
  have hTk : ∀ t ∈ T, k ≤ t := by
    intro t ht
    rcases hT t ht with hr | ⟨r, g, _, _, hrh, htr⟩
    · have := reads_lt hcl hr; omega
    · have := reads_lt hcl hrh; have := reads_lt hcl htr; omega
  have hcount := Helpers.elim_count N acc0 post hnokpost (T.image fun t => t - k) (by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    have htk := hTk t ht
    have hpt : post[t - k]? = gs[t]? := by
      rw [hpost, List.getElem?_drop]; congr 1; omega
    rcases hT t ht with ⟨g, hg, hhg⟩ | ⟨r, g', hg', hop, hrh, ⟨g, hg, hrg⟩⟩
    · refine ⟨g, by rw [hpt]; exact hg, h, hhg, ?_, true, ?_⟩
      · have := (hcl t g hg).lt h hhg; omega
      · rw [← hacc]; exact hsth
    · refine ⟨g, by rw [hpt]; exact hg, N + r, hrg, ?_, ?_⟩
      · have := (hcl t g hg).lt _ hrg; omega
      · have hrk : k ≤ r := by have := reads_lt hcl hrh; omega
        obtain ⟨g'', hg'', hhg''⟩ := hrh
        rw [hg'] at hg''
        cases hg''
        have hpr : post[r - k]? = some g' := by
          rw [hpost, List.getElem?_drop]
          have e : k + (r - k) = r := by omega
          rw [e]; exact hg'
        obtain ⟨c, hc⟩ := exch_const_reader N post acc0 hnokpost h (r - k) g' hpr hop hhg''
          (by omega) hsth0
        refine ⟨c, ?_⟩
        have e : acc0.1.length + (r - k) = N + r := by omega
        rw [e] at hc; exact hc)
  have hcard : (T.image fun t => t - k).card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have := hTk a ha; have := hTk b hb
    simp only at hab; omega
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + T.card ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega
  have hwhA : ∀ x : Fin N → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false = vl gs x h := by
    intro x
    rw [htl, wiresFrom_append, hwh, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hval : ∀ x : Fin N → Bool, vl gs x h = true →
      (acc.1.getD o (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = F x := by
    intro x hx
    rw [((hinv x hx).2 o).2, ← hev x]; rfl
  have hvalid : (acc.1.getD o (Sum.inl false)).Valid (N + acc.2.length) :=
    ((hinv x0 hx0).2 o).1
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      apply hnotT
      intro x
      by_cases hx : vl gs x h = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>
      refine ⟨pre ++ [⟨GateOp.not, [h]⟩], N + k, ?_, ?_, ?_⟩
      · intro p g hp
        by_cases hlt : p < pre.length
        · rw [List.getElem?_append_left hlt] at hp; exact hclpre p g hp
        · rw [List.getElem?_append_right (by omega)] at hp
          have hp0 : p - pre.length = 0 := by
            by_contra hne
            rw [List.getElem?_singleton, if_neg hne] at hp; cases hp
          rw [hp0, List.getElem?_singleton, if_pos rfl] at hp
          cases hp
          have hpl : p = k := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · intro x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (N + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = N + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (N + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : vl gs x h = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | inr j =>
    rw [hst] at hvalid
    have hj : j < N + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩], N + L + 1, ?_, ?_, ?_⟩
    · intro p g hp
      by_cases hlt : p < L
      · rw [List.getElem?_append_left hlt] at hp; exact hclacc p g hp
      · rw [List.getElem?_append_right (by omega)] at hp
        by_cases h0 : p - L = 0
        · rw [h0] at hp
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          have hpl : p = L := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
        · by_cases h1 : p - L = 1
          · rw [h1] at hp
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hp
            subst hp
            have hpl : p = L + 1 := by omega
            rw [hpl]
            exact Or.inr ⟨Or.inr rfl, j, N + L, by omega, by omega, rfl⟩
          · obtain ⟨d, hd⟩ : ∃ d, p - L = d + 2 := ⟨p - L - 2, by omega⟩
            rw [hd] at hp
            simp at hp
    · intro x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩])
        (List.ofFn x)).getD (N + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = N + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = N + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, N + L].map fun i => W'.getD i false)]).getD
        (N + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (N + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : vl gs x h = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : vl gs x h = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]
theorem stmtLift : StmtLift := by
  intro N F gs o p l h g hle hnc hg hop hin hbel
  have hcl := hle.hcl
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length N p l gs hp
  have ho := out_lt_of_nc hle.hev hnc
  have hlh : l < N + p ∧ h < N + p := by
    rcases hcl p g hg with ⟨h1, _⟩ | ⟨_, j, k, hj, hk, h2⟩
    · rw [hop] at h1; cases h1
    · rcases hin with e | e <;> rw [e] at h2 <;> simp at h2 <;> omega
  obtain ⟨hl, hh⟩ := hlh
  have hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p) = vl gs x l := by
    intro x hx
    rw [vl_gate _ hcl x p g hg, hop]
    rcases hin with e | e <;> rw [e] <;> simp [hx, GateOp.eval]
  have hro : rd N p l o < N + (gs.length - 1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩] with hgs2
  have hcl' := rdel_clean N p l gs hcl hp hl
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p l gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1, e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p l gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl, rd N p l o, h, by omega, by omega, rfl⟩
  have hlast : (gs2)[gs.length - 1]? = some ⟨GateOp.or, [rd N p l o, h]⟩ := by
    rw [hgs2, List.getElem?_append_right (by omega)]
    rw [show gs.length - 1 - (rdel N p l gs).length = 0 by omega]; rfl
  have hval : ∀ x : Fin N → Bool, vl gs2 x (N + (gs.length - 1)) = F x := by
    intro x
    rw [vl_gate _ hcl2 x _ _ hlast]
    have e1 : vl gs2 x (rd N p l o) = vl (rdel N p l gs) x (rd N p l o) :=
      vl_append_lt _ _ x _ (by omega)
    have e2 : vl gs2 x h = vl gs x h := by
      rw [vl_append_lt _ _ x _ (by omega), rdel_prefix N p l gs hcl hp hl x h hh]
    simp only [List.map, GateOp.eval, e1, e2]
    cases hx : vl gs x h
    · rw [rdel_all N p l gs hcl hp hl x (hS x hx) o, hle.hev x]; simp
    · rw [hbel x hx]; simp
  refine ⟨least_of hle hcl2 hval (by simp [hgs2]; omega), ?_⟩
  intro hnt t ht
  have hpt := ht.lt_of_not hp hnt
  have := tailGE_rdel_app N F gs [⟨GateOp.or, [rd N p l o, h]⟩] p l t
    (fun x : Fin N → Bool => vl gs x h = false) hcl hp hl ht hpt hS
    (fun x hx => hbel x (by simpa using hx)) ?_
  · simpa using this
  · intro i hi
    simp at hi
    subst hi
    refine ⟨_, by simpa using hlast, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
    rw [← hval x]; simpa using hx
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem not_tailOK_and {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) (hop : g.op = GateOp.and) : ¬ TailOK N F gs j := by
  rintro ⟨g0, hg0, h | ⟨h, _⟩⟩ <;>
  · rw [hg] at hg0
    cases hg0
    rw [hop] at h
    cases h
theorem vl_and_true {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = true) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]
theorem stmtXMove : StmtXMove := by
  intro N F gs o p p' l q h g g' hL hnc hpp hg hop hin hg' hop' hin' hbel
  have hcl := hL.hcl
  have hp's : p' < gs.length := (List.getElem?_eq_some_iff.1 hg').1
  have hl : l < N + p := (hcl p g hg).lt l (by rcases hin with hi | hi <;> simp [hi])
  have hh : h < N + p := (hcl p g hg).lt h (by rcases hin with hi | hi <;> simp [hi])
  have hq : q < N + p' := (hcl p' g' hg').lt q (by rcases hin' with hi | hi <;> simp [hi])
  have ho : o < N + gs.length := by
    by_contra hc
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hL.hev x, ← hL.hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]
  have hcl1 := rdel_clean N p' q gs hcl hp's hq
  have hlen1 := rdel_length N p' q gs hp's
  have hp1 : p < (rdel N p' q gs).length := by omega
  have hg1 : (rdel N p' q gs)[p]? = some g := by rw [rdel_get_lt N p' q gs hp's p hpp, hg]
  have hcl2 := rdel_clean N p l (rdel N p' q gs) hcl1 hp1 hl
  have hlen2 := rdel_length N p l (rdel N p' q gs) hp1
  have ho2 : rd N p l (rd N p' q o) < N + (rdel N p l (rdel N p' q gs)).length := by
    unfold rd
    split_ifs <;> omega
  have hh2 : h < N + (rdel N p l (rdel N p' q gs)).length := by omega
  have hgood : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p l (rdel N p' q gs)) x (rd N p l (rd N p' q o)) = F x ∧
      vl (rdel N p l (rdel N p' q gs)) x h = true := by
    intro x hx
    have hx1 := vl_and_true gs hcl x p' q h g' hg' hop' hin' hx
    have hx2 : vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
      rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
        rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
      exact vl_and_true gs hcl x p l h g hg hop hin hx
    refine ⟨?_, ?_⟩
    · rw [rdel_all N p l _ hcl1 hp1 hl x hx2, rdel_all N p' q gs hcl hp's hq x hx1, hL.hev x]
    · rw [rdel_prefix N p l _ hcl1 hp1 hl x h hh,
        rdel_prefix N p' q gs hcl hp's hq x h (by omega), hx]
  set gs2 := rdel N p l (rdel N p' q gs) with hgs2
  set o2 := rd N p l (rd N p' q o) with ho2def
  set new : List Gate := [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [o2, N + gs2.length]⟩] with hnew
  have hget0 : (gs2 ++ new)[gs2.length]? = some ⟨GateOp.not, [h]⟩ := by simp [hnew]
  have hget1 : (gs2 ++ new)[gs2.length + 1]? = some ⟨GateOp.or, [o2, N + gs2.length]⟩ := by
    simp [hnew]
  have hclA : CleanL N (gs2 ++ new) := by
    intro j g0 hj
    by_cases hj2 : j < gs2.length
    · rw [List.getElem?_append_left hj2] at hj
      exact hcl2 j g0 hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hjl : j - gs2.length < 2 := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simpa [hnew] using this
      rcases (by omega : j - gs2.length = 0 ∨ j - gs2.length = 1) with e | e
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inr ⟨Or.inr rfl, o2, N + gs2.length, by omega, by omega, rfl⟩
  have hvtop : ∀ x : Fin N → Bool, vl (gs2 ++ new) x (N + (gs2.length + 1)) = F x := by
    intro x
    have h0 : vl (gs2 ++ new) x (N + gs2.length) = !vl gs2 x h := by
      rw [vl_gate _ hclA x _ _ hget0]
      simp [GateOp.eval, vl_append_lt gs2 new x h hh2]
    rw [vl_gate _ hclA x _ _ hget1]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [h0, vl_append_lt gs2 new x o2 ho2]
    by_cases hx : vl gs x h = true
    · obtain ⟨e1, e2⟩ := hgood x hx
      rw [e1, e2]
      simp
    · have hF := hbel x (by simpa using hx)
      have e2 : vl gs2 x h = vl gs x h := by
        rw [hgs2, rdel_prefix N p l _ hcl1 hp1 hl x h hh,
          rdel_prefix N p' q gs hcl hp's hq x h (by omega)]
      rw [hF, e2]
      simp [hx]
  have hlenA : (gs2 ++ new).length = gs.length := by simp [hnew]; omega
  refine ⟨gs2 ++ new, N + (gs2.length + 1),
    least_of hL hclA hvtop (le_of_eq hlenA), ?_⟩
  intro t ht
  have hpt' : p' + t < gs.length := ht.lt_of_not hp's (not_tailOK_and hg' hop')
  have hF : ∀ x : Fin N → Bool, ¬ (vl gs x h = true) → F x = true :=
    fun x hx => hbel x (by simpa using hx)
  have ht1 : TailGE N F (rdel N p' q gs) t := by
    have := tailGE_rdel_app N F gs [] p' q t (fun x => vl gs x h = true) hcl hp's hq ht hpt'
      (fun x hx => vl_and_true gs hcl x p' q h g' hg' hop' hin' hx) hF
      (fun i hi => absurd hi (by simp))
    simpa using this
  have hS2 : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
    intro x hx
    rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
      rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
    exact vl_and_true gs hcl x p l h g hg hop hin hx
  have hlen2' : gs2.length = (rdel N p' q gs).length - 1 := by omega
  have := tailGE_rdel_app N F (rdel N p' q gs) new p l t (fun x => vl gs x h = true) hcl1 hp1 hl
    ht1 (by omega) hS2 hF (by
      intro i hi
      have hi2 : i < 2 := by simpa [hnew] using hi
      rw [← hlen2']
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact ⟨_, by simpa using hget0, Or.inl rfl⟩
      · refine ⟨_, hget1, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
        rw [show N + (gs2.length + 1) = N + (gs2.length + 1) from rfl, hvtop x] at hx
        exact hx)
  simpa [hnew] using this
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
def andSwap (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) : List Gate :=
  gs.set ph ⟨GateOp.not, [(y : ℕ)]⟩
theorem andSwap_length (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) :
    (andSwap gs ph y).length = gs.length := by
  simp [andSwap]
theorem andSwap_get_ne (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (r : ℕ) (hr : r ≠ ph) :
    (andSwap gs ph y)[r]? = gs[r]? := by
  simp [andSwap, Ne.symm hr]
theorem andSwap_get_eq (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (hph : ph < gs.length) :
    (andSwap gs ph y)[ph]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
  simp [andSwap, hph]
theorem andSwap_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (y : Fin N) (hcl : CleanL N gs)
    (hph : ph < gs.length) : CleanL N (andSwap gs ph y) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [andSwap_get_eq gs r y hph] at hr'
    cases hr'
    exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [andSwap_get_ne gs ph y r hrp] at hr'
    exact hcl r g' hr'
theorem andSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = false) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = false := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))
theorem andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x
theorem and_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = false)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [andSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc
theorem stmtAnd : StmtAnd := by
  intro n F gs o p ph l g y L hnc _hdep hgp hop hin hlit hph hone ho1 ho2
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < n + 1 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ n + 1 + ph := by
    intro e
    apply L.no_alias hfnc p hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  refine ⟨fun hly => ?_, fun hly => ?_⟩
  ·
    subst hly
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = false → vl gs x y = false := by
      intro x hx
      rw [vl_input gs x y y.isLt]
      exact hx
    have hcp : IsC n (andSwap gs ph y) y false (n + 1 + p) :=
      isC_reader hcl' y p g hgp' hlmem false (Or.inr (by simp [fixBit, hop]))
    have h3 := and_core n F gs o p ph y g y L false (hnc false) hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  ·
    rcases hlit with e | ⟨pn, rfl, hpn⟩
    · exact absurd e hly
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x (n + 1 + pn) = false := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) true (Or.inl rfl)
    have hc0 : c = false := by
      have h1 := st_val_const n _ hcl' y true _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc0
    have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
      const_read n _ hcl' y true p g hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := and_core n F gs o p ph (n + 1 + pn) g y L true (hnc true) hgp hop hin hlne hph
      hone ho2 hlx {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpnR
        · exact rc_of_reads hpR ⟨false, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem vl_dfree {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {h : ℕ} (hD : DFree D gs h)
    (u u' : Fin N → Bool) (hu : ∀ i, i ∉ D → u i = u' i) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h (fun i hi =>
    hu i (fun hiD => hD i hiD hi))
theorem out_ne_lit {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (y : Fin N)
    (hnc : ∀ b : Bool, ∃ x x' : Fin N → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (l : ℕ) (hl : IsLit N gs y l) : o ≠ l := by
  intro e
  subst e
  obtain ⟨x, x', hne⟩ := hnc false
  apply hne
  rw [← hev, ← hev]
  rcases hl with e | ⟨pn, e, hpn⟩
  · rw [e, vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
  · rw [e, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl,
      vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
theorem win_core {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)} {gs : List Gate}
    {o p : ℕ} {g : Gate} {y : Fin N} {l h : ℕ} (H : DeepHyp F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (hO : OneReader D gs)
    (hF : Front D gs p g y l h) : ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
  exfalso
  have hz : F (zeroOn D x) = false := by
    cases e : F (zeroOn D x) with
    | false => rfl
    | true => rw [H.mono x e] at hFx; cases hFx
  obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win y hy x hz
  have hagr : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hx'D i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (N + p) = fixBit g :=
    vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (N + p) = fixBit g :=
    vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr]; exact hx)
  have hol : o ≠ l := out_ne_lit hcl hev y (H.nc y hy) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit hcl hev y (H.nc y hy) y (Or.inl rfl)
  have key := agree_B gs hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin N) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by
            rcases hBa with e | e
            · exact e
            · rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq
            right
            rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads)
              ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [hev, hev, hF0, hF1] at key
  cases key
theorem stmtWin : StmtWin := by
  intro n F D gs o p g y l h H L hO hF
  have core := win_core H L.hcl L.hev hO hF
  refine ⟨fun e x hx => core x (by simp [fixBit, e, hx]),
    fun e => ⟨fun x hx => core x (by simp [fixBit, e, hx]), ?_⟩⟩
  by_contra hge
  have hlt : h < n + 1 := by omega
  have h0 := core (fun _ => false) (by rw [vl_input _ _ _ hlt]; simp [fixBit, e])
  rw [H.zero] at h0
  cases h0
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x
theorem stmtTwo : StmtExch → StmtWin → StmtTwo := by
  intro hEx hWin n F D gs o p g y l h hD L hOne hF hand hsec
  obtain ⟨hgp, _, hin, hyD, hlit, hfree⟩ := hF
  have hcl := L.hcl
  have hnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', hx⟩ := hD.nc y hyD false
    exact ⟨_, _, hx⟩
  obtain ⟨-, hW⟩ := hWin n F D gs o p g y l h hD L hOne ⟨hgp, Or.inl hand, hin, hyD, hlit, hfree⟩
  obtain ⟨hcov, hhN⟩ := hW hand
  have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
      T.card ≤ 2 := by
    intro T hTm
    obtain ⟨gs', o', hc', he', hlen⟩ := hEx (n + 1) F gs o h T hcl L.hev hnc hcov hTm
    have := L.hmin gs' o' hc' he'
    omega
  have hpread : Reads gs p h := ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
  obtain ⟨r, hrp, hrr⟩ := hsec
  have hall : ∀ t, Reads gs t h → t = p ∨ t = r := by
    intro t ht
    by_contra hne
    push_neg at hne
    have := hT {p, r, t} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl hpread
      · exact Or.inl hrr
      · exact Or.inl ht)
    rw [Finset.card_insert_of_notMem (by simp [hrp.symm, hne.1.symm]),
      Finset.card_insert_of_notMem (by simp [hne.2.symm]), Finset.card_singleton] at this
    omega
  obtain ⟨gr, hgr, hhr⟩ := hrr
  have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
  have hhlt : h < n + 1 + r := reads_lt hcl ⟨gr, hgr, hhr⟩
  rcases hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop, j, k, _, _, hjk⟩
  ·
    exfalso
    have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
    rw [hj] at hjin
    by_cases ho : o = n + 1 + r
    ·
      have h0 : F (zeroOn D (fun _ => false)) = false := by
        have : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
          funext i; simp [zeroOn]
        rw [this]; exact hD.zero
      obtain ⟨x', _, hx'y, hFx', hFx''⟩ := hD.win y hyD _ h0
      have e1 := L.hev x'
      have e2 := L.hev (Function.update x' y true)
      rw [ho, vl_not gs hcl _ r gr hgr h hnot hjin] at e1 e2
      rw [vl_update_of_not_supp gs h y (hfree y hyD) x' true] at e2
      have : F x' = F (Function.update x' y true) := by rw [← e1, ← e2]
      rw [this, hFx''] at hFx'
      exact Bool.noConfusion hFx'
    · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
      have htp : t ≠ p := by
        rintro rfl
        obtain ⟨g2, hg2, hmem⟩ := htr
        have := gate_eq hgp hg2 rfl
        subst this
        have hm : n + 1 + r = l ∨ n + 1 + r = h := by
          rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
        rcases hm with e | e
        · rcases hlit with e' | ⟨pn, e', hpn⟩
          · have := y.isLt; omega
          · have hrpn : r = pn := by omega
            subst hrpn
            have := gate_eq hgr hpn rfl
            rw [this] at hjin
            simp at hjin
            have := y.isLt; omega
        · omega
      have := hT {p, r, t} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
      omega
  · rcases hop with hop | hop
    ·
      refine ⟨r, gr, (if j = h then k else j), hrp, hgr, hop, ?_, hall⟩
      rw [hjk] at hhr ⊢
      by_cases hjh : j = h
      · subst hjh; right; simp
      · left
        simp at hhr ⊢
        omega
    ·
      exfalso
      by_cases ho : o = n + 1 + r
      ·
        apply hnc.elim
        intro x hx
        obtain ⟨x', hxx'⟩ := hx
        have key : ∀ z : Fin (n + 1) → Bool, F z = true := by
          intro z
          cases hz : vl gs z h
          · exact hcov z hz
          · rw [← L.hev z, ho, vl_gate gs hcl z r gr hgr, hop, hjk]
            rw [hjk] at hhr
            simp at hhr
            rcases hhr with e | e <;> subst e <;> simp [GateOp.eval, hz]
        exact hxx' (by rw [key x, key x'])
      · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
        have htp : t ≠ p := by
          rintro rfl
          obtain ⟨g2, hg2, hmem⟩ := htr
          have := gate_eq hgp hg2 rfl
          subst this
          have hm : n + 1 + r = l ∨ n + 1 + r = h := by
            rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
          rcases hm with e | e
          · rcases hlit with e' | ⟨pn, e', hpn⟩
            · have := y.isLt; omega
            · have hrpn : r = pn := by omega
              subst hrpn
              have := gate_eq hgr hpn rfl
              rw [this] at hop
              exact GateOp.noConfusion hop
          · omega
        have := hT {p, r, t} (by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact Or.inl hpread
          · exact Or.inl ⟨gr, hgr, hhr⟩
          · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
        rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
        omega
end Maj.EdgeFn
namespace Maj.EdgeFn
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
theorem front_suppsFrom_prefix {m : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin m)), ∃ T, suppsFrom gs L = L ++ T := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨T, hT⟩ := ih (L ++ [gateSupp L g])
    exact ⟨[gateSupp L g] ++ T, by
      show suppsFrom gs (L ++ [gateSupp L g]) = _
      rw [hT, List.append_assoc]⟩
theorem front_supp_input {m : ℕ} (gs : List Gate) (i : ℕ) (hi : i < m) :
    (suppsFrom gs (inputSupps m)).getD i ∅ = {(⟨i, hi⟩ : Fin m)} := by
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix gs (inputSupps m)
  rw [hT, List.getD_append _ _ _ _ (by simp [inputSupps]; exact hi)]
  simp [inputSupps, hi]
theorem front_supp_beyond {m : ℕ} (gs : List Gate) (w : ℕ) (hw : m + gs.length ≤ w) :
    (suppsFrom gs (inputSupps m)).getD w ∅ = ∅ :=
  List.getD_eq_default _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)
theorem front_supp_gate {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (i : Fin m) :
    i ∈ (suppsFrom gs (inputSupps m)).getD (m + p) ∅ ↔
      ∃ a ∈ g.inputs, i ∈ (suppsFrom gs (inputSupps m)).getD a ∅ := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  set L0 := suppsFrom pre (inputSupps m) with hL0
  have hl0 : L0.length = m + pre.length := by rw [hL0, length_suppsFrom]; simp [inputSupps]
  have e : suppsFrom (pre ++ g :: post) (inputSupps m)
      = suppsFrom post (L0 ++ [gateSupp L0 g]) := by
    rw [suppsFrom_append]; rfl
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix post (L0 ++ [gateSupp L0 g])
  have full : ∀ j, j < m + pre.length →
      (suppsFrom (pre ++ g :: post) (inputSupps m)).getD j ∅ = L0.getD j ∅ := by
    intro j hj
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (suppsFrom (pre ++ g :: post) (inputSupps m)).getD (m + pre.length) ∅
      = gateSupp L0 g := by
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]), ← hl0, getD_snoc_eq]
  rw [top, mem_gateSupp]
  constructor
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [full a (hlt a ha)]; exact hia⟩
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [← full a (hlt a ha)]; exact hia⟩
section ProofScope6
variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}
theorem front_nlit (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool) :
    ¬ ∀ u, F u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  apply hx
  rw [h, h]
  simp
theorem front_fnc (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) :
    ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  exact ⟨_, _, hx⟩
theorem front_dep (DH : DeepHyp F D) (L : Least (n + 1) F gs o) {y : Fin (n + 1)} (hy : y ∈ D) :
    y ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
  have hz : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
    funext i; simp [zeroOn]
  obtain ⟨x', -, -, hF0, hF1⟩ := DH.win y hy (fun _ => false) (by rw [hz]; exact DH.zero)
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x' y true) x' gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  have e : F (Function.update x' y true) = F x' := by
    rw [← L.hev, ← L.hev]
    exact hag
  rw [hF0, hF1] at e
  cases e
theorem front_dlit (L : Least (n + 1) F gs o) (hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x')
    (p0 : ℕ) (hmin : ∀ r < p0, ∀ g, gs[r]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅) :
    ∀ w, w < n + 1 + p0 → (∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD w ∅) →
      ∃ y ∈ D, ∃ c : Bool, (∀ u, vl gs u w = xor (u y) c) ∧
        (w = y ∨ ∃ pn, pn < p0 ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro hw ⟨i, hi, his⟩
    by_cases hwn : w < n + 1
    · rw [front_supp_input gs w hwn, Finset.mem_singleton] at his
      subst his
      exact ⟨⟨w, hwn⟩, hi, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
      cases hg : gs[r]? with
      | none =>
        have hlen : gs.length ≤ r := List.getElem?_eq_none_iff.1 hg
        rw [front_supp_beyond gs _ (by omega)] at his
        simp at his
      | some g =>
        have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
        · obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl r g hg i).1 his
          rw [hin, List.mem_singleton] at ha
          subst ha
          obtain ⟨y, hy, c, hv, hs⟩ := ih a (by omega) (by omega) ⟨i, hi, hia⟩
          rcases hs with e | ⟨pn, hpn, e, hgpn⟩
          · have hge : g = ⟨GateOp.not, [(y : ℕ)]⟩ := by
              cases g
              simp only at hop hin
              rw [hop, hin, e]
            refine ⟨y, hy, !c, fun u => ?_, Or.inr ⟨r, by omega, rfl, by rw [← hge]; exact hg⟩⟩
            rw [vl_not gs L.hcl u r g hg a hop hin, hv]
            cases u y <;> cases c <;> rfl
          · exfalso
            have hpl : pn < gs.length := (List.getElem?_eq_some_iff.1 hgpn).1
            refine L.no_alias hfnc r hrl y (by have := y.isLt; omega) (fun u => ?_)
            rw [vl_not gs L.hcl u r g hg a hop hin, e,
              vl_not gs L.hcl u pn _ hgpn (y : ℕ) rfl rfl, vl_input gs u y y.isLt]
            simp
        · exact absurd his (hmin r (by omega) g hg hop i hi)
theorem front_out (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (l : ℕ)
    (hl : l ∈ g.inputs) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ n + 1 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := DH.nc y hy (xor (fixBit g) c)
  have hc : ∀ z : Fin (n + 1) → Bool, F (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]
    simp
  exact hx (by rw [hc, hc])
theorem front_two (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (OR : OneReader D gs) (p : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ)
    (hin : g.inputs = [j, k]) (hj : j < n + 1 + p) (hk : k < n + 1 + p)
    (yj : Fin (n + 1)) (hyj : yj ∈ D) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin (n + 1)) (hyk : yk ∈ D) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc := front_fnc DH hyj
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), v ∈ D → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw
  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (n + 1 + p) = vl gs u' (n + 1 + p) → F u = F u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (yj : ℕ) ∨ n + 1 + p' = (yk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact front_nlit DH hyj false (fun x => by
          rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact front_nlit DH hyk false (fun x => by
          rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact front_nlit DH hyj cj (fun x => by rw [← L.hev, e, hvj])
      · exact front_nlit DH hyk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (n + 1 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply DH.nf yj hyj yk hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
end ProofScope6
theorem stmtFront : StmtFront := by
  intro n F D gs o DH hD L OR
  classical
  obtain ⟨y0, hy0⟩ := hD
  have hfnc := front_fnc DH hy0
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin (n + 1)),
        (w = y ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit (n + 1) gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact front_two DH L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop j (by rw [hin]; simp) hy c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop k (by rw [hin]; simp) hy c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨y, hy, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨y0, hy0, front_dep DH L hy0⟩
      exact front_nlit DH hy c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]
end Maj.EdgeFn
namespace Maj
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9191.Maj.Helpers
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.PermInputs
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Forest
open PEqualNP.Outside.L_meta_9191.Maj.Helpers.Readers
open PEqualNP.Outside.L_meta_9191.Maj.EdgeFn
theorem stmtML_final : StmtML :=
  stmtML stmtAnd (stmtExt stmtLift stmtXMove stmtFront stmtWin (stmtTwo stmtExch stmtWin))
end Maj

namespace Net

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev B := BitVec 36
abbrev Sig := B × B

def targetFun (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)

def pairs : List (ℕ × ℕ) :=
  [(3, 28), (3, 42), (3, 49), (3, 56), (5, 28), (5, 42), (5, 49), (5, 56), (6, 28), (6, 42), (6, 49), (6, 56), (9, 28), (9, 42), (9, 49), (9, 56), (18, 28), (18, 42), (18, 49), (18, 56), (36, 28), (36, 42), (36, 49), (36, 56), (29, 28), (30, 28), (60, 28), (43, 42), (46, 42), (58, 42), (51, 49), (53, 49), (57, 49), (57, 56), (58, 56), (60, 56)]

def maskFun (m : ℕ) : Fin 6 → Bool := fun i => m.testBit i.val

def pairA (r : Fin 36) : Fin 6 → Bool := maskFun (pairs.getD r.val (0, 0)).1
def pairB (r : Fin 36) : Fin 6 → Bool := maskFun (pairs.getD r.val (0, 0)).2

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 36 → Bool) : B :=
  BitVec.ofNat 36 (mkBVLoop 36 (fun i => if h : i < 36 then p ⟨i, h⟩ else false))

lemma testBit_mkBVLoop (n : ℕ) : ∀ (p : ℕ → Bool) (i : ℕ), i < n →
    (mkBVLoop n p).testBit i = p i := by
  induction n with
  | zero => intro p i hi; omega
  | succ n ih =>
    intro p i hi
    cases i with
    | zero =>
      simp only [mkBVLoop]
      cases p 0 <;> simp
    | succ i =>
      simp only [mkBVLoop]
      have hbit : (2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0).testBit (i + 1) =
          (mkBVLoop n (fun k => p (k + 1))).testBit i := by
        cases p 0 <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (fun k => p (k + 1)) i (by omega)]

lemma getElem_mkBV (p : Fin 36 → Bool) (i : ℕ) (hi : i < 36) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 36 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 36) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 36
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)

def neg (a : Sig) : Sig := (~~~ a.1, ~~~ a.2)

def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~ a.2

def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a :: l => sep d a ||| unionSep d l

def before (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)

def dropped (del v : List Sig) : List Sig :=
  v.filter (fun x => !del.contains x)

def tryGate (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains target
  | k + 1, t, v =>
    v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (search k t) v rest (bin false a b) keep ||
         tryGate k t (search k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 36 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

def initList : List Sig :=
  [(16257183999, 7520666692),
   (19227676431, 941761058),
   (36908830704, 118558993),
   (65481535488, 61198810043),
   (68301029376, 67777715677),
   (68668096512, 68600917742)]

def evalGateSig (g : Gate) (W : List Sig) : Sig :=
  match g.op, g.inputs with
  | GateOp.and, [] => one
  | GateOp.and, [p] => W.getD p zero
  | GateOp.and, [p, q] => bin false (W.getD p zero) (W.getD q zero)
  | GateOp.or, [] => zero
  | GateOp.or, [p] => W.getD p zero
  | GateOp.or, [p, q] => bin true (W.getD p zero) (W.getD q zero)
  | GateOp.not, [] => one
  | GateOp.not, p :: _ => neg (W.getD p zero)
  | _, _ => zero

def evalGates (gs : List Gate) (W : List Sig) : List Sig :=
  gs.foldl (fun W g => W ++ [evalGateSig g W]) W

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_cons (g : Gate) (rest : List Gate) (W : List Sig) :
    evalGates (g :: rest) W = evalGates rest (W ++ [evalGateSig g W]) := rfl

lemma evalWires_cons (g : Gate) (rest : List Gate) (w : List Bool) :
    evalWires (g :: rest) w =
      evalWires rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma initList_eq :
    wiresToSigs (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 6 = initList := by
  decide

lemma pairA_true : ∀ r : Fin 36, targetFun (pairA r) = true := by decide
lemma pairB_false : ∀ r : Fin 36, targetFun (pairB r) = false := by decide
lemma initList_nodup : initList.Nodup := by decide
lemma initList_len : initList.length = 6 := by decide
lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

lemma all_init_needed_bool :
    initList.all (fun s => unionSep true (initList.erase s) != top) = true := by decide

lemma all_init_needed : ∀ s ∈ initList, unionSep true (initList.erase s) ≠ top := by
  intro s hs
  have h := List.all_eq_true.1 all_init_needed_bool s hs
  exact bne_iff_ne.1 h

def cellNot (k t : ℕ) (v : List Sig) (a : Sig) : Bool :=
  tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]]

def cell (k t : ℕ) (v : List Sig) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a, b] v
     let keep := [[], [a], [b], [a, b]]
     tryGate k t (search k t) v rest (bin false a b) keep ||
     tryGate k t (search k t) v rest (bin true a b) keep)

lemma search_succ (k t : ℕ) (v : List Sig) :
    search (k + 1) t v = (v.contains target ||
      (decide (0 < t) && v.any (fun a => cellNot k t v a)) ||
      (decide (t ≤ k) && v.any (fun a => v.any (fun b => cell k t v a b)))) := rfl

lemma any_init_false {p : Sig → Bool} (h : ∀ i : Fin 6, p (initList.getD i zero) = false) :
    initList.any p = false := by
  rw [List.any_eq_false]
  intro a ha hpa
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hin : i < 6 := by simpa [initList_len] using hi
  have h' := h ⟨i, hin⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h'
  rw [h'] at hpa
  exact Bool.false_ne_true hpa

lemma target_not_init : initList.contains target = false := by decide

lemma search_succ_false (k t : ℕ)
    (hnot : t = 0 ∨ ∀ i : Fin 6, cellNot k t initList (initList.getD i zero) = false)
    (hbin : ∀ i j : Fin 6, cell k t initList (initList.getD i zero) (initList.getD j zero) = false) :
    search (k + 1) t initList = false := by
  rw [search_succ]
  have h1 : (decide (0 < t) && initList.any (fun a => cellNot k t initList a)) = false := by
    rcases hnot with rfl | hn
    · simp
    · rw [any_init_false hn, Bool.and_false]
  have h2 : initList.any (fun a => initList.any (fun b => cell k t initList a b)) = false :=
    any_init_false (fun i => any_init_false (fun j => hbin i j))
  rw [target_not_init, h1, h2]
  simp

set_option maxRecDepth 20000 in
lemma search_5_0 : search 5 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_6_0 : search 6 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_6_1 : search 6 1 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_0 : search 7 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_1 : search 7 1 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_2 : search 7 2 initList = false := by decide +kernel

lemma bin_comm (isOr : Bool) (a b : Sig) : bin isOr a b = bin isOr b a := by
  cases isOr <;> simp only [bin, BitVec.or_comm, BitVec.and_comm]

lemma bin_self (isOr : Bool) (a : Sig) : bin isOr a a = a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.and_self]
  · simp only [bin, ↓reduceIte, BitVec.or_self]

lemma bin_zero_left (isOr : Bool) (a : Sig) : bin isOr zero a = if isOr then a else zero := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, zero, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp
  · simp only [bin, zero, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp

lemma bin_zero_right (isOr : Bool) (a : Sig) : bin isOr a zero = if isOr then a else zero := by
  rw [bin_comm, bin_zero_left]

lemma bin_one_left (isOr : Bool) (a : Sig) : bin isOr one a = if isOr then one else a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, one, top, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
  · simp only [bin, one, top, ↓reduceIte, BitVec.allOnes_or]

lemma bin_one_right (isOr : Bool) (a : Sig) : bin isOr a one = if isOr then one else a := by
  rw [bin_comm, bin_one_left]

lemma neg_zero : neg zero = one := by decide
lemma neg_one : neg one = zero := by decide

lemma before_trichotomy {a b : Sig} (hne : a ≠ b) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases h1 : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h1 h)
    have h2n : a.2.toNat ≠ b.2.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = true := by rw [beq_iff_eq]; exact h1
    have hb2 : (b.1 == a.1) = true := by rw [beq_iff_eq]; exact h1.symm
    rw [hb1, hb2]
    simp only [↓reduceIte, decide_eq_true_eq]
    omega
  · have h1n : a.1.toNat ≠ b.1.toNat := fun h => h1 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = false := beq_false_of_ne h1
    have hb2 : (b.1 == a.1) = false := beq_false_of_ne (Ne.symm h1)
    rw [hb1, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

lemma unionSep_perm {d : Bool} {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    unionSep d v₁ = unionSep d v₂ := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [unionSep, ih]
  | swap a b l =>
    simp only [unionSep]
    rw [← BitVec.or_assoc, ← BitVec.or_assoc, BitVec.or_comm (sep d a) (sep d b)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma unionSep_append (d : Bool) (l₁ l₂ : List Sig) :
    unionSep d (l₁ ++ l₂) = unionSep d l₁ ||| unionSep d l₂ := by
  induction l₁ with
  | nil => simp [unionSep]
  | cons a t ih => simp only [List.cons_append, unionSep, ih, BitVec.or_assoc]

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 36) :
    (unionSep d v)[i] = true ↔ ∃ s ∈ v, (sep d s)[i] = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a t ih =>
    simp only [unionSep, BitVec.getElem_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, rfl | hs, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, h⟩

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 36), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 36) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 36) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 36) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 36) :
    (sep d (bin isOr a b))[i] = true → (sep d a)[i] = true ∨ (sep d b)[i] = true := by
  cases d <;> cases isOr <;>
    simp only [sep, bin, ↓reduceIte, Bool.false_eq_true, BitVec.getElem_and,
      BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not] <;>
    cases a.1[i] <;> cases a.2[i] <;> cases b.1[i] <;> cases b.2[i] <;> decide

lemma unionSep_target_eq_top : unionSep false [target] = top := by decide

lemma dropped_perm {del v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    (dropped del v₁).Perm (dropped del v₂) :=
  hp.filter _

lemma contains_perm {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) (x : Sig) :
    v₁.contains x = v₂.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

lemma list_any_eq_of_eq {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma search_perm : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search k t v₁ = search k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp target
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate k t' (search k t') v₁ rest₁ g keep =
          tryGate k t' (search k t') v₂ rest₂ g keep := by
      intro t' rest₁ rest₂ g keep hrest
      have hlen : rest₁.length = rest₂.length := hrest.length_eq
      have hcont : v₁.contains g = v₂.contains g := contains_perm hp g
      have husep : unionSep (decide (0 < t')) rest₁ = unionSep (decide (0 < t')) rest₂ :=
        unionSep_perm hrest
      simp only [tryGate, hcont, hlen, husep]
      congr 1
      refine list_any_eq_of_eq keep _ _ (fun h _ => ?_)
      have hp' : (g :: (h ++ rest₁)).Perm (g :: (h ++ rest₂)) :=
        List.Perm.cons g (List.Perm.append_left h hrest)
      rw [ih t' hp']
    have hcontT : v₁.contains target = v₂.contains target := contains_perm hp target
    have hunary : v₁.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.1 ha, ?_⟩
        rw [← htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.2 ha, ?_⟩
        rw [htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
    have hbinary :
        v₁.any (fun a => v₁.any (fun b => before a b &&
          (let rest := dropped [a, b] v₁
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₁ rest (bin false a b) keep ||
           tryGate k t (search k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₂ rest (bin false a b) keep ||
           tryGate k t (search k t) v₂ rest (bin true a b) keep))) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.2 ha, b, hp.mem_iff.2 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
    simp only [search, hcontT, hunary, hbinary]

lemma getD_mem_of_ne {W : List Sig} {p : ℕ} (hne : W.getD p zero ≠ zero) :
    W.getD p zero ∈ W := by
  by_cases hp : p < W.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  · rw [List.getD_eq_default _ _ (by omega)] at hne
    exact absurd rfl hne

lemma perm_of_nodup_same_mem {l₁ l₂ : List Sig} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hmem

lemma mem_dropped_iff {del v : List Sig} {x : Sig} :
    x ∈ dropped del v ↔ x ∈ v ∧ x ∉ del := by
  simp only [dropped, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, fun hm => ?_⟩
    have hc : del.contains x = true := List.contains_iff_mem.2 hm
    rw [hc] at hnot
    cases hnot
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    cases hc : del.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot

lemma tryGate_eq_true {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search (k + 1) t V = true := by
  obtain ⟨a, b, hab_ord, haW, hbW, ha0, ha1, hb0, hb1, hab, hbin⟩ :
      ∃ a b : Sig, before a b = true ∧ a ∈ W ∧ b ∈ W ∧ a ≠ zero ∧ a ≠ one ∧
        b ≠ zero ∧ b ≠ one ∧ a ≠ b ∧ sg = bin isOr a b := by
    rcases before_trichotomy hab_ne with h | h
    · exact ⟨a0, b0, h, ha0W, hb0W, ha0_ne0, ha0_ne1, hb0_ne0, hb0_ne1, hab_ne, hsgeq⟩
    · exact ⟨b0, a0, h, hb0W, ha0W, hb0_ne0, hb0_ne1, ha0_ne0, ha0_ne1, hab_ne.symm,
        by rw [hsgeq, bin_comm]⟩
  let addA : List Sig := if a ∈ U then [] else [a]
  let addB : List Sig := if b ∈ U then [] else [b]
  let V : List Sig := addA ++ addB ++ U
  have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x = b ∨ x ∈ U := by
    intro x
    simp only [V, addA, addB, List.mem_append]
    constructor
    · intro hx
      rcases hx with (hx | hx) | hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inl hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · by_cases haU : x ∈ U
        · exact Or.inr haU
        · exact Or.inl (Or.inl (by simp [haU]))
      · by_cases hbU : x ∈ U
        · exact Or.inr hbU
        · exact Or.inl (Or.inr (by simp [hbU]))
      · exact Or.inr hx
  have hV_nd : V.Nodup := by
    simp only [V, addA, addB]
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU, hUnd, hab]
  have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
    intro s hs
    rw [hV_mem] at hs
    rcases hs with rfl | rfl | hsU
    · exact ⟨haW, ha0, ha1⟩
    · exact ⟨hbW, hb0, hb1⟩
    · exact hUsub s hsU
  have hV_len : V.length ≤ (k + 1) - t + 1 := by
    have hA : addA.length ≤ 1 := by simp only [addA]; split_ifs <;> simp
    have hB : addB.length ≤ 1 := by simp only [addB]; split_ifs <;> simp
    have hlenV : V.length = addA.length + addB.length + U.length := by
      simp only [V, List.length_append]
    omega
  have hV_sep : unionSep (decide (0 < t)) V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hsV', hsi⟩ := htop
    rw [hPermV'.mem_iff, List.mem_cons] at hsV'
    rcases hsV' with rfl | hsU
    · rw [hbin] at hsi
      rcases sep_bin_bit _ _ a b i hi hsi with ha_b | hb_b
      · exact ⟨a, (hV_mem a).2 (Or.inl rfl), ha_b⟩
      · exact ⟨b, (hV_mem b).2 (Or.inr (Or.inl rfl)), hb_b⟩
    · exact ⟨s, (hV_mem s).2 (Or.inr (Or.inr hsU)), hsi⟩
  let hkeep : List Sig :=
    if a ∈ U then (if b ∈ U then [a, b] else [a]) else (if b ∈ U then [b] else [])
  have hhkeep_mem : hkeep ∈ [[], [a], [b], [a, b]] := by
    simp only [hkeep]; split_ifs <;> simp
  have hdrop_nd : (dropped [a, b] V).Nodup := hV_nd.filter _
  have hperm_next : (sg :: (hkeep ++ dropped [a, b] V)).Perm V' := by
    refine perm_of_nodup_same_mem ?_ hVnd ?_
    · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
      have hkh_nd : hkeep.Nodup := by
        simp only [hkeep]; split_ifs <;> simp [hab]
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
      · intro hm
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · apply hsgU
          simp only [hkeep] at hm
          split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> assumption
        · exact hsgV_not (mem_dropped_iff.1 hm).1
      · intro x hx y hy hxy
        subst hxy
        have hynot := (mem_dropped_iff.1 hy).2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hynot
        simp only [hkeep] at hx
        split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
    · intro x
      rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro (rfl | hx | hx)
        · exact Or.inl rfl
        · right
          simp only [hkeep] at hx
          split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> assumption
        · right
          have hx' := mem_dropped_iff.1 hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
          rw [hV_mem] at hx'
          rcases hx'.1 with rfl | rfl | hxU
          · exact absurd rfl hx'.2.1
          · exact absurd rfl hx'.2.2
          · exact hxU
      · rintro (rfl | hxU)
        · exact Or.inl rfl
        · right
          by_cases hxa : x = a
          · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
          · by_cases hxb : x = b
            · subst hxb; left; simp only [hkeep]; split_ifs <;> simp
            · right
              rw [mem_dropped_iff]
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨(hV_mem x).2 (Or.inr (Or.inr hxU)), hxa, hxb⟩
  have htry_ok : tryGate k t (search k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm k t hperm_next]
      exact hVsearch
  have hsearch_new : search (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma extract_live (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, target ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search k t V = true := by
  induction gs with
  | nil =>
    intro W hT
    refine ⟨0, le_rfl, 0, le_rfl, [target], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self target)
  | cons g rest ih =>
    intro W hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hT
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
      intro s hs
      obtain ⟨hsmem, hs0, hs1⟩ := hVsub s hs
      rw [List.mem_append, List.mem_singleton] at hsmem
      rcases hsmem with hsmem | rfl
      · exact ⟨hsmem, hs0, hs1⟩
      · rcases hskip with hnot | hin
        · exact absurd hs hnot
        · exact ⟨hin, hs0, hs1⟩
    · push Not at hskip
      obtain ⟨hsgV, hsgW⟩ := hskip
      have hsg01 := hVsub sg hsgV
      have hsg0 : sg ≠ zero := hsg01.2.1
      have hsg1 : sg ≠ one := hsg01.2.2
      set U := V'.erase sg
      have hUnd : U.Nodup := hVnd.erase sg
      have hsgU : sg ∉ U := List.Nodup.not_mem_erase hVnd
      have hPermV' : V'.Perm (sg :: U) := List.perm_cons_erase hsgV
      have hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
        intro s hs
        have hsV : s ∈ V' := List.mem_of_mem_erase hs
        have hsne : s ≠ sg := fun h => hsgU (h ▸ hs)
        obtain ⟨hsm, hs0, hs1⟩ := hVsub s hsV
        rw [List.mem_append, List.mem_singleton] at hsm
        exact ⟨hsm.resolve_right hsne, hs0, hs1⟩
      have hUlen : U.length + 1 = V'.length := by
        have := hPermV'.length_eq
        simp at this
        omega
      rcases hg with ⟨hop, hinlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin false (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_left]; rfl
          have hb0_ne0 : b0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_right]; rfl
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_left]; simpa using hb0W
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_right]; simpa using ha0W
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg0; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin true (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h
            have hsgeq' : sg = b0 := by rw [hsgeq, h, bin_zero_left]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have hb0_ne0 : b0 ≠ zero := by
            intro h
            have hsgeq' : sg = a0 := by rw [hsgeq, h, bin_zero_right]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_left]; rfl
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_right]; rfl
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · have hsgeq : sg = neg (W.getD p zero) := by simp [sg, evalGateSig, hop, hin]
          set a := W.getD p zero
          have ha0 : a ≠ zero := by intro h; apply hsg1; rw [hsgeq, h, neg_zero]
          have ha1 : a ≠ one := by intro h; apply hsg0; rw [hsgeq, h, neg_one]
          have haW : a ∈ W := getD_mem_of_ne ha0
          let V : List Sig := if a ∈ U then U else a :: U
          have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x ∈ U := by
            intro x
            simp only [V]
            by_cases haU : a ∈ U
            · simp only [haU, ↓reduceIte]
              exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ haU) id⟩
            · simp only [haU, ↓reduceIte, List.mem_cons]
          have hV_nd : V.Nodup := by
            simp only [V]
            by_cases haU : a ∈ U <;> simp [haU, hUnd]
          have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
            intro s hs
            rw [hV_mem] at hs
            rcases hs with rfl | hsU
            · exact ⟨haW, ha0, ha1⟩
            · exact hUsub s hsU
          have hV_len : V.length ≤ (k + 1) - (t + 1) + 1 := by
            have : V.length ≤ U.length + 1 := by simp only [V]; split_ifs <;> simp
            omega
          have hV_sep : unionSep (decide (0 < t + 1)) V = top := by
            apply bv_eq_top_of_bits
            intro i hi
            rw [unionSep_bit_iff _ _ i hi]
            have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
            rw [unionSep_bit_iff _ _ i hi] at htop
            obtain ⟨s, hsV', hsi⟩ := htop
            have hsi' : (sep true s)[i] = true := sep_mono_true _ s i hi hsi
            rw [hPermV'.mem_iff, List.mem_cons] at hsV'
            rcases hsV' with rfl | hsU
            · rw [hsgeq, sep_neg_true a i hi] at hsi'
              exact ⟨a, (hV_mem a).2 (Or.inl rfl), by simpa using hsi'⟩
            · exact ⟨s, (hV_mem s).2 (Or.inr hsU), by simpa using hsi'⟩
          let hkeep : List Sig := if a ∈ U then [a] else []
          have hhkeep_mem : hkeep ∈ [[], [a]] := by simp only [hkeep]; split_ifs <;> simp
          have hdrop_nd : (dropped [a] V).Nodup := hV_nd.filter _
          have hperm_next : (sg :: (hkeep ++ dropped [a] V)).Perm V' := by
            refine perm_of_nodup_same_mem ?_ hVnd ?_
            · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
              have hkh_nd : hkeep.Nodup := by simp only [hkeep]; split_ifs <;> simp
              rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
              · intro hm
                rw [List.mem_append] at hm
                rcases hm with hm | hm
                · apply hsgU
                  simp only [hkeep] at hm
                  split_ifs at hm <;> simp at hm
                  rw [hm]; assumption
                · exact hsgV_not (mem_dropped_iff.1 hm).1
              · intro x hx y hy hxy
                subst hxy
                have hynot := (mem_dropped_iff.1 hy).2
                simp only [List.mem_singleton] at hynot
                simp only [hkeep] at hx
                split_ifs at hx <;> simp at hx
                exact hynot hx
            · intro x
              rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
              constructor
              · rintro (rfl | hx | hx)
                · exact Or.inl rfl
                · right
                  simp only [hkeep] at hx
                  split_ifs at hx <;> simp at hx
                  subst hx; assumption
                · right
                  have hx' := mem_dropped_iff.1 hx
                  simp only [List.mem_singleton] at hx'
                  rw [hV_mem] at hx'
                  exact hx'.1.resolve_left hx'.2
              · rintro (rfl | hxU)
                · exact Or.inl rfl
                · right
                  by_cases hxa : x = a
                  · subst hxa; left; simp only [hkeep]; split_ifs; simp
                  · right
                    rw [mem_dropped_iff]
                    simp only [List.mem_singleton]
                    exact ⟨(hV_mem x).2 (Or.inr hxU), hxa⟩
          have hsearch_new : search (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma wiresToSigs_getD (wa wb : Fin 36 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len) (i : ℕ) :
    (wiresToSigs wa wb len).getD i zero =
      (mkBV (fun r => (wa r).getD i false),
       mkBV (fun r => (wb r).getD i false)) := by
  by_cases hi : i < len
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [wiresToSigs]
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_default _ _ (by omega)]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwb ⟨r, hr⟩]; omega)]

lemma wiresToSigs_step (wa wb : Fin 36 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    wiresToSigs
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1) =
    wiresToSigs wa wb len ++ [evalGateSig g (wiresToSigs wa wb len)] := by
  have hprefix :
      (List.range len).map (fun idx =>
        (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD idx false),
         mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD idx false))) =
      wiresToSigs wa wb len := by
    unfold wiresToSigs
    apply List.map_congr_left
    intro idx hidx
    rw [List.mem_range] at hidx
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwa ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwa ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwb ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwb ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwb ⟨r, hr⟩]; omega)]
  have hlast :
      (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false),
       mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false)) =
      evalGateSig g (wiresToSigs wa wb len) := by
    have hgetLast : ∀ (w : List Bool) (v : Bool), w.length = len → (w ++ [v]).getD len false = v := by
      intro w v hw
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_append_right (by omega)]
      simp [hw]
    have hA : (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wa r).getD i false) := by
      funext r; exact hgetLast (wa r) _ (hwa r)
    have hB : (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wb r).getD i false) := by
      funext r; exact hgetLast (wb r) _ (hwb r)
    rw [hA, hB]
    rcases hg with ⟨hop, hinlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.all_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.any_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          (simp only [zero, getElem_mkBV]; exact (zero_bit r hr).symm)
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, ↓reduceIte, BitVec.getElem_or, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.headD_cons]
        rw [wiresToSigs_getD wa wb len hwa hwb p]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [neg, BitVec.getElem_not, getElem_mkBV]
  show (List.range (len + 1)).map _ = _
  rw [List.range_succ, List.map_append, List.map_singleton, hprefix, hlast]

lemma evalWires_len (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g rest ih =>
    rw [evalWires_cons, ih]
    simp
    omega

lemma wiresToSigs_evalGates (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (wa wb : Fin 36 → List Bool) (len : ℕ),
      (∀ r, (wa r).length = len) → (∀ r, (wb r).length = len) →
      wiresToSigs (fun r => evalWires gs (wa r)) (fun r => evalWires gs (wb r)) (len + gs.length) =
        evalGates gs (wiresToSigs wa wb len) := by
  induction gs with
  | nil =>
    intro wa wb len _ _
    simp [evalWires, evalGates]
  | cons g rest ih =>
    intro wa wb len hwa hwb
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    have h1 := ih hrest
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1)
      (fun r => by simp [hwa r])
      (fun r => by simp [hwb r])
    simp only [List.length_cons]
    rw [show len + (rest.length + 1) = len + 1 + rest.length by omega]
    have hwa_eq : (fun r => evalWires (g :: rest) (wa r)) =
        (fun r => evalWires rest (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])) := rfl
    have hwb_eq : (fun r => evalWires (g :: rest) (wb r)) =
        (fun r => evalWires rest (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])) := rfl
    rw [hwa_eq, hwb_eq, evalGates_cons, h1, wiresToSigs_step wa wb len hwa hwb g hg]

lemma sample_lower (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (accepts : ∀ r : Fin 36, C.eval (List.ofFn (pairA r)) = true)
    (rejects : ∀ r : Fin 36, C.eval (List.ofFn (pairB r)) = false) :
    8 ≤ C.size := by
  by_contra small
  have hlen : C.gates.length ≤ 7 := by
    change ¬ 8 ≤ C.gates.length at small
    omega
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 6
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates initList).getD C.output zero = target := by
    rw [← initList_eq, ← hW]
    rw [wiresToSigs_getD _ _ (6 + C.gates.length)
      (fun r => by rw [evalWires_len]; simp)
      (fun r => by rw [evalWires_len]; simp) C.output]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [target, top, getElem_mkBV, BitVec.getElem_allOnes]
      exact accepts ⟨r, hr⟩
    · simp only [target, getElem_mkBV]
      rw [zero_bit r hr]
      exact rejects ⟨r, hr⟩
  have hTmem : target ∈ evalGates C.gates initList :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live C.gates hfan initList hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ initList, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ initList := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm initList :=
    perm_of_nodup_same_mem hVnd initList_nodup (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen6 : V.length = 6 := hPermInit.length_eq.trans initList_len
  have hk7 : k ≤ 7 := le_trans hk hlen
  have hsearch_init : search k t initList = true := by
    rw [← search_perm k t hPermInit]
    exact hVsearch
  have hcases : (k = 5 ∧ t = 0) ∨
      (k = 6 ∧ t = 0) ∨
      (k = 6 ∧ t = 1) ∨
      (k = 7 ∧ t = 0) ∨
      (k = 7 ∧ t = 1) ∨
      (k = 7 ∧ t = 2) := by omega
  rcases hcases with ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · rw [search_5_0] at hsearch_init; simp at hsearch_init
  · rw [search_6_0] at hsearch_init; simp at hsearch_init
  · rw [search_6_1] at hsearch_init; simp at hsearch_init
  · rw [search_7_0] at hsearch_init; simp at hsearch_init
  · rw [search_7_1] at hsearch_init; simp at hsearch_init
  · rw [search_7_2] at hsearch_init; simp at hsearch_init
lemma lower (s : ℕ) (hc : HasCircuitSize 6 targetFun s) : 8 ≤ s := by
  obtain ⟨C, hfan, hsize, hcorrect⟩ := hc
  apply le_trans (sample_lower C hfan ?_ ?_) hsize
  · intro r
    exact (hcorrect _).trans (pairA_true r)
  · intro r
    exact (hcorrect _).trans (pairB_false r)

end Net

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Maj.Helpers Maj.Helpers.Readers Maj.EdgeFn

def netOnNine (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) ||
    (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)

def target (x : Fin 9 → Bool) : Bool :=
  netOnNine x || (x 6 && (x 8 || x 7)) || (x 8 && x 7)

def special : Finset (Fin 9) := {6, 7}

lemma net_zero (x : Fin 9 → Bool) : netOnNine (zeroOn special x) = netOnNine x := by
  simp [netOnNine, zeroOn, special]

lemma net_update6 (x : Fin 9 → Bool) (b : Bool) :
    netOnNine (Function.update x 6 b) = netOnNine x := by
  simp [netOnNine, Function.update_apply]

lemma net_update7 (x : Fin 9 → Bool) (b : Bool) :
    netOnNine (Function.update x 7 b) = netOnNine x := by
  simp [netOnNine, Function.update_apply]

lemma deep_target : DeepHyp target special := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy b
    simp [special] at hy
    rcases hy with rfl | rfl <;> cases b
    all_goals refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    all_goals simp [target, netOnNine, Function.update_apply]
  · intro y hy z hz hne
    simp [special] at hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
    · exact (hne rfl).elim
    · rintro ⟨a, b, h⟩
      have h0 := h (fun _ => false)
      have h1 := h (fun i => decide (i = 8))
      cases a <;> cases b <;> simp [target, netOnNine, set2, Function.update_apply] at h0 h1
    · rintro ⟨a, b, h⟩
      have h0 := h (fun _ => false)
      have h1 := h (fun i => decide (i = 8))
      cases a <;> cases b <;> simp [target, netOnNine, set2, Function.update_apply] at h0 h1
    · exact (hne rfl).elim
  · intro y hy x hx
    have hg : netOnNine x = false := by
      have hz : netOnNine (zeroOn special x) = false := by simpa [target, zeroOn, special] using hx
      exact (net_zero x).symm.trans hz
    simp [special] at hy
    rcases hy with rfl | rfl
    · let x' := Function.update (Function.update x 6 false) 7 (!x 8)
      refine ⟨x', ?_, ?_, ?_, ?_⟩
      · intro i hi
        simp [special] at hi
        simp [x', Function.update_of_ne hi.1, Function.update_of_ne hi.2]
      · simp [x']
      · simp [target, net_update6, net_update7, x', hg]
      · cases h8 : x 8 <;> simp [target, net_update6, net_update7, x', hg, h8]
    · let x' := Function.update (Function.update x 7 false) 6 (!x 8)
      refine ⟨x', ?_, ?_, ?_, ?_⟩
      · intro i hi
        simp [special] at hi
        simp [x', Function.update_of_ne hi.1, Function.update_of_ne hi.2]
      · simp [x']
      · simp [target, net_update6, net_update7, x', hg]
      · cases h8 : x 8 <;> simp [target, net_update6, net_update7, x', hg, h8]
  · intro x hx
    have hg : netOnNine x = true := by
      have hz : netOnNine (zeroOn special x) = true := by simpa [target, zeroOn, special] using hx
      exact (net_zero x).symm.trans hz
    simp [target, hg]
  · decide

lemma restrict_one {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (i : Fin (n + 1)) (b : Bool) (dep : Dep f i)
    (nc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (circuit : HasCircuitSize (n + 1) f s) : Drop f i b 1 s := by
  obtain ⟨gs, o, least, size⟩ := exists_least (n + 1) f s (dep_nc dep) circuit
  have read : ∃ q, Reads gs q i := by
    by_contra none
    have noRead : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
      intro g hg hi
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
      exact none ⟨q, g, hq, hi⟩
    have outputDifferent : o ≠ i := by
      intro he
      obtain ⟨x, y, hxy⟩ := nc
      apply hxy
      rw [← least.hev, ← least.hev, he, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
      simp
    obtain ⟨x, hx⟩ := dep
    apply hx
    rw [← least.hev, ← least.hev]
    refine agree_except i gs _ _ noRead (by simp) ?_ o outputDifferent
    intro j hj
    by_cases within : j < n + 1
    · rw [show (List.ofFn (Function.update x i (!x i))).getD j false =
            Function.update x i (!x i) ⟨j, within⟩ from getD_ofFn _ _ false ⟨j, within⟩,
          show (List.ofFn x).getD j false = x ⟨j, within⟩ from getD_ofFn _ _ false ⟨j, within⟩]
      exact Function.update_of_ne (fun h => hj (congrArg Fin.val h)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨r, hr⟩ := read
  exact (least.save i b nc {r} (by simpa using rc_input b hr)).mono (by simp) size

def remainder (z : Fin 9) (b : Bool) (x : Fin 9 → Bool) : Bool :=
  netOnNine x || (if b then x z || x 8 else x z && x 8)

def withFreeInput (x : Fin 9 → Bool) : Bool := netOnNine x || x 8

lemma remainder_update (z : Fin 9) (hz : z = 6 ∨ z = 7) (b : Bool) :
    (fun x => remainder z b (Function.update x z (!b))) = withFreeInput := by
  rcases hz with rfl | rfl <;> cases b <;> funext x <;>
    simp [remainder, withFreeInput, net_update6, net_update7]

lemma free_update : (fun x => withFreeInput (Function.update x 8 false)) = netOnNine := by
  funext x
  simp [withFreeInput, netOnNine, Function.update_apply]

lemma netOnNine_lower (s : ℕ) (h : HasCircuitSize 9 netOnNine s) : 8 ≤ s := by
  let π : Fin 9 → Fin 6 := ![0, 1, 2, 3, 4, 5, 0, 0, 0]
  have h' := Maj.Helpers.PermInputs.relabel_size π netOnNine s h
  exact Net.lower s h'

lemma remainder_lower (z : Fin 9) (hz : z = 6 ∨ z = 7) (b : Bool) (s : ℕ)
    (h : HasCircuitSize 9 (remainder z b) s) : 10 ≤ s := by
  have dep : Dep (remainder z b) z := by
    rcases hz with rfl | rfl <;> cases b
    · exact ⟨fun i => decide (i = 8), by decide⟩
    · exact ⟨fun _ => false, by decide⟩
    · exact ⟨fun i => decide (i = 8), by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  have nc : ∃ x y, remainder z b (Function.update x z (!b)) ≠
      remainder z b (Function.update y z (!b)) := by
    change ∃ x y, (fun a => remainder z b (Function.update a z (!b))) x ≠
      (fun a => remainder z b (Function.update a z (!b))) y
    rw [remainder_update z hz b]
    exact ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨s', h', c'⟩ := restrict_one z (!b) dep nc h
  rw [remainder_update z hz b] at c'
  have dep' : Dep withFreeInput 8 := ⟨fun _ => false, by decide⟩
  have nc' : ∃ x y, withFreeInput (Function.update x 8 false) ≠
      withFreeInput (Function.update y 8 false) := ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨s'', h'', c''⟩ := restrict_one 8 false dep' nc' c'
  rw [free_update] at c''
  have := netOnNine_lower s'' c''
  omega

lemma target_cofactor6 (b : Bool) :
    (fun x => target (Function.update x 6 b)) = remainder 7 b := by
  cases b <;> funext x <;> cases h7 : x 7 <;> cases h8 : x 8 <;>
    simp [target, remainder, net_update6, h7, h8]

lemma target_cofactor7 (b : Bool) :
    (fun x => target (Function.update x 7 b)) = remainder 6 b := by
  cases b <;> funext x <;> cases h6 : x 6 <;> cases h8 : x 8 <;>
    simp [target, remainder, net_update7, h6, h8]

lemma target_lower (s : ℕ) (h : HasCircuitSize 9 target s) : 13 ≤ s := by
  obtain ⟨y, hy, hc⟩ := Maj.stmtML_final 8 target special s deep_target (by simp [special]) h
  have hcofactor (b : Bool) (t : ℕ)
      (hs : HasCircuitSize 9 (fun x => target (Function.update x y b)) t) : 10 ≤ t := by
    simp [special] at hy
    rcases hy with rfl | rfl
    · rw [target_cofactor6] at hs
      exact remainder_lower 7 (Or.inr rfl) b t hs
    · rw [target_cofactor7] at hs
      exact remainder_lower 6 (Or.inl rfl) b t hs
  rcases hc with ⟨t, hsize, ht⟩ | ⟨t, hsize, ht⟩
  · have := hcofactor false t ht
    omega
  · have := hcofactor true t ht
    omega

end PEqualNP.Outside.L_meta_9191

theorem PEqualNP.Outside.L_meta_9191 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 5 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 6 && x 8)) t → 13 ≤ t := by
  intro t h
  let π : Fin 9 → Fin 9 := ![0, 6, 4, 5, 3, 7, 1, 8, 2]
  have h' := PEqualNP.Outside.L_meta_9191.Maj.Helpers.PermInputs.relabel_size π _ t h
  apply PEqualNP.Outside.L_meta_9191.target_lower t
  convert h' using 1
  funext x
  simp [π, PEqualNP.Outside.L_meta_9191.target, PEqualNP.Outside.L_meta_9191.netOnNine]
  grind
