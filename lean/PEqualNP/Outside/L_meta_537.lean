import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_537_aux.Helpers
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

end PEqualNP.Outside.L_meta_537_aux.Helpers

namespace PEqualNP.Outside.L_meta_537_aux.Helpers
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

end PEqualNP.Outside.L_meta_537_aux.Helpers

namespace PEqualNP.Outside.L_meta_537_aux.Helpers
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

end PEqualNP.Outside.L_meta_537_aux.Helpers

namespace PEqualNP.Outside.L_meta_537_aux.Perm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_537_aux.Helpers



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
end PEqualNP.Outside.L_meta_537_aux.Perm

namespace PEqualNP.Outside.L_meta_537_aux.M168

namespace L_meta_168_helpers

open PEqualNP.CircuitLowerBounds


private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ)
    (h : L.length = k) : (L ++ [S]).getD k d = S := by
  subst h; simp


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
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]


private theorem getD_wiresFrom_input (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    have h' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i h'
    exact this.trans (List.getD_append _ _ _ _ h)


private theorem mem_take_one {α : Type} {a : α} (l : List α) :
    a ∈ l.take 1 ↔ l.head? = some a := by
  rw [List.take_one]
  cases l <;> simp [eq_comm]


private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]


private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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


private theorem mem_normGate_inputs_iff (n : ℕ) (g : Gate) :
    n ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some n) ∨
      (g.op ≠ GateOp.not ∧ n ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    simp only [normGate]
    rw [mem_take_one inputs]
    simp
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]


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

private theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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


private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

private theorem elim_len_add_count_le (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3]
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hk' : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : ∃ c, (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl c := by
      obtain ⟨c, hc⟩ := hc
      refine ⟨c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hih := ih (elimStep n acc g) hok' hk' hc'
    by_cases hkg : k ∈ g.inputs
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) + 1 := by
        rw [List.countP_cons]
        simp [hkg]
      have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · obtain ⟨c, hc⟩ := hc
          exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [hcnt, List.length_cons]
      omega
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) := by
        rw [List.countP_cons]
        simp [hkg]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [hcnt, List.length_cons]
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj



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



private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

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



private theorem wiresFrom_agree_off {n : ℕ} (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ n → w.getD i false = w'.getD i false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ hagree j hj
    exact hagree j hj
  | cons g gs ih =>
    intro w w' hlen hagree j hj
    have hno' : ∀ g' ∈ gs, n ∉ g'.inputs :=
      fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    have hgn : n ∉ g.inputs := hno g List.mem_cons_self
    have hlen1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
      simp [hlen]
    have hagree1 : ∀ i, i ≠ n →
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w.length
        · subst heq
          rw [getD_snoc_len w _ _ w.length rfl, getD_snoc_len w' _ _ w.length hlen.symm]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hagree a (fun e => hgn (e ▸ ha))
        · have hwl : i ≠ w'.length := by omega
          rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ hwl]
          exact hagree i hi
    exact ih hno'
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      hlen1 hagree1 j hj

private theorem two_le_countP_of_two_getElem {α : Type} (p : α → Bool) (l : List α)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      have ha : p a = true := by simpa using hpi
      have hj' : j < l.length := by simpa using hj
      have hpj' : p l[j] = true := by simpa using hpj
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[j], List.getElem_mem hj', hpj'⟩
      omega
    | i + 1, 0 =>
      have ha : p a = true := by simpa using hpj
      have hi' : i < l.length := by simpa using hi
      have hpi' : p l[i] = true := by simpa using hpi
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[i], List.getElem_mem hi', hpi'⟩
      omega
    | i + 1, j + 1 =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have hij' : i ≠ j := by omega
      have hpi' : p l[i] = true := by simpa using hpi
      have hpj' : p l[j] = true := by simpa using hpj
      have hrec := ih i j hi' hj' hij' hpi' hpj'
      rw [List.countP_cons]
      have hle : l.countP p ≤ l.countP p + (if p a then 1 else 0) := Nat.le_add_right _ _
      omega

end L_meta_168_helpers

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open L_meta_168_helpers

theorem L_meta_168 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∃ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) ∧ ∀ j' : Fin C.gates.length, ((C.gates.get j').op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j').inputs.head? = some n ∨ (C.gates.get j').op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j').inputs) → j' = j := by
  intro n C hmin hdep hnc hsize
  obtain ⟨hCok, _⟩ := hmin
  set gs : List Gate := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hCok g0 hg0)
  have hout : C.output ≠ n := by
    intro houtn
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have hv : ∀ z : Fin n → Bool, circuitFun (n + 1) C (Fin.snoc z false) = false := by
      intro z
      show (wiresFrom C.gates (List.ofFn (Fin.snoc z false))).getD C.output false = false
      rw [houtn]
      rw [getD_wiresFrom_input C.gates _ n (by
        rw [List.length_ofFn]; exact Nat.lt_succ_self n)]
      rw [ofFn_snoc]
      rw [getD_snoc_len _ _ _ n (by simp [List.length_ofFn])]
    rw [hv y, hv y']
  have hex : ∃ j : Fin C.gates.length, n ∈ (normGate (C.gates.get j)).inputs := by
    by_contra hnone
    push_neg at hnone
    have hno : ∀ g ∈ gs, n ∉ g.inputs := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hg0
      rw [← hi]
      exact hnone i
    obtain ⟨y, hne⟩ := hdep
    have hlen : (List.ofFn (Fin.snoc y false)).length
        = (List.ofFn (Fin.snoc y true)).length := by simp
    have hagree : ∀ i, i ≠ n →
        (List.ofFn (Fin.snoc y false)).getD i false
          = (List.ofFn (Fin.snoc y true)).getD i false := by
      intro i hi
      rw [ofFn_snoc, ofFn_snoc]
      by_cases hlt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt),
            List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt)]
      · have hli : i ≠ (List.ofFn y).length := by simp [List.length_ofFn]; omega
        rw [getD_snoc_ne _ _ _ _ hli, getD_snoc_ne _ _ _ _ hli]
    have hEq := wiresFrom_agree_off (n := n) gs hno _ _ hlen hagree C.output hout
    apply hne
    show (wiresFrom C.gates (List.ofFn (Fin.snoc y false))).getD C.output false
        = (wiresFrom C.gates (List.ofFn (Fin.snoc y true))).getD C.output false
    simpa [hgs, wiresFrom_norm] using hEq
  set acc : List Stat × List Gate := elim n gs (initStats n false, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y false))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n false y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = circuitFun (n + 1) C (Fin.snoc y false) := by
    intro y
    rw [((hinv y).2 C.output).2]
    rw [hgs, wiresFrom_norm]
    rfl
  have hcs : HasCircuitSize n
      (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y false)) acc.2.length := by
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hnc
      apply hne
      rw [← hval y, ← hval y', hst]
      rfl
    | inr j =>
      refine ⟨⟨acc.2, j⟩, ?_, le_rfl, ?_⟩
      · intro g hg
        exact elim_ok n gs (initStats n false, []) (by simp) g hg
      · intro y
        change (⟨acc.2, j⟩ : Circuit).eval (List.ofFn y)
          = circuitFun (n + 1) C (Fin.snoc y false)
        rw [← hval y, hst]
        rfl
  have hsize' : C.size ≤ acc.2.length + 1 := hsize acc.2.length hcs
  have hcount_bound : acc.2.length + gs.countP (fun g => decide (n ∈ g.inputs)) ≤ C.size := by
    have h := elim_len_add_count_le n n gs (initStats n false, []) hnok
      (by simp [initStats]) ⟨false, getD_snoc_len _ _ _ _ (by simp)⟩
    simpa [acc, hgs, Circuit.size, List.length_nil, Nat.zero_add] using h
  have hcount_le : gs.countP (fun g => decide (n ∈ g.inputs)) ≤ 1 := by omega
  obtain ⟨j0, hj0⟩ := hex
  refine ⟨j0, (mem_normGate_inputs_iff n (C.gates.get j0)).1 hj0, ?_⟩
  intro j' hj'
  by_contra hne
  have hdec0 : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j0) = true := by
    simpa using hj0
  have hdecj : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j') = true := by
    simpa using (mem_normGate_inputs_iff n (C.gates.get j')).2 hj'
  have hij : j0.val ≠ j'.val := by
    intro h
    exact (Ne.symm hne) (Fin.ext h)
  have h2' := two_le_countP_of_two_getElem (fun g => decide (n ∈ (normGate g).inputs))
    C.gates j0.val j'.val j0.isLt j'.isLt hij hdec0 hdecj
  have h2 : 2 ≤ gs.countP (fun g => decide (n ∈ g.inputs)) := by
    rw [hgs, List.countP_map]
    exact h2'
  omega

end PEqualNP.Outside.L_meta_537_aux.M168

namespace PEqualNP.Outside.L_meta_537_aux.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


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


private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]


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

end PEqualNP.Outside.L_meta_537_aux.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_537_aux.Meta169 in
theorem PEqualNP.Outside.L_meta_537_aux.L_meta_169_thm : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
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

namespace PEqualNP.Outside.L_meta_537_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_537_aux.Helpers
open PEqualNP.Outside.L_meta_537_aux.Perm

private theorem list_map_id_mem {α : Type} {f : α → α} :
    ∀ {l : List α}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, h x List.mem_cons_self,
      list_map_id_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

private theorem circuitFun_eq_getD (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (wiresFrom C.gates (List.ofFn x)).getD C.output false := rfl

private theorem wiresFrom_getElem_gate {gs : List Gate} {w : List Bool} {j : ℕ}
    (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append]
  set W := wiresFrom (gs.take j) w
  have hW : W.length = w.length + j := by
    simp [W, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hstep : wiresFrom (gs[j] :: gs.drop (j + 1)) W =
      wiresFrom (gs.drop (j + 1)) (W ++ [(gs[j]).op.eval ((gs[j]).inputs.map fun i => W.getD i false)]) := rfl
  rw [hstep, getD_wiresFrom _ _ _ (by simp [hW]), ← hW, getD_snoc_eq]

private theorem wiresFrom_getD_take_eq {gs : List Gate} {w : List Bool} {j i : ℕ}
    (hj : j < gs.length) (hi : i < w.length + j) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    simp [length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  conv_rhs => rw [hsplit, wiresFrom_append]
  exact (getD_wiresFrom (gs.drop j) (wiresFrom (gs.take j) w) i (by omega)).symm

private theorem wiresFrom_gate_eval_rb {n : ℕ} {C : Circuit} (hrb : ReadsBack n C)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) :
    (wiresFrom C.gates (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (wiresFrom C.gates (List.ofFn x)).getD i false) := by
  have h1 := wiresFrom_getElem_gate (gs := C.gates) (w := List.ofFn x) hj
  simp only [List.length_ofFn] at h1
  have hga : gateAt C j = C.gates[j] := gateAt_eq_getElem hj
  rw [hga, h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hrb j hj i (hga ▸ hi)
  exact wiresFrom_getD_take_eq hj (by simp; exact hilt)

private theorem wiresFrom_input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [getD_wiresFrom _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

private theorem graphFun_erase {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (haA : a ∈ A) (x : Fin n → Bool) :
    graphFun K A x = (x a || graphFun K (A.erase a) x) := by
  unfold graphFun
  by_cases hxa : x a = true
  · simp [hxa, show ∃ b ∈ A, x b = true from ⟨a, haA, hxa⟩]
  · have hxaf : x a = false := Bool.eq_false_iff.2 hxa
    have hiff : (∃ b ∈ A, x b = true) ↔ (∃ b ∈ A.erase a, x b = true) := by
      constructor
      · rintro ⟨b, hbA, hxb⟩
        have hba : b ≠ a := fun h => hxa (h ▸ hxb)
        exact ⟨b, Finset.mem_erase.2 ⟨hba, hbA⟩, hxb⟩
      · rintro ⟨b, hbe, hxb⟩
        exact ⟨b, (Finset.mem_erase.1 hbe).2, hxb⟩
    simp [hxaf, hiff]

private theorem graphFun_erase_update {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (x : Fin n → Bool) (val : Bool) :
    graphFun K (A.erase a) (Function.update x a val) = graphFun K (A.erase a) x := by
  unfold graphFun
  have h1 : (∃ b ∈ A.erase a, Function.update x a val b = true) ↔
      (∃ b ∈ A.erase a, x b = true) := by
    constructor <;> rintro ⟨b, hb, hxb⟩ <;> refine ⟨b, hb, ?_⟩
    · rwa [Function.update_of_ne (Finset.mem_erase.1 hb).1] at hxb
    · rwa [Function.update_of_ne (Finset.mem_erase.1 hb).1]
  have h2 : (∃ u v, K.Adj u v ∧ Function.update x a val u = true ∧ Function.update x a val v = true) ↔
      (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true) := by
    constructor <;> rintro ⟨u, v, huv, hu, hv⟩
    · have hua : u ≠ a := fun h => hAdisj a haA v (h ▸ huv)
      have hva : v ≠ a := fun h => hAdisj a haA u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hu
      rw [Function.update_of_ne hva] at hv
      exact ⟨u, v, huv, hu, hv⟩
    · have hua : u ≠ a := fun h => hAdisj a haA v (h ▸ huv)
      have hva : v ≠ a := fun h => hAdisj a haA u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩
  simp only [h1, h2]

private theorem graphFun_update_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (x : Fin n → Bool) :
    graphFun K A (Function.update x a false) = graphFun K (A.erase a) x := by
  rw [graphFun_erase K A a haA, Function.update_self, Bool.false_or,
    graphFun_erase_update K A a hAdisj haA]

private theorem graphFun_update_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (haA : a ∈ A) (x : Fin n → Bool) :
    graphFun K A (Function.update x a true) = true := by
  rw [graphFun_erase K A a haA, Function.update_self, Bool.true_or]

private theorem graphFun_erase_nonconst {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (haA : a ∈ A)
    (hne : (∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card) :
    ∃ x0 x1 : Fin n → Bool,
      graphFun K (A.erase a) x0 = false ∧ graphFun K (A.erase a) x1 = true := by
  refine ⟨fun _ => false, ?_⟩
  rcases hne with ⟨u, v, huv⟩ | hcard
  · refine ⟨fun i => decide (i = u ∨ i = v), by simp [graphFun], ?_⟩
    unfold graphFun
    have h2 : ∃ u' v', K.Adj u' v' ∧ decide (u' = u ∨ u' = v) = true ∧ decide (v' = u ∨ v' = v) = true :=
      ⟨u, v, huv, by simp, by simp⟩
    simp only [h2, decide_true, Bool.or_true]
  · have hpos : 0 < (A.erase a).card := by
      rw [Finset.card_erase_of_mem haA]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
    refine ⟨fun i => decide (i = b), by simp [graphFun], ?_⟩
    unfold graphFun
    have h1 : ∃ c ∈ A.erase a, decide (c = b) = true := ⟨b, hb, by simp⟩
    simp only [h1, decide_true, Bool.true_or]

private theorem not_mem_minCover_of_isolated {n : ℕ} {K : SimpleGraph (Fin n)} {T : Finset (Fin n)}
    (hT : IsMinCover K T) (b : Fin n) (hb : ∀ v : Fin n, ¬ K.Adj b v) : b ∉ T := by
  intro hbT
  have hcov : K.IsVertexCover ((T.erase b : Finset (Fin n)) : Set (Fin n)) := by
    intro u v huv
    rcases hT.1 huv with hu | hv
    · have hub : u ≠ b := fun h => hb v (h ▸ huv)
      exact Or.inl (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hub, hu⟩))
    · have hvb : v ≠ b := fun h => hb u (h ▸ huv.symm)
      exact Or.inr (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvb, hv⟩))
  have hle := hT.2 (T.erase b) hcov
  have hlt : (T.erase b).card < T.card := Finset.card_erase_lt_of_mem hbT
  omega

private theorem exists_circuit (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ s, HasCircuitSize n f s := by
  obtain ⟨gs, out, hok, hlen, _, hev⟩ := shannon n f n (le_refl n)
  refine ⟨5 * 2 ^ n, ⟨gs, out⟩, hok, by change gs.length ≤ 5 * 2 ^ n; omega, ?_⟩
  intro x
  have h1 := hev (List.ofFn x) (by simp)
  have hf : (fun i : Fin n => (List.ofFn x).getD i false) = x := by
    funext i
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
  rw [hf] at h1
  exact h1

private theorem exists_minimal_circuit (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ C : Circuit, IsMinimalCircuit n C ∧ circuitFun n C = f := by
  classical
  have hex := exists_circuit n f
  obtain ⟨C, hfit, hsz, hev⟩ := Nat.find_spec hex
  have hcf : circuitFun n C = f := funext hev
  refine ⟨C, ⟨hfit, ?_⟩, hcf⟩
  intro D hDfit hDcf
  have hDhas : HasCircuitSize n f D.size := ⟨D, hDfit, le_refl _, fun x => by
    rw [← hcf]; exact congrFun hDcf x⟩
  have hmin : Nat.find hex ≤ D.size := Nat.find_min' hex hDhas
  omega

private theorem relabel_perm_fanInTwo {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : FanInTwo C) : FanInTwo (relabel n n σ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  exact ⟨(h g0 hg0).1, by simpa [relGate] using (h g0 hg0).2⟩

private theorem relabel_perm_size {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (relabel n n σ C).size = C.size := by
  simp [relabel, Circuit.size]

private theorem relabel_perm_circuitFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (x : Fin n → Bool) :
    circuitFun n (relabel n n σ C) x = circuitFun n C (x ∘ σ) := by
  exact (rel_fold n n σ C.gates _ _ (rel_init n n σ x)).2.2 C.output

private theorem relabel_perm_minimal {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : IsMinimalCircuit n C) : IsMinimalCircuit n (relabel n n σ C) := by
  refine ⟨relabel_perm_fanInTwo σ C h.1, ?_⟩
  intro D hDfit hDcf
  let D' := relabel n n σ.symm D
  have hD'cf : circuitFun n D' = circuitFun n C := by
    funext x
    rw [relabel_perm_circuitFun, hDcf, relabel_perm_circuitFun]
    congr 1
    funext i
    simp
  have hle := h.2 D' (relabel_perm_fanInTwo σ.symm D hDfit) hD'cf
  simpa [D', relabel_perm_size] using hle

private theorem wmap_perm_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) :
    wmap n n σ w = if h : w < n then (σ ⟨w, h⟩ : ℕ) else w := by
  unfold wmap
  split
  · rfl
  · omega

private theorem wmap_perm_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (j w : ℕ) :
    wmap n n σ w < n + j ↔ w < n + j := by
  rw [wmap_perm_eq]
  split
  · rename_i h
    have h2 := (σ ⟨w, h⟩).isLt
    omega
  · rfl

private theorem size_jump {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (hne : (∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card)
    (C0 : Circuit) (hC0min : IsMinimalCircuit n C0)
    (hC0fun : circuitFun n C0 = graphFun K (A.erase a)) :
    HasCircuitSize n (graphFun K A) (C0.size + 1) ∧
    (∀ D : Circuit, FanInTwo D → circuitFun n D = graphFun K A → C0.size + 1 ≤ D.size) := by
  obtain ⟨x0, x1, hx0, hx1⟩ := graphFun_erase_nonconst K A a haA hne
  constructor
  · have hout : C0.output < n + C0.gates.length := by
      by_contra hge
      push Not at hge
      have e1 : circuitFun n C0 x1 = true := by rw [hC0fun]; exact hx1
      have e2 : circuitFun n C0 x1 = false := by
        rw [circuitFun_eq_getD]
        exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
      rw [e2] at e1
      cases e1
    refine ⟨⟨C0.gates ++ [⟨GateOp.or, [C0.output, a.val]⟩], n + C0.gates.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hC0min.1 g hg
      · simp
    · simp [Circuit.size]
    · intro x
      set W := wiresFrom C0.gates (List.ofFn x)
      have hWlen : W.length = n + C0.gates.length := by
        simp [W, length_wiresFrom]
      have hWo : W.getD C0.output false = graphFun K (A.erase a) x := by
        rw [← hC0fun]; rfl
      have hWa : W.getD a.val false = x a := by
        rw [show W = wiresFrom C0.gates (List.ofFn x) from rfl,
          getD_wiresFrom _ _ _ (by simp [a.isLt]),
          List.getD_eq_getElem _ _ (by simp [a.isLt]), List.getElem_ofFn]
      change (wiresFrom (C0.gates ++ [⟨GateOp.or, [C0.output, a.val]⟩]) (List.ofFn x)).getD
        (n + C0.gates.length) false = graphFun K A x
      rw [wiresFrom_append, ← hWlen]
      change (W ++ [GateOp.or.eval [W.getD C0.output false, W.getD a.val false]]).getD
        W.length false = graphFun K A x
      rw [getD_snoc_eq, hWo, hWa, graphFun_erase K A a haA]
      simp [GateOp.eval, Bool.or_comm]
  · intro D hDfit hDfun
    cases n with
    | zero => exact Fin.elim0 a
    | succ n' =>
      have hpos : 1 ≤ D.size := by
        by_contra h0
        have hsz0 : D.size = 0 := by omega
        have hnil : D.gates = [] := List.eq_nil_of_length_eq_zero hsz0
        have hev : ∀ x, graphFun K A x = (List.ofFn x).getD D.output false := by
          intro x; rw [← hDfun]; simp [circuitFun, Circuit.eval, wires_eq, hnil, wiresFrom]
        by_cases ho : D.output < n' + 1
        · have hproj : ∀ x, graphFun K A x = x ⟨D.output, ho⟩ := by
            intro x; rw [hev x, List.getD_eq_getElem _ _ (by simp [ho]), List.getElem_ofFn]
          by_cases hka : (⟨D.output, ho⟩ : Fin (n' + 1)) = a
          · have h1 := hproj (Function.update x1 a false)
            rw [graphFun_update_false K A a hAdisj haA, hx1, hka, Function.update_self] at h1
            cases h1
          · have h1 := hproj (Function.update x0 a true)
            rw [graphFun_update_true K A a haA, Function.update_of_ne hka] at h1
            have h2 := hproj (Function.update x0 a false)
            rw [graphFun_update_false K A a hAdisj haA, hx0, Function.update_of_ne hka] at h2
            rw [← h2] at h1
            cases h1
        · have h1 := hev (Function.update x0 a true)
          rw [graphFun_update_true K A a haA, List.getD_eq_default _ _ (by simp; omega)] at h1
          cases h1
      set σ : Equiv.Perm (Fin (n' + 1)) := Equiv.swap a (Fin.last n')
      have hss : ∀ x : Fin (n' + 1) → Bool, (x ∘ σ) ∘ σ = x := by
        intro x; funext i; simp [σ]
      have hsnoc_swap : ∀ (x : Fin (n' + 1) → Bool) (b : Bool),
          Fin.snoc (fun j : Fin n' => x (σ j.castSucc)) b ∘ σ = Function.update x a b := by
        intro x b; funext i
        by_cases hia : i = a
        · rw [hia]
          have h1 : σ a = Fin.last n' := Equiv.swap_apply_left a (Fin.last n')
          simp [h1]
        · have hne' : σ i ≠ Fin.last n' := by
            intro h; apply hia; apply σ.injective; rw [h, Equiv.swap_apply_left]
          obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hne'
          simp only [Function.comp_apply, ← hj, Fin.snoc_castSucc, Function.update_of_ne hia]
          have h2 : σ (σ i) = i := Equiv.swap_apply_self a (Fin.last n') i
          rw [hj, h2]
      let f' : (Fin (n' + 1) → Bool) → Bool := fun x => graphFun K A (x ∘ σ)
      have hD' : HasCircuitSize (n' + 1) f' ((D.size - 1) + 1) := by
        rw [Nat.sub_add_cancel hpos]
        exact relabel_size σ (graphFun K A) D.size ⟨D, hDfit, le_refl _, fun x => congrFun hDfun x⟩
      have hdep : ∃ x : Fin (n' + 1) → Bool,
          f' (Function.update x (Fin.last n') (!x (Fin.last n'))) ≠ f' x := by
        refine ⟨Function.update x0 a false ∘ σ, ?_⟩
        have hsl : σ.symm (Fin.last n') = a := by
          simp [σ, Equiv.swap_apply_right]
        have hlast : (Function.update x0 a false ∘ σ) (Fin.last n') = false := by
          simp [σ, Equiv.swap_apply_right]
        simp only [f', hlast, Bool.not_false]
        rw [Function.update_comp_equiv, hsl, hss, Function.update_idem,
          graphFun_update_true K A a haA, graphFun_update_false K A a hAdisj haA, hx0]
        decide
      have hnc : ∃ y y' : Fin n' → Bool, f' (Fin.snoc y false) ≠ f' (Fin.snoc y' false) := by
        refine ⟨fun j => x0 (σ j.castSucc), fun j => x1 (σ j.castSucc), ?_⟩
        simp only [f', hsnoc_swap, graphFun_update_false K A a hAdisj haA, hx0, hx1]
        decide
      have helim := gate_elim n' f' false (D.size - 1) hdep hnc hD'
      have hback := relabel_size (fun j : Fin n' => σ j.castSucc) _ (D.size - 1) helim
      have heq : (fun x : Fin (n' + 1) → Bool =>
          f' (Fin.snoc (x ∘ fun j : Fin n' => σ j.castSucc) false)) = graphFun K (A.erase a) := by
        funext x
        simp only [f']
        have h1 := hsnoc_swap x false
        change graphFun K A (Fin.snoc (fun j : Fin n' => x (σ j.castSucc)) false ∘ σ) = _
        rw [h1, graphFun_update_false K A a hAdisj haA]
      rw [heq] at hback
      obtain ⟨E, hEfit, hEsz, hEev⟩ := hback
      have hEcf : circuitFun (n' + 1) E = circuitFun (n' + 1) C0 := by
        rw [hC0fun]; exact funext hEev
      have hmin := hC0min.2 E hEfit hEcf
      omega

private def readsEff (C : Circuit) (w : ℕ) (j : Fin C.gates.length) : Prop :=
  ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some w) ∨
  ((C.gates.get j).op ≠ GateOp.not ∧ w ∈ (C.gates.get j).inputs)

private theorem unique_or_reader {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (hne : (∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card)
    (C0 : Circuit) (hC0min : IsMinimalCircuit n C0)
    (hC0fun : circuitFun n C0 = graphFun K (A.erase a))
    (C : Circuit) (hCmin : IsMinimalCircuit n C) (hCfun : circuitFun n C = graphFun K A) :
    ∃ (p : Fin C.gates.length) (w : ℕ),
      readsEff C a.val p ∧
      (∀ j : Fin C.gates.length, readsEff C a.val j → j = p) ∧
      (gateAt C p.val).op = GateOp.or ∧
      ((gateAt C p.val).inputs = [a.val, w] ∨ (gateAt C p.val).inputs = [w, a.val]) ∧
      w ≠ a.val ∧ w < n + p.val := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n' =>
    obtain ⟨x0, x1, hx0, hx1⟩ := graphFun_erase_nonconst K A a haA hne
    obtain ⟨hup, hlo⟩ := size_jump K A a hAdisj haA hne C0 hC0min hC0fun
    have hCsz : C.size = C0.size + 1 := by
      obtain ⟨U, hUfit, hUsz, hUev⟩ := hup
      have h1 := hCmin.2 U hUfit (by rw [hCfun]; exact funext hUev)
      have h2 := hlo C hCmin.1 hCfun
      omega
    set σ : Equiv.Perm (Fin (n' + 1)) := Equiv.swap a (Fin.last n')
    have hσinv : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self a (Fin.last n') i
    have hsnoc_swap : ∀ (x : Fin (n' + 1) → Bool) (b : Bool),
        Fin.snoc (fun j : Fin n' => x (σ j.castSucc)) b ∘ σ = Function.update x a b := by
      intro x b; funext i
      by_cases hia : i = a
      · rw [hia]
        have h1 : σ a = Fin.last n' := Equiv.swap_apply_left a (Fin.last n')
        simp [h1]
      · have hne' : σ i ≠ Fin.last n' := by
          intro h; apply hia; apply σ.injective; rw [h, Equiv.swap_apply_left]
        obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hne'
        simp only [Function.comp_apply, ← hj, Fin.snoc_castSucc, Function.update_of_ne hia]
        rw [hj, hσinv]
    let Cσ := relabel (n' + 1) (n' + 1) σ C
    have hCσmin : IsMinimalCircuit (n' + 1) Cσ := relabel_perm_minimal σ C hCmin
    have hCσfun : ∀ x, circuitFun (n' + 1) Cσ x = graphFun K A (x ∘ σ) := by
      intro x; rw [relabel_perm_circuitFun, hCfun]
    have hdep : ∃ y : Fin n' → Bool,
        circuitFun (n' + 1) Cσ (Fin.snoc y false) ≠ circuitFun (n' + 1) Cσ (Fin.snoc y true) := by
      refine ⟨fun j => x0 (σ j.castSucc), ?_⟩
      rw [hCσfun, hCσfun, hsnoc_swap, hsnoc_swap,
        graphFun_update_false K A a hAdisj haA, graphFun_update_true K A a haA, hx0]
      decide
    have hnc : ∃ y y' : Fin n' → Bool,
        circuitFun (n' + 1) Cσ (Fin.snoc y false) ≠ circuitFun (n' + 1) Cσ (Fin.snoc y' false) := by
      refine ⟨fun j => x0 (σ j.castSucc), fun j => x1 (σ j.castSucc), ?_⟩
      rw [hCσfun, hCσfun, hsnoc_swap, hsnoc_swap,
        graphFun_update_false K A a hAdisj haA, graphFun_update_false K A a hAdisj haA, hx0, hx1]
      decide
    have hbound : ∀ s : ℕ, HasCircuitSize n' (fun y : Fin n' → Bool =>
        circuitFun (n' + 1) Cσ (Fin.snoc y false)) s → Cσ.size ≤ s + 1 := by
      intro s hs
      have hback := relabel_size (fun j : Fin n' => σ j.castSucc) _ s hs
      have heq : (fun x : Fin (n' + 1) → Bool =>
          circuitFun (n' + 1) Cσ (Fin.snoc (x ∘ fun j : Fin n' => σ j.castSucc) false)) =
          graphFun K (A.erase a) := by
        funext x
        rw [hCσfun]
        change graphFun K A (Fin.snoc (fun j : Fin n' => x (σ j.castSucc)) false ∘ σ) = _
        rw [hsnoc_swap, graphFun_update_false K A a hAdisj haA]
      rw [heq] at hback
      obtain ⟨E, hEfit, hEsz, hEev⟩ := hback
      have hmin := hC0min.2 E hEfit (by rw [hC0fun]; exact funext hEev)
      have hCσsz : Cσ.size = C.size := relabel_perm_size σ C
      omega
    obtain ⟨pσ, hpσ_read, hpσ_uniq⟩ := M168.L_meta_168 n' Cσ hCσmin hdep hnc hbound
    have hpσ_or := L_meta_169_thm n' Cσ hCσmin hdep hnc hbound pσ hpσ_read
    have hlen : Cσ.gates.length = C.gates.length := by simp [Cσ, relabel]
    have hwmap_eq_n : ∀ u, wmap (n' + 1) (n' + 1) σ u = n' ↔ u = a.val := by
      intro u
      rw [wmap_perm_eq]
      split
      · rename_i hu
        constructor
        · intro h
          have h1 : σ ⟨u, hu⟩ = Fin.last n' := Fin.ext h
          have h2 : (⟨u, hu⟩ : Fin (n' + 1)) = a := by
            have := congrArg σ h1
            simpa [hσinv, σ, Equiv.swap_apply_right] using this
          exact congrArg Fin.val h2
        · intro h
          have h1 : (⟨u, hu⟩ : Fin (n' + 1)) = a := Fin.ext h
          rw [h1]
          exact congrArg Fin.val (Equiv.swap_apply_left a (Fin.last n'))
      · rename_i hu
        constructor <;> intro h <;> have := a.isLt <;> omega
    have hget : ∀ (j : Fin C.gates.length),
        Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩ = relGate (n' + 1) (n' + 1) σ (C.gates.get j) := by
      intro j; simp [Cσ, relabel]
    have hreads_iff : ∀ (j : Fin C.gates.length),
        readsEff C a.val j ↔
          ((Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).op = GateOp.not ∧
            (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).inputs.head? = some n' ∨
           (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).op ≠ GateOp.not ∧
            n' ∈ (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).inputs) := by
      intro j
      rw [hget j]
      simp only [readsEff, relGate, List.head?_map, List.mem_map]
      constructor
      · rintro (⟨hop, hhd⟩ | ⟨hop, hmem⟩)
        · left; refine ⟨hop, ?_⟩
          rw [hhd]; simp [(hwmap_eq_n a.val).2 rfl]
        · right; exact ⟨hop, a.val, hmem, (hwmap_eq_n a.val).2 rfl⟩
      · rintro (⟨hop, hhd⟩ | ⟨hop, u, hu, hwu⟩)
        · left; refine ⟨hop, ?_⟩
          cases h : (C.gates.get j).inputs with
          | nil => rw [h] at hhd; simp at hhd
          | cons u tl =>
            rw [h] at hhd
            simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
            simp [(hwmap_eq_n u).1 hhd]
        · right; rw [(hwmap_eq_n u).1 hwu] at hu; exact ⟨hop, hu⟩
    let p : Fin C.gates.length := ⟨pσ.val, hlen ▸ pσ.isLt⟩
    have hp_get : Cσ.gates.get pσ = relGate (n' + 1) (n' + 1) σ (C.gates.get p) := hget p
    obtain ⟨hop, hinlen, _, wσ, hwσ_mem, hwσ_ne, hwσ_lt⟩ := hpσ_or
    rw [hp_get] at hop hinlen hwσ_mem
    simp only [relGate, List.length_map, List.mem_map] at hop hinlen hwσ_mem
    obtain ⟨w, hw_mem, rfl⟩ := hwσ_mem
    have hw_ne : w ≠ a.val := fun h => hwσ_ne ((hwmap_eq_n w).2 h)
    have hw_lt : w < n' + 1 + p.val := (wmap_perm_lt_iff σ p.val w).1 hwσ_lt
    have hp_read : readsEff C a.val p := (hreads_iff p).2 hpσ_read
    have hp_uniq : ∀ j : Fin C.gates.length, readsEff C a.val j → j = p := by
      intro j hj
      have hjσ := (hreads_iff j).1 hj
      have heq := hpσ_uniq ⟨j.val, hlen.symm ▸ j.isLt⟩ hjσ
      have hval : j.val = pσ.val := congrArg Fin.val heq
      exact Fin.ext hval
    have hga : gateAt C p.val = C.gates.get p := gateAt_eq_getElem p.isLt
    have ha_mem : a.val ∈ (C.gates.get p).inputs := by
      rcases hp_read with ⟨hnot, _⟩ | ⟨_, hmem⟩
      · rw [hop] at hnot; cases hnot
      · exact hmem
    have hins : (C.gates.get p).inputs = [a.val, w] ∨ (C.gates.get p).inputs = [w, a.val] := by
      rcases hlist : (C.gates.get p).inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
      · rw [hlist] at hinlen; simp at hinlen
      · rw [hlist] at hinlen; simp at hinlen
      · rw [hlist] at ha_mem hw_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_mem hw_mem
        rcases ha_mem with rfl | rfl <;> rcases hw_mem with rfl | rfl
        · exact (hw_ne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hw_ne rfl).elim
      · rw [hlist] at hinlen; simp at hinlen
    exact ⟨p, w, hp_read, hp_uniq, hga ▸ hop, hga ▸ hins, hw_ne, hw_lt⟩

private def rd (n p w u : ℕ) : ℕ :=
  if u < n + p then u else if u = n + p then w else u - 1

private def shiftIdx (p j : ℕ) : ℕ :=
  if j < p then j else j + 1

private def unshiftIdx (p j : ℕ) : ℕ :=
  if j < p then j else j - 1

private def shiftW (n p u : ℕ) : ℕ :=
  if u < n + p then u else u + 1

private def delGate (n p w : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rd n p w)⟩

private def rdelGates (n p w : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map (delGate n p w)

private def rdelC (n p w : ℕ) (C : Circuit) : Circuit :=
  ⟨rdelGates n p w C.gates, rd n p w C.output⟩

private theorem rd_shiftW (n p w u : ℕ) : rd n p w (shiftW n p u) = u := by
  unfold rd shiftW; split_ifs <;> omega

private theorem shiftW_rd (n p w u : ℕ) (hu : u ≠ n + p) : shiftW n p (rd n p w u) = u := by
  unfold rd shiftW; split_ifs <;> omega

private theorem shiftW_lt (n p u : ℕ) (h : u < n + p) : shiftW n p u = u := by
  unfold shiftW; simp [h]

private theorem shiftW_inj (n p : ℕ) : Function.Injective (shiftW n p) := by
  intro u v h
  have := congrArg (rd n p 0) h
  simpa [rd_shiftW] using this

private theorem shiftIdx_inj (p : ℕ) : Function.Injective (shiftIdx p) := by
  intro i j h
  unfold shiftIdx at h
  split_ifs at h <;> omega

private theorem shiftW_add (n p j : ℕ) : shiftW n p (n + j) = n + shiftIdx p j := by
  unfold shiftW shiftIdx; split_ifs <;> omega

private theorem shiftW_ne_mid (n p u : ℕ) : shiftW n p u ≠ n + p := by
  unfold shiftW; split_ifs <;> omega

private theorem shiftIdx_ne (p j : ℕ) : shiftIdx p j ≠ p := by
  unfold shiftIdx; split_ifs <;> omega

private theorem unshiftIdx_shiftIdx (p j : ℕ) : unshiftIdx p (shiftIdx p j) = j := by
  unfold unshiftIdx shiftIdx; split_ifs <;> omega

private theorem shiftIdx_unshiftIdx (p j : ℕ) (hj : j ≠ p) : shiftIdx p (unshiftIdx p j) = j := by
  unfold unshiftIdx shiftIdx; split_ifs <;> omega

private theorem rd_add_of_ne (n p w j : ℕ) (hj : j ≠ p) :
    rd n p w (n + j) = n + unshiftIdx p j := by
  unfold rd unshiftIdx; split_ifs <;> omega

private theorem rdelGates_length (n p w : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdelGates n p w gs).length + 1 = gs.length := by
  simp [rdelGates, List.length_take, List.length_drop]; omega

private theorem shiftIdx_lt_of_rdel {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    {j' : ℕ} (hj' : j' < (rdelC n p w C).gates.length) : shiftIdx p j' < C.gates.length := by
  have hlen := rdelGates_length n p w C.gates hp
  change j' < (rdelGates n p w C.gates).length at hj'
  unfold shiftIdx; split_ifs <;> omega

private theorem unshiftIdx_lt_rdel {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    {j : ℕ} (hj : j < C.gates.length) (hjp : j ≠ p) :
    unshiftIdx p j < (rdelC n p w C).gates.length := by
  have hlen := rdelGates_length n p w C.gates hp
  change unshiftIdx p j < (rdelGates n p w C.gates).length
  unfold unshiftIdx; split_ifs <;> omega

private theorem rdelC_fanInTwo (n p w : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (rdelC n p w C) := by
  intro g hg
  simp only [rdelC, rdelGates, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · have h0 := h g0 (List.mem_of_mem_drop hg0)
    exact ⟨h0.1, by simpa [delGate] using h0.2⟩

private theorem gateAt_rdelC_lt {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    {j' : ℕ} (hj' : j' < p) :
    gateAt (rdelC n p w C) j' = gateAt C j' := by
  have hlen := rdelGates_length n p w C.gates hp
  have hj1 : j' < (rdelC n p w C).gates.length := by change j' < (rdelGates n p w C.gates).length; omega
  have hj2 : j' < C.gates.length := by omega
  have htk : (C.gates.take p).length = p := by simp [List.length_take]; omega
  rw [gateAt_eq_getElem hj1, gateAt_eq_getElem hj2]
  simp only [rdelC, rdelGates, List.getElem_append, htk, hj', ↓reduceDIte, List.getElem_take]

private theorem gateAt_rdelC_ge {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    {j' : ℕ} (hj1 : p ≤ j') (hj2 : j' < (rdelC n p w C).gates.length) :
    gateAt (rdelC n p w C) j' = delGate n p w (gateAt C (j' + 1)) := by
  have hlen := rdelGates_length n p w C.gates hp
  have hj2' : j' < (rdelGates n p w C.gates).length := hj2
  have hjC : j' + 1 < C.gates.length := by omega
  have htk : (C.gates.take p).length = p := by simp [List.length_take]; omega
  have hnotlt : ¬ j' < p := by omega
  rw [gateAt_eq_getElem hj2, gateAt_eq_getElem hjC]
  simp only [rdelC, rdelGates, List.getElem_append, htk, hnotlt, ↓reduceDIte, List.getElem_map,
    List.getElem_drop]
  have heq : p + 1 + (j' - p) = j' + 1 := by omega
  simp [heq]

private theorem gateAt_rdelC_of_rb {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb : ReadsBack n C) {j' : ℕ} (hj' : j' < (rdelC n p w C).gates.length) :
    gateAt (rdelC n p w C) j' = delGate n p w (gateAt C (shiftIdx p j')) := by
  by_cases hlt : j' < p
  · rw [gateAt_rdelC_lt hp hlt, show shiftIdx p j' = j' by simp [shiftIdx, hlt]]
    unfold delGate
    cases hg : gateAt C j' with
    | mk op ins =>
      congr 1
      symm
      apply list_map_id_mem
      intro i hi
      have hlti : i < n + j' := hrb j' (by omega) i (by rw [hg]; exact hi)
      unfold rd; simp [show i < n + p by omega]
  · rw [gateAt_rdelC_ge hp (by omega) hj', show shiftIdx p j' = j' + 1 by simp [shiftIdx, hlt]]

private theorem readsBack_of_rdelC {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb' : ReadsBack n (rdelC n p w C))
    (hp_rb : ∀ i ∈ (gateAt C p).inputs, i < n + p) :
    ReadsBack n C := by
  intro j hj i hi
  have hlen := rdelGates_length n p w C.gates hp
  rcases Nat.lt_trichotomy j p with hlt | rfl | hgt
  · have hga := gateAt_rdelC_lt (n := n) (w := w) hp hlt
    have hj' : j < (rdelC n p w C).gates.length := by change j < (rdelGates n p w C.gates).length; omega
    exact hrb' j hj' i (hga.symm ▸ hi)
  · exact hp_rb i hi
  · have hj' : j - 1 < (rdelC n p w C).gates.length := by change j - 1 < (rdelGates n p w C.gates).length; omega
    have hga := gateAt_rdelC_ge (n := n) (w := w) hp (j' := j - 1) (by omega) hj'
    have hj1 : j - 1 + 1 = j := by omega
    rw [hj1] at hga
    have hmem : rd n p w i ∈ (gateAt (rdelC n p w C) (j - 1)).inputs := by
      rw [hga]; exact List.mem_map_of_mem hi
    have hlt' := hrb' (j - 1) hj' (rd n p w i) hmem
    unfold rd at hlt'
    split_ifs at hlt' <;> omega

private theorem readsBack_rdelC {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hw : w < n + p) (hrb : ReadsBack n C) :
    ReadsBack n (rdelC n p w C) := by
  intro j' hj' i' hi'
  rw [gateAt_rdelC_of_rb hp hrb hj'] at hi'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
  have hlt := hrb (shiftIdx p j') (shiftIdx_lt_of_rdel hp hj') i hi
  unfold rd shiftIdx at *
  split_ifs at * <;> omega

private theorem rdel_eval_suffix (n p w : ℕ) (hw : w < n + p) (gs : List Gate) :
    ∀ (WC WC' : List Bool),
      WC.length = WC'.length + 1 → n + p ≤ WC'.length →
      (∀ u : ℕ, WC'.getD (rd n p w u) false = WC.getD u false) →
      ∀ u : ℕ, (wiresFrom (gs.map (delGate n p w)) WC').getD (rd n p w u) false =
        (wiresFrom gs WC).getD u false := by
  induction gs with
  | nil => intro WC WC' _ _ h u; exact h u
  | cons g gs ih =>
    intro WC WC' hlen hge h u
    have hev : (delGate n p w g).op.eval ((delGate n p w g).inputs.map fun i => WC'.getD i false) =
        g.op.eval (g.inputs.map fun i => WC.getD i false) := by
      simp only [delGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    change (wiresFrom (gs.map (delGate n p w))
        (WC' ++ [(delGate n p w g).op.eval ((delGate n p w g).inputs.map fun i => WC'.getD i false)])).getD
        (rd n p w u) false =
      (wiresFrom gs (WC ++ [g.op.eval (g.inputs.map fun i => WC.getD i false)])).getD u false
    rw [hev]
    apply ih
    · simp; omega
    · simp; omega
    · intro v
      rcases Nat.lt_trichotomy v WC.length with hv | hv | hv
      · have hv' : rd n p w v < WC'.length := by unfold rd; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hv', List.getD_append _ _ _ _ hv]
        exact h v
      · have hv' : rd n p w v = WC'.length := by unfold rd; split_ifs <;> omega
        rw [hv', hv, getD_snoc_eq, getD_snoc_eq]
      · have hv' : WC'.length + 1 ≤ rd n p w v := by unfold rd; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem rdel_eval {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length) (hw : w < n + p)
    (x : Fin n → Bool)
    (heq : (wiresFrom C.gates (List.ofFn x)).getD (n + p) false =
      (wiresFrom C.gates (List.ofFn x)).getD w false) :
    ∀ u : ℕ, (wiresFrom (rdelC n p w C).gates (List.ofFn x)).getD (rd n p w u) false =
      (wiresFrom C.gates (List.ofFn x)).getD u false := by
  have hsplit : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
    have h1 := (List.take_append_drop p C.gates).symm
    rw [List.drop_eq_getElem_cons hp] at h1
    exact h1
  set W0 := wiresFrom (C.gates.take p) (List.ofFn x)
  have hW0len : W0.length = n + p := by
    simp [W0, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hp)]
  have hCsplit : wiresFrom C.gates (List.ofFn x) =
      wiresFrom (C.gates.drop (p + 1)) (W0 ++ [(C.gates[p]).op.eval ((C.gates[p]).inputs.map fun i => W0.getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]
    rfl
  have hC'split : wiresFrom (rdelC n p w C).gates (List.ofFn x) =
      wiresFrom ((C.gates.drop (p + 1)).map (delGate n p w)) W0 := by
    simp [rdelC, rdelGates, wiresFrom_append, W0]
  set b := (C.gates[p]).op.eval ((C.gates[p]).inputs.map fun i => W0.getD i false)
  have hb : b = W0.getD w false := by
    have h1 : (wiresFrom C.gates (List.ofFn x)).getD (n + p) false = b := by
      rw [hCsplit, getD_wiresFrom _ _ _ (by simp [hW0len]), ← hW0len, getD_snoc_eq]
    have h2 : (wiresFrom C.gates (List.ofFn x)).getD w false = W0.getD w false := by
      rw [hCsplit, getD_wiresFrom _ _ _ (by simp [hW0len]; omega),
        List.getD_append _ _ _ _ (by omega)]
    rw [← h1, heq, h2]
  intro u
  rw [hC'split, hCsplit]
  apply rdel_eval_suffix n p w hw (C.gates.drop (p + 1)) (W0 ++ [b]) W0
  · simp
  · omega
  · intro v
    unfold rd
    split_ifs with h1 h2
    · rw [List.getD_append _ _ _ _ (by omega)]
    · rw [h2, ← hW0len, getD_snoc_eq, hb]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem wiresFrom_agree_off_a (a : ℕ) (gs : List Gate)
    (hno : ∀ g ∈ gs, (g.op = GateOp.not → g.inputs.head? ≠ some a) ∧
      (g.op ≠ GateOp.not → a ∉ g.inputs)) :
    ∀ (w w' : List Bool), w.length = w'.length → a < w.length →
      (∀ i, i ≠ a → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ a → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ hag i hi; exact hag i hi
  | cons g gs ih =>
    intro w w' hlen ha hag i hi
    have hg := hno g List.mem_cons_self
    have hev : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => w'.getD k false) := by
      by_cases hnot : g.op = GateOp.not
      · rw [hnot]
        cases hins : g.inputs with
        | nil => rfl
        | cons u tl =>
          have hua : u ≠ a := fun h => hg.1 hnot (by simp [hins, h])
          simp only [List.map_cons, GateOp.eval, List.headD_cons]
          rw [hag u hua]
      · congr 1
        apply List.map_congr_left
        intro u hu
        have hua : u ≠ a := fun h => hg.2 hnot (h ▸ hu)
        exact hag u hua
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).getD i false =
      (wiresFrom gs (w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)])).getD i false
    rw [hev]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))
    · simp [hlen]
    · simp; omega
    · intro k hk
      by_cases hkl : k < w.length
      · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (by omega)]
        exact hag k hk
      · by_cases hke : k = w.length
        · subst hke; rw [getD_snoc_eq, hlen, getD_snoc_eq]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hi

private theorem wiresFrom_agree_off_two (a b : ℕ) (gs : List Gate)
    (hno : ∀ g ∈ gs, a ∉ g.inputs ∧ b ∉ g.inputs) :
    ∀ (w w' : List Bool), w.length = w'.length → a < w.length → b < w.length →
      (∀ i, i ≠ a → i ≠ b → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ a → i ≠ b → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ _ hag i hi1 hi2; exact hag i hi1 hi2
  | cons g gs ih =>
    intro w w' hlen ha hb hag i hi1 hi2
    have hg := hno g List.mem_cons_self
    have hev : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => w'.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro u hu
      exact hag u (fun h => hg.1 (h ▸ hu)) (fun h => hg.2 (h ▸ hu))
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).getD i false =
      (wiresFrom gs (w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)])).getD i false
    rw [hev]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))
    · simp [hlen]
    · simp; omega
    · simp; omega
    · intro k hk1 hk2
      by_cases hkl : k < w.length
      · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (by omega)]
        exact hag k hk1 hk2
      · by_cases hke : k = w.length
        · subst hke; rw [getD_snoc_eq, hlen, getD_snoc_eq]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hi1
    · exact hi2

private theorem count_map_rd_eq_w {n p w : ℕ} (hw : w < n + p) :
    ∀ l : List ℕ, (l.map (rd n p w)).count w = l.count w + l.count (n + p)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.count_cons, count_map_rd_eq_w hw xs]
    by_cases hxw : x = w
    · rw [hxw]
      have hne : w ≠ n + p := by omega
      have h1 : rd n p w w = w := by unfold rd; simp [hw]
      simp [h1, hne]; omega
    · by_cases hxp : x = n + p
      · rw [hxp]
        have h1 : rd n p w (n + p) = w := by unfold rd; simp
        have hne : n + p ≠ w := by omega
        simp [h1, hne]; omega
      · have h1 : rd n p w x ≠ w := by unfold rd; split_ifs <;> omega
        simp [h1, hxw, hxp]

private theorem count_map_rd_ne_w {n p w u' : ℕ} (hu : u' ≠ w) :
    ∀ l : List ℕ, (l.map (rd n p w)).count u' = l.count (shiftW n p u')
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.count_cons, count_map_rd_ne_w hu xs]
    have hiff : rd n p w x = u' ↔ x = shiftW n p u' := by
      constructor
      · intro h
        by_cases hxp : x = n + p
        · rw [hxp] at h
          have : rd n p w (n + p) = w := by unfold rd; simp
          rw [this] at h; exact (hu h.symm).elim
        · rw [← h, shiftW_rd n p w x hxp]
      · intro h; rw [h, rd_shiftW]
    by_cases h : x = shiftW n p u'
    · have h' : rd n p w x = u' := hiff.2 h
      rw [h', h]; simp
    · have h' : rd n p w x ≠ u' := fun e => h (hiff.1 e)
      simp [h, h']

private theorem orTree_rho_mem {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (htree : IsOrTree n C G L ρ) : ρ ∈ L ∨ (n ≤ ρ ∧ ρ - n ∈ G) := by
  have h4 := htree.2.2.2
  by_cases hGe : G = ∅
  · simp only [hGe, ↓reduceIte] at h4
    left; rw [h4]; exact Finset.mem_singleton_self ρ
  · simp only [hGe, ↓reduceIte] at h4
    obtain ⟨j, hjG, hρ⟩ := h4
    right; rw [hρ]; exact ⟨by omega, by simpa using hjG⟩

private theorem orTree_le_root {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hrb : ReadsBack n C) (hG : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → u ≤ ρ := by
  have hmain : ∀ (k u : ℕ), n + C.gates.length - u ≤ k →
      (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → u ≤ ρ := by
    intro k
    induction k with
    | zero =>
      intro u hk hu
      by_cases heq : u = ρ
      · omega
      · have h1 : readsIn C G u = 1 := by
          rcases hu with huL | ⟨hnu, huG⟩
          · rw [(htree.2.1 u huL).2, if_neg heq]
          · have h2 := htree.2.2.1 (u - n) huG
            rw [Nat.add_sub_cancel' hnu] at h2
            rw [h2, if_neg heq]
        obtain ⟨j, hjG, hcnt⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by change readsIn C G u ≠ 0; omega)
        have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.1 (Nat.pos_of_ne_zero hcnt)
        have hlt := hrb j (hG j hjG) u hmem
        have hjlt := hG j hjG
        omega
    | succ k ih =>
      intro u hk hu
      by_cases heq : u = ρ
      · omega
      · have h1 : readsIn C G u = 1 := by
          rcases hu with huL | ⟨hnu, huG⟩
          · rw [(htree.2.1 u huL).2, if_neg heq]
          · have h2 := htree.2.2.1 (u - n) huG
            rw [Nat.add_sub_cancel' hnu] at h2
            rw [h2, if_neg heq]
        obtain ⟨j, hjG, hcnt⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by change readsIn C G u ≠ 0; omega)
        have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.1 (Nat.pos_of_ne_zero hcnt)
        have hlt := hrb j (hG j hjG) u hmem
        have hle := ih (n + j) (by omega) (Or.inr ⟨by omega, by simpa using hjG⟩)
        omega
  intro u hu
  exact hmain (n + C.gates.length - u) u (le_refl _) hu

private theorem orTree_true_up {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hrb : ReadsBack n C) (hG : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) →
      (wiresFrom C.gates (List.ofFn x)).getD u false = true →
      (wiresFrom C.gates (List.ofFn x)).getD ρ false = true := by
  have hmain : ∀ (k u : ℕ), n + C.gates.length - u ≤ k →
      (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) →
      (wiresFrom C.gates (List.ofFn x)).getD u false = true →
      (wiresFrom C.gates (List.ofFn x)).getD ρ false = true := by
    intro k
    induction k with
    | zero =>
      intro u hk hu hval
      by_cases heq : u = ρ
      · rwa [← heq]
      · have h1 : readsIn C G u = 1 := by
          rcases hu with huL | ⟨hnu, huG⟩
          · rw [(htree.2.1 u huL).2, if_neg heq]
          · have h2 := htree.2.2.1 (u - n) huG
            rw [Nat.add_sub_cancel' hnu] at h2
            rw [h2, if_neg heq]
        obtain ⟨j, hjG, hcnt⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by change readsIn C G u ≠ 0; omega)
        have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.1 (Nat.pos_of_ne_zero hcnt)
        have hlt := hrb j (hG j hjG) u hmem
        have hjlt := hG j hjG
        omega
    | succ k ih =>
      intro u hk hu hval
      by_cases heq : u = ρ
      · rwa [← heq]
      · have h1 : readsIn C G u = 1 := by
          rcases hu with huL | ⟨hnu, huG⟩
          · rw [(htree.2.1 u huL).2, if_neg heq]
          · have h2 := htree.2.2.1 (u - n) huG
            rw [Nat.add_sub_cancel' hnu] at h2
            rw [h2, if_neg heq]
        obtain ⟨j, hjG, hcnt⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by change readsIn C G u ≠ 0; omega)
        have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.1 (Nat.pos_of_ne_zero hcnt)
        have hlt := hrb j (hG j hjG) u hmem
        have hop := (htree.1 j hjG).1
        have hlen := (htree.1 j hjG).2.1
        have hjval : (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = true := by
          rw [wiresFrom_gate_eval_rb hrb x (hG j hjG), hop]
          rcases hins : (gateAt C j).inputs with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩
          · rw [hins] at hlen; simp at hlen
          · rw [hins] at hlen; simp at hlen
          · rw [hins] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            simp only [List.map_cons, List.map_nil, GateOp.eval]
            rcases hmem with rfl | rfl
            · rw [hval]; rfl
            · rw [hval]; simp
          · rw [hins] at hlen; simp at hlen
        exact ih (n + j) (by omega) (Or.inr ⟨by omega, by simpa using hjG⟩) hjval
  intro u hu hval
  exact hmain (n + C.gates.length - u) u (le_refl _) hu hval

private theorem centreFlags_step_suffix (n p w : ℕ) (d d' : NCCData n) (gs : List Gate) :
    ∀ (FC FC' : List Bool),
      FC.length = FC'.length + 1 → n + p ≤ FC'.length →
      (∀ (k : ℕ) (hk : k < gs.length),
        d.role (FC.length - n + k) = d'.role (FC'.length - n + k) ∧
        ((d'.role (FC'.length - n + k)).1 = Kind.z → n + p ∉ (gs[k]'hk).inputs)) →
      (∀ u : ℕ, FC.getD (shiftW n p u) false = FC'.getD u false) →
      ∀ u : ℕ,
        (gs.foldl
          (fun fl g => fl ++ [decide ((d.role (fl.length - n)).1 = Kind.z) &&
            g.inputs.any (fun i => fl.getD i false)]) FC).getD (shiftW n p u) false =
        ((gs.map (delGate n p w)).foldl
          (fun fl g => fl ++ [decide ((d'.role (fl.length - n)).1 = Kind.z) &&
            g.inputs.any (fun i => fl.getD i false)]) FC').getD u false := by
  induction gs with
  | nil => intro FC FC' _ _ _ h u; exact h u
  | cons g gs ih =>
    intro FC FC' hlen hge hrole h u
    have h0 := hrole 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have hbit :
        (decide ((d.role (FC.length - n)).1 = Kind.z) && g.inputs.any (fun i => FC.getD i false)) =
        (decide ((d'.role (FC'.length - n)).1 = Kind.z) &&
          (delGate n p w g).inputs.any (fun i => FC'.getD i false)) := by
      rw [h0.1]
      by_cases hz : (d'.role (FC'.length - n)).1 = Kind.z
      · simp only [hz, decide_true, Bool.true_and, delGate, List.any_map]
        have hno := h0.2 hz
        have hfun : ∀ i ∈ g.inputs, FC.getD i false = FC'.getD (rd n p w i) false := by
          intro i hi
          have hne : i ≠ n + p := fun e => hno (e ▸ hi)
          have h1 := h (rd n p w i)
          rwa [shiftW_rd n p w i hne] at h1
        clear h0 hrole h hz
        generalize g.inputs = l at hfun ⊢
        induction l with
        | nil => rfl
        | cons a tl ihl =>
          simp only [List.any_cons, Function.comp_apply]
          rw [hfun a List.mem_cons_self, ihl (fun i hi => hfun i (List.mem_cons_of_mem a hi))]
      · simp [hz]
    simp only [List.map_cons, List.foldl_cons, hbit]
    apply ih
    · simp; omega
    · simp; omega
    · intro k hk
      have h1 := hrole (k + 1) (by simp; omega)
      have ha1 : (FC ++ [decide ((d'.role (FC'.length - n)).1 = Kind.z) &&
          (delGate n p w g).inputs.any (fun i => FC'.getD i false)]).length - n + k =
          FC.length - n + (k + 1) := by simp; omega
      have ha2 : (FC' ++ [decide ((d'.role (FC'.length - n)).1 = Kind.z) &&
          (delGate n p w g).inputs.any (fun i => FC'.getD i false)]).length - n + k =
          FC'.length - n + (k + 1) := by simp; omega
      rw [ha1, ha2]
      exact h1
    · intro v
      rcases Nat.lt_trichotomy v FC'.length with hv | hv | hv
      · have hvC : shiftW n p v < FC.length := by unfold shiftW; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hvC, List.getD_append _ _ _ _ hv]
        exact h v
      · have hvC : shiftW n p v = FC.length := by unfold shiftW; split_ifs <;> omega
        rw [hvC, hv, getD_snoc_eq, getD_snoc_eq]
      · have hvC : FC.length + 1 ≤ shiftW n p v := by unfold shiftW; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem centreFlags_prefix_eq (n : ℕ) (d d' : NCCData n) (gs : List Gate)
    (F : List Bool) (hge : n ≤ F.length)
    (hrole : ∀ k < gs.length, d.role (F.length - n + k) = d'.role (F.length - n + k)) :
    gs.foldl (fun fl g => fl ++ [decide ((d.role (fl.length - n)).1 = Kind.z) &&
      g.inputs.any (fun i => fl.getD i false)]) F =
    gs.foldl (fun fl g => fl ++ [decide ((d'.role (fl.length - n)).1 = Kind.z) &&
      g.inputs.any (fun i => fl.getD i false)]) F := by
  induction gs generalizing F with
  | nil => rfl
  | cons g gs ih =>
    have h0 := hrole 0 (by simp)
    simp only [add_zero] at h0
    simp only [List.foldl_cons, h0]
    apply ih
    · simp; omega
    · intro k hk
      have h1 := hrole (k + 1) (by simp; omega)
      have ha : (F ++ [decide ((d'.role (F.length - n)).1 = Kind.z) &&
          g.inputs.any (fun i => F.getD i false)]).length - n + k = F.length - n + (k + 1) := by
        simp; omega
      rw [ha]; exact h1

private theorem foldl_append_length {α β : Type} (f : List α → β → α) (gs : List β) :
    ∀ L : List α, (gs.foldl (fun fl g => fl ++ [f fl g]) L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp
  | cons g gs ih => intro L; simp [ih]; omega

private theorem isCentred_shiftW {n p w : ℕ} {C : Circuit} {d d' : NCCData n}
    (hp : p < C.gates.length) (hcov : d.cover = d'.cover)
    (hrp : (d.role p).1 = Kind.top)
    (hrole : ∀ j' < (rdelC n p w C).gates.length, d.role (shiftIdx p j') = d'.role j')
    (hnoz : ∀ j' < (rdelC n p w C).gates.length, (d'.role j').1 = Kind.z →
      n + p ∉ (gateAt C (shiftIdx p j')).inputs) :
    ∀ u : ℕ, IsCentred n C d (shiftW n p u) ↔ IsCentred n (rdelC n p w C) d' u := by
  have hlen := rdelGates_length n p w C.gates hp
  have hsplit : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
    have h1 := (List.take_append_drop p C.gates).symm
    rw [List.drop_eq_getElem_cons hp] at h1
    exact h1
  let stepC := fun (fl : List Bool) (g : Gate) =>
    fl ++ [decide ((d.role (fl.length - n)).1 = Kind.z) && g.inputs.any (fun i => fl.getD i false)]
  let stepC' := fun (fl : List Bool) (g : Gate) =>
    fl ++ [decide ((d'.role (fl.length - n)).1 = Kind.z) && g.inputs.any (fun i => fl.getD i false)]
  let Finit : List Bool := List.ofFn fun i : Fin n => decide (i ∈ d.cover)
  have hFinit' : (List.ofFn fun i : Fin n => decide (i ∈ d'.cover)) = Finit := by
    simp [Finit, hcov]
  let F0 := (C.gates.take p).foldl stepC' Finit
  have hF0eq : (C.gates.take p).foldl stepC Finit = F0 := by
    apply centreFlags_prefix_eq n d d' (C.gates.take p) Finit (by simp [Finit])
    intro k hk
    have hkp : k < p := by
      have : (C.gates.take p).length = p := by simp [List.length_take]; omega
      omega
    have hk' : k < (rdelC n p w C).gates.length := by change k < (rdelGates n p w C.gates).length; omega
    have h1 := hrole k hk'
    have h2 : Finit.length - n + k = k := by simp [Finit]
    rw [h2, ← h1]; simp [shiftIdx, hkp]
  have hF0len : F0.length = n + p := by
    dsimp only [F0, stepC']
    rw [foldl_append_length]
    simp [Finit, List.length_take]; omega
  have hflag_eq : ∀ u : ℕ,
      (centreFlags n C d).getD (shiftW n p u) false =
      (centreFlags n (rdelC n p w C) d').getD u false := by
    intro u
    unfold centreFlags
    rw [hFinit']
    change (C.gates.foldl stepC Finit).getD (shiftW n p u) false =
      ((rdelC n p w C).gates.foldl stepC' Finit).getD u false
    conv_lhs => rw [hsplit, List.foldl_append, hF0eq, List.foldl_cons]
    have hp_step : stepC F0 C.gates[p] = F0 ++ [false] := by
      dsimp only [stepC]
      have hsub : F0.length - n = p := by omega
      rw [hsub, hrp]; simp
    rw [hp_step]
    change ((C.gates.drop (p + 1)).foldl stepC (F0 ++ [false])).getD (shiftW n p u) false =
      (((C.gates.take p ++ (C.gates.drop (p + 1)).map (delGate n p w)).foldl stepC' Finit)).getD u false
    rw [List.foldl_append]
    apply centreFlags_step_suffix n p w d d' (C.gates.drop (p + 1)) (F0 ++ [false]) F0
    · simp
    · omega
    · intro k hk
      have hk_dr : k < C.gates.length - (p + 1) := by simpa [List.length_drop] using hk
      have hk' : p + k < (rdelC n p w C).gates.length := by
        change p + k < (rdelGates n p w C.gates).length; omega
      have ha1 : (F0 ++ [false]).length - n + k = p + k + 1 := by simp [hF0len]; omega
      have ha2 : F0.length - n + k = p + k := by omega
      rw [ha1, ha2]
      have hsh : shiftIdx p (p + k) = p + k + 1 := by unfold shiftIdx; split_ifs <;> omega
      refine ⟨?_, ?_⟩
      · rw [← hsh]; exact hrole (p + k) hk'
      · intro hz
        have hno := hnoz (p + k) hk' hz
        rw [hsh] at hno
        have hge : (C.gates.drop (p + 1))[k]'hk = gateAt C (p + k + 1) := by
          rw [List.getElem_drop, gateAt_eq_getElem (by omega)]
          congr 1; omega
        rw [hge]; exact hno
    · intro v
      unfold shiftW
      split_ifs with hv
      · rw [List.getD_append _ _ _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by simp [hF0len]; omega),
          List.getD_eq_default _ _ (by omega)]
  intro u
  simp only [IsCentred, hflag_eq u]

private theorem isOrTree_shiftW {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb : ReadsBack n C)
    (G' : Finset ℕ) (hG' : ∀ j' ∈ G', j' < (rdelC n p w C).gates.length)
    (hno : ∀ j' ∈ G', n + p ∉ (gateAt C (shiftIdx p j')).inputs)
    (L' : Finset ℕ) (ρ' : ℕ) :
    IsOrTree n C (G'.image (shiftIdx p)) (L'.image (shiftW n p)) (shiftW n p ρ') ↔
    IsOrTree n (rdelC n p w C) G' L' ρ' := by
  have hG_inputs : ∀ j' ∈ G',
      (gateAt C (shiftIdx p j')).inputs = (gateAt (rdelC n p w C) j').inputs.map (shiftW n p) ∧
      (gateAt C (shiftIdx p j')).op = (gateAt (rdelC n p w C) j').op := by
    intro j' hj'
    have hga := gateAt_rdelC_of_rb hp hrb (hG' j' hj')
    rw [hga]
    refine ⟨?_, rfl⟩
    simp only [delGate, List.map_map]
    symm
    apply list_map_id_mem
    intro i hi
    exact shiftW_rd n p w i (fun e => hno j' hj' (e ▸ hi))
  have hreads : ∀ u : ℕ,
      readsIn C (G'.image (shiftIdx p)) (shiftW n p u) = readsIn (rdelC n p w C) G' u := by
    intro u
    unfold readsIn
    rw [Finset.sum_image (fun a _ b _ h => shiftIdx_inj p h)]
    apply Finset.sum_congr rfl
    intro j' hj'
    rw [(hG_inputs j' hj').1, List.count_map_of_injective _ _ (shiftW_inj n p)]
  have hmem_G : ∀ u : ℕ, (n ≤ shiftW n p u ∧ shiftW n p u - n ∈ G'.image (shiftIdx p)) ↔
      (n ≤ u ∧ u - n ∈ G') := by
    intro u
    constructor
    · rintro ⟨hge, hmem⟩
      obtain ⟨j', hj', hjeq⟩ := Finset.mem_image.1 hmem
      have heq : shiftW n p u = shiftW n p (n + j') := by
        rw [shiftW_add, hjeq, Nat.add_sub_cancel' hge]
      have hu : u = n + j' := shiftW_inj n p heq
      rw [hu]
      exact ⟨by omega, by simpa using hj'⟩
    · rintro ⟨hge, hmem⟩
      have hu : u = n + (u - n) := (Nat.add_sub_cancel' hge).symm
      rw [hu, shiftW_add]
      exact ⟨by omega, by simpa using Finset.mem_image_of_mem (shiftIdx p) hmem⟩
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j' hj'
      have hj := h1 (shiftIdx p j') (Finset.mem_image_of_mem _ hj')
      obtain ⟨hins, hop⟩ := hG_inputs j' hj'
      refine ⟨hop ▸ hj.1, by have := hj.2.1; rw [hins, List.length_map] at this; exact this, ?_⟩
      intro i' hi'
      have hi : shiftW n p i' ∈ (gateAt C (shiftIdx p j')).inputs := by
        rw [hins]; exact List.mem_map_of_mem hi'
      rcases hj.2.2 _ hi with hL | hGm
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.1 hL
        rw [← shiftW_inj n p heq]; exact Or.inl hu
      · exact Or.inr ((hmem_G i').1 hGm)
    · intro u' hu'
      have h2u := h2 (shiftW n p u') (Finset.mem_image_of_mem _ hu')
      refine ⟨fun h => h2u.1 ((hmem_G u').2 h), ?_⟩
      rw [← hreads u', h2u.2]
      by_cases he : u' = ρ'
      · simp [he]
      · simp [he, show shiftW n p u' ≠ shiftW n p ρ' from fun e => he (shiftW_inj n p e)]
    · intro j' hj'
      have h3j := h3 (shiftIdx p j') (Finset.mem_image_of_mem _ hj')
      rw [← shiftW_add, hreads] at h3j
      rw [h3j]
      by_cases he : n + j' = ρ'
      · simp [he]
      · simp [he, show shiftW n p (n + j') ≠ shiftW n p ρ' from fun e => he (shiftW_inj n p e)]
    · by_cases hGe : G' = ∅
      · subst hGe
        simp only [Finset.image_empty, ↓reduceIte] at h4 ⊢
        ext u'
        constructor
        · intro hu'
          have : shiftW n p u' ∈ L'.image (shiftW n p) := Finset.mem_image_of_mem _ hu'
          rw [h4, Finset.mem_singleton] at this
          exact Finset.mem_singleton.2 (shiftW_inj n p this)
        · intro hu'
          rw [Finset.mem_singleton] at hu'
          rw [hu']
          have : shiftW n p ρ' ∈ L'.image (shiftW n p) := by rw [h4]; exact Finset.mem_singleton_self _
          obtain ⟨v, hv, heq⟩ := Finset.mem_image.1 this
          rwa [← shiftW_inj n p heq]
      · have hGne : G'.image (shiftIdx p) ≠ ∅ := by
          intro h; exact hGe (Finset.image_eq_empty.1 h)
        simp only [hGne, hGe, ↓reduceIte] at h4 ⊢
        obtain ⟨j, hj, hρ⟩ := h4
        obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
        rw [← shiftW_add] at hρ
        exact ⟨j', hj', shiftW_inj n p hρ⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
      have hj'1 := h1 j' hj'
      obtain ⟨hins, hop⟩ := hG_inputs j' hj'
      refine ⟨hop.trans hj'1.1, by rw [hins, List.length_map]; exact hj'1.2.1, ?_⟩
      intro i hi
      rw [hins] at hi
      obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hi
      rcases hj'1.2.2 i' hi' with hL | hGm
      · exact Or.inl (Finset.mem_image_of_mem _ hL)
      · exact Or.inr ((hmem_G i').2 hGm)
    · intro u hu
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
      have h2u := h2 u' hu'
      refine ⟨fun h => h2u.1 ((hmem_G u').1 h), ?_⟩
      rw [hreads u', h2u.2]
      by_cases he : u' = ρ'
      · simp [he]
      · simp [he, show shiftW n p u' ≠ shiftW n p ρ' from fun e => he (shiftW_inj n p e)]
    · intro j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
      rw [← shiftW_add, hreads, h3 j' hj']
      by_cases he : n + j' = ρ'
      · simp [he]
      · simp [he, show shiftW n p (n + j') ≠ shiftW n p ρ' from fun e => he (shiftW_inj n p e)]
    · by_cases hGe : G' = ∅
      · subst hGe
        simp only [Finset.image_empty, ↓reduceIte] at h4 ⊢
        rw [h4, Finset.image_singleton]
      · have hGne : G'.image (shiftIdx p) ≠ ∅ := by
          intro h; exact hGe (Finset.image_eq_empty.1 h)
        simp only [hGne, hGe, ↓reduceIte] at h4 ⊢
        obtain ⟨j', hj', hρ⟩ := h4
        refine ⟨shiftIdx p j', Finset.mem_image_of_mem _ hj', ?_⟩
        rw [hρ, shiftW_add]

private theorem readsIn_rdel_eq_w {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hw : w < n + p) (hrb : ReadsBack n C)
    (G' : Finset ℕ) (hG' : ∀ j' ∈ G', j' < (rdelC n p w C).gates.length) :
    readsIn (rdelC n p w C) G' w =
      readsIn C (G'.image (shiftIdx p)) w + readsIn C (G'.image (shiftIdx p)) (n + p) := by
  unfold readsIn
  rw [Finset.sum_image (fun a _ b _ h => shiftIdx_inj p h),
    Finset.sum_image (fun a _ b _ h => shiftIdx_inj p h), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j' hj'
  rw [gateAt_rdelC_of_rb hp hrb (hG' j' hj')]
  exact count_map_rd_eq_w hw _

private theorem readsIn_rdel_ne_w {n p w u' : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb : ReadsBack n C) (hu : u' ≠ w)
    (G' : Finset ℕ) (hG' : ∀ j' ∈ G', j' < (rdelC n p w C).gates.length) :
    readsIn (rdelC n p w C) G' u' = readsIn C (G'.image (shiftIdx p)) (shiftW n p u') := by
  unfold readsIn
  rw [Finset.sum_image (fun a _ b _ h => shiftIdx_inj p h)]
  apply Finset.sum_congr rfl
  intro j' hj'
  rw [gateAt_rdelC_of_rb hp hrb (hG' j' hj')]
  exact count_map_rd_ne_w hu _

private theorem isOrTree_top_delete {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb : ReadsBack n C) {a : Fin n}
    {G L : Finset ℕ} {ρ : ℕ}
    (hG : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ)
    (haL : a.val ∈ L) (haρ : a.val ≠ ρ) (hpG : p ∈ G)
    (hp_in : (gateAt C p).inputs = [a.val, w] ∨ (gateAt C p).inputs = [w, a.val])
    (hwa : w ≠ a.val) (hw : w < n + p)
    (ha_only : ∀ j ∈ G, j ≠ p → a.val ∉ (gateAt C j).inputs) :
    IsOrTree n (rdelC n p w C)
      ((G.erase p).image (unshiftIdx p))
      ((L.erase a.val).image (rd n p w))
      (rd n p w ρ) := by
  let G' := (G.erase p).image (unshiftIdx p)
  let L' := (L.erase a.val).image (rd n p w)
  have hG'_lt : ∀ j' ∈ G', j' < (rdelC n p w C).gates.length := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    obtain ⟨hjp, hjG⟩ := Finset.mem_erase.1 hj
    exact unshiftIdx_lt_rdel hp (hG j hjG) hjp
  have hG_img : G'.image (shiftIdx p) = G.erase p := by
    ext j
    simp only [G', Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨j', ⟨k, ⟨hkp, hkG⟩, rfl⟩, rfl⟩
      rw [shiftIdx_unshiftIdx p k hkp]; exact ⟨hkp, hkG⟩
    · rintro ⟨hjp, hjG⟩
      exact ⟨unshiftIdx p j, ⟨j, ⟨hjp, hjG⟩, rfl⟩, shiftIdx_unshiftIdx p j hjp⟩
  have hG_eq : G = insert p (G'.image (shiftIdx p)) := by
    rw [hG_img, Finset.insert_erase hpG]
  have hp_not_img : p ∉ G'.image (shiftIdx p) := by
    rw [hG_img]; exact Finset.notMem_erase p G
  have hL_ne_mid : ∀ u ∈ L.erase a.val, u ≠ n + p := by
    intro u hu heq
    have huL := (Finset.mem_erase.1 hu).2
    exact (htree.2.1 u huL).1 ⟨by omega, by simpa [heq] using hpG⟩
  have hL_img : L'.image (shiftW n p) = L.erase a.val := by
    ext u
    simp only [L', Finset.mem_image]
    constructor
    · rintro ⟨u', ⟨v, hv, rfl⟩, rfl⟩
      rwa [shiftW_rd n p w v (hL_ne_mid v hv)]
    · intro hu
      exact ⟨rd n p w u, ⟨u, hu, rfl⟩, shiftW_rd n p w u (hL_ne_mid u hu)⟩
  have hw_lt_ρ : w < ρ := by
    have h1 := orTree_le_root hrb hG htree (n + p) (Or.inr ⟨by omega, by simpa using hpG⟩)
    omega
  have hw_ne_ρ : w ≠ ρ := by omega
  have hw_mem_G_or_L : w ∈ L ∨ (n ≤ w ∧ w - n ∈ G) := by
    have hmem : w ∈ (gateAt C p).inputs := by rcases hp_in with h | h <;> simp [h]
    exact (htree.1 p hpG).2.2 w hmem
  have hreads_C_w : readsIn C G w = 1 := by
    rcases hw_mem_G_or_L with hwL | ⟨hnw, hwG⟩
    · rw [(htree.2.1 w hwL).2, if_neg hw_ne_ρ]
    · have h := htree.2.2.1 (w - n) hwG
      rw [Nat.add_sub_cancel' hnw] at h
      rw [h, if_neg hw_ne_ρ]
  have hcnt_p_w : (gateAt C p).inputs.count w = 1 := by
    rcases hp_in with h | h <;> simp [h, hwa, hwa.symm]
  have hcnt_p_mid : (gateAt C p).inputs.count (n + p) = 0 := by
    have h1 : a.val ≠ n + p := by have := a.isLt; omega
    have h2 : w ≠ n + p := by omega
    rcases hp_in with h | h <;> simp [h, h1, h2]
  have hreads_rdel_w : readsIn (rdelC n p w C) G' w = if w = rd n p w ρ then 0 else 1 := by
    rw [readsIn_rdel_eq_w hp hw hrb G' hG'_lt]
    have hw_er : readsIn C (G'.image (shiftIdx p)) w = 0 := by
      have hsum : readsIn C G w = (gateAt C p).inputs.count w + readsIn C (G'.image (shiftIdx p)) w := by
        conv_lhs => rw [hG_eq]
        unfold readsIn; rw [Finset.sum_insert hp_not_img]
      omega
    have hmid_er : readsIn C (G'.image (shiftIdx p)) (n + p) = readsIn C G (n + p) := by
      conv_rhs => rw [hG_eq]
      unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt_p_mid, zero_add]
    rw [hw_er, zero_add, hmid_er, htree.2.2.1 p hpG]
    by_cases hρp : n + p = ρ
    · have h1 : rd n p w ρ = w := by rw [← hρp]; unfold rd; simp
      simp [hρp, h1]
    · have h1 : rd n p w ρ ≠ w := by unfold rd; split_ifs <;> omega
      simp [hρp, Ne.symm h1]
  have hreads_rdel_ne : ∀ u', u' ≠ w → u' ≠ a.val →
      readsIn (rdelC n p w C) G' u' = readsIn C G (shiftW n p u') := by
    intro u' huw hua
    rw [readsIn_rdel_ne_w hp hrb huw G' hG'_lt]
    have hcnt : (gateAt C p).inputs.count (shiftW n p u') = 0 := by
      have h1 : a.val ≠ shiftW n p u' := by
        intro e
        have h1' : rd n p w a.val = u' := by rw [e, rd_shiftW]
        have h2' : rd n p w a.val = a.val := by
          unfold rd; simp [show a.val < n + p by have := a.isLt; omega]
        omega
      have h2 : w ≠ shiftW n p u' := by
        intro e
        have h1' : rd n p w w = u' := by rw [e, rd_shiftW]
        have h2' : rd n p w w = w := by unfold rd; simp [hw]
        omega
      rcases hp_in with h | h <;> simp [h, h1, h2]
    conv_rhs => rw [hG_eq]
    unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt, zero_add]
  have hmem_G'_iff : ∀ u', (n ≤ u' ∧ u' - n ∈ G') ↔
      (n ≤ shiftW n p u' ∧ shiftW n p u' - n ∈ G.erase p) := by
    intro u'
    rw [← hG_img]
    constructor
    · rintro ⟨hnu', hu'⟩
      have heq : u' = n + (u' - n) := (Nat.add_sub_cancel' hnu').symm
      rw [heq, shiftW_add]
      exact ⟨by omega, by simpa using Finset.mem_image_of_mem (shiftIdx p) hu'⟩
    · rintro ⟨hnu, hu⟩
      obtain ⟨j', hj', hjeq⟩ := Finset.mem_image.1 hu
      have heq : shiftW n p u' = shiftW n p (n + j') := by
        rw [shiftW_add, hjeq, Nat.add_sub_cancel' hnu]
      have hu' : u' = n + j' := shiftW_inj n p heq
      rw [hu']
      exact ⟨by omega, by simpa using hj'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j' hj'
    have hj_mem : shiftIdx p j' ∈ G.erase p := by
      rw [← hG_img]; exact Finset.mem_image_of_mem _ hj'
    obtain ⟨hjp, hjG⟩ := Finset.mem_erase.1 hj_mem
    have hga := gateAt_rdelC_of_rb hp hrb (hG'_lt j' hj')
    have hj1 := htree.1 (shiftIdx p j') hjG
    refine ⟨by rw [hga]; exact hj1.1, by rw [hga]; simp [delGate, hj1.2.1], ?_⟩
    intro i' hi'
    rw [hga] at hi'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
    by_cases himid : i = n + p
    · rw [himid]
      have hrd : rd n p w (n + p) = w := by unfold rd; simp
      rw [hrd]
      rcases hw_mem_G_or_L with hwL | ⟨hnw, hwG⟩
      · left
        have hw_er : w ∈ L.erase a.val := Finset.mem_erase.2 ⟨hwa, hwL⟩
        have h1 : rd n p w w = w := by unfold rd; simp [hw]
        exact Finset.mem_image.2 ⟨w, hw_er, h1⟩
      · right
        have hwp : w - n ≠ p := by omega
        exact ⟨hnw, Finset.mem_image.2 ⟨w - n, Finset.mem_erase.2 ⟨hwp, hwG⟩, by
          unfold unshiftIdx; split_ifs <;> omega⟩⟩
    · rcases hj1.2.2 i hi with hiL | ⟨hni, hiG⟩
      · left
        have hia : i ≠ a.val := fun e => ha_only (shiftIdx p j') hjG hjp (e ▸ hi)
        exact Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hia, hiL⟩)
      · right
        have hip : i - n ≠ p := fun e => himid (by omega)
        have hsh : shiftW n p (rd n p w i) = i := shiftW_rd n p w i himid
        exact (hmem_G'_iff (rd n p w i)).2 ⟨by omega, by rw [hsh]; exact Finset.mem_erase.2 ⟨hip, hiG⟩⟩
  · intro u' hu'
    have hu_er : shiftW n p u' ∈ L.erase a.val := by
      rw [← hL_img]; exact Finset.mem_image_of_mem _ hu'
    obtain ⟨hua, huL⟩ := Finset.mem_erase.1 hu_er
    have hua' : u' ≠ a.val := by
      intro e; apply hua; rw [e]; unfold shiftW; simp [show a.val < n + p by have := a.isLt; omega]
    refine ⟨fun h => (htree.2.1 _ huL).1 (by
      obtain ⟨h1, h2⟩ := (hmem_G'_iff u').1 h
      exact ⟨h1, (Finset.mem_erase.1 h2).2⟩), ?_⟩
    by_cases huw : u' = w
    · rw [huw]; exact hreads_rdel_w
    · rw [hreads_rdel_ne u' huw hua', (htree.2.1 _ huL).2]
      by_cases hρp : ρ = n + p
      · have h1 : shiftW n p u' ≠ ρ := by rw [hρp]; exact shiftW_ne_mid n p u'
        have h2 : u' ≠ rd n p w ρ := by rw [hρp]; unfold rd; simp [huw]
        simp [h1, h2]
      · have hiff : shiftW n p u' = ρ ↔ u' = rd n p w ρ := by
          constructor
          · intro h; rw [← h, rd_shiftW]
          · intro h; rw [h, shiftW_rd n p w ρ hρp]
        by_cases h : u' = rd n p w ρ
        · rw [if_pos (hiff.2 h), if_pos h]
        · rw [if_neg (fun e => h (hiff.1 e)), if_neg h]
  · intro j' hj'
    have hj_mem : shiftIdx p j' ∈ G.erase p := by
      rw [← hG_img]; exact Finset.mem_image_of_mem _ hj'
    obtain ⟨hjp, hjG⟩ := Finset.mem_erase.1 hj_mem
    have hna : n + j' ≠ a.val := by have := a.isLt; omega
    by_cases huw : n + j' = w
    · rw [huw]; exact hreads_rdel_w
    · rw [hreads_rdel_ne (n + j') huw hna, shiftW_add, htree.2.2.1 (shiftIdx p j') hjG]
      by_cases hρp : ρ = n + p
      · have h1 : n + shiftIdx p j' ≠ ρ := by rw [hρp]; intro h; exact shiftIdx_ne p j' (by omega)
        have h2 : n + j' ≠ rd n p w ρ := by rw [hρp]; unfold rd; simp [huw]
        simp [h1, h2]
      · have hiff : n + shiftIdx p j' = ρ ↔ n + j' = rd n p w ρ := by
          rw [← shiftW_add]
          constructor
          · intro h; rw [← h, rd_shiftW]
          · intro h; rw [h, shiftW_rd n p w ρ hρp]
        by_cases h : n + j' = rd n p w ρ
        · rw [if_pos (hiff.2 h), if_pos h]
        · rw [if_neg (fun e => h (hiff.1 e)), if_neg h]
  · change if G' = ∅ then L' = {rd n p w ρ} else ∃ j' ∈ G', rd n p w ρ = n + j'
    by_cases hG'e : G' = ∅
    · simp only [hG'e, ↓reduceIte]
      have hG1 : G = {p} := by rw [hG_eq, hG'e]; simp
      have hρp : ρ = n + p := by
        have h4 := htree.2.2.2
        have hGne : G ≠ ∅ := by rw [hG1]; simp
        simp only [hGne, ↓reduceIte] at h4
        obtain ⟨j, hj, hρj⟩ := h4
        rw [hG1, Finset.mem_singleton] at hj; rw [hj] at hρj; exact hρj
      have hrdρ : rd n p w ρ = w := by rw [hρp]; unfold rd; simp
      rw [hrdρ]
      ext u'
      constructor
      · intro hu'
        have hu_er : shiftW n p u' ∈ L.erase a.val := by
          rw [← hL_img]; exact Finset.mem_image_of_mem _ hu'
        obtain ⟨hua, huL⟩ := Finset.mem_erase.1 hu_er
        have hneρ : shiftW n p u' ≠ ρ := by rw [hρp]; exact shiftW_ne_mid n p u'
        have hr1 : readsIn C G (shiftW n p u') = 1 := by
          rw [(htree.2.1 _ huL).2, if_neg hneρ]
        rw [hG1] at hr1
        have hcnt : (gateAt C p).inputs.count (shiftW n p u') = 1 := by
          simpa [readsIn] using hr1
        have hmem : shiftW n p u' ∈ (gateAt C p).inputs := List.count_pos_iff.1 (by omega)
        rcases hp_in with h | h <;> rw [h] at hmem <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        · rcases hmem with h1 | h2
          · exact (hua h1).elim
          · have : u' = w := by
              have := congrArg (rd n p w) h2
              rw [rd_shiftW] at this
              simpa [rd, hw] using this
            exact Finset.mem_singleton.2 this
        · rcases hmem with h2 | h1
          · have : u' = w := by
              have := congrArg (rd n p w) h2
              rw [rd_shiftW] at this
              simpa [rd, hw] using this
            exact Finset.mem_singleton.2 this
          · exact (hua h1).elim
      · intro hu'
        rw [Finset.mem_singleton] at hu'
        rw [hu']
        rcases hw_mem_G_or_L with hwL | ⟨hnw, hwG⟩
        · have h1 : rd n p w w = w := by unfold rd; simp [hw]
          exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwa, hwL⟩, h1⟩
        · rw [hG1, Finset.mem_singleton] at hwG; omega
    · simp only [hG'e, ↓reduceIte]
      by_cases hρp : ρ = n + p
      · have hne_er : (G.erase p).Nonempty := by
          rw [← hG_img]; exact (Finset.nonempty_iff_ne_empty.2 hG'e).image _
        let jmax := (G.erase p).max' hne_er
        have hjmax_er : jmax ∈ G.erase p := Finset.max'_mem _ hne_er
        obtain ⟨hjmax_p, hjmax_G⟩ := Finset.mem_erase.1 hjmax_er
        have hneρ : n + jmax ≠ ρ := by rw [hρp]; omega
        have hr1 : readsIn C G (n + jmax) = 1 := by
          rw [htree.2.2.1 jmax hjmax_G, if_neg hneρ]
        have h0_er : readsIn C (G.erase p) (n + jmax) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hle : j ≤ jmax := Finset.le_max' (G.erase p) j hj
          apply List.count_eq_zero.2
          intro hmem
          have hlt := hrb j (hG j (Finset.mem_erase.1 hj).2) (n + jmax) hmem
          omega
        have hp_cnt : (gateAt C p).inputs.count (n + jmax) = 1 := by
          have hsum : readsIn C G (n + jmax) =
              (gateAt C p).inputs.count (n + jmax) + readsIn C (G.erase p) (n + jmax) := by
            conv_lhs => rw [← Finset.insert_erase hpG]
            unfold readsIn; rw [Finset.sum_insert (Finset.notMem_erase p G)]
          omega
        have hmem : n + jmax ∈ (gateAt C p).inputs := List.count_pos_iff.1 (by omega)
        have hw_eq : w = n + jmax := by
          have ha_lt : a.val < n := a.isLt
          rcases hp_in with h | h <;> rw [h] at hmem <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          · rcases hmem with h1 | h2
            · omega
            · exact h2.symm
          · rcases hmem with h2 | h1
            · exact h2.symm
            · omega
        have hjmax_lt : jmax < p := by omega
        refine ⟨unshiftIdx p jmax, Finset.mem_image_of_mem _ hjmax_er, ?_⟩
        rw [hρp, show rd n p w (n + p) = w by unfold rd; simp, hw_eq]
        simp [unshiftIdx, hjmax_lt]
      · have hGne : G ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨p, hpG⟩
        have h4 := htree.2.2.2
        simp only [hGne, ↓reduceIte] at h4
        obtain ⟨jout, hjoutG, hρeq⟩ := h4
        have hjout_p : jout ≠ p := fun e => hρp (hρeq.trans (by omega))
        refine ⟨unshiftIdx p jout, Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hjout_p, hjoutG⟩), ?_⟩
        rw [hρeq, rd_add_of_ne n p w jout hjout_p]

private theorem isOrTree_top_insert {n p w : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hrb : ReadsBack n C) {a : Fin n}
    {G' L' : Finset ℕ} {ρ' : ℕ}
    (hG' : ∀ j' ∈ G', j' < (rdelC n p w C).gates.length)
    (htree' : IsOrTree n (rdelC n p w C) G' L' ρ')
    (haL' : a.val ∉ L') (hwa : w ≠ a.val) (hw : w < n + p)
    (hw_top : w ∈ L' ∨ (n ≤ w ∧ w - n ∈ G'))
    (hp_op : (gateAt C p).op = GateOp.or)
    (hp_in : (gateAt C p).inputs = [a.val, w] ∨ (gateAt C p).inputs = [w, a.val])
    (hcase : (w = ρ' ∧ C.output = n + p ∧ readsIn C (G'.image (shiftIdx p)) (n + p) = 0) ∨
      (w ≠ ρ' ∧ C.output = shiftW n p ρ' ∧ readsIn C (G'.image (shiftIdx p)) (n + p) = 1)) :
    IsOrTree n C (insert p (G'.image (shiftIdx p))) (insert a.val (L'.image (shiftW n p))) C.output := by
  let G := insert p (G'.image (shiftIdx p))
  let L := insert a.val (L'.image (shiftW n p))
  have hp_not_img : p ∉ G'.image (shiftIdx p) := by
    intro h; obtain ⟨j', _, hjeq⟩ := Finset.mem_image.1 h; exact shiftIdx_ne p j' hjeq
  have ha_lt_mid : a.val < n + p := by have := a.isLt; omega
  have hsh_a : shiftW n p a.val = a.val := shiftW_lt n p a.val ha_lt_mid
  have hsh_w : shiftW n p w = w := shiftW_lt n p w hw
  have hcnt_p_a : (gateAt C p).inputs.count a.val = 1 := by
    rcases hp_in with h | h <;> simp [h, hwa, hwa.symm]
  have hcnt_p_w : (gateAt C p).inputs.count w = 1 := by
    rcases hp_in with h | h <;> simp [h, hwa, hwa.symm]
  have hcnt_p_mid : (gateAt C p).inputs.count (n + p) = 0 := by
    have h1 : a.val ≠ n + p := by omega
    have h2 : w ≠ n + p := by omega
    rcases hp_in with h | h <;> simp [h, h1, h2]
  have hcnt_p_other : ∀ u, u ≠ a.val → u ≠ w → (gateAt C p).inputs.count u = 0 := by
    intro u h1 h2; rcases hp_in with h | h <;> simp [h, h1.symm, h2.symm]
  have ha_no_img : readsIn C (G'.image (shiftIdx p)) a.val = 0 := by
    have h1 := readsIn_rdel_ne_w (u' := a.val) hp hrb hwa.symm G' hG'
    rw [hsh_a] at h1
    rw [← h1]
    apply Finset.sum_eq_zero
    intro j' hj'
    apply List.count_eq_zero.2
    intro hmem
    rcases (htree'.1 j' hj').2.2 a.val hmem with hL | ⟨hge, _⟩
    · exact haL' hL
    · have := a.isLt; omega
  have hreads_rdel_w_eq : readsIn (rdelC n p w C) G' w = if w = ρ' then 0 else 1 := by
    rcases hw_top with hwL' | ⟨hnw, hwG'⟩
    · exact (htree'.2.1 w hwL').2
    · have h := htree'.2.2.1 (w - n) hwG'
      rwa [Nat.add_sub_cancel' hnw] at h
  have hreads_img_w : readsIn C (G'.image (shiftIdx p)) w = 0 := by
    have h1 := readsIn_rdel_eq_w hp hw hrb G' hG'
    rw [hreads_rdel_w_eq] at h1
    rcases hcase with ⟨hwρ, _, hmid0⟩ | ⟨hwρ, _, hmid1⟩
    · rw [if_pos hwρ] at h1; omega
    · rw [if_neg hwρ] at h1; omega
  have hreads_G_w : readsIn C G w = 1 := by
    change readsIn C (insert p (G'.image (shiftIdx p))) w = 1
    unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt_p_w]
    change 1 + readsIn C (G'.image (shiftIdx p)) w = 1; omega
  have hreads_G_a : readsIn C G a.val = 1 := by
    change readsIn C (insert p (G'.image (shiftIdx p))) a.val = 1
    unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt_p_a]
    change 1 + readsIn C (G'.image (shiftIdx p)) a.val = 1; omega
  have hreads_G_mid : readsIn C G (n + p) = if n + p = C.output then 0 else 1 := by
    change readsIn C (insert p (G'.image (shiftIdx p))) (n + p) = _
    unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt_p_mid, zero_add]
    change readsIn C (G'.image (shiftIdx p)) (n + p) = _
    rcases hcase with ⟨_, hout, hmid0⟩ | ⟨_, hout, hmid1⟩
    · simp [hout, hmid0]
    · have hne : n + p ≠ C.output := by rw [hout]; exact (shiftW_ne_mid n p ρ').symm
      simp [hne, hmid1]
  have hreads_G_shift : ∀ u', u' ≠ a.val →
      readsIn (rdelC n p w C) G' u' = (if u' = ρ' then 0 else 1) →
      readsIn C G (shiftW n p u') = if shiftW n p u' = C.output then 0 else 1 := by
    intro u' hua hr'
    by_cases huw : u' = w
    · rw [huw, hsh_w, hreads_G_w]
      have hne : w ≠ C.output := by
        rcases hcase with ⟨_, hout, _⟩ | ⟨hwρ, hout, _⟩
        · rw [hout]; omega
        · rw [hout, ← hsh_w]; exact fun e => hwρ (shiftW_inj n p e)
      simp [hne]
    · have hne_w : shiftW n p u' ≠ w := fun e => huw (shiftW_inj n p (e.trans hsh_w.symm))
      have hne_a : shiftW n p u' ≠ a.val := fun e => hua (shiftW_inj n p (e.trans hsh_a.symm))
      have h1 := readsIn_rdel_ne_w (u' := u') hp hrb huw G' hG'
      have hsum : readsIn C G (shiftW n p u') = readsIn (rdelC n p w C) G' u' := by
        change readsIn C (insert p (G'.image (shiftIdx p))) (shiftW n p u') = _
        unfold readsIn; rw [Finset.sum_insert hp_not_img, hcnt_p_other _ hne_a hne_w, zero_add]
        exact h1.symm
      rw [hsum, hr']
      have hiff : (shiftW n p u' = C.output) ↔ (u' = ρ') := by
        rcases hcase with ⟨hwρ, hout, _⟩ | ⟨_, hout, _⟩
        · constructor
          · intro h; rw [hout] at h; exact (shiftW_ne_mid n p u' h).elim
          · intro h; exact (huw (h.trans hwρ.symm)).elim
        · rw [hout]
          exact ⟨fun h => shiftW_inj n p h, fun h => congrArg (shiftW n p) h⟩
      by_cases h : u' = ρ'
      · rw [if_pos h, if_pos (hiff.2 h)]
      · rw [if_neg h, if_neg (fun e => h (hiff.1 e))]
  have hmem_G_iff : ∀ u', (n ≤ shiftW n p u' ∧ shiftW n p u' - n ∈ G) ↔ (n ≤ u' ∧ u' - n ∈ G') := by
    intro u'
    constructor
    · rintro ⟨hge, hmem⟩
      rw [Finset.mem_insert] at hmem
      rcases hmem with hpeq | himg
      · exfalso; apply shiftW_ne_mid n p u'; omega
      · obtain ⟨j', hj', hjeq⟩ := Finset.mem_image.1 himg
        have heq : shiftW n p u' = shiftW n p (n + j') := by
          rw [shiftW_add, hjeq, Nat.add_sub_cancel' hge]
        have hu : u' = n + j' := shiftW_inj n p heq
        rw [hu]; exact ⟨by omega, by simpa using hj'⟩
    · rintro ⟨hge, hmem⟩
      have hu : u' = n + (u' - n) := (Nat.add_sub_cancel' hge).symm
      rw [hu, shiftW_add]
      refine ⟨by omega, ?_⟩
      have hsub : n + shiftIdx p (u' - n) - n = shiftIdx p (u' - n) := by omega
      rw [hsub]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem (shiftIdx p) hmem)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj_img
    · refine ⟨hp_op, by rcases hp_in with h | h <;> simp [h], ?_⟩
      intro i hi
      rcases hp_in with h | h <;> rw [h] at hi <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      · rcases hi with rfl | hiw
        · exact Or.inl (Finset.mem_insert_self _ _)
        · rw [hiw]
          rcases hw_top with hwL' | ⟨hnw, hwG'⟩
          · exact Or.inl (Finset.mem_insert_of_mem (hsh_w ▸ Finset.mem_image_of_mem _ hwL'))
          · exact Or.inr (hsh_w ▸ (hmem_G_iff w).2 ⟨hnw, hwG'⟩)
      · rcases hi with hiw | rfl
        · rw [hiw]
          rcases hw_top with hwL' | ⟨hnw, hwG'⟩
          · exact Or.inl (Finset.mem_insert_of_mem (hsh_w ▸ Finset.mem_image_of_mem _ hwL'))
          · exact Or.inr (hsh_w ▸ (hmem_G_iff w).2 ⟨hnw, hwG'⟩)
        · exact Or.inl (Finset.mem_insert_self _ _)
    · obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj_img
      have hga := gateAt_rdelC_of_rb hp hrb (hG' j' hj')
      have hj'1 := htree'.1 j' hj'
      refine ⟨by have := hj'1.1; rw [hga] at this; exact this,
        by have := hj'1.2.1; rw [hga] at this; simpa [delGate] using this, ?_⟩
      intro i hi
      by_cases himid : i = n + p
      · rw [himid]; exact Or.inr ⟨by omega, by simpa using Finset.mem_insert_self p _⟩
      · have hi' : rd n p w i ∈ (gateAt (rdelC n p w C) j').inputs := by
          rw [hga]; exact List.mem_map_of_mem hi
        have hsh : shiftW n p (rd n p w i) = i := shiftW_rd n p w i himid
        rcases hj'1.2.2 _ hi' with hL' | hG'm
        · exact Or.inl (Finset.mem_insert_of_mem (hsh ▸ Finset.mem_image_of_mem _ hL'))
        · exact Or.inr (hsh ▸ (hmem_G_iff _).2 hG'm)
  · intro u hu
    rw [Finset.mem_insert] at hu
    rcases hu with rfl | hu_img
    · refine ⟨fun h => by have := a.isLt; omega, ?_⟩
      rw [hreads_G_a]
      have ha_ne_out : a.val ≠ C.output := by
        rcases hcase with ⟨_, hout, _⟩ | ⟨_, hout, _⟩
        · rw [hout]; omega
        · rw [hout, ← hsh_a]
          intro e
          have heq : a.val = ρ' := shiftW_inj n p e
          rcases orTree_rho_mem htree' with hL' | ⟨hge, _⟩
          · exact haL' (heq ▸ hL')
          · have := a.isLt; omega
      simp [ha_ne_out]
    · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu_img
      have hua : u' ≠ a.val := fun e => haL' (e ▸ hu')
      refine ⟨fun h => (htree'.2.1 u' hu').1 ((hmem_G_iff u').1 h), ?_⟩
      exact hreads_G_shift u' hua (htree'.2.1 u' hu').2
  · intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj_img
    · exact hreads_G_mid
    · obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj_img
      rw [← shiftW_add]
      have hna : n + j' ≠ a.val := by have := a.isLt; omega
      exact hreads_G_shift (n + j') hna (htree'.2.2.1 j' hj')
  · change if G = ∅ then L = {C.output} else ∃ j ∈ G, C.output = n + j
    have hGne : G ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨p, Finset.mem_insert_self p _⟩
    simp only [hGne, ↓reduceIte]
    rcases hcase with ⟨_, hout, _⟩ | ⟨hwρ, hout, _⟩
    · exact ⟨p, Finset.mem_insert_self p _, hout⟩
    · have hG'ne : G' ≠ ∅ := by
        intro hG'e
        have h4 := htree'.2.2.2
        simp only [hG'e, ↓reduceIte] at h4
        rcases hw_top with hwL' | ⟨_, hwG'⟩
        · rw [h4, Finset.mem_singleton] at hwL'; exact hwρ hwL'
        · rw [hG'e] at hwG'; exact (Finset.notMem_empty _ hwG').elim
      have h4 := htree'.2.2.2
      simp only [hG'ne, ↓reduceIte] at h4
      obtain ⟨j', hj', hρ'⟩ := h4
      refine ⟨shiftIdx p j', Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj'), ?_⟩
      rw [hout, hρ', shiftW_add]

private theorem valid_fanInTwo {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) : FanInTwo C := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [← gateAt_eq_getElem hj]
  rcases hv.2.2.2.2.1 j hj with htop | ⟨t, ht, hrt, hbt⟩
  · have hjG : j ∈ topGates d C := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, htop⟩
    have h1 := hv.2.2.2.2.2.2.1 j hjG
    exact ⟨by simp [h1.1], by omega⟩
  · cases hkind : (d.role j).1
    · have hjG : j ∈ gatesOf d C Kind.z t.val :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩
      have h1 := (hv.2.2.2.2.2.1 t ht).2.1.1 j hjG
      exact ⟨by simp [h1.1], by omega⟩
    · have hjG : j ∈ gatesOf d C Kind.o t.val :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩
      have h1 := (hv.2.2.2.2.2.1 t ht).2.2.1.1 j hjG
      exact ⟨by simp [h1.1], by omega⟩
    · obtain ⟨j0, _, hbw0, _, hop0, hin0⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hbwj := hbt hkind
      have hjeq : j = j0 := by omega
      subst hjeq
      exact ⟨by simp [hop0], by rcases hin0 with h | h <;> simp [h]⟩
    · have hjG : j ∈ topGates d C := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hkind⟩
      have h1 := hv.2.2.2.2.2.2.1 j hjG
      exact ⟨by simp [h1.1], by omega⟩

private theorem valid_gate_no_not {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op ≠ GateOp.not := by
  rcases hv.2.2.2.2.1 j hj with htop | ⟨t, ht, hrt, hbt⟩
  · have h1 := hv.2.2.2.2.2.2.1 j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, htop⟩)
    rw [h1.1]; intro h; cases h
  · cases hkind : (d.role j).1
    · have h1 := (hv.2.2.2.2.2.1 t ht).2.1.1 j
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩)
      rw [h1.1]; intro h; cases h
    · have h1 := (hv.2.2.2.2.2.1 t ht).2.2.1.1 j
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩)
      rw [h1.1]; intro h; cases h
    · obtain ⟨j0, _, hbw0, _, hop0, _⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hbwj := hbt hkind
      have hjeq : j = j0 := by omega
      subst hjeq; rw [hop0]; intro h; cases h
    · have h1 := hv.2.2.2.2.2.2.1 j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hkind⟩)
      rw [h1.1]; intro h; cases h

private theorem valid_role_ne_top_wires {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) {p : ℕ}
    (hp_top : (d.role p).1 = Kind.top) :
    (∀ t ∈ d.cover, d.bw t ≠ n + p ∧ d.zroot t ≠ n + p ∧ d.oroot t ≠ n + p ∧
      ∀ r, d.owns t r = true → d.lam t r ≠ n + p) ∧
    (∀ j < C.gates.length, (d.role j).1 ≠ Kind.top → n + p ∉ (gateAt C j).inputs) := by
  have hnot_top : ∀ u, (u < n ∨ ∃ j < C.gates.length, u = n + j ∧ (d.role j).1 ≠ Kind.top) →
      u ≠ n + p := by
    rintro u (hlt | ⟨j, _, rfl, hjnt⟩) heq
    · omega
    · have : j = p := by omega
      subst this; exact hjnt hp_top
  have hbw : ∀ t ∈ d.cover, d.bw t ≠ n + p := by
    intro t ht
    obtain ⟨j, hj, hbwj, hrolej, _, _⟩ := (hv.2.2.2.2.2.1 t ht).1
    exact hnot_top _ (Or.inr ⟨j, hj, hbwj, by rw [hrolej]; intro h; cases h⟩)
  have hzmem : ∀ t ∈ d.cover, ∀ u, (u ∈ zLeaves d t ∨ (n ≤ u ∧ u - n ∈ gatesOf d C Kind.z t.val)) →
      u ≠ n + p := by
    intro t ht u hu
    rcases hu with huL | ⟨hge, huG⟩
    · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at huL
      rcases huL with rfl | ⟨s, ⟨hs, _⟩, rfl⟩
      · exact hnot_top _ (Or.inl t.isLt)
      · exact hbw s hs
    · have hfl := (Finset.mem_filter.1 huG).2
      have hlt := Finset.mem_range.1 (Finset.mem_filter.1 huG).1
      exact hnot_top _ (Or.inr ⟨u - n, hlt, (Nat.add_sub_cancel' hge).symm, by rw [hfl]; intro h; cases h⟩)
  have hlam : ∀ t ∈ d.cover, ∀ r, d.owns t r = true → d.lam t r ≠ n + p := by
    intro t ht r hr
    have hL := (hv.2.2.2.2.2.1 t ht).2.2.2 r hr
    unfold LamOK at hL
    split at hL
    · rcases hL.2.1 with heq | ⟨j, hj, heq, hrj⟩
      · exact hnot_top _ (Or.inl (heq ▸ r.isLt))
      · exact hnot_top _ (Or.inr ⟨j, hj, heq, by rw [hrj]; intro h; cases h⟩)
    · exact hnot_top _ (Or.inl (hL ▸ r.isLt))
  have homem : ∀ t ∈ d.cover, ∀ u, (u ∈ oLeaves d t ∨ (n ≤ u ∧ u - n ∈ gatesOf d C Kind.o t.val)) →
      u ≠ n + p := by
    intro t ht u hu
    rcases hu with huL | ⟨hge, huG⟩
    · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at huL
      obtain ⟨r, hr, rfl⟩ := huL
      exact hlam t ht r hr
    · have hfl := (Finset.mem_filter.1 huG).2
      have hlt := Finset.mem_range.1 (Finset.mem_filter.1 huG).1
      exact hnot_top _ (Or.inr ⟨u - n, hlt, (Nat.add_sub_cancel' hge).symm, by rw [hfl]; intro h; cases h⟩)
  have hzroot : ∀ t ∈ d.cover, d.zroot t ≠ n + p := fun t ht =>
    hzmem t ht _ (orTree_rho_mem (hv.2.2.2.2.2.1 t ht).2.1)
  have horoot : ∀ t ∈ d.cover, d.oroot t ≠ n + p := fun t ht =>
    homem t ht _ (orTree_rho_mem (hv.2.2.2.2.2.1 t ht).2.2.1)
  refine ⟨fun t ht => ⟨hbw t ht, hzroot t ht, horoot t ht, hlam t ht⟩, ?_⟩
  intro j hj hjnt hmem
  rcases hv.2.2.2.2.1 j hj with htop | ⟨t, ht, hrt, hbt⟩
  · exact hjnt htop
  · cases hkind : (d.role j).1
    · have hjG : j ∈ gatesOf d C Kind.z t.val :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩
      exact hzmem t ht (n + p) ((hv.2.2.2.2.2.1 t ht).2.1.1 j hjG |>.2.2 _ hmem) rfl
    · have hjG : j ∈ gatesOf d C Kind.o t.val :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, Prod.ext hkind hrt⟩
      exact homem t ht (n + p) ((hv.2.2.2.2.2.1 t ht).2.2.1.1 j hjG |>.2.2 _ hmem) rfl
    · obtain ⟨j0, _, hbw0, _, _, hin0⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hjeq : j = j0 := by have := hbt hkind; omega
      subst hjeq
      rcases hin0 with h | h <;> rw [h] at hmem <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      · rcases hmem with h1 | h2
        · exact hzroot t ht h1.symm
        · exact horoot t ht h2.symm
      · rcases hmem with h1 | h2
        · exact horoot t ht h1.symm
        · exact hzroot t ht h2.symm
    · exact hjnt hkind

private theorem valid_to_min {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (hne : (∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card)
    (hIH : ∀ C : Circuit,
      (IsMinimalCircuit n C ∧ circuitFun n C = graphFun K (A.erase a)) ↔
      IsNestedCoverCircuit n K (A.erase a) C)
    (C : Circuit) (hNCC : IsNestedCoverCircuit n K A C) :
    IsMinimalCircuit n C ∧ circuitFun n C = graphFun K A := by
  obtain ⟨d, hv⟩ := hNCC
  have hrb := hv.1
  have hmincov := hv.2.1
  have hown := hv.2.2.1
  have htie := hv.2.2.2.1
  have hroles := hv.2.2.2.2.1
  have hcov := hv.2.2.2.2.2.1
  have htop := hv.2.2.2.2.2.2
  have ha_not_cov : a ∉ d.cover := not_mem_minCover_of_isolated hmincov a (hAdisj a haA)
  have ha_topL : a.val ∈ topLeaves d A :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem Fin.val haA)
  have hex_other : ∃ u ∈ topLeaves d (A.erase a), u ≠ a.val := by
    rcases hne with ⟨u0, v0, huv0⟩ | hcard
    · have hcov_ne : d.cover.Nonempty := by
        rcases hmincov.1 huv0 with hu | hv0
        · exact ⟨u0, hu⟩
        · exact ⟨v0, hv0⟩
      obtain ⟨tmax, htmax_cov, htmax_ge⟩ := Finset.exists_max_image d.cover d.bw hcov_ne
      have htmax_untied : d.tie tmax = none := by
        cases htie_eq : d.tie tmax with
        | none => rfl
        | some t' =>
          exfalso
          have hown_t' := (htie tmax t' htie_eq).2
          have ht'_cov := (hown.1 t' tmax hown_t').2
          have hbw_mem : d.bw tmax ∈ zLeaves d t' := by
            simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
            exact Or.inr ⟨tmax, ⟨htmax_cov, htie_eq⟩, rfl⟩
          have hle_z : d.bw tmax ≤ d.zroot t' :=
            orTree_le_root hrb (fun j hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
              (hcov t' ht'_cov).2.1 (d.bw tmax) (Or.inl hbw_mem)
          obtain ⟨j', hj', hbw', _, _, hin'⟩ := (hcov t' ht'_cov).1
          have hz_in : d.zroot t' ∈ (gateAt C j').inputs := by
            rcases hin' with h | h <;> simp [h]
          have hlt_b : d.zroot t' < d.bw t' := by
            rw [hbw']; exact hrb j' hj' _ hz_in
          have hge_max := htmax_ge t' ht'_cov
          omega
      obtain ⟨jm, _, hbwm, _, _, _⟩ := (hcov tmax htmax_cov).1
      refine ⟨d.bw tmax, Finset.mem_union_right _ (Finset.mem_image_of_mem d.bw
        (Finset.mem_filter.2 ⟨htmax_cov, htmax_untied⟩)), ?_⟩
      have := a.isLt; omega
    · have hpos : 0 < (A.erase a).card := by rw [Finset.card_erase_of_mem haA]; omega
      obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
      refine ⟨b.val, Finset.mem_union_left _ (Finset.mem_image_of_mem Fin.val hb), ?_⟩
      intro heq
      exact (Finset.mem_erase.1 hb).1 (Fin.ext heq)
  obtain ⟨u0, hu0L, hu0ne⟩ := hex_other
  have hu0_topL : u0 ∈ topLeaves d A := by
    simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hu0L ⊢
    rcases hu0L with ⟨b, hb, rfl⟩ | ⟨t, ht, rfl⟩
    · exact Or.inl ⟨b, (Finset.mem_erase.1 hb).2, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩
  have htop_ne : topGates d C ≠ ∅ := by
    intro hemp
    have h4 := htop.2.2.2
    simp only [hemp, ↓reduceIte] at h4
    have h1 : a.val = C.output := Finset.mem_singleton.1 (h4 ▸ ha_topL)
    have h2 : u0 = C.output := Finset.mem_singleton.1 (h4 ▸ hu0_topL)
    exact hu0ne (h2.trans h1.symm)
  have hCout_ge : n ≤ C.output := by
    have h4 := htop.2.2.2
    simp only [htop_ne, ↓reduceIte] at h4
    obtain ⟨j, _, hj⟩ := h4; omega
  have ha_ne_out : a.val ≠ C.output := by have := a.isLt; omega
  have hreads_a : readsIn C (topGates d C) a.val = 1 := by
    rw [(htop.2.1 a.val ha_topL).2, if_neg ha_ne_out]
  obtain ⟨p, hpG, hcnt_ne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by change readsIn C (topGates d C) a.val ≠ 0; omega)
  have hp_lt : p < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hpG).1
  have hp_top : (d.role p).1 = Kind.top := (Finset.mem_filter.1 hpG).2
  have hcnt_p_a : (gateAt C p).inputs.count a.val = 1 := by
    have hle : (gateAt C p).inputs.count a.val ≤ readsIn C (topGates d C) a.val :=
      Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count a.val) (fun _ _ => Nat.zero_le _) hpG
    omega
  have ha_only : ∀ j ∈ topGates d C, j ≠ p → a.val ∉ (gateAt C j).inputs := by
    intro j hjG hjp hmem
    have hcntj : 1 ≤ (gateAt C j).inputs.count a.val := List.count_pos_iff.2 hmem
    have hsum : (gateAt C p).inputs.count a.val + (gateAt C j).inputs.count a.val ≤
        readsIn C (topGates d C) a.val := by
      have hsub : ({p, j} : Finset ℕ) ⊆ topGates d C := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h1 := Finset.sum_le_sum_of_subset (f := fun k => (gateAt C k).inputs.count a.val) hsub
      rw [Finset.sum_pair (Ne.symm hjp)] at h1
      exact h1
    omega
  have hp_op : (gateAt C p).op = GateOp.or := (htop.1 p hpG).1
  have hp_len : (gateAt C p).inputs.length = 2 := (htop.1 p hpG).2.1
  have hp_w : ∃ w, ((gateAt C p).inputs = [a.val, w] ∨ (gateAt C p).inputs = [w, a.val]) ∧
      w ≠ a.val ∧ w < n + p := by
    rcases hins : (gateAt C p).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · rw [hins] at hp_len; simp at hp_len
    · rw [hins] at hp_len; simp at hp_len
    · rw [hins] at hcnt_p_a
      by_cases hxa : x = a.val
      · subst hxa
        have hya : y ≠ a.val := by intro h; subst h; simp at hcnt_p_a
        exact ⟨y, Or.inl rfl, hya, hrb p hp_lt y (by simp [hins])⟩
      · have hya : y = a.val := by
          by_contra hne'; simp [hxa, hne'] at hcnt_p_a
        subst hya
        exact ⟨x, Or.inr rfl, hxa, hrb p hp_lt x (by simp [hins])⟩
    · rw [hins] at hp_len; simp at hp_len
  obtain ⟨w, hp_in, hwa, hw_lt⟩ := hp_w
  obtain ⟨hnt_wires, hnt_no⟩ := valid_role_ne_top_wires hv hp_top
  let C' := rdelC n p w C
  let d' : NCCData n := {
    cover := d.cover
    owns := d.owns
    tie := d.tie
    role := fun j' => d.role (shiftIdx p j')
    bw := fun t => rd n p w (d.bw t)
    zroot := fun t => rd n p w (d.zroot t)
    oroot := fun t => rd n p w (d.oroot t)
    lam := fun t r => rd n p w (d.lam t r)
  }
  have hlen' : C'.gates.length + 1 = C.gates.length := rdelGates_length n p w C.gates hp_lt
  have hsh_bw : ∀ t ∈ d.cover, shiftW n p (d'.bw t) = d.bw t := fun t ht =>
    shiftW_rd n p w (d.bw t) (hnt_wires t ht).1
  have hsh_zr : ∀ t ∈ d.cover, shiftW n p (d'.zroot t) = d.zroot t := fun t ht =>
    shiftW_rd n p w (d.zroot t) (hnt_wires t ht).2.1
  have hsh_or : ∀ t ∈ d.cover, shiftW n p (d'.oroot t) = d.oroot t := fun t ht =>
    shiftW_rd n p w (d.oroot t) (hnt_wires t ht).2.2.1
  have hsh_lam : ∀ t ∈ d.cover, ∀ r, d.owns t r = true → shiftW n p (d'.lam t r) = d.lam t r :=
    fun t ht r hr => shiftW_rd n p w (d.lam t r) ((hnt_wires t ht).2.2.2 r hr)
  have hgates_eq : ∀ k t, k ≠ Kind.top →
      gatesOf d C k t = (gatesOf d' C' k t).image (shiftIdx p) := by
    intro k t hk
    ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hrj⟩
      have hjp : j ≠ p := by intro e; subst e; rw [hrj] at hp_top; exact hk hp_top
      refine ⟨unshiftIdx p j, ⟨unshiftIdx_lt_rdel hp_lt hj hjp, ?_⟩, shiftIdx_unshiftIdx p j hjp⟩
      dsimp only [d']; rw [shiftIdx_unshiftIdx p j hjp]; exact hrj
    · rintro ⟨j', ⟨hj', hrj'⟩, rfl⟩
      exact ⟨shiftIdx_lt_of_rdel hp_lt hj', hrj'⟩
  have hzL_eq : ∀ t ∈ d.cover, zLeaves d t = (zLeaves d' t).image (shiftW n p) := by
    intro t ht
    ext u
    simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨s, ⟨hs, hts⟩, rfl⟩)
      · exact ⟨t.val, Or.inl rfl, shiftW_lt n p t.val (by have := t.isLt; omega)⟩
      · exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs, hts⟩, rfl⟩, hsh_bw s hs⟩
    · rintro ⟨v, (rfl | ⟨s, ⟨hs, hts⟩, rfl⟩), rfl⟩
      · exact Or.inl (shiftW_lt n p t.val (by have := t.isLt; omega))
      · exact Or.inr ⟨s, ⟨hs, hts⟩, (hsh_bw s hs).symm⟩
  have hoL_eq : ∀ t ∈ d.cover, oLeaves d t = (oLeaves d' t).image (shiftW n p) := by
    intro t ht
    ext u
    simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨d'.lam t r, ⟨r, hr, rfl⟩, hsh_lam t ht r hr⟩
    · rintro ⟨v, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, (hsh_lam t ht r hr).symm⟩
  have hcent := isCentred_shiftW (w := w) (d := d) (d' := d') hp_lt rfl hp_top
    (fun _ _ => rfl) (fun j' hj' hz => hnt_no (shiftIdx p j') (shiftIdx_lt_of_rdel hp_lt hj')
      (by rw [hz]; intro h; cases h))
  have hv' : Valid n K (A.erase a) C' d' := by
    refine ⟨readsBack_rdelC hp_lt hw_lt hrb, hmincov, hown, htie, ?_, ?_, ?_⟩
    · intro j' hj'
      have hj : shiftIdx p j' < C.gates.length := shiftIdx_lt_of_rdel hp_lt hj'
      rcases hroles (shiftIdx p j') hj with htopj | ⟨t, ht, hrt, hbt⟩
      · exact Or.inl htopj
      · right; refine ⟨t, ht, hrt, fun hb => ?_⟩
        dsimp only [d']
        rw [hbt hb, rd_add_of_ne n p w (shiftIdx p j') (shiftIdx_ne p j'), unshiftIdx_shiftIdx]
    · intro t ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨j, hj, hbwj, hrj, hopj, hinj⟩ := (hcov t ht).1
        have hjp : j ≠ p := by intro e; subst e; rw [hrj] at hp_top; cases hp_top
        have hj' : unshiftIdx p j < C'.gates.length := unshiftIdx_lt_rdel hp_lt hj hjp
        have hshj : shiftIdx p (unshiftIdx p j) = j := shiftIdx_unshiftIdx p j hjp
        have hga := gateAt_rdelC_of_rb (w := w) hp_lt hrb hj'
        rw [hshj] at hga
        refine ⟨unshiftIdx p j, hj', ?_, ?_, by rw [hga]; exact hopj, ?_⟩
        · dsimp only [d']; rw [hbwj, rd_add_of_ne n p w j hjp]
        · dsimp only [d']; rw [hshj]; exact hrj
        · rw [hga]; rcases hinj with h | h <;> simp [delGate, h, d']
      · have hz := (hcov t ht).2.1
        rw [hgates_eq Kind.z t.val (by intro h; cases h), hzL_eq t ht, ← hsh_zr t ht] at hz
        exact (isOrTree_shiftW hp_lt hrb _ (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
          (fun j' hj' => hnt_no (shiftIdx p j')
            (shiftIdx_lt_of_rdel hp_lt (Finset.mem_range.1 (Finset.mem_filter.1 hj').1))
            (by have := (Finset.mem_filter.1 hj').2; dsimp only [d'] at this; rw [this]; intro h; cases h))
          _ _).1 hz
      · have ho := (hcov t ht).2.2.1
        rw [hgates_eq Kind.o t.val (by intro h; cases h), hoL_eq t ht, ← hsh_or t ht] at ho
        exact (isOrTree_shiftW hp_lt hrb _ (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
          (fun j' hj' => hnt_no (shiftIdx p j')
            (shiftIdx_lt_of_rdel hp_lt (Finset.mem_range.1 (Finset.mem_filter.1 hj').1))
            (by have := (Finset.mem_filter.1 hj').2; dsimp only [d'] at this; rw [this]; intro h; cases h))
          _ _).1 ho
      · intro r hr
        have hL := (hcov t ht).2.2.2 r hr
        unfold LamOK at hL ⊢
        split at hL
        · rename_i hrc
          simp only [d', hrc, ↓reduceIte]
          refine ⟨(hcent (d'.lam t r)).1 (by rw [hsh_lam t ht r hr]; exact hL.1), ?_, ?_⟩
          · rcases hL.2.1 with heq | ⟨j, hj, heq, hrj⟩
            · left; rw [heq]; unfold rd; simp [show r.val < n + p by have := r.isLt; omega]
            · right
              have hjp : j ≠ p := by intro e; subst e; rw [hrj] at hp_top; cases hp_top
              refine ⟨unshiftIdx p j, unshiftIdx_lt_rdel hp_lt hj hjp,
                by rw [heq, rd_add_of_ne n p w j hjp], by rw [shiftIdx_unshiftIdx p j hjp]; exact hrj⟩
          · intro htr; rw [hL.2.2 htr]
        · rename_i hrc
          simp only [d', hrc, ↓reduceIte]
          rw [hL]; unfold rd; simp [show r.val < n + p by have := r.isLt; omega]
    · have htopG' : topGates d' C' = ((topGates d C).erase p).image (unshiftIdx p) := by
        ext j'
        simp only [topGates, Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨hj', hr'⟩
          exact ⟨shiftIdx p j', ⟨shiftIdx_ne p j', shiftIdx_lt_of_rdel hp_lt hj', hr'⟩,
            unshiftIdx_shiftIdx p j'⟩
        · rintro ⟨j, ⟨hjp, hj, hrj⟩, rfl⟩
          refine ⟨unshiftIdx_lt_rdel hp_lt hj hjp, ?_⟩
          dsimp only [d']; rw [shiftIdx_unshiftIdx p j hjp]; exact hrj
      have htopL' : topLeaves d' (A.erase a) = ((topLeaves d A).erase a.val).image (rd n p w) := by
        ext u'
        simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro (⟨b, ⟨hba, hbA⟩, rfl⟩ | ⟨t, ⟨ht, htu⟩, rfl⟩)
          · exact ⟨b.val, ⟨fun e => hba (Fin.ext e), Or.inl ⟨b, hbA, rfl⟩⟩,
              by unfold rd; simp [show b.val < n + p by have := b.isLt; omega]⟩
          · obtain ⟨jt, _, hbwt, _, _, _⟩ := (hcov t ht).1
            exact ⟨d.bw t, ⟨by have := a.isLt; omega, Or.inr ⟨t, ⟨ht, htu⟩, rfl⟩⟩, rfl⟩
        · rintro ⟨u, ⟨hua, ⟨b, hbA, rfl⟩ | ⟨t, ⟨ht, htu⟩, rfl⟩⟩, rfl⟩
          · left; refine ⟨b, ⟨fun e => hua (congrArg Fin.val e), hbA⟩, ?_⟩
            unfold rd; simp [show b.val < n + p by have := b.isLt; omega]
          · right; exact ⟨t, ⟨ht, htu⟩, rfl⟩
      rw [htopG', htopL']
      exact isOrTree_top_delete hp_lt hrb (fun j hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
        htop ha_topL ha_ne_out hpG hp_in hwa hw_lt ha_only
  obtain ⟨hC'min, hC'fun⟩ := (hIH C').2 ⟨d', hv'⟩
  have hCfun : circuitFun n C = graphFun K A := by
    funext x
    by_cases hxa : x a = true
    · rw [graphFun_erase K A a haA, hxa, Bool.true_or]
      have hp_true : (wiresFrom C.gates (List.ofFn x)).getD (n + p) false = true := by
        rw [wiresFrom_gate_eval_rb hrb x hp_lt, hp_op]
        have ha_v : (wiresFrom C.gates (List.ofFn x)).getD a.val false = true := by
          rw [wiresFrom_input_val C x a.isLt, hxa]
        rcases hp_in with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, GateOp.eval, ha_v] <;> simp
      have hmem_p : n + p - n ∈ topGates d C := by
        rw [Nat.add_sub_cancel_left]
        exact hpG
      exact orTree_true_up hrb (fun j hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
        htop x (n + p) (Or.inr ⟨by omega, hmem_p⟩) hp_true
    · have hxaf : x a = false := Bool.eq_false_iff.2 hxa
      have hp_eq : (wiresFrom C.gates (List.ofFn x)).getD (n + p) false =
          (wiresFrom C.gates (List.ofFn x)).getD w false := by
        rw [wiresFrom_gate_eval_rb hrb x hp_lt, hp_op]
        have ha_v : (wiresFrom C.gates (List.ofFn x)).getD a.val false = false := by
          rw [wiresFrom_input_val C x a.isLt, hxaf]
        rcases hp_in with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, GateOp.eval, ha_v] <;> simp
      have hev := rdel_eval hp_lt hw_lt x hp_eq C.output
      rw [graphFun_erase K A a haA, hxaf, Bool.false_or, ← hC'fun]
      exact hev.symm
  refine ⟨⟨valid_fanInTwo hv, ?_⟩, hCfun⟩
  intro D hDfit hDfun
  have hlo := (size_jump K A a hAdisj haA hne C' hC'min hC'fun).2 D hDfit (hDfun.trans hCfun)
  have hsz : C.size = C'.size + 1 := by change C.gates.length = C'.gates.length + 1; omega
  omega

private theorem min_to_valid {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (hne : (∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card)
    (hIH : ∀ C : Circuit,
      (IsMinimalCircuit n C ∧ circuitFun n C = graphFun K (A.erase a)) ↔
      IsNestedCoverCircuit n K (A.erase a) C)
    (C : Circuit) (hCmin : IsMinimalCircuit n C) (hCfun : circuitFun n C = graphFun K A) :
    IsNestedCoverCircuit n K A C := by
  obtain ⟨x0, x1, hx0, hx1⟩ := graphFun_erase_nonconst K A a haA hne
  obtain ⟨C0, hC0min, hC0fun⟩ := exists_minimal_circuit n (graphFun K (A.erase a))
  obtain ⟨hup, hlo⟩ := size_jump K A a hAdisj haA hne C0 hC0min hC0fun
  have hCsz : C.size = C0.size + 1 := by
    obtain ⟨U, hUfit, hUsz, hUev⟩ := hup
    have h1 := hCmin.2 U hUfit (by rw [hCfun]; exact funext hUev)
    have h2 := hlo C hCmin.1 hCfun
    omega
  obtain ⟨p, w, hp_read, hp_uniq, hp_op, hp_in, hwa, hw_lt⟩ :=
    unique_or_reader K A a hAdisj haA hne C0 hC0min hC0fun C hCmin hCfun
  have hCout_ne_a : C.output ≠ a.val := by
    intro h
    have h1 : circuitFun n C (Function.update x1 a false) = false := by
      rw [circuitFun_eq_getD, h, wiresFrom_input_val C _ a.isLt, Function.update_self]
    rw [hCfun, graphFun_update_false K A a hAdisj haA, hx1] at h1
    cases h1
  let C' := rdelC n p.val w C
  have hlen' : C'.gates.length + 1 = C.gates.length := rdelGates_length n p.val w C.gates p.isLt
  have hC'no_a : ∀ g ∈ C'.gates, (g.op = GateOp.not → g.inputs.head? ≠ some a.val) ∧
      (g.op ≠ GateOp.not → a.val ∉ g.inputs) := by
    intro g hg
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hg
    have hj_ne_p : shiftIdx p.val j' ≠ p.val := shiftIdx_ne p.val j'
    have hj_lt : shiftIdx p.val j' < C.gates.length := shiftIdx_lt_of_rdel p.isLt hj'
    have hnot_read : ¬ readsEff C a.val ⟨shiftIdx p.val j', hj_lt⟩ := fun h =>
      hj_ne_p (congrArg Fin.val (hp_uniq _ h))
    rw [← gateAt_eq_getElem hj']
    have hgaC : C.gates.get ⟨shiftIdx p.val j', hj_lt⟩ = gateAt C (shiftIdx p.val j') :=
      (gateAt_eq_getElem hj_lt).symm
    rw [readsEff, hgaC] at hnot_read
    by_cases hlt : j' < p.val
    · rw [gateAt_rdelC_lt p.isLt hlt]
      have hsh : shiftIdx p.val j' = j' := by simp [shiftIdx, hlt]
      rw [hsh] at hnot_read
      exact ⟨fun hnot hhd => hnot_read (Or.inl ⟨hnot, hhd⟩),
        fun hne' hmem => hnot_read (Or.inr ⟨hne', hmem⟩)⟩
    · rw [gateAt_rdelC_ge p.isLt (by omega) hj']
      have hsh : shiftIdx p.val j' = j' + 1 := by simp [shiftIdx, hlt]
      rw [hsh] at hnot_read
      have hrd_a : ∀ u, rd n p.val w u = a.val ↔ u = a.val := by
        intro u; unfold rd; have ha_lt := a.isLt
        split_ifs
        · rfl
        · exact ⟨fun e => (hwa e).elim, fun e => by omega⟩
        · exact ⟨fun e => by omega, fun e => by omega⟩
      simp only [delGate, List.head?_map, List.mem_map]
      refine ⟨fun hnot hhd => ?_, fun hne' ⟨u, hu, hru⟩ => ?_⟩
      · cases hins : (gateAt C (j' + 1)).inputs with
        | nil => rw [hins] at hhd; simp at hhd
        | cons u tl =>
          rw [hins] at hhd
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
          exact hnot_read (Or.inl ⟨hnot, by simp [hins, (hrd_a u).1 hhd]⟩)
      · rw [(hrd_a u).1 hru] at hu
        exact hnot_read (Or.inr ⟨hne', hu⟩)
  have hC'out_ne_a : C'.output ≠ a.val := by
    change rd n p.val w C.output ≠ a.val
    unfold rd; have ha_lt := a.isLt
    split_ifs
    · exact hCout_ne_a
    · exact hwa
    · omega
  have hC'fun : circuitFun n C' = graphFun K (A.erase a) := by
    funext x
    let x0' := Function.update x a false
    have h1 : circuitFun n C' x = circuitFun n C' x0' := by
      rw [circuitFun_eq_getD, circuitFun_eq_getD]
      apply wiresFrom_agree_off_a a.val C'.gates hC'no_a (List.ofFn x) (List.ofFn x0')
        (by simp) (by simp [a.isLt]) _ C'.output hC'out_ne_a
      intro i hi
      by_cases hil : i < n
      · rw [List.getD_eq_getElem _ _ (by simp [hil]), List.getD_eq_getElem _ _ (by simp [hil]),
          List.getElem_ofFn, List.getElem_ofFn]
        have hne_a : (⟨i, hil⟩ : Fin n) ≠ a := fun e => hi (congrArg Fin.val e)
        exact (Function.update_of_ne hne_a false x).symm
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hp_eq : (wiresFrom C.gates (List.ofFn x0')).getD (n + p.val) false =
        (wiresFrom C.gates (List.ofFn x0')).getD w false := by
      have hga : C.gates[p.val] = gateAt C p.val := (gateAt_eq_getElem p.isLt).symm
      have h1' := wiresFrom_getElem_gate (gs := C.gates) (w := List.ofFn x0') p.isLt
      simp only [List.length_ofFn, hga, hp_op] at h1'
      have ha_tk : (wiresFrom (C.gates.take p.val) (List.ofFn x0')).getD a.val false = false := by
        rw [wiresFrom_getD_take_eq p.isLt (by simp; have := a.isLt; omega),
          wiresFrom_input_val C x0' a.isLt]
        simp [x0']
      have hw_tk : (wiresFrom (C.gates.take p.val) (List.ofFn x0')).getD w false =
          (wiresFrom C.gates (List.ofFn x0')).getD w false :=
        wiresFrom_getD_take_eq p.isLt (by simp; exact hw_lt)
      rw [h1']
      rcases hp_in with h | h <;> rw [h] <;>
        simp only [List.map_cons, List.map_nil, GateOp.eval, ha_tk, hw_tk] <;> simp
    rw [h1, circuitFun_eq_getD, show C'.output = rd n p.val w C.output from rfl,
      rdel_eval p.isLt hw_lt x0' hp_eq C.output, ← circuitFun_eq_getD, hCfun,
      graphFun_update_false K A a hAdisj haA]
  have hC'min : IsMinimalCircuit n C' := by
    refine ⟨rdelC_fanInTwo n p.val w C hCmin.1, ?_⟩
    intro D hDfit hDfun
    have hDmin := hC0min.2 D hDfit (hDfun.trans (hC'fun.trans hC0fun.symm))
    have hsz' : C'.size = C0.size := by
      have : C'.gates.length + 1 = C.gates.length := hlen'
      have : C.gates.length = C0.gates.length + 1 := hCsz
      change C'.gates.length = C0.gates.length; omega
    omega
  obtain ⟨d', hv'⟩ := (hIH C').1 ⟨hC'min, hC'fun⟩
  have hrb' := hv'.1
  have hmincov := hv'.2.1
  have hown := hv'.2.2.1
  have htie := hv'.2.2.2.1
  have hroles' := hv'.2.2.2.2.1
  have hcov' := hv'.2.2.2.2.2.1
  have htop' := hv'.2.2.2.2.2.2
  have hrb : ReadsBack n C := readsBack_of_rdelC p.isLt hrb' (by
    intro i hi
    rcases hp_in with h | h <;> rw [h] at hi <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    · rcases hi with h1 | h2
      · rw [h1]; have := a.isLt; omega
      · rw [h2]; exact hw_lt
    · rcases hi with h1 | h2
      · rw [h1]; exact hw_lt
      · rw [h2]; have := a.isLt; omega)
  have hno_a_C : ∀ j < C.gates.length, j ≠ p.val → a.val ∉ (gateAt C j).inputs := by
    intro j hj hjp hmem
    have hj' : unshiftIdx p.val j < C'.gates.length := unshiftIdx_lt_rdel p.isLt hj hjp
    have hga := gateAt_rdelC_of_rb (w := w) p.isLt hrb hj'
    rw [shiftIdx_unshiftIdx p.val j hjp] at hga
    have hnot : (gateAt C j).op ≠ GateOp.not := by
      have h1 := valid_gate_no_not hv' hj'
      rw [hga] at h1; exact h1
    have hgaC : C.gates.get ⟨j, hj⟩ = gateAt C j := (gateAt_eq_getElem hj).symm
    have hread : readsEff C a.val ⟨j, hj⟩ := Or.inr ⟨hgaC ▸ hnot, hgaC ▸ hmem⟩
    exact hjp (congrArg Fin.val (hp_uniq ⟨j, hj⟩ hread))
  have ha_not_cov : a ∉ d'.cover := not_mem_minCover_of_isolated hmincov a (hAdisj a haA)
  have hbw'_ge : ∀ t ∈ d'.cover, n ≤ d'.bw t := by
    intro t ht; obtain ⟨j, _, hbw, _, _, _⟩ := (hcov' t ht).1; omega
  have hbw'_role : ∀ t ∈ d'.cover, ∃ j' < C'.gates.length, d'.bw t = n + j' ∧ d'.role j' = (Kind.b, t.val) := by
    intro t ht; obtain ⟨j', hj', hbw, hr, _, _⟩ := (hcov' t ht).1; exact ⟨j', hj', hbw, hr⟩
  have hw_top : w ∈ topLeaves d' (A.erase a) ∨ (n ≤ w ∧ w - n ∈ topGates d' C') := by
    by_contra hnot_top
    push Not at hnot_top
    obtain ⟨hw_notL, hw_notG⟩ := hnot_top
    have hex_tstar : ∃ tstar : Option (Fin n),
        (∀ u ∈ d'.cover, some u ≠ tstar →
          w ∉ zLeaves d' u ∧ ¬ (n ≤ w ∧ w - n ∈ gatesOf d' C' Kind.z u.val)) ∧
        (∀ u ∈ d'.cover, some u = tstar →
          w ∉ oLeaves d' u ∧ ¬ (n ≤ w ∧ w - n ∈ gatesOf d' C' Kind.o u.val)) := by
      by_cases hwn : w < n
      · let r : Fin n := ⟨w, hwn⟩
        by_cases hrc : r ∈ d'.cover
        · refine ⟨some r, ?_, ?_⟩
          · intro u hu hne_u
            refine ⟨?_, fun h => by omega⟩
            simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
            rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
            · exact hne_u (congrArg some (Fin.ext heq.symm))
            · have := hbw'_ge s hs; omega
          · intro u hu heq_u
            have hur : u = r := Option.some.inj heq_u
            subst hur
            refine ⟨?_, fun h => by omega⟩
            simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            rintro ⟨v, hv, hlam⟩
            have hnv : r ≠ v := K.ne_of_adj (hown.1 r v hv).1
            have hL := (hcov' r hu).2.2.2 v hv
            unfold LamOK at hL
            split at hL
            · rcases hL.2.1 with h1 | ⟨j', _, h2, _⟩
              · rw [h1] at hlam; exact hnv (Fin.ext hlam.symm)
              · rw [h2] at hlam; omega
            · rw [hL] at hlam; exact hnv (Fin.ext hlam.symm)
        · refine ⟨none, ?_, ?_⟩
          · intro u hu _
            refine ⟨?_, fun h => by omega⟩
            simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
            rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
            · exact hrc ((Fin.ext heq : r = u) ▸ hu)
            · have := hbw'_ge s hs; omega
          · intro _ _ heq; cases heq
      · have hwn_ge : n ≤ w := by omega
        have hj0_lt : w - n < C'.gates.length := by omega
        rcases hroles' (w - n) hj0_lt with htop0 | ⟨t0, ht0, hrt0, hbt0⟩
        · exfalso; exact hw_notG hwn_ge (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj0_lt, htop0⟩)
        · cases hkind0 : (d'.role (w - n)).1
          · refine ⟨some t0, ?_, ?_⟩
            · intro u hu hne_u
              refine ⟨?_, ?_⟩
              · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
                rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
                · have := u.isLt; omega
                · obtain ⟨js, _, hbws, hrs⟩ := hbw'_role s hs
                  have hjeq : w - n = js := by omega
                  rw [hjeq, hrs] at hkind0; cases hkind0
              · rintro ⟨_, hmem⟩
                have hfl := (Finset.mem_filter.1 hmem).2
                have hv_eq : u.val = t0.val := by
                  have h2 := congrArg Prod.snd hfl; exact h2.symm.trans hrt0
                exact hne_u (congrArg some (Fin.ext hv_eq))
            · intro u hu heq_u
              have hut : u = t0 := Option.some.inj heq_u
              rw [hut] at hu ⊢
              refine ⟨?_, ?_⟩
              · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                rintro ⟨v, hv, hlam⟩
                have hnv : t0 ≠ v := K.ne_of_adj (hown.1 t0 v hv).1
                have hL := (hcov' t0 hu).2.2.2 v hv
                unfold LamOK at hL
                split at hL
                · rcases hL.2.1 with h1 | ⟨j', _, h2, hrj'⟩
                  · rw [h1] at hlam; have := v.isLt; omega
                  · have hjeq : w - n = j' := by rw [← hlam, h2]; omega
                    rw [hjeq, hrj'] at hrt0
                    exact hnv (Fin.ext hrt0.symm)
                · rw [hL] at hlam; have := v.isLt; omega
              · rintro ⟨_, hmem⟩
                have hfl := (Finset.mem_filter.1 hmem).2
                have h1 := congrArg Prod.fst hfl
                rw [hkind0] at h1; cases h1
          · refine ⟨none, ?_, ?_⟩
            · intro u hu _
              refine ⟨?_, ?_⟩
              · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
                rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
                · have := u.isLt; omega
                · obtain ⟨js, _, hbws, hrs⟩ := hbw'_role s hs
                  have hjeq : w - n = js := by omega
                  rw [hjeq, hrs] at hkind0; cases hkind0
              · rintro ⟨_, hmem⟩
                have hfl := (Finset.mem_filter.1 hmem).2
                have h1 := congrArg Prod.fst hfl
                rw [hkind0] at h1; cases h1
            · intro _ _ heq; cases heq
          · have hbwt0 : d'.bw t0 = w := by have := hbt0 hkind0; omega
            cases htie0 : d'.tie t0 with
            | none =>
              exfalso
              exact hw_notL (Finset.mem_union_right _ (Finset.mem_image.2
                ⟨t0, Finset.mem_filter.2 ⟨ht0, htie0⟩, hbwt0⟩))
            | some t1 =>
              refine ⟨some t1, ?_, ?_⟩
              · intro u hu hne_u
                refine ⟨?_, ?_⟩
                · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
                  rintro (heq | ⟨s, ⟨hs, hts⟩, heq⟩)
                  · have := u.isLt; omega
                  · obtain ⟨js, _, hbws, hrs⟩ := hbw'_role s hs
                    have hjeq : w - n = js := by omega
                    rw [hjeq, hrs] at hrt0
                    have hst0 : s = t0 := Fin.ext hrt0
                    subst hst0
                    rw [htie0] at hts
                    exact hne_u hts.symm
                · rintro ⟨_, hmem⟩
                  have hfl := (Finset.mem_filter.1 hmem).2
                  have h1 := congrArg Prod.fst hfl
                  rw [hkind0] at h1; cases h1
              · intro u hu heq_u
                refine ⟨?_, ?_⟩
                · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                  rintro ⟨v, hv, hlam⟩
                  have hL := (hcov' u hu).2.2.2 v hv
                  unfold LamOK at hL
                  split at hL
                  · rcases hL.2.1 with h1 | ⟨j', _, h2, hrj'⟩
                    · rw [h1] at hlam; have := v.isLt; omega
                    · have hjeq : w - n = j' := by rw [← hlam, h2]; omega
                      rw [hjeq, hrj'] at hkind0; cases hkind0
                  · rw [hL] at hlam; have := v.isLt; omega
                · rintro ⟨_, hmem⟩
                  have hfl := (Finset.mem_filter.1 hmem).2
                  have h1 := congrArg Prod.fst hfl
                  rw [hkind0] at h1; cases h1
          · exfalso; exact hw_notG hwn_ge (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj0_lt, hkind0⟩)
    obtain ⟨tstar, hex_z, hex_o⟩ := hex_tstar
    let xa : Fin n → Bool := Function.update (fun _ => false) a true
    have hxa_ne : ∀ i : Fin n, i ≠ a → xa i = false := fun i hi => Function.update_of_ne hi _ _
    have hind : ∀ j < C.gates.length, j ≠ p.val →
        ((∃ u ∈ d'.cover, d'.role (unshiftIdx p.val j) = (Kind.b, u.val)) ∨
         (∃ u ∈ d'.cover, some u ≠ tstar ∧ d'.role (unshiftIdx p.val j) = (Kind.z, u.val)) ∨
         (∃ u ∈ d'.cover, some u = tstar ∧ d'.role (unshiftIdx p.val j) = (Kind.o, u.val)) ∨
         (d'.role (unshiftIdx p.val j)).1 = Kind.top) →
        (wiresFrom C.gates (List.ofFn xa)).getD (n + j) false = false := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj hjp hclause
        let j' := unshiftIdx p.val j
        have hj'_lt : j' < C'.gates.length := unshiftIdx_lt_rdel p.isLt hj hjp
        have hga := gateAt_rdelC_of_rb (w := w) p.isLt hrb hj'_lt
        rw [shiftIdx_unshiftIdx p.val j hjp] at hga
        have hin_val : ∀ i ∈ (gateAt C j).inputs, i < n + j := hrb j hj
        have hwire_false : ∀ i, i < n + j → i ≠ n + p.val →
            (rd n p.val w i < n ∧ rd n p.val w i ≠ a.val ∨
             (∃ k' < C'.gates.length, rd n p.val w i = n + k' ∧
               ((∃ u ∈ d'.cover, d'.role k' = (Kind.b, u.val)) ∨
                (∃ u ∈ d'.cover, some u ≠ tstar ∧ d'.role k' = (Kind.z, u.val)) ∨
                (∃ u ∈ d'.cover, some u = tstar ∧ d'.role k' = (Kind.o, u.val)) ∨
                (d'.role k').1 = Kind.top))) →
            (wiresFrom C.gates (List.ofFn xa)).getD i false = false := by
          intro i hilt himid hcase_i
          rcases hcase_i with ⟨hrlt, hrne⟩ | ⟨k', hk'lt, hreq, hck⟩
          · have hilt_n : i < n := by unfold rd at hrlt; split_ifs at hrlt <;> omega
            have hine_a : i ≠ a.val := by
              intro e; apply hrne; rw [e]; unfold rd; simp [show a.val < n + p.val by have := a.isLt; omega]
            rw [wiresFrom_input_val C xa hilt_n]
            exact hxa_ne ⟨i, hilt_n⟩ (fun e => hine_a (congrArg Fin.val e))
          · have hi_eq : i = n + shiftIdx p.val k' := by
              rw [← shiftW_rd n p.val w i himid, hreq, shiftW_add]
            rw [hi_eq]
            apply ih (shiftIdx p.val k') (by omega) (shiftIdx_lt_of_rdel p.isLt hk'lt) (shiftIdx_ne p.val k')
            simpa [unshiftIdx_shiftIdx] using hck
        have hbin_or : (gateAt C j).op = GateOp.or → (gateAt C j).inputs.length = 2 →
            (∀ i ∈ (gateAt C j).inputs, (wiresFrom C.gates (List.ofFn xa)).getD i false = false) →
            (wiresFrom C.gates (List.ofFn xa)).getD (n + j) false = false := by
          intro hop hlen hall
          rw [wiresFrom_gate_eval_rb hrb xa hj, hop]
          rcases hins : (gateAt C j).inputs with _ | ⟨x1', _ | ⟨x2', _ | _⟩⟩
          · rw [hins] at hlen; simp at hlen
          · rw [hins] at hlen; simp at hlen
          · simp only [List.map_cons, List.map_nil, GateOp.eval,
              hall x1' (by simp [hins]), hall x2' (by simp [hins])]
            rfl
          · rw [hins] at hlen; simp at hlen
        rcases hclause with ⟨u, hu, hrb_u⟩ | ⟨u, hu, hune, hrz_u⟩ | ⟨u, hu, hueq, hro_u⟩ | hrt_j
        · obtain ⟨j0, hj0, hbw0, hr0, hop0, hin0⟩ := (hcov' u hu).1
          have hj'eq : j' = j0 := by
            rcases hroles' j' hj'_lt with htop_c | ⟨t', ht', hrt', hbt'⟩
            · rw [hrb_u] at htop_c; cases htop_c
            · have hut' : t' = u := Fin.ext (by rw [hrb_u] at hrt'; exact hrt'.symm)
              subst hut'; have := hbt' (by rw [hrb_u]); omega
          have hga0 : gateAt C' j0 = delGate n p.val w (gateAt C j) := hj'eq ▸ hga
          have hopC : (gateAt C j).op = GateOp.and := by rw [hga0] at hop0; exact hop0
          have hlenC : (gateAt C j).inputs.length = 2 := by
            have : ((gateAt C j).inputs.map (rd n p.val w)).length = 2 := by
              change (delGate n p.val w (gateAt C j)).inputs.length = 2
              rw [← hga0]; rcases hin0 with h | h <;> simp [h]
            simpa using this
          have hex_in : ∀ target, target ∈ (gateAt C' j0).inputs →
              ∃ i ∈ (gateAt C j).inputs, rd n p.val w i = target := by
            intro target htarg; rw [hga0] at htarg; exact List.mem_map.1 htarg
          have hand_false : ∀ i ∈ (gateAt C j).inputs,
              (wiresFrom C.gates (List.ofFn xa)).getD i false = false →
              (wiresFrom C.gates (List.ofFn xa)).getD (n + j) false = false := by
            intro i hi hif
            rw [wiresFrom_gate_eval_rb hrb xa hj, hopC]
            rcases hins : (gateAt C j).inputs with _ | ⟨x1', _ | ⟨x2', _ | _⟩⟩
            · rw [hins] at hlenC; simp at hlenC
            · rw [hins] at hlenC; simp at hlenC
            · rw [hins] at hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              simp only [List.map_cons, List.map_nil, GateOp.eval]
              rcases hi with rfl | rfl
              · rw [hif]; rfl
              · rw [hif]; simp
            · rw [hins] at hlenC; simp at hlenC
          by_cases hustar : some u = tstar
          · obtain ⟨i, hi, hri⟩ := hex_in (d'.oroot u) (by rcases hin0 with h | h <;> simp [h])
            apply hand_false i hi
            have hor_mem := orTree_rho_mem (hcov' u hu).2.2.1
            have himid : i ≠ n + p.val := by
              intro e
              have hweq : w = d'.oroot u := by rw [← hri, e]; unfold rd; simp
              rcases hor_mem with hL | hG
              · exact (hex_o u hu hustar).1 (hweq ▸ hL)
              · exact (hex_o u hu hustar).2 (hweq ▸ hG)
            apply hwire_false i (hin_val i hi) himid
            rw [hri]
            rcases hor_mem with hL | ⟨hge, hG⟩
            · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hL
              obtain ⟨r, hr, hlam⟩ := hL
              rw [← hlam]
              have hnr : u ≠ r := K.ne_of_adj (hown.1 u r hr).1
              have hra : r ≠ a := fun e => hAdisj a haA u (e ▸ (hown.1 u r hr).1.symm)
              have hLam := (hcov' u hu).2.2.2 r hr
              unfold LamOK at hLam
              split at hLam
              · rename_i hrc
                rcases hLam.2.1 with h1 | ⟨k', hk', h2, hrk'⟩
                · left; rw [h1]; exact ⟨r.isLt, fun e => hra (Fin.ext e)⟩
                · right; exact ⟨k', hk', h2, Or.inr (Or.inl ⟨r, hrc, by intro e; exact hnr (Option.some.inj (hustar.trans e.symm)), hrk'⟩)⟩
              · left; rw [hLam]; exact ⟨r.isLt, fun e => hra (Fin.ext e)⟩
            · right
              have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
              have hrk' := (Finset.mem_filter.1 hG).2
              exact ⟨d'.oroot u - n, hk'lt, (Nat.add_sub_cancel' hge).symm,
                Or.inr (Or.inr (Or.inl ⟨u, hu, hustar, hrk'⟩))⟩
          · obtain ⟨i, hi, hri⟩ := hex_in (d'.zroot u) (by rcases hin0 with h | h <;> simp [h])
            apply hand_false i hi
            have hzr_mem := orTree_rho_mem (hcov' u hu).2.1
            have himid : i ≠ n + p.val := by
              intro e
              have hweq : w = d'.zroot u := by rw [← hri, e]; unfold rd; simp
              rcases hzr_mem with hL | hG
              · exact (hex_z u hu hustar).1 (hweq ▸ hL)
              · exact (hex_z u hu hustar).2 (hweq ▸ hG)
            apply hwire_false i (hin_val i hi) himid
            rw [hri]
            rcases hzr_mem with hL | ⟨hge, hG⟩
            · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hL
              rcases hL with heq | ⟨s, ⟨hs, _⟩, heq⟩
              · left; rw [heq]; exact ⟨u.isLt, fun e => ha_not_cov (Fin.ext e ▸ hu)⟩
              · right; obtain ⟨k', hk', hbws, hrk'⟩ := hbw'_role s hs
                exact ⟨k', hk', heq.symm.trans hbws, Or.inl ⟨s, hs, hrk'⟩⟩
            · right
              have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
              have hrk' := (Finset.mem_filter.1 hG).2
              exact ⟨d'.zroot u - n, hk'lt, (Nat.add_sub_cancel' hge).symm,
                Or.inr (Or.inl ⟨u, hu, hustar, hrk'⟩)⟩
        · have hj'G : j' ∈ gatesOf d' C' Kind.z u.val :=
            Finset.mem_filter.2 ⟨Finset.mem_range.2 hj'_lt, hrz_u⟩
          have hz1 := (hcov' u hu).2.1.1 j' hj'G
          apply hbin_or (by rw [hga] at hz1; exact hz1.1)
            (by have := hz1.2.1; rw [hga] at this; simpa [delGate] using this)
          intro i hi
          have hi' : rd n p.val w i ∈ (gateAt C' j').inputs := by
            rw [hga]; exact List.mem_map_of_mem hi
          have hmem' := hz1.2.2 _ hi'
          have himid : i ≠ n + p.val := by
            intro e
            have hweq : rd n p.val w i = w := by rw [e]; unfold rd; simp
            rw [hweq] at hmem'
            rcases hmem' with hL | hG
            · exact (hex_z u hu hune).1 hL
            · exact (hex_z u hu hune).2 hG
          apply hwire_false i (hin_val i hi) himid
          rcases hmem' with hL | ⟨hge, hG⟩
          · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hL
            rcases hL with heq | ⟨s, ⟨hs, _⟩, heq⟩
            · left; rw [heq]; exact ⟨u.isLt, fun e => ha_not_cov (Fin.ext e ▸ hu)⟩
            · right; obtain ⟨k', hk', hbws, hrk'⟩ := hbw'_role s hs
              exact ⟨k', hk', heq.symm.trans hbws, Or.inl ⟨s, hs, hrk'⟩⟩
          · right
            have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
            have hrk' := (Finset.mem_filter.1 hG).2
            exact ⟨rd n p.val w i - n, hk'lt, (Nat.add_sub_cancel' hge).symm,
              Or.inr (Or.inl ⟨u, hu, hune, hrk'⟩)⟩
        · have hj'G : j' ∈ gatesOf d' C' Kind.o u.val :=
            Finset.mem_filter.2 ⟨Finset.mem_range.2 hj'_lt, hro_u⟩
          have ho1 := (hcov' u hu).2.2.1.1 j' hj'G
          apply hbin_or (by rw [hga] at ho1; exact ho1.1)
            (by have := ho1.2.1; rw [hga] at this; simpa [delGate] using this)
          intro i hi
          have hi' : rd n p.val w i ∈ (gateAt C' j').inputs := by
            rw [hga]; exact List.mem_map_of_mem hi
          have hmem' := ho1.2.2 _ hi'
          have himid : i ≠ n + p.val := by
            intro e
            have hweq : rd n p.val w i = w := by rw [e]; unfold rd; simp
            rw [hweq] at hmem'
            rcases hmem' with hL | hG
            · exact (hex_o u hu hueq).1 hL
            · exact (hex_o u hu hueq).2 hG
          apply hwire_false i (hin_val i hi) himid
          rcases hmem' with hL | ⟨hge, hG⟩
          · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hL
            obtain ⟨r, hr, hlam⟩ := hL
            rw [← hlam]
            have hnr : u ≠ r := K.ne_of_adj (hown.1 u r hr).1
            have hra : r ≠ a := fun e => hAdisj a haA u (e ▸ (hown.1 u r hr).1.symm)
            have hLam := (hcov' u hu).2.2.2 r hr
            unfold LamOK at hLam
            split at hLam
            · rename_i hrc
              rcases hLam.2.1 with h1 | ⟨k', hk', h2, hrk'⟩
              · left; rw [h1]; exact ⟨r.isLt, fun e => hra (Fin.ext e)⟩
              · right; exact ⟨k', hk', h2, Or.inr (Or.inl ⟨r, hrc, by intro e; exact hnr (Option.some.inj (hueq.trans e.symm)), hrk'⟩)⟩
            · left; rw [hLam]; exact ⟨r.isLt, fun e => hra (Fin.ext e)⟩
          · right
            have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
            have hrk' := (Finset.mem_filter.1 hG).2
            exact ⟨rd n p.val w i - n, hk'lt, (Nat.add_sub_cancel' hge).symm,
              Or.inr (Or.inr (Or.inl ⟨u, hu, hueq, hrk'⟩))⟩
        · have hj'G : j' ∈ topGates d' C' :=
            Finset.mem_filter.2 ⟨Finset.mem_range.2 hj'_lt, hrt_j⟩
          have ht1 := htop'.1 j' hj'G
          apply hbin_or (by rw [hga] at ht1; exact ht1.1)
            (by have := ht1.2.1; rw [hga] at this; simpa [delGate] using this)
          intro i hi
          have hi' : rd n p.val w i ∈ (gateAt C' j').inputs := by
            rw [hga]; exact List.mem_map_of_mem hi
          have hmem' := ht1.2.2 _ hi'
          have himid : i ≠ n + p.val := by
            intro e
            have hweq : rd n p.val w i = w := by rw [e]; unfold rd; simp
            rw [hweq] at hmem'
            rcases hmem' with hL | hG
            · exact hw_notL hL
            · exact hw_notG hG.1 hG.2
          apply hwire_false i (hin_val i hi) himid
          rcases hmem' with hL | ⟨hge, hG⟩
          · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hL
            rcases hL with ⟨b, hb, heq⟩ | ⟨s, ⟨hs, _⟩, heq⟩
            · left; rw [← heq]; exact ⟨b.isLt, fun e => (Finset.mem_erase.1 hb).1 (Fin.ext e)⟩
            · right; obtain ⟨k', hk', hbws, hrk'⟩ := hbw'_role s hs
              exact ⟨k', hk', heq.symm.trans hbws, Or.inl ⟨s, hs, hrk'⟩⟩
          · right
            have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
            have hrk' := (Finset.mem_filter.1 hG).2
            exact ⟨rd n p.val w i - n, hk'lt, (Nat.add_sub_cancel' hge).symm, Or.inr (Or.inr (Or.inr hrk'))⟩
    have hout_mem := orTree_rho_mem htop'
    have hCout_ne_mid : C.output ≠ n + p.val := by
      intro e
      have hweq : C'.output = w := by change rd n p.val w C.output = w; rw [e]; unfold rd; simp
      rw [hweq] at hout_mem
      rcases hout_mem with hL | hG
      · exact hw_notL hL
      · exact hw_notG hG.1 hG.2
    have hCxa_false : circuitFun n C xa = false := by
      rw [circuitFun_eq_getD]
      have hsh_out : C.output = shiftW n p.val C'.output := (shiftW_rd n p.val w C.output hCout_ne_mid).symm
      rw [hsh_out]
      rcases hout_mem with hL | ⟨hge, hG⟩
      · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hL
        rcases hL with ⟨b, hb, heq⟩ | ⟨s, ⟨hs, _⟩, heq⟩
        · rw [← heq, shiftW_lt n p.val b.val (by have := b.isLt; omega),
            wiresFrom_input_val C xa b.isLt]
          exact hxa_ne b (Finset.mem_erase.1 hb).1
        · obtain ⟨k', hk', hbws, hrk'⟩ := hbw'_role s hs
          rw [← heq, hbws, shiftW_add]
          apply hind (shiftIdx p.val k') (shiftIdx_lt_of_rdel p.isLt hk') (shiftIdx_ne p.val k')
          simpa [unshiftIdx_shiftIdx] using Or.inl ⟨s, hs, hrk'⟩
      · have hk'lt := Finset.mem_range.1 (Finset.mem_filter.1 hG).1
        have hrk' := (Finset.mem_filter.1 hG).2
        have hC'eq : C'.output = n + (C'.output - n) := (Nat.add_sub_cancel' hge).symm
        rw [hC'eq, shiftW_add]
        apply hind (shiftIdx p.val (C'.output - n)) (shiftIdx_lt_of_rdel p.isLt hk'lt) (shiftIdx_ne p.val _)
        simpa [unshiftIdx_shiftIdx] using Or.inr (Or.inr (Or.inr hrk'))
    have hCxa_true : circuitFun n C xa = true := by
      rw [hCfun]; exact graphFun_update_true K A a haA (fun _ => false)
    rw [hCxa_false] at hCxa_true
    cases hCxa_true
  have hno_nontop_w : ∀ j' < C'.gates.length, (d'.role j').1 ≠ Kind.top → w ∉ (gateAt C' j').inputs := by
    have hnot_in_cov : ∀ u ∈ d'.cover, w ∉ zLeaves d' u ∧ w ∉ oLeaves d' u ∧
        ¬ (n ≤ w ∧ w - n ∈ gatesOf d' C' Kind.z u.val) ∧
        ¬ (n ≤ w ∧ w - n ∈ gatesOf d' C' Kind.o u.val) := by
      intro u hu
      rcases hw_top with hwL | ⟨hnw, hwG⟩
      · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hwL
        rcases hwL with ⟨b, hb, hbw_eq⟩ | ⟨t, ⟨ht, ht_none⟩, hbw_eq⟩
        · have hb_not_cov : b ∉ d'.cover :=
            not_mem_minCover_of_isolated hmincov b (hAdisj b (Finset.mem_erase.1 hb).2)
          refine ⟨?_, ?_, fun h => by have := b.isLt; omega, fun h => by have := b.isLt; omega⟩
          · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
            rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
            · exact hb_not_cov (Fin.ext (hbw_eq.trans heq) ▸ hu)
            · have := hbw'_ge s hs; have := b.isLt; omega
          · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            rintro ⟨r, hr, hlam⟩
            have hL := (hcov' u hu).2.2.2 r hr
            unfold LamOK at hL
            split at hL
            · rcases hL.2.1 with h1 | ⟨_, _, h2, _⟩
              · rw [h1] at hlam
                have hrb' : r = b := Fin.ext (hlam.trans hbw_eq.symm)
                subst hrb'; exact hAdisj r (Finset.mem_erase.1 hb).2 u (hown.1 u r hr).1.symm
              · rw [h2] at hlam; have := b.isLt; omega
            · rw [hL] at hlam
              have hrb' : r = b := Fin.ext (hlam.trans hbw_eq.symm)
              subst hrb'; exact hAdisj r (Finset.mem_erase.1 hb).2 u (hown.1 u r hr).1.symm
        · obtain ⟨jt, hjt, hbwt, hrt⟩ := hbw'_role t ht
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
            rintro (heq | ⟨s, ⟨hs, hts⟩, heq⟩)
            · have := u.isLt; omega
            · obtain ⟨js, _, hbws, hrs⟩ := hbw'_role s hs
              have hjeq : js = jt := by omega
              rw [hjeq, hrt] at hrs
              have hst : s = t := Fin.ext (congrArg Prod.snd hrs).symm
              subst hst; rw [ht_none] at hts; cases hts
          · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            rintro ⟨r, hr, hlam⟩
            have hL := (hcov' u hu).2.2.2 r hr
            unfold LamOK at hL
            split at hL
            · rcases hL.2.1 with h1 | ⟨jr, _, h2, hrj⟩
              · rw [h1] at hlam; have := r.isLt; omega
              · have hjeq : jr = jt := by omega
                rw [hjeq, hrt] at hrj; cases hrj
            · rw [hL] at hlam; have := r.isLt; omega
          · rintro ⟨_, hmem⟩
            have hfl := (Finset.mem_filter.1 hmem).2
            have hjeq : w - n = jt := by omega
            rw [hjeq, hrt] at hfl; cases hfl
          · rintro ⟨_, hmem⟩
            have hfl := (Finset.mem_filter.1 hmem).2
            have hjeq : w - n = jt := by omega
            rw [hjeq, hrt] at hfl; cases hfl
      · have hrw := (Finset.mem_filter.1 hwG).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
          rintro (heq | ⟨s, ⟨hs, _⟩, heq⟩)
          · have := u.isLt; omega
          · obtain ⟨js, _, hbws, hrs⟩ := hbw'_role s hs
            have hjeq : w - n = js := by omega
            rw [hjeq, hrs] at hrw; cases hrw
        · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          rintro ⟨r, hr, hlam⟩
          have hL := (hcov' u hu).2.2.2 r hr
          unfold LamOK at hL
          split at hL
          · rcases hL.2.1 with h1 | ⟨jr, _, h2, hrj⟩
            · rw [h1] at hlam; have := r.isLt; omega
            · have hjeq : w - n = jr := by omega
              rw [hjeq, hrj] at hrw; cases hrw
          · rw [hL] at hlam; have := r.isLt; omega
        · rintro ⟨_, hmem⟩
          have hfl := (Finset.mem_filter.1 hmem).2
          have h1 := congrArg Prod.fst hfl; rw [hrw] at h1; cases h1
        · rintro ⟨_, hmem⟩
          have hfl := (Finset.mem_filter.1 hmem).2
          have h1 := congrArg Prod.fst hfl; rw [hrw] at h1; cases h1
    intro j' hj' hjnt hmem
    rcases hroles' j' hj' with htop_c | ⟨u, hu, hru, hbu⟩
    · exact hjnt htop_c
    · obtain ⟨hzL, hoL, hzG, hoG⟩ := hnot_in_cov u hu
      cases hkind : (d'.role j').1
      · have hjG : j' ∈ gatesOf d' C' Kind.z u.val :=
          Finset.mem_filter.2 ⟨Finset.mem_range.2 hj', Prod.ext hkind hru⟩
        rcases ((hcov' u hu).2.1.1 j' hjG).2.2 w hmem with h1 | h2
        · exact hzL h1
        · exact hzG h2
      · have hjG : j' ∈ gatesOf d' C' Kind.o u.val :=
          Finset.mem_filter.2 ⟨Finset.mem_range.2 hj', Prod.ext hkind hru⟩
        rcases ((hcov' u hu).2.2.1.1 j' hjG).2.2 w hmem with h1 | h2
        · exact hoL h1
        · exact hoG h2
      · obtain ⟨j0, _, hbw0, _, _, hin0⟩ := (hcov' u hu).1
        have hjeq : j' = j0 := by have := hbu hkind; omega
        subst hjeq
        rcases hin0 with h | h <;> rw [h] at hmem <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        · rcases hmem with h1 | h2
          · rcases orTree_rho_mem (hcov' u hu).2.1 with hl | hg
            · exact hzL (h1 ▸ hl)
            · exact hzG (h1 ▸ hg)
          · rcases orTree_rho_mem (hcov' u hu).2.2.1 with hl | hg
            · exact hoL (h2 ▸ hl)
            · exact hoG (h2 ▸ hg)
        · rcases hmem with h1 | h2
          · rcases orTree_rho_mem (hcov' u hu).2.2.1 with hl | hg
            · exact hoL (h1 ▸ hl)
            · exact hoG (h1 ▸ hg)
          · rcases orTree_rho_mem (hcov' u hu).2.1 with hl | hg
            · exact hzL (h2 ▸ hl)
            · exact hzG (h2 ▸ hg)
      · exact hjnt hkind
  have hno_nontop_mid : ∀ j' < C'.gates.length, (d'.role j').1 ≠ Kind.top →
      n + p.val ∉ (gateAt C (shiftIdx p.val j')).inputs := by
    intro j' hj' hjnt hmem
    have hga := gateAt_rdelC_of_rb (w := w) p.isLt hrb hj'
    have hw_in : w ∈ (gateAt C' j').inputs := by
      rw [hga]
      exact List.mem_map.2 ⟨n + p.val, hmem, by unfold rd; simp⟩
    exact hno_nontop_w j' hj' hjnt hw_in
  have hmust_use_mid : readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) = 0 →
      C.output = n + p.val := by
    intro h0
    by_contra hne_out
    have hno_mid_C : ∀ j < C.gates.length, n + p.val ∉ (gateAt C j).inputs := by
      intro j hj hmem
      by_cases hjp : j = p.val
      · rw [hjp] at hmem; have := hrb p.val p.isLt (n + p.val) hmem; omega
      · have hj' : unshiftIdx p.val j < C'.gates.length := unshiftIdx_lt_rdel p.isLt hj hjp
        have hsh := shiftIdx_unshiftIdx p.val j hjp
        by_cases htopj : (d'.role (unshiftIdx p.val j)).1 = Kind.top
        · have hj'_mem : unshiftIdx p.val j ∈ topGates d' C' :=
            Finset.mem_filter.2 ⟨Finset.mem_range.2 hj', htopj⟩
          have hj_img : j ∈ (topGates d' C').image (shiftIdx p.val) :=
            Finset.mem_image.2 ⟨unshiftIdx p.val j, hj'_mem, hsh⟩
          have hle : (gateAt C j).inputs.count (n + p.val) ≤
              readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) :=
            Finset.single_le_sum (f := fun k => (gateAt C k).inputs.count (n + p.val))
              (fun _ _ => Nat.zero_le _) hj_img
          have hpos : 1 ≤ (gateAt C j).inputs.count (n + p.val) := List.count_pos_iff.2 hmem
          omega
        · exact hno_nontop_mid (unshiftIdx p.val j) hj' htopj (hsh.symm ▸ hmem)
    let xF := Function.update x0 a false
    let xT := Function.update x0 a true
    have hsplit : C.gates = C.gates.take p.val ++ C.gates[p.val] :: C.gates.drop (p.val + 1) := by
      have h1 := (List.take_append_drop p.val C.gates).symm
      rw [List.drop_eq_getElem_cons p.isLt] at h1; exact h1
    have hno_pre : ∀ g ∈ C.gates.take p.val,
        (g.op = GateOp.not → g.inputs.head? ≠ some a.val) ∧ (g.op ≠ GateOp.not → a.val ∉ g.inputs) := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hjlt : j < p.val := by have := List.length_take (i := p.val) (l := C.gates); omega
      have hge : (C.gates.take p.val)[j] = gateAt C j := by
        rw [List.getElem_take, gateAt_eq_getElem (by omega)]
      rw [hge]
      have hna := hno_a_C j (by omega) (by omega)
      refine ⟨fun _ hhd => ?_, fun _ => hna⟩
      cases hins : (gateAt C j).inputs with
      | nil => rw [hins] at hhd; simp at hhd
      | cons u tl =>
        rw [hins] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        exact hna (by simp [hins, hhd])
    have hpre_ag : ∀ i, i ≠ a.val →
        (wiresFrom (C.gates.take p.val) (List.ofFn xF)).getD i false =
        (wiresFrom (C.gates.take p.val) (List.ofFn xT)).getD i false := by
      apply wiresFrom_agree_off_a a.val (C.gates.take p.val) hno_pre (List.ofFn xF) (List.ofFn xT)
        (by simp) (by simp [a.isLt])
      intro i hi
      by_cases hil : i < n
      · rw [List.getD_eq_getElem _ _ (by simp [hil]), List.getD_eq_getElem _ _ (by simp [hil]),
          List.getElem_ofFn, List.getElem_ofFn]
        have hne_a : (⟨i, hil⟩ : Fin n) ≠ a := fun e => hi (congrArg Fin.val e)
        simp [xF, xT, Function.update_of_ne hne_a]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hno_post : ∀ g ∈ C.gates.drop (p.val + 1), a.val ∉ g.inputs ∧ n + p.val ∉ g.inputs := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hlt : p.val + 1 + k < C.gates.length := by simp [List.length_drop] at hk; omega
      have hge : (C.gates.drop (p.val + 1))[k] = gateAt C (p.val + 1 + k) := by
        rw [List.getElem_drop, gateAt_eq_getElem hlt]
      rw [hge]
      exact ⟨hno_a_C _ hlt (by omega), hno_mid_C _ hlt⟩
    set WF0 := wiresFrom (C.gates.take p.val) (List.ofFn xF)
    set WT0 := wiresFrom (C.gates.take p.val) (List.ofFn xT)
    have hWFlen : WF0.length = n + p.val := by
      simp [WF0, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt p.isLt)]
    have hWTlen : WT0.length = n + p.val := by
      simp [WT0, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt p.isLt)]
    set WF1 := WF0 ++ [(C.gates[p.val]).op.eval ((C.gates[p.val]).inputs.map fun i => WF0.getD i false)]
    set WT1 := WT0 ++ [(C.gates[p.val]).op.eval ((C.gates[p.val]).inputs.map fun i => WT0.getD i false)]
    have hpost_ag : (wiresFrom (C.gates.drop (p.val + 1)) WF1).getD C.output false =
        (wiresFrom (C.gates.drop (p.val + 1)) WT1).getD C.output false := by
      apply wiresFrom_agree_off_two a.val (n + p.val) (C.gates.drop (p.val + 1)) hno_post WF1 WT1
        (by simp [WF1, WT1, hWFlen, hWTlen]) (by simp [WF1, hWFlen]; have := a.isLt; omega)
        (by simp [WF1, hWFlen]) _ C.output hCout_ne_a hne_out
      intro i hi1 hi2
      by_cases hil : i < n + p.val
      · rw [show WF1.getD i false = WF0.getD i false from List.getD_append _ _ _ _ (by omega),
          show WT1.getD i false = WT0.getD i false from List.getD_append _ _ _ _ (by omega)]
        exact hpre_ag i hi1
      · have hgt : n + p.val + 1 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simp [WF1, hWFlen]; omega),
          List.getD_eq_default _ _ (by simp [WT1, hWTlen]; omega)]
    have heq_ev : circuitFun n C xF = circuitFun n C xT := by
      rw [circuitFun_eq_getD, circuitFun_eq_getD]
      conv_lhs => rw [hsplit, wiresFrom_append]
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact hpost_ag
    rw [hCfun, graphFun_update_false K A a hAdisj haA, graphFun_update_true K A a haA, hx0] at heq_ev
    cases heq_ev
  have hcase : (w = C'.output ∧ C.output = n + p.val ∧
      readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) = 0) ∨
      (w ≠ C'.output ∧ C.output = shiftW n p.val C'.output ∧
      readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) = 1) := by
    have hsum := readsIn_rdel_eq_w p.isLt hw_lt hrb (topGates d' C')
      (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
    have hreads_w : readsIn C' (topGates d' C') w = if w = C'.output then 0 else 1 := by
      rcases hw_top with hwL' | ⟨hnw, hwG'⟩
      · exact (htop'.2.1 w hwL').2
      · have h := htop'.2.2.1 (w - n) hwG'
        rwa [Nat.add_sub_cancel' hnw] at h
    rw [hreads_w] at hsum
    by_cases hwout : w = C'.output
    · simp only [hwout, ↓reduceIte] at hsum
      have hmid0 : readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) = 0 := by omega
      exact Or.inl ⟨hwout, hmust_use_mid hmid0, hmid0⟩
    · simp only [hwout, ↓reduceIte] at hsum
      have hne_mid : C.output ≠ n + p.val := by
        intro e; apply hwout
        change w = rd n p.val w C.output; rw [e]; unfold rd; simp
      have hmid_ne0 : readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) ≠ 0 :=
        fun h0 => hne_mid (hmust_use_mid h0)
      have hmid1 : readsIn C ((topGates d' C').image (shiftIdx p.val)) (n + p.val) = 1 := by omega
      exact Or.inr ⟨hwout, (shiftW_rd n p.val w C.output hne_mid).symm, hmid1⟩
  let d : NCCData n := {
    cover := d'.cover
    owns := d'.owns
    tie := d'.tie
    role := fun j => if j = p.val then (Kind.top, 0) else d'.role (unshiftIdx p.val j)
    bw := fun t => shiftW n p.val (d'.bw t)
    zroot := fun t => shiftW n p.val (d'.zroot t)
    oroot := fun t => shiftW n p.val (d'.oroot t)
    lam := fun t r => shiftW n p.val (d'.lam t r)
  }
  have hrole_sh : ∀ j', d.role (shiftIdx p.val j') = d'.role j' := by
    intro j'; dsimp only [d]; rw [if_neg (shiftIdx_ne p.val j'), unshiftIdx_shiftIdx]
  have hgates_eq : ∀ k t, k ≠ Kind.top →
      gatesOf d C k t = (gatesOf d' C' k t).image (shiftIdx p.val) := by
    intro k t hk
    ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hrj⟩
      have hjp : j ≠ p.val := by
        intro e; subst e; dsimp only [d] at hrj; simp only [↓reduceIte] at hrj
        exact hk (congrArg Prod.fst hrj).symm
      dsimp only [d] at hrj; rw [if_neg hjp] at hrj
      exact ⟨unshiftIdx p.val j, ⟨unshiftIdx_lt_rdel p.isLt hj hjp, hrj⟩,
        shiftIdx_unshiftIdx p.val j hjp⟩
    · rintro ⟨j', ⟨hj', hrj'⟩, rfl⟩
      exact ⟨shiftIdx_lt_of_rdel p.isLt hj', by rw [hrole_sh]; exact hrj'⟩
  have hzL_eq : ∀ t, zLeaves d t = (zLeaves d' t).image (shiftW n p.val) := by
    intro t
    ext u
    simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨s, ⟨hs, hts⟩, rfl⟩)
      · exact ⟨t.val, Or.inl rfl, shiftW_lt n p.val t.val (by have := t.isLt; omega)⟩
      · exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs, hts⟩, rfl⟩, rfl⟩
    · rintro ⟨v, (rfl | ⟨s, ⟨hs, hts⟩, rfl⟩), rfl⟩
      · exact Or.inl (shiftW_lt n p.val t.val (by have := t.isLt; omega))
      · exact Or.inr ⟨s, ⟨hs, hts⟩, rfl⟩
  have hoL_eq : ∀ t, oLeaves d t = (oLeaves d' t).image (shiftW n p.val) := by
    intro t
    ext u
    simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨d'.lam t r, ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩
  have hcent := isCentred_shiftW (w := w) (d := d) (d' := d') p.isLt rfl (by simp [d])
    (fun j' _ => hrole_sh j')
    (fun j' hj' hz => hno_nontop_mid j' hj' (by rw [hz]; intro h; cases h))
  refine ⟨d, hrb, hmincov, hown, htie, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjp : j = p.val
    · left; simp [d, hjp]
    · have hj' : unshiftIdx p.val j < C'.gates.length := unshiftIdx_lt_rdel p.isLt hj hjp
      dsimp only [d]; rw [if_neg hjp]
      rcases hroles' (unshiftIdx p.val j) hj' with htop_c | ⟨t, ht, hrt, hbt⟩
      · exact Or.inl htop_c
      · right; refine ⟨t, ht, hrt, fun hb => ?_⟩
        rw [hbt hb, shiftW_add, shiftIdx_unshiftIdx p.val j hjp]
  · intro t ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨j', hj', hbw', hr', hop', hin'⟩ := (hcov' t ht).1
      have hga := gateAt_rdelC_of_rb (w := w) p.isLt hrb hj'
      have hnomid : n + p.val ∉ (gateAt C (shiftIdx p.val j')).inputs :=
        hno_nontop_mid j' hj' (by rw [hr']; intro h; cases h)
      have hinsC : (gateAt C (shiftIdx p.val j')).inputs =
          (gateAt C' j').inputs.map (shiftW n p.val) := by
        rw [hga]; simp only [delGate, List.map_map]; symm
        apply list_map_id_mem
        intro i hi; exact shiftW_rd n p.val w i (fun e => hnomid (e ▸ hi))
      refine ⟨shiftIdx p.val j', shiftIdx_lt_of_rdel p.isLt hj',
        by dsimp only [d]; rw [hbw', shiftW_add], by rw [hrole_sh]; exact hr',
        by rw [hga] at hop'; exact hop', ?_⟩
      rw [hinsC]; rcases hin' with h | h <;> simp [h, d]
    · rw [hgates_eq Kind.z t.val (by intro h; cases h), hzL_eq t]
      exact (isOrTree_shiftW p.isLt hrb _ (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
        (fun j' hj' => hno_nontop_mid j' (Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
          (by rw [(Finset.mem_filter.1 hj').2]; intro h; cases h)) _ _).2 (hcov' t ht).2.1
    · rw [hgates_eq Kind.o t.val (by intro h; cases h), hoL_eq t]
      exact (isOrTree_shiftW p.isLt hrb _ (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
        (fun j' hj' => hno_nontop_mid j' (Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
          (by rw [(Finset.mem_filter.1 hj').2]; intro h; cases h)) _ _).2 (hcov' t ht).2.2.1
    · intro r hr
      have hL := (hcov' t ht).2.2.2 r hr
      unfold LamOK at hL ⊢
      split at hL
      · rename_i hrc
        simp only [d, hrc, ↓reduceIte]
        refine ⟨(hcent (d'.lam t r)).2 hL.1, ?_, ?_⟩
        · rcases hL.2.1 with h1 | ⟨j', hj', h2, hrj'⟩
          · left; rw [h1, shiftW_lt n p.val r.val (by have := r.isLt; omega)]
          · right; refine ⟨shiftIdx p.val j', shiftIdx_lt_of_rdel p.isLt hj',
              by rw [h2, shiftW_add], by rw [if_neg (shiftIdx_ne p.val j'), unshiftIdx_shiftIdx]; exact hrj'⟩
        · intro htr; rw [hL.2.2 htr]
      · rename_i hrc
        simp only [d, hrc, ↓reduceIte]
        rw [hL, shiftW_lt n p.val r.val (by have := r.isLt; omega)]
  · have htopG : topGates d C = insert p.val ((topGates d' C').image (shiftIdx p.val)) := by
      ext j
      simp only [topGates, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨hj, hrj⟩
        by_cases hjp : j = p.val
        · exact Or.inl hjp
        · right; dsimp only [d] at hrj; rw [if_neg hjp] at hrj
          exact ⟨unshiftIdx p.val j, ⟨unshiftIdx_lt_rdel p.isLt hj hjp, hrj⟩,
            shiftIdx_unshiftIdx p.val j hjp⟩
      · rintro (rfl | ⟨j', ⟨hj', hr'⟩, rfl⟩)
        · exact ⟨p.isLt, by simp [d]⟩
        · exact ⟨shiftIdx_lt_of_rdel p.isLt hj', by rw [hrole_sh]; exact hr'⟩
    have htopL : topLeaves d A = insert a.val ((topLeaves d' (A.erase a)).image (shiftW n p.val)) := by
      ext u
      simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (⟨b, hbA, rfl⟩ | ⟨t, ⟨ht, htu⟩, rfl⟩)
        · by_cases hba : b = a
          · exact Or.inl (congrArg Fin.val hba)
          · right; exact ⟨b.val, Or.inl ⟨b, ⟨hba, hbA⟩, rfl⟩, shiftW_lt n p.val b.val (by have := b.isLt; omega)⟩
        · right; exact ⟨d'.bw t, Or.inr ⟨t, ⟨ht, htu⟩, rfl⟩, rfl⟩
      · rintro (rfl | ⟨v, ⟨b, ⟨_, hbA⟩, rfl⟩ | ⟨t, ⟨ht, htu⟩, rfl⟩, rfl⟩)
        · exact Or.inl ⟨a, haA, rfl⟩
        · exact Or.inl ⟨b, hbA, (shiftW_lt n p.val b.val (by have := b.isLt; omega)).symm⟩
        · exact Or.inr ⟨t, ⟨ht, htu⟩, rfl⟩
    have ha_not_topL' : a.val ∉ topLeaves d' (A.erase a) := by
      simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
      rintro (⟨b, ⟨hba, _⟩, heq⟩ | ⟨t, ⟨ht, _⟩, heq⟩)
      · exact hba (Fin.ext heq)
      · have := hbw'_ge t ht; have := a.isLt; omega
    rw [htopG, htopL]
    exact isOrTree_top_insert p.isLt hrb (fun j' hj' => Finset.mem_range.1 (Finset.mem_filter.1 hj').1)
      htop' ha_not_topL' hwa hw_lt hw_top hp_op hp_in hcase

end PEqualNP.Outside.L_meta_537_aux

theorem PEqualNP.Outside.L_meta_537 :
    ∀ (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)) (a : Fin n), ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k → Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj) → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → a ∈ A → ((∃ u v : Fin n, K.Adj u v) ∨ 2 ≤ A.card) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K (A.erase a)) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K (A.erase a) C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C) := by
  intro n K _ A a k m H _ _ hAdisj haA hne hIH C
  constructor
  · rintro ⟨hCmin, hCfun⟩
    exact PEqualNP.Outside.L_meta_537_aux.min_to_valid K A a hAdisj haA hne hIH C hCmin hCfun
  · intro hNCC
    exact PEqualNP.Outside.L_meta_537_aux.valid_to_min K A a hAdisj haA hne hIH C hNCC
