import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

namespace H926
open PEqualNP PEqualNP.MetaComplexity

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

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

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

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

theorem orChain (k : ℕ) : ∀ m : ℕ, k + 1 ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = k ∧ out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∃ i : Fin (k + 1), w.getD i false = true) := by
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], 0, by simp, rfl, by simp; omega, ?_⟩
    intro w _
    simp [wiresFrom]
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.or, [out, k + 1]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD (k + 1) false = w.getD (k + 1) false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      have step : wiresFrom [⟨GateOp.or, [out, k + 1]⟩] v
          = v ++ [GateOp.or.eval ([out, k + 1].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [ev w hw, e1]
      simp [Fin.exists_fin_succ']

theorem or_size (n s : ℕ) :
    HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true)) s ↔ n ≤ s + 1 := by
  constructor
  · apply dep_lower
    intro i
    refine ⟨fun _ => false, ?_⟩
    simp only [Bool.not_false, ne_eq]
    have h1 : (∃ j : Fin n, Function.update (fun _ : Fin n => false) i true j = true) :=
      ⟨i, by simp⟩
    simp [h1]
  · intro h
    cases n with
    | zero =>
      refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
      intro x
      simp [Circuit.eval, Circuit.wires]
    | succ k =>
      obtain ⟨gs, out, ok, len, _, ev⟩ := orChain k (k + 1) le_rfl
      refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
      intro x
      have h := ev (List.ofFn x) (by simp)
      simp only [Circuit.eval, wires_eq, h, getD_ofFn]

end H926

namespace H926.EdgeUpper
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds H926

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  apply bld_hasCircuitSize
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

end H926.EdgeUpper


def ad1 (i j : Fin 2) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0)])

def G1 : SimpleGraph (Fin 2) where
  Adj i j := ad1 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst1 : DecidableRel G1.Adj := fun i j => inferInstanceAs (Decidable (ad1 i j = true))

theorem hfun1 : (fun x : Fin 2 → Bool => (x 0 && x 1)) = (fun x : Fin 2 → Bool => decide (∃ i j : Fin 2, G1.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b : Bool, ((a && b)) = decide (∃ i j : Fin 2, G1.Adj i j ∧ (![a, b] : Fin 2 → Bool) i = true ∧ (![a, b] : Fin 2 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard1 : G1.edgeFinset.card = 1 := by
  decide +kernel

theorem hcovb1 : ∀ i j : Fin 2, G1.Adj i j → i ∈ ({0} : Finset (Fin 2)) ∨ j ∈ ({0} : Finset (Fin 2)) := by
  decide

theorem main1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  rw [hfun1]
  have h := H926.EdgeUpper.edge_upper 2 G1 {0} ⟨0, 1, by decide⟩ hcovb1
  rw [hcard1] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 2)).card = 1 := by decide
  rw [this] at h2
  omega

def ad2 (i j : Fin 3) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0)])

def G2 : SimpleGraph (Fin 3) where
  Adj i j := ad2 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst2 : DecidableRel G2.Adj := fun i j => inferInstanceAs (Decidable (ad2 i j = true))

theorem hfun2 : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) = (fun x : Fin 3 → Bool => decide (∃ i j : Fin 3, G2.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c : Bool, ((a && b) || (a && c)) = decide (∃ i j : Fin 3, G2.Adj i j ∧ (![a, b, c] : Fin 3 → Bool) i = true ∧ (![a, b, c] : Fin 3 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard2 : G2.edgeFinset.card = 2 := by
  decide +kernel

theorem hcovb2 : ∀ i j : Fin 3, G2.Adj i j → i ∈ ({0} : Finset (Fin 3)) ∨ j ∈ ({0} : Finset (Fin 3)) := by
  decide

theorem main2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  rw [hfun2]
  have h := H926.EdgeUpper.edge_upper 3 G2 {0} ⟨0, 1, by decide⟩ hcovb2
  rw [hcard2] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 3)).card = 1 := by decide
  rw [this] at h2
  omega

def ad3 (i j : Fin 3) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1)])

def G3 : SimpleGraph (Fin 3) where
  Adj i j := ad3 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst3 : DecidableRel G3.Adj := fun i j => inferInstanceAs (Decidable (ad3 i j = true))

theorem hfun3 : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) = (fun x : Fin 3 → Bool => decide (∃ i j : Fin 3, G3.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c : Bool, ((a && b) || (a && c) || (b && c)) = decide (∃ i j : Fin 3, G3.Adj i j ∧ (![a, b, c] : Fin 3 → Bool) i = true ∧ (![a, b, c] : Fin 3 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard3 : G3.edgeFinset.card = 3 := by
  decide +kernel

theorem hcovb3 : ∀ i j : Fin 3, G3.Adj i j → i ∈ ({0, 1} : Finset (Fin 3)) ∨ j ∈ ({0, 1} : Finset (Fin 3)) := by
  decide

theorem main3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  rw [hfun3]
  have h := H926.EdgeUpper.edge_upper 3 G3 {0, 1} ⟨0, 1, by decide⟩ hcovb3
  rw [hcard3] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  rw [this] at h2
  omega

def ad4 (i j : Fin 4) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(2,3),(3,2)])

def G4 : SimpleGraph (Fin 4) where
  Adj i j := ad4 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst4 : DecidableRel G4.Adj := fun i j => inferInstanceAs (Decidable (ad4 i j = true))

theorem hfun4 : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) = (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G4.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d : Bool, ((a && b) || (c && d)) = decide (∃ i j : Fin 4, G4.Adj i j ∧ (![a, b, c, d] : Fin 4 → Bool) i = true ∧ (![a, b, c, d] : Fin 4 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard4 : G4.edgeFinset.card = 2 := by
  decide +kernel

theorem hcovb4 : ∀ i j : Fin 4, G4.Adj i j → i ∈ ({0, 2} : Finset (Fin 4)) ∨ j ∈ ({0, 2} : Finset (Fin 4)) := by
  decide

theorem main4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  rw [hfun4]
  have h := H926.EdgeUpper.edge_upper 4 G4 {0, 2} ⟨0, 1, by decide⟩ hcovb4
  rw [hcard4] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
  rw [this] at h2
  omega

def ad5 (i j : Fin 4) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0)])

def G5 : SimpleGraph (Fin 4) where
  Adj i j := ad5 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst5 : DecidableRel G5.Adj := fun i j => inferInstanceAs (Decidable (ad5 i j = true))

theorem hfun5 : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) = (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G5.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d : Bool, ((a && b) || (a && c) || (a && d)) = decide (∃ i j : Fin 4, G5.Adj i j ∧ (![a, b, c, d] : Fin 4 → Bool) i = true ∧ (![a, b, c, d] : Fin 4 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard5 : G5.edgeFinset.card = 3 := by
  decide +kernel

theorem hcovb5 : ∀ i j : Fin 4, G5.Adj i j → i ∈ ({0} : Finset (Fin 4)) ∨ j ∈ ({0} : Finset (Fin 4)) := by
  decide

theorem main5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  rw [hfun5]
  have h := H926.EdgeUpper.edge_upper 4 G5 {0} ⟨0, 1, by decide⟩ hcovb5
  rw [hcard5] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 4)).card = 1 := by decide
  rw [this] at h2
  omega

def ad6 (i j : Fin 4) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1)])

def G6 : SimpleGraph (Fin 4) where
  Adj i j := ad6 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst6 : DecidableRel G6.Adj := fun i j => inferInstanceAs (Decidable (ad6 i j = true))

theorem hfun6 : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) = (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G6.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d : Bool, ((a && b) || (a && c) || (b && d)) = decide (∃ i j : Fin 4, G6.Adj i j ∧ (![a, b, c, d] : Fin 4 → Bool) i = true ∧ (![a, b, c, d] : Fin 4 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard6 : G6.edgeFinset.card = 3 := by
  decide +kernel

theorem hcovb6 : ∀ i j : Fin 4, G6.Adj i j → i ∈ ({0, 1} : Finset (Fin 4)) ∨ j ∈ ({0, 1} : Finset (Fin 4)) := by
  decide

theorem main6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  rw [hfun6]
  have h := H926.EdgeUpper.edge_upper 4 G6 {0, 1} ⟨0, 1, by decide⟩ hcovb6
  rw [hcard6] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  rw [this] at h2
  omega

def ad7 (i j : Fin 4) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1)])

def G7 : SimpleGraph (Fin 4) where
  Adj i j := ad7 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst7 : DecidableRel G7.Adj := fun i j => inferInstanceAs (Decidable (ad7 i j = true))

theorem hfun7 : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) = (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G7.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d : Bool, ((a && b) || (a && c) || (a && d) || (b && c)) = decide (∃ i j : Fin 4, G7.Adj i j ∧ (![a, b, c, d] : Fin 4 → Bool) i = true ∧ (![a, b, c, d] : Fin 4 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard7 : G7.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb7 : ∀ i j : Fin 4, G7.Adj i j → i ∈ ({0, 1} : Finset (Fin 4)) ∨ j ∈ ({0, 1} : Finset (Fin 4)) := by
  decide

theorem main7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  rw [hfun7]
  have h := H926.EdgeUpper.edge_upper 4 G7 {0, 1} ⟨0, 1, by decide⟩ hcovb7
  rw [hcard7] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  rw [this] at h2
  omega

def ad8 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(3,4),(4,3)])

def G8 : SimpleGraph (Fin 5) where
  Adj i j := ad8 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst8 : DecidableRel G8.Adj := fun i j => inferInstanceAs (Decidable (ad8 i j = true))

theorem hfun8 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G8.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (d && e)) = decide (∃ i j : Fin 5, G8.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard8 : G8.edgeFinset.card = 3 := by
  decide +kernel

theorem hcovb8 : ∀ i j : Fin 5, G8.Adj i j → i ∈ ({0, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 3} : Finset (Fin 5)) := by
  decide

theorem main8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  rw [hfun8]
  have h := H926.EdgeUpper.edge_upper 5 G8 {0, 3} ⟨0, 1, by decide⟩ hcovb8
  rw [hcard8] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 3} : Finset (Fin 5)).card = 2 := by decide
  rw [this] at h2
  omega

def ad9 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0)])

def G9 : SimpleGraph (Fin 5) where
  Adj i j := ad9 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst9 : DecidableRel G9.Adj := fun i j => inferInstanceAs (Decidable (ad9 i j = true))

theorem hfun9 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G9.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (a && e)) = decide (∃ i j : Fin 5, G9.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard9 : G9.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb9 : ∀ i j : Fin 5, G9.Adj i j → i ∈ ({0} : Finset (Fin 5)) ∨ j ∈ ({0} : Finset (Fin 5)) := by
  decide

theorem main9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  rw [hfun9]
  have h := H926.EdgeUpper.edge_upper 5 G9 {0} ⟨0, 1, by decide⟩ hcovb9
  rw [hcard9] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 5)).card = 1 := by decide
  rw [this] at h2
  omega

def ad10 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1)])

def G10 : SimpleGraph (Fin 5) where
  Adj i j := ad10 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst10 : DecidableRel G10.Adj := fun i j => inferInstanceAs (Decidable (ad10 i j = true))

theorem hfun10 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G10.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (b && e)) = decide (∃ i j : Fin 5, G10.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard10 : G10.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb10 : ∀ i j : Fin 5, G10.Adj i j → i ∈ ({0, 1} : Finset (Fin 5)) ∨ j ∈ ({0, 1} : Finset (Fin 5)) := by
  decide

theorem main10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  rw [hfun10]
  have h := H926.EdgeUpper.edge_upper 5 G10 {0, 1} ⟨0, 1, by decide⟩ hcovb10
  rw [hcard10] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [this] at h2
  omega

def ad11 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1),(3,4),(4,3)])

def G11 : SimpleGraph (Fin 5) where
  Adj i j := ad11 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst11 : DecidableRel G11.Adj := fun i j => inferInstanceAs (Decidable (ad11 i j = true))

theorem hfun11 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G11.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (b && c) || (d && e)) = decide (∃ i j : Fin 5, G11.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard11 : G11.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb11 : ∀ i j : Fin 5, G11.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 5)) := by
  decide

theorem main11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  rw [hfun11]
  have h := H926.EdgeUpper.edge_upper 5 G11 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb11
  rw [hcard11] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 5)).card = 3 := by decide
  rw [this] at h2
  omega

def ad12 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2)])

def G12 : SimpleGraph (Fin 5) where
  Adj i j := ad12 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst12 : DecidableRel G12.Adj := fun i j => inferInstanceAs (Decidable (ad12 i j = true))

theorem hfun12 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G12.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (b && d) || (c && e)) = decide (∃ i j : Fin 5, G12.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard12 : G12.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb12 : ∀ i j : Fin 5, G12.Adj i j → i ∈ ({1, 2} : Finset (Fin 5)) ∨ j ∈ ({1, 2} : Finset (Fin 5)) := by
  decide

theorem main12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  rw [hfun12]
  have h := H926.EdgeUpper.edge_upper 5 G12 {1, 2} ⟨0, 1, by decide⟩ hcovb12
  rw [hcard12] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({1, 2} : Finset (Fin 5)).card = 2 := by decide
  rw [this] at h2
  omega

def ad13 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1)])

def G13 : SimpleGraph (Fin 5) where
  Adj i j := ad13 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst13 : DecidableRel G13.Adj := fun i j => inferInstanceAs (Decidable (ad13 i j = true))

theorem hfun13 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G13.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c)) = decide (∃ i j : Fin 5, G13.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard13 : G13.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb13 : ∀ i j : Fin 5, G13.Adj i j → i ∈ ({0, 1} : Finset (Fin 5)) ∨ j ∈ ({0, 1} : Finset (Fin 5)) := by
  decide

theorem main13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  rw [hfun13]
  have h := H926.EdgeUpper.edge_upper 5 G13 {0, 1} ⟨0, 1, by decide⟩ hcovb13
  rw [hcard13] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [this] at h2
  omega

def ad14 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1)])

def G14 : SimpleGraph (Fin 5) where
  Adj i j := ad14 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst14 : DecidableRel G14.Adj := fun i j => inferInstanceAs (Decidable (ad14 i j = true))

theorem hfun14 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G14.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e)) = decide (∃ i j : Fin 5, G14.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard14 : G14.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb14 : ∀ i j : Fin 5, G14.Adj i j → i ∈ ({0, 1} : Finset (Fin 5)) ∨ j ∈ ({0, 1} : Finset (Fin 5)) := by
  decide

theorem main14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  rw [hfun14]
  have h := H926.EdgeUpper.edge_upper 5 G14 {0, 1} ⟨0, 1, by decide⟩ hcovb14
  rw [hcard14] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [this] at h2
  omega

def ad15 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(3,4),(4,3)])

def G15 : SimpleGraph (Fin 5) where
  Adj i j := ad15 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst15 : DecidableRel G15.Adj := fun i j => inferInstanceAs (Decidable (ad15 i j = true))

theorem hfun15 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G15.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (d && e)) = decide (∃ i j : Fin 5, G15.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard15 : G15.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb15 : ∀ i j : Fin 5, G15.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 5)) := by
  decide

theorem main15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  rw [hfun15]
  have h := H926.EdgeUpper.edge_upper 5 G15 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb15
  rw [hcard15] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 5)).card = 3 := by decide
  rw [this] at h2
  omega

def ad16 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,4),(4,3)])

def G16 : SimpleGraph (Fin 5) where
  Adj i j := ad16 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst16 : DecidableRel G16.Adj := fun i j => inferInstanceAs (Decidable (ad16 i j = true))

theorem hfun16 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G16.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && e)) = decide (∃ i j : Fin 5, G16.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard16 : G16.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb16 : ∀ i j : Fin 5, G16.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 5)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 5)) := by
  decide

theorem main16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  rw [hfun16]
  have h := H926.EdgeUpper.edge_upper 5 G16 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb16
  rw [hcard16] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 5)).card = 3 := by decide
  rw [this] at h2
  omega

def ad17 (i j : Fin 5) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(3,4),(4,3)])

def G17 : SimpleGraph (Fin 5) where
  Adj i j := ad17 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst17 : DecidableRel G17.Adj := fun i j => inferInstanceAs (Decidable (ad17 i j = true))

theorem hfun17 : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G17.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && e)) = decide (∃ i j : Fin 5, G17.Adj i j ∧ (![a, b, c, d, e] : Fin 5 → Bool) i = true ∧ (![a, b, c, d, e] : Fin 5 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard17 : G17.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb17 : ∀ i j : Fin 5, G17.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 5)) := by
  decide

theorem main17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  rw [hfun17]
  have h := H926.EdgeUpper.edge_upper 5 G17 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb17
  rw [hcard17] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 5)).card = 3 := by decide
  rw [this] at h2
  omega

def ad18 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)])

def G18 : SimpleGraph (Fin 6) where
  Adj i j := ad18 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst18 : DecidableRel G18.Adj := fun i j => inferInstanceAs (Decidable (ad18 i j = true))

theorem hfun18 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G18.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (c && d) || (e && f)) = decide (∃ i j : Fin 6, G18.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard18 : G18.edgeFinset.card = 3 := by
  decide +kernel

theorem hcovb18 : ∀ i j : Fin 6, G18.Adj i j → i ∈ ({0, 2, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 2, 4} : Finset (Fin 6)) := by
  decide

theorem main18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  rw [hfun18]
  have h := H926.EdgeUpper.edge_upper 6 G18 {0, 2, 4} ⟨0, 1, by decide⟩ hcovb18
  rw [hcard18] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 2, 4} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad19 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4)])

def G19 : SimpleGraph (Fin 6) where
  Adj i j := ad19 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst19 : DecidableRel G19.Adj := fun i j => inferInstanceAs (Decidable (ad19 i j = true))

theorem hfun19 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G19.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (e && f)) = decide (∃ i j : Fin 6, G19.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard19 : G19.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb19 : ∀ i j : Fin 6, G19.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  decide

theorem main19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  rw [hfun19]
  have h := H926.EdgeUpper.edge_upper 6 G19 {0, 4} ⟨0, 1, by decide⟩ hcovb19
  rw [hcard19] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad20 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(4,5),(5,4)])

def G20 : SimpleGraph (Fin 6) where
  Adj i j := ad20 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst20 : DecidableRel G20.Adj := fun i j => inferInstanceAs (Decidable (ad20 i j = true))

theorem hfun20 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G20.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (b && d) || (e && f)) = decide (∃ i j : Fin 6, G20.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard20 : G20.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb20 : ∀ i j : Fin 6, G20.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 6)) := by
  decide

theorem main20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  rw [hfun20]
  have h := H926.EdgeUpper.edge_upper 6 G20 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb20
  rw [hcard20] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad21 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(3,4),(4,3),(3,5),(5,3)])

def G21 : SimpleGraph (Fin 6) where
  Adj i j := ad21 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst21 : DecidableRel G21.Adj := fun i j => inferInstanceAs (Decidable (ad21 i j = true))

theorem hfun21 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G21.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (d && e) || (d && f)) = decide (∃ i j : Fin 6, G21.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard21 : G21.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb21 : ∀ i j : Fin 6, G21.Adj i j → i ∈ ({0, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 3} : Finset (Fin 6)) := by
  decide

theorem main21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  rw [hfun21]
  have h := H926.EdgeUpper.edge_upper 6 G21 {0, 3} ⟨0, 1, by decide⟩ hcovb21
  rw [hcard21] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 3} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad22 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0)])

def G22 : SimpleGraph (Fin 6) where
  Adj i j := ad22 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst22 : DecidableRel G22.Adj := fun i j => inferInstanceAs (Decidable (ad22 i j = true))

theorem hfun22 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G22.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f)) = decide (∃ i j : Fin 6, G22.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard22 : G22.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb22 : ∀ i j : Fin 6, G22.Adj i j → i ∈ ({0} : Finset (Fin 6)) ∨ j ∈ ({0} : Finset (Fin 6)) := by
  decide

theorem main22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  rw [hfun22]
  have h := H926.EdgeUpper.edge_upper 6 G22 {0} ⟨0, 1, by decide⟩ hcovb22
  rw [hcard22] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 6)).card = 1 := by decide
  rw [this] at h2
  omega

def ad23 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1)])

def G23 : SimpleGraph (Fin 6) where
  Adj i j := ad23 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst23 : DecidableRel G23.Adj := fun i j => inferInstanceAs (Decidable (ad23 i j = true))

theorem hfun23 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G23.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f)) = decide (∃ i j : Fin 6, G23.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard23 : G23.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb23 : ∀ i j : Fin 6, G23.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem main23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  rw [hfun23]
  have h := H926.EdgeUpper.edge_upper 6 G23 {0, 1} ⟨0, 1, by decide⟩ hcovb23
  rw [hcard23] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad24 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(4,5),(5,4)])

def G24 : SimpleGraph (Fin 6) where
  Adj i j := ad24 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst24 : DecidableRel G24.Adj := fun i j => inferInstanceAs (Decidable (ad24 i j = true))

theorem hfun24 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G24.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (e && f)) = decide (∃ i j : Fin 6, G24.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard24 : G24.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb24 : ∀ i j : Fin 6, G24.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 6)) := by
  decide

theorem main24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  rw [hfun24]
  have h := H926.EdgeUpper.edge_upper 6 G24 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb24
  rw [hcard24] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad25 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(1,5),(5,1)])

def G25 : SimpleGraph (Fin 6) where
  Adj i j := ad25 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst25 : DecidableRel G25.Adj := fun i j => inferInstanceAs (Decidable (ad25 i j = true))

theorem hfun25 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G25.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (b && f)) = decide (∃ i j : Fin 6, G25.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard25 : G25.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb25 : ∀ i j : Fin 6, G25.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem main25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  rw [hfun25]
  have h := H926.EdgeUpper.edge_upper 6 G25 {0, 1} ⟨0, 1, by decide⟩ hcovb25
  rw [hcard25] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad26 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2)])

def G26 : SimpleGraph (Fin 6) where
  Adj i j := ad26 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst26 : DecidableRel G26.Adj := fun i j => inferInstanceAs (Decidable (ad26 i j = true))

theorem hfun26 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G26.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f)) = decide (∃ i j : Fin 6, G26.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard26 : G26.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb26 : ∀ i j : Fin 6, G26.Adj i j → i ∈ ({0, 1, 2} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 2} : Finset (Fin 6)) := by
  decide

theorem main26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  rw [hfun26]
  have h := H926.EdgeUpper.edge_upper 6 G26 {0, 1, 2} ⟨0, 1, by decide⟩ hcovb26
  rw [hcard26] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad27 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(4,5),(5,4)])

def G27 : SimpleGraph (Fin 6) where
  Adj i j := ad27 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst27 : DecidableRel G27.Adj := fun i j => inferInstanceAs (Decidable (ad27 i j = true))

theorem hfun27 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G27.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (e && f)) = decide (∃ i j : Fin 6, G27.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard27 : G27.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb27 : ∀ i j : Fin 6, G27.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  decide

theorem main27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  rw [hfun27]
  have h := H926.EdgeUpper.edge_upper 6 G27 {0, 4} ⟨0, 1, by decide⟩ hcovb27
  rw [hcard27] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad28 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1),(3,4),(4,3),(3,5),(5,3)])

def G28 : SimpleGraph (Fin 6) where
  Adj i j := ad28 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst28 : DecidableRel G28.Adj := fun i j => inferInstanceAs (Decidable (ad28 i j = true))

theorem hfun28 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G28.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (b && c) || (d && e) || (d && f)) = decide (∃ i j : Fin 6, G28.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard28 : G28.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb28 : ∀ i j : Fin 6, G28.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  rw [hfun28]
  have h := H926.EdgeUpper.edge_upper 6 G28 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb28
  rw [hcard28] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad29 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,5),(5,3)])

def G29 : SimpleGraph (Fin 6) where
  Adj i j := ad29 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst29 : DecidableRel G29.Adj := fun i j => inferInstanceAs (Decidable (ad29 i j = true))

theorem hfun29 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G29.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && f)) = decide (∃ i j : Fin 6, G29.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard29 : G29.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb29 : ∀ i j : Fin 6, G29.Adj i j → i ∈ ({0, 2, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 2, 3} : Finset (Fin 6)) := by
  decide

theorem main29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  rw [hfun29]
  have h := H926.EdgeUpper.edge_upper 6 G29 {0, 2, 3} ⟨0, 1, by decide⟩ hcovb29
  rw [hcard29] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 2, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad30 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(1,2),(2,1)])

def G30 : SimpleGraph (Fin 6) where
  Adj i j := ad30 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst30 : DecidableRel G30.Adj := fun i j => inferInstanceAs (Decidable (ad30 i j = true))

theorem hfun30 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G30.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c)) = decide (∃ i j : Fin 6, G30.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard30 : G30.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb30 : ∀ i j : Fin 6, G30.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem main30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  rw [hfun30]
  have h := H926.EdgeUpper.edge_upper 6 G30 {0, 1} ⟨0, 1, by decide⟩ hcovb30
  rw [hcard30] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad31 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1)])

def G31 : SimpleGraph (Fin 6) where
  Adj i j := ad31 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst31 : DecidableRel G31.Adj := fun i j => inferInstanceAs (Decidable (ad31 i j = true))

theorem hfun31 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G31.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f)) = decide (∃ i j : Fin 6, G31.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard31 : G31.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb31 : ∀ i j : Fin 6, G31.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem main31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  rw [hfun31]
  have h := H926.EdgeUpper.edge_upper 6 G31 {0, 1} ⟨0, 1, by decide⟩ hcovb31
  rw [hcard31] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 6)).card = 2 := by decide
  rw [this] at h2
  omega

def ad32 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(3,5),(5,3)])

def G32 : SimpleGraph (Fin 6) where
  Adj i j := ad32 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst32 : DecidableRel G32.Adj := fun i j => inferInstanceAs (Decidable (ad32 i j = true))

theorem hfun32 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G32.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f)) = decide (∃ i j : Fin 6, G32.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard32 : G32.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb32 : ∀ i j : Fin 6, G32.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  rw [hfun32]
  have h := H926.EdgeUpper.edge_upper 6 G32 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb32
  rw [hcard32] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad33 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(2,5),(5,2)])

def G33 : SimpleGraph (Fin 6) where
  Adj i j := ad33 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst33 : DecidableRel G33.Adj := fun i j => inferInstanceAs (Decidable (ad33 i j = true))

theorem hfun33 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G33.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f)) = decide (∃ i j : Fin 6, G33.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard33 : G33.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb33 : ∀ i j : Fin 6, G33.Adj i j → i ∈ ({0, 1, 2} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 2} : Finset (Fin 6)) := by
  decide

theorem main33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  rw [hfun33]
  have h := H926.EdgeUpper.edge_upper 6 G33 {0, 1, 2} ⟨0, 1, by decide⟩ hcovb33
  rw [hcard33] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad34 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(3,5),(5,3)])

def G34 : SimpleGraph (Fin 6) where
  Adj i j := ad34 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst34 : DecidableRel G34.Adj := fun i j => inferInstanceAs (Decidable (ad34 i j = true))

theorem hfun34 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G34.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f)) = decide (∃ i j : Fin 6, G34.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard34 : G34.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb34 : ∀ i j : Fin 6, G34.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  rw [hfun34]
  have h := H926.EdgeUpper.edge_upper 6 G34 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb34
  rw [hcard34] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad35 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(3,4),(4,3),(3,5),(5,3)])

def G35 : SimpleGraph (Fin 6) where
  Adj i j := ad35 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst35 : DecidableRel G35.Adj := fun i j => inferInstanceAs (Decidable (ad35 i j = true))

theorem hfun35 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G35.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (d && f)) = decide (∃ i j : Fin 6, G35.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard35 : G35.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb35 : ∀ i j : Fin 6, G35.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  rw [hfun35]
  have h := H926.EdgeUpper.edge_upper 6 G35 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb35
  rw [hcard35] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad36 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(3,4),(4,3),(4,5),(5,4)])

def G36 : SimpleGraph (Fin 6) where
  Adj i j := ad36 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst36 : DecidableRel G36.Adj := fun i j => inferInstanceAs (Decidable (ad36 i j = true))

theorem hfun36 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G36.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f)) = decide (∃ i j : Fin 6, G36.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard36 : G36.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb36 : ∀ i j : Fin 6, G36.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 6)) := by
  decide

theorem main36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  rw [hfun36]
  have h := H926.EdgeUpper.edge_upper 6 G36 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb36
  rw [hcard36] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad37 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(4,5),(5,4)])

def G37 : SimpleGraph (Fin 6) where
  Adj i j := ad37 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst37 : DecidableRel G37.Adj := fun i j => inferInstanceAs (Decidable (ad37 i j = true))

theorem hfun37 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G37.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f)) = decide (∃ i j : Fin 6, G37.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard37 : G37.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb37 : ∀ i j : Fin 6, G37.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 6)) := by
  decide

theorem main37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  rw [hfun37]
  have h := H926.EdgeUpper.edge_upper 6 G37 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb37
  rw [hcard37] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad38 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1),(3,4),(4,3),(3,5),(5,3),(4,5),(5,4)])

def G38 : SimpleGraph (Fin 6) where
  Adj i j := ad38 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst38 : DecidableRel G38.Adj := fun i j => inferInstanceAs (Decidable (ad38 i j = true))

theorem hfun38 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G38.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && f)) = decide (∃ i j : Fin 6, G38.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard38 : G38.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb38 : ∀ i j : Fin 6, G38.Adj i j → i ∈ ({0, 1, 3, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3, 4} : Finset (Fin 6)) := by
  decide

theorem main38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  rw [hfun38]
  have h := H926.EdgeUpper.edge_upper 6 G38 {0, 1, 3, 4} ⟨0, 1, by decide⟩ hcovb38
  rw [hcard38] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3, 4} : Finset (Fin 6)).card = 4 := by decide
  rw [this] at h2
  omega

def ad39 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,5),(5,3),(4,5),(5,4)])

def G39 : SimpleGraph (Fin 6) where
  Adj i j := ad39 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst39 : DecidableRel G39.Adj := fun i j => inferInstanceAs (Decidable (ad39 i j = true))

theorem hfun39 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G39.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && f)) = decide (∃ i j : Fin 6, G39.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard39 : G39.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb39 : ∀ i j : Fin 6, G39.Adj i j → i ∈ ({0, 3, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 3, 4} : Finset (Fin 6)) := by
  decide

theorem main39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  rw [hfun39]
  have h := H926.EdgeUpper.edge_upper 6 G39 {0, 3, 4} ⟨0, 1, by decide⟩ hcovb39
  rw [hcard39] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 3, 4} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad40 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(1,2),(2,1),(3,4),(4,3)])

def G40 : SimpleGraph (Fin 6) where
  Adj i j := ad40 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst40 : DecidableRel G40.Adj := fun i j => inferInstanceAs (Decidable (ad40 i j = true))

theorem hfun40 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G40.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && e)) = decide (∃ i j : Fin 6, G40.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard40 : G40.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb40 : ∀ i j : Fin 6, G40.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  rw [hfun40]
  have h := H926.EdgeUpper.edge_upper 6 G40 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb40
  rw [hcard40] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad41 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1),(3,4),(4,3)])

def G41 : SimpleGraph (Fin 6) where
  Adj i j := ad41 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst41 : DecidableRel G41.Adj := fun i j => inferInstanceAs (Decidable (ad41 i j = true))

theorem hfun41 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G41.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e)) = decide (∃ i j : Fin 6, G41.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard41 : G41.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb41 : ∀ i j : Fin 6, G41.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 6)) := by
  decide

theorem main41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  rw [hfun41]
  have h := H926.EdgeUpper.edge_upper 6 G41 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb41
  rw [hcard41] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad42 (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(3,5),(5,3),(4,5),(5,4)])

def G42 : SimpleGraph (Fin 6) where
  Adj i j := ad42 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst42 : DecidableRel G42.Adj := fun i j => inferInstanceAs (Decidable (ad42 i j = true))

theorem hfun42 : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G42.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && f)) = decide (∃ i j : Fin 6, G42.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard42 : G42.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb42 : ∀ i j : Fin 6, G42.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 6)) := by
  decide

theorem main42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  rw [hfun42]
  have h := H926.EdgeUpper.edge_upper 6 G42 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb42
  rw [hcard42] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 6)).card = 3 := by decide
  rw [this] at h2
  omega

def ad43 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(3,4),(4,3),(5,6),(6,5)])

def G43 : SimpleGraph (Fin 7) where
  Adj i j := ad43 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst43 : DecidableRel G43.Adj := fun i j => inferInstanceAs (Decidable (ad43 i j = true))

theorem hfun43 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G43.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (d && e) || (f && g)) = decide (∃ i j : Fin 7, G43.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard43 : G43.edgeFinset.card = 4 := by
  decide +kernel

theorem hcovb43 : ∀ i j : Fin 7, G43.Adj i j → i ∈ ({0, 3, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 3, 5} : Finset (Fin 7)) := by
  decide

theorem main43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  rw [hfun43]
  have h := H926.EdgeUpper.edge_upper 7 G43 {0, 3, 5} ⟨0, 1, by decide⟩ hcovb43
  rw [hcard43] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 3, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad44 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(5,6),(6,5)])

def G44 : SimpleGraph (Fin 7) where
  Adj i j := ad44 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst44 : DecidableRel G44.Adj := fun i j => inferInstanceAs (Decidable (ad44 i j = true))

theorem hfun44 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G44.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (f && g)) = decide (∃ i j : Fin 7, G44.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard44 : G44.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb44 : ∀ i j : Fin 7, G44.Adj i j → i ∈ ({0, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 5} : Finset (Fin 7)) := by
  decide

theorem main44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  rw [hfun44]
  have h := H926.EdgeUpper.edge_upper 7 G44 {0, 5} ⟨0, 1, by decide⟩ hcovb44
  rw [hcard44] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 5} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad45 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(5,6),(6,5)])

def G45 : SimpleGraph (Fin 7) where
  Adj i j := ad45 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst45 : DecidableRel G45.Adj := fun i j => inferInstanceAs (Decidable (ad45 i j = true))

theorem hfun45 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G45.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (f && g)) = decide (∃ i j : Fin 7, G45.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard45 : G45.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb45 : ∀ i j : Fin 7, G45.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  rw [hfun45]
  have h := H926.EdgeUpper.edge_upper 7 G45 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb45
  rw [hcard45] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad46 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4),(4,6),(6,4)])

def G46 : SimpleGraph (Fin 7) where
  Adj i j := ad46 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst46 : DecidableRel G46.Adj := fun i j => inferInstanceAs (Decidable (ad46 i j = true))

theorem hfun46 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G46.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G46.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard46 : G46.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb46 : ∀ i j : Fin 7, G46.Adj i j → i ∈ ({0, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 4} : Finset (Fin 7)) := by
  decide

theorem main46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  rw [hfun46]
  have h := H926.EdgeUpper.edge_upper 7 G46 {0, 4} ⟨0, 1, by decide⟩ hcovb46
  rw [hcard46] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad47 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1),(3,4),(4,3),(5,6),(6,5)])

def G47 : SimpleGraph (Fin 7) where
  Adj i j := ad47 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst47 : DecidableRel G47.Adj := fun i j => inferInstanceAs (Decidable (ad47 i j = true))

theorem hfun47 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G47.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && c) || (d && e) || (f && g)) = decide (∃ i j : Fin 7, G47.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard47 : G47.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb47 : ∀ i j : Fin 7, G47.Adj i j → i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3, 5} : Finset (Fin 7)) := by
  decide

theorem main47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  rw [hfun47]
  have h := H926.EdgeUpper.edge_upper 7 G47 {0, 1, 3, 5} ⟨0, 1, by decide⟩ hcovb47
  rw [hcard47] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3, 5} : Finset (Fin 7)).card = 4 := by decide
  rw [this] at h2
  omega

def ad48 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(5,6),(6,5)])

def G48 : SimpleGraph (Fin 7) where
  Adj i j := ad48 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst48 : DecidableRel G48.Adj := fun i j => inferInstanceAs (Decidable (ad48 i j = true))

theorem hfun48 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G48.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (f && g)) = decide (∃ i j : Fin 7, G48.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard48 : G48.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb48 : ∀ i j : Fin 7, G48.Adj i j → i ∈ ({1, 2, 5} : Finset (Fin 7)) ∨ j ∈ ({1, 2, 5} : Finset (Fin 7)) := by
  decide

theorem main48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  rw [hfun48]
  have h := H926.EdgeUpper.edge_upper 7 G48 {1, 2, 5} ⟨0, 1, by decide⟩ hcovb48
  rw [hcard48] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({1, 2, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad49 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(4,5),(5,4),(4,6),(6,4)])

def G49 : SimpleGraph (Fin 7) where
  Adj i j := ad49 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst49 : DecidableRel G49.Adj := fun i j => inferInstanceAs (Decidable (ad49 i j = true))

theorem hfun49 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G49.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && d) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G49.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard49 : G49.edgeFinset.card = 5 := by
  decide +kernel

theorem hcovb49 : ∀ i j : Fin 7, G49.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 7)) := by
  decide

theorem main49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  rw [hfun49]
  have h := H926.EdgeUpper.edge_upper 7 G49 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb49
  rw [hcard49] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad50 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(0,6),(6,0)])

def G50 : SimpleGraph (Fin 7) where
  Adj i j := ad50 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst50 : DecidableRel G50.Adj := fun i j => inferInstanceAs (Decidable (ad50 i j = true))

theorem hfun50 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G50.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g)) = decide (∃ i j : Fin 7, G50.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard50 : G50.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb50 : ∀ i j : Fin 7, G50.Adj i j → i ∈ ({0} : Finset (Fin 7)) ∨ j ∈ ({0} : Finset (Fin 7)) := by
  decide

theorem main50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  rw [hfun50]
  have h := H926.EdgeUpper.edge_upper 7 G50 {0} ⟨0, 1, by decide⟩ hcovb50
  rw [hcard50] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0} : Finset (Fin 7)).card = 1 := by decide
  rw [this] at h2
  omega

def ad51 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(1,6),(6,1)])

def G51 : SimpleGraph (Fin 7) where
  Adj i j := ad51 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst51 : DecidableRel G51.Adj := fun i j => inferInstanceAs (Decidable (ad51 i j = true))

theorem hfun51 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G51.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && g)) = decide (∃ i j : Fin 7, G51.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard51 : G51.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb51 : ∀ i j : Fin 7, G51.Adj i j → i ∈ ({0, 1} : Finset (Fin 7)) ∨ j ∈ ({0, 1} : Finset (Fin 7)) := by
  decide

theorem main51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  rw [hfun51]
  have h := H926.EdgeUpper.edge_upper 7 G51 {0, 1} ⟨0, 1, by decide⟩ hcovb51
  rw [hcard51] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad52 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(5,6),(6,5)])

def G52 : SimpleGraph (Fin 7) where
  Adj i j := ad52 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst52 : DecidableRel G52.Adj := fun i j => inferInstanceAs (Decidable (ad52 i j = true))

theorem hfun52 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G52.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (f && g)) = decide (∃ i j : Fin 7, G52.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard52 : G52.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb52 : ∀ i j : Fin 7, G52.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  rw [hfun52]
  have h := H926.EdgeUpper.edge_upper 7 G52 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb52
  rw [hcard52] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad53 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(1,6),(6,1)])

def G53 : SimpleGraph (Fin 7) where
  Adj i j := ad53 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst53 : DecidableRel G53.Adj := fun i j => inferInstanceAs (Decidable (ad53 i j = true))

theorem hfun53 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G53.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g)) = decide (∃ i j : Fin 7, G53.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard53 : G53.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb53 : ∀ i j : Fin 7, G53.Adj i j → i ∈ ({0, 1} : Finset (Fin 7)) ∨ j ∈ ({0, 1} : Finset (Fin 7)) := by
  decide

theorem main53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  rw [hfun53]
  have h := H926.EdgeUpper.edge_upper 7 G53 {0, 1} ⟨0, 1, by decide⟩ hcovb53
  rw [hcard53] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad54 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(2,6),(6,2)])

def G54 : SimpleGraph (Fin 7) where
  Adj i j := ad54 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst54 : DecidableRel G54.Adj := fun i j => inferInstanceAs (Decidable (ad54 i j = true))

theorem hfun54 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G54.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g)) = decide (∃ i j : Fin 7, G54.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard54 : G54.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb54 : ∀ i j : Fin 7, G54.Adj i j → i ∈ ({0, 1, 2} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 2} : Finset (Fin 7)) := by
  decide

theorem main54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  rw [hfun54]
  have h := H926.EdgeUpper.edge_upper 7 G54 {0, 1, 2} ⟨0, 1, by decide⟩ hcovb54
  rw [hcard54] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 2} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad55 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(5,6),(6,5)])

def G55 : SimpleGraph (Fin 7) where
  Adj i j := ad55 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst55 : DecidableRel G55.Adj := fun i j => inferInstanceAs (Decidable (ad55 i j = true))

theorem hfun55 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G55.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g)) = decide (∃ i j : Fin 7, G55.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard55 : G55.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb55 : ∀ i j : Fin 7, G55.Adj i j → i ∈ ({0, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 5} : Finset (Fin 7)) := by
  decide

theorem main55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  rw [hfun55]
  have h := H926.EdgeUpper.edge_upper 7 G55 {0, 5} ⟨0, 1, by decide⟩ hcovb55
  rw [hcard55] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 5} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad56 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(5,6),(6,5)])

def G56 : SimpleGraph (Fin 7) where
  Adj i j := ad56 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst56 : DecidableRel G56.Adj := fun i j => inferInstanceAs (Decidable (ad56 i j = true))

theorem hfun56 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G56.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (f && g)) = decide (∃ i j : Fin 7, G56.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard56 : G56.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb56 : ∀ i j : Fin 7, G56.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  rw [hfun56]
  have h := H926.EdgeUpper.edge_upper 7 G56 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb56
  rw [hcard56] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad57 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(3,4),(4,3),(5,6),(6,5)])

def G57 : SimpleGraph (Fin 7) where
  Adj i j := ad57 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst57 : DecidableRel G57.Adj := fun i j => inferInstanceAs (Decidable (ad57 i j = true))

theorem hfun57 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G57.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (f && g)) = decide (∃ i j : Fin 7, G57.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard57 : G57.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb57 : ∀ i j : Fin 7, G57.Adj i j → i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3, 5} : Finset (Fin 7)) := by
  decide

theorem main57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  rw [hfun57]
  have h := H926.EdgeUpper.edge_upper 7 G57 {0, 1, 3, 5} ⟨0, 1, by decide⟩ hcovb57
  rw [hcard57] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3, 5} : Finset (Fin 7)).card = 4 := by decide
  rw [this] at h2
  omega

def ad58 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(4,5),(5,4),(4,6),(6,4)])

def G58 : SimpleGraph (Fin 7) where
  Adj i j := ad58 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst58 : DecidableRel G58.Adj := fun i j => inferInstanceAs (Decidable (ad58 i j = true))

theorem hfun58 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G58.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G58.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard58 : G58.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb58 : ∀ i j : Fin 7, G58.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 7)) := by
  decide

theorem main58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  rw [hfun58]
  have h := H926.EdgeUpper.edge_upper 7 G58 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb58
  rw [hcard58] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad59 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(1,5),(5,1),(2,6),(6,2)])

def G59 : SimpleGraph (Fin 7) where
  Adj i j := ad59 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst59 : DecidableRel G59.Adj := fun i j => inferInstanceAs (Decidable (ad59 i j = true))

theorem hfun59 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G59.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g)) = decide (∃ i j : Fin 7, G59.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard59 : G59.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb59 : ∀ i j : Fin 7, G59.Adj i j → i ∈ ({0, 1, 2} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 2} : Finset (Fin 7)) := by
  decide

theorem main59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  rw [hfun59]
  have h := H926.EdgeUpper.edge_upper 7 G59 {0, 1, 2} ⟨0, 1, by decide⟩ hcovb59
  rw [hcard59] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 2} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad60 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(3,6),(6,3)])

def G60 : SimpleGraph (Fin 7) where
  Adj i j := ad60 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst60 : DecidableRel G60.Adj := fun i j => inferInstanceAs (Decidable (ad60 i j = true))

theorem hfun60 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G60.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g)) = decide (∃ i j : Fin 7, G60.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard60 : G60.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb60 : ∀ i j : Fin 7, G60.Adj i j → i ∈ ({1, 2, 3} : Finset (Fin 7)) ∨ j ∈ ({1, 2, 3} : Finset (Fin 7)) := by
  decide

theorem main60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  rw [hfun60]
  have h := H926.EdgeUpper.edge_upper 7 G60 {1, 2, 3} ⟨0, 1, by decide⟩ hcovb60
  rw [hcard60] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({1, 2, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad61 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(4,6),(6,4)])

def G61 : SimpleGraph (Fin 7) where
  Adj i j := ad61 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst61 : DecidableRel G61.Adj := fun i j => inferInstanceAs (Decidable (ad61 i j = true))

theorem hfun61 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G61.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g)) = decide (∃ i j : Fin 7, G61.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard61 : G61.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb61 : ∀ i j : Fin 7, G61.Adj i j → i ∈ ({0, 2, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 2, 4} : Finset (Fin 7)) := by
  decide

theorem main61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  rw [hfun61]
  have h := H926.EdgeUpper.edge_upper 7 G61 {0, 2, 4} ⟨0, 1, by decide⟩ hcovb61
  rw [hcard61] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 2, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad62 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(4,5),(5,4),(4,6),(6,4)])

def G62 : SimpleGraph (Fin 7) where
  Adj i j := ad62 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst62 : DecidableRel G62.Adj := fun i j => inferInstanceAs (Decidable (ad62 i j = true))

theorem hfun62 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G62.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G62.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard62 : G62.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb62 : ∀ i j : Fin 7, G62.Adj i j → i ∈ ({0, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 4} : Finset (Fin 7)) := by
  decide

theorem main62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  rw [hfun62]
  have h := H926.EdgeUpper.edge_upper 7 G62 {0, 4} ⟨0, 1, by decide⟩ hcovb62
  rw [hcard62] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad63 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(4,5),(5,4),(5,6),(6,5)])

def G63 : SimpleGraph (Fin 7) where
  Adj i j := ad63 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst63 : DecidableRel G63.Adj := fun i j => inferInstanceAs (Decidable (ad63 i j = true))

theorem hfun63 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G63.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (f && g)) = decide (∃ i j : Fin 7, G63.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard63 : G63.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb63 : ∀ i j : Fin 7, G63.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  rw [hfun63]
  have h := H926.EdgeUpper.edge_upper 7 G63 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb63
  rw [hcard63] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad64 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4),(4,6),(6,4),(5,6),(6,5)])

def G64 : SimpleGraph (Fin 7) where
  Adj i j := ad64 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst64 : DecidableRel G64.Adj := fun i j => inferInstanceAs (Decidable (ad64 i j = true))

theorem hfun64 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G64.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (e && f) || (e && g) || (f && g)) = decide (∃ i j : Fin 7, G64.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard64 : G64.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb64 : ∀ i j : Fin 7, G64.Adj i j → i ∈ ({0, 4, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 4, 5} : Finset (Fin 7)) := by
  decide

theorem main64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  rw [hfun64]
  have h := H926.EdgeUpper.edge_upper 7 G64 {0, 4, 5} ⟨0, 1, by decide⟩ hcovb64
  rw [hcard64] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad65 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1),(3,4),(4,3),(3,5),(5,3),(4,6),(6,4)])

def G65 : SimpleGraph (Fin 7) where
  Adj i j := ad65 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst65 : DecidableRel G65.Adj := fun i j => inferInstanceAs (Decidable (ad65 i j = true))

theorem hfun65 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G65.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && g)) = decide (∃ i j : Fin 7, G65.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard65 : G65.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb65 : ∀ i j : Fin 7, G65.Adj i j → i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)) := by
  decide

theorem main65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  rw [hfun65]
  have h := H926.EdgeUpper.edge_upper 7 G65 {0, 1, 3, 4} ⟨0, 1, by decide⟩ hcovb65
  rw [hcard65] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3, 4} : Finset (Fin 7)).card = 4 := by decide
  rw [this] at h2
  omega

def ad66 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,4),(4,3),(5,6),(6,5)])

def G66 : SimpleGraph (Fin 7) where
  Adj i j := ad66 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst66 : DecidableRel G66.Adj := fun i j => inferInstanceAs (Decidable (ad66 i j = true))

theorem hfun66 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G66.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && e) || (f && g)) = decide (∃ i j : Fin 7, G66.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard66 : G66.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb66 : ∀ i j : Fin 7, G66.Adj i j → i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 4, 5} : Finset (Fin 7)) := by
  decide

theorem main66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  rw [hfun66]
  have h := H926.EdgeUpper.edge_upper 7 G66 {0, 1, 4, 5} ⟨0, 1, by decide⟩ hcovb66
  rw [hcard66] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4, 5} : Finset (Fin 7)).card = 4 := by decide
  rw [this] at h2
  omega

def ad67 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,5),(5,3),(4,6),(6,4)])

def G67 : SimpleGraph (Fin 7) where
  Adj i j := ad67 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst67 : DecidableRel G67.Adj := fun i j => inferInstanceAs (Decidable (ad67 i j = true))

theorem hfun67 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G67.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && g)) = decide (∃ i j : Fin 7, G67.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard67 : G67.edgeFinset.card = 6 := by
  decide +kernel

theorem hcovb67 : ∀ i j : Fin 7, G67.Adj i j → i ∈ ({0, 3, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 3, 4} : Finset (Fin 7)) := by
  decide

theorem main67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  rw [hfun67]
  have h := H926.EdgeUpper.edge_upper 7 G67 {0, 3, 4} ⟨0, 1, by decide⟩ hcovb67
  rw [hcard67] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 3, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad68 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(0,6),(6,0),(1,2),(2,1)])

def G68 : SimpleGraph (Fin 7) where
  Adj i j := ad68 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst68 : DecidableRel G68.Adj := fun i j => inferInstanceAs (Decidable (ad68 i j = true))

theorem hfun68 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G68.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g) || (b && c)) = decide (∃ i j : Fin 7, G68.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard68 : G68.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb68 : ∀ i j : Fin 7, G68.Adj i j → i ∈ ({0, 1} : Finset (Fin 7)) ∨ j ∈ ({0, 1} : Finset (Fin 7)) := by
  decide

theorem main68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  rw [hfun68]
  have h := H926.EdgeUpper.edge_upper 7 G68 {0, 1} ⟨0, 1, by decide⟩ hcovb68
  rw [hcard68] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad69 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(1,2),(2,1),(1,6),(6,1)])

def G69 : SimpleGraph (Fin 7) where
  Adj i j := ad69 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst69 : DecidableRel G69.Adj := fun i j => inferInstanceAs (Decidable (ad69 i j = true))

theorem hfun69 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G69.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (b && g)) = decide (∃ i j : Fin 7, G69.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard69 : G69.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb69 : ∀ i j : Fin 7, G69.Adj i j → i ∈ ({0, 1} : Finset (Fin 7)) ∨ j ∈ ({0, 1} : Finset (Fin 7)) := by
  decide

theorem main69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  rw [hfun69]
  have h := H926.EdgeUpper.edge_upper 7 G69 {0, 1} ⟨0, 1, by decide⟩ hcovb69
  rw [hcard69] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad70 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(1,2),(2,1),(3,6),(6,3)])

def G70 : SimpleGraph (Fin 7) where
  Adj i j := ad70 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst70 : DecidableRel G70.Adj := fun i j => inferInstanceAs (Decidable (ad70 i j = true))

theorem hfun70 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G70.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && g)) = decide (∃ i j : Fin 7, G70.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard70 : G70.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb70 : ∀ i j : Fin 7, G70.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 7)) := by
  decide

theorem main70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  rw [hfun70]
  have h := H926.EdgeUpper.edge_upper 7 G70 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb70
  rw [hcard70] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad71 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1),(1,6),(6,1)])

def G71 : SimpleGraph (Fin 7) where
  Adj i j := ad71 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst71 : DecidableRel G71.Adj := fun i j => inferInstanceAs (Decidable (ad71 i j = true))

theorem hfun71 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G71.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (b && g)) = decide (∃ i j : Fin 7, G71.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard71 : G71.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb71 : ∀ i j : Fin 7, G71.Adj i j → i ∈ ({0, 1} : Finset (Fin 7)) ∨ j ∈ ({0, 1} : Finset (Fin 7)) := by
  decide

theorem main71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  rw [hfun71]
  have h := H926.EdgeUpper.edge_upper 7 G71 {0, 1} ⟨0, 1, by decide⟩ hcovb71
  rw [hcard71] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [this] at h2
  omega

def ad72 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1),(2,6),(6,2)])

def G72 : SimpleGraph (Fin 7) where
  Adj i j := ad72 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst72 : DecidableRel G72.Adj := fun i j => inferInstanceAs (Decidable (ad72 i j = true))

theorem hfun72 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G72.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (c && g)) = decide (∃ i j : Fin 7, G72.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard72 : G72.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb72 : ∀ i j : Fin 7, G72.Adj i j → i ∈ ({0, 1, 2} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 2} : Finset (Fin 7)) := by
  decide

theorem main72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  rw [hfun72]
  have h := H926.EdgeUpper.edge_upper 7 G72 {0, 1, 2} ⟨0, 1, by decide⟩ hcovb72
  rw [hcard72] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 2} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad73 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1),(3,6),(6,3)])

def G73 : SimpleGraph (Fin 7) where
  Adj i j := ad73 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst73 : DecidableRel G73.Adj := fun i j => inferInstanceAs (Decidable (ad73 i j = true))

theorem hfun73 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G73.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && g)) = decide (∃ i j : Fin 7, G73.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard73 : G73.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb73 : ∀ i j : Fin 7, G73.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 7)) := by
  decide

theorem main73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  rw [hfun73]
  have h := H926.EdgeUpper.edge_upper 7 G73 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb73
  rw [hcard73] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad74 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(1,5),(5,1),(5,6),(6,5)])

def G74 : SimpleGraph (Fin 7) where
  Adj i j := ad74 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst74 : DecidableRel G74.Adj := fun i j => inferInstanceAs (Decidable (ad74 i j = true))

theorem hfun74 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G74.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (f && g)) = decide (∃ i j : Fin 7, G74.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard74 : G74.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb74 : ∀ i j : Fin 7, G74.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  rw [hfun74]
  have h := H926.EdgeUpper.edge_upper 7 G74 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb74
  rw [hcard74] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad75 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(3,5),(5,3),(3,6),(6,3)])

def G75 : SimpleGraph (Fin 7) where
  Adj i j := ad75 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst75 : DecidableRel G75.Adj := fun i j => inferInstanceAs (Decidable (ad75 i j = true))

theorem hfun75 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G75.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (d && g)) = decide (∃ i j : Fin 7, G75.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard75 : G75.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb75 : ∀ i j : Fin 7, G75.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 7)) := by
  decide

theorem main75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  rw [hfun75]
  have h := H926.EdgeUpper.edge_upper 7 G75 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb75
  rw [hcard75] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad76 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,2),(2,1),(3,5),(5,3),(5,6),(6,5)])

def G76 : SimpleGraph (Fin 7) where
  Adj i j := ad76 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst76 : DecidableRel G76.Adj := fun i j => inferInstanceAs (Decidable (ad76 i j = true))

theorem hfun76 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G76.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (f && g)) = decide (∃ i j : Fin 7, G76.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard76 : G76.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb76 : ∀ i j : Fin 7, G76.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  rw [hfun76]
  have h := H926.EdgeUpper.edge_upper 7 G76 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb76
  rw [hcard76] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad77 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(1,6),(6,1),(5,6),(6,5)])

def G77 : SimpleGraph (Fin 7) where
  Adj i j := ad77 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst77 : DecidableRel G77.Adj := fun i j => inferInstanceAs (Decidable (ad77 i j = true))

theorem hfun77 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G77.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g) || (f && g)) = decide (∃ i j : Fin 7, G77.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard77 : G77.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb77 : ∀ i j : Fin 7, G77.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  rw [hfun77]
  have h := H926.EdgeUpper.edge_upper 7 G77 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb77
  rw [hcard77] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad78 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(2,6),(6,2),(5,6),(6,5)])

def G78 : SimpleGraph (Fin 7) where
  Adj i j := ad78 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst78 : DecidableRel G78.Adj := fun i j => inferInstanceAs (Decidable (ad78 i j = true))

theorem hfun78 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G78.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g) || (f && g)) = decide (∃ i j : Fin 7, G78.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard78 : G78.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb78 : ∀ i j : Fin 7, G78.Adj i j → i ∈ ({0, 1, 6} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 6} : Finset (Fin 7)) := by
  decide

theorem main78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  rw [hfun78]
  have h := H926.EdgeUpper.edge_upper 7 G78 {0, 1, 6} ⟨0, 1, by decide⟩ hcovb78
  rw [hcard78] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 6} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad79 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(2,5),(5,2),(3,6),(6,3)])

def G79 : SimpleGraph (Fin 7) where
  Adj i j := ad79 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst79 : DecidableRel G79.Adj := fun i j => inferInstanceAs (Decidable (ad79 i j = true))

theorem hfun79 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G79.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (d && g)) = decide (∃ i j : Fin 7, G79.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard79 : G79.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb79 : ∀ i j : Fin 7, G79.Adj i j → i ∈ ({1, 2, 3} : Finset (Fin 7)) ∨ j ∈ ({1, 2, 3} : Finset (Fin 7)) := by
  decide

theorem main79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  rw [hfun79]
  have h := H926.EdgeUpper.edge_upper 7 G79 {1, 2, 3} ⟨0, 1, by decide⟩ hcovb79
  rw [hcard79] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({1, 2, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad80 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(3,5),(5,3),(3,6),(6,3)])

def G80 : SimpleGraph (Fin 7) where
  Adj i j := ad80 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst80 : DecidableRel G80.Adj := fun i j => inferInstanceAs (Decidable (ad80 i j = true))

theorem hfun80 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G80.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g)) = decide (∃ i j : Fin 7, G80.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard80 : G80.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb80 : ∀ i j : Fin 7, G80.Adj i j → i ∈ ({0, 1, 3} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 3} : Finset (Fin 7)) := by
  decide

theorem main80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  rw [hfun80]
  have h := H926.EdgeUpper.edge_upper 7 G80 {0, 1, 3} ⟨0, 1, by decide⟩ hcovb80
  rw [hcard80] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 3} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad81 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,4),(4,1),(3,5),(5,3),(5,6),(6,5)])

def G81 : SimpleGraph (Fin 7) where
  Adj i j := ad81 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst81 : DecidableRel G81.Adj := fun i j => inferInstanceAs (Decidable (ad81 i j = true))

theorem hfun81 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G81.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (f && g)) = decide (∃ i j : Fin 7, G81.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard81 : G81.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb81 : ∀ i j : Fin 7, G81.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 7)) := by
  decide

theorem main81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  rw [hfun81]
  have h := H926.EdgeUpper.edge_upper 7 G81 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb81
  rw [hcard81] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad82 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(3,4),(4,3),(4,5),(5,4),(4,6),(6,4)])

def G82 : SimpleGraph (Fin 7) where
  Adj i j := ad82 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst82 : DecidableRel G82.Adj := fun i j => inferInstanceAs (Decidable (ad82 i j = true))

theorem hfun82 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G82.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G82.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard82 : G82.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb82 : ∀ i j : Fin 7, G82.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 7)) := by
  decide

theorem main82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  rw [hfun82]
  have h := H926.EdgeUpper.edge_upper 7 G82 {0, 1, 4} ⟨0, 1, by decide⟩ hcovb82
  rw [hcard82] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad83 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(1,5),(5,1),(2,6),(6,2),(4,6),(6,4)])

def G83 : SimpleGraph (Fin 7) where
  Adj i j := ad83 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst83 : DecidableRel G83.Adj := fun i j => inferInstanceAs (Decidable (ad83 i j = true))

theorem hfun83 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G83.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g) || (e && g)) = decide (∃ i j : Fin 7, G83.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard83 : G83.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb83 : ∀ i j : Fin 7, G83.Adj i j → i ∈ ({0, 1, 6} : Finset (Fin 7)) ∨ j ∈ ({0, 1, 6} : Finset (Fin 7)) := by
  decide

theorem main83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  rw [hfun83]
  have h := H926.EdgeUpper.edge_upper 7 G83 {0, 1, 6} ⟨0, 1, by decide⟩ hcovb83
  rw [hcard83] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 1, 6} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad84 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(4,5),(5,4),(4,6),(6,4)])

def G84 : SimpleGraph (Fin 7) where
  Adj i j := ad84 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst84 : DecidableRel G84.Adj := fun i j => inferInstanceAs (Decidable (ad84 i j = true))

theorem hfun84 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G84.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f) || (e && g)) = decide (∃ i j : Fin 7, G84.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard84 : G84.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb84 : ∀ i j : Fin 7, G84.Adj i j → i ∈ ({0, 2, 4} : Finset (Fin 7)) ∨ j ∈ ({0, 2, 4} : Finset (Fin 7)) := by
  decide

theorem main84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  rw [hfun84]
  have h := H926.EdgeUpper.edge_upper 7 G84 {0, 2, 4} ⟨0, 1, by decide⟩ hcovb84
  rw [hcard84] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 2, 4} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

def ad85 (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(4,6),(6,4),(5,6),(6,5)])

def G85 : SimpleGraph (Fin 7) where
  Adj i j := ad85 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst85 : DecidableRel G85.Adj := fun i j => inferInstanceAs (Decidable (ad85 i j = true))

theorem hfun85 : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = (fun x : Fin 7 → Bool => decide (∃ i j : Fin 7, G85.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g) || (f && g)) = decide (∃ i j : Fin 7, G85.Adj i j ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) i = true ∧ (![a, b, c, d, e, f, g] : Fin 7 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard85 : G85.edgeFinset.card = 7 := by
  decide +kernel

theorem hcovb85 : ∀ i j : Fin 7, G85.Adj i j → i ∈ ({0, 4, 5} : Finset (Fin 7)) ∨ j ∈ ({0, 4, 5} : Finset (Fin 7)) := by
  decide

theorem main85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  rw [hfun85]
  have h := H926.EdgeUpper.edge_upper 7 G85 {0, 4, 5} ⟨0, 1, by decide⟩ hcovb85
  rw [hcard85] at h
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, ?_, h3⟩
  have : ({0, 4, 5} : Finset (Fin 7)).card = 3 := by decide
  rw [this] at h2
  omega

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux in
theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨main1, main2, main3, main4, main5, main6, main7, main8, main9, main10, main11, main12, main13, main14, main15, main16, main17, main18, main19, main20, main21, main22, main23, main24, main25, main26, main27, main28, main29, main30, main31, main32, main33, main34, main35, main36, main37, main38, main39, main40, main41, main42, main43, main44, main45, main46, main47, main48, main49, main50, main51, main52, main53, main54, main55, main56, main57, main58, main59, main60, main61, main62, main63, main64, main65, main66, main67, main68, main69, main70, main71, main72, main73, main74, main75, main76, main77, main78, main79, main80, main81, main82, main83, main84, main85⟩
