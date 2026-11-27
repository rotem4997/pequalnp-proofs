import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3630
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def rgm (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem gsim (r : ℕ → ℕ) (d : ℕ) (B : List Gate) : ∀ U U' : List Bool,
    U'.length = U.length + d → (∀ t, U.length ≤ t → r t = t + d) →
    (∀ i, i < U.length → r i < U'.length) →
    (∀ i, U.getD i false = U'.getD (r i) false) →
    ∀ i, (fl EV B U).getD i false = (fl EV (B.map (rgm r)) U').getD (r i) false := by
  induction B with
  | nil => intro U U' _ _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen ht hlt h i
    rw [List.map_cons, fl_cons, fl_cons]
    have hv : EV U g = EV U' (rgm r g) := by
      show g.op.eval (g.inputs.map fun i => U.getD i false)
        = g.op.eval ((g.inputs.map r).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    apply ih
    · rw [List.length_append, List.length_append, hlen]; simp; omega
    · intro t htt
      rw [List.length_append] at htt
      exact ht t (by omega)
    · intro j hj
      rw [List.length_append] at hj
      rw [List.length_append]
      by_cases hj2 : j < U.length
      · have := hlt j hj2; omega
      · have hj3 : j = U.length := by simp at hj; omega
        rw [ht j (by omega), hlen, hj3]; simp
    · intro t
      rcases Nat.lt_trichotomy t U.length with h1 | h1 | h1
      · rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ (hlt t h1)]
        exact h t
      · rw [h1, getD_snoc_eq, ht U.length (le_refl _), ← hlen, getD_snoc_eq]
        exact hv
      · rw [getD_snoc_gt _ _ _ h1, ht t (le_of_lt h1), getD_snoc_gt _ _ _ (by omega)]

theorem gx (x : Fin 9 → Bool) (i : Fin 9) (t : List Bool) :
    (List.ofFn x ++ t).getD i.1 false = x i := by
  rw [List.getD_append _ _ _ _ (by simp)]
  exact getD_ofFn x i

theorem snocN (L : List Bool) (v : Bool) (k : ℕ) (h : L.length = k) :
    (L ++ [v]).getD k false = v := by
  rw [← h]; exact getD_snoc_eq L v

theorem gen (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C) (S : Finset (Fin 9))
    (pre : List Gate) (d q : ℕ) (hpre : PEqualNP.MetaComplexity.FanInTwo ⟨pre, 0⟩)
    (hd : pre.length = d + 1) (hq : q < 11 + d)
    (h10 : ∀ x : Fin 9 → Bool, (fl EV pre (List.ofFn x ++ [false])).getD 10 false = (x 0 || x 4))
    (hqv : ∀ x : Fin 9 → Bool, (fl EV pre (List.ofFn x ++ [false])).getD q false = true ↔
      ∃ t ∈ S, x t = true) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size + (d + 1) ∧
      ∀ (x : Fin 9 → Bool) (b : Bool), (b = true ↔ ∃ t ∈ S, x t = true) →
        D.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x ++ [x 0 || x 4, b]) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, r = fun i =>
      if i < 9 then i else if i = 9 then 10 else if i = 10 then q else i + d := ⟨_, rfl⟩
  refine ⟨⟨pre ++ C.gates.map (rgm r), r C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hpre g h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      refine ⟨(hF g0 hg0).1, ?_⟩
      show (g0.inputs.map r).length ≤ 2
      rw [List.length_map]; exact (hF g0 hg0).2
  · show (pre ++ C.gates.map (rgm r)).length = C.gates.length + (d + 1)
    rw [List.length_append, List.length_map, hd]; omega
  · intro x b hb
    have hX : (List.ofFn x).length = 9 := by simp
    have hU : List.ofFn x ++ [x 0 || x 4, b] = (List.ofFn x ++ [x 0 || x 4]) ++ [b] := by simp
    have hUl : (List.ofFn x ++ [x 0 || x 4, b]).length = 11 := by simp
    have hU'l : (fl EV pre (List.ofFn x ++ [false])).length = 11 + d := by
      rw [fl_len, hd]; simp; omega
    show (fl EV (pre ++ C.gates.map (rgm r)) (List.ofFn x ++ [false])).getD (r C.output) false
      = (fl EV C.gates (List.ofFn x ++ [x 0 || x 4, b])).getD C.output false
    rw [fl_append]
    symm
    apply gsim r d C.gates
    · rw [hU'l, hUl]
    · intro t ht
      rw [hUl] at ht
      rw [hr]
      show (if t < 9 then t else if t = 9 then 10 else if t = 10 then q else t + d) = t + d
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · intro i hi
      rw [hUl] at hi
      rw [hU'l, hr]
      show (if i < 9 then i else if i = 9 then 10 else if i = 10 then q else i + d) < 11 + d
      split_ifs <;> omega
    · intro i
      rw [hr]
      show _ = (fl EV pre (List.ofFn x ++ [false])).getD
        (if i < 9 then i else if i = 9 then 10 else if i = 10 then q else i + d) false
      by_cases h1 : i < 9
      · rw [if_pos h1, fl_keep _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by rw [hX]; exact h1),
          List.getD_append _ _ _ _ (by rw [hX]; exact h1)]
      · rw [if_neg h1]
        by_cases h2 : i = 9
        · rw [if_pos h2, h2, h10 x, hU, getD_snoc_lt _ _ _ (by simp)]
          exact snocN _ _ 9 hX
        · rw [if_neg h2]
          by_cases h3 : i = 10
          · rw [if_pos h3, h3, hU, snocN _ _ 10 (by simp)]
            apply Bool.eq_iff_iff.2
            rw [hb, hqv x]
          · rw [if_neg h3, List.getD_eq_default _ _ (by rw [hUl]; omega),
              List.getD_eq_default _ _ (by rw [hU'l]; omega)]

theorem pre1_val (x : Fin 9 → Bool) :
    fl EV [⟨GateOp.or, [0, 4]⟩] (List.ofFn x ++ [false]) = (List.ofFn x ++ [false]) ++ [x 0 || x 4] := by
  have e0 : (List.ofFn x ++ [false]).getD 0 false = x 0 := gx x 0 [false]
  have e4 : (List.ofFn x ++ [false]).getD 4 false = x 4 := gx x 4 [false]
  show (List.ofFn x ++ [false]) ++ [GateOp.or.eval [(List.ofFn x ++ [false]).getD 0 false,
    (List.ofFn x ++ [false]).getD 4 false]] = _
  rw [e0, e4]
  simp [GateOp.eval]

theorem pre2_val (x : Fin 9 → Bool) (a b : Fin 9) :
    fl EV [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [a.1, b.1]⟩] (List.ofFn x ++ [false])
      = ((List.ofFn x ++ [false]) ++ [x 0 || x 4]) ++ [x a || x b] := by
  rw [fl_cons]
  have h1 := pre1_val x
  rw [fl_cons] at h1
  have h2 : fl EV [] (List.ofFn x ++ [false] ++ [EV (List.ofFn x ++ [false]) ⟨GateOp.or, [0, 4]⟩])
      = List.ofFn x ++ [false] ++ [EV (List.ofFn x ++ [false]) ⟨GateOp.or, [0, 4]⟩] := rfl
  rw [h2] at h1
  rw [h1]
  have ea : (List.ofFn x ++ ([false] ++ [x 0 || x 4])).getD a.1 false = x a := gx x a _
  have eb : (List.ofFn x ++ ([false] ++ [x 0 || x 4])).getD b.1 false = x b := gx x b _
  rw [← List.append_assoc] at ea eb
  show (List.ofFn x ++ [false] ++ [x 0 || x 4]) ++ [GateOp.or.eval
    [(List.ofFn x ++ [false] ++ [x 0 || x 4]).getD a.1 false,
     (List.ofFn x ++ [false] ++ [x 0 || x 4]).getD b.1 false]] = _
  rw [ea, eb]
  simp [GateOp.eval]

theorem fan1 : PEqualNP.MetaComplexity.FanInTwo ⟨[⟨GateOp.or, [0, 4]⟩], 0⟩ := by
  intro g hg
  simp at hg
  subst hg
  exact ⟨by simp, by simp⟩

theorem fan2 (a b : ℕ) :
    PEqualNP.MetaComplexity.FanInTwo ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [a, b]⟩], 0⟩ := by
  intro g hg
  simp at hg
  rcases hg with rfl | rfl
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

theorem or_iff (p q : Bool) : (p || q) = true ↔ (p = true ∨ q = true) := by
  cases p <;> cases q <;> simp

end PEqualNP.Outside.L_meta_3630

open PEqualNP.Outside.L_meta_3630 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) := by
  intro C S hF hcard
  have hXl : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [false]).length = 10 := by intro x; simp
  have fin : ∀ (d : ℕ), (d + 1 ≤ if S.card ≤ 1 ∨ S = {0, 4} then 1 else 2) →
      (∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size + (d + 1) ∧
        ∀ (x : Fin 9 → Bool) (b : Bool), (b = true ↔ ∃ t ∈ S, x t = true) →
          D.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x ++ [x 0 || x 4, b])) →
      ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧
        (x5.size ≤ C.size + if S.card ≤ 1 ∨ S = {0, 4} then 1 else 2) ∧
        ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false])
          = C.eval (List.ofFn x6 ++ [x6 0 || x6 4, decide (∃ x7 ∈ S, x6 x7 = true)]) := by
    intro d hd ⟨D, h1, h2, h3⟩
    exact ⟨D, h1, by rw [h2]; omega, fun x => h3 x _ (by simp)⟩
  by_cases hS : S = {0, 4}
  · apply fin 0 (by rw [if_pos (Or.inr hS)])
    apply gen C hF S _ 0 10 fan1 rfl (by omega)
    · intro x
      rw [pre1_val]; exact snocN _ _ 10 (hXl x)
    · intro x
      rw [pre1_val, snocN _ _ 10 (hXl x), hS, or_iff]
      simp
  · rcases Nat.lt_or_ge S.card 2 with hc | hc
    · have hc1 : S.card ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos S.card with h0 | h0
      · have hSe : S = ∅ := Finset.card_eq_zero.1 h0
        apply fin 0 (by rw [if_pos (Or.inl hc1)])
        apply gen C hF S _ 0 9 fan1 rfl (by omega)
        · intro x
          rw [pre1_val]; exact snocN _ _ 10 (hXl x)
        · intro x
          rw [pre1_val, getD_snoc_lt _ _ _ (by rw [hXl x]; omega), snocN _ _ 9 (by simp), hSe]
          simp
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by omega : S.card = 1)
        apply fin 0 (by rw [if_pos (Or.inl hc1)])
        apply gen C hF S _ 0 a.1 fan1 rfl (by omega)
        · intro x
          rw [pre1_val]; exact snocN _ _ 10 (hXl x)
        · intro x
          rw [pre1_val, List.append_assoc, gx x a, ha]
          simp
    · have hc2 : S.card = 2 := by omega
      obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.1 hc2
      apply fin 1 (by rw [if_neg (by rw [not_or]; exact ⟨by omega, hS⟩)])
      apply gen C hF S _ 1 11 (fan2 a.1 b.1) rfl (by omega)
      · intro x
        rw [pre2_val, getD_snoc_lt _ _ _ (by simp)]
        exact snocN _ _ 10 (hXl x)
      · intro x
        rw [pre2_val, snocN _ _ 11 (by simp), hSab, or_iff]
        simp
