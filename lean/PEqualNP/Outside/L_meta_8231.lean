import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8231

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


def LL : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]

def EE : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8231

theorem PEqualNP.Outside.L_meta_8231 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (40 : ℕ)), x1.eval (List.map (fun (x4 : ℕ) => x4.testBit ↑x3) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]) = Nat.testBit (65535 : ℕ) ↑x3) → ∀ (x4 : Fin (11 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)), (↑x5, ↑x6) ∈ [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true := by
  intro C hC hrow x
  let row : ℕ → List Bool := fun j => PEqualNP.Outside.L_meta_8231.LL.map fun a => a.testBit j
  have hrow' : ∀ j : Fin 40, C.eval (row j) = Nat.testBit 65535 j := hrow
  have gx : ∀ i (hi : i < 11), (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have gr : ∀ j i, (row j).getD i false = (PEqualNP.Outside.L_meta_8231.LL.getD i 0).testBit j := by
    intro j i
    rcases Nat.lt_or_ge i PEqualNP.Outside.L_meta_8231.LL.length with h | h
    · simp [row, List.getD_eq_getElem?_getD, h]
    · rw [List.getD_eq_default _ _ (by simpa [row] using h), List.getD_eq_default _ _ h, Nat.zero_testBit]
  have hm := PEqualNP.Outside.L_meta_8231.mono C.gates
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => by simpa using (hC g hg).1
  have llen : ∀ j, (row j).length = 11 := by intro j; simp [row, PEqualNP.Outside.L_meta_8231.LL]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have key : ∀ m : Fin 2048, (∀ e ∈ PEqualNP.Outside.L_meta_8231.EE, ((m : ℕ).testBit e.1 && (m : ℕ).testBit e.2) = false) → ∃ j : Fin 40, (Nat.testBit 65535 (j : ℕ) = false) ∧ ∀ i : Fin 11, (m : ℕ).testBit (i : ℕ) = true → (PEqualNP.Outside.L_meta_8231.LL.getD (i : ℕ) 0).testBit (j : ℕ) = true := by decide +kernel
    have tb : ∀ i : Fin 11, (Nat.ofBits x).testBit (i : ℕ) = x i := fun i => Nat.testBit_ofBits_lt x i i.isLt
    have hlt : ∀ e ∈ PEqualNP.Outside.L_meta_8231.EE, e.1 < 11 ∧ e.2 < 11 := by decide
    obtain ⟨j, hj, hle⟩ := key ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x⟩ (by
      intro e he
      obtain ⟨h1, h2⟩ := hlt e he
      have e1 := tb ⟨e.1, h1⟩
      have e2 := tb ⟨e.2, h2⟩
      simp only at e1 e2 ⊢
      rw [e1, e2]
      cases hx1 : x ⟨e.1, h1⟩
      · rfl
      · have := hcon ⟨e.1, h1⟩ ⟨e.2, h2⟩ he hx1
        simpa using this)
    have := hm (List.ofFn x) (row j) (by rw [llen]; simp) (fun i hi => ?_) hop C.output h
    · have h' : C.eval (row j) = true := this
      rw [hrow' j, hj] at h'; cases h'
    · by_cases hin : i < 11
      · rw [gx i hin] at hi
        rw [gr]
        exact hle ⟨i, hin⟩ ((tb ⟨i, hin⟩).trans hi)
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
  · rintro ⟨a, b, hab, ha, hb⟩
    have key : ∀ e ∈ PEqualNP.Outside.L_meta_8231.EE, ∃ j : Fin 40, Nat.testBit 65535 (j : ℕ) = true ∧ ∀ i : Fin 11, (PEqualNP.Outside.L_meta_8231.LL.getD (i : ℕ) 0).testBit (j : ℕ) = true → (i : ℕ) = e.1 ∨ (i : ℕ) = e.2 := by decide +kernel
    obtain ⟨j, hj, hle⟩ := key _ hab
    refine hm (row j) (List.ofFn x) (by rw [llen]; simp) (fun i hi => ?_) hop C.output ?_
    · by_cases hin : i < 11
      · rw [gr] at hi
        rw [gx i hin]
        rcases hle ⟨i, hin⟩ hi with e | e
        · have : (⟨i, hin⟩ : Fin 11) = a := Fin.ext e
          rw [this]; exact ha
        · have : (⟨i, hin⟩ : Fin 11) = b := Fin.ext e
          rw [this]; exact hb
      · rw [List.getD_eq_default _ _ (by rw [llen]; omega)] at hi; cases hi
    · have := hrow' j
      rw [hj] at this; exact this
