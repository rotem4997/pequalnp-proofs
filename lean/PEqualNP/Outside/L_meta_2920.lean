import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def gat (gs : List Gate) (k : ℕ) : Gate := gs.getD k ⟨GateOp.or, []⟩

def gval (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun q => w.getD q false)

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem gat_eq (gs : List Gate) (k : ℕ) (hk : k < gs.length) : gat gs k = gs[k] :=
  List.getD_eq_getElem _ _ hk

theorem gat_set_eq (gs : List Gate) (i : ℕ) (g : Gate) (hi : i < gs.length) :
    gat (gs.set i g) i = g := by
  unfold gat
  rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hi)]
  simp

theorem gat_set_ne (gs : List Gate) (i k : ℕ) (g : Gate) (h : k ≠ i) :
    gat (gs.set i g) k = gat gs k := by
  unfold gat
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem len2 (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) :
    ((gs.set i g1).set m g2).length = gs.length := by
  simp

theorem g2_m (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) (hm : m < gs.length) :
    gat ((gs.set i g1).set m g2) m = g2 :=
  gat_set_eq _ _ _ (by rw [List.length_set]; exact hm)

theorem g2_i (gs : List Gate) (i m : ℕ) (g1 g2 : Gate) (hi : i < gs.length) (h : i ≠ m) :
    gat ((gs.set i g1).set m g2) i = g1 := by
  rw [gat_set_ne _ _ _ _ h, gat_set_eq _ _ _ hi]

theorem g2_o (gs : List Gate) (i m k : ℕ) (g1 g2 : Gate) (h1 : k ≠ i) (h2 : k ≠ m) :
    gat ((gs.set i g1).set m g2) k = gat gs k := by
  rw [gat_set_ne _ _ _ _ h2, gat_set_ne _ _ _ _ h1]

theorem gate_eq (g : Gate) (o : GateOp) (l : List ℕ) (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  subst h1
  subst h2
  rfl

theorem val_and2 (w : List Bool) (p q : ℕ) :
    gval ⟨GateOp.and, [p, q]⟩ w = (w.getD p false && w.getD q false) := by
  simp [gval, GateOp.eval]

theorem val_or2 (w : List Bool) (p q : ℕ) :
    gval ⟨GateOp.or, [p, q]⟩ w = (w.getD p false || w.getD q false) := by
  simp [gval, GateOp.eval]

theorem W_take (gs : List Gate) (x : List Bool) (k q : ℕ) (hk : k ≤ gs.length)
    (hq : q < x.length + k) :
    (W (gs.take k) x).getD q false = (W gs x).getD q false := by
  have e : W gs x = W (gs.drop k) (W (gs.take k) x) := by
    rw [← W_append, List.take_append_drop]
  rw [e, W_prefix (gs.drop k) (W (gs.take k) x) q
    (by rw [W_length, List.length_take]; omega)]

theorem W_fix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ q ∈ (gat gs k).inputs, q < x.length + k) :
    (W gs x).getD (x.length + k) false = gval (gat gs k) (W gs x) := by
  have e : W gs x = W (gs.drop (k + 1)) (step (W (gs.take k) x) (gat gs k)) := by
    rw [gat_eq gs k hk, ← W_cons, ← List.drop_eq_getElem_cons hk, ← W_append,
      List.take_append_drop]
  have hl : (W (gs.take k) x).length = x.length + k := by
    rw [W_length, List.length_take]; omega
  have h2 : (step (W (gs.take k) x) (gat gs k)).getD (x.length + k) false
      = gval (gat gs k) (W (gs.take k) x) := by
    show ((W (gs.take k) x) ++ [gval (gat gs k) (W (gs.take k) x)]).getD (x.length + k) false = _
    rw [← hl]
    exact getD_app_len _ _
  conv_lhs => rw [e]
  rw [W_prefix _ _ _ (by rw [step_len]; omega), h2]
  unfold gval
  congr 1
  apply List.map_congr_left
  intro q hq
  exact W_take gs x k q (le_of_lt hk) (hr q hq)

theorem W_fix_take (gs : List Gate) (x : List Bool) (k m q : ℕ) (hm : m ≤ gs.length)
    (hkm : k < m) (hq : q = x.length + k)
    (hr : ∀ r ∈ (gat gs k).inputs, r < x.length + k) :
    (W (gs.take m) x).getD q false = gval (gat gs k) (W (gs.take m) x) := by
  subst hq
  rw [W_take gs x m _ hm (by omega), W_fix gs x k (by omega) hr]
  unfold gval
  congr 1
  apply List.map_congr_left
  intro r hr2
  exact (W_take gs x m r hm (by have := hr r hr2; omega)).symm

theorem step_agree (w w' : List Bool) (g g' : Gate) (p : ℕ) (hl : w'.length = w.length)
    (h : ∀ q, q ≠ p → w'.getD q false = w.getD q false)
    (hv : w.length = p ∨ gval g' w' = gval g w) :
    ∀ q, q ≠ p → (step w' g').getD q false = (step w g).getD q false := by
  intro q hq
  show (w' ++ [gval g' w']).getD q false = (w ++ [gval g w]).getD q false
  by_cases h1 : q < w.length
  · rw [getD_app_lt w' _ q (by omega), getD_app_lt w _ q h1]
    exact h q hq
  · by_cases h2 : q = w.length
    · have e1 : (w ++ [gval g w]).getD q false = gval g w := by
        rw [h2]; exact getD_app_len w _
      have e2 : (w' ++ [gval g' w']).getD q false = gval g' w' := by
        rw [h2, ← hl]; exact getD_app_len w' _
      rw [e1, e2]
      rcases hv with hv | hv
      · exact absurd (h2.trans hv) hq
      · exact hv
    · have e1 : (w ++ [gval g w]).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      have e2 : (w' ++ [gval g' w']).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none e1, List.getElem?_eq_none e2]

theorem agree (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat gs' k = gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      gval (gat gs' m) (W (gs'.take m) x) = gval (gat gs m) (W (gs.take m) x)) :
    ∀ k, k ≤ gs.length → ∀ q, q ≠ p →
      (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false := by
  intro k
  induction k with
  | zero => intro _ q _; simp
  | succ k ih =>
    intro hk
    have hk1 : k < gs.length := by omega
    have hk2 : k < gs'.length := by omega
    have IH := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk2,
      W_append, W_append, W_single, W_single, ← gat_eq gs k hk1, ← gat_eq gs' k hk2]
    have l1 : (W (gs.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    have l2 : (W (gs'.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    refine step_agree _ _ _ _ p (by omega) IH ?_
    by_cases hki : k = i
    · left; omega
    · right
      by_cases hkm : k = m
      · subst hkm
        exact hval IH
      · rw [hsame k hki hkm]
        unfold gval
        congr 1
        apply List.map_congr_left
        intro r hr
        apply IH
        intro hre
        rw [hre] at hr
        exact hread k hk1 hkm hr

theorem agree_full (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat gs' k = gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      gval (gat gs' m) (W (gs'.take m) x) = gval (gat gs m) (W (gs.take m) x)) :
    ∀ q, q ≠ p → (W gs' x).getD q false = (W gs x).getD q false := by
  intro q hq
  have h := agree x gs gs' i m p hp hlen hsame hread hval gs.length le_rfl q hq
  rwa [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h

theorem rb_core (n : ℕ) (gs G : List Gate) (i m : ℕ) (hlen : G.length = gs.length)
    (hRB : ∀ k < gs.length, ∀ q ∈ (gat gs k).inputs, q < n + k)
    (hsame : ∀ k, k ≠ i → k ≠ m → gat G k = gat gs k)
    (hi : ∀ q ∈ (gat G i).inputs, q < n + i)
    (hm : ∀ q ∈ (gat G m).inputs, q < n + m) :
    ∀ k < G.length, ∀ q ∈ (gat G k).inputs, q < n + k := by
  intro k hk q hq
  by_cases h1 : k = i
  · subst h1; exact hi q hq
  · by_cases h2 : k = m
    · subst h2; exact hm q hq
    · rw [hsame k h1 h2] at hq
      exact hRB k (by omega) q hq

theorem step_agreeP (w w' : List Bool) (g g' : Gate) (P : ℕ → Prop) (hl : w'.length = w.length)
    (h : ∀ q, ¬ P q → w'.getD q false = w.getD q false)
    (hv : P w.length ∨ gval g' w' = gval g w) :
    ∀ q, ¬ P q → (step w' g').getD q false = (step w g).getD q false := by
  intro q hq
  show (w' ++ [gval g' w']).getD q false = (w ++ [gval g w]).getD q false
  by_cases h1 : q < w.length
  · rw [getD_app_lt w' _ q (by omega), getD_app_lt w _ q h1]
    exact h q hq
  · by_cases h2 : q = w.length
    · have e1 : (w ++ [gval g w]).getD q false = gval g w := by
        rw [h2]; exact getD_app_len w _
      have e2 : (w' ++ [gval g' w']).getD q false = gval g' w' := by
        rw [h2, ← hl]; exact getD_app_len w' _
      rw [e1, e2]
      rcases hv with hv | hv
      · rw [h2] at hq
        exact absurd hv hq
      · exact hv
    · have e1 : (w ++ [gval g w]).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      have e2 : (w' ++ [gval g' w']).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none e1, List.getElem?_eq_none e2]

theorem agreeP (x : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hlen : gs'.length = gs.length)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false) →
      gval (gat gs' k) (W (gs'.take k) x) = gval (gat gs k) (W (gs.take k) x)) :
    ∀ k, k ≤ gs.length → ∀ q, ¬ P q →
      (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false := by
  intro k
  induction k with
  | zero => intro _ q _; simp
  | succ k ih =>
    intro hk
    have hk1 : k < gs.length := by omega
    have hk2 : k < gs'.length := by omega
    have IH := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk2,
      W_append, W_append, W_single, W_single, ← gat_eq gs k hk1, ← gat_eq gs' k hk2]
    have l1 : (W (gs.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    have l2 : (W (gs'.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    refine step_agreeP _ _ _ _ P (by omega) IH ?_
    by_cases hP : P (x.length + k)
    · left
      rw [l1]
      exact hP
    · right
      exact hstep k hk1 hP IH

theorem agreeP_full (x : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hlen : gs'.length = gs.length)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false) →
      gval (gat gs' k) (W (gs'.take k) x) = gval (gat gs k) (W (gs.take k) x)) :
    ∀ q, ¬ P q → (W gs' x).getD q false = (W gs x).getD q false := by
  intro q hq
  have h := agreeP x gs gs' P hlen hstep gs.length le_rfl q hq
  rwa [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h

theorem notP (q p1 p2 : ℕ) (h1 : q ≠ p1) (h2 : q ≠ p2) : ¬ (q = p1 ∨ q = p2) := by
  rintro (h | h)
  · exact h1 h
  · exact h2 h

theorem lt_of_some (gs : List Gate) (k : ℕ) (g : Gate) (h : gs[k]? = some g) : k < gs.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem gat_of (gs : List Gate) (k : ℕ) (g : Gate) (h : gs[k]? = some g) : gat gs k = g := by
  unfold gat
  rw [List.getD_eq_getElem?_getD, h]
  rfl

theorem rf_core (gs G : List Gate) (X : List Bool) (n j is iv iw a b c z o : ℕ)
    (op1 op2 : GateOp)
    (hX : X.length = n) (hlen : G.length = gs.length) (hjl : j < gs.length)
    (hisj : is < j) (hvw : iv < iw) (hwj : iw < j)
    (hgs : gat gs is = ⟨op2, [a, b]⟩) (hgv : gat gs iv = ⟨op2, [a, c]⟩)
    (hgw : gat gs iw = ⟨op1, [n + iv, z]⟩)
    (hgj : gat gs j = ⟨op1, [n + is, n + iw]⟩ ∨ gat gs j = ⟨op1, [n + iw, n + is]⟩)
    (hGv : gat G iv = ⟨op1, [b, c]⟩) (hGw : gat G iw = ⟨op2, [a, n + iv]⟩)
    (hGj : gat G j = ⟨op1, [n + iw, z]⟩)
    (hsame : ∀ k, k ≠ iv → k ≠ iw → k ≠ j → gat G k = gat gs k)
    (ha1 : a < n + is) (hb1 : b < n + is) (ha : a < n + iv) (hb : b < n + iv)
    (hc : c < n + iv) (hz : z < n + iw) (hzv : z ≠ n + iv)
    (hr1 : ∀ k < gs.length, k ≠ iw → n + iv ∉ (gat gs k).inputs)
    (hr2 : ∀ k < gs.length, k ≠ j → n + iw ∉ (gat gs k).inputs)
    (hid1 : ∀ A B D Z : Bool, op1.eval [op2.eval [A, op1.eval [B, D]], Z]
      = op1.eval [op2.eval [A, B], op1.eval [op2.eval [A, D], Z]])
    (hid2 : ∀ A B D Z : Bool, op1.eval [op2.eval [A, op1.eval [B, D]], Z]
      = op1.eval [op1.eval [op2.eval [A, D], Z], op2.eval [A, B]])
    (ho1 : o ≠ n + iv) (ho2 : o ≠ n + iw) :
    (W G X).getD o false = (W gs X).getD o false := by
  refine agreeP_full X gs G (fun q => q = n + iv ∨ q = n + iw) hlen ?_ o (notP _ _ _ ho1 ho2)
  intro k hk hP hag
  have hkv : k ≠ iv := fun h => hP (by left; omega)
  have hkw : k ≠ iw := fun h => hP (by right; omega)
  by_cases hkj : k = j
  · subst k
    have hjG : j ≤ G.length := by omega
    have hjg : j ≤ gs.length := by omega
    have f1 : (W (G.take j) X).getD (n + iv) false
        = op1.eval [(W (G.take j) X).getD b false, (W (G.take j) X).getD c false] := by
      rw [W_fix_take G X iv j (n + iv) hjG (by omega) (by omega)
        (by rw [hGv]; intro r hr; simp at hr; omega), hGv]
      rfl
    have f2 : (W (G.take j) X).getD (n + iw) false
        = op2.eval [(W (G.take j) X).getD a false, (W (G.take j) X).getD (n + iv) false] := by
      rw [W_fix_take G X iw j (n + iw) hjG hwj (by omega)
        (by rw [hGw]; intro r hr; simp at hr; omega), hGw]
      rfl
    have g1 : (W (gs.take j) X).getD (n + is) false
        = op2.eval [(W (gs.take j) X).getD a false, (W (gs.take j) X).getD b false] := by
      rw [W_fix_take gs X is j (n + is) hjg hisj (by omega)
        (by rw [hgs]; intro r hr; simp at hr; omega), hgs]
      rfl
    have g2 : (W (gs.take j) X).getD (n + iw) false
        = op1.eval [(W (gs.take j) X).getD (n + iv) false, (W (gs.take j) X).getD z false] := by
      rw [W_fix_take gs X iw j (n + iw) hjg hwj (by omega)
        (by rw [hgw]; intro r hr; simp at hr; omega), hgw]
      rfl
    have g3 : (W (gs.take j) X).getD (n + iv) false
        = op2.eval [(W (gs.take j) X).getD a false, (W (gs.take j) X).getD c false] := by
      rw [W_fix_take gs X iv j (n + iv) hjg (by omega) (by omega)
        (by rw [hgv]; intro r hr; simp at hr; omega), hgv]
      rfl
    have ea := hag a (notP _ _ _ (by omega) (by omega))
    have eb := hag b (notP _ _ _ (by omega) (by omega))
    have ec := hag c (notP _ _ _ (by omega) (by omega))
    have ez := hag z (notP _ _ _ hzv (by omega))
    rw [hGj]
    rcases hgj with hgj | hgj
    · rw [hgj]
      show op1.eval [(W (G.take j) X).getD (n + iw) false, (W (G.take j) X).getD z false]
        = op1.eval [(W (gs.take j) X).getD (n + is) false, (W (gs.take j) X).getD (n + iw) false]
      rw [f2, f1, g1, g2, g3, ea, eb, ec, ez]
      exact hid1 _ _ _ _
    · rw [hgj]
      show op1.eval [(W (G.take j) X).getD (n + iw) false, (W (G.take j) X).getD z false]
        = op1.eval [(W (gs.take j) X).getD (n + iw) false, (W (gs.take j) X).getD (n + is) false]
      rw [f2, f1, g1, g2, g3, ea, eb, ec, ez]
      exact hid2 _ _ _ _
  · rw [hsame k hkv hkw hkj]
    unfold gval
    congr 1
    apply List.map_congr_left
    intro r hr
    apply hag
    refine notP _ _ _ ?_ ?_
    · intro h
      rw [h] at hr
      exact hr1 k hk hkw hr
    · intro h
      rw [h] at hr
      exact hr2 k hk hkj hr

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hop hs hv hw hj hisj hvw hwj ha1 hb1 ha hb hc hz hzv
    hr1 hr2 ho1 ho2
  have hjl : j < C.gates.length := by
    rcases hj with h | h
    · exact lt_of_some _ _ _ h
    · exact lt_of_some _ _ _ h
  have hivl : iv < C.gates.length := lt_of_some _ _ _ hv
  have hiwl : iw < C.gates.length := lt_of_some _ _ _ hw
  have hgs := gat_of _ _ _ hs
  have hgv := gat_of _ _ _ hv
  have hgw := gat_of _ _ _ hw
  have hgj : gat C.gates j = ⟨op1, [n + is, n + iw]⟩ ∨ gat C.gates j = ⟨op1, [n + iw, n + is]⟩ := by
    rcases hj with h | h
    · left; exact gat_of _ _ _ h
    · right; exact gat_of _ _ _ h
  have hr1' : ∀ k < C.gates.length, k ≠ iw → n + iv ∉ (gat C.gates k).inputs := by
    intro k hk hkw
    rw [gat_eq _ _ hk]
    exact hr1 k _ (List.getElem?_eq_getElem hk) hkw
  have hr2' : ∀ k < C.gates.length, k ≠ j → n + iw ∉ (gat C.gates k).inputs := by
    intro k hk hkj
    rw [gat_eq _ _ hk]
    exact hr2 k _ (List.getElem?_eq_getElem hk) hkj
  have hid1 : ∀ A B D Z : Bool, op1.eval [op2.eval [A, op1.eval [B, D]], Z]
      = op1.eval [op2.eval [A, B], op1.eval [op2.eval [A, D], Z]] := by
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro A B D Z <;>
      cases A <;> cases B <;> cases D <;> cases Z <;> rfl
  have hid2 : ∀ A B D Z : Bool, op1.eval [op2.eval [A, op1.eval [B, D]], Z]
      = op1.eval [op1.eval [op2.eval [A, D], Z], op2.eval [A, B]] := by
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro A B D Z <;>
      cases A <;> cases B <;> cases D <;> cases Z <;> rfl
  generalize hG : ((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
    ⟨op1, [n + iw, z]⟩ = G
  have hL : G.length = C.gates.length := by rw [← hG]; simp
  have hGv : gat G iv = ⟨op1, [b, c]⟩ := by
    rw [← hG, gat_set_ne _ _ _ _ (by omega), gat_set_ne _ _ _ _ (by omega),
      gat_set_eq _ _ _ hivl]
  have hGw : gat G iw = ⟨op2, [a, n + iv]⟩ := by
    rw [← hG, gat_set_ne _ _ _ _ (by omega),
      gat_set_eq _ _ _ (by rw [List.length_set]; exact hiwl)]
  have hGj : gat G j = ⟨op1, [n + iw, z]⟩ := by
    rw [← hG, gat_set_eq _ _ _ (by rw [List.length_set, List.length_set]; exact hjl)]
  have hsame : ∀ k, k ≠ iv → k ≠ iw → k ≠ j → gat G k = gat C.gates k := by
    intro k h1 h2 h3
    rw [← hG, gat_set_ne _ _ _ _ h3, gat_set_ne _ _ _ _ h2, gat_set_ne _ _ _ _ h1]
  refine ⟨?_, hL⟩
  funext x0
  show (W G (List.ofFn x0)).getD C.output false = (W C.gates (List.ofFn x0)).getD C.output false
  exact rf_core C.gates G (List.ofFn x0) n j is iv iw a b c z C.output op1 op2 (by simp) hL hjl
    hisj hvw hwj hgs hgv hgw hgj hGv hGw hGj hsame ha1 hb1 ha hb hc hz hzv hr1' hr2' hid1 hid2
    ho1 ho2

end PEqualNP.Outside.L_meta_2920

theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length :=
  PEqualNP.Outside.L_meta_2920.main_aux
