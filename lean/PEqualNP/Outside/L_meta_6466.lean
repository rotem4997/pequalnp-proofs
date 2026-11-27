import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_6466

def st (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem st_len (w : List Bool) (g : Gate) : (st w g).length = w.length + 1 := by
  simp [st]

theorem st_get (w : List Bool) (g : Gate) (i : ℕ) : (st w g).getD i false = if i < w.length then w.getD i false else if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false) else false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · rw [if_pos h]
    unfold st
    rw [List.getD_append _ _ _ _ h]
  · subst h
    rw [if_neg (lt_irrefl _), if_pos rfl]
    unfold st
    simp
  · rw [if_neg (by omega), if_neg (by omega)]
    unfold st
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem st_get2 (w : List Bool) (g : Gate) (i : ℕ) : ((st w g)[i]?).getD false = if i < w.length then (w[i]?).getD false else if i = w.length then g.op.eval (g.inputs.map fun j => (w[j]?).getD false) else false := by
  have h := st_get w g i
  simp only [List.getD_eq_getElem?_getD] at h
  exact h

theorem st_old (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) : (st w g).getD i false = w.getD i false := by
  rw [st_get, if_pos h]

theorem st_new (w : List Bool) (g : Gate) (i : ℕ) (h : i = w.length) : (st w g).getD i false = g.op.eval (g.inputs.map fun j => w.getD j false) := by
  rw [st_get, if_neg (by omega), if_pos h]

def ng (N o a3 a4 a5 a6 a7 a8 : ℕ) : List Gate := [⟨GateOp.or, [a4, a5]⟩, ⟨GateOp.or, [N, a6]⟩, ⟨GateOp.and, [a3, N + 1]⟩, ⟨GateOp.or, [a7, a8]⟩, ⟨GateOp.and, [a4, N + 3]⟩, ⟨GateOp.or, [o, N + 2]⟩, ⟨GateOp.or, [N + 5, N + 4]⟩]

theorem chain (W : List Bool) (N o a3 a4 a5 a6 a7 a8 : ℕ) (hW : W.length = N) (ho : o < N) (h3 : a3 < N) (h4 : a4 < N) (h5 : a5 < N) (h6 : a6 < N) (h7 : a7 < N) (h8 : a8 < N) :
    (((ng N o a3 a4 a5 a6 a7 a8).foldl st W).getD (N + 6) false = (W.getD o false || W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false) || W.getD a4 false && (W.getD a7 false || W.getD a8 false))) ∧
    (W.getD a4 false = false → ((ng N o a3 a4 a5 a6 a7 a8).foldl st W).getD (N + 6) false = ((ng N o a3 a4 a5 a6 a7 a8).foldl st W).getD (N + 5) false) ∧
    (W.getD a3 false = false → (((ng N o a3 a4 a5 a6 a7 a8).take 6).foldl st W).getD (N + 5) false = (((ng N o a3 a4 a5 a6 a7 a8).take 6).foldl st W).getD o false) := by
  obtain ⟨W1, hW1⟩ : ∃ W1, W1 = st W ⟨GateOp.or, [a4, a5]⟩ := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = st W1 ⟨GateOp.or, [N, a6]⟩ := ⟨_, rfl⟩
  obtain ⟨W3, hW3⟩ : ∃ W3, W3 = st W2 ⟨GateOp.and, [a3, N + 1]⟩ := ⟨_, rfl⟩
  obtain ⟨W4, hW4⟩ : ∃ W4, W4 = st W3 ⟨GateOp.or, [a7, a8]⟩ := ⟨_, rfl⟩
  obtain ⟨W5, hW5⟩ : ∃ W5, W5 = st W4 ⟨GateOp.and, [a4, N + 3]⟩ := ⟨_, rfl⟩
  obtain ⟨W6, hW6⟩ : ∃ W6, W6 = st W5 ⟨GateOp.or, [o, N + 2]⟩ := ⟨_, rfl⟩
  obtain ⟨W7, hW7⟩ : ∃ W7, W7 = st W6 ⟨GateOp.or, [N + 5, N + 4]⟩ := ⟨_, rfl⟩
  have e7 : (ng N o a3 a4 a5 a6 a7 a8).foldl st W = W7 := by
    subst hW7 hW6 hW5 hW4 hW3 hW2 hW1
    rfl
  have e6 : ((ng N o a3 a4 a5 a6 a7 a8).take 6).foldl st W = W6 := by
    subst hW6 hW5 hW4 hW3 hW2 hW1
    rfl
  have l1 : W1.length = N + 1 := by rw [hW1, st_len, hW]
  have l2 : W2.length = N + 2 := by rw [hW2, st_len, l1]
  have l3 : W3.length = N + 3 := by rw [hW3, st_len, l2]
  have l4 : W4.length = N + 4 := by rw [hW4, st_len, l3]
  have l5 : W5.length = N + 5 := by rw [hW5, st_len, l4]
  have l6 : W6.length = N + 6 := by rw [hW6, st_len, l5]
  have l7 : W7.length = N + 7 := by rw [hW7, st_len, l6]
  have p1 : ∀ i < N, W1.getD i false = W.getD i false := fun i hi => by rw [hW1, st_old _ _ _ (by omega)]
  have p2 : ∀ i < N, W2.getD i false = W.getD i false := fun i hi => by rw [hW2, st_old _ _ _ (by omega), p1 i hi]
  have p3 : ∀ i < N, W3.getD i false = W.getD i false := fun i hi => by rw [hW3, st_old _ _ _ (by omega), p2 i hi]
  have p4 : ∀ i < N, W4.getD i false = W.getD i false := fun i hi => by rw [hW4, st_old _ _ _ (by omega), p3 i hi]
  have p5 : ∀ i < N, W5.getD i false = W.getD i false := fun i hi => by rw [hW5, st_old _ _ _ (by omega), p4 i hi]
  have p6 : ∀ i < N, W6.getD i false = W.getD i false := fun i hi => by rw [hW6, st_old _ _ _ (by omega), p5 i hi]
  have n1 : W1.getD N false = (W.getD a4 false || W.getD a5 false) := by
    rw [hW1, st_new _ _ _ (by omega)]
    show (W.getD a4 false || (W.getD a5 false || false)) = _
    rw [Bool.or_false]
  have n2 : W2.getD (N + 1) false = (W.getD a4 false || W.getD a5 false || W.getD a6 false) := by
    rw [hW2, st_new _ _ _ (by omega)]
    show (W1.getD N false || (W1.getD a6 false || false)) = _
    rw [Bool.or_false, n1, p1 a6 h6]
  have n3 : W3.getD (N + 2) false = (W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false)) := by
    rw [hW3, st_new _ _ _ (by omega)]
    show (W2.getD a3 false && (W2.getD (N + 1) false && true)) = _
    rw [Bool.and_true, n2, p2 a3 h3]
  have n3b : W4.getD (N + 2) false = (W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false)) := by
    rw [hW4, st_old _ _ _ (by omega), n3]
  have n4 : W4.getD (N + 3) false = (W.getD a7 false || W.getD a8 false) := by
    rw [hW4, st_new _ _ _ (by omega)]
    show (W3.getD a7 false || (W3.getD a8 false || false)) = _
    rw [Bool.or_false, p3 a7 h7, p3 a8 h8]
  have n3c : W5.getD (N + 2) false = (W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false)) := by
    rw [hW5, st_old _ _ _ (by omega), n3b]
  have n5 : W5.getD (N + 4) false = (W.getD a4 false && (W.getD a7 false || W.getD a8 false)) := by
    rw [hW5, st_new _ _ _ (by omega)]
    show (W4.getD a4 false && (W4.getD (N + 3) false && true)) = _
    rw [Bool.and_true, n4, p4 a4 h4]
  have n5b : W6.getD (N + 4) false = (W.getD a4 false && (W.getD a7 false || W.getD a8 false)) := by
    rw [hW6, st_old _ _ _ (by omega), n5]
  have n6 : W6.getD (N + 5) false = (W.getD o false || W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false)) := by
    rw [hW6, st_new _ _ _ (by omega)]
    show (W5.getD o false || (W5.getD (N + 2) false || false)) = _
    rw [Bool.or_false, n3c, p5 o ho]
  have n6b : W7.getD (N + 5) false = (W.getD o false || W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false)) := by
    rw [hW7, st_old _ _ _ (by omega), n6]
  have n7 : W7.getD (N + 6) false = (W.getD o false || W.getD a3 false && (W.getD a4 false || W.getD a5 false || W.getD a6 false) || W.getD a4 false && (W.getD a7 false || W.getD a8 false)) := by
    rw [hW7, st_new _ _ _ (by omega)]
    show (W6.getD (N + 5) false || (W6.getD (N + 4) false || false)) = _
    rw [Bool.or_false, n6, n5b]
  rw [e7, e6]
  refine ⟨n7, ?_, ?_⟩
  · intro hb
    rw [n7, n6b, hb]
    simp
  · intro hb
    rw [n6, p6 o ho, hb]
    simp

theorem wires_app (C : Circuit) (L : List Gate) (o : ℕ) (x : List Bool) : (Circuit.mk (C.gates ++ L) o).wires x = L.foldl st (C.wires x) := by
  unfold Circuit.wires
  rw [List.foldl_append]
  rfl

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  generalize C.gates = G
  induction G generalizing x with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem wires_prefix (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) : (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  generalize C.gates = G
  induction G generalizing x with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem inp (C : Circuit) (n : ℕ) (x : Fin n → Bool) (a : Fin n) : (C.wires (List.ofFn x)).getD ↑a false = x a := by
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem erase_app (n : ℕ) (G L : List Gate) (g : Gate) (o p : ℕ) : PEqualNP.CircuitMoves.eraseGate n ⟨G ++ (L ++ [g]), o⟩ (G.length + L.length) p = ⟨G ++ L, PEqualNP.CircuitMoves.eraseRedirect n (G.length + L.length) p o⟩ := by
  have h : (G ++ (L ++ [g])) = (G ++ L) ++ [g] := by simp
  have hl : G.length + L.length = (G ++ L).length := by simp
  rw [h, hl]
  generalize G ++ L = M
  unfold PEqualNP.CircuitMoves.eraseGate
  simp

theorem step_eq (n : ℕ) (G L : List Gate) (g : Gate) (C C' : Circuit) (p m : ℕ) (hm : m = G.length + L.length) (hC : C.gates = G ++ (L ++ [g])) (hC' : C'.gates = G ++ L) (ho : PEqualNP.CircuitMoves.eraseRedirect n m p C.output = C'.output) : C' = PEqualNP.CircuitMoves.eraseGate n C m p := by
  subst hm
  cases C
  cases C'
  simp only at hC hC' ho
  subst hC hC'
  rw [erase_app, ho]

theorem drop_nil (G L : List Gate) (m : ℕ) (h : G.length + L.length ≤ m) : List.drop m (G ++ L) = [] := by
  apply List.drop_eq_nil_of_le
  simp
  omega

def Cs (n : ℕ) (C : Circuit) (a3 a4 a5 a6 a7 a8 : ℕ) (k : ℕ) : Circuit :=
  ⟨C.gates ++ (ng (n + C.gates.length) C.output a3 a4 a5 a6 a7 a8).take (7 - k), match k with
    | 0 => n + C.gates.length + 6
    | 1 => n + C.gates.length + 5
    | _ => C.output⟩

theorem Cs_wires (n : ℕ) (C : Circuit) (a3 a4 a5 a6 a7 a8 : ℕ) (k : ℕ) (x : List Bool) : (Cs n C a3 a4 a5 a6 a7 a8 k).wires x = ((ng (n + C.gates.length) C.output a3 a4 a5 a6 a7 a8).take (7 - k)).foldl st (C.wires x) :=
  wires_app C _ _ x

theorem helper : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 x7 x8 : Fin x1),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.output < x1 + x2.size →       ∃ (x11 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo (x11 (0 : ℕ)) ∧           (x11 (0 : ℕ)).size = x2.size + (7 : ℕ) ∧             (∀ (x12 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 (x11 (0 : ℕ)) x12 = (PEqualNP.MetaComplexity.circuitFun x1 x2 x12 || x12 x3 && (x12 x4 || x12 x5 || x12 x6) || x12 x4 && (x12 x7 || x12 x8))) ∧               ∀ x12 < (7 : ℕ),                 ∃ (x14 : ℕ) (x15 : ℕ),                   x14 < (x11 x12).size ∧                     (x15 < x1 + x14 ∨ x1 + (x11 x12).size ≤ x15) ∧                       x11 (x12 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x11 x12) x14 x15 ∧                         ((∀ (x16 : Fin x1 → Bool),                             have x17 : List Bool := (x11 x12).wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false));                             x17.getD (x1 + x14) Bool.false = x17.getD x15 Bool.false) ∨                           (x11 x12).output ≠ x1 + x14 ∧ ∀ x16 ∈ List.drop (x14 + (1 : ℕ)) (x11 x12).gates, x1 + x14 ∉ x16.inputs) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hF ho
  have ho' : x2.output < x1 + x2.gates.length := ho
  have i3 := x3.isLt
  have i4 := x4.isLt
  have i5 := x5.isLt
  have i6 := x6.isLt
  have i7 := x7.isLt
  have i8 := x8.isLt
  refine ⟨(Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8), ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ x2.gates ++ (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) := hg
    rcases List.mem_append.mp hg' with h | h
    · exact hF g h
    · simp [ng] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · show (x2.gates ++ (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length = x2.gates.length + 7
    simp [ng]
  · intro x12
    have key := chain (x2.wires (List.ofFn x12)) (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8 (by rw [wires_len]; simp) ho' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    show (((Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) 0).wires (List.ofFn x12)).getD (x1 + x2.gates.length + 6) false = _
    rw [Cs_wires]
    refine key.1.trans ?_
    simp only [inp]
    rfl
  · intro k hk
    interval_cases k
    · refine ⟨x2.gates.length + 6, x1 + x2.gates.length + 5, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 6 < (x2.gates ++ List.take 7 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 6 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.or, [(x1 + x2.gates.length) + 5, (x1 + x2.gates.length) + 4]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 7 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 6 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 6) (x1 + x2.gates.length + 5) (x1 + x2.gates.length + 6) = x1 + x2.gates.length + 5
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · left
        intro x16
        have key := chain (x2.wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false))) (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8 (by rw [wires_len]; simp) ho' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hb : (x2.wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false))).getD ↑x4 false = false := by
          rw [inp]
          simp
        show (((Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) 0).wires _).getD (x1 + (x2.gates.length + 6)) false = (((Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) 0).wires _).getD (x1 + x2.gates.length + 5) false
        rw [Cs_wires, show x1 + (x2.gates.length + 6) = x1 + x2.gates.length + 6 by omega]
        exact key.2.1 hb
    · refine ⟨x2.gates.length + 5, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 5 < (x2.gates ++ List.take 6 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 5 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.or, [x2.output, (x1 + x2.gates.length) + 2]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 6 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 5 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 5) (x2.output) (x1 + x2.gates.length + 5) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · left
        intro x16
        have key := chain (x2.wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false))) (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8 (by rw [wires_len]; simp) ho' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hb : (x2.wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false))).getD ↑x3 false = false := by
          rw [inp]
          simp [Function.update_apply]
        show (((Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) 1).wires _).getD (x1 + (x2.gates.length + 5)) false = (((Cs x1 x2 ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) 1).wires _).getD x2.output false
        rw [Cs_wires, show x1 + (x2.gates.length + 5) = x1 + x2.gates.length + 5 by omega]
        exact key.2.2 hb
    · refine ⟨x2.gates.length + 4, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 4 < (x2.gates ++ List.take 5 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 4 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.and, [↑x4, (x1 + x2.gates.length) + 3]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 5 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 4 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 4) (x2.output) (x2.output) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · right
        refine ⟨?_, ?_⟩
        · show x2.output ≠ x1 + (x2.gates.length + 4)
          omega
        · intro g hg
          have hg' : g ∈ List.drop (x2.gates.length + 4 + 1) (x2.gates ++ List.take 5 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) := hg
          rw [drop_nil x2.gates _ _ (by simp [ng])] at hg'
          exact absurd hg' List.not_mem_nil
    · refine ⟨x2.gates.length + 3, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 3 < (x2.gates ++ List.take 4 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 3 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.or, [↑x7, ↑x8]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 4 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 3 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 3) (x2.output) (x2.output) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · right
        refine ⟨?_, ?_⟩
        · show x2.output ≠ x1 + (x2.gates.length + 3)
          omega
        · intro g hg
          have hg' : g ∈ List.drop (x2.gates.length + 3 + 1) (x2.gates ++ List.take 4 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) := hg
          rw [drop_nil x2.gates _ _ (by simp [ng])] at hg'
          exact absurd hg' List.not_mem_nil
    · refine ⟨x2.gates.length + 2, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 2 < (x2.gates ++ List.take 3 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 2 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.and, [↑x3, (x1 + x2.gates.length) + 1]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 3 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 2 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 2) (x2.output) (x2.output) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · right
        refine ⟨?_, ?_⟩
        · show x2.output ≠ x1 + (x2.gates.length + 2)
          omega
        · intro g hg
          have hg' : g ∈ List.drop (x2.gates.length + 2 + 1) (x2.gates ++ List.take 3 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) := hg
          rw [drop_nil x2.gates _ _ (by simp [ng])] at hg'
          exact absurd hg' List.not_mem_nil
    · refine ⟨x2.gates.length + 1, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 1 < (x2.gates ++ List.take 2 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 1 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.or, [(x1 + x2.gates.length), ↑x6]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 2 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 1 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 1) (x2.output) (x2.output) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · right
        refine ⟨?_, ?_⟩
        · show x2.output ≠ x1 + (x2.gates.length + 1)
          omega
        · intro g hg
          have hg' : g ∈ List.drop (x2.gates.length + 1 + 1) (x2.gates ++ List.take 2 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) := hg
          rw [drop_nil x2.gates _ _ (by simp [ng])] at hg'
          exact absurd hg' List.not_mem_nil
    · refine ⟨x2.gates.length + 0, x2.output, ?_, ?_, ?_, ?_⟩
      · show x2.gates.length + 0 < (x2.gates ++ List.take 1 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)).length
        simp [ng]
      · left
        omega
      · refine step_eq x1 x2.gates (List.take 0 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) ⟨GateOp.or, [↑x4, ↑x5]⟩ _ _ _ _ (by simp [ng]) ?_ ?_ ?_
        · show x2.gates ++ List.take 1 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          simp [ng]
        · show x2.gates ++ List.take 0 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8) = _
          rfl
        · show PEqualNP.CircuitMoves.eraseRedirect x1 (x2.gates.length + 0) (x2.output) (x2.output) = x2.output
          unfold PEqualNP.CircuitMoves.eraseRedirect
          split_ifs <;> first | rfl | omega
      · right
        refine ⟨?_, ?_⟩
        · show x2.output ≠ x1 + (x2.gates.length + 0)
          omega
        · intro g hg
          have hg' : g ∈ List.drop (x2.gates.length + 0 + 1) (x2.gates ++ List.take 1 (ng (x1 + x2.gates.length) x2.output ↑x3 ↑x4 ↑x5 ↑x6 ↑x7 ↑x8)) := hg
          rw [drop_nil x2.gates _ _ (by simp [ng])] at hg'
          exact absurd hg' List.not_mem_nil

end PEqualNP.Outside.L_meta_6466

theorem PEqualNP.Outside.L_meta_6466 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 x7 x8 : Fin x1),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.output < x1 + x2.size →       ∃ (x11 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo (x11 (0 : ℕ)) ∧           (x11 (0 : ℕ)).size = x2.size + (7 : ℕ) ∧             (∀ (x12 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 (x11 (0 : ℕ)) x12 = (PEqualNP.MetaComplexity.circuitFun x1 x2 x12 || x12 x3 && (x12 x4 || x12 x5 || x12 x6) || x12 x4 && (x12 x7 || x12 x8))) ∧               ∀ x12 < (7 : ℕ),                 ∃ (x14 : ℕ) (x15 : ℕ),                   x14 < (x11 x12).size ∧                     (x15 < x1 + x14 ∨ x1 + (x11 x12).size ≤ x15) ∧                       x11 (x12 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x11 x12) x14 x15 ∧                         ((∀ (x16 : Fin x1 → Bool),                             have x17 : List Bool := (x11 x12).wires (List.ofFn (Function.update (Function.update x16 x3 Bool.false) x4 Bool.false));                             x17.getD (x1 + x14) Bool.false = x17.getD x15 Bool.false) ∨                           (x11 x12).output ≠ x1 + x14 ∧ ∀ x16 ∈ List.drop (x14 + (1 : ℕ)) (x11 x12).gates, x1 + x14 ∉ x16.inputs) :=
  PEqualNP.Outside.L_meta_6466.helper
