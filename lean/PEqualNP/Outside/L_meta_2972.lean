import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2972

def run {α : Type} (F : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) init

lemma run_cons {α : Type} (F : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    run F (g :: gs) init = run F gs (init ++ [F init g]) := rfl

lemma run_append {α : Type} (F : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    run F (gs ++ hs) init = run F hs (run F gs init) := by
  unfold run; rw [List.foldl_append]

lemma run_length {α : Type} (F : List α → Gate → α) (gs : List Gate) :
    ∀ init : List α, (run F gs init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp [run]
  | cons g gs ih => intro init; rw [run_cons, ih]; simp; omega

lemma run_getD_lt {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (i : ℕ), i < init.length → (run F gs init).getD i d = init.getD i d := by
  induction gs with
  | nil => intro init i _; rfl
  | cons g gs ih =>
    intro init i hi
    rw [run_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_getD_gate {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (j : ℕ) (g : Gate), gs[j]? = some g →
      (run F gs init).getD (init.length + j) d = F (run F (gs.take j) init) g := by
  induction gs with
  | nil => intro init j g h; simp at h
  | cons g0 gs ih =>
    intro init j g h
    cases j with
    | zero =>
      simp at h
      subst h
      rw [run_cons, run_getD_lt F d gs _ _ (by simp)]
      simp [run]
    | succ j =>
      simp at h
      rw [run_cons]
      have h1 := ih (init ++ [F init g0]) j g h
      simp only [List.length_append, List.length_singleton] at h1
      rw [show init.length + (j + 1) = init.length + 1 + j by omega, h1]
      simp [run_cons]

lemma run_take_getD {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) :
    (run F (gs.take j) init).getD i d = (run F gs init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  rw [run_getD_lt F d (gs.drop j) (run F (gs.take j) init) i
    (by rw [run_length, List.length_take, Nat.min_eq_left hj]; exact hi)]

def lpF (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  match g.op with
  | GateOp.or => ((g.inputs.map fun i => w.getD i (false, false)).any (·.1),
      (g.inputs.map fun i => w.getD i (false, false)).any (·.2))
  | GateOp.and => (g.inputs.map fun i => w.getD i (false, false)).foldl
      (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lpInit (N : ℕ) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if (decide (i < N)) then (false, b) else (b, false)

lemma linearParts_eq (C : Circuit) (N : ℕ) (x : List Bool) :
    PEqualNP.ReadK.linearParts C (fun i => decide (i < N)) x = run lpF C.gates (lpInit N x) := rfl

def wvF (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = run wvF C.gates x := rfl

def xs (N : ℕ) (x : ℕ → Bool) : List Bool := (List.range (N + N)).map x

def pP (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C (fun i => decide (i < N)) (xs N x)).getD w (false, false)

def pA (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).1

def pB (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).2

def pV (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (C.wires (xs N x)).getD w false

lemma lpInit_length (N : ℕ) (x : List Bool) : (lpInit N x).length = x.length := by
  simp [lpInit]

lemma xs_length (N : ℕ) (x : ℕ → Bool) : (xs N x).length = N + N := by simp [xs]

lemma pP_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pP C N x w = if w < N then (false, x w) else (x w, false) := by
  unfold pP
  rw [linearParts_eq, run_getD_lt _ _ _ _ _ (by rw [lpInit_length, xs_length]; exact hw)]
  simp [lpInit, xs, List.getD_eq_getElem?_getD, hw]

lemma pV_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pV C N x w = x w := by
  unfold pV
  rw [wires_eq, run_getD_lt _ _ _ _ _ (by rw [xs_length]; exact hw)]
  simp [xs, List.getD_eq_getElem?_getD, hw]

lemma pP_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pP C N x w = (false, false) := by
  unfold pP
  rw [linearParts_eq]
  apply List.getD_eq_default
  rw [run_length, lpInit_length, xs_length]; exact hw

lemma pV_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pV C N x w = false := by
  unfold pV
  rw [wires_eq]
  apply List.getD_eq_default
  rw [run_length, xs_length]; exact hw

lemma pP_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pP C N x (N + N + j) = lpF [pP C N x a, pP C N x b] ⟨op, [0, 1]⟩ := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (lpInit N (xs N x)).length = N + N := by rw [lpInit_length, xs_length]
  unfold pP
  rw [linearParts_eq]
  have h1 := run_getD_gate lpF (false, false) C.gates (lpInit N (xs N x)) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  cases op <;> simp [lpF, ea, eb]

lemma pV_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pV C N x (N + N + j) = op.eval [pV C N x a, pV C N x b] := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (xs N x).length = N + N := xs_length N x
  unfold pV
  rw [wires_eq]
  have h1 := run_getD_gate wvF false C.gates (xs N x) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD wvF false C.gates (xs N x) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD wvF false C.gates (xs N x) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  simp [wvF, ea, eb]

def Good (C : Circuit) (N : ℕ) : Prop :=
  (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
  (∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j) ∧
  ∀ g ∈ C.gates, g.inputs.length = 2

lemma gate_view (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < N + N + j ∧ b < N + N + j ∧
      (C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∨ C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) := by
  obtain ⟨h1, h2, h3⟩ := hG
  have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have e1 := h1 _ hm
  have e2 := h2 j hj
  have e3 := h3 _ hm
  rw [List.getD_eq_getElem _ _ hj] at e2
  rcases hgj : C.gates[j] with ⟨op, ins⟩
  rw [hgj] at e1 e2 e3
  simp only at e1 e2 e3
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp e3
  refine ⟨a, b, e2 a (by simp), e2 b (by simp), ?_⟩
  rw [List.getElem?_eq_getElem hj, hgj]
  rcases e1 with e1 | e1
  · right; rw [e1]
  · left; rw [e1]

lemma wire_kind (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) :
    w < N ∨ (N ≤ w ∧ w < N + N) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) ∨
    N + N + C.gates.length ≤ w := by
  by_cases h1 : w < N
  · exact Or.inl h1
  by_cases h2 : w < N + N
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  by_cases h3 : N + N + C.gates.length ≤ w
  · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  obtain ⟨a, b, ha, hb, h⟩ := gate_view C N hG (w - (N + N)) (by omega)
  have e : w = N + N + (w - (N + N)) := by omega
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩)))

lemma ev_pt (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N) :
    pA C N x w = false ∧ pB C N x w = x w ∧ pV C N x w = x w := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w (by omega), hw]
  · simp [pB, pP_input C N x w (by omega), hw]
  · exact pV_input C N x w (by omega)

lemma ev_ln (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    pA C N x w = x w ∧ pB C N x w = false ∧ pV C N x w = x w := by
  have h3 : ¬ w < N := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w h2, h3]
  · simp [pB, pP_input C N x w h2, h3]
  · exact pV_input C N x w h2

lemma ev_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pA C N x w = false ∧ pB C N x w = false ∧ pV C N x w = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_out C N x w hw]
  · simp [pB, pP_out C N x w hw]
  · exact pV_out C N x w hw

lemma ev_or (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a || pA C N x b) ∧
    pB C N x (N + N + j) = (pB C N x a || pB C N x b) ∧
    pV C N x (N + N + j) = (pV C N x a || pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma ev_and (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a && pA C N x b) ∧
    pB C N x (N + N + j) = ((pA C N x a && pB C N x b) || (pB C N x a && pA C N x b)) ∧
    pV C N x (N + N + j) = (pV C N x a && pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pA, pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma pA_mono (C : Circuit) (N : ℕ) (hG : Good C N) (x x' : ℕ → Bool)
    (hx : ∀ i, N ≤ i → x i = true → x' i = true) :
    ∀ w, pA C N x w = true → pA C N x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · rw [(ev_pt C N x w h).1]; simp
    · rw [(ev_ln C N x w h1 h2).1, (ev_ln C N x' w h1 h2).1]; exact hx w h1
    · rw [(ev_or C N x j a b hg ha hb).1, (ev_or C N x' j a b hg ha hb).1]
      simp only [Bool.or_eq_true]
      rintro (h | h)
      · exact Or.inl (ih a ha h)
      · exact Or.inr (ih b hb h)
    · rw [(ev_and C N x j a b hg ha hb).1, (ev_and C N x' j a b hg ha hb).1]
      simp only [Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      exact ⟨ih a ha h1, ih b hb h2⟩
    · rw [(ev_out C N x w h).1]; simp

lemma parts_le_val (C : Circuit) (N : ℕ) (hG : Good C N) (x : ℕ → Bool) :
    ∀ w, (pA C N x w = true ∨ pB C N x w = true) → pV C N x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · obtain ⟨e1, e2, e3⟩ := ev_pt C N x w h
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_ln C N x w h1 h2
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_or C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_and C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true, Bool.and_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_out C N x w h
      rw [e1, e2, e3]; simp

def inp (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 1 else 0) 0

def sib (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 0 else 1) 0

def isAnd (C : Circuit) (j : ℕ) : Prop := ∃ a b, C.gates[j]? = some ⟨GateOp.and, [a, b]⟩

def side (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  isAnd C j → pA C N P (sib C j s) = true

def ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) : ℕ → ℕ → Prop
  | 0, w => w = C.output
  | k + 1, w => ∃ j s, j < C.gates.length ∧ w = inp C j s ∧ ctx C N P k (N + N + j) ∧
      side C N P j s

def Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) : Prop := ∃ k, ctx C N P k w

def term (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  j < C.gates.length ∧ Ctx C N P (N + N + j) ∧ side C N P j s

lemma inp_sib (C : Circuit) (j : ℕ) (op : GateOp) (a b : ℕ)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) :
    inp C j false = a ∧ inp C j true = b ∧ sib C j false = b ∧ sib C j true = a := by
  simp [inp, sib, List.getD_eq_getElem?_getD, hg]

lemma inp_lt (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (s : Bool) (hj : j < C.gates.length) :
    inp C j s < N + N + j := by
  obtain ⟨a, b, ha, hb, hg⟩ := gate_view C N hG j hj
  rcases hg with hg | hg
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb

lemma not_isAnd_of_or (C : Circuit) (j a b : ℕ) (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) :
    ¬ isAnd C j := by
  rintro ⟨a', b', h'⟩
  rw [hg] at h'
  simp at h'

lemma Ctx_out (C : Circuit) (N : ℕ) (P : ℕ → Bool) : Ctx C N P C.output := ⟨0, by simp [ctx]⟩

lemma Ctx_cases (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) (h : Ctx C N P w) :
    w = C.output ∨ ∃ j s, w = inp C j s ∧ term C N P j s := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => left; simpa [ctx] using hk
  | succ k =>
    simp only [ctx] at hk
    obtain ⟨j, s, hj, hw, hc, hs⟩ := hk
    exact Or.inr ⟨j, s, hw, hj, ⟨k, hc⟩, hs⟩

lemma term_to_Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool)
    (h : term C N P j s) : Ctx C N P (inp C j s) := by
  obtain ⟨hj, ⟨k, hk⟩, hs⟩ := h
  refine ⟨k + 1, ?_⟩
  simp only [ctx]
  exact ⟨j, s, hj, rfl, hk, hs⟩

lemma sib_inp (C : Circuit) (j : ℕ) (s : Bool) : sib C j s = inp C j (!s) := by
  cases s <;> rfl

lemma ctx_mono (C : Circuit) (N : ℕ) (hG : Good C N) (P P' : ℕ → Bool)
    (h : ∀ i, N ≤ i → P i = true → P' i = true) :
    ∀ k w, ctx C N P k w → ctx C N P' k w := by
  intro k
  induction k with
  | zero => intro w hw; simpa [ctx] using hw
  | succ k ih =>
    intro w hw
    simp only [ctx] at hw ⊢
    obtain ⟨j, s, hj, e, hc, hs⟩ := hw
    exact ⟨j, s, hj, e, ih _ hc, fun ha => pA_mono C N hG P P' h _ (hs ha)⟩

def xin (P : ℕ → Bool) (l : ℕ) : ℕ → Bool := fun i => P i || i == l

lemma ctx_B (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool) (l : ℕ) :
    ∀ k w, ctx C N P k w → pB C N (xin P l) w = true → pB C N (xin P l) C.output = true := by
  intro k
  induction k with
  | zero =>
    intro w h hb
    simp only [ctx] at h
    rw [← h]; exact hb
  | succ k ih =>
    intro w h hb
    simp only [ctx] at h
    obtain ⟨j, s, hj, hw, hc, hs⟩ := h
    apply ih _ hc
    obtain ⟨a, b, ha, hb', hg⟩ := gate_view C N hG j hj
    rcases hg with hg | hg
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      rw [(ev_or C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; simp [hb]
      · rw [hw, e2] at hb; simp [hb]
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hs' := pA_mono C N hG P (xin P l) (by intro i _ h; simp [xin, h]) _ (hs ⟨a, b, hg⟩)
      rw [(ev_and C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; rw [e3] at hs'; simp [hb, hs']
      · rw [hw, e2] at hb; rw [e4] at hs'; simp [hb, hs']

lemma B_ctx (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool)
    (hP : ∀ i, P i = true → N ≤ i) (p : ℕ) (hp : p < N) :
    ∀ w, Ctx C N P w → pB C N (xin P p) w = true → Ctx C N P p := by
  have hmono : ∀ c, pA C N (xin P p) c = true → pA C N P c = true := by
    intro c
    apply pA_mono C N hG (xin P p) P
    intro i hi h
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact h
    · omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hc hb
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · rw [(ev_pt C N _ w h).2.1] at hb
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb | hb
      · exact absurd (hP w hb) (by omega)
      · rw [← hb]; exact hc
    · rw [(ev_ln C N _ w h1 h2).2.1] at hb; simp at hb
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hns := not_isAnd_of_or C j a b hg
      rw [(ev_or C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · apply ih a ha _ hb
        rw [← e1]; exact term_to_Ctx C N P j false ⟨hj, hc, fun h => absurd h hns⟩
      · apply ih b hb' _ hb
        rw [← e2]; exact term_to_Ctx C N P j true ⟨hj, hc, fun h => absurd h hns⟩
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      rw [(ev_and C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply ih b hb' _ h2
        rw [← e2]
        exact term_to_Ctx C N P j true ⟨hj, hc, fun _ => by rw [e4]; exact hmono a h1⟩
      · apply ih a ha _ h1
        rw [← e1]
        exact term_to_Ctx C N P j false ⟨hj, hc, fun _ => by rw [e3]; exact hmono b h2⟩
    · rw [(ev_out C N _ w h).2.1] at hb; simp at hb

lemma ofFn_xs (N : ℕ) (x : ℕ → Bool) : List.ofFn (fun i : Fin (N + N) => x i) = xs N x := by
  apply List.ext_getElem <;> simp [xs]

def inL (N : ℕ) (L : Finset (Fin N)) : ℕ → Bool :=
  fun i => decide (∃ l ∈ L, i = N + (l : ℕ))

lemma inL_supp (N : ℕ) (L : Finset (Fin N)) (i : ℕ) (h : inL N L i = true) : N ≤ i := by
  simp only [inL, decide_eq_true_eq] at h
  obtain ⟨l, _, e⟩ := h
  omega

lemma inL_mono (N : ℕ) (L L' : Finset (Fin N)) (h : L ⊆ L') (i : ℕ)
    (hi : inL N L i = true) : inL N L' i = true := by
  simp only [inL, decide_eq_true_eq] at hi ⊢
  obtain ⟨l, hl, e⟩ := hi
  exact ⟨l, h hl, e⟩

lemma inL_mem (N : ℕ) (L : Finset (Fin N)) (a : Fin N) (h : inL N L (N + (a : ℕ)) = true) :
    a ∈ L := by
  simp only [inL, decide_eq_true_eq] at h
  obtain ⟨l, hl, e⟩ := h
  have e' : a = l := Fin.ext (by omega)
  rw [e']; exact hl

def AL (C : Circuit) (N : ℕ) (w : ℕ) : Finset (Fin N) → Prop :=
  fun L => pA C N (inL N L) w = true

def CL (C : Circuit) (N : ℕ) (w : ℕ) : Finset (Fin N) → Prop :=
  fun L => Ctx C N (inL N L) w

def TL (C : Circuit) (N : ℕ) (j : ℕ) (s : Bool) : Finset (Fin N) → Prop :=
  fun L => term C N (inL N L) j s

def MonoL (N : ℕ) (φ : Finset (Fin N) → Prop) : Prop :=
  ∀ L L' : Finset (Fin N), L ⊆ L' → φ L → φ L'

lemma mono_AL (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) : MonoL N (AL C N w) :=
  fun L L' h hf => pA_mono C N hG (inL N L) (inL N L')
    (fun i _ hi => inL_mono N L L' h i hi) w hf

lemma mono_CL (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) : MonoL N (CL C N w) :=
  fun L L' h hf => by
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, ctx_mono C N hG (inL N L) (inL N L')
      (fun i _ hi => inL_mono N L L' h i hi) k w hk⟩

lemma ctx_sound (C : Circuit) (N q : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (hS : ∀ (x11 : Fin (N + N) → Bool),
      Fintype.card { x12 : Fin N // x11 (Fin.natAdd N x12) = Bool.true } ≤ q →
      (¬∃ (x13 : Fin N) (x14 : Fin N), I x13 x14 ∧ x11 (Fin.castAdd N x13) = Bool.true ∧
        x11 (Fin.natAdd N x14) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x11 = Bool.false)
    (p : Fin N) (L : Finset (Fin N)) (hc : L.card ≤ q) (h : CL C N p L) :
    ∃ l ∈ L, I p l := by
  have hB : pB C N (xin (inL N L) p) C.output = true := by
    obtain ⟨k, hk⟩ := h
    apply ctx_B C N hG (inL N L) p k p hk
    rw [(ev_pt C N _ p p.isLt).2.1]
    simp [xin]
  have hV := parts_le_val C N hG _ C.output (Or.inr hB)
  by_contra hne
  have hline : ∀ a : Fin N, xin (inL N L) p (N + (a : ℕ)) = true → a ∈ L := by
    intro a ha
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with ha | ha
    · exact inL_mem N L a ha
    · have := p.isLt; omega
  have h0 := hS (fun i => xin (inL N L) p i) (by
      refine le_trans ?_ hc
      rw [← Fintype.card_coe L]
      apply Fintype.card_le_of_injective
        (fun x : { x12 : Fin N // xin (inL N L) p (Fin.natAdd N x12) = Bool.true } =>
          (⟨x.1, hline x.1 (by have h' := x.2; simpa only [Fin.val_natAdd] using h')⟩ :
            { a // a ∈ L }))
      intro x y e
      apply Subtype.ext
      exact congrArg (fun z : { a // a ∈ L } => z.1) e) (by
      rintro ⟨p', l', hinc, hp', hl'⟩
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hp' hl'
      have hl'L := hline l' hl'
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hp'
      rcases hp' with hp' | hp'
      · have h1 := inL_supp N L _ hp'
        have h2 := p'.isLt
        omega
      · have e : p' = p := Fin.ext hp'
        rw [e] at hinc
        exact hne ⟨l', hl'L, hinc⟩)
  have h1 : pV C N (xin (inL N L) p) C.output = false := by
    unfold pV
    rw [← ofFn_xs]
    exact h0
  rw [h1] at hV
  simp at hV

lemma ls_eq (C : Circuit) (N : ℕ) (p l : Fin N)
    (h : PEqualNP.ReadK.lineSingle C (N + N) (fun x13 => decide (x13 < N)) p (N + l) = true) :
    pB C N (xin (inL N {l}) p) C.output = true := by
  have hf : (fun i : ℕ => (i == (p : ℕ) || i == N + (l : ℕ))) = xin (inL N {l}) p := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [xin, inL, or_comm]
  unfold PEqualNP.ReadK.lineSingle at h
  rw [hf] at h
  exact h

def Below1 (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) : Prop :=
  ∀ L : Finset (Fin N), L.card ≤ 1 → φ L → ∃ l ∈ L, I p l

lemma below1_single (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (h : Below1 N I φ p) (l : Fin N) (hl : φ {l}) : I p l := by
  obtain ⟨l', h1, h2⟩ := h {l} (by simp) hl
  rw [Finset.mem_singleton] at h1
  rw [← h1]; exact h2

lemma owner_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (φ : Finset (Fin N) → Prop) (p p' : Fin N) (h : Below1 N I φ p) (h' : Below1 N I φ p')
    (l1 l2 : Fin N) (hne : l1 ≠ l2) (h1 : φ {l1}) (h2 : φ {l2}) : p = p' := by
  by_contra hp
  obtain ⟨m, _, hm⟩ := hU p p' hp
  have e1 := hm l1 ⟨below1_single N I φ p h l1 h1, below1_single N I φ p' h' l1 h1⟩
  have e2 := hm l2 ⟨below1_single N I φ p h l2 h2, below1_single N I φ p' h' l2 h2⟩
  exact hne (e1.trans e2.symm)

noncomputable def wit (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop)
    (p : Fin N) : Finset (Fin N) := by
  classical
  exact if h : ∃ a, ¬ I p a ∧ φ {a} then {Classical.choose h} else ∅

lemma wit_card (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) :
    (wit N I φ p).card ≤ 1 := by
  classical
  unfold wit
  split_ifs <;> simp

lemma wit_avoid (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (a : Fin N) (ha : a ∈ wit N I φ p) : ¬ I p a := by
  classical
  unfold wit at ha
  split_ifs at ha with h
  · rw [Finset.mem_singleton] at ha
    rw [ha]; exact (Classical.choose_spec h).1
  · simp at ha

lemma wit_accept (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (hm : MonoL N φ) (hb : ¬ Below1 N I φ p) (L' : Finset (Fin N))
    (hL : wit N I φ p ⊆ L') : φ L' := by
  classical
  unfold Below1 at hb
  rw [not_forall] at hb
  obtain ⟨L, hb⟩ := hb
  rw [Classical.not_imp] at hb
  obtain ⟨hc, hb⟩ := hb
  rw [Classical.not_imp] at hb
  obtain ⟨hφ, hno⟩ := hb
  rcases Nat.eq_zero_or_pos L.card with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at hφ
    exact hm ∅ L' (Finset.empty_subset _) hφ
  · have h1 : L.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have hex : ∃ a, ¬ I p a ∧ φ {a} :=
      ⟨a, fun hI => hno ⟨a, Finset.mem_singleton_self a, hI⟩, hφ⟩
    unfold wit at hL
    split_ifs at hL
    exact hm _ L' hL (Classical.choose_spec hex).2

def Owned (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) : Prop :=
  Below1 N I φ p ∧ ∃ l1 l2 : Fin N, l1 ≠ l2 ∧ φ {l1} ∧ φ {l2}

def Owns (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) : Prop :=
  (τ.2 = true ∧ Owned N I (AL C N (N + N + (τ.1 : ℕ))) p) ∨
  (τ.2 = false ∧ Owned N I (CL C N (N + N + (τ.1 : ℕ))) p)

lemma owns_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p p' : Fin N) (τ : Fin C.gates.length × Bool)
    (h : Owns C N I p τ) (h' : Owns C N I p' τ) : p = p' := by
  rcases h with ⟨e, hb, l1, l2, hne, h1, h2⟩ | ⟨e, hb, l1, l2, hne, h1, h2⟩
  · rcases h' with ⟨e', hb', _⟩ | ⟨e', _⟩
    · exact owner_unique N I hU _ p p' hb hb' l1 l2 hne h1 h2
    · rw [e] at e'; simp at e'
  · rcases h' with ⟨e', _⟩ | ⟨e', hb', _⟩
    · rw [e] at e'; simp at e'
    · exact owner_unique N I hU _ p p' hb hb' l1 l2 hne h1 h2

noncomputable def ownedSet (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    Finset (Fin C.gates.length × Bool) := by
  classical
  exact Finset.univ.filter (fun τ => Owns C N I p τ)

lemma mem_ownedSet (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) : τ ∈ ownedSet C N I p ↔ Owns C N I p τ := by
  classical
  unfold ownedSet
  simp

noncomputable def Lstar (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    Finset (Fin N) :=
  (ownedSet C N I p).biUnion (fun τ =>
    wit N I (AL C N (inp C τ.1 false)) p ∪ wit N I (AL C N (inp C τ.1 true)) p)

lemma Lstar_card (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    (Lstar C N I p).card ≤ 2 * (ownedSet C N I p).card := by
  unfold Lstar
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 2 ?_) ?_
  · intro τ _
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := wit_card N I (AL C N (inp C τ.1 false)) p
    have h2 := wit_card N I (AL C N (inp C τ.1 true)) p
    omega
  · simp [mul_comm]

lemma Lstar_avoid (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) (a : Fin N)
    (ha : a ∈ Lstar C N I p) : ¬ I p a := by
  unfold Lstar at ha
  rw [Finset.mem_biUnion] at ha
  obtain ⟨τ, _, ha⟩ := ha
  rw [Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact wit_avoid N I _ p a ha
  · exact wit_avoid N I _ p a ha

lemma Lstar_sub (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) (h : Owns C N I p τ) (s : Bool) :
    wit N I (AL C N (inp C τ.1 s)) p ⊆ Lstar C N I p := by
  intro a ha
  unfold Lstar
  rw [Finset.mem_biUnion]
  refine ⟨τ, (mem_ownedSet C N I p τ).mpr h, ?_⟩
  rw [Finset.mem_union]
  cases s
  · exact Or.inl ha
  · exact Or.inr ha

def RA (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (j : ℕ) (s : Bool) :
    Prop :=
  Below1 N I (AL C N (N + N + j)) p ∧ AL C N (N + N + j) {l} ∧
  (∃ l1, l1 ≠ l ∧ AL C N (N + N + j) {l1}) ∧
  AL C N (inp C j s) {l} ∧ ∀ l', AL C N (inp C j s) {l'} → l' = l

def RC (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (j : ℕ) (s : Bool) :
    Prop :=
  Below1 N I (CL C N (inp C j s)) p ∧ CL C N (inp C j s) {l} ∧
  ((∃ l1, l1 ≠ l ∧ CL C N (inp C j s) {l1}) ∨ inp C j s = (p : ℕ)) ∧
  TL C N j s {l} ∧ ∀ l', TL C N j s {l'} → l' = l

lemma RA_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (j : ℕ) (s : Bool)
    (h : RA C N I p l j s) (h' : RA C N I p' l' j s) : p = p' ∧ l = l' := by
  obtain ⟨b, a1, ⟨l1, hne, a2⟩, c1, u⟩ := h
  obtain ⟨b', a1', _, c1', u'⟩ := h'
  exact ⟨owner_unique N I hU _ p p' b b' l1 l hne a2 a1, u' l c1⟩

lemma RC_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (j : ℕ) (s : Bool)
    (h : RC C N I p l j s) (h' : RC C N I p' l' j s) : p = p' ∧ l = l' := by
  obtain ⟨b, a1, d, c1, u⟩ := h
  obtain ⟨b', a1', d', c1', u'⟩ := h'
  refine ⟨?_, u' l c1⟩
  rcases d with ⟨l1, hne, a2⟩ | e
  · exact owner_unique N I hU _ p p' b b' l1 l hne a2 a1
  · rcases d' with ⟨l1, hne, a2⟩ | e'
    · exact owner_unique N I hU _ p p' b b' l1 l' hne a2 a1'
    · exact Fin.ext (e.symm.trans e')

lemma AL_or (C : Circuit) (N : ℕ) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j)
    (L : Finset (Fin N)) : AL C N (N + N + j) L ↔ (AL C N a L ∨ AL C N b L) := by
  unfold AL
  rw [(ev_or C N (inL N L) j a b hg ha hb).1]
  simp

lemma AL_and (C : Circuit) (N : ℕ) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j)
    (L : Finset (Fin N)) : AL C N (N + N + j) L ↔ (AL C N a L ∧ AL C N b L) := by
  unfold AL
  rw [(ev_and C N (inL N L) j a b hg ha hb).1]
  simp

lemma findA (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    ∀ w, Below1 N I (AL C N w) p → AL C N w {l} → (∃ l1, l1 ≠ l ∧ AL C N w {l1}) →
      (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
      (∀ L', Lstar C N I p ⊆ L' → AL C N w L') := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hb hl hl1
    obtain ⟨l1, hne, hl1⟩ := hl1
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · exfalso
      unfold AL at hl
      rw [(ev_pt C N _ w h).1] at hl
      simp at hl
    · exfalso
      unfold AL at hl hl1
      rw [(ev_ln C N _ w h1 h2).1] at hl hl1
      simp only [inL, Finset.mem_singleton, exists_eq_left, decide_eq_true_eq] at hl hl1
      exact hne (Fin.ext (by omega))
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hor := AL_or C N j a b hg ha hb'
      have key : ∀ (s : Bool) (c : ℕ), inp C j s = c → c < N + N + j →
          (∀ L, AL C N c L → AL C N (N + N + j) L) → AL C N c {l} →
          (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
          (∀ L', Lstar C N I p ⊆ L' → AL C N (N + N + j) L') := by
        intro s c hc hlt hle hcl
        have hbc : Below1 N I (AL C N c) p := fun L hL hf => hb L hL (hle L hf)
        by_cases hu : ∀ l', AL C N c {l'} → l' = l
        · left
          refine ⟨j, s, hj, hb, hl, ⟨l1, hne, hl1⟩, ?_, ?_⟩
          · rw [hc]; exact hcl
          · rw [hc]; exact hu
        · rw [not_forall] at hu
          obtain ⟨l2, hu⟩ := hu
          rw [Classical.not_imp] at hu
          rcases ih c hlt hbc hcl ⟨l2, hu.2, hu.1⟩ with h | h
          · exact Or.inl h
          · exact Or.inr (fun L' hL' => hle L' (h L' hL'))
      rcases (hor {l}).mp hl with hla | hlb
      · exact key false a e1 ha (fun L h => (hor L).mpr (Or.inl h)) hla
      · exact key true b e2 hb' (fun L h => (hor L).mpr (Or.inr h)) hlb
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hand := AL_and C N j a b hg ha hb'
      have hown : Owns C N I p (⟨j, hj⟩, true) :=
        Or.inl ⟨rfl, hb, l, l1, hne.symm, hl, hl1⟩
      have key : ∀ (s : Bool) (c : ℕ), inp C j s = c → c < N + N + j →
          AL C N c {l} → AL C N c {l1} →
          (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
          (∀ L', Lstar C N I p ⊆ L' → AL C N c L') := by
        intro s c hc hlt hcl hcl1
        by_cases hbc : Below1 N I (AL C N c) p
        · exact ih c hlt hbc hcl ⟨l1, hne, hcl1⟩
        · right
          intro L' hL'
          apply wit_accept N I (AL C N c) p (mono_AL C N hG c) hbc L'
          have hs := Lstar_sub C N I p (⟨j, hj⟩, true) hown s
          rw [← hc]
          exact Finset.Subset.trans hs hL'
      obtain ⟨hla, hlb⟩ := (hand {l}).mp hl
      obtain ⟨hl1a, hl1b⟩ := (hand {l1}).mp hl1
      rcases key false a e1 ha hla hl1a with h | h
      · exact Or.inl h
      · rcases key true b e2 hb' hlb hl1b with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun L' hL' => (hand L').mpr ⟨h L' hL', h' L' hL'⟩)
    · exfalso
      unfold AL at hl
      rw [(ev_out C N _ w h).1] at hl
      simp at hl

def Inv (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (w : ℕ) : Prop :=
  Below1 N I (CL C N w) p ∧ CL C N w {l} ∧ ((∃ l1, l1 ≠ l ∧ CL C N w {l1}) ∨ w = (p : ℕ))

def Done (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) : Prop :=
  (∃ j s, j < C.gates.length ∧ RC C N I p l j s) ∨
  (∃ j s, j < C.gates.length ∧ RA C N I p l j s)

def Esc (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) (w : ℕ) : Prop :=
  ∃ E : Finset (Fin N), E.card ≤ 2 ∧ (∀ a ∈ E, ¬ I p a) ∧ CL C N w (Lstar C N I p ∪ E)

lemma walk_step (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (p l : Fin N) (w : ℕ)
    (ih : ∀ j, j < C.gates.length → w < N + N + j → Inv C N I p l (N + N + j) →
      Done C N I p l ∨ Esc C N I p (N + N + j)) :
    Inv C N I p l w → Done C N I p l ∨ Esc C N I p w := by
  rintro ⟨hb, hl, hd⟩
  rcases Ctx_cases C N _ w hl with ho | ⟨j, s, hw, ht⟩
  · exfalso
    obtain ⟨a, ha, _⟩ := hb ∅ (by simp)
      (by show Ctx C N (inL N ∅) w; rw [ho]; exact Ctx_out C N _)
    simp at ha
  · have hj := ht.1
    have hlt : inp C j s < N + N + j := inp_lt C N hG j s hj
    by_cases hu : ∀ l', TL C N j s {l'} → l' = l
    · left; left
      refine ⟨j, s, hj, ?_, ?_, ?_, ht, hu⟩
      · rw [← hw]; exact hb
      · rw [← hw]; exact hl
      · rw [← hw]; exact hd
    · rw [not_forall] at hu
      obtain ⟨l2, hu⟩ := hu
      rw [Classical.not_imp] at hu
      obtain ⟨ht2, hne2⟩ := hu
      have hside : Done C N I p l ∨ ∀ L', Lstar C N I p ∪ wit N I (AL C N (sib C j s)) p ⊆ L' →
          side C N (inL N L') j s := by
        by_cases hand : isAnd C j
        · have hcl : AL C N (sib C j s) {l} := ht.2.2 hand
          have hcl2 : AL C N (sib C j s) {l2} := ht2.2.2 hand
          by_cases hbc : Below1 N I (AL C N (sib C j s)) p
          · rcases findA C N hG I p l (sib C j s) hbc hcl ⟨l2, hne2, hcl2⟩ with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (fun L' hL' _ =>
                h L' (Finset.Subset.trans Finset.subset_union_left hL'))
          · right
            intro L' hL' _
            exact wit_accept N I _ p (mono_AL C N hG _) hbc L'
              (Finset.Subset.trans Finset.subset_union_right hL')
        · exact Or.inr (fun L' _ ha => absurd ha hand)
      rcases hside with hdone | hside
      · exact Or.inl hdone
      by_cases hbg : Below1 N I (CL C N (N + N + j)) p
      · have hown : Owns C N I p (⟨j, hj⟩, false) :=
          Or.inr ⟨rfl, hbg, l, l2, Ne.symm hne2, ht.2.1, ht2.2.1⟩
        have hsub : wit N I (AL C N (sib C j s)) p ⊆ Lstar C N I p := by
          rw [sib_inp]
          exact Lstar_sub C N I p (⟨j, hj⟩, false) hown (!s)
        rcases ih j hj (by omega) ⟨hbg, ht.2.1, Or.inl ⟨l2, hne2, ht2.2.1⟩⟩ with
          h | ⟨E, hE1, hE2, hE3⟩
        · exact Or.inl h
        · right
          refine ⟨E, hE1, hE2, ?_⟩
          show Ctx C N (inL N (Lstar C N I p ∪ E)) w
          rw [hw]
          apply term_to_Ctx C N _ j s
          refine ⟨hj, hE3, hside _ ?_⟩
          exact Finset.union_subset Finset.subset_union_left
            (Finset.Subset.trans hsub Finset.subset_union_left)
      · right
        refine ⟨wit N I (CL C N (N + N + j)) p ∪ wit N I (AL C N (sib C j s)) p, ?_, ?_, ?_⟩
        · refine le_trans (Finset.card_union_le _ _) ?_
          have h1 := wit_card N I (CL C N (N + N + j)) p
          have h2 := wit_card N I (AL C N (sib C j s)) p
          omega
        · intro a ha
          rw [Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact wit_avoid N I _ p a ha
          · exact wit_avoid N I _ p a ha
        · show Ctx C N (inL N _) w
          rw [hw]
          apply term_to_Ctx C N _ j s
          refine ⟨hj, ?_, hside _ ?_⟩
          · exact wit_accept N I _ p (mono_CL C N hG _) hbg _
              (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)
          · exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_right

lemma walk (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    ∀ m w, N + N + C.gates.length ≤ w + m → Inv C N I p l w →
      Done C N I p l ∨ Esc C N I p w := by
  intro m
  induction m with
  | zero =>
    intro w hw
    apply walk_step C N hG I p l w
    intro j hj hlt
    omega
  | succ m ih =>
    intro w hw
    apply walk_step C N hG I p l w
    intro j hj hlt
    exact ih (N + N + j) (by omega)

lemma stuck_bound (C : Circuit) (N q : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q → CL C N p L → ∃ l ∈ L, I p l)
    (hq : 1 ≤ q) (p l : Fin N) (hK : CL C N (p : ℕ) {l}) (hnd : ¬ Done C N I p l) :
    q + 1 ≤ 2 * (ownedSet C N I p).card + 2 := by
  have hinv : Inv C N I p l p :=
    ⟨fun L hL hf => hsound p L (le_trans hL hq) hf, hK, Or.inr rfl⟩
  rcases walk C N hG I p l (N + N + C.gates.length) p (by omega) hinv with
    h | ⟨E, hE1, hE2, hE3⟩
  · exact absurd h hnd
  · by_contra hlt
    have hcard : (Lstar C N I p ∪ E).card ≤ q := by
      have h1 := Finset.card_union_le (Lstar C N I p) E
      have h2 := Lstar_card C N I p
      omega
    obtain ⟨a, ha, hI⟩ := hsound p _ hcard hE3
    rw [Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact Lstar_avoid C N I p a ha hI
    · exact hE2 a ha hI

lemma pencil_le (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ (x8 : Fin N), Fintype.card { x9 : Fin N // I x9 x8 } = q + 1)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p : Fin N) (Lp : Finset (Fin N)) (hLp : ∀ l ∈ Lp, I p l) : Lp.card ≤ q + 1 := by
  have hT : ∀ l ∈ Lp, ((Finset.univ.filter (fun r => I r l)).erase p).card = q := by
    intro l hl
    have hpl : I p l := hLp l hl
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl⟩)]
    have h1 : (Finset.univ.filter (fun r => I r l)).card = q + 1 := by
      rw [← hL l]
      exact (Fintype.card_of_subtype _ (fun x => by simp)).symm
    omega
  have hdisj : ∀ l ∈ Lp, ∀ l' ∈ Lp, l ≠ l' →
      Disjoint ((Finset.univ.filter (fun r => I r l)).erase p)
        ((Finset.univ.filter (fun r => I r l')).erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_erase, Finset.mem_filter] at hr hr'
    obtain ⟨m, _, hm⟩ := hU p r (fun e => hr.1 e.symm)
    have e1 := hm l ⟨hLp l hl, hr.2.2⟩
    have e2 := hm l' ⟨hLp l' hl', hr'.2.2⟩
    exact hne (e1.trans e2.symm)
  have hcard : (Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)).card
      = Lp.card * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hT]
  have hsub : Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)
      ⊆ Finset.univ.erase p := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨l, _, hr⟩ := hr
    rw [Finset.mem_erase] at hr ⊢
    exact ⟨hr.1, Finset.mem_univ r⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
    Fintype.card_fin] at h1
  have h3 : N - 1 = (q + 1) * q := by
    rw [hN]
    have h4 : q ^ 2 + q + 1 - 1 = q ^ 2 + q := by omega
    rw [h4]; ring
  rw [h3] at h1
  exact Nat.le_of_mul_le_mul_right h1 hq

def Rel (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool) → Prop
  | Sum.inl (j, s) => RC C N I p l j s
  | Sum.inr (j, s) => RA C N I p l j s

lemma rel_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (σ : (Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool))
    (h : Rel C N I p l σ) (h' : Rel C N I p' l' σ) : p = p' ∧ l = l' := by
  rcases σ with ⟨j, s⟩ | ⟨j, s⟩
  · simp only [Rel] at h h'
    exact RC_unique C N I hU p l p' l' j s h h'
  · simp only [Rel] at h h'
    exact RA_unique C N I hU p l p' l' j s h h'

lemma done_rel (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N)
    (h : Done C N I p l) : ∃ σ, Rel C N I p l σ := by
  rcases h with ⟨j, s, hj, h⟩ | ⟨j, s, hj, h⟩
  · exact ⟨Sum.inl (⟨j, hj⟩, s), h⟩
  · exact ⟨Sum.inr (⟨j, hj⟩, s), h⟩

lemma count (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hG : Good C N)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q → CL C N p L → ∃ l ∈ L, I p l)
    (hpen : ∀ (p : Fin N) (Lp : Finset (Fin N)), (∀ l ∈ Lp, I p l) → Lp.card ≤ q + 1)
    (hq : 2 ≤ q) {S : Type} [Fintype S] (π : S → Fin N × Fin N) (hπ : Function.Injective π)
    (hI : ∀ x, I (π x).1 (π x).2) (hK : ∀ x, CL C N ((π x).1 : ℕ) {(π x).2}) :
    Fintype.card S ≤ 10 * C.gates.length := by
  classical
  by_cases hq5 : 5 ≤ q
  · have hemb : ∀ p : Fin N, ∃ e : { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } →
        (Fin C.gates.length × Bool) × Fin 3,
        Function.Injective e ∧ ∀ x, Owns C N I p (e x).1 := by
      intro p
      have hc : Fintype.card { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } ≤
          Fintype.card ({ τ : Fin C.gates.length × Bool // Owns C N I p τ } × Fin 3) := by
        rw [Fintype.card_prod, Fintype.card_fin]
        have ho : Fintype.card { τ : Fin C.gates.length × Bool // Owns C N I p τ }
            = (ownedSet C N I p).card :=
          Fintype.card_of_subtype _ (fun τ => mem_ownedSet C N I p τ)
        rw [ho]
        by_cases hne : Nonempty { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ }
        · obtain ⟨⟨l0, h0⟩⟩ := hne
          have hb := stuck_bound C N q hG I hsound (by omega) p l0 h0.1.2
            (fun hd => h0.2 (done_rel C N I p l0 hd))
          have hp : Fintype.card { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } ≤ q + 1 := by
            rw [Fintype.card_of_subtype
              (Finset.univ.filter (fun l : Fin N => (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ))
              (fun x => by
                rw [Finset.mem_filter]
                exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩)]
            exact hpen p _ (fun l hl => (Finset.mem_filter.mp hl).2.1.1)
          omega
        · rw [not_nonempty_iff] at hne
          rw [Fintype.card_eq_zero_iff.mpr hne]
          exact Nat.zero_le _
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
      refine ⟨fun x => ((e x).1.1, (e x).2), ?_, fun x => (e x).1.2⟩
      intro x y h
      dsimp only at h
      have h1 : (e x).1.1 = (e y).1.1 := (Prod.mk.inj h).1
      have h2 : (e x).2 = (e y).2 := (Prod.mk.inj h).2
      exact e.injective (Prod.ext (Subtype.ext h1) h2)
    choose E hEinj hEown using hemb
    have hEglob : ∀ (p p' l l' : Fin N) (h : (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ)
        (h' : (I p' l' ∧ CL C N (p' : ℕ) {l'}) ∧ ¬ ∃ σ, Rel C N I p' l' σ),
        E p ⟨l, h⟩ = E p' ⟨l', h'⟩ → p = p' ∧ l = l' := by
      intro p p' l l' h h' e
      have hp : p = p' := owns_unique C N I hU p p' _ (hEown p ⟨l, h⟩)
        (by rw [e]; exact hEown p' ⟨l', h'⟩)
      subst hp
      exact ⟨rfl, congrArg Subtype.val (hEinj p e)⟩
    have hcard := Fintype.card_le_of_injective
      (fun x : S => if h : ∃ σ, Rel C N I (π x).1 (π x).2 σ then
          (Sum.inl (Classical.choose h) :
            ((Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool)) ⊕
              ((Fin C.gates.length × Bool) × Fin 3))
        else Sum.inr (E (π x).1 ⟨(π x).2, ⟨⟨hI x, hK x⟩, h⟩⟩))
      (by
        intro x y hxy
        dsimp only at hxy
        by_cases hx : ∃ σ, Rel C N I (π x).1 (π x).2 σ
        · by_cases hy : ∃ σ, Rel C N I (π y).1 (π y).2 σ
          · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_left_of_eq_true (eq_true hy)] at hxy
            have e := Sum.inl.inj hxy
            have h1 := Classical.choose_spec hx
            have h2 := Classical.choose_spec hy
            have h3 := rel_unique C N I hU _ _ _ _ (Classical.choose hx) h1
              (by rw [show Classical.choose hx = Classical.choose hy from e]; exact h2)
            exact hπ (Prod.ext h3.1 h3.2)
          · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_right_of_eq_false (eq_false hy)] at hxy
            cases hxy
        · by_cases hy : ∃ σ, Rel C N I (π y).1 (π y).2 σ
          · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_left_of_eq_true (eq_true hy)] at hxy
            cases hxy
          · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_right_of_eq_false (eq_false hy)] at hxy
            have e := Sum.inr.inj hxy
            have h3 := hEglob _ _ _ _ _ _ e
            exact hπ (Prod.ext h3.1 h3.2))
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      at hcard
    omega
  · have hrd : ∀ x : S, ∃ σ : Fin C.gates.length × Bool,
        inp C σ.1 σ.2 = ((π x).1 : ℕ) := by
      intro x
      rcases Ctx_cases C N _ _ (hK x) with ho | ⟨j, s, hw, ht⟩
      · exfalso
        obtain ⟨a, ha, _⟩ := hsound (π x).1 ∅ (by simp)
          (by show Ctx C N (inL N ∅) ((π x).1 : ℕ); rw [ho]; exact Ctx_out C N _)
        simp at ha
      · exact ⟨(⟨j, ht.1⟩, s), hw.symm⟩
    have hemb5 : ∀ p : Fin N, ∃ e : { l : Fin N // I p l } → Fin 5, Function.Injective e := by
      intro p
      have hc : Fintype.card { l : Fin N // I p l } ≤ Fintype.card (Fin 5) := by
        rw [Fintype.card_fin, Fintype.card_of_subtype
          (Finset.univ.filter (fun l : Fin N => I p l))
          (fun x => by
            rw [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩)]
        have h1 := hpen p (Finset.univ.filter (fun l : Fin N => I p l))
          (fun l hl => (Finset.mem_filter.mp hl).2)
        omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
      exact ⟨e, e.injective⟩
    choose E5 hE5 using hemb5
    have hE5glob : ∀ (p p' l l' : Fin N) (h : I p l) (h' : I p' l'), p = p' →
        E5 p ⟨l, h⟩ = E5 p' ⟨l', h'⟩ → l = l' := by
      intro p p' l l' h h' hp e
      subst hp
      exact congrArg Subtype.val (hE5 p e)
    have hcard := Fintype.card_le_of_injective
      (fun x : S => ((Classical.choose (hrd x), E5 (π x).1 ⟨(π x).2, hI x⟩) :
        (Fin C.gates.length × Bool) × Fin 5))
      (by
        intro x y hxy
        dsimp only at hxy
        have e1 : Classical.choose (hrd x) = Classical.choose (hrd y) := congrArg Prod.fst hxy
        have e2 : E5 (π x).1 ⟨(π x).2, hI x⟩ = E5 (π y).1 ⟨(π y).2, hI y⟩ :=
          congrArg Prod.snd hxy
        have s1 := Classical.choose_spec (hrd x)
        have s2 := Classical.choose_spec (hrd y)
        rw [e1] at s1
        have hp : (π x).1 = (π y).1 := Fin.ext (s1.symm.trans s2)
        have hl := hE5glob _ _ _ _ _ _ hp e2
        exact hπ (Prod.ext hp hl))
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
    omega

end PEqualNP.Outside.L_meta_2972

theorem PEqualNP.Outside.L_meta_2972 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I inst C hq hN hL hU hAO hS
  have hG : PEqualNP.Outside.L_meta_2972.Good C N := ⟨hAO.1, hAO.2.1, hAO.2.2⟩
  have hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q →
      PEqualNP.Outside.L_meta_2972.CL C N p L → ∃ l ∈ L, I p l :=
    fun p L hc h => PEqualNP.Outside.L_meta_2972.ctx_sound C N q hG I hS p L hc h
  have hpen : ∀ (p : Fin N) (Lp : Finset (Fin N)), (∀ l ∈ Lp, I p l) → Lp.card ≤ q + 1 :=
    fun p Lp h => PEqualNP.Outside.L_meta_2972.pencil_le N q I (by omega) hN hL hU p Lp h
  exact PEqualNP.Outside.L_meta_2972.count q N I C hG hU hsound hpen hq Subtype.val
    Subtype.val_injective (fun x => x.2.1) (fun x => by
      apply PEqualNP.Outside.L_meta_2972.B_ctx C N hG _
        (fun i hi => PEqualNP.Outside.L_meta_2972.inL_supp N _ i hi) x.1.1 x.1.1.isLt
        C.output (PEqualNP.Outside.L_meta_2972.Ctx_out C N _)
      exact PEqualNP.Outside.L_meta_2972.ls_eq C N x.1.1 x.1.2 x.2.2)
