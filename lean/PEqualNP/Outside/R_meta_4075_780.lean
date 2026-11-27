import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4075_780
    (hAnd : ∀ (b : Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u a c : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ → gs.length ≤ 16 →
      11 ≤ u → u < 11 + gs.length → 11 ≤ a → a < 11 + gs.length → 11 ≤ c → c < 11 + gs.length →
      a ≠ u → c ≠ u →
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10));
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD p false;
      (∃ x, w x u = true ∧ (w x a && w x c) = false) → (∃ x, w x u = false ∧ (w x a && w x c) = true) →
      (∀ x, f x = true → w x u = true ∧ (w x a && w x c) = true) →
      ∃ x, f x = false ∧ w x u = true ∧ (w x a && w x c) = true)
    (hOr : ∀ (b : Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u a c : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ → gs.length ≤ 16 →
      11 ≤ u → u < 11 + gs.length → a ≠ u → c ≠ u →
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10));
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD p false;
      (∃ x, w x u = true ∧ (w x a || w x c) = false) → (∃ x, w x u = false ∧ (w x a || w x c) = true) →
      (∀ x, f x = true → w x u = true ∧ (w x a || w x c) = true) →
      ∃ x, f x = false ∧ w x u = true ∧ (w x a || w x c) = true)
    (hNot : ∀ (b : Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u a : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ → gs.length ≤ 16 →
      11 ≤ u → u < 11 + gs.length → 11 ≤ a → a < 11 + gs.length → a ≠ u →
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10));
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD p false;
      (∃ x, w x u = true ∧ (!w x a) = false) → (∃ x, w x u = false ∧ (!w x a) = true) →
      (∀ x, f x = true → w x u = true ∧ (!w x a) = true) →
      ∃ x, f x = false ∧ w x u = true ∧ (!w x a) = true) :
(∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true)
 := by

  have witC : ∀ (b : Bool) (p : Fin 11),
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ =>
        (fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) (Fin.ofNat _ (e / 10)) &&
        (fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) (Fin.ofNat _ (e % 10))) = true ∧
      (List.ofFn (fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) ++
        [(fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) 0 &&
          if b = true then (fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) 1
          else (fun i : Fin 10 => decide (if (p.val = 5 ∨ p.val = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) 2]).getD p.val false = false := by
    decide
  have allT : ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ =>
      (fun _ : Fin 10 => true) (Fin.ofNat _ (e / 10)) && (fun _ : Fin 10 => true) (Fin.ofNat _ (e % 10))) = true := by
    decide
  have seedT : ∀ (b : Bool) (p : Fin 11),
      (List.ofFn (fun _ : Fin 10 => true) ++ [true && if b = true then true else true]).getD p.val false = true := by
    decide
  intro b D u0 v0 fan small x7 w0 H1 H2 H3
  have pc10 : ∀ x : Fin 10 → Bool, ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) = x7 x := by
    intro x
    have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
        (a0 && a1 || (a1 && a2 || (a2 && a3 || (a3 && a4 || (a4 && a0 || (a0 && a5 || (a1 && a6 || (a2 && a7 || (a3 && a8 || (a4 && a9 || (a5 && a7 || (a7 && a9 || (a9 && a6 || (a6 && a8 || (a8 && a5 || false))))))))))))))) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a4 && a9 || a5 && a7 || a7 && a9 || a9 && a6 || a6 && a8 || a8 && a5) := by
      decide
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
  let f : (Fin 10 → Bool) → Bool := fun x => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))
  have hf : ∀ x, f x = x7 x := pc10
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let seed : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && if b = true then x 1 else x 2]
  have seedLen : ∀ x, (seed x).length = 11 := by intro x; simp [seed]
  have runLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have runPre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons, ih (step ws g) i (by simp only [step, List.length_append]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ hi]

  have gateWire : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p : ℕ),
      (∀ x, f x = true → (gs.foldl step (seed x)).getD p false = true) → 11 ≤ p ∧ p < 11 + gs.length := by
    intro gs p hp
    constructor
    · by_contra hlt
      have hlt' : p < 11 := by omega
      obtain ⟨h1, h2⟩ := witC b ⟨p, hlt'⟩
      have := hp (fun i : Fin 10 => decide (if (p = 5 ∨ p = 7) then (i.val = 0 ∨ i.val = 1) else (i.val = 5 ∨ i.val = 7))) h1
      rw [runPre _ _ _ (by rw [seedLen]; exact hlt')] at this
      have h2' := h2
      simp only at h2'
      exact absurd this (by rw [show (seed _).getD p false = false from h2']; decide)
    · by_contra hge
      have := hp (fun _ => true) allT
      rw [List.getD_eq_default _ _ (by rw [runLen, seedLen]; omega)] at this
      exact Bool.false_ne_true this
  have hw0 : ∀ x p, w0 x p = (D.gates.foldl step (seed x)).getD p false := fun _ _ => rfl
  have core : ∀ u v, u < v → (∃ x, w0 x u = true ∧ w0 x v = false) → (∃ x, w0 x u = false ∧ w0 x v = true) →
      (∀ x, f x = true → w0 x u = true ∧ w0 x v = true) → ∃ x, f x = false ∧ w0 x u = true ∧ w0 x v = true := by
    intro u v huv K1 K2 K3
    have hu := gateWire D.gates u (fun x hx => (K3 x hx).1)
    have hv := gateWire D.gates v (fun x hx => (K3 x hx).2)
    have hk : v - 11 < D.gates.length := by omega
    obtain ⟨gs, g, rest, hsplit, gsLen⟩ : ∃ gs g rest, D.gates = gs ++ g :: rest ∧ gs.length = v - 11 :=
      ⟨D.gates.take (v - 11), D.gates[v - 11], D.gates.drop (v - 11 + 1),
        by rw [← List.drop_eq_getElem_cons hk, List.take_append_drop], by simp; omega⟩
    have WLen : ∀ x, (gs.foldl step (seed x)).length = v := by
      intro x; rw [runLen, seedLen, gsLen]; omega
    have wv : ∀ x, w0 x v = g.op.eval (g.inputs.map fun i => (gs.foldl step (seed x)).getD i false) := by
      intro x
      rw [hw0, hsplit, List.foldl_append, List.foldl_cons, runPre _ _ _ (by simp only [step, List.length_append, WLen]; simp)]
      simp only [step]
      rw [List.getD_append_right _ _ _ _ (by rw [WLen]), WLen, Nat.sub_self]
      rfl
    have wu : ∀ x, w0 x u = (gs.foldl step (seed x)).getD u false := by
      intro x
      rw [hw0, hsplit, List.foldl_append, List.foldl_cons, runPre _ _ _ (by simp only [step, List.length_append, WLen]; simp; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ (by rw [WLen]; exact huv)]
    have fanG : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ :=
      fun g' hg' => fan g' (by rw [hsplit]; exact List.mem_append_left _ hg')
    have small' : gs.length ≤ 16 := by
      change D.gates.length ≤ 17 at small; rw [hsplit] at small; simp at small; omega
    have hu' : u < 11 + gs.length := by omega
    have andCase : ∀ a c, (∀ x, w0 x v = ((gs.foldl step (seed x)).getD a false && (gs.foldl step (seed x)).getD c false)) →
        ∃ x, f x = false ∧ w0 x u = true ∧ w0 x v = true := by
      intro a c hvv
      simp only [wu, hvv] at K1 K2 K3 ⊢
      by_cases hau : a = u
      · rw [hau] at K2; obtain ⟨x, h1, h2⟩ := K2; rw [h1] at h2; simp at h2
      by_cases hcu : c = u
      · rw [hcu] at K2; obtain ⟨x, h1, h2⟩ := K2; rw [h1] at h2; simp at h2
      have ra := gateWire gs a (fun x hx => ((Bool.and_eq_true _ _).mp (K3 x hx).2).1)
      have rc := gateWire gs c (fun x hx => ((Bool.and_eq_true _ _).mp (K3 x hx).2).2)
      exact hAnd b gs u a c fanG small' hu.1 hu' ra.1 ra.2 rc.1 rc.2 hau hcu K1 K2 K3
    have orCase : ∀ a c, (∀ x, w0 x v = ((gs.foldl step (seed x)).getD a false || (gs.foldl step (seed x)).getD c false)) →
        ∃ x, f x = false ∧ w0 x u = true ∧ w0 x v = true := by
      intro a c hvv
      simp only [wu, hvv] at K1 K2 K3 ⊢
      by_cases hau : a = u
      · rw [hau] at K1; obtain ⟨x, h1, h2⟩ := K1; rw [h1] at h2; simp at h2
      by_cases hcu : c = u
      · rw [hcu] at K1; obtain ⟨x, h1, h2⟩ := K1; rw [h1] at h2; simp at h2
      exact hOr b gs u a c fanG small' hu.1 hu' hau hcu K1 K2 K3
    have notCase : ∀ a, (∀ x, w0 x v = !(gs.foldl step (seed x)).getD a false) →
        ∃ x, f x = false ∧ w0 x u = true ∧ w0 x v = true := by
      intro a hvv
      simp only [wu, hvv] at K1 K2 K3 ⊢
      by_cases hau : a = u
      · rw [hau] at K3; obtain ⟨h1, h2⟩ := K3 (fun _ => true) allT; rw [h1] at h2; simp at h2
      have ra : 11 ≤ a ∧ a < 11 + gs.length := by
        constructor
        · by_contra hlt
          obtain ⟨_, h2⟩ := K3 (fun _ => true) allT
          rw [runPre _ _ _ (by rw [seedLen]; omega)] at h2
          have e : (seed fun _ => true).getD a false = true := seedT b ⟨a, by omega⟩
          rw [e] at h2; simp at h2
        · by_contra hge
          obtain ⟨x, _, h2⟩ := K1
          rw [List.getD_eq_default _ _ (by rw [runLen, seedLen]; omega)] at h2
          simp at h2
      exact hNot b gs u a fanG small' hu.1 hu' ra.1 ra.2 hau K1 K2 K3
    obtain ⟨hop, hlen⟩ := fan g (by rw [hsplit]; simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · rcases hin : g.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨d, t⟩⟩⟩
      · exfalso; obtain ⟨x, _, h2⟩ := K1; rw [wv x, hop, hin] at h2; have h3 : true = false := h2; exact Bool.noConfusion h3
      · exact andCase a a (fun x => by rw [wv, hop, hin]; show ((gs.foldl step (seed x)).getD a false && true) = ((gs.foldl step (seed x)).getD a false && (gs.foldl step (seed x)).getD a false); generalize (gs.foldl step (seed x)).getD a false = p; cases p <;> rfl)
      · exact andCase a c (fun x => by rw [wv, hop, hin]; show ((gs.foldl step (seed x)).getD a false && ((gs.foldl step (seed x)).getD c false && true)) = ((gs.foldl step (seed x)).getD a false && (gs.foldl step (seed x)).getD c false); generalize (gs.foldl step (seed x)).getD a false = p; generalize (gs.foldl step (seed x)).getD c false = q; cases p <;> cases q <;> rfl)
      · rw [hin] at hlen; simp at hlen
    · rcases hin : g.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨d, t⟩⟩⟩
      · exfalso; have h2 := (K3 (fun _ => true) allT).2; rw [wv, hop, hin] at h2; have h3 : false = true := h2; exact Bool.noConfusion h3
      · exact orCase a a (fun x => by rw [wv, hop, hin]; show ((gs.foldl step (seed x)).getD a false || false) = ((gs.foldl step (seed x)).getD a false || (gs.foldl step (seed x)).getD a false); generalize (gs.foldl step (seed x)).getD a false = p; cases p <;> rfl)
      · exact orCase a c (fun x => by rw [wv, hop, hin]; show ((gs.foldl step (seed x)).getD a false || ((gs.foldl step (seed x)).getD c false || false)) = ((gs.foldl step (seed x)).getD a false || (gs.foldl step (seed x)).getD c false); generalize (gs.foldl step (seed x)).getD a false = p; generalize (gs.foldl step (seed x)).getD c false = q; cases p <;> cases q <;> rfl)
      · rw [hin] at hlen; simp at hlen
    · rcases hin : g.inputs with _ | ⟨a, _ | ⟨c, _ | ⟨d, t⟩⟩⟩
      · exfalso; obtain ⟨x, _, h2⟩ := K1; rw [wv x, hop, hin] at h2; have h3 : true = false := h2; exact Bool.noConfusion h3
      · exact notCase a (fun x => by rw [wv, hop, hin]; rfl)
      · exact notCase a (fun x => by rw [wv, hop, hin]; rfl)
      · rw [hin] at hlen; simp at hlen
  have H3' : ∀ x, f x = true → w0 x u0 = true ∧ w0 x v0 = true :=
    fun x hx => H3 x (by rw [← hf x]; exact hx)
  rcases lt_trichotomy u0 v0 with h | h | h
  · obtain ⟨x, hx1, hx2, hx3⟩ := core u0 v0 h H1 H2 H3'
    exact ⟨x, by rw [← hf x]; exact hx1, hx2, hx3⟩
  · subst h; obtain ⟨x, h1, h2⟩ := H1; rw [h1] at h2; exact absurd h2 (by decide)
  · obtain ⟨y1, p1, q1⟩ := H1
    obtain ⟨y2, p2, q2⟩ := H2
    obtain ⟨x, hx1, hx2, hx3⟩ := core v0 u0 h ⟨y2, q2, p2⟩ ⟨y1, q1, p1⟩ (fun x hx => (H3' x hx).symm)
    exact ⟨x, by rw [← hf x]; exact hx1, hx3, hx2⟩
