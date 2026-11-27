import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8411

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton l a ih => rw [W_snoc]; simp [ih]; omega

def Computes (n : ℕ) (gs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  w < n + gs.length ∧ ∀ x : Fin n → Bool, (W gs (List.ofFn x)).getD w false = f x

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, 0⟩

theorem Computes_congr {n : ℕ} {gs : List Gate} {w : ℕ} {f h : (Fin n → Bool) → Bool}
    (hfh : ∀ x, f x = h x) (hc : Computes n gs w f) : Computes n gs w h :=
  ⟨hc.1, fun x => by rw [hc.2 x, hfh x]⟩

theorem Computes_snoc_mono {n : ℕ} {gs : List Gate} {w : ℕ} {f : (Fin n → Bool) → Bool}
    (g : Gate) (hc : Computes n gs w f) : Computes n (gs ++ [g]) w f := by
  refine ⟨by have := hc.1; simp; omega, fun x => ?_⟩
  rw [W_snoc, ← hc.2 x]
  have hl : w < (W gs (List.ofFn x)).length := by rw [W_length]; simpa using hc.1
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]

theorem Computes_mono {n : ℕ} {gs : List Gate} {w : ℕ} {f : (Fin n → Bool) → Bool}
    (gs' : List Gate) (hc : Computes n gs w f) : Computes n (gs ++ gs') w f := by
  induction gs' using List.reverseRecOn with
  | nil => simpa using hc
  | append_singleton l a ih => rw [← List.append_assoc]; exact Computes_snoc_mono a ih

theorem Computes_input {n : ℕ} (gs : List Gate) (v : Fin n) :
    Computes n gs v.val (fun x => x v) := by
  have h0 : Computes n [] v.val (fun x => x v) := by
    refine ⟨by simp, fun x => ?_⟩
    simp [W, List.getD_eq_getElem?_getD]
  simpa using Computes_mono gs h0

theorem Computes_gate {n : ℕ} {gs : List Gate} {a b : ℕ} {f h : (Fin n → Bool) → Bool}
    (ha : Computes n gs a f) (hb : Computes n gs b h) :
    Computes n (gs ++ [⟨GateOp.and, [a, b]⟩]) (n + gs.length) (fun x => f x && h x) ∧
    Computes n (gs ++ [⟨GateOp.or, [a, b]⟩]) (n + gs.length) (fun x => f x || h x) := by
  constructor
  · refine ⟨by simp, fun x => ?_⟩
    show _ = (f x && h x)
    rw [W_snoc, ← ha.2 x, ← hb.2 x]
    have hl : (W gs (List.ofFn x)).length = n + gs.length := by rw [W_length]; simp
    simp [List.getD_eq_getElem?_getD, ← hl, GateOp.eval]
  · refine ⟨by simp, fun x => ?_⟩
    show _ = (f x || h x)
    rw [W_snoc, ← ha.2 x, ← hb.2 x]
    have hl : (W gs (List.ofFn x)).length = n + gs.length := by rw [W_length]; simp
    simp [List.getD_eq_getElem?_getD, ← hl, GateOp.eval]

theorem Ok_snoc {n : ℕ} {gs : List Gate} (hok : Ok n gs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) {a b : ℕ}
    (ha : a < n + gs.length) (hb : b < n + gs.length) : Ok n (gs ++ [⟨op, [a, b]⟩]) := by
  obtain ⟨h1, h2⟩ := hok
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h1 g hg
    · refine ⟨?_, by simp⟩
      rcases hop with rfl | rfl <;> simp
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · apply h2 j hjl i
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hjl] using hi
    · have hje : j = gs.length := by omega
      subst hje
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl <;> assumption

theorem or_list {n : ℕ} (l : List (Fin n)) (hl : l ≠ []) (gs : List Gate) (hok : Ok n gs) :
    ∃ gs', Ok n (gs ++ gs') ∧ gs'.length + 1 = l.length ∧
      ∃ w, Computes n (gs ++ gs') w (fun x => l.any x) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons i t ih =>
    cases t with
    | nil =>
      refine ⟨[], by simpa using hok, by simp, i.val, ?_⟩
      have := Computes_input (gs ++ []) i
      exact Computes_congr (fun x => by simp) this
    | cons j t' =>
      obtain ⟨gs', hok', hlen, w, hw⟩ := ih (by simp)
      have hi := Computes_input (gs ++ gs') i
      refine ⟨gs' ++ [⟨GateOp.or, [i.val, w]⟩], ?_, by simp at hlen ⊢; omega,
        n + (gs ++ gs').length, ?_⟩
      · rw [← List.append_assoc]
        exact Ok_snoc hok' _ (Or.inr rfl) hi.1 hw.1
      · rw [← List.append_assoc]
        exact Computes_congr (fun x => by simp) (Computes_gate hi hw).2

theorem step {n : ℕ} (v : Fin n) (L : List (Fin n)) (gs : List Gate) (hok : Ok n gs)
    (w : ℕ) (f : (Fin n → Bool) → Bool) (hw : Computes n gs w f) :
    ∃ gs', Ok n (gs ++ gs') ∧ gs'.length ≤ L.length + 1 ∧
      ∃ w', Computes n (gs ++ gs') w' (fun x => f x || (x v && L.any x)) := by
  by_cases hL : L = []
  · subst hL
    exact ⟨[], by simpa using hok, by simp, w, by
      simpa using Computes_congr (fun x => by simp) hw⟩
  · obtain ⟨gs1, hok1, hlen1, w1, hw1⟩ := or_list L hL gs hok
    have hv := Computes_input (gs ++ gs1) v
    have hok2 := Ok_snoc hok1 GateOp.and (Or.inl rfl) hv.1 hw1.1
    have hc2 := (Computes_gate hv hw1).1
    have hwm : Computes n (gs ++ gs1 ++ [⟨GateOp.and, [v.val, w1]⟩]) w f := by
      rw [List.append_assoc]; exact Computes_mono _ hw
    have hok3 := Ok_snoc hok2 GateOp.or (Or.inr rfl) hwm.1 hc2.1
    have hc3 := (Computes_gate hwm hc2).2
    refine ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩] ++ [⟨GateOp.or, [w, n + (gs ++ gs1).length]⟩],
      ?_, by simp; omega,
      n + (gs ++ gs1 ++ [(⟨GateOp.and, [v.val, w1]⟩ : Gate)]).length, ?_⟩
    · simpa only [List.append_assoc] using hok3
    · simpa only [List.append_assoc] using hc3

theorem all {n : ℕ} (l : List (Fin n × List (Fin n))) : ∀ (gs : List Gate), Ok n gs →
    ∀ (w : ℕ) (f : (Fin n → Bool) → Bool), Computes n gs w f →
    ∃ gs', Ok n (gs ++ gs') ∧ gs'.length ≤ (l.map fun p => p.2.length + 1).sum ∧
      ∃ w', Computes n (gs ++ gs') w' (fun x => f x || l.any fun p => x p.1 && p.2.any x) := by
  induction l with
  | nil =>
    intro gs hok w f hw
    exact ⟨[], by simpa using hok, by simp, w, by
      simpa using Computes_congr (fun x => by simp) hw⟩
  | cons p t ih =>
    intro gs hok w f hw
    obtain ⟨gs1, hok1, hlen1, w1, hw1⟩ := step p.1 p.2 gs hok w f hw
    obtain ⟨gs2, hok2, hlen2, w2, hw2⟩ := ih (gs ++ gs1) hok1 w1 _ hw1
    refine ⟨gs1 ++ gs2, by simpa only [List.append_assoc] using hok2, by
      simp only [List.length_append, List.map_cons, List.sum_cons]; omega, w2, ?_⟩
    rw [← List.append_assoc]
    exact Computes_congr (fun x => by simp [Bool.or_assoc]) hw2

end PEqualNP.Outside.L_meta_8411

theorem PEqualNP.Outside.L_meta_8411 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin x1 × List (Fin x1))), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size ≤ x2.size + (List.map (fun (x8 : Fin x1 × List (Fin x1)) => x8.2.length + (1 : ℕ)) x3).sum ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (x2.eval (List.ofFn x8) || x3.any fun (x9 : Fin x1 × List (Fin x1)) => x8 x9.1 && x9.2.any x8) := by
  intro x1 x2 x3 hm hr ho
  obtain ⟨gs', hok, hlen, w, hw⟩ := PEqualNP.Outside.L_meta_8411.all x3 x2.gates ⟨hm, hr⟩
    x2.output (fun x => x2.eval (List.ofFn x)) ⟨ho, fun x => rfl⟩
  refine ⟨⟨x2.gates ++ gs', w⟩, hok.1, hok.2, by
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append]; omega, fun x => ?_⟩
  exact hw.2 x
