import PEqualNP.Library.Helpers.TableauEnc

/-!
# One step of a stack machine as a layered circuit

Helper module (proofs only, no statement may use it).

* Layer A (`eA`) computes the window bits from the configuration bits: the top symbols of each
  stack, picked out with the height bits, `O(H)` gates per window bit.
* Layer B (`exists_eB`) computes each new configuration bit from the window and the local bits
  of its cell, with a constant number of gates per bit.
* `sim_step`: the composite is a `Sim` of size linear in `H` computing `stepT` on the bits of
  every configuration with symbols in `T` and stacks of height at most `H`.
* `sim_init`: the bits of the initial configuration from the input bits.
-/

open Turing

namespace PEqualNP.Library.Helpers.Tableau

open PEqualNP.Library.Helpers.Enum
open Classical

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- A disjunction of a list of formulas. -/
def orL {α : Type} : List (Ex α) → Ex α
  | [] => .const false
  | e :: l => .or e (orL l)

theorem eval_orL {α : Type} (ρ : α → Bool) (l : List (Ex α)) :
    Ex.eval ρ (orL l) = l.any (Ex.eval ρ) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [orL, Ex.eval, ih]

theorem size_orL {α : Type} (l : List (Ex α)) :
    Ex.size (orL l) = (l.map Ex.size).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [orL, Ex.size, ih]; omega

section step

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} [Fintype Λ]
  [Fintype σ] (T : Set (Σ k, Γ k)) [Fintype T] (H d p : ℕ)

/-- Every stack holds at most `H` symbols. -/
def Bounded (c : TM2.Cfg Γ Λ σ) : Prop := ∀ k, (c.stk k).length ≤ H

/-- The height bit at position `m` of stack `k` (false beyond `H`). -/
def Ubit (k : K) (m : ℕ) : Ex (Idx Λ σ T H) :=
  if h : m < H then .var (.inr (.inr (.inr (k, ⟨m, h⟩)))) else .const false

theorem eval_Ubit (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (k : K) (m : ℕ) :
    Ex.eval (enc T H c) (Ubit (Λ := Λ) (σ := σ) T H k m) = decide (m < (c.stk k).length) := by
  unfold Ubit
  split_ifs with h
  · rfl
  · have := hc k
    simp only [Ex.eval]
    symm; rw [decide_eq_false_iff_not]; omega

theorem size_Ubit (k : K) (m : ℕ) : Ex.size (Ubit (Λ := Λ) (σ := σ) T H k m) = 1 := by
  unfold Ubit; split_ifs <;> rfl

/-- Layer A: the configuration bits are kept, the window bits are computed. -/
noncomputable def eA : Idx Λ σ T H ⊕ Wix Λ σ T d → Ex (Idx Λ σ T H)
  | .inl j => .var j
  | .inr (.inl l) => .var (.inl l)
  | .inr (.inr (.inl s)) => .var (.inr (.inl s))
  | .inr (.inr (.inr (k, r, g))) =>
    orL ((List.finRange H).map fun i =>
      .and (.and (Ubit T H k (i.1 + r.1)) (.not (Ubit T H k (i.1 + r.1 + 1))))
        (.var (.inr (.inr (.inl (k, i, g))))))

theorem size_eA (b : Idx Λ σ T H ⊕ Wix Λ σ T d) : Ex.size (eA T H d b) ≤ 7 * H + 1 := by
  rcases b with j | l | s | ⟨k, r, g⟩
  · simp [eA, Ex.size]
  · simp [eA, Ex.size]
  · simp [eA, Ex.size]
  · simp only [eA, size_orL, List.length_map, List.length_finRange, List.map_map]
    have : ∀ x ∈ List.map (Ex.size ∘ fun i : Fin H =>
        Ex.and (Ex.and (Ubit (Λ := Λ) (σ := σ) T H k (i.1 + r.1))
          (Ex.not (Ubit T H k (i.1 + r.1 + 1))))
          (Ex.var (Sum.inr (Sum.inr (Sum.inl (k, i, g)))))) (List.finRange H), x = 6 := by
      intro x hx
      simp only [List.mem_map, Function.comp] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp [Ex.size, size_Ubit]
    rw [List.sum_eq_card_nsmul _ 6 this]
    simp; omega

theorem eval_eA (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (b : Idx Λ σ T H ⊕ Wix Λ σ T d) :
    Ex.eval (enc T H c) (eA T H d b) = Sum.elim (enc T H c) (wenc T d c) b := by
  rcases b with j | l | s | ⟨k, r, g⟩
  · rfl
  · rfl
  · rfl
  · simp only [eA, eval_orL, Sum.elim_inr, wenc]
    rw [Bool.eq_iff_iff, List.any_map, List.any_eq_true]
    simp only [List.mem_finRange, true_and, Function.comp, Ex.eval, eval_Ubit T H c hc,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, enc]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, h3⟩
      have hi : i.1 < (c.stk k).length := by omega
      rw [List.getElem?_reverse hi] at h3
      have e : (c.stk k).length - 1 - i.1 = r.1 := by omega
      rw [e] at h3; exact h3
    · intro h
      have hr : r.1 < (c.stk k).length := by
        by_contra hr
        rw [List.getElem?_eq_none (by omega)] at h
        simp [symBit] at h
      have hH := hc k
      refine ⟨⟨(c.stk k).length - 1 - r.1, by omega⟩, ⟨by simp; omega, by simp; omega⟩, ?_⟩
      rw [List.getElem?_reverse (by simp; omega)]
      have e : (c.stk k).length - 1 - ((c.stk k).length - 1 - r.1) = r.1 := by omega
      simp only [e]; exact h

/-- The local variables of cell `i` of stack `k`, read off the wires of layer A. -/
noncomputable def tau (k : K) (i : Fin H) :
    Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T → Ex (Idx Λ σ T H ⊕ Wix Λ σ T d)
  | .inl w => .var (.inr w)
  | .inr (.inl δ) =>
    if δ.1 + i.1 < rad d p then .const true
    else if h : δ.1 + i.1 - rad d p < H then .var (.inl (.inr (.inr (.inr (k, ⟨_, h⟩)))))
    else .const false
  | .inr (.inr g) => .var (.inl (.inr (.inr (.inl (k, i, g)))))

theorem size_tau (k : K) (i : Fin H) (v : Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) :
    Ex.size (tau T H d p k i v) = 1 := by
  rcases v with w | δ | g
  · rfl
  · simp only [tau]; split_ifs <;> rfl
  · rfl

theorem eval_tau (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (k : K) (i : Fin H)
    (v : Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) :
    Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v) = locenc T d p c k i.1 v := by
  rcases v with w | δ | g
  · rfl
  · simp only [tau, locenc]
    have hH := hc k
    split_ifs with h1 h2
    · simp only [Ex.eval]; symm; rw [decide_eq_true_iff]; omega
    · simp only [Ex.eval, Sum.elim_inl, enc, decide_eq_decide]; omega
    · simp only [Ex.eval]; symm; rw [decide_eq_false_iff_not]; omega
  · rfl

/-- The size bound of one formula of layer B. -/
noncomputable def CB : ℕ :=
  7 * 2 ^ (Fintype.card (Wix Λ σ T d) + 2 * rad d p + Fintype.card T)

theorem exists_eB (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p) :
    ∃ eB : Idx Λ σ T H → Ex (Idx Λ σ T H ⊕ Wix Λ σ T d),
      (∀ j, Ex.size (eB j) ≤ CB (Λ := Λ) (σ := σ) T d p) ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c → ∀ j,
        Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (eB j) = enc T H (stepT M c) j := by
  have hW : 7 * 2 ^ Fintype.card (Wix Λ σ T d) ≤ CB (Λ := Λ) (σ := σ) T d p := by
    unfold CB
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hL : 7 * 2 ^ Fintype.card (Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) ≤
      CB (Λ := Λ) (σ := σ) T d p := by
    unfold CB
    simp [Fintype.card_sum, Nat.add_assoc]
  have key : ∀ j : Idx Λ σ T H, ∃ E : Ex (Idx Λ σ T H ⊕ Wix Λ σ T d),
      Ex.size E ≤ CB (Λ := Λ) (σ := σ) T d p ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c →
        Ex.eval (Sum.elim (enc T H c) (wenc T d c)) E = enc T H (stepT M c) j := by
    intro j
    rcases j with l' | s' | ⟨k, i, g⟩ | ⟨k, i⟩
    · obtain ⟨E, hs, he⟩ := exists_ex_det (wenc T d) (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide ((stepT M c).l = l'))
        (fun x y hx hy h => by rw [(stepT_det_l T d M hd x y hx hy h).1])
      refine ⟨Ex.bind (fun w => .var (.inr w)) E, ?_, fun c hc _ => ?_⟩
      · rw [Ex.size_bind _ (fun _ => rfl)]; omega
      · rw [Ex.eval_bind]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (wenc T d) (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide ((stepT M c).var = s'))
        (fun x y hx hy h => by rw [(stepT_det_l T d M hd x y hx hy h).2])
      refine ⟨Ex.bind (fun w => .var (.inr w)) E, ?_, fun c hc _ => ?_⟩
      · rw [Ex.size_bind _ (fun _ => rfl)]; omega
      · rw [Ex.eval_bind]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (fun c => locenc T d p c k i.1)
        (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => symBit k (((stepT M c).stk k).reverse[i.1]?) g)
        (fun x y hx hy h => by rw [(locenc_det T d M p hd hp x y k i.1 hx hy h).1])
      refine ⟨Ex.bind (tau T H d p k i) E, ?_, fun c hc hb => ?_⟩
      · rw [Ex.size_bind _ (size_tau T H d p k i)]; omega
      · rw [Ex.eval_bind]
        have e : (fun v => Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v)) =
            locenc T d p c k i.1 := funext (eval_tau T H d p c hb k i)
        rw [e]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (fun c => locenc T d p c k i.1)
        (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide (i.1 < ((stepT M c).stk k).length))
        (fun x y hx hy h => by
          simp only [decide_eq_decide]; exact (locenc_det T d M p hd hp x y k i.1 hx hy h).2)
      refine ⟨Ex.bind (tau T H d p k i) E, ?_, fun c hc hb => ?_⟩
      · rw [Ex.size_bind _ (size_tau T H d p k i)]; omega
      · rw [Ex.eval_bind]
        have e : (fun v => Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v)) =
            locenc T d p c k i.1 := funext (eval_tau T H d p c hb k i)
        rw [e]; exact he c hc
  choose eB h1 h2 using key
  exact ⟨eB, h1, fun c hc hb j => h2 j c hc hb⟩

theorem sim_step (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p) :
    ∃ F : (Idx Λ σ T H → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H ⊕ Wix (K := K) Λ σ T d) * (7 * H + 1) +
        Fintype.card (Idx (K := K) Λ σ T H) * CB (Λ := Λ) (σ := σ) T d p) ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c → F (enc T H c) = enc T H (stepT M c) := by
  obtain ⟨eB, hs, he⟩ := exists_eB T H d p M hd hp
  have hA := sim_layer (eA (Λ := Λ) (σ := σ) T H d)
  have hB := sim_layer eB
  refine ⟨_, sim_mono (sim_comp hA hB) ?_, fun c hc hb => ?_⟩
  · apply add_le_add
    · refine (Finset.sum_le_card_nsmul _ _ _ (fun b _ => size_eA T H d b)).trans ?_
      simp
    · refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hs j)).trans ?_
      simp
  · funext j
    have e : (fun b => Ex.eval (enc T H c) (eA T H d b)) = Sum.elim (enc T H c) (wenc T d c) :=
      funext (eval_eA T H d c hb)
    simp only [e]
    exact he c hc hb j

end step

end PEqualNP.Library.Helpers.Tableau
