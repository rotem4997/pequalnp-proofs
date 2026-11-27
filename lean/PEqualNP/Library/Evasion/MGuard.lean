import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Evasion.Clock
import PEqualNP.Library.Machines.FirstGRun
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Machines.AllTrue

/-!
# Evasion chain: negating a decider and the length guard

* `notTime : StmtNotTime`: negation costs no step. The same machine computes `!f` once its
  output alphabet equivalence is composed with `Bool.not` (the answer is the one-symbol string
  `encodeBool b = [b]`).
* `gfirst_time`: the generic "run on the first component" machine `Gen.firstM` with an explicit
  time bound and a typed second component.
* `lenLE_time`: the length comparison machine `LenCmp.lenM` within `2 * n + 3` steps.
* `lenGuard : StmtLenGuard`: the scheme of `nf_and` (`Machines/NormalForm.lean`) with explicit
  linear times: duplicate the pair, run the decider of `B` on the first copy, swap, run the length
  comparison on the pair, and answer whether both bits are true.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- Negation as an equivalence of `Bool`. -/
def notEquiv : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- Negating a Boolean answer costs no step. -/
theorem notTime : StmtNotTime := by
  intro f t ⟨c, hc⟩
  refine ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet.trans notEquiv
    time := c.time
    outputsFun := fun a => ?_ }, fun n => (hc n).trans (Nat.le_add_right _ _)⟩
  have e : List.map (c.outputAlphabet.trans notEquiv).invFun
      (Computability.encodeBool (!f a)) =
      List.map c.outputAlphabet.invFun (Computability.encodeBool (f a)) := by
    simp [Computability.encodeBool, notEquiv]
  rw [e]
  exact c.outputsFun a

/-- Running a machine on the first component of a pair, with an explicit time bound. -/
theorem gfirst_time {α β γ A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (ec : γ → List C) (f : α → β) (t : ℕ → ℕ)
    (ht : Monotone t) (L : ℕ) (hL : ∀ a, (eb (f a)).length ≤ L)
    (h : ComputableInTime ea eb f t) :
    ComputableInTime (fun p : α × γ => Gen.gpair (ea p.1, ec p.2))
      (fun p : β × γ => Gen.gpair (eb p.1, ec p.2)) (fun p => (f p.1, p.2))
      (fun n => t n + 2 * n + 2 * L + 5) := by
  obtain ⟨c, hc⟩ := h
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : ℕ → ℕ := fun n => t n + 2 * n + 2 * L + 5
  have key : ∀ p : α × γ, ∃ n, n ≤ T (Gen.gpair (ea p.1, ec p.2)).length ∧
      (flip bind (TM2.step (Gen.firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (Gen.firstM c.tm C e₀ e₁) (Gen.gpair (ea p.1, ec p.2)))) =
        some (haltList (Gen.firstM c.tm C e₀ e₁) (Gen.gpair (eb (f p.1), ec p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ c.time (ea a).length ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := Gen.first_run (C := C) e₀ e₁ (ea a) (ec w) _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have b2 : c.time (ea a).length ≤ t ((ea a).length + (ec w).length) :=
      (hc _).trans (ht (by omega))
    have b3 := hL a
    simp only [T, Gen.gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := Gen.firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (Gen.firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (Gen.firstM c.tm C e₀ e₁) l)))
            (hm _ (Gen.gpair (ea p.1, ec p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (Gen.firstM c.tm C e₀ e₁) l))
              (hm _ (Gen.gpair (eb (f p.1), ec p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }, fun _ => le_rfl⟩

/-- The length comparison within `2 * n + 3` steps. -/
theorem lenLE_time : ComputableInTime encodePair Computability.encodeBool
    (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) (fun n => 2 * n + 3) :=
  ⟨{
    tm := LenCmp.lenM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 2 * n + 3
    outputsFun := fun p =>
      { steps := Classical.choose (LenCmp.lenLE_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.2.length ≤ p.1.length)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.2.length ≤ p.1.length))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => LenCmp.lenStep^[Classical.choose (LenCmp.lenLE_run p)]
            (some (initList LenCmp.lenM x))) (hm _ (encodePair p))).trans
            ((Classical.choose_spec (LenCmp.lenLE_run p)).2.trans
              (congrArg (fun x => some (haltList LenCmp.lenM x)) hout))
        steps_le_m := (Classical.choose_spec (LenCmp.lenLE_run p)).1 } }, fun _ => le_rfl⟩

/-- Conjunction of two bits written as a pair, in constant time. -/
theorem and2_time : ∃ k : ℕ, ComputableInTime
    (fun q : Bool × Bool => Gen.gpair (Computability.encodeBool q.1, Computability.encodeBool q.2))
    Computability.encodeBool (fun q : Bool × Bool => q.1 && q.2) (fun _ => k) := by
  obtain ⟨c⟩ := allTrue_polyTime
  refine ⟨c.time.eval 2, ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet
    time := fun _ => c.time.eval 2
    outputsFun := fun q =>
      { steps := (c.outputsFun ([q.1], [q.2])).steps
        evals_in_steps := ?_
        steps_le_m := (c.outputsFun ([q.1], [q.2])).steps_le_m } }, fun _ => le_rfl⟩⟩
  have e1 : Gen.gpair (Computability.encodeBool q.1, Computability.encodeBool q.2) =
      encodePair ([q.1], [q.2]) := rfl
  have e2 : (q.1 && q.2) = ([q.1] ++ [q.2]).all id := by simp
  rw [e1, e2]
  exact (c.outputsFun ([q.1], [q.2])).evals_in_steps

/-- The guard `|p.2| ≤ |p.1|` in front of a linear-time decider costs linear time. -/
theorem lenGuard : StmtLenGuard := by
  intro B K ⟨fB, hfB, hcB⟩
  -- duplicate
  have h1 : ComputableInTime encodePair
      (fun q : (List Bool × List Bool) × (List Bool × List Bool) =>
        Gen.gpair (encodePair q.1, encodePair q.2))
      (fun p : List Bool × List Bool => (p, p)) (fun n => 4 * n + 4) :=
    tp_time _ _ _ (fun s : Bool ⊕ Bool => some (Sum.inl s)) (fun s => some (Sum.inr s))
      (Sum.inl (Sum.inl true)) (fun p => by
        simp [Gen.gpair])
  -- run the decider of `B` on the first copy
  have h2 := gfirst_time (A := Bool ⊕ Bool) (B := Bool) (C := Bool ⊕ Bool) encodePair
    Computability.encodeBool encodePair fB _
    (fun a b hab => Nat.add_le_add_right (Nat.mul_le_mul_left K hab) K) 1
    (fun _ => le_rfl) hcB
  -- swap
  have h3 : ComputableInTime
      (fun q : Bool × (List Bool × List Bool) =>
        Gen.gpair (Computability.encodeBool q.1, encodePair q.2))
      (fun q : (List Bool × List Bool) × Bool =>
        Gen.gpair (encodePair q.1, Computability.encodeBool q.2))
      (fun q => (q.2, q.1)) (fun n => 4 * n + 4) :=
    tp_time _ _ _
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s)
      (Sum.inr true) (fun q => by
        have e1 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
            (fun s : Bool ⊕ (Bool ⊕ Bool) =>
              Sum.elim (fun _ => none) (fun b => some (Sum.inl (β := Bool) b)) s) =
            l.map Sum.inl := by
          intro l; induction l with
          | nil => rfl
          | cons a l ih => simp [ih]
        have e2 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
            (fun s : Bool ⊕ (Bool ⊕ Bool) =>
              Sum.elim (fun b => some (Sum.inr (α := Bool ⊕ Bool) b)) (fun _ => none) s) =
              [] := by
          intro l; induction l with
          | nil => rfl
          | cons a l ih => simp
        simp only [Gen.gpair, List.filterMap_append, e1, e2]
        rfl)
  -- the length comparison on the pair
  have h4 := gfirst_time (A := Bool ⊕ Bool) (B := Bool) (C := Bool) encodePair
    Computability.encodeBool Computability.encodeBool
    (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) _
    (fun a b hab => by show 2 * a + 3 ≤ 2 * b + 3; omega) 1 (fun _ => le_rfl) lenLE_time
  obtain ⟨k, h5⟩ := and2_time
  -- glue
  obtain ⟨C12, h12⟩ := lin_comp (C₁ := 4) (C₂ := K + 7) (D := 2) h1
    (time_mono h2 fun n => by
      show K * n + K + 2 * n + 2 * 1 + 5 ≤ (K + 7) * n + (K + 7)
      nlinarith) (fun p => by
    simp [Gen.gpair_length, encodePair]; omega)
  obtain ⟨C123, h123⟩ := lin_comp (C₂ := 4) (D := 1) h12 h3 (fun p => by
    simp [Gen.gpair_length, encodePair, Computability.encodeBool]; omega)
  obtain ⟨C1234, h1234⟩ := lin_comp (C₂ := 10) (D := 1) h123
    (time_mono h4 fun n => show 2 * n + 3 + 2 * n + 2 * 1 + 5 ≤ 10 * n + 10 by omega)
    (fun p => by simp [Gen.gpair_length, encodePair, Computability.encodeBool])
  have hall := comp_time _ _ _ _ _ _ _ (fun _ => 2) h1234 h5 (fun _ _ _ => le_rfl)
    (fun p => by simp [Gen.gpair_length, Computability.encodeBool])
  refine ⟨C1234 + 6 + k, _, fun p => ?_, time_mono hall fun n => ?_⟩
  · show p ∈ {p : List Bool × List Bool | p.2.length ≤ p.1.length ∧ p ∈ B} ↔
      (decide (p.2.length ≤ p.1.length) && fB p) = true
    simp only [Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_iff, hfB]
  · show C1234 * n + C1234 + (2 * 2 + 2) + k ≤ (C1234 + 6 + k) * n + (C1234 + 6 + k)
    nlinarith [Nat.zero_le ((6 + k) * n)]

end PEqualNP.Library.Evasion

