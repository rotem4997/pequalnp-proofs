import PEqualNP.Library.Evasion.Plan
import PEqualNP.Library.L083
import PEqualNP.Library.Machines.SquareClock
import PEqualNP.Library.Helpers.PadMap

/-!
# Evasion chain: the constant-factor unary scaling (T2a) and the exponential clock (CLK)

* `tp_time`: the two-pass machine with the explicit bound `4 * n + 4`.
* `lin_comp`: linear time composes with linear time when the intermediate output is linear.
* `scalePair`: `x ↦ (x, 1^(M * |x|))` in linear time, by `M` passes of the two-pass machine on
  the pair encoding, each pass appending `|x|` symbols to the second component.
* `t2a : StmtT2a`: `x ↦ 1^(a * |x| + b)` in linear time (project, then `b` times `true ::`).
* `clk : StmtCLK`: scale by `p`, the exponential clock L083 at `k = 1`, scale by `K` and add `K`.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-- The two-pass machine with an explicit time bound. -/
theorem tp_time {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] (ea : α → List Γ₀) (eb : β → List Γ₁)
    (f : α → β) (φ₁ φ₂ : Γ₀ → Option Γ₁) (y : Γ₁)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    PEqualNP.Library.ComputableInTime ea eb f (fun n => 4 * n + 4) := by
  have hd : ∀ φ : Γ₀ → Option Γ₁, (some y : Option Γ₁) = none → ∀ x, φ x = none :=
    fun φ h => by simp at h
  exact ⟨{
    tm := tp φ₁ φ₂ (some y)
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ (some y) (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ (some y))))^[(ea a).length
            + 1 + ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ (some y)) l))) (hm Γ₀ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ (some y)) l))
              ((h a).symm.trans (hm Γ₁ (eb (f a))).symm)))
        steps_le_m := by
          show _ ≤ 4 * (ea a).length + 4
          omega } }, fun _ => le_rfl⟩

/-- Linear time after linear time, with a linearly bounded intermediate output. -/
theorem lin_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} {C₁ C₂ D : ℕ}
    (h₁ : PEqualNP.Library.ComputableInTime ea eb f (fun n => C₁ * n + C₁))
    (h₂ : PEqualNP.Library.ComputableInTime eb ec g (fun n => C₂ * n + C₂))
    (hlen : ∀ a, (eb (f a)).length ≤ D * (ea a).length + D) :
    ∃ C : ℕ, PEqualNP.Library.ComputableInTime ea ec (fun a => g (f a)) (fun n => C * n + C) := by
  have h := comp_time ea eb ec f g _ _ (fun n => D * n + D) h₁ h₂
    (fun a b hab => by
      show C₂ * a + C₂ ≤ C₂ * b + C₂
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hab) _) hlen
  refine ⟨C₁ + 2 * D + 2 + C₂ * D + C₂, time_mono h fun n => ?_⟩
  show C₁ * n + C₁ + (2 * (D * n + D) + 2) + (C₂ * (D * n + D) + C₂) ≤
    (C₁ + 2 * D + 2 + C₂ * D + C₂) * n + (C₁ + 2 * D + 2 + C₂ * D + C₂)
  nlinarith [Nat.zero_le (C₂ * n), Nat.zero_le n]

theorem filterMap_const {Γ₀ Γ₁ : Type} (c : Γ₁) (l : List Γ₀) :
    l.filterMap (fun _ => some c) = List.replicate l.length c := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

/-- Keep the first component. -/
def stφ₁ : Bool ⊕ Bool → Option (Bool ⊕ Bool)
  | Sum.inl b => some (Sum.inl b)
  | Sum.inr _ => none

/-- Second component of the pair encoding. -/
def prφ : Bool ⊕ Bool → Option Bool
  | Sum.inl _ => none
  | Sum.inr b => some b

theorem filterMap_stφ₁ (x y : List Bool) :
    (PEqualNP.Library.encodePair (x, y)).filterMap stφ₁ = x.map Sum.inl := by
  induction x with
  | nil =>
    simp only [PEqualNP.Library.encodePair, List.map_nil, List.nil_append]
    induction y with
    | nil => rfl
    | cons b y ih => simp [stφ₁]
  | cons b x ih => simpa [PEqualNP.Library.encodePair, stφ₁] using ih

theorem filterMap_prφ (x y : List Bool) :
    (PEqualNP.Library.encodePair (x, y)).filterMap prφ = y := by
  induction x with
  | nil =>
    simp only [PEqualNP.Library.encodePair, List.map_nil, List.nil_append]
    induction y with
    | nil => rfl
    | cons b y ih => simpa [prφ] using ih
  | cons b x ih => exact (List.filterMap_cons_none rfl).trans ih

/-- One pass: append `|x|` ones to the second component. -/
theorem step_time : PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair
    PEqualNP.Library.encodePair
    (fun q : List Bool × List Bool => (q.1, List.replicate (q.1.length + q.2.length) true))
    (fun n => 4 * n + 4) :=
  tp_time _ _ _ stφ₁ (fun _ => some (Sum.inr true)) (Sum.inl true) (fun q => by
    rw [filterMap_const, filterMap_stφ₁]
    simp [PEqualNP.Library.encodePair, List.map_replicate])

/-- The pair `(x, 1^(M * |x|))` in linear time. -/
theorem scalePair (M : ℕ) : ∃ C : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    PEqualNP.Library.encodePair (fun x : List Bool => (x, List.replicate (M * x.length) true))
    (fun n => C * n + C) := by
  induction M with
  | zero =>
    refine ⟨4, time_mono (tp_time _ _ _ (fun b => some (Sum.inl b)) (fun _ => none)
      (Sum.inl true) (fun x => ?_)) fun n => by omega⟩
    simp [PEqualNP.Library.encodePair]
  | succ M ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := lin_comp (D := M + 1) hC
      (time_mono step_time fun n => (by omega : 4 * n + 4 ≤ 4 * n + 4)) (fun x => by
        simp only [PEqualNP.Library.encodePair, List.length_append, List.length_map,
          List.length_replicate]
        nlinarith)
    refine ⟨C', ?_⟩
    have e : (fun x : List Bool => (x, List.replicate ((M + 1) * x.length) true)) =
        (fun x : List Bool => (x, List.replicate (x.length + (M * x.length)) true)) := by
      funext x; congr 2; ring
    rw [e]
    simpa only [List.length_replicate] using hC'

/-- T2a: `x ↦ 1^(a * |x| + b)` in linear time. -/
theorem t2a : StmtT2a := by
  intro a b
  induction b with
  | zero =>
    obtain ⟨C, hC⟩ := scalePair a
    have hp : PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair
        (fun x : List Bool => x) (fun q : List Bool × List Bool => q.2) (fun n => 4 * n + 4) :=
      tp_time _ _ _ prφ (fun _ => none) true (fun q => by
        rw [filterMap_prφ]; simp)
    obtain ⟨C', hC'⟩ := lin_comp (D := a + 1) hC hp (fun x => by
      simp only [PEqualNP.Library.encodePair, List.length_append, List.length_map,
        List.length_replicate]
      nlinarith)
    exact ⟨C', by simpa using hC'⟩
  | succ b ih =>
    obtain ⟨C, hC⟩ := ih
    have hc : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
        (fun x : List Bool => x) (fun y : List Bool => true :: y) (fun n => 3 * n + 3) :=
      time_mono PEqualNP.Library.Helpers.consTrue_time fun n => by omega
    obtain ⟨C', hC'⟩ := lin_comp (D := a + b) hC hc (fun x => by
      simp only [List.length_replicate]
      nlinarith)
    refine ⟨C', ?_⟩
    have e : (fun x : List Bool => List.replicate (a * x.length + (b + 1)) true) =
        (fun x : List Bool => true :: List.replicate (a * x.length + b) true) := by
      funext x; rw [← Nat.add_assoc, List.replicate_succ]
    rw [e]
    exact hC'

/-- CLK: the clock `m ↦ K * 2 ^ (p * m) + K` is constructible. -/
theorem clk : StmtCLK := by
  intro p K hp hK
  refine ⟨fun a b hab => ?_, fun n => ?_, ?_⟩
  · show K * 2 ^ (p * a) + K ≤ K * 2 ^ (p * b) + K
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.mul_le_mul_left p hab)
    exact Nat.add_le_add_right (Nat.mul_le_mul_left K this) K
  · show n ≤ K * 2 ^ (p * n) + K
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (p * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left n hp)
    have h3 : 2 ^ (p * n) ≤ K * 2 ^ (p * n) := Nat.le_mul_of_pos_left _ hK
    omega
  · obtain ⟨C₁, hC₁⟩ := t2a p 0
    obtain ⟨c, hc⟩ := PEqualNP.Library.L083 1 le_rfl
    obtain ⟨C₃, hC₃⟩ := t2a K K
    have h12 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x) _ _ _ _ (fun n => p * n + 0) hC₁ hc
      (fun a b hab => by
        show c * 2 ^ (a ^ 1) + c ≤ c * 2 ^ (b ^ 1) + c
        simp only [pow_one]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left c
          (Nat.pow_le_pow_right (by norm_num) hab)) c)
      (fun x => by simp)
    have h123 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x) _ _ _ _ (fun n => 2 ^ ((p * n + 0) ^ 1)) h12 hC₃
      (fun a b hab => by
        show C₃ * a + C₃ ≤ C₃ * b + C₃
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hab) _)
      (fun x => by simp)
    simp only [List.length_replicate, pow_one, Nat.add_zero] at h123
    refine ⟨C₁ + 2 * p + c + 2 + C₃ + C₁ + c + C₃ + 4, time_mono h123 fun n => ?_⟩
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (p * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left n hp)
    have h3 : 2 ^ (p * n) ≤ K * 2 ^ (p * n) := Nat.le_mul_of_pos_left _ hK
    show _ ≤ (C₁ + 2 * p + c + 2 + C₃ + C₁ + c + C₃ + 4) * (K * 2 ^ (p * n) + K) +
      (C₁ + 2 * p + c + 2 + C₃ + C₁ + c + C₃ + 4)
    generalize 2 ^ (p * n) = E at *
    generalize K * E = KE at *
    have hnE : n ≤ E := by omega
    nlinarith [Nat.mul_le_mul_left C₁ hnE, Nat.mul_le_mul_left p hnE,
      Nat.mul_le_mul_left (C₁ + 2 * p + c + 2 + C₃ + C₁ + c + C₃ + 4) h3]

end PEqualNP.Library.Evasion
