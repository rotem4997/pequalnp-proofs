import PEqualNP.Library.Helpers.TableauStep

/-!
# A whole run of a stack machine as a layered circuit

Helper module (proofs only, no statement may use it).

* `sim_init`: the bits of the initial configuration on input bits `ρ`, a constant number of
  gates per bit.
* `run_bits`: for `n + p * tt ≤ H`, a `Sim` from the `n` input bits to the bits of the
  configuration after `tt` total steps, of size linear in `H` per step.
-/

open Turing

namespace PEqualNP.Library.Helpers.Tableau

open PEqualNP.Library.Helpers.Enum
open Classical

set_option linter.unusedSectionVars false
set_option linter.deprecated false

section run

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} [Fintype Λ]
  [Fintype σ] (T : Set (Σ k, Γ k)) [Fintype T] (H d p : ℕ)
  (k₀ : K) (main : Λ) (s0 : σ) (ι : Bool → Γ k₀)

/-- The initial configuration on input bits `ρ`. -/
def initCfg {n : ℕ} (ρ : Fin n → Bool) : TM2.Cfg Γ Λ σ :=
  ⟨some main, s0, Function.update (fun _ => []) k₀ ((List.ofFn ρ).map ι)⟩

theorem init_det {n : ℕ} (ρ ρ' : Fin n → Bool) (k : K) (i : ℕ)
    (h : ∀ hi : i < n, ρ ⟨n - 1 - i, by omega⟩ = ρ' ⟨n - 1 - i, by omega⟩) :
    ((initCfg k₀ main s0 ι ρ).stk k).reverse[i]? =
      ((initCfg k₀ main s0 ι ρ').stk k).reverse[i]? := by
  by_cases hk : k = k₀
  · subst hk
    simp only [initCfg, Function.update_self]
    by_cases hi : i < n
    · rw [List.getElem?_reverse (by simpa using hi), List.getElem?_reverse (by simpa using hi)]
      simp only [List.length_map, List.length_ofFn, List.getElem?_map, List.getElem?_ofFn]
      rw [dif_pos (by omega), dif_pos (by omega)]
      simp only [Option.map_some]
      rw [h hi]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · simp [initCfg, Function.update_of_ne hk]

theorem init_len {n : ℕ} (ρ : Fin n → Bool) (k : K) :
    ((initCfg k₀ main s0 ι ρ).stk k).length = if k = k₀ then n else 0 := by
  by_cases hk : k = k₀
  · subst hk; simp [initCfg]
  · simp [initCfg, hk]

theorem sim_init (n : ℕ) :
    ∃ F : (Fin n → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H) * 14) ∧
      ∀ ρ, F ρ = enc T H (initCfg k₀ main s0 ι ρ) := by
  have key : ∀ j : Idx Λ σ T H, ∃ E : Ex (Fin n), Ex.size E ≤ 14 ∧
      ∀ ρ, Ex.eval ρ E = enc T H (initCfg k₀ main s0 ι ρ) j := by
    intro j
    rcases j with l | s | ⟨k, i, g⟩ | ⟨k, i⟩
    · exact ⟨.const (decide (some main = l)), by simp [Ex.size], fun ρ => rfl⟩
    · exact ⟨.const (decide (s0 = s)), by simp [Ex.size], fun ρ => rfl⟩
    · let v : Unit → Ex (Fin n) := fun _ =>
        if hi : i.1 < n then .var ⟨n - 1 - i.1, by omega⟩ else .const false
      have hv : ∀ u, Ex.size (v u) = 1 := by intro u; simp only [v]; split_ifs <;> rfl
      obtain ⟨E, hs, he⟩ := exists_ex_det (V := Unit)
        (fun ρ (_ : Unit) => Ex.eval ρ (v ())) (fun _ => True)
        (fun ρ => enc T H (initCfg k₀ main s0 ι ρ) (.inr (.inr (.inl (k, i, g)))))
        (fun x y _ _ hxy => by
          simp only [enc]
          rw [init_det k₀ main s0 ι x y k i.1]
          intro hi
          have := congrFun hxy ()
          simpa [v, hi, Ex.eval] using this)
      refine ⟨Ex.bind v E, ?_, fun ρ => ?_⟩
      · rw [Ex.size_bind v hv]; simp at hs; omega
      · rw [Ex.eval_bind]; exact he ρ trivial
    · refine ⟨.const (decide (i.1 < if k = k₀ then n else 0)), by simp [Ex.size], fun ρ => ?_⟩
      simp only [Ex.eval, enc, init_len]
  choose eI h1 h2 using key
  refine ⟨_, sim_mono (sim_layer eI) ?_, fun ρ => funext fun j => h2 j ρ⟩
  refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => h1 j)).trans ?_
  simp

theorem stepT_len (M : Λ → TM2.Stmt Γ Λ σ)
    (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p) (c : TM2.Cfg Γ Λ σ) (k : K) :
    ((stepT M c).stk k).length ≤ (c.stk k).length + p := by
  cases hl : c.l with
  | none => rw [stepT_none M c hl]; omega
  | some l =>
    simp only [stepT, hl]
    exact (PEqualNP.Library.Machines.stepAux_length _ _ _ _).trans (by have := hp l; omega)

theorem stepT_good (M : Λ → TM2.Stmt Γ Λ σ) (hT : ∀ l, pushSet (M l) ⊆ T) (c : TM2.Cfg Γ Λ σ)
    (hc : Good T c.stk) : Good T (stepT M c).stk := by
  cases hl : c.l with
  | none => rw [stepT_none M c hl]; exact hc
  | some l =>
    simp only [stepT, hl]
    exact good_stepAux T (M l) (hT l) c.var c.stk hc

theorem run_bits (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p) (hT : ∀ l, pushSet (M l) ⊆ T)
    (hι : ∀ b, (⟨k₀, ι b⟩ : Σ k, Γ k) ∈ T) (n tt : ℕ) (hH : n + p * tt ≤ H) :
    ∃ F : (Fin n → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H) * 14 +
        tt * (Fintype.card (Idx (K := K) Λ σ T H ⊕ Wix (K := K) Λ σ T d) * (7 * H + 1) +
          Fintype.card (Idx (K := K) Λ σ T H) * CB (Λ := Λ) (σ := σ) T d p)) ∧
      ∀ ρ, F ρ = enc T H ((stepT M)^[tt] (initCfg k₀ main s0 ι ρ)) := by
  obtain ⟨FI, hI, eI⟩ := sim_init T H k₀ main s0 ι n
  obtain ⟨FS, hS, eS⟩ := sim_step T H d p M hd hp
  refine ⟨fun ρ => FS^[tt] (FI ρ), sim_comp hI (sim_iter hS tt), fun ρ => ?_⟩
  -- invariants along the run
  have hgood : ∀ j, Good T ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)).stk := by
    intro j
    induction j with
    | zero =>
      intro k s hs
      by_cases hk : k = k₀
      · subst hk
        simp only [Function.iterate_zero, id, initCfg, Function.update_self, List.mem_map] at hs
        obtain ⟨b, _, rfl⟩ := hs
        exact hι b
      · simp [initCfg, Function.update_of_ne hk] at hs
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact stepT_good T M hT _ ih
  have hlen : ∀ j k, (((stepT M)^[j] (initCfg k₀ main s0 ι ρ)).stk k).length ≤ n + p * j := by
    intro j
    induction j with
    | zero =>
      intro k
      simp only [Function.iterate_zero, id, init_len]
      split_ifs <;> omega
    | succ j ih =>
      intro k
      rw [Function.iterate_succ_apply']
      have := stepT_len p M hp ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)) k
      have := ih k
      rw [Nat.mul_succ]; omega
  have main' : ∀ j, j ≤ tt →
      FS^[j] (FI ρ) = enc T H ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)) := by
    intro j
    induction j with
    | zero => intro _; simp [eI]
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      apply eS _ (hgood j)
      intro k
      have := hlen j k
      have : p * j ≤ p * tt := Nat.mul_le_mul_left _ (by omega)
      omega
  exact main' tt le_rfl

end run

end PEqualNP.Library.Helpers.Tableau
