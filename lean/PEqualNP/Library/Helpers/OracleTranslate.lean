import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Translating a machine to other stack indices, alphabets, labels and states

Helper module (proofs only, no statement may use it). Given an equivalence of stack indices
`eK`, a map of labels `eΛ`, an equivalence of internal states `eσ`, a map `π` of all stack
symbols into one alphabet `G`, and partial inverses `ι k : G → Option (Γ k)` of `π` on a set
`T` of symbols, `tr` rewrites a statement over the new types. As long as every symbol on the
stacks lies in `T` and every symbol the statement pushes lies in `T`, the translated statement
does exactly what the original does, read through `mapC` (`stepAux_tr`).
-/

open Turing

namespace PEqualNP.Library.Helpers.Enum

set_option linter.unusedSectionVars false

section tr

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  {K' : Type} [DecidableEq K'] {G Λ' σ' : Type}
  (eK : K ≃ K') (eΛ : Λ → Λ') (eσ : σ ≃ σ') (π : (Σ k, Γ k) → G) (ι : ∀ k, G → Option (Γ k))

/-- The translated statement. -/
def tr : TM2.Stmt Γ Λ σ → TM2.Stmt (fun _ : K' => G) Λ' σ'
  | .push k f q => .push (eK k) (fun v => π ⟨k, f (eσ.symm v)⟩) (tr q)
  | .peek k f q => .peek (eK k) (fun v o => eσ (f (eσ.symm v) (o.bind (ι k)))) (tr q)
  | .pop k f q => .pop (eK k) (fun v o => eσ (f (eσ.symm v) (o.bind (ι k)))) (tr q)
  | .load a q => .load (fun v => eσ (a (eσ.symm v))) (tr q)
  | .branch f q₁ q₂ => .branch (fun v => f (eσ.symm v)) (tr q₁) (tr q₂)
  | .goto f => .goto (fun v => eΛ (f (eσ.symm v)))
  | .halt => .halt

/-- The translated stacks. -/
def mapS (S : ∀ k, List (Γ k)) : K' → List G :=
  fun k' => (S (eK.symm k')).map (fun s => π ⟨eK.symm k', s⟩)

/-- The translated configuration. -/
def mapC (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K' => G) Λ' σ' :=
  ⟨c.l.map eΛ, eσ c.var, mapS eK π c.stk⟩

/-- The symbols a statement may push. -/
def pushSet : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ pushSet q
  | .peek _ _ q => pushSet q
  | .pop _ _ q => pushSet q
  | .load _ q => pushSet q
  | .branch _ q₁ q₂ => pushSet q₁ ∪ pushSet q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushSet_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (pushSet q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- Every symbol on the stacks lies in `T`. -/
def Good (T : Set (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k, ∀ s ∈ S k, (⟨k, s⟩ : Σ k, Γ k) ∈ T

theorem mapS_apply (S : ∀ k, List (Γ k)) (k : K) :
    mapS eK π S (eK k) = (S k).map (fun s => π ⟨k, s⟩) := by
  unfold mapS
  rw [Equiv.symm_apply_apply]

theorem mapS_update (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    mapS eK π (Function.update S k l) =
      Function.update (mapS eK π S) (eK k) (l.map (fun s => π ⟨k, s⟩)) := by
  funext k'
  obtain ⟨j, rfl⟩ := eK.surjective k'
  rw [mapS_apply]
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne (eK.injective.ne h), mapS_apply]

theorem mapS_empty : mapS eK π (fun _ => ([] : List (Γ _))) = fun _ => [] := rfl

variable {π ι} (T : Set (Σ k, Γ k))

theorem good_update {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) (l : List (Γ k))
    (hl : ∀ s ∈ l, (⟨k, s⟩ : Σ k, Γ k) ∈ T) : Good T (Function.update S k l) := by
  intro j s hs
  by_cases h : j = k
  · subst h; rw [Function.update_self] at hs; exact hl s hs
  · rw [Function.update_of_ne h] at hs; exact hS j s hs

theorem head_bind (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) :
    ((mapS eK π S (eK k)).head?).bind (ι k) = (S k).head? := by
  rw [mapS_apply]
  have hk := hS k
  cases h : S k with
  | nil => rfl
  | cons s r =>
    rw [h] at hk
    simp only [List.map_cons, List.head?_cons, Option.bind_some]
    exact hι k s (hk s (by simp))

theorem stepAux_tr (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    (q : TM2.Stmt Γ Λ σ) (hq : pushSet q ⊆ T) (v : σ) (S : ∀ k, List (Γ k)) (hS : Good T S) :
    TM2.stepAux (tr eK eΛ eσ π ι q) (eσ v) (mapS eK π S) = mapC eK eΛ eσ π (TM2.stepAux q v S) ∧
      Good T (TM2.stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    have hq' : pushSet q ⊆ T := fun x hx => hq (Or.inr hx)
    have hf : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
    have hS' : Good T (Function.update S k (f v :: S k)) := by
      refine good_update T hS k _ (fun s hs => ?_)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hf
      · exact hS k s hs
    have e : Function.update (mapS eK π S) (eK k) (π ⟨k, f (eσ.symm (eσ v))⟩ :: mapS eK π S (eK k))
        = mapS eK π (Function.update S k (f v :: S k)) := by
      rw [mapS_update, mapS_apply, Equiv.symm_apply_apply, List.map_cons]
    simp only [tr, TM2.stepAux]
    rw [e]
    exact ih hq' v _ hS'
  | peek k f q ih =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply, head_bind eK T hι hS k]
    exact ih hq _ S hS
  | pop k f q ih =>
    have hS' : Good T (Function.update S k (S k).tail) :=
      good_update T hS k _ (fun s hs => hS k s (List.mem_of_mem_tail hs))
    have e : Function.update (mapS eK π S) (eK k) (mapS eK π S (eK k)).tail
        = mapS eK π (Function.update S k (S k).tail) := by
      rw [mapS_update, mapS_apply, List.map_tail]
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply, head_bind eK T hι hS k, e]
    exact ih hq _ _ hS'
  | load a q ih =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply]
    exact ih hq _ S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply]
    cases f v
    · exact ih₂ (fun x hx => hq (Or.inr hx)) v S hS
    · exact ih₁ (fun x hx => hq (Or.inl hx)) v S hS
  | goto f =>
    simp only [tr, TM2.stepAux, Equiv.symm_apply_apply]
    exact ⟨rfl, hS⟩
  | halt =>
    simp only [tr, TM2.stepAux]
    exact ⟨rfl, hS⟩

theorem mapC_inj (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    (heΛ : Function.Injective eΛ) {c c' : TM2.Cfg Γ Λ σ} (hc : Good T c.stk)
    (hc' : Good T c'.stk) (h : mapC eK eΛ eσ π c = mapC eK eΛ eσ π c') : c = c' := by
  obtain ⟨l, v, S⟩ := c
  obtain ⟨l', v', S'⟩ := c'
  simp only [mapC, TM2.Cfg.mk.injEq] at h
  obtain ⟨hl, hv, hS⟩ := h
  have hl' : l = l' := Option.map_injective heΛ hl
  have hv' : v = v' := eσ.injective hv
  subst hl' hv'
  have hS' : S = S' := by
    funext k
    have e := congrFun hS (eK k)
    rw [mapS_apply, mapS_apply] at e
    have e2 := congrArg (List.map (ι k)) e
    rw [List.map_map, List.map_map] at e2
    have r1 : (S k).map (ι k ∘ fun s => π ⟨k, s⟩) = (S k).map some :=
      List.map_congr_left (fun s hs => hι k s (hc k s hs))
    have r2 : (S' k).map (ι k ∘ fun s => π ⟨k, s⟩) = (S' k).map some :=
      List.map_congr_left (fun s hs => hι k s (hc' k s hs))
    rw [r1, r2] at e2
    exact List.map_injective_iff.mpr (Option.some_injective _) e2
  rw [hS']

end tr

end PEqualNP.Library.Helpers.Enum
