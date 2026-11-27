import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Statements over finite types form a countable type

Helper module (proofs only, no statement may use it). A statement is written in prefix (Polish)
form as a list of labels, each label being one constructor with its non-recursive data. The
labels form a finite type when the stack indices, the alphabets, the labels and the internal
states are finite, and the prefix form is injective, so the statements are countable.
-/

open Turing

namespace PEqualNP.Library.Helpers.Enum

set_option linter.unusedSimpArgs false

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- One constructor of a statement with its non-recursive data. -/
abbrev StmtLabel (Γ : K → Type) (Λ σ : Type) :=
  (Σ k, σ → Γ k) ⊕ (Σ k, σ → Option (Γ k) → σ) ⊕ (Σ k, σ → Option (Γ k) → σ) ⊕ (σ → σ) ⊕
    (σ → Bool) ⊕ (σ → Λ) ⊕ Unit

/-- The prefix form of a statement. -/
def stmtCode : TM2.Stmt Γ Λ σ → List (StmtLabel Γ Λ σ)
  | .push k f q => .inl ⟨k, f⟩ :: stmtCode q
  | .peek k f q => .inr (.inl ⟨k, f⟩) :: stmtCode q
  | .pop k f q => .inr (.inr (.inl ⟨k, f⟩)) :: stmtCode q
  | .load a q => .inr (.inr (.inr (.inl a))) :: stmtCode q
  | .branch f q₁ q₂ => .inr (.inr (.inr (.inr (.inl f)))) :: (stmtCode q₁ ++ stmtCode q₂)
  | .goto f => [.inr (.inr (.inr (.inr (.inr (.inl f)))))]
  | .halt => [.inr (.inr (.inr (.inr (.inr (.inr ())))))]

theorem stmtCode_append_inj (s : TM2.Stmt Γ Λ σ) :
    ∀ (t : TM2.Stmt Γ Λ σ) (l l' : List (StmtLabel Γ Λ σ)),
      stmtCode s ++ l = stmtCode t ++ l' → s = t ∧ l = l' := by
  induction s with
  | push k f q ih =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.cons.injEq, reduceCtorEq,
      false_and, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, hf⟩, h⟩ := h
    obtain rfl := eq_of_heq hf
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h
    exact ⟨rfl, rfl⟩
  | peek k f q ih =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.cons.injEq, reduceCtorEq,
      false_and, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, hf⟩, h⟩ := h
    obtain rfl := eq_of_heq hf
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h
    exact ⟨rfl, rfl⟩
  | pop k f q ih =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.cons.injEq, reduceCtorEq,
      false_and, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, hf⟩, h⟩ := h
    obtain rfl := eq_of_heq hf
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h
    exact ⟨rfl, rfl⟩
  | load a q ih =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.cons.injEq, reduceCtorEq,
      false_and, Sum.inl.injEq, Sum.inr.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h
    exact ⟨rfl, rfl⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.cons.injEq, reduceCtorEq,
      false_and, Sum.inl.injEq, Sum.inr.injEq, List.append_assoc] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, h2⟩ := ih₁ _ _ _ h
    obtain ⟨rfl, rfl⟩ := ih₂ _ _ _ h2
    exact ⟨rfl, rfl⟩
  | goto f =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.nil_append, List.cons.injEq,
      reduceCtorEq, false_and, Sum.inl.injEq, Sum.inr.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | halt =>
    intro t l l' h
    cases t <;> simp only [stmtCode, List.cons_append, List.nil_append, List.cons.injEq,
      reduceCtorEq, false_and, Sum.inl.injEq, Sum.inr.injEq] at h
    exact ⟨rfl, h.2⟩

theorem stmtCode_injective : Function.Injective (stmtCode : TM2.Stmt Γ Λ σ → _) := by
  intro s t h
  exact (stmtCode_append_inj s t [] [] (by simpa using h)).1

theorem stmt_countable [Countable (StmtLabel Γ Λ σ)] : Countable (TM2.Stmt Γ Λ σ) :=
  stmtCode_injective.countable

instance stmt_countable_fin (a b c d : ℕ) :
    Countable (TM2.Stmt (fun _ : Fin a => Fin d) (Fin b) (Fin c)) :=
  stmt_countable

end PEqualNP.Library.Helpers.Enum
