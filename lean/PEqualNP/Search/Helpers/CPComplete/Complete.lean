import PEqualNP.Defs.SearchCP
import Mathlib.Tactic

/-!
# Completeness of cutting planes

Every unsatisfiable set of clauses over a finite variable type has a cutting planes
refutation (Cook, Coullard and Turan 1987). Decision tree over the variables: for a partial
assignment `ρ` on `ds`, derive the clause line saying some variable of `ds` differs from `ρ`.
Leaves come from a falsified axiom weakened by Boolean axioms; two children on `u` are added
(the two literals of `u` sum to the line `0 ≥ -1`) and divided by `2`.
-/

namespace PEqualNP.Search.Helpers.CPComplete

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

theorem append {F : Set (Clause V)} {π₂ : List (CPLine V)} (h₂ : IsCPDerivation F π₂) :
    ∀ {π₁ : List (CPLine V)}, IsCPDerivation F π₁ → IsCPDerivation F (π₁ ++ π₂) := by
  intro π₁ h₁
  induction h₁ with
  | nil => simpa using h₂
  | ax C _ hC ih => exact IsCPDerivation.ax C ih hC
  | boolLo v _ ih => exact IsCPDerivation.boolLo v ih
  | boolHi v _ ih => exact IsCPDerivation.boolHi v ih
  | add _ he he' ih =>
    exact IsCPDerivation.add ih (List.mem_append_left _ he) (List.mem_append_left _ he')
  | mul k _ he ih => exact IsCPDerivation.mul k ih (List.mem_append_left _ he)
  | div d _ he hd hdv ih => exact IsCPDerivation.div d ih (List.mem_append_left _ he) hd hdv

/-- `e` is derivable from `F`: it is a line of some derivation. -/
def Der (F : Set (Clause V)) (e : CPLine V) : Prop :=
  ∃ π, IsCPDerivation F π ∧ e ∈ π

theorem der_ax {F : Set (Clause V)} {C : Clause V} (hC : C ∈ F) : Der F (clauseCP C) :=
  ⟨_, IsCPDerivation.ax C IsCPDerivation.nil hC, List.mem_cons_self⟩

theorem der_lo (F : Set (Clause V)) (v : V) : Der F (fun u => if u = v then 1 else 0, 0) :=
  ⟨_, IsCPDerivation.boolLo v IsCPDerivation.nil, List.mem_cons_self⟩

theorem der_hi (F : Set (Clause V)) (v : V) : Der F (fun u => if u = v then -1 else 0, -1) :=
  ⟨_, IsCPDerivation.boolHi v IsCPDerivation.nil, List.mem_cons_self⟩

theorem der_add {F : Set (Clause V)} {e e' : CPLine V} (h : Der F e) (h' : Der F e') :
    Der F (e + e') := by
  obtain ⟨π₁, h₁, m₁⟩ := h
  obtain ⟨π₂, h₂, m₂⟩ := h'
  exact ⟨_, IsCPDerivation.add (append h₂ h₁) (List.mem_append_left _ m₁)
    (List.mem_append_right _ m₂), List.mem_cons_self⟩

theorem der_div {F : Set (Clause V)} {e : CPLine V} (d : ℕ) (h : Der F e) (hd : 0 < d)
    (hdv : ∀ v, (d : ℤ) ∣ e.1 v) :
    Der F (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) := by
  obtain ⟨π, hπ, m⟩ := h
  exact ⟨_, IsCPDerivation.div d hπ m hd hdv, List.mem_cons_self⟩

/-- The Boolean axiom line of a literal. -/
def litLine (l : V × Bool) : CPLine V :=
  if l.2 then (fun u => if u = l.1 then 1 else 0, 0) else (fun u => if u = l.1 then -1 else 0, -1)

theorem der_lit (F : Set (Clause V)) (l : V × Bool) : Der F (litLine l) := by
  unfold litLine
  split
  · exact der_lo F l.1
  · exact der_hi F l.1

theorem clauseCP_insert {l : V × Bool} {C : Clause V} (hl : l ∉ C) :
    clauseCP (insert l C) = clauseCP C + litLine l := by
  obtain ⟨v, b⟩ := l
  unfold clauseCP litLine
  rw [Finset.sum_insert hl]
  cases b
  · ext u
    · simp only [Prod.fst_add, Pi.add_apply, Finset.sum_insert hl]
      by_cases h : v = u
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    · simp; ring
  · ext u
    · simp only [Prod.fst_add, Pi.add_apply, Finset.sum_insert hl]
      by_cases h : v = u
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    · simp

theorem der_weaken {F : Set (Clause V)} {C : Clause V} (h : Der F (clauseCP C)) :
    ∀ E : Clause V, Der F (clauseCP (C ∪ E)) := by
  intro E
  induction E using Finset.induction_on with
  | empty => simpa using h
  | insert a E _ ih =>
    by_cases ha : a ∈ C ∪ E
    · have : C ∪ insert a E = C ∪ E := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Finset.mem_union.1 ha
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [this]; exact ih
    · have : C ∪ insert a E = insert a (C ∪ E) := by
        rw [Finset.union_insert]
      rw [this, clauseCP_insert ha]
      exact der_add ih (der_lit F a)

/-- The clause saying some variable of `ds` differs from `ρ`. -/
def nclause (ds : Finset V) (ρ : V → Bool) : Clause V :=
  ds.image fun v => (v, !ρ v)

theorem nclause_update {ds : Finset V} {u : V} (hu : u ∉ ds) (ρ : V → Bool) (b : Bool) :
    nclause (insert u ds) (Function.update ρ u b) = insert (u, !b) (nclause ds ρ) := by
  unfold nclause
  rw [Finset.image_insert, Function.update_self]
  congr 1
  apply Finset.image_congr
  intro v hv
  have : v ≠ u := fun h => hu (h ▸ hv)
  simp [Function.update_of_ne this]

theorem not_mem_nclause {ds : Finset V} {u : V} (hu : u ∉ ds) (ρ : V → Bool) (b : Bool) :
    (u, b) ∉ nclause ds ρ := by
  unfold nclause
  rw [Finset.mem_image]
  rintro ⟨v, hv, h⟩
  exact hu ((Prod.mk.inj h).1 ▸ hv)

theorem merge {F : Set (Clause V)} {D : Clause V} {u : V} (hT : (u, true) ∉ D)
    (hF : (u, false) ∉ D) (h1 : Der F (clauseCP (insert (u, false) D)))
    (h0 : Der F (clauseCP (insert (u, true) D))) : Der F (clauseCP D) := by
  rw [clauseCP_insert hF] at h1
  rw [clauseCP_insert hT] at h0
  have h := der_div 2 (der_add h1 h0) (by norm_num) (by
    intro v
    simp only [litLine, Prod.fst_add, Pi.add_apply]
    by_cases hv : v = u
    · subst hv; simp; exact ⟨(clauseCP D).1 v, by ring⟩
    · simp [hv]; exact ⟨(clauseCP D).1 v, by ring⟩)
  convert h using 1
  ext v
  · simp only [litLine, Prod.fst_add, Pi.add_apply]
    by_cases hv : v = u
    · subst hv; simp; omega
    · simp [hv]; omega
  · simp only [litLine, Prod.snd_add]
    simp
    omega

theorem step (F : Set (Clause V)) (hF : ¬ Satisfiable F) :
    ∀ (us : List V) (ds : Finset V), (∀ v, v ∈ ds ∨ v ∈ us) → ∀ ρ : V → Bool,
      Der F (clauseCP (nclause ds ρ)) := by
  intro us
  induction us with
  | nil =>
    intro ds hcov ρ
    have hρ : ¬ Satisfies ρ F := fun h => hF ⟨ρ, h⟩
    unfold Satisfies at hρ
    simp only [not_forall, exists_prop] at hρ
    obtain ⟨C, hC, hCf⟩ := hρ
    have hsub : C ⊆ nclause ds ρ := by
      intro l hl
      obtain ⟨v, b⟩ := l
      have h2 : ρ v ≠ b := fun h => hCf ⟨(v, b), hl, h⟩
      have hv : v ∈ ds := by
        rcases hcov v with h | h
        · exact h
        · simp at h
      unfold nclause
      refine Finset.mem_image.2 ⟨v, hv, ?_⟩
      revert h2; cases ρ v <;> cases b <;> simp
    have := der_weaken (der_ax hC) (nclause ds ρ)
    rwa [Finset.union_eq_right.2 hsub] at this
  | cons u us ih =>
    intro ds hcov ρ
    by_cases hu : u ∈ ds
    · refine ih ds (fun v => ?_) ρ
      rcases hcov v with h | h
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl hu
        · exact Or.inr h
    · have hcov' : ∀ v, v ∈ insert u ds ∨ v ∈ us := by
        intro v
        rcases hcov v with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr h
      have T1 := ih (insert u ds) hcov' (Function.update ρ u true)
      have T0 := ih (insert u ds) hcov' (Function.update ρ u false)
      rw [nclause_update hu] at T1 T0
      exact merge (not_mem_nclause hu ρ true) (not_mem_nclause hu ρ false) T1 T0

variable [Fintype V]

/-- Completeness of cutting planes. -/
theorem complete (F : Set (Clause V)) (hF : ¬ Satisfiable F) :
    ∃ π : List (CPLine V), IsCPRefutation F π := by
  obtain ⟨π, hπ, m⟩ := step F hF Finset.univ.toList ∅
    (fun v => Or.inr (Finset.mem_toList.2 (Finset.mem_univ v))) (fun _ => false)
  refine ⟨π, hπ, ?_⟩
  have : clauseCP (nclause (∅ : Finset V) (fun _ => false)) = ((0 : V → ℤ), (1 : ℤ)) := by
    unfold nclause clauseCP
    ext v <;> simp
  rwa [this] at m

end PEqualNP.Search.Helpers.CPComplete
