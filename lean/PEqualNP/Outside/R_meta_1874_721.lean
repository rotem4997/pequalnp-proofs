import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.LowMerge

-- A leak is a nonincident singleton pair accepted by one wire. Compatible opposite leaks fit into one quadrangle.
-- The middle child concerns only a fixed 117-vertex graph, not circuit evaluation.
theorem PEqualNP.Outside.R_meta_1874_721
  (crossing : ∀ (C : Circuit) (a b : ℕ), Monotone2 C → let V := fun (w : ℕ) (Q : Finset (Fin 13)) => wireVal C (incidenceInput Q (missLines singerLines3 Q)) w; let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 ∉ singerLines3 e.2 ∧ wireVal C (incidenceInput {e.1} {e.2}) w = true); (∀ Q, IsQuadrangle singerLines3 Q → V a Q=false ∨ V b Q=false) → ∀ e∈E a, ∀ f∈E b, e.1∈singerLines3 f.2 ∨ f.1∈singerLines3 e.2)
  (packing : ∀ (A B : Finset (Fin 13 × Fin 13)), (∀ e∈A∪B, e.1∉singerLines3 e.2) → (∀ e∈A, ∀ f∈B, e.1∈singerLines3 f.2 ∨ f.1∈singerLines3 e.2) → A.card≤12 ∨ B.card≤12)
  (sparse : ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → a < 26+C.size → b < 26+C.size → let V := fun (w : ℕ) (Q : Finset (Fin 13)) => wireVal C (incidenceInput Q (missLines singerLines3 Q)) w; let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 ∉ singerLines3 e.2 ∧ wireVal C (incidenceInput {e.1} {e.2}) w = true); (E a).card≤12 → RightOnIncidentPairs singerLines3 ⟨C.gates,a⟩ → RightOnIncidentPairs singerLines3 ⟨C.gates,b⟩ → (∀ Q, IsQuadrangle singerLines3 Q → V a Q=false ∨ V b Q=false) → (∃ Q, IsQuadrangle singerLines3 Q ∧ V a Q=false ∧ V b Q=true) → (∃ Q, IsQuadrangle singerLines3 Q ∧ V b Q=false ∧ V a Q=true) → 63≤C.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  classical
  intro C a b mono back va vb d posIn negIn good W yes safe wa wb
  have eqI : ∀ p l : Fin 13, p∈singerLines3 l ↔ p-l∈d := by decide
  have pos (p l : Fin 13) : incidenceInput {p} {l}=posIn p l := by
    change List.ofFn (fun i : Fin 13 => decide (i∈({p} : Finset _))) ++ List.ofFn (fun i : Fin 13 => decide (i∈({l} : Finset _)))=_
    simp only [Finset.mem_singleton]; rfl
  have quad (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ good Q := by
    have eq (l : Fin 13) : Q∩singerLines3 l=Q.filter (fun p => p-l∈d) := by ext p; simp only [Finset.mem_inter,Finset.mem_filter,eqI]
    change (Q.card=4 ∧ ∀ l, (Q∩singerLines3 l).card≤2) ↔ _; simp only [eq]; rfl
  have neg (Q : Finset (Fin 13)) : incidenceInput Q (missLines singerLines3 Q)=negIn Q := by
    have misses (l : Fin 13) : l∈missLines singerLines3 Q ↔ ∀ p∈Q, p-l∉d := by
      change l∈Finset.univ.filter (fun k => Disjoint (singerLines3 k) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,eqI]
    change (List.ofFn _ ++ List.ofFn (fun l : Fin 13 => decide (l∈missLines singerLines3 Q)))=_; simp only [misses]; rfl
  let V := fun (w : ℕ) (Q : Finset (Fin 13)) => wireVal C (incidenceInput Q (missLines singerLines3 Q)) w
  let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 ∉ singerLines3 e.2 ∧ wireVal C (incidenceInput {e.1} {e.2}) w = true)
  have both w (hw : w=a ∨ w=b) : RightOnIncidentPairs singerLines3 ⟨C.gates,w⟩ := by
    intro l p h; change wireVal C (incidenceInput {p} {l}) w=true; rw [pos]; rcases hw with rfl|rfl
    · exact (yes _ _ ((eqI ..).mp h)).1
    · exact (yes _ _ ((eqI ..).mp h)).2
  have valEq w Q : V w Q=W w (negIn Q) := by change wireVal C _ w=_; rw [neg]; rfl
  have sn : ∀ Q, IsQuadrangle singerLines3 Q → V a Q=false ∨ V b Q=false := by intro Q h; simpa only [valEq] using safe Q ((quad Q).mp h)
  have wit (x y : ℕ) (h : ∃ Q, good Q ∧ W x (negIn Q)=false ∧ W y (negIn Q)=true) : ∃ Q, IsQuadrangle singerLines3 Q ∧ V x Q=false ∧ V y Q=true := by
    obtain ⟨Q,h,z,t⟩ := h; exact ⟨Q,(quad Q).mpr h,(valEq x Q).trans z,(valEq y Q).trans t⟩
  have miss : ∀ e∈E a∪E b, e.1∉singerLines3 e.2 := by
    intro e h; rcases Finset.mem_union.mp h with h|h <;> exact (Finset.mem_filter.mp h).2.1
  rcases packing (E a) (E b) miss (crossing C a b mono sn) with ha|hb
  · exact sparse C a b mono back va vb ha (both _ (.inl rfl)) (both _ (.inr rfl)) sn (wit _ _ wa) (wit _ _ wb)
  · exact sparse C b a mono back vb va hb (both _ (.inr rfl)) (both _ (.inl rfl)) (fun Q h => (sn Q h).symm) (wit _ _ wb) (wit _ _ wa)
