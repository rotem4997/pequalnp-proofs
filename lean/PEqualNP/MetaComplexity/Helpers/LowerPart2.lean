import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

/-!
# More on normal-form circuits with one dirty AND

`reach_trans`, `above_and` (every low gate is under an operand of an AND, through ORs), `dup_lt` (a gate with
the function of an earlier wire can go), `PZ` (partner vertices) and its adjacency facts.
-/

namespace PEqualNP.MetaComplexity.LowerPart

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

theorem srcOf_gate (j : ℕ) : srcOf n (n + j) = (some (Sum.inr j) : Src n ℕ) := by
  simp [srcOf]

theorem srcOf_input (v : Fin n) : srcOf n (v : ℕ) = (some (Sum.inl v) : Src n ℕ) := by
  simp [srcOf, v.2]

theorem srcOf_cases (w : ℕ) : (∃ v : Fin n, w = v) ∨ ∃ j, w = n + j := by
  by_cases h : w < n
  · exact Or.inl ⟨⟨w, h⟩, rfl⟩
  · exact Or.inr ⟨w - n, by omega⟩

theorem fin2 (c d : Fin 2) (h : c ≠ d) : d = 1 - c := by
  revert h; revert c d; decide

theorem fin2_inv (c : Fin 2) : 1 - (1 - c) = c := by
  revert c; decide

theorem fin2_ne (c : Fin 2) : c ≠ 1 - c := by
  revert c; decide

theorem fin2_or (c d : Fin 2) : d = c ∨ d = 1 - c := by
  revert c d; decide

theorem fin2_one (i : Fin 2) (h : i ≠ 0) : i = 1 := by
  revert i; decide

theorem fin2_one' (i : Fin 2) (h : 1 - i = 0) : i = 1 := by
  revert i; decide

theorem val_and' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) (c : Fin 2) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k c) x = true ∧ wireVal n C (opnd C k (1 - c)) x = true := by
  rw [val_and C hC k hk ho x]
  fin_cases c
  · exact Iff.rfl
  · exact and_comm

theorem val_or' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C k x = true ↔ ∃ c, wireVal n C (opnd C k c) x = true := by
  rw [val_or C hC k hk ho x]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr h

theorem reach_self (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) : OrReaches n C (n + k) k :=
  (reach_gate C hC k k hk).2 (Or.inl rfl)

theorem reach_trans (C : Circuit) (hC : IsAO2 n C) (k g : ℕ) (hk : k < C.gates.length)
    (hkg : OrReaches n C (n + k) g) : ∀ w < n + C.gates.length, OrReaches n C w k → OrReaches n C w g := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w k hw)) ?_
  intro j hj ih h
  rcases (reach_gate C hC j k hj).1 h with rfl | ⟨ho, c, hc⟩
  · exact hkg
  · exact (reach_gate C hC j g hj).2 (Or.inr ⟨ho, c, ih c hc⟩)

/-- Vertex `z` is a partner variable of the AND `k`. -/
def PZ (C : Circuit) (g k : ℕ) (z : Fin n) : Prop :=
  (OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput z) = true) ∨
  (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput z) = true)

theorem pz_iff (C : Circuit) (g k : ℕ) (z : Fin n) : PZ C g k z ↔
    ∃ c, OrReaches n C (opnd C k c) g ∧ wireVal n C (opnd C k (1 - c)) (unitInput z) = true := by
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr h

theorem pair_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n)
    (h : graphFun G ∅ (pairInput y z) = true) : G.Adj y z := by
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 h
  simp only [pairInput, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)

theorem unit_le (y : Fin n) (x : Fin n → Bool) (hy : x y = true) (a : Fin n) (ha : unitInput y a = true) :
    x a = true := by
  simp only [unitInput, decide_eq_true_eq] at ha
  rw [ha]; exact hy

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

theorem and_pair' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hkg : k ≠ g) (c : Fin 2) (y z : Fin n) (hy : wireVal n C (opnd C k c) (unitInput y) = true)
    (hz : wireVal n C (opnd C k (1 - c)) (unitInput z) = true) : G.Adj y z := by
  fin_cases c
  · exact and_pair H k hk ho hkg y z hy hz
  · exact (and_pair H k hk ho hkg z y hz hy).symm

theorem not_both' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (c : Fin 2) (h : OrReaches n C (opnd C k c) g) : ¬ OrReaches n C (opnd C k (1 - c)) g := by
  intro h'
  fin_cases c
  · exact not_both H k hk ho ⟨h, h'⟩
  · exact not_both H k hk ho ⟨h', h⟩

theorem pz_ne (H : OneDirty G C g) (k : ℕ) (z : Fin n) (h : PZ C g k z) : k ≠ g := by
  rintro rfl
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact not_reach_opnd C H.ao k H.hg 0 h
  · exact not_reach_opnd C H.ao k H.hg 1 h

/-- Where `g` is on and a partner vertex is on, `F` is true. -/
theorem pz_F (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (x : Fin n → Bool) (hx : gateVal n C g x = true) (hz : x z = true) :
    graphFun G ∅ x = true := by
  obtain ⟨c, hr, hw⟩ := (pz_iff C g k z).1 h
  have hl0 := opnd_lt C H.ao k hk c
  have hl1 := opnd_lt C H.ao k hk (1 - c)
  refine H.others k hk ho (pz_ne H k z h) x ((val_and' C H.ao k hk ho x c).2 ⟨?_, ?_⟩)
  · exact (reach_le C H.ao g _ (by omega) hr).2 x hx
  · exact mono C H.ao _ _ (unit_le z x hz) _ (by omega) hw

/-- A partner vertex in one operand of `g` is adjacent to every variable of the other. -/
theorem pz_opnd (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (y : Fin n) (c : Fin 2)
    (hzc : wireVal n C (opnd C g c) (unitInput z) = true)
    (hy : wireVal n C (opnd C g (1 - c)) (unitInput y) = true) : G.Adj z y := by
  apply pair_adj
  have hg := H.hg
  have hl0 := opnd_lt C H.ao g hg c
  have hl1 := opnd_lt C H.ao g hg (1 - c)
  refine pz_F H k hk ho z h _ ((val_and' C H.ao g hg H.gand _ c).2 ⟨?_, ?_⟩) (by simp [pairInput])
  · exact mono C H.ao _ _ (unit_le z _ (by simp [pairInput])) _ (by omega) hzc
  · exact mono C H.ao _ _ (unit_le y _ (by simp [pairInput])) _ (by omega) hy

/-- A low gate lies under an operand of an AND, through ORs. -/
theorem above_and (H : OneDirty G C g) : ∀ k < C.gates.length, Low G C (n + k) →
    ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
  have key : ∀ m, ∀ k < C.gates.length, C.gates.length - k = m → Low G C (n + k) →
      ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk hm hl
      obtain ⟨o, hol, hoo, hob⟩ := out_gate H
      obtain ⟨_, h | ⟨_, hin⟩⟩ := H.cone k hk
      · have : o = k := by omega
        subst this
        exact absurd hob hl
      · rw [LiveSize.cone_iff] at hin
        obtain ⟨j, ⟨hjl, hkj, hmem⟩, _⟩ := Relation.TransGen.head'_iff.1 hin
        obtain ⟨c, hc⟩ := mem_opnd C H.ao j hjl _ hmem
        rcases LeafBound.ao_op H.ao hjl with ho | ho
        · exact ⟨j, hjl, ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩
        · have hjlow : Low G C (n + j) := fun hb => hl fun x hx =>
            below_or H.ao j hjl ho hb c x (by rw [hc]; exact hx)
          obtain ⟨T, hT, hTo, d, hd⟩ := ih (C.gates.length - j) (by omega) j hjl rfl hjlow
          have hlt := opnd_lt C H.ao T hT d
          refine ⟨T, hT, hTo, d, reach_trans C H.ao j k hjl ?_ _ (by omega) hd⟩
          exact (reach_gate C H.ao j k hjl).2 (Or.inr ⟨ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩)
  exact fun k hk => key _ k hk rfl

/-- A gate with the function of an earlier wire can go. -/
theorem dup_lt (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (w : ℕ) (hw : w < n + k)
    (hsame : ∀ x, gateVal n C k x = wireVal n C w x) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  obtain ⟨o, hol, hoo, _⟩ := out_gate H
  let r : ℕ → ℕ := fun u => if u = n + k then w else u
  have hrv : ∀ u x, wireVal n C (r u) x = wireVal n C u x := by
    intro u x
    simp only [r]
    split_ifs with h
    · rw [h, ← hsame x]; rfl
    · rfl
  have hrk : ∀ u, r u ≠ n + k ∧ r u ≤ u := by
    intro u
    simp only [r]
    split_ifs with h <;> omega
  have hsv : ∀ x, srcAt x (fun j => gateVal n C j x) (srcOf n (r C.output)) = graphFun G ∅ x := by
    intro x
    rw [srcAt_srcOf, hrv, ← H.comp]
    rfl
  refine redirect_lt G C ((Finset.range C.gates.length).erase k) ?_ (fun j b => srcOf n (r (opnd C j b))) ?_
    (srcOf n (r C.output)) ?_ (adj_of_AO G C hAO H.comp (by omega)) ?_ ?_ ⟨k, hk, Or.inl (by simp)⟩
  · intro j hj
    exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
  · intro j hj b i hi
    have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    have hlt := opnd_lt C hAO j hjl b
    have hi' := srcOf_inr _ _ hi
    have := hrk (opnd C j b)
    exact ⟨Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩, by omega⟩
  · intro i hi
    have hi' := srcOf_inr _ _ hi
    have := hrk C.output
    exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  · intro x hx
    refine ⟨fun j => gateVal n C j x, super_of_le C hAO _ ?_ _ x ?_, ?_⟩
    · intro j hj
      exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    · intro j _ b h
      rw [srcAt_srcOf, hrv] at h
      exact h
    · rw [hsv x]; exact hx
  · intro p q hpq
    refine ⟨fun j => gateVal n C j (pairInput p q), ?_, ?_⟩
    · intro j hj h
      have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
      simp only at h
      rw [gate_eq C hAO j hjl] at h
      rw [srcAt_srcOf, srcAt_srcOf, hrv, hrv]
      exact h
    · rw [hsv]
      exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩

end

end PEqualNP.MetaComplexity.LowerPart
