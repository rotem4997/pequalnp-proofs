import PEqualNP.MetaComplexity.Helpers.EdgeFnRun4
import PEqualNP.MetaComplexity.Helpers.ForestElim
import PEqualNP.Library.Helpers.PeelableSanity

/-!
# Run-of-four assembly (row L-meta-658), part 1: the graph side, the free step, the induction

Paper: the run-of-four argument in direct form, section 2 and its list of owed lemmas
section 2 (Lemmas FS, FI) and its local form.

* `asmCls`: every degree at most 3 and the dichotomy "good leaf or run of four" at every
  `delVerts G X` with an edge (the cycle bound of the row is not read by the proof).
* `asm_hered`: closed under `delV`.
* `asm_dich`: a graph of the class with an edge has a good leaf or an `r4Run` whose two outer
  vertices have at most three neighbours each, named.
* `asm_free` (Lemma FS), `asm_free_all` (Lemma FI): the bound at `A = ∅` gives it at every `A`.
* `asm_ind`: the induction on the edge count, from a run step that proves the bound at `A = ∅`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn
open SimpleGraph

/-- The run clauses of the row, at a graph `H`. -/
def asmRunCl {n : ℕ} (H : SimpleGraph (Fin n)) (q0 q1 q2 q3 q4 q5 : Fin n) : Prop :=
  [q1, q2, q3, q4].Nodup ∧ q0 ∉ [q1, q2, q3, q4] ∧ q5 ∉ [q1, q2, q3, q4] ∧
    (∀ w : Fin n, H.Adj q1 w ↔ w = q0 ∨ w = q2) ∧
    (∀ w : Fin n, H.Adj q2 w ↔ w = q1 ∨ w = q3) ∧
    (∀ w : Fin n, H.Adj q3 w ↔ w = q2 ∨ w = q4) ∧
    (∀ w : Fin n, H.Adj q4 w ↔ w = q3 ∨ w = q5)

/-- The class used by the induction: degrees at most 3, and at every `delVerts G X` with an edge
a good leaf or a run of four. -/
def asmCls (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) ∧
    ∀ X : Finset (Fin n), (∃ i j : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj i j) →
      PEqualNP.Library.Peel.GoodLeaf (PEqualNP.Library.Peel.delVerts G X) ∨
        ∃ q0 q1 q2 q3 q4 q5 : Fin n,
          asmRunCl (PEqualNP.Library.Peel.delVerts G X) q0 q1 q2 q3 q4 q5

theorem asm_hered : Hered asmCls := by
  intro n G X ⟨hdeg, hd⟩
  refine ⟨fun v => le_trans (Set.ncard_le_ncard (fun w hw => (delV_adj G X v w).1 hw |>.1)) (hdeg v),
    fun Y hY => ?_⟩
  rw [PEqualNP.Library.Peel.Scratch.delV_eq, PEqualNP.Library.Peel.Scratch.delVerts_delVerts] at hY ⊢
  exact hd _ hY

/-- A vertex `v` adjacent to `u` with at most three neighbours: two names for the others. -/
theorem asm_deg3 {n : ℕ} (G : SimpleGraph (Fin n)) (v u : Fin n)
    (hdeg : (G.neighborSet v).ncard ≤ 3) (hvu : G.Adj v u) :
    ∃ c d : Fin n, ∀ w, G.Adj v w → w = u ∨ w = c ∨ w = d := by
  classical
  set S : Finset (Fin n) := (Finset.univ.filter (fun w => G.Adj v w)).erase u with hS
  have hcard : S.card ≤ 2 := by
    have h1 : (Finset.univ.filter (fun w => G.Adj v w)).card ≤ 3 := by
      have e : ((Finset.univ.filter (fun w => G.Adj v w) : Finset (Fin n)) : Set (Fin n)) =
          G.neighborSet v := by
        ext w; simp
      rw [← e, Set.ncard_coe_finset] at hdeg
      exact hdeg
    have h2 := Finset.card_erase_of_mem (s := Finset.univ.filter (fun w => G.Adj v w))
      (a := u) (by simp [hvu])
    rw [← hS] at h2
    omega
  have hmem : ∀ w, G.Adj v w → w = u ∨ w ∈ S := by
    intro w hw
    by_cases h : w = u
    · exact Or.inl h
    · exact Or.inr (by simp [hS, h, hw])
  interval_cases hc : S.card
  · rw [Finset.card_eq_zero] at hc
    refine ⟨u, u, fun w hw => ?_⟩
    rcases hmem w hw with h | h
    · exact Or.inl h
    · rw [hc] at h; simp at h
  · obtain ⟨c, hc'⟩ := Finset.card_eq_one.1 hc
    refine ⟨c, c, fun w hw => ?_⟩
    rcases hmem w hw with h | h
    · exact Or.inl h
    · rw [hc'] at h; simp at h; exact Or.inr (Or.inl h)
  · obtain ⟨c, d, -, hc'⟩ := Finset.card_eq_two.1 hc
    refine ⟨c, d, fun w hw => ?_⟩
    rcases hmem w hw with h | h
    · exact Or.inl h
    · rw [hc'] at h; simp at h; exact Or.inr h

/-- The run, with its outer vertices of at most three neighbours named. -/
def asmRun4 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ q0 q1 q2 q3 q4 q5 c0 d0 c5 d5 : Fin n, r4Run G q0 q1 q2 q3 q4 q5 ∧
    (∀ w, G.Adj q0 w → w = q1 ∨ w = c0 ∨ w = d0) ∧ (∀ w, G.Adj q5 w → w = q4 ∨ w = c5 ∨ w = d5)

theorem asm_dich {n : ℕ} (G : SimpleGraph (Fin n)) (hG : asmCls n G) (hE : ∃ i j, G.Adj i j) :
    GoodLeaf G ∨ asmRun4 G := by
  obtain ⟨hdeg, hd⟩ := hG
  have hE' : ∃ i j : Fin n, (PEqualNP.Library.Peel.delVerts G ∅).Adj i j := by
    rw [PEqualNP.Library.Peel.Scratch.delVerts_empty]; exact hE
  rcases hd ∅ hE' with h | ⟨q0, q1, q2, q3, q4, q5, hr⟩
  · left
    rw [PEqualNP.Library.Peel.Scratch.delVerts_empty] at h
    exact h
  · right
    rw [PEqualNP.Library.Peel.Scratch.delVerts_empty] at hr
    obtain ⟨nd, o0, o5, h1, h2, h3, h4⟩ := hr
    have hR : r4Run G q0 q1 q2 q3 q4 q5 := ⟨nd, o0, o5, h1, h2, h3, h4⟩
    obtain ⟨c0, d0, hc0⟩ := asm_deg3 G q0 q1 (hdeg q0) (G.adj_symm ((h1 q0).2 (Or.inl rfl)))
    obtain ⟨c5, d5, hc5⟩ := asm_deg3 G q5 q4 (hdeg q5) (G.adj_symm ((h4 q5).2 (Or.inr rfl)))
    exact ⟨q0, q1, q2, q3, q4, q5, c0, d0, c5, d5, hR, hc0, hc5⟩

/-! ## The free step (Lemma FS) and the set induction (Lemma FI) -/

theorem asm_free {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (hinv : AFree G A) (ha : a ∈ A) (hE : ∃ i j, G.Adj i j)
    (hb : BoundOf (HasCircuitSize n) G (A.erase a)) : BoundOf (HasCircuitSize n) G A := by
  intro s hC
  obtain ⟨i, j, hij⟩ := hE
  have hiA : i ∉ A := hinv i j hij
  have hjA : j ∉ A := hinv j i hij.symm
  have hai : a ≠ i := fun e => hiA (e ▸ ha)
  have haj : a ≠ j := fun e => hjA (e ▸ ha)
  have hs : 2 ≤ s + 1 := by
    have := dep_lower_set n (F G A) {a, i} (by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact F_dep_A G A t ha
      · rw [Finset.mem_singleton] at ht
        subst ht
        exact F_dep G A t j hij hjA) s hC
    rwa [Finset.card_pair hai] at this
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := a.2; omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hnc : ∃ x y : Fin (n' + 1) → Bool,
      F G A (Function.update x a false) ≠ F G A (Function.update y a false) := by
    refine ⟨fun _ => false, fun w => decide (w = i ∨ w = j), ?_⟩
    have e1 : Function.update (fun _ : Fin (n' + 1) => false) a false = fun _ => false := by
      funext w; by_cases h : w = a <;> simp [h]
    rw [e1, F_zero]
    have : F G A (Function.update (fun w => decide (w = i ∨ w = j)) a false) = true :=
      F_true_of i j hij (by simp [Function.update_apply, Ne.symm hai])
        (by simp [Function.update_apply, Ne.symm haj])
    rw [this]; simp
  have h1 := one_gate_at n' (F G A) a false s' (F_dep_A G A a ha) hnc hC
  have e : (fun x => F G A (Function.update x a false)) = F G (A.erase a) :=
    funext fun x => Loc.Res.ToolResA_proof _ G A a x hinv ha
  rw [e] at h1
  have h2 := hb s' h1
  have h3 := Finset.card_erase_add_one ha
  unfold Phi1 at h2 ⊢
  omega

theorem asm_free_all {n : ℕ} (G : SimpleGraph (Fin n)) (hE : ∃ i j, G.Adj i j)
    (h0 : BoundOf (HasCircuitSize n) G ∅) :
    ∀ A : Finset (Fin n), AFree G A → BoundOf (HasCircuitSize n) G A := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; exact h0
  | insert a B haB ih =>
    intro hinv
    have hB : AFree G B := fun i j h hi => hinv i j h (Finset.mem_insert_of_mem hi)
    apply asm_free G (insert a B) a hinv (Finset.mem_insert_self a B) hE
    rw [Finset.erase_insert haB]
    exact ih hB

/-! ## The induction -/

/-- The induction on the edge count, from a run step at `A = ∅`. -/
theorem asm_ind {P : (n : ℕ) → SimpleGraph (Fin n) → Prop} (hH : Hered P)
    (hDi : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), P n G → (∃ i j, G.Adj i j) →
      GoodLeaf G ∨ asmRun4 G)
    (hR : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), asmRun4 G → IHV G →
      BoundOf (HasCircuitSize n) G ∅) : StmtA1 P := by
  suffices key : ∀ (e n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      G.edgeSet.ncard = e → P n G → AFree G A → BoundOf (HasCircuitSize n) G A from
    fun n G A hP hinv => key _ n G A rfl hP hinv
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro n G A he hP hinv
  have hih : IHV G := fun X A' hinv' hlt =>
    ihe _ (he ▸ hlt) n (delV G X) A' rfl (hH n G X hP) hinv'
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · intro s hC
    have hE' : ∀ i j, ¬ G.Adj i j := fun i j h => hE ⟨i, j, h⟩
    have hdep := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    have h0 := noedge_ncard G hE'
    have ht := tau_le G ∅ (fun i j h => absurd h (hE' i j))
    rw [Finset.card_empty] at ht
    unfold Phi1
    omega
  rcases hDi n G hP hE with hg | hr
  · exact stmtG6 n G A hinv hih hg
  · exact asm_free_all G hE (hR n G hr hih) A hinv

/-- The row's bound from the class form. -/
theorem asm_row_of_a1 (hA : StmtA1 asmCls) : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 5 ≤ c.length) → (∀ X : Finset (Fin n), (∃ i j : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj i j) → PEqualNP.Library.Peel.GoodLeaf (PEqualNP.Library.Peel.delVerts G X) ∨ ∃ q0 q1 q2 q3 q4 q5 : Fin n, [q1, q2, q3, q4].Nodup ∧ q0 ∉ [q1, q2, q3, q4] ∧ q5 ∉ [q1, q2, q3, q4] ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q1 w ↔ w = q0 ∨ w = q2) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q2 w ↔ w = q1 ∨ w = q3) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q3 w ↔ w = q2 ∨ w = q4) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q4 w ↔ w = q3 ∨ w = q5)) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1 := by
  intro n k s G A hdeg _ hd hinv _ hk hC
  have hb := hA n G A ⟨hdeg, hd⟩ hinv s hC
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  have := hk T hT
  unfold Phi1 at hb
  omega

end PEqualNP.MetaComplexity.Helpers.RunAsm
