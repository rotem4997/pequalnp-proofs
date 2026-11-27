import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1772_418
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      (∃ a b, G.Adj a b) → (∀ a, G.degree a ≠ 1) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n C j u v)
    (restore : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      ∀ a b, G.degree a = 1 → G.Adj a b → H = G.deleteEdges {s(a,b)} →
      (∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun H ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, H.Adj u v ∧ Owns n C j u v) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n C j u v) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G decG tri four
  classical
  let good := fun (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] => ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun H ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, H.Adj u v ∧ Owns n C j u v
  change good G
  suffices all : ∀ k : ℕ, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.edgeFinset.card = k → (∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a) →
      NoFourCycle H → good H by
    exact all _ G rfl tri four
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro H decH count ht hf
    by_cases hex : ∃ a b, H.Adj a b
    · by_cases leaf : ∃ a, H.degree a = 1
      · obtain ⟨a, ha⟩ := leaf
        obtain ⟨b, hab⟩ := (H.degree_pos_iff_exists_adj (v := a)).mp (by omega)
        let K := H.deleteEdges {s(a,b)}
        have sub : K ≤ H := H.deleteEdges_le _
        have missing : ¬ K.Adj a b := by simp [K, SimpleGraph.deleteEdges_adj]
        have strict : K < H := lt_of_le_of_ne sub (fun eq => missing (eq ▸ hab))
        have less : K.edgeFinset.card < k := count ▸ Finset.card_lt_card
          (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr strict)
        apply restore n H K ht hf a b ha hab rfl
        apply ih _ less K rfl
        · exact fun i j l hij hjl hli => ht i j l (sub hij) (sub hjl) (sub hli)
        · intro i j hij
          apply le_trans _ (hf i j hij)
          apply Finset.card_le_card
          intro z hz
          obtain ⟨_, hzi, hzj⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub hzi, sub hzj⟩
      · exact core n H ht hf hex (fun a ha => leaf ⟨a,ha⟩)
    · have empty : ∀ a b, ¬ H.Adj a b := fun a b hab => hex ⟨a,b,hab⟩
      refine ⟨⟨[], n⟩, ⟨by intro g hg; exact False.elim (List.not_mem_nil hg), fun _ _ _ => Nat.zero_le _⟩, ?_, ?_⟩
      · funext x
        change (List.ofFn x).getD n false =
          (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
           decide (∃ a b, H.Adj a b ∧ x a = true ∧ x b = true))
        simp [empty, List.getD_eq_getElem?_getD]
      · intro j hj
        simp at hj
