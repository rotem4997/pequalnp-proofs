import PEqualNP.Defs

open PEqualNP.AndCount

-- Up to twenty gates leave six genuine incidence flags at one internal gate.
-- Each flag crosses its two bare sides, crosses no output gate's bare sides,
-- and reaches an output through gates true on that two-vertex input.
theorem PEqualNP.Outside.R_meta_7840_491
    (extract : let G := SimpleGraph.fromRel (fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List ℕ))
    ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ → (∀ i v, C.gateVal {v} i = false) →
    (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size ≤ 20 → 19 ≤ C.size ∧ (let raw := fun (i : Fin C.size) (e : Fin 42 × Fin 42) =>
      (e.1 ∈ C.leftVars i ∧ e.2 ∈ C.rightVars i) ∨ (e.2 ∈ C.leftVars i ∧ e.1 ∈ C.rightVars i)
    ∃ i : Fin C.size, i ∉ C.outGates ∧ ∃ S : Finset (Fin 42 × Fin 42), S.card = 6 ∧
      ∀ e ∈ S, e.1.val < 21 ∧ G.Adj e.1 e.2 ∧ raw i e ∧
        (∀ o ∈ C.outGates, ¬ raw o e) ∧
        ∃ o ∈ C.outGates, Relation.ReflTransGen (fun a b : Fin C.size =>
          (a ∈ C.leftGates b ∨ a ∈ C.rightGates b) ∧ C.gateVal {e.1,e.2} b = true) i o))
    (separate : let G := SimpleGraph.fromRel (fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List ℕ))
    ∀ C : AndCountCircuit 42, C.WellFormed → C.outVars = ∅ → (∀ i v, C.gateVal {v} i = false) →
    (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → (C.size = 19 ∨ C.size = 20) →
    (∀ u v, G.Adj u v → C.eval {u,v} = true) → (let raw := fun (i : Fin C.size) (e : Fin 42 × Fin 42) =>
      (e.1 ∈ C.leftVars i ∧ e.2 ∈ C.rightVars i) ∨ (e.2 ∈ C.leftVars i ∧ e.1 ∈ C.rightVars i)
    ∃ i : Fin C.size, i ∉ C.outGates ∧ ∃ S : Finset (Fin 42 × Fin 42), S.card = 6 ∧
      ∀ e ∈ S, e.1.val < 21 ∧ G.Adj e.1 e.2 ∧ raw i e ∧
        (∀ o ∈ C.outGates, ¬ raw o e) ∧
        ∃ o ∈ C.outGates, Relation.ReflTransGen (fun a b : Fin C.size =>
          (a ∈ C.leftGates b ∨ a ∈ C.rightGates b) ∧ C.gateVal {e.1,e.2} b = true) i o) →
    ∃ X : Finset (Fin 42), Maximal (fun Y : Finset (Fin 42) =>
      ∀ u ∈ Y, ∀ v ∈ Y, ¬ G.Adj u v) X ∧ C.eval X = true) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → (∃ (x8 : Fin x2.size), ∃ x9 ∈ x2.leftVars x8, ∃ x10 ∈ x2.rightVars x8, ¬x1.Adj x9 x10) → (21 : ℕ) ≤ x2.size := by
  intro G C wf computes empty off apart _
  by_contra! low
  have small : C.size ≤ 20 := by omega
  obtain ⟨nineteen,witness⟩ := extract C wf computes empty off apart small
  have sizes : C.size = 19 ∨ C.size = 20 := by omega
  have yes (u v : Fin 42) (edge : G.Adj u v) : C.eval {u,v} = true :=
    (computes _).mpr ⟨u,by simp,v,by simp,edge⟩
  obtain ⟨X,maximal,accept⟩ := separate C wf empty off apart sizes yes witness
  obtain ⟨u,hu,v,hv,edge⟩ := (computes X).mp accept
  exact maximal.1 u hu v hv edge
