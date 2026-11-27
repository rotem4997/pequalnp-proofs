import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17134_412
    (chain : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∃ hs : List ((Fin n → Bool) → Bool),
        hs.length = List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false
            (fun (_ : ℕ) => Bool.false) Bool.false g.op) C.gates ∧
        (∀ j < hs.length, ∃ (S1 S2 : List (Fin n)) (T1 T2 : List ℕ), ∀ x : Fin n → Bool,
          hs.getD j (fun _ => Bool.false) x =
            ((S1.any x || T1.any fun i => (hs.take j).getD i (fun _ => Bool.false) x) &&
              (S2.any x || T2.any fun i => (hs.take j).getD i (fun _ => Bool.false) x))) ∧
        ∃ (S : List (Fin n)) (T : List ℕ), ∀ x : Fin n → Bool,
          PEqualNP.MetaComplexity.circuitFun n C x =
            (S.any x || T.any fun i => hs.getD i (fun _ => Bool.false) x))
    (core :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (v : Fin (11 : ℕ)) (hs : List ((Fin (11 : ℕ) → Bool) → Bool)), v.val < (4 : ℕ) →
        hs.length < (6 : ℕ) →
        (∀ j < hs.length, ∃ (S1 S2 : List (Fin (11 : ℕ))) (T1 T2 : List ℕ), ∀ x : Fin (11 : ℕ) → Bool,
          hs.getD j (fun _ => Bool.false) x =
            ((S1.any x || T1.any fun i => (hs.take j).getD i (fun _ => Bool.false) x) &&
              (S2.any x || T2.any fun i => (hs.take j).getD i (fun _ => Bool.false) x))) →
        ∀ (S : List (Fin (11 : ℕ))) (T : List ℕ), ∃ x : Fin (11 : ℕ) → Bool, x v = Bool.false ∧
          (S.any x || T.any fun i => hs.getD i (fun _ => Bool.false) x) ≠
            PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  intro G v C hv ao agree
  obtain ⟨hs, hlen, hch, S, T, hout⟩ := chain 11 C ao
  by_contra hlt
  have h6 : hs.length < 6 := by rw [hlen]; omega
  obtain ⟨x, hx, hne⟩ := core v hs hv h6 hch S T
  exact hne ((hout x).symm.trans (agree x hx))
