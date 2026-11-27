import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2262_2
    (localization : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ),
    IsAO2 n C → TopForm G C → junk G C={d,e} →
    ∀ (u v : Fin n), s(u,v)∈G.edgeFinset → ∀ a∈tops G C, ∀ i : Fin 2, ∀ j : ℕ, (j=d ∨ j=e) →
    gateVal n C a (pairInput u v)=true → OrReaches n C (opnd C a i) j →
    gateVal n C j (pairInput u v)=true →
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    s(u,v)∈A d ∨ s(u,v)∈A e ∨
    ((∀ x, gateVal n C d x=true → gateVal n C e x=true → graphFun G ∅ x=true) ∧
      s(u,v)∈gammaE G C d ∩ gammaE G C e))
    (profiles : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ),
    G=edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → IsAO2 11 C → TopForm G C → junk G C={d,e} →
    ¬InCone 11 C d e → ¬InCone 11 C e d → (∃ a∈tops G C, InCone 11 C d a ∧ InCone 11 C e a) →
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    let both := gammaE G C d ∩ gammaE G C e
    let safe := ∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun G ∅ x=true
    (A d).card≤7 ∧ (A e).card≤7 ∧ (safe → both.card≤8) ∧
    (safe ∨ (wmax G C d ∩ wmax G C e).Nonempty))
    (accounting : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ),
    G=edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → IsLeastAO G C → TopForm G C → C.size<22 → junk G C={d,e} →
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    let both := gammaE G C d ∩ gammaE G C e
    let safe := ∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun G ∅ x=true
    let U := Ustar G C
    ((A d).card≤7 ∧ (A e).card≤7 ∧ (safe → both.card≤8) ∧
    (safe ∨ (wmax G C d ∩ wmax G C e).Nonempty)) → (∀ h∈U, h∈A d ∨ h∈A e ∨ safe ∧ h∈both) →
    ∃ S : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) S ∧
      5+U.card ≤ S.card+2*(centreless G C).card+(orN G C \ lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G inst C d e graph least form T Z U cone sides source budget cover order pair de ed common
  classical
  by_contra! small
  have bounds := profiles G C d e graph least.1 form pair de ed common
  have all (h) (hh : h∈U) :
      h∈(gammaE G C d).filter (fun f => ∃ z∈wmax G C d, z∈f) ∨
      h∈(gammaE G C e).filter (fun f => ∃ z∈wmax G C e, z∈f) ∨
      (∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun G ∅ x=true) ∧
        h∈gammaE G C d ∩ gammaE G C e := by
    induction h using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨a,ha,i,j,which,active,reaches,on⟩ := source u v hh
      have edge : s(u,v)∈G.edgeFinset := (Finset.mem_sdiff.mp hh).1
      exact localization 11 G C d e least.1 form pair u v edge a ha i j which active reaches on
  obtain ⟨S,hs,hc⟩ := accounting G C d e graph least form small pair bounds all
  have sc := cover S hs
  change 5+U.card ≤ S.card+2*Z.card+(orN G C \ lam G C).card at hc
  omega
