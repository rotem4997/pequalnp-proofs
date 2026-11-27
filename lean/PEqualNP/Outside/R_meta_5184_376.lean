import Mathlib
import PEqualNP.Defs

open SimpleGraph PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitLowerBounds

-- The first bound accounts for the eleven edges whose deletion permits a new five-set.
-- At positive slack the second bound tests only inclusion-minimal induced edge sets.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5184_376
  (budget :
    let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ a b : ℕ, junk G C = {a,b} ∧ InCone 11 C a b) →
      let U := Ustar G C
      let p := 2 * (centreless G C).card + (orN G C \ lam G C).card
      2 ≤ U.card → U.card + (if U ⊆ ({s(4,10),s(5,8),s(6,10),s(7,9),s(8,9)} : Finset (Sym2 (Fin 11))) then 0 else 1) ≤ 2+p)
  (larger :
    let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ a b : ℕ, junk G C = {a,b} ∧ InCone 11 C a b) →
      let U := Ustar G C
      let p := 2 * (centreless G C).card + (orN G C \ lam G C).card
      let d := 2 + p - U.card
      let cuts := (Finset.univ.filter (fun A : Finset (Fin 11) => A.card = 5+d ∧ ¬ ({3,8,9,10} : Finset (Fin 11)) ⊆ A)).image
        (fun A => G.edgeFinset ∩ A.sym2)
      0 < d → ([1,2,3,5,8,12] : List ℕ).getD d 0 ≤ U.card →
      ∀ B ∈ cuts, (∀ B' ∈ cuts, B' ⊂ B → False) → ¬ B ⊆ U)
  : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               x13 ≠ ∅ →                 (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →                   have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};                   have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};                   (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  have g11Cover5184 (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj]
      (T : Finset (Fin 11)) (M : Finset (Fin 11 × Fin 11))
      (split : ∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T ∨ (a,b) ∈ M ∨ (b,a) ∈ M)
      (S : Finset (Fin 11)) (sub : S ⊆ T) (nonempty : S ≠ ∅)
      (indep : ∀ a ∈ T \ S, ∀ b ∈ T \ S, ¬ H.Adj a b) :
      let N : Finset (Fin 11) := {v ∈ Finset.univ \ T | ∃ u ∈ T \ S, H.Adj u v}
      let R : Finset (Fin 11 × Fin 11) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ N ∧ e.2 ∉ N}
      ∃ K : Finset (Fin 11), (∃ t ∈ T, t ∈ K) ∧ K.card ≤ S.card + N.card + R.card ∧
        ∀ a b, H.Adj a b → a ∈ K ∨ b ∈ K := by
    clear budget larger
    intro N R
    let K := (S ∪ N) ∪ R.image Prod.fst
    have inS {v : Fin 11} (h : v ∈ S) : v ∈ K :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    have inN {v : Fin 11} (h : v ∈ N) : v ∈ K :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
    have inR {a b : Fin 11} (h : (a,b) ∈ R) : a ∈ K :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(a,b),h,rfl⟩))
    have atT {a b : Fin 11} (ha : a ∈ T) (edge : H.Adj a b) : a ∈ K ∨ b ∈ K := by
      by_cases sa : a ∈ S
      · exact Or.inl (inS sa)
      have da : a ∈ T \ S := Finset.mem_sdiff.mpr ⟨ha,sa⟩
      by_cases sb : b ∈ S
      · exact Or.inr (inS sb)
      have outside : b ∉ T := fun hb => indep a da b (Finset.mem_sdiff.mpr ⟨hb,sb⟩) edge
      apply Or.inr
      apply inN
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,outside⟩,a,da,edge⟩
    have atM {a b : Fin 11} (h : (a,b) ∈ M) (edge : H.Adj a b) : a ∈ K ∨ b ∈ K := by
      by_cases na : a ∈ N
      · exact Or.inl (inN na)
      by_cases nb : b ∈ N
      · exact Or.inr (inN nb)
      exact Or.inl (inR (b := b) (Finset.mem_filter.mpr ⟨h,edge,na,nb⟩))
    refine ⟨K,?_,?_,?_⟩
    · obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
      exact ⟨t,sub ht,inS ht⟩
    · calc
        K.card ≤ (S ∪ N).card + (R.image Prod.fst).card := Finset.card_union_le _ _
        _ ≤ S.card + N.card + R.card := Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le
    · intro a b edge
      rcases split a b edge with ha | hb | hab | hba
      · exact atT ha edge
      · exact (atT hb edge.symm).symm
      · exact atM hab edge
      · exact (atM hba edge.symm).symm

  have g11Geometry5184 :
      let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
      let safe := ({s(4,10),s(5,8),s(6,10),s(7,9),s(8,9)} : Finset (Sym2 (Fin 11)))
      ∀ A : Finset (Fin 11), (A.card = 5 → ¬ G.edgeFinset ∩ A.sym2 ⊆ safe) ∧
        ([0,0,0,0,0,1,2,3,5,8,12,16] : List ℕ).getD A.card 0 ≤ (G.edgeFinset ∩ A.sym2).card := by
    clear budget larger g11Cover5184
    intro G safe
    let es := ({s(0,9),s(0,10),s(1,4),s(1,8),s(2,5),s(2,10),s(3,6),s(3,7),s(4,8),s(4,10),s(5,8),s(5,9),s(6,7),s(6,10),s(7,9),s(8,9)} : Finset (Sym2 (Fin 11)))
    have table : ∀ a b : Fin 11, G.Adj a b ↔ s(a,b) ∈ es := by decide +kernel
    have names : G.edgeFinset = es := by
      ext e
      induction e using Sym2.inductionOn with
      | _ a b => exact SimpleGraph.mem_edgeFinset.trans (G.mem_edgeSet.trans (table a b))
    rw [names]
    decide +kernel

  have g11Ports : ∀ a b : Fin 11, (edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))).Adj a b →
      a ∈ ({3,8,9,10} : Finset (Fin 11)) ∨ b ∈ ({3,8,9,10} : Finset (Fin 11)) ∨
      (a,b) ∈ ({(1,4),(2,5),(6,7)} : Finset (Fin 11 × Fin 11)) ∨
      (b,a) ∈ ({(1,4),(2,5),(6,7)} : Finset (Fin 11 × Fin 11)) := by decide +kernel
  intro graph inst C ident least top size nested
  subst graph
  let codes : List ℕ := [9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97]
  let es := codes.map (fun n => (n / 11,n % 11))
  let G := edgeGraph 11 es
  let ref (a b : Fin 11) : Decidable (G.Adj a b) :=
    inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ es ∨ (b.val,a.val) ∈ es)))
  have sameInst : inst = ref := Subsingleton.elim _ _
  subst inst
  let U := Ustar G C
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let T := ({3,8,9,10} : Finset (Fin 11))
  let pairs := ({(1,4),(2,5),(6,7)} : Finset (Fin 11 × Fin 11))
  let safe := ({s(4,10),s(5,8),s(6,10),s(7,9),s(8,9)} : Finset (Sym2 (Fin 11)))
  let pay := 2 * (centreless G C).card + (orN G C \ lam G C).card
  intro postedU postedH postedT postedPairs S hS nonempty ind neighbors savedPairs
  have ports : ∀ a b : Fin 11, G.Adj a b → a ∈ T ∨ b ∈ T ∨ (a,b) ∈ pairs ∨ (b,a) ∈ pairs := g11Ports
  have portsH (a b : Fin 11) (h : H.Adj a b) : a ∈ T ∨ b ∈ T ∨ (a,b) ∈ pairs ∨ (b,a) ∈ pairs :=
    ports a b (SimpleGraph.deleteEdges_adj.mp h).1
  obtain ⟨K,meet,count,cover⟩ := g11Cover5184 H T pairs portsH S hS nonempty ind
  change K.card ≤ S.card + neighbors.card + savedPairs.card at count
  suffices 5 + U.card ≤ K.card + pay by
    change 5 + U.card ≤ S.card + neighbors.card + savedPairs.card + 2 * (centreless G C).card + (orN G C \ lam G C).card
    dsimp only [pay] at this
    omega
  have credit := budget C least top size nested
  change 2 ≤ U.card → U.card + (if U ⊆ safe then 0 else 1) ≤ 2 + pay at credit
  have paid : U.card ≤ 2 + pay := by
    by_cases two : 2 ≤ U.card
    · have h := credit two
      omega
    · omega
  by_contra! failure
  let d := 2 + pay - U.card
  obtain ⟨t,tT,tK⟩ := meet
  have posK : 0 < K.card := Finset.card_pos.mpr ⟨t,tK⟩
  have sizeK : K.card ≤ 11 := by simpa using Finset.card_le_univ K
  have comp : Kᶜ.card = 11 - K.card := by rw [Finset.card_compl,Fintype.card_fin]
  have want : 5+d ≤ Kᶜ.card := by dsimp only [d]; omega
  have last : d ≤ 5 := by omega
  obtain ⟨I,subI,icard⟩ := Finset.exists_subset_card_eq want
  have outside : ¬ T ⊆ I := fun sub => (Finset.mem_compl.mp (subI (sub tT))) tK
  let B := G.edgeFinset ∩ I.sym2
  have deleted : B ⊆ U := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b =>
      intro he
      obtain ⟨edge,ab⟩ := Finset.mem_inter.mp he
      obtain ⟨ia,ib⟩ := Finset.mk_mem_sym2_iff.mp ab
      by_contra kept
      have residual : H.Adj a b := SimpleGraph.deleteEdges_adj.mpr
        ⟨G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp edge),kept⟩
      rcases cover a b residual with ha | hb
      · exact (Finset.mem_compl.mp (subI ia)) ha
      · exact (Finset.mem_compl.mp (subI ib)) hb
  have geom := g11Geometry5184 I
  change (I.card = 5 → ¬ B ⊆ safe) ∧
    ([0,0,0,0,0,1,2,3,5,8,12,16] : List ℕ).getD I.card 0 ≤ B.card at geom
  by_cases zero : d = 0
  · have tight : U.card = 2+pay := by dsimp only [d] at zero; omega
    have bound := credit (by omega)
    have good : U ⊆ safe := by
      by_contra bad
      rw [if_neg bad] at bound
      omega
    exact geom.1 (by omega) (deleted.trans good)
  · have lookup : ∀ h : Fin 6,
        ([0,0,0,0,0,1,2,3,5,8,12,16] : List ℕ).getD (5+h.val) 0 =
        ([1,2,3,5,8,12] : List ℕ).getD h.val 0 := by decide
    have ear := geom.2
    rw [icard,lookup ⟨d,by omega⟩] at ear
    have reachable := ear.trans (Finset.card_le_card deleted)
    let cuts := (Finset.univ.filter (fun A : Finset (Fin 11) => A.card = 5+d ∧ ¬ T ⊆ A)).image
      (fun A => G.edgeFinset ∩ A.sym2)
    have hit : B ∈ cuts := Finset.mem_image.mpr
      ⟨I,Finset.mem_filter.mpr ⟨Finset.mem_univ _,icard,outside⟩,rfl⟩
    let bads := cuts.filter (fun Z => Z ⊆ U)
    have hasBad : bads.Nonempty := ⟨B,Finset.mem_filter.mpr ⟨hit,deleted⟩⟩
    obtain ⟨V,mem,best⟩ := Finset.exists_min_image bads Finset.card hasBad
    obtain ⟨atCuts,missing⟩ := Finset.mem_filter.mp mem
    have minimal (W : Finset (Sym2 (Fin 11))) (hw : W ∈ cuts) (lt : W ⊂ V) : False := by
      have sw := (Finset.ssubset_iff_subset_ne.mp lt).1
      have le := best W (Finset.mem_filter.mpr ⟨hw,sw.trans missing⟩)
      exact (Nat.not_lt_of_ge le) (Finset.card_lt_card lt)
    have other := larger C least top size nested
    change 0 < d → ([1,2,3,5,8,12] : List ℕ).getD d 0 ≤ U.card →
      ∀ W ∈ cuts, (∀ W' ∈ cuts, W' ⊂ W → False) → ¬ W ⊆ U at other
    exact other (Nat.pos_of_ne_zero zero) reachable V atCuts minimal missing
