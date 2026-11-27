import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Seven point stars cover the union of two lines through the origin.
-- The remaining six points sit on two rails of three. The other nine lines
-- form a three by three grid. The boundary calculation supplies thirteen intermediate ORs at no extra cost.
-- The general sorted-wire encoding hypothesis is shared with R_meta_4893_34.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_4893_629
  (grid :
    let rs : List ℕ := [29,225,1793,294,586,1170]
    let qs : List ℕ := [3,40,1064,272,336,516,644,48,560,264,392,68,1092]
    let bank := fun (p w : ℕ) => (List.range 6).map p.testBit ++ (List.range 11).map w.testBit ++
      qs.map (fun q => decide (w &&& q ≠ 0))
    let single := fun i : ℕ => (2 : ℕ)^i
    ∃ B : Circuit, IsAO2 30 B ∧ B.size = 28 ∧ B.output = 57 ∧
      (∀ i : Fin 6, ∀ j : Fin 11, (rs.getD i.val 0).testBit j.val = true →
        B.eval (bank (single i.val) (single j.val)) = true) ∧
      (∀ p w : ℕ, p &&& 7 ≠ 7 → p &&& 56 ≠ 56 →
        (∀ q ∈ rs ++ qs, ((List.range 11).filter (w &&& q).testBit).length ≤ 2) →
        (∀ i : Fin 6, p.testBit i.val = true → w &&& rs.getD i.val 0 = 0) →
        B.eval (bank p w) = false))
  (encode :
    let run := fun (d : Fin 63 → Bool) (a b : Fin 63 → Fin 89) (x : Fin 26 → Bool) =>
      ((List.ofFn (fun j : Fin 63 => (d j, a j, b j))).foldl
        (fun (w : List Bool) g => w ++ [bif g.1 then w.getD g.2.1.val false && w.getD g.2.2.val false
          else w.getD g.2.1.val false || w.getD g.2.2.val false]) (List.ofFn x)).getD 88 false
    ∀ C : Circuit, IsAO2 26 C → C.size = 63 → C.output = 88 →
      ∃ (d : Fin 63 → Bool) (a b : Fin 63 → Fin 89),
        (∀ j, (a j).val < 26 + j.val ∧ (b j).val < 26 + j.val ∧ a j ≤ b j) ∧
        ∀ x, run d a b x = circuitFun 26 C x) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (63 : ℕ) → Bool) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x6 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x7 : Fin (63 : ℕ)), ↑(x5 x7) < (26 : ℕ) + ↑x7 ∧ ↑(x6 x7) < (26 : ℕ) + ↑x7 ∧ x5 x7 ≤ x6 x7) ∧     have x7 : (Fin (26 : ℕ) → Bool) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x4 x8, x5 x8, x6 x8))).getD (88 : ℕ) Bool.false;     (∀ (x8 x9 : Fin (13 : ℕ)), (∃ x10 ∈ x1, x8 = x9 + x10) → (x7 fun (x11 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧ ∀ x8 ∈ x2, ∀ x10 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x12 : Fin (13 : ℕ)) (x13 : Bool), x7 (x3 x8 x10 x12 x13) = Bool.false := by
  intro D R row
  let rs : List ℕ := [29,225,1793,294,586,1170]
  let qs : List ℕ := [3,40,1064,272,336,516,644,48,560,264,392,68,1092]
  let bank (p w : ℕ) := (List.range 6).map p.testBit ++ (List.range 11).map w.testBit ++
    qs.map (fun q => decide (w &&& q ≠ 0))
  obtain ⟨B,hB,sB,oB,positive,negative⟩ := grid
  change ∀ i : Fin 6, ∀ j : Fin 11, (rs.getD i.val 0).testBit j.val = true →
    B.eval (bank (2^i.val) (2^j.val)) = true at positive
  change ∀ p w : ℕ, p &&& 7 ≠ 7 → p &&& 56 ≠ 56 →
    (∀ q ∈ rs ++ qs, ((List.range 11).filter (w &&& q).testBit).length ≤ 2) →
    (∀ i : Fin 6, p.testBit i.val = true → w &&& rs.getD i.val 0 = 0) →
    B.eval (bank p w) = false at negative
  let pre : List Gate := [⟨.or,[23,25]⟩,
      ⟨.or,[26,13]⟩,
      ⟨.or,[27,17]⟩,
      ⟨.and,[0,28]⟩,
      ⟨.or,[14,18]⟩,
      ⟨.or,[30,24]⟩,
      ⟨.or,[13,31]⟩,
      ⟨.and,[1,32]⟩,
      ⟨.or,[15,16]⟩,
      ⟨.or,[34,20]⟩,
      ⟨.or,[13,35]⟩,
      ⟨.and,[3,36]⟩,
      ⟨.or,[19,21]⟩,
      ⟨.or,[38,22]⟩,
      ⟨.or,[13,39]⟩,
      ⟨.and,[9,40]⟩,
      ⟨.or,[14,16]⟩,
      ⟨.or,[42,21]⟩,
      ⟨.or,[17,43]⟩,
      ⟨.and,[4,44]⟩,
      ⟨.or,[15,18]⟩,
      ⟨.or,[46,22]⟩,
      ⟨.or,[17,47]⟩,
      ⟨.and,[5,48]⟩,
      ⟨.or,[19,20]⟩,
      ⟨.or,[50,24]⟩,
      ⟨.or,[17,51]⟩,
      ⟨.and,[7,52]⟩,
      ⟨.or,[29,33]⟩,
      ⟨.or,[54,37]⟩,
      ⟨.or,[55,41]⟩,
      ⟨.or,[56,45]⟩,
      ⟨.or,[57,49]⟩,
      ⟨.or,[58,53]⟩]
  let ids : List ℕ := [6,10,11,2,8,12,23,25,19,18,16,14,20,22,15,21,24,26,30,31,34,35,38,39,42,43,46,47,50,51]
  let posIds : List ℕ := [6,10,11,2,8,12]
  let lineIds : List ℕ := [23,25,19,18,16,14,20,22,15,21,24]
  let mask (idx : List ℕ) (x : Fin 26 → Bool) :=
    (idx.map fun i => x (Fin.ofNat 26 i)).foldr (fun b n => b.toNat+2*n) 0
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let start (x : Fin 26 → Bool) := pre.foldl step (List.ofFn x)
  let ports (x : Fin 26 → Bool) := ids.map fun i => (start x).getD i false
  let boundary (x : Fin 26 → Bool) := (start x).getD 59 false
  let edge (p l : Fin 13) := fun k : Fin 26 => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)
  have geomPos : ∀ p l : Fin 13, (∃ d ∈ D, p = l + d) →
      boundary (edge p l) = true ∨
      let i := Fin.ofNat 6 (posIds.idxOf p.val)
      let j := Fin.ofNat 11 (lineIds.idxOf (13+l.val))
      (rs.getD i.val 0).testBit j.val = true ∧ ports (edge p l) = bank (2^i.val) (2^j.val) := by
    decide +kernel
  let good (x : Fin 26 → Bool) :=
    let p := mask posIds x
    let w := mask lineIds x
    boundary x = false ∧ ports x = bank p w ∧ p &&& 7 ≠ 7 ∧ p &&& 56 ≠ 56 ∧
      (∀ q ∈ rs ++ qs, ((List.range 11).filter (w &&& q).testBit).length ≤ 2) ∧
      (∀ i : Fin 6, p.testBit i.val = true → w &&& rs.getD i.val 0 = 0)
  have geomNeg : ∀ z ∈ R, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t dual, good (row z m t dual) := by
    intro z hz
    change z ∈ ([(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)] : List (ℕ × ℕ)) at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  let toc (i : ℕ) := if i < 30 then ids.getD i 0 else i+30
  let liftGate (g : Gate) : Gate := ⟨g.op,g.inputs.map toc⟩
  let last : Gate := ⟨.or,[59,87]⟩
  let C : Circuit := ⟨(pre ++ B.gates.map liftGate) ++ [last],88⟩
  have preLen : pre.length = 34 := rfl
  have idsLen : ids.length = 30 := rfl
  have bLen : B.gates.length = 28 := sB
  have prior : ∀ i : Fin 30, ids.getD i.val 0 < 60 := by decide +kernel
  have smallImage (i n : ℕ) (hi : i < 30+n) : toc i < 60+n := by
    by_cases h : i < 30
    · have h' := prior ⟨i,h⟩
      simpa [toc,h] using
        (show ids.getD i 0 < 60+n from lt_of_lt_of_le h' (by omega))
    · simp [toc,h]; omega
  have preShape : IsAO2 26 (⟨pre,59⟩ : Circuit) := by decide +kernel
  have cSize : C.size = 63 := by
    change ((pre ++ B.gates.map liftGate) ++ [last]).length = 63
    simp only [List.length_append,List.length_map,List.length_singleton,preLen,bLen]
  have cShape : IsAO2 26 C := by
    have dataAt (g : Gate) (hg : g ∈ C.gates) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
      change g ∈ (pre ++ B.gates.map liftGate) ++ [last] at hg
      simp only [List.mem_append,List.mem_singleton,List.mem_map] at hg
      rcases hg with ((hp | ⟨q,hq,rfl⟩) | rfl)
      · exact ⟨preShape.1 g hp,preShape.2.2 g hp⟩
      · exact ⟨hB.1 q hq,by simpa only [liftGate,List.length_map] using hB.2.2 q hq⟩
      · exact ⟨Or.inr rfl,rfl⟩
    refine ⟨fun g hg => (dataAt g hg).1,?_,fun g hg => (dataAt g hg).2⟩
    intro j hj w hw
    have range : j < 63 := cSize ▸ hj
    change w ∈ (((pre ++ B.gates.map liftGate) ++ [last]).getD j ⟨.or,[]⟩).inputs at hw
    have both : (pre ++ B.gates.map liftGate).length = 62 := by simp [preLen,bLen]
    by_cases h : j < 62
    · rw [List.getD_append _ _ _ _ (both ▸ h)] at hw
      by_cases lo : j < 34
      · rw [List.getD_append _ _ _ _ (preLen ▸ lo)] at hw
        exact preShape.2.1 j (preLen ▸ lo) w hw
      · rw [List.getD_append_right _ _ _ _ (by omega),preLen] at hw
        have ix : j-34 < B.gates.length := by omega
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ix),List.getElem_map] at hw
        change w ∈ B.gates[j-34].inputs.map toc at hw
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
        have mem : v ∈ (gateAt B (j-34)).inputs := by
          change v ∈ (B.gates.getD (j-34) ⟨.or,[]⟩).inputs
          rw [List.getD_eq_getElem _ _ ix]; exact hv
        have eqn := smallImage v (j-34) (hB.2.1 _ ix v mem)
        omega
    · have eqn : j = 62 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega),both,eqn,Nat.sub_self,List.getD_cons_zero] at hw
      change w ∈ [59,87] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      omega
  have foldLen (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega
  have kept (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step xs g) (by simp [step];omega)]
      exact List.getD_append _ _ _ _ hi
  let relate (a b : List Bool) := ∀ i, b.getD (toc i) false = a.getD i false
  have sim (gs : List Gate) (a b : List Bool) (al : 30 ≤ a.length) (bl : b.length = a.length+30)
      (ab : relate a b) : relate (gs.foldl step a) ((gs.map liftGate).foldl step b) := by
    induction gs generalizing a b with
    | nil => exact ab
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih
      · simp only [step,List.length_append,List.length_singleton]; omega
      · simp only [step,List.length_append,List.length_singleton]; omega
      · intro i
        have same : (liftGate g).op.eval ((liftGate g).inputs.map fun j => b.getD j false) =
            g.op.eval (g.inputs.map fun j => a.getD j false) := by
          change g.op.eval ((g.inputs.map toc).map _) = _
          rw [List.map_map]; congr 1; exact List.map_congr_left (fun j _ => ab j)
        change (b ++ [_]).getD (toc i) false = (a ++ [_]).getD i false
        rw [same]
        by_cases lo : i < a.length
        · have below : toc i < b.length := by
            have e := smallImage i (a.length-30) (by omega)
            omega
          rw [List.getD_append _ _ _ _ lo,List.getD_append _ _ _ _ below]
          exact ab i
        · have high : ¬ i < 30 := by omega
          have toci : toc i = i+30 := by simp [toc,high]
          rw [toci,List.getD_append_right _ _ _ _ (show b.length ≤ i+30 by omega),
            List.getD_append_right _ _ _ _ (show a.length ≤ i by omega),
            show i+30-b.length = i-a.length by omega]
  have computes (x : Fin 26 → Bool) : circuitFun 26 C x = (boundary x || B.eval (ports x)) := by
    let base := start x
    let small := ports x
    have nBase : base.length = 60 := by simp only [base,start,foldLen,List.length_ofFn,preLen]
    have nSmall : small.length = 30 := by simp only [small,ports,List.length_map,idsLen]
    have init : relate small base := by
      intro i
      by_cases hi : i < 30
      · have hIds : i < ids.length := idsLen ▸ hi
        change base.getD (toc i) false = (ids.map (fun k => base.getD k false)).getD i false
        rw [show toc i = ids.getD i 0 by simp [toc,hi],
          List.getD_eq_getElem (ids.map (fun k => base.getD k false)) false (by simpa only [List.length_map] using hIds),
          List.getElem_map,List.getD_eq_getElem ids 0 hIds]
      · rw [show toc i = i+30 by simp [toc,hi],List.getD_eq_default base false (by omega),List.getD_eq_default small false (by omega)]
    let before := (B.gates.map liftGate).foldl step base
    have nb : before.length = 88 := by simp only [before,foldLen,nBase,List.length_map,bLen]
    have pb : before.getD 59 false = boundary x := kept _ base 59 (by omega)
    have qb : before.getD 87 false = B.eval small := by
      have h := sim B.gates small base (by omega) (by omega) init B.output
      rw [oB] at h
      change before.getD 87 false = (B.gates.foldl step small).getD 57 false at h
      change before.getD 87 false = (B.gates.foldl step small).getD B.output false
      rwa [oB]
    change (((pre ++ B.gates.map liftGate) ++ [last]).foldl step (List.ofFn x)).getD 88 false = _
    rw [List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (before ++ [_]).getD 88 false = _
    rw [List.getD_append_right _ _ _ _ nb.le,nb,Nat.sub_self,List.getD_cons_zero]
    change (before.getD 59 false || (before.getD 87 false || false)) = _
    rw [pb,qb,Bool.or_false]
  obtain ⟨d,a,b,back,eval⟩ := encode C cShape cSize rfl
  refine ⟨d,a,b,back,?_,?_⟩
  · intro p l h
    refine (eval (edge p l)).trans ((computes (edge p l)).trans ?_)
    rcases geomPos p l h with hb | hg
    · simp only [hb,Bool.true_or]
    · dsimp only at hg
      rw [hg.2,positive _ _ hg.1,Bool.or_true]
  · intro z hz m hm t dual
    refine (eval (row z m t dual)).trans ((computes (row z m t dual)).trans ?_)
    obtain ⟨hb,portsEq,ha,hb',hc,hd⟩ := geomNeg z hz m hm t dual
    simp only [hb,portsEq,negative _ _ ha hb' hc hd,Bool.false_or]
