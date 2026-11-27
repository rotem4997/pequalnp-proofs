import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The checked graph argument for L-meta-614, with only pair tests, suffices through order 299.
-- Count the lines through a point by partitioning the other points. The regular graph
-- then needs at least N vertices to cover all of its incidences.
theorem PEqualNP.Outside.R_meta_2866_42
    (pairLower : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ v w : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = v ∨ i = w)) = true ↔ G.Adj v w) → n + t ≤ C.size + 1)
    (largeOrder : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          circuitFun (N+N) C x = false) → N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);                 have x14 : ℕ → Fin x2 → Fin x2 → Bool := fun (x14 : ℕ) (x15 x16 : Fin x2) => (x5.wires (List.ofFn (x13 x15) ++ List.ofFn (x13 x16))).getD x14 Bool.false;                 have x15 : ℕ → ℕ → Fin x2 → Fin x2 → Bool := fun (x15 x16 : ℕ) (x17 x18 : Fin x2) => x14 x15 x17 x18 && x14 x16 x17 x18;                 ∀ (x16 : Finset ℕ), (∀ (x17 : ℕ) (x18 : PEqualNP.CircuitLowerBounds.Gate) (x19 x20 : ℕ), x5.gates[x17]? = Option.some x18 → x18.op = PEqualNP.CircuitLowerBounds.GateOp.and → x18.inputs = [x19, x20] → x17 ∉ x16 → (∃ x25 ∈ [x19, x20], ∀ (x26 x27 : Fin x2), x15 x19 x20 x26 x27 = x14 x25 x26 x27) ∨ ((∀ (x25 x26 : Fin x2), x15 x19 x20 x25 x26 = Bool.true → x3 x25 x26) → ∀ (x26 x27 x28 x29 : Fin x2), x15 x19 x20 x26 x28 = Bool.true → x15 x19 x20 x27 x29 = Bool.true → x26 = x27 ∨ x28 = x29)) → (100 : ℕ) * x16.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
  let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
  have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
    intro equal
    have val := congrArg Fin.val equal
    change p.val = N + l.val at val
    have inRange := p.isLt
    omega
  have leftInjective {N : ℕ} : Function.Injective (@L N) := by
    intro a b eq
    have valuations : (L a).val = (L b).val := congrArg Fin.val eq
    exact Fin.ext valuations
  have rightInjective {N : ℕ} : Function.Injective (@R N) := by
    intro a b eq
    have val := congrArg Fin.val eq
    change N + a.val = N + b.val at val
    exact Fin.ext (by omega)
  let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
    SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
  have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
      (graph I).Adj x y ↔
        (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
    unfold graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro ok
      refine ⟨?_,ok⟩
      rintro rfl
      rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
      · exact sides p l (atP.symm.trans atL)
      · exact sides p l (atP.symm.trans atL)
  have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
      · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
      · exact (sides p l invalid).elim
    · rintro ⟨l,eq,inc⟩
      exact Or.inl ⟨p,l,rfl,eq,inc⟩
  have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
      · exact (sides p l invalid.symm).elim
      · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
    · rintro ⟨p,eq,inc⟩
      exact Or.inr ⟨p,l,eq,rfl,inc⟩
  have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
      (graph I).Adj (L p) (R l) ↔ I p l := by
    rw [leftNeighbors]
    constructor
    · rintro ⟨k,eq,inc⟩
      exact (rightInjective eq).symm ▸ inc
    · exact fun inc => ⟨l,rfl,inc⟩
  have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
      (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
      (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
    have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
        (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
        (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
        (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
      obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
      obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
      have rk := (leftRight I r k).mp pair
      have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
      have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
      exact differentL (congrArg R same)
    rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
    · exact crosses p l v b vertices neighbors pl ub va vb
    · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
  have enoughNeighbors (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (big : 200 ≤ q) (order : N = q^2+q+1)
      (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ (graph I).Adj v a ∧ (graph I).Adj v b := by
    classical
    have roomy : q+1 < N := by rw [order]; nlinarith
    have pointsOn (l : Fin N) : (Finset.univ.filter fun p : Fin N => I p l).card = q+1 :=
      (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
    have outside (l : Fin N) : ∃ p, ¬ I p l := by
      by_contra! every
      have full : (Finset.univ.filter fun p : Fin N => I p l) = Finset.univ := by ext p; simp [every]
      have count := pointsOn l
      rw [full] at count
      simp at count
      omega
    have twoPoints : ∃ a b : Fin N, a ≠ b := by
      obtain ⟨a,b,_,_,distinct⟩ := Finset.one_lt_card_iff.mp
        (show 1 < (Finset.univ : Finset (Fin N)).card from by simp; omega)
      exact ⟨a,b,distinct⟩
    refine Fin.addCases (fun p => ?_) (fun l => ?_) v
    · obtain ⟨a,b,distinct⟩ := twoPoints
      have other : ∃ r : Fin N, p ≠ r := by by_cases eq : p=a; exact ⟨b,eq ▸ distinct⟩; exact ⟨a,eq⟩
      obtain ⟨r,diff⟩ := other
      obtain ⟨l,onL,_⟩ := unique p r diff
      obtain ⟨z,off⟩ := outside l
      have newPoint : p ≠ z := fun eq => off (eq ▸ onL.1)
      obtain ⟨k,onK,_⟩ := unique p z newPoint
      have otherLine : l ≠ k := fun eq => off (eq ▸ onK.2)
      exact ⟨R l,R k,fun eq => otherLine (rightInjective eq),(leftRight I p l).mpr onL.1,
        (leftRight I p k).mpr onK.1⟩
    · obtain ⟨a,b,memA,memB,distinct⟩ := Finset.one_lt_card_iff.mp
        (show 1 < (Finset.univ.filter fun p : Fin N => I p l).card from by rw [pointsOn]; omega)
      exact ⟨L a,L b,fun eq => distinct (leftInjective eq),
        (graph I).adj_symm ((leftRight I a l).mpr (Finset.mem_filter.mp memA).2),
        (graph I).adj_symm ((leftRight I b l).mpr (Finset.mem_filter.mp memB).2)⟩
  have pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (positive : 0 < q) (order : N = q^2+q+1)
      (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
    classical
    let through := Finset.univ.filter (fun l : Fin N => I p l)
    let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
    have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
      let full := Finset.univ.filter (fun r : Fin N => I r l)
      have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
      have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
      have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
      rw [same,Finset.card_erase_of_mem inFull,cardFull]
      omega
    have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
      intro l other k more different
      refine Finset.disjoint_left.mpr ?_
      intro r here there
      have throughL : I p l := (Finset.mem_filter.mp other).2
      have throughK : I p k := (Finset.mem_filter.mp more).2
      obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
      have rk := (Finset.mem_filter.mp there).2.1
      exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
    have together : through.biUnion rest = Finset.univ.erase p := by
      ext r
      constructor
      · intro seen
        obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
      · intro seen
        have diff := (Finset.mem_erase.mp seen).1
        obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
        exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
    have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
      rw [Nat.add_sub_cancel]
      ring
    have scale : through.card*q = (q+1)*q := by
      calc
        through.card*q = ∑ l ∈ through, q := by simp
        _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
        _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
        _ = (q+1)*q := by rw [together,rightSize]
    exact Nat.eq_of_mul_eq_mul_right positive scale
  have coverBudget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (rowDegree : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q+1)
      (columnDegree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (S : Finset (Fin (N+N))) (covers : ∀ p l, I p l → L p ∈ S ∨ R l ∈ S) : N ≤ S.card := by
    classical
    let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
    let rows (p : Fin N) := (Finset.univ.filter fun l : Fin N => I p l).image fun l => (p,l)
    let columns (l : Fin N) := (Finset.univ.filter fun p : Fin N => I p l).image fun p => (p,l)
    let star (v : Fin (N+N)) : Finset (Fin N × Fin N) := Fin.addCases rows columns v
    have rowSize (p : Fin N) : (rows p).card = q+1 := by
      dsimp only [rows]
      rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),rowDegree]
    have columnSize (l : Fin N) : (columns l).card = q+1 := by
      dsimp only [columns]
      rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),
        ← Fintype.card_subtype (fun p => I p l),columnDegree]
    have starSize (v : Fin (N+N)) : (star v).card = q+1 := by
      refine Fin.addCases (fun p => ?_) (fun l => ?_) v
      · simpa [star] using rowSize p
      · simpa only [star,Fin.addCases_right] using columnSize l
    have distinct : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint columns := by
      intro l _ k _ different
      refine Finset.disjoint_left.mpr ?_
      intro e inL inK
      obtain ⟨p,_,left⟩ := Finset.mem_image.mp inL
      obtain ⟨r,_,right⟩ := Finset.mem_image.mp inK
      exact different (congrArg Prod.snd (left.trans right.symm))
    have edgeSize : edges.card = N*(q+1) := by
      have same : edges = Finset.univ.biUnion columns := by
        ext e
        rcases e with ⟨p,l⟩
        simp [edges,columns,Prod.mk.injEq]
      rw [same,Finset.card_biUnion distinct]
      simp [columnSize]
    have capture : edges ⊆ S.biUnion star := by
      rintro ⟨p,l⟩ good
      have relation := (Finset.mem_filter.mp good).2
      rcases covers p l relation with atP | atL
      · apply Finset.mem_biUnion.mpr
        refine ⟨L p,atP,?_⟩
        have inRow : (p,l) ∈ rows p := Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
        simpa [star,L] using inRow
      · apply Finset.mem_biUnion.mpr
        refine ⟨R l,atL,?_⟩
        have inCol : (p,l) ∈ columns l := Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
        simpa only [star,R,Fin.addCases_right] using inCol
    have budget : edges.card ≤ S.card*(q+1) :=
      (Finset.card_le_card capture).trans (Finset.card_biUnion_le.trans (by simp [starSize]))
    rw [edgeSize] at budget
    exact Nat.le_of_mul_le_mul_right budget (by omega)
  have pairTests (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (big : 200 ≤ q) (C : Circuit)
      (positive : ∀ p l : Fin N, I p l →
        circuitFun (N+N) C (fun i => decide (i = L p ∨ i = R l)) = true)
      (negative : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (R l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (N+N) C x = false) :
      ∀ u v : Fin (N+N), C.eval (List.ofFn fun i : Fin (N+N) => decide (i = u ∨ i = v)) = true ↔
        (graph I).Adj u v := by
    intro u v
    let x : Fin (N+N) → Bool := fun i => decide (i=u ∨ i=v)
    change circuitFun (N+N) C x = true ↔ (graph I).Adj u v
    constructor
    · intro recognized
      by_contra missing
      let toPair (a : {l : Fin N // x (R l) = true}) : {v' : Fin (N+N) // v' ∈ ({u,v} : Finset _)} := by
        refine ⟨R a.val,?_⟩
        have sits : R a.val = u ∨ R a.val = v := of_decide_eq_true a.property
        simpa only [Finset.mem_insert,Finset.mem_singleton] using sits
      have injective : Function.Injective toPair := by
        intro a b equal
        apply Subtype.ext
        have same := congrArg (fun z : {j : Fin (N+N) // j ∈ ({u,v} : Finset _)} => z.val) equal
        change R a.val = R b.val at same
        exact rightInjective same
      have small : Fintype.card {l : Fin N // x (R l) = true} ≤ q := by
        apply (Fintype.card_le_of_injective toPair injective).trans
        rw [Fintype.card_of_subtype ({u,v} : Finset (Fin (N+N))) (fun _ => Iff.rfl)]
        have bound := Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
        simp only [Finset.card_singleton] at bound
        omega
      have cannot : ¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
        rintro ⟨p,l,inc,onP,onL⟩
        have hereP : L p = u ∨ L p = v := of_decide_eq_true onP
        have hereL : R l = u ∨ R l = v := of_decide_eq_true onL
        rcases hereP with left | right <;> rcases hereL with first | second
        · exact sides p l (left.trans first.symm)
        · apply missing
          exact (adjEither I u v).mpr (Or.inl ⟨p,l,left.symm,second.symm,inc⟩)
        · apply missing
          exact (adjEither I u v).mpr (Or.inr ⟨p,l,right.symm,first.symm,inc⟩)
        · exact sides p l (right.trans second.symm)
      rw [negative x small cannot] at recognized
      contradiction
    · intro inc
      rcases (adjEither I u v).mp inc with ⟨p,l,rfl,rfl,hit⟩ | ⟨p,l,rfl,rfl,hit⟩
      · exact positive p l hit
      · have eq : x = (fun i => decide (i=L p ∨ i=R l)) := by funext i; simp [x,or_comm]
        rw [eq]
        exact positive p l hit
  intro q N I _ C big order degrees unique mono positive negative
  dsimp only
  intro _ _ _
  by_cases high : 300 ≤ q
  · exact largeOrder q N I C high order degrees unique mono positive negative
  classical
  let G := graph I
  have neighbors (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b :=
    enoughNeighbors q N I big order degrees unique v
  have atLeastTwo (v : Fin (N+N)) : 2 ≤ (G.neighborSet v).ncard := by
    obtain ⟨a,b,diff,va,vb⟩ := neighbors v
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite]
    exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr va,finite.mem_toFinset.mpr vb,diff⟩
  have noTwins (v w : Fin (N+N)) (different : v ≠ w) : ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v
    exact noFour I unique v w a b different distinct va vb ((same a).mp va) ((same b).mp vb)
  have other (v w : Fin (N+N)) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,different,va,vb⟩ := neighbors v
    by_cases first : a = w
    · exact ⟨b,vb,fun second => different (first.trans second.symm)⟩
    · exact ⟨a,va,first⟩
  have adjacent (v w : Fin (N+N)) (edge : G.Adj v w) :
      ∃ a b : Fin (N+N), G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬G.Adj a b) := by
    obtain ⟨a,va,notW⟩ := other v w
    obtain ⟨b,wb,notV⟩ := other w v
    refine ⟨a,b,va,notW,wb,notV,Or.inr ?_⟩
    intro ab
    exact noFour I unique w a v b (Ne.symm notW) (Ne.symm notV) (G.adj_symm edge) wb (G.adj_symm va) ab
  let cover (S : Finset (Fin (N+N))) : Prop :=
    ∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S
  let coverSize (k : ℕ) : Prop := ∃ S : Finset (Fin (N+N)), cover S ∧ S.card = k
  have some : ∃ k, coverSize k :=
    ⟨_,Finset.univ,fun _ _ _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  let t := Nat.find some
  have minimum : ∀ S : Finset (Fin (N+N)), cover S → t ≤ S.card := fun S ok =>
    Nat.find_min' some ⟨S,ok,rfl⟩
  obtain ⟨S,coverS,count⟩ := Nat.find_spec some
  have rows := pointDegree q N I (by omega) order degrees unique
  have tBig : N ≤ t := by
    change N ≤ Nat.find some
    rw [← count]
    apply coverBudget q N I rows degrees S
    intro p l inc
    exact coverS (L p) (R l) ((leftRight I p l).mpr inc) (atLeastTwo _) (atLeastTwo _)
  have floor := pairLower (N+N) t G C
    (fun v => by obtain ⟨a,_,_,adj,_⟩ := neighbors v; exact ⟨a,adj⟩)
    (fun v w distinct _ _ _ => noTwins v w distinct)
    (fun v w edge _ _ => adjacent v w edge)
    ⟨S,coverS,count⟩ minimum mono (pairTests q N I big C positive negative)
  have planeSize : 100 ≤ N := by rw [order]; omega
  have factor : N*q ≤ N*299 := Nat.mul_le_mul_left _ (by omega)
  omega
