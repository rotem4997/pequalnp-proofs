import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- A flag is an incident point and line. A port is relevant when its singleton
-- point support contains the point and lies on the line. It serves at most q+1
-- flags. Double counting therefore charges at most eight flags per circuit gate
-- for flags with more than q/4 relevant AND gates. At any other flag, one
-- two-line witness per dormant sibling fits in half the line budget. The
-- remaining half is free for an arbitrary prescribed negative test.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1782_741
    (star : ∀ (N q : ℕ) (S : Fin N → Finset (Fin N)),
      0 < q → N=q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l) →
      ∀ A : Finset (Fin N), ∀ F : Finset (Fin N × Fin N),
        (∀ e∈F, e.1∈A ∧ A⊆S e.2) → F.card≤q+1)
    (residual : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199≤q → N=q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l) →
      Monotone2 C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) →
      let V := fun (p : Fin N) (W : Finset (Fin N)) (w : ℕ) =>
        (C.wires (incidenceInput {p} W)).getD w false
      ∀ E : Finset (Fin N × Fin N), (∀ e∈E, e.1∈S e.2 ∧
        ∀ U : Finset (Fin N), 2*U.card≤q → (∀ l∈U, e.1∉S l) →
        ∃ T : Finset (Fin N), U⊆T ∧ T.card≤q ∧ (∀ l∈T, e.1∉S l) ∧
          ∀ g∈C.gates, g.op=GateOp.and →
          ∀ a∈g.inputs, V e.1 ∅ a=true → (∀ r, V r ∅ a=true → r∈S e.2) →
          ∀ b∈g.inputs, (∃ W : Finset (Fin N), W.card≤2 ∧ (∀ l∈W, e.1∉S l) ∧ V e.1 W b=true) →
          V e.1 T b=true) → E.card≤92*C.size)
    :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → ∀ (x13 : Fin (x2 + x2) → Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true → x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } → (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by

  classical
  intro q n R _ C qLarge geom degree joins mono accept reject _ _ _ _ _
  let S (l : Fin n) := Finset.univ.filter (fun p => R p l)
  have incident (p l : Fin n) : p∈S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card=q+1 := by simpa [S,Fintype.card_subtype] using degree l
  have through (p r : Fin n) (ne : p≠r) : ∃! l, p∈S l ∧ r∈S l := by
    simpa only [incident] using joins p r ne
  let vector (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have vp (X Y : Finset (Fin n)) (p : Fin n) : vector X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.addCases_left ..
  have vl (X Y : Finset (Fin n)) (l : Fin n) : vector X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.addCases_right ..
  have diff (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    have lt := p.isLt
    omega
  have pair (p l : Fin n) :
      vector {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
    funext i
    refine Fin.addCases (motive := fun i => vector {p} {l} i =
      decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) ?_ ?_ i
    · intro a
      rw [vp]
      simp only [Finset.mem_singleton, Fin.castAdd_inj, diff a l, or_false]
    · intro b
      rw [vl]
      simp only [Finset.mem_singleton, Fin.natAdd_inj, Ne.symm (diff p b), false_or]
  have correct : RightOnIncidentPairs S C := by
    intro l p hp
    rw [← listForm, pair]
    exact accept p l ((incident p l).mp hp)
  have sound (X Y : Finset (Fin n)) (budget : Y.card ≤ q) (empty : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    have count : Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight (fun l => ?_)
      simp only [vl, decide_eq_true_eq]
    have outside : ¬ ∃ (p l : Fin n), R p l ∧ vector X Y (Fin.castAdd n p) = true ∧
        vector X Y (Fin.natAdd n l) = true := by
      rintro ⟨p,l,h,px,ly⟩
      have pX : p ∈ X := of_decide_eq_true ((vp X Y p).symm.trans px)
      have lY : l ∈ Y := of_decide_eq_true ((vl X Y l).symm.trans ly)
      exact Finset.disjoint_left.mp (empty l lY) ((incident p l).mpr h) pX
    rw [← listForm]
    exact reject (vector X Y) (count.trans_le budget) outside
  let V (p : Fin n) (W : Finset (Fin n)) (w : ℕ) := (C.wires (incidenceInput {p} W)).getD w false
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let rel (a b : List Bool) := a.length=b.length ∧ ∀ i, a.getD i false=true → b.getD i false=true
  have push (w : List Bool) (v : Bool) (i : ℕ) :
      (w++[v]).getD i false = if i=w.length then v else w.getD i false := by
    by_cases hl : i<w.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hl,Nat.ne_of_lt hl]
    · rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
      by_cases he : i=w.length
      · simp [he]
      · simp [he,List.getElem?_eq_none (by omega : w.length ≤ i),List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp;omega : [v].length ≤ i-w.length)]
  have andLaw (z : List Bool) : GateOp.and.eval z = z.all id := rfl
  have orLaw (z : List Bool) : GateOp.or.eval z = z.any id := rfl
  have grows (gs : List Gate) (good : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (a b : List Bool)
      (le : rel a b) : rel (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => good k (List.mem_cons_of_mem g hk))
      refine ⟨by simp [step,le.1],?_⟩
      intro i
      simp only [step,push,le.1]
      split
      · have hh := le.2
        rcases good g List.mem_cons_self with op | op
        · simp [op,andLaw]
          intro h k hk
          exact hh k (h k hk)
        · simp [op,orLaw]
          intro k hk on
          exact ⟨k,hk,hh k on⟩
      · exact le.2 i

  have wireMono (p : Fin n) (W T : Finset (Fin n)) (sub : W⊆T) (b : ℕ) :
      V p W b=true → V p T b=true := by
    have le : ∀ i, vector {p} W i=true → vector {p} T i=true := by
      intro i
      refine Fin.addCases (motive := fun i => vector {p} W i=true → vector {p} T i=true) ?_ ?_ i
      · intro u
        simp only [vp,imp_self]
      · intro l
        simp only [vl,decide_eq_true_eq]
        exact fun h => sub h
    unfold V
    rw [← listForm,← listForm]
    apply (grows C.gates (fun g hg => (mono g hg).1)
      (List.ofFn (vector {p} W)) (List.ofFn (vector {p} T)) _).2 b
    refine ⟨by simp,?_⟩
    intro i
    by_cases hi : i<n+n
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some] using le ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
  let A (a : ℕ) := Finset.univ.filter (fun p : Fin n => V p ∅ a=true)
  let flags := Finset.univ.filter (fun e : Fin n × Fin n => e.1∈S e.2)
  let port (a : ℕ) := flags.filter (fun e => e.1∈A a ∧ A a ⊆ S e.2)
  have cap (a : ℕ) : (port a).card ≤ q+1 :=
    star n q S (by omega) geom lineSize through (A a) (port a) (fun _ h => (Finset.mem_filter.mp h).2)
  let G := C.gates.toFinset.filter (fun g => g.op=GateOp.and)
  have actual {g : Gate} (hg : g ∈ G) : g ∈ C.gates :=
    List.mem_toFinset.mp (Finset.mem_filter.mp hg).1
  have fan {g : Gate} (hg : g ∈ G) : g.inputs.toFinset.card ≤ 2 :=
    (List.toFinset_card_le _).trans (mono _ (actual hg)).2
  let F (g : Gate) := g.inputs.toFinset.biUnion port
  have gateCap (g : Gate) (hg : g∈G) : (F g).card ≤ 2*(q+1) := by
    exact (Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => cap a)).trans
      (Nat.mul_le_mul_right _ (fan hg))
  let D (e : Fin n × Fin n) := G.filter (fun g => e∈F g)
  let heavy := flags.filter (fun e => q < 4*(D e).card)
  let light := flags.filter (fun e => ¬ q < 4*(D e).card)
  have partition : heavy.card+light.card=flags.card := Finset.card_filter_add_card_filter_not ..
  have heavyCost : heavy.card ≤ 8*C.size := by
    let r := fun (e : Fin n × Fin n) (g : Gate) => e∈F g
    have down (g) (hg : g∈G) : (heavy.bipartiteBelow r g).card ≤ 2*(q+1) :=
      (Finset.card_le_card (show heavy.bipartiteBelow r g ⊆ F g from fun _ h => (Finset.mem_filter.mp h).2)).trans (gateCap g hg)
    have sumCap : (∑ e∈heavy, (D e).card) ≤ G.card*(2*(q+1)) := by
      calc
        _ = ∑ e∈heavy, (G.bipartiteAbove r e).card := rfl
        _ = ∑ g∈G, (heavy.bipartiteBelow r g).card := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
        _ ≤ _ := by simpa using G.sum_le_card_nsmul (fun g => (heavy.bipartiteBelow r g).card) _ down
    have counts : heavy.card*(q+1) ≤ 4*(∑ e∈heavy, (D e).card) := by
      rw [Finset.mul_sum]
      simpa using (Finset.sum_le_sum (s:=heavy) (f:=fun _ => q+1) (g:=fun e => 4*(D e).card)
        (fun e h => (Finset.mem_filter.mp h).2))
    have gateCount : G.card≤C.size :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (List.toFinset_card_le _)
    refine Nat.le_of_mul_le_mul_right ?_ (show 0<q+1 by omega)
    calc
      heavy.card*(q+1) ≤ 4*(G.card*(2*(q+1))) := counts.trans (Nat.mul_le_mul_left _ sumCap)
      _ ≤ 4*(C.size*(2*(q+1))) := by gcongr
      _ = 8*C.size*(q+1) := by ring
  have lightCost : light.card ≤ 92*C.size := by
    apply residual q n S C qLarge geom lineSize through mono correct sound light
    intro e he
    obtain ⟨hflag, budget⟩ := Finset.mem_filter.mp he
    refine ⟨(Finset.mem_filter.mp hflag).2, ?_⟩
    intro U hU avoidU
    let ok (b : ℕ) (W : Finset (Fin n)) :=
      W.card≤2 ∧ (∀ l∈W, e.1∉S l) ∧ V e.1 W b=true
    let witness (b : ℕ) : Finset (Fin n) := if h : ∃ W, ok b W then h.choose else ∅
    have spec (b : ℕ) (h : ∃ W, ok b W) : ok b (witness b) := by
      simpa only [witness,dite_eq_left h] using h.choose_spec
    have small (b : ℕ) : (witness b).card ≤ 2 := by
      by_cases h : ∃ W, ok b W
      · exact (spec b h).1
      · simp [witness,h]
    have avoid (b : ℕ) (l) (hl : l∈witness b) : e.1∉S l := by
      by_cases h : ∃ W, ok b W
      · exact (spec b h).2.1 l hl
      · simp [witness,h] at hl
    let dormant (g : Gate) := g.inputs.toFinset.filter (fun b => V e.1 ∅ b ≠ true)
    let pool (g : Gate) := (dormant g).biUnion witness
    let T := U ∪ (D e).biUnion pool
    have poolCap (g : Gate) (hg : g∈D e) : (pool g).card≤2 := by
      obtain ⟨member, activePort⟩ := Finset.mem_filter.mp hg
      obtain ⟨a,ha,pa⟩ := Finset.mem_biUnion.mp activePort
      have active : V e.1 ∅ a=true := (Finset.mem_filter.mp (Finset.mem_filter.mp pa).2.1).2
      have sub : dormant g ⊆ g.inputs.toFinset.erase a := by
        intro b hb
        obtain ⟨mem,off⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_erase.mpr ⟨fun eq => off (eq ▸ active),mem⟩
      have ports := Finset.card_le_card sub
      rw [Finset.card_erase_of_mem ha] at ports
      have totalPorts := fan member
      have bound := Finset.card_biUnion_le_card_mul (dormant g) witness 2 (fun b _ => small b)
      dsimp only [pool]
      omega
    refine ⟨T, Finset.subset_union_left, ?_, ?_, ?_⟩
    · have bound := Finset.card_biUnion_le_card_mul (D e) pool 2 poolCap
      have both := Finset.card_union_le U ((D e).biUnion pool)
      dsimp only [T]
      omega
    · intro l hl
      rcases Finset.mem_union.mp hl with hu | h
      · exact avoidU l hu
      · obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp h
        obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hg
        exact avoid b l hb
    · intro g hg op a ha active anchor b hb possible
      have ga : g∈G := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hg,op⟩
      have pa : e∈port a := Finset.mem_filter.mpr ⟨hflag,Finset.mem_filter.mpr ⟨Finset.mem_univ _,active⟩,
        fun r hr => anchor r (Finset.mem_filter.mp hr).2⟩
      have gd : g∈D e := Finset.mem_filter.mpr ⟨ga,Finset.mem_biUnion.mpr ⟨a,List.mem_toFinset.mpr ha,pa⟩⟩
      by_cases free : V e.1 ∅ b=true
      · exact wireMono _ _ _ (Finset.empty_subset _) _ free
      · apply wireMono _ _ _ _ _ (spec b possible).2.2
        intro l hl
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,gd,
          Finset.mem_biUnion.mpr ⟨b,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb,free⟩,hl⟩⟩)
  have total : flags.card=n*(q+1) := by
    let fiber (l : Fin n) := (S l).image (fun p => (p,l))
    have pieces : flags = Finset.univ.biUnion fiber := by
      ext e
      simp [flags,fiber,Prod.ext_iff]
    rw [pieces,Finset.card_biUnion]
    · have sizes (l : Fin n) : (fiber l).card=q+1 := by
        have inj : Function.Injective (fun p : Fin n => (p,l)) := fun _ _ h => congrArg Prod.fst h
        exact (Finset.card_image_of_injective _ inj).trans (lineSize l)
      simp [sizes]
    · intro l _ m _ h
      refine Finset.disjoint_left.mpr (fun e hl hm => h ?_)
      obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hl
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
      exact congrArg Prod.snd (hp.trans hr.symm)
  calc
    n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (by omega)
    _ = flags.card := total.symm
    _ = heavy.card + light.card := partition.symm
    _ ≤ 100*C.size := by omega
