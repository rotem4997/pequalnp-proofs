import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace PEqualNP.Outside.L_meta_6696

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private lemma noTriangle {V : Type} {G : SimpleGraph V} (hg : (7 : ℕ∞) ≤ G.egirth)
    {v a b : V} (hva : G.Adj v a) (hab : G.Adj a b) (hbv : G.Adj b v) : False := by
  let p : G.Walk v v := .cons hva (.cons hab (.cons hbv .nil))
  have hc : p.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨SimpleGraph.Walk.IsPath.mk' ?_, by simp [p]⟩
    simp [p, SimpleGraph.Walk.tail_cons, hab.ne, hva.ne.symm, hbv.ne]
  have hp := SimpleGraph.le_egirth.mp hg v p hc
  change (7 : ℕ∞) ≤ (3 : ℕ∞) at hp
  exact (by decide : ¬ (7 : ℕ∞) ≤ 3) hp

private lemma noSquare {V : Type} {G : SimpleGraph V} (hg : (7 : ℕ∞) ≤ G.egirth)
    {v a u b : V} (hva : G.Adj v a) (hau : G.Adj a u)
    (hub : G.Adj u b) (hbv : G.Adj b v) (huv : u ≠ v) (hab : a ≠ b) : False := by
  let p : G.Walk v v := .cons hva (.cons hau (.cons hub (.cons hbv .nil)))
  have hc : p.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨SimpleGraph.Walk.IsPath.mk' ?_, by simp [p]⟩
    simp [p, SimpleGraph.Walk.tail_cons, hau.ne, hab, hva.ne.symm, hub.ne, huv, hbv.ne]
  have hp := SimpleGraph.le_egirth.mp hg v p hc
  change (7 : ℕ∞) ≤ (4 : ℕ∞) at hp
  exact (by decide : ¬ (7 : ℕ∞) ≤ 4) hp

private lemma freeNeighbor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hg : (7 : ℕ∞) ≤ G.egirth) {v : Fin n} (hd : G.degree v = 3)
    {T : Finset (Fin n)} (hT : T.card ≤ 2) (hv : v ∉ T) :
    ∃ w, G.Adj v w ∧ ∀ u ∈ T, w ≠ u ∧ ¬ G.Adj u w := by
  classical
  by_contra h
  have hbad (w : G.neighborFinset v) :
      ∃ u ∈ T, (w : Fin n) = u ∨ G.Adj u w := by
    by_contra hn
    apply h
    refine ⟨w, (G.mem_neighborFinset v _).mp w.property, ?_⟩
    intro u hu
    exact ⟨fun he => hn ⟨u, hu, Or.inl he⟩, fun ha => hn ⟨u, hu, Or.inr ha⟩⟩
  choose f hf hfrel using hbad
  have hcard : (G.neighborFinset v).card ≤ T.card := by
    apply Finset.card_le_card_of_injective (f := fun w => ⟨f w, hf w⟩)
    intro a b he
    have he' : f a = f b := congrArg Subtype.val he
    by_contra hne
    have hab : (a : Fin n) ≠ b := fun hab => hne (Subtype.ext hab)
    have hva := (G.mem_neighborFinset v _).mp a.property
    have hvb := (G.mem_neighborFinset v _).mp b.property
    have hua : (a : Fin n) = f a ∨ G.Adj (f a) a := hfrel a
    have hub : (b : Fin n) = f a ∨ G.Adj (f a) b := by
      rw [he']
      exact hfrel b
    rcases hua with ha | ha <;> rcases hub with hb | hb
    · exact hab (ha.trans hb.symm)
    · exact noTriangle hg hva (ha.symm ▸ hb) hvb.symm
    · exact noTriangle hg hvb (hb.symm ▸ ha) hva.symm
    · exact noSquare hg hva ha.symm hb hvb.symm (fun hu => hv (hu ▸ hf a)) hab
  rw [G.card_neighborFinset_eq_degree, hd] at hcard
  omega

private def reads (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [gateValue g ws]) w

private lemma readValue {C : Circuit} (hf : FanInTwo C) {g : Gate} (hg : g ∈ C.gates)
    (f : ℕ → Bool) : g.op.eval (g.inputs.map f) = g.op.eval ((reads g).map f) := by
  obtain ⟨hop, hlen⟩ := hf g hg
  rcases hop with h | h | h
  · change g.op = GateOp.and at h
    have he : reads g = g.inputs := by
      unfold reads
      rw [h]
      exact List.take_of_length_le hlen
    rw [he]
  · change g.op = GateOp.or at h
    have he : reads g = g.inputs := by
      unfold reads
      rw [h]
      exact List.take_of_length_le hlen
    rw [he]
  · change g.op = GateOp.not at h
    unfold reads
    rw [h]
    cases g.inputs <;> rfl

private lemma getLeft (a b : List Bool) {i : ℕ} (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getRight (a b : List Bool) {i : ℕ} (hi : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma runPrefix (gs : List Gate) (a : List Bool) {i : ℕ} (hi : i < a.length) :
    (run gs a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (a ++ [gateValue g a])).getD i false = _
    rw [ih _ (by simpa using Nat.lt_succ_of_lt hi), getLeft _ _ hi]

private lemma inputGet {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    (List.ofFn a).getD i.val false = a i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma gateAgree {n : ℕ} {C : Circuit} (hf : FanInTwo C) {g : Gate}
    (hg : g ∈ C.gates) (v : Fin n) (a b : List Bool)
    (he : ∀ j ≠ v.val, a.getD j false = b.getD j false)
    (hblock : v.val ∈ reads g → ∃ i : Fin n, i.val ∈ g.inputs ∧
      (a.getD i.val false = true ∧ b.getD i.val false = true ∧ g.op = GateOp.or ∨
       a.getD i.val false = false ∧ b.getD i.val false = false ∧ g.op = GateOp.and)) :
    gateValue g a = gateValue g b := by
  by_cases hv : v.val ∈ reads g
  · obtain ⟨i, hi, h | h⟩ := hblock hv
    · obtain ⟨ha, hb, hop⟩ := h
      simp only [gateValue, hop, GateOp.eval]
      have hor (w : List Bool) (hw : w.getD i.val false = true) :
          (g.inputs.map fun j => w.getD j false).any id = true := by
        exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨i.val, hi, hw⟩, rfl⟩
      rw [hor a ha, hor b hb]
    · obtain ⟨ha, hb, hop⟩ := h
      simp only [gateValue, hop, GateOp.eval]
      have hand (w : List Bool) (hw : w.getD i.val false = false) :
          (g.inputs.map fun j => w.getD j false).all id = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact Bool.false_ne_true
          (List.all_eq_true.mp htrue false (List.mem_map.mpr ⟨i.val, hi, hw⟩))
      rw [hand a ha, hand b hb]
  · unfold gateValue
    rw [readValue hf hg, readValue hf hg]
    congr 1
    exact List.map_congr_left fun j hj => he j (fun h => hv (h ▸ hj))

private lemma runAgree {n : ℕ} {C : Circuit} (hf : FanInTwo C)
    (v : Fin n) (gs : List Gate) (a b : List Bool) (hs : ∀ g ∈ gs, g ∈ C.gates)
    (hn : n ≤ a.length) (hlen : a.length = b.length)
    (he : ∀ j ≠ v.val, a.getD j false = b.getD j false)
    (hblock : ∀ g ∈ gs, v.val ∈ reads g → ∃ i : Fin n, i.val ∈ g.inputs ∧
      (a.getD i.val false = true ∧ b.getD i.val false = true ∧ g.op = GateOp.or ∨
       a.getD i.val false = false ∧ b.getD i.val false = false ∧ g.op = GateOp.and)) :
    ∀ j ≠ v.val, (run gs a).getD j false = (run gs b).getD j false := by
  induction gs generalizing a b with
  | nil => exact he
  | cons g gs ih =>
    have hv := gateAgree hf (hs g (by simp)) v a b he (hblock g (by simp))
    change ∀ j ≠ v.val, (run gs (a ++ [gateValue g a])).getD j false =
      (run gs (b ++ [gateValue g b])).getD j false
    apply ih _ _ (fun k hk => hs k (List.mem_cons_of_mem _ hk))
      (by simp; omega) (by simp [hlen])
    · intro j hj
      by_cases h : j < a.length
      · rw [getLeft _ _ h, getLeft _ _ (hlen ▸ h), he j hj]
      · have hge := Nat.le_of_not_lt h
        rw [getRight _ _ hge, getRight _ _ (hlen ▸ hge), hv, hlen]
    · intro k hk hr
      obtain ⟨i, hi, hb⟩ := hblock k (List.mem_cons_of_mem _ hk) hr
      have hi' := i.isLt.trans_le hn
      exact ⟨i, hi, by rwa [getLeft _ _ hi', getLeft _ _ (hlen ▸ hi')]⟩

private def bits {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool :=
  decide (v ∈ S)

private lemma graphFalse {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A S : Finset (Fin n)} (hA : ∀ u ∈ S, u ∉ A)
    (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w) : graphFun G A (bits S) = false := by
  simp only [graphFun, bits, decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨fun ⟨u, hu, hs⟩ => hA u hs hu, fun ⟨u, w, he, hu, hw⟩ => hS u hu w hw he⟩

private lemma mainProof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (hd : ∀ u, G.degree u = if u ∈ A then 0 else 3) (hg : (7 : ℕ∞) ≤ G.egirth)
    (hf : FanInTwo C) (hc : circuitFun n C = graphFun G A)
    (v : Fin n) (hv : v ∉ A) (P Q : Finset (Fin n)) (hcard : (P ∪ Q).card ≤ 2)
    (hvPQ : v ∉ P ∪ Q) (hp : G.IsIndepSet ↑P) (ha : Disjoint A P) (hpq : Disjoint P Q)
    (hblock : ∀ g ∈ C.gates, v.val ∈ reads g → ∃ u : Fin n, u.val ∈ g.inputs ∧
      (u ∈ P ∧ g.op = GateOp.or ∨ u ∈ Q ∧ g.op = GateOp.and)) : False := by
  obtain ⟨w, hvw, hw⟩ := freeNeighbor hg (by simpa [hv] using hd v) hcard hvPQ
  have hnotA : w ∉ A := by
    intro hwA
    have hpos := hvw.degree_pos_right
    simp [hd w, hwA] at hpos
  have hvQ : v ∉ Q := fun h => hvPQ (Finset.mem_union_right _ h)
  have hwQ : w ∉ Q := fun h => (hw w (Finset.mem_union_right _ h)).1 rfl
  let S := insert w P
  let a := bits S
  let b := bits (insert v S)
  have hfalse : graphFun G A a = false := by
    apply graphFalse
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hnotA
      · exact fun h => Finset.disjoint_left.mp ha h hu
    · intro u hu t ht
      rcases Finset.mem_insert.mp hu with rfl | huP
      · rcases Finset.mem_insert.mp ht with rfl | htP
        · exact G.irrefl
        · exact fun he => (hw t (Finset.mem_union_left _ htP)).2 he.symm
      · rcases Finset.mem_insert.mp ht with htw | htP
        · rw [htw]
          exact (hw u (Finset.mem_union_left _ huP)).2
        · intro he
          exact hp huP htP he.ne he
  have htrue : graphFun G A b = true := by
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨v, w, hvw, by simp [b, bits], by simp [b, S, bits]⟩
  have hout : C.output ≠ v.val := by
    intro ho
    let c := bits ({v} : Finset (Fin n))
    have hzero : graphFun G A c = false := by
      apply graphFalse
      · intro u hu
        rwa [Finset.mem_singleton.mp hu]
      · intro u hu t ht
        rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp ht]
        exact G.irrefl
    have hval := congrFun hc c
    change (run C.gates (List.ofFn c)).getD C.output false = graphFun G A c at hval
    rw [ho, runPrefix _ _ (by simp), inputGet c v, hzero] at hval
    simp [c, bits] at hval
  have hsame : circuitFun n C a = circuitFun n C b := by
    apply runAgree hf v C.gates (List.ofFn a) (List.ofFn b) (fun _ h => h)
      (by simp) (by simp) ?_ ?_ C.output hout
    · intro j hj
      by_cases hlt : j < n
      · let u : Fin n := ⟨j, hlt⟩
        have huv : u ≠ v := fun h => hj (congrArg Fin.val h)
        change (List.ofFn a).getD u.val false = (List.ofFn b).getD u.val false
        rw [inputGet, inputGet]
        simp [a, b, bits, huv]
      · simp [List.getD_eq_getElem?_getD, hlt]
    · intro g hmem hr
      obtain ⟨u, hu, h | h⟩ := hblock g hmem hr <;>
        refine ⟨u, hu, ?_⟩ <;> rw [inputGet, inputGet]
      · exact Or.inl ⟨by simp [a, S, bits, h.1], by simp [b, S, bits, h.1], h.2⟩
      · have huP : u ∉ P := fun hm => Finset.disjoint_left.mp hpq hm h.1
        have huw : u ≠ w := fun he => hwQ (he ▸ h.1)
        have huv : u ≠ v := fun he => hvQ (he ▸ h.1)
        exact Or.inr ⟨by simp [a, S, bits, huP, huw], by simp [b, S, bits, huP, huw, huv], h.2⟩
  rw [hc, hfalse, htrue] at hsame
  exact Bool.false_ne_true hsame

end PEqualNP.Outside.L_meta_6696

theorem PEqualNP.Outside.L_meta_6696 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin x1) => List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x5.gates;   (∀ (x7 : Fin x1), x2.degree x7 = if x7 ∈ x4 then (0 : ℕ) else (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → ∀ x11 ∉ x4, ∀ (x13 x14 : Finset (Fin x1)), (x13 ∪ x14).card ≤ (2 : ℕ) → x11 ∉ x13 ∪ x14 → x2.IsIndepSet ↑x13 → Disjoint x4 x13 → Disjoint x13 x14 → ¬∀ x20 ∈ x6 x11, ∃ (x22 : Fin x1), ↑x22 ∈ x20.inputs ∧ (x22 ∈ x13 ∧ x20.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x22 ∈ x14 ∧ x20.op = PEqualNP.CircuitLowerBounds.GateOp.and) := by
  intro n G inst A C
  dsimp only
  intro hd hg hf hc v hv P Q hcard hvPQ hp ha hpq hblock
  apply PEqualNP.Outside.L_meta_6696.mainProof G A C hd hg hf hc v hv P Q hcard hvPQ hp ha hpq
  intro g hmem hr
  apply hblock g
  exact List.mem_filter.mpr ⟨hmem, List.contains_iff_mem.mpr hr⟩
