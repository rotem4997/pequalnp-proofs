import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7537

open PEqualNP.AndCount AndCountCircuit
open scoped BigOperators

abbrev V := Fin 42

def rel (v w : V) : Prop :=
  v.val < 21 ∧ 21 ≤ w.val ∧ (w.val + 21 - v.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)

def plane : SimpleGraph V := SimpleGraph.fromRel rel

def adjDec (v w : V) : Decidable (plane.Adj v w) := by
  change Decidable (v ≠ w ∧ (rel v w ∨ rel w v))
  unfold rel
  infer_instance

def color (v : V) : Bool := decide (v.val < 21)

def part (b : Bool) : Finset V := Finset.univ.filter fun v => color v = b

def neighbors (v : V) : Finset V :=
  @Finset.filter V (plane.Adj v) (adjDec v) Finset.univ

lemma mem_neighbors {v w : V} : w ∈ neighbors v ↔ plane.Adj v w := by
  simp [neighbors]

lemma mem_part {b : Bool} {v : V} : v ∈ part b ↔ color v = b := by
  simp [part]

lemma part_card (b : Bool) : (part b).card = 21 := by
  cases b <;> decide

def neighborTable (v : V) : Finset V :=
  let f (d : ℕ) : V :=
    if v.val < 21 then Fin.ofNat 42 (21 + (v.val + d) % 21)
    else Fin.ofNat 42 ((v.val + 21 - d) % 21)
  {f 0, f 5, f 7, f 17, f 20}

lemma neighbors_table : ∀ v, neighbors v = neighborTable v := by decide +kernel

lemma table_degree : ∀ v, (neighborTable v).card = 5 := by decide +kernel

lemma degree (v : V) : (neighbors v).card = 5 := by
  rw [neighbors_table, table_degree]

lemma cross {v w : V} (edge : plane.Adj v w) : color v ≠ color w := by
  change v ≠ w ∧ (rel v w ∨ rel w v) at edge
  rcases edge.2 with e | e <;> simp [color, e.1, Nat.not_lt.mpr e.2.1]

lemma table_intersection : ∀ v w : V, v ≠ w →
    (neighborTable v ∩ neighborTable w).card = if color v = color w then 1 else 0 := by
  decide +kernel

lemma intersections (v w : V) (ne : v ≠ w) : (neighbors v ∩ neighbors w).card ≤ 1 := by
  rw [neighbors_table, neighbors_table, table_intersection v w ne]
  split <;> decide

lemma common_same (v w : V) (ne : v ≠ w) (col : color v = color w) :
    (neighbors v ∩ neighbors w).Nonempty := by
  apply Finset.card_pos.mp
  rw [neighbors_table, neighbors_table, table_intersection v w ne, ite_eq_left col]
  decide

lemma unique_common {v w a b : V} (vw : v ≠ w)
    (va : plane.Adj v a) (wa : plane.Adj w a)
    (vb : plane.Adj v b) (wb : plane.Adj w b) : a = b :=
  Finset.card_le_one.mp (intersections v w vw) a
    (Finset.mem_inter.mpr ⟨mem_neighbors.mpr va, mem_neighbors.mpr wa⟩) b
    (Finset.mem_inter.mpr ⟨mem_neighbors.mpr vb, mem_neighbors.mpr wb⟩)

lemma has_neighbor (v : V) : ∃ w, plane.Adj v w := by
  have h : 0 < (neighbors v).card := by rw [degree]; decide
  obtain ⟨w, hw⟩ := Finset.card_pos.mp h
  exact ⟨w, mem_neighbors.mp hw⟩

lemma avoids (v : V) (T : Finset V) (hcard : T.card ≤ 4) (hv : v ∉ T) :
    ∃ w, plane.Adj v w ∧ ∀ t ∈ T, ¬ plane.Adj t w := by
  classical
  by_contra! h
  have sub : neighbors v ⊆ T.biUnion (fun t => neighbors v ∩ neighbors t) := by
    intro w hw
    obtain ⟨t, ht, he⟩ := h w (mem_neighbors.mp hw)
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_inter.mpr ⟨hw, mem_neighbors.mpr he⟩⟩
  have bound : (neighbors v).card ≤ ∑ t ∈ T, (neighbors v ∩ neighbors t).card :=
    (Finset.card_le_card sub).trans Finset.card_biUnion_le
  have cap : (∑ t ∈ T, (neighbors v ∩ neighbors t).card) ≤ ∑ _t ∈ T, 1 :=
    Finset.sum_le_sum fun t ht => intersections v t (fun eq => hv (eq ▸ ht))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at cap
  rw [degree] at bound
  omega

def Independent (U : Finset V) : Prop :=
  ∀ v ∈ U, ∀ w ∈ U, ¬ plane.Adj v w

lemma independent_parts {A B : Finset V} {b : Bool}
    (hA : ∀ a ∈ A, color a = b) (hB : ∀ a ∈ B, color a ≠ b)
    (no : ∀ a ∈ A, ∀ w ∈ B, ¬ plane.Adj a w) : Independent (A ∪ B) := by
  intro v hv w hw e
  rcases Finset.mem_union.mp hv with hv | hv <;> rcases Finset.mem_union.mp hw with hw | hw
  · exact cross e ((hA v hv).trans (hA w hw).symm)
  · exact no v hv w hw e
  · exact no w hw v hv e.symm
  · exact cross e ((Bool.eq_not_of_ne (hB v hv)).trans (Bool.eq_not_of_ne (hB w hw)).symm)

abbrev Slot (C : AndCountCircuit 42) := Fin C.size × Bool

def other {C : AndCountCircuit 42} (s : Slot C) : Slot C := (s.1, !s.2)

lemma other_other {C : AndCountCircuit 42} (s : Slot C) : other (other s) = s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

lemma other_ne {C : AndCountCircuit 42} (s : Slot C) : other s ≠ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [other]

lemma other_inj {C : AndCountCircuit 42} {s t : Slot C} (h : other s = other t) : s = t := by
  simpa only [other_other] using congrArg other h

lemma other_of_gate {C : AndCountCircuit 42} {s t : Slot C}
    (h : s.1 = t.1) (ne : s ≠ t) : other s = t := by
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, d⟩
  change i = j at h
  subst j
  cases b <;> cases d <;> first | rfl | exact (ne rfl).elim

def raw (C : AndCountCircuit 42) (s : Slot C) : Finset V :=
  if s.2 then C.rightVars s.1 else C.leftVars s.1

def positions (C : AndCountCircuit 42) (v : V) : Finset (Slot C) :=
  Finset.univ.filter fun s => v ∈ raw C s

lemma mem_positions {C : AndCountCircuit 42} {v : V} {s : Slot C} :
    s ∈ positions C v ↔ v ∈ raw C s := by simp [positions]

noncomputable def readCount (C : AndCountCircuit 42) (v : V) : ℕ :=
  {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard

lemma positions_card (C : AndCountCircuit 42) (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (v : V) : (positions C v).card = readCount C v := by
  let gates : Finset (Fin C.size) :=
    Finset.univ.filter fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i
  have img : (positions C v).image Prod.fst = gates := by
    ext i
    simp only [gates, Finset.mem_image, mem_positions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j,b⟩,hj,rfl⟩
      cases b <;> simp_all [raw]
    · rintro (h | h)
      · exact ⟨(i,false), h, rfl⟩
      · exact ⟨(i,true), h, rfl⟩
  have inj : Set.InjOn Prod.fst (positions C v : Set (Slot C)) := by
    rintro ⟨i,b⟩ hi ⟨j,d⟩ hj eq
    change i = j at eq
    subst j
    have h₁ := mem_positions.mp (Finset.mem_coe.mp hi)
    have h₂ := mem_positions.mp (Finset.mem_coe.mp hj)
    have no {a : V} : a ∈ C.leftVars i → a ∉ C.rightVars i :=
      fun ha => Finset.disjoint_left.mp (hd i) ha
    cases b <;> cases d <;> first | rfl | exact (by simp [raw] at h₁ h₂; tauto)
  rw [← Finset.card_image_of_injOn inj, img]
  have eq : (gates : Set (Fin C.size)) = {i | v ∈ C.leftVars i ∨ v ∈ C.rightVars i} := by
    ext i
    simp [gates]
  rw [readCount, ← eq, Set.ncard_coe_finset]

def Hits (C : AndCountCircuit 42) (U : Finset V) (s : Slot C) : Prop :=
  ∃ v ∈ raw C s, v ∈ U

lemma eval_eq_of_hits (C : AndCountCircuit 42) (out : C.outVars = ∅)
    {U W : Finset V} (h : ∀ s, Hits C U s ↔ Hits C W s) : C.eval U = C.eval W := by
  have fuel (d : ℕ) (i : Fin C.size) : C.gateValFuel U d i = C.gateValFuel W d i := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      have l := h (i,false)
      have r := h (i,true)
      simp only [Hits, raw, Bool.false_eq_true, ite_false, ite_true] at l r
      simp only [gateValFuel, sideTrue, ih]
      congr 1
      · exact decide_eq_decide.mpr (or_congr l Iff.rfl)
      · exact decide_eq_decide.mpr (or_congr r Iff.rfl)
  simp only [AndCountCircuit.eval, out, Finset.notMem_empty, false_and, exists_false, false_or,
    gateVal, fuel]

lemma separation {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    {U : Finset V} (hu : Independent U) {v w : V} (hw : w ∈ U) (edge : plane.Adj v w) :
    ∃ s ∈ positions C v, ¬ Hits C U s := by
  classical
  by_contra! h
  have eq := eval_eq_of_hits C out (U := U) (W := insert v U) fun s => by
    constructor
    · rintro ⟨a, ha, hm⟩
      exact ⟨a, ha, Finset.mem_insert_of_mem hm⟩
    · rintro ⟨a, ha, hm⟩
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact h s (mem_positions.mpr ha)
      · exact ⟨a, ha, hm⟩
  have yes : C.eval (insert v U) = true :=
    (hc _).mpr ⟨v, by simp, w, Finset.mem_insert_of_mem hw, edge⟩
  obtain ⟨a, ha, b, hb, ab⟩ := (hc _).mp (eq.trans yes)
  exact hu a ha b hb ab

lemma witness {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {v w : V} (edge : plane.Adj v w) :
    ∃ s ∈ positions C v, w ∈ raw C (other s) := by
  have yes := (hc ({v,w} : Finset V)).mpr ⟨v, by simp, w, by simp, edge⟩
  simp only [AndCountCircuit.eval, out, decide_eq_true_eq, Finset.notMem_empty, false_and,
    exists_false, false_or, gateVal] at yes
  have base (d : ℕ) (i : Fin C.size) (h : C.gateValFuel {v,w} d i = true) :
      ∃ s ∈ positions C v, w ∈ raw C (other s) := by
    induction d generalizing i with
    | zero => simp [gateValFuel] at h
    | succ d ih =>
      simp only [gateValFuel, Bool.and_eq_true, sideTrue, decide_eq_true_eq] at h
      rcases h with ⟨⟨a, ha, ma⟩ | ⟨j, _, _, hj⟩, ⟨b, hb, mb⟩ | ⟨k, _, _, hk⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ma mb
        rcases ma with rfl | rfl <;> rcases mb with rfl | rfl
        · exact (Finset.disjoint_left.mp (hd i) ha hb).elim
        · exact ⟨(i,false), mem_positions.mpr ha, hb⟩
        · exact ⟨(i,true), mem_positions.mpr hb, ha⟩
        · exact (Finset.disjoint_left.mp (hd i) ha hb).elim
      · exact ih k hk
      · exact ih j hj
      · exact ih j hj
  obtain ⟨i, _, hi⟩ := yes
  exact base _ i hi

lemma pure_slot {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (v : V) : ∃ s ∈ positions C v, ∀ w ∈ raw C s, color w = color v := by
  let U := part (!color v)
  have hi : Independent U := fun p hp q hq e => cross e ((mem_part.mp hp).trans (mem_part.mp hq).symm)
  obtain ⟨w, hw⟩ := has_neighbor v
  have hwU : w ∈ U := mem_part.mpr (Bool.eq_not_of_ne (cross hw).symm)
  obtain ⟨s, hs, hn⟩ := separation hc out hi hwU hw
  refine ⟨s, hs, fun a ha => ?_⟩
  by_contra ne
  exact hn ⟨a, ha, mem_part.mpr (Bool.eq_not_of_ne ne)⟩

lemma private_slot {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (v : V) (cap : (positions C v).card ≤ 4) :
    ∃ s ∈ positions C v, ∀ w ∈ raw C s, color w = color v → w = v := by
  classical
  by_contra! h
  let f (s : Slot C) : V := if hs : s ∈ positions C v then Classical.choose (h s hs) else v
  let T := (positions C v).image f
  have spec (s : Slot C) (hs : s ∈ positions C v) :
      f s ∈ raw C s ∧ color (f s) = color v ∧ f s ≠ v := by
    simpa only [f, dite_eq_left hs] using Classical.choose_spec (h s hs)
  have hv : v ∉ T := by
    intro hm
    obtain ⟨s, hs, eq⟩ := Finset.mem_image.mp hm
    exact (spec s hs).2.2 eq
  obtain ⟨w, e, no⟩ := avoids v T (Finset.card_image_le.trans cap) hv
  have cols : ∀ a ∈ T, color a = color v := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    exact (spec s hs).2.1
  have ind : Independent (T ∪ {w}) := independent_parts cols
    (by simpa using (cross e).symm) (by simpa using no)
  obtain ⟨s, hs, hn⟩ := separation hc out ind (by simp) e
  exact hn ⟨f s, (spec s hs).1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)⟩


lemma avoids_excluding (v : V) (T F : Finset V) (hcard : T.card + F.card ≤ 4)
    (hv : v ∉ T) : ∃ w, plane.Adj v w ∧ (∀ t ∈ T, ¬ plane.Adj t w) ∧ w ∉ F := by
  classical
  by_contra! h
  have sub : neighbors v ⊆ T.biUnion (fun t => neighbors v ∩ neighbors t) ∪ F := by
    intro w hw
    by_cases hf : w ∈ F
    · exact Finset.mem_union_right _ hf
    have bad : ¬ (∀ t ∈ T, ¬ plane.Adj t w) := fun hno => hf (h w (mem_neighbors.mp hw) hno)
    push Not at bad
    obtain ⟨t, ht, he⟩ := bad
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_inter.mpr ⟨hw, mem_neighbors.mpr he⟩⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have sumCap : (∑ t ∈ T, (neighbors v ∩ neighbors t).card) ≤ T.card := by
    simpa using (Finset.sum_le_sum (g := fun _ => (1 : ℕ))
      fun t ht => intersections v t (fun eq => hv (eq ▸ ht)))
  have unionCap := Finset.card_biUnion_le (s := T) (t := fun t => neighbors v ∩ neighbors t)
  rw [degree] at bound
  omega

def low (C : AndCountCircuit 42) (b : Bool) : Finset V :=
  (part b).filter fun v => (positions C v).card ≤ 1

lemma mem_low {C : AndCountCircuit 42} {b : Bool} {v : V} :
    v ∈ low C b ↔ color v = b ∧ (positions C v).card ≤ 1 := by
  simp [low, mem_part]

lemma low_star {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {v : V}
    (cap : (positions C v).card ≤ 1) :
    ∃ s : Slot C, positions C v = {s} ∧ raw C s = {v} ∧ neighbors v ⊆ raw C (other s) := by
  obtain ⟨w, e⟩ := has_neighbor v
  obtain ⟨s, hs, _⟩ := witness hc out hd e
  have eq : positions C v = {s} := (Finset.eq_of_subset_of_card_le
    (Finset.singleton_subset_iff.mpr hs) (by simpa using cap)).symm
  obtain ⟨p, hp, pure⟩ := pure_slot hc out v
  obtain ⟨q, hq, priv⟩ := private_slot hc out v (cap.trans (by decide))
  have pEq : p = s := by simpa [eq] using hp
  have qEq : q = s := by simpa [eq] using hq
  subst p
  subst q
  refine ⟨s, eq, Finset.eq_singleton_iff_unique_mem.mpr
    ⟨mem_positions.mp hs, fun a ha => priv a ha (pure a ha)⟩, ?_⟩
  intro a ha
  obtain ⟨t, ht, h⟩ := witness hc out hd (mem_neighbors.mp ha)
  have tEq : t = s := by simpa [eq] using ht
  simpa only [tEq] using h

def Star (C : AndCountCircuit 42) (v : V) (s : Slot C) : Prop :=
  raw C s = {v} ∧ (raw C (other s) ∩ neighbors v).card ≥ 3

lemma low_has_star {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {v : V}
    (cap : (positions C v).card ≤ 1) : ∃ s, Star C v s := by
  obtain ⟨s, _, h, sub⟩ := low_star hc out hd cap
  exact ⟨s, h, by rw [Finset.inter_eq_right.mpr sub, degree]; decide⟩

lemma singleton_ne {C : AndCountCircuit 42} {a b : V} {s t : Slot C}
    (sa : raw C s = {a}) (tb : raw C t = {b}) (ne : a ≠ b) : s ≠ t := by
  intro e
  apply ne
  simpa using (show {a} = ({b} : Finset V) from sa.symm.trans (e ▸ tb))

lemma common_star {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {a b v : V} (ab : a ≠ b)
    (aLow : (positions C a).card ≤ 1) (bLow : (positions C b).card ≤ 1)
    (av : plane.Adj a v) (bv : plane.Adj b v) (cap : (positions C v).card ≤ 3) :
    ∃ s, Star C v s ∧ ∀ d, (positions C d).card ≤ 1 → plane.Adj d v → d = a ∨ d = b := by
  classical
  obtain ⟨p, pa, pRaw, pN⟩ := low_star hc out hd aLow
  obtain ⟨q, qb, qRaw, qN⟩ := low_star hc out hd bLow
  have pq : other p ≠ other q := fun h => singleton_ne pRaw qRaw ab (other_inj h)
  have hp := mem_positions.mpr (pN (mem_neighbors.mpr av))
  have hq := mem_positions.mpr (qN (mem_neighbors.mpr bv))
  obtain ⟨t, vt, _, tF⟩ := avoids_excluding v ∅ {a,b}
    (by simpa using (Finset.card_le_two.trans (show 2 ≤ 4 by decide) :
      ({a,b} : Finset V).card ≤ 4)) (by simp)
  have ta : t ≠ a := fun h => tF (by simp [h])
  have tb : t ≠ b := fun h => tF (by simp [h])
  obtain ⟨s, hs, ts⟩ := witness hc out hd vt
  have sp : s ≠ other p := by
    intro eq
    apply ta
    simpa [eq, other_other, pRaw] using ts
  have sq : s ≠ other q := by
    intro eq
    apply tb
    simpa [eq, other_other, qRaw] using ts
  have positions_eq : positions C v = {s, other p, other q} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [sp,sq]),
        Finset.card_insert_of_notMem (by simp [pq]), Finset.card_singleton]
      exact cap
  have sRaw : raw C s = {v} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_positions.mp hs, fun z hz => ?_⟩
    by_contra zv
    have zp : z ≠ a := by
      intro e
      subst z
      have eq : s = p := by simpa [pa] using mem_positions.mpr hz
      have hv := mem_positions.mp hs
      have : v = a := by simpa [eq, pRaw] using hv
      exact plane.ne_of_adj av this.symm
    have zq : z ≠ b := by
      intro e
      subst z
      have eq : s = q := by simpa [qb] using mem_positions.mpr hz
      have hv := mem_positions.mp hs
      have : v = b := by simpa [eq, qRaw] using hv
      exact plane.ne_of_adj bv this.symm
    obtain ⟨u, vu, zu, uF⟩ := avoids_excluding v {z} {a,b}
      (by simp only [Finset.card_singleton]; have := Finset.card_le_two (a := a) (b := b); omega)
       (by simpa using (Ne.symm zv))
    have ua : u ≠ a := fun e => uF (by simp [e])
    have ub : u ≠ b := fun e => uF (by simp [e])
    obtain ⟨x, ax, xn⟩ := avoids a {u,z}
      (Finset.card_le_two.trans (by decide)) (by simp [ua.symm,zp.symm])
    obtain ⟨y, by_, yn⟩ := avoids b {u,z}
      (Finset.card_le_two.trans (by decide)) (by simp [ub.symm,zq.symm])
    have axC : color x = color v :=
      (Bool.eq_not_of_ne (cross ax).symm).trans (Bool.eq_not_of_ne (cross av).symm).symm
    have byC : color y = color v :=
      (Bool.eq_not_of_ne (cross by_).symm).trans (Bool.eq_not_of_ne (cross bv).symm).symm
    let J : Finset V := ({x,y} : Finset V) ∪ {u}
    have indep : Independent J := by
      apply independent_parts (b := color v)
      · intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
      · simpa using (cross vu).symm
      · intro k hk l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
        subst l
        rcases hk with rfl | rfl
        · exact fun h => xn u (by simp) h.symm
        · exact fun h => yn u (by simp) h.symm
    have zJ : ∀ k ∈ J, ¬ plane.Adj z k := by
      intro k hk
      simp only [J, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | rfl
      · exact xn z (by simp)
      · exact yn z (by simp)
      · exact zu z (by simp)
    have ind : Independent (insert z J) := by
      intro j hj k hk e
      rcases Finset.mem_insert.mp hj with ej | hj
      · subst j
        rcases Finset.mem_insert.mp hk with ek | hk
        · subst k
          exact plane.loopless.irrefl _ e
        · exact zJ k hk e
      · rcases Finset.mem_insert.mp hk with ek | hk
        · subst k
          exact zJ j hj e.symm
        · exact indep j hj k hk e
    obtain ⟨k, hk, hno⟩ := separation hc out ind (by simp [J]) vu
    rw [positions_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hno ⟨z, hz, by simp⟩
    · exact hno ⟨x, pN (mem_neighbors.mpr ax), by simp [J]⟩
    · exact hno ⟨y, qN (mem_neighbors.mpr by_), by simp [J]⟩
  have extNeighbors : ((neighbors v).erase a).erase b ⊆ raw C (other s) ∩ neighbors v := by
    intro u hu
    obtain ⟨ub, hu⟩ := Finset.mem_erase.mp hu
    obtain ⟨ua, hu⟩ := Finset.mem_erase.mp hu
    obtain ⟨k, hk, huOpp⟩ := witness hc out hd (mem_neighbors.mp hu)
    rw [positions_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨huOpp, hu⟩
    · exact (ua (by simpa [other_other,pRaw] using huOpp)).elim
    · exact (ub (by simpa [other_other,qRaw] using huOpp)).elim
  have cardA := Finset.card_erase_add_one (mem_neighbors.mpr av.symm)
  have cardB := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨ab.symm, mem_neighbors.mpr bv.symm⟩)
  have bound := Finset.card_le_card extNeighbors
  rw [degree] at cardA
  refine ⟨s, ⟨sRaw, by omega⟩, fun d dl dv => ?_⟩
  obtain ⟨k, kd, kRaw, kN⟩ := low_star hc out hd dl
  have kpos := mem_positions.mpr (kN (mem_neighbors.mpr dv))
  rw [positions_eq] at kpos
  simp only [Finset.mem_insert, Finset.mem_singleton] at kpos
  rcases kpos with e | e | e
  · have os : other s = k := by rw [← e, other_other]
    have sub := Finset.card_le_card extNeighbors
    rw [os, kRaw] at sub
    have z := Finset.card_le_card (Finset.inter_subset_left (s₁ := ({d} : Finset V))
      (s₂ := neighbors v))
    rw [Finset.card_singleton] at z
    omega
  · have ep := other_inj e
    exact Or.inl (by simpa [ep, pRaw] using (show d ∈ raw C k by simp [kRaw]))
  · have eq := other_inj e
    exact Or.inr (by simpa [eq, qRaw] using (show d ∈ raw C k by simp [kRaw]))

def Private (C : AndCountCircuit 42) (v : V) (s : Slot C) : Prop :=
  v ∈ raw C s ∧ ∀ w ∈ raw C s, color w = color v → w = v

lemma star_neighbors {C : AndCountCircuit 42} {v : V} {s : Slot C}
    (h : Star C v s) : ∃ a b, a ∈ raw C (other s) ∧ b ∈ raw C (other s) ∧
      plane.Adj v a ∧ plane.Adj v b ∧ a ≠ b := by
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp
    (show 1 < (raw C (other s) ∩ neighbors v).card from by have := h.2; omega)
  obtain ⟨ha, ea⟩ := Finset.mem_inter.mp ha
  obtain ⟨hb, eb⟩ := Finset.mem_inter.mp hb
  exact ⟨a, b, ha, hb, mem_neighbors.mp ea, mem_neighbors.mp eb, ne⟩

lemma star_budget {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (size : C.size = 19) (cap : ∀ v, (positions C v).card ≤ 3)
    (T : Finset V) {b : Bool} (col : ∀ v ∈ T, color v = !b)
    (stars : ∀ v ∈ T, ∃ s, Star C v s) : T.card ≤ 8 := by
  classical
  have priv (v : V) : ∃ s, Private C v s := by
    obtain ⟨s, hs, h⟩ := private_slot hc out v ((cap v).trans (by decide))
    exact ⟨s, mem_positions.mp hs, h⟩
  choose p hp using priv
  let star (v : V) : Slot C := if hv : v ∈ T then Classical.choose (stars v hv) else p v
  have hs (v : V) (hv : v ∈ T) : Star C v (star v) := by
    simpa only [star, dite_eq_left hv] using Classical.choose_spec (stars v hv)
  let f (z : V × Bool) : Slot C := if z.2 then other (star z.1) else star z.1
  have injStar : Set.InjOn f (T.product (Finset.univ : Finset Bool) : Set (V × Bool)) := by
    rintro ⟨v, a⟩ hv ⟨w, d⟩ hw e
    have hvT := (Finset.mem_product.mp (Finset.mem_coe.mp hv)).1
    have hwT := (Finset.mem_product.mp (Finset.mem_coe.mp hw)).1
    have diff (v w : V) (hv : v ∈ T) (hw : w ∈ T) : star v ≠ other (star w) := by
      intro eq
      obtain ⟨x, y, hx, hy, _, _, ne⟩ := star_neighbors (hs w hw)
      rw [← eq, (hs v hv).1, Finset.mem_singleton] at hx hy
      exact ne (hx.trans hy.symm)
    have same (eq : star v = star w) : v = w := by
      by_contra ne
      exact singleton_ne (hs v hvT).1 (hs w hwT).1 ne eq
    cases a <;> cases d
    · exact Prod.ext (same e) rfl
    · exact (diff v w hvT hwT e).elim
    · exact (diff w v hwT hvT e.symm).elim
    · exact Prod.ext (same (other_inj e)) rfl
  have injPriv : Set.InjOn p (part b : Set V) := by
    intro v hv w hw e
    have colEq := (mem_part.mp (Finset.mem_coe.mp hw)).trans
      (mem_part.mp (Finset.mem_coe.mp hv)).symm
    exact ((hp v).2 w (e.symm ▸ (hp w).1) colEq).symm
  have dis : Disjoint ((part b).image p) ((T.product Finset.univ).image f) := by
    apply Finset.disjoint_left.mpr
    intro s h₁ h₂
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨⟨w,d⟩, hw, eq⟩ := Finset.mem_image.mp h₂
    have hwT := (Finset.mem_product.mp hw).1
    have vc := mem_part.mp hv
    have wc := col w hwT
    cases d
    · have he : star w = p v := eq
      have e : v = w := by
        simpa only [← he, (hs w hwT).1, Finset.mem_singleton] using (hp v).1
      subst v
      simp [vc] at wc
    · have he : other (star w) = p v := eq
      obtain ⟨a, c, ha, hc', wa, wc', ne⟩ := star_neighbors (hs w hwT)
      have cEq (x : V) (edge : plane.Adj w x) : color x = color v := by
        rw [vc]
        simpa [wc] using (Bool.eq_not_of_ne (cross edge).symm)
      exact ne (((hp v).2 a (he ▸ ha) (cEq a wa)).trans
        ((hp v).2 c (he ▸ hc') (cEq c wc')).symm)
  have bound := Finset.card_le_univ (((part b).image p) ∪ ((T.product Finset.univ).image f))
  rw [Finset.card_union_of_disjoint dis, Finset.card_image_of_injOn injPriv,
    Finset.card_image_of_injOn injStar, part_card] at bound
  change 21 + (T ×ˢ (Finset.univ : Finset Bool)).card ≤ Fintype.card (Slot C) at bound
  simp [Finset.card_product, Fintype.card_prod, size] at bound
  omega

lemma pair_star_budget {C : AndCountCircuit 42} (hc : C.Computes plane)
    (out : C.outVars = ∅) (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (size : C.size = 19) (cap : ∀ v, (positions C v).card ≤ 3) (b : Bool) :
    (low C b).card.choose 2 + (low C (!b)).card ≤ 8 := by
  classical
  let P := (low C b).powersetCard 2
  have pair (s : Finset V) (hs : s ∈ P) :
      ∃ v, color v = !b ∧ (∃ k, Star C v k) ∧
        (∀ d, d ∈ s ↔ (positions C d).card ≤ 1 ∧ plane.Adj d v) ∧ v ∉ low C (!b) := by
    obtain ⟨sub, card⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨a, c, ac, rfl⟩ := Finset.card_eq_two.mp card
    have al := mem_low.mp (sub (by simp : a ∈ ({a,c} : Finset V)))
    have cl := mem_low.mp (sub (by simp : c ∈ ({a,c} : Finset V)))
    obtain ⟨v, hv⟩ := common_same a c ac (al.1.trans cl.1.symm)
    obtain ⟨av, cv⟩ := Finset.mem_inter.mp hv
    have av := mem_neighbors.mp av
    have cv := mem_neighbors.mp cv
    obtain ⟨k, hk, only⟩ := common_star hc out hd ac al.2 cl.2 av cv (cap v)
    refine ⟨v, by simpa [al.1] using Bool.eq_not_of_ne (cross av).symm, ⟨k,hk⟩, ?_, ?_⟩
    · intro d
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨al.2, av⟩
        · exact ⟨cl.2, cv⟩
      · exact fun h => only d h.1 h.2
    · intro vl
      obtain ⟨p, _, pRaw, pN⟩ := low_star hc out hd al.2
      obtain ⟨q, _, qRaw, qN⟩ := low_star hc out hd cl.2
      have pl : other p ∈ positions C v := mem_positions.mpr (pN (mem_neighbors.mpr av))
      have ql : other q ∈ positions C v := mem_positions.mpr (qN (mem_neighbors.mpr cv))
      exact (singleton_ne pRaw qRaw ac) (other_inj (Finset.card_le_one.mp (mem_low.mp vl).2 _ pl _ ql))
  let f (s : Finset V) : V := if h : s ∈ P then Classical.choose (pair s h) else 0
  have spec (s : Finset V) (hs : s ∈ P) := Classical.choose_spec (pair s hs)
  have fs (s : Finset V) (hs : s ∈ P) :
      color (f s) = !b ∧ (∃ k, Star C (f s) k) ∧
        (∀ d, d ∈ s ↔ (positions C d).card ≤ 1 ∧ plane.Adj d (f s)) ∧ f s ∉ low C (!b) := by
    simpa only [f, dite_eq_left hs] using spec s hs
  have inj : Set.InjOn f (P : Set (Finset V)) := by
    intro s hs t ht eq
    have h := (fs s (Finset.mem_coe.mp hs)).2.2.1
    have h' := (fs t (Finset.mem_coe.mp ht)).2.2.1
    ext d
    exact (h d).trans (eq.symm ▸ (h' d).symm)
  have dis : Disjoint (P.image f) (low C (!b)) := by
    apply Finset.disjoint_left.mpr
    intro v hv vl
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    exact (fs s hs).2.2.2 vl
  have hb := star_budget hc out size cap (P.image f ∪ low C (!b)) (b := b)
    (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
        exact (fs s hs).1
      · exact (mem_low.mp hv).1)
    (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
        exact (fs s hs).2.1
      · exact low_has_star hc out hd (mem_low.mp hv).2)
  rwa [Finset.card_union_of_disjoint dis, Finset.card_image_of_injOn inj,
    Finset.card_powersetCard] at hb

lemma low_total (a b : ℕ) (h₁ : a.choose 2 + b ≤ 8) (h₂ : b.choose 2 + a ≤ 8) :
    a + b ≤ 6 := by
  have cap (n : ℕ) (h : n.choose 2 ≤ 8) : n ≤ 4 := by
    by_contra! hn
    have bound := Nat.choose_le_choose 2 (show 5 ≤ n by omega)
    have val : (5 : ℕ).choose 2 = 10 := by decide
    omega
  have ha := cap a (by omega)
  have hb := cap b (by omega)
  have six : (4 : ℕ).choose 2 = 6 := by decide
  by_cases ea : a = 4
  · rw [ea,six] at h₁
    omega
  by_cases eb : b = 4
  · rw [eb,six] at h₂
    omega
  omega

def Pure (C : AndCountCircuit 42) (s : Slot C) : Prop :=
  ∃ b : Bool, ∀ v ∈ raw C s, color v = b

def Solo (C : AndCountCircuit 42) (v : V) : Prop :=
  ∃ s, raw C s = {v}

def Layout (C : AndCountCircuit 42) (p q : V → Slot C) : Prop :=
  ∀ v, v ∈ raw C (p v) ∧ Pure C (p v) ∧ Private C v (q v) ∧
    (Solo C v → raw C (q v) = {v})

def Shared {C : AndCountCircuit 42} (q : V → Slot C) (v : V) : Prop :=
  ∃ w, w ≠ v ∧ q w = q v

lemma obtain_layout {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (cap : ∀ v, (positions C v).card ≤ 2) : ∃ p q, Layout C p q := by
  classical
  have hp (v : V) : ∃ s, v ∈ raw C s ∧ Pure C s := by
    obtain ⟨s, hs, h⟩ := pure_slot hc out v
    exact ⟨s, mem_positions.mp hs, color v, h⟩
  have hq (v : V) : ∃ s, Private C v s ∧ (Solo C v → raw C s = {v}) := by
    by_cases solo : Solo C v
    · obtain ⟨s, hs⟩ := solo
      exact ⟨s, ⟨by simp [hs], by simp [hs]⟩, fun _ => hs⟩
    · obtain ⟨s, hs, h⟩ := private_slot hc out v ((cap v).trans (by decide))
      exact ⟨s, ⟨mem_positions.mp hs, h⟩, fun z => (solo z).elim⟩
  choose p hp' using hp
  choose q hq' using hq
  exact ⟨p, q, fun v => ⟨(hp' v).1, (hp' v).2, (hq' v).1, (hq' v).2⟩⟩

section TwoReads

variable {C : AndCountCircuit 42} {p q : V → Slot C}

lemma pure_color (layout : Layout C p q) {v w : V} (hw : w ∈ raw C (p v)) :
    color w = color v := by
  obtain ⟨b, h⟩ := (layout v).2.1
  exact (h w hw).trans (h v (layout v).1).symm

lemma private_inj (layout : Layout C p q) {v w : V} (col : color v = color w)
    (eq : q v = q w) : v = w :=
  ((layout v).2.2.1.2 w (eq.symm ▸ (layout w).2.2.1.1) col.symm).symm

lemma shared_data (layout : Layout C p q) {v w : V} (wv : w ≠ v) (eq : q w = q v) :
    color w ≠ color v ∧ raw C (q v) = {v,w} ∧ ¬ Solo C v := by
  have wm : w ∈ raw C (q v) := eq ▸ (layout w).2.2.1.1
  have col : color w ≠ color v := fun h => wv (private_inj layout h eq)
  refine ⟨col, ?_, fun h => wv (by simpa [(layout v).2.2.2 h] using wm)⟩
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    by_cases h : color z = color v
    · exact Or.inl ((layout v).2.2.1.2 z hz h)
    · exact Or.inr ((layout w).2.2.1.2 z (eq.symm ▸ hz)
        ((Bool.eq_not_of_ne h).trans (Bool.eq_not_of_ne col).symm))
  · rintro (e | e)
    · exact e.symm ▸ (layout v).2.2.1.1
    · exact e.symm ▸ wm

lemma positions_two (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {v : V} (ns : ¬ Solo C v) : positions C v = {p v, q v} := by
  have ne : p v ≠ q v := by
    intro e
    apply ns
    refine ⟨p v, Finset.eq_singleton_iff_unique_mem.mpr ⟨(layout v).1, ?_⟩⟩
    intro w hw
    exact (layout v).2.2.1.2 w (e ▸ hw) (pure_color layout hw)
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact mem_positions.mpr (layout v).1
    · exact mem_positions.mpr (layout v).2.2.1.1
  · simpa [ne] using cap v

lemma two_companions {v a b : V} {s t : Slot C}
    (hc : C.Computes plane) (out : C.outVars = ∅)
    (reads : positions C v = {s,t}) (av : a ≠ v) (bv : b ≠ v)
    (aslot : a ∈ raw C s) (bslot : b ∈ raw C t) : plane.Adj a b := by
  classical
  by_contra ab
  obtain ⟨w, vw, h⟩ := avoids v {a,b} (Finset.card_le_two.trans (by decide))
    (by simp [Ne.symm av, Ne.symm bv])
  have ind : Independent ({a,b} ∪ ({w} : Finset V)) := by
    intro x hx y hy e
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with (rfl | rfl) | rfl <;> rcases hy with (rfl | rfl) | rfl
    all_goals first
      | exact plane.loopless.irrefl _ e
      | exact ab e
      | exact ab e.symm
      | exact h _ (by simp) e
      | exact h _ (by simp) e.symm
  obtain ⟨r, hr, hno⟩ := separation hc out ind (by simp) vw
  rw [reads] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact hno ⟨a, aslot, by simp⟩
  · exact hno ⟨b, bslot, by simp⟩

lemma shared_adj (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {v w z : V} (wv : w ≠ v) (eq : q w = q v)
    (hz : z ∈ raw C (p v)) (zv : z ≠ v) : plane.Adj w z := by
  have data := shared_data layout wv eq
  exact (two_companions hc out (positions_two layout cap data.2.2) zv wv hz
    (eq ▸ (layout w).2.2.1.1)).symm

lemma covered_two (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {v w : V} (sh : Shared q v) (edge : plane.Adj v w) :
    w ∈ raw C (other (p v)) ∨ w ∈ raw C (other (q v)) := by
  obtain ⟨u, uv, eq⟩ := sh
  obtain ⟨s, hs, h⟩ := witness hc out hd edge
  rw [positions_two layout cap (shared_data layout uv eq).2.2] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

lemma raw_disjoint_other (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (s : Slot C) : Disjoint (raw C s) (raw C (other s)) := by
  rcases s with ⟨i,b⟩
  cases b
  · exact hd i
  · exact (hd i).symm

lemma mate_pure_card (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {v w : V} (wv : w ≠ v) (eq : q w = q v) : (raw C (p v)).card ≤ 6 := by
  have sub : raw C (p v) ⊆ insert v (neighbors w) := by
    intro z hz
    by_cases e : z = v
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert_of_mem (mem_neighbors.mpr (shared_adj hc out layout cap wv eq hz e))
  have h := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  rw [degree] at h
  exact h

lemma pure_three_card (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {a b c u v : V} (ab : a ≠ b) (ca : c ≠ a) (cb : c ≠ b)
    (pb : p b = p a) (pc : p c = p a)
    (ua : u ≠ a) (vb : v ≠ b) (qu : q u = q a) (qv : q v = q b) :
    (raw C (p a)).card ≤ 3 := by
  have col := pure_color layout (pb ▸ (layout b).1)
  have qne : q a ≠ q b := fun e => ab (private_inj layout col.symm e)
  have ne : u ≠ v := fun e => qne (qu.symm.trans ((congrArg q e).trans qv))
  have cm : c ∈ raw C (p a) := pc ▸ (layout c).1
  have uc := shared_adj hc out layout cap ua qu cm ca
  have vc := shared_adj hc out layout cap vb qv (pb.symm ▸ cm) cb
  have sub : raw C (p a) ⊆ ({a,b,c} : Finset V) := by
    intro z hz
    by_cases za : z = a
    · simp [za]
    by_cases zb : z = b
    · simp [zb]
    have uz := shared_adj hc out layout cap ua qu hz za
    have vz := shared_adj hc out layout cap vb qv (pb.symm ▸ hz) zb
    simp [unique_common ne uz vz uc vc]
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right Finset.card_le_two 1))

lemma mate_on_opposite (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {v w : V} (wv : w ≠ v) (eq : q w = q v)
    (hw : w ∈ raw C (other (p v))) : p w = other (p v) := by
  have h := mem_positions.mpr hw
  rw [positions_two layout cap (shared_data layout wv.symm eq.symm).2.2] at h
  rcases Finset.mem_insert.mp h with e | e
  · exact e.symm
  · have bad := (Finset.mem_singleton.mp e).trans eq
    exact ((Finset.disjoint_left.mp (raw_disjoint_other hd (p v))) (layout v).1
      (bad.symm ▸ (layout v).2.2.1.1)).elim

lemma many_common_targets {a b u v : V} (ab : a ≠ b) (R : Finset V)
    (ha : neighbors a ⊆ insert u R) (hb : neighbors b ⊆ insert v R) :
    7 ≤ R.card := by
  let A := neighbors a ∩ R
  let B := neighbors b ∩ R
  have lower (x y : V) (h : neighbors x ⊆ insert y R) :
      4 ≤ (neighbors x ∩ R).card := by
    have sub : neighbors x ⊆ insert y (neighbors x ∩ R) := by
      intro z hz
      rcases Finset.mem_insert.mp (h hz) with e | e
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hz,e⟩)
    have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
    rw [degree] at bound
    omega
  have hA : 4 ≤ A.card := lower a u ha
  have hB : 4 ≤ B.card := lower b v hb
  have sub : A ∩ B ⊆ neighbors a ∩ neighbors b := by
    intro z hz
    obtain ⟨ha', hb'⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha').1, (Finset.mem_inter.mp hb').1⟩
  have hI := (Finset.card_le_card sub).trans (intersections a b ab)
  have hU : (A ∪ B).card ≤ R.card := Finset.card_le_card (Finset.union_subset
    (Finset.inter_subset_right : A ⊆ R) (Finset.inter_subset_right : B ⊆ R))
  have h := Finset.card_union_add_card_inter A B
  omega

lemma triple_mixed_separate (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {a b c : V} (ab : a ≠ b) (ca : c ≠ a) (cb : c ≠ b)
    (pb : p b = p a) (pc : p c = p a)
    (sa : Shared q a) (sb : Shared q b) (sc : Shared q c) :
    other (q a) ≠ q b := by
  obtain ⟨u, ua, qu⟩ := sa
  obtain ⟨v, vb, qv⟩ := sb
  obtain ⟨w, wc, qw⟩ := sc
  have col := pure_color layout (pb ▸ (layout b).1)
  have wcol := pure_color layout (pc ▸ (layout c).1)
  have dara := shared_data layout ua qu
  have darb := shared_data layout vb qv
  have darc := shared_data layout wc qw
  intro op
  have op' : other (q b) = q a := by rw [← op, other_other]
  have wa := shared_adj hc out layout cap wc qw (pc.symm ▸ (layout a).1) ca.symm
  have wr : w ∈ raw C (other (p a)) := by
    rcases covered_two hc out hd layout cap ⟨u,ua,qu⟩ wa.symm with h | h
    · exact h
    · rw [op, darb.2.1, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with e | e
      · exact (darc.1 (by rw [e, col, wcol])).elim
      · have same : q c = q b := qw.symm.trans ((congrArg q e).trans qv)
        have eq : c = b := private_inj layout (wcol.trans col.symm) same
        exact (cb eq).elim
  have pureW := mate_on_opposite hd layout cap wc qw (pc ▸ wr)
  have small := mate_pure_card hc out layout cap wc.symm qw.symm
  rw [pureW, pc] at small
  have cover (x y t : V) (sx : Shared q x) (px : p x = p a)
      (opp : raw C (other (q x)) = {y,t}) (same : color y = color x) :
      neighbors x ⊆ insert t (raw C (other (p a))) := by
    intro z hz
    have e := mem_neighbors.mp hz
    rcases covered_two hc out hd layout cap sx e with h | h
    · exact Finset.mem_insert_of_mem (px ▸ h)
    · rw [opp, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact ((cross e) same.symm).elim
      · exact Finset.mem_insert_self _ _
  have large := many_common_targets ab (raw C (other (p a)))
    (cover a b v ⟨u,ua,qu⟩ rfl (by rw [op, darb.2.1]) col)
    (cover b a u ⟨v,vb,qv⟩ pb (by rw [op', dara.2.1]) col.symm)
  omega

lemma triple_mates_opposite (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {a b c u : V} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (pb : p b = p a) (pc : p c = p a) (ua : u ≠ a) (qu : q u = q a)
    (sb : Shared q b) (sc : Shared q c) :
    p u = other (p a) := by
  have sa : Shared q a := ⟨u,ua,qu⟩
  have qb : other (q b) ≠ q a :=
    triple_mixed_separate hc out hd layout cap ab.symm bc.symm ac.symm pb.symm
      (pc.trans pb.symm) sb sa sc
  have qc : other (q c) ≠ q a :=
    triple_mixed_separate hc out hd layout cap ac.symm bc ab.symm pc.symm
      (pb.trans pc.symm) sc sa sb
  have bcol := pure_color layout (pb ▸ (layout b).1)
  have ccol := pure_color layout (pc ▸ (layout c).1)
  have qbc : q b ≠ q c := fun e => bc (private_inj layout (bcol.trans ccol.symm) e)
  have ub := shared_adj hc out layout cap ua qu (pb ▸ (layout b).1) ab.symm
  have uc := shared_adj hc out layout cap ua qu (pc ▸ (layout c).1) ac.symm
  apply mate_on_opposite hd layout cap ua qu
  by_contra h
  have hitB : u ∈ raw C (other (q b)) :=
    (covered_two hc out hd layout cap sb ub.symm).resolve_left (fun e => h (pb ▸ e))
  have hitC : u ∈ raw C (other (q c)) :=
    (covered_two hc out hd layout cap sc uc.symm).resolve_left (fun e => h (pc ▸ e))
  have reads := positions_two layout cap (shared_data layout ua.symm qu.symm).2.2
  have one (s : Slot C) (hs : u ∈ raw C s) (ne : s ≠ q a) : s = p u := by
    have hm := mem_positions.mpr hs
    rw [reads, Finset.mem_insert, Finset.mem_singleton, qu] at hm
    exact hm.resolve_right ne
  exact qbc (other_inj ((one _ hitB qb).trans (one _ hitC qc).symm))

lemma two_outside {v : V} {A B : Finset V} (small : A.card ≤ 3)
    (cover : neighbors v ⊆ A ∪ B) :
    ∃ x y, x ∈ B ∧ y ∈ B ∧ plane.Adj v x ∧ plane.Adj v y ∧ x ≠ y := by
  have sub : neighbors v ⊆ A ∪ (neighbors v ∩ B) := by
    intro w hw
    rcases Finset.mem_union.mp (cover hw) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw,h⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [degree] at bound
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp
    (show 1 < (neighbors v ∩ B).card by omega)
  obtain ⟨xa,xb⟩ := Finset.mem_inter.mp hx
  obtain ⟨ya,yb⟩ := Finset.mem_inter.mp hy
  exact ⟨x,y,xb,yb,mem_neighbors.mp xa,mem_neighbors.mp ya,ne⟩

lemma triple_spare (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q) (cap : ∀ v, (positions C v).card ≤ 2)
    {a b c : V} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (pb : p b = p a) (pc : p c = p a) (sa : Shared q a) (sb : Shared q b) (sc : Shared q c) :
    ¬ Pure C (other (q a)) ∧ ∀ z, ¬ Private C z (other (q a)) := by
  obtain ⟨u, ua, qu⟩ := sa
  obtain ⟨v, vb, qv⟩ := sb
  obtain ⟨w, wc, qw⟩ := sc
  have bcol := pure_color layout (pb ▸ (layout b).1)
  have ccol := pure_color layout (pc ▸ (layout c).1)
  have uv : u ≠ v := fun e => ab (private_inj layout bcol.symm
    (qu.symm.trans ((congrArg q e).trans qv)))
  have uw : u ≠ w := fun e => ac (private_inj layout ccol.symm
    (qu.symm.trans ((congrArg q e).trans qw)))
  have vw : v ≠ w := fun e => bc (private_inj layout (bcol.trans ccol.symm)
    (qv.symm.trans ((congrArg q e).trans qw)))
  have pu := triple_mates_opposite hc out hd layout cap ab ac bc pb pc ua qu
    ⟨v,vb,qv⟩ ⟨w,wc,qw⟩
  have pv := triple_mates_opposite hc out hd layout cap ab.symm bc ac pb.symm
    (pc.trans pb.symm) vb qv ⟨u,ua,qu⟩ ⟨w,wc,qw⟩
  have pw := triple_mates_opposite hc out hd layout cap ac.symm bc.symm ab pc.symm
    (pb.trans pc.symm) wc qw ⟨u,ua,qu⟩ ⟨v,vb,qv⟩
  have pvu : p v = p u := by rw [pv,pb,pu]
  have pwu : p w = p u := by rw [pw,pc,pu]
  have smallA := pure_three_card hc out layout cap ab ac.symm bc.symm pb pc ua vb qu qv
  have smallU := pure_three_card hc out layout cap uv uw.symm vw.symm pvu pwu
    ua.symm vb.symm qu.symm qv.symm
  have sA : (raw C (other (p a))).card ≤ 3 := by rwa [← pu]
  have sU : (raw C (other (p u))).card ≤ 3 := by rwa [pu, other_other]
  have cover (x : V) (sx : Shared q x) :
      neighbors x ⊆ raw C (other (p x)) ∪ raw C (other (q x)) := by
    intro z hz
    exact Finset.mem_union.mpr (covered_two hc out hd layout cap sx (mem_neighbors.mp hz))
  obtain ⟨x,y,hx,hy,ax,ay,xy⟩ := two_outside sA (cover a ⟨u,ua,qu⟩)
  obtain ⟨i,j,hi,hj,ui,uj,ij⟩ := two_outside sU (cover u ⟨a,ua.symm,qu.symm⟩)
  rw [qu] at hi hj
  have uaCol := (shared_data layout ua qu).1
  have xx : color x = color u :=
    (Bool.eq_not_of_ne (cross ax).symm).trans (Bool.eq_not_of_ne uaCol).symm
  have yy : color y = color u :=
    (Bool.eq_not_of_ne (cross ay).symm).trans (Bool.eq_not_of_ne uaCol).symm
  have ii : color i = color a :=
    (Bool.eq_not_of_ne (cross ui).symm).trans (Bool.eq_not_of_ne (Ne.symm uaCol)).symm
  have jj : color j = color a :=
    (Bool.eq_not_of_ne (cross uj).symm).trans (Bool.eq_not_of_ne (Ne.symm uaCol)).symm
  refine ⟨fun ⟨d,h⟩ => uaCol (xx.symm.trans ((h x hx).trans ((h i hi).symm.trans ii))), ?_⟩
  intro z h
  by_cases e : color z = color a
  · exact ij ((h.2 i hi (ii.trans e.symm)).trans (h.2 j hj (jj.trans e.symm)).symm)
  · have e' : color z = color u := (Bool.eq_not_of_ne e).trans (Bool.eq_not_of_ne uaCol).symm
    exact xy ((h.2 x hx (xx.trans e'.symm)).trans (h.2 y hy (yy.trans e'.symm)).symm)

lemma two_reads_impossible {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (size : C.size = 19)
    (cap : ∀ v, (positions C v).card ≤ 2) : False := by
  classical
  obtain ⟨p,q,layout⟩ := obtain_layout hc out cap
  let A := (Finset.univ : Finset V).image q
  let S := (Finset.univ : Finset V).filter (Shared q)
  let reserved (s : Slot C) := Pure C s ∨ s ∈ A
  let f (v : V) := if reserved (other (q v)) then p v else other (q v)
  let B := S.image f
  have isShared {v : V} : v ∈ S ↔ Shared q v := by simp [S]
  have notPrivate (v : V) (hv : Shared q v) : ∀ z, ¬ Private C z (p v) := by
    obtain ⟨w,ne,eq⟩ := hv
    intro z h
    obtain ⟨b,e⟩ := (layout v).2.1
    have vz : v = z := h.2 v (layout v).1 ((e v (layout v).1).trans (e z h.1).symm)
    subst z
    exact (shared_data layout ne eq).2.2 ⟨p v, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨h.1, fun x hx => h.2 x hx ((e x hx).trans (e v h.1).symm)⟩⟩
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro s ha hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z,_,eq⟩ := Finset.mem_image.mp ha
    by_cases r : reserved (other (q v))
    · have e : q z = p v := by simpa only [f, ite_eq_left r] using eq
      exact notPrivate v (isShared.mp hv) z (e ▸ (layout z).2.2.1)
    · have e : q z = other (q v) := by simpa only [f, ite_eq_right r] using eq
      exact r (Or.inr (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, e⟩))
  have qFiber (s : Slot C) :
      ((Finset.univ : Finset V).filter fun v => q v = s).card ≤ 2 := by
    have h := Finset.card_le_card_of_injOn color
      (t := (Finset.univ : Finset Bool)) (s := (Finset.univ : Finset V).filter fun v => q v = s)
      (fun _ _ => Finset.mem_univ _) (by
        intro v hv w hw col
        exact private_inj layout col ((Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2.trans
          (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2.symm))
    simpa using h
  have fFiber (s : Slot C) : (S.filter fun v => f v = s).card ≤ 2 := by
    have fm {v : V} (hv : v ∈ S.filter fun v => f v = s) := Finset.mem_filter.mp hv
    by_cases hPure : Pure C s
    · have fromPure {v : V} (hv : v ∈ S.filter fun v => f v = s) :
          reserved (other (q v)) ∧ p v = s := by
        have eq := (fm hv).2
        by_cases r : reserved (other (q v))
        · exact ⟨r, by simpa only [f, ite_eq_left r] using eq⟩
        · have e : other (q v) = s := by simpa only [f, ite_eq_right r] using eq
          exact (r (Or.inl (e.symm ▸ hPure))).elim
      by_contra! h
      obtain ⟨a,ha,b,hb,c,hc',ab,ac,bc⟩ := Finset.two_lt_card.mp h
      have ha' := fromPure ha
      have hSpare := triple_spare hc out hd layout cap ab ac bc
        ((fromPure hb).2.trans ha'.2.symm) ((fromPure hc').2.trans ha'.2.symm)
        (isShared.mp (fm ha).1) (isShared.mp (fm hb).1) (isShared.mp (fm hc').1)
      rcases ha'.1 with h | h
      · exact hSpare.1 h
      · obtain ⟨z,_,eq⟩ := Finset.mem_image.mp h
        exact hSpare.2 z (eq ▸ (layout z).2.2.1)
    · have fromMixed {v : V} (hv : v ∈ S.filter fun v => f v = s) : q v = other s := by
        have eq := (fm hv).2
        by_cases r : reserved (other (q v))
        · have e : p v = s := by simpa only [f, ite_eq_left r] using eq
          exact (hPure (e ▸ (layout v).2.1)).elim
        · have e : other (q v) = s := by simpa only [f, ite_eq_right r] using eq
          rw [← e, other_other]
      refine (Finset.card_le_card ?_).trans (qFiber (other s))
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fromMixed hv⟩
  have sharedCount : S.card ≤ 2 * B.card := by
    rw [Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_image_of_mem f hv)]
    calc
      (∑ s ∈ B, (S.filter fun v => f v = s).card) ≤ ∑ _s ∈ B, 2 :=
        Finset.sum_le_sum fun s _ => fFiber s
      _ = 2 * B.card := by simp [Nat.mul_comm]
  have countAt (s : Slot C) (hs : s ∈ A) :
      2 * ((Finset.univ : Finset V).filter fun v => q v = s).card =
        2 + (S.filter fun v => q v = s).card := by
    let T := (Finset.univ : Finset V).filter fun v => q v = s
    let R := S.filter fun v => q v = s
    obtain ⟨v,_,eq⟩ := Finset.mem_image.mp hs
    have vm : v ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq⟩
    have capT : T.card ≤ 2 := qFiber s
    change 2 * T.card = 2 + R.card
    by_cases h : 1 < T.card
    · have same : T = R := by
        ext x
        simp only [T,R,Finset.mem_filter,Finset.mem_univ,true_and,isShared]
        constructor
        · intro e
          refine ⟨?_,e⟩
          obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp h
          have ea := (Finset.mem_filter.mp ha).2
          have eb := (Finset.mem_filter.mp hb).2
          by_cases ax : a = x
          · exact ⟨b, ax ▸ ab.symm, eb.trans e.symm⟩
          · exact ⟨a, ax, ea.trans e.symm⟩
        · exact And.right
      rw [← same]
      omega
    · have only := Finset.card_le_one.mp (show T.card ≤ 1 by omega)
      have emp : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hsh,hx'⟩ := Finset.mem_filter.mp hx
        obtain ⟨y,ne,e⟩ := isShared.mp hsh
        exact ne (only y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.trans hx'⟩)
          x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩))
      have pos := Finset.card_pos.mpr ⟨v,vm⟩
      rw [emp,Finset.card_empty]
      omega
  have accounted : 84 = 2 * A.card + S.card := by
    have all := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset V)) (t := A) (f := q)
      (fun v hv => Finset.mem_image_of_mem q hv)
    have sh := Finset.card_eq_sum_card_fiberwise (s := S) (t := A) (f := q)
      (fun v _ => Finset.mem_image_of_mem q (Finset.mem_univ v))
    calc
      84 = 2 * (Finset.univ : Finset V).card := by decide
      _ = 2 * (∑ s ∈ A, ((Finset.univ : Finset V).filter fun v => q v = s).card) :=
        congrArg (fun n : ℕ => 2 * n) all
      _ = ∑ s ∈ A, 2 * ((Finset.univ : Finset V).filter fun v => q v = s).card :=
        Finset.mul_sum _ _ _
      _ = ∑ s ∈ A, (2 + (S.filter fun v => q v = s).card) :=
        Finset.sum_congr rfl countAt
      _ = (∑ _s ∈ A, (2 : ℕ)) + ∑ s ∈ A, (S.filter fun v => q v = s).card :=
        Finset.sum_add_distrib
      _ = 2 * A.card + S.card := by
        rw [← sh]
        simp [Nat.mul_comm]
  have total := Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint dis] at total
  simp [Fintype.card_prod, size] at total
  omega

end TwoReads

lemma low_count (C : AndCountCircuit 42) (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (low C true).card = {v : V | v.val < 21 ∧ readCount C v ≤ 1}.ncard ∧
    (low C false).card = {v : V | 21 ≤ v.val ∧ readCount C v ≤ 1}.ncard := by
  have ht : (low C true : Set V) = {v : V | v.val < 21 ∧ readCount C v ≤ 1} := by
    ext v
    simp [mem_low, color, positions_card C hd]
  have hf : (low C false : Set V) = {v : V | 21 ≤ v.val ∧ readCount C v ≤ 1} := by
    ext v
    simp [mem_low, color, positions_card C hd]
  exact ⟨by rw [← ht, Set.ncard_coe_finset], by rw [← hf, Set.ncard_coe_finset]⟩

end PEqualNP.Outside.L_meta_7537


open PEqualNP.Outside.L_meta_7537

theorem PEqualNP.Outside.L_meta_7537 :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.Computes x1 →     x2.outVars = ∅ →       (∀ (x5 : Fin x2.size), Disjoint (x2.leftVars x5) (x2.rightVars x5)) →         x2.size = (19 : ℕ) →           (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin x2.size | x7 ∈ x2.leftVars x8 ∨ x7 ∈ x2.rightVars x8}.ncard ≤ (3 : ℕ)) →             have x8 : Fin (42 : ℕ) → ℕ := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9}.ncard;             have x9 : ℕ := {x9 : Fin (42 : ℕ) | ↑x9 < (21 : ℕ) ∧ x8 x9 ≤ (1 : ℕ)}.ncard;             have x10 : ℕ := {x10 : Fin (42 : ℕ) | (21 : ℕ) ≤ ↑x10 ∧ x8 x10 ≤ (1 : ℕ)}.ncard;             x9.choose (2 : ℕ) + x10 ≤ (8 : ℕ) ∧ x10.choose (2 : ℕ) + x9 ≤ (8 : ℕ) ∧ x9 + x10 ≤ (6 : ℕ) ∧ ∃ (x11 : Fin (42 : ℕ)), x8 x11 = (3 : ℕ) := by
  intro graph C hc out hd size bound
  change C.Computes plane at hc
  have cap (v : V) : (positions C v).card ≤ 3 := by
    rw [positions_card C hd]
    exact bound v
  have h₁ := pair_star_budget hc out hd size cap true
  have h₂ := pair_star_budget hc out hd size cap false
  change (low C true).card.choose 2 + (low C false).card ≤ 8 at h₁
  change (low C false).card.choose 2 + (low C true).card ≤ 8 at h₂
  have hsum := low_total _ _ h₁ h₂
  have three : ∃ v, readCount C v = 3 := by
    by_contra! h
    apply two_reads_impossible hc out hd size
    intro v
    have ca := cap v
    have ne := h v
    rw [positions_card C hd] at ca ⊢
    omega
  obtain ⟨ht,hf⟩ := low_count C hd
  rw [ht,hf] at h₁ h₂ hsum
  exact ⟨h₁,h₂,hsum,three⟩
