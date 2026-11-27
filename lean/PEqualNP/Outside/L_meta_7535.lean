import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7535

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

lemma table_intersection : ∀ v w : V, v.val < w.val →
    (neighborTable v ∩ neighborTable w).card ≤ 1 := by
  decide +kernel

lemma intersections (v w : V) (ne : v ≠ w) : (neighbors v ∩ neighbors w).card ≤ 1 := by
  rw [neighbors_table, neighbors_table]
  have h : v.val ≠ w.val := fun e => ne (Fin.ext e)
  rcases lt_or_gt_of_ne h with h | h
  · exact table_intersection v w h
  · rw [Finset.inter_comm]
    exact table_intersection w v h

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
      exact congrArg₂ (· && ·) (decide_eq_decide.mpr (or_congr l Iff.rfl))
        (decide_eq_decide.mpr (or_congr r Iff.rfl))
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


def pick (S : Finset V) (b : Bool) : Finset V := S.filter fun v => color v = b

lemma mem_pick {S : Finset V} {b : Bool} {v : V} :
    v ∈ pick S b ↔ v ∈ S ∧ color v = b := by simp [pick]

lemma pick_card (S : Finset V) :
    (pick S true).card + (pick S false).card = S.card := by
  have eq : pick S true ∪ pick S false = S := by
    ext v
    cases h : color v <;> simp [mem_pick, h]
  have hd : Disjoint (pick S true) (pick S false) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    exact Bool.noConfusion (show true = false from (mem_pick.mp hv).2.symm.trans (mem_pick.mp hw).2)
  rw [← Finset.card_union_of_disjoint hd, eq]


def between (S T : Finset V) : Finset (V × V) :=
  @Finset.filter _ (fun p : V × V => plane.Adj p.1 p.2)
    (fun p => adjDec p.1 p.2) (S ×ˢ T)

lemma mem_between {S T : Finset V} {p : V × V} :
    p ∈ between S T ↔ p.1 ∈ S ∧ p.2 ∈ T ∧ plane.Adj p.1 p.2 := by
  simp only [between, Finset.mem_filter, Finset.mem_product, and_assoc]

lemma between_symm (S T : Finset V) : (between S T).card = (between T S).card := by
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    obtain ⟨hs, ht, ha⟩ := mem_between.mp hp
    exact mem_between.mpr ⟨ht, hs, ha.symm⟩
  · intro a ha b hb e
    exact congrArg Prod.swap e
  · intro p hp
    obtain ⟨ht, hs, ha⟩ := mem_between.mp hp
    exact ⟨p.swap, mem_between.mpr ⟨hs, ht, ha.symm⟩, rfl⟩

def links (S : Finset V) (w : V) := S ∩ neighbors w

lemma between_sum (S T : Finset V) :
    (between S T).card = ∑ w ∈ T, (links S w).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := T)
    (fun p hp => (mem_between.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨hp, h⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, _, ha⟩ := mem_between.mp hp
    exact Finset.mem_inter.mpr ⟨hx, mem_neighbors.mpr (h ▸ ha.symm)⟩
  · intro a ha b hb e
    exact Prod.ext e ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  · intro v hv
    obtain ⟨hs, hn⟩ := Finset.mem_inter.mp hv
    exact ⟨(v,w), Finset.mem_filter.mpr ⟨mem_between.mpr
      ⟨hs, hw, (mem_neighbors.mp hn).symm⟩, rfl⟩, rfl⟩

lemma links_le (S : Finset V) (w : V) : (links S w).card ≤ 5 := by
  rw [← degree w]
  exact Finset.card_le_card Finset.inter_subset_right

-- Each pair of vertices in S can have at most one common neighbor in T.
lemma between_pairs (S T : Finset V) :
    (∑ w ∈ T, ((links S w).card.choose 2)) ≤ S.card.choose 2 := by
  let f (w : V) := (links S w).powersetCard 2
  have dis : (T : Set V).PairwiseDisjoint f := by
    intro v hv w hw ne
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨ht, _⟩ := Finset.mem_powersetCard.mp hQ
    have sub : P ⊆ neighbors v ∩ neighbors w := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hs ha)).2,
        (Finset.mem_inter.mp (ht ha)).2⟩
    have := (Finset.card_le_card sub).trans (intersections v w ne)
    omega
  have sub : T.biUnion f ⊆ S.powersetCard 2 := by
    intro P hP
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hw
    exact Finset.mem_powersetCard.mpr ⟨hs.trans Finset.inter_subset_left, hc⟩
  have h := Finset.card_le_card sub
  simpa [Finset.card_biUnion dis, Finset.card_powersetCard, f] using h

def triangle (n : ℕ) : ℕ := n * (n-1) / 2

lemma triangle_eq (n : ℕ) : triangle n = n.choose 2 := (Nat.choose_two_right n).symm

def rectangleBound (a b : ℕ) : ℕ :=
  min (a*b) (min (5*a) (min (5*b) (min (b + triangle a) (min (a + triangle b)
    (min ((3*b + triangle a)/2) ((3*a + triangle b)/2))))))

lemma between_bound_aux (S T : Finset V) :
    (between S T).card ≤ 5*T.card ∧
    (between S T).card ≤ T.card + S.card.choose 2 ∧
    2*(between S T).card ≤ 3*T.card + S.card.choose 2 := by
  have small (n : ℕ) (hn : n ≤ 5) : n ≤ 1 + n.choose 2 ∧ 2*n ≤ 3 + n.choose 2 := by
    interval_cases n <;> decide
  have h₁ := Finset.sum_le_sum (s := T) (g := fun _ => 5) (fun w _ => links_le S w)
  have h₂ := Finset.sum_le_sum (s := T) (g := fun w => 1 + (links S w).card.choose 2)
    (fun w _ => (small _ (links_le S w)).1)
  have h₃ := Finset.sum_le_sum (s := T) (g := fun w => 3 + (links S w).card.choose 2)
    (fun w _ => (small _ (links_le S w)).2)
  have h₄ := between_pairs S T
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ← Finset.mul_sum, ← between_sum] at h₁ h₂ h₃
  omega

lemma between_bound (S T : Finset V) :
    (between S T).card ≤ rectangleBound S.card T.card := by
  have h₁ := between_bound_aux S T
  have h₂ := between_bound_aux T S
  rw [← between_symm S T] at h₂
  let : DecidablePred (fun p : V × V => plane.Adj p.1 p.2) := fun p => adjDec p.1 p.2
  have h₃ := Finset.card_filter_le (s := S ×ˢ T) (p := fun p => plane.Adj p.1 p.2)
  change (between S T).card ≤ (S ×ˢ T).card at h₃
  rw [Finset.card_product] at h₃
  simp only [rectangleBound, triangle_eq, le_min_iff]
  omega

-- Verify the rectangle inequality on the four color counts for a narrow gate.
def arithmeticCheck (a b c d : ℕ) : Bool :=
  if a+b ≤ 5 ∧ a+c ≤ 21 ∧ b+d ≤ 21 ∧
      ¬ (5 ≤ min (a+b) (c+d) ∧ 6 ≤ max (a+b) (c+d) ∨
        4 ≤ min (a+b) (c+d) ∧ 14 ≤ max (a+b) (c+d)) then
    let e := rectangleBound a d + rectangleBound c b
    let q := (if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
      (if c=1 then 1 else 0) + (if d=1 then 1 else 0)
    let lhs := 90*e+75*q+8*((a+c)*(b+d))
    let rhs := 128*(a+b+c+d)
    if lhs < rhs then true else decide (lhs = rhs ∧ (q = 0 ∨ q = 4))
  else true

lemma arithmeticCheck_true : ∀ a b : Fin 6, ∀ c d : Fin 22,
    arithmeticCheck a.val b.val c.val d.val = true := by
  decide +kernel

lemma arithmetic_small : ∀ x y : Fin 6, ∀ c d : Fin 22,
    let a := x.val; let b := y.val; let c := c.val; let d := d.val
    a+b ≤ 5 → a+c ≤ 21 → b+d ≤ 21 →
    (¬ (5 ≤ min (a+b) (c+d) ∧ 6 ≤ max (a+b) (c+d) ∨
        4 ≤ min (a+b) (c+d) ∧ 14 ≤ max (a+b) (c+d))) →
    let e := rectangleBound a d + rectangleBound c b
    let q := (if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
      (if c=1 then 1 else 0) + (if d=1 then 1 else 0)
    90*e+75*q+8*((a+c)*(b+d)) ≤ 128*(a+b+c+d) ∧
      (90*e+75*q+8*((a+c)*(b+d)) = 128*(a+b+c+d) → q = 0 ∨ q = 4) := by
  intro a b c d
  dsimp only
  intro hs hp hl hn
  have checked := arithmeticCheck_true a b c d
  unfold arithmeticCheck at checked
  rw [ite_eq_left ⟨hs,hp,hl,hn⟩] at checked
  let q := (if a.val=1 then 1 else 0) + (if b.val=1 then 1 else 0) +
    (if c.val=1 then 1 else 0) + (if d.val=1 then 1 else 0)
  let L := 90*(rectangleBound a.val d.val + rectangleBound c.val b.val) +
    75*q + 8*((a.val+c.val)*(b.val+d.val))
  let R := 128*(a.val+b.val+c.val+d.val)
  change (if L < R then true else decide (L = R ∧ (q = 0 ∨ q = 4))) = true at checked
  change L ≤ R ∧ (L = R → q = 0 ∨ q = 4)
  by_cases lt : L < R
  · exact ⟨Nat.le_of_lt lt, fun h => (Nat.ne_of_lt lt h).elim⟩
  · rw [ite_eq_right lt] at checked
    have eq := of_decide_eq_true checked
    exact ⟨eq.1.le, fun _ => eq.2⟩


abbrev Gate (C : AndCountCircuit 42) := Fin C.size

def gateVars (C : AndCountCircuit 42) (i : Gate C) := C.leftVars i ∪ C.rightVars i

lemma card_set {C : AndCountCircuit 42} (p : Gate C → Prop) [DecidablePred p] :
    {i | p i}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

def isolated (S : Finset V) (b : Bool) : ℕ := if (pick S b).card = 1 then 1 else 0

def isolation (C : AndCountCircuit 42) (i : Gate C) : ℕ :=
  isolated (C.leftVars i) true + isolated (C.leftVars i) false +
  isolated (C.rightVars i) true + isolated (C.rightVars i) false

lemma isolation_sum {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (cap : ∀ v, (positions C v).card ≤ 3) :
    42 ≤ ∑ i, isolation C i := by
  classical
  have one (v : V) : ∃ s : Slot C, pick (raw C s) (color v) = {v} := by
    obtain ⟨s, hs, h⟩ := private_slot hc out v ((cap v).trans (by decide))
    exact ⟨s, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_pick.mpr ⟨mem_positions.mp hs, rfl⟩, fun w hw =>
        h w (mem_pick.mp hw).1 (mem_pick.mp hw).2⟩⟩
  choose f hf using one
  let T : Finset (Gate C × (Bool × Bool)) := Finset.univ.filter fun p =>
    (pick (raw C (p.1, p.2.1)) p.2.2).card = 1
  have inj : Function.Injective (fun v : V => (f v |>.1, (f v |>.2, color v))) := by
    intro v w eq
    have hslot : f v = f w := Prod.ext (congrArg (fun p : Gate C × (Bool × Bool) => p.1) eq)
      (congrArg (fun p : Gate C × (Bool × Bool) => p.2.1) eq)
    have hcolor : color v = color w := congrArg (fun p => p.2.2) eq
    have same := hf v
    rw [hslot, hcolor, hf w] at same
    simpa using same.symm
  have bound := Finset.card_le_card (s := Finset.univ.image
    (fun v : V => (f v |>.1, (f v |>.2, color v)))) (t := T) (by
      intro p hp
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
      simp [T, hf])
  rw [Finset.card_image_of_injective _ inj] at bound
  have eq : T.card = ∑ i, isolation C i := calc
    T.card = ∑ _p ∈ T, (1 : ℕ) := by simp
    _ = ∑ i, isolation C i := by
      unfold T
      rw [Finset.sum_filter]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, isolation, isolated, raw,
        Bool.false_eq_true, ite_false, ite_true]
      ac_rfl
  simpa [eq] using bound

def orient (b : Bool) (S T : Finset V) := between (pick S b) (pick T (!b))

def graphEdges : Finset (V × V) := between (part true) (part false)

def missedPairs : Finset (V × V) :=
  @Finset.filter _ (fun p : V × V => ¬plane.Adj p.1 p.2)
    (fun p => @instDecidableNot _ (adjDec p.1 p.2)) (part true ×ˢ part false)


lemma mem_missed {p : V × V} :
    p ∈ missedPairs ↔ p.1 ∈ part true ∧ p.2 ∈ part false ∧ ¬plane.Adj p.1 p.2 := by
  simp only [missedPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

lemma neighbors_part (v : V) : neighbors v ⊆ part (!color v) := by
  intro w hw
  exact mem_part.mpr (Bool.eq_not_of_ne (cross (mem_neighbors.mp hw)).symm)

lemma graphEdges_card : graphEdges.card = 105 := by
  rw [graphEdges, between_sum]
  have all (v : V) (hv : v ∈ part false) : (links (part true) v).card = 5 := by
    have h := neighbors_part v
    rw [mem_part.mp hv] at h
    rw [links, Finset.inter_eq_right.mpr (show neighbors v ⊆ part true from h), degree]
  rw [Finset.sum_congr rfl all]
  simp [part_card]

lemma nonneighbors_card (v : V) : (part (!color v) \ neighbors v).card = 16 := by
  rw [Finset.card_sdiff_of_subset (neighbors_part v), part_card, degree]

lemma missedPairs_fst (p : V) (h : color p = true) :
    (missedPairs.filter fun q => q.1 = p).card = 16 := by
  rw [← nonneighbors_card p, h]
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, h₂, hn⟩ := mem_missed.mp hm
    exact Finset.mem_sdiff.mpr ⟨h₂, fun hd => hn (hp.symm ▸ mem_neighbors.mp hd)⟩
  · intro a ha b hb eq
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) eq
  · intro v hv
    obtain ⟨h₂, hn⟩ := Finset.mem_sdiff.mp hv
    exact ⟨(p,v), Finset.mem_filter.mpr ⟨mem_missed.mpr
      ⟨mem_part.mpr h, h₂, fun e => hn (mem_neighbors.mpr e)⟩, rfl⟩, rfl⟩

lemma missedPairs_snd (p : V) (h : color p = false) :
    (missedPairs.filter fun q => q.2 = p).card = 16 := by
  rw [← nonneighbors_card p, h]
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨h₁, _, hn⟩ := mem_missed.mp hm
    exact Finset.mem_sdiff.mpr ⟨h₁, fun hd => hn (hp.symm ▸ (mem_neighbors.mp hd).symm)⟩
  · intro a ha b hb eq
    exact Prod.ext eq ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  · intro v hv
    obtain ⟨h₁, hn⟩ := Finset.mem_sdiff.mp hv
    exact ⟨(v,p), Finset.mem_filter.mpr ⟨mem_missed.mpr
      ⟨h₁, mem_part.mpr h, fun e => hn (mem_neighbors.mpr e.symm)⟩, rfl⟩, rfl⟩

lemma missedPairs_card : missedPairs.card = 336 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := part true)
    (fun p hp => (mem_missed.mp hp).1)]
  rw [Finset.sum_congr rfl (fun p hp => missedPairs_fst p (mem_part.mp hp))]
  simp [part_card]

def across (C : AndCountCircuit 42) (i : Gate C) (p : V × V) : Prop :=
  (p.1 ∈ C.leftVars i ∧ p.2 ∈ C.rightVars i) ∨
  (p.1 ∈ C.rightVars i ∧ p.2 ∈ C.leftVars i)

def covered (C : AndCountCircuit 42) (i : Gate C) : Finset (V × V) :=
  graphEdges.filter fun p =>
    (p.1 ∈ C.leftVars i ∧ p.2 ∈ C.rightVars i) ∨
    (p.1 ∈ C.rightVars i ∧ p.2 ∈ C.leftVars i)

lemma mem_covered {C : AndCountCircuit 42} {i : Gate C} {p : V × V} :
    p ∈ covered C i ↔ p ∈ graphEdges ∧ across C i p := by simp [covered, across]

lemma cover_sum {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    105 ≤ ∑ i, (covered C i).card := by
  have sub : graphEdges ⊆ Finset.univ.biUnion (covered C) := by
    intro p hp
    obtain ⟨_, _, e⟩ := mem_between.mp hp
    obtain ⟨⟨i,b⟩, hs, hw⟩ := witness hc out hd e
    have hv := mem_positions.mp hs
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, mem_covered.mpr
      ⟨hp, by cases b <;> first | exact Or.inl ⟨hv, hw⟩ | exact Or.inr ⟨hv, hw⟩⟩⟩
  rw [← graphEdges_card]
  exact (Finset.card_le_card sub).trans Finset.card_biUnion_le

lemma covered_eq {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i)) :
    (covered C i).card = (orient true (C.leftVars i) (C.rightVars i)).card +
      (orient true (C.rightVars i) (C.leftVars i)).card := by
  have eq : covered C i =
      orient true (C.leftVars i) (C.rightVars i) ∪ orient true (C.rightVars i) (C.leftVars i) := by
    ext p
    simp only [mem_covered, graphEdges, mem_between, mem_part, across, Finset.mem_union,
      orient, mem_pick, Bool.not_true]
    tauto
  have dj : Disjoint (orient true (C.leftVars i) (C.rightVars i))
      (orient true (C.rightVars i) (C.leftVars i)) := by
    rw [Finset.disjoint_left]
    intro p hl hr
    exact Finset.disjoint_left.mp hd (mem_pick.mp (mem_between.mp hl).1).1
      (mem_pick.mp (mem_between.mp hr).1).1
  rw [eq, Finset.card_union_of_disjoint dj]

def seen (C : AndCountCircuit 42) (i : Gate C) : Finset (V × V) :=
  missedPairs.filter fun p => p.1 ∈ gateVars C i ∨ p.2 ∈ gateVars C i

lemma seen_sum {C : AndCountCircuit 42}
    (joint : ∀ p l : V, p.val < 21 → 21 ≤ l.val → ¬plane.Adj p l →
      {i : Gate C | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 5) :
    (∑ i, (seen C i).card) ≤ 1680 := by
  classical
  have count (i : Gate C) : (seen C i).card = ∑ p ∈ missedPairs, if p.1 ∈ gateVars C i ∨ p.2 ∈ gateVars C i then 1 else 0 := by
    rw [← Finset.sum_filter]; simp [seen]
  simp_rw [count]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _p ∈ missedPairs, (5 : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_filter]; simp only [Finset.sum_const, smul_eq_mul, mul_one]
      have pp := mem_missed.mp hp
      have h₁ : p.1.val < 21 := by simpa [mem_part, color] using pp.1
      have h₂ : 21 ≤ p.2.val := by simpa [mem_part, color] using pp.2.1
      have h := joint p.1 p.2 h₁ h₂ pp.2.2
      rw [card_set] at h
      simpa only [gateVars, Finset.mem_union, or_assoc] using h
    _ = 1680 := by simp [missedPairs_card]

lemma recall_count (S : Finset V) (b : Bool) :
    (missedPairs.filter fun p => (if b then p.1 else p.2) ∈ S).card =
      16 * (pick S b).card := by
  classical
  let f : V × V → V := if b then Prod.fst else Prod.snd
  have hmap (p : V × V) (hp : p ∈ missedPairs) : color (f p) = b := by
    have h := mem_missed.mp hp
    cases b
    · exact mem_part.mp h.2.1
    · exact mem_part.mp h.1
  have eq : (missedPairs.filter fun p => (if b then p.1 else p.2) ∈ S) =
      missedPairs.filter fun p => f p ∈ S := by cases b <;> rfl
  rw [eq, Finset.card_eq_sum_card_fiberwise (f := f) (t := pick S b) (by
    intro p hp
    obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hp
    exact mem_pick.mpr ⟨hs, hmap p hm⟩)]
  have each (v : V) (hv : v ∈ pick S b) :
      ((missedPairs.filter fun p => f p ∈ S).filter fun p => f p = v).card = 16 := by
    have eq' : ((missedPairs.filter fun p => f p ∈ S).filter fun p => f p = v) =
      (missedPairs.filter fun p => f p = v) := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,h.2.symm ▸ (mem_pick.mp hv).1⟩,h.2⟩⟩
    rw [eq']
    have col := (mem_pick.mp hv).2
    cases b
    · exact missedPairs_snd v col
    · exact missedPairs_fst v col
  rw [Finset.sum_congr rfl each]
  simp [Nat.mul_comm]

-- Inclusion-exclusion counts nonedges touching either operand. The covered edges
-- fit in the same point-line product as the nonedges touching both endpoints.
lemma seen_cost {C : AndCountCircuit 42} {i : Gate C} :
    let S := gateVars C i
    16*S.card + (covered C i).card ≤
      (seen C i).card + (pick S true).card*(pick S false).card := by
  classical
  intro S
  let A := missedPairs.filter fun p => p.1 ∈ S
  let B := missedPairs.filter fun p => p.2 ∈ S
  have eUnion : A ∪ B = seen C i := by
    ext p
    simp only [A, B, seen, S, Finset.mem_union, Finset.mem_filter]
    tauto
  have hA : A.card = 16*(pick S true).card := recall_count S true
  have hB : B.card = 16*(pick S false).card := recall_count S false
  have h := Finset.card_union_add_card_inter A B
  rw [eUnion, hA,hB, ← Nat.mul_add, pick_card] at h
  have dj : Disjoint (A ∩ B) (covered C i) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have hn := (mem_missed.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).1).2.2
    exact hn (mem_between.mp (mem_covered.mp hp').1).2.2
  have sub : (A ∩ B) ∪ covered C i ⊆ pick S true ×ˢ pick S false := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hp
      obtain ⟨hm, h₁⟩ := Finset.mem_filter.mp ha
      have h₂ := (Finset.mem_filter.mp hb).2
      obtain ⟨hc, hd, _⟩ := mem_missed.mp hm
      exact Finset.mem_product.mpr ⟨mem_pick.mpr ⟨h₁, mem_part.mp hc⟩,
        mem_pick.mpr ⟨h₂, mem_part.mp hd⟩⟩
    · obtain ⟨he, ha⟩ := mem_covered.mp hp
      obtain ⟨hc, hd, _⟩ := mem_between.mp he
      refine Finset.mem_product.mpr ⟨mem_pick.mpr ⟨?_, mem_part.mp hc⟩,
        mem_pick.mpr ⟨?_, mem_part.mp hd⟩⟩
      · exact Finset.mem_union.mpr (ha.imp And.left And.left)
      · exact Finset.mem_union.mpr (ha.symm.imp And.right And.right)
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dj, Finset.card_product] at bound
  omega


lemma pick_disjoint_union (S T : Finset V) (b : Bool) (hd : Disjoint S T) :
    (pick (S ∪ T) b).card = (pick S b).card + (pick T b).card := by
  have eq : pick (S ∪ T) b = pick S b ∪ pick T b := by
    ext v
    simp only [mem_pick, Finset.mem_union]
    tauto
  rw [eq, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr fun _ hv hw => Finset.disjoint_left.mp hd
    (mem_pick.mp hv).1 (mem_pick.mp hw).1

lemma pick_le (S : Finset V) (b : Bool) : (pick S b).card ≤ 21 := by
  rw [← part_card b]
  exact Finset.card_le_card fun _ hv => mem_part.mpr (mem_pick.mp hv).2

def Wide (l r : ℕ) : Prop :=
  (5 ≤ min l r ∧ 6 ≤ max l r) ∨ (4 ≤ min l r ∧ 14 ≤ max l r)

lemma width_certificate (a b c d e : ℕ) (hp : a+c ≤ 21) (hl : b+d ≤ 21)
    (narrow : ¬Wide (a+b) (c+d)) (he : e ≤ rectangleBound a d + rectangleBound c b) :
    let q := (if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
      (if c=1 then 1 else 0) + (if d=1 then 1 else 0)
    90*e+75*q+8*((a+c)*(b+d)) ≤ 128*(a+b+c+d) ∧
      (90*e+75*q+8*((a+c)*(b+d)) = 128*(a+b+c+d) → q = 0 ∨ q = 4) := by
  have s : a+b ≤ 5 ∨ c+d ≤ 5 := by
    by_contra! h
    apply narrow
    exact Or.inl ⟨le_min (by omega) (by omega), (by omega : 6 ≤ c+d).trans (le_max_right _ _)⟩
  have h : 90*(rectangleBound a d + rectangleBound c b)+
      75*((if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
        (if c=1 then 1 else 0) + (if d=1 then 1 else 0))+
      8*((a+c)*(b+d)) ≤ 128*(a+b+c+d) ∧
      (90*(rectangleBound a d + rectangleBound c b)+
        75*((if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
          (if c=1 then 1 else 0) + (if d=1 then 1 else 0))+
        8*((a+c)*(b+d)) = 128*(a+b+c+d) →
        ((if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
          (if c=1 then 1 else 0) + (if d=1 then 1 else 0)) = 0 ∨
        ((if a=1 then 1 else 0) + (if b=1 then 1 else 0) +
          (if c=1 then 1 else 0) + (if d=1 then 1 else 0)) = 4) := by
    rcases s with s | s
    · exact arithmetic_small ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ s hp hl narrow
    · have hn : ¬Wide (c+d) (a+b) := by simpa [Wide, min_comm, max_comm] using narrow
      have hh := arithmetic_small ⟨c, by omega⟩ ⟨d, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ s
        (Nat.add_comm a c ▸ hp) (Nat.add_comm b d ▸ hl) hn
      dsimp only at hh
      simpa only [add_left_comm, add_comm, add_assoc] using hh
  intro q
  change _ ≤ _ ∧ (_ = _ → _) at h
  refine ⟨by omega, fun heq => h.2 (by omega)⟩

lemma width_gate {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i))
    (hn : ¬Wide (C.leftVars i).card (C.rightVars i).card) :
    98*(covered C i).card + 75*isolation C i ≤ 8*(seen C i).card ∧
    (98*(covered C i).card + 75*isolation C i = 8*(seen C i).card →
      isolation C i = 0 ∨ isolation C i = 4) := by
  let L := C.leftVars i
  let R := C.rightVars i
  let a := (pick L true).card
  let b := (pick L false).card
  let c := (pick R true).card
  let d := (pick R false).card
  have hp := pick_disjoint_union L R true hd
  have hl := pick_disjoint_union L R false hd
  have auxp := pick_le (L ∪ R) true
  have auxl := pick_le (L ∪ R) false
  have hL : a+b = L.card := pick_card L
  have hR : c+d = R.card := pick_card R
  have hS : (gateVars C i).card = a+b+c+d := by
    change (L ∪ R).card = _
    rw [Finset.card_union_of_disjoint hd]
    change L.card+R.card = _
    omega
  have he : (covered C i).card ≤ rectangleBound a d + rectangleBound c b := by
    rw [covered_eq hd]
    exact Nat.add_le_add (between_bound _ _) (between_bound _ _)
  have cert := width_certificate a b c d (covered C i).card
    (by change _ = a+c at hp; omega) (by change _ = b+d at hl; omega)
    (by rw [hL,hR]; exact hn) he
  change 90*(covered C i).card + 75*isolation C i + 8*((a+c)*(b+d)) ≤ _ ∧
    (90*(covered C i).card + 75*isolation C i + 8*((a+c)*(b+d)) = _ → _) at cert
  have cost := seen_cost (C := C) (i := i)
  change 16*(gateVars C i).card + (covered C i).card ≤ (seen C i).card +
    (pick (L ∪ R) true).card * (pick (L ∪ R) false).card at cost
  change _ = a+c at hp
  change _ = b+d at hl
  rw [hS, hp, hl] at cost
  exact ⟨by omega, fun eq => cert.2 (by omega)⟩

-- All three counts must attain equality if every gate is narrow. Equality
-- makes each isolation count a multiple of four, although their sum is 42.
lemma wide_gate {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (cap : ∀ v, (positions C v).card ≤ 3)
    (joint : ∀ p l : V, p.val < 21 → 21 ≤ l.val → ¬plane.Adj p l →
      {i : Gate C | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 5) :
    ∃ i, Wide (C.leftVars i).card (C.rightVars i).card := by
  classical
  by_contra! no
  let lhs (i : Gate C) := 98*(covered C i).card + 75*isolation C i
  let rhs (i : Gate C) := 8*(seen C i).card
  have le (i : Gate C) : lhs i ≤ rhs i := (width_gate (hd i) (no i)).1
  have sums : (∑ i, lhs i) ≤ ∑ i, rhs i := Finset.sum_le_sum fun i _ => le i
  have he := cover_sum hc out hd
  have hq := isolation_sum hc out cap
  have hcost := seen_sum joint
  have sumL : (∑ i, lhs i) = 98*(∑ i, (covered C i).card)+75*(∑ i, isolation C i) := by
    simp [lhs, Finset.sum_add_distrib, Finset.mul_sum]
  have sumR : (∑ i, rhs i) = 8*(∑ i, (seen C i).card) := by simp [rhs, Finset.mul_sum]
  rw [sumL,sumR] at sums
  have exactQ : (∑ i, isolation C i) = 42 := by omega
  have exactSum : (∑ i, lhs i) = ∑ i, rhs i := by rw [sumL,sumR]; omega
  have kernel (i : Gate C) : isolation C i = 0 ∨ isolation C i = 4 := by
    apply (width_gate (hd i) (no i)).2
    change lhs i = rhs i
    by_contra! ne
    have lt := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => le i)
      ⟨i, Finset.mem_univ _, lt_of_le_of_ne (le i) ne⟩
    omega
  have four (i : Gate C) : isolation C i = 4 * (if isolation C i = 4 then 1 else 0) := by
    rcases kernel i with h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => four i), ← Finset.mul_sum] at exactQ
  omega



lemma avoid_companions {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    {v x y : V} (xv : x ≠ v) (yv : y ≠ v) (xy : ¬plane.Adj x y) :
    ∃ s ∈ positions C v, x ∉ raw C s ∧ y ∉ raw C s := by
  obtain ⟨w, e, no⟩ := avoids v {x,y} (Finset.card_le_two.trans (by decide))
    (by simp [xv.symm,yv.symm])
  have nx := no x (by simp)
  have ny := no y (by simp)
  have hi : Independent (({x,y} : Finset V) ∪ {w}) := by
    intro a ha b hb ab
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with (rfl | rfl) | rfl <;> rcases hb with (rfl | rfl) | rfl
    all_goals first
      | exact plane.irrefl ab
      | exact xy ab
      | exact xy ab.symm
      | exact nx ab
      | exact nx ab.symm
      | exact ny ab
      | exact ny ab.symm
  obtain ⟨s, hs, hn⟩ := separation hc out hi (by simp) e
  exact ⟨s,hs,fun h => hn ⟨x,h,by simp⟩,fun h => hn ⟨y,h,by simp⟩⟩

-- On a large operand there is room for a replacement nonadjacent to w.
-- Separation therefore has to find an operand at another gate.
lemma outside_avoid {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card) {v w : V} (wv : w ≠ v) :
    ∃ s ∈ positions C v, s.1 ≠ k ∧ w ∉ raw C s := by
  classical
  have choose_other : ∃ x : V, x ≠ v ∧ ¬plane.Adj x w ∧
      ∀ b : Bool, v ∈ raw C (k,b) → x ∈ raw C (k,b) := by
    by_cases hv : ∃ b : Bool, v ∈ raw C (k,b)
    · obtain ⟨b,hb⟩ := hv
      have small : (insert v (neighbors w)).card ≤ 6 :=
        (Finset.card_insert_le _ _).trans (by rw [degree])
      obtain ⟨x,hx,hn⟩ : ∃ x ∈ raw C (k,b), x ∉ insert v (neighbors w) := by
        by_contra! all
        have := Finset.card_le_card all
        have := big b
        omega
      refine ⟨x,fun eq => hn (by simp [eq]),fun e => hn
        (Finset.mem_insert_of_mem (mem_neighbors.mpr e.symm)),?_⟩
      intro d hv'
      have bd : b = d := by
        cases b <;> cases d <;> first | rfl |
          exact (Finset.disjoint_left.mp (hd k) hb hv').elim |
          exact (Finset.disjoint_left.mp (hd k) hv' hb).elim
      exact bd ▸ hx
    · exact ⟨w,wv,plane.loopless.irrefl w,fun b hb => (hv ⟨b,hb⟩).elim⟩
  obtain ⟨x,xv,xy,choose⟩ := choose_other
  obtain ⟨⟨i,b⟩,hs,nx,nw⟩ := avoid_companions hc out xv wv xy
  refine ⟨(i,b),hs,?_,nw⟩
  intro e
  change i = k at e
  subst i
  exact nx (choose b (mem_positions.mp hs))

def outsideSlots (C : AndCountCircuit 42) (k : Gate C) (v : V) :=
  (positions C v).filter fun s => s.1 ≠ k

lemma outside_nonempty {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card) (v : V) :
    (outsideSlots C k v).Nonempty := by
  obtain ⟨w,h⟩ := exists_ne v
  obtain ⟨s,hs,nk,_⟩ := outside_avoid hc out hd big h
  exact ⟨s,Finset.mem_filter.mpr ⟨hs,nk⟩⟩

lemma outside_single {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card) {v : V} {s : Slot C}
    (hs : s ∈ outsideSlots C k v) (cap : (outsideSlots C k v).card ≤ 1) :
    raw C s = {v} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_positions.mp (Finset.mem_filter.mp hs).1,?_⟩
  intro w hw
  by_contra ne
  obtain ⟨t,ht,nk,nw⟩ := outside_avoid hc out hd big ne
  exact nw ((Finset.card_le_one.mp cap _ hs _ (Finset.mem_filter.mpr ⟨ht,nk⟩)) ▸ hw)

def IsBad (C : AndCountCircuit 42) (i : Gate C) : Prop :=
  ∃ v ∈ C.leftVars i, ∃ w ∈ C.rightVars i, ¬plane.Adj v w

def Clashes (C : AndCountCircuit 42) (i : Gate C) : Prop :=
  ∃ v ∈ C.leftVars i, ∃ w ∈ C.rightVars i, color v = color w

noncomputable def capacity (C : AndCountCircuit 42) (i : Gate C) : ℕ := by
  classical exact if IsBad C i then 4 else 2

lemma color_filter_of_const (S : Finset V) {b : Bool} (h : ∀ v ∈ S, color v = b) :
    pick S b = S ∧ pick S (!b) = ∅ := by
  constructor
  · ext v
    exact ⟨fun hv => (mem_pick.mp hv).1, fun hv => mem_pick.mpr ⟨hv,h v hv⟩⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have eq := (h v (mem_pick.mp hv).1).symm.trans (mem_pick.mp hv).2
    cases b <;> contradiction

lemma clean_colors {S T : Finset V} (h : ∀ v ∈ S, ∀ w ∈ T, plane.Adj v w)
    (hs : S.Nonempty) (ht : T.Nonempty) :
    ∃ b : Bool, (∀ v ∈ S, color v = b) ∧ (∀ w ∈ T, color w = !b) := by
  obtain ⟨s,hs⟩ := hs
  obtain ⟨t,ht⟩ := ht
  refine ⟨color s,?_,fun w hw => Bool.eq_not_of_ne (cross (h s hs w hw)).symm⟩
  intro v hv
  exact (Bool.eq_not_of_ne (cross (h v hv t ht))).trans
    (Bool.eq_not_of_ne (cross (h s hs t ht))).symm

lemma clean_small {S T : Finset V} (h : ∀ v ∈ S, ∀ w ∈ T, plane.Adj v w) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra! hh
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp hh.1
  have sub : T ⊆ neighbors u ∩ neighbors v := by
    intro w hw
    exact Finset.mem_inter.mpr ⟨mem_neighbors.mpr (h u hu w hw),mem_neighbors.mpr (h v hv w hw)⟩
  have := (Finset.card_le_card sub).trans (intersections u v ne)
  omega

lemma covered_side_bound {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i)) :
    (covered C i).card ≤ 5*(C.leftVars i).card ∧
    (covered C i).card ≤ 5*(C.rightVars i).card := by
  rw [covered_eq hd]
  unfold orient
  simp only [Bool.not_true]
  let A := pick (C.leftVars i) true
  let B := pick (C.leftVars i) false
  let D := pick (C.rightVars i) true
  let E := pick (C.rightVars i) false
  change (between A E).card + (between D B).card ≤ _ ∧
    (between A E).card + (between D B).card ≤ _
  have h1 := (between_bound_aux A E).1
  have h2 := (between_bound_aux D B).1
  have h3 := (between_bound_aux E A).1
  have h4 := (between_bound_aux B D).1
  rw [← between_symm A E] at h3
  rw [← between_symm D B] at h4
  have hl : A.card+B.card = _ := pick_card (C.leftVars i)
  have hr : D.card+E.card = _ := pick_card (C.rightVars i)
  omega

lemma isolation_many {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i)) :
    (3 ≤ isolation C i → (covered C i).card ≤ 6) ∧
    (isolation C i = 4 → (covered C i).card ≤ 2) ∧
    isolation C i ≤ 4 := by
  rw [covered_eq hd]
  let a := (pick (C.leftVars i) true).card
  let b := (pick (C.leftVars i) false).card
  let c := (pick (C.rightVars i) true).card
  let d := (pick (C.rightVars i) false).card
  let E := (orient true (C.leftVars i) (C.rightVars i)).card
  let F := (orient true (C.rightVars i) (C.leftVars i)).card
  have ne := between_bound (pick (C.leftVars i) true) (pick (C.rightVars i) false)
  have nf := between_bound (pick (C.rightVars i) true) (pick (C.leftVars i) false)
  change E ≤ rectangleBound a d at ne
  change F ≤ rectangleBound c b at nf
  simp only [rectangleBound, le_min_iff] at ne nf
  change (3 ≤ ((if a=1 then 1 else 0)+(if b=1 then 1 else 0)+(if c=1 then 1 else 0)+
    (if d=1 then 1 else 0)) → E+F ≤ 6) ∧
    (((if a=1 then 1 else 0)+(if b=1 then 1 else 0)+(if c=1 then 1 else 0)+
    (if d=1 then 1 else 0)) = 4 → E+F ≤ 2) ∧
    ((if a=1 then 1 else 0)+(if b=1 then 1 else 0)+(if c=1 then 1 else 0)+
    (if d=1 then 1 else 0)) ≤ 4
  by_cases ha : a=1 <;> by_cases hb : b=1 <;> by_cases hc : c=1 <;> by_cases hdd : d=1 <;>
    simp only [ha,hb,hc,hdd,ite_true,ite_false,Nat.one_mul,Nat.mul_one] at * <;> omega

lemma clean_stats {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i)) (clean : ¬IsBad C i) :
    isolation C i ≤ 2 ∧ (covered C i).card ≤ 5 ∧
    (isolation C i = 2 → (gateVars C i).card = 2 ∧ (covered C i).card ≤ 1) ∧
    ((C.leftVars i).card = 1 → (C.rightVars i).card = 1 → isolation C i = 2) ∧
    ((C.leftVars i).card ≤ 1 ∨ (C.rightVars i).card ≤ 1) := by
  classical
  let L := C.leftVars i
  let R := C.rightVars i
  have good (v) (hv : v ∈ L) (w) (hw : w ∈ R) : plane.Adj v w := by
    by_contra no
    exact clean ⟨v,hv,w,hw,no⟩
  have hs := clean_small good
  have bl : (covered C i).card ≤ 5*L.card ∧ (covered C i).card ≤ 5*R.card := covered_side_bound hd
  have e := covered_eq hd
  change (covered C i).card = (orient true L R).card + (orient true R L).card at e
  have stat (S : Finset V) : isolated S true + isolated S false ≤ 2 ∧
      (isolated S true + isolated S false = 2 → S.card = 2) := by
    have h := pick_card S
    unfold isolated
    split <;> split <;> omega
  have eq : (gateVars C i).card = L.card + R.card := Finset.card_union_of_disjoint hd
  have defQ : isolation C i = (isolated L true + isolated L false) +
      (isolated R true + isolated R false) := by simp [isolation, L, R, Nat.add_assoc]
  have sl (S : Finset V) (b : Bool) (h : ∀ v ∈ S, color v = b) :
      isolated S true + isolated S false = if S.card = 1 then 1 else 0 := by
    obtain ⟨x,y⟩ := color_filter_of_const S h
    cases b <;> simp_all [isolated]
  have le5 : (covered C i).card ≤ 5 := by
    change L.card ≤ 1 ∨ R.card ≤ 1 at hs
    change (covered C i).card ≤ 5*L.card ∧ (covered C i).card ≤ 5*R.card at bl
    omega
  refine ⟨?_,le5,?_,?_,hs⟩
  · by_cases le : L = ∅
    · simpa [defQ, le, isolated, pick] using (stat R).1
    by_cases re : R = ∅
    · simpa [defQ, re, isolated, pick] using (stat L).1
    obtain ⟨col,cl,cr⟩ := clean_colors good (Finset.nonempty_iff_ne_empty.mpr le)
      (Finset.nonempty_iff_ne_empty.mpr re)
    rw [defQ, sl L col cl, sl R (!col) cr]
    split <;> split <;> omega
  · intro q
    by_cases le : L = ∅
    · have qr : isolated R true + isolated R false = 2 := by simpa [defQ, le, isolated, pick] using q
      rw [eq, le, Finset.card_empty, Nat.zero_add]
      have zero : (covered C i).card ≤ 0 := by simpa only [le, Finset.card_empty, Nat.mul_zero] using bl.1
      exact ⟨(stat R).2 qr, zero.trans (by decide)⟩
    by_cases re : R = ∅
    · have ql : isolated L true + isolated L false = 2 := by simpa [defQ, re, isolated, pick] using q
      rw [eq, re, Finset.card_empty, Nat.add_zero]
      have zero : (covered C i).card ≤ 0 := by simpa only [re, Finset.card_empty, Nat.mul_zero] using bl.2
      exact ⟨(stat L).2 ql, zero.trans (by decide)⟩
    obtain ⟨col,cl,cr⟩ := clean_colors good (Finset.nonempty_iff_ne_empty.mpr le)
      (Finset.nonempty_iff_ne_empty.mpr re)
    rw [defQ, sl L col cl, sl R (!col) cr] at q
    have cardL : L.card = 1 := by
      by_contra hn
      simp only [ite_eq_right hn,Nat.zero_add] at q
      split at q <;> omega
    have cardR : R.card = 1 := by
      by_contra hn
      simp only [ite_eq_right hn,Nat.add_zero] at q
      split at q <;> omega
    refine ⟨eq.trans (by rw [cardL,cardR]), ?_⟩
    obtain ⟨x,y⟩ := color_filter_of_const L cl
    obtain ⟨z,t⟩ := color_filter_of_const R cr
    have b1 : (between (pick L true) (pick R false)).card ≤
        (pick L true).card * (pick R false).card :=
      (between_bound _ _).trans (min_le_left _ _)
    have b2 : (between (pick R true) (pick L false)).card ≤
        (pick R true).card * (pick L false).card :=
      (between_bound _ _).trans (min_le_left _ _)
    rw [e]
    change (between (pick L true) (pick R false)).card +
      (between (pick R true) (pick L false)).card ≤ 1
    cases col
    · change pick L true = ∅ at y
      change pick R true = R at z
      change pick R false = ∅ at t
      rw [y,t,Finset.card_empty,Nat.zero_mul] at b1
      rw [z,x,cardL,cardR] at b2
      rw [y,t,z,x]
      have em : between ∅ ∅ = ∅ := by simp [between]
      rw [em,Finset.card_empty,Nat.zero_add]
      exact b2
    · change pick L false = ∅ at y
      change pick R false = R at z
      change pick R true = ∅ at t
      rw [t,y,Finset.card_empty,Nat.zero_mul] at b2
      rw [x,z,cardL,cardR] at b1
      rw [x,z,t,y]
      have em : between ∅ ∅ = ∅ := by simp [between]
      rw [em,Finset.card_empty,Nat.add_zero]
      exact b1
  · intro l r
    change L.card = 1 at l
    change R.card = 1 at r
    obtain ⟨col,cl,cr⟩ := clean_colors good (Finset.card_pos.mp (by omega : 0 < L.card))
      (Finset.card_pos.mp (by omega : 0 < R.card))
    simp [defQ, sl L col cl, sl R (!col) cr, l, r]

lemma capacity_stats {C : AndCountCircuit 42} {i : Gate C}
    (hd : Disjoint (C.leftVars i) (C.rightVars i)) :
    isolation C i ≤ capacity C i ∧
    (isolation C i = capacity C i → (gateVars C i).card = capacity C i) := by
  classical
  by_cases bad : IsBad C i
  · have hs := isolation_many hd
    simp only [capacity, ite_eq_left, bad]
    refine ⟨hs.2.2, fun q => ?_⟩
    have cl := pick_card (C.leftVars i)
    have cr := pick_card (C.rightVars i)
    rw [gateVars, Finset.card_union_of_disjoint hd]
    unfold isolation isolated at q
    split at q <;> split at q <;> split at q <;> split at q <;> omega
  · have hs := clean_stats hd bad
    exact ⟨by simpa [capacity,bad] using hs.1,
      fun h => by simpa [capacity,bad] using (hs.2.2.1 (by simpa [capacity,bad] using h)).1⟩


lemma outside_card_gate {C : AndCountCircuit 42} {k : Gate C} {v : V}
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (D : Finset (Gate C))
    (sub : ∀ s ∈ outsideSlots C k v, s.1 ∈ D) :
    (outsideSlots C k v).card ≤ D.card := by
  apply Finset.card_le_card_of_injOn Prod.fst (fun s hs => sub s hs)
  rintro ⟨i,b⟩ hi ⟨j,d⟩ hj e
  change i = j at e
  subst j
  have vi := mem_positions.mp (Finset.mem_filter.mp hi).1
  have vj := mem_positions.mp (Finset.mem_filter.mp hj).1
  cases b <;> cases d <;> first | rfl |
    exact (Finset.disjoint_left.mp (hd i) vi vj).elim |
    exact (Finset.disjoint_left.mp (hd i) vj vi).elim

def code (C : AndCountCircuit 42) (i : Gate C) (v : V) : Fin 3 :=
  if v ∈ C.leftVars i then 1 else if v ∈ C.rightVars i then 2 else 0

def extendsCode (x y : Fin 3 × Fin 3) : Bool :=
  decide ((x.1 = 0 ∨ x.1 = y.1) ∧ (x.2 = 0 ∨ x.2 = y.2))

-- These four chains partition the two-gate signatures under extension.
def chain (x : Fin 3 × Fin 3) : Fin 4 :=
  if x.2 = 0 then (if x.1 = 2 then 2 else 0)
  else if x.2 = 1 then (if x.1 = 1 then 0 else 1)
  else (if x.1 = 2 then 2 else 3)

lemma same_chain : ∀ x y : Fin 3 × Fin 3,
    chain x = chain y → extendsCode x y = true ∨ extendsCode y x = true := by
  decide +kernel

lemma codes_bound (s : Finset (Fin 3 × Fin 3))
    (anti : ∀ x ∈ s, ∀ y ∈ s, extendsCode x y = true → x = y) : s.card ≤ 4 := by
  have inj : Set.InjOn chain s := by
    intro x hx y hy e
    rcases same_chain x y e with a | a
    · exact anti x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) a
    · exact (anti y (Finset.mem_coe.mp hy) x (Finset.mem_coe.mp hx) a).symm
  rw [← Finset.card_image_of_injOn inj]
  simpa using Finset.card_le_univ (s.image chain)

lemma code_reads {C : AndCountCircuit 42} {i : Gate C} {b : Bool} {v w : V}
    (hd : Disjoint (C.leftVars i) (C.rightVars i))
    (hv : v ∈ raw C (i,b)) (he : code C i v = 0 ∨ code C i v = code C i w) :
    w ∈ raw C (i,b) := by
  cases b
  · have cv : code C i v = 1 := by simp [code, show v ∈ C.leftVars i from hv]
    change w ∈ C.leftVars i
    by_contra nw
    have cw := he.resolve_left (by rw [cv]; decide)
    rw [cv] at cw
    change 1 = (if w ∈ C.leftVars i then 1 else if w ∈ C.rightVars i then 2 else 0) at cw
    rw [ite_eq_right nw] at cw
    split at cw <;> contradiction
  · have hv' : v ∈ C.rightVars i := hv
    have hl : v ∉ C.leftVars i := fun h => Finset.disjoint_left.mp hd h hv'
    have cv : code C i v = 2 := by simp [code, hv', hl]
    have cw := he.resolve_left (by rw [cv]; decide)
    rw [cv] at cw
    change w ∈ C.rightVars i
    by_contra nw
    unfold code at cw
    rw [ite_eq_right nw] at cw
    split at cw <;> contradiction

lemma remaining_bound {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card)
    (M : Finset V) (D : Finset (Gate C))
    (sub : ∀ v ∈ M, ∀ s ∈ outsideSlots C k v, s.1 ∈ D)
    (i j : Gate C) (cover : D ⊆ {i,j}) : M.card ≤ 4 := by
  let f (v : V) := (code C i v, code C j v)
  have separates (v : V) (hv : v ∈ M) (w : V) (ne : w ≠ v) :
      extendsCode (f v) (f w) ≠ true := by
    intro he
    have ex := of_decide_eq_true he
    obtain ⟨⟨g,b⟩, hs, nk, nw⟩ := outside_avoid hc out hd big ne
    have hOut : (g,b) ∈ outsideSlots C k v := Finset.mem_filter.mpr ⟨hs,nk⟩
    have hm := cover (sub v hv (g,b) hOut)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    change (code C i v = 0 ∨ code C i v = code C i w) ∧
      (code C j v = 0 ∨ code C j v = code C j w) at ex
    rcases hm with e | e
    · change g = i at e
      subst g
      exact nw (code_reads (hd i) (mem_positions.mp hs) ex.1)
    · change g = j at e
      subst g
      exact nw (code_reads (hd j) (mem_positions.mp hs) ex.2)
  have inj : Set.InjOn f M := by
    intro v hv w hw eq
    by_contra ne
    exact separates v (Finset.mem_coe.mp hv) w (Ne.symm ne) (by simp [extendsCode, eq])
  rw [← Finset.card_image_of_injOn inj]
  apply codes_bound
  intro x hx y hy he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hy
  by_contra ne
  exact separates v hv w (fun e => ne (e ▸ rfl)) he

lemma clean_remaining_bound {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card)
    (M : Finset V) (D : Finset (Gate C))
    (sub : ∀ v ∈ M, ∀ s ∈ outsideSlots C k v, s.1 ∈ D) (cap : D.card ≤ 2)
    (cn : ∀ i ∈ D, ¬IsBad C i ∧ isolation C i ≠ capacity C i) :
    M.card ≤ D.card + 1 ∧ (D.card ≤ 1 → M.card ≤ D.card) := by
  classical
  obtain ⟨side, hside⟩ : ∃ b : Gate C → Bool, ∀ i ∈ D,
      (raw C (i,b i)).card ≤ 1 ∧ (raw C (i,!b i)).card ≠ 1 := by
    have h (i : Gate C) (hi : i ∈ D) : ∃ b : Bool,
        (raw C (i,b)).card ≤ 1 ∧ (raw C (i,!b)).card ≠ 1 := by
      have st := clean_stats (hd i) (cn i hi).1
      have q : isolation C i ≠ 2 := by simpa [capacity, (cn i hi).1] using (cn i hi).2
      have no : ¬((C.leftVars i).card = 1 ∧ (C.rightVars i).card = 1) :=
        fun a => q (st.2.2.2.1 a.1 a.2)
      by_cases l : (C.leftVars i).card = 1
      · exact ⟨false, by exact ⟨Nat.le_of_eq l,fun r => no ⟨l,r⟩⟩⟩
      by_cases r : (C.rightVars i).card = 1
      · exact ⟨true, by exact ⟨Nat.le_of_eq r,l⟩⟩
      rcases st.2.2.2.2 with h | h
      · exact ⟨false, h, r⟩
      · exact ⟨true, h, l⟩
    choose b hb using h
    exact ⟨fun i => if hi : i ∈ D then b i hi else false, by
      intro i hi; simpa only [dite_eq_left hi] using hb i hi⟩
  let X := D.biUnion (fun i => raw C (i,side i))
  let Y := M \ X
  have xc : X.card ≤ D.card := by
    refine Finset.card_biUnion_le.trans ?_
    simpa using Finset.sum_le_sum (s := D) (g := fun _ => (1 : ℕ))
      (fun i hi => (hside i hi).1)
  have noX (v : V) (hv : v ∈ Y) (s : Slot C) (hs : s ∈ outsideSlots C k v) :
      s.1 ∈ D ∧ s.2 = !side s.1 := by
    obtain ⟨hvM,hvX⟩ := Finset.mem_sdiff.mp hv
    have hg := sub v hvM s hs
    refine ⟨hg,Bool.eq_not_of_ne ?_⟩
    intro eq
    apply hvX
    have read := mem_positions.mp (Finset.mem_filter.mp hs).1
    rcases s with ⟨i,b⟩
    change b = side i at eq
    exact Finset.mem_biUnion.mpr ⟨i,hg,eq ▸ read⟩
  have twice (v : V) (hv : v ∈ Y) : 2 ≤ (outsideSlots C k v).card := by
    obtain ⟨s,hs⟩ := outside_nonempty hc out hd big v
    by_contra! small
    have single := outside_single hc out hd big hs (by omega)
    obtain ⟨hi,hside'⟩ := noX v hv s hs
    have card := congrArg Finset.card single
    rw [Finset.card_singleton] at card
    rcases s with ⟨i,b⟩
    change b = !side i at hside'
    subst b
    exact (hside i hi).2 card
  have all (v : V) (hv : v ∈ Y) (i : Gate C) (hi : i ∈ D) :
      v ∈ raw C (i,!side i) := by
    by_contra nv
    have sub' (s : Slot C) (hs : s ∈ outsideSlots C k v) : s.1 ∈ D.erase i := by
      obtain ⟨hj,hb⟩ := noX v hv s hs
      refine Finset.mem_erase.mpr ⟨?_,hj⟩
      intro eq
      rcases s with ⟨j,b⟩
      change j = i at eq
      subst j
      change b = !side i at hb
      subst b
      exact nv (mem_positions.mp (Finset.mem_filter.mp hs).1)
    have h := outside_card_gate hd (D.erase i) sub'
    rw [Finset.card_erase_of_mem hi] at h
    have := twice v hv
    omega
  have yc : Y.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro v hv w hw
    by_contra ne
    obtain ⟨s,hs,nk,nw⟩ := outside_avoid hc out hd big (Ne.symm ne)
    obtain ⟨hi,hb⟩ := noX v hv s (Finset.mem_filter.mpr ⟨hs,nk⟩)
    rcases s with ⟨i,b⟩
    change b = !side i at hb
    subst b
    exact nw (all w hw i hi)
  have eq : M ⊆ X ∪ Y := by
    intro v hv
    by_cases hx : v ∈ X
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,hx⟩)
  have bound := (Finset.card_le_card eq).trans (Finset.card_union_le X Y)
  refine ⟨by omega,fun small => ?_⟩
  have empty : Y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have h := outside_card_gate hd D (fun s hs => (noX v hv s hs).1)
    have := twice v hv
    omega
  rw [empty,Finset.card_empty] at bound
  omega


lemma outside_count (C : AndCountCircuit 42) (k : Gate C)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (∑ v, (outsideSlots C k v).card) = ∑ i ∈ Finset.univ.erase k, (gateVars C i).card := by
  classical
  let G := (Finset.univ.erase k) ×ˢ (Finset.univ : Finset Bool)
  have eq (v : V) : (outsideSlots C k v).card = ∑ s ∈ G, if v ∈ raw C s then 1 else 0 := by
    have e : outsideSlots C k v = G.filter (fun s => v ∈ raw C s) := by
      ext s
      simp [outsideSlots, G, mem_positions, and_comm]
    rw [e, ← Finset.sum_filter]
    simp
  simp_rw [eq]
  rw [Finset.sum_comm]
  have inner (s : Slot C) : (∑ v : V, if v ∈ raw C s then 1 else 0) = (raw C s).card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp
  simp_rw [inner]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  exact (Nat.add_comm _ _).trans (Finset.card_union_of_disjoint (hd i)).symm

lemma outside_too_many {C : AndCountCircuit 42}
    (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (size : C.size = 19) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card) :
    42 < ∑ i ∈ Finset.univ.erase k, (gateVars C i).card := by
  rw [← outside_count C k hd]
  by_contra! upper
  have pos (v : V) : 1 ≤ (outsideSlots C k v).card :=
    Finset.card_pos.mpr (outside_nonempty hc out hd big v)
  have cap (v : V) : (outsideSlots C k v).card ≤ 1 := by
    by_contra! lt
    have h := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
      (fun a _ => pos a) ⟨v,Finset.mem_univ _,lt⟩
    simp at h
    exact (Nat.not_lt_of_ge upper) h
  have single (v : V) : ∃ s : Slot C, raw C s = {v} := by
    obtain ⟨s,hs⟩ := outside_nonempty hc out hd big v
    exact ⟨s,outside_single hc out hd big hs (cap v)⟩
  choose f hf using single
  have inj : Function.Injective f := by
    intro v w e
    have h := hf v
    rw [e,hf w] at h
    simpa using h.symm
  have := Fintype.card_le_of_injective f inj
  simp [Fintype.card_prod,size] at this

lemma one_remaining_bound {C : AndCountCircuit 42}
    (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {k : Gate C}
    (big : ∀ b : Bool, 7 ≤ (raw C (k,b)).card) (M : Finset V) (i : Gate C)
    (sub : ∀ v ∈ M, ∀ s ∈ outsideSlots C k v, s.1 = i) : M.card ≤ 2 := by
  have h (v : V) (hv : v ∈ M) : ∃ b : Bool, raw C (i,b) = {v} := by
    have cap := outside_card_gate hd ({i} : Finset (Gate C))
      (fun s hs => Finset.mem_singleton.mpr (sub v hv s hs))
    obtain ⟨⟨j,b⟩,hs⟩ := outside_nonempty hc out hd big v
    have eq := sub v hv (j,b) hs
    change j = i at eq
    subst j
    exact ⟨b,outside_single hc out hd big hs (by simpa using cap)⟩
  classical
  choose f hf using h
  let g (v : V) := if hv : v ∈ M then f v hv else false
  have inj : Set.InjOn g M := by
    intro v hv w hw e
    have ev : raw C (i,g v) = {v} := by simpa only [g, dite_eq_left (Finset.mem_coe.mp hv)] using hf v (Finset.mem_coe.mp hv)
    have ew : raw C (i,g w) = {w} := by simpa only [g, dite_eq_left (Finset.mem_coe.mp hw)] using hf w (Finset.mem_coe.mp hw)
    rw [e,ew] at ev
    simpa using ev.symm
  have le := Finset.card_image_of_injOn inj
  rw [← le]
  simpa using Finset.card_le_univ (M.image g)

-- Four bad gates leave only four unused isolation places. A gate covering
-- more than 30 edges consumes at least two of them. Vertices missing from
-- the full-capacity gates must be distinguished using at most two other gates.
lemma many_bad {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (size : C.size = 19) (reads : ∀ v, (positions C v).card ≤ 3)
    (four : 4 ≤ {i : Gate C | Clashes C i}.ncard) :
    5 ≤ {i : Gate C | IsBad C i}.ncard := by
  classical
  let B := Finset.univ.filter (IsBad C)
  have hB : {i : Gate C | IsBad C i}.ncard = B.card := card_set (IsBad C)
  have fourB : 4 ≤ B.card := by
    rw [card_set] at four
    apply four.trans (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨v,hv,w,hw,e⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨v,hv,w,hw,fun he => cross he e⟩⟩
  by_contra! few
  have bc : B.card = 4 := by omega
  let deficit (i : Gate C) := capacity C i - isolation C i
  have qcap (i : Gate C) := (capacity_stats (hd i)).1
  have capSum : (∑ i, capacity C i) = 46 := by
    have eq (i : Gate C) : capacity C i = 2 + if IsBad C i then 2 else 0 := by
      by_cases hh : IsBad C i <;> simp [capacity,hh]
    simp_rw [eq, Finset.sum_add_distrib, ← Finset.sum_filter]
    have u : (Finset.univ : Finset (Gate C)).card = 19 := by simp [size]
    simp only [Finset.sum_const, smul_eq_mul, u]
    change 19*2+B.card*2 = 46
    omega
  have dsum : (∑ i, deficit i) ≤ 4 := by
    have eq (i : Gate C) : isolation C i + deficit i = capacity C i := by
      have h := qcap i
      dsimp [deficit]
      omega
    have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => eq i)
    rw [Finset.sum_add_distrib, capSum] at h
    have hq := isolation_sum hc out reads
    omega
  have cover := cover_sum hc out hd
  obtain ⟨k,kbad,large⟩ : ∃ i, IsBad C i ∧ 30 < (covered C i).card := by
    by_contra! small
    have point (i : Gate C) : (covered C i).card ≤
        1 + (if IsBad C i then 1 else 0) + 14*deficit i := by
      by_cases bad : IsBad C i
      · have e := small i bad
        have h := isolation_many (hd i)
        simp only [deficit,capacity,bad,ite_true]
        by_cases z : isolation C i = 4
        · have := h.2.1 z
          omega
        by_cases t : isolation C i = 3
        · have := h.1 (by omega)
          omega
        omega
      · have h := clean_stats (hd i) bad
        simp only [deficit,capacity,bad,ite_false]
        by_cases z : isolation C i = 2
        · have := (h.2.2.1 z).2
          omega
        omega
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => point i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_filter] at h
    have u : (Finset.univ : Finset (Gate C)).card = 19 := by simp [size]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, u] at h
    change (∑ i, (covered C i).card) ≤ 19+B.card+14*(∑ i, deficit i) at h
    omega
  have big (b : Bool) : 7 ≤ (raw C (k,b)).card := by
    have h := covered_side_bound (hd k)
    cases b <;> simp only [raw, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have kCap : capacity C k = 4 := by simp [capacity,kbad]
  have kDef : 2 ≤ deficit k := by
    have h := (isolation_many (hd k)).1
    rw [show deficit k = 4 - isolation C k from congrArg (fun n => n - isolation C k) kCap]
    omega
  let S := Finset.univ.erase k
  let D := S.filter (fun i => isolation C i ≠ capacity C i)
  let I := S.filter (fun i => isolation C i = capacity C i)
  have split_sum (f : Gate C → ℕ) :
      (∑ i ∈ D, f i) + (∑ i ∈ I, f i) + f k = ∑ i, f i := by
    have eq : D ∪ I = S := by
      ext i
      simp only [D,I,Finset.mem_filter,Finset.mem_union]
      tauto
    have dj : Disjoint D I := by
      apply Finset.disjoint_left.mpr
      intro i h₁ h₂
      exact (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
    rw [← Finset.sum_union dj, eq, Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have dpos (i : Gate C) (hi : i ∈ D) : 1 ≤ deficit i := by
    have h := qcap i
    have n := (Finset.mem_filter.mp hi).2
    dsimp [deficit]
    omega
  have dcap : D.card ≤ 2 := by
    have hh := split_sum deficit
    have h : D.card ≤ ∑ i ∈ D, deficit i := by
      simpa using Finset.sum_le_sum (s := D) (f := fun _ => (1 : ℕ)) dpos
    omega
  have capIdeal : (∑ i ∈ D, capacity C i) + (∑ i ∈ I, capacity C i) = 42 := by
    have hh := split_sum (capacity C)
    omega
  have rawIdeal : (∑ i ∈ I, (gateVars C i).card) = ∑ i ∈ I, capacity C i :=
    Finset.sum_congr rfl fun i hi => (capacity_stats (hd i)).2 (Finset.mem_filter.mp hi).2
  have dNon : D.Nonempty := by
    by_contra! no
    have eq : I = S := by
      ext i
      have e : D ∪ I = S := by
        ext u
        simp only [D,I,Finset.mem_filter,Finset.mem_union]
        tauto
      rw [← e, no, Finset.empty_union]
    have h := outside_too_many hc out hd size big
    change 42 < ∑ i ∈ S, (gateVars C i).card at h
    rw [← eq,rawIdeal] at h
    omega
  let Y := I.biUnion (gateVars C)
  let M : Finset V := Finset.univ \ Y
  have lower : (∑ i ∈ D, capacity C i) ≤ M.card := by
    have h := Finset.card_biUnion_le (s := I) (t := gateVars C)
    change Y.card ≤ _ at h
    have t : M.card = 42-Y.card := by simp [M, Finset.card_sdiff_of_subset (Finset.subset_univ Y)]
    rw [rawIdeal] at h
    omega
  have sub (v : V) (hv : v ∈ M) (s : Slot C) (hs : s ∈ outsideSlots C k v) : s.1 ∈ D := by
    obtain ⟨read,nk⟩ := Finset.mem_filter.mp hs
    have notY := (Finset.mem_sdiff.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨nk,Finset.mem_univ _⟩,fun e => ?_⟩
    apply notY
    have h := mem_positions.mp read
    rcases s with ⟨i,b⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨nk,Finset.mem_univ _⟩,e⟩, by
        cases b
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h⟩
  have cap2 (i : Gate C) : 2 ≤ capacity C i := by
    by_cases e : IsBad C i <;> simp [capacity,e]
  have lower2 : 2*D.card ≤ M.card := by
    apply Nat.le_trans _ lower
    simpa [Nat.mul_comm] using Finset.sum_le_sum (s := D) (f := fun _ => (2 : ℕ))
      (fun i _ => cap2 i)
  have allClean : ∀ i ∈ D, ¬IsBad C i := by
    intro i hi bad
    have largeCap : capacity C i = 4 := by simp [capacity,bad]
    have dpos := Finset.card_pos.mpr dNon
    by_cases one : D.card = 1
    · have eq : D = {i} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hi) (by simp [one])).symm
      have upper := one_remaining_bound hc out hd big M i
        (fun v hv s hs => Finset.mem_singleton.mp (eq ▸ sub v hv s hs))
      rw [eq, Finset.sum_singleton, largeCap] at lower
      omega
    · have two : D.card = 2 := by omega
      obtain ⟨u,v,ne,eq⟩ := Finset.card_eq_two.mp two
      have upper := remaining_bound hc out hd big M D sub u v (by rw [eq])
      have other := Finset.sum_le_sum (s := D.erase i) (f := fun _ => (2 : ℕ))
        (fun g _ => cap2 g)
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hi, two] at other
      have sep := Finset.sum_erase_add D (capacity C) hi
      omega
  obtain ⟨bound, tiny⟩ := clean_remaining_bound hc out hd big M D sub dcap
    (fun i hi => ⟨allClean i hi,(Finset.mem_filter.mp hi).2⟩)
  have positive := Finset.card_pos.mpr dNon
  by_cases small : D.card ≤ 1
  · have := tiny small
    omega
  · omega


end PEqualNP.Outside.L_meta_7535

theorem PEqualNP.Outside.L_meta_7535 :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.Computes x1 →     x2.outVars = ∅ →       (∀ (x5 : Fin x2.size), Disjoint (x2.leftVars x5) (x2.rightVars x5)) →         x2.size = (19 : ℕ) →           (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin x2.size | x7 ∈ x2.leftVars x8 ∨ x7 ∈ x2.rightVars x8}.ncard ≤ (3 : ℕ)) →             (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin x2.size | x8 ∈ x2.leftVars x13 ∨ x8 ∈ x2.rightVars x13 ∨ x9 ∈ x2.leftVars x13 ∨ x9 ∈ x2.rightVars x13}.ncard ≤ (5 : ℕ)) →               (4 : ℕ) ≤ {x9 : Fin x2.size | ∃ x10 ∈ x2.leftVars x9, ∃ x11 ∈ x2.rightVars x9, ↑x10 < (21 : ℕ) ↔ ↑x11 < (21 : ℕ)}.ncard →                 (5 : ℕ) ≤ {x10 : Fin x2.size | ∃ x11 ∈ x2.leftVars x10, ∃ x12 ∈ x2.rightVars x10, ¬x1.Adj x11 x12}.ncard ∧                   ∃ (x10 : Fin x2.size),                     have x11 : ℕ := (x2.leftVars x10).card;                     have x12 : ℕ := (x2.rightVars x10).card;                     (5 : ℕ) ≤ Min.min x11 x12 ∧ (6 : ℕ) ≤ Max.max x11 x12 ∨ (4 : ℕ) ≤ Min.min x11 x12 ∧ (14 : ℕ) ≤ Max.max x11 x12 := by
  classical
  intro G C hc out hd size read joint clash
  change C.Computes PEqualNP.Outside.L_meta_7535.plane at hc
  have reads (v : PEqualNP.Outside.L_meta_7535.V) : (PEqualNP.Outside.L_meta_7535.positions C v).card ≤ 3 := by
    rw [PEqualNP.Outside.L_meta_7535.positions_card C hd]
    exact read v
  have cset : {i : Fin C.size | PEqualNP.Outside.L_meta_7535.Clashes C i} =
      {i : Fin C.size | ∃ v ∈ C.leftVars i, ∃ w ∈ C.rightVars i, v.val < 21 ↔ w.val < 21} := by
    ext i
    simp only [Set.mem_ofPred_eq, PEqualNP.Outside.L_meta_7535.Clashes, PEqualNP.Outside.L_meta_7535.color, decide_eq_decide]
  refine ⟨L_meta_7535.many_bad hc out hd size reads (cset.symm ▸ clash), ?_⟩
  exact PEqualNP.Outside.L_meta_7535.wide_gate hc out hd reads joint

