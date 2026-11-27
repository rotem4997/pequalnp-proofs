import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7533

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

def neighbors (v : V) : Finset V :=
  @Finset.filter V (plane.Adj v) (adjDec v) Finset.univ

lemma mem_neighbors {v w : V} : w ∈ neighbors v ↔ plane.Adj v w := by
  simp [neighbors]

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



def block (C : AndCountCircuit 42) (s : Slot C) (b : Bool) : Finset V :=
  (raw C s).filter fun v => color v = b

lemma mem_block {C : AndCountCircuit 42} {s : Slot C} {b : Bool} {v : V} :
    v ∈ block C s b ↔ v ∈ raw C s ∧ color v = b := by
  simp [block]

lemma block_partition (C : AndCountCircuit 42) (s : Slot C) :
    (raw C s).card = (block C s false).card + (block C s true).card := by
  have eq : ((raw C s).filter fun v => ¬color v = false) = block C s true := by
    ext v
    cases h : color v <;> simp [block, h]
  rw [← eq]
  exact (Finset.card_filter_add_card_filter_not (s := raw C s) (p := fun v => color v = false)).symm

def occupied (n : ℕ) : ℕ := if 0 < n then 1 else 0

def credit (n : ℕ) : ℕ := if n = 1 then 1 else 0

def crowded (n : ℕ) : ℕ := if 2 ≤ n then 1 else 0

lemma credit_crowded (n : ℕ) : credit n + crowded n = occupied n := by
  unfold credit crowded occupied
  split <;> split <;> split <;> omega

lemma count_of_zero_crowd (n : ℕ) (h : crowded n = 0) : n = credit n := by
  unfold crowded credit at *
  split at h <;> split <;> omega

def tally (C : AndCountCircuit 42) (f : ℕ → ℕ) (i : Fin C.size) : ℕ :=
  f (block C (i,false) false).card + f (block C (i,false) true).card +
  (f (block C (i,true) false).card + f (block C (i,true) true).card)

def clash (C : AndCountCircuit 42) (i : Fin C.size) : Prop :=
  ∃ a ∈ C.leftVars i, ∃ b ∈ C.rightVars i, color a = color b

noncomputable def allowance (C : AndCountCircuit 42) (i : Fin C.size) : ℕ :=
  by classical exact 2 + if clash C i then 2 else 0

lemma occupied_le_allowance (C : AndCountCircuit 42) (i : Fin C.size) :
    tally C occupied i ≤ allowance C i := by
  classical
  by_cases h : clash C i
  · unfold tally occupied allowance
    simp only [ite_eq_left h]
    split <;> split <;> split <;> split <;> omega
  · have dis (b : Bool) :
        occupied (block C (i,false) b).card + occupied (block C (i,true) b).card ≤ 1 := by
      unfold occupied
      split
      next h₁ =>
        split
        next h₂ =>
          obtain ⟨v, hv⟩ := Finset.card_pos.mp h₁
          obtain ⟨w, hw⟩ := Finset.card_pos.mp h₂
          exact (h ⟨v, (mem_block.mp hv).1, w, (mem_block.mp hw).1,
            (mem_block.mp hv).2.trans (mem_block.mp hw).2.symm⟩).elim
        next => decide
      next => split <;> decide
    have h₁ := dis false
    have h₂ := dis true
    unfold tally allowance
    simp only [ite_eq_right h]
    omega

lemma gate_budget (C : AndCountCircuit 42) (i : Fin C.size) :
    tally C credit i + tally C crowded i ≤ allowance C i := by
  have h := occupied_le_allowance C i
  unfold tally at *
  simp only [← credit_crowded] at h
  omega

-- Each vertex has a gate-side color class in which it is the sole member.
lemma credit_total {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (cap : ∀ v, (positions C v).card ≤ 3) :
    42 ≤ ∑ i, tally C credit i := by
  classical
  have priv (v : V) : ∃ s, block C s (color v) = {v} := by
    obtain ⟨s, hs, h⟩ := private_slot hc out v ((cap v).trans (by decide))
    refine ⟨s, Finset.eq_singleton_iff_unique_mem.mpr ?_⟩
    exact ⟨mem_block.mpr ⟨mem_positions.mp hs, rfl⟩,
      fun w hw => h w (mem_block.mp hw).1 (mem_block.mp hw).2⟩
  choose s hs using priv
  let T := Finset.univ.filter fun z : Fin C.size × (Bool × Bool) =>
    (block C (z.1,z.2.1) z.2.2).card = 1
  have inj : Function.Injective (fun v : V => (s v |>.1,(s v |>.2,color v))) := by
    intro v w h
    have g : (s v).1 = (s w).1 := congrArg (fun (z : Fin C.size × (Bool × Bool)) => z.1) h
    have side : (s v).2 = (s w).2 := congrArg (fun z => z.2.1) h
    have e : s v = s w := Prod.ext g side
    have c : color v = color w := congrArg (fun z => z.2.2) h
    have eq := hs v
    rw [e, c, hs w] at eq
    simpa using eq.symm
  have le := Finset.card_le_card (s := Finset.univ.image
    (fun v : V => (s v |>.1,(s v |>.2,color v)))) (t := T) (by
    rintro z hz
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
    simp [T, hs v])
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at le
  have cardT : T.card = ∑ i, tally C credit i := by
    calc
      T.card = ∑ z : Fin C.size × (Bool × Bool), credit (block C (z.1,z.2.1) z.2.2).card :=
        (Finset.sum_boole _ _).symm
      _ = ∑ i, tally C credit i := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
        unfold tally
        dsimp only
        omega
  rwa [← cardT]

lemma allowance_total {C : AndCountCircuit 42} (size : C.size = 19)
    (few : {i : Fin C.size | clash C i}.ncard ≤ 3) :
    (∑ i, allowance C i) ≤ 44 := by
  classical
  let B := Finset.univ.filter (clash C)
  have eq : (B : Set (Fin C.size)) = {i | clash C i} := by
    ext i
    simp [B]
  rw [← eq, Set.ncard_coe_finset] at few
  have step : (∑ i, (if clash C i then (2 : ℕ) else 0)) = B.card * 2 := by
    rw [← Finset.sum_filter]
    simp [B]
  unfold allowance
  rw [Finset.sum_add_distrib, step]
  simp [size]
  omega

def edges : Finset (V × V) :=
  Finset.univ.filter fun e => e.1.val < 21 ∧ 21 ≤ e.2.val ∧
    (e.2.val + 21 - e.1.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)

set_option maxRecDepth 6000 in
lemma edges_card : edges.card = 105 := by decide +kernel

lemma rel_adj {v w : V} (h : rel v w) : plane.Adj v w := by
  have ne : v ≠ w := by
    rintro rfl
    have := h.1
    have := h.2.1
    omega
  exact ⟨ne, Or.inl h⟩

def edgeBlock (C : AndCountCircuit 42) (i : Fin C.size) (b : Bool) : Finset (V × V) :=
  ((block C (i,b) true).product (block C (i,!b) false)).filter (· ∈ edges)

lemma covers {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    105 ≤ ∑ i, ∑ b : Bool, (edgeBlock C i b).card := by
  classical
  let U := Finset.univ.biUnion fun i : Fin C.size =>
    Finset.univ.biUnion (edgeBlock C i)
  have sub : edges ⊆ U := by
    rintro ⟨v,w⟩ h
    have rvw : rel v w := (Finset.mem_filter.mp h).2
    obtain ⟨⟨i,b⟩, hv, hw⟩ := witness hc out hd (rel_adj rvw)
    apply Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_block.mpr ⟨mem_positions.mp hv, by simp [color, rvw.1]⟩,
       mem_block.mpr ⟨hw, by simp [color, Nat.not_lt.mpr rvw.2.1]⟩⟩, h⟩
  rw [← edges_card]
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))

lemma edgeBlock_left (C : AndCountCircuit 42) (i : Fin C.size) (b : Bool) :
    (edgeBlock C i b).card ≤ (block C (i,b) true).card * 5 := by
  classical
  let A := block C (i,b) true
  have sub : edgeBlock C i b ⊆ A.biUnion (fun v => ({v} : Finset V).product (neighbors v)) := by
    rintro ⟨v,w⟩ h
    obtain ⟨hv, r⟩ := Finset.mem_filter.mp h
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_product.mp hv).1,
      Finset.mem_product.mpr ⟨by simp, mem_neighbors.mpr (rel_adj (Finset.mem_filter.mp r).2)⟩⟩
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans (by
    simp [degree, A]))

lemma edgeBlock_right (C : AndCountCircuit 42) (i : Fin C.size) (b : Bool) :
    (edgeBlock C i b).card ≤ (block C (i,!b) false).card * 5 := by
  classical
  let B := block C (i,!b) false
  have sub : edgeBlock C i b ⊆ B.biUnion (fun w => (neighbors w).product ({w} : Finset V)) := by
    rintro ⟨v,w⟩ h
    obtain ⟨hv, r⟩ := Finset.mem_filter.mp h
    exact Finset.mem_biUnion.mpr ⟨w, (Finset.mem_product.mp hv).2,
      Finset.mem_product.mpr ⟨mem_neighbors.mpr (rel_adj (Finset.mem_filter.mp r).2).symm,
        by simp⟩⟩
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans (by
    simp [degree, B]))

lemma edgeBlock_bound (C : AndCountCircuit 42) (i : Fin C.size) (b : Bool)
    (small : (block C (i,b) true).card ≤ 6 ∨ (block C (i,!b) false).card ≤ 6) :
    (edgeBlock C i b).card ≤
      1 + 15 * (crowded (block C (i,b) true).card + crowded (block C (i,!b) false).card) := by
  have l := edgeBlock_left C i b
  have r := edgeBlock_right C i b
  unfold crowded
  split <;> split
  · omega
  · omega
  · omega
  · have p := Finset.card_filter_le
      ((block C (i,b) true).product (block C (i,!b) false)) (· ∈ edges)
    change (edgeBlock C i b).card ≤
      ((block C (i,b) true) ×ˢ (block C (i,!b) false)).card at p
    rw [Finset.card_product] at p
    have bp : (block C (i,b) true).card * (block C (i,!b) false).card ≤ 1 * 1 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

lemma concentrate {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (size : C.size = 19)
    (cap : ∀ v, (positions C v).card ≤ 3)
    (few : {i : Fin C.size | clash C i}.ncard ≤ 3) :
    ∃ k : Fin C.size, 7 ≤ (C.leftVars k).card ∧ 7 ≤ (C.rightVars k).card ∧
      (∑ j ∈ Finset.univ.erase k, ((C.leftVars j).card + (C.rightVars j).card)) ≤ 42 := by
  classical
  have alloc := allowance_total size few
  have demand := credit_total hc out cap
  have combined := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin C.size)))
    fun i _ => gate_budget C i
  rw [Finset.sum_add_distrib] at combined
  have crowd : (∑ i, tally C crowded i) ≤ 2 := by omega
  -- If one class in each opposite-color pair has size at most six,
  -- the two nonsingleton classes cannot account for all 105 edges.
  have big : ∃ i : Fin C.size, ∃ b : Bool,
      7 ≤ (block C (i,b) true).card ∧ 7 ≤ (block C (i,!b) false).card := by
    by_contra! h
    have localBound (i : Fin C.size) :
        (∑ b : Bool, (edgeBlock C i b).card) ≤ 2 + 15 * tally C crowded i := by
      have h₁ := edgeBlock_bound C i false (by have := h i false; omega)
      have h₂ := edgeBlock_bound C i true (by have := h i true; omega)
      rw [Fintype.sum_bool]
      unfold tally
      simp only [Bool.not_false, Bool.not_true] at h₁ h₂
      omega
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin C.size)))
      fun i _ => localBound i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at total
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, size] at total
    have edgeSum := covers hc out hd
    omega
  obtain ⟨k,b,hl,hr⟩ := big
  have two : 2 ≤ tally C crowded k := by
    have h₁ : crowded (block C (k,b) true).card = 1 := ite_eq_left (by omega)
    have h₂ : crowded (block C (k,!b) false).card = 1 := ite_eq_left (by omega)
    unfold tally
    cases b <;> simp only [Bool.not_false, Bool.not_true] at h₁ h₂ <;> omega
  have zero (i : Fin C.size) (ne : i ≠ k) : tally C crowded i = 0 := by
    have hk := Finset.sum_erase_add (Finset.univ : Finset (Fin C.size)) (tally C crowded)
      (Finset.mem_univ k)
    have hi := Finset.single_le_sum (f := tally C crowded) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨ne, Finset.mem_univ i⟩)
    omega
  have cardBound (i : Fin C.size) (ne : i ≠ k) :
      (C.leftVars i).card + (C.rightVars i).card ≤ allowance C i := by
    have z := zero i ne
    have eq := gate_budget C i
    rw [z, Nat.add_zero] at eq
    unfold tally at z eq
    have h00 := count_of_zero_crowd _ (by omega : crowded (block C (i,false) false).card = 0)
    have h01 := count_of_zero_crowd _ (by omega : crowded (block C (i,false) true).card = 0)
    have h10 := count_of_zero_crowd _ (by omega : crowded (block C (i,true) false).card = 0)
    have h11 := count_of_zero_crowd _ (by omega : crowded (block C (i,true) true).card = 0)
    have hl' := block_partition C (i,false)
    have hr' := block_partition C (i,true)
    change (C.leftVars i).card = _ at hl'
    change (C.rightVars i).card = _ at hr'
    omega
  have outside := Finset.sum_le_sum (s := (Finset.univ.erase k)) fun i hi =>
    cardBound i (Finset.mem_erase.mp hi).1
  have splitK := Finset.sum_erase_add (Finset.univ : Finset (Fin C.size)) (allowance C)
    (Finset.mem_univ k)
  have minK : 2 ≤ allowance C k := by unfold allowance; omega
  have lb := hl.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have rb := hr.trans (Finset.card_le_card (Finset.filter_subset _ _))
  refine ⟨k, ?_, ?_, by omega⟩
  · cases b <;> first | exact lb | exact rb
  · cases b <;> first | exact lb | exact rb

end PEqualNP.Outside.L_meta_7533

theorem PEqualNP.Outside.L_meta_7533 :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.Computes x1 → x2.outVars = ∅ → (∀ (x5 : Fin x2.size), Disjoint (x2.leftVars x5) (x2.rightVars x5)) → x2.size = (19 : ℕ) → (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin x2.size | x7 ∈ x2.leftVars x8 ∨ x7 ∈ x2.rightVars x8}.ncard ≤ (3 : ℕ)) → {x8 : Fin x2.size | ∃ x9 ∈ x2.leftVars x8, ∃ x10 ∈ x2.rightVars x8, ↑x9 < (21 : ℕ) ↔ ↑x10 < (21 : ℕ)}.ncard ≤ (3 : ℕ) → ∃ (x9 : Fin x2.size), (7 : ℕ) ≤ (x2.leftVars x9).card ∧ (7 : ℕ) ≤ (x2.rightVars x9).card ∧ ∑ x10 ∈ Finset.univ.erase x9, ((x2.leftVars x10).card + (x2.rightVars x10).card) ≤ (42 : ℕ) := by
  intro G C hc out hd size read few
  change C.Computes PEqualNP.Outside.L_meta_7533.plane at hc
  apply PEqualNP.Outside.L_meta_7533.concentrate hc out hd size
  · intro v
    rw [PEqualNP.Outside.L_meta_7533.positions_card C hd v]
    exact read v
  · convert few using 2
    ext i
    simp [PEqualNP.Outside.L_meta_7533.clash, PEqualNP.Outside.L_meta_7533.color]
