import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5871

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev V := Fin 11
abbrev I := Fin 16

abbrev G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def ends : I → V × V := ![(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def edge (i : I) : Sym2 V := s((ends i).1, (ends i).2)

def pair (i j : I) : Finset (Sym2 V) := {edge i, edge j}

def drop (D : Finset (Sym2 V)) := G.deleteEdges ↑D

def Premise (D : Finset (Sym2 V)) : Prop :=
  ∃ c : V, ∀ u v : V, s(u, v) ∈ D →
    ∃ w : V, (w = u ∨ w = v) ∧ (drop D).Adj c w ∧
      ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop D).Adj t z) ∧
          (∀ a b : V, s(a, b) ∈ D → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false

lemma premise_mono {D F : Finset (Sym2 V)} (hsub : D ⊆ F) (h : Premise F) :
    Premise D := by
  have adj {u v : V} (h : (drop F).Adj u v) : (drop D).Adj u v := by
    obtain ⟨ha, hm⟩ := SimpleGraph.deleteEdges_adj.mp h
    exact SimpleGraph.deleteEdges_adj.mpr ⟨ha, fun hd => hm (hsub hd)⟩
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun u v hmem => ?_⟩
  obtain ⟨w, hw, ha, hx⟩ := hc u v (hsub hmem)
  refine ⟨w, hw, adj ha, fun x hwx hG => ?_⟩
  obtain ⟨S, hs, hcover, hfalse⟩ := hx x hwx hG
  refine ⟨S, ?_, fun a b hab => hcover a b (hsub hab), hfalse⟩
  rcases hs with hs | ⟨z, hz⟩
  · exact Or.inl hs
  · exact Or.inr ⟨z, fun t ht => adj (hz t ht)⟩

def neighborMask : V → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

def adjacent (u v : V) : Bool := (neighborMask u).testBit v.val

lemma adj_iff (u v : V) : G.Adj u v ↔ adjacent u v = true := by
  revert u v
  decide

def between (i : I) (u v : V) : Bool :=
  let (a, b) := ends i
  (u == a && v == b) || (u == b && v == a)

lemma between_iff (i : I) (u v : V) : between i u v = true ↔ s(u, v) = edge i := by
  rw [edge, Sym2.eq_iff]
  simp [between]

lemma index_exists : ∀ u v : V, adjacent u v = true → ∃ i : I, between i u v = true := by
  decide

lemma edge_index {a : Sym2 V} (h : a ∈ G.edgeFinset) : ∃ i : I, a = edge i := by
  revert h
  induction a using Sym2.ind with
  | _ u v =>
    intro h
    obtain ⟨i, hi⟩ := index_exists u v ((adj_iff u v).mp (show G.Adj u v from SimpleGraph.mem_edgeFinset.mp h))
    exact ⟨i, (between_iff i u v).mp hi⟩

def near (i j : I) (u v : V) : Bool :=
  adjacent u v && !between i u v && !between j u v

lemma near_iff (i j : I) (u v : V) : near i j u v = true ↔ (drop (pair i j)).Adj u v := by
  simp [near, drop, pair, SimpleGraph.deleteEdges_adj, adj_iff, ← between_iff, and_assoc]

def hit (k : I) (f : V → Bool) : Bool := f (ends k).1 || f (ends k).2

def hits (i j : I) (f : V → Bool) : Bool := hit i f && hit j f

lemma hits_of_cover {i j : I} {S : Finset V} {f : V → Bool}
    (hcover : ∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S)
    (hf : ∀ t ∈ S, f t = true) : hits i j f = true := by
  have one (k : I) (hk : edge k ∈ pair i j) : hit k f = true := by
    rcases hcover (ends k).1 (ends k).2 hk with h | h
    · simp [hit, hf _ h]
    · simp [hit, hf _ h]
  simp [hits, one i (by simp [pair]), one j (by simp [pair])]

-- Each probe selects one vertex, or the two vertices in an exceptional entry.
def extra (i j : I) (w : V) : V :=
  match i, j, w with
  | 0, 2, 9 => 4
  | 0, 2, 4 => 9
  | 0, 4, 9 => 2
  | 0, 4, 0 => 5
  | 0, 6, 9 => 6
  | 0, 6, 6 => 9
  | 0, 8, 9 => 4
  | 0, 8, 0 => 8
  | 1, 3, 10 => 8
  | 1, 3, 8 => 10
  | 1, 7, 10 => 7
  | 1, 7, 7 => 10
  | 2, 4, 5 => 4
  | 2, 4, 4 => 5
  | 3, 5, 10 => 8
  | 3, 5, 8 => 10
  | 4, 8, 5 => 4
  | 4, 8, 2 => 8
  | 4, 12, 5 => 6
  | 4, 12, 2 => 7
  | 5, 14, 10 => 9
  | 5, 14, 9 => 10
  | 8, 12, 8 => 6
  | 8, 12, 4 => 7
  | 9, 10, 4 => 5
  | 9, 10, 10 => 8
  | 9, 14, 10 => 9
  | 9, 14, 9 => 10
  | 9, 15, 10 => 8
  | 9, 15, 4 => 9
  | 11, 13, 9 => 10
  | 11, 13, 10 => 9
  | 13, 14, 10 => 7
  | 13, 14, 6 => 9
  | 13, 15, 10 => 9
  | 13, 15, 9 => 10
  | _, _, w => w

def probe (i j : I) (w t : V) : Bool := t == w || t == extra i j w

-- A mask records which vertices can hit both edges, either directly or as a center.
def vertexMask (u : V) : ℕ := 2 ^ u.val

lemma vertex_bit (u v : V) : (vertexMask u).testBit v.val = (u == v) := by
  apply Bool.eq_iff_iff.mpr
  simp [vertexMask, Nat.testBit_two_pow, Fin.ext_iff]

lemma conditional_bit (b : Bool) (m k : ℕ) :
    (if b then m else 0).testBit k = (b && m.testBit k) := by
  cases b <;> simp

def removedAt (k : I) (u : V) : ℕ :=
  (if u == (ends k).1 then vertexMask (ends k).2 else 0) |||
  (if u == (ends k).2 then vertexMask (ends k).1 else 0)

lemma removed_bit (k : I) (u v : V) : (removedAt k u).testBit v.val = between k u v := by
  simp only [removedAt, Nat.testBit_or, conditional_bit, vertex_bit, between]
  have swap (a b : V) : (a == b) = (b == a) := by
    apply Bool.eq_iff_iff.mpr
    simpa using (eq_comm : a = b ↔ b = a)
  rw [swap (ends k).2 v, swap (ends k).1 v]

def neighbors (i j : I) (u : V) : ℕ :=
  neighborMask u &&& (2047 ^^^ (removedAt i u ||| removedAt j u))

lemma neighbor_bit (i j : I) (u v : V) : (neighbors i j u).testBit v.val = near i j u v := by
  have hall : (2047 : ℕ).testBit v.val = true := by
    change (2^11 - 1 : ℕ).testBit v.val = true
    exact (Nat.testBit_two_pow_sub_one 11 v.val).trans (decide_eq_true v.isLt)
  unfold neighbors near adjacent
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, removed_bit, removed_bit, hall]
  cases between i u v <;> cases between j u v <;> simp

def reachMask (k : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
  (if f (ends k).1 then m (ends k).1 else 0) |||
  (if f (ends k).2 then m (ends k).2 else 0)

def meetMask (i j : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
  reachMask i f m &&& reachMask j f m

lemma meet_bit (i j : I) (f : V → Bool) (m : V → ℕ) (c : V) :
    (meetMask i j f m).testBit c.val = hits i j (fun t => f t && (m t).testBit c.val) := by
  simp [meetMask, reachMask, conditional_bit, hits, hit]

def failed (i j : I) (w : V) : Bool :=
  let available := fun t => !probe i j w t
  !adjacent w (extra i j w) &&
    (meetMask i j available vertexMask == 0) &&
    (meetMask i j available (neighbors i j) == 0)

lemma probe_false {i j : I} {w : V} (h : adjacent w (extra i j w) = false) :
    graphFun G ∅ (probe i j w) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u, v, ha, hu, hv⟩
  have hu' : u = w ∨ u = extra i j w := by simpa [probe] using hu
  have hv' : v = w ∨ v = extra i j w := by simpa [probe] using hv
  have nh : ¬ G.Adj w (extra i j w) := by simp [adj_iff, h]
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at ha
  · exact G.irrefl ha
  · exact nh ha
  · exact nh ha.symm
  · exact G.irrefl ha

lemma failed_blocks {i j : I} {w : V} (h : failed i j w = true)
    (hw : ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop (pair i j)).Adj t z) ∧
          (∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false) :
    False := by
  simp only [failed, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hind, hsingle⟩, hstandard⟩ := h
  let x := probe i j w
  obtain ⟨S, hs, hcover, hfalse⟩ := hw x (by simp [x, probe]) (probe_false hind)
  have blocked (c : V) (m : V → ℕ) (hm : meetMask i j (fun t => !x t) m = 0)
      (hf : ∀ t ∈ S, (!x t && (m t).testBit c.val) = true) : False := by
    have hb := meet_bit i j (fun t => !x t) m c
    rw [hm, hits_of_cover hcover hf] at hb
    exact Bool.false_ne_true (by simpa only [Nat.zero_testBit] using hb)
  rcases hs with hs | ⟨c, hc⟩
  · have hmem := hcover (ends i).1 (ends i).2 (by change edge i ∈ pair i j; simp [pair])
    have hne : S.Nonempty := hmem.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
    obtain ⟨c, hc⟩ := hne
    refine blocked c vertexMask hsingle fun t ht => ?_
    simp [vertex_bit, Finset.card_le_one.mp hs t ht c hc, hfalse c hc]
  · refine blocked c (neighbors i j) hstandard fun t ht => ?_
    simp [neighbor_bit, (near_iff i j t c).mpr (hc t ht), hfalse t ht]

def allowed (i j : I) : Bool :=
  (i == 1 && j == 10) || (i == 2 && j == 11) ||
  (i == 5 && j == 15) || (i == 9 && j == 11)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma pair_certificate : ∀ i j : I, i < j →
    allowed i j = true ∨ meetMask i j (fun w => !failed i j w) (neighbors i j) = 0 := by
  decide

lemma pair_allowed {i j : I} (hlt : i < j) (h : Premise (pair i j)) : allowed i j = true := by
  obtain ⟨c, hc⟩ := h
  have one (k : I) (hk : edge k ∈ pair i j) :
      hit k (fun w => !failed i j w && (neighbors i j w).testBit c.val) = true := by
    obtain ⟨w, hw, hcw, hx⟩ := hc (ends k).1 (ends k).2 hk
    have hfail : failed i j w = false := Bool.eq_false_iff.mpr fun hf => failed_blocks hf hx
    have hadj := (near_iff i j w c).mpr hcw.symm
    rcases hw with rfl | rfl <;> simp [hit, neighbor_bit, hadj, hfail]
  rcases pair_certificate i j hlt with ha | hbad
  · exact ha
  · have hb := meet_bit i j (fun w => !failed i j w) (neighbors i j) c
    rw [hbad] at hb
    simp [hits, one i (by simp [pair]), one j (by simp [pair])] at hb

def allowedEither (i j : I) : Bool := allowed i j || allowed j i

lemma subpair_allowed {D : Finset (Sym2 V)} (h : Premise D) {i j : I}
    (hi : edge i ∈ D) (hj : edge j ∈ D) (hij : i ≠ j) : allowedEither i j = true := by
  have hs (p q : I) (hp : edge p ∈ D) (hq : edge q ∈ D) : pair p q ⊆ D := by
    intro z hz
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp [allowedEither, pair_allowed hlt (premise_mono (hs i j hi hj) h)]
  · simp [allowedEither, pair_allowed hgt (premise_mono (hs j i hj hi) h)]

lemma no_triple : ∀ i j k : I, allowedEither i j = true → allowedEither i k = true →
    allowedEither j k = false := by
  decide

lemma allowed_cases {i j : I} (h : allowed i j = true) :
    (i = 1 ∧ j = 10) ∨ (i = 2 ∧ j = 11) ∨ (i = 5 ∧ j = 15) ∨ (i = 9 ∧ j = 11) := by
  simpa [allowed, or_assoc] using h


-- A cover pays at least one vertex for an edge and two for a triangle.
lemma edge_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
    {a b : V} (hab : K.Adj a b) : 1 ≤ (T ∩ {a, b}).card := by
  apply Finset.card_pos.mpr
  rcases hT hab with ha | hb
  · exact ⟨a, Finset.mem_inter.mpr ⟨ha, by simp⟩⟩
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb, by simp⟩⟩

lemma triangle_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
    {a b c : V} (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c) :
    2 ≤ (T ∩ {a, b, c}).card := by
  have two (u v : V) (huv : u ≠ v) (hu : u ∈ T) (hv : v ∈ T)
      (hu' : u ∈ ({a, b, c} : Finset V)) (hv' : v ∈ ({a, b, c} : Finset V)) :
      2 ≤ (T ∩ {a, b, c}).card := by
    rw [← Finset.card_pair huv]
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu, hu'⟩
    · exact Finset.mem_inter.mpr ⟨hv, hv'⟩
  rcases hT hab with ha | hb
  · rcases hT hbc with hb | hc
    · exact two a b hab.ne ha hb (by simp) (by simp)
    · exact two a c hac.ne ha hc (by simp) (by simp)
  · rcases hT hac with ha | hc
    · exact two a b hab.ne ha hb (by simp) (by simp)
    · exact two b c hbc.ne hb hc (by simp) (by simp)

lemma add_lower {T A B : Finset V} {a b : ℕ} (hd : Disjoint A B)
    (ha : a ≤ (T ∩ A).card) (hb : b ≤ (T ∩ B).card) :
    a + b ≤ (T ∩ (A ∪ B)).card := by
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]
  exact Nat.add_le_add ha hb

def packingA : List (V × V) := [(0, 9), (1, 8), (2, 5), (3, 6), (3, 7), (6, 7), (4, 10)]

def packingB : List (V × V) := [(0, 9), (1, 4), (1, 8), (4, 8), (2, 10), (3, 6), (3, 7), (6, 7)]

lemma lowerA {i j : I}
    (hp : packingA.all (fun p => near i j p.1 p.2) = true)
    {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
  have adj (u v : V) (hm : (u, v) ∈ packingA) : (drop (pair i j)).Adj u v :=
    (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
  have h1 := edge_lower hT (adj 0 9 (by decide))
  have h2 := edge_lower hT (adj 1 8 (by decide))
  have h3 := edge_lower hT (adj 2 5 (by decide))
  have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
  have h5 := edge_lower hT (adj 4 10 (by decide))
  have h12 := add_lower (by decide) h1 h2
  have h123 := add_lower (by decide) h12 h3
  have h1234 := add_lower (by decide) h123 h4
  have h12345 := add_lower (by decide) h1234 h5
  exact h12345.trans (Finset.card_le_card Finset.inter_subset_left)

lemma lowerB {i j : I}
    (hp : packingB.all (fun p => near i j p.1 p.2) = true)
    {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
  have adj (u v : V) (hm : (u, v) ∈ packingB) : (drop (pair i j)).Adj u v :=
    (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
  have h1 := edge_lower hT (adj 0 9 (by decide))
  have h2 := triangle_lower hT (adj 1 4 (by decide)) (adj 1 8 (by decide)) (adj 4 8 (by decide))
  have h3 := edge_lower hT (adj 2 10 (by decide))
  have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
  have h12 := add_lower (by decide) h1 h2
  have h123 := add_lower (by decide) h12 h3
  have h1234 := add_lower (by decide) h123 h4
  exact h1234.trans (Finset.card_le_card Finset.inter_subset_left)

lemma witness {i j : I} (S : Finset V) (z : V) (hc : S.card = 6)
    (hS : ∀ u v : V, near i j u v = true → u ∈ S ∨ v ∈ S)
    (hG : ∀ u v : V, adjacent u v = true → u ∈ (S ∪ {z}) ∨ v ∈ (S ∪ {z}))
    (hl : ∀ T : Finset V, (drop (pair i j)).IsVertexCover ↑T → 6 ≤ T.card) :
    ∃ T E : Finset V, IsMinCover (drop (pair i j)) T ∧ G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 1 := by
  refine ⟨S, {z}, ⟨?_, ?_⟩, ?_, by simp⟩
  · intro u v h
    exact hS u v ((near_iff i j u v).mpr h)
  · intro T hT
    rw [hc]
    exact hl T hT
  · intro u v h
    exact hG u v ((adj_iff u v).mp h)

lemma solve_pair {i j : I} (ha : allowed i j = true) :
    ∃ T E : Finset V, IsMinCover (drop (pair i j)) T ∧ G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 1 := by
  rcases allowed_cases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact witness {2, 3, 4, 6, 8, 9} 0 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
  · exact witness {0, 2, 4, 6, 7, 8} 5 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
  · exact witness {0, 4, 5, 6, 7, 8} 2 (by decide) (by decide) (by decide) (fun _ => lowerA (by decide))
  · exact witness {0, 2, 4, 6, 7, 8} 5 (by decide) (by decide) (by decide) (fun _ => lowerB (by decide))

lemma solve (D : Finset (Sym2 V)) (hsub : D ⊆ G.edgeFinset)
    (hlo : 2 ≤ D.card) (hhi : D.card ≤ 3) (h : Premise D) :
    ∃ T E : Finset V, IsMinCover (drop D) T ∧ G.IsVertexCover ↑(T ∪ E) ∧ E.card ≤ 3 - D.card := by
  have index (a : Sym2 V) (ha : a ∈ D) : ∃ i : I, a = edge i := edge_index (hsub ha)
  have hc : D.card = 2 := by
    by_contra hn
    obtain ⟨a, b, c, hab, hac, hbc, hd⟩ := Finset.card_eq_three.mp (show D.card = 3 by omega)
    obtain ⟨i, rfl⟩ := index a (by simp [hd])
    obtain ⟨j, rfl⟩ := index b (by simp [hd])
    obtain ⟨k, rfl⟩ := index c (by simp [hd])
    have ij := subpair_allowed h (i := i) (j := j) (by simp [hd]) (by simp [hd]) (fun e => hab (congrArg edge e))
    have ik := subpair_allowed h (i := i) (j := k) (by simp [hd]) (by simp [hd]) (fun e => hac (congrArg edge e))
    have jk := subpair_allowed h (i := j) (j := k) (by simp [hd]) (by simp [hd]) (fun e => hbc (congrArg edge e))
    rw [no_triple i j k ij ik] at jk
    cases jk
  rw [hc]
  obtain ⟨a, b, hab, hd⟩ := Finset.card_eq_two.mp hc
  obtain ⟨i, rfl⟩ := index a (by simp [hd])
  obtain ⟨j, rfl⟩ := index b (by simp [hd])
  have hij : i ≠ j := fun e => hab (congrArg edge e)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hd' : D = pair i j := hd
    rw [hd'] at h ⊢
    exact solve_pair (pair_allowed hlt h)
  · have hd' : D = pair j i := by rw [hd, pair, Finset.pair_comm]
    rw [hd'] at h ⊢
    exact solve_pair (pair_allowed hgt h)

end PEqualNP.Outside.L_meta_5871

theorem PEqualNP.Outside.L_meta_5871 :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ x2 ⊆ x1.edgeFinset,   (2 : ℕ) ≤ x2.card →     x2.card ≤ (3 : ℕ) →       have x6 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x2;       (∃ (x7 : Fin (11 : ℕ)), ∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ x2 → ∃ (x11 : Fin (11 : ℕ)), (x11 = x8 ∨ x11 = x9) ∧ x6.Adj x7 x11 ∧ ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x11 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x12 = Bool.false → ∃ (x15 : Finset (Fin (11 : ℕ))), (x15.card ≤ (1 : ℕ) ∨ ∃ (x16 : Fin (11 : ℕ)), ∀ x17 ∈ x15, x6.Adj x17 x16) ∧ (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x2 → x16 ∈ x15 ∨ x17 ∈ x15) ∧ ∀ x16 ∈ x15, x12 x16 = Bool.false) → ∃ (x8 : Finset (Fin (11 : ℕ))) (x9 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover x6 x8 ∧ x1.IsVertexCover ↑(x8 ∪ x9) ∧ x9.card ≤ (3 : ℕ) - x2.card := by
  intro _ D hsub hlo hhi _ h
  exact PEqualNP.Outside.L_meta_5871.solve D hsub hlo hhi h
