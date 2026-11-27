import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9498



-- A binary circuit with 54 necessary inputs and at most 61 gates can copy a
-- live value at most eight times. Each copy costs at most two vertex deletions
-- to remove. An explicit cyclic potential proves that at least eighteen
-- deletions are needed to remove all induced four-vertex paths in this graph.

abbrev V := Fin 27
abbrev W := Option V → Option V → Prop

structure Box where
  left : Finset V
  right : Finset V
  deriving DecidableEq

def Box.union (a b : Box) : Box := ⟨a.left ∪ b.left, a.right ∪ b.right⟩
def Sep (a b : Box) : Prop := Disjoint a.left b.left ∧ Disjoint a.right b.right

def Cluster (R : V → V → Prop) : Prop :=
  ∀ {r s c d}, R r c → R r d → R s c → R s d

def Core (T : Box) (w : W) (r c : V) : Prop :=
  r ∈ T.left ∧ c ∈ T.right ∧ w (some r) (some c) ∧ ¬w (some r) none ∧ ¬w none (some c)

structure Good (T S : Box) (w : W) : Prop where
  empty : ¬w none none
  leftOff : ∀ r ∈ T.left, r ∉ S.left → ¬w (some r) none
  rightOff : ∀ c ∈ T.right, c ∉ S.right → ¬w none (some c)
  dropLeft : ∀ r ∈ T.left, ∀ c ∈ T.right, r ∉ S.left → (w (some r) (some c) ↔ w none (some c))
  dropRight : ∀ r ∈ T.left, ∀ c ∈ T.right, c ∉ S.right → (w (some r) (some c) ↔ w (some r) none)
  cluster : Cluster (Core T w)

theorem coreSupport {T S w r c} (h : Good T S w) (p : Core T w r c) :
    r ∈ S.left ∧ c ∈ S.right := by
  obtain ⟨hr,hc,hp,hnr,hnc⟩ := p
  constructor
  · by_contra hbad
    exact hnc ((h.dropLeft r hr c hc hbad).mp hp)
  · by_contra hbad
    exact hnr ((h.dropRight r hr c hc hbad).mp hp)

theorem clusterUnion {R Q : V → V → Prop} (hR : Cluster R) (hQ : Cluster Q)
    (rows : ∀ {r c d}, R r c → Q r d → False)
    (cols : ∀ {r s c}, R r c → Q s c → False) :
    Cluster (fun r c => R r c ∨ Q r c) := by
  intro r s c d a b e
  rcases a with a|a <;> rcases b with b|b <;> rcases e with e|e
  · exact Or.inl (hR a b e)
  · exact (cols a e).elim
  · exact (rows a b).elim
  · exact (rows a b).elim
  · exact (rows b a).elim
  · exact (rows b a).elim
  · exact (cols e a).elim
  · exact Or.inr (hQ a b e)

def either (u v : W) : W := fun r c => u r c ∨ v r c
def both (u v : W) : W := fun r c => u r c ∧ v r c

theorem disjointCore {T A B u v} (a : Good T A u) (b : Good T B v) (indep : Sep A B) :
    ∀ r c, Core T (either u v) r c ↔ Core T u r c ∨ Core T v r c := by
  intro r c
  constructor
  · rintro ⟨hr,hc,h,hl,hd⟩
    rcases h with h|h
    · exact Or.inl ⟨hr,hc,h,fun x => hl (Or.inl x),fun x => hd (Or.inl x)⟩
    · exact Or.inr ⟨hr,hc,h,fun x => hl (Or.inr x),fun x => hd (Or.inr x)⟩
  · rintro (h|h)
    · obtain ⟨ra,ca⟩ := coreSupport a h
      have nr := b.leftOff r h.1 (Finset.disjoint_left.mp indep.1 ra)
      have nc := b.rightOff c h.2.1 (Finset.disjoint_left.mp indep.2 ca)
      exact ⟨h.1,h.2.1,Or.inl h.2.2.1,fun x => x.elim h.2.2.2.1 nr,fun x => x.elim h.2.2.2.2 nc⟩
    · obtain ⟨rb,cb⟩ := coreSupport b h
      have nr := a.leftOff r h.1 (Finset.disjoint_right.mp indep.1 rb)
      have nc := a.rightOff c h.2.1 (Finset.disjoint_right.mp indep.2 cb)
      exact ⟨h.1,h.2.1,Or.inr h.2.2.1,fun x => x.elim nr h.2.2.2.1,fun x => x.elim nc h.2.2.2.2⟩

def rectangle (T : Box) (u v : W) (r c : V) : Prop :=
  (r ∈ T.left ∧ u (some r) none) ∧ (c ∈ T.right ∧ v none (some c))

theorem rectangleCluster (T : Box) (u v : W) : Cluster (rectangle T u v) := by
  intro r s c d _ a b
  exact ⟨b.1,a.2⟩

set_option maxHeartbeats 900000 in
theorem disjointProduct {T A B u v} (a : Good T A u) (b : Good T B v) (indep : Sep A B) :
    ∀ r c, Core T (both u v) r c ↔ rectangle T u v r c ∨ rectangle T v u r c := by
  intro r c
  by_cases hr : r ∈ T.left
  · by_cases hc : c ∈ T.right
    · have ar := a.leftOff r hr
      have ac := a.rightOff c hc
      have br := b.leftOff r hr
      have bc := b.rightOff c hc
      have al := a.dropLeft r hr c hc
      have ad := a.dropRight r hr c hc
      have bl := b.dropLeft r hr c hc
      have bd := b.dropRight r hr c hc
      have rs : r ∈ A.left → r ∈ B.left → False := fun x y => Finset.disjoint_left.mp indep.1 x y
      have cs : c ∈ A.right → c ∈ B.right → False := fun x y => Finset.disjoint_left.mp indep.2 x y
      simp only [Core, both, rectangle, hr, hc, true_and]
      by_cases ra : r ∈ A.left <;> by_cases rb : r ∈ B.left <;>
        by_cases ca : c ∈ A.right <;> by_cases cb : c ∈ B.right <;>
        simp_all only [not_true_eq_false, not_false_eq_true, false_implies, true_implies,
          and_false, false_and, or_false, false_or, and_true]
      all_goals tauto
    · simp [Core, rectangle, hc]
  · simp [Core, rectangle, hr]

theorem eitherGood {T A B u v} (a : Good T A u) (b : Good T B v) (h : Sep A B) :
    Good T (A.union B) (either u v) := by
  refine ⟨fun z => z.elim a.empty b.empty, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr off z
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact z.elim (a.leftOff r hr ha) (b.leftOff r hr hb)
  · intro c hc off z
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact z.elim (a.rightOff c hc ha) (b.rightOff c hc hb)
  · intro r hr c hc off
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact or_congr (a.dropLeft r hr c hc ha) (b.dropLeft r hr c hc hb)
  · intro r hr c hc off
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact or_congr (a.dropRight r hr c hc ha) (b.dropRight r hr c hc hb)
  · have rows {r c d} (x : Core T u r c) (y : Core T v r d) :=
      Finset.disjoint_left.mp h.1 (coreSupport a x).1 (coreSupport b y).1
    have cols {r s c} (x : Core T u r c) (y : Core T v s c) :=
      Finset.disjoint_left.mp h.2 (coreSupport a x).2 (coreSupport b y).2
    intro r s c d p q e
    apply (disjointCore a b h s d).mpr
    exact clusterUnion (R := Core T u) (Q := Core T v) a.cluster b.cluster rows cols
      ((disjointCore a b h r c).mp p) ((disjointCore a b h r d).mp q) ((disjointCore a b h s c).mp e)

theorem bothGood {T A B u v} (a : Good T A u) (b : Good T B v) (h : Sep A B) :
    Good T (A.union B) (both u v) := by
  refine ⟨fun z => a.empty z.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr off z
    exact a.leftOff r hr (fun ha => off (Finset.mem_union_left _ ha)) z.1
  · intro c hc off z
    exact a.rightOff c hc (fun ha => off (Finset.mem_union_left _ ha)) z.1
  · intro r hr c hc off
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact and_congr (a.dropLeft r hr c hc ha) (b.dropLeft r hr c hc hb)
  · intro r hr c hc off
    obtain ⟨ha,hb⟩ := not_or.mp (fun x => off (Finset.mem_union.mpr x))
    exact and_congr (a.dropRight r hr c hc ha) (b.dropRight r hr c hc hb)
  · have rows {r c d} (x : rectangle T u v r c) (y : rectangle T v u r d) : False := by
      by_cases hr : r ∈ A.left
      · exact b.leftOff r x.1.1 (Finset.disjoint_left.mp h.1 hr) y.1.2
      · exact a.leftOff r x.1.1 hr x.1.2
    have cols {r s c} (x : rectangle T u v r c) (y : rectangle T v u s c) : False := by
      by_cases hc : c ∈ B.right
      · exact a.rightOff c x.2.1 (Finset.disjoint_right.mp h.2 hc) y.2.2
      · exact b.rightOff c x.2.1 hc x.2.2
    intro r s c d p q e
    apply (disjointProduct a b h s d).mpr
    exact clusterUnion (R := rectangle T u v) (Q := rectangle T v u)
      (rectangleCluster T u v) (rectangleCluster T v u) rows cols
      ((disjointProduct a b h r c).mp p) ((disjointProduct a b h r d).mp q) ((disjointProduct a b h s c).mp e)


def Box.empty : Box := ⟨∅,∅⟩
def Box.minus (T A : Box) : Box := ⟨T.left \ A.left, T.right \ A.right⟩
def Box.cost (T : Box) : ℕ := T.left.card + T.right.card
def Smaller (U T : Box) : Prop := U.left ⊆ T.left ∧ U.right ⊆ T.right

structure Path4 (G : V → V → Prop) (r s c d : V) : Prop where
  rc : G r c
  rd : G r d
  sc : G s c
  sd : ¬G s d

structure Inside (T : Box) (r s c d : V) : Prop where
  rmem : r ∈ T.left
  smem : s ∈ T.left
  cmem : c ∈ T.right
  dmem : d ∈ T.right

def Preserves (G : V → V → Prop) (T D U : Box) : Prop :=
  ∀ r s c d, Path4 G r s c d → Inside T r s c d →
    Inside (T.minus D) r s c d → Inside U r s c d

def TwinShield (G : V → V → Prop) : Prop :=
  ∀ i j : V, i ≠ j → ∃ d : V, ∀ y, y ≠ d → G i y → G j y → ∀ x, G x y → x = i ∨ x = j

theorem rowShield {G : V → V → Prop} (shield : TwinShield G) (T : Box) (X : Finset V)
    (twins : ∀ i ∈ X, ∀ j ∈ X, ∀ y ∈ T.right, G i y ↔ G j y) :
    ∃ D : Box, D.cost ≤ 1 ∧ ∀ r s c d, Path4 G r s c d → Inside T r s c d →
    Inside (T.minus D) r s c d → r ∉ X ∧ s ∉ X := by
  classical
  by_cases pair : ∃ i ∈ X, ∃ j ∈ X, i ≠ j
  · obtain ⟨i,hi,j,hj,hij⟩ := pair
    obtain ⟨e,he⟩ := shield i j hij
    refine ⟨⟨∅,{e}⟩, by simp [Box.cost], ?_⟩
    intro r s c d path hT avoid
    have ce : c ≠ e := by simpa [Box.minus] using (Finset.mem_sdiff.mp avoid.cmem).2
    have impossible (k : V) (hk : k ∈ X) (hc : G k c) : False := by
      have neighbors := he c ce ((twins k hk i hi c hT.cmem).mp hc) ((twins k hk j hj c hT.cmem).mp hc)
      have rx : r ∈ X := (neighbors r path.rc).elim (fun h => h ▸ hi) (fun h => h ▸ hj)
      have sx : s ∈ X := (neighbors s path.sc).elim (fun h => h ▸ hi) (fun h => h ▸ hj)
      exact path.sd ((twins r rx s sx d hT.dmem).mp path.rd)
    exact ⟨fun h => impossible r h path.rc, fun h => impossible s h path.sc⟩
  · have size : X.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra h
      exact pair ⟨i,hi,j,hj,h⟩
    refine ⟨⟨X,∅⟩, by simpa [Box.cost], ?_⟩
    intro r s c d _ _ h
    exact ⟨(Finset.mem_sdiff.mp h.rmem).2, (Finset.mem_sdiff.mp h.smem).2⟩

def transpose (A : Box) : Box := ⟨A.right,A.left⟩

theorem colShield {G : V → V → Prop} (shield : TwinShield (fun c r => G r c)) (T : Box)
    (X : Finset V) (twins : ∀ i ∈ X, ∀ j ∈ X, ∀ y ∈ T.left, G y i ↔ G y j) :
    ∃ D : Box, D.cost ≤ 1 ∧ ∀ r s c d, Path4 G r s c d → Inside T r s c d →
    Inside (T.minus D) r s c d → c ∉ X ∧ d ∉ X := by
  obtain ⟨D,low,cover⟩ := rowShield shield (transpose T) X twins
  refine ⟨transpose D, by simpa [Box.cost, transpose, Nat.add_comm] using low, ?_⟩
  intro r s c d h i j
  exact cover c d r s ⟨h.rc,h.sc,h.rd,h.sd⟩ ⟨i.cmem,i.dmem,i.rmem,i.smem⟩
    ⟨j.cmem,j.dmem,j.rmem,j.smem⟩

theorem costUnion (A B : Box) : (A.union B).cost ≤ A.cost + B.cost := by
  have hl := Finset.card_union_le A.left B.left
  have hr := Finset.card_union_le A.right B.right
  unfold Box.union Box.cost
  dsimp
  omega

theorem minusSmall (T S : Box) : Smaller (T.minus S) T :=
  ⟨Finset.sdiff_subset, Finset.sdiff_subset⟩

theorem insideSub {T U : Box} (sub : Smaller U T) {r s c d} (h : Inside U r s c d) :
    Inside T r s c d := ⟨sub.1 h.rmem, sub.1 h.smem, sub.2 h.cmem, sub.2 h.dmem⟩

theorem insideAvoidUnion {T A B : Box} {r s c d} (h : Inside (T.minus (A.union B)) r s c d) :
    Inside (T.minus A) r s c d ∧ Inside (T.minus B) r s c d := by
  have hs {z : Finset V} (a b : Finset V) :
      z \ (a ∪ b) ⊆ z \ a ∧ z \ (a ∪ b) ⊆ z \ b :=
    ⟨Finset.sdiff_subset_sdiff (by rfl) Finset.subset_union_left,
     Finset.sdiff_subset_sdiff (by rfl) Finset.subset_union_right⟩
  obtain ⟨h1,h2⟩ := @hs T.left A.left B.left
  obtain ⟨h3,h4⟩ := @hs T.right A.right B.right
  exact ⟨⟨h1 h.rmem,h1 h.smem,h3 h.cmem,h3 h.dmem⟩,⟨h2 h.rmem,h2 h.smem,h4 h.cmem,h4 h.dmem⟩⟩

def output (G : V → V → Prop) : W
  | some r, some c => G r c
  | _, _ => False

def OptIn (S : Finset V) : Option V → Prop
  | none => True
  | some v => v ∈ S

def Determines (s : Finset W) (G : V → V → Prop) : Prop :=
  ∀ r c r' c', (∀ w ∈ s, w r c ↔ w r' c') → (output G r c ↔ output G r' c')

structure State (T : Box) (s : Finset W) (L : W → Box) : Prop where
  good : ∀ w ∈ s, Good T (L w) w
  sep : ∀ w ∈ s, ∀ v ∈ s, w ≠ v → Sep (L w) (L v)

theorem foreignRow {T s L w v} (st : State T s L) (hw : w ∈ s) (hv : v ∈ s) (diff : w ≠ v)
    (r c) (tr : OptIn T.left r) (sr : OptIn (L w).left r) (tc : OptIn T.right c) :
    v r c ↔ v none c := by
  cases r with
  | none => rfl
  | some r =>
    have out := Finset.disjoint_left.mp (st.sep w hw v hv diff).1 sr
    cases c with
    | none => exact iff_of_false ((st.good v hv).leftOff r tr out) (st.good v hv).empty
    | some c => exact (st.good v hv).dropLeft r tr c tc out

theorem foreignCol {T s L w v} (st : State T s L) (hw : w ∈ s) (hv : v ∈ s) (diff : w ≠ v)
    (r c) (tc : OptIn T.right c) (sc : OptIn (L w).right c) (tr : OptIn T.left r) :
    v r c ↔ v r none := by
  cases c with
  | none => rfl
  | some c =>
    have out := Finset.disjoint_left.mp (st.sep w hw v hv diff).2 sc
    cases r with
    | none => exact iff_of_false ((st.good v hv).rightOff c tc out) (st.good v hv).empty
    | some r => exact (st.good v hv).dropRight r tr c tc out

theorem compareRows {T s L w G} (st : State T s L) (hw : w ∈ s) (det : Determines s G)
    {r r' c} (tr : OptIn T.left r) (sr : OptIn (L w).left r)
    (tr' : OptIn T.left r') (sr' : OptIn (L w).left r') (tc : OptIn T.right c)
    (same : w r c ↔ w r' c) : output G r c ↔ output G r' c := by
  apply det
  intro v hv
  by_cases eq : w = v
  · exact eq ▸ same
  · exact (foreignRow st hw hv eq r c tr sr tc).trans (foreignRow st hw hv eq r' c tr' sr' tc).symm

theorem compareCols {T s L w G} (st : State T s L) (hw : w ∈ s) (det : Determines s G)
    {r c c'} (tc : OptIn T.right c) (sc : OptIn (L w).right c)
    (tc' : OptIn T.right c') (sc' : OptIn (L w).right c') (tr : OptIn T.left r)
    (same : w r c ↔ w r c') : output G r c ↔ output G r c' := by
  apply det
  intro v hv
  by_cases eq : w = v
  · exact eq ▸ same
  · exact (foreignCol st hw hv eq r c tc sc tr).trans (foreignCol st hw hv eq r c' tc' sc' tr).symm

theorem insideCompare {T s L w G} (st : State T s L) (hw : w ∈ s) (det : Determines s G)
    {r c r' c'} (tr : OptIn T.left r) (sr : OptIn (L w).left r)
    (tc : OptIn T.right c) (sc : OptIn (L w).right c)
    (tr' : OptIn T.left r') (sr' : OptIn (L w).left r')
    (tc' : OptIn T.right c') (sc' : OptIn (L w).right c')
    (same : w r c ↔ w r' c') : output G r c ↔ output G r' c' := by
  apply det
  intro v hv
  by_cases eq : w = v
  · exact eq ▸ same
  · exact (foreignRow st hw hv eq r c tr sr tc).trans <|
      (foreignCol st hw hv eq none c tc sc trivial).trans <|
      (foreignCol st hw hv eq none c' tc' sc' trivial).symm.trans
      (foreignRow st hw hv eq r' c' tr' sr' tc').symm

-- Before a value is copied, its inputs reach the remaining computation only
-- through that value. An internal edge isolates a read-once component.
-- Otherwise the surviving inputs on each shore have identical neighborhoods.
theorem paidPrune {T s L w G} (st : State T s L) (hw : w ∈ s) (det : Determines s G)
    (shL : TwinShield G) (shR : TwinShield (fun c r => G r c)) :
    ∃ D : Box, D.cost ≤ 2 ∧ Preserves G T D (T.minus (L w)) := by
  classical
  have good := st.good w hw
  have leftPos {r c} (hr : r ∈ T.left) (hs : r ∈ (L w).left) (hc : c ∈ T.right)
      (off : c ∉ (L w).right) (edge : G r c) : w (some r) none := by
    by_contra hn
    have x := (good.dropRight r hr c hc off).not.mpr hn
    have eq := iff_of_false x (good.rightOff c hc off)
    exact (compareRows st hw det (r := some r) (r' := none) (c := some c) hr hs trivial trivial hc eq).mp edge
  have rightPos {r c} (hr : r ∈ T.left) (off : r ∉ (L w).left) (hc : c ∈ T.right)
      (hs : c ∈ (L w).right) (edge : G r c) : w none (some c) := by
    by_contra hn
    have x := (good.dropLeft r hr c hc off).not.mpr hn
    have eq := iff_of_false x (good.leftOff r hr off)
    exact (compareCols st hw det (c := some c) (c' := none) (r := some r) hc hs trivial trivial hr eq).mp edge
  by_cases connected : ∃ r ∈ T.left, ∃ c ∈ T.right, r ∈ (L w).left ∧ c ∈ (L w).right ∧ G r c
  · obtain ⟨u,hu,v,hv,su,sv,uv⟩ := connected
    have hpos : w (some u) (some v) := by
      by_contra h
      exact (insideCompare st hw det (r := some u) (c := some v) (r' := none) (c' := none)
        hu su hv sv trivial trivial trivial trivial (iff_of_false h good.empty)).mp uv
    have inside {r c} (tr : OptIn T.left r) (sr : OptIn (L w).left r)
        (tc : OptIn T.right c) (sc : OptIn (L w).right c) : w r c ↔ output G r c := by
      by_cases p : w r c
      · exact iff_of_true p ((insideCompare st hw det (r' := some u) (c' := some v)
          tr sr tc sc hu su hv sv (iff_of_true p hpos)).mpr uv)
      · have eq := insideCompare st hw det (r' := none) (c' := none)
          tr sr tc sc trivial trivial trivial trivial (iff_of_false p good.empty)
        exact iff_of_false p (fun h => eq.mp h)
    have aligned {r c} (hr : r ∈ T.left) (hc : c ∈ T.right) (edge : G r c) :
        r ∈ (L w).left ↔ c ∈ (L w).right := by
      constructor
      · intro rs
        by_contra off
        exact (inside (r := some r) (c := none) hr rs trivial trivial).mp (leftPos hr rs hc off edge)
      · intro cs
        by_contra off
        exact (inside (r := none) (c := some c) trivial trivial hc cs).mp (rightPos hr off hc cs edge)
    have core {r c} (hr : r ∈ T.left) (rs : r ∈ (L w).left) (hc : c ∈ T.right)
        (cs : c ∈ (L w).right) (edge : G r c) : Core T w r c :=
      ⟨hr,hc,(inside (r := some r) (c := some c) hr rs hc cs).mpr edge,
        (inside (r := some r) (c := none) hr rs trivial trivial).mp,
        (inside (r := none) (c := some c) trivial trivial hc cs).mp⟩
    refine ⟨Box.empty, by simp [Box.empty, Box.cost], ?_⟩
    intro r s c d p t _
    have a := aligned t.rmem t.cmem p.rc
    have b := aligned t.rmem t.dmem p.rd
    have e := aligned t.smem t.cmem p.sc
    have rr : r ∉ (L w).left := by
      intro r0
      have c0 := a.mp r0
      have d0 := b.mp r0
      have s0 := e.mpr c0
      have hc := good.cluster (core t.rmem r0 t.cmem c0 p.rc)
        (core t.rmem r0 t.dmem d0 p.rd) (core t.smem s0 t.cmem c0 p.sc)
      exact p.sd ((inside (r := some s) (c := some d) t.smem s0 t.dmem d0).mp hc.2.2.1)
    exact ⟨Finset.mem_sdiff.mpr ⟨t.rmem,rr⟩, Finset.mem_sdiff.mpr ⟨t.smem,fun h => rr (a.mpr (e.mp h))⟩,
      Finset.mem_sdiff.mpr ⟨t.cmem,fun h => rr (a.mpr h)⟩,Finset.mem_sdiff.mpr ⟨t.dmem,fun h => rr (b.mpr h)⟩⟩
  · have noInside {r c} (hr : r ∈ T.left) (hc : c ∈ T.right) (rs : r ∈ (L w).left)
        (cs : c ∈ (L w).right) : ¬ G r c := fun h => connected ⟨r,hr,c,hc,rs,cs,h⟩
    let X := T.left.filter (fun r => r ∈ (L w).left ∧ w (some r) none)
    let Y := T.right.filter (fun c => c ∈ (L w).right ∧ w none (some c))
    have twinL : ∀ r ∈ X, ∀ b ∈ X, ∀ c ∈ T.right, G r c ↔ G b c := by
      intro r hr b hb c hc
      obtain ⟨tr,sr,ar⟩ := Finset.mem_filter.mp hr
      obtain ⟨tb,sb,ab⟩ := Finset.mem_filter.mp hb
      by_cases sc : c ∈ (L w).right
      · exact iff_of_false (noInside tr hc sr sc) (noInside tb hc sb sc)
      · exact compareRows st hw det (r := some r) (r' := some b) (c := some c) tr sr tb sb hc
          (iff_of_true ((good.dropRight r tr c hc sc).mpr ar) ((good.dropRight b tb c hc sc).mpr ab))
    have twinR : ∀ c ∈ Y, ∀ d ∈ Y, ∀ r ∈ T.left, G r c ↔ G r d := by
      intro c hc d hd r hr
      obtain ⟨tc,sc,ac⟩ := Finset.mem_filter.mp hc
      obtain ⟨td,sd,ad⟩ := Finset.mem_filter.mp hd
      by_cases sr : r ∈ (L w).left
      · exact iff_of_false (noInside hr tc sr sc) (noInside hr td sr sd)
      · exact compareCols st hw det (r := some r) (c := some c) (c' := some d) tc sc td sd hr
          (iff_of_true ((good.dropLeft r hr c tc sr).mpr ac) ((good.dropLeft r hr d td sr).mpr ad))
    obtain ⟨D1,h1,coverL⟩ := rowShield shL T X twinL
    obtain ⟨D2,h2,coverR⟩ := colShield shR T Y twinR
    refine ⟨D1.union D2, le_trans (costUnion _ _) (by omega), ?_⟩
    intro r s c d p t avoid
    obtain ⟨a,b⟩ := insideAvoidUnion avoid
    obtain ⟨rx,sx⟩ := coverL r s c d p t a
    obtain ⟨cy,dy⟩ := coverR r s c d p t b
    have leftOK {i j} (hi : i ∈ T.left) (hj : j ∈ T.right) (edge : G i j) (x : i ∉ X) : i ∉ (L w).left := by
      intro is
      have off : j ∉ (L w).right := fun js => noInside hi hj is js edge
      exact x (Finset.mem_filter.mpr ⟨hi,is,leftPos hi is hj off edge⟩)
    have rightOK {i j} (hi : i ∈ T.left) (hj : j ∈ T.right) (edge : G i j) (y : j ∉ Y) : j ∉ (L w).right := by
      intro js
      have off : i ∉ (L w).left := fun is => noInside hi hj is js edge
      exact y (Finset.mem_filter.mpr ⟨hj,js,rightPos hi off hj js edge⟩)
    exact ⟨Finset.mem_sdiff.mpr ⟨t.rmem,leftOK t.rmem t.cmem p.rc rx⟩,
      Finset.mem_sdiff.mpr ⟨t.smem,leftOK t.smem t.cmem p.sc sx⟩,
      Finset.mem_sdiff.mpr ⟨t.cmem,rightOK t.rmem t.cmem p.rc cy⟩,
      Finset.mem_sdiff.mpr ⟨t.dmem,rightOK t.rmem t.dmem p.rd dy⟩⟩
-- Live-chain compression follows the argument in the project proof L_meta_6342.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hsub : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def liveChain (ops : α → α → Finset α) (goal : α) : List (α × α × α) → Finset α → Prop
  | [], s => s = {goal}
  | (a, b, z) :: gs, s =>
    a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ z ∈ ops a b ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveChain ops goal gs (insert z rest)

theorem compress_chain {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ ∃ s ⊆ available, liveChain ops goal gs s := by
  induction k generalizing available with
  | zero =>
    exact ⟨[], Nat.le_refl 0, {goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨gs, hlen, s, hs, hrun⟩ := ih skip
      exact ⟨gs, Nat.le_succ_of_le hlen, s, hs, hrun⟩
    · obtain ⟨gs, hlen, t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨gs, Nat.le_succ_of_le hlen, t, sub, hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨(a, b, z) :: gs, Nat.succ_le_succ hlen, s, hs,
          by simp [s], by simp [s], hab, hz, fun h => hzout (hs h), rest, rfl, ?_⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem chain_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {gs : List (α × α × α)} {s : Finset α} (h : liveChain ops goal gs s) : ∃ w ∈ s, D w := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, _, hz, _, rest, rfl, tail⟩
    obtain ⟨w, hw, hD⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops a b w hz hD with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · exact ⟨w, by simp [hw], hD⟩

end Live

noncomputable local instance : DecidableEq W := Classical.decEq _
noncomputable def joins (u v : W) : Finset W := {both u v, either u v}

theorem chainDetermines {G s gs} (run : liveChain joins (output G) gs s) : Determines s G := by
  induction gs generalizing s with
  | nil =>
    change s = {output G} at run
    intro r c r' c' eq
    exact eq _ (by simp [run])
  | cons g gs ih =>
    rcases g with ⟨a,b,z⟩
    obtain ⟨ha,hb,_,hz,_,rest,hs,tail⟩ := run
    intro r c r' c' eq
    apply ih tail
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hf
    · rcases (show f = both a b ∨ f = either a b by simpa [joins] using hz) with rfl|rfl
      · exact and_congr (eq a ha) (eq b hb)
      · exact or_congr (eq a ha) (eq b hb)
    · exact eq f (by simp [hs,hf])

theorem goodShrink {T U L w} (a : Good T L w) (u : Smaller U T) : Good U L w := by
  refine ⟨a.empty,fun r hr => a.leftOff r (u.1 hr),fun c hc => a.rightOff c (u.2 hc),
    fun r hr c hc => a.dropLeft r (u.1 hr) c (u.2 hc),
    fun r hr c hc => a.dropRight r (u.1 hr) c (u.2 hc),?_⟩
  have lift {r c} (p : Core U w r c) : Core T w r c := ⟨u.1 p.1,u.2 p.2.1,p.2.2⟩
  intro r s c d p q e
  exact ⟨e.1,q.2.1,(a.cluster (lift p) (lift q) (lift e)).2.2⟩

theorem sepSymm {A B : Box} (h : Sep A B) : Sep B A := ⟨h.1.symm,h.2.symm⟩

theorem sepUnion {A B C : Box} (a : Sep A C) (b : Sep B C) : Sep (A.union B) C :=
  ⟨Finset.disjoint_union_left.mpr ⟨a.1,b.1⟩,Finset.disjoint_union_left.mpr ⟨a.2,b.2⟩⟩

theorem dropState {T s L w} (state : State T s L) (hw : w ∈ s) :
    State (T.minus (L w)) s (Function.update L w Box.empty) := by
  constructor
  · intro v hv
    by_cases e : v = w
    · subst v
      rw [Function.update_self]
      have old := state.good w hw
      refine ⟨old.empty, ?_, ?_, ?_, ?_, (goodShrink old (minusSmall T _)).cluster⟩
      · intro r h _
        exact old.leftOff r (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h).2
      · intro c h _
        exact old.rightOff c (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h).2
      · intro r hr c hc _
        exact old.dropLeft r (Finset.mem_sdiff.mp hr).1 c (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hr).2
      · intro r hr c hc _
        exact old.dropRight r (Finset.mem_sdiff.mp hr).1 c (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hc).2
    · rw [Function.update_of_ne e]
      exact goodShrink (state.good v hv) (minusSmall T _)
  · intro x hx y hy xy
    by_cases xw : x = w
    · subst x
      simp [Sep, Box.empty]
    by_cases yw : y = w
    · subst y
      simp [Sep, Box.empty]
    simpa [Function.update_of_ne xw, Function.update_of_ne yw] using state.sep x hx y hy xy

theorem composePreserves {G T U Z A B} (p : Preserves G T A U) (q : Preserves G U B Z) :
    Preserves G T (A.union B) Z := by
  intro r s c d h ht avoid
  obtain ⟨ha,hb⟩ := insideAvoidUnion avoid
  have u := p _ _ _ _ h ht ha
  exact q _ _ _ _ h u
    ⟨Finset.mem_sdiff.mpr ⟨u.rmem,(Finset.mem_sdiff.mp hb.rmem).2⟩,
     Finset.mem_sdiff.mpr ⟨u.smem,(Finset.mem_sdiff.mp hb.smem).2⟩,
     Finset.mem_sdiff.mpr ⟨u.cmem,(Finset.mem_sdiff.mp hb.cmem).2⟩,
     Finset.mem_sdiff.mpr ⟨u.dmem,(Finset.mem_sdiff.mp hb.dmem).2⟩⟩

theorem maybeDrop {T s L w G} (st : State T s L) (hw : w ∈ s) (det : Determines s G)
    (shL : TwinShield G) (shR : TwinShield (fun c r => G r c)) (rest : Finset W) :
    ∃ D U L', D.cost ≤ (if w ∈ rest then 2 else 0) ∧ Preserves G T D U ∧ State U s L' ∧
      (w ∈ rest → L' w = Box.empty) ∧ ∀ v, v ≠ w → L' v = L v := by
  by_cases keep : w ∈ rest
  · obtain ⟨D,hc,hp⟩ := paidPrune st hw det shL shR
    exact ⟨D,T.minus (L w),Function.update L w Box.empty,by simpa [keep] using hc,
      hp,dropState st hw,fun _ => Function.update_self _ _ _,fun _ h => Function.update_of_ne h _ _⟩
  · exact ⟨Box.empty,T,L,by simp [Box.empty,Box.cost],fun _ _ _ _ _ u _ => u, st,
      fun h => (keep h).elim, fun _ _ => rfl⟩

theorem combineState {T L a b z rest} (st : State T (insert a (insert b rest)) L)
    (ab : a ≠ b) (op : z ∈ joins a b) (fresh : z ∉ insert a (insert b rest))
    (ka : a ∈ rest → L a = Box.empty) (kb : b ∈ rest → L b = Box.empty) :
    State T (insert z rest) (Function.update L z ((L a).union (L b))) := by
  have a0 : a ∈ insert a (insert b rest) := by simp
  have b0 : b ∈ insert a (insert b rest) := by simp
  have mem {v} (h : v ∈ rest) : v ∈ insert a (insert b rest) := by simp [h]
  have nz {v} (h : v ∈ rest) : v ≠ z := fun e => fresh (e ▸ mem h)
  have sg (v) (h : v ∈ rest) : Sep ((L a).union (L b)) (L v) := by
    apply sepUnion
    · by_cases e : v = a
      · subst v; simp [ka h,Sep,Box.empty]
      · exact st.sep a a0 v (mem h) (Ne.symm e)
    · by_cases e : v = b
      · subst v; simp [kb h,Sep,Box.empty]
      · exact st.sep b b0 v (mem h) (Ne.symm e)
  constructor
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl|h
    · rw [Function.update_self]
      rcases (show v = both a b ∨ v = either a b by simpa [joins] using op) with rfl|rfl
      · exact bothGood (st.good a a0) (st.good b b0) (st.sep a a0 b b0 ab)
      · exact eitherGood (st.good a a0) (st.good b b0) (st.sep a a0 b b0 ab)
    · rw [Function.update_of_ne (nz h)]
      exact st.good _ (mem h)
  · intro v hv w hw dif
    rcases Finset.mem_insert.mp hv with h|h <;> rcases Finset.mem_insert.mp hw with j|j
    · exact (dif (h.trans j.symm)).elim
    · subst v
      simpa [Function.update_of_ne (nz j)] using sg w j
    · subst w
      simpa [Function.update_of_ne (nz h)] using sepSymm (sg v h)
    · simpa [Function.update_of_ne (nz h),Function.update_of_ne (nz j)] using st.sep v (mem h) w (mem j) dif

def NoPath (G : V → V → Prop) (T : Box) : Prop :=
  ∀ r s c d, Path4 G r s c d → Inside T r s c d → False

-- A retained operand is a copy. The cardinality of the live set counts
-- these copies exactly when the inequalities are summed through the chain.
theorem deletionFromChain {G} (sl : TwinShield G) (sr : TwinShield (fun c r => G r c))
    {gs s} (run : liveChain joins (output G) gs s) {T L} (st : State T s L) :
    ∃ D : Box, D.cost + 2*s.card ≤ 2*(gs.length+1) ∧ NoPath G (T.minus D) := by
  induction gs generalizing s T L with
  | nil =>
    change s = {output G} at run
    subst s
    refine ⟨Box.empty,by simp [Box.empty,Box.cost],?_⟩
    intro r s c d p h
    have i := insideSub (minusSmall T Box.empty) h
    have good := st.good (output G) (by simp)
    have core {r c} (a : r ∈ T.left) (b : c ∈ T.right) (e : G r c) : Core T (output G) r c :=
      ⟨a,b,e,id,id⟩
    exact p.sd (good.cluster (core i.rmem i.cmem p.rc) (core i.rmem i.dmem p.rd)
      (core i.smem i.cmem p.sc)).2.2.1
  | cons g gs ih =>
    have det := chainDetermines run
    rcases g with ⟨a,b,z⟩
    obtain ⟨ha,hb,ab,hz,fresh,rest,rfl,tail⟩ := run
    obtain ⟨A,U,LU,ca,pa,ua,ka,_⟩ := maybeDrop st ha det sl sr rest
    obtain ⟨B,Z,LZ,cb,pb,zb,kb,persist⟩ := maybeDrop ua hb det sl sr rest
    have ka' (h : a ∈ rest) : LZ a = Box.empty := (persist a ab).trans (ka h)
    obtain ⟨E,ce,clear⟩ := ih tail (combineState zb ab hz fresh ka' kb)
    have pab := composePreserves pa pb
    have zr : z ∉ rest := fun h => fresh (by simp [h])
    rw [Finset.card_insert_of_notMem zr] at ce
    refine ⟨(A.union B).union E,?_,?_⟩
    · have c1 := costUnion A B
      have c2 := costUnion (A.union B) E
      simp only [List.length_cons]
      by_cases ar : a ∈ rest <;> by_cases br : b ∈ rest <;>
        simp [ar,br,ab,Finset.card_insert_of_notMem] at ca cb ⊢ <;> omega
    · intro r s c d p avoid
      obtain ⟨x,y⟩ := insideAvoidUnion avoid
      have alku := insideSub (minusSmall T _) avoid
      have t := pab r s c d p alku x
      exact clear r s c d p
        ⟨Finset.mem_sdiff.mpr ⟨t.rmem,(Finset.mem_sdiff.mp y.rmem).2⟩,
         Finset.mem_sdiff.mpr ⟨t.smem,(Finset.mem_sdiff.mp y.smem).2⟩,
         Finset.mem_sdiff.mpr ⟨t.cmem,(Finset.mem_sdiff.mp y.cmem).2⟩,
         Finset.mem_sdiff.mpr ⟨t.dmem,(Finset.mem_sdiff.mp y.dmem).2⟩⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def zWord : W := fun _ _ => False
def tWord : W := fun _ _ => True
def leftWire (i : V) : W := fun r _ => r = some i
def rightWire (i : V) : W := fun _ c => c = some i
def inputWords : List W := List.ofFn leftWire ++ List.ofFn rightWire
def isAvailable (av : Finset W) (a : W) : Prop := a = zWord ∨ a = tWord ∨ a ∈ av
def nextValue (av : Finset W) (f : W) : Prop :=
  isAvailable av f ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ f ∈ joins a b

theorem combineAvailable {av : Finset W} {a b : W} (pa : isAvailable av a) (pb : isAvailable av b) :
    nextValue av (both a b) ∧ nextValue av (either a b) := by
  classical
  have equal {x y : W} (h : ∀ r c, x r c ↔ y r c) : x = y := funext fun r => funext fun c => propext (h r c)
  have hz (v : W) : both zWord v = zWord ∧ either zWord v = v ∧ both v zWord = zWord ∧ either v zWord = v := by
    exact ⟨equal (by simp [both,zWord]),equal (by simp [either,zWord]),equal (by simp [both,zWord]),equal (by simp [either,zWord])⟩
  have ht (v : W) : both tWord v = v ∧ either tWord v = tWord ∧ both v tWord = v ∧ either v tWord = tWord := by
    exact ⟨equal (by simp [both,tWord]),equal (by simp [either,tWord]),equal (by simp [both,tWord]),equal (by simp [either,tWord])⟩
  have zero : nextValue av zWord := Or.inl (Or.inl rfl)
  have one : nextValue av tWord := Or.inl (Or.inr (Or.inl rfl))
  rcases pa with h|h|ha
  · subst a; rw [(hz b).1,(hz b).2.1]; exact ⟨zero,Or.inl pb⟩
  · subst a; rw [(ht b).1,(ht b).2.1]; exact ⟨Or.inl pb,one⟩
  rcases pb with h|h|hb
  · subst b; rw [(hz a).2.2.1,(hz a).2.2.2]; exact ⟨zero,Or.inl (Or.inr (Or.inr ha))⟩
  · subst b; rw [(ht a).2.2.1,(ht a).2.2.2]; exact ⟨Or.inl (Or.inr (Or.inr ha)),one⟩
  by_cases eq : a = b
  · subst b
    have h₁ : both a a = a := equal (by simp [both])
    have h₂ : either a a = a := equal (by simp [either])
    rw [h₁,h₂]
    exact ⟨Or.inl (Or.inr (Or.inr ha)),Or.inl (Or.inr (Or.inr ha))⟩
  · exact ⟨Or.inr ⟨a,ha,b,hb,eq,by simp [joins]⟩,Or.inr ⟨a,ha,b,hb,eq,by simp [joins]⟩⟩

noncomputable def sample (r c : Option V) (v : W) : Bool := by classical exact decide (v r c)
def boolStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem sampleRead (w : List W) (i : ℕ) (r c : Option V) :
    (w.map (sample r c)).getD i false = sample r c (w.getD i zWord) := by
  classical
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt h),sample,zWord]

theorem readAv {av} (w : List W) (all : ∀ v ∈ w, isAvailable av v) (i : ℕ) :
    isAvailable av (w.getD i zWord) := by
  by_cases h : i < w.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using all w[i] (List.getElem_mem h)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h),isAvailable]

theorem liftGate {av} (w : List W) (all : ∀ v ∈ w, isAvailable av v) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ z, nextValue av z ∧ ∀ r c, boolStep (w.map (sample r c)) g = (w ++ [z]).map (sample r c) := by
  classical
  rcases g with ⟨op,args⟩
  obtain ⟨hop,hlen⟩ := legal
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl|rfl
    · exact ⟨tWord,Or.inl (Or.inr (Or.inl rfl)),by simp [boolStep,GateOp.eval,sample,tWord]; exact fun _ _ => @decide_eq_true True (Classical.propDecidable _) trivial⟩
    · exact ⟨zWord,Or.inl (Or.inl rfl),by simp [boolStep,GateOp.eval,sample,zWord]; exact fun _ _ => @decide_eq_false False (Classical.propDecidable _) id⟩
  | cons i tl =>
    cases tl with
    | nil =>
      rcases hop with rfl|rfl <;>
        exact ⟨_,Or.inl (readAv w all i),by intro r c; simp only [boolStep,List.map_cons,List.map_nil,sampleRead]; simp [GateOp.eval]⟩
    | cons j tl =>
      cases tl with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl|rfl
        · exact ⟨_,(combineAvailable (readAv w all i) (readAv w all j)).1, by
            intro r c; simp only [boolStep,List.map_cons,List.map_nil,sampleRead]; simp [GateOp.eval,sample,both]; apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true,decide_eq_true_eq]; exact (@decide_eq_true_iff _ (Classical.propDecidable _)).symm⟩
        · exact ⟨_,(combineAvailable (readAv w all i) (readAv w all j)).2, by
            intro r c; simp only [boolStep,List.map_cons,List.map_nil,sampleRead]; simp [GateOp.eval,sample,either]; apply Bool.eq_iff_iff.mpr; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact (@decide_eq_true_iff _ (Classical.propDecidable _)).symm⟩

theorem compile {goal : W} (nz : goal ≠ zWord) (nt : goal ≠ tWord) (gs : List Gate) (out : ℕ)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List W) (av : Finset W) (hw : ∀ v ∈ w, isAvailable av v)
    (he : ∀ r c, (gs.foldl boolStep (w.map (sample r c))).getD out false = sample r c goal) :
    build joins goal gs.length av := by
  classical
  induction gs generalizing w av with
  | nil =>
    have eq : w.getD out zWord = goal := by
      funext r c
      have h := he r c
      simp only [List.foldl_nil,sampleRead] at h
      simpa [sample] using h
    have v := readAv w hw out
    rw [eq] at v
    rcases v with f|f|f
    · exact (nz f).elim
    · exact (nt f).elim
    · exact f
  | cons g gs ih =>
    obtain ⟨z,hz,hs⟩ := liftGate w hw g (legal g (by simp))
    have fn := ih (fun b hb => legal b (by simp [hb])) (w ++ [z])
    have he' : ∀ r c, (gs.foldl boolStep ((w ++ [z]).map (sample r c))).getD out false = sample r c goal := by
      intro r c; simpa only [List.foldl_cons,hs] using he r c
    rcases hz with hz|⟨a,ha,b,hb,ab,hop⟩
    · apply Or.inl (fn av ?_ he')
      intro x hx
      rcases List.mem_append.mp hx with xw|xz
      · exact hw _ xw
      · simpa [List.mem_singleton.mp xz] using hz
    · refine Or.inr ⟨a,ha,b,hb,ab,z,hop,fn (insert z av) ?_ he'⟩
      intro x hx
      rcases List.mem_append.mp hx with xw|xz
      · exact (hw _ xw).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · exact Or.inr (Or.inr (by simp [List.mem_singleton.mp xz]))

noncomputable def truth (C : Circuit) : W := fun r c => C.eval (inputWords.map (sample r c)) = true

theorem actualSamples (r c : V) :
    inputWords.map (sample (some r) (some c)) = PEqualNP.Represents.oneEach r c := by
  classical
  simp [inputWords,PEqualNP.Represents.oneEach,sample,leftWire,rightWire,eq_comm]

theorem rowCorrect {C : Circuit} {G : V → V → Prop} [DecidableRel G]
    (hr : PEqualNP.Represents.Represents (fun a b => decide (G a b)) C) (r c : V) :
    truth C (some r) (some c) ↔ G r c := by
  simp only [truth,actualSamples, hr r c,decide_eq_true_eq]

theorem inputCases {w} (hw : w ∈ inputWords.toFinset) : (∃ r, w = leftWire r) ∨ (∃ c, w = rightWire c) := by
  simpa only [Finset.mem_coe, List.mem_toFinset,inputWords,List.mem_append,List.mem_ofFn,eq_comm] using hw

noncomputable def initialLabel (w : W) : Box := by
  classical
  exact ⟨Finset.univ.filter (fun r => w = leftWire r),Finset.univ.filter (fun c => w = rightWire c)⟩

def full : Box := ⟨Finset.univ,Finset.univ⟩

theorem initialState {s : Finset W} (sub : s ⊆ inputWords.toFinset) : State full s initialLabel := by
  classical
  constructor
  · intro w hw
    rcases inputCases (sub hw) with ⟨i,rfl⟩|⟨i,rfl⟩
    · refine ⟨by simp [leftWire], ?_, by simp [leftWire], ?_, by simp [leftWire], ?_⟩
      · intro r _ off eq
        have ri : r = i := Option.some.inj eq
        exact off (by simp [ri,initialLabel])
      · intro r _ c _ off
        have ri : r ≠ i := fun h => off (by simp [h,initialLabel])
        simp [leftWire,ri]
      · intro r s c d h
        exact (h.2.2.2.1 h.2.2.1).elim
    · refine ⟨by simp [rightWire], by simp [rightWire], ?_, by simp [rightWire], ?_, ?_⟩
      · intro c _ off eq
        have ci : c = i := Option.some.inj eq
        exact off (by simp [ci,initialLabel])
      · intro r _ c _ off
        have ci : c ≠ i := fun h => off (by simp [h,initialLabel])
        simp [rightWire,ci]
      · intro r s c d h
        exact (h.2.2.2.2 h.2.2.1).elim
  · intro a _ b _ ab
    constructor <;> apply Finset.disjoint_left.mpr <;> intro i p q <;>
      simp only [initialLabel,Finset.mem_filter,Finset.mem_univ,true_and] at p q <;> exact ab (p.trans q.symm)

theorem mainBound {G : V → V → Prop} [DecidableRel G] (diag : ∀ i, ¬G i i)
    (posL : ∀ i, ∃ j, G i j) (posR : ∀ j, ∃ i, G i j)
    (sl : TwinShield G) (sr : TwinShield (fun c r => G r c))
    (deletions : ∀ D, NoPath G (full.minus D) → 18 ≤ D.cost) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun r c => decide (G r c)) 61 := by
  rintro ⟨C,hg,small,hr⟩
  classical
  have correct := rowCorrect hr
  have nz : truth C ≠ zWord := by
    obtain ⟨j,hj⟩ := posL 0
    intro e
    have h := (correct 0 j).mpr hj
    rwa [e] at h
  have nt : truth C ≠ tWord := by
    intro e
    exact diag 0 ((correct 0 0).mp (by rw [e]; trivial))
  have checked : build joins (truth C) C.gates.length inputWords.toFinset :=
    compile nz nt C.gates C.output hg inputWords inputWords.toFinset
      (fun x h => Or.inr (Or.inr (List.mem_toFinset.mpr h))) (by
        intro r c; change C.eval _ = sample r c (truth C); apply Bool.eq_iff_iff.mpr; simp only [sample,truth]; exact (@decide_eq_true_iff _ (Classical.propDecidable _)).symm)
  obtain ⟨gs,hlen,s,sub,chain⟩ := compress_chain checked
  have bothDiffer (r c r' c' : Option V) (hd : truth C r c ∧ ¬truth C r' c') :
      ∃ w ∈ s, w r c ∧ ¬w r' c' := by
    apply chain_separates (fun w : W => w r c ∧ ¬w r' c') hd _ chain
    intro a b z hz h
    rcases (show z = both a b ∨ z = either a b by simpa [joins] using hz) with rfl|rfl
    · unfold both at h; tauto
    · unfold either at h; tauto
  have neg (i : V) : ¬truth C (some i) (some i) := fun h => diag i ((correct i i).mp h)
  have emptyRows (i : V) : ¬truth C (some i) none := by
    intro h
    obtain ⟨w,hw,p,n⟩ := bothDiffer _ _ _ _ ⟨h,neg i⟩
    rcases inputCases (sub hw) with ⟨k,rfl⟩|⟨k,rfl⟩ <;> simp_all [leftWire,rightWire]
  have emptyCols (j : V) : ¬truth C none (some j) := by
    intro h
    obtain ⟨w,hw,p,n⟩ := bothDiffer _ _ _ _ ⟨h,neg j⟩
    rcases inputCases (sub hw) with ⟨k,rfl⟩|⟨k,rfl⟩ <;> simp_all [leftWire,rightWire]
  have empty : ¬truth C none none := by
    intro h
    obtain ⟨w,hw,p,n⟩ := bothDiffer _ _ _ _ ⟨h,neg 0⟩
    rcases inputCases (sub hw) with ⟨k,rfl⟩|⟨k,rfl⟩ <;> simp_all [leftWire,rightWire]
  have allL (i : V) : leftWire i ∈ s := by
    obtain ⟨j,hj⟩ := posL i
    obtain ⟨w,hw,p,n⟩ := bothDiffer _ _ _ _ ⟨(correct i j).mpr hj, neg j⟩
    rcases inputCases (sub hw) with ⟨k,rfl⟩|⟨k,rfl⟩
    · have ik : i = k := Option.some.inj p
      simpa [ik] using hw
    · exact (n p).elim
  have allR (j : V) : rightWire j ∈ s := by
    obtain ⟨i,hi⟩ := posR j
    obtain ⟨w,hw,p,n⟩ := bothDiffer _ _ _ _ ⟨(correct i j).mpr hi, neg i⟩
    rcases inputCases (sub hw) with ⟨k,rfl⟩|⟨k,rfl⟩
    · exact (n p).elim
    · have jk : j = k := Option.some.inj p
      simpa [jk] using hw
  let inj : V ⊕ V → (↑s : Type) := Sum.elim (fun i => ⟨leftWire i,allL i⟩) (fun i => ⟨rightWire i,allR i⟩)
  have hinj : Function.Injective inj := by
    intro a b eq
    have w := congrArg Subtype.val eq
    cases a with
    | inl i =>
      have test := congrFun (congrFun w (some i)) none
      cases b with
      | inl j => simp [inj,leftWire] at test; simp [test]
      | inr j => simp [inj,leftWire,rightWire] at test
    | inr i =>
      have test := congrFun (congrFun w none) (some i)
      cases b with
      | inl j => simp [inj,rightWire,leftWire] at test
      | inr j => simp [inj,rightWire] at test; simp [test]
  have card : 54 ≤ s.card := by simpa using Fintype.card_le_of_injective inj hinj
  have equals : truth C = output G := by
    funext r c
    cases r with
    | none => cases c with
      | none => exact propext (iff_of_false empty id)
      | some j => exact propext (iff_of_false (emptyCols j) id)
    | some i => cases c with
      | none => exact propext (iff_of_false (emptyRows i) id)
      | some j => exact propext (correct i j)
  rw [equals] at chain
  obtain ⟨D,cost,nopath⟩ := deletionFromChain sl sr chain (initialState sub)
  have lower := deletions D nopath
  change C.gates.length ≤ 61 at small
  omega

-- Rows of the posted relation as 27-bit neighbor masks.
def nbr (i : V) : BitVec 27 := BitVec.ofNat 27 (0x80400008040000804000080400008040000804000080400008040000806000000a000100200010020001002000100200010020001002000100200014010081401028040102804010280401028040102804010280401028060102 >>> (27*i.val))
def graph (i j : V) : Prop := (nbr i)[j.val] = true
instance graphDec : DecidableRel graph := fun _ _ => inferInstanceAs (Decidable (_ = true))
def chooseShield (i j : V) : V := Fin.ofNat 27 ((0x200000000001000000002000000000000001c0000000380e0000000000000000000000180000000300c0000000000000000000000140000000280a0000000000000000000000100000000200800000000000000000000000c0000000180600000000000000000000000800000001004000000000000000000000004000000008020000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000400000000801c00000000000000000000e0380000000001800000000000000000000c0300000000001400000000000000000000a028000000000100000000000000000000080200000000000c00000000000000000000601800000000008000000000000000000004010000000000040000000000000000000020080e00000000000380000000001c0000000400c0000000010030000000000180000100380a000000000e02800001c0001400000003008000000000c0200000180001000000002806000000000a0180000140000c0000000200400000000080100000100000800000001802000000000600800000c000040000000100000000000040000000080002000000000800800000000204000000400 >>> (5*(27*i.val+j.val))) % 32)
def twoBits (i j : V) : BitVec 27 := ((1 : BitVec 27) <<< i.val) ||| ((1 : BitVec 27) <<< j.val)
theorem graphSym : ∀ i j, graph i j ↔ graph j i := by decide +kernel
theorem graphDiag : ∀ i, ¬graph i i := by decide +kernel
theorem graphNeighbors : ∀ i, ∃ j, graph i j := by decide +kernel
theorem shieldsWork : ∀ i j y : V, i ≠ j → y ≠ chooseShield i j → graph i y → graph j y →
    nbr y = twoBits i j := by decide +kernel
theorem twoOnly : ∀ i j x : V, (twoBits i j)[x.val] = true → x = i ∨ x = j := by decide +kernel

theorem graphShield : TwinShield graph := by
  intro i j ij
  refine ⟨chooseShield i j,?_⟩
  intro y yne p q x xy
  have yx : (nbr y)[x.val] = true := (graphSym x y).mp xy
  rw [shieldsWork i j y ij yne p q] at yx
  exact twoOnly i j x yx

abbrev Cell := Fin 18
abbrev Mask := Fin 8

def vertex (t : Cell) (k : Fin 3) : V ⊕ V :=
  let label := Fin.ofNat 27 (t.val % 9 + (if k.val = 0 then 0 else if k.val = 1 then 18 else 9))
  if (t.val % 2 = 0) = (k.val ≠ 1) then Sum.inl label else Sum.inr label

def selected (D : Box) : V ⊕ V → Bool
  | .inl r => decide (r ∈ D.left)
  | .inr c => decide (c ∈ D.right)

def mkMask (a b c : Bool) : Mask := ⟨a.toNat + 2*b.toNat + 4*c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩
def cellMask (D : Box) (t : Cell) : Mask :=
  mkMask (selected D (vertex t 0)) (selected D (vertex t 1)) (selected D (vertex t 2))
def countBits (a : Mask) : ℕ := (#[0,1,1,2,1,2,2,3] : Array ℕ)[a.val]?.getD 0
-- The potential is stored as one two-bit value per triple of deletion masks.
def pot (a b c : Mask) : ℕ := (0xfffefffefffefffefffefffefffefee9fffefffefffefffefffefffefffefee9fffefffefffefffefffefffefffefee9fffefffefffefffefffefffefffefee9fffefffefffefffefffefffefffefee9fffefffefffefffefffefffefee9fee9fffefffefffefee9fffefee9fee9e994fffefffefffefee9fffefee9fee9e994 >>> (2*(64*a.val + 8*b.val + c.val))) % 4

def patterns : List ℕ := [27, 75, 57, 105, 201, 585, 30, 78, 60, 108, 204, 588]
def packed (a b c d : Mask) : ℕ :=
  a.val ||| (b.val <<< 3) ||| (c.val <<< 6) ||| (d.val <<< 9)
def hitsAll (a b c d : Mask) : Bool := patterns.all (fun p => p &&& packed a b c d != 0)

def bitVertex (t : Cell) (j : Fin 12) : V ⊕ V :=
  vertex (t + Fin.ofNat 18 (j.val/3)) (Fin.ofNat 3 j.val)
def position (t : Cell) (k : Fin 12) (n : Fin 4) : Fin 12 :=
  Fin.ofNat 12 ((0x269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340269326732653245362134213069306730653045360134013932673265326532413621342930673065306530413601340 >>> (4*(48*t.val+4*k.val+n.val))) % 16)
def vertexLabel : V ⊕ V → V := Sum.elim id id
def point (t : Cell) (k : Fin 12) (n : Fin 4) : V :=
  vertexLabel (bitVertex t (position t k n))

theorem patternCert : ∀ t : Cell, ∀ k : Fin 12,
    let v := point t k
    (bitVertex t (position t k 0) = Sum.inl (v 0) ∧ bitVertex t (position t k 1) = Sum.inl (v 1) ∧
     bitVertex t (position t k 2) = Sum.inr (v 2) ∧ bitVertex t (position t k 3) = Sum.inr (v 3)) ∧
    (graph (v 0) (v 2) ∧ graph (v 0) (v 3) ∧ graph (v 1) (v 2) ∧ ¬graph (v 1) (v 3)) ∧
    (∀ n : Fin 4, (patterns.getD k.val 0).testBit (position t k n).val = true) := by decide +kernel

theorem mkMaskBit0 : ∀ a b c, (mkMask a b c).val.testBit 0 = a := by decide
theorem mkMaskBit1 : ∀ a b c, (mkMask a b c).val.testBit 1 = b := by decide
theorem mkMaskBit2 : ∀ a b c, (mkMask a b c).val.testBit 2 = c := by decide
theorem mkMaskHigh (m : Mask) (j : ℕ) (hj : 3 ≤ j) : m.val.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  have hpow : 2^3 ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
  omega

theorem maskModTwo : ∀ a b c, decide ((mkMask a b c).val % 2 = 1) = a := by decide

theorem bitSelected (D : Box) (t : Cell) (j : Fin 12) :
    (packed (cellMask D t) (cellMask D (t+1)) (cellMask D (t+2)) (cellMask D (t+3))).testBit j.val =
      selected D (bitVertex t j) := by
  fin_cases j <;> simp only [packed,Nat.testBit_or,Nat.testBit_shiftLeft] <;>
    norm_num [bitVertex, cellMask, Nat.testBit_or, Nat.testBit_shiftLeft, mkMaskBit0, mkMaskBit1, mkMaskBit2,
      mkMaskHigh _ _ (by decide : 3 ≤ 3), mkMaskHigh _ _ (by decide : 3 ≤ 4),
      mkMaskHigh _ _ (by decide : 3 ≤ 5), mkMaskHigh _ _ (by decide : 3 ≤ 6),
      mkMaskHigh _ _ (by decide : 3 ≤ 7), mkMaskHigh _ _ (by decide : 3 ≤ 8),
      mkMaskHigh _ _ (by decide : 3 ≤ 9), mkMaskHigh _ _ (by decide : 3 ≤ 10),
      mkMaskHigh _ _ (by decide : 3 ≤ 11), maskModTwo] <;> rfl

theorem coversMasks (D : Box) (clear : NoPath graph (full.minus D)) (t : Cell) :
    hitsAll (cellMask D t) (cellMask D (t+1)) (cellMask D (t+2)) (cellMask D (t+3)) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨k,hl,eq⟩ := List.getElem_of_mem hp
  let idx : Fin 12 := ⟨k,hl⟩
  obtain ⟨⟨r0,r1,c0,c1⟩,⟨a,b,c,d⟩,mem⟩ := patternCert t idx
  apply bne_iff_ne.mpr
  intro bad
  have avoid (n : Fin 4) : selected D (bitVertex t (position t idx n)) = false := by
    rw [← bitSelected]
    have zero := congrArg (fun q : ℕ => q.testBit (position t idx n).val) bad
    have ip : patterns.getD idx.val 0 = p := by
      simp [idx,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,eq]
    have bit := mem n
    rw [ip] at bit
    simpa only [Nat.testBit_and,bit,Bool.true_and,Nat.zero_testBit] using zero
  have v0 := avoid 0
  have v1 := avoid 1
  have v2 := avoid 2
  have v3 := avoid 3
  rw [r0] at v0
  rw [r1] at v1
  rw [c0] at v2
  rw [c1] at v3
  apply clear _ _ _ _ ⟨a,b,c,d⟩
  simp only [selected,decide_eq_false_iff_not] at v0 v1 v2 v3
  exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,v0⟩,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,v1⟩,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,v2⟩,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,v3⟩⟩

def vertexFn (p : Cell × Fin 3) : V ⊕ V := vertex p.1 p.2
theorem vertexBij : Function.Bijective vertexFn := by
  change (∀ a b, vertexFn a = vertexFn b → a = b) ∧ ∀ y, ∃ p, vertexFn p = y
  decide +kernel

theorem maskCharge : ∀ a b c, countBits (mkMask a b c) = a.toNat + b.toNat + c.toNat := by decide

theorem countDeleted (D : Box) : (∑ i : Cell, countBits (cellMask D i)) = D.cost := by
  classical
  let e := Equiv.ofBijective vertexFn vertexBij
  calc
    _ = ∑ p : Cell × Fin 3, (selected D (vertexFn p)).toNat := by
      simp [Fintype.sum_prod_type,Fin.sum_univ_three,cellMask,vertexFn,maskCharge,add_assoc]
    _ = ∑ v : V ⊕ V, (selected D v).toNat := Equiv.sum_comp e (fun v => (selected D v).toNat)
    _ = _ := by rw [Fintype.sum_sum_type]; simp [selected,Bool.toNat,Box.cost]

private theorem stepAt0 : ∀ b c d : Mask, hitsAll 0 b c d = true →
    1 + pot b c d ≤ countBits d + pot 0 b c := by decide +kernel

private theorem stepAt1 : ∀ b c d : Mask, hitsAll 1 b c d = true →
    1 + pot b c d ≤ countBits d + pot 1 b c := by decide +kernel

private theorem stepAt2 : ∀ b c d : Mask, hitsAll 2 b c d = true →
    1 + pot b c d ≤ countBits d + pot 2 b c := by decide +kernel

private theorem stepAt3 : ∀ b c d : Mask, hitsAll 3 b c d = true →
    1 + pot b c d ≤ countBits d + pot 3 b c := by decide +kernel

private theorem stepAt4 : ∀ b c d : Mask, hitsAll 4 b c d = true →
    1 + pot b c d ≤ countBits d + pot 4 b c := by decide +kernel

private theorem stepAt5 : ∀ b c d : Mask, hitsAll 5 b c d = true →
    1 + pot b c d ≤ countBits d + pot 5 b c := by decide +kernel

private theorem stepAt6 : ∀ b c d : Mask, hitsAll 6 b c d = true →
    1 + pot b c d ≤ countBits d + pot 6 b c := by decide +kernel

private theorem stepAt7 : ∀ b c d : Mask, hitsAll 7 b c d = true →
    1 + pot b c d ≤ countBits d + pot 7 b c := by decide +kernel

private theorem stepBound : ∀ a b c d : Mask, hitsAll a b c d = true →
    1 + pot b c d ≤ countBits d + pot a b c := by
  intro a
  fin_cases a <;> first | exact stepAt0 | exact stepAt1 | exact stepAt2 | exact stepAt3 | exact stepAt4 | exact stepAt5 | exact stepAt6 | exact stepAt7

private theorem shiftSum (f : Cell → ℕ) (d : Cell) :
    (∑ i : Cell, f (i+d)) = ∑ i : Cell, f i := by
  exact Equiv.sum_comp (Equiv.addRight d) f

theorem eighteenDeletions (m : Cell → Mask)
    (hits : ∀ i : Cell, hitsAll (m i) (m (i+1)) (m (i+2)) (m (i+3)) = true) :
    18 ≤ ∑ i : Cell, countBits (m i) := by
  let p (i : Cell) := pot (m i) (m (i+1)) (m (i+2))
  have bound (i : Cell) : 1 + p (i+1) ≤ countBits (m (i+3)) + p i := by
    have h := stepBound _ _ _ _ (hits i)
    simpa [p, add_assoc] using h
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset Cell)) (fun i _ => bound i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at total
  rw [shiftSum p 1, shiftSum (fun i => countBits (m i)) 3] at total
  omega


theorem graphDeletions (D : Box) (clear : NoPath graph (full.minus D)) : 18 ≤ D.cost := by
  rw [← countDeleted]
  exact eighteenDeletions (cellMask D) (coversMasks D clear)

theorem reverseShield : TwinShield (fun c r => graph r c) := by
  have h : (fun c r => graph r c) = graph := funext fun c => funext fun r => propext (graphSym r c)
  rw [h]
  exact graphShield

def posted : V → V → Bool := fun a b : Fin 27 => decide (∃ i : Fin 9, ((a.val = i.val ∨ a.val = 9 + i.val) ∧ (b.val = (i.val + 1) % 9 ∨ b.val = 18 + i.val)) ∨ ((b.val = i.val ∨ b.val = 9 + i.val) ∧ (a.val = (i.val + 1) % 9 ∨ a.val = 18 + i.val)))

theorem agrees : ∀ a b, decide (graph a b) = posted a b := by decide +kernel

theorem answer : ¬ PEqualNP.Represents.RepSizeAtMost posted 61 := by
  have eq : (fun a b => decide (graph a b)) = posted := funext fun a => funext (agrees a)
  rw [← eq]
  exact mainBound graphDiag graphNeighbors
    (fun j => (graphNeighbors j).imp (fun i h => (graphSym j i).mp h))
    graphShield reverseShield graphDeletions

end PEqualNP.Outside.L_meta_9498

theorem PEqualNP.Outside.L_meta_9498 : ¬ PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 27 => decide (∃ i : Fin 9, ((a.val = i.val ∨ a.val = 9 + i.val) ∧ (b.val = (i.val + 1) % 9 ∨ b.val = 18 + i.val)) ∨ ((b.val = i.val ∨ b.val = 9 + i.val) ∧ (a.val = (i.val + 1) % 9 ∨ a.val = 18 + i.val)))) 60 := by
  rintro ⟨C, mono, size, represents⟩
  exact PEqualNP.Outside.L_meta_9498.answer ⟨C, mono, by omega, represents⟩
