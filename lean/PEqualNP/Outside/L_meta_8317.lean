import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8317

variable {n : ℕ} {G : SimpleGraph (Fin n)}

lemma noTriangle
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a u v : Fin n} (hau : G.Adj a u) (huv : G.Adj u v) (hva : G.Adj v a) : False := by
  let p := SimpleGraph.Walk.cons hau (SimpleGraph.Walk.cons huv
    (SimpleGraph.Walk.cons hva SimpleGraph.Walk.nil))
  have hc : p.IsCycle := by
    dsimp [p]
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff, huv.ne, hva.ne, hau.ne.symm]
    · simp [hau.ne, hau.ne.symm, huv.ne, hva.ne.symm]
  have h := girth a p hc
  simp [p] at h

lemma noSquare
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a u v b : Fin n} (hau : G.Adj a u) (huv : G.Adj u v) (hvb : G.Adj v b)
    (hba : G.Adj b a) (hub : u ≠ b) (hva : v ≠ a) : False := by
  let p := SimpleGraph.Walk.cons hau (SimpleGraph.Walk.cons huv
    (SimpleGraph.Walk.cons hvb (SimpleGraph.Walk.cons hba SimpleGraph.Walk.nil)))
  have hc : p.IsCycle := by
    dsimp [p]
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff, huv.ne, hvb.ne, hba.ne, hub, hva, hau.ne.symm]
    · simp [hau.ne, hau.ne.symm, huv.ne, hba.ne.symm, hub, hva.symm]
  have h := girth a p hc
  simp [p] at h

def border (G : SimpleGraph (Fin n)) (a b w : Fin n) : Prop :=
  (G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b

lemma border_independent
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a b u v : Fin n} (hab : a = b ∨ G.Adj a b)
    (hu : border G a b u) (hv : border G a b v) (huv : G.Adj u v) : False := by
  rcases hu with ⟨hu, hua, hub⟩
  rcases hv with ⟨hv, hva, hvb⟩
  rcases hab with rfl | hab
  · simp only [or_self] at hu hv
    exact noTriangle girth hu huv hv.symm
  · rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact noTriangle girth hu huv hv.symm
    · exact noSquare girth hu huv hv.symm hab.symm hub hva
    · exact noSquare girth hu huv hv.symm hab hua hvb
    · exact noTriangle girth hu huv hv.symm

lemma short_border_walk {a b u v : Fin n} (hab : a = b ∨ G.Adj a b)
    (hu : border G a b u) (hv : border G a b v) :
    ∃ p : G.Walk u v, p.length ≤ 3 := by
  have same {c} (huc : G.Adj c u) (hvc : G.Adj c v) :
      ∃ p : G.Walk u v, p.length ≤ 3 :=
    ⟨SimpleGraph.Walk.cons huc.symm (SimpleGraph.Walk.cons hvc SimpleGraph.Walk.nil), by simp⟩
  have cross {c d} (huc : G.Adj c u) (hcd : G.Adj c d) (hvd : G.Adj d v) :
      ∃ p : G.Walk u v, p.length ≤ 3 :=
    ⟨SimpleGraph.Walk.cons huc.symm (SimpleGraph.Walk.cons hcd
      (SimpleGraph.Walk.cons hvd SimpleGraph.Walk.nil)), by simp⟩
  have hu' := hu.1
  have hv' := hv.1
  rcases hab with rfl | hab
  · simp only [or_self] at hu' hv'
    exact same hu' hv'
  · rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact same hu' hv'
    · exact cross hu' hab hv'
    · exact cross hu' hab.symm hv'
    · exact same hu' hv'

noncomputable def negative (G : SimpleGraph (Fin n)) (a b w : Fin n) : Bool := by
  classical
  exact decide (border G a b w)

lemma negative_true {a b w : Fin n} :
    negative G a b w = true ↔ border G a b w := by
  simp [negative]

def positive (u v w : Fin n) : Bool := w == u || w == v

lemma positive_true {u v w : Fin n} : positive u v w = true ↔ w = u ∨ w = v := by
  simp [positive]

def setMarked (x : Fin n → Bool) (mark : Option (Fin n)) : Fin n → Bool :=
  match mark with
  | none => x
  | some w => Function.update x w true

lemma setMarked_preserves {x : Fin n → Bool} {i : Fin n} (m : Option (Fin n))
    (hi : x i = true) : setMarked x m i = true := by
  cases m with
  | none => exact hi
  | some w =>
    by_cases h : i = w
    · subst i
      simp [setMarked]
    · simp [setMarked, Function.update_of_ne h, hi]

lemma setMarked_agrees {x y : Fin n → Bool} {i : Fin n} {m : Option (Fin n)}
    (hm : ∀ w, m = some w → y w = true) (hi : y i ≠ true) :
    setMarked x m i = x i := by
  cases m with
  | none => rfl
  | some w =>
    have hne : i ≠ w := fun h => hi (h ▸ hm w rfl)
    exact Function.update_of_ne hne true x

noncomputable def marker (S : Finset (Fin n)) (y : Fin n → Bool) : Option (Fin n) := by
  classical
  exact if h : ∃ w ∈ S, y w = true then some (Classical.choose h) else none

lemma marker_spec (S : Finset (Fin n)) (y : Fin n → Bool) :
    (∀ w, marker S y = some w → w ∈ S ∧ y w = true) ∧
    (marker S y = none → ∀ w ∈ S, y w ≠ true) := by
  classical
  unfold marker
  split
  next h =>
    constructor
    · intro w hw
      exact Option.some.inj hw ▸ Classical.choose_spec h
    · simp
  next h =>
    constructor
    · simp
    · exact fun _ w hw ht => h ⟨w, hw, ht⟩

def restrictMarker (D : Finset (Fin n)) (m : Option (Fin n)) : Option D :=
  match m with
  | none => none
  | some w => if h : w ∈ D then some ⟨w, h⟩ else none

lemma keeps_positive {f g : (Fin n → Bool) → Bool}
    (S : Finset (Fin n))
    (h : ∀ x, g x = f x ∨ g x = true ∧
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ x u = true ∧ x v = true)
    {x : Fin n → Bool} (hx : f x = true) : g x = true := by
  rcases h x with he | he
  · exact he.trans hx
  · exact he.1

end PEqualNP.Outside.L_meta_8317

open PEqualNP.Outside.L_meta_8317

theorem PEqualNP.Outside.L_meta_8317 :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Fin x1) (x5 : (Fin x1 → Bool) → Bool),   (∀ (x6 : Fin x1) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →     (∀ (x7 : Fin x1 → Bool), x5 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →       (∃ (x8 : Finset (Fin x1)) (x9 : (Fin x1 → Bool) → Bool) (x10 : ℕ) (x11 : Fin x10 → (Fin x1 → Bool) → Bool) (x12 : Fin x10 → (Fin x1 → Bool) → Bool) (x13 : Fin x10 → ℕ) (x14 : Fin x10 → Bool) (x15 : Fin x10 → Finset (Fin x1)),           PEqualNP.MetaComplexity.IsLiteralPartition x1 x9 x10 x11 x12 x13 x14 ∧             (∀ (x16 : Fin x1 → Bool), x9 x16 = x5 x16 ∨ x9 x16 = Bool.true ∧ ∃ x17 ∈ x8, ∃ x18 ∈ x8, x17 ≠ x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) ∧               (∀ (x16 : Fin x10), x14 x16 = Bool.false → ∃ x18 ∈ x8, x13 x16 = ↑x18) ∧                 (∀ x16 ∈ x8, ∀ x18 ∈ x8, x16 ≠ x18 → ∀ (x21 : x3.Walk x16 x18), (3 : ℕ) < x21.length) ∧                   (∀ (x16 : Fin x10),                       x14 x16 = Bool.true →                         ∀ x18 ∈ x8,                           x18 ∉ x15 x16 →                             ∀ (x21 x22 : Fin x1),                               x3.Adj x21 x22 →                                 have x24 : Fin x1 → Bool := fun (x24 : Fin x1) => x24 == x21 || x24 == x22;                                 x11 x16 (Function.update x24 x18 Bool.true) = x11 x16 x24) ∧                     ∑ x16 : { x16 : Fin x10 // x14 x16 = Bool.true }, ((1 : ℕ) + (x15 ↑x16).card) ≤ x2) →         ∃ (x9 : Fin x2 → Fin x1 → Fin x1 → Prop) (x10 : Fin x2 → Fin x1 → Fin x1 → Prop) (x11 : Fin x2 → Fin x1), ∀ (x12 x13 x14 x15 : Fin x1), x3.Adj x12 x13 → x14 = x15 ∨ x3.Adj x14 x15 → (∃! x18 : Fin x2, x9 x18 x12 x13 ∧ x10 x18 x14 x15) ∧ ∀ (x18 : Fin x2), x9 x18 x12 x13 → x10 x18 x14 x15 → (x11 x18 = x12 ∨ x11 x18 = x13) ∧ ¬((x3.Adj x14 (x11 x18) ∨ x3.Adj x15 (x11 x18)) ∧ x11 x18 ≠ x14 ∧ x11 x18 ≠ x15) := by
  classical
  intro n m G z f girth hf hyp
  obtain ⟨S, g, k, A, B, pos, bit, D, part, hg, hneg, separated, invariant, budget⟩ := hyp
  have hcol {a b : Fin n} (hab : a = b ∨ G.Adj a b) :
      g (negative G a b) = false ∧
      ∀ u ∈ S, ∀ v ∈ S, negative G a b u = true → negative G a b v = true → u = v := by
    have hunique : ∀ u ∈ S, ∀ v ∈ S,
        negative G a b u = true → negative G a b v = true → u = v := by
      intro u hu v hv hnu hnv
      by_contra hne
      obtain ⟨p, hp⟩ := short_border_walk hab (negative_true.mp hnu) (negative_true.mp hnv)
      exact (Nat.not_lt_of_ge hp) (separated u hu v hv hne p)
    have hfalse : f (negative G a b) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨u, v, huv, hu, hv⟩ := (hf _).mp ht
      exact border_independent girth hab (negative_true.mp hu) (negative_true.mp hv) huv
    refine ⟨?_, hunique⟩
    rcases hg (negative G a b) with he | ⟨_, u, hu, v, hv, hne, hnu, hnv⟩
    · exact he.trans hfalse
    · exact (hne (hunique u hu v hv hnu hnv)).elim
  let J := {j : Fin k // bit j = true}
  let T := Σ j : J, Option (D j.val)
  let row (t : T) (u v : Fin n) : Prop :=
    A t.1.val (setMarked (positive u v) (t.2.map Subtype.val)) = true
  let col (t : T) (a b : Fin n) : Prop :=
    B t.1.val (negative G a b) = true ∧
      t.2 = restrictMarker (D t.1.val) (marker S (negative G a b))
  let label (t : T) : Fin n :=
    if h : pos t.1.val < n then ⟨pos t.1.val, h⟩ else z
  have hcard : Fintype.card T ≤ m := by
    simpa [T, J, Fintype.card_sigma, Fintype.card_option, Fintype.card_coe, Nat.add_comm]
      using budget
  let embed : T ↪ Fin m := (Fintype.equivFin T).toEmbedding.trans (Fin.castLEEmb hcard)
  let R (r : Fin m) (u v : Fin n) : Prop := ∃ t : T, embed t = r ∧ row t u v
  let C := Function.extend (⇑embed) col (fun _ _ _ => False)
  let L := Function.extend (⇑embed) label (fun _ => z)
  have hC (t : T) : C (embed t) = col t := embed.injective.extend_apply _ _ _
  have hL (t : T) : L (embed t) = label t := embed.injective.extend_apply _ _ _
  refine ⟨R, C, L, ?_⟩
  intro u v a b huv hab
  let y := negative G a b
  let mk := marker S y
  let x := setMarked (positive u v) mk
  obtain ⟨hy, hunique⟩ := hcol hab
  obtain ⟨selected, absent⟩ := marker_spec S y
  have hmark (w : Fin n) (hw : w ∈ S) (hwy : y w = true) : mk = some w := by
    cases hm : mk with
    | none => exact (absent hm w hw hwy).elim
    | some t =>
      have hs := selected t hm
      exact congrArg some (hunique t hs.1 w hw hs.2 hwy)
  have hx : g x = true :=
    keeps_positive S hg ((hf x).mpr ⟨u, v, huv,
      setMarked_preserves mk (positive_true.mpr (Or.inl rfl)),
      setMarked_preserves mk (positive_true.mpr (Or.inr rfl))⟩)
  have hA (j : J) :
      A j.val (setMarked (positive u v)
        ((restrictMarker (D j.val) mk).map Subtype.val)) = A j.val x := by
    cases hm : mk with
    | none => simp [x, hm, restrictMarker]
    | some w =>
      by_cases hd : w ∈ D j.val
      · simp [x, hm, restrictMarker, hd]
      · have hi := invariant j.val j.property w (selected w hm).1 hd u v huv
        simp only [x, hm, restrictMarker, dite_eq_right hd, Option.map_none, setMarked]
        exact hi.symm
  have hit (t : T) : (row t u v ∧ col t a b) ↔
      A t.1.val x = true ∧ B t.1.val y = true ∧
        t.2 = restrictMarker (D t.1.val) mk := by
    rcases t with ⟨j, o⟩
    change (A j.val (setMarked (positive u v) (o.map Subtype.val)) = true ∧
      B j.val y = true ∧ o = restrictMarker (D j.val) mk) ↔
      A j.val x = true ∧ B j.val y = true ∧ o = restrictMarker (D j.val) mk
    constructor
    · rintro ⟨hr, hb, rfl⟩
      exact ⟨(hA j).symm.trans hr, hb, rfl⟩
    · rintro ⟨hr, hb, rfl⟩
      exact ⟨(hA j).trans hr, hb, rfl⟩
  obtain ⟨j, hj, huniq⟩ := part.2.2.2 x y hx hy
  have hjpos : bit j = true := by
    by_contra h
    have hfalse : bit j = false := Bool.eq_false_iff.mpr h
    obtain ⟨w, hw, hpw⟩ := hneg j hfalse
    obtain ⟨i, hpi, hxi, hyi⟩ := part.2.2.1 j x y hj.1 hj.2
    have hiw : i = w := Fin.ext (hpi.symm.trans hpw)
    subst i
    have hwy : y w = true := by
      cases hval : y w with
      | false => exact (hyi (hval.trans hfalse.symm)).elim
      | true => rfl
    have hxw : x w = true := by simp [x, hmark w hw hwy, setMarked]
    exact Bool.false_ne_true (hfalse.symm.trans (hxi.symm.trans hxw))
  let jPos : J := ⟨j, hjpos⟩
  let t : T := ⟨jPos, restrictMarker (D j) mk⟩
  have ht := (hit t).mpr ⟨hj.1, hj.2, rfl⟩
  constructor
  · refine ⟨embed t, ⟨⟨t, rfl, ht.1⟩, (hC t).symm ▸ ht.2⟩, ?_⟩
    rintro r ⟨⟨s, rfl, hs⟩, hc⟩
    rw [hC] at hc
    obtain ⟨hsA, hsB, htag⟩ := (hit s).mp ⟨hs, hc⟩
    have he : s.1 = jPos := Subtype.ext (huniq s.1.val ⟨hsA, hsB⟩)
    have hst : s = t := by
      rcases s with ⟨j', o⟩
      change j' = jPos at he
      subst j'
      exact congrArg (Sigma.mk jPos) htag
    exact congrArg embed hst
  · rintro r ⟨s, rfl, hs⟩ hc
    rw [hC] at hc
    rw [hL]
    obtain ⟨hsA, hsB, _⟩ := (hit s).mp ⟨hs, hc⟩
    obtain ⟨i, hpi, hxi, hyi⟩ := part.2.2.1 s.1.val x y hsA hsB
    rw [s.1.property] at hxi hyi
    have hl : label s = i := by
      have hlt : pos s.1.val < n := hpi.symm ▸ i.isLt
      exact Fin.ext (by simpa [label, hlt] using hpi)
    rw [hl]
    have hsame := setMarked_agrees (fun w hw => (selected w hw).2) hyi
      (x := positive u v) (m := mk)
    exact ⟨positive_true.mp (hsame.symm.trans hxi), fun h => hyi (negative_true.mpr h)⟩

