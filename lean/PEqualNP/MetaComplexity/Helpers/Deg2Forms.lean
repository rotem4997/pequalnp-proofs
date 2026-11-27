import PEqualNP.MetaComplexity.Helpers.Deg2Path

/-!
# Sound partial forms, STEP 1 (helper for L-meta-649, package P2, part one)

Cards D2-09 (`card09_form_clean`), D2-10 E1 part (`card10_e1`) and D2-11 (`card11_cover`) of
the degree-two card plan, with their statements exactly as there.

* D2-09: every AND of the DAG reading a never-dead label `f` (degree 0) and a wire `v` of degree
  1 is replaced in place by `or v v`. Degrees are unchanged, values go up, and values are equal
  at every test input with at most two lines; soundness comes back through the fact that a wire
  of degree at most `d` true at `z` is true at `z` with at most `d` of its lines.
* D2-10 E1: the path of D2-05 with the dead set `{w}`; the last wire with two alive points is a
  gate of degree 0 of the form, and its line `w` is unique (no rectangle): two charges per gate.
* D2-11: a walk from the root down to `y_w`; soundness gives a label below `sum_w`, and outside
  `E1` it is a p-gate; beta at the first p-gate passes down the path to the last one.

Everything here is conjecture until the checker accepts it.
-/

namespace PEqualNP.MetaComplexity.Deg2.Forms

open PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

/-! ## Inputs -/

theorem inp_castAdd (P S : Finset (Fin N)) (p : Fin N) :
    inp P S (Fin.castAdd N p) = decide (p ∈ P) := by
  unfold inp
  exact Fin.addCases_left _

theorem inp_natAdd (P S : Finset (Fin N)) (l : Fin N) :
    inp P S (Fin.natAdd N l) = decide (l ∈ S) := by
  unfold inp
  exact Fin.addCases_right _

theorem inp_le {P S : Finset (Fin N)} {x : Fin (N + N) → Bool}
    (hP : ∀ p ∈ P, x (Fin.castAdd N p) = true) (hS : ∀ l ∈ S, x (Fin.natAdd N l) = true) :
    inp P S ≤ x := by
  intro j
  refine Fin.addCases (fun p => ?_) (fun l => ?_) j
  · rw [inp_castAdd]
    by_cases h : p ∈ P
    · rw [hP p h]; exact Bool.le_true _
    · simp [h]
  · rw [inp_natAdd]
    by_cases h : l ∈ S
    · rw [hS l h]; exact Bool.le_true _
    · simp [h]

theorem testInput_castAdd (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) (p : Fin N) :
    testInput I S (Fin.castAdd N p) = true ↔ ∀ l ∈ S, ¬ I p l := by
  classical
  unfold testInput
  rw [inp_castAdd]
  simp

theorem testInput_natAdd (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) (l : Fin N) :
    testInput I S (Fin.natAdd N l) = true ↔ l ∈ S := by
  classical
  unfold testInput
  rw [inp_natAdd]
  simp

theorem val_point (D : Dag N) (x : Fin (N + N) → Bool) (p : Fin N) :
    D.val x p.val = x (Fin.castAdd N p) := by
  rw [Dag.val, dif_pos (by omega)]
  rfl

theorem val_line (D : Dag N) (x : Fin (N + N) → Bool) (l : Fin N) :
    D.val x (N + l.val) = x (Fin.natAdd N l) := by
  rw [Dag.val, dif_pos (by omega)]
  rfl

theorem deg_line (D : Dag N) (l : Fin N) : D.deg (N + l.val) = 1 := by
  rw [Dag.deg, if_pos (by omega), if_pos (by omega)]

/-- `e_p` and `e_p + e_w` agree on the points. -/
theorem pt_ep_points (p w : Fin N) (q : Fin N) :
    pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) := by
  unfold pt ep
  rw [inp_castAdd, inp_castAdd]

/-! ## Gates -/

theorem gateAt_of_get {D : Dag N} {i : ℕ} {g : G} (hi : N + N ≤ i)
    (hg : D.gates[i - (N + N)]? = some g) : D.gateAt i = some g := by
  unfold Dag.gateAt
  rw [if_pos hi]
  exact hg

theorem kid_gate {D : Dag N} {i c : ℕ} (h : D.Kid i c) :
    N + N ≤ i ∧ i < N + N + D.size := by
  obtain ⟨g, hg, -, -⟩ := h
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  have := (List.getElem?_eq_some_iff.1 hg).1
  unfold Dag.size
  omega

theorem val_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem val_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a || D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem deg_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem deg_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) : D.deg i = max (D.deg a) (D.deg b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

/-- A gate true at `y` and false at `x` has a kid true at `y` and false at `x`. -/
theorem exists_kid (D : Dag N) {f : ℕ} (hf : N + N ≤ f) {x y : Fin (N + N) → Bool}
    (h1 : D.val y f = true) (h0 : D.val x f = false) :
    ∃ c, D.Kid f c ∧ D.val y c = true ∧ D.val x c = false := by
  rw [Dag.val, dif_neg (by omega)] at h1 h0
  cases hg : D.gates[f - (N + N)]? with
  | none => rw [hg] at h1; simp at h1
  | some g =>
    have hga := gateAt_of_get hf hg
    rw [hg] at h1 h0
    cases g with
    | and a b =>
      dsimp only at h1 h0
      rw [Bool.and_eq_true] at h1
      obtain ⟨ha, hb⟩ := h1
      split_ifs at ha with hax
      split_ifs at hb with hbx
      have hka : D.Kid f a := ⟨_, hga, by simp [G.kids], hax⟩
      have hkb : D.Kid f b := ⟨_, hga, by simp [G.kids], hbx⟩
      rw [dif_pos hax, dif_pos hbx, Bool.and_eq_false_iff] at h0
      rcases h0 with h0 | h0
      · exact ⟨a, hka, ha, h0⟩
      · exact ⟨b, hkb, hb, h0⟩
    | or a b =>
      dsimp only at h1 h0
      rw [Bool.or_eq_false_iff] at h0
      obtain ⟨h0a, h0b⟩ := h0
      rw [Bool.or_eq_true] at h1
      rcases h1 with ha | hb
      · split_ifs at ha with hax
        have hka : D.Kid f a := ⟨_, hga, by simp [G.kids], hax⟩
        rw [dif_pos hax] at h0a
        exact ⟨a, hka, ha, h0a⟩
      · split_ifs at hb with hbx
        have hkb : D.Kid f b := ⟨_, hga, by simp [G.kids], hbx⟩
        rw [dif_pos hbx] at h0b
        exact ⟨b, hkb, hb, h0b⟩
    | cst v =>
      dsimp only at h1 h0
      rw [h1] at h0
      cases h0

/-! ## Alive sets -/

theorem alive_input_card (D : Dag N) {i : ℕ} (hi : i < N + N) : (D.alive i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  unfold Dag.alive at ha hb
  rw [Finset.mem_filter, Dag.val, dif_pos hi] at ha hb
  have h1 := Path.pt_val hi ha.2
  have h2 := Path.pt_val hi hb.2
  exact Fin.ext (by omega)

theorem two_le_alive_gate (D : Dag N) {i : ℕ} (h : 2 ≤ (D.alive i).card) : N + N ≤ i := by
  by_contra hi
  have := alive_input_card D (i := i) (by omega)
  omega

theorem alive_eq_single (D : Dag N) {c : ℕ} {p : Fin N} (hp : p ∈ D.alive c)
    (h : ¬ 2 ≤ (D.alive c).card) : D.alive c = {p} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨hp, fun q hq => ?_⟩
  exact Finset.card_le_one.1 (by omega) q hq p hp

theorem mem_alive {D : Dag N} {f : ℕ} {p : Fin N} : p ∈ D.alive f ↔ D.val (pt p) f = true := by
  unfold Dag.alive
  simp

/-- All alive points of a wire false at `z_{w}` are on `w`. -/
theorem alive_on_line (I : Fin N → Fin N → Prop) (D : Dag N) {g : ℕ} {w : Fin N}
    (h : D.val (testInput I {w}) g = false) {q : Fin N} (hq : q ∈ D.alive g) : I q w := by
  by_contra hqw
  have hle : pt q ≤ testInput I {w} := by
    unfold pt
    apply inp_le
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      rw [testInput_castAdd]
      intro l hl
      rw [Finset.mem_singleton] at hl
      subst hl
      exact hqw
    · intro l hl
      simp at hl
  have := Api.api_val_mono D g hle
  rw [mem_alive.1 hq, h] at this
  exact absurd this (by decide)

/-- A wire with two alive points is false at `z_{w}` for at most one line `w`. -/
theorem line_unique (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {g : ℕ}
    (h2 : 2 ≤ (D.alive g).card) {w w' : Fin N} (h : D.val (testInput I {w}) g = false)
    (h' : D.val (testInput I {w'}) g = false) : w = w' := by
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (D.alive g).card)
  exact hI a b w w' hab hne ⟨alive_on_line I D h ha, alive_on_line I D h' ha,
    alive_on_line I D h hb, alive_on_line I D h' hb⟩

/-- A wire of degree 0 false at `z_{w}` is below `sum_w`. -/
theorem leSum_of (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {w : Fin N}
    (hd : D.deg f = 0) (h : D.val (testInput I {w}) f = false) : D.LeSum I f w := by
  classical
  intro z hz
  by_contra hno
  push_neg at hno
  let z' : Fin (N + N) → Bool := inp (Finset.univ.filter (fun q => z (Fin.castAdd N q) = true)) ∅
  have heq : D.val z f = D.val z' f := by
    apply Api.api_val_xonly D hd
    intro q
    simp only [z', inp_castAdd, Finset.mem_filter, Finset.mem_univ, true_and]
    cases z (Fin.castAdd N q) <;> rfl
  have hle : z' ≤ testInput I {w} := by
    apply inp_le
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [testInput_castAdd]
      intro l hl
      rw [Finset.mem_singleton] at hl
      subst hl
      intro hql
      exact absurd hq.2 (by simp [hno q hql])
    · intro l hl
      simp at hl
  have := Api.api_val_mono D f hle
  rw [← heq, hz, h] at this
  exact absurd this (by decide)

/-- `LeSum` gives `false` at `z_{w}`. -/
theorem false_of_leSum (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {w : Fin N}
    (h : D.LeSum I f w) : D.val (testInput I {w}) f = false := by
  by_contra hf
  rw [Bool.not_eq_false] at hf
  obtain ⟨q, hq, hz⟩ := h _ hf
  rw [testInput_castAdd] at hz
  exact hz w (Finset.mem_singleton_self w) hq

/-! ## Cones -/

theorem mem_coneOf_reach {D : Dag N} {S : Finset ℕ} {i j : ℕ} (hi : i ∈ D.coneOf S)
    (hr : D.Reach i j) (hj : N + N ≤ j) (hj' : j < N + N + D.size) : j ∈ D.coneOf S := by
  classical
  unfold Dag.coneOf at hi ⊢
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨-, -, r, hr', hreach⟩ := hi
  exact ⟨hj', hj, r, hr', Relation.ReflTransGen.trans hreach hr⟩

theorem mem_rootCone {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ} {w : Fin N} (hw : w ∈ W)
    {j : ℕ} (hr : D.Reach (R w) j) (hj : N + N ≤ j) (hj' : j < N + N + D.size) :
    j ∈ D.rootCone W R := by
  classical
  unfold Dag.rootCone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  exact ⟨hj', hj, R w, ⟨w, hw, rfl⟩, hr⟩

/-! ## D2-10, the E1 part -/

/-- The walk of E1: from a wire with two alive points, alive at `p` and false at `x`, down to
the last wire with two alive points; its next wire has alive set `{p}`. -/
theorem walk_two (D : Dag N) (p : Fin N) (x : Fin (N + N) → Bool) :
    ∀ f, D.val (pt p) f = true → D.val x f = false → 2 ≤ (D.alive f).card →
      ∃ g c, D.Reach f g ∧ D.Kid g c ∧ 2 ≤ (D.alive g).card ∧ D.alive c = {p} ∧
        D.val x g = false := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro h1 h0 h2
    obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (two_le_alive_gate D h2) h1 h0
    obtain ⟨_, _, _, hcf⟩ := id hk
    by_cases hc2 : 2 ≤ (D.alive c).card
    · obtain ⟨g, c', hr, hk', hg2, hc', hg0⟩ := ih c hcf hc1 hc0 hc2
      exact ⟨g, c', Relation.ReflTransGen.head hk hr, hk', hg2, hc', hg0⟩
    · exact ⟨f, c, Relation.ReflTransGen.refl, hk, h2, alive_eq_single D (mem_alive.2 hc1) hc2,
        h0⟩

open Classical in
/-- At most two points `q` with a kid of `g` of alive set `{q}`. -/
theorem kid_points_card (D : Dag N) (g : ℕ) :
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})).card ≤ 2 := by
  classical
  cases hg : D.gateAt g with
  | none =>
    have : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q}) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, not_and]
      intro c hk
      obtain ⟨g', hg', -⟩ := hk
      rw [hg] at hg'
      cases hg'
    rw [this]
    simp
  | some gg =>
    have hsub : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q}) ⊆
        gg.kids.toFinset.biUnion (fun c => if (D.alive c).card ≤ 1 then D.alive c else ∅) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨c, hk, hc⟩ := hq.2
      obtain ⟨g', hg', hcm, -⟩ := hk
      rw [hg] at hg'
      cases hg'
      rw [Finset.mem_biUnion]
      refine ⟨c, List.mem_toFinset.2 hcm, ?_⟩
      rw [hc]
      simp
    have hb := Finset.card_biUnion_le (s := gg.kids.toFinset)
      (t := fun c => if (D.alive c).card ≤ 1 then D.alive c else ∅)
    have hs : ∑ c ∈ gg.kids.toFinset,
        (if (D.alive c).card ≤ 1 then D.alive c else ∅).card ≤ ∑ _c ∈ gg.kids.toFinset, 1 := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs with h
      · exact h
      · simp
    have hk : gg.kids.toFinset.card ≤ 2 := by
      refine le_trans (List.toFinset_card_le _) ?_
      cases gg <;> simp [G.kids]
    have := Finset.card_le_card hsub
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
    omega

/-- D2-10 (E1). -/
theorem card10_e1 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.e1Set I W R).card ≤ 2 * ((D.rootCone W R).filter (fun f => D.deg f = 0)).card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})) ×ˢ
      (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card))
  have hT : ∀ g, (T g).card ≤ 2 := by
    intro g
    rw [Finset.card_product]
    have h1 := kid_points_card D g
    have h2 : (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact line_unique I hI D ha.2.2 ha.2.1 hb.2.1
    calc _ ≤ 2 * 1 := Nat.mul_le_mul h1 h2
      _ = 2 := rfl
  have hsub : D.e1Set I W R ⊆ ((D.rootCone W R).filter (fun f => D.deg f = 0)).biUnion T := by
    intro e he
    unfold Dag.e1Set at he
    rw [Finset.mem_filter] at he
    obtain ⟨hce, f, hf, hfd, hle, hp, h2⟩ := he
    have hf0 := false_of_leSum I D hle
    obtain ⟨g, c, hr, hk, hg2, hc, hg0⟩ := walk_two D e.1 _ f (mem_alive.1 hp) hf0 h2
    have hgd : D.deg g = 0 := by
      have := Api.api_reach_deg D hr
      omega
    obtain ⟨hgN, hgs⟩ := kid_gate hk
    rw [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.2 ⟨mem_coneOf_reach hf hr hgN hgs, hgd⟩, ?_⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, c, hk, hc⟩, Finset.mem_univ _, hg0, hg2⟩
  calc (D.e1Set I W R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ (D.rootCone W R).filter (fun f => D.deg f = 0), (T g).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ (D.rootCone W R).filter (fun f => D.deg f = 0), 2 :=
        Finset.sum_le_sum (fun g _ => hT g)
    _ = 2 * ((D.rootCone W R).filter (fun f => D.deg f = 0)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Paths as lists -/

theorem path_len_pos {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) : 0 < π.length := by
  obtain ⟨hh, -, -⟩ := h
  cases π with
  | nil => simp at hh
  | cons _ _ => simp

theorem path_getD_mem {π : List ℕ} {k : ℕ} (hk : k < π.length) : π.getD k 0 ∈ π := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem path_head {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) : π.getD 0 0 = a := by
  obtain ⟨hh, -, -⟩ := h
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hh]
  rfl

theorem path_last {D : Dag N} {π : List ℕ} {a b : ℕ} (h : D.IsPath π a b) :
    π.getD (π.length - 1) 0 = b := by
  obtain ⟨-, hl, -⟩ := h
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hl]
  rfl

theorem getD_snoc_lt {π : List ℕ} {c k : ℕ} (hk : k < π.length) :
    (π ++ [c]).getD k 0 = π.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_snoc_eq {π : List ℕ} {c : ℕ} : (π ++ [c]).getD π.length 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem isPath_snoc {D : Dag N} {π : List ℕ} {a b c : ℕ} (hp : D.IsPath π a b)
    (hk : D.Kid b c) : D.IsPath (π ++ [c]) a c := by
  have hlen := path_len_pos hp
  have hlast := path_last hp
  obtain ⟨hh, -, hs⟩ := hp
  refine ⟨?_, by simp, ?_⟩
  · rw [List.head?_append, hh]
    rfl
  · intro k hk'
    simp only [List.length_append, List.length_singleton] at hk'
    by_cases h : k + 1 < π.length
    · rw [getD_snoc_lt (by omega), getD_snoc_lt h]
      exact hs k h
    · have hk1 : k + 1 = π.length := by omega
      rw [getD_snoc_lt (by omega), hk1, getD_snoc_eq]
      rw [show k = π.length - 1 by omega, hlast]
      exact hk

theorem labelsAlive_snoc {D : Dag N} {π : List ℕ} {a b c : ℕ} {x : Fin (N + N) → Bool}
    (hp : D.IsPath π a b) (hl : D.LabelsAlive π x)
    (hc : ∀ f, D.LabAnd b f c → D.val x f = true) : D.LabelsAlive (π ++ [c]) x := by
  have hlen := path_len_pos hp
  have hlast := path_last hp
  intro k f hk' hlab
  simp only [List.length_append, List.length_singleton] at hk'
  by_cases h : k + 1 < π.length
  · rw [getD_snoc_lt (by omega), getD_snoc_lt h] at hlab
    exact hl k f h hlab
  · have hk1 : k + 1 = π.length := by omega
    rw [getD_snoc_lt (by omega), hk1, getD_snoc_eq, show k = π.length - 1 by omega,
      hlast] at hlab
    exact hc f hlab

/-! ## D2-11 -/

theorem ep_input {p w : Fin N} {i : ℕ} (hi : i < N + N) (h1 : ep p w ⟨i, hi⟩ = true)
    (h0 : pt p ⟨i, hi⟩ = false) : i = N + w.val := by
  by_cases hN : i < N
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, hN⟩ := rfl
    rw [this, ← pt_ep_points p w] at h1
    rw [this, h1] at h0
    cases h0
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
      ext
      simp only [Fin.natAdd_mk]
      omega
    rw [this] at h1
    unfold ep at h1
    rw [inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at h1
    have := congrArg Fin.val h1
    simp only at this
    omega

/-- The walk of D2-11: from a wire true at `e_p + e_w` and false at `e_p` down to `y_w`. -/
theorem edge_walk (D : Dag N) (p w : Fin N) : ∀ f, D.val (ep p w) f = true →
    D.val (pt p) f = false →
    ∃ π, D.IsPath π f (N + w.val) ∧ ∀ v ∈ π, D.val (ep p w) v = true ∧
      D.val (pt p) v = false ∧ D.Reach f v ∧ D.Reach v (N + w.val) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro h1 h0
    by_cases hi : f < N + N
    · have h1' := h1
      have h0' := h0
      rw [Dag.val, dif_pos hi] at h1' h0'
      have hf := ep_input hi h1' h0'
      subst hf
      refine ⟨[N + w.val], Path.isPath_single D _, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨h1, h0, .refl, .refl⟩
    · obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (by omega) h1 h0
      obtain ⟨_, _, _, hcf⟩ := id hk
      obtain ⟨π, hπ, hv⟩ := ih c hcf hc1 hc0
      refine ⟨f :: π, Path.isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · have hcm : c ∈ π := by
          obtain ⟨hh, -, -⟩ := hπ
          exact List.mem_of_mem_head? hh
        exact ⟨h1, h0, .refl, Relation.ReflTransGen.head hk (hv c hcm).2.2.2⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hv v hv'
        exact ⟨a1, a2, Relation.ReflTransGen.head hk a3, a4⟩

theorem labAnd_val {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v)
    (x : Fin (N + N) → Bool) : D.val x e = (D.val x f && D.val x v) := by
  rcases h.1 with hg | hg
  · exact val_and hg (hwf _ _ hg f (by simp [G.kids])) (hwf _ _ hg v (by simp [G.kids])) x
  · rw [val_and hg (hwf _ _ hg v (by simp [G.kids])) (hwf _ _ hg f (by simp [G.kids])) x,
      Bool.and_comm]

theorem labAnd_kid {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v) : D.Kid e f := by
  rcases h.1 with hg | hg
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg f (by simp [G.kids])⟩
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg f (by simp [G.kids])⟩

/-- One step of a path of degree-1 wires: an OR reading `c`, or an AND of `c` and a label. -/
theorem step_cases {D : Dag N} (hwf : D.WF) {v c : ℕ} (hk : D.Kid v c) (hv : D.deg v = 1)
    (hc : D.deg c = 1) :
    (∀ x, D.val x c = true → D.val x v = true) ∨ ∃ f, D.LabAnd v f c := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  cases g with
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    rw [deg_and hg ha hb] at hv
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    right
    rcases hcm with rfl | rfl
    · exact ⟨b, Or.inr hg, by omega, hc⟩
    · exact ⟨a, Or.inl hg, by omega, hc⟩
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    left
    intro x hx
    rw [val_or hg ha hb x]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl <;> simp [hx]
  | cst _ => simp [G.kids] at hcm

/-- D2-11. -/
theorem card11_cover (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    D.countedEdges W R ⊆
      D.e0Set W R ∪ D.e1Set I W R ∪ D.alphaEdges I W R ∪ D.betaEdges I W R := by
  classical
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  intro e he
  have he' := he
  unfold Dag.countedEdges at he'
  rw [Finset.mem_filter] at he'
  obtain ⟨-, hw, hep⟩ := he'
  obtain ⟨p, w⟩ := e
  dsimp only at hw hep
  simp only [Finset.mem_union]
  by_cases h0 : D.val (pt p) (R w) = true
  · left; left; left
    unfold Dag.e0Set
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw, h0⟩
  rw [Bool.not_eq_true] at h0
  obtain ⟨π, hπ, hv⟩ := edge_walk D p w (R w) hep h0
  have hdeg1 : ∀ v ∈ π, D.deg v = 1 := by
    intro v hv'
    obtain ⟨-, -, r1, r2⟩ := hv v hv'
    have a1 := Api.api_reach_deg D r1
    have a2 := Api.api_reach_deg D r2
    have a3 := hdeg w hw
    rw [deg_line] at a2
    omega
  have hlen := path_len_pos hπ
  by_cases hlab : ∃ k f, k + 1 < π.length ∧ D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) ∧
      D.val (testInput I {w}) f = false
  swap
  · exfalso
    push_neg at hlab
    have hall : ∀ m k, k + m + 1 = π.length →
        D.val (testInput I {w}) (π.getD k 0) = true := by
      intro m
      induction m with
      | zero =>
        intro k hk
        rw [show k = π.length - 1 by omega, path_last hπ, val_line, testInput_natAdd]
        exact Finset.mem_singleton_self w
      | succ m ih =>
        intro k hk
        have h1 := ih (k + 1) (by omega)
        have hk' : k + 1 < π.length := by omega
        have hkid := hπ.2.2 k hk'
        rcases step_cases hwf hkid (hdeg1 _ (path_getD_mem (by omega)))
            (hdeg1 _ (path_getD_mem hk')) with h | ⟨f, hf⟩
        · exact h _ h1
        · rw [labAnd_val hwf hf, h1, Bool.and_true]
          have := hlab k f hk' hf
          simpa using this
    have hR := hall (π.length - 1) 0 (by omega)
    rw [path_head hπ] at hR
    have hy : testInput I {w} (Fin.natAdd N w) = true := by
      rw [testInput_natAdd]
      exact Finset.mem_singleton_self w
    obtain ⟨q, l, hql, hq, hl⟩ := hsound (testInput I {w}) ⟨w, hw, hy, hR⟩
    rw [testInput_natAdd] at hl
    rw [testInput_castAdd] at hq
    exact hq l hl hql
  obtain ⟨k, f, hk, hlabk, hf0⟩ := hlab
  have hfd : D.deg f = 0 := hlabk.2.1
  have hvk := hv _ (path_getD_mem (by omega : k < π.length))
  have hfep : D.val (ep p w) f = true := by
    have := hvk.1
    rw [labAnd_val hwf hlabk, Bool.and_eq_true] at this
    exact this.1
  have hfpt : D.val (pt p) f = true := by
    rw [Api.api_val_xonly D hfd (pt_ep_points p w)]
    exact hfep
  by_cases h2 : 2 ≤ (D.alive f).card
  · left; left; right
    have hkf := labAnd_kid hwf hlabk
    have hr : D.Reach (R w) f := Relation.ReflTransGen.tail hvk.2.2.1 hkf
    obtain ⟨-, hes⟩ := kid_gate hkf
    obtain ⟨_, _, _, hfe⟩ := id hkf
    unfold Dag.e1Set
    rw [Finset.mem_filter]
    exact ⟨he, f, mem_rootCone hw hr (two_le_alive_gate D h2) (by omega), hfd,
      leSum_of I D hfd hf0, mem_alive.2 hfpt, h2⟩
  have hpg : D.PGateAt p π k := ⟨hk, f, hlabk, alive_eq_single D (mem_alive.2 hfpt) h2⟩
  have hex : ∃ k, D.PGateAt p π k := ⟨k, hpg⟩
  have hk0 : D.PGateAt p π (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ k' < Nat.find hex, ¬ D.PGateAt p π k' := fun k' h => Nat.find_min hex h
  have hEP : D.EdgePath R p w π := ⟨hπ, fun v hv' => ⟨(hv v hv').1, (hv v hv').2.1⟩⟩
  by_cases hb : D.IsBeta I W R p (π.getD (Nat.find hex + 1) 0)
  · right
    have hk1 : D.PGateAt p π (Nat.findGreatest (fun k => D.PGateAt p π k) π.length) :=
      Nat.findGreatest_spec (m := Nat.find hex) (by have := hk0.1; omega) hk0
    have hmax : ∀ k', Nat.findGreatest (fun k => D.PGateAt p π k) π.length < k' →
        ¬ D.PGateAt p π k' := by
      intro k' hlt hk'
      have := hk'.1
      exact Nat.findGreatest_is_greatest hlt (by omega) hk'
    have hle : Nat.find hex ≤ Nat.findGreatest (fun k => D.PGateAt p π k) π.length :=
      Nat.find_min' hex hk1
    have hprop : ∀ j, Nat.find hex + 1 ≤ j → j < π.length →
        D.IsBeta I W R p (π.getD j 0) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; exact hb
      | succ j hj ih =>
        intro hjl
        obtain ⟨u, hu, hoff, π', hπ', hla⟩ := ih (by omega)
        have hkid := hπ.2.2 j hjl
        refine ⟨u, hu, hoff, π' ++ [π.getD (j + 1) 0], isPath_snoc hπ' hkid,
          labelsAlive_snoc hπ' hla ?_⟩
        intro f' hf'
        have h1 := (hv _ (path_getD_mem (by omega : j < π.length))).1
        rw [labAnd_val hwf hf', Bool.and_eq_true] at h1
        rw [Api.api_val_xonly D hf'.2.1 (pt_ep_points p w)]
        exact h1.1
    unfold Dag.betaEdges
    rw [Finset.mem_filter]
    exact ⟨he, π, hEP, _, hk1, hmax, hprop _ (by omega) hk1.1⟩
  · left; right
    unfold Dag.alphaEdges
    rw [Finset.mem_filter]
    exact ⟨he, π, hEP, Nat.find hex, hk0, hmin, hb⟩

/-! ## D2-09 -/

theorem inp_mono {P S S' : Finset (Fin N)} (h : S ⊆ S') : inp P S ≤ inp P S' := by
  apply inp_le
  · intro p hp
    rw [inp_castAdd]
    simpa using hp
  · intro l hl
    rw [inp_natAdd]
    simpa using h hl

theorem bool_true_le {b : Bool} (h : true ≤ b) : b = true := by
  revert h
  cases b <;> decide

/-- A wire of degree at most `d` true at `x` is true at the points of `x` and at most `d` of the
lines of `x`. -/
theorem exists_few_lines (D : Dag N) (x : Fin (N + N) → Bool) : ∀ i, D.val x i = true →
    ∃ S : Finset (Fin N), S.card ≤ D.deg i ∧ (∀ l ∈ S, x (Fin.natAdd N l) = true) ∧
      D.val (inp (Finset.univ.filter (fun q => x (Fin.castAdd N q) = true)) S) i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < N + N
    · by_cases hN : i < N
      · obtain ⟨p, rfl⟩ : ∃ p : Fin N, p.val = i := ⟨⟨i, hN⟩, rfl⟩
        rw [val_point] at h
        refine ⟨∅, by simp, by simp, ?_⟩
        rw [val_point, inp_castAdd]
        simpa using h
      · obtain ⟨l, rfl⟩ : ∃ l : Fin N, N + l.val = i := ⟨⟨i - N, by omega⟩, by simp; omega⟩
        rw [val_line] at h
        refine ⟨{l}, by rw [deg_line]; simp, ?_, ?_⟩
        · intro l' hl'
          rw [Finset.mem_singleton] at hl'
          subst hl'
          exact h
        · rw [val_line, inp_natAdd]
          simp
    · rw [Dag.val, dif_neg hi] at h
      cases hg : D.gates[i - (N + N)]? with
      | none => rw [hg] at h; simp at h
      | some g =>
        have hga := gateAt_of_get (by omega) hg
        rw [hg] at h
        cases g with
        | and a b =>
          dsimp only at h
          rw [Bool.and_eq_true] at h
          obtain ⟨ha, hb⟩ := h
          split_ifs at ha with hax
          split_ifs at hb with hbx
          obtain ⟨Sa, hSa, hla, hva⟩ := ih a hax ha
          obtain ⟨Sb, hSb, hlb, hvb⟩ := ih b hbx hb
          refine ⟨Sa ∪ Sb, ?_, ?_, ?_⟩
          · rw [deg_and hga hax hbx]
            exact le_trans (Finset.card_union_le _ _) (by omega)
          · intro l hl
            rcases Finset.mem_union.1 hl with hl | hl
            · exact hla l hl
            · exact hlb l hl
          · rw [val_and hga hax hbx, Bool.and_eq_true]
            constructor
            · have m := Api.api_val_mono D a
                (inp_mono (P := Finset.univ.filter (fun q => x (Fin.castAdd N q) = true))
                  (S := Sa) (S' := Sa ∪ Sb) Finset.subset_union_left)
              rw [hva] at m
              exact bool_true_le m
            · have m := Api.api_val_mono D b
                (inp_mono (P := Finset.univ.filter (fun q => x (Fin.castAdd N q) = true))
                  (S := Sb) (S' := Sa ∪ Sb) Finset.subset_union_right)
              rw [hvb] at m
              exact bool_true_le m
        | or a b =>
          dsimp only at h
          rw [Bool.or_eq_true] at h
          rcases h with ha | hb
          · split_ifs at ha with hax
            obtain ⟨Sa, hSa, hla, hva⟩ := ih a hax ha
            refine ⟨Sa, ?_, hla, ?_⟩
            · have : D.deg a ≤ D.deg i := Api.deg_kid ⟨_, hga, by simp [G.kids], hax⟩
              omega
            · rw [Dag.val, dif_neg hi, hg]
              dsimp only
              rw [dif_pos hax, hva]
              rfl
          · split_ifs at hb with hbx
            obtain ⟨Sb, hSb, hlb, hvb⟩ := ih b hbx hb
            refine ⟨Sb, ?_, hlb, ?_⟩
            · have : D.deg b ≤ D.deg i := Api.deg_kid ⟨_, hga, by simp [G.kids], hbx⟩
              omega
            · rw [Dag.val, dif_neg hi, hg]
              dsimp only
              rw [dif_pos hbx, hvb]
              simp
        | cst v =>
          dsimp only at h
          refine ⟨∅, by simp, by simp, ?_⟩
          rw [Dag.val, dif_neg hi, hg]
          exact h

open Classical in
/-- The cleaning of one gate: an AND of a never-dead label (degree 0) and a wire of degree 1
becomes `or v v`. -/
noncomputable def cleanGate (I : Fin N → Fin N → Prop) (D : Dag N) : G → G
  | .and a b =>
      if D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ then .or b b
      else if D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ then .or a a else .and a b
  | .or a b => .or a b
  | .cst v => .cst v

/-- The cleaned DAG: every gate cleaned in place. -/
noncomputable def cleanDag (I : Fin N → Fin N → Prop) (D : Dag N) : Dag N :=
  ⟨D.gates.map (cleanGate I D), D.out⟩

theorem cleanGate_and (I : Fin N → Fin N → Prop) (D : Dag N) (a b : ℕ) :
    (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅ ∧
      cleanGate I D (.and a b) = .or b b) ∨
    (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅ ∧
      cleanGate I D (.and a b) = .or a a) ∨
    (¬ (D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅) ∧
      ¬ (D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅) ∧
      cleanGate I D (.and a b) = .and a b) := by
  by_cases h1 : D.deg a = 0 ∧ D.deg b = 1 ∧ D.deadSets I 2 a = ∅
  · left
    exact ⟨h1.1, h1.2.1, h1.2.2, by rw [cleanGate, if_pos h1]⟩
  · by_cases h2 : D.deg b = 0 ∧ D.deg a = 1 ∧ D.deadSets I 2 b = ∅
    · right; left
      exact ⟨h2.1, h2.2.1, h2.2.2, by rw [cleanGate, if_neg h1, if_pos h2]⟩
    · right; right
      exact ⟨h1, h2, by rw [cleanGate, if_neg h1, if_neg h2]⟩

theorem clean_get (I : Fin N → Fin N → Prop) (D : Dag N) (j : ℕ) :
    (cleanDag I D).gates[j]? = (D.gates[j]?).map (cleanGate I D) := by
  simp [cleanDag]

theorem clean_size (I : Fin N → Fin N → Prop) (D : Dag N) : (cleanDag I D).size = D.size := by
  simp [cleanDag, Dag.size]

theorem clean_gateAt (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (cleanDag I D).gateAt i = (D.gateAt i).map (cleanGate I D) := by
  unfold Dag.gateAt
  split_ifs
  · exact clean_get I D _
  · rfl

theorem cleanGate_kids (I : Fin N → Fin N → Prop) (D : Dag N) (g : G) :
    ∀ c ∈ (cleanGate I D g).kids, c ∈ g.kids := by
  intro c hc
  cases g with
  | and a b =>
    rcases cleanGate_and I D a b with ⟨-, -, -, e⟩ | ⟨-, -, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e] at hc <;> simp_all [G.kids]
  | or a b => simpa [cleanGate] using hc
  | cst v => simp [cleanGate, G.kids] at hc

theorem clean_kid {I : Fin N → Fin N → Prop} {D : Dag N} {i c : ℕ}
    (h : (cleanDag I D).Kid i c) : D.Kid i c := by
  obtain ⟨g', hg', hc, hlt⟩ := h
  rw [clean_gateAt, Option.map_eq_some_iff] at hg'
  obtain ⟨g, hg, rfl⟩ := hg'
  exact ⟨g, hg, cleanGate_kids I D g c hc, hlt⟩

theorem clean_reach {I : Fin N → Fin N → Prop} {D : Dag N} {i j : ℕ}
    (h : (cleanDag I D).Reach i j) : D.Reach i j := by
  induction h with
  | refl => exact .refl
  | tail _ hk ih => exact Relation.ReflTransGen.tail ih (clean_kid hk)

theorem clean_deg (I : Fin N → Fin N → Prop) (D : Dag N) (i : ℕ) :
    (cleanDag I D).deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hg : ∀ a, (if _ : a < i then (cleanDag I D).deg a else 0) =
        (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with h
      · exact ih a h
      · rfl
    conv_lhs => rw [Dag.deg]
    conv_rhs => rw [Dag.deg]
    by_cases hi : i < N + N
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        cases g with
        | and a b =>
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨h1, -, -, e⟩ | ⟨h1, -, -, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · simp only [hg, max_self]
            split_ifs <;> simp [h1]
          · simp only [hg, max_self]
            split_ifs <;> simp [h1]
          · simp only [hg]
        | or a b => simp only [Option.map_some, cleanGate, hg]
        | cst v => simp only [Option.map_some, cleanGate]

theorem band_le_bor_right : ∀ a b c : Bool, b ≤ c → (a && b) ≤ (c || c) := by decide
theorem band_le_bor_left : ∀ a b c : Bool, a ≤ c → (a && b) ≤ (c || c) := by decide

theorem clean_val_ge (I : Fin N → Fin N → Prop) (D : Dag N) (x : Fin (N + N) → Bool)
    (i : ℕ) : D.val x i ≤ (cleanDag I D).val x i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then (cleanDag I D).val x a else false) := by
      intro a
      split_ifs with h
      · exact ih a h
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b =>
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨-, -, -, e⟩ | ⟨-, -, -, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · exact band_le_bor_right _ _ _ (hd b)
          · exact band_le_bor_left _ _ _ (hd a)
          · exact Api.band_mono _ _ _ _ (hd a) (hd b)
        | or a b =>
          simp only [Option.map_some, cleanGate]
          exact Api.bor_mono _ _ _ _ (hd a) (hd b)
        | cst v => simp only [Option.map_some, cleanGate]; exact le_rfl

theorem never_dead {I : Fin N → Fin N → Prop} {D : Dag N} {a : ℕ} (h : D.deadSets I 2 a = ∅)
    {S : Finset (Fin N)} (hS : S.card ≤ 2) : D.val (testInput I S) a = true := by
  classical
  by_contra hc
  rw [Bool.not_eq_true] at hc
  have : S ∈ D.deadSets I 2 a := by
    unfold Dag.deadSets
    simp [hS, hc]
  rw [h] at this
  simp at this

theorem clean_val_test (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    {S : Finset (Fin N)} (hS : S.card ≤ 2) (i : ℕ) :
    (cleanDag I D).val (testInput I S) i = D.val (testInput I S) i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then (cleanDag I D).val (testInput I S) a else false) =
        (if _ : a < i then D.val (testInput I S) a else false) := by
      intro a
      split_ifs with h
      · exact ih a h
      · rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi, clean_get]
      cases hgi : D.gates[i - (N + N)]? with
      | none => rfl
      | some g =>
        have hga := gateAt_of_get (by omega) hgi
        cases g with
        | and a b =>
          have ha := hwf _ _ hga a (by simp [G.kids])
          have hb := hwf _ _ hga b (by simp [G.kids])
          rw [Option.map_some]
          rcases cleanGate_and I D a b with ⟨-, -, h3, e⟩ | ⟨-, -, h3, e⟩ | ⟨-, -, e⟩ <;>
            rw [e] <;> dsimp only
          · simp only [hd, dif_pos ha, dif_pos hb, never_dead h3 hS]
            simp
          · simp only [hd, dif_pos ha, dif_pos hb, never_dead h3 hS]
            simp
          · simp only [hd, dif_pos ha, dif_pos hb]
        | or a b => simp only [Option.map_some, cleanGate, hd]
        | cst v => simp only [Option.map_some, cleanGate]

theorem clean_deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (f : ℕ) :
    (cleanDag I D).deadSets I 2 f = D.deadSets I 2 f := by
  classical
  unfold Dag.deadSets
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, by rwa [clean_val_test I D hwf h] at h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, by rwa [clean_val_test I D hwf h]⟩

/-- D2-09. -/
theorem card09_form_clean (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    ∃ D' : Dag N, Dag.SoundPartialForm I D' W R ∧
      (D'.rootCone W R).card ≤ (D.rootCone W R).card ∧
      D.countedEdges W R ⊆ D'.countedEdges W R ∧ D'.Cleaned I (D'.rootCone W R) := by
  classical
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  refine ⟨cleanDag I D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i g hg c hc
    rw [clean_gateAt, Option.map_eq_some_iff] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hwf i g0 hg0 c (cleanGate_kids I D g0 c hc)
  · intro w hw
    rw [clean_deg]
    exact hdeg w hw
  · rintro z ⟨w, hw, hzw, hval⟩
    by_contra hno
    push_neg at hno
    obtain ⟨S, hSc, hSl, hSv⟩ := exists_few_lines (cleanDag I D) z (R w) hval
    rw [clean_deg] at hSc
    have hd1 := hdeg w hw
    have hcard : (insert w S).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by omega)
    have hle : inp (Finset.univ.filter (fun q => z (Fin.castAdd N q) = true)) (insert w S) ≤
        testInput I (insert w S) := by
      apply inp_le
      · intro q hq
        rw [Finset.mem_filter] at hq
        rw [testInput_castAdd]
        intro l hl hql
        have hzl : z (Fin.natAdd N l) = true := by
          rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hzw
          · exact hSl l hl
        exact hno q l hql hq.2 hzl
      · intro l hl
        rw [testInput_natAdd]
        exact hl
    have h1 := Api.api_val_mono (cleanDag I D) (R w) (le_trans (inp_mono (Finset.subset_insert w S)) hle)
    rw [hSv, clean_val_test I D hwf hcard] at h1
    have h2 := bool_true_le h1
    obtain ⟨q, l, hql, hq, hl⟩ := hsound _
      ⟨w, hw, by rw [testInput_natAdd]; exact Finset.mem_insert_self w S, h2⟩
    rw [testInput_castAdd] at hq
    rw [testInput_natAdd] at hl
    exact hq l hl hql
  · apply Finset.card_le_card
    intro i hi
    unfold Dag.rootCone Dag.coneOf at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨h1, h2, r, hr, hreach⟩ := hi
    rw [clean_size] at h1
    exact ⟨h1, h2, r, hr, clean_reach hreach⟩
  · intro e he
    unfold Dag.countedEdges at he ⊢
    rw [Finset.mem_filter] at he ⊢
    refine ⟨he.1, he.2.1, ?_⟩
    have := clean_val_ge I D (ep e.1 e.2) (R e.2)
    rw [he.2.2] at this
    exact bool_true_le this
  · intro e _ f v hlab
    obtain ⟨hg, hf, hv⟩ := hlab
    rw [clean_deg] at hf hv
    rw [clean_deadSets I D hwf]
    rw [clean_gateAt] at hg
    rcases hg with hg | hg <;> obtain ⟨g0, -, hc⟩ := Option.map_eq_some_iff.1 hg
    · cases g0 with
      | and a b =>
        simp only [cleanGate] at hc
        split_ifs at hc with h1 h2 <;> cases hc
        intro hde
        exact h1 ⟨hf, hv, hde⟩
      | or a b => simp [cleanGate] at hc
      | cst _ => simp [cleanGate] at hc
    · cases g0 with
      | and a b =>
        simp only [cleanGate] at hc
        split_ifs at hc with h1 h2 <;> cases hc
        intro hde
        exact h2 ⟨hf, hv, hde⟩
      | or a b => simp [cleanGate] at hc
      | cst _ => simp [cleanGate] at hc

end PEqualNP.MetaComplexity.Deg2.Forms
