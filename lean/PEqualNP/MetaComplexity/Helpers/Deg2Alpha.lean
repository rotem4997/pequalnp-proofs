import PEqualNP.MetaComplexity.Helpers.Deg2Forms

/-!
# The alpha count D2-12 (helper for L-meta-649)

Card `card12_alpha` of the degree-two card plan, with its statement exactly as
there. Paper proof: the paper text of the cards, section 2.

* `Q o`: the points `p` of an alpha edge `(p, w)` (outside the exclusions) with an alpha witness
  path on which `o` comes no later than the first labelled step.
* Privacy: two distinct points of `Q o` have the same line. Otherwise the unlabelled prefix of
  one witness, joined to the other witness from `o` down to the child of its p-gate, is a path
  from a root of a line off `p` whose labels are alive at `p`: that p-gate would be beta.
* Small part (`|Q (R w)| <= 1`): at most one edge per line of `W`. Big part: the last wire of the
  unlabelled prefix with `|Q| >= 2` is a gate of degree 1 of the form; at an OR gate the next
  wire has `Q = {p}` (two kids), at an AND gate `p` is an alive point of its label on the common
  line, at most two of them since the edge is not in `F_2` and the form is cleaned.

The "first p-gate" clause of `alphaEdges` is not used. Everything here is conjecture until the
checker accepts it.
-/

namespace PEqualNP.MetaComplexity.Deg2.Alpha

open PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

/-- A step whose label, if any, is true at `x`. -/
def Step (D : Dag N) (x : Fin (N + N) → Bool) (a b : ℕ) : Prop :=
  D.Kid a b ∧ ∀ f, D.LabAnd a f b → D.val x f = true

/-- Step `i` of `π` is labelled. -/
def Lab (D : Dag N) (π : List ℕ) (i : ℕ) : Prop :=
  ∃ f, D.LabAnd (π.getD i 0) f (π.getD (i + 1) 0)

/-- An alpha witness: an edge path with a p-gate at `k` whose child is not beta. -/
def AW (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p w : Fin N) (π : List ℕ) (k : ℕ) : Prop :=
  D.EdgePath R p w π ∧ D.PGateAt p π k ∧ ¬ D.IsBeta I W R p (π.getD (k + 1) 0)

/-- `o` is on an alpha witness of `(p, w)`, no later than its first labelled step. -/
def Pref (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p w : Fin N) (o : ℕ) : Prop :=
  ∃ π k i, AW I D W R p w π k ∧ (∀ i' < i, ¬ Lab D π i') ∧ π.getD i 0 = o

/-- The set counted by the card. -/
noncomputable def Aset (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)

open Classical in
/-- `Q o`. -/
noncomputable def Q (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (o : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun p => ∃ w, (p, w) ∈ Aset I D W R ∧ Pref I D W R p w o)

open Classical in
/-- The fibre of a gate `o`. -/
noncomputable def T (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (o : ℕ) : Finset (Fin N × Fin N) :=
  (Aset I D W R).filter (fun e => Pref I D W R e.1 e.2 o ∧ 2 ≤ (Q I D W R o).card ∧
    (((∀ f v, ¬ D.LabAnd o f v) ∧ ∃ c, D.Kid o c ∧ Q I D W R c = {e.1}) ∨
      ∃ f v, D.LabAnd o f v ∧ e.1 ∈ D.alive f))

/-! ## Paths from chains -/

theorem labelsAlive_cons {D : Dag N} {π : List ℕ} {a c b : ℕ} {x : Fin (N + N) → Bool}
    (hp : D.IsPath π c b) (hl : D.LabelsAlive π x)
    (ha : ∀ f, D.LabAnd a f c → D.val x f = true) : D.LabelsAlive (a :: π) x := by
  intro k f hk hlab
  cases k with
  | zero =>
    rw [List.getD_cons_zero, List.getD_cons_succ, Forms.path_head hp] at hlab
    exact ha f hlab
  | succ k =>
    rw [List.getD_cons_succ, List.getD_cons_succ] at hlab
    simp only [List.length_cons] at hk
    exact hl k f (by omega) hlab

theorem reach_path {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (Step D x) a b) :
    ∃ π, D.IsPath π a b ∧ D.LabelsAlive π x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], Path.isPath_single D b, fun k f hk _ => by simp at hk⟩
  | head hs _ ih =>
    obtain ⟨π, hπ, hl⟩ := ih
    exact ⟨_ :: π, Path.isPath_cons D hs.1 hπ, labelsAlive_cons hπ hl hs.2⟩

theorem chain_reach {r : ℕ → ℕ → Prop} {π : List ℕ} {i j : ℕ}
    (h : ∀ k, i ≤ k → k < j → r (π.getD k 0) (π.getD (k + 1) 0)) (hij : i ≤ j) :
    Relation.ReflTransGen r (π.getD i 0) (π.getD j 0) := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact .refl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact .refl
    · exact (ih (fun k h1 h2 => h k h1 (by omega)) (by omega)).tail (h j (by omega) (by omega))

/-! ## Facts on witnesses -/

variable {I : Fin N → Fin N → Prop} {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ}

theorem label_alive (hwf : D.WF) {p w : Fin N} {a f b : ℕ}
    (ha : D.val (ep p w) a = true) (h : D.LabAnd a f b) : D.val (pt p) f = true := by
  rw [Forms.labAnd_val hwf h] at ha
  rw [Api.api_val_xonly D h.2.1 (y := ep p w) (fun q => Forms.pt_ep_points p w q)]
  rw [Bool.and_eq_true] at ha
  exact ha.1

theorem counted_inc (hs : Dag.SoundPartialForm I D W R) {e : Fin N × Fin N}
    (h : e ∈ D.countedEdges W R) : I e.1 e.2 ∧ e.2 ∈ W := by
  classical
  unfold Dag.countedEdges at h
  rw [Finset.mem_filter] at h
  obtain ⟨-, hw, hv⟩ := h
  have hl : ep e.1 e.2 (Fin.natAdd N e.2) = true := by
    unfold ep
    rw [Forms.inp_natAdd]
    simp
  obtain ⟨p0, l, hI0, hp0, hl0⟩ := hs.2.2 (ep e.1 e.2) ⟨e.2, hw, hl, hv⟩
  unfold ep at hp0 hl0
  rw [Forms.inp_castAdd, decide_eq_true_eq, Finset.mem_singleton] at hp0
  rw [Forms.inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at hl0
  subst hp0
  subst hl0
  exact ⟨hI0, hw⟩

theorem aset_counted {e : Fin N × Fin N} (he : e ∈ Aset I D W R) : e ∈ D.countedEdges W R := by
  classical
  unfold Aset at he
  have h := (Finset.mem_sdiff.1 he).1
  unfold Dag.alphaEdges at h
  exact (Finset.mem_filter.1 h).1

theorem aset_not_fSet {e : Fin N × Fin N} (he : e ∈ Aset I D W R) :
    e ∉ D.fSet I (D.rootCone W R) 2 := by
  intro hf
  unfold Aset at he
  exact (Finset.mem_sdiff.1 he).2 (Finset.mem_union_right _ hf)

theorem aw_of_mem {e : Fin N × Fin N} (he : e ∈ Aset I D W R) :
    ∃ π k, AW I D W R e.1 e.2 π k := by
  classical
  unfold Aset at he
  have h := (Finset.mem_sdiff.1 he).1
  unfold Dag.alphaEdges at h
  rw [Finset.mem_filter] at h
  obtain ⟨-, π, hep, k, hpg, -, hnb⟩ := h
  exact ⟨π, k, hep, hpg, hnb⟩

theorem pref_le {p w : Fin N} {π : List ℕ} {k i : ℕ} (ha : AW I D W R p w π k)
    (hn : ∀ i' < i, ¬ Lab D π i') : i ≤ k := by
  by_contra h
  obtain ⟨-, f, hf, -⟩ := ha.2.1
  exact hn k (by omega) ⟨f, hf⟩

theorem pref_reach {p w : Fin N} {π : List ℕ} {k i : ℕ} (ha : AW I D W R p w π k)
    (hn : ∀ i' < i, ¬ Lab D π i') (x : Fin (N + N) → Bool) :
    Relation.ReflTransGen (Step D x) (R w) (π.getD i 0) := by
  have hle := pref_le ha hn
  have hk := ha.2.1.1
  rw [← Forms.path_head ha.1.1]
  exact chain_reach (fun j _ hj => ⟨ha.1.1.2.2 j (by omega),
    fun f hf => absurd ⟨f, hf⟩ (hn j hj)⟩) (Nat.zero_le i)

theorem tail_reach (hwf : D.WF) {p w : Fin N} {π : List ℕ} {k : ℕ} (ha : AW I D W R p w π k)
    {i : ℕ} (hi : i ≤ k + 1) :
    Relation.ReflTransGen (Step D (pt p)) (π.getD i 0) (π.getD (k + 1) 0) := by
  have hk := ha.2.1.1
  exact chain_reach (fun j _ hj => ⟨ha.1.1.2.2 j (by omega),
    fun f hf => label_alive hwf (ha.1.2 _ (Forms.path_getD_mem (by omega))).1 hf⟩) hi

theorem aw_deg (hs : Dag.SoundPartialForm I D W R) {p w : Fin N} {π : List ℕ} {k : ℕ}
    (ha : AW I D W R p w π k) (hw : w ∈ W) {i : ℕ} (hi : i < π.length) :
    D.deg (π.getD i 0) = 1 ∧ D.Reach (R w) (π.getD i 0) := by
  have hr : D.Reach (R w) (π.getD i 0) := by
    rw [← Forms.path_head ha.1.1]
    exact chain_reach (fun j _ hj => ha.1.1.2.2 j (by omega)) (Nat.zero_le i)
  refine ⟨?_, hr⟩
  have h1 := Api.api_reach_deg D hr
  have h2 := hs.2.1 w hw
  have hv := ha.1.2 _ (Forms.path_getD_mem hi)
  by_contra hne
  have h0 : D.deg (π.getD i 0) = 0 := by omega
  have := Api.api_val_xonly D h0 (x := pt p) (y := ep p w) (fun q => Forms.pt_ep_points p w q)
  rw [hv.1, hv.2] at this
  cases this

/-- A labelled gate with a kid of degree 1: the kid is the wire of the label. -/
theorem labAnd_of_kid {o f v c : ℕ} (h : D.LabAnd o f v) (hk : D.Kid o c)
    (hc : D.deg c = 1) : D.LabAnd o f c := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  obtain ⟨hgo, hf, hv⟩ := h
  rcases hgo with h1 | h1
  · rw [h1] at hg
    obtain rfl := Option.some.inj hg
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · omega
    · exact ⟨Or.inl h1, hf, hc⟩
  · rw [h1] at hg
    obtain rfl := Option.some.inj hg
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · exact ⟨Or.inr h1, hf, hc⟩
    · omega

/-! ## Privacy -/

theorem inc_of_pref (hwf : D.WF) {p1 w1 p2 w2 : Fin N} {o : ℕ}
    (h1 : Pref I D W R p1 w1 o) (h2 : Pref I D W R p2 w2 o) (hw2 : w2 ∈ W) : I p1 w2 := by
  by_contra hn
  obtain ⟨π1, k1, i1, ha1, hn1, ho1⟩ := h1
  obtain ⟨π2, k2, i2, ha2, hn2, ho2⟩ := h2
  have hle1 := pref_le ha1 hn1
  have r2 := pref_reach ha2 hn2 (pt p1)
  have r1 := tail_reach hwf ha1 (i := i1) (by omega)
  rw [ho2] at r2
  rw [ho1] at r1
  obtain ⟨ρ, hρ, hl⟩ := reach_path (r2.trans r1)
  exact ha1.2.2 ⟨w2, hw2, hn, ρ, hρ, hl⟩

theorem privacy (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R) {p1 w1 p2 w2 : Fin N}
    {o : ℕ} (ha1 : (p1, w1) ∈ Aset I D W R) (hp1 : Pref I D W R p1 w1 o)
    (ha2 : (p2, w2) ∈ Aset I D W R) (hp2 : Pref I D W R p2 w2 o) (hne : p1 ≠ p2) :
    w1 = w2 := by
  obtain ⟨hi1, hw1⟩ := counted_inc hs (aset_counted ha1)
  obtain ⟨hi2, hw2⟩ := counted_inc hs (aset_counted ha2)
  have h12 := inc_of_pref hs.1 hp1 hp2 hw2
  have h21 := inc_of_pref hs.1 hp2 hp1 hw1
  by_contra hw
  exact hI p1 p2 w1 w2 hne hw ⟨hi1, h12, h21, hi2⟩

theorem line_common (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R) {o : ℕ}
    (h2 : 2 ≤ (Q I D W R o).card) {p w p' w' : Fin N}
    (ha : (p, w) ∈ Aset I D W R) (hp : Pref I D W R p w o)
    (ha' : (p', w') ∈ Aset I D W R) (hp' : Pref I D W R p' w' o) : w = w' := by
  classical
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (by omega : 1 < (Q I D W R o).card) p
  unfold Q at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨-, u, hau, hpu⟩ := hq
  have h1 : w = u := privacy hI hs ha hp hau hpu (Ne.symm hqp)
  by_cases hpq : p' = q
  · subst hpq
    exact privacy hI hs ha hp ha' hp' (Ne.symm hqp)
  · exact h1.trans (privacy hI hs ha' hp' hau hpu hpq).symm

/-! ## Counting -/

open Classical in
/-- At most two points `q` with a kid `c` of `g` and `Φ c = {q}`. -/
theorem kid_points_card' (D : Dag N) (Φ : ℕ → Finset (Fin N)) (g : ℕ) :
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q})).card ≤ 2 := by
  classical
  cases hg : D.gateAt g with
  | none =>
    have : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q}) = ∅ := by
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
    have hsub : Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ Φ c = {q}) ⊆
        gg.kids.toFinset.biUnion (fun c => if (Φ c).card ≤ 1 then Φ c else ∅) := by
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
      (t := fun c => if (Φ c).card ≤ 1 then Φ c else ∅)
    have hs : ∑ c ∈ gg.kids.toFinset,
        (if (Φ c).card ≤ 1 then Φ c else ∅).card ≤ ∑ _c ∈ gg.kids.toFinset, 1 := by
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

theorem mem_Q_root {e : Fin N × Fin N} (he : e ∈ Aset I D W R) : e.1 ∈ Q I D W R (R e.2) := by
  classical
  obtain ⟨π, k, ha⟩ := aw_of_mem he
  unfold Q
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, e.2, he, π, k, 0, ha, fun i' h => absurd h (Nat.not_lt_zero _),
    Forms.path_head ha.1.1⟩

theorem small_card (hs : Dag.SoundPartialForm I D W R) :
    ((Aset I D W R).filter (fun e => (Q I D W R (R e.2)).card ≤ 1)).card ≤ W.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    exact (counted_inc hs (aset_counted he.1)).2
  · intro e he e' he' h
    rw [Finset.mem_coe, Finset.mem_filter] at he he'
    have hq1 := mem_Q_root he.1
    have hq2 := mem_Q_root he'.1
    rw [h] at hq1
    exact Prod.ext (Finset.card_le_one.1 he'.2 _ hq1 _ hq2) h

theorem T_card (hI : NoRect I) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) {o : ℕ} (ho : o ∈ D.rootCone W R) :
    (T I D W R o).card ≤ 2 := by
  classical
  have hwf := hs.1
  have hmem : ∀ e ∈ T I D W R o, e ∈ Aset I D W R ∧ Pref I D W R e.1 e.2 o ∧
      2 ≤ (Q I D W R o).card ∧
      (((∀ f v, ¬ D.LabAnd o f v) ∧ ∃ c, D.Kid o c ∧ Q I D W R c = {e.1}) ∨
        ∃ f v, D.LabAnd o f v ∧ e.1 ∈ D.alive f) := by
    intro e he
    unfold T at he
    rw [Finset.mem_filter] at he
    exact ⟨he.1, he.2⟩
  have hline : ∀ e ∈ T I D W R o, ∀ e' ∈ T I D W R o, e.2 = e'.2 := by
    intro e he e' he'
    obtain ⟨ha, hp, h2, -⟩ := hmem e he
    obtain ⟨ha', hp', -, -⟩ := hmem e' he'
    exact line_common hI hs h2 ha hp ha' hp'
  have hinj : Set.InjOn Prod.fst (T I D W R o : Set (Fin N × Fin N)) := by
    intro e he e' he' h
    exact Prod.ext h (hline e he e' he')
  rw [← Finset.card_image_of_injOn hinj]
  by_cases hlab : ∃ f v, D.LabAnd o f v
  · obtain ⟨f0, v0, h0⟩ := hlab
    rcases (T I D W R o).eq_empty_or_nonempty with hT | ⟨e0, he0⟩
    · rw [hT]
      simp
    have hsub : (T I D W R o).image Prod.fst ⊆ D.alive f0 ∩ ptsOn I e0.2 := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨e, he, rfl⟩ := hq
      obtain ⟨ha, -, -, hc⟩ := hmem e he
      rcases hc with ⟨hno, -⟩ | ⟨f, v, hf, hal⟩
      · exact absurd h0 (hno f0 v0)
      · obtain ⟨rfl, -⟩ := Api.labAnd_unique hf h0
        rw [Finset.mem_inter]
        refine ⟨hal, ?_⟩
        unfold ptsOn
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hline e he e0 he0]
        exact (counted_inc hs (aset_counted ha)).1
    refine le_trans (Finset.card_le_card hsub) ?_
    by_contra h3
    obtain ⟨ha0, -, -, hc0⟩ := hmem e0 he0
    have hal0 : e0.1 ∈ D.alive f0 := by
      rcases hc0 with ⟨hno, -⟩ | ⟨f, v, hf, hal⟩
      · exact absurd h0 (hno f0 v0)
      · obtain ⟨rfl, -⟩ := Api.labAnd_unique hf h0
        exact hal
    have hkid := Forms.labAnd_kid hwf h0
    have hint := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f0)
      (s₂ := ptsOn I e0.2))
    have hfN : N + N ≤ f0 := by
      by_contra hlt
      have := Forms.alive_input_card D (i := f0) (by omega)
      omega
    obtain ⟨-, hos⟩ := Forms.kid_gate hkid
    obtain ⟨_, _, _, hflt⟩ := id hkid
    have hfc : f0 ∈ D.rootCone W R :=
      Forms.mem_coneOf_reach ho (Relation.ReflTransGen.single hkid) hfN (by omega)
    apply aset_not_fSet ha0
    unfold Dag.fSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (counted_inc hs (aset_counted ha0)).1, f0, hfc, h0.2.1,
      hcl o ho f0 v0 h0, hal0, by omega⟩
  · refine le_trans (Finset.card_le_card ?_) (kid_points_card' D (Q I D W R) o)
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨e, he, rfl⟩ := hq
    obtain ⟨-, -, -, hc⟩ := hmem e he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hc with ⟨-, c, hk, hq⟩ | ⟨f, v, hf, -⟩
    · exact ⟨c, hk, hq⟩
    · exact absurd ⟨f, v, hf⟩ hlab

theorem big_mem (hs : Dag.SoundPartialForm I D W R) {e : Fin N × Fin N}
    (he : e ∈ Aset I D W R) (h2 : 2 ≤ (Q I D W R (R e.2)).card) :
    ∃ o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), e ∈ T I D W R o := by
  classical
  obtain ⟨p, w⟩ := e
  dsimp only at h2
  have hwf := hs.1
  obtain ⟨π, k, ha⟩ := aw_of_mem he
  have hw := (counted_inc hs (aset_counted he)).2
  have hk := ha.2.1.1
  let J : ℕ → Prop := fun i => (∀ i' < i, ¬ Lab D π i') ∧ 2 ≤ (Q I D W R (π.getD i 0)).card
  have hJ0 : J 0 := ⟨fun i' h => absurd h (Nat.not_lt_zero _), by
    show 2 ≤ (Q I D W R (π.getD 0 0)).card
    rw [Forms.path_head ha.1.1]
    exact h2⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.findGreatest J k := ⟨_, rfl⟩
  have hJm : J m := by
    rw [hm]
    exact Nat.findGreatest_spec (Nat.zero_le k) hJ0
  have hmk : m ≤ k := by
    rw [hm]
    exact Nat.findGreatest_le k
  have hgr : ∀ j, m < j → j ≤ k → ¬ J j := fun j h1 h2 =>
    Nat.findGreatest_is_greatest (by rw [← hm]; exact h1) h2
  have hmlen : m + 1 < π.length := by omega
  obtain ⟨hdo, hro⟩ := aw_deg hs ha hw (i := m) (by omega)
  obtain ⟨hdc, -⟩ := aw_deg hs ha hw (i := m + 1) hmlen
  have hkid : D.Kid (π.getD m 0) (π.getD (m + 1) 0) := ha.1.1.2.2 m hmlen
  obtain ⟨hoN, hos⟩ := Forms.kid_gate hkid
  refine ⟨π.getD m 0, Finset.mem_filter.2 ⟨Forms.mem_rootCone hw hro hoN hos, hdo⟩, ?_⟩
  unfold T
  rw [Finset.mem_filter]
  refine ⟨he, ⟨π, k, m, ha, hJm.1, rfl⟩, hJm.2, ?_⟩
  by_cases hL : Lab D π m
  · right
    obtain ⟨f, hf⟩ := hL
    exact ⟨f, _, hf, Forms.mem_alive.2
      (label_alive hwf (ha.1.2 _ (Forms.path_getD_mem (by omega))).1 hf)⟩
  · left
    refine ⟨fun f v hfv => hL ⟨f, labAnd_of_kid hfv hkid hdc⟩, π.getD (m + 1) 0, hkid, ?_⟩
    have hnl : ∀ i' < m + 1, ¬ Lab D π i' := by
      intro i' hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
      · exact hJm.1 i' h
      · rw [h]
        exact hL
    have hp : p ∈ Q I D W R (π.getD (m + 1) 0) := by
      unfold Q
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, w, he, π, k, m + 1, ha, hnl, rfl⟩
    have hmk' : m + 1 ≤ k := by
      rcases Nat.lt_or_eq_of_le hmk with h | h
      · omega
      · exfalso
        rw [h] at hL
        obtain ⟨-, f, hf, -⟩ := ha.2.1
        exact hL ⟨f, hf⟩
    have hc1 : (Q I D W R (π.getD (m + 1) 0)).card ≤ 1 := by
      by_contra hc
      exact hgr (m + 1) (Nat.lt_succ_self m) hmk' ⟨hnl, by omega⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hp, fun q hq => Finset.card_le_one.1 hc1 q hq p hp⟩

end PEqualNP.MetaComplexity.Deg2.Alpha

namespace PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

/-- D2-12. Alpha count. -/
theorem card12_alpha (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) :
    (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
      2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card := by
  classical
  change (Alpha.Aset I D W R).card ≤ _
  have hsub : Alpha.Aset I D W R ⊆
      (Alpha.Aset I D W R).filter (fun e => (Alpha.Q I D W R (R e.2)).card ≤ 1) ∪
        ((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion (Alpha.T I D W R) := by
    intro e he
    by_cases hsm : (Alpha.Q I D W R (R e.2)).card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hsm⟩)
    · apply Finset.mem_union_right
      obtain ⟨o, ho, het⟩ := Alpha.big_mem hs he (by omega)
      exact Finset.mem_biUnion.2 ⟨o, ho, het⟩
  have hsm := Alpha.small_card hs
  have hb : (((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion
      (Alpha.T I D W R)).card ≤ 2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
    calc _ ≤ ∑ o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), (Alpha.T I D W R o).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _o ∈ (D.rootCone W R).filter (fun f => D.deg f = 1), 2 :=
          Finset.sum_le_sum (fun o ho => Alpha.T_card hI hs hcl (Finset.mem_filter.1 ho).1)
      _ = 2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hu := Finset.card_union_le
    ((Alpha.Aset I D W R).filter (fun e => (Alpha.Q I D W R (R e.2)).card ≤ 1))
    (((D.rootCone W R).filter (fun f => D.deg f = 1)).biUnion (Alpha.T I D W R))
  have hc := Finset.card_le_card hsub
  omega

end PEqualNP.MetaComplexity.Deg2
