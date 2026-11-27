import PEqualNP.MetaComplexity.Helpers.Deg2Transp2

/-!
# Toward D2-16: the terms of the marker form (helper for L-meta-649)

Semantic lemmas for `card16_form` of the degree-two card plan: a marker of `w`
is above `y_w`; a term (context AND the other factors) under `y_w` is below the edge function;
a degree-one marker item never has the constant context; a degree-one item other than the
output has a parent OR of T, and an OR of T has at most one child of degree at most one.
Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

/-- `V*` reaches only through ORs: the line `y_u` forces every wire whose `V*` holds `u`. -/
theorem tr_vreach_above {D : Dag N} (hwf : D.WF) {v : ℕ} {u : Fin N} (h : D.VReach v u)
    (z : Fin (N + N) → Bool) (hz : z (Fin.natAdd N u) = true) : D.val z v = true := by
  induction h with
  | leaf u =>
    rw [Dag.val, dif_pos (by omega)]
    exact hz
  | @step v c u hor _ hk _ ih =>
    obtain ⟨a, b, hg⟩ := hor
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    obtain ⟨g, hg', hcg, -⟩ := hk
    rw [hg] at hg'
    cases hg'
    rw [tr_val_or hg ha hb]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
    rcases hcg with rfl | rfl <;> simp [ih hz]

/-- A marker of `w` is true whenever `y_w` is on. -/
theorem tr_marker_above {D : Dag N} (hwf : D.WF) {r : ℕ} {w : Fin N} (hm : D.IsMarker r w)
    (z : Fin (N + N) → Bool) (hz : z (Fin.natAdd N w) = true) : D.val z r = true := by
  classical
  have hw : w ∈ D.Vstar r := by rw [hm.2]; exact Finset.mem_singleton_self w
  exact tr_vreach_above hwf (Finset.mem_filter.1 hw).2 z hz

/-- A term under `y_w` is below the edge function: an item `b`, a factor `r` of `b` that is a
marker of `w`, `y_w` on, the context true and every other factor true. -/
theorem tr_term_sound (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) {b r : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hm : D.IsMarker r w) (z : Fin (N + N) → Bool)
    (hz : z (Fin.natAdd N w) = true) (hctx : D.ctx b z = true)
    (hrest : ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true) :
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  refine (hc z).1 ((card15_identity I D hwf hc hd z).2 ⟨b, hb, hctx, fun x hx => ?_⟩)
  by_cases hxr : x = r
  · subst hxr; exact tr_marker_above hwf hm z hz
  · exact hrest x hx hxr

/-- G2: a marker item of degree at most one never has the constant context. -/
theorem tr_no_const (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) {b : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hb1 : D.deg b ≤ 1) (hm : D.IsMarker b w) : ¬ ∀ x, D.ctx b x = true := by
  classical
  intro hall
  have hz : inp (∅ : Finset (Fin N)) {w} (Fin.natAdd N w) = true := by
    unfold inp; rw [Fin.addCases_right]; simp
  obtain ⟨p, l, -, hp, -⟩ := tr_term_sound I hwf hc hd hb hm _ hz (hall _)
    (fun x hx hxb => by
      rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · exact absurd rfl hxb
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
  unfold inp at hp
  rw [Fin.addCases_left] at hp
  simp at hp

/-- A degree-one item other than the output is a child of an OR of T. -/
theorem tr_item_parent {D : Dag N} {ok : ℕ → Prop} {b : ℕ} (hT : D.Top ok b)
    (hne : b ≠ D.out) (hb1 : D.deg b ≤ 1) : ∃ h ∈ D.Tor, D.Kid h b := by
  cases hT with
  | root => exact absurd rfl hne
  | orStep _ ht hk _ => exact ⟨_, ht, hk⟩
  | andStep _ _ _ _ hc2 _ _ _ => omega

/-- An OR of T has at most one child of degree at most one. -/
theorem tr_tor_low_unique {D : Dag N} (hwf : D.WF) {h b b' : ℕ} (ht : h ∈ D.Tor)
    (hk : D.Kid h b) (hk' : D.Kid h b') (hb : D.deg b ≤ 1) (hb' : D.deg b' ≤ 1) : b = b' := by
  classical
  obtain ⟨hT, a, c, hg⟩ := Finset.mem_filter.1 ht
  have h2 := (Finset.mem_filter.1 hT).2
  have ha := hwf _ _ hg a (by simp [G.kids])
  have hc := hwf _ _ hg c (by simp [G.kids])
  rw [tr_deg_or hg ha hc] at h2
  obtain ⟨g, hg1, hbg, -⟩ := hk
  obtain ⟨g', hg2, hbg', -⟩ := hk'
  rw [hg] at hg1 hg2
  cases hg1
  cases hg2
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hbg hbg'
  rcases hbg with rfl | rfl <;> rcases hbg' with rfl | rfl <;> first | rfl | omega

/-! ### Counting the terms -/

/-- The three kinds of gates of T are disjoint. -/
theorem tr_T_split (D : Dag N) : D.Tor.card + D.Tandf.card + D.Tmix.card ≤ D.T.card := by
  classical
  have h1 := Api.card_filter_disj (s := D.T) (p := D.IsOr)
    (q := fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0)) (by
      rintro i ⟨a, b, ha⟩ ⟨a', b', hb, -⟩
      rw [ha] at hb
      cases hb)
  have h2 := Api.card_filter_disj (s := D.T)
    (p := fun i => D.IsOr i ∨ ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0))
    (q := fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1) (by
      rintro i (⟨a, b, ha⟩ | ⟨a, b, ha, hab⟩) ⟨a', b', hb, h1, h2⟩
      · rw [ha] at hb; cases hb
      · rw [ha] at hb; cases hb; omega)
  have h3 := Finset.card_filter_le D.T (fun i => (D.IsOr i ∨
      ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0)) ∨
      ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1)
  unfold Dag.Tor Dag.Tandf Dag.Tmix
  omega

/-- A wire reached by the pass is the output or below the last gate. -/
theorem tr_top_lt {D : Dag N} {ok : ℕ → Prop} {b : ℕ} (hT : D.Top ok b) :
    b = D.out ∨ b < N + N + D.size := by
  classical
  cases hT with
  | root => exact Or.inl rfl
  | orStep _ ht hk _ =>
    right
    have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out}
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1)
    obtain ⟨_, _, _, hlt⟩ := hk
    omega
  | andStep _ ht _ _ _ _ hch _ =>
    right
    have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out}
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1)
    omega

theorem tr_factor_le {D : Dag N} {b r : ℕ} (h : D.IsFactor b r) : r ≤ b := by
  rcases h with ⟨-, rfl⟩ | ⟨-, _, _, _, hlt⟩
  · exact le_rfl
  · exact le_of_lt hlt

open Classical in
/-- The jobs of the form: items `b`, factors `r` of `b`, `r` a marker of `w`. -/
noncomputable def tr_jobs (D : Dag N) : Finset (ℕ × ℕ × Fin N) :=
  ((Finset.range (D.out + N + N + D.size + 1)) ×ˢ
    ((Finset.range (D.out + N + N + D.size + 1)) ×ˢ (Finset.univ : Finset (Fin N)))).filter
    (fun j => D.IsItem j.1 ∧ D.IsFactor j.1 j.2.1 ∧ D.IsMarker j.2.1 j.2.2)

theorem tr_mem_jobs {D : Dag N} {b r : ℕ} {w : Fin N} :
    (b, r, w) ∈ tr_jobs D ↔ D.IsItem b ∧ D.IsFactor b r ∧ D.IsMarker r w := by
  classical
  unfold tr_jobs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true]
  constructor
  · exact fun h => h.2
  · rintro ⟨hb, hr, hm⟩
    have h1 := tr_top_lt hb.1
    have h2 := tr_factor_le hr
    refine ⟨⟨by omega, by omega⟩, hb, hr, hm⟩

theorem tr_marker_line {D : Dag N} {r : ℕ} {w w' : Fin N} (h : D.IsMarker r w)
    (h' : D.IsMarker r w') : w = w' := by
  have := h.2.symm.trans h'.2
  exact Finset.singleton_inj.1 this

/-- Jobs of a degree-one item: at most one per OR of T. -/
theorem tr_jobs1_card (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card ≤ D.Tor.card := by
  classical
  have key : ∀ j ∈ (tr_jobs D).filter (fun j => D.deg j.1 ≤ 1),
      j.2.1 = j.1 ∧ ∃ h ∈ D.Tor, D.Kid h j.1 := by
    intro j hj
    obtain ⟨b, r, w⟩ := j
    rw [Finset.mem_filter, tr_mem_jobs] at hj
    obtain ⟨⟨hb, hr, hm⟩, h1⟩ := hj
    have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; dsimp only at h1; omega
    subst hrb
    refine ⟨rfl, tr_item_parent hb.1 ?_ h1⟩
    rintro rfl
    exact tr_no_const I hwf hc hd hb h1 hm (fun x => by
      unfold Dag.ctx; exact decide_eq_true Dag.Top.root)
  let f : ℕ × ℕ × Fin N → ℕ := fun j =>
    if h : ∃ h ∈ D.Tor, D.Kid h j.1 then h.choose else 0
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    have hx := (key j hj).2
    simp only [f, dif_pos hx]
    exact hx.choose_spec.1
  · intro j hj j' hj' he
    have hx := (key j hj).2
    have hx' := (key j' hj').2
    simp only [f, dif_pos hx, dif_pos hx'] at he
    have hk := hx.choose_spec.2
    rw [he] at hk
    have h1 := (Finset.mem_filter.1 hj).2
    have h1' := (Finset.mem_filter.1 hj').2
    have hbb := tr_tor_low_unique hwf hx'.choose_spec.1 hk hx'.choose_spec.2 h1 h1'
    obtain ⟨b, r, w⟩ := j
    obtain ⟨b', r', w'⟩ := j'
    have hm := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj).1)).2.2
    have hm' := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj').1)).2.2
    have e1 := (key _ hj).1
    have e2 := (key _ hj').1
    dsimp only at hbb e1 e2 hm hm'
    subst e1 e2 hbb
    rw [tr_marker_line hm hm']

/-- Jobs of a gate of T_mix: at most two per gate. -/
theorem tr_jobs2_card {D : Dag N} :
    ((tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1)).card ≤ 2 * D.Tmix.card := by
  classical
  have key : ∀ j ∈ (tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1),
      j.1 ∈ D.Tmix ∧ D.Kid j.1 j.2.1 := by
    intro j hj
    obtain ⟨b, r, w⟩ := j
    rw [Finset.mem_filter, tr_mem_jobs] at hj
    obtain ⟨⟨hb, hr, hm⟩, h1⟩ := hj
    rcases hr with ⟨h, -⟩ | hr
    · exact absurd h h1
    · exact hr
  let first : ℕ → ℕ := fun b =>
    match D.gateAt b with
    | some (.and a _) => a
    | _ => 0
  let f : ℕ × ℕ × Fin N → ℕ × ℕ := fun j => (j.1, if j.2.1 = first j.1 then 0 else 1)
  have hcard : (D.Tmix ×ˢ Finset.range 2).card = 2 * D.Tmix.card := by
    rw [Finset.card_product, Finset.card_range, mul_comm]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    show f j ∈ D.Tmix ×ˢ Finset.range 2
    rw [Finset.mem_product]
    exact ⟨(key j hj).1, by rw [Finset.mem_range]; dsimp only [f]; split_ifs <;> omega⟩
  · intro j hj j' hj' he
    obtain ⟨hmix, hk⟩ := key j hj
    obtain ⟨hmix', hk'⟩ := key j' hj'
    have hm := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj).1)).2.2
    have hm' := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj').1)).2.2
    obtain ⟨b, r, w⟩ := j
    obtain ⟨b', r', w'⟩ := j'
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    dsimp only at hmix hk hk' hm hm'
    obtain ⟨-, a, a', hg, -⟩ := Finset.mem_filter.1 hmix
    have hfirst : first b = a := by simp only [first, hg]
    obtain ⟨g, hg1, hr1, -⟩ := hk
    obtain ⟨g', hg2, hr2, -⟩ := hk'
    rw [hg] at hg1 hg2
    cases hg1
    cases hg2
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hr1 hr2
    have hrr : r = r' := by
      rw [hfirst] at he
      rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl <;> first | rfl | (split_ifs at he <;> simp_all)
    subst hrr
    rw [tr_marker_line hm hm']

end PEqualNP.MetaComplexity.Deg2
