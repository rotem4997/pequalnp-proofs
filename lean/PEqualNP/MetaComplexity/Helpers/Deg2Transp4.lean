import PEqualNP.MetaComplexity.Helpers.Deg2Transp3

/-!
# D2-16: the form of the marker edges (helper for L-meta-649)

Card `card16_form` of the degree-two card plan. The gates of D2-15 (iii) are
taken as given (`card15c_contexts`); the jobs (item, marker factor, line) are processed in a
list; each job makes a term (the context wire, or context AND the other factor, or the other
factor alone when the context is the constant one) and merges it into the root of its line by
one OR. Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

theorem tr_reach_le {D : Dag N} {u m : ℕ} (h : D.Reach u m) : m ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hk ih =>
    obtain ⟨_, _, _, hlt⟩ := hk
    exact le_trans (le_of_lt hlt) ih

theorem tr_reach_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) {u m : ℕ}
    (hu : u < N + N + gs.length) (h : (⟨gs', o'⟩ : Dag N).Reach u m) :
    (⟨gs, o⟩ : Dag N).Reach u m := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c hr hk ih =>
    have ha := tr_reach_le hr
    obtain ⟨g, hg, hc, hlt⟩ := hk
    rw [tr_gateAt_prefix hp o o' (by omega)] at hg
    exact ih.tail ⟨g, hg, hc, hlt⟩

theorem tr_val_lt {D : Dag N} {x : Fin (N + N) → Bool} {i : ℕ} (h : D.val x i = true) :
    i < N + N + D.size := by
  rw [Dag.val] at h
  split_ifs at h with hi
  · omega
  · cases hg : D.gates[i - (N + N)]? with
    | none => rw [hg] at h; simp at h
    | some g =>
      have := (List.getElem?_eq_some_iff.1 hg).1
      unfold Dag.size
      omega

theorem tr_ctx_xonly {D : Dag N} {b : ℕ} {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.ctx b x = D.ctx b y := by
  classical
  unfold Dag.ctx
  have e : D.Top (fun f => D.val x f = true) b ↔ D.Top (fun f => D.val y f = true) b :=
    ⟨tr_top_mono (fun f hf hv => by rw [← Api.api_val_xonly D hf h]; exact hv),
     tr_top_mono (fun f hf hv => by rw [Api.api_val_xonly D hf h]; exact hv)⟩
  by_cases hb : D.Top (fun f => D.val x f = true) b
  · rw [decide_eq_true hb, decide_eq_true (e.1 hb)]
  · rw [decide_eq_false hb, decide_eq_false (fun h' => hb (e.2 h'))]

theorem tr_pt_ep (p w : Fin N) (q : Fin N) :
    pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) := by
  simp only [pt, ep, inp, Fin.addCases_left]

/-! ### Wires the form may read -/

/-- An old wire of `D'` of degree at most one whose cone is in `M ∪ X` or the context gates. -/
def tr_Old (D D' : Dag N) (u : ℕ) : Prop :=
  u < N + N + D'.size ∧ D'.deg u ≤ 1 ∧ ∀ m, D'.Reach u m → N + N ≤ m →
    m ∈ D.M ∨ m ∈ D.X ∨ (N + N + D.size ≤ m ∧ m < N + N + D'.size)

def tr_Good4 (D D' : Dag N) (len u : ℕ) : Prop :=
  tr_Old D D' u ∨ (N + N + D'.size ≤ u ∧ u < N + N + len)

def tr_NewG (D D' : Dag N) (j : ℕ) (g : G) : Prop :=
  (∃ i v, g = .and i v ∧ tr_Old D D' i ∧ D'.deg i = 0 ∧ tr_Old D D' v) ∨
    (∃ u v, g = .or u v ∧ tr_Good4 D D' j u ∧ tr_Good4 D D' j v)

def tr_Base (D D' : Dag N) (gs : List G) : Prop :=
  D'.gates <+: gs ∧ ∀ j g, D'.size ≤ j → gs[j]? = some g → tr_NewG D D' j g

theorem tr_Good4_mono {D D' : Dag N} {j len u : ℕ} (h : tr_Good4 D D' j u) (hj : j ≤ len) :
    tr_Good4 D D' len u := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by omega⟩

theorem tr_Good4_lt {D D' : Dag N} {len u : ℕ} (h : tr_Good4 D D' len u)
    (hl : D'.size ≤ len) : u < N + N + len := by
  rcases h with h | h
  · have := h.1; omega
  · exact h.2

theorem tr_Base_append {D D' : Dag N} {gs : List G} (h : tr_Base D D' gs) {g : G}
    (hg : tr_NewG D D' gs.length g) : tr_Base D D' (gs ++ [g]) := by
  refine ⟨h.1.trans (List.prefix_append gs [g]), fun j g' hj hg' => ?_⟩
  by_cases hjl : j < gs.length
  · rw [List.getElem?_append_left hjl] at hg'
    exact h.2 j g' hj hg'
  · by_cases hje : j = gs.length
    · subst hje
      simp at hg'
      subst hg'
      exact hg
    · have : (gs ++ [g])[j]? = none := by
        rw [List.getElem?_eq_none_iff]; simp; omega
      rw [this] at hg'; cases hg'

/-- The value of an old wire in the form is its value in `D'`. -/
theorem tr_val_old {D D' : Dag N} {gs : List G} (hB : tr_Base D D' gs) {u : ℕ}
    (hu : u < N + N + D'.size) (x : Fin (N + N) → Bool) :
    (⟨gs, D.out⟩ : Dag N).val x u = D'.val x u :=
  tr_val_prefix hB.1 D'.out D.out x u hu

/-! ### The contexts as wires -/

open Classical in
/-- The context wire of `b` (below the last gate of `D'`), if any. -/
noncomputable def tr_psi (D D' : Dag N) (b : ℕ) : Option ℕ :=
  if h : ∃ i, i < N + N + D'.size ∧ D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
      D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size)
  then some h.choose else none

theorem tr_psi_some {D D' : Dag N} {b i : ℕ} (h : tr_psi D D' b = some i) :
    i < N + N + D'.size ∧ D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
      D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size) := by
  unfold tr_psi at h
  split_ifs at h with hh
  cases h
  exact hh.choose_spec

theorem tr_psi_none {D D' : Dag N}
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {b : ℕ} (hb : D.IsItem b) (h : tr_psi D D' b = none) :
    (∀ x, D.ctx b x = true) ∨ (∀ x, D.ctx b x = false) := by
  rcases hit b hb with h1 | ⟨i, hi0, hiv, hic⟩
  · exact Or.inl h1
  · right
    intro x
    by_contra hx
    have hx' : D'.val x i = true := by rw [hiv]; simpa using hx
    have hlt := tr_val_lt hx'
    unfold tr_psi at h
    rw [dif_pos ⟨i, hlt, hi0, hiv, hic⟩] at h
    cases h

theorem tr_old_psi {D D' : Dag N} {b i : ℕ} (h : tr_psi D D' b = some i) : tr_Old D D' i := by
  classical
  obtain ⟨hlt, h0, -, hc⟩ := tr_psi_some h
  refine ⟨hlt, by omega, fun m hr hm => ?_⟩
  have hmi := tr_reach_le hr
  have hmc : m ∈ D'.coneOf {i} := by
    unfold Dag.coneOf
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨by omega, hm, i, rfl, hr⟩
  rcases Finset.mem_union.1 (hc hmc) with h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Finset.mem_Ico.1 h1))

theorem tr_old_kid {D D' : Dag N} (hpre : D.gates <+: D'.gates) {b r : ℕ} (hb : b ∈ D.cone)
    (hk : D.Kid b r) (hd : D.deg r ≤ 1) : tr_Old D D' r := by
  classical
  have hbl := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out} hb)
  have hrb : r < b := by obtain ⟨_, _, _, hlt⟩ := hk; exact hlt
  have hsz : D.size ≤ D'.size := hpre.length_le
  have hrl : r < N + N + D.gates.length := by unfold Dag.size at hbl; omega
  have hreach : D.Reach D.out b := by
    unfold Dag.cone Dag.coneOf at hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hb
    obtain ⟨-, -, r0, rfl, h⟩ := hb
    exact h
  refine ⟨by omega, ?_, fun m hr hm => ?_⟩
  · rw [tr_deg_prefix hpre D.out D'.out r hrl]; exact hd
  · have hr' : D.Reach r m := tr_reach_prefix hpre D.out D'.out hrl hr
    have hml := tr_reach_le hr'
    have hcone : m ∈ D.cone := tr_mem_cone hm (by omega) ((hreach.tail hk).trans hr')
    have hdm := le_trans (Api.api_reach_deg D hr') hd
    by_cases h0 : D.deg m = 0
    · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨hcone, h0⟩))
    · exact Or.inl (Finset.mem_filter.2 ⟨hcone, by omega⟩)

/-! ### The other factor -/

def tr_other (D : Dag N) (b r : ℕ) : ℕ :=
  match D.gateAt b with
  | some (.and a a') => if r = a then a' else a
  | _ => r

theorem tr_other_spec {D : Dag N} (hwf : D.WF) {b r : ℕ} (hb : b ∈ D.Tmix) (hk : D.Kid b r) :
    D.Kid b (tr_other D b r) ∧ D.deg (tr_other D b r) = 1 ∧
      ∀ x, D.IsFactor b x → x ≠ r → x = tr_other D b r := by
  classical
  obtain ⟨hT, a, a', hg, h1, h2⟩ := Finset.mem_filter.1 hb
  have ha := hwf _ _ hg a (by simp [G.kids])
  have ha' := hwf _ _ hg a' (by simp [G.kids])
  have hT2 := (Finset.mem_filter.1 hT).2
  have ho : tr_other D b r = if r = a then a' else a := by simp only [tr_other, hg]
  obtain ⟨g, hg1, hr1, -⟩ := hk
  rw [hg] at hg1
  cases hg1
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hr1
  rw [ho]
  refine ⟨?_, ?_, fun x hx hxr => ?_⟩
  · split_ifs
    · exact tr_kid_of hg (by simp [G.kids]) ha'
    · exact tr_kid_of hg (by simp [G.kids]) ha
  · split_ifs <;> assumption
  · rcases hx with ⟨h3, -⟩ | ⟨-, g, hg2, hx2, -⟩
    · omega
    · rw [hg] at hg2
      cases hg2
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hx2
      split_ifs with hra
      · rcases hx2 with rfl | rfl
        · exact absurd hra.symm hxr
        · rfl
      · rcases hx2 with rfl | rfl
        · rfl
        · rcases hr1 with rfl | rfl
          · exact absurd rfl hra
          · exact absurd rfl hxr

/-! ### One job -/

open Classical in
/-- The term of the job `(b, r)`, appended to `gs` when it needs a gate. -/
noncomputable def tr_term (D D' : Dag N) (gs : List G) (b r : ℕ) : List G × Option ℕ :=
  if D.deg b ≤ 1 then (gs, tr_psi D D' b)
  else
    match tr_psi D D' b with
    | some i => (gs ++ [.and i (tr_other D b r)], some (N + N + gs.length))
    | none => (gs, if ∀ x, D.ctx b x = true then some (tr_other D b r) else none)

/-- Merge a term into the root of line `w`. -/
def tr_put (N : ℕ) (gs : List G) (ρ : Fin N → Option ℕ) (w : Fin N) :
    Option ℕ → List G × (Fin N → Option ℕ)
  | none => (gs, ρ)
  | some v =>
    match ρ w with
    | none => (gs, Function.update ρ w (some v))
    | some u => (gs ++ [.or u v], Function.update ρ w (some (N + N + gs.length)))

noncomputable def tr_job (D D' : Dag N) (st : List G × (Fin N → Option ℕ))
    (j : ℕ × ℕ × Fin N) : List G × (Fin N → Option ℕ) :=
  tr_put N (tr_term D D' st.1 j.1 j.2.1).1 st.2 j.2.2 (tr_term D D' st.1 j.1 j.2.1).2

/-- The job `(b, r, w)` is live at `p`. -/
def tr_Cond (D : Dag N) (j : ℕ × ℕ × Fin N) (p : Fin N) : Prop :=
  D.ctx j.1 (pt p) = true ∧ ∀ x, D.IsFactor j.1 x → D.val (ep p j.2.2) x = true

/-- The cost of a job: one gate, two for an item of T_mix. -/
def tr_cost (D : Dag N) (j : ℕ × ℕ × Fin N) : ℕ := if D.deg j.1 ≤ 1 then 1 else 2

/-- `u` read under `y_w` is below the edge function, in the gate list `gs`. -/
def tr_Snd (I : Fin N → Fin N → Prop) (D : Dag N) (gs : List G) (w : Fin N) (u : ℕ) : Prop :=
  ∀ z, z (Fin.natAdd N w) = true → (⟨gs, D.out⟩ : Dag N).val z u = true →
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

theorem tr_val_lift {D D' : Dag N} {gs gs' : List G} (hB : tr_Base D D' gs) (hp : gs <+: gs')
    {u : ℕ} (hu : tr_Good4 D D' gs.length u) (x : Fin (N + N) → Bool) :
    (⟨gs', D.out⟩ : Dag N).val x u = (⟨gs, D.out⟩ : Dag N).val x u :=
  tr_val_prefix hp D.out D.out x u (tr_Good4_lt hu hB.1.length_le)

theorem tr_lift {I : Fin N → Fin N → Prop} {D D' : Dag N} {gs gs' : List G}
    (hB : tr_Base D D' gs) (hp : gs <+: gs') {w : Fin N} {u : ℕ}
    (hu : tr_Good4 D D' gs.length u ∧ tr_Snd I D gs w u) :
    tr_Good4 D D' gs'.length u ∧ tr_Snd I D gs' w u := by
  refine ⟨tr_Good4_mono hu.1 hp.length_le, fun z hz hv => hu.2 z hz ?_⟩
  rwa [tr_val_lift hB hp hu.1] at hv

theorem tr_term_ok (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {gs : List G} (hB : tr_Base D D' gs) {b r : ℕ} {w : Fin N}
    (hj : (b, r, w) ∈ tr_jobs D) :
    tr_Base D D' (tr_term D D' gs b r).1 ∧ gs <+: (tr_term D D' gs b r).1 ∧
      (tr_term D D' gs b r).1.length + 1 ≤ gs.length + tr_cost D (b, r, w) ∧
      (∀ v, (tr_term D D' gs b r).2 = some v →
        tr_Good4 D D' (tr_term D D' gs b r).1.length v ∧ tr_Snd I D (tr_term D D' gs b r).1 w v) ∧
      (∀ p, tr_Cond D (b, r, w) p → ∃ v, (tr_term D D' gs b r).2 = some v ∧
        (⟨(tr_term D D' gs b r).1, D.out⟩ : Dag N).val (ep p w) v = true) := by
  classical
  obtain ⟨hb, hr, hm⟩ := tr_mem_jobs.1 hj
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  have hxo : ∀ p, ∀ q : Fin N, pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) :=
    fun p q => tr_pt_ep p w q
  by_cases h1 : D.deg b ≤ 1
  · have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega
    subst hrb
    have e : tr_term D D' gs r r = (gs, tr_psi D D' r) := by
      unfold tr_term; rw [if_pos h1]
    have hcost : tr_cost D (r, r, w) = 1 := by unfold tr_cost; rw [if_pos h1]
    rw [e, hcost]
    refine ⟨hB, List.prefix_refl _, le_rfl, fun v hv => ?_, fun p hp => ?_⟩
    · have hold := tr_old_psi hv
      obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hv
      refine ⟨Or.inl hold, fun z hz hvz => ?_⟩
      rw [tr_val_old hB hlt, hval] at hvz
      exact tr_term_sound I hwf hc hd hb hm z hz hvz (fun x hx hxr => by
        rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
        · exact absurd rfl hxr
        · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
    · cases hps : tr_psi D D' r with
      | none =>
        rcases tr_psi_none hit hb hps with hall | hall
        · exact absurd hall (tr_no_const I hwf hc hd hb h1 hm)
        · have := hp.1; rw [hall] at this; cases this
      | some v =>
        obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hps
        refine ⟨v, rfl, ?_⟩
        rw [tr_val_old hB hlt, hval, ← tr_ctx_xonly (hxo p)]
        exact hp.1
  · have hbm : b ∈ D.Tmix := by
      rcases hb.2 with h | h
      · exact absurd h h1
      · exact h
    have hkr : D.Kid b r := by
      rcases hr with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h h1
      · exact h
    obtain ⟨hko, hdo, hfo⟩ := tr_other_spec hwf hbm hkr
    have hbc : b ∈ D.cone := (Finset.mem_filter.1 (Finset.mem_filter.1 hbm).1).1
    have hoo : tr_Old D D' (tr_other D b r) := tr_old_kid hpre hbc hko (by omega)
    have hol := hoo.1
    have hoD : (tr_other D b r) < N + N + D.gates.length := by
      have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out} hbc)
      obtain ⟨_, _, _, hlt⟩ := hko
      unfold Dag.size at this; omega
    have hvo : ∀ (gs' : List G), tr_Base D D' gs' → ∀ x,
        (⟨gs', D.out⟩ : Dag N).val x (tr_other D b r) = D.val x (tr_other D b r) := by
      intro gs' hB' x
      rw [tr_val_old hB' hol]
      exact tr_val_prefix hpre D.out D'.out x _ hoD
    have hrest : ∀ z, D.val z (tr_other D b r) = true →
        ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true := by
      intro z hz x hx hxr
      rw [hfo x hx hxr]; exact hz
    have hcost : tr_cost D (b, r, w) = 2 := by unfold tr_cost; dsimp only; rw [if_neg h1]
    rw [hcost]
    cases hps : tr_psi D D' b with
    | some i =>
      have e : tr_term D D' gs b r =
          (gs ++ [.and i (tr_other D b r)], some (N + N + gs.length)) := by
        unfold tr_term; rw [if_neg h1, hps]
      rw [e]
      obtain ⟨hlt, hi0, hval, -⟩ := tr_psi_some hps
      have hold := tr_old_psi hps
      have hB' := tr_Base_append hB (g := .and i (tr_other D b r)) (Or.inl ⟨_, _, rfl, hold, hi0, hoo⟩)
      have hgate := tr_gateAt_last (N := N) gs (.and i (tr_other D b r)) D.out
      have hv : ∀ z, (⟨gs ++ [.and i (tr_other D b r)], D.out⟩ : Dag N).val z (N + N + gs.length) =
          (D.ctx b z && D.val z (tr_other D b r)) := by
        intro z
        rw [tr_val_and hgate (by omega) (by omega), tr_val_old hB' hlt, hval, hvo _ hB']
      refine ⟨hB', List.prefix_append _ _, by simp, fun v hv' => ?_, fun p hp => ?_⟩
      · cases hv'
        refine ⟨Or.inr ⟨by omega, by simp⟩, fun z hz hvz => ?_⟩
        rw [hv, Bool.and_eq_true] at hvz
        exact tr_term_sound I hwf hc hd hb hm z hz hvz.1 (hrest z hvz.2)
      · refine ⟨_, rfl, ?_⟩
        rw [hv, Bool.and_eq_true, ← tr_ctx_xonly (hxo p)]
        exact ⟨hp.1, hp.2 _ (Or.inr ⟨hbm, hko⟩)⟩
    | none =>
      by_cases hall : ∀ x, D.ctx b x = true
      · have e : tr_term D D' gs b r = (gs, some (tr_other D b r)) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_pos hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega, fun v hv' => ?_, fun p hp => ?_⟩
        · cases hv'
          refine ⟨Or.inl hoo, fun z hz hvz => ?_⟩
          rw [hvo _ hB] at hvz
          exact tr_term_sound I hwf hc hd hb hm z hz (hall z) (hrest z hvz)
        · refine ⟨_, rfl, ?_⟩
          rw [hvo _ hB]
          exact hp.2 _ (Or.inr ⟨hbm, hko⟩)
      · have e : tr_term D D' gs b r = (gs, none) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_neg hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega,
          fun v hv' => absurd hv' (by simp), fun p hp => ?_⟩
        rcases tr_psi_none hit hb hps with h2 | h2
        · exact absurd h2 hall
        · have := hp.1; rw [h2] at this; cases this

theorem tr_put_ok {I : Fin N → Fin N → Prop} {D D' : Dag N} {gs : List G}
    (hB : tr_Base D D' gs) {ρ : Fin N → Option ℕ}
    (hρ : ∀ w u, ρ w = some u → tr_Good4 D D' gs.length u ∧ tr_Snd I D gs w u)
    {w : Fin N} {t : Option ℕ}
    (ht : ∀ v, t = some v → tr_Good4 D D' gs.length v ∧ tr_Snd I D gs w v) :
    tr_Base D D' (tr_put N gs ρ w t).1 ∧ gs <+: (tr_put N gs ρ w t).1 ∧
      (tr_put N gs ρ w t).1.length ≤ gs.length + 1 ∧
      (∀ w0 u, (tr_put N gs ρ w t).2 w0 = some u →
        tr_Good4 D D' (tr_put N gs ρ w t).1.length u ∧ tr_Snd I D (tr_put N gs ρ w t).1 w0 u) ∧
      (∀ w0 u z, ρ w0 = some u → (⟨gs, D.out⟩ : Dag N).val z u = true →
        ∃ u', (tr_put N gs ρ w t).2 w0 = some u' ∧
          (⟨(tr_put N gs ρ w t).1, D.out⟩ : Dag N).val z u' = true) ∧
      (∀ v z, t = some v → (⟨gs, D.out⟩ : Dag N).val z v = true →
        ∃ u', (tr_put N gs ρ w t).2 w = some u' ∧
          (⟨(tr_put N gs ρ w t).1, D.out⟩ : Dag N).val z u' = true) := by
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  cases t with
  | none =>
    simp only [tr_put]
    exact ⟨hB, List.prefix_refl _, by omega, hρ, fun w0 u z h hv => ⟨u, h, hv⟩,
      fun v z h => by cases h⟩
  | some v =>
    obtain ⟨hvg, hvs⟩ := ht v rfl
    cases hw : ρ w with
    | none =>
      simp only [tr_put, hw]
      refine ⟨hB, List.prefix_refl _, by omega, fun w0 u h => ?_, fun w0 u z h hv => ?_,
        fun v' z h hv => ?_⟩
      · by_cases e : w0 = w
        · subst e; rw [Function.update_self] at h; cases h; exact ⟨hvg, hvs⟩
        · rw [Function.update_of_ne e] at h; exact hρ w0 u h
      · by_cases e : w0 = w
        · subst e; rw [hw] at h; cases h
        · exact ⟨u, by rw [Function.update_of_ne e]; exact h, hv⟩
      · cases h; exact ⟨v, Function.update_self _ _ _, hv⟩
    | some u0 =>
      simp only [tr_put, hw]
      obtain ⟨hug, hus⟩ := hρ w u0 hw
      have hp : gs <+: gs ++ [G.or u0 v] := List.prefix_append _ _
      have hB' := tr_Base_append hB (Or.inr ⟨u0, v, rfl, hug, hvg⟩)
      have hul := tr_Good4_lt hug hsz
      have hvl := tr_Good4_lt hvg hsz
      have hnew : ∀ z, (⟨gs ++ [G.or u0 v], D.out⟩ : Dag N).val z (N + N + gs.length) =
          ((⟨gs, D.out⟩ : Dag N).val z u0 || (⟨gs, D.out⟩ : Dag N).val z v) := by
        intro z
        rw [tr_val_or (tr_gateAt_last gs _ D.out) hul hvl, tr_val_lift hB hp hug,
          tr_val_lift hB hp hvg]
      refine ⟨hB', hp, by simp, fun w0 u h => ?_, fun w0 u z h hv => ?_,
        fun v' z h hv => ?_⟩
      · by_cases e : w0 = w
        · subst e
          rw [Function.update_self] at h
          cases h
          refine ⟨Or.inr ⟨by omega, by simp⟩, fun z hz hvz => ?_⟩
          rw [hnew, Bool.or_eq_true] at hvz
          rcases hvz with h1 | h1
          · exact hus z hz h1
          · exact hvs z hz h1
        · rw [Function.update_of_ne e] at h
          exact tr_lift hB hp (hρ w0 u h)
      · by_cases e : w0 = w
        · subst e
          rw [hw] at h
          cases h
          refine ⟨_, Function.update_self _ _ _, ?_⟩
          rw [hnew, hv]; rfl
        · refine ⟨u, by rw [Function.update_of_ne e]; exact h, ?_⟩
          rw [tr_val_lift hB hp (hρ w0 u h).1]; exact hv
      · cases h
        refine ⟨_, Function.update_self _ _ _, ?_⟩
        rw [hnew, hv]; simp

/-- The invariant after the jobs of the list `Pl`. -/
def tr_Inv4 (I : Fin N → Fin N → Prop) (D D' : Dag N) (st : List G × (Fin N → Option ℕ))
    (Pl : List (ℕ × ℕ × Fin N)) : Prop :=
  tr_Base D D' st.1 ∧ st.1.length ≤ D'.size + (Pl.map (tr_cost D)).sum ∧
    (∀ w u, st.2 w = some u → tr_Good4 D D' st.1.length u ∧ tr_Snd I D st.1 w u) ∧
    (∀ j ∈ Pl, ∀ p, tr_Cond D j p → ∃ u, st.2 j.2.2 = some u ∧
      (⟨st.1, D.out⟩ : Dag N).val (ep p j.2.2) u = true)

theorem tr_job_ok (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {st : List G × (Fin N → Option ℕ)} {Pl : List (ℕ × ℕ × Fin N)}
    (hI : tr_Inv4 I D D' st Pl) {j : ℕ × ℕ × Fin N} (hj : j ∈ tr_jobs D) :
    tr_Inv4 I D D' (tr_job D D' st j) (Pl ++ [j]) := by
  obtain ⟨gs, ρ⟩ := st
  obtain ⟨b, r, w⟩ := j
  obtain ⟨hB, hlen, hρ, hcov⟩ := hI
  dsimp only at hB hlen hρ hcov
  obtain ⟨hB1, hp1, hl1, ht1, hc1⟩ := tr_term_ok I hwf hc hd hpre hit hB hj
  unfold tr_job
  dsimp only
  generalize tr_term D D' gs b r = t at hB1 hp1 hl1 ht1 hc1 ⊢
  obtain ⟨gs1, t⟩ := t
  dsimp only at hB1 hp1 hl1 ht1 hc1 ⊢
  have hρ1 : ∀ w u, ρ w = some u → tr_Good4 D D' gs1.length u ∧ tr_Snd I D gs1 w u :=
    fun w u h => tr_lift hB hp1 (hρ w u h)
  obtain ⟨hB2, hp2, hl2, hρ2, hmono, hnew⟩ := tr_put_ok hB1 hρ1 ht1
  generalize tr_put N gs1 ρ w t = st2 at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  obtain ⟨gs2, ρ2⟩ := st2
  dsimp only at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  refine ⟨hB2, ?_, hρ2, ?_⟩
  · rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · intro j hj p hp
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨u, hu, hv⟩ := hcov j hj p hp
      exact hmono _ u _ hu (by rw [tr_val_lift hB hp1 (hρ _ u hu).1]; exact hv)
    · simp only [List.mem_singleton] at hj
      subst hj
      obtain ⟨v, hv, hvv⟩ := hc1 p hp
      exact hnew v _ hv hvv

theorem tr_fold4 (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size)) :
    ∀ (L : List (ℕ × ℕ × Fin N)) st Pl, (∀ j ∈ L, j ∈ tr_jobs D) → tr_Inv4 I D D' st Pl →
      tr_Inv4 I D D' (L.foldl (tr_job D D') st) (Pl ++ L) := by
  intro L
  induction L with
  | nil => intro st Pl _ hI; simpa using hI
  | cons j t ih =>
    intro st Pl hL hI
    rw [List.foldl_cons, show Pl ++ j :: t = (Pl ++ [j]) ++ t by simp]
    exact ih _ _ (fun j' h => hL j' (List.mem_cons_of_mem _ h))
      (tr_job_ok I hwf hc hd hpre hit hI (hL j (by simp)))

theorem tr_wf4 {D D' : Dag N} (hwf' : D'.WF) {gs : List G} (hB : tr_Base D D' gs) (o : ℕ) :
    (⟨gs, o⟩ : Dag N).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg'⟩ := Api.gateAt_some hg
  dsimp only at hg'
  by_cases hj : i - (N + N) < D'.size
  · have e : (⟨gs, o⟩ : Dag N).gateAt i = (⟨D'.gates, D'.out⟩ : Dag N).gateAt i :=
      tr_gateAt_prefix hB.1 D'.out o (by unfold Dag.size at hj; omega)
    rw [e] at hg
    exact hwf' i g hg c hc
  · rcases hB.2 _ g (by omega) hg' with ⟨u, v, rfl, hu, -, hv⟩ | ⟨u, v, rfl, hu, hv⟩
    · have := hu.1; have := hv.1
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> omega
    · have := tr_Good4_lt hu (by omega)
      have := tr_Good4_lt hv (by omega)
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> omega

theorem tr_old_kid' {D D' : Dag N} {n m : ℕ} (hn : tr_Old D D' n) (hk : D'.Kid n m) :
    tr_Old D D' m := by
  obtain ⟨hl, hd, hr⟩ := hn
  have hml : m < n := by obtain ⟨_, _, _, h⟩ := hk; exact h
  refine ⟨by omega, le_trans (Api.deg_kid hk) hd, fun m' hr' hm' => ?_⟩
  exact hr m' (Relation.ReflTransGen.head hk hr') hm'

theorem tr_good4_final {D D' : Dag N} {gs : List G} (hB : tr_Base D D' gs) (o : ℕ) :
    ∀ n, tr_Good4 D D' gs.length n → (⟨gs, o⟩ : Dag N).deg n ≤ 1 ∧
      ∀ m, (⟨gs, o⟩ : Dag N).Kid n m → tr_Good4 D D' gs.length m := by
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  have hdeg_old : ∀ u, tr_Old D D' u → (⟨gs, o⟩ : Dag N).deg u = D'.deg u := fun u hu =>
    tr_deg_prefix hB.1 D'.out o u hu.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases hn with hn | ⟨hn1, hn2⟩
  · refine ⟨by rw [hdeg_old n hn]; exact hn.2.1, fun m hk => ?_⟩
    obtain ⟨g, hg, hmg, hmn⟩ := hk
    rw [tr_gateAt_prefix hB.1 D'.out o hn.1] at hg
    exact Or.inl (tr_old_kid' hn ⟨g, hg, hmg, hmn⟩)
  · cases hgs : gs[n - (N + N)]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hgs
      omega
    | some g =>
      have hgate : (⟨gs, o⟩ : Dag N).gateAt n = some g := by
        unfold Dag.gateAt
        rw [if_pos (by omega)]
        exact hgs
      rcases hB.2 _ g (by unfold Dag.size at hn1 ⊢; omega) hgs with
        ⟨u, v, rfl, hu, hu0, hv⟩ | ⟨u, v, rfl, hu, hv⟩
      · have hun : u < n := by have := hu.1; omega
        have hvn : v < n := by have := hv.1; omega
        refine ⟨?_, fun m hk => ?_⟩
        · rw [tr_deg_and hgate hun hvn, hdeg_old u hu, hdeg_old v hv, hu0]
          have := hv.2.1; omega
        · obtain ⟨g', hg', hmg, -⟩ := hk
          rw [hgate] at hg'
          cases hg'
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg
          rcases hmg with rfl | rfl
          · exact Or.inl hu
          · exact Or.inl hv
      · have hj : n - (N + N) ≤ gs.length := by omega
        have hun : u < n := by have := tr_Good4_lt hu (by unfold Dag.size at hn1 ⊢; omega); omega
        have hvn : v < n := by have := tr_Good4_lt hv (by unfold Dag.size at hn1 ⊢; omega); omega
        have hu2 := tr_Good4_mono hu hj
        have hv2 := tr_Good4_mono hv hj
        refine ⟨?_, fun m hk => ?_⟩
        · rw [tr_deg_or hgate hun hvn]
          have := (ih u hun hu2).1
          have := (ih v hvn hv2).1
          omega
        · obtain ⟨g', hg', hmg, -⟩ := hk
          rw [hgate] at hg'
          cases hg'
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg
          rcases hmg with rfl | rfl
          · exact hu2
          · exact hv2

/-- D2-16 (constant 48 version). The form built from the marker terms: sound, covers the marker
edges, of size at most `|M| + |X| + 4 |T|`. -/
theorem card16_form (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
      D.markerEdges I ⊆ F.countedEdges W R ∧
      (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card := by
  classical
  obtain ⟨D', hpre, hwf', hsz', hit⟩ := card15c_contexts D hwf hd
  have hinit : tr_Inv4 I D D' (D'.gates, fun _ => none) [] := by
    refine ⟨⟨List.prefix_refl _, fun j g hj hg => ?_⟩, by simp [Dag.size], ?_, ?_⟩
    rotate_left
    · intro w u h; simp at h
    · intro j hj; simp at hj
    have : D'.gates[j]? = none :=
      List.getElem?_eq_none_iff.2 (by unfold Dag.size at hj; omega)
    rw [this] at hg
    cases hg
  have hfin := tr_fold4 I hwf hc hd hpre hit (tr_jobs D).toList _ []
    (fun j hj => Finset.mem_toList.1 hj) hinit
  rw [List.nil_append] at hfin
  generalize List.foldl (tr_job D D') (D'.gates, fun _ => none) (tr_jobs D).toList = st at hfin
  obtain ⟨hB, hlen, hρ, hcov⟩ := hfin
  have hroot : ∀ w, (st.2 w).isSome → ∃ u, st.2 w = some u := fun w h =>
    Option.isSome_iff_exists.1 h
  refine ⟨⟨st.1, D.out⟩, Finset.univ.filter (fun w => (st.2 w).isSome),
    fun w => (st.2 w).getD 0, ⟨tr_wf4 hwf' hB D.out, ?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some]
    exact (tr_good4_final hB D.out u (hρ w u hu).1).1
  · rintro z ⟨w, hw, hz, hv⟩
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some] at hv
    exact (hρ w u hu).2 z hz hv
  · rintro ⟨p, w⟩ he
    unfold Dag.markerEdges at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨-, b, hb, hctx, hfac, r, hr, hm⟩ := he
    have hj : (b, r, w) ∈ (tr_jobs D).toList :=
      Finset.mem_toList.2 (tr_mem_jobs.2 ⟨hb, hr, hm⟩)
    obtain ⟨u, hu, hv⟩ := hcov _ hj p ⟨hctx, hfac⟩
    unfold Dag.countedEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only at hu hv
    refine ⟨by simp [hu], ?_⟩
    simp only [hu, Option.getD_some]
    exact hv
  · have hsz : D'.size ≤ st.1.length := hB.1.length_le
    have hDD : D.size ≤ D'.size := hpre.length_le
    have hsub : (⟨st.1, D.out⟩ : Dag N).rootCone (Finset.univ.filter (fun w => (st.2 w).isSome))
        (fun w => (st.2 w).getD 0) ⊆
        (D.M ∪ D.X) ∪ Finset.Ico (N + N + D.size) (N + N + st.1.length) := by
      intro m hm
      unfold Dag.rootCone Dag.coneOf at hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hm
      obtain ⟨-, hm1, r, ⟨w, hw, rfl⟩, hr⟩ := hm
      obtain ⟨u, hu⟩ := hroot w hw.2
      simp only [hu, Option.getD_some] at hr
      have hg : tr_Good4 D D' st.1.length m := by
        clear hm1
        induction hr with
        | refl => exact (hρ w u hu).1
        | tail _ hk ih => exact (tr_good4_final hB D.out _ ih).2 _ hk
      rcases hg with hold | hnew
      · rcases hold.2.2 m Relation.ReflTransGen.refl hm1 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨h.1, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨by omega, hnew.2⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (D.M ∪ D.X) (Finset.Ico (N + N + D.size) (N + N + st.1.length))
    have h3 := Finset.card_union_le D.M D.X
    have h4 : (Finset.Ico (N + N + D.size) (N + N + st.1.length)).card =
        st.1.length - D.size := by rw [Nat.card_Ico]; omega
    have hsum : ((tr_jobs D).toList.map (tr_cost D)).sum =
        ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card +
          2 * ((tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1)).card := by
      rw [Finset.sum_map_toList]
      unfold tr_cost
      rw [Finset.sum_ite]
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hj1 := tr_jobs1_card I hwf hc hd
    have hj2 := tr_jobs2_card (D := D)
    have hT := tr_T_split D
    show ((⟨st.1, D.out⟩ : Dag N).rootCone _ _).card ≤ _
    omega

end PEqualNP.MetaComplexity.Deg2
