import PEqualNP.MetaComplexity.Helpers.Deg2Circuit
import PEqualNP.MetaComplexity.Helpers.HonestFactor

/-!
# The universal cover at degree two: card D2-17 (cover), from the identity of D2-15

Conjecture until the checker accepts it. `cv_cover_of_identity` proves the statement of
`card17_cover` of the skeleton plan (the degree-two card plan) under one extra
hypothesis: the exact statement of `card15_identity` of the same plan.

Proof (builder sheet, card D2-17): the edge input `e_p + e_w` is accepted, so by the identity an
item `b` is alive there; by the honest factor lemma (D2-02, `HonestFactor.main`, with the context of
`b` as the point-only part) some factor `r` of `b` is p-honest, of degree 1; the honest path
(D2-06, `card06_honest_path`) runs from `r` to `y_w`. Below the last labelled wire of the path (or
from `r` when there is none) every step is an OR of degree 1, so `w` is in `V*` of that wire. Two
lines in `V*`: pinned. One line: below a labelled wire `AND(f, v)` the label has a dead set
(cleaned), so the pair is served (at most two alive points of `f` on `w`) or in `F_2` (three or
more); with no labelled wire, `r` is a marker of `w` and the pair is a marker edge.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.MetaComplexity.Deg2.Api PEqualNP.MetaComplexity.Deg2.Path

variable {N : ℕ}

/-! ## The top pass -/

theorem cv_top_mono (D : Dag N) {ok ok' : ℕ → Prop} (h : ∀ f, D.deg f = 0 → ok f → ok' f)
    {b : ℕ} (hb : D.Top ok b) : D.Top ok' b := by
  induction hb with
  | root => exact Dag.Top.root
  | orStep _ hT hk hd ih => exact Dag.Top.orStep ih hT hk hd
  | andStep _ hT hg hf hc hfh hch hok ih =>
    exact Dag.Top.andStep ih hT hg hf hc hfh hch (h _ hf hok)

theorem cv_top_reach (D : Dag N) {ok : ℕ → Prop} {b : ℕ} (hb : D.Top ok b) :
    D.Reach D.out b := by
  induction hb with
  | root => exact Relation.ReflTransGen.refl
  | orStep _ _ hk _ ih => exact ih.tail hk
  | andStep _ _ hg _ _ _ hch _ ih =>
    rcases hg with hg | hg
    · exact ih.tail (circ_kid_of hg (by simp [G.kids]) hch)
    · exact ih.tail (circ_kid_of hg (by simp [G.kids]) hch)

theorem cv_ctx_pts (D : Dag N) (b : ℕ) {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.ctx b x = D.ctx b y := by
  unfold Dag.ctx
  rw [decide_eq_decide]
  constructor
  · exact cv_top_mono D (fun f hf hok => by rw [← api_val_xonly D hf h]; exact hok)
  · exact cv_top_mono D (fun f hf hok => by rw [api_val_xonly D hf h]; exact hok)

theorem cv_ctx_mono (D : Dag N) (b : ℕ) : Monotone (D.ctx b) := by
  intro x y hxy
  by_cases hx : D.ctx b x = true
  · have hy : D.ctx b y = true := by
      simp only [Dag.ctx, decide_eq_true_eq] at hx ⊢
      exact cv_top_mono D (fun f _ hok => by
        have := api_val_mono D f hxy
        rw [hok] at this
        exact HonestFactor.eq_true_of_true_le' this) hx
    rw [hy]
    exact le_top
  · rw [Bool.not_eq_true] at hx
    rw [hx]
    exact Bool.false_le _

/-! ## Inputs as in the honest factor lemma -/

theorem cv_natAdd_ne_castAdd (j p : Fin N) : Fin.natAdd N j ≠ Fin.castAdd N p :=
  fun h => HonestFactor.castAdd_ne_natAdd' p j h.symm

theorem cv_ep_eq (p w : Fin N) :
    ep p w = fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · unfold ep inp
    rw [Fin.addCases_left]
    simp only [Finset.mem_singleton, HonestFactor.castAdd_inj',
      HonestFactor.castAdd_ne_natAdd', or_false]
  · unfold ep inp
    rw [Fin.addCases_right]
    simp only [Finset.mem_singleton, HonestFactor.natAdd_inj', cv_natAdd_ne_castAdd, false_or]

theorem cv_pt_eq (p : Fin N) : pt p = fun k => decide (k = Fin.castAdd N p) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · unfold pt inp
    rw [Fin.addCases_left]
    simp only [Finset.mem_singleton, HonestFactor.castAdd_inj']
  · unfold pt inp
    rw [Fin.addCases_right]
    simp only [Finset.notMem_empty, cv_natAdd_ne_castAdd, decide_false]

theorem cv_ep_eq' (p u : Fin N) :
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) = ep p u :=
  (cv_ep_eq p u).symm

/-! ## The honest factor (D2-02) -/

theorem cv_honest_of_list (I : Fin N → Fin N → Prop) (D : Dag N) (hc : Computes I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) (ws : List ℕ)
    (hws : ∀ r, D.IsFactor b r ↔ r ∈ ws) :
    ∃ r ∈ ws, IsHonest I (fun x => D.val x r) p := by
  have key := HonestFactor.main N I (D.ctx b) (ws.map (fun r x => D.val x r)) p w
    (cv_ctx_mono D b) (fun z z' h => cv_ctx_pts D b h)
    (by
      intro f hfm
      simp only [List.mem_map] at hfm
      obtain ⟨r, -, rfl⟩ := hfm
      intro x y hxy
      exact api_val_mono D r hxy)
    (by
      intro z hz
      rw [Bool.and_eq_true, List.all_map, List.all_eq_true] at hz
      apply (hc z).1
      apply (hid z).2
      refine ⟨b, hb, hz.1, fun r hr => ?_⟩
      have := hz.2 r ((hws r).1 hr)
      simpa using this)
    (by
      rw [cv_ep_eq', Bool.and_eq_true, List.all_map, List.all_eq_true]
      refine ⟨hctx, fun r hr => ?_⟩
      have := hf r ((hws r).2 hr)
      simpa using this)
  obtain ⟨-, f, hfm, hf0, hfu⟩ := key
  simp only [List.mem_map] at hfm
  obtain ⟨r, hr, rfl⟩ := hfm
  refine ⟨r, hr, ?_, fun u hu => hfu u ?_⟩
  · rw [cv_pt_eq]; exact hf0
  · rw [cv_ep_eq']; exact hu

theorem cv_honest_factor (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) :
    ∃ r, D.IsFactor b r ∧ D.deg r = 1 ∧ IsHonest I (fun x => D.val x r) p := by
  classical
  rcases hb.2 with hb1 | hbt
  · have hws : ∀ r, D.IsFactor b r ↔ r ∈ [b] := by
      intro r
      constructor
      · rintro (⟨_, rfl⟩ | ⟨hT, _⟩)
        · simp
        · have : D.deg b = 2 := by
            unfold Dag.Tmix Dag.T at hT
            exact (Finset.mem_filter.1 (Finset.mem_filter.1 hT).1).2
          omega
      · intro hr
        simp only [List.mem_singleton] at hr
        exact Or.inl ⟨hb1, hr⟩
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list I D hc hid p w hb hctx hf [b] hws
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨r, Or.inl ⟨hb1, rfl⟩, ?_, hh⟩
    rcases Nat.lt_or_ge (D.deg r) 1 with h0 | h1
    · exfalso
      have e1 := hf r (Or.inl ⟨hb1, rfl⟩)
      rw [← api_val_xonly D (by omega) (x := pt p) (y := ep p w)
        (fun q => by rw [circ_ep_pts])] at e1
      have := hh.1
      simp only at this
      rw [this] at e1
      exact Bool.false_ne_true e1
    · omega
  · have hbt' := hbt
    unfold Dag.Tmix at hbt'
    obtain ⟨-, a, a', hg, ha1, ha1'⟩ := Finset.mem_filter.1 hbt'
    have hlt := hwf b _ hg
    have hal : a < b := hlt a (by simp [G.kids])
    have hal' : a' < b := hlt a' (by simp [G.kids])
    have hT2 : D.deg b = 2 := by
      unfold Dag.Tmix Dag.T at hbt
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hbt).1).2
    have hws : ∀ r, D.IsFactor b r ↔ r ∈ [a, a'] := by
      intro r
      constructor
      · rintro (⟨h, _⟩ | ⟨_, hk⟩)
        · omega
        · obtain ⟨g, hg', hrg, -⟩ := hk
          rw [hg] at hg'
          cases hg'
          simpa [G.kids] using hrg
      · intro hr
        refine Or.inr ⟨hbt, circ_kid_of hg ?_ ?_⟩
        · simpa [G.kids] using hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list I D hc hid p w ⟨hb.1, Or.inr hbt⟩ hctx hf [a, a'] hws
    refine ⟨r, (hws r).2 hr, ?_, hh⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption

/-! ## The cone -/

theorem cv_gate_lt (D : Dag N) {v : ℕ} {g : G} (hg : D.gateAt v = some g) :
    N + N ≤ v ∧ v < N + N + D.size := by
  obtain ⟨hi, hgs⟩ := gateAt_some hg
  have hlt : v - (N + N) < D.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hgs
    cases hgs
  exact ⟨hi, by unfold Dag.size; omega⟩

theorem cv_mem_cone (D : Dag N) {v : ℕ} (h1 : N + N ≤ v) (h2 : v < N + N + D.size)
    (hr : D.Reach D.out v) : v ∈ D.cone := by
  classical
  unfold Dag.cone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, exists_eq_left]
  exact ⟨h2, h1, hr⟩

theorem cv_path_reach (D : Dag N) {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) :
    ∀ j, j < π.length → D.Reach a (π.getD j 0) := by
  intro j
  induction j with
  | zero =>
    intro hj
    obtain ⟨hh, -, -⟩ := hp
    cases π with
    | nil => simp at hj
    | cons c rest =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      exact Relation.ReflTransGen.refl
  | succ j ih =>
    intro hj
    exact (ih (by omega)).tail (hp.2.2 j hj)

/-! ## Label-free steps -/

theorem cv_step (D : Dag N) (hwf : D.WF) {g c : ℕ} {w : Fin N} (hk : D.Kid g c)
    (hg1 : D.deg g = 1) (hc1 : D.deg c = 1) (hnl : ∀ f, ¬ D.LabAnd g f c)
    (hv : D.VReach c w) : D.VReach g w := by
  obtain ⟨G0, hG, hcG, hcg⟩ := hk
  cases G0 with
  | or a b => exact Dag.VReach.step ⟨a, b, hG⟩ hg1 ⟨_, hG, hcG, hcg⟩ hv
  | cst v => simp [G.kids] at hcG
  | and a b =>
    exfalso
    have hlt := hwf g _ hG
    have ha : a < g := hlt a (by simp [G.kids])
    have hb : b < g := hlt b (by simp [G.kids])
    have hd := circ_deg_and D hG ha hb
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcG
    rcases hcG with rfl | rfl
    · exact hnl b ⟨Or.inr hG, by omega, hc1⟩
    · exact hnl a ⟨Or.inl hG, by omega, hc1⟩

theorem cv_getLast (π : List ℕ) {b : ℕ} (h : π.getLast? = some b) :
    π.getD (π.length - 1) 0 = b := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]
  rfl

/-- Below a position with no labelled wire at or after it, the path reaches `y_w` through ORs of
degree 1. -/
theorem cv_vreach_suffix (D : Dag N) (hwf : D.WF) {π : List ℕ} {a : ℕ} {w : Fin N}
    (hp : D.IsPath π a (N + w.val)) (hdeg : ∀ v ∈ π, D.deg v = 1) :
    ∀ n j, j + n + 1 = π.length →
      (∀ k f, j ≤ k → k + 1 < π.length → ¬ D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)) →
      D.VReach (π.getD j 0) w := by
  intro n
  induction n with
  | zero =>
    intro j hj _
    have := cv_getLast π hp.2.1
    rw [show j = π.length - 1 by omega, this]
    exact Dag.VReach.leaf w
  | succ n ih =>
    intro j hj hnl
    have h1 := ih (j + 1) (by omega) (fun k f hk hk' => hnl k f (by omega) hk')
    have hk := hp.2.2 j (by omega)
    exact cv_step D hwf hk (hdeg _ (circ_getD_mem (by omega)))
      (hdeg _ (circ_getD_mem (by omega))) (fun f => hnl j f le_rfl (by omega)) h1

/-! ## The pinned case -/

theorem cv_vstar_mem {D : Dag N} {v : ℕ} {w : Fin N} (h : D.VReach v w) : w ∈ D.Vstar v := by
  classical
  unfold Dag.Vstar
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩

theorem cv_isOr_of_card (D : Dag N) {v : ℕ} {w : Fin N} (h : D.VReach v w)
    (h2 : 2 ≤ (D.Vstar v).card) : D.IsOr v := by
  classical
  cases h with
  | step hor _ _ _ => exact hor
  | leaf =>
    exfalso
    have : (D.Vstar (N + w.val)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      unfold Dag.Vstar at ha hb
      rw [Finset.mem_filter] at ha hb
      have h1 := circ_vreach_input D ha.2 (by omega)
      have h2 := circ_vreach_input D hb.2 (by omega)
      exact Fin.ext (by omega)
    omega

theorem cv_pinned (I : Fin N → Fin N → Prop) (D : Dag N) {v : ℕ} {p w : Fin N}
    (hv : D.VReach v w) (hr : D.Reach D.out v) (hd : D.deg v = 1)
    (hsub : D.Vstar v ⊆ pencil I p) (h2 : 2 ≤ (D.Vstar v).card) : (p, w) ∈ D.pinned I := by
  classical
  have hor := cv_isOr_of_card D hv h2
  obtain ⟨a, b, hg⟩ := hor
  have hlt := cv_gate_lt D hg
  have hcone := cv_mem_cone D hlt.1 hlt.2 hr
  have hOrM : v ∈ D.OrM := by
    unfold Dag.OrM Dag.M
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hcone, hd⟩, ⟨a, b, hg⟩⟩
  unfold Dag.pinned
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hOrM, ⟨⟨a, b, hg⟩, hd, h2, hsub⟩,
    cv_vstar_mem hv⟩

theorem cv_card_split {s : Finset (Fin N)} {w : Fin N} (hw : w ∈ s) :
    2 ≤ s.card ∨ s = {w} := by
  by_cases h : 2 ≤ s.card
  · exact Or.inl h
  · right
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hw, fun x hx => Finset.card_le_one.1 (by omega) x hx w hw⟩

/-! ## The cover, from the identity -/

/-- D2-17 (cover), under the statement of D2-15 (i) (`card15_identity`) as a hypothesis. -/
theorem cv_cover_of_identity
    (hid : ∀ (I : Fin N → Fin N → Prop) (D : Dag N), D.WF → Computes I D.fn →
      D.deg D.out ≤ 2 → ∀ (x : Fin (N + N) → Bool), D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone) :
    ∀ p w : Fin N, I p w →
      (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I := by
  classical
  intro p w hpw
  have hid' := hid I D hwf hc hd
  have hacc : D.fn (ep p w) = true := by
    apply (hc _).2
    refine ⟨p, w, hpw, ?_, ?_⟩
    · unfold ep inp; rw [Fin.addCases_left]; simp
    · unfold ep inp; rw [Fin.addCases_right]; simp
  obtain ⟨b, hb, hctx, hf⟩ := (hid' _).1 hacc
  obtain ⟨r, hfac, hr1, hh⟩ := cv_honest_factor I D hwf hc hid' p w hb hctx hf
  have hrw := hf r hfac
  obtain ⟨π, hπ, hπv, hlab, hpen⟩ := card06_honest_path I D r p w hr1 hh hrw
  have hdeg : ∀ v ∈ π, D.deg v = 1 := fun v hv => (hπv v hv).1
  have hreach_r : D.Reach D.out r := by
    rcases hfac with ⟨_, rfl⟩ | ⟨_, hk⟩
    · exact cv_top_reach D hb.1
    · exact (cv_top_reach D hb.1).tail hk
  have hreach : ∀ j, j < π.length → D.Reach D.out (π.getD j 0) :=
    fun j hj => hreach_r.trans (cv_path_reach D hπ j hj)
  have hlen : 0 < π.length := by
    cases π with
    | nil => simp [Dag.IsPath] at hπ
    | cons _ _ => simp
  have hhead : π.getD 0 0 = r := by
    obtain ⟨hh0, -, -⟩ := hπ
    cases π with
    | nil => simp at hh0
    | cons c _ => simpa using hh0
  simp only [Finset.mem_union]
  let P : ℕ → Prop := fun k => k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)
  by_cases hex : ∃ k, P k
  · -- I: a labelled wire on the path; the last one
    obtain ⟨k0, hk0⟩ := hex
    let K := Nat.findGreatest P π.length
    have hPK : P K := Nat.findGreatest_spec (P := P) (by have := hk0.1; omega) hk0
    have hmax : ∀ k, K < k → ¬ P k := by
      intro k hk hPk
      exact Nat.findGreatest_is_greatest hk (by have := hPk.1; omega) hPk
    obtain ⟨hK, f, hfl⟩ := hPK
    set e := π.getD K 0 with he
    set v := π.getD (K + 1) 0 with hv
    have hvr : D.VReach v w := by
      refine cv_vreach_suffix D hwf hπ hdeg (π.length - (K + 1) - 1) (K + 1) (by omega) ?_
      intro k f' hk hk' hl
      exact hmax k (by omega) ⟨hk', f', hl⟩
    have hvmem : v ∈ π := circ_getD_mem hK
    rcases cv_card_split (cv_vstar_mem hvr) with h2 | h1
    · left; left; left
      exact cv_pinned I D hvr (hreach _ hK) (hdeg v hvmem) (hpen v hvmem) h2
    · -- the labelled wire e = AND(f, v)
      obtain ⟨hgate, hf0, -⟩ := hfl
      have hemem : e ∈ π := circ_getD_mem (by omega)
      have hgE : ∃ g, D.gateAt e = some g := by
        rcases hgate with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨gE, hgE⟩ := hgE
      have hElt := cv_gate_lt D hgE
      have hEcone := cv_mem_cone D hElt.1 hElt.2 (hreach K (by omega))
      have hAndM : e ∈ D.AndM := by
        unfold Dag.AndM Dag.M
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hEcone, hdeg e hemem⟩, ?_⟩
        rcases hgate with h | h
        · exact ⟨_, _, h⟩
        · exact ⟨_, _, h⟩
      have hdead := hcl e hEcone f v ⟨hgate, hf0, hdeg v hvmem⟩
      have halive : p ∈ D.alive f := by
        unfold Dag.alive
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlab K f hK ⟨hgate, hf0, hdeg v hvmem⟩⟩
      by_cases hle : (D.alive f ∩ ptsOn I w).card ≤ 2
      · left; left; right
        unfold Dag.served
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hAndM, f, v,
          ⟨hgate, hf0, hdeg v hvmem⟩, h1, halive, hpw, hle⟩
      · left; right
        have hfk : D.Kid e f := by
          rcases hgate with h | h
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
        have hfgate : N + N ≤ f := by
          by_contra hlt
          have h1' := circ_alive_input D (i := f) (by omega)
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
            (s₂ := ptsOn I w))
          omega
        have hfcone : f ∈ D.cone :=
          cv_mem_cone D hfgate (by have := circ_kid_lt hfk; omega)
            ((hreach K (by omega)).tail hfk)
        unfold Dag.fSet
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, hfcone, hf0, hdead, halive,
          by show 2 + 1 ≤ (D.alive f ∩ ptsOn I w).card; omega⟩
  · -- II: no labelled wire on the path
    have hrv : D.VReach r w := by
      have := cv_vreach_suffix D hwf hπ hdeg (π.length - 1) 0 (by omega)
        (fun k f' _ hk' hl => hex ⟨k, hk', f', hl⟩)
      rwa [hhead] at this
    have hrmem : r ∈ π := by rw [← hhead]; exact circ_getD_mem hlen
    rcases cv_card_split (cv_vstar_mem hrv) with h2 | h1
    · left; left; left
      exact cv_pinned I D hrv hreach_r hr1 (hpen r hrmem) h2
    · right
      unfold Dag.markerEdges
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, b, hb, ?_, hf, r, hfac, hr1, h1⟩
      rw [cv_ctx_pts D b (y := ep p w) (fun q => by rw [circ_ep_pts])]
      exact hctx

end PEqualNP.MetaComplexity.Deg2
