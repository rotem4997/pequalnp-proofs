import PEqualNP.MetaComplexity.Helpers.Deg2Circuit
import PEqualNP.MetaComplexity.Helpers.Deg2Forms

/-!
# The beta count: card D2-13 (helper for L-meta-649)

Conjecture until the checker accepts it. `card13_beta` has the statement of the skeleton plan
(the degree-two card plan) verbatim.

Proof (paper: the paper text of the cards, section 3, in a simpler
form: the condition "LAST p-gate" is not used, only the p-gate with a beta child).

* A wire `v` is beta for `p` when a root `R u` of a line `u` off `p` reaches it by a path whose
  labels are true at `e_p`. A beta wire reaching `y_{u'}` through ORs of degree 1 has `u'`
  through `p` (soundness at the input with the point `p` and the lines `u, u'`).
* From the beta child of the p-gate, walk down to `y_w` along wires true at `e_p + e_w` and false
  at `e_p`; each step keeps the wire beta. At the last labelled step `e = AND(f, v)` with `w` in
  `V*(v)`: if `V*(v) = {w}`, charge the AND gate `e` (cleaning and `(p, w)` outside `F_2` leave
  at most two alive points of `f` on `w`); otherwise the last OR below `v` with two lines in `V*`
  is pinned to `p` and has a child with `V* = {w}`: charge that OR (no rectangle).
* Every charged gate is of degree 1 in the root cone and takes at most two edges.
-/

namespace PEqualNP.MetaComplexity.Deg2.Beta

open PEqualNP.MetaComplexity.Deg2 PEqualNP.MetaComplexity.Deg2.Api
  PEqualNP.MetaComplexity.Deg2.Forms

variable {N : ℕ}

/-! ## Steps with labels true at an input -/

/-- A step down whose label, if any, is true at `x`. -/
def LStep (D : Dag N) (x : Fin (N + N) → Bool) (a b : ℕ) : Prop :=
  D.Kid a b ∧ ∀ f, D.LabAnd a f b → D.val x f = true

theorem lstep_reach {D : Dag N} {x : Fin (N + N) → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (LStep D x) a b) : D.Reach a b :=
  by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail hs.1

/-- A path with live labels is a chain of such steps. -/
theorem path_lstep {D : Dag N} {x : Fin (N + N) → Bool} :
    ∀ (π : List ℕ) (a b : ℕ), D.IsPath π a b → D.LabelsAlive π x →
      Relation.ReflTransGen (LStep D x) a b := by
  intro π
  induction π with
  | nil => intro a b h; exact absurd h.1 (by simp)
  | cons a' rest ih =>
    intro a b hp hl
    obtain ⟨hh, hlast, hs⟩ := hp
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact .refl
    | cons c rest' =>
      have hk : D.Kid a' c := by simpa using hs 0 (by simp)
      have hpc : D.IsPath (c :: rest') c b := by
        refine ⟨rfl, ?_, ?_⟩
        · rw [List.getLast?_cons_cons] at hlast; exact hlast
        · intro k hk'
          have := hs (k + 1) (by simp only [List.length_cons] at hk' ⊢; omega)
          simpa using this
      have hlc : D.LabelsAlive (c :: rest') x := by
        intro k f hk' hlab
        exact hl (k + 1) f (by simp only [List.length_cons] at hk' ⊢; omega) (by simpa using hlab)
      exact Relation.ReflTransGen.head ⟨hk, fun f hf => hl 0 f (by simp) (by simpa using hf)⟩
        (ih c b hpc hlc)

/-- Every wire of a path is reached from its head. -/
theorem path_reach {D : Dag N} {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) :
    ∀ k, k < π.length → D.Reach a (π.getD k 0) := by
  intro k
  induction k with
  | zero => intro _; rw [path_head hp]; exact .refl
  | succ k ih =>
    intro hk
    exact Relation.ReflTransGen.tail (ih (by omega)) (hp.2.2 k hk)

/-! ## Degrees and values -/

theorem gate_bounds {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ i < N + N + D.size := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  have := (List.getElem?_eq_some_iff.1 hg).1
  unfold Dag.size
  omega

/-- A wire below a root of degree at most 1 that tells `e_p + e_w` from `e_p` has degree 1. -/
theorem deg_eq_one {D : Dag N} {r v : ℕ} {p w : Fin N} (hr : D.deg r ≤ 1) (hreach : D.Reach r v)
    (h1 : D.val (ep p w) v = true) (h0 : D.val (pt p) v = false) : D.deg v = 1 := by
  have := api_reach_deg D hreach
  by_contra hne
  have hd : D.deg v = 0 := by omega
  have := api_val_xonly D hd (x := pt p) (y := ep p w) (fun q => pt_ep_points p w q)
  rw [h1, h0] at this
  cases this

/-- A label on a gate true at `e_p + e_w` is true at `e_p`. -/
theorem label_alive {D : Dag N} (hwf : D.WF) {e f v : ℕ} {p w : Fin N} (h : D.LabAnd e f v)
    (he : D.val (ep p w) e = true) : D.val (pt p) f = true := by
  rw [labAnd_val hwf h, Bool.and_eq_true] at he
  rw [api_val_xonly D h.2.1 (x := pt p) (y := ep p w) (fun q => pt_ep_points p w q)]
  exact he.1

theorem vreach_deg {D : Dag N} {v : ℕ} {u : Fin N} (h : D.VReach v u) : D.deg v = 1 := by
  cases h with
  | leaf => exact deg_line D u
  | step _ hd _ _ => exact hd

theorem mem_vstar {D : Dag N} {v : ℕ} {u : Fin N} : u ∈ D.Vstar v ↔ D.VReach v u := by
  classical
  unfold Dag.Vstar
  simp

theorem labAnd_kid_v {D : Dag N} (hwf : D.WF) {e f v : ℕ} (h : D.LabAnd e f v) : D.Kid e v := by
  rcases h.1 with hg | hg
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg v (by simp [G.kids])⟩
  · exact ⟨_, hg, by simp [G.kids], hwf _ _ hg v (by simp [G.kids])⟩

/-- Truth goes up a chain of steps with live labels, between wires of degree 1. -/
theorem lstep_up {D : Dag N} (hwf : D.WF) {x y : Fin (N + N) → Bool} (hxy : x ≤ y) {a b : ℕ}
    (h : Relation.ReflTransGen (LStep D x) a b) (ha : D.deg a ≤ 1) (hb : 1 ≤ D.deg b)
    (hy : D.val y b = true) : D.val y a = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | @head a a' hst hrest ih =>
    obtain ⟨hk, hlab⟩ := hst
    have ha' : D.deg a' ≤ 1 := le_trans (deg_kid hk) ha
    have hva' := ih ha'
    have hda' : 1 ≤ D.deg a' := le_trans hb (api_reach_deg D (lstep_reach hrest))
    obtain ⟨g, hg, hcm, hlt⟩ := id hk
    cases g with
    | and c d =>
      have hc := hwf _ _ hg c (by simp [G.kids])
      have hd := hwf _ _ hg d (by simp [G.kids])
      have hdeg := deg_and hg hc hd
      rw [val_and hg hc hd]
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with h | h
      · subst h
        have hlb : D.LabAnd a d a' := ⟨Or.inr hg, by omega, by omega⟩
        have hm := Api.api_val_mono D d hxy
        rw [hlab d hlb] at hm
        rw [hva', bool_true_le hm]
        rfl
      · subst h
        have hlb : D.LabAnd a c a' := ⟨Or.inl hg, by omega, by omega⟩
        have hm := Api.api_val_mono D c hxy
        rw [hlab c hlb] at hm
        rw [hva', bool_true_le hm]
        rfl
    | or c d => exact circ_val_or_kid D hg hk hva'
    | cst _ => simp [G.kids] at hcm

/-! ## Beta wires -/

/-- `v` is beta for `p`: a root of a line of `W` off `p` reaches `v` with labels true at `e_p`. -/
def IsB (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) (p : Fin N)
    (v : ℕ) : Prop :=
  ∃ u ∈ W, ¬ I p u ∧ Relation.ReflTransGen (LStep D (pt p)) (R u) v

/-- R1 of the sheet: a beta wire reaching `y_{u'}` through ORs has `u'` through `p`. -/
theorem beta_line (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)} {R : Fin N → ℕ}
    (hs : Dag.SoundPartialForm I D W R) {p u' : Fin N} {v : ℕ} (hb : IsB I D W R p v)
    (hv : D.VReach v u') : I p u' := by
  classical
  obtain ⟨u, hu, hpu, hρ⟩ := hb
  obtain ⟨hwf, hdeg, hsound⟩ := hs
  have hxz : pt p ≤ inp {p} {u, u'} := inp_mono (Finset.empty_subset _)
  have hzv : D.val (inp {p} {u, u'}) v = true := circ_vreach_val D hv (by rw [inp_natAdd]; simp)
  have hzr := lstep_up hwf hxz hρ (hdeg u hu) (by rw [vreach_deg hv]) hzv
  obtain ⟨p0, l, hI, hp0, hl⟩ := hsound _ ⟨u, hu, by rw [inp_natAdd]; simp, hzr⟩
  simp only [inp_castAdd, inp_natAdd, decide_eq_true_eq, Finset.mem_singleton,
    Finset.mem_insert] at hp0 hl
  subst hp0
  rcases hl with rfl | rfl
  · exact absurd hI hpu
  · exact hI

/-- Counted edges are incident. -/
theorem counted_incident (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) {p w : Fin N} (hw : w ∈ W)
    (h : D.val (ep p w) (R w) = true) : I p w := by
  obtain ⟨-, -, hsound⟩ := hs
  obtain ⟨p0, l, hI, hp0, hl⟩ := hsound (ep p w) ⟨w, hw, by unfold ep; rw [inp_natAdd]; simp, h⟩
  simp only [ep, inp_castAdd, inp_natAdd, decide_eq_true_eq, Finset.mem_singleton] at hp0 hl
  subst hp0; subst hl
  exact hI

/-! ## Charges -/

/-- OR charge: `g` is pinned to `p` and has a child with `V* = {w}`. -/
def OrCh (I : Fin N → Fin N → Prop) (D : Dag N) (g : ℕ) (e : Fin N × Fin N) : Prop :=
  Dag.PinnedTo I D g e.1 ∧ ∃ c, D.Kid g c ∧ D.Vstar c = {e.2}

/-- AND charge: `g = AND(f, v)` with `V*(v) = {w}`, `p` alive in `f` and on `w`, at most two
alive points of `f` on `w`. -/
def AndCh (I : Fin N → Fin N → Prop) (D : Dag N) (g : ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
    (D.alive f ∩ ptsOn I e.2).card ≤ 2

/-- `(p, w)` is charged to a gate of `Gs`. -/
def Charged (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) (e : Fin N × Fin N) : Prop :=
  ∃ g ∈ Gs, OrCh I D g e ∨ AndCh I D g e

/-- The charge at a labelled step `e = AND(f, v)` with `v` beta and `w ∈ V*(v)`. -/
theorem charge_at (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) (hcl : D.Cleaned I (D.rootCone W R))
    {p w : Fin N} (hw : w ∈ W) (hpw : I p w) (hnf : (p, w) ∉ D.fSet I (D.rootCone W R) 2)
    {e f v : ℕ} (he : D.LabAnd e f v) (hre : D.Reach (R w) e) (hde : D.deg e = 1)
    (hf : D.val (pt p) f = true) (hb : IsB I D W R p v) (hwv : w ∈ D.Vstar v) :
    Charged I D ((D.rootCone W R).filter (fun f => D.deg f = 1)) (p, w) := by
  classical
  have hwf := hs.1
  have hkv := labAnd_kid_v hwf he
  have hkf := labAnd_kid hwf he
  have heb := kid_gate hkv
  have hecone : e ∈ D.rootCone W R := mem_rootCone hw hre heb.1 heb.2
  by_cases h2 : 2 ≤ (D.Vstar v).card
  · obtain ⟨o, c, hr, ho, hod, ho2, hos, hk, hc⟩ := circ_pin_charge D (mem_vstar.1 hwv) h2
    obtain ⟨a', b', hga⟩ := ho
    have hob := gate_bounds hga
    have hro : D.Reach (R w) o :=
      Relation.ReflTransGen.trans (Relation.ReflTransGen.tail hre hkv) hr
    refine ⟨o, Finset.mem_filter.2 ⟨mem_rootCone hw hro hob.1 hob.2, hod⟩, Or.inl ⟨⟨⟨a', b', hga⟩,
      hod, ho2, ?_⟩, c, hk, hc⟩⟩
    intro u' hu'
    have := beta_line I hs hb (mem_vstar.1 (hos hu'))
    unfold pencil
    simpa using this
  · have hsing : D.Vstar v = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hwv, fun x hx => Finset.card_le_one.1 (by omega) x hx w hwv⟩
    refine ⟨e, Finset.mem_filter.2 ⟨hecone, hde⟩, Or.inr ⟨f, v, he, hsing, mem_alive.2 hf, hpw, ?_⟩⟩
    by_contra hgt
    rw [not_le] at hgt
    apply hnf
    have hsubf := Finset.card_le_card
      (Finset.inter_subset_left (s₁ := D.alive f) (s₂ := ptsOn I w))
    have hf2 : 2 ≤ (D.alive f).card := by simp only at hgt; omega
    have hfg := two_le_alive_gate D hf2
    obtain ⟨_, _, _, hfe⟩ := id hkf
    have hfcone : f ∈ D.rootCone W R :=
      mem_rootCone hw (Relation.ReflTransGen.tail hre hkf) hfg (by omega)
    unfold Dag.fSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hpw, f, hfcone, he.2.1, hcl e hecone f v he, mem_alive.2 hf,
      by omega⟩

/-- A step between wires of degree 1 with no label goes through an OR. -/
theorem or_of_not_lab {D : Dag N} (hwf : D.WF) {v c : ℕ} (hk : D.Kid v c) (hv : D.deg v = 1)
    (hc : D.deg c = 1) (hn : ¬ ∃ f, D.LabAnd v f c) : D.IsOr v := by
  obtain ⟨g, hg, hcm, -⟩ := hk
  cases g with
  | and a b =>
    exfalso
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    rw [deg_and hg ha hb] at hv
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · exact hn ⟨b, Or.inr hg, by omega, hc⟩
    · exact hn ⟨a, Or.inl hg, by omega, hc⟩
  | or a b => exact ⟨a, b, hg⟩
  | cst _ => simp [G.kids] at hcm

/-- The walk down from a beta wire: either `w ∈ V*` of the wire, or `(p, w)` is charged. -/
theorem descend (I : Fin N → Fin N → Prop) {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) (hcl : D.Cleaned I (D.rootCone W R))
    {p w : Fin N} (hw : w ∈ W) (hpw : I p w) (hnf : (p, w) ∉ D.fSet I (D.rootCone W R) 2) :
    ∀ v, D.val (ep p w) v = true → D.val (pt p) v = false → D.Reach (R w) v → IsB I D W R p v →
      w ∈ D.Vstar v ∨ Charged I D ((D.rootCone W R).filter (fun f => D.deg f = 1)) (p, w) := by
  have hwf := hs.1
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro h1 h0 hr hb
    by_cases hi : v < N + N
    · left
      rw [circ_val_input D _ hi] at h1
      rw [circ_val_input D _ hi] at h0
      have := ep_input hi h1 h0
      subst this
      exact mem_vstar.2 (Dag.VReach.leaf w)
    · obtain ⟨c, hk, hc1, hc0⟩ := exists_kid D (by omega) h1 h0
      have hrc : D.Reach (R w) c := Relation.ReflTransGen.tail hr hk
      have hdv := deg_eq_one (hs.2.1 w hw) hr h1 h0
      have hdc := deg_eq_one (hs.2.1 w hw) hrc hc1 hc0
      have hbc : IsB I D W R p c := by
        obtain ⟨u, hu, hpu, hρ⟩ := hb
        exact ⟨u, hu, hpu, Relation.ReflTransGen.tail hρ ⟨hk, fun f hf => label_alive hwf hf h1⟩⟩
      rcases ih c (circ_kid_lt hk) hc1 hc0 hrc hbc with hwc | hch
      · by_cases hl : ∃ f, D.LabAnd v f c
        · obtain ⟨f, hlab⟩ := hl
          exact Or.inr (charge_at I hs hcl hw hpw hnf hlab hr hdv (label_alive hwf hlab h1)
            hbc hwc)
        · exact Or.inl (circ_vstar_sub D (or_of_not_lab hwf hk hdv hdc hl) hdv hk hwc)
      · exact Or.inr hch

/-! ## The fibres -/

open Classical in
theorem fibre_le (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (g : ℕ) :
    (Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e)).card ≤ 2 := by
  classical
  by_cases hor : D.IsOr g
  · let U : ℕ → Finset (Fin N × Fin N) := fun c =>
      Finset.univ.filter (fun e => Dag.PinnedTo I D g e.1 ∧ D.Vstar c = {e.2})
    have hU : ∀ c, (U c).card ≤ 1 := by
      intro c
      rw [Finset.card_le_one]
      intro e he e' he'
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
      have h1 := circ_pinned_unique I hI D he.1 he'.1
      have h2 : e.2 = e'.2 := Finset.singleton_inj.1 (he.2.symm.trans he'.2)
      exact Prod.ext h1 h2
    have hsub : Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e) ⊆
        (circKids D g).biUnion U := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨hp, c, hk, hc⟩ | ⟨f, v, hlab, -⟩
      · rw [Finset.mem_biUnion]
        exact ⟨c, circKids_mem hk, by simp [U, hp, hc]⟩
      · exfalso
        obtain ⟨a, b, hg⟩ := hor
        rcases hlab.1 with h | h <;> rw [hg] at h <;> simp at h
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => hU c)) ?_
    have := circKids_card D g
    omega
  · have hsub : Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e) ⊆
        Finset.univ.filter (fun e => AndCh I D g e) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases he with ⟨hp, -⟩ | h
      · exact absurd hp.1 hor
      · exact h
    refine le_trans (Finset.card_le_card hsub) ?_
    by_cases hne : (Finset.univ.filter (fun e => AndCh I D g e)).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨f0, v0, h1, h2, -, -, h5⟩ := (Finset.mem_filter.1 he0).2
      have hsub' : Finset.univ.filter (fun e => AndCh I D g e) ⊆
          (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨f, v, k1, k2, k3, k4, -⟩ := (Finset.mem_filter.1 he).2
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp

end PEqualNP.MetaComplexity.Deg2.Beta

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.MetaComplexity.Deg2.Api PEqualNP.MetaComplexity.Deg2.Forms
  PEqualNP.MetaComplexity.Deg2.Beta

variable {N : ℕ}

/-- D2-13. Beta count (the sheet's `2 #AND(M'') + #OR(M'')`, weakened to `2 |M''|`). -/
theorem card13_beta (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
    (hcl : D.Cleaned I (D.rootCone W R)) :
    (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
      2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card := by
  classical
  set Gs := (D.rootCone W R).filter (fun f => D.deg f = 1) with hGs
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    Finset.univ.filter (fun e => OrCh I D g e ∨ AndCh I D g e)
  have hsub : D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2) ⊆
      Gs.biUnion T := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hbe, hout⟩ := he
    have hnf : e ∉ D.fSet I (D.rootCone W R) 2 := fun h => hout (Finset.mem_union_right _ h)
    unfold Dag.betaEdges at hbe
    rw [Finset.mem_filter] at hbe
    obtain ⟨hce, π, hEP, k, hPG, -, hB⟩ := hbe
    unfold Dag.countedEdges at hce
    rw [Finset.mem_filter] at hce
    obtain ⟨-, hw, hval⟩ := hce
    obtain ⟨p, w⟩ := e
    dsimp only at hw hval hnf hEP hPG hB ⊢
    have hpw := counted_incident I hs hw hval
    obtain ⟨hk1, f, hlab, hal⟩ := hPG
    have hpath := hEP.1
    have hm0 := path_getD_mem (π := π) (k := k) (by omega)
    have hm1 := path_getD_mem (π := π) (k := k + 1) hk1
    obtain ⟨he1, he0⟩ := hEP.2 _ hm0
    obtain ⟨hg1, hg0⟩ := hEP.2 _ hm1
    have hr0 := path_reach hpath k (by omega)
    have hr1 := path_reach hpath (k + 1) hk1
    have hdeg0 := deg_eq_one (hs.2.1 w hw) hr0 he1 he0
    have hbeta : IsB I D W R p (π.getD (k + 1) 0) := by
      obtain ⟨u, hu, hpu, ρ, hρ, hla⟩ := hB
      exact ⟨u, hu, hpu, path_lstep ρ _ _ hρ hla⟩
    have hfp : D.val (pt p) f = true := by
      rw [← mem_alive, hal]; exact Finset.mem_singleton_self p
    have hch : Charged I D Gs (p, w) := by
      rcases descend I hs hcl hw hpw hnf _ hg1 hg0 hr1 hbeta with hwv | hch
      · exact charge_at I hs hcl hw hpw hnf hlab hr0 hdeg0 hfp hbeta hwv
      · exact hch
    obtain ⟨g, hg, hc⟩ := hch
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
  calc _ ≤ (Gs.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ Gs, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Gs, 2 := Finset.sum_le_sum (fun g _ => fibre_le I hI D g)
    _ = 2 * Gs.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end PEqualNP.MetaComplexity.Deg2
