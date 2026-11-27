import PEqualNP.MetaComplexity.Helpers.Deg2Path

/-!
# The top part of the degree-two chain: D2-15 (helper for L-meta-649)

Card `card15_identity` of the degree-two card plan, with its statement as in
the plan. Proof: a single downward walk (no frontier invariant). Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

theorem tr_val_and {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.and a b)) (ha : a < h)
    (hb : b < h) (x : Fin (N + N) → Bool) : D.val x h = (D.val x a && D.val x b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.val]
  rw [dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem tr_val_or {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.or a b)) (ha : a < h)
    (hb : b < h) (x : Fin (N + N) → Bool) : D.val x h = (D.val x a || D.val x b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.val]
  rw [dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem tr_deg_and {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.and a b)) (ha : a < h)
    (hb : b < h) : D.deg h = D.deg a + D.deg b := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem tr_deg_or {D : Dag N} {h a b : ℕ} (hg : D.gateAt h = some (.or a b)) (ha : a < h)
    (hb : b < h) : D.deg h = max (D.deg a) (D.deg b) := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  conv_lhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem tr_deg_cst {D : Dag N} {h : ℕ} {v : Bool} (hg : D.gateAt h = some (.cst v)) :
    D.deg h = 0 := by
  obtain ⟨hh, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]

/-- A wire of degree at least 2 is a gate wire. -/
theorem tr_gate_of_deg {D : Dag N} {c : ℕ} (hd : 2 ≤ D.deg c) :
    ∃ g, D.gateAt c = some g ∧ c < N + N + D.size := by
  have hd' := hd
  rw [Dag.deg] at hd'
  by_cases hc : c < N + N
  · rw [if_pos hc] at hd'
    split_ifs at hd' <;> omega
  · rw [if_neg hc] at hd'
    cases hg : D.gates[c - (N + N)]? with
    | none => rw [hg] at hd'; simp at hd'
    | some g =>
      refine ⟨g, ?_, ?_⟩
      · unfold Dag.gateAt; rw [if_pos (by omega), hg]
      · have := (List.getElem?_eq_some_iff.1 hg).1
        unfold Dag.size; omega

theorem tr_kid_of {D : Dag N} {h c : ℕ} {g : G} (hg : D.gateAt h = some g) (hc : c ∈ g.kids)
    (hlt : c < h) : D.Kid h c := ⟨g, hg, hc, hlt⟩

/-- Wires reached by the pass are reachable from the output. -/
theorem tr_top_reach {D : Dag N} {ok : ℕ → Prop} {c : ℕ} (h : D.Top ok c) :
    D.Reach D.out c := by
  induction h with
  | root => exact Relation.ReflTransGen.refl
  | @orStep h c _ _ hk _ ih => exact ih.tail hk
  | @andStep h f c _ _ hg _ _ _ hc _ ih =>
    rcases hg with hg | hg
    · exact ih.tail (tr_kid_of hg (by simp [G.kids]) hc)
    · exact ih.tail (tr_kid_of hg (by simp [G.kids]) hc)

theorem tr_top_mono {D : Dag N} {ok ok' : ℕ → Prop} (hok : ∀ f, D.deg f = 0 → ok f → ok' f)
    {c : ℕ} (h : D.Top ok c) : D.Top ok' c := by
  induction h with
  | root => exact Dag.Top.root
  | @orStep h c _ ht hk hd ih => exact Dag.Top.orStep ih ht hk hd
  | @andStep h f c _ ht hg hf hc2 hfh hch hokf ih =>
    exact Dag.Top.andStep ih ht hg hf hc2 hfh hch (hok f hf hokf)

/-- A true wire reached by a pass with true labels makes the output true. -/
theorem tr_top_val {D : Dag N} (hwf : D.WF) {x : Fin (N + N) → Bool} {c : ℕ}
    (h : D.Top (fun f => D.val x f = true) c) : D.val x c = true → D.val x D.out = true := by
  induction h with
  | root => exact id
  | @orStep h c _ ht hk _ ih =>
    classical
    intro hv
    apply ih
    obtain ⟨g, hg, hcg, hch⟩ := hk
    obtain ⟨-, a, b, hab⟩ := Finset.mem_filter.1 ht
    rw [hab] at hg
    cases hg
    have ha := hwf _ _ hab a (by simp [G.kids])
    have hb := hwf _ _ hab b (by simp [G.kids])
    rw [tr_val_or hab ha hb]
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
    rcases hcg with rfl | rfl <;> simp [hv]
  | @andStep h f c _ _ hg _ _ hfh hch hokf ih =>
    intro hv
    apply ih
    rcases hg with hg | hg
    · rw [tr_val_and hg hfh hch]; simp [hv, hokf]
    · rw [tr_val_and hg hch hfh]; simp [hv, hokf]

theorem tr_mem_cone {D : Dag N} {c : ℕ} (h1 : N + N ≤ c) (h2 : c < N + N + D.size)
    (hr : D.Reach D.out c) : c ∈ D.cone := by
  classical
  unfold Dag.cone Dag.coneOf
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  exact ⟨h2, h1, D.out, rfl, hr⟩

/-- The input `x` with every line off. -/
def tr_noLines (x : Fin (N + N) → Bool) : Fin (N + N) → Bool :=
  fun i => if (i : ℕ) < N then x i else false

theorem tr_noLines_pts (x : Fin (N + N) → Bool) (p : Fin N) :
    x (Fin.castAdd N p) = tr_noLines x (Fin.castAdd N p) := by
  simp [tr_noLines, Fin.coe_castAdd, p.isLt]

/-- A degree-0 child of a reached wire is false whenever the labels on the way are true. -/
theorem tr_drop {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Computes I D.fn)
    {x : Fin (N + N) → Bool} {c a : ℕ} (hT : D.Top (fun f => D.val x f = true) c)
    (ha0 : D.deg a = 0) (hva : D.val x a = true)
    (hup : D.val (tr_noLines x) a = true → D.val (tr_noLines x) c = true) : False := by
  have hx := tr_noLines_pts x
  have hT' : D.Top (fun f => D.val (tr_noLines x) f = true) c := by
    refine tr_top_mono ?_ hT
    intro f hf hv
    rw [← Api.api_val_xonly D hf hx]; exact hv
  have hva' : D.val (tr_noLines x) a = true := by
    rw [← Api.api_val_xonly D ha0 hx]; exact hva
  have hout := tr_top_val hwf hT' (hup hva')
  obtain ⟨p, l, -, -, hl⟩ := (hc (tr_noLines x)).1 hout
  simp [tr_noLines, Fin.coe_natAdd] at hl

theorem tr_descend {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Computes I D.fn)
    (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    ∀ c, D.Top (fun f => D.val x f = true) c → D.val x c = true →
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hT hv
  have hitem : D.Top (fun _ => True) c := tr_top_mono (fun _ _ _ => trivial) hT
  have hctx : D.ctx c x = true := by unfold Dag.ctx; exact decide_eq_true hT
  have hreach := tr_top_reach hT
  have hdc : D.deg c ≤ 2 := le_trans (Api.api_reach_deg D hreach) hd
  by_cases h1 : D.deg c ≤ 1
  · refine ⟨c, ⟨hitem, Or.inl h1⟩, hctx, ?_⟩
    intro r hr
    rcases hr with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact hv
    · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).2; omega
  have h2 : D.deg c = 2 := by omega
  obtain ⟨g, hg, hlt⟩ := tr_gate_of_deg (D := D) (c := c) (by omega)
  have hge := (Api.gateAt_some hg).1
  have hcone := tr_mem_cone hge hlt hreach
  have hT2 : c ∈ D.T := Finset.mem_filter.2 ⟨hcone, h2⟩
  cases g with
  | cst v => rw [tr_deg_cst hg] at h2; omega
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hdeg := tr_deg_and hg ha hb
    rw [tr_val_and hg ha hb, Bool.and_eq_true] at hv
    by_cases hab : D.deg a = 1 ∧ D.deg b = 1
    · have hmix : c ∈ D.Tmix := Finset.mem_filter.2 ⟨hT2, a, b, hg, hab⟩
      refine ⟨c, ⟨hitem, Or.inr hmix⟩, hctx, ?_⟩
      intro r hr
      rcases hr with ⟨h1', -⟩ | ⟨-, g', hg', hrg, -⟩
      · omega
      · rw [hg] at hg'; cases hg'
        simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hrg
        rcases hrg with rfl | rfl
        · exact hv.1
        · exact hv.2
    · have hf : D.deg a = 0 ∨ D.deg b = 0 := by omega
      have hTf : c ∈ D.Tandf := Finset.mem_filter.2 ⟨hT2, a, b, hg, hf⟩
      rcases hf with hf | hf
      · exact ih b hb (Dag.Top.andStep hT hTf (Or.inl hg) hf (by omega) ha hb hv.1) hv.2
      · exact ih a ha (Dag.Top.andStep hT hTf (Or.inr hg) hf (by omega) hb ha hv.2) hv.1
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hTor : c ∈ D.Tor := Finset.mem_filter.2 ⟨hT2, a, b, hg⟩
    rw [tr_val_or hg ha hb, Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · by_cases h0 : D.deg a = 0
      · exact (tr_drop hwf hc hT h0 hv (fun h => by rw [tr_val_or hg ha hb, h]; rfl)).elim
      · exact ih a ha (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) ha)
          (by omega)) hv
    · by_cases h0 : D.deg b = 0
      · exact (tr_drop hwf hc hT h0 hv
          (fun h => by rw [tr_val_or hg ha hb, h]; simp)).elim
      · exact ih b hb (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) hb)
          (by omega)) hv

/-- D2-15 (i), (ii). The identity: the output is the OR over items of context AND factors. -/
theorem card15_identity (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  constructor
  · intro h
    exact tr_descend hwf hc hd x D.out Dag.Top.root h
  · rintro ⟨b, ⟨-, hb⟩, hctx, hfac⟩
    have hT : D.Top (fun f => D.val x f = true) b := by
      unfold Dag.ctx at hctx; exact of_decide_eq_true hctx
    apply tr_top_val hwf hT
    rcases hb with hb | hb
    · exact hfac b (Or.inl ⟨hb, rfl⟩)
    · obtain ⟨-, a, a', hg, -, -⟩ := Finset.mem_filter.1 hb
      have ha := hwf _ _ hg a (by simp [G.kids])
      have ha' := hwf _ _ hg a' (by simp [G.kids])
      rw [tr_val_and hg ha ha', hfac a (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha⟩),
        hfac a' (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha'⟩)]
      rfl

end PEqualNP.MetaComplexity.Deg2
