import PEqualNP.MetaComplexity.Helpers.Deg2Path

/-!
# Walks and counts on one circuit: cards D2-06, D2-07, D2-08 (helper for L-meta-649)

Conjecture until the checker accepts it. Statements exactly as in the skeleton plan
(the degree-two card plan).

* D2-06 (honest path): strong induction on the wire with the invariant "degree 1, true at
  `e_p + e_w`, false at `e_p`, and true at `e_p + e_u` only for `u` through `p`".
* D2-07 (two-line privacy at `D = 2`): a gate with a dead set of at most two lines has at most two
  lines carrying three of its alive points (no rectangle); each pair of `F_2` is charged, along
  the walk of D2-05, to a gate of such a line and one of its two children holding at most two
  alive points of the line.
* D2-08 (pinned ORs): on the OR walk from a pinned OR to `y_u`, the last OR with two lines in
  `V*` is pinned to the same point and has a child with `V* = {u}`; an OR is pinned to one point
  at most (no rectangle).
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.MetaComplexity.Deg2.Api PEqualNP.MetaComplexity.Deg2.Path

variable {N : ℕ}

/-! ## Gate evaluation -/

theorem circ_val_input (D : Dag N) (x : Fin (N + N) → Bool) {i : ℕ} (hi : i < N + N) :
    D.val x i = x ⟨i, hi⟩ := by
  rw [Dag.val, dif_pos hi]

theorem circ_deg_input (D : Dag N) {i : ℕ} (hi : i < N + N) :
    D.deg i = if N ≤ i then 1 else 0 := by
  rw [Dag.deg, if_pos hi]

theorem circ_val_and_eq (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem circ_val_and (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = true) :
    a < i ∧ b < i ∧ D.val x a = true ∧ D.val x b = true := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨ha, hb⟩ := hv
  split_ifs at ha with hax
  split_ifs at hb with hbx
  exact ⟨hax, hbx, ha, hb⟩

theorem circ_val_or_true (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.or a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = true) :
    (a < i ∧ D.val x a = true) ∨ (b < i ∧ D.val x b = true) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.or_eq_true] at hv
  rcases hv with ha | hb
  · split_ifs at ha with hax
    exact Or.inl ⟨hax, ha⟩
  · split_ifs at hb with hbx
    exact Or.inr ⟨hbx, hb⟩

theorem circ_val_or_false (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.or a b))
    {x : Fin (N + N) → Bool} (hv : D.val x i = false) :
    (a < i → D.val x a = false) ∧ (b < i → D.val x b = false) := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg] at hv
  dsimp only at hv
  rw [Bool.or_eq_false_iff] at hv
  obtain ⟨ha, hb⟩ := hv
  refine ⟨fun hax => ?_, fun hbx => ?_⟩
  · rwa [dif_pos hax] at ha
  · rwa [dif_pos hbx] at hb

/-- A true child of an OR makes it true. -/
theorem circ_val_or_kid (D : Dag N) {i a b c : ℕ} (h : D.gateAt i = some (.or a b))
    (hk : D.Kid i c) {x : Fin (N + N) → Bool} (hc : D.val x c = true) : D.val x i = true := by
  obtain ⟨g, hg, hcg, hci⟩ := hk
  rw [h, Option.some.injEq] at hg
  subst hg
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.val, dif_neg (by omega), hg]
  dsimp only
  simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hcg
  rw [Bool.or_eq_true]
  rcases hcg with rfl | rfl
  · left; rw [dif_pos hci]; exact hc
  · right; rw [dif_pos hci]; exact hc

theorem circ_deg_and (D : Dag N) {i a b : ℕ} (h : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := gateAt_some h
  rw [Dag.deg, if_neg (by omega), hg]
  dsimp only
  rw [dif_pos ha, dif_pos hb]

theorem circ_kid_lt {D : Dag N} {i c : ℕ} (h : D.Kid i c) : c < i := by
  obtain ⟨_, _, _, h⟩ := h
  exact h

theorem circ_kid_gate {D : Dag N} {i c : ℕ} (h : D.Kid i c) : N + N ≤ i := by
  obtain ⟨_, hg, _, _⟩ := h
  exact (gateAt_some hg).1

theorem circ_kid_of {D : Dag N} {i c : ℕ} {g : G} (h : D.gateAt i = some g) (hc : c ∈ g.kids)
    (hci : c < i) : D.Kid i c := ⟨g, h, hc, hci⟩

/-! ## Inputs -/

theorem circ_ep_pts (p u : Fin N) (q : Fin N) : ep p u (Fin.castAdd N q) = pt p (Fin.castAdd N q) := by
  simp [ep, pt, inp]

theorem circ_ep_line {p w : Fin N} {i : ℕ} (hi : i < N + N) (hN : N ≤ i)
    (h : ep p w ⟨i, hi⟩ = true) : i = N + w.val := by
  unfold ep inp at h
  have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
    ext; simp; omega
  rw [this, Fin.addCases_right] at h
  simp only [Finset.mem_singleton, decide_eq_true_eq] at h
  have := congrArg Fin.val h
  simp at this
  omega

theorem circ_getD_mem {π : List ℕ} {k : ℕ} (hk : k < π.length) : π.getD k 0 ∈ π := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- A path from `a` to a different wire `b` starts with a child of `a` on the path. -/
theorem circ_path_first {D : Dag N} {π : List ℕ} {a b : ℕ} (hp : D.IsPath π a b) (hab : a ≠ b) :
    ∃ c, D.Kid a c ∧ c ∈ π := by
  obtain ⟨hh, hl, hc⟩ := hp
  cases π with
  | nil => simp at hh
  | cons a' rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil => simp at hl; exact absurd hl hab
    | cons c rest' =>
      refine ⟨c, ?_, by simp⟩
      have := hc 0 (by simp)
      simpa using this

/-- A wire reaching `y_u` through degree-1 ORs is true wherever `y_u` is. -/
theorem circ_vreach_val (D : Dag N) {v : ℕ} {u : Fin N} (h : D.VReach v u)
    {x : Fin (N + N) → Bool} (hx : x (Fin.natAdd N u) = true) : D.val x v = true := by
  induction h with
  | leaf u =>
    rw [circ_val_input D x (by omega)]
    exact hx
  | step hor _ hk _ ih =>
    obtain ⟨a, b, hg⟩ := hor
    exact circ_val_or_kid D hg hk (ih hx)

/-! ## D2-06: honest path -/

theorem circ_honest_core (I : Fin N → Fin N → Prop) (D : Dag N) (p w : Fin N) :
    ∀ g, D.deg g = 1 → D.val (ep p w) g = true → D.val (pt p) g = false →
      (∀ u, D.val (ep p u) g = true → I p u) →
      ∃ π, D.IsPath π g (N + w.val) ∧ ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hd h1 h0 hh
    have extend : ∀ c, D.Kid g c → D.deg c = 1 → D.val (ep p w) c = true →
        D.val (pt p) c = false → (∀ u, D.val (ep p u) c = true → I p u) →
        ∃ π, D.IsPath π g (N + w.val) ∧ ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
      intro c hk hcd hc1 hc0 hch
      obtain ⟨π, hπ, hv⟩ := ih c (circ_kid_lt hk) hcd hc1 hc0 hch
      refine ⟨g :: π, isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact ⟨hd, h1, hh⟩
      · exact hv v hv'
    by_cases hi : g < N + N
    · rw [circ_deg_input D hi] at hd
      have hN : N ≤ g := by
        by_contra hN; rw [if_neg hN] at hd; exact absurd hd zero_ne_one
      rw [circ_val_input D _ hi] at h1
      have hgw := circ_ep_line hi hN h1
      refine ⟨[g], ?_, ?_⟩
      · rw [hgw]; exact isPath_single D _
      · intro v hv
        simp only [List.mem_singleton] at hv
        subst hv
        refine ⟨by rw [circ_deg_input D hi, if_pos hN], ?_⟩
        refine ⟨?_, ?_⟩
        · rw [circ_val_input D _ hi]; exact h1
        · exact hh
    · have hga : ∀ gg, D.gates[g - (N + N)]? = some gg → D.gateAt g = some gg := by
        intro gg hg; unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
      cases hg : D.gates[g - (N + N)]? with
      | none =>
        rw [Dag.deg, if_neg hi, hg] at hd
        exact absurd hd zero_ne_one
      | some gg =>
        have hgA := hga gg hg
        cases gg with
        | cst v =>
          rw [Dag.deg, if_neg hi, hg] at hd
          exact absurd hd zero_ne_one
        | or a b =>
          have hstep : ∀ c, c < g → (c = a ∨ c = b) → D.val (ep p w) c = true →
              D.val (pt p) c = false →
              ∃ π, D.IsPath π g (N + w.val) ∧
                ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
            intro c hcg hcab hc1 hc0
            have hk : D.Kid g c := circ_kid_of hgA (by rcases hcab with rfl | rfl <;> simp [G.kids]) hcg
            have hle : D.deg c ≤ 1 := hd ▸ deg_kid hk
            have hcd : D.deg c = 1 := by
              by_contra hne
              have h0' : D.deg c = 0 := by omega
              have := api_val_xonly D h0' (x := ep p w) (y := pt p) (circ_ep_pts p w)
              rw [hc1, hc0] at this
              cases this
            refine extend c hk hcd hc1 hc0 ?_
            intro u hu
            exact hh u (circ_val_or_kid D hgA hk hu)
          have h0' := circ_val_or_false D hgA h0
          rcases circ_val_or_true D hgA h1 with ⟨ha, ha1⟩ | ⟨hb, hb1⟩
          · exact hstep a ha (Or.inl rfl) ha1 (h0'.1 ha)
          · exact hstep b hb (Or.inr rfl) hb1 (h0'.2 hb)
        | and a b =>
          obtain ⟨ha, hb, ha1, hb1⟩ := circ_val_and D hgA h1
          have hdeg := circ_deg_and D hgA ha hb
          have hstep : ∀ f v, v < g → (v = a ∨ v = b) → D.deg f = 0 → D.deg v = 1 →
              D.val (ep p w) f = true → D.val (ep p w) v = true →
              (∀ x, D.val x g = (D.val x f && D.val x v)) →
              ∃ π, D.IsPath π g (N + w.val) ∧
                ∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true ∧
          ∀ u, D.val (ep p u) v = true → I p u := by
            intro f v hvg hvab hf hv hf1 hv1 heq
            have hk : D.Kid g v := circ_kid_of hgA (by rcases hvab with rfl | rfl <;> simp [G.kids]) hvg
            have hfp : ∀ u, D.val (ep p u) f = true := by
              intro u
              rw [api_val_xonly D hf (x := ep p u) (y := ep p w)
                (fun q => by rw [circ_ep_pts, circ_ep_pts])]
              exact hf1
            have hfpt : D.val (pt p) f = true := by
              rw [api_val_xonly D hf (x := pt p) (y := ep p w)
                (fun q => by rw [circ_ep_pts])]
              exact hf1
            have hv0 : D.val (pt p) v = false := by
              rw [heq, hfpt, Bool.true_and] at h0; exact h0
            refine extend v hk hv hv1 hv0 ?_
            intro u hu
            apply hh u
            rw [heq, hfp u, hu]; rfl
          by_cases hda : D.deg a = 0
          · exact hstep a b hb (Or.inr rfl) hda (by omega) ha1 hb1
              (circ_val_and_eq D hgA ha hb)
          · exact hstep b a ha (Or.inl rfl) (by omega) (by omega) hb1 ha1
              (fun x => by rw [circ_val_and_eq D hgA ha hb x, Bool.and_comm])

/-- D2-06. Honest path. -/
theorem card06_honest_path (I : Fin N → Fin N → Prop) (D : Dag N) (r : ℕ) (p w : Fin N)
    (hr : D.deg r = 1) (hh : IsHonest I (fun x => D.val x r) p)
    (h1 : D.val (ep p w) r = true) :
    ∃ π, D.IsPath π r (N + w.val) ∧ (∀ v ∈ π, D.deg v = 1 ∧ D.val (ep p w) v = true) ∧
      D.LabelsAlive π (pt p) ∧ ∀ v ∈ π, D.Vstar v ⊆ pencil I p := by
  obtain ⟨π, hπ, hv⟩ := circ_honest_core I D p w r hr h1 hh.1
    (fun u hu => hh.2 u hu)
  refine ⟨π, hπ, fun v hv' => ⟨(hv v hv').1, (hv v hv').2.1⟩, ?_, ?_⟩
  · intro k f hk hlab
    have hg1 := (hv _ (circ_getD_mem (by omega : k < π.length))).2.1
    obtain ⟨hgate, hf, -⟩ := hlab
    have hf1 : D.val (ep p w) f = true := by
      rcases hgate with hgate | hgate
      · exact (circ_val_and D hgate hg1).2.2.1
      · exact (circ_val_and D hgate hg1).2.2.2
    rw [api_val_xonly D hf (x := pt p) (y := ep p w) (fun q => by rw [circ_ep_pts])]
    exact hf1
  · intro v hv' u hu
    classical
    unfold Dag.Vstar at hu
    rw [Finset.mem_filter] at hu
    have hval := circ_vreach_val D hu.2 (x := ep p u) (by unfold ep inp; rw [Fin.addCases_right]; simp)
    unfold pencil
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hv v hv').2.2 u hval⟩

/-! ## Children as a finset -/

/-- The wires a gate reads, as a finset (empty for an input). -/
def circKids (D : Dag N) (g : ℕ) : Finset ℕ := (((D.gateAt g).map G.kids).getD []).toFinset

theorem circKids_card (D : Dag N) (g : ℕ) : (circKids D g).card ≤ 2 := by
  unfold circKids
  refine le_trans (List.toFinset_card_le _) ?_
  cases D.gateAt g with
  | none => simp
  | some gg => cases gg <;> simp [G.kids]

theorem circKids_mem {D : Dag N} {g c : ℕ} (h : D.Kid g c) : c ∈ circKids D g := by
  obtain ⟨gg, hg, hc, -⟩ := h
  unfold circKids
  rw [hg]
  simpa using hc

/-! ## D2-07: two-line privacy -/

theorem circ_alive_input (D : Dag N) {i : ℕ} (hi : i < N + N) : (D.alive i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  unfold Dag.alive at ha hb
  rw [Finset.mem_filter, circ_val_input D _ hi] at ha hb
  have h1 := pt_val hi ha.2
  have h2 := pt_val hi hb.2
  exact Fin.ext (by omega)

theorem circ_pt_le_test (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) {q : Fin N}
    (hq : ∀ l ∈ S, ¬ I q l) : pt q ≤ testInput I S := by
  classical
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · unfold pt testInput inp
    rw [Fin.addCases_left, Fin.addCases_left]
    by_cases hj : j = q
    · subst hj
      have : j ∈ Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hq⟩
      simp only [Finset.mem_singleton, decide_true]
      rw [decide_eq_true this]
    · simp [hj]
  · unfold pt testInput inp
    rw [Fin.addCases_right, Fin.addCases_right]
    simp

/-- An alive point of a wire false at `z_S` lies on a line of `S`. -/
theorem circ_alive_on (I : Fin N → Fin N → Prop) (D : Dag N) {f : ℕ} {S : Finset (Fin N)}
    (h0 : D.val (testInput I S) f = false) {q : Fin N} (hq : q ∈ D.alive f) :
    ∃ s ∈ S, I q s := by
  by_contra hne
  push_neg at hne
  have hle := api_val_mono D f (circ_pt_le_test I S hne)
  unfold Dag.alive at hq
  rw [Finset.mem_filter] at hq
  rw [hq.2, h0] at hle
  exact absurd hle (by decide)

/-- With a dead set of at most two lines, at most two lines carry three alive points. -/
theorem circ_lines_le_two (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {f : ℕ}
    {S : Finset (Fin N)} (hS : S.card ≤ 2) (h0 : D.val (testInput I S) f = false) :
    (Finset.univ.filter (fun l => 3 ≤ (D.alive f ∩ ptsOn I l).card)).card ≤ 2 := by
  classical
  refine le_trans (Finset.card_le_card (t := S) ?_) hS
  intro l hl
  rw [Finset.mem_filter] at hl
  by_contra hlS
  have hsub : D.alive f ∩ ptsOn I l ⊆ S.biUnion (fun s => ptsOn I s ∩ ptsOn I l) := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨s, hs, hqs⟩ := circ_alive_on I D h0 hq.1
    rw [Finset.mem_biUnion]
    refine ⟨s, hs, Finset.mem_inter.2 ⟨?_, hq.2⟩⟩
    unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hqs⟩
  have hb := Finset.card_biUnion_le_card_mul S (fun s => ptsOn I s ∩ ptsOn I l) 1 (by
    intro s hs
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hsl : s ≠ l := by rintro rfl; exact hlS hs
    unfold ptsOn at ha hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hI a b s l hab hsl ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have := Finset.card_le_card hsub
  omega

/-- The charge of D2-07: descending the walk of D2-05 from a gate of `Gs` with three alive
points on `l`, the last such gate has a child holding `p` and at most two alive points of `l`. -/
theorem circ_charge (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ)
    (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) (p l : Fin N)
    (S : Finset (Fin N)) :
    ∀ f, f ∈ Gs → D.deg f = 0 → D.val (pt p) f = true → D.val (testInput I S) f = false →
      3 ≤ (D.alive f ∩ ptsOn I l).card →
      ∃ g ∈ Gs, D.deg g = 0 ∧ D.val (testInput I S) g = false ∧
        3 ≤ (D.alive g ∩ ptsOn I l).card ∧
        ∃ c, D.Kid g c ∧ p ∈ D.alive c ∧ (D.alive c ∩ ptsOn I l).card ≤ 2 := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf hd h1 h0 h3
    by_cases hi : f < N + N
    · have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
        (s₂ := ptsOn I l))) (circ_alive_input D hi)
      omega
    · obtain ⟨π, hπ, hv⟩ := card05_path I D f p S h1 h0
      have hne : f ≠ p.val := by have := p.isLt; omega
      obtain ⟨c, hk, hcπ⟩ := circ_path_first hπ hne
      obtain ⟨hc1, hc0⟩ := hv c hcπ
      have hcd : D.deg c = 0 := by have := deg_kid hk; omega
      by_cases hc3 : 3 ≤ (D.alive c ∩ ptsOn I l).card
      · have hcg : N + N ≤ c := by
          by_contra hcn
          have := le_trans (Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive c)
            (s₂ := ptsOn I l))) (circ_alive_input D (by omega : c < N + N))
          omega
        exact ih c (circ_kid_lt hk) (hdown f hf c hk hcg) hcd hc1 hc0 hc3
      · refine ⟨f, hf, hd, h0, h3, c, hk, ?_, by omega⟩
        unfold Dag.alive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc1⟩

/-- D2-07 at `D = 2`. Two-line privacy over any downward-closed gate set. -/
theorem card07_two_line (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
    (Gs : Finset ℕ) (hdown : ∀ i ∈ Gs, ∀ c, D.Kid i c → N + N ≤ c → c ∈ Gs) :
    (D.fSet I Gs 2).card ≤ 8 * (Gs.filter (fun f => D.deg f = 0)).card := by
  classical
  let Lg : ℕ → Finset (Fin N) := fun g => Finset.univ.filter (fun l =>
    3 ≤ (D.alive g ∩ ptsOn I l).card ∧
      ∃ S : Finset (Fin N), S.card ≤ 2 ∧ D.val (testInput I S) g = false)
  let Tc : Fin N → ℕ → Finset (Fin N × Fin N) := fun l c =>
    if (D.alive c ∩ ptsOn I l).card ≤ 2 then (D.alive c ∩ ptsOn I l).image (fun q => (q, l))
    else ∅
  have hLg : ∀ g, (Lg g).card ≤ 2 := by
    intro g
    by_cases hS : ∃ S : Finset (Fin N), S.card ≤ 2 ∧ D.val (testInput I S) g = false
    · obtain ⟨S, hS2, hS0⟩ := hS
      refine le_trans (Finset.card_le_card ?_) (circ_lines_le_two I hI D hS2 hS0)
      intro l hl
      simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.1
    · have : Lg g = ∅ := by
        ext l
        simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro _ h; exact hS h
      rw [this]; simp
  have hTc : ∀ l c, (Tc l c).card ≤ 2 := by
    intro l c
    simp only [Tc]
    split_ifs with h
    · exact le_trans Finset.card_image_le h
    · simp
  have hsub : D.fSet I Gs 2 ⊆ (Gs.filter (fun f => D.deg f = 0)).biUnion
      (fun g => (Lg g).biUnion (fun l => (circKids D g).biUnion (fun c => Tc l c))) := by
    intro e he
    unfold Dag.fSet at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hIe, f, hf, hfd, hdead, hp, h3⟩ := he
    obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hdead
    unfold Dag.deadSets at hS
    rw [Finset.mem_filter] at hS
    obtain ⟨-, hS2, hS0⟩ := hS
    unfold Dag.alive at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨g, hg, hgd, hg0, hg3, c, hk, hpc, hc2⟩ :=
      circ_charge I D Gs hdown e.1 e.2 S f hf hfd hp.2 hS0 h3
    simp only [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.2 ⟨hg, hgd⟩, e.2, ?_, c, circKids_mem hk, ?_⟩
    · simp only [Lg, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hg3, S, hS2, hg0⟩
    · simp only [Tc]
      rw [if_pos hc2, Finset.mem_image]
      refine ⟨e.1, Finset.mem_inter.2 ⟨hpc, ?_⟩, rfl⟩
      unfold ptsOn; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hIe⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 8 ?_) (by rw [mul_comm])
  intro g _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 ?_) ?_
  · intro l _
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2 (fun c _ => hTc l c)) ?_
    have := circKids_card D g
    omega
  · have := hLg g
    omega

/-! ## D2-08: pinned ORs -/

theorem circ_vreach_input (D : Dag N) {i : ℕ} {u : Fin N} (h : D.VReach i u) (hi : i < N + N) :
    i = N + u.val := by
  cases h with
  | leaf => rfl
  | step hor _ _ _ =>
    obtain ⟨a, b, hg⟩ := hor
    have := (gateAt_some hg).1
    omega

theorem circ_vstar_sub (D : Dag N) {v c : ℕ} (hor : D.IsOr v) (hd : D.deg v = 1)
    (hk : D.Kid v c) : D.Vstar c ⊆ D.Vstar v := by
  classical
  intro u hu
  unfold Dag.Vstar at hu ⊢
  rw [Finset.mem_filter] at hu ⊢
  exact ⟨Finset.mem_univ _, Dag.VReach.step hor hd hk hu.2⟩

theorem circ_pin_charge (D : Dag N) {v : ℕ} {u : Fin N} (h : D.VReach v u) :
    2 ≤ (D.Vstar v).card →
    ∃ o c, D.Reach v o ∧ D.IsOr o ∧ D.deg o = 1 ∧ 2 ≤ (D.Vstar o).card ∧
      D.Vstar o ⊆ D.Vstar v ∧ D.Kid o c ∧ D.Vstar c = {u} := by
  classical
  induction h with
  | leaf u =>
    intro h2
    exfalso
    have : (D.Vstar (N + u.val)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      unfold Dag.Vstar at ha hb
      rw [Finset.mem_filter] at ha hb
      have h1 := circ_vreach_input D ha.2 (by omega)
      have h2 := circ_vreach_input D hb.2 (by omega)
      exact Fin.ext (by omega)
    omega
  | @step v c u hor hd hk hc ih =>
    intro h2
    by_cases h2c : 2 ≤ (D.Vstar c).card
    · obtain ⟨o, c', hr, ho, hod, ho2, hos, hk', hc'⟩ := ih h2c
      exact ⟨o, c', Relation.ReflTransGen.head hk hr, ho, hod, ho2,
        hos.trans (circ_vstar_sub D hor hd hk), hk', hc'⟩
    · refine ⟨v, c, Relation.ReflTransGen.refl, hor, hd, h2, subset_refl _, hk, ?_⟩
      have hu : u ∈ D.Vstar c := by
        unfold Dag.Vstar; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hu, fun x hx => ?_⟩
      exact Finset.card_le_one.1 (by omega) x hx u hu

theorem circ_pinned_unique (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) {o : ℕ}
    {p p' : Fin N} (h : Dag.PinnedTo I D o p) (h' : Dag.PinnedTo I D o p') : p = p' := by
  classical
  obtain ⟨-, -, h2, hs⟩ := h
  obtain ⟨-, -, -, hs'⟩ := h'
  obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.1 (by omega : 1 < (D.Vstar o).card)
  by_contra hpp
  have m := fun {q l} (h : l ∈ pencil I q) => (Finset.mem_filter.1 h).2
  exact hI p p' u u' hpp huu ⟨m (hs hu), m (hs hu'), m (hs' hu), m (hs' hu')⟩

/-- An OR of degree 1 reached from a gate of `OrM` is in `OrM`. -/
theorem circ_orM_reach (D : Dag N) {v o : ℕ} (hv : v ∈ D.OrM) (hr : D.Reach v o)
    (ho : D.IsOr o) (hod : D.deg o = 1) : o ∈ D.OrM := by
  classical
  unfold Dag.OrM Dag.M Dag.cone Dag.coneOf at hv ⊢
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    exists_eq_left] at hv ⊢
  obtain ⟨a, b, hg⟩ := ho
  obtain ⟨hi, hgs⟩ := gateAt_some hg
  have hlt : o - (N + N) < D.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hgs
    cases hgs
  refine ⟨⟨⟨by unfold Dag.size; omega, hi, hv.1.1.2.2.trans hr⟩, hod⟩, a, b, hg⟩

/-- D2-08. Pinned-OR count. -/
theorem card08_pinned (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) :
    (D.pinned I).card ≤ 2 * D.OrM.card := by
  classical
  let T : ℕ → ℕ → Finset (Fin N × Fin N) := fun o c =>
    Finset.univ.filter (fun e => Dag.PinnedTo I D o e.1 ∧ D.Vstar c = {e.2})
  have hT : ∀ o c, (T o c).card ≤ 1 := by
    intro o c
    rw [Finset.card_le_one]
    intro e he e' he'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    have h1 := circ_pinned_unique I hI D he.1 he'.1
    have h2 : e.2 = e'.2 := by
      have := he.2.symm.trans he'.2
      exact Finset.singleton_inj.1 this
    exact Prod.ext h1 h2
  have hsub : D.pinned I ⊆ D.OrM.biUnion (fun o => (circKids D o).biUnion (fun c => T o c)) := by
    intro e he
    unfold Dag.pinned at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, v, hv, hpin, hu⟩ := he
    have hvr : D.VReach v e.2 := by
      unfold Dag.Vstar at hu; exact (Finset.mem_filter.1 hu).2
    obtain ⟨o, c, hr, ho, hod, ho2, hos, hk, hc⟩ := circ_pin_charge D hvr hpin.2.2.1
    simp only [Finset.mem_biUnion]
    refine ⟨o, circ_orM_reach D hv hr ho hod, c, circKids_mem hk, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨ho, hod, ho2, hos.trans hpin.2.2.2⟩, hc⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2 ?_) (by rw [mul_comm])
  intro o _
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => hT o c)) ?_
  have := circKids_card D o
  omega

end PEqualNP.MetaComplexity.Deg2
