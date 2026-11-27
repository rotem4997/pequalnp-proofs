import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18800_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len_w (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]; omega

theorem foldl_len_or (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]; omega

theorem getD_append_lt {α : Type*} (d : α) (l1 l2 : List α) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_left hi,
      List.getD_eq_getElem _ _ hi]

theorem getD_snoc {α : Type*} (d : α) (l : List α) (x : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

theorem foldl_w_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    exact getD_append_lt false w _ i hi

theorem foldl_w_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl wstep w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        ((gs.take j).foldl wstep w).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl wstep w).length = w.length + gs.length := foldl_len_w gs w
    by_cases hlt : j < gs.length
    · rw [wstep, getD_append_lt false _ _ _ (by omega)]
      rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact ih hlt
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      rw [wstep, ← hlen, getD_snoc]
      simp

theorem foldl_w_gate_mono_or (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hor : (gs[j]).op = GateOp.or) (u : ℕ) (hu : u ∈ (gs[j]).inputs)
    (hval : ((gs.take j).foldl wstep w).getD u false = true) :
    (gs.foldl wstep w).getD (w.length + j) false = true := by
  rw [foldl_w_gate gs w j hj, hor]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨u, hu, hval⟩, rfl⟩

theorem foldl_orSets_mono (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    ∀ j < gs.length, ∀ k ∈ (gs.foldl (orStep n) []).getD j [],
      (gs.foldl wstep (List.ofFn x)).getD (n + k) false = true →
      (gs.foldl wstep (List.ofFn x)).getD (n + j) false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj k hk htk
    have hlen_or : (gs.foldl (orStep n) []).length = gs.length := by
      rw [foldl_len_or]; simp
    have hlen_w : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
      rw [foldl_len_w, List.length_ofFn]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hk htk ⊢
    by_cases hlt : j < gs.length
    · rw [orStep, getD_append_lt [] _ _ j (by omega)] at hk
      have hk_lt : k < gs.length := by
        have hmem : ∀ (gs' : List Gate) (j' : ℕ), j' < gs'.length →
            ∀ k' ∈ (gs'.foldl (orStep n) []).getD j' [], k' < gs'.length := by
          intro gs'
          induction gs' using List.reverseRecOn with
          | nil => intro _ hj'; simp at hj'
          | append_singleton gs' g' ih' =>
            intro j' hj' k' hk'
            have hl' : (gs'.foldl (orStep n) []).length = gs'.length := by rw [foldl_len_or]; simp
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep] at hk'
            by_cases hlt' : j' < gs'.length
            · rw [getD_append_lt [] _ _ j' (by omega)] at hk'
              have := ih' j' hlt' k' hk'
              simp; omega
            · have heq' : j' = gs'.length := by simp at hj'; omega
              subst heq'
              rw [← hl', getD_snoc] at hk'
              simp only [List.mem_cons] at hk'
              rcases hk' with rfl | hk'
              · rw [hl']; simp
              · split at hk'
                · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk'
                  rcases hk' with ⟨w, ⟨_, hw1, hw2⟩, hk''⟩
                  have := ih' (w - n) (by omega) k' hk''
                  simp; omega
                · simp at hk'
        exact hmem gs j hlt k hk
      rw [wstep, getD_append_lt false _ _ _ (by omega)] at htk
      rw [wstep, getD_append_lt false _ _ _ (by omega)]
      exact ih j hlt k hk htk
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      rw [orStep, ← hlen_or, getD_snoc] at hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · rw [hlen_or] at htk; exact htk
      · split at hk
        · rename_i hor
          simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk
          rcases hk with ⟨w, ⟨hw_in, hw1, hw2⟩, hk'⟩
          rw [hlen_or] at hw2
          have hwn : w - n < gs.length := by omega
          have hkw : (gs.foldl wstep (List.ofFn x)).getD (n + k) false = true := by
            have hk_lt : k < gs.length := by
              have hmem : ∀ (gs' : List Gate) (j' : ℕ), j' < gs'.length →
                  ∀ k' ∈ (gs'.foldl (orStep n) []).getD j' [], k' < gs'.length := by
                intro gs'
                induction gs' using List.reverseRecOn with
                | nil => intro _ hj'; simp at hj'
                | append_singleton gs' g' ih' =>
                  intro j' hj' k' hk'
                  have hl' : (gs'.foldl (orStep n) []).length = gs'.length := by rw [foldl_len_or]; simp
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep] at hk'
                  by_cases hlt' : j' < gs'.length
                  · rw [getD_append_lt [] _ _ j' (by omega)] at hk'
                    have := ih' j' hlt' k' hk'; simp; omega
                  · have heq' : j' = gs'.length := by simp at hj'; omega
                    subst heq'
                    rw [← hl', getD_snoc] at hk'
                    simp only [List.mem_cons] at hk'
                    rcases hk' with rfl | hk'
                    · rw [hl']; simp
                    · split at hk'
                      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk'
                        rcases hk' with ⟨w', ⟨_, hw1', hw2'⟩, hk''⟩
                        have := ih' (w' - n) (by omega) k' hk''; simp; omega
                      · simp at hk'
              exact hmem gs (w - n) hwn k hk'
            rw [wstep, getD_append_lt false _ _ _ (by omega)] at htk
            exact htk
          have hw_true : (gs.foldl wstep (List.ofFn x)).getD w false = true := by
            have := ih (w - n) hwn k hk' hkw
            rwa [show n + (w - n) = w by omega] at this
          rw [wstep, ← hlen_w, getD_snoc, hor]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map]
          exact ⟨true, ⟨w, hw_in, hw_true⟩, rfl⟩
        · simp at hk

theorem orIn_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (u : Fin n)
    (hu : u ∈ orIn n C w) (hx : x u = true) :
    (C.wires (List.ofFn x)).getD w false = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with heq | ⟨k, hk, hreach, hor, hin⟩
  · subst heq
    change (C.gates.foldl wstep (List.ofFn x)).getD u.val false = true
    rw [foldl_w_prefix C.gates (List.ofFn x) u.val (by simp),
        List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact hx
  · rcases hreach with ⟨hnw, hmem⟩
    have hwn_lt : w - n < C.gates.length := by
      by_contra h
      have hlen : (orSets n C).length = C.gates.length := by
        unfold orSets; rw [foldl_len_or]; simp
      rw [List.getD_eq_default _ _ (by omega)] at hmem
      simp at hmem
    have hgk : (C.gates[k]).op = GateOp.or := by
      simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hor
    have hgin : u.val ∈ (C.gates[k]).inputs := by
      simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hin
    have hku : ((C.gates.take k).foldl wstep (List.ofFn x)).getD u.val false = true := by
      rw [foldl_w_prefix _ _ u.val (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      exact hx
    have hk_true : (C.gates.foldl wstep (List.ofFn x)).getD (n + k) false = true := by
      have := foldl_w_gate_mono_or C.gates (List.ofFn x) k hk hgk u.val hgin hku
      rwa [List.length_ofFn] at this
    have hw_true := foldl_orSets_mono n C.gates x (w - n) hwn_lt k hmem hk_true
    rwa [show n + (w - n) = w by omega] at hw_true

theorem top_cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hao : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (u v : Fin n)
    (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) : G.Adj u v := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨ha_lt, ha_and, ha_below⟩
  have hga : gateAt C a = C.gates[a] := List.getD_eq_getElem _ _ ha_lt
  have hlen2 : (C.gates[a]).inputs.length = 2 := hao.2.2 _ (List.getElem_mem ha_lt)
  obtain ⟨w0, w1, hw⟩ : ∃ w0 w1, (C.gates[a]).inputs = [w0, w1] := by
    match h : (C.gates[a]).inputs with
    | [w0, w1] => exact ⟨w0, w1, rfl⟩
    | [] | [_] | _ :: _ :: _ :: _ => simp [h] at hlen2
  have hop0 : opnd C a 0 = w0 := by
    simp only [opnd, hga, hw]; rfl
  have hop1 : opnd C a 1 = w1 := by
    simp only [opnd, hga, hw]; rfl
  have hw0_lt : w0 < n + a := hao.2.1 a ha_lt w0 (by rw [hga, hw]; simp)
  have hw1_lt : w1 < n + a := hao.2.1 a ha_lt w1 (by rw [hga, hw]; simp)
  let x : Fin n → Bool := pairInput u v
  have hxu : x u = true := by simp [x, pairInput]
  have hxv : x v = true := by simp [x, pairInput]
  have h0_full : (C.wires (List.ofFn x)).getD w0 false = true :=
    orIn_true C x w0 u (hop0 ▸ hu) hxu
  have h1_full : (C.wires (List.ofFn x)).getD w1 false = true :=
    orIn_true C x w1 v (hop1 ▸ hv) hxv
  have hpref_take : ∀ i < n + a,
      ((C.gates.take a).foldl wstep (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
    intro i hi
    have hsplit : C.gates = C.gates.take a ++ C.gates.drop a := (List.take_append_drop a C.gates).symm
    have hlen_t : ((C.gates.take a).foldl wstep (List.ofFn x)).length = n + a := by
      rw [foldl_len_w, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt ha_lt)]
    change _ = (C.gates.foldl wstep (List.ofFn x)).getD i false
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_w_prefix (C.gates.drop a) _ i (by omega)).symm
  have hgate_true : gateVal n C a x = true := by
    change (C.gates.foldl wstep (List.ofFn x)).getD (n + a) false = true
    have := foldl_w_gate C.gates (List.ofFn x) a ha_lt
    rw [List.length_ofFn] at this
    rw [this, show (C.gates[a]).op = GateOp.and from hga ▸ ha_and, hw]
    simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, Bool.and_true]
    rw [hpref_take w0 hw0_lt, hpref_take w1 hw1_lt, h0_full, h1_full]
    rfl
  have hgf := ha_below x hgate_true
  simp [graphFun] at hgf
  rcases hgf with ⟨p, q, hpq, hp, hq⟩
  simp only [x, pairInput, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl (G.ne_of_adj hpq)
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl (G.ne_of_adj hpq)

theorem main_proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), NoFourCycle G → IsLeastAO G C → TopForm G C →
      ∃ S : Finset (Fin n),
        (∀ u v, G.Adj u v → s(u, v) ∉ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        S.card ≤ (tops G C \ centreless G C).card := by
  classical
  intro n G _ C hno4 hleast _
  have hao : IsAO2 n C := hleast.1
  have hcard1 : ∀ a ∈ tops G C \ centreless G C,
      (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    rcases ha with ⟨ha_top, ha_nc⟩
    simp only [centreless, Finset.mem_filter, not_and, not_or] at ha_nc
    rcases ha_nc ha_top with ⟨h0ne, h1ne⟩
    have h0pos : 0 < (side (n := n) C a 0).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0ne)
    have h1pos : 0 < (side (n := n) C a 1).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h1ne)
    by_contra hboth
    push Not at hboth
    have h0ge2 : 1 < (side (n := n) C a 0).card := by omega
    have h1ge2 : 1 < (side (n := n) C a 1).card := by omega
    rcases Finset.one_lt_card.mp h0ge2 with ⟨u1, hu1, u2, hu2, hune⟩
    rcases Finset.one_lt_card.mp h1ge2 with ⟨v1, hv1, v2, hv2, hvne⟩
    have hsub : {v1, v2} ⊆ Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj u2 w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨top_cross_adj G C hao a ha_top u1 w hu1 hv1,
               top_cross_adj G C hao a ha_top u2 w hu2 hv1⟩
      · exact ⟨top_cross_adj G C hao a ha_top u1 w hu1 hv2,
               top_cross_adj G C hao a ha_top u2 w hu2 hv2⟩
    have h2 : 2 ≤ (Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj u2 w).card := by
      calc 2 = ({v1, v2} : Finset (Fin n)).card := (Finset.card_pair hvne).symm
        _ ≤ _ := Finset.card_le_card hsub
    have h1 := hno4 u1 u2 hune
    omega
  have hex : ∀ a ∈ tops G C \ centreless G C, ∃ c : Fin n,
      (∀ u ∈ side (n := n) C a 0, u = c) ∨ (∀ v ∈ side (n := n) C a 1, v = c) := by
    intro a ha
    rcases hcard1 a ha with h0 | h1
    · rcases Finset.card_eq_one.mp h0 with ⟨c, hc⟩
      exact ⟨c, Or.inl (fun u hu => by rw [hc] at hu; exact Finset.mem_singleton.mp hu)⟩
    · rcases Finset.card_eq_one.mp h1 with ⟨c, hc⟩
      exact ⟨c, Or.inr (fun v hv => by rw [hc] at hv; exact Finset.mem_singleton.mp hv)⟩
  let S : Finset (Fin n) := (tops G C \ centreless G C).attach.image fun a => (hex a.1 a.2).choose
  refine ⟨S, ?_, ?_⟩
  · intro u v huv hnotU
    have hedge : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    have hstar : s(u, v) ∈ starEdges G C := by
      by_contra h
      exact hnotU (Finset.mem_sdiff.mpr ⟨hedge, h⟩)
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hstar
    rcases hstar with ⟨a, ha_top, ⟨p, q⟩, ⟨hp, hq⟩, hpq⟩
    have ha_sdiff : a ∈ tops G C \ centreless G C := by
      rw [Finset.mem_sdiff]
      refine ⟨ha_top, ?_⟩
      simp only [centreless, Finset.mem_filter, not_and, not_or]
      intro _
      exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨p, hp⟩, Finset.nonempty_iff_ne_empty.mp ⟨q, hq⟩⟩
    have hspec := (hex a ha_sdiff).choose_spec
    have hc_mem : (hex a ha_sdiff).choose ∈ S :=
      Finset.mem_image.mpr ⟨⟨a, ha_sdiff⟩, Finset.mem_attach _ _, rfl⟩
    rw [Sym2.eq_iff] at hpq
    rcases hspec with h0 | h1
    · have hpc : p = (hex a ha_sdiff).choose := h0 p hp
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (hpc ▸ hc_mem)
      · exact Or.inr (hpc ▸ hc_mem)
    · have hqc : q = (hex a ha_sdiff).choose := h1 q hq
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (hqc ▸ hc_mem)
      · exact Or.inl (hqc ▸ hc_mem)
  · calc S.card ≤ (tops G C \ centreless G C).attach.card := Finset.card_image_le
      _ = (tops G C \ centreless G C).card := Finset.card_attach

end PEqualNP.Outside.L_meta_18800_aux

theorem PEqualNP.Outside.L_meta_18800 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → s(x9, x10) ∉ PEqualNP.TopForm.Ustar x2 x4 → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card)  := by
  exact PEqualNP.Outside.L_meta_18800_aux.main_proof
