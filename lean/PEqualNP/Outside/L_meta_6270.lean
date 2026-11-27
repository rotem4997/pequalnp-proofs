import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6270_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

/-! ## Section 1: Monotonicity of Monotone2 Circuits -/

private def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ u v : List Bool, u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      (gs.foldl circuitStep u).length = (gs.foldl circuitStep v).length ∧
      ∀ i, (gs.foldl circuitStep u).getD i false = true →
        (gs.foldl circuitStep v).getD i false = true := by
  induction gs with
  | nil => intro u v hlen hle; exact ⟨hlen, hle⟩
  | cons g gs ih =>
    intro u v hlen hle
    have hg := hmono g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    have hbit : g.op.eval (g.inputs.map fun i => u.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
      rcases hg with hop | hop
      · rw [hop]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
        rintro h _ ⟨idx, hidx, rfl⟩
        exact hle idx (h _ ⟨idx, hidx, rfl⟩)
      · rw [hop]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨idx, hidx, rfl⟩, htrue⟩
        exact ⟨v.getD idx false, ⟨idx, hidx, rfl⟩, hle idx htrue⟩
    rw [List.foldl_cons, List.foldl_cons]
    apply ih hgs (circuitStep u g) (circuitStep v g)
    · simp [circuitStep, hlen]
    · intro i hi
      by_cases hlt : i < u.length
      · have h1 : (circuitStep u g).getD i false = u.getD i false := by
          simp [circuitStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        have h2 : (circuitStep v g).getD i false = v.getD i false := by
          simp [circuitStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < v.length)]
        rw [h1] at hi; rw [h2]; exact hle i hi
      · by_cases heq : i = u.length
        · subst heq
          have h1 : (circuitStep u g).getD u.length false = g.op.eval (g.inputs.map fun j => u.getD j false) := by
            simp [circuitStep, List.getD_eq_getElem?_getD]
          have h2 : (circuitStep v g).getD u.length false = g.op.eval (g.inputs.map fun j => v.getD j false) := by
            rw [hlen]; simp [circuitStep, List.getD_eq_getElem?_getD]
          rw [h1] at hi; rw [h2]; exact hbit hi
        · have h1 : (circuitStep u g).getD i false = false :=
            List.getD_eq_default _ _ (by simp [circuitStep]; omega)
          rw [h1] at hi; cases hi

private lemma eval_incidenceInput_mono (C : Circuit) (hmono : Monotone2 C)
    {X₁ X₂ Y₁ Y₂ : Finset (Fin 13)} (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) :
    C.eval (incidenceInput X₁ Y₁) = true → C.eval (incidenceInput X₂ Y₂) = true := by
  have hmg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  have hlen : (incidenceInput X₁ Y₁).length = (incidenceInput X₂ Y₂).length := by
    simp [incidenceInput]
  have hle : ∀ i, (incidenceInput X₁ Y₁).getD i false = true →
      (incidenceInput X₂ Y₂).getD i false = true := by
    intro i hi
    by_cases h1 : i < 13
    · have hu : (incidenceInput X₁ Y₁).getD i false = decide (⟨i, h1⟩ ∈ X₁) := by
        simp only [incidenceInput, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [h1] : i < (List.ofFn fun p : Fin 13 => decide (p ∈ X₁)).length),
          List.getElem?_ofFn, h1, ↓reduceDIte, Option.getD_some]
      have hv : (incidenceInput X₂ Y₂).getD i false = decide (⟨i, h1⟩ ∈ X₂) := by
        simp only [incidenceInput, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [h1] : i < (List.ofFn fun p : Fin 13 => decide (p ∈ X₂)).length),
          List.getElem?_ofFn, h1, ↓reduceDIte, Option.getD_some]
      rw [hu, decide_eq_true_eq] at hi
      rw [hv, decide_eq_true_eq]
      exact hX hi
    · by_cases h2 : i < 26
      · have hi' : i - 13 < 13 := by omega
        have hu : (incidenceInput X₁ Y₁).getD i false = decide (⟨i - 13, hi'⟩ ∈ Y₁) := by
          simp only [incidenceInput, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp; omega : (List.ofFn fun p : Fin 13 => decide (p ∈ X₁)).length ≤ i),
            List.length_ofFn, List.getElem?_ofFn, hi', ↓reduceDIte, Option.getD_some]
        have hv : (incidenceInput X₂ Y₂).getD i false = decide (⟨i - 13, hi'⟩ ∈ Y₂) := by
          simp only [incidenceInput, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp; omega : (List.ofFn fun p : Fin 13 => decide (p ∈ X₂)).length ≤ i),
            List.length_ofFn, List.getElem?_ofFn, hi', ↓reduceDIte, Option.getD_some]
        rw [hu, decide_eq_true_eq] at hi
        rw [hv, decide_eq_true_eq]
        exact hY hi
      · have hu : (incidenceInput X₁ Y₁).getD i false = false :=
          List.getD_eq_default _ _ (by simp [incidenceInput]; omega)
        rw [hu] at hi; cases hi
  exact (foldl_mono C.gates hmg _ _ hlen hle).2 C.output

/-! ## Section 2: PG(2, 3) Finite Combinatorics -/

private def inc (p l : Fin 13) : Bool :=
  let d := (p.val + 13 - l.val) % 13
  d == 0 || d == 1 || d == 3 || d == 9

private lemma mem_singerLines3_iff (p l : Fin 13) :
    p ∈ singerLines3 l ↔ inc p l = true := by
  revert p l; decide

private lemma inc_add (p l s : Fin 13) : inc (p + s) (l + s) = inc p l := by
  have h : ∀ a b c : Fin 13, inc (a + c) (b + c) = inc a b := by decide
  exact h p l s

private lemma inc_sub_cancel (p l s : Fin 13) : inc (p + s) l = inc p (l - s) := by
  have h : l = (l - s) + s := (sub_add_cancel l s).symm
  conv_lhs => rw [h]
  exact inc_add p (l - s) s

private lemma card_filter_eq_length (P : Fin 13 → Bool) :
    (Finset.univ.filter fun x : Fin 13 => P x = true).card = ((List.finRange 13).filter P).length := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter P)]
  congr 1; ext x; simp

private lemma lines_through_card_decide :
    (List.finRange 13).all (fun p => decide (((List.finRange 13).filter fun l => inc p l).length = 4)) = true := by
  decide

private lemma lines_through_card (p : Fin 13) :
    (Finset.univ.filter fun l : Fin 13 => inc p l = true).card = 4 := by
  rw [card_filter_eq_length]
  simpa using List.all_eq_true.mp lines_through_card_decide p (List.mem_finRange p)

private lemma exists_line_through_decide :
    (List.finRange 13).all (fun p => (List.finRange 13).all fun q =>
      (List.finRange 13).any fun l => inc p l && inc q l) = true := by decide

private lemma exists_line_through (p q : Fin 13) :
    ∃ l : Fin 13, inc p l = true ∧ inc q l = true := by
  have h1 := List.all_eq_true.mp exists_line_through_decide p (List.mem_finRange p)
  have h2 := List.all_eq_true.mp h1 q (List.mem_finRange q)
  obtain ⟨l, _, hl⟩ := List.any_eq_true.mp h2
  simp only [Bool.and_eq_true] at hl
  exact ⟨l, hl⟩

private lemma unique_inter_decide :
    (List.finRange 13).all (fun l0 => (List.finRange 13).all fun l1 =>
      if l0 == l1 then true
      else (List.finRange 13).any fun q =>
        inc q l0 && inc q l1 &&
        (List.finRange 13).all fun p => !(inc p l0 && inc p l1) || p == q) = true := by decide

private lemma unique_inter_of_ne {l0 l1 : Fin 13} (hne : l0 ≠ l1) :
    ∃ q : Fin 13, inc q l0 = true ∧ inc q l1 = true ∧
      ∀ p : Fin 13, inc p l0 = true → inc p l1 = true → p = q := by
  have h1 := List.all_eq_true.mp unique_inter_decide l0 (List.mem_finRange l0)
  have h2 := List.all_eq_true.mp h1 l1 (List.mem_finRange l1)
  have hne' : (l0 == l1) = false := beq_false_of_ne hne
  simp only [hne', Bool.false_eq_true, ↓reduceIte, List.any_eq_true, Bool.and_eq_true] at h2
  rcases h2 with ⟨q, _, ⟨hq0, hq1⟩, hall⟩
  refine ⟨q, hq0, hq1, fun p hp0 hp1 => ?_⟩
  have hp := List.all_eq_true.mp hall p (List.mem_finRange p)
  simp [hp0, hp1] at hp
  exact hp

private lemma miss_pair_card_decide :
    (List.finRange 13).all (fun p0 => (List.finRange 13).all fun p1 =>
      if p0 == p1 then true
      else decide (((List.finRange 13).filter fun l => !inc p0 l && !inc p1 l).length = 6)) = true := by
  decide

private lemma miss_tri_card_decide :
    (List.finRange 13).all (fun p1 => (List.finRange 13).all fun p2 =>
      if p1 == 0 || p2 == 0 || p1 == p2 ||
         (List.finRange 13).any (fun l => inc 0 l && inc p1 l && inc p2 l) then true
      else decide (((List.finRange 13).filter fun l => !inc 0 l && !inc p1 l && !inc p2 l).length = 4)) = true := by
  decide

private lemma no_five_arc_0_decide :
    ([1, 3, 9] : List (Fin 13)).all (fun a =>
      ([12, 2, 8] : List (Fin 13)).all (fun b =>
        ([10, 11, 6] : List (Fin 13)).all (fun c =>
          ([4, 5, 7] : List (Fin 13)).all (fun d =>
            (List.finRange 13).any fun l =>
              decide (3 ≤ (if inc 0 l then 1 else 0) + (if inc a l then 1 else 0) +
                (if inc b l then 1 else 0) + (if inc c l then 1 else 0) +
                (if inc d l then 1 else 0)))))) = true := by decide

private lemma fin13_ne0_mem_branch :
    (List.finRange 13).all (fun p =>
      if p == 0 then true
      else (p ∈ ([1, 3, 9] : List (Fin 13))) || (p ∈ ([12, 2, 8] : List (Fin 13))) ||
           (p ∈ ([10, 11, 6] : List (Fin 13))) || (p ∈ ([4, 5, 7] : List (Fin 13)))) = true := by
  decide

private lemma branches_on_lines :
    (([1, 3, 9] : List (Fin 13)).all fun p => inc p 0) &&
    (([12, 2, 8] : List (Fin 13)).all fun p => inc p 12) &&
    (([10, 11, 6] : List (Fin 13)).all fun p => inc p 10) &&
    (([4, 5, 7] : List (Fin 13)).all fun p => inc p 4) &&
    inc 0 0 && inc 0 12 && inc 0 10 && inc 0 4 = true := by decide

private lemma tri_lines_comp_quad_decide :
    (List.finRange 13).all (fun l1 => (List.finRange 13).all fun l2 =>
      if l1 == 0 || l2 == 0 || l1 == l2 ||
         (List.finRange 13).any (fun p => inc p 0 && inc p l1 && inc p l2) then true
      else
        let Q := (List.finRange 13).filter fun p => !inc p 0 && !inc p l1 && !inc p l2
        decide (Q.length = 4) &&
        (List.finRange 13).all fun l => decide ((Q.filter fun p => inc p l).length ≤ 2)) = true := by
  decide

private lemma quad0_miss_props_decide :
    (List.finRange 13).all (fun b => (List.finRange 13).all fun c => (List.finRange 13).all fun d =>
      let ok := b != 0 && c != 0 && d != 0 && b != c && b != d && c != d &&
        (List.finRange 13).all fun l =>
          decide ((if inc 0 l then 1 else 0) + (if inc b l then 1 else 0) +
            (if inc c l then 1 else 0) + (if inc d l then 1 else 0) ≤ 2)
      if !ok then true
      else
        let ms := (List.finRange 13).filter fun l => !inc 0 l && !inc b l && !inc c l && !inc d l
        decide (ms.length ≤ 3) &&
        (List.finRange 13).all fun p => decide ((ms.filter fun l => inc p l).length ≤ 2)) = true := by
  decide

/-! ## Section 3: Quadrangle Missed-Line Properties -/

private lemma card_eq_four_of_card_eq_four {α : Type*} [DecidableEq α] {s : Finset α}
    (h : s.card = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have h3 : (s.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, h]
  obtain ⟨b, c, d, hbc, hbd, hcd, heq⟩ := Finset.card_eq_three.mp h3
  have hba : b ≠ a := fun h => by
    have : b ∈ s.erase a := by rw [heq]; simp
    rw [h] at this; exact Finset.notMem_erase a s this
  have hca : c ≠ a := fun h => by
    have : c ∈ s.erase a := by rw [heq]; simp
    rw [h] at this; exact Finset.notMem_erase a s this
  have hda : d ≠ a := fun h => by
    have : d ∈ s.erase a := by rw [heq]; simp
    rw [h] at this; exact Finset.notMem_erase a s this
  refine ⟨a, b, c, d, hba.symm, hca.symm, hda.symm, hbc, hbd, hcd, ?_⟩
  rw [← Finset.insert_erase ha, heq]

private lemma card_inter_eq_sum4 {a b c d : Fin 13}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (l : Fin 13) :
    (({a, b, c, d} : Finset (Fin 13)) ∩ singerLines3 l).card =
      (if inc a l then 1 else 0) + (if inc b l then 1 else 0) +
      (if inc c l then 1 else 0) + (if inc d l then 1 else 0) := by
  have hstep : ∀ (x : Fin 13) (T : Finset (Fin 13)), x ∉ T →
      ((insert x T) ∩ singerLines3 l).card = (if inc x l then 1 else 0) + (T ∩ singerLines3 l).card := by
    intro x T hxT
    by_cases hx : inc x l = true
    · have hxm : x ∈ singerLines3 l := (mem_singerLines3_iff x l).mpr hx
      have heq : insert x T ∩ singerLines3 l = insert x (T ∩ singerLines3 l) := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hT, hy⟩; exact Or.inl rfl; exact Or.inr ⟨hT, hy⟩
        · rintro (rfl | ⟨hT, hy⟩); exact ⟨Or.inl rfl, hxm⟩; exact ⟨Or.inr hT, hy⟩
      rw [heq, Finset.card_insert_of_notMem (fun h => hxT (Finset.mem_inter.mp h).1)]
      simp [hx]; omega
    · have hxm : x ∉ singerLines3 l := fun h => hx ((mem_singerLines3_iff x l).mp h)
      have heq : insert x T ∩ singerLines3 l = T ∩ singerLines3 l := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hT, hy⟩; exact (hxm hy).elim; exact ⟨hT, hy⟩
        · rintro ⟨hT, hy⟩; exact ⟨Or.inr hT, hy⟩
      rw [heq]; simp [hx]
  have h1 := hstep a {b, c, d} (by simp [hab, hac, had])
  have h2 := hstep b {c, d} (by simp [hbc, hbd])
  have h3 := hstep c {d} (by simp [hcd])
  have h4 := hstep d ∅ (by simp)
  change (({d} : Finset (Fin 13)) ∩ singerLines3 l).card =
    (if inc d l = true then 1 else 0) + (∅ ∩ singerLines3 l).card at h4
  simp only [Finset.empty_inter, Finset.card_empty, Nat.add_zero] at h4
  omega

private lemma quad_missLines_props (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
    (missLines singerLines3 Q).card ≤ 3 ∧
    ∀ p : Fin 13, {l ∈ missLines singerLines3 Q | p ∈ singerLines3 l}.card ≤ 2 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four_of_card_eq_four hQ.1
  let b' := b - a; let c' := c - a; let d' := d - a
  have hne_b : b' ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
  have hne_c : c' ≠ 0 := fun h => hac (sub_eq_zero.mp h).symm
  have hne_d : d' ≠ 0 := fun h => had (sub_eq_zero.mp h).symm
  have hne_bc : b' ≠ c' := fun h => hbc (by have := congrArg (· + a) h; simpa [b', c'] using this)
  have hne_bd : b' ≠ d' := fun h => hbd (by have := congrArg (· + a) h; simpa [b', d'] using this)
  have hne_cd : c' ≠ d' := fun h => hcd (by have := congrArg (· + a) h; simpa [c', d'] using this)
  have hok : (b' != 0 && c' != 0 && d' != 0 && b' != c' && b' != d' && c' != d' &&
      (List.finRange 13).all fun l =>
        decide ((if inc 0 l then 1 else 0) + (if inc b' l then 1 else 0) +
          (if inc c' l then 1 else 0) + (if inc d' l then 1 else 0) ≤ 2)) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨hne_b, hne_c⟩, hne_d⟩, hne_bc⟩, hne_bd⟩, hne_cd⟩, ?_⟩
    intro l _
    have hle := hQ.2 (l + a)
    rw [card_inter_eq_sum4 hab hac had hbc hbd hcd (l + a)] at hle
    have h0 : inc 0 l = inc a (l + a) := by simpa using (inc_add 0 l a).symm
    have hb : inc b' l = inc b (l + a) := by simpa [b', sub_add_cancel] using (inc_add b' l a).symm
    have hc : inc c' l = inc c (l + a) := by simpa [c', sub_add_cancel] using (inc_add c' l a).symm
    have hd : inc d' l = inc d (l + a) := by simpa [d', sub_add_cancel] using (inc_add d' l a).symm
    rw [h0, hb, hc, hd]
    exact hle
  have hdec1 := List.all_eq_true.mp quad0_miss_props_decide b' (List.mem_finRange _)
  have hdec2 := List.all_eq_true.mp hdec1 c' (List.mem_finRange _)
  have hdec3 := List.all_eq_true.mp hdec2 d' (List.mem_finRange _)
  simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hdec3
  rcases hdec3 with ⟨hms_len, hms_deg⟩
  have hmiss_eq : missLines singerLines3 {a, b, c, d} =
      (Finset.univ.filter fun l : Fin 13 =>
        (!inc 0 l && !inc b' l && !inc c' l && !inc d' l) = true).image (· + a) := by
    ext l
    simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right,
      Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hdisj
      refine ⟨l - a, ?_, sub_add_cancel l a⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      have ha' : inc a l = false := by
        cases h : inc a l; rfl; exact (hdisj (Or.inl rfl) ((mem_singerLines3_iff a l).mpr h)).elim
      have hb' : inc b l = false := by
        cases h : inc b l; rfl; exact (hdisj (Or.inr (Or.inl rfl)) ((mem_singerLines3_iff b l).mpr h)).elim
      have hc' : inc c l = false := by
        cases h : inc c l; rfl; exact (hdisj (Or.inr (Or.inr (Or.inl rfl))) ((mem_singerLines3_iff c l).mpr h)).elim
      have hd' : inc d l = false := by
        cases h : inc d l; rfl; exact (hdisj (Or.inr (Or.inr (Or.inr rfl))) ((mem_singerLines3_iff d l).mpr h)).elim
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simpa [← inc_sub_cancel] using ha'
      · simpa [b', ← inc_sub_cancel, sub_add_cancel] using hb'
      · simpa [c', ← inc_sub_cancel, sub_add_cancel] using hc'
      · simpa [d', ← inc_sub_cancel, sub_add_cancel] using hd'
    · rintro ⟨l', hl', rfl⟩ p hp hpl
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hl'
      rw [mem_singerLines3_iff] at hpl
      rcases hp with hp | hp | hp | hp
      · rw [hp] at hpl
        have : inc 0 l' = true := by rw [← inc_add 0 l' a, zero_add]; exact hpl
        rw [hl'.1.1.1] at this; cases this
      · rw [hp] at hpl
        have : inc b' l' = true := by rw [← inc_add b' l' a, sub_add_cancel]; exact hpl
        rw [hl'.1.1.2] at this; cases this
      · rw [hp] at hpl
        have : inc c' l' = true := by rw [← inc_add c' l' a, sub_add_cancel]; exact hpl
        rw [hl'.1.2] at this; cases this
      · rw [hp] at hpl
        have : inc d' l' = true := by rw [← inc_add d' l' a, sub_add_cancel]; exact hpl
        rw [hl'.2] at this; cases this
  constructor
  · rw [hmiss_eq, Finset.card_image_of_injective _ (add_left_injective a), card_filter_eq_length]
    exact hms_len
  · intro p
    have hfilt_eq : {l ∈ missLines singerLines3 {a, b, c, d} | p ∈ singerLines3 l} =
        (Finset.univ.filter fun l : Fin 13 =>
          ((!inc 0 l && !inc b' l && !inc c' l && !inc d' l) && inc (p - a) l) = true).image (· + a) := by
      ext l
      rw [hmiss_eq]
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨l', hl', rfl⟩, hpl⟩
        refine ⟨l', ⟨hl', ?_⟩, rfl⟩
        rw [mem_singerLines3_iff] at hpl
        simpa [sub_add_cancel] using (inc_add (p - a) l' a).symm.trans (by simpa [sub_add_cancel] using hpl)
      · rintro ⟨l', ⟨hl', hpl'⟩, rfl⟩
        refine ⟨⟨l', hl', rfl⟩, ?_⟩
        rw [mem_singerLines3_iff]
        simpa [sub_add_cancel] using (inc_add (p - a) l' a).trans hpl'
    rw [hfilt_eq, Finset.card_image_of_injective _ (add_left_injective a), card_filter_eq_length]
    have hfl : ((List.finRange 13).filter fun l =>
        (!inc 0 l && !inc b' l && !inc c' l && !inc d' l) && inc (p - a) l) =
      (((List.finRange 13).filter fun l => !inc 0 l && !inc b' l && !inc c' l && !inc d' l).filter fun l =>
        inc (p - a) l) := by
      rw [List.filter_filter]; congr 1; funext l; exact Bool.and_comm _ _
    rw [hfl]
    exact hms_deg (p - a) (List.mem_finRange _)

/-! ## Section 4: Every Arc in PG(2, 3) Has Size ≤ 4 -/

private lemma arc_card_le_four (X : Finset (Fin 13))
    (harc : ∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2) : X.card ≤ 4 := by
  by_contra h5
  push Not at h5
  obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  let X' : Finset (Fin 13) := X.image (· - p0)
  have hX'_card : 5 ≤ X'.card := by
    rw [Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h)]; omega
  have h0_mem : (0 : Fin 13) ∈ X' := Finset.mem_image.mpr ⟨p0, hp0, sub_self p0⟩
  have harc' : ∀ l : Fin 13, (X' ∩ singerLines3 l).card ≤ 2 := by
    intro l
    have heq : (X' ∩ singerLines3 l).card = (X ∩ singerLines3 (l + p0)).card := by
      have hsub : X' ∩ singerLines3 l = (X ∩ singerLines3 (l + p0)).image (· - p0) := by
        ext q
        simp only [X', Finset.mem_inter, Finset.mem_image]
        constructor
        · rintro ⟨⟨p, hp, rfl⟩, hql⟩
          refine ⟨p, ⟨hp, ?_⟩, rfl⟩
          rw [mem_singerLines3_iff] at hql ⊢
          rw [← sub_add_cancel p p0, inc_add]; exact hql
        · rintro ⟨p, ⟨hp, hpl⟩, rfl⟩
          refine ⟨⟨p, hp, rfl⟩, ?_⟩
          rw [mem_singerLines3_iff] at hpl ⊢
          rw [← sub_add_cancel p p0, inc_add] at hpl; exact hpl
      rw [hsub, Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h)]
    rw [heq]; exact harc (l + p0)
  let B0 : Finset (Fin 13) := {1, 3, 9}
  let B1 : Finset (Fin 13) := {12, 2, 8}
  let B2 : Finset (Fin 13) := {10, 11, 6}
  let B3 : Finset (Fin 13) := {4, 5, 7}
  have hle1 : ∀ (B : Finset (Fin 13)) (l : Fin 13), (0 : Fin 13) ∉ B →
      inc 0 l = true → (∀ p ∈ B, inc p l = true) → (X' ∩ B).card ≤ 1 := by
    intro B l h0nB h0l hBl
    have hsub : insert (0 : Fin 13) (X' ∩ B) ⊆ X' ∩ singerLines3 l := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_inter] at hp ⊢
      rcases hp with rfl | ⟨hpX, hpB⟩
      · exact ⟨h0_mem, (mem_singerLines3_iff 0 l).mpr h0l⟩
      · exact ⟨hpX, (mem_singerLines3_iff p l).mpr (hBl p hpB)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (fun h => h0nB (Finset.mem_inter.mp h).2)] at hc
    have := harc' l
    omega
  have hb := branches_on_lines
  simp only [Bool.and_eq_true, List.all_eq_true] at hb
  have hc0 : (X' ∩ B0).card ≤ 1 := hle1 B0 0 (by decide) hb.1.1.1.2 (fun p hp => hb.1.1.1.1.1.1.1 p (by simpa [B0] using hp))
  have hc1 : (X' ∩ B1).card ≤ 1 := hle1 B1 12 (by decide) hb.1.1.2 (fun p hp => hb.1.1.1.1.1.1.2 p (by simpa [B1] using hp))
  have hc2 : (X' ∩ B2).card ≤ 1 := hle1 B2 10 (by decide) hb.1.2 (fun p hp => hb.1.1.1.1.1.2 p (by simpa [B2] using hp))
  have hc3 : (X' ∩ B3).card ≤ 1 := hle1 B3 4 (by decide) hb.2 (fun p hp => hb.1.1.1.1.2 p (by simpa [B3] using hp))
  have hcov : X'.erase 0 ⊆ (X' ∩ B0) ∪ (X' ∩ B1) ∪ (X' ∩ B2) ∪ (X' ∩ B3) := by
    intro p hp
    have hne : p ≠ 0 := (Finset.mem_erase.mp hp).1
    have hpX : p ∈ X' := (Finset.mem_erase.mp hp).2
    have hm := List.all_eq_true.mp fin13_ne0_mem_branch p (List.mem_finRange p)
    have hne' : (p == 0) = false := beq_false_of_ne hne
    simp only [hne', Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hm
    simp only [Finset.mem_union, Finset.mem_inter, B0, B1, B2, B3, Finset.mem_insert, Finset.mem_singleton]
    rcases hm with ((h | h) | h) | h
    · left; left; left; exact ⟨hpX, by simpa using h⟩
    · left; left; right; exact ⟨hpX, by simpa using h⟩
    · left; right; exact ⟨hpX, by simpa using h⟩
    · right; exact ⟨hpX, by simpa using h⟩
  have hce : (X'.erase 0).card = X'.card - 1 := Finset.card_erase_of_mem h0_mem
  have hcu : (X'.erase 0).card ≤ (X' ∩ B0).card + (X' ∩ B1).card + (X' ∩ B2).card + (X' ∩ B3).card := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le ((X' ∩ B0) ∪ (X' ∩ B1) ∪ (X' ∩ B2)) (X' ∩ B3)
    have h3 := Finset.card_union_le ((X' ∩ B0) ∪ (X' ∩ B1)) (X' ∩ B2)
    have h4 := Finset.card_union_le (X' ∩ B0) (X' ∩ B1)
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (X' ∩ B0).card)
  obtain ⟨b, hb'⟩ := Finset.card_pos.mp (by omega : 0 < (X' ∩ B1).card)
  obtain ⟨c, hc'⟩ := Finset.card_pos.mp (by omega : 0 < (X' ∩ B2).card)
  obtain ⟨d, hd'⟩ := Finset.card_pos.mp (by omega : 0 < (X' ∩ B3).card)
  have haL : a ∈ ([1, 3, 9] : List (Fin 13)) := by simpa [B0] using (Finset.mem_inter.mp ha).2
  have hbL : b ∈ ([12, 2, 8] : List (Fin 13)) := by simpa [B1] using (Finset.mem_inter.mp hb').2
  have hcL : c ∈ ([10, 11, 6] : List (Fin 13)) := by simpa [B2] using (Finset.mem_inter.mp hc').2
  have hdL : d ∈ ([4, 5, 7] : List (Fin 13)) := by simpa [B3] using (Finset.mem_inter.mp hd').2
  have h5col := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp no_five_arc_0_decide a haL) b hbL) c hcL) d hdL
  obtain ⟨l, _, hl⟩ := List.any_eq_true.mp h5col
  simp only [decide_eq_true_eq] at hl
  have hsub5 : ({0, a, b, c, d} : Finset (Fin 13)) ⊆ X' := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h0_mem
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp hb').1
    · exact (Finset.mem_inter.mp hc').1
    · exact (Finset.mem_inter.mp hd').1
  have hdist : (0 : Fin 13) ∉ ({a, b, c, d} : Finset (Fin 13)) ∧
      a ∉ ({b, c, d} : Finset (Fin 13)) ∧ b ∉ ({c, d} : Finset (Fin 13)) ∧ c ≠ d := by
    have h01 : ∀ x ∈ B0, ∀ y ∈ B1, x ≠ y := by decide
    have h02 : ∀ x ∈ B0, ∀ y ∈ B2, x ≠ y := by decide
    have h03 : ∀ x ∈ B0, ∀ y ∈ B3, x ≠ y := by decide
    have h12 : ∀ x ∈ B1, ∀ y ∈ B2, x ≠ y := by decide
    have h13 : ∀ x ∈ B1, ∀ y ∈ B3, x ≠ y := by decide
    have h23 : ∀ x ∈ B2, ∀ y ∈ B3, x ≠ y := by decide
    have hz0 : ∀ x ∈ B0, x ≠ 0 := by decide
    have hz1 : ∀ x ∈ B1, x ≠ 0 := by decide
    have hz2 : ∀ x ∈ B2, x ≠ 0 := by decide
    have hz3 : ∀ x ∈ B3, x ≠ 0 := by decide
    have haB : a ∈ B0 := (Finset.mem_inter.mp ha).2
    have hbB : b ∈ B1 := (Finset.mem_inter.mp hb').2
    have hcB : c ∈ B2 := (Finset.mem_inter.mp hc').2
    have hdB : d ∈ B3 := (Finset.mem_inter.mp hd').2
    refine ⟨?_, ?_, ?_, h23 c hcB d hdB⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hz0 a haB).symm, (hz1 b hbB).symm, (hz2 c hcB).symm, (hz3 d hdB).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01 a haB b hbB, h02 a haB c hcB, h03 a haB d hdB⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12 b hbB c hcB, h13 b hbB d hdB⟩
  have hcard5 : (({0, a, b, c, d} : Finset (Fin 13)) ∩ singerLines3 l).card =
      (if inc 0 l then 1 else 0) + (if inc a l then 1 else 0) +
      (if inc b l then 1 else 0) + (if inc c l then 1 else 0) + (if inc d l then 1 else 0) := by
    have h4 := card_inter_eq_sum4 (by simp [Finset.mem_insert, Finset.mem_singleton] at hdist; exact hdist.2.1.1)
      (by simp [Finset.mem_insert, Finset.mem_singleton] at hdist; exact hdist.2.1.2.1)
      (by simp [Finset.mem_insert, Finset.mem_singleton] at hdist; exact hdist.2.1.2.2)
      (by simp [Finset.mem_insert, Finset.mem_singleton] at hdist; exact hdist.2.2.1.1)
      (by simp [Finset.mem_insert, Finset.mem_singleton] at hdist; exact hdist.2.2.1.2)
      hdist.2.2.2 l
    by_cases h0l : inc 0 l = true
    · have heq : ({0, a, b, c, d} : Finset (Fin 13)) ∩ singerLines3 l =
          insert 0 ({a, b, c, d} ∩ singerLines3 l) := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hT, hy⟩; exact Or.inl rfl; exact Or.inr ⟨hT, hy⟩
        · rintro (rfl | ⟨hT, hy⟩); exact ⟨Or.inl rfl, (mem_singerLines3_iff 0 l).mpr h0l⟩; exact ⟨Or.inr hT, hy⟩
      rw [heq, Finset.card_insert_of_notMem (fun h => hdist.1 (Finset.mem_inter.mp h).1), h4]
      simp [h0l]; omega
    · have heq : ({0, a, b, c, d} : Finset (Fin 13)) ∩ singerLines3 l = {a, b, c, d} ∩ singerLines3 l := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hT, hy⟩; exact (h0l ((mem_singerLines3_iff 0 l).mp hy)).elim; exact ⟨hT, hy⟩
        · rintro ⟨hT, hy⟩; exact ⟨Or.inr hT, hy⟩
      rw [heq, h4]; simp [h0l]
  have hle2 := le_trans (Finset.card_le_card (Finset.inter_subset_inter_right hsub5)) (harc' l)
  omega

/-! ## Section 5: Extending (X, Y) to a Quadrangle -/

private lemma miss_arc_card_ge_four (X : Finset (Fin 13))
    (hX3 : X.card ≤ 3) (harc : ∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2) :
    4 ≤ (Finset.univ.filter fun l : Fin 13 => ∀ p ∈ X, inc p l = false).card := by
  rcases hX : X.card with _ | _ | _ | _ | n
  · have hx : X = ∅ := Finset.card_eq_zero.mp hX; subst hx
    simp
  · obtain ⟨p0, rfl⟩ := Finset.card_eq_one.mp hX
    have heq : (Finset.univ.filter fun l : Fin 13 => ∀ p ∈ ({p0} : Finset (Fin 13)), inc p l = false) =
        Finset.univ \ (Finset.univ.filter fun l : Fin 13 => inc p0 l = true) := by
      ext l; simp
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, lines_through_card p0]
    omega
  · obtain ⟨p0, p1, hne, rfl⟩ := Finset.card_eq_two.mp hX
    have heq : (Finset.univ.filter fun l : Fin 13 => ∀ p ∈ ({p0, p1} : Finset (Fin 13)), inc p l = false) =
        Finset.univ.filter fun l : Fin 13 => (!inc p0 l && !inc p1 l) = true := by
      ext l; simp
    rw [heq, card_filter_eq_length]
    have hd := List.all_eq_true.mp (List.all_eq_true.mp miss_pair_card_decide p0 (List.mem_finRange _)) p1 (List.mem_finRange _)
    have hne' : (p0 == p1) = false := beq_false_of_ne hne
    simp only [hne', Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hd
    omega
  · obtain ⟨p0, p1, p2, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp hX
    let q1 := p1 - p0; let q2 := p2 - p0
    have hq1 : (q1 == 0) = false := beq_false_of_ne (fun h => h01 (sub_eq_zero.mp h).symm)
    have hq2 : (q2 == 0) = false := beq_false_of_ne (fun h => h02 (sub_eq_zero.mp h).symm)
    have hq12 : (q1 == q2) = false := beq_false_of_ne (fun h => h12 (by have := congrArg (· + p0) h; simpa [q1, q2] using this))
    have hnc : ((List.finRange 13).any fun l => inc 0 l && inc q1 l && inc q2 l) = false := by
      cases hc : (List.finRange 13).any fun l => inc 0 l && inc q1 l && inc q2 l
      · rfl
      · exfalso
        obtain ⟨l, _, hl⟩ := List.any_eq_true.mp hc
        simp only [Bool.and_eq_true] at hl
        have hsub : ({p0, p1, p2} : Finset (Fin 13)) ⊆ ({p0, p1, p2} ∩ singerLines3 (l + p0)) := by
          intro p hp
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          refine ⟨hp, ?_⟩
          rw [mem_singerLines3_iff]
          rcases hp with hp | hp | hp
          · rw [hp]; simpa using (inc_add 0 l p0).trans hl.1.1
          · rw [hp]; simpa [q1, sub_add_cancel] using (inc_add q1 l p0).trans hl.1.2
          · rw [hp]; simpa [q2, sub_add_cancel] using (inc_add q2 l p0).trans hl.2
        have h3 := Finset.card_le_card hsub
        rw [hX] at h3
        have := harc (l + p0)
        omega
    have hd := List.all_eq_true.mp (List.all_eq_true.mp miss_tri_card_decide q1 (List.mem_finRange _)) q2 (List.mem_finRange _)
    simp only [hq1, hq2, hq12, hnc, Bool.or_false, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hd
    have heq : (Finset.univ.filter fun l : Fin 13 => ∀ p ∈ ({p0, p1, p2} : Finset (Fin 13)), inc p l = false) =
        (Finset.univ.filter fun l : Fin 13 => (!inc 0 l && !inc q1 l && !inc q2 l) = true).image (· + p0) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton, Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · intro h
        refine ⟨l - p0, ⟨⟨?_, ?_⟩, ?_⟩, sub_add_cancel l p0⟩
        · simpa [← inc_sub_cancel] using h p0 (Or.inl rfl)
        · simpa [q1, ← inc_sub_cancel, sub_add_cancel] using h p1 (Or.inr (Or.inl rfl))
        · simpa [q2, ← inc_sub_cancel, sub_add_cancel] using h p2 (Or.inr (Or.inr rfl))
      · rintro ⟨l', ⟨⟨h0', h1'⟩, h2'⟩, rfl⟩ p hp
        rcases hp with hp | hp | hp
        · rw [hp]; simpa using (inc_add 0 l' p0).trans h0'
        · rw [hp]; simpa [q1, sub_add_cancel] using (inc_add q1 l' p0).trans h1'
        · rw [hp]; simpa [q2, sub_add_cancel] using (inc_add q2 l' p0).trans h2'
    rw [heq, Finset.card_image_of_injective _ (add_left_injective p0), card_filter_eq_length]
    omega
  · omega

private lemma step_add_line (X Y : Finset (Fin 13))
    (hX3 : X.card ≤ 3) (harc : ∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2)
    (hY2 : Y.card ≤ 2) (hni : ∀ p ∈ X, ∀ l ∈ Y, inc p l = false) :
    ∃ l : Fin 13, l ∉ Y ∧ (∀ p ∈ X, inc p l = false) ∧
      ∀ p : Fin 13, {m ∈ insert l Y | p ∈ singerLines3 m}.card ≤ 2 := by
  let M : Finset (Fin 13) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ X, inc p l = false
  have hM4 : 4 ≤ M.card := miss_arc_card_ge_four X hX3 harc
  rcases hYc : Y.card with _ | _ | _ | m
  · have hY0 : Y = ∅ := Finset.card_eq_zero.mp hYc; subst hY0
    obtain ⟨l, hlM⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
    refine ⟨l, by simp, (Finset.mem_filter.mp hlM).2, fun p => ?_⟩
    have := Finset.card_le_card (Finset.filter_subset (fun m => p ∈ singerLines3 m) {l})
    simp at this ⊢; omega
  · obtain ⟨l0, rfl⟩ := Finset.card_eq_one.mp hYc
    have hpos : 0 < (M.erase l0).card := by
      have := Finset.card_erase_le (s := M) (a := l0)
      by_cases hm : l0 ∈ M
      · rw [Finset.card_erase_of_mem hm]; omega
      · rw [Finset.erase_eq_of_notMem hm]; omega
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
    have hne : l ≠ l0 := (Finset.mem_erase.mp hl).1
    have hlM : l ∈ M := (Finset.mem_erase.mp hl).2
    refine ⟨l, by simp [hne], (Finset.mem_filter.mp hlM).2, fun p => ?_⟩
    have hle := Finset.card_le_card (Finset.filter_subset (fun m => p ∈ singerLines3 m) (insert l {l0}))
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at hle
    exact hle
  · obtain ⟨l0, l1, h01, rfl⟩ := Finset.card_eq_two.mp hYc
    obtain ⟨q, hq0, hq1, hquniq⟩ := unique_inter_of_ne h01
    let B : Finset (Fin 13) := M.filter fun l => inc q l = true
    have hB_lt_M : B.card < M.card := by
      by_cases hXeq3 : X.card = 3
      · -- Every line l ∈ B must be l0 or l1!
        have hBsub : B ⊆ {l0, l1} := by
          intro l hlB
          have hlM : l ∈ M := (Finset.mem_filter.mp hlB).1
          have hql : inc q l = true := (Finset.mem_filter.mp hlB).2
          by_contra hnot
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          -- The 4 lines through q contain l0, l1, l, and 1 remaining line lrem!
          let Lq : Finset (Fin 13) := Finset.univ.filter fun m : Fin 13 => inc q m = true
          have hLq4 : Lq.card = 4 := lines_through_card q
          have h3sub : ({l0, l1, l} : Finset (Fin 13)) ⊆ Lq := by
            intro m hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            simp only [Lq, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hm with rfl | rfl | rfl <;> assumption
          have h3card : ({l0, l1, l} : Finset (Fin 13)).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [h01, Ne.symm hnot.1]),
                Finset.card_insert_of_notMem (by simp [Ne.symm hnot.2]), Finset.card_singleton]
          have hrem_card : (Lq \ {l0, l1, l}).card = 1 := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h3sub, hLq4, h3card]
          obtain ⟨lrem, hlrem_eq⟩ := Finset.card_eq_one.mp hrem_card
          -- Every p ∈ X lies on some line through q, which cannot be l0, l1, or l, so must be lrem!
          have hXsub : X ⊆ X ∩ singerLines3 lrem := by
            intro p hpX
            refine Finset.mem_inter.mpr ⟨hpX, ?_⟩
            obtain ⟨m, hqm, hpm⟩ := exists_line_through q p
            have hmLq : m ∈ Lq := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqm⟩
            have hm_ne0 : m ≠ l0 := fun h => by rw [h] at hpm; have := hni p hpX l0 (by simp); rw [this] at hpm; cases hpm
            have hm_ne1 : m ≠ l1 := fun h => by rw [h] at hpm; have := hni p hpX l1 (by simp); rw [this] at hpm; cases hpm
            have hm_nel : m ≠ l := fun h => by rw [h] at hpm; have := (Finset.mem_filter.mp hlM).2 p hpX; rw [this] at hpm; cases hpm
            have hm_rem : m ∈ Lq \ {l0, l1, l} := by
              simp [hmLq, hm_ne0, hm_ne1, hm_nel]
            rw [hlrem_eq, Finset.mem_singleton] at hm_rem
            subst hm_rem
            exact (mem_singerLines3_iff p m).mpr hpm
          have h3le := Finset.card_le_card hXsub
          have hle2 := harc lrem
          omega
        have hB2 : B.card ≤ 2 := by
          have := Finset.card_le_card hBsub
          rw [Finset.card_insert_of_notMem (by simp [h01]), Finset.card_singleton] at this
          exact this
        omega
      · -- X.card ≤ 2: M.card ≥ 6 while B.card ≤ 4!
        have hB4 : B.card ≤ 4 := by
          have hsub : B ⊆ Finset.univ.filter fun m : Fin 13 => inc q m = true :=
            fun m hm => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm).2⟩
          have := Finset.card_le_card hsub
          rw [lines_through_card q] at this
          exact this
        have hM6 : 6 ≤ M.card := by
          rcases hXc : X.card with _ | _ | _ | k
          · have hx : X = ∅ := Finset.card_eq_zero.mp hXc; subst hx; simp [M]
          · obtain ⟨p0, rfl⟩ := Finset.card_eq_one.mp hXc
            have heq : M = Finset.univ \ (Finset.univ.filter fun l : Fin 13 => inc p0 l = true) := by
              ext l; simp [M]
            rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, lines_through_card p0]
            omega
          · obtain ⟨p0, p1, hne, rfl⟩ := Finset.card_eq_two.mp hXc
            have heq : M = Finset.univ.filter fun l : Fin 13 => (!inc p0 l && !inc p1 l) = true := by
              ext l; simp [M]
            rw [heq, card_filter_eq_length]
            have hd := List.all_eq_true.mp (List.all_eq_true.mp miss_pair_card_decide p0 (List.mem_finRange _)) p1 (List.mem_finRange _)
            have hne' : (p0 == p1) = false := beq_false_of_ne hne
            simp only [hne', Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hd
            omega
          · omega
        omega
    have hdiff_pos : 0 < (M \ B).card := by
      have hBM : B ⊆ M := Finset.filter_subset _ M
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBM]; omega
    obtain ⟨l, hlMB⟩ := Finset.card_pos.mp hdiff_pos
    have hlM : l ∈ M := (Finset.mem_sdiff.mp hlMB).1
    have hlnotB : l ∉ B := (Finset.mem_sdiff.mp hlMB).2
    have hql_f : inc q l = false := by
      cases h : inc q l; rfl
      exact (hlnotB (Finset.mem_filter.mpr ⟨hlM, h⟩)).elim
    have hl_notY : l ∉ ({l0, l1} : Finset (Fin 13)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro h; rw [h, hq0] at hql_f; cases hql_f
      · intro h; rw [h, hq1] at hql_f; cases hql_f
    refine ⟨l, hl_notY, (Finset.mem_filter.mp hlM).2, fun p => ?_⟩
    by_contra hgt
    push Not at hgt
    have h3 : (insert l ({l0, l1} : Finset (Fin 13))).card = 3 := by
      rw [Finset.card_insert_of_notMem hl_notY, Finset.card_insert_of_notMem (by simp [h01]), Finset.card_singleton]
    have hall : (insert l ({l0, l1} : Finset (Fin 13))).filter (fun m => p ∈ singerLines3 m) =
        insert l ({l0, l1} : Finset (Fin 13)) :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h3]; omega)
    have hmem_all : ∀ m ∈ insert l ({l0, l1} : Finset (Fin 13)), p ∈ singerLines3 m := by
      intro m hm
      rw [← hall, Finset.mem_filter] at hm
      exact hm.2
    have hp0 : inc p l0 = true := (mem_singerLines3_iff p l0).mp (hmem_all l0 (by simp))
    have hp1 : inc p l1 = true := (mem_singerLines3_iff p l1).mp (hmem_all l1 (by simp))
    have hpl : inc p l = true := (mem_singerLines3_iff p l).mp (hmem_all l (by simp))
    have hpq : p = q := hquniq p hp0 hp1
    rw [hpq, hql_f] at hpl; cases hpl
  · omega

private lemma tri_lines_comp_isQuadrangle (Y : Finset (Fin 13))
    (hY3 : Y.card = 3) (hdual : ∀ p : Fin 13, {l ∈ Y | p ∈ singerLines3 l}.card ≤ 2) :
    IsQuadrangle singerLines3 (Finset.univ.filter fun p : Fin 13 => ∀ l ∈ Y, inc p l = false) := by
  obtain ⟨l0, l1, l2, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp hY3
  let m1 := l1 - l0; let m2 := l2 - l0
  have hm1 : (m1 == 0) = false := beq_false_of_ne (fun h => h01 (sub_eq_zero.mp h).symm)
  have hm2 : (m2 == 0) = false := beq_false_of_ne (fun h => h02 (sub_eq_zero.mp h).symm)
  have hm12 : (m1 == m2) = false := beq_false_of_ne (fun h => h12 (by have := congrArg (· + l0) h; simpa [m1, m2] using this))
  have hnc : ((List.finRange 13).any fun p => inc p 0 && inc p m1 && inc p m2) = false := by
    cases hc : (List.finRange 13).any fun p => inc p 0 && inc p m1 && inc p m2
    · rfl
    · exfalso
      obtain ⟨p, _, hp⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true] at hp
      have hsub : ({l0, l1, l2} : Finset (Fin 13)) ⊆ {l ∈ ({l0, l1, l2} : Finset (Fin 13)) | p + l0 ∈ singerLines3 l} := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        refine ⟨hl, ?_⟩
        rw [mem_singerLines3_iff]
        rcases hl with hl | hl | hl
        · rw [hl]; simpa using (inc_add p 0 l0).trans hp.1.1
        · rw [hl]; simpa [m1, sub_add_cancel] using (inc_add p m1 l0).trans hp.1.2
        · rw [hl]; simpa [m2, sub_add_cancel] using (inc_add p m2 l0).trans hp.2
      have h3 := Finset.card_le_card hsub
      rw [hY3] at h3
      have := hdual (p + l0)
      omega
  have hd := List.all_eq_true.mp (List.all_eq_true.mp tri_lines_comp_quad_decide m1 (List.mem_finRange _)) m2 (List.mem_finRange _)
  simp only [hm1, hm2, hm12, hnc, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hd
  rcases hd with ⟨hQlen, hQdeg⟩
  have hQeq : (Finset.univ.filter fun p : Fin 13 => ∀ l ∈ ({l0, l1, l2} : Finset (Fin 13)), inc p l = false) =
      (Finset.univ.filter fun p : Fin 13 => (!inc p 0 && !inc p m1 && !inc p m2) = true).image (· + l0) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · intro h
      refine ⟨p - l0, ⟨⟨?_, ?_⟩, ?_⟩, sub_add_cancel p l0⟩
      · have h0 := h l0 (Or.inl rfl)
        simpa [sub_add_cancel] using (inc_add (p - l0) 0 l0).symm.trans (by simpa [sub_add_cancel] using h0)
      · have h1 := h l1 (Or.inr (Or.inl rfl))
        simpa [m1, sub_add_cancel] using (inc_add (p - l0) m1 l0).symm.trans (by simpa [m1, sub_add_cancel] using h1)
      · have h2 := h l2 (Or.inr (Or.inr rfl))
        simpa [m2, sub_add_cancel] using (inc_add (p - l0) m2 l0).symm.trans (by simpa [m2, sub_add_cancel] using h2)
    · rintro ⟨p', ⟨⟨h0', h1'⟩, h2'⟩, rfl⟩ l hl
      rcases hl with hl | hl | hl
      · rw [hl]; simpa using (inc_add p' 0 l0).trans h0'
      · rw [hl]; simpa [m1, sub_add_cancel] using (inc_add p' m1 l0).trans h1'
      · rw [hl]; simpa [m2, sub_add_cancel] using (inc_add p' m2 l0).trans h2'
  constructor
  · rw [hQeq, Finset.card_image_of_injective _ (add_left_injective l0), card_filter_eq_length]
    exact hQlen
  · intro l
    have hinter : ((Finset.univ.filter fun p : Fin 13 => ∀ m ∈ ({l0, l1, l2} : Finset (Fin 13)), inc p m = false) ∩
        singerLines3 l) =
      (Finset.univ.filter fun p : Fin 13 =>
        ((!inc p 0 && !inc p m1 && !inc p m2) && inc p (l - l0)) = true).image (· + l0) := by
      rw [hQeq]
      ext p
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨p', hp', rfl⟩, hpl⟩
        refine ⟨p', ⟨hp', ?_⟩, rfl⟩
        rw [mem_singerLines3_iff, inc_sub_cancel] at hpl
        exact hpl
      · rintro ⟨p', ⟨hp', hpl⟩, rfl⟩
        refine ⟨⟨p', hp', rfl⟩, ?_⟩
        rw [mem_singerLines3_iff, inc_sub_cancel]
        exact hpl
    rw [hinter, Finset.card_image_of_injective _ (add_left_injective l0), card_filter_eq_length]
    have hfl : ((List.finRange 13).filter fun p => (!inc p 0 && !inc p m1 && !inc p m2) && inc p (l - l0)) =
        (((List.finRange 13).filter fun p => !inc p 0 && !inc p m1 && !inc p m2).filter fun p => inc p (l - l0)) := by
      rw [List.filter_filter]; congr 1; funext p; exact Bool.and_comm _ _
    rw [hfl]
    exact hQdeg (l - l0) (List.mem_finRange _)

private lemma extend_to_quadrangle (X Y : Finset (Fin 13))
    (harc : ∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2)
    (hY3 : Y.card ≤ 3)
    (hdual : ∀ p : Fin 13, {l ∈ Y | p ∈ singerLines3 l}.card ≤ 2)
    (hni : ∀ p ∈ X, ∀ l ∈ Y, inc p l = false) :
    ∃ Q : Finset (Fin 13),
      IsQuadrangle singerLines3 Q ∧ X ⊆ Q ∧ Y ⊆ missLines singerLines3 Q := by
  have hX4 : X.card ≤ 4 := arc_card_le_four X harc
  by_cases hXeq4 : X.card = 4
  · refine ⟨X, ⟨hXeq4, harc⟩, Finset.Subset.refl X, ?_⟩
    intro l hlY
    simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
    intro p hpX hpl
    have := hni p hpX l hlY
    rw [(mem_singerLines3_iff p l).mp hpl] at this; cases this
  · have hX3 : X.card ≤ 3 := by omega
    have hextY : ∀ k, ∀ Y' : Finset (Fin 13), Y'.card + k = 3 →
        (∀ p : Fin 13, {l ∈ Y' | p ∈ singerLines3 l}.card ≤ 2) →
        (∀ p ∈ X, ∀ l ∈ Y', inc p l = false) →
        ∃ Y'' : Finset (Fin 13), Y' ⊆ Y'' ∧ Y''.card = 3 ∧
          (∀ p : Fin 13, {l ∈ Y'' | p ∈ singerLines3 l}.card ≤ 2) ∧
          (∀ p ∈ X, ∀ l ∈ Y'', inc p l = false) := by
      intro k
      induction k with
      | zero =>
        intro Y' hk hd hn
        exact ⟨Y', Finset.Subset.refl _, by omega, hd, hn⟩
      | succ k ih =>
        intro Y' hk hd hn
        obtain ⟨l, hlnot, hlm, hld⟩ := step_add_line X Y' hX3 harc (by omega) hn
        have hni' : ∀ p ∈ X, ∀ m ∈ insert l Y', inc p m = false := by
          intro p hp m hm
          rcases Finset.mem_insert.mp hm with rfl | hmY
          · exact hlm p hp
          · exact hn p hp m hmY
        have hcard' : (insert l Y').card + k = 3 := by
          rw [Finset.card_insert_of_notMem hlnot]; omega
        obtain ⟨Y'', hsub, h3, hd'', hn''⟩ := ih (insert l Y') hcard' hld hni'
        exact ⟨Y'', Finset.Subset.trans (Finset.subset_insert l Y') hsub, h3, hd'', hn''⟩
    obtain ⟨Y'', hYsub, hY''3, hd'', hn''⟩ := hextY (3 - Y.card) Y (by omega) hdual hni
    let Q : Finset (Fin 13) := Finset.univ.filter fun p : Fin 13 => ∀ l ∈ Y'', inc p l = false
    refine ⟨Q, tri_lines_comp_isQuadrangle Y'' hY''3 hd'', ?_, ?_⟩
    · intro p hpX
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl => hn'' p hpX l hl⟩
    · intro l hlY
      simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
      intro p hpQ hpl
      have := (Finset.mem_filter.mp hpQ).2 l (hYsub hlY)
      rw [(mem_singerLines3_iff p l).mp hpl] at this; cases this

/-! ## Section 6: Main Equivalence -/

private lemma main_iff (C : Circuit) (hmono : Monotone2 C) :
    (RightOnIncidentPairs singerLines3 C ∧
      ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
        C.eval (incidenceInput Q (missLines singerLines3 Q)) = Bool.false) ↔
    ∀ X Y : Finset (Fin 13),
      (∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2) →
      Y.card ≤ 3 →
      (∀ p : Fin 13, {l ∈ Y | p ∈ singerLines3 l}.card ≤ 2) →
      C.eval (incidenceInput X Y) = incidenceFun singerLines3 X Y := by
  constructor
  · rintro ⟨hinc, hquad⟩ X Y harc hY3 hdual
    cases hf : incidenceFun singerLines3 X Y
    · -- False input: extend to quadrangle Q!
      have hni : ∀ p ∈ X, ∀ l ∈ Y, inc p l = false := by
        intro p hp l hl
        cases h : inc p l
        · rfl
        · exfalso
          have htr : incidenceFun singerLines3 X Y = true :=
            decide_eq_true ⟨p, hp, l, hl, (mem_singerLines3_iff p l).mpr h⟩
          rw [htr] at hf; cases hf
      obtain ⟨Q, hQ, hXQ, hYQ⟩ := extend_to_quadrangle X Y harc hY3 hdual hni
      cases hc : C.eval (incidenceInput X Y)
      · rfl
      · exfalso
        have htr := eval_incidenceInput_mono C hmono hXQ hYQ hc
        rw [hquad Q hQ] at htr; cases htr
    · -- True input: contains an incident pair (p, l)!
      unfold incidenceFun at hf
      rw [decide_eq_true_eq] at hf
      rcases hf with ⟨p, hpX, l, hlY, hpl⟩
      have h1 : C.eval (incidenceInput {p} {l}) = true := hinc l p hpl
      exact eval_incidenceInput_mono C hmono (Finset.singleton_subset_iff.mpr hpX)
        (Finset.singleton_subset_iff.mpr hlY) h1
  · intro hall
    constructor
    · intro l p hpl
      have h1 : ∀ m : Fin 13, (({p} : Finset (Fin 13)) ∩ singerLines3 m).card ≤ 2 := by
        intro m
        have := Finset.card_le_card (Finset.inter_subset_left (s₁ := {p}) (s₂ := singerLines3 m))
        simp at this; omega
      have h2 : ({l} : Finset (Fin 13)).card ≤ 3 := by simp
      have h3 : ∀ q : Fin 13, {m ∈ ({l} : Finset (Fin 13)) | q ∈ singerLines3 m}.card ≤ 2 := by
        intro q
        have := Finset.card_le_card (Finset.filter_subset (fun m => q ∈ singerLines3 m) {l})
        simp at this; omega
      rw [hall {p} {l} h1 h2 h3]
      exact decide_eq_true ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hpl⟩
    · intro Q hQ
      obtain ⟨hm3, hmd⟩ := quad_missLines_props Q hQ
      rw [hall Q (missLines singerLines3 Q) hQ.2 hm3 hmd]
      unfold incidenceFun
      rw [decide_eq_false_iff_not]
      rintro ⟨p, hpQ, l, hlM, hpl⟩
      have hdisj := (Finset.mem_filter.mp hlM).2
      exact Finset.disjoint_right.mp hdisj hpQ hpl

end PEqualNP.Outside.L_meta_6270_aux

theorem PEqualNP.Outside.L_meta_6270 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ((PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = Bool.false) ↔ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) :=
  PEqualNP.Outside.L_meta_6270_aux.main_iff
