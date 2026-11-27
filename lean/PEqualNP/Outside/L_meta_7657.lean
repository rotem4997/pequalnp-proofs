import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

private lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

private lemma W_append (a b : List Gate) (w : List Bool) :
    W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma W_length (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

private lemma getD_append_lt (l₁ l₂ : List Bool) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_append_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

private lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma W_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_append_lt w _ i hi

private lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false :=
  getD_ge _ _ (by rw [W_length]; exact h)

private lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  have htlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hprelen : (W (gs.take j) w).length = w.length + j := by
    rw [W_length, htlen]
  conv_lhs => rw [hsplit, W_append, W_cons]
  rw [W_prefix (gs.drop (j + 1)) (step (W (gs.take j) w) gs[j]) (w.length + j)
    (by rw [step_len, hprelen]; omega)]
  have hlast : (step (W (gs.take j) w) gs[j]).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (W (gs.take j) w).getD i false) := by
    rw [← hprelen]
    exact getD_append_len _ _
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + j
  · simp only [hi, ↓reduceIte]
    have hpref : (W gs w).getD i false = (W (gs.take j) w).getD i false := by
      conv_lhs => rw [hsplit, W_append]
      exact W_prefix (gs[j] :: gs.drop (j + 1)) (W (gs.take j) w) i (by rw [hprelen]; exact hi)
    exact hpref.symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge (W (gs.take j) w) i (by rw [hprelen]; omega)

private lemma val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false :=
  W_prefix C.gates x i hi

private lemma val_ge (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    val C x i = false :=
  W_ge C.gates x i hi

private lemma val_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (x.length + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then val C x i else false) :=
  W_gate C.gates x j hj

private lemma gate_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {w₁ w₂ : List Bool} (hw : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hw i (h _ ⟨i, hi, rfl⟩)
  · simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hw i hb⟩

private lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (hw : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₁).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₂).getD i false = true := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [hlen]
    · intro i
      by_cases hi : i < w₁.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
        exact hw i
      · have hge := Nat.le_of_not_gt hi
        rw [List.getD_append_right _ _ _ _ hge,
          List.getD_append_right _ _ _ _ (hlen ▸ hge), ← hlen]
        cases i - w₁.length with
        | zero => exact gate_mono g (hgs g (List.mem_cons_self ..)) hw
        | succ k => simp


private lemma mono_wires (C : Circuit) (hC : Monotone2 C)
    {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hxy : ∀ i, xs.getD i false = true → ys.getD i false = true) (i : ℕ) :
    val C xs i = true → val C ys i = true :=
  fold_mono C.gates (fun g hg => by simpa using (hC g hg).1) xs ys hlen hxy i

private lemma getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : Fin m) :
    (List.ofFn f).getD i false = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private lemma mono_ofFn {m : ℕ} {f g : Fin m → Bool}
    (h : ∀ i, f i = true → g i = true) (i : ℕ) :
    (List.ofFn f).getD i false = true → (List.ofFn g).getD i false = true := by
  by_cases hi : i < m
  · simpa only [getD_ofFn f (⟨i, hi⟩ : Fin m), getD_ofFn g (⟨i, hi⟩ : Fin m)]
      using h ⟨i, hi⟩
  · rw [getD_ge _ _ (by simpa using Nat.le_of_not_gt hi)]
    simp

private lemma replicate_false (m i : ℕ) :
    (List.replicate m false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

private lemma first_change (C : Circuit) (hC : Monotone2 C)
    {m : ℕ} {f g : Fin m → Bool} {a : Fin m}
    (hm : ∀ i, f i = true → g i = true) (ha : ∀ i ≠ a, f i = g i)
    (hne : C.output ≠ a.val)
    (hf : C.eval (List.ofFn f) = false) (hg : C.eval (List.ofFn g) = true) :
    ∃ j : Fin C.size, a.val ∈ (C.gates.get j).inputs ∧
      val C (List.replicate m false) (m + j.val) = false ∧
      val C (List.ofFn g) (m + j.val) = true := by
  let xs := List.ofFn f
  let ys := List.ofFn g
  change val C xs C.output = false at hf
  change val C ys C.output = true at hg
  have hxl : xs.length = m := List.length_ofFn
  have hyl : ys.length = m := List.length_ofFn
  have hmono := mono_wires C hC (hxl.trans hyl.symm) (mono_ofFn hm)
  have hin (i : ℕ) (hi : i < m) (hn : i ≠ a.val) : val C xs i = val C ys i := by
    rw [val_input C xs i (by rwa [hxl]), val_input C ys i (by rwa [hyl])]
    let k : Fin m := ⟨i, hi⟩
    change (List.ofFn f).getD k false = (List.ofFn g).getD k false
    rw [getD_ofFn, getD_ofFn]
    exact ha k (fun he => hn (congrArg Fin.val he))
  have hex : ∃ j : ℕ, j < C.gates.length ∧
      val C xs (m + j) = false ∧ val C ys (m + j) = true := by
    have hlo : m ≤ C.output := by
      by_contra! h
      rw [hin C.output h hne, hg] at hf
      contradiction
    have hhi : C.output < m + C.gates.length := by
      by_contra! h
      rw [val_ge C ys C.output (by simpa only [hyl] using h)] at hg
      contradiction
    refine ⟨C.output - m, by omega, ?_⟩
    rw [Nat.add_sub_of_le hlo]
    exact ⟨hf, hg⟩
  classical
  -- Every earlier wire other than the changed input agrees on the two runs.
  let j := Nat.find hex
  obtain ⟨hj, hxf, hyt⟩ := Nat.find_spec hex
  have earlier (i : ℕ) (hi : i < m + j) (hn : i ≠ a.val) :
      val C xs i = val C ys i := by
    by_cases h : i < m
    · exact hin i h hn
    have he : m + (i - m) = i := Nat.add_sub_of_le (by omega)
    by_contra hne'
    have hd : val C xs i = false ∧ val C ys i = true := by
      have hh := hmono i
      cases hx : val C xs i <;> cases hy : val C ys i <;>
        simp [hx, hy] at hh hne' ⊢
    exact Nat.find_min hex (show i - m < j by omega)
      ⟨by omega, by rwa [he]⟩
  have hreads : a.val ∈ C.gates[j].inputs := by
    by_contra habs
    have he : val C xs (m + j) = val C ys (m + j) := by
      have hx := val_gate C xs j hj
      have hy := val_gate C ys j hj
      rw [hxl] at hx
      rw [hyl] at hy
      rw [hx, hy]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases h : i < m + j
      · have hne' : i ≠ a.val := fun he => habs (he ▸ hi)
        simp only [h, ↓reduceIte, earlier i h hne']
      · simp only [h, ↓reduceIte]
    change val C xs (m + j) = false at hxf
    change val C ys (m + j) = true at hyt
    rw [hxf, hyt] at he
    contradiction
  refine ⟨⟨j, hj⟩, hreads, ?_, hyt⟩
  cases hb : val C (List.replicate m false) (m + j) with
  | false => rfl
  | true =>
    have hb' := mono_wires C hC (ys := xs) (by simp [hxl])
      (fun i h => by rw [replicate_false] at h; contradiction) (m + j) hb
    rw [hxf] at hb'
    contradiction

private def single {m : ℕ} (a : Fin m) (i : Fin m) : Bool := decide (i = a)

private lemma single_false (C : Circuit) (hC : Monotone2 C) {m : ℕ}
    (a : Fin m) (z : Fin m → Bool) (hz : z a = true)
    (h : C.eval (List.ofFn z) = false) :
    C.eval (List.ofFn (single a)) = false := by
  have hle (i : Fin m) (hi : single a i = true) : z i = true := by
    have he : i = a := of_decide_eq_true hi
    subst i
    exact hz
  cases he : C.eval (List.ofFn (single a)) with
  | false => rfl
  | true =>
    have hh := mono_wires C hC (by simp) (mono_ofFn hle) C.output he
    change val C (List.ofFn z) C.output = false at h
    rw [h] at hh
    contradiction

private lemma pair_change (C : Circuit) (hC : Monotone2 C) {m : ℕ}
    (a b : Fin m) (g : Fin m → Bool) (hpair : ∀ i, g i = true ↔ i = a ∨ i = b)
    (hsa : C.eval (List.ofFn (single a)) = false)
    (hsb : C.eval (List.ofFn (single b)) = false)
    (hg : C.eval (List.ofFn g) = true) :
    ∃ j : Fin C.size, a.val ∈ (C.gates.get j).inputs ∧
      val C (List.replicate m false) (m + j.val) = false ∧
      val C (List.ofFn g) (m + j.val) = true := by
  apply first_change C hC (f := single b) (g := g) (a := a) _ _ _ hsb hg
  · intro i hi
    exact (hpair i).2 (Or.inr (of_decide_eq_true hi))
  · intro i hi
    have he : single b i = true ↔ g i = true := by simp [single, hpair, hi]
    cases hb : single b i <;> cases hgi : g i <;> simp [hb, hgi] at he ⊢
  · intro he
    change val C (List.ofFn (single a)) C.output = false at hsa
    rw [he, val_input C _ _ (by simp), getD_ofFn] at hsa
    simp [single] at hsa

private lemma count_inputs {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (lines : Fin n → Finset (Fin n))
    (pair : Fin n → Fin n → Fin (n + n) → Bool)
    (hp : ∀ p l i, pair p l i = true ↔ i = Fin.castAdd n p ∨ i = Fin.natAdd n l)
    (hs : ∀ i : Fin (n + n), C.eval (List.ofFn (single i)) = false)
    (he : ∀ l p, p ∈ lines l → C.eval (List.ofFn (pair p l)) = true) :
    (Finset.univ.biUnion lines).card + Fintype.card {l : Fin n // (lines l).Nonempty} ≤
      2 * Fintype.card {j : Fin C.size //
        val C (List.replicate (n + n) false) (n + n + j.val) = false ∧
          ∃ l, ∃ p ∈ lines l, val C (List.ofFn (pair p l)) (n + n + j.val) = true} := by
  classical
  let active := Finset.univ.filter (fun j : Fin C.size =>
    val C (List.replicate (n + n) false) (n + n + j.val) = false ∧
      ∃ l, ∃ p ∈ lines l, val C (List.ofFn (pair p l)) (n + n + j.val) = true)
  let inputSet (j : Fin C.size) := (C.gates.get j).inputs.toFinset
  let points := (Finset.univ.biUnion lines).image Fin.val
  let nonemptyLines := Finset.univ.filter (fun l : Fin n => (lines l).Nonempty)
  let shifted := nonemptyLines.image (fun l => n + l.val)
  -- Each participating point or line is an input of an active gate.
  have hcover : points ∪ shifted ⊆ active.biUnion inputSet := by
    intro i hi
    rcases Finset.mem_union.mp hi with hip | hil
    · obtain ⟨p, hp', rfl⟩ := Finset.mem_image.mp hip
      obtain ⟨l, _, hpl⟩ := Finset.mem_biUnion.mp hp'
      obtain ⟨j, hj, hz, ht⟩ := pair_change C hC (Fin.castAdd n p) (Fin.natAdd n l)
        (pair p l) (hp p l) (hs _) (hs _) (he l p hpl)
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, l, p, hpl, ht⟩,
        List.mem_toFinset.mpr hj⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hil
      obtain ⟨p, hpl⟩ := (Finset.mem_filter.mp hl).2
      obtain ⟨j, hj, hz, ht⟩ := pair_change C hC (Fin.natAdd n l) (Fin.castAdd n p)
        (pair p l) (fun i => (hp p l i).trans or_comm) (hs _) (hs _) (he l p hpl)
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, l, p, hpl, ht⟩,
        List.mem_toFinset.mpr hj⟩
  have hd : Disjoint points shifted := by
    refine Finset.disjoint_left.mpr fun i hip hil => ?_
    obtain ⟨p, _, hpi⟩ := Finset.mem_image.mp hip
    obtain ⟨l, _, hli⟩ := Finset.mem_image.mp hil
    have := p.isLt
    omega
  have hleft : (points ∪ shifted).card =
      (Finset.univ.biUnion lines).card + Fintype.card {l : Fin n // (lines l).Nonempty} := by
    rw [Finset.card_union_of_disjoint hd]
    change ((Finset.univ.biUnion lines).image Fin.val).card +
      (nonemptyLines.image (fun l => n + l.val)).card = _
    rw [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
    congr 1
    exact (Fintype.card_of_subtype nonemptyLines (by simp [nonemptyLines])).symm
  have hright : Fintype.card {j : Fin C.size //
        val C (List.replicate (n + n) false) (n + n + j.val) = false ∧
          ∃ l, ∃ p ∈ lines l, val C (List.ofFn (pair p l)) (n + n + j.val) = true} =
      active.card :=
    Fintype.card_of_subtype active (by simp [active])
  rw [← hleft, hright, Nat.mul_comm]
  refine (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul active inputSet 2 ?_)
  intro j _
  exact (List.toFinset_card_le _).trans (hC _ (List.get_mem _ _)).2

end PEqualNP.Outside.L_meta_7657

theorem PEqualNP.Outside.L_meta_7657 :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1 → Finset (Fin x1)),   have x7 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x7 : Finset (Fin x1)) (x8 : Fin (x1 + x1)) => Fin.addCases (fun (x9 : Fin x1) => Decidable.decide ¬∃ x10 ∈ x7, x2 x9 x10) (fun (x9 : Fin x1) => Decidable.decide (x9 ∈ x7)) x8;   have x8 : Fin x1 → Fin x1 → Fin (x1 + x1) → Bool := fun (x8 x9 : Fin x1) (x10 : Fin (x1 + x1)) => Decidable.decide (x10 = Fin.castAdd x1 x8 ∨ x10 = Fin.natAdd x1 x9);   x4.output = x5.output → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → x4.eval (List.ofFn (x7 x11)) = Bool.false) → (∀ (x12 x13 : Fin x1), x13 ∈ x6 x12 → x4.eval (List.ofFn (x8 x13 x12)) = Bool.true ∧ x5.eval (List.ofFn (x8 x13 x12)) = Bool.false) → (Finset.univ.biUnion x6).card + Fintype.card { x13 : Fin x1 // (x6 x13).Nonempty } ≤ (2 : ℕ) * Fintype.card { x13 : Fin x4.size // (x4.wires (List.replicate (x1 + x1) Bool.false)).getD (x1 + x1 + ↑x13) Bool.false = Bool.false ∧ ∃ (x14 : Fin x1), ∃ x15 ∈ x6 x14, (x4.wires (List.ofFn (x8 x15 x14))).getD (x1 + x1 + ↑x13) Bool.false = Bool.true } := by
  intro n R _ C D lines
  dsimp only
  intro _ hC hsmall hpair
  open PEqualNP.Outside.L_meta_7657 in
  refine count_inputs C hC lines
    (fun p l i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) ?_ ?_ ?_
  · intro p l i
    simp only [decide_eq_true_eq]
  · intro i
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · refine single_false C hC (Fin.castAdd n p) _ ?_ (hsmall ∅ (by simp))
      rw [Fin.addCases_left]
      simp
    · refine single_false C hC (Fin.natAdd n l) _ ?_ (hsmall {l} (by simp))
      rw [Fin.addCases_right]
      simp
  · exact fun l p hp => (hpair l p hp).1
