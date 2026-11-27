import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3763_aux

private def evalStep (ws : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  let va := ws.getD g.2.1 false
  let vb := ws.getD g.2.2 false
  ws ++ [if g.1 then (va || vb) else (va && vb)]

private def evalWiresFrom (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (z : ℕ → Bool) : List Bool :=
  gs.foldl evalStep (List.ofFn (fun i : Fin n => z i.val))

private def wireVal (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) (z : ℕ → Bool) : Bool :=
  (evalWiresFrom n gs z).getD w false

private def Wf (n : ℕ) (gs : List (Bool × ℕ × ℕ)) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), gs[j].2.1 < n + j ∧ gs[j].2.2 < n + j

private lemma foldl_len (gs : List (Bool × ℕ × ℕ)) (init : List Bool) :
    (gs.foldl evalStep init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [evalStep]; omega

private lemma evalWiresFrom_length (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (z : ℕ → Bool) :
    (evalWiresFrom n gs z).length = n + gs.length := by
  unfold evalWiresFrom
  rw [foldl_len, List.length_ofFn]

private lemma foldl_prefix (gs : List (Bool × ℕ × ℕ)) (init : List Bool) (w : ℕ) (hw : w < init.length) :
    (gs.foldl evalStep init).getD w false = init.getD w false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hw' : w < (evalStep init g).length := by simp [evalStep]; omega
    rw [ih _ hw']
    simp [evalStep, List.getD, List.getElem?_append_left hw]

private lemma wireVal_input {n : ℕ} {gs : List (Bool × ℕ × ℕ)} {w : ℕ} (hw : w < n) (z : ℕ → Bool) :
    wireVal n gs w z = z w := by
  unfold wireVal evalWiresFrom
  rw [foldl_prefix _ _ w (by simp [hw])]
  simp [List.getD, hw]

private lemma foldl_snoc (gs : List (Bool × ℕ × ℕ)) (g : Bool × ℕ × ℕ) (init : List Bool) :
    ((gs ++ [g]).foldl evalStep init) = evalStep (gs.foldl evalStep init) g := by
  simp [List.foldl_append]

private lemma wireVal_gate {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {j : ℕ} (hj : j < gs.length) (z : ℕ → Bool) :
    wireVal n gs (n + j) z =
      if gs[j].1 then (wireVal n gs gs[j].2.1 z || wireVal n gs gs[j].2.2 z)
      else (wireVal n gs gs[j].2.1 z && wireVal n gs gs[j].2.2 z) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    rw [List.append_assoc]
    exact h1.symm
  have hlenTake : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  unfold wireVal evalWiresFrom
  conv_lhs => rw [hsplit]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set ws0 := (gs.take j).foldl evalStep (List.ofFn (fun i : Fin n => z i.val))
  have hlen0 : ws0.length = n + j := by
    dsimp only [ws0]
    rw [foldl_len, List.length_ofFn, hlenTake]
  have hlen1 : (evalStep ws0 gs[j]).length = n + j + 1 := by
    simp [evalStep, hlen0]
  rw [foldl_prefix _ _ (n + j) (by omega)]
  have hget : (evalStep ws0 gs[j]).getD (n + j) false =
      if gs[j].1 then (ws0.getD gs[j].2.1 false || ws0.getD gs[j].2.2 false)
      else (ws0.getD gs[j].2.1 false && ws0.getD gs[j].2.2 false) := by
    simp [evalStep, List.getD, hlen0]
  rw [hget]
  have hpref : ∀ u < n + j, (gs.foldl evalStep (List.ofFn (fun i : Fin n => z i.val))).getD u false = ws0.getD u false := by
    intro u hu
    conv_lhs => rw [hsplit]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [foldl_prefix _ _ u (by change u < (evalStep ws0 gs[j]).length; omega)]
    change (evalStep ws0 gs[j]).getD u false = ws0.getD u false
    simp [evalStep, List.getD, List.getElem?_append_left (by omega : u < ws0.length)]
  have hwfj := hwf j hj
  rw [hpref gs[j].2.1 hwfj.1, hpref gs[j].2.2 hwfj.2]

private lemma wireVal_mono {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {z1 z2 : ℕ → Bool} (hle : ∀ i < n, z1 i = true → z2 i = true) :
    ∀ w < n + gs.length, wireVal n gs w z1 = true → wireVal n gs w z2 = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h1
    by_cases hlt : w < n
    · rw [wireVal_input hlt] at h1 ⊢
      exact hle w hlt h1
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < gs.length := by omega
      rw [hwj] at h1 ⊢
      rw [wireVal_gate hwf hj] at h1 ⊢
      have hwfj := hwf j hj
      cases hop : gs[j].1 <;> simp only [hop, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at h1 ⊢
      · exact ⟨ih _ (by omega) (by omega) h1.1, ih _ (by omega) (by omega) h1.2⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (ih _ (by omega) (by omega) h1)
        · exact Or.inr (ih _ (by omega) (by omega) h1)

private lemma wireVal_zero {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs) :
    ∀ w < n + gs.length, wireVal n gs w (fun _ => false) = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wireVal_input hlt]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < gs.length := by omega
      rw [hwj, wireVal_gate hwf hj]
      have hwfj := hwf j hj
      rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      cases gs[j].1 <;> rfl

-- Conversion from Set-of-Finsets circuit S to a pure AND/OR circuit
private lemma set_to_circuit {n m : ℕ} {S : ℕ → Set (Finset ℕ)}
    (hinit : ∀ i < n, S i = {{i}})
    (hstep : ∀ j < m, ∃ a < n + j, ∃ b < n + j,
      S (n + j) = Set.image2 (fun x y => x ∪ y) (S a) (S b) ∨
      S (n + j) = S a ∨
      S (n + j) = {∅} ∨
      S (n + j) = S a ∪ S b) :
    ∀ k ≤ m, ∃ (gs : List (Bool × ℕ × ℕ)) (env : ℕ → Option ℕ),
      gs.length ≤ k ∧ Wf n gs ∧
      (∀ w < n + k, match env w with
        | none => ∀ z : ℕ → Bool, ∃ M ∈ S w, ∀ u ∈ M, z u = false
        | some idx => idx < n + gs.length ∧
            ∀ z : ℕ → Bool, wireVal n gs idx z = false ↔ ∃ M ∈ S w, ∀ u ∈ M, z u = false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, le_rfl, fun j hj => by simp at hj, ?_⟩
    intro w hw
    have hw' : w < n := by omega
    refine ⟨by simpa using hw', fun z => ?_⟩
    rw [wireVal_input hw', hinit w hw']
    simp
  | succ k ih =>
    intro hkm
    obtain ⟨gs, env, hlen, hwf, henv⟩ := ih (Nat.le_of_lt hkm)
    obtain ⟨a, ha, b, hb, hcases⟩ := hstep k (Nat.lt_of_succ_le hkm)
    have hpref_val : ∀ (g : Bool × ℕ × ℕ) (idx : ℕ), idx < n + gs.length → ∀ z,
        wireVal n (gs ++ [g]) idx z = wireVal n gs idx z := by
      intro g idx hidx z
      unfold wireVal evalWiresFrom
      rw [foldl_snoc]
      have hlen_ws : (gs.foldl evalStep (List.ofFn (fun i : Fin n => z i.val))).length = n + gs.length := by
        rw [foldl_len, List.length_ofFn]
      simp [evalStep, List.getD, List.getElem?_append_left (by omega : idx < (gs.foldl evalStep (List.ofFn (fun i : Fin n => z i.val))).length)]
    have hwf_snoc : ∀ (g : Bool × ℕ × ℕ), g.2.1 < n + gs.length → g.2.2 < n + gs.length →
        Wf n (gs ++ [g]) := by
      intro g hg1 hg2 j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt]; exact hwf j hlt
      · have hjeq : j = gs.length := by omega
        subst hjeq
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        exact ⟨hg1, hg2⟩
    rcases hcases with hOr | hCopy | hEmpty | hAnd
    · -- image2 (∪) -> OR gate
      cases hea : env a with
      | none =>
        have ha_spec := henv a ha; rw [hea] at ha_spec
        refine ⟨gs, fun w => if w = n + k then env b else env w, by omega, hwf, ?_⟩
        intro w hw
        by_cases hwk : w = n + k
        · subst hwk
          simp only [↓reduceIte]
          have hb_spec := henv b hb
          cases heb : env b with
          | none =>
            rw [heb] at hb_spec
            intro z
            obtain ⟨M1, hM1, hz1⟩ := ha_spec z
            obtain ⟨M2, hM2, hz2⟩ := hb_spec z
            refine ⟨M1 ∪ M2, ?_, fun u hu => by
              simp only [Finset.mem_union] at hu
              rcases hu with hu | hu
              · exact hz1 u hu
              · exact hz2 u hu⟩
            rw [hOr]; exact Set.mem_image2_of_mem hM1 hM2
          | some ib =>
            rw [heb] at hb_spec
            refine ⟨hb_spec.1, fun z => ?_⟩
            rw [hb_spec.2 z, hOr]
            constructor
            · rintro ⟨M2, hM2, hz2⟩
              obtain ⟨M1, hM1, hz1⟩ := ha_spec z
              refine ⟨M1 ∪ M2, Set.mem_image2_of_mem hM1 hM2, fun u hu => ?_⟩
              simp only [Finset.mem_union] at hu
              rcases hu with hu | hu
              · exact hz1 u hu
              · exact hz2 u hu
            · rintro ⟨M, hM, hz⟩
              rcases Set.mem_image2.mp hM with ⟨M1, _, M2, hM2, rfl⟩
              exact ⟨M2, hM2, fun u hu => hz u (Finset.mem_union_right _ hu)⟩
        · simp only [hwk, ↓reduceIte]
          exact henv w (by omega)
      | some ia =>
        have ha_spec := henv a ha; rw [hea] at ha_spec
        cases heb : env b with
        | none =>
          have hb_spec := henv b hb; rw [heb] at hb_spec
          refine ⟨gs, fun w => if w = n + k then some ia else env w, by omega, hwf, ?_⟩
          intro w hw
          by_cases hwk : w = n + k
          · subst hwk
            simp only [↓reduceIte]
            refine ⟨ha_spec.1, fun z => ?_⟩
            rw [ha_spec.2 z, hOr]
            constructor
            · rintro ⟨M1, hM1, hz1⟩
              obtain ⟨M2, hM2, hz2⟩ := hb_spec z
              refine ⟨M1 ∪ M2, Set.mem_image2_of_mem hM1 hM2, fun u hu => ?_⟩
              simp only [Finset.mem_union] at hu
              rcases hu with hu | hu
              · exact hz1 u hu
              · exact hz2 u hu
            · rintro ⟨M, hM, hz⟩
              rcases Set.mem_image2.mp hM with ⟨M1, hM1, M2, _, rfl⟩
              exact ⟨M1, hM1, fun u hu => hz u (Finset.mem_union_left _ hu)⟩
          · simp only [hwk, ↓reduceIte]
            exact henv w (by omega)
        | some ib =>
          have hb_spec := henv b hb; rw [heb] at hb_spec
          let gnew : Bool × ℕ × ℕ := (true, ia, ib)
          have hwf' := hwf_snoc gnew ha_spec.1 hb_spec.1
          refine ⟨gs ++ [gnew], fun w => if w = n + k then some (n + gs.length) else env w,
            by simp; omega, hwf', ?_⟩
          intro w hw
          by_cases hwk : w = n + k
          · subst hwk
            simp only [↓reduceIte]
            refine ⟨by simp, fun z => ?_⟩
            have hglt : gs.length < (gs ++ [gnew]).length := by simp
            rw [wireVal_gate hwf' hglt z]
            have hge : (gs ++ [gnew])[gs.length]'hglt = gnew := by simp
            rw [hge]
            dsimp only [gnew]
            rw [hpref_val gnew ia ha_spec.1 z, hpref_val gnew ib hb_spec.1 z]
            simp only [↓reduceIte, Bool.or_eq_false_iff, ha_spec.2 z, hb_spec.2 z, hOr]
            constructor
            · rintro ⟨⟨M1, hM1, hz1⟩, ⟨M2, hM2, hz2⟩⟩
              refine ⟨M1 ∪ M2, Set.mem_image2_of_mem hM1 hM2, fun u hu => ?_⟩
              simp only [Finset.mem_union] at hu
              rcases hu with hu | hu
              · exact hz1 u hu
              · exact hz2 u hu
            · rintro ⟨M, hM, hz⟩
              rcases Set.mem_image2.mp hM with ⟨M1, hM1, M2, hM2, rfl⟩
              exact ⟨⟨M1, hM1, fun u hu => hz u (Finset.mem_union_left _ hu)⟩,
                     ⟨M2, hM2, fun u hu => hz u (Finset.mem_union_right _ hu)⟩⟩
          · simp only [hwk, ↓reduceIte]
            have hw_spec := henv w (by omega)
            cases hew : env w with
            | none => rw [hew] at hw_spec; exact hw_spec
            | some iw =>
              rw [hew] at hw_spec
              refine ⟨by simp; omega, fun z => ?_⟩
              rw [hpref_val gnew iw hw_spec.1 z]
              exact hw_spec.2 z
    · -- Copy gate: S (n + k) = S a
      refine ⟨gs, fun w => if w = n + k then env a else env w, by omega, hwf, ?_⟩
      intro w hw
      by_cases hwk : w = n + k
      · subst hwk; simp only [↓reduceIte]
        have ha_spec := henv a ha
        cases hea : env a with
        | none => rw [hea] at ha_spec; rw [hCopy]; exact ha_spec
        | some ia => rw [hea] at ha_spec; rw [hCopy]; exact ha_spec
      · simp only [hwk, ↓reduceIte]; exact henv w (by omega)
    · -- Empty gate: S (n + k) = {∅}
      refine ⟨gs, fun w => if w = n + k then none else env w, by omega, hwf, ?_⟩
      intro w hw
      by_cases hwk : w = n + k
      · subst hwk; simp only [↓reduceIte]
        intro z; exact ⟨∅, by rw [hEmpty]; exact Set.mem_singleton _, fun u hu => by simp at hu⟩
      · simp only [hwk, ↓reduceIte]; exact henv w (by omega)
    · -- Union gate: S (n + k) = S a ∪ S b -> AND gate
      cases hea : env a with
      | none =>
        have ha_spec := henv a ha; rw [hea] at ha_spec
        refine ⟨gs, fun w => if w = n + k then none else env w, by omega, hwf, ?_⟩
        intro w hw
        by_cases hwk : w = n + k
        · subst hwk; simp only [↓reduceIte]
          intro z; obtain ⟨M, hM, hz⟩ := ha_spec z
          exact ⟨M, by rw [hAnd]; exact Or.inl hM, hz⟩
        · simp only [hwk, ↓reduceIte]; exact henv w (by omega)
      | some ia =>
        have ha_spec := henv a ha; rw [hea] at ha_spec
        cases heb : env b with
        | none =>
          have hb_spec := henv b hb; rw [heb] at hb_spec
          refine ⟨gs, fun w => if w = n + k then none else env w, by omega, hwf, ?_⟩
          intro w hw
          by_cases hwk : w = n + k
          · subst hwk; simp only [↓reduceIte]
            intro z; obtain ⟨M, hM, hz⟩ := hb_spec z
            exact ⟨M, by rw [hAnd]; exact Or.inr hM, hz⟩
          · simp only [hwk, ↓reduceIte]; exact henv w (by omega)
        | some ib =>
          have hb_spec := henv b hb; rw [heb] at hb_spec
          let gnew : Bool × ℕ × ℕ := (false, ia, ib)
          have hwf' := hwf_snoc gnew ha_spec.1 hb_spec.1
          refine ⟨gs ++ [gnew], fun w => if w = n + k then some (n + gs.length) else env w,
            by simp; omega, hwf', ?_⟩
          intro w hw
          by_cases hwk : w = n + k
          · subst hwk; simp only [↓reduceIte]
            refine ⟨by simp, fun z => ?_⟩
            have hglt : gs.length < (gs ++ [gnew]).length := by simp
            rw [wireVal_gate hwf' hglt z]
            have hge : (gs ++ [gnew])[gs.length]'hglt = gnew := by simp
            rw [hge]; dsimp only [gnew]
            rw [hpref_val gnew ia ha_spec.1 z, hpref_val gnew ib hb_spec.1 z]
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_false_iff, ha_spec.2 z, hb_spec.2 z, hAnd]
            constructor
            · rintro (⟨M, hM, hz⟩ | ⟨M, hM, hz⟩)
              · exact ⟨M, Or.inl hM, hz⟩
              · exact ⟨M, Or.inr hM, hz⟩
            · rintro ⟨M, hM | hM, hz⟩
              · exact Or.inl ⟨M, hM, hz⟩
              · exact Or.inr ⟨M, hM, hz⟩
          · simp only [hwk, ↓reduceIte]
            have hw_spec := henv w (by omega)
            cases hew : env w with
            | none => rw [hew] at hw_spec; exact hw_spec
            | some iw =>
              rw [hew] at hw_spec
              refine ⟨by simp; omega, fun z => ?_⟩
              rw [hpref_val gnew iw hw_spec.1 z]
              exact hw_spec.2 z

-- Fanout of wire w in gs
private def fanout (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : ℕ :=
  ∑ j ∈ Finset.range gs.length,
    ((if (gs.getD j (false, 0, 0)).2.1 = w then 1 else 0) +
     (if (gs.getD j (false, 0, 0)).2.2 = w then 1 else 0))

private lemma sum_fanout_eq (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (hwf : Wf n gs) :
    ∑ w ∈ Finset.range (n + gs.length), fanout gs w = 2 * gs.length := by
  unfold fanout
  rw [Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range gs.length,
      (∑ w ∈ Finset.range (n + gs.length),
        ((if (gs.getD j (false, 0, 0)).2.1 = w then 1 else 0) +
         (if (gs.getD j (false, 0, 0)).2.2 = w then 1 else 0))) = 2 := by
    intro j hj
    have hjlt : j < gs.length := Finset.mem_range.mp hj
    have hget : gs.getD j (false, 0, 0) = gs[j] := by simp [List.getD, hjlt]
    rw [hget, Finset.sum_add_distrib]
    have hwfj := hwf j hjlt
    have h1 : gs[j].2.1 ∈ Finset.range (n + gs.length) := Finset.mem_range.mpr (by omega)
    have h2 : gs[j].2.2 ∈ Finset.range (n + gs.length) := Finset.mem_range.mpr (by omega)
    simp [Finset.sum_ite_eq, h1, h2]
  rw [Finset.sum_congr rfl hterm]
  simp; omega

-- Dead gate deletion
private def shiftIdx (cut w : ℕ) : ℕ :=
  if w < cut then w else w - 1

private def deleteGate (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (k : ℕ) : List (Bool × ℕ × ℕ) :=
  (gs.eraseIdx k).map (fun g => (g.1, shiftIdx (n + k) g.2.1, shiftIdx (n + k) g.2.2))

private lemma deleteGate_spec {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {out k : ℕ} (hout : out < n + gs.length) (hk : k < gs.length)
    (hne : out ≠ n + k) (hdead : fanout gs (n + k) = 0) :
    let gs' := deleteGate n gs k
    let out' := shiftIdx (n + k) out
    gs'.length = gs.length - 1 ∧
    Wf n gs' ∧
    out' < n + gs'.length ∧
    ∀ z : ℕ → Bool, wireVal n gs' out' z = wireVal n gs out z := by
  intro gs' out'
  have hlen : gs'.length = gs.length - 1 := by
    simp [gs', deleteGate, List.length_eraseIdx, hk]
  have hnoread : ∀ (j : ℕ) (hj : j < gs.length), gs[j].2.1 ≠ n + k ∧ gs[j].2.2 ≠ n + k := by
    intro j hj
    have hmem : j ∈ Finset.range gs.length := Finset.mem_range.mpr hj
    have hle : (if (gs.getD j (false, 0, 0)).2.1 = n + k then 1 else 0) +
        (if (gs.getD j (false, 0, 0)).2.2 = n + k then 1 else 0) ≤ fanout gs (n + k) :=
      Finset.single_le_sum (f := fun i =>
        (if (gs.getD i (false, 0, 0)).2.1 = n + k then 1 else 0) +
        (if (gs.getD i (false, 0, 0)).2.2 = n + k then 1 else 0))
        (fun _ _ => Nat.zero_le _) hmem
    have hget : gs.getD j (false, 0, 0) = gs[j] := by simp [List.getD, hj]
    rw [hget, hdead] at hle
    constructor <;> intro heq <;> simp [heq] at hle
  have hwf' : Wf n gs' := by
    intro j hj
    have hj_er : j < (gs.eraseIdx k).length := by simpa [gs', deleteGate] using hj
    have hget : gs'[j] =
        ((gs.eraseIdx k)[j].1, shiftIdx (n + k) (gs.eraseIdx k)[j].2.1, shiftIdx (n + k) (gs.eraseIdx k)[j].2.2) := by
      simp [gs', deleteGate]
    rw [hget]
    by_cases hjk : j < k
    · have her : (gs.eraseIdx k)[j] = gs[j]'(by omega) := List.getElem_eraseIdx_of_lt hj_er hjk
      rw [her]
      have hwfj := hwf j (by omega)
      simp only [shiftIdx]
      split_ifs <;> omega
    · have her : (gs.eraseIdx k)[j] = gs[j + 1]'(by rw [List.length_eraseIdx_of_lt hk] at hj_er; omega) :=
        List.getElem_eraseIdx_of_ge hj_er (by omega)
      rw [her]
      have hwfj := hwf (j + 1) (by rw [List.length_eraseIdx_of_lt hk] at hj_er; omega)
      have hnr := hnoread (j + 1) (by rw [List.length_eraseIdx_of_lt hk] at hj_er; omega)
      simp only [shiftIdx]
      split_ifs <;> omega
  have hout' : out' < n + gs'.length := by
    dsimp only [out', shiftIdx]; split_ifs <;> omega
  refine ⟨hlen, hwf', hout', fun z => ?_⟩
  have hall : ∀ w < n + gs.length, w ≠ n + k →
      wireVal n gs' (shiftIdx (n + k) w) z = wireVal n gs w z := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwne
      by_cases hlt : w < n
      · have hsh : shiftIdx (n + k) w = w := by simp [shiftIdx]; omega
        rw [hsh, wireVal_input hlt, wireVal_input hlt]
      · set j := w - n
        have hwj : w = n + j := by omega
        have hj : j < gs.length := by omega
        have hjk_ne : j ≠ k := by omega
        rw [hwj, wireVal_gate hwf hj z]
        have hnr := hnoread j hj
        have hwfj := hwf j hj
        by_cases hjk : j < k
        · have hsh : shiftIdx (n + k) (n + j) = n + j := by simp [shiftIdx]; omega
          have hj' : j < gs'.length := by omega
          rw [hsh, wireVal_gate hwf' hj' z]
          have hget : gs'[j]'hj' = (gs[j].1, shiftIdx (n + k) gs[j].2.1, shiftIdx (n + k) gs[j].2.2) := by
            simp [gs', deleteGate, List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt hk]; omega) hjk]
          rw [hget]
          dsimp only
          rw [ih _ (by omega) (by omega) hnr.1, ih _ (by omega) (by omega) hnr.2]
        · have hsh : shiftIdx (n + k) (n + j) = n + (j - 1) := by
            simp only [shiftIdx, show ¬ (n + j < n + k) by omega, ↓reduceIte]; omega
          have hj' : j - 1 < gs'.length := by omega
          rw [hsh, wireVal_gate hwf' hj' z]
          have hget : gs'[j - 1]'hj' = (gs[j].1, shiftIdx (n + k) gs[j].2.1, shiftIdx (n + k) gs[j].2.2) := by
            have hj1 : j - 1 + 1 = j := by omega
            simp only [gs', deleteGate, List.getElem_map]
            have her : (gs.eraseIdx k)[j - 1]'(by rw [List.length_eraseIdx_of_lt hk]; omega) = gs[j - 1 + 1]'(by omega) :=
              List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt hk]; omega) (by omega)
            simp only [hj1] at her
            rw [her]
          rw [hget]
          dsimp only
          rw [ih _ (by omega) (by omega) hnr.1, ih _ (by omega) (by omega) hnr.2]
  exact hall out hout hne

-- Projective plane combinatorial helpers
private lemma plane_point_deg {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p : Fin N) :
    Fintype.card { l : Fin N // I p l } = q + 1 := by
  have hsum : ∑ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l)).card =
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext p'
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, _, hne, _⟩; exact hne
      · intro hne
        obtain ⟨l, ⟨hpl, hp'l⟩, _⟩ := huniq p p' (Ne.symm hne)
        exact ⟨l, hpl, hne, hp'l⟩
    · intro l1 hl1 l2 hl2 hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p' h1 h2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2 h1 h2
      obtain ⟨l0, _, huniq0⟩ := huniq p p' (Ne.symm h1.1)
      have e1 : l1 = l0 := huniq0 l1 ⟨hl1, h1.2⟩
      have e2 : l2 = l0 := huniq0 l2 ⟨hl2, h2.2⟩
      exact hne (e1.trans e2.symm)
  have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have hcard : (Finset.univ.filter (fun p' : Fin N => I p' l)).card = q + 1 := by
      simpa [Fintype.card_subtype] using hline l
    have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) := by simp [hl]
    have heq : Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l) =
        (Finset.univ.filter (fun p' : Fin N => I p' l)).erase p := by
      ext p'; simp [and_comm]
    rw [heq, Finset.card_erase_of_mem hmem, hcard]; omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hsum
  have hrhs : (Finset.univ.filter (fun p' : Fin N => p' ≠ p)).card = N - 1 := by
    have heq : Finset.univ.filter (fun p' : Fin N => p' ≠ p) = Finset.univ.erase p := by
      ext p'; simp
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  have hsum' : (Finset.univ.filter (fun l : Fin N => I p l)).card * q = q ^ 2 + q := by omega
  have hcard_eq : Fintype.card { l : Fin N // I p l } =
      (Finset.univ.filter (fun l : Fin N => I p l)).card := Fintype.card_subtype _
  rw [hcard_eq]
  have hmul : (Finset.univ.filter (fun l : Fin N => I p l)).card * q = (q + 1) * q := by
    rw [hsum', Nat.add_mul, Nat.one_mul, sq]
  exact Nat.eq_of_mul_eq_mul_right (by omega) hmul

private lemma plane_line_diff_nonempty {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {l1 l2 : Fin N} (hne : l1 ≠ l2) :
    ∃ p : Fin N, I p l1 ∧ ¬ I p l2 := by
  by_contra hall
  push Not at hall
  have hcard : (Finset.univ.filter (fun p : Fin N => I p l1)).card = q + 1 := by
    simpa [Fintype.card_subtype] using hline l1
  have h2 : 2 ≤ (Finset.univ.filter (fun p : Fin N => I p l1)).card := by omega
  obtain ⟨p1, hp1, p2, hp2, hp12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun p : Fin N => I p l1)).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
  obtain ⟨l0, _, huniq0⟩ := huniq p1 p2 hp12
  exact hne ((huniq0 l1 ⟨hp1, hp2⟩).trans (huniq0 l2 ⟨hall p1 hp1, hall p2 hp2⟩).symm)

private lemma plane_point_avoid_line {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {p1 p2 : Fin N} (hne : p1 ≠ p2) :
    ∃ l : Fin N, I p1 l ∧ ¬ I p2 l := by
  have hdeg : (Finset.univ.filter (fun l : Fin N => I p1 l)).card = q + 1 := by
    simpa [Fintype.card_subtype] using plane_point_deg hq hN hline huniq p1
  obtain ⟨l1, hl1, l2, hl2, hl12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun l : Fin N => I p1 l)).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2
  by_cases h : I p2 l1
  · refine ⟨l2, hl2, fun h2 => ?_⟩
    obtain ⟨l0, _, huniq0⟩ := huniq p1 p2 hne
    exact hl12 ((huniq0 l1 ⟨hl1, h⟩).trans (huniq0 l2 ⟨hl2, h2⟩).symm)
  · exact ⟨l1, hl1, h⟩

private lemma plane_point_two_lines {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p l : Fin N) (hpl : I p l) :
    ∃ l' : Fin N, l' ≠ l ∧ I p l' := by
  have hdeg : (Finset.univ.filter (fun l0 : Fin N => I p l0)).card = q + 1 := by
    simpa [Fintype.card_subtype] using plane_point_deg hq hN hline huniq p
  have hmem : l ∈ Finset.univ.filter (fun l0 : Fin N => I p l0) := by simp [hpl]
  have hpos : 0 < ((Finset.univ.filter (fun l0 : Fin N => I p l0)).erase l).card := by
    rw [Finset.card_erase_of_mem hmem, hdeg]; omega
  obtain ⟨l', hl'⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
  exact ⟨l', hl'.1, hl'.2⟩

private lemma plane_indep_le {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (UP UL : Finset (Fin N))
    (hind : ∀ p ∈ UP, ∀ l ∈ UL, ¬ I p l) :
    UP.card + UL.card ≤ N := by
  have hcount1 : ∑ p ∈ UP, (Finset.univ.filter (fun l : Fin N => I p l)).card = UP.card * (q + 1) := by
    have h : ∀ p ∈ UP, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1 := fun p _ => by
      simpa [Fintype.card_subtype] using plane_point_deg hq hN hline huniq p
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]
  have hcount2 : ∑ p ∈ UP, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤
      ∑ l ∈ Finset.univ \ UL, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
    have hlhs : ∑ p ∈ UP, (Finset.univ.filter (fun l : Fin N => I p l)).card =
        ∑ p ∈ UP, ∑ l ∈ Finset.univ \ UL, if I p l then 1 else 0 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.card_filter]
      congr 1; ext l
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨fun hl => hind p hp l hl h, h⟩, fun h => h.2⟩
    rw [hlhs, Finset.sum_comm]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.card_filter]
    exact Finset.card_le_card (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp.2)
  have hcount3 : ∑ l ∈ Finset.univ \ UL, (Finset.univ.filter (fun p : Fin N => I p l)).card =
      (N - UL.card) * (q + 1) := by
    have h : ∀ l ∈ Finset.univ \ UL, (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := fun l _ => by
      simpa [Fintype.card_subtype] using hline l
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]
    have hsub : UL ⊆ Finset.univ := Finset.subset_univ _
    have hcard : (Finset.univ \ UL).card = N - UL.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin]
    rw [hcard]
  have hle : UP.card * (q + 1) ≤ (N - UL.card) * (q + 1) := by omega
  have hle' : UP.card ≤ N - UL.card := Nat.le_of_mul_le_mul_right hle (by omega)
  have hUL : UL.card ≤ N := by
    have := Finset.card_le_univ UL; simpa using this
  omega

-- Main lower bound on a pure AND/OR circuit
private def Good {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List (Bool × ℕ × ℕ)) (out : ℕ) : Prop :=
  Wf (N + N) gs ∧ out < N + N + gs.length ∧
  (∀ p l : Fin N, I p l →
    wireVal (N + N) gs out (fun u => decide (u = p.val ∨ u = N + l.val)) = true) ∧
  (∀ L : Finset (Fin N), L.card ≤ q →
    wireVal (N + N) gs out
      (fun u => if h : u < N then decide (∀ l ∈ L, ¬ I ⟨u, h⟩ l)
                else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ L)
                else false) = false)

private lemma good_zL_val {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    (L : Finset (Fin N)) (hL : L.card ≤ q) :
    let zL : ℕ → Bool := fun u =>
      if h : u < N then decide (∀ l ∈ L, ¬ I ⟨u, h⟩ l)
      else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ L)
      else false
    wireVal (N + N) gs out zL = false :=
  hG.2.2.2 L hL

private lemma good_unit_false {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    (w : ℕ) (hw : w < N + N) :
    wireVal (N + N) gs out (fun u => decide (u = w)) = false := by
  by_cases hlt : w < N
  · have h0 := good_zL_val hG ∅ (by simp)
    cases hval : wireVal (N + N) gs out (fun u => decide (u = w)) with
    | false => rfl
    | true =>
      have hm := wireVal_mono hG.1 (z1 := fun u => decide (u = w))
        (z2 := fun u => if h : u < N then decide (∀ l ∈ (∅ : Finset (Fin N)), ¬ I ⟨u, h⟩ l)
                        else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ (∅ : Finset (Fin N)))
                        else false)
        (fun i hi h1 => by
          simp only [decide_eq_true_eq] at h1; subst h1
          simp [hlt])
        out hG.2.1 hval
      rw [h0] at hm; cases hm
  · let l : Fin N := ⟨w - N, by omega⟩
    have h1 := good_zL_val hG {l} (by simp; omega)
    cases hval : wireVal (N + N) gs out (fun u => decide (u = w)) with
    | false => rfl
    | true =>
      have hm := wireVal_mono hG.1 (z1 := fun u => decide (u = w))
        (z2 := fun u => if h : u < N then decide (∀ l0 ∈ ({l} : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
                        else if h2 : u < N + N then decide ((⟨u - N, by omega⟩ : Fin N) ∈ ({l} : Finset (Fin N)))
                        else false)
        (fun i hi h1' => by
          simp only [decide_eq_true_eq] at h1'; subst h1'
          simp only [hlt, hw, ↓reduceDIte, decide_eq_true_eq, Finset.mem_singleton]
          rfl)
        out hG.2.1 hval
      rw [h1] at hm; cases hm

-- Separation witness for flipping input w from false to true, while keeping another input w' true!
private lemma sep_witness {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    {w w' : ℕ} (hw : w < N + N) (hw' : w' < N + N) (hne : w ≠ w') :
    ∃ z : ℕ → Bool, z w = false ∧ z w' = true ∧
      wireVal (N + N) gs out z = false ∧
      wireVal (N + N) gs out (Function.update z w true) = true := by
  by_cases hwp : w < N
  · let p : Fin N := ⟨w, hwp⟩
    by_cases hw'p : w' < N
    · let p' : Fin N := ⟨w', hw'p⟩
      have hpp' : p ≠ p' := fun h => hne (congrArg Fin.val h)
      obtain ⟨l, hpl, hp'l⟩ := plane_point_avoid_line hq hN hline huniq hpp'
      let z : ℕ → Bool := fun u =>
        if h : u < N then decide (∀ l0 ∈ ({l} : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
        else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ ({l} : Finset (Fin N)))
        else false
      refine ⟨z, by simp [z, hwp, p, hpl], by simp [z, hw'p, p', hp'l], good_zL_val hG {l} (by simp; omega), ?_⟩
      exact wireVal_mono hG.1
        (fun i hi h1 => by
          simp only [decide_eq_true_eq] at h1
          rcases h1 with rfl | rfl
          · simp [p]
          · have hneq : N + l.val ≠ w := by omega
            simp [Function.update_of_ne hneq, z, Nat.not_lt.mpr (Nat.le_add_right N l.val), hi])
        out hG.2.1 (hG.2.2.1 p l hpl)
    · let l' : Fin N := ⟨w' - N, by omega⟩
      by_cases hpl' : I p l'
      · let z : ℕ → Bool := fun u =>
          if h : u < N then decide (∀ l0 ∈ ({l'} : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
          else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ ({l'} : Finset (Fin N)))
          else false
        refine ⟨z, by simp [z, hwp, p, hpl'], by simp [z, hw'p, hw', l'], good_zL_val hG {l'} (by simp; omega), ?_⟩
        exact wireVal_mono hG.1
          (fun i hi h1 => by
            simp only [decide_eq_true_eq] at h1
            rcases h1 with rfl | rfl
            · simp [p]
            · have hneq : N + l'.val ≠ w := by omega
              simp [Function.update_of_ne hneq, z, Nat.not_lt.mpr (Nat.le_add_right N l'.val), hi])
          out hG.2.1 (hG.2.2.1 p l' hpl')
      · have hdeg : 0 < (Finset.univ.filter (fun l0 : Fin N => I p l0)).card := by
          have := plane_point_deg hq hN hline huniq p
          rw [Fintype.card_subtype] at this; omega
        obtain ⟨l, hl⟩ := Finset.card_pos.mp hdeg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        let L : Finset (Fin N) := {l, l'}
        have hL : L.card ≤ q := by
          have := Finset.card_le_two (a := l) (b := l'); dsimp only [L]; omega
        let z : ℕ → Bool := fun u =>
          if h : u < N then decide (∀ l0 ∈ L, ¬ I ⟨u, h⟩ l0)
          else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ L)
          else false
        refine ⟨z, ?_, ?_, good_zL_val hG L hL, ?_⟩
        · simp only [z, hwp, ↓reduceDIte, decide_eq_false_iff_not, not_forall, not_not]
          exact ⟨l, by simp [L], hl⟩
        · simp [z, hw'p, hw', l', L]
        · exact wireVal_mono hG.1
            (fun i hi h1 => by
              simp only [decide_eq_true_eq] at h1
              rcases h1 with rfl | rfl
              · simp [p]
              · have hneq : N + l.val ≠ w := by omega
                simp [Function.update_of_ne hneq, z, Nat.not_lt.mpr (Nat.le_add_right N l.val), hi, L])
            out hG.2.1 (hG.2.2.1 p l hl)
  · let l : Fin N := ⟨w - N, by omega⟩
    by_cases hw'p : w' < N
    · have hpos : 0 < (Finset.univ.filter (fun p0 : Fin N => I p0 l)).card := by
        have := hline l; rw [Fintype.card_subtype] at this; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      let z : ℕ → Bool := fun u =>
        if h : u < N then decide (∀ l0 ∈ (∅ : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
        else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ (∅ : Finset (Fin N)))
        else false
      refine ⟨z, by simp [z, hwp], by simp [z, hw'p], good_zL_val hG ∅ (by simp), ?_⟩
      exact wireVal_mono hG.1
        (fun i hi h1 => by
          simp only [decide_eq_true_eq] at h1
          rcases h1 with rfl | rfl
          · have hneq : p.val ≠ w := by omega
            simp [Function.update_of_ne hneq, z, p.isLt]
          · have heq : N + l.val = w := by dsimp only [l]; omega
            simp [heq])
        out hG.2.1 (hG.2.2.1 p l hp)
    · let l' : Fin N := ⟨w' - N, by omega⟩
      have hll' : l ≠ l' := fun h => hne (by have := congrArg Fin.val h; dsimp [l, l'] at this; omega)
      obtain ⟨p, hpl, hpl'⟩ := plane_line_diff_nonempty hq hline huniq hll'
      let z : ℕ → Bool := fun u =>
        if h : u < N then decide (∀ l0 ∈ ({l'} : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
        else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ ({l'} : Finset (Fin N)))
        else false
      refine ⟨z, by simp [z, hwp, hw, l, hll'], by simp [z, hw'p, hw', l'], good_zL_val hG {l'} (by simp; omega), ?_⟩
      exact wireVal_mono hG.1
        (fun i hi h1 => by
          simp only [decide_eq_true_eq] at h1
          rcases h1 with rfl | rfl
          · have hneq : p.val ≠ w := by omega
            simp [Function.update_of_ne hneq, z, p.isLt, hpl']
          · have heq : N + l.val = w := by dsimp only [l]; omega
            simp [heq])
        out hG.2.1 (hG.2.2.1 p l hpl)

-- Unique reader helper
private lemma unique_reader_of_fanout_one {gs : List (Bool × ℕ × ℕ)} {w : ℕ}
    (hf : fanout gs w = 1) :
    ∃ (j : ℕ) (hj : j < gs.length),
      ((gs[j].2.1 = w ∧ gs[j].2.2 ≠ w) ∨ (gs[j].2.1 ≠ w ∧ gs[j].2.2 = w)) ∧
      ∀ (k : ℕ) (hk : k < gs.length), k ≠ j → gs[k].2.1 ≠ w ∧ gs[k].2.2 ≠ w := by
  have hex : ∃ j ∈ Finset.range gs.length,
      (if (gs.getD j (false, 0, 0)).2.1 = w then 1 else 0) +
      (if (gs.getD j (false, 0, 0)).2.2 = w then 1 else 0) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : fanout gs w = 0 := Finset.sum_eq_zero hall
    omega
  obtain ⟨j, hjmem, hjne⟩ := hex
  have hj : j < gs.length := Finset.mem_range.mp hjmem
  have hsplit := Finset.add_sum_erase (Finset.range gs.length)
    (fun i => (if (gs.getD i (false, 0, 0)).2.1 = w then 1 else 0) +
              (if (gs.getD i (false, 0, 0)).2.2 = w then 1 else 0)) hjmem
  change _ + _ = fanout gs w at hsplit
  rw [hf] at hsplit
  have hj1 : (if (gs.getD j (false, 0, 0)).2.1 = w then 1 else 0) +
      (if (gs.getD j (false, 0, 0)).2.2 = w then 1 else 0) = 1 := by omega
  have hrest : ∑ i ∈ (Finset.range gs.length).erase j,
      ((if (gs.getD i (false, 0, 0)).2.1 = w then 1 else 0) +
       (if (gs.getD i (false, 0, 0)).2.2 = w then 1 else 0)) = 0 := by omega
  have hgetj : gs.getD j (false, 0, 0) = gs[j] := by simp [List.getD, hj]
  rw [hgetj] at hj1
  refine ⟨j, hj, ?_, ?_⟩
  · by_cases h1 : gs[j].2.1 = w <;> by_cases h2 : gs[j].2.2 = w <;> simp [h1, h2] at hj1
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · intro k hk hkj
    have hkm : k ∈ (Finset.range gs.length).erase j := Finset.mem_erase.mpr ⟨hkj, Finset.mem_range.mpr hk⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) k hkm
    have hgetk : gs.getD k (false, 0, 0) = gs[k] := by simp [List.getD, hk]
    rw [hgetk] at h0
    constructor <;> intro heq <;> simp [heq] at h0

-- OR-chain from a wire w with fanout 1
private def orStep (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : Option ℕ :=
  if fanout gs w == 1 then
    match (List.range gs.length).find? (fun j =>
      let g := gs.getD j (false, 0, 0)
      g.1 && (g.2.1 == w || g.2.2 == w)) with
    | some j => some (n + j)
    | none => none
  else none

private lemma orStep_spec {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs) {w v : ℕ}
    (hs : orStep n gs w = some v) :
    fanout gs w = 1 ∧ ∃ (j : ℕ) (hj : j < gs.length),
      v = n + j ∧ w < v ∧ gs[j].1 = true ∧ (gs[j].2.1 = w ∨ gs[j].2.2 = w) ∧
      ∀ (k : ℕ) (hk : k < gs.length), k ≠ j → gs[k].2.1 ≠ w ∧ gs[k].2.2 ≠ w := by
  unfold orStep at hs
  by_cases hf : fanout gs w = 1
  · simp only [hf, beq_self_eq_true, ↓reduceIte] at hs
    cases hfind : (List.range gs.length).find? (fun j =>
        let g := gs.getD j (false, 0, 0)
        g.1 && (g.2.1 == w || g.2.2 == w)) with
    | none => rw [hfind] at hs; simp at hs
    | some j =>
      rw [hfind] at hs
      simp only [Option.some.injEq] at hs
      have hmem := List.mem_of_find?_eq_some hfind
      have hj : j < gs.length := List.mem_range.mp hmem
      have hpred := List.find?_some hfind
      dsimp only at hpred
      have hget : gs.getD j (false, 0, 0) = gs[j] := by simp [List.getD, hj]
      rw [hget] at hpred
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpred
      obtain ⟨j0, hj0, hreads0, huniq0⟩ := unique_reader_of_fanout_one hf
      have hjj0 : j = j0 := by
        by_contra hne
        have := huniq0 j hj hne
        rcases hpred.2 with h | h
        · exact this.1 h
        · exact this.2 h
      subst hjj0
      have hwfj := hwf j hj
      have hwlt : w < v := by rcases hpred.2 with h | h <;> omega
      exact ⟨hf, j, hj, hs.symm, hwlt, hpred.1, hpred.2, huniq0⟩
  · have hbf : (fanout gs w == 1) = false := beq_false_of_ne hf
    simp [hbf] at hs

private def orChainAux (n : ℕ) (gs : List (Bool × ℕ × ℕ)) : ℕ → ℕ → List ℕ
  | 0, w => [w]
  | fuel + 1, w =>
    match orStep n gs w with
    | some v => w :: orChainAux n gs fuel v
    | none => [w]

private def orChain (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : List ℕ :=
  orChainAux n gs (n + gs.length + 1) w

private lemma orStep_none_of_fanout_one {n : ℕ} {gs : List (Bool × ℕ × ℕ)} {w : ℕ}
    (hf : fanout gs w = 1) (hnone : orStep n gs w = none) :
    ∃ (j : ℕ) (hj : j < gs.length),
      gs[j].1 = false ∧
      ((gs[j].2.1 = w ∧ gs[j].2.2 ≠ w) ∨ (gs[j].2.1 ≠ w ∧ gs[j].2.2 = w)) ∧
      ∀ (k : ℕ) (hk : k < gs.length), k ≠ j → gs[k].2.1 ≠ w ∧ gs[k].2.2 ≠ w := by
  obtain ⟨j, hj, hreads, huniq⟩ := unique_reader_of_fanout_one hf
  refine ⟨j, hj, ?_, hreads, huniq⟩
  by_contra htrue
  have h1 : gs[j].1 = true := by cases hg : gs[j].1 <;> simp_all
  unfold orStep at hnone
  simp only [hf, beq_self_eq_true, ↓reduceIte] at hnone
  cases hfind : (List.range gs.length).find? (fun i =>
      let g := gs.getD i (false, 0, 0)
      g.1 && (g.2.1 == w || g.2.2 == w)) with
  | some _ => rw [hfind] at hnone; simp at hnone
  | none =>
    have hall := List.find?_eq_none.mp hfind j (List.mem_range.mpr hj)
    dsimp only at hall
    have hget : gs.getD j (false, 0, 0) = gs[j] := by simp [List.getD, hj]
    rw [hget, h1] at hall
    rcases hreads with ⟨h, _⟩ | ⟨_, h⟩ <;> simp [h] at hall

private lemma orChainAux_props {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs) :
    ∀ (fuel w : ℕ), w < n + gs.length → n + gs.length - w ≤ fuel →
      let ch := orChainAux n gs fuel w
      ∃ top, ch.getLast? = some top ∧
        w ∈ ch ∧ top ∈ ch ∧ top < n + gs.length ∧
        orStep n gs top = none ∧
        (∀ u ∈ ch, w ≤ u ∧ u ≤ top ∧ u < n + gs.length) ∧
        (∀ u ∈ ch, u ≠ w → n ≤ u ∧ (gs.getD (u - n) (false, 0, 0)).1 = true) ∧
        (∀ u ∈ ch, ∀ z : ℕ → Bool, wireVal n gs w z = true → wireVal n gs u z = true) ∧
        (∀ u ∈ ch, u ≠ top → ∀ (k : ℕ) (hk : k < gs.length),
          gs[k].2.1 = u ∨ gs[k].2.2 = u →
          n + k ∈ ch ∧ ∀ x ∈ ch, u < x → n + k ≤ x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hw hfuel; omega
  | succ fuel ih =>
    intro w hw hfuel
    dsimp only [orChainAux]
    cases hs : orStep n gs w with
    | none =>
      refine ⟨w, rfl, by simp, by simp, hw, hs,
        fun u hu => by simp at hu; subst hu; exact ⟨le_rfl, le_rfl, hw⟩,
        fun u hu hne => by simp at hu; exact False.elim (hne hu),
        fun u hu z hz => by simp at hu; subst hu; exact hz,
        fun u hu hne => by simp at hu; exact False.elim (hne hu)⟩
    | some v =>
      obtain ⟨hfw, j, hj, hv, hwv, hgj1, hgjr, huniq⟩ := orStep_spec hwf hs
      have hvlt : v < n + gs.length := by omega
      have hfuel' : n + gs.length - v ≤ fuel := by omega
      obtain ⟨top, hlast, hvmem, htopmem, htoplt, htopnone, hbounds, hgates, hmono, hread⟩ :=
        ih v hvlt hfuel'
      have hne_nil : orChainAux n gs fuel v ≠ [] := by
        intro hnil; rw [hnil] at hvmem; simp at hvmem
      refine ⟨top, ?_, List.mem_cons_self, List.mem_cons_of_mem w htopmem, htoplt, htopnone,
        ?_, ?_, ?_, ?_⟩
      · change (w :: orChainAux n gs fuel v).getLast? = some top
        cases hch : orChainAux n gs fuel v with
        | nil => exact False.elim (hne_nil hch)
        | cons a as =>
          rw [hch] at hlast
          simpa [List.getLast?_cons] using hlast
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · have hvt := (hbounds v hvmem).2.1
          exact ⟨le_rfl, by omega, hw⟩
        · have hbu := hbounds u hu'
          exact ⟨by omega, hbu.2.1, hbu.2.2⟩
      · intro u hu hne
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact False.elim (hne rfl)
        · by_cases huv : u = v
          · rw [huv]
            refine ⟨by omega, ?_⟩
            have hsub : v - n = j := by omega
            rw [hsub]
            simp [List.getD, hj, hgj1]
          · exact hgates u hu' huv
      · intro u hu z hz
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hz
        · have hvtrue : wireVal n gs v z = true := by
            rw [hv, wireVal_gate hwf hj z, hgj1]
            simp only [↓reduceIte, Bool.or_eq_true]
            rcases hgjr with h | h
            · left; rw [h]; exact hz
            · right; rw [h]; exact hz
          exact hmono u hu' z hvtrue
      · intro u hu hne k hk hkr
        rcases List.mem_cons.mp hu with huw | hu'
        · rw [huw] at hkr ⊢
          have hkj : k = j := by
            by_contra hkne
            have hnu := huniq k hk hkne
            rcases hkr with h | h
            · exact hnu.1 h
            · exact hnu.2 h
          subst hkj
          rw [← hv]
          refine ⟨List.mem_cons_of_mem w hvmem, fun x hx hwx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · omega
          · exact (hbounds x hx').1
        · obtain ⟨hmemk, hlek⟩ := hread u hu' hne k hk hkr
          refine ⟨List.mem_cons_of_mem w hmemk, fun x hx hux => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · have hbu := (hbounds u hu').1
            omega
          · exact hlek x hx' hux

private def orTop (n : ℕ) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : ℕ :=
  (orChain n gs w).getLast?.getD w

private lemma orChain_props {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {w : ℕ} (hw : w < n) :
    let ch := orChain n gs w
    let top := orTop n gs w
    w ∈ ch ∧ top ∈ ch ∧ top < n + gs.length ∧
    orStep n gs top = none ∧
    (∀ u ∈ ch, w ≤ u ∧ u ≤ top ∧ u < n + gs.length) ∧
    (∀ u ∈ ch, u ≠ w → n ≤ u ∧ (gs.getD (u - n) (false, 0, 0)).1 = true) ∧
    (∀ u ∈ ch, ∀ z : ℕ → Bool, z w = true → wireVal n gs u z = true) ∧
    (∀ u ∈ ch, u ≠ top → ∀ (k : ℕ) (hk : k < gs.length),
      gs[k].2.1 = u ∨ gs[k].2.2 = u →
      n + k ∈ ch ∧ ∀ x ∈ ch, u < x → n + k ≤ x) := by
  have hwlt : w < n + gs.length := by omega
  have hfuel : n + gs.length - w ≤ n + gs.length + 1 := by omega
  have hraw := orChainAux_props hwf (n + gs.length + 1) w hwlt hfuel
  obtain ⟨top, hlast, hwmem, htopmem, htoplt, htopnone, hbounds, hgates, hmono, hread⟩ := hraw
  have htop_eq : orTop n gs w = top := by
    simp [orTop, orChain, hlast]
  rw [htop_eq]
  refine ⟨hwmem, htopmem, htoplt, htopnone, hbounds, hgates, fun u hu z hz => ?_, hread⟩
  exact hmono u hu z (by rw [wireVal_input hw]; exact hz)

-- Dominator lemma for any node v in orChain n gs w
private lemma orChain_dom {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {w v : ℕ} (hw : w < n) (hv : v ∈ orChain n gs w)
    {z1 z2 : ℕ → Bool}
    (hagree : ∀ i < n, i ≠ w → z1 i = z2 i)
    (hv_eq : wireVal n gs v z1 = wireVal n gs v z2) :
    ∀ u < n + gs.length, (u ∉ orChain n gs w ∨ v ≤ u) →
      wireVal n gs u z1 = wireVal n gs u z2 := by
  have ⟨hwmem, htopmem, htoplt, htopnone, hbounds, hgates, hmono, hread⟩ := orChain_props hwf hw
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hcond
    by_cases hlt : u < n
    · by_cases huw : u = w
      · rw [huw] at hcond ⊢
        have hv_ge : w ≤ v := (hbounds v hv).1
        have hvw : v ≤ w := by
          rcases hcond with hnot | hle
          · exact False.elim (hnot hwmem)
          · exact hle
        have heq : v = w := by omega
        rw [← heq]; exact hv_eq
      · rw [wireVal_input hlt, wireVal_input hlt]
        exact hagree u hlt huw
    · by_cases huv : u = v
      · subst huv; exact hv_eq
      · set k := u - n
        have huk : u = n + k := by omega
        have hk : k < gs.length := by omega
        rw [huk, wireVal_gate hwf hk, wireVal_gate hwf hk]
        have hwfj := hwf k hk
        have hinput_cond : ∀ r, (gs[k].2.1 = r ∨ gs[k].2.2 = r) → r ∉ orChain n gs w ∨ v ≤ r := by
          intro r hr
          by_contra hneg
          push Not at hneg
          have hvt := (hbounds v hv).2.1
          have hr_ne_top : r ≠ orTop n gs w := by omega
          obtain ⟨hmemk, hlek⟩ := hread r hneg.1 hr_ne_top k hk hr
          have hle_v : n + k ≤ v := hlek v hv hneg.2
          rw [← huk] at hmemk hle_v
          rcases hcond with hnot | hge
          · exact hnot hmemk
          · omega
        have ha := ih gs[k].2.1 (by omega) (by omega) (hinput_cond gs[k].2.1 (Or.inl rfl))
        have hb := ih gs[k].2.2 (by omega) (by omega) (hinput_cond gs[k].2.2 (Or.inr rfl))
        rw [ha, hb]

-- Dominator lemma through the unique reader of orTop n gs w
private lemma orChain_reader_dom {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {w j : ℕ} (hw : w < n) (hj : j < gs.length)
    (huniq : ∀ (k : ℕ) (hk : k < gs.length), k ≠ j →
      gs[k].2.1 ≠ orTop n gs w ∧ gs[k].2.2 ≠ orTop n gs w)
    {z1 z2 : ℕ → Bool}
    (hagree : ∀ i < n, i ≠ w → z1 i = z2 i)
    (ha_eq : wireVal n gs (n + j) z1 = wireVal n gs (n + j) z2) :
    ∀ u < n + gs.length, u ∉ orChain n gs w →
      wireVal n gs u z1 = wireVal n gs u z2 := by
  have ⟨hwmem, _, _, _, _, _, _, hread⟩ := orChain_props hwf hw
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hnot
    by_cases hlt : u < n
    · have huw : u ≠ w := fun h => hnot (h ▸ hwmem)
      rw [wireVal_input hlt, wireVal_input hlt]
      exact hagree u hlt huw
    · set k := u - n
      have huk : u = n + k := by omega
      have hk : k < gs.length := by omega
      by_cases hkj : k = j
      · subst hkj; rw [huk]; exact ha_eq
      · rw [huk, wireVal_gate hwf hk, wireVal_gate hwf hk]
        have hwfj := hwf k hk
        have hinput_not : ∀ r, (gs[k].2.1 = r ∨ gs[k].2.2 = r) → r ∉ orChain n gs w := by
          intro r hr hrmem
          by_cases hrt : r = orTop n gs w
          · subst hrt
            have hnu := huniq k hk hkj
            rcases hr with h | h
            · exact hnu.1 h
            · exact hnu.2 h
          · obtain ⟨hmemk, _⟩ := hread r hrmem hrt k hk hr
            rw [← huk] at hmemk
            exact hnot hmemk
        have ha := ih gs[k].2.1 (by omega) (by omega) (hinput_not gs[k].2.1 (Or.inl rfl))
        have hb := ih gs[k].2.2 (by omega) (by omega) (hinput_not gs[k].2.2 (Or.inr rfl))
        rw [ha, hb]

-- Independence of wires strictly before the unique reader of orTop n gs w
private lemma orChain_indep_lt_reader {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {w j : ℕ} (hw : w < n) (hj : j < gs.length)
    (huniq : ∀ (k : ℕ) (hk : k < gs.length), k ≠ j →
      gs[k].2.1 ≠ orTop n gs w ∧ gs[k].2.2 ≠ orTop n gs w)
    {z1 z2 : ℕ → Bool}
    (hagree : ∀ i < n, i ≠ w → z1 i = z2 i) :
    ∀ u < n + j, u ∉ orChain n gs w →
      wireVal n gs u z1 = wireVal n gs u z2 := by
  have ⟨hwmem, _, _, _, _, _, _, hread⟩ := orChain_props hwf hw
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hnot
    by_cases hlt : u < n
    · have huw : u ≠ w := fun h => hnot (h ▸ hwmem)
      rw [wireVal_input hlt, wireVal_input hlt]
      exact hagree u hlt huw
    · set k := u - n
      have huk : u = n + k := by omega
      have hk : k < gs.length := by omega
      have hkj : k ≠ j := by omega
      rw [huk, wireVal_gate hwf hk, wireVal_gate hwf hk]
      have hwfj := hwf k hk
      have hinput_not : ∀ r, (gs[k].2.1 = r ∨ gs[k].2.2 = r) → r ∉ orChain n gs w := by
        intro r hr hrmem
        by_cases hrt : r = orTop n gs w
        · subst hrt
          have hnu := huniq k hk hkj
          rcases hr with h | h
          · exact hnu.1 h
          · exact hnu.2 h
        · obtain ⟨hmemk, _⟩ := hread r hrmem hrt k hk hr
          rw [← huk] at hmemk
          exact hnot hmemk
      have ha := ih gs[k].2.1 (by omega) (by omega) (hinput_not gs[k].2.1 (Or.inl rfl))
      have hb := ih gs[k].2.2 (by omega) (by omega) (hinput_not gs[k].2.2 (Or.inr rfl))
      rw [ha, hb]

-- Independence when fanout = 0
private lemma wireVal_indep_of_fanout_zero {n : ℕ} {gs : List (Bool × ℕ × ℕ)} (hwf : Wf n gs)
    {w : ℕ} (hf0 : fanout gs w = 0)
    {z1 z2 : ℕ → Bool} (hagree : ∀ i < n, i ≠ w → z1 i = z2 i) :
    ∀ u < n + gs.length, u ≠ w → wireVal n gs u z1 = wireVal n gs u z2 := by
  have hnoread : ∀ (k : ℕ) (hk : k < gs.length), gs[k].2.1 ≠ w ∧ gs[k].2.2 ≠ w := by
    intro k hk
    have hmem : k ∈ Finset.range gs.length := Finset.mem_range.mpr hk
    have hle : (if (gs.getD k (false, 0, 0)).2.1 = w then 1 else 0) +
        (if (gs.getD k (false, 0, 0)).2.2 = w then 1 else 0) ≤ fanout gs w :=
      Finset.single_le_sum (f := fun i =>
        (if (gs.getD i (false, 0, 0)).2.1 = w then 1 else 0) +
        (if (gs.getD i (false, 0, 0)).2.2 = w then 1 else 0))
        (fun _ _ => Nat.zero_le _) hmem
    have hget : gs.getD k (false, 0, 0) = gs[k] := by simp [List.getD, hk]
    rw [hget, hf0] at hle
    constructor <;> intro heq <;> simp [heq] at hle
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hne
    by_cases hlt : u < n
    · rw [wireVal_input hlt, wireVal_input hlt]
      exact hagree u hlt hne
    · set k := u - n
      have huk : u = n + k := by omega
      have hk : k < gs.length := by omega
      rw [huk, wireVal_gate hwf hk, wireVal_gate hwf hk]
      have hwfj := hwf k hk
      have hnr := hnoread k hk
      rw [ih gs[k].2.1 (by omega) (by omega) hnr.1, ih gs[k].2.2 (by omega) (by omega) hnr.2]

-- Out is not in any OR-chain of an input
private lemma out_not_mem_orChain {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    {w : ℕ} (hw : w < N + N) :
    out ∉ orChain (N + N) gs w := by
  intro hmem
  have ⟨_, _, _, _, _, _, hmono, _⟩ := orChain_props hG.1 hw
  have ht := hmono out hmem (fun u => decide (u = w)) (by simp)
  have hf := good_unit_false hq hG w hw
  rw [hf] at ht; cases ht

-- OR-chains of distinct inputs are disjoint
private lemma orChain_disjoint {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    {w w' : ℕ} (hw : w < N + N) (hw' : w' < N + N) (hne : w ≠ w')
    {v : ℕ} (hv1 : v ∈ orChain (N + N) gs w) (hv2 : v ∈ orChain (N + N) gs w') : False := by
  obtain ⟨z, hzw, hzw', hzf, hzt⟩ := sep_witness hq hN hline huniq hG hw hw' hne
  have ⟨_, _, _, _, _, _, hmono', _⟩ := orChain_props hG.1 hw'
  have hv_z : wireVal (N + N) gs v z = true := hmono' v hv2 z hzw'
  have hv_z' : wireVal (N + N) gs v (Function.update z w true) = true :=
    hmono' v hv2 (Function.update z w true) (by rw [Function.update_of_ne hne.symm]; exact hzw')
  have hout_not : out ∉ orChain (N + N) gs w := out_not_mem_orChain hq hG hw
  have heq := orChain_dom hG.1 hw hv1 (z1 := z) (z2 := Function.update z w true)
    (fun i _ hi => (Function.update_of_ne hi true z).symm)
    (hv_z.trans hv_z'.symm)
    out hG.2.1 (Or.inl hout_not)
  rw [hzf, hzt] at heq; cases heq

-- No strictly earlier AND-reader among two distinct inputs whose pair activates out
private lemma no_earlier_and_reader {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    {w1 w2 : ℕ} (hw1 : w1 < N + N) (hw2 : w2 < N + N) (_hne : w1 ≠ w2)
    (hpair : wireVal (N + N) gs out (fun u => decide (u = w1 ∨ u = w2)) = true)
    {j1 j2 : ℕ} (hj1 : j1 < gs.length) (hj2 : j2 < gs.length) (hjl : j1 < j2)
    (hand1 : gs[j1].1 = false)
    (hreads1 : (gs[j1].2.1 = orTop (N + N) gs w1 ∧ gs[j1].2.2 ≠ orTop (N + N) gs w1) ∨
               (gs[j1].2.1 ≠ orTop (N + N) gs w1 ∧ gs[j1].2.2 = orTop (N + N) gs w1))
    (huniq1 : ∀ (k : ℕ) (hk : k < gs.length), k ≠ j1 →
      gs[k].2.1 ≠ orTop (N + N) gs w1 ∧ gs[k].2.2 ≠ orTop (N + N) gs w1)
    (huniq2 : ∀ (k : ℕ) (hk : k < gs.length), k ≠ j2 →
      gs[k].2.1 ≠ orTop (N + N) gs w2 ∧ gs[k].2.2 ≠ orTop (N + N) gs w2) : False := by
  let zUnit2 : ℕ → Bool := fun u => decide (u = w2)
  let zPair : ℕ → Bool := fun u => decide (u = w1 ∨ u = w2)
  let zUnit1 : ℕ → Bool := fun u => decide (u = w1)
  have hout_u2 : wireVal (N + N) gs out zUnit2 = false := good_unit_false hq hG w2 hw2
  have ha1_pair : wireVal (N + N) gs (N + N + j1) zPair = true := by
    cases ha : wireVal (N + N) gs (N + N + j1) zPair with
    | true => rfl
    | false =>
      have ha_u2 : wireVal (N + N) gs (N + N + j1) zUnit2 = false := by
        cases h2 : wireVal (N + N) gs (N + N + j1) zUnit2 with
        | false => rfl
        | true =>
          have hm := wireVal_mono hG.1 (z1 := zUnit2) (z2 := zPair)
            (fun i _ hi => by simp only [zUnit2, decide_eq_true_eq] at hi; simp [zPair, hi])
            (N + N + j1) (by omega) h2
          rw [ha] at hm; cases hm
      have heq := orChain_reader_dom hG.1 hw1 hj1 huniq1 (z1 := zUnit2) (z2 := zPair)
        (fun i _ hi => by simp [zUnit2, zPair, hi])
        (ha_u2.trans ha.symm)
        out hG.2.1 (out_not_mem_orChain hq hG hw1)
      rw [hout_u2, hpair] at heq; cases heq
  -- N + N + j1 is an AND gate so it is not in orChain w2
  have ha1_not_ch2 : N + N + j1 ∉ orChain (N + N) gs w2 := by
    intro hmem
    have ⟨_, _, _, _, _, hgates2, _, _⟩ := orChain_props hG.1 hw2
    have hne2 : N + N + j1 ≠ w2 := by omega
    have hg := (hgates2 (N + N + j1) hmem hne2).2
    have hsub : N + N + j1 - (N + N) = j1 := by omega
    rw [hsub] at hg
    simp [List.getD, hj1, hand1] at hg
  have ha1_u1 : wireVal (N + N) gs (N + N + j1) zUnit1 = true := by
    have heq := orChain_indep_lt_reader hG.1 hw2 hj2 huniq2 (z1 := zUnit1) (z2 := zPair)
      (fun i _ hi => by simp [zUnit1, zPair, hi])
      (N + N + j1) (by omega) ha1_not_ch2
    rw [heq]; exact ha1_pair
  rw [wireVal_gate hG.1 hj1 zUnit1, hand1] at ha1_u1
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ha1_u1
  have hwfj1 := hG.1 j1 hj1
  have ⟨_, _, _, _, hbounds1, _, _, hread1⟩ := orChain_props hG.1 hw1
  have hother : ∀ r, r < N + N + j1 → r ≠ orTop (N + N) gs w1 →
      (gs[j1].2.1 = r ∨ gs[j1].2.2 = r) → wireVal (N + N) gs r zUnit1 = true → False := by
    intro r hrlt hrne hr_in hr_true
    have hr_not_ch1 : r ∉ orChain (N + N) gs w1 := by
      intro hrmem
      obtain ⟨hmem_j1, _⟩ := hread1 r hrmem hrne j1 hj1 hr_in
      have hle_top := (hbounds1 (N + N + j1) hmem_j1).2.1
      have htop_lt : orTop (N + N) gs w1 < N + N + j1 := by
        rcases hreads1 with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
      omega
    have heq := orChain_indep_lt_reader hG.1 hw1 hj1 huniq1 (z1 := fun _ => false) (z2 := zUnit1)
      (fun i _ hi => by simp [zUnit1, hi])
      r hrlt hr_not_ch1
    rw [wireVal_zero hG.1 r (by omega), hr_true] at heq
    cases heq
  rcases hreads1 with ⟨_, hne2⟩ | ⟨hne1, _⟩
  · exact hother gs[j1].2.2 hwfj1.2 hne2 (Or.inr rfl) ha1_u1.2
  · exact hother gs[j1].2.1 hwfj1.1 hne1 (Or.inl rfl) ha1_u1.1

-- Main circuit lower bound on a minimal Good circuit
private lemma good_size_bound {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {gs : List (Bool × ℕ × ℕ)} {out : ℕ} (hG : Good (q := q) I gs out)
    (hmin : ∀ k < gs.length, N + N + k ≠ out → fanout gs (N + N + k) ≠ 0) :
    3 * N ≤ gs.length + 1 := by
  have hNpos : 7 ≤ N := by
    have hsq : 4 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq 2
    omega
  have hout_ge : N + N ≤ out := by
    by_contra hlt
    push Not at hlt
    have hf := good_unit_false hq hG out hlt
    rw [wireVal_input hlt] at hf
    simp at hf
  have hglen_pos : 1 ≤ gs.length := by have := hG.2.1; omega
  have hfan_in : ∀ w < N + N, 1 ≤ fanout gs w := by
    intro w hw
    by_contra h0
    have hf0 : fanout gs w = 0 := by omega
    let w' : ℕ := if w = 0 then 1 else 0
    have hw' : w' < N + N := by dsimp [w']; split_ifs <;> omega
    have hne : w ≠ w' := by dsimp [w']; split_ifs <;> omega
    obtain ⟨z, _, _, hzf, hzt⟩ := sep_witness hq hN hline huniq hG hw hw' hne
    have heq := wireVal_indep_of_fanout_zero hG.1 hf0 (z1 := z) (z2 := Function.update z w true)
      (fun i _ hi => (Function.update_of_ne hi true z).symm)
      out hG.2.1 (by omega)
    rw [hzf, hzt] at heq; cases heq
  -- Properties of orTop on inputs
  have htop_inj : ∀ w1 < N + N, ∀ w2 < N + N, orTop (N + N) gs w1 = orTop (N + N) gs w2 → w1 = w2 := by
    intro w1 hw1 w2 hw2 heq
    by_contra hne
    have h1 := (orChain_props hG.1 hw1).2.1
    have h2 := (orChain_props hG.1 hw2).2.1
    rw [← heq] at h2
    exact orChain_disjoint hq hN hline huniq hG hw1 hw2 hne h1 h2
  have htop_ne_out : ∀ w < N + N, orTop (N + N) gs w ≠ out := by
    intro w hw heq
    have hmem := (orChain_props hG.1 hw).2.1
    rw [heq] at hmem
    exact out_not_mem_orChain hq hG hw hmem
  have htop_fan_pos : ∀ w < N + N, 1 ≤ fanout gs (orTop (N + N) gs w) := by
    intro w hw
    by_cases hlt : orTop (N + N) gs w < N + N
    · exact hfan_in _ hlt
    · have htoplt := (orChain_props hG.1 hw).2.2.1
      set k := orTop (N + N) gs w - (N + N)
      have hk : k < gs.length := by omega
      have heq : N + N + k = orTop (N + N) gs w := by omega
      have hne := htop_ne_out w hw
      have hnz := hmin k hk (by omega)
      rw [heq] at hnz; omega
  -- Define partitions of inputs
  let Inputs := Finset.range (N + N)
  let U1 := Inputs.filter (fun w => fanout gs w = 1)
  let Uge2 := Inputs.filter (fun w => 2 ≤ fanout gs w)
  let Ubranch := U1.filter (fun w => 2 ≤ fanout gs (orTop (N + N) gs w))
  let Uand := U1.filter (fun w => fanout gs (orTop (N + N) gs w) = 1)
  have hInputs_disj : Disjoint U1 Uge2 := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [U1, Uge2, Finset.mem_filter] at h1 h2; omega
  have hInputs_union : U1 ∪ Uge2 = Inputs := by
    ext w
    simp only [U1, Uge2, Finset.mem_union, Finset.mem_filter, Inputs, Finset.mem_range]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hw
      have hf := hfan_in w hw
      by_cases h1 : fanout gs w = 1
      · exact Or.inl ⟨hw, h1⟩
      · exact Or.inr ⟨hw, by omega⟩
  have hU1_disj : Disjoint Ubranch Uand := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Ubranch, Uand, Finset.mem_filter] at h1 h2; omega
  have hU1_union : Ubranch ∪ Uand = U1 := by
    ext w
    simp only [Ubranch, Uand, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hw
      have hwlt : w < N + N := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have hf := htop_fan_pos w hwlt
      by_cases h1 : fanout gs (orTop (N + N) gs w) = 1
      · exact Or.inr ⟨hw, h1⟩
      · exact Or.inl ⟨hw, by omega⟩
  have hcard_in : U1.card + Uge2.card = N + N := by
    rw [← Finset.card_union_of_disjoint hInputs_disj, hInputs_union, Finset.card_range]
  have hcard_U1 : Ubranch.card + Uand.card = U1.card := by
    rw [← Finset.card_union_of_disjoint hU1_disj, hU1_union]
  -- Independent set property for Uand
  let UP : Finset (Fin N) := Finset.univ.filter (fun p : Fin N => p.val ∈ Uand)
  let UL : Finset (Fin N) := Finset.univ.filter (fun l : Fin N => N + l.val ∈ Uand)
  have hUand_indep : ∀ p ∈ UP, ∀ l ∈ UL, ¬ I p l := by
    intro p hp l hl hpl
    simp only [UP, UL, Finset.mem_filter, Finset.mem_univ, true_and] at hp hl
    have hp_lt : p.val < N + N := by omega
    have hl_lt : N + l.val < N + N := by omega
    have hpl_ne : p.val ≠ N + l.val := by omega
    have hfp1 : fanout gs (orTop (N + N) gs p.val) = 1 := (Finset.mem_filter.mp hp).2
    have hfl1 : fanout gs (orTop (N + N) gs (N + l.val)) = 1 := (Finset.mem_filter.mp hl).2
    have hnone_p := (orChain_props hG.1 hp_lt).2.2.2.1
    have hnone_l := (orChain_props hG.1 hl_lt).2.2.2.1
    obtain ⟨jp, hjp, hjp_and, hjp_reads, hjp_uniq⟩ := orStep_none_of_fanout_one hfp1 hnone_p
    obtain ⟨jl, hjl, hjl_and, hjl_reads, hjl_uniq⟩ := orStep_none_of_fanout_one hfl1 hnone_l
    have hpair_pl : wireVal (N + N) gs out (fun u => decide (u = p.val ∨ u = N + l.val)) = true :=
      hG.2.2.1 p l hpl
    by_cases hlt_j : jp < jl
    · exact no_earlier_and_reader hq hG hp_lt hl_lt hpl_ne hpair_pl hjp hjl hlt_j
        hjp_and hjp_reads hjp_uniq hjl_uniq
    · by_cases hgt_j : jl < jp
      · have hpair_lp : wireVal (N + N) gs out (fun u => decide (u = N + l.val ∨ u = p.val)) = true := by
          convert hpair_pl using 2; ext u; simp [or_comm]
        exact no_earlier_and_reader hq hG hl_lt hp_lt hpl_ne.symm hpair_lp hjl hjp hgt_j
          hjl_and hjl_reads hjl_uniq hjp_uniq
      · -- jp = jl
        have hjeq : jp = jl := by omega
        subst hjeq
        obtain ⟨l', hl'ne, hpl'⟩ := plane_point_two_lines hq hN hline huniq p l hpl
        let zU : ℕ → Bool := fun u => decide (u = N + l'.val)
        let zP : ℕ → Bool := fun u => decide (u = p.val ∨ u = N + l'.val)
        have hout_u : wireVal (N + N) gs out zU = false := good_unit_false hq hG (N + l'.val) (by omega)
        have hout_p : wireVal (N + N) gs out zP = true := hG.2.2.1 p l' hpl'
        have ha_p : wireVal (N + N) gs (N + N + jp) zP = true := by
          cases ha : wireVal (N + N) gs (N + N + jp) zP with
          | true => rfl
          | false =>
            have ha_u : wireVal (N + N) gs (N + N + jp) zU = false := by
              cases h2 : wireVal (N + N) gs (N + N + jp) zU with
              | false => rfl
              | true =>
                have hm := wireVal_mono hG.1 (z1 := zU) (z2 := zP)
                  (fun i _ hi => by simp only [zU, decide_eq_true_eq] at hi; simp [zP, hi])
                  (N + N + jp) (by omega) h2
                rw [ha] at hm; cases hm
            have heq := orChain_reader_dom hG.1 hp_lt hjp hjp_uniq (z1 := zU) (z2 := zP)
              (fun i _ hi => by simp [zU, zP, hi])
              (ha_u.trans ha.symm)
              out hG.2.1 (out_not_mem_orChain hq hG hp_lt)
            rw [hout_u, hout_p] at heq; cases heq
        -- Therefore orTop (N + N) gs (N + l.val) is true at zP
        rw [wireVal_gate hG.1 hjp zP, hjp_and] at ha_p
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ha_p
        have htopl_p : wireVal (N + N) gs (orTop (N + N) gs (N + l.val)) zP = true := by
          rcases hjl_reads with ⟨h, _⟩ | ⟨_, h⟩
          · rw [← h]; exact ha_p.1
          · rw [← h]; exact ha_p.2
        have htopl_lt : orTop (N + N) gs (N + l.val) < N + N + jp := by
          have hwfj := hG.1 jp hjp
          rcases hjl_reads with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
        have htopl_not_chp : orTop (N + N) gs (N + l.val) ∉ orChain (N + N) gs p.val := by
          intro hmem
          exact orChain_disjoint hq hN hline huniq hG hp_lt hl_lt hpl_ne hmem
            (orChain_props hG.1 hl_lt).2.1
        have htopl_u : wireVal (N + N) gs (orTop (N + N) gs (N + l.val)) zU = true := by
          have heq := orChain_indep_lt_reader hG.1 hp_lt hjp hjp_uniq (z1 := zU) (z2 := zP)
            (fun i _ hi => by simp [zU, zP, hi])
            (orTop (N + N) gs (N + l.val)) htopl_lt htopl_not_chp
          rw [heq]; exact htopl_p
        -- Now evaluate at z_{l'} vs update z_{l'} (N + l.val) true
        let zl' : ℕ → Bool := fun u =>
          if h : u < N then decide (∀ l0 ∈ ({l'} : Finset (Fin N)), ¬ I ⟨u, h⟩ l0)
          else if h2 : u < N + N then decide (⟨u - N, by omega⟩ ∈ ({l'} : Finset (Fin N)))
          else false
        have htopl_zl' : wireVal (N + N) gs (orTop (N + N) gs (N + l.val)) zl' = true := by
          exact wireVal_mono hG.1 (z1 := zU) (z2 := zl')
            (fun i hi h1 => by
              simp only [zU, decide_eq_true_eq] at h1; subst h1
              simp [zl', Nat.not_lt.mpr (Nat.le_add_right N l'.val), hi])
            (orTop (N + N) gs (N + l.val)) (orChain_props hG.1 hl_lt).2.2.1 htopl_u
        have htopl_zl'2 : wireVal (N + N) gs (orTop (N + N) gs (N + l.val))
            (Function.update zl' (N + l.val) true) = true := by
          exact wireVal_mono hG.1 (z1 := zl') (z2 := Function.update zl' (N + l.val) true)
            (fun i _ hi => by
              by_cases h : i = N + l.val
              · subst h; simp
              · rw [Function.update_of_ne h]; exact hi)
            (orTop (N + N) gs (N + l.val)) (orChain_props hG.1 hl_lt).2.2.1 htopl_zl'
        have hout_zl' : wireVal (N + N) gs out zl' = false :=
          good_zL_val hG {l'} (by simp; omega)
        obtain ⟨p', hp'l, hp'l'⟩ := plane_line_diff_nonempty hq hline huniq hl'ne.symm
        have hout_zl'2 : wireVal (N + N) gs out (Function.update zl' (N + l.val) true) = true := by
          exact wireVal_mono hG.1
            (fun i _ hi => by
              simp only [decide_eq_true_eq] at hi
              rcases hi with rfl | rfl
              · have hneq : p'.val ≠ N + l.val := by omega
                rw [Function.update_of_ne hneq]
                simp [zl', p'.isLt, hp'l']
              · simp)
            out hG.2.1 (hG.2.2.1 p' l hp'l)
        have heq := orChain_dom hG.1 hl_lt (orChain_props hG.1 hl_lt).2.1
          (z1 := zl') (z2 := Function.update zl' (N + l.val) true)
          (fun i _ hi => (Function.update_of_ne hi true zl').symm)
          (htopl_zl'.trans htopl_zl'2.symm)
          out hG.2.1 (Or.inl (out_not_mem_orChain hq hG hl_lt))
        rw [hout_zl', hout_zl'2] at heq; cases heq
  have hUand_card : Uand.card ≤ N := by
    have hle := plane_indep_le hq hN hline huniq UP UL hUand_indep
    have heq_set : Uand = UP.image Fin.val ∪ UL.image (fun l : Fin N => N + l.val) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, UP, UL, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hw
        have hwlt : w < N + N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
        by_cases hlt : w < N
        · exact Or.inl ⟨⟨w, hlt⟩, hw, rfl⟩
        · exact Or.inr ⟨⟨w - N, by omega⟩, by simpa [Nat.add_sub_of_le (Nat.not_lt.mp hlt)] using hw, by dsimp only; omega⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
        · exact hp
        · exact hl
    have hdisj_img : Disjoint (UP.image Fin.val) (UL.image (fun l : Fin N => N + l.val)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨p, _, rfl⟩
      rcases h2 with ⟨l, _, h⟩
      omega
    have hcard_eq : Uand.card = UP.card + UL.card := by
      rw [heq_set, Finset.card_union_of_disjoint hdisj_img,
          Finset.card_image_of_injective _ Fin.val_injective,
          Finset.card_image_of_injective _ (fun a b hab => Fin.ext (by omega))]
    omega
  -- Fanout sum accounting
  have hsum_all := sum_fanout_eq (N + N) gs hG.1
  let Gates := (Finset.range gs.length).image (fun j => N + N + j)
  have hrange_split : Finset.range (N + N + gs.length) = Inputs ∪ Gates := by
    ext w
    simp only [Finset.mem_range, Finset.mem_union, Inputs, Gates, Finset.mem_image]
    constructor
    · intro hw
      by_cases hlt : w < N + N
      · exact Or.inl hlt
      · exact Or.inr ⟨w - (N + N), by omega, by omega⟩
    · rintro (h | ⟨j, hj, rfl⟩) <;> omega
  have hdisj_IG : Disjoint Inputs Gates := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Inputs, Gates, Finset.mem_range, Finset.mem_image] at h1 h2
    rcases h2 with ⟨j, _, rfl⟩; omega
  rw [hrange_split, Finset.sum_union hdisj_IG] at hsum_all
  -- Lower bound on Inputs sum
  have hsum_in : U1.card + 2 * Uge2.card ≤ ∑ w ∈ Inputs, fanout gs w := by
    rw [← hInputs_union, Finset.sum_union hInputs_disj]
    have h1 : U1.card ≤ ∑ w ∈ U1, fanout gs w := by
      have := Finset.sum_le_sum (s := U1) (f := fun _ => 1) (g := fanout gs)
        (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega)
      simpa using this
    have h2 : 2 * Uge2.card ≤ ∑ w ∈ Uge2, fanout gs w := by
      have := Finset.sum_le_sum (s := Uge2) (f := fun _ => 2) (g := fanout gs)
        (fun w hw => (Finset.mem_filter.mp hw).2)
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    omega
  -- Lower bound on Gates sum
  let GatesNe := Gates.erase out
  let TopBranch := Ubranch.image (orTop (N + N) gs)
  have hout_mem_Gates : out ∈ Gates := by
    simp only [Gates, Finset.mem_image, Finset.mem_range]
    exact ⟨out - (N + N), by have := hG.2.1; omega, by omega⟩
  have hGates_card : Gates.card = gs.length := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  have hGatesNe_card : GatesNe.card = gs.length - 1 := by
    rw [Finset.card_erase_of_mem hout_mem_Gates, hGates_card]
  have hTopBranch_sub : TopBranch ⊆ GatesNe := by
    intro g hg
    simp only [TopBranch, Finset.mem_image] at hg
    rcases hg with ⟨w, hw, rfl⟩
    have hwU1 : w ∈ U1 := (Finset.mem_filter.mp hw).1
    have hwlt : w < N + N := Finset.mem_range.mp (Finset.mem_filter.mp hwU1).1
    have hfw1 : fanout gs w = 1 := (Finset.mem_filter.mp hwU1).2
    have hftop2 : 2 ≤ fanout gs (orTop (N + N) gs w) := (Finset.mem_filter.mp hw).2
    have htop_ne_w : orTop (N + N) gs w ≠ w := by intro h; rw [h] at hftop2; omega
    have htop_ge : N + N ≤ orTop (N + N) gs w :=
      ((orChain_props hG.1 hwlt).2.2.2.2.2.1 _ (orChain_props hG.1 hwlt).2.1 htop_ne_w).1
    have htop_lt := (orChain_props hG.1 hwlt).2.2.1
    rw [Finset.mem_erase]
    refine ⟨htop_ne_out w hwlt, ?_⟩
    simp only [Gates, Finset.mem_image, Finset.mem_range]
    exact ⟨orTop (N + N) gs w - (N + N), by omega, by omega⟩
  have hTopBranch_card : TopBranch.card = Ubranch.card := by
    apply Finset.card_image_of_injOn
    intro w1 hw1 w2 hw2 heq
    have hw1lt : w1 < N + N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw1).1).1
    have hw2lt : w2 < N + N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw2).1).1
    exact htop_inj w1 hw1lt w2 hw2lt heq
  have hsum_gates : Ubranch.card + (gs.length - 1) ≤ ∑ g ∈ Gates, fanout gs g := by
    have hle1 : ∑ g ∈ GatesNe, fanout gs g ≤ ∑ g ∈ Gates, fanout gs g :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset out Gates)
    have hsplit_G : ∑ g ∈ GatesNe, fanout gs g =
        (∑ g ∈ TopBranch, fanout gs g) + (∑ g ∈ GatesNe \ TopBranch, fanout gs g) := by
      rw [← Finset.sum_sdiff hTopBranch_sub, add_comm]
    have htb : 2 * TopBranch.card ≤ ∑ g ∈ TopBranch, fanout gs g := by
      have := Finset.sum_le_sum (s := TopBranch) (f := fun _ => 2) (g := fanout gs)
        (fun g hg => by
          simp only [TopBranch, Finset.mem_image] at hg
          rcases hg with ⟨w, hw, rfl⟩
          exact (Finset.mem_filter.mp hw).2)
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have hrest : (GatesNe \ TopBranch).card ≤ ∑ g ∈ GatesNe \ TopBranch, fanout gs g := by
      have := Finset.sum_le_sum (s := GatesNe \ TopBranch) (f := fun _ => 1) (g := fanout gs)
        (fun g hg => by
          have hgNe : g ∈ GatesNe := (Finset.mem_sdiff.mp hg).1
          rw [Finset.mem_erase] at hgNe
          simp only [Gates, Finset.mem_image, Finset.mem_range] at hgNe
          rcases hgNe.2 with ⟨j, hj, rfl⟩
          have hnz := hmin j hj hgNe.1
          omega)
      simpa using this
    have hsdiff_card : (GatesNe \ TopBranch).card = GatesNe.card - TopBranch.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTopBranch_sub]
    have hcard_le : TopBranch.card ≤ GatesNe.card := Finset.card_le_card hTopBranch_sub
    omega
  omega

end PEqualNP.Outside.L_meta_3763_aux

open PEqualNP.Outside.L_meta_3763_aux in
theorem PEqualNP.Outside.L_meta_3763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) := by
  intro q N I _ hq hN hline huniq m outIdx S houtIdx hinit hstep hpos hneg
  obtain ⟨gs0, env, hlen0, hwf0, henv0⟩ := set_to_circuit hinit hstep m le_rfl
  have hNpos : 0 < N := by omega
  have hex_inc : ∃ p l : Fin N, I p l := by
    let l0 : Fin N := ⟨0, hNpos⟩
    have hcard : 0 < (Finset.univ.filter (fun p : Fin N => I p l0)).card := by
      have := hline l0; rw [Fintype.card_subtype] at this; omega
    obtain ⟨p0, hp0⟩ := Finset.card_pos.mp hcard
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp0
    exact ⟨p0, l0, hp0⟩
  have hspec := henv0 outIdx houtIdx
  cases he : env outIdx with
  | none =>
    rw [he] at hspec
    obtain ⟨p0, l0, hpl0⟩ := hex_inc
    obtain ⟨M, hM, hzM⟩ := hspec (fun u => decide (u = p0.val ∨ u = N + l0.val))
    rcases hpos M hM p0 l0 hpl0 with h1 | h2
    · have := hzM p0.val h1; simp at this
    · have := hzM (N + l0.val) h2; simp at this
  | some out0 =>
    rw [he] at hspec
    have hG0 : Good (q := q) I gs0 out0 := by
      refine ⟨hwf0, hspec.1, ?_, ?_⟩
      · intro p l hpl
        cases hval : wireVal (N + N) gs0 out0 (fun u => decide (u = p.val ∨ u = N + l.val)) with
        | true => rfl
        | false =>
          obtain ⟨M, hM, hzM⟩ := (hspec.2 _).mp hval
          rcases hpos M hM p l hpl with h1 | h2
          · have := hzM p.val h1; simp at this
          · have := hzM (N + l.val) h2; simp at this
      · intro L hL
        rw [hspec.2]
        obtain ⟨M, hM, hMprop⟩ := hneg L hL
        refine ⟨M, hM, fun u hu => ?_⟩
        by_cases h1 : u < N
        · simp only [h1, ↓reduceDIte, decide_eq_false_iff_not, not_forall, not_not]
          rcases (hMprop ⟨u, h1⟩).1.mp hu with ⟨l, hl, hil⟩
          exact ⟨l, hl, hil⟩
        · by_cases h2 : u < N + N
          · simp only [h1, h2, ↓reduceDIte, decide_eq_false_iff_not]
            have hu' : N + (⟨u - N, by omega⟩ : Fin N).val ∈ M := by simpa [Nat.add_sub_of_le (Nat.not_lt.mp h1)] using hu
            exact (hMprop ⟨u - N, by omega⟩).2.mp hu'
          · simp [h1, h2]
    classical
    have hex : ∃ k : ℕ, ∃ (gs : List (Bool × ℕ × ℕ)) (out : ℕ), gs.length = k ∧ Good (q := q) I gs out :=
      ⟨gs0.length, gs0, out0, rfl, hG0⟩
    let kmin := Nat.find hex
    have hkmin_le : kmin ≤ gs0.length := Nat.find_min' hex ⟨gs0, out0, rfl, hG0⟩
    obtain ⟨gs, out, hglen, hG⟩ := Nat.find_spec hex
    have hmin : ∀ k < gs.length, N + N + k ≠ out → fanout gs (N + N + k) ≠ 0 := by
      intro k hk hne hdead
      have hdel := deleteGate_spec hG.1 hG.2.1 hk (Ne.symm hne) hdead
      have hG' : Good (q := q) I (deleteGate (N + N) gs k) (shiftIdx (N + N + k) out) := by
        refine ⟨hdel.2.1, hdel.2.2.1, ?_, ?_⟩
        · intro p l hpl
          rw [hdel.2.2.2]; exact hG.2.2.1 p l hpl
        · intro L hL
          rw [hdel.2.2.2]; exact hG.2.2.2 L hL
      have hlt_kmin : (deleteGate (N + N) gs k).length < kmin := by omega
      exact Nat.find_min hex hlt_kmin ⟨deleteGate (N + N) gs k, shiftIdx (N + N + k) out, rfl, hG'⟩
    have hbound := good_size_bound hq hN hline huniq hG hmin
    omega
