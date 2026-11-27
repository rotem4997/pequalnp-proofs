import PEqualNP.MetaComplexity.Helpers.OneNotSplit

/-!
# Few NOT gates: splitting at the first NOT gate

Step 4 of the few-NOT build plan, generalizing `on1_split` (at most one NOT gate) to at most
`s` NOT gates, counted by indices: a map `ι : Fin s → Fin gates.length` whose image covers
every index holding a NOT gate (the form used by the few-NOT statement, since `GateOp` has no
decidable equality).

A gate list of AND, OR and NOT gates of fan-in at most two either has no NOT gate, or is
`pre ++ NOT ins :: post` with `pre` free of NOT gates; then `1 ≤ s`, and replacing the NOT
gate in place by `AND []` or by `OR []` keeps the gate condition and leaves at most `s - 1`
NOT gates, counted by indices in the same form.
-/

namespace PEqualNP.MetaComplexity.FewNot

open PEqualNP.CircuitLowerBounds

/-- Replacing one gate in place changes no other position. -/
theorem fn_split_getElem?_ne (pre post : List Gate) (a b : Gate) (i : ℕ)
    (hi : i ≠ pre.length) : (pre ++ b :: post)[i]? = (pre ++ a :: post)[i]? := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- The count by indices after an in-place replacement of a NOT gate by a gate that is not a
NOT gate: one index fewer. -/
theorem fn_split_count (t : ℕ) (pre post : List Gate) (a b : Gate)
    (hb : b.op ≠ GateOp.not)
    (ι : Fin (t + 1) → Fin (pre ++ a :: post).length)
    (hι : ∀ i : Fin (pre ++ a :: post).length, ((pre ++ a :: post).get i).op = GateOp.not →
      ∃ j : Fin (t + 1), ι j = i)
    (j0 : Fin (t + 1)) (hj0 : (ι j0).val = pre.length) :
    ∃ ι' : Fin t → Fin (pre ++ b :: post).length,
      ∀ i : Fin (pre ++ b :: post).length, ((pre ++ b :: post).get i).op = GateOp.not →
        ∃ j : Fin t, ι' j = i := by
  have hlen : (pre ++ b :: post).length = (pre ++ a :: post).length := by simp
  refine ⟨fun j => ⟨(ι (j0.succAbove j)).val, by have := (ι (j0.succAbove j)).isLt; omega⟩, ?_⟩
  intro i hi
  have hne : i.val ≠ pre.length := by
    intro h
    apply hb
    have : (pre ++ b :: post).get i = b := by
      simp only [List.get_eq_getElem, h, List.getElem_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem_cons_zero]
    rw [← this]; exact hi
  have hget : (pre ++ a :: post).get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ b :: post).get i := by
    have := fn_split_getElem?_ne pre post a b i.val hne
    simp only [List.get_eq_getElem]
    rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem (by have := i.isLt; omega)] at this
    exact (Option.some.inj this).symm
  obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
  have hjne : j ≠ j0 := by
    rintro rfl
    apply hne
    rw [← hj0, hj]
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjne
  refine ⟨j', ?_⟩
  apply Fin.ext
  simp only [hj]

/-- Step 4 of the few-NOT plan: the split at the first NOT gate, with the count of NOT gates
by indices dropping by one under either in-place replacement (`AND []` or `OR []`). -/
theorem fn_split_first : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      1 ≤ s ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ∨
          g' = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }) →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin (s - 1) → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin (s - 1), ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    have hs : 1 ≤ s := by
      rcases s with _ | t
      · exact j0.elim0
      · omega
    refine ⟨pre, post, (gates[k]).inputs, hsplit', ?_, hs, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg'
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with rfl | rfl <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h; rcases hg' with rfl | rfl <;> simp
          · exact hops g (by rw [hsplit]; simp [h])
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

/-- The split at the first NOT gate in the form of row L-meta-709: `s = s' + 1`, the NOT gate has
at most two inputs, and the in-place replacement may be any AND or OR gate with at most two
inputs, after which at most `s'` NOT gates remain, counted by indices. -/
theorem fn_split_general : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      s = s' + 1 ∧
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      ins.length ≤ 2 ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        g'.inputs.length ≤ 2 →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin s', ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
      rcases s with _ | t
      · exact j0.elim0
      · exact ⟨t, rfl⟩
    refine ⟨t, pre, post, (gates[k]).inputs, rfl, hsplit',
      (hops gates[k] (List.getElem_mem hk)).2, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg' hg'len
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with h | h <;> rw [h] <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h
            rcases hg' with h | h
            · exact ⟨Or.inl h, hg'len⟩
            · exact ⟨Or.inr (Or.inl h), hg'len⟩
          · exact hops g (by rw [hsplit]; simp [h])
      · have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ =
              (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

end PEqualNP.MetaComplexity.FewNot
