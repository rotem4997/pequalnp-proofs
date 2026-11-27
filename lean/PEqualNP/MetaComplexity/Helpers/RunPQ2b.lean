import PEqualNP.MetaComplexity.Helpers.RunPQ2

/-!
# The q2 side, stage 2: tracking `passG` against the source list

Conjecture until the checker accepts. For the pass `elim` of `Elim.lean` (the cleaning at one
fixed input), a gate position `p` of the source list that emits a gate lands at position
`pq2E p` (the number of gates emitted by the earlier positions) of the emitted list, with its
operation kept and its operands mapped through the final statuses; and every emitted gate
comes from such a position.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem pq2_elim_snoc (n : ℕ) (gs : List Gate) (g : Gate) (acc : List Stat × List Gate) :
    elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
  simp [elim, List.foldl_append]

/-- Every emitted gate comes from a source position (or was emitted before). -/
theorem pq2_src (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∀ (k : ℕ) (g' : Gate), (elim n gs acc).2[k]? = some g' → k < acc.2.length ∨
      ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ (elim n (gs.take p) acc).2.length = k ∧
        (simplify g.op (n + k) (g.inputs.map fun a =>
          (elim n (gs.take p) acc).1.getD a (Stat.const false))).1 = some g' := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k g' h
    left
    have : (elim n [] acc).2 = acc.2 := rfl
    rw [this] at h
    exact (List.getElem?_eq_some_iff.1 h).1
  | append_singleton gs g ih =>
    intro k g' h
    rw [pq2_elim_snoc] at h
    have hs : (elimStep n (elim n gs acc) g).2 = (elim n gs acc).2 ++
        (simplify g.op (n + (elim n gs acc).2.length) (g.inputs.map fun a =>
          (elim n gs acc).1.getD a (Stat.const false))).1.toList := rfl
    rw [hs] at h
    by_cases hk : k < (elim n gs acc).2.length
    · rw [List.getElem?_append_left hk] at h
      rcases ih k g' h with h1 | ⟨p, g0, hp, hl, hsim⟩
      · exact Or.inl h1
      · right
        have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
        refine ⟨p, g0, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_left hpl]; exact hp
        · rw [List.take_append_of_le_length (by omega)]; exact hl
        · rw [List.take_append_of_le_length (by omega)]; exact hsim
    · rw [List.getElem?_append_right (by omega)] at h
      right
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ h
      have hk' : k = (elim n gs acc).2.length := by
        have := (List.getElem?_eq_some_iff.1 h).1
        simp at this; omega
      refine ⟨gs.length, g, by simp, ?_, ?_⟩
      · rw [List.take_left]; omega
      · rw [List.take_left, hk']
        simpa using hmem

theorem pq2_snd_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length) (g.inputs.map fun a =>
      acc.1.getD a (Stat.const false))).1.toList ++ t, ?_⟩
    rw [elim_cons, ht]
    show (acc.2 ++ _) ++ t = _
    simp

/-- The number of gates emitted by the source positions before `p`. -/
def pq2E (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : ℕ :=
  (elim n (gs.take p) (statAt n i b, [])).2.length

/-- A source gate at `p` that emits a gate `g'` puts it at position `pq2E p` of `passG`, and the
status of its wire is what `simplify` makes of the final statuses of its operands. -/
theorem pq2_emit (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    stF n gs i b (n + 1 + p) =
        (simplify g.op (n + pq2E n gs i b p) (g.inputs.map (stF n gs i b))).2 ∧
      ∀ g', (simplify g.op (n + pq2E n gs i b p) (g.inputs.map (stF n gs i b))).1 = some g' →
        (passG n gs i b)[pq2E n gs i b p]? = some g' := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, hgs, hpre⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have htake : gs.take p = pre := by
    rw [hgs, ← hpre, List.take_left]
  have hmap : g.inputs.map (stF n gs i b) = g.inputs.map fun a =>
      (elim n pre (statAt n i b, [])).1.getD a (Stat.const false) := by
    apply List.map_congr_left
    intro a ha
    have hal := hlt a ha
    show (elim n gs (statAt n i b, [])).1.getD a _ = _
    rw [hgs, elim_split_getD_lt n pre g post _ a _ (by rw [hL]; omega)]
  have hE : pq2E n gs i b p = (elim n pre (statAt n i b, [])).2.length := by
    unfold pq2E; rw [htake]
  rw [hmap, hE]
  constructor
  · have e1 : stF n gs i b (n + 1 + p)
        = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + p) (Stat.const false) := by
      show (elim n gs (statAt n i b, [])).1.getD _ _ = _
      rw [hgs, ← hpre]
      exact elim_split_getD n pre g post _ _ _ (by rw [hL])
    rw [e1]
    exact getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL, hpre])
  · intro g' hg'
    obtain ⟨t, ht⟩ := pq2_snd_prefix n post (elimStep n (elim n pre (statAt n i b, [])) g)
    have : (passG n gs i b) = ((elim n pre (statAt n i b, [])).2 ++
        (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length) (g.inputs.map fun a =>
          (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).1.toList) ++ t := by
      unfold passG
      rw [hgs, elim_append, elim_cons, ht]
      rfl
    rw [this, hg']
    simp [List.getElem?_append_left, List.getElem?_append_right]

/-- An emitted gate keeps the operation, reads statuses that are wires, and has status the new wire. -/
theorem pq2_simplify_shape (op : GateOp) (m : ℕ) (ins : List Stat) (g' : Gate)
    (h : (simplify op m ins).1 = some g') :
    g'.op = op ∧ (∀ j ∈ g'.inputs, Stat.wire j ∈ ins) ∧ (simplify op m ins).2 = Stat.wire m := by
  cases op <;> simp only [simplify] at h ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h
    subst h
    simp [simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h
    subst h
    simp [simpOr]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at h
    subst h
    simp [simpNot]
  · simp at h
  · simp at h

/-- The statuses of the operands at a source position are the final statuses. -/
theorem pq2_inputs_stat (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    g.inputs.map (stF n gs i b) = g.inputs.map fun a =>
      (elim n (gs.take p) (statAt n i b, [])).1.getD a (Stat.const false) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, hgs, hpre⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have htake : gs.take p = pre := by
    rw [hgs, ← hpre, List.take_left]
  rw [htake]
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  show (elim n gs (statAt n i b, [])).1.getD a _ = _
  rw [hgs, elim_split_getD_lt n pre g post _ a _ (by rw [hL]; omega)]

/-- A reader in `passG` of a wire comes from a source gate of the same operation at the position
`pq2E`, one of whose operands has final status that wire. -/
theorem pq2_reader (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (k : ℕ) (g' : Gate) (hk : (passG n gs i b)[k]? = some g') (j : ℕ)
    (hj : j ∈ g'.inputs) :
    ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ pq2E n gs i b p = k ∧ g'.op = g.op ∧
      stF n gs i b (n + 1 + p) = Stat.wire (n + k) ∧
      ∃ a ∈ g.inputs, stF n gs i b a = Stat.wire j := by
  rcases pq2_src n gs (statAt n i b, []) k g' hk with h | ⟨p, g, hp, hl, hsim⟩
  · simp at h
  · have hE : pq2E n gs i b p = k := hl
    have hst := pq2_inputs_stat n gs hcl i b p g hp
    rw [← hst] at hsim
    obtain ⟨hop, hin, hs2⟩ := pq2_simplify_shape _ _ _ _ hsim
    refine ⟨p, g, hp, hE, hop, ?_, ?_⟩
    · rw [(pq2_emit n gs hcl i b p g hp).1, hE, hs2]
    · obtain ⟨s, hs, hsw⟩ := List.mem_map.1 (hin j hj)
      exact ⟨s, hs, hsw⟩

/-- A source gate that emits sits at `pq2E p` of `passG` with its operation kept and its operands
mapped (binary form). -/
theorem pq2_kept_bin (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a1 a2 : ℕ)
    (hin : g.inputs = [a1, a2]) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j1 j2 : ℕ)
    (h1 : stF n gs i b a1 = Stat.wire j1) (h2 : stF n gs i b a2 = Stat.wire j2) :
    stF n gs i b (n + 1 + p) = Stat.wire (n + pq2E n gs i b p) ∧
      (passG n gs i b)[pq2E n gs i b p]? = some ⟨g.op, [j1, j2]⟩ := by
  obtain ⟨he1, he2⟩ := pq2_emit n gs hcl i b p g hp
  rw [hin] at he1 he2
  simp only [List.map_cons, List.map_nil, h1, h2] at he1 he2
  rcases hop with h | h <;> rw [h] at he1 he2 ⊢ <;> simp [simplify, simpAnd, simpOr] at he1 he2 ⊢
  · exact ⟨he1, he2⟩
  · exact ⟨he1, he2⟩

theorem pq2_E_mono (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) {p p' : ℕ}
    (h : p ≤ p') : pq2E n gs i b p ≤ pq2E n gs i b p' := by
  unfold pq2E
  have e : gs.take p' = gs.take p ++ (gs.take p').drop p := by
    have := List.take_append_drop p (gs.take p')
    rw [List.take_take, min_eq_left h] at this
    exact this.symm
  obtain ⟨t, ht⟩ := pq2_snd_prefix n ((gs.take p').drop p) (elim n (gs.take p) (statAt n i b, []))
  rw [e, elim_append, ht]
  simp

/-- A source gate that emits raises the count by one. -/
theorem pq2_E_succ (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (g' : Gate)
    (h : (simplify g.op (n + pq2E n gs i b p) (g.inputs.map (stF n gs i b))).1 = some g') :
    pq2E n gs i b (p + 1) = pq2E n gs i b p + 1 := by
  have hst := pq2_inputs_stat n gs hcl i b p g hp
  have htk : gs.take (p + 1) = gs.take p ++ [g] := by
    rw [List.take_succ, hp]; rfl
  unfold pq2E at h ⊢
  rw [hst] at h
  rw [htk, pq2_elim_snoc]
  show ((elim n (gs.take p) (statAt n i b, [])).2 ++ _).length = _
  rw [List.length_append, h]
  simp

/-- Distinct emitting positions land at distinct emitted positions. -/
theorem pq2_E_lt (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p p' : ℕ) (g : Gate) (hp : gs[p]? = some g) (g' : Gate)
    (h : (simplify g.op (n + pq2E n gs i b p) (g.inputs.map (stF n gs i b))).1 = some g')
    (hpp : p < p') : pq2E n gs i b p < pq2E n gs i b p' := by
  have h1 := pq2_E_succ n gs hcl i b p g hp g' h
  have h2 := pq2_E_mono n gs i b (show p + 1 ≤ p' by omega)
  omega

end PEqualNP.MetaComplexity.Helpers.RunAsm
