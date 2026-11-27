import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7730

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value w g]) w

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [value w g])
    exact ⟨value w g :: t, by
      change run gs (w ++ [value w g]) = _
      rw [ht, List.append_assoc]
      rfl, by simp [hl]⟩

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_before (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_take (gs : List Gate) (w : List Bool) {j i : ℕ}
    (hj : j ≤ gs.length) (hi : i < w.length + j) :
    (run (gs.take j) w).getD i false = (run gs w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_before _ _ _ (by simpa [run_length, List.length_take, min_eq_left hj])).symm

lemma gateAt_eq (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

lemma split_gate (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) = C.gates := by
  rw [gateAt_eq C hj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

lemma value_prefix (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hj : j ≤ C.gates.length) (g : Gate) (hb : ∀ i ∈ g.inputs, i < n + j) :
    value (run (C.gates.take j) xs) g = value (C.wires xs) g := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_take _ _ hj (by rw [hx]; exact hb i hi)

lemma wire_gate (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hr : ReadsBack n C) (hj : j < C.gates.length) :
    (C.wires xs).getD (n + j) false = value (C.wires xs) (gateAt C j) := by
  let w := run (C.gates.take j) xs
  let b := value w (gateAt C j)
  have hl : w.length = n + j := by
    simp [w, run_length, hx, List.length_take, min_eq_left (Nat.le_of_lt hj)]
  have he : C.wires xs = run (C.gates.drop (j + 1)) (w ++ [b]) := by
    change run C.gates xs = _
    conv_lhs => rw [← split_gate C hj, run_append]
    rfl
  calc
    _ = (w ++ [b]).getD (n + j) false := by
      rw [he, run_before _ _ _ (by simp [hl])]
    _ = b := by rw [← hl]; simp
    _ = _ := value_prefix C xs hx hj.le _ (hr j hj)

def clean (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .not →
    ∃ w, (gateAt C j).inputs.head? = some w ∧
      (∀ k < j, w = n + k → (gateAt C k).op ≠ .not) ∧
      ∀ k < j, (gateAt C k).op = .not → (gateAt C k).inputs.head? ≠ some w

lemma replacement (C : Circuit) {n j : ℕ} (hr : ReadsBack n C)
    (hj : j < C.gates.length) (hn : (gateAt C j).op = .not)
    (hbad : ¬ ∃ w, (gateAt C j).inputs.head? = some w ∧
      (∀ k < j, w = n + k → (gateAt C k).op ≠ .not) ∧
      ∀ k < j, (gateAt C k).op = .not → (gateAt C k).inputs.head? ≠ some w) :
    ∃ g : Gate, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 ∧
      (∀ i ∈ g.inputs, i < n + j) ∧
      ∀ xs : List Bool, xs.length = n →
        value (C.wires xs) g = value (C.wires xs) (gateAt C j) := by
  classical
  cases hjw : (gateAt C j).inputs with
  | nil =>
    exact ⟨⟨.and, []⟩, Or.inl rfl, by simp, by simp,
      fun xs _ => by simp [value, hn, hjw, GateOp.eval]⟩
  | cons w ws =>
    by_cases hd : ∃ k < j, w = n + k ∧ (gateAt C k).op = .not
    · obtain ⟨k, hk, hw, hkn⟩ := hd
      have hkC : k < C.gates.length := hk.trans hj
      cases hku : (gateAt C k).inputs with
      | nil =>
        refine ⟨⟨.or, []⟩, Or.inr rfl, by simp, by simp, ?_⟩
        intro xs hx
        have hv := wire_gate C xs hx hr hkC
        simp [value, hkn, hku, GateOp.eval] at hv
        simp [value, hn, hjw, GateOp.eval, hw, hv]
      | cons u us =>
        have hu := hr k hkC u (by simp [hku])
        refine ⟨⟨.or, [u]⟩, Or.inr rfl, by simp, ?_, ?_⟩
        · intro i hi
          simp at hi
          omega
        · intro xs hx
          have hv := wire_gate C xs hx hr hkC
          simp [value, hkn, hku, GateOp.eval] at hv
          simp [value, hn, hjw, GateOp.eval, hw, hv]
    · have dup : ∃ k < j, (gateAt C k).op = .not ∧
          (gateAt C k).inputs.head? = some w := by
        by_contra h
        exact hbad ⟨w, by simp [hjw], fun k hk hw hn' => hd ⟨k, hk, hw, hn'⟩,
          fun k hk hn' hw => h ⟨k, hk, hn', hw⟩⟩
      obtain ⟨k, hk, hkn, hkw⟩ := dup
      refine ⟨⟨.or, [n + k]⟩, Or.inr rfl, by simp, ?_, ?_⟩
      · intro i hi
        simp at hi
        omega
      · intro xs hx
        have hv := wire_gate C xs hx hr (hk.trans hj)
        cases hic : (gateAt C k).inputs with
        | nil => simp [hic] at hkw
        | cons u us =>
          have h : u = w := by simpa [hic] using hkw
          simp [value, hkn, hic, h, GateOp.eval] at hv
          simp [value, hn, hjw, GateOp.eval, hv]

def edit (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma edit_gate (C : Circuit) (j : ℕ) (g : Gate) {k : ℕ}
    (hk : k < C.gates.length) :
    gateAt (edit C j g) k = if j = k then g else gateAt C k := by
  have he : k < (edit C j g).gates.length := by simpa [edit]
  rw [gateAt_eq _ he, gateAt_eq _ hk]
  by_cases h : j = k
  · subst k
    simp [edit]
  · simp [edit, h, List.getElem_set_ne]

lemma edit_spec (C : Circuit) {n j : ℕ} (hf : FanInTwo C) (hr : ReadsBack n C)
    (hj : j < C.gates.length) (hn : (gateAt C j).op = .not) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hb : ∀ i ∈ g.inputs, i < n + j)
    (hv : ∀ xs : List Bool, xs.length = n →
      value (C.wires xs) g = value (C.wires xs) (gateAt C j)) :
    FanInTwo (edit C j g) ∧ ReadsBack n (edit C j g) ∧
      notCount (edit C j g) < notCount C ∧
      ∀ xs : List Bool, xs.length = n → (edit C j g).eval xs = C.eval xs := by
  have hlen' : (edit C j g).gates.length = C.gates.length := by simp [edit]
  have hs : (edit C j g).gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    simp [edit, List.set_eq_take_append_cons_drop, hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp ha
    have hk' : k < C.gates.length := by simpa only [hlen'] using hk
    rw [← he, ← gateAt_eq _ hk, edit_gate C j g hk']
    split
    · exact ⟨by simpa using Or.imp_right (fun h => Or.inl h) hop, hlen⟩
    · exact hf _ (by rw [gateAt_eq _ hk']; exact List.getElem_mem _)
  · intro k hk i hi
    have hk' : k < C.gates.length := by simpa only [hlen'] using hk
    rw [edit_gate C j g hk'] at hi
    split at hi
    · next h => exact h ▸ hb i hi
    · exact hr k hk' i hi
  · have hgn : g.op ≠ .not := by rcases hop with h | h <;> simp [h]
    unfold notCount
    conv_rhs => rw [← split_gate C hj]
    simp [hs, hn, hgn, List.filter_append]
  · intro xs hx
    have he : value (run (C.gates.take j) xs) g =
        value (run (C.gates.take j) xs) (gateAt C j) :=
      (value_prefix C xs hx hj.le g hb).trans
        ((hv xs hx).trans (value_prefix C xs hx hj.le _ (hr j hj)).symm)
    change (run (edit C j g).gates xs).getD C.output false =
      (run C.gates xs).getD C.output false
    conv_rhs => rw [← split_gate C hj, run_append]
    rw [hs, run_append]
    change (run (C.gates.drop (j + 1)) (run (C.gates.take j) xs ++
      [value (run (C.gates.take j) xs) g])).getD C.output false = _
    rw [he]
    rfl

lemma normalize (n : ℕ) (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack n C) :
    ∃ D : Circuit, FanInTwo D ∧ ReadsBack n D ∧ D.size = C.size ∧
      D.output = C.output ∧ notCount D ≤ notCount C ∧ clean n D ∧
      ∀ xs : List Bool, xs.length = n → D.eval xs = C.eval xs := by
  classical
  generalize hm : notCount C = m
  induction m using Nat.strong_induction_on generalizing C with
  | ind m ih =>
    by_cases hc : clean n C
    · exact ⟨C, hf, hr, rfl, rfl, hm.le, hc, fun _ _ => rfl⟩
    · obtain ⟨j, hj, hn, hbad⟩ : ∃ (j : ℕ) (_ : j < C.gates.length) (_ : (gateAt C j).op = .not),
          ¬ ∃ w, (gateAt C j).inputs.head? = some w ∧
            (∀ k < j, w = n + k → (gateAt C k).op ≠ .not) ∧
            ∀ k < j, (gateAt C k).op = .not → (gateAt C k).inputs.head? ≠ some w := by
        simpa only [clean, not_forall, not_imp] using hc
      obtain ⟨g, hop, hl, hb, hv⟩ := replacement C hr hj hn hbad
      obtain ⟨hf', hr', hm', hv'⟩ := edit_spec C hf hr hj hn g hop hl hb hv
      obtain ⟨D, hD, hR, hS, hO, hM, hC, hV⟩ :=
        ih _ (hm ▸ hm') (edit C j g) hf' hr' rfl
      refine ⟨D, hD, hR, ?_, hO, hM.trans (hm'.le.trans hm.le), hC,
        fun xs hx => (hV xs hx).trans (hv' xs hx)⟩
      simpa [edit, Circuit.size] using hS

lemma finish (n : ℕ) (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack n C)
    (ho : n ≤ C.output) (hs : C.output < n + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      D.output = C.output ∧ D.output + 1 = n + D.size ∧
      notCount D ≤ notCount C ∧ clean n D ∧
      ∀ xs : List Bool, xs.length = n → D.eval xs = C.eval xs := by
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by unfold k; change C.output < n + C.gates.length at hs; omega
  have hnk : n + k = C.output + 1 := by unfold k; omega
  let T : Circuit := ⟨C.gates.take k, C.output⟩
  have ht : T.size = k := by simp [T, Circuit.size, List.length_take, min_eq_left hk]
  have hsub := List.take_sublist k C.gates
  have htF : FanInTwo T := fun g hg => hf g (hsub.subset hg)
  have htR : ReadsBack n T := by
    intro j hj i hi
    have hj' : j < C.gates.length := by
      change j < T.size at hj
      omega
    have he : gateAt T j = gateAt C j := by
      rw [gateAt_eq T hj, gateAt_eq C hj']
      exact List.getElem_take
    exact hr j hj' i (he ▸ hi)
  obtain ⟨D, hdF, hdR, hdS, hdO, hdM, hdC, hdV⟩ := normalize n T htF htR
  have hout : D.output = C.output := hdO
  refine ⟨D, hdF, hdR, by rw [hdS, ht]; exact hk, hout, by rw [hout, hdS, ht, hnk],
    hdM.trans (hsub.filter _).length_le, hdC, ?_⟩
  intro xs hx
  refine (hdV xs hx).trans ?_
  exact run_take _ _ hk (by rw [hx, hnk]; omega)

end PEqualNP.Outside.L_meta_7730


theorem PEqualNP.Outside.L_meta_7730 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size ≤ x2.size ∧ x7.output = x2.output ∧ x7.output + (1 : ℕ) = x1 + x7.size ∧ PEqualNP.NotBracket.notCount x7 ≤ PEqualNP.NotBracket.notCount x2 ∧ (∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs.head? = Option.some x11 ∧ (∀ x12 < x8, x11 = x1 + x12 → (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ x12 < x8, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs.head? ≠ Option.some x11) ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = x2.eval x8 := by
  exact PEqualNP.Outside.L_meta_7730.finish
