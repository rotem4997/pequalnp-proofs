import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# Tools for Theorem QA in circuit form (row L-meta-596): Fact E and tool W

Stated on root circuits (`Circuit.wires`, `circuitFun`), since the later steps apply them to
the least circuit `C` of the row itself, whose reader clauses are written on root gates. The
read relation is the one of the recorded statement: a NOT gate reads the head of its list, any
other gate reads every listed wire.

* `qa_val_gate`: the value of gate `j` is its operation on the earlier wires (a listed wire at
  or after its own position reads `false`).
* `qa_agree`: two inputs agree on every wire outside a bad set, as soon as the inputs agree
  there and every good gate maps agreeing earlier wires to the same value.
* `qa_factE` (P1), `qa_toolW_or` (P2), `qa_toolW_or_and` (P3).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- The read relation of the recorded statement: gate `g` reads wire `a`. -/
def qaReads (g : Gate) (a : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs)

theorem qa_getD_append_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  rw [List.getD_append _ _ _ _ h]

/-- The value of gate `j`. -/
theorem qa_val_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (wiresFrom gs w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (wiresFrom gs w).getD i false else false) := by
  have hjl : j < gs.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; exact absurd hj (by simp)
  have hg : gs[j] = g := by
    rw [List.getElem?_eq_getElem hjl] at hj; exact Option.some.inj hj
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hjl, hg]
  set w' := wiresFrom (gs.take j) w with hw'
  have hlen : w'.length = w.length + j := by
    rw [hw', length_wiresFrom, List.length_take]; omega
  set val := g.op.eval (g.inputs.map fun i => w'.getD i false) with hval
  have hfull : wiresFrom gs w = wiresFrom (gs.drop (j + 1)) (w' ++ [val]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hlow : ∀ i, i < w.length + j → (wiresFrom gs w).getD i false = w'.getD i false := by
    intro i hi
    rw [hfull, getD_wiresFrom _ _ _ (by simp; omega), qa_getD_append_lt _ _ _ (by omega)]
  have hmap : (g.inputs.map fun i =>
      if i < w.length + j then (wiresFrom gs w).getD i false else false) =
      g.inputs.map fun i => w'.getD i false := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < w.length + j
    · rw [if_pos hi, hlow i hi]
    · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
  rw [hmap, hfull, getD_wiresFrom _ _ _ (by simp; omega), ← hlen,
    List.getD_append_right _ _ _ _ (le_refl _)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  exact hval

/-- Agreement outside a bad set of wires. -/
theorem qa_agree (gs : List Gate) (x x' : List Bool) (hl : x.length = x'.length)
    (B : ℕ → Prop)
    (hx : ∀ i, i < x.length → ¬ B i → x.getD i false = x'.getD i false)
    (hg : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → ¬ B (x.length + j) →
      (∀ i, i < x.length + j → ¬ B i →
        (wiresFrom gs x).getD i false = (wiresFrom gs x').getD i false) →
      g.op.eval (g.inputs.map fun i =>
          if i < x.length + j then (wiresFrom gs x).getD i false else false) =
        g.op.eval (g.inputs.map fun i =>
          if i < x.length + j then (wiresFrom gs x').getD i false else false)) :
    ∀ t, ¬ B t → (wiresFrom gs x).getD t false = (wiresFrom gs x').getD t false := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases h1 : t < x.length
    · rw [getD_wiresFrom _ _ _ h1, getD_wiresFrom _ _ _ (by omega)]
      exact hx t h1 ht
    · obtain ⟨j, rfl⟩ : ∃ j, t = x.length + j := ⟨t - x.length, by omega⟩
      cases hj : gs[j]? with
      | none =>
        have : gs.length ≤ j := by
          by_contra h; rw [List.getElem?_eq_getElem (by omega)] at hj; exact absurd hj (by simp)
        rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; omega),
          List.getD_eq_default _ _ (by rw [length_wiresFrom]; omega)]
      | some g =>
        rw [qa_val_gate gs x j g hj, hl, qa_val_gate gs x' j g hj, ← hl]
        exact hg j g hj ht (fun i hi hb => ih i hi hb)

/-- The evaluation of a gate only depends on the values it reads. -/
theorem qa_eval_congr (g : Gate) (f f' : ℕ → Bool)
    (h : ∀ a, qaReads g a → f a = f' a) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  by_cases hn : g.op = GateOp.not
  · rw [hn]
    cases hl : g.inputs with
    | nil => rfl
    | cons a t =>
      have := h a (Or.inl ⟨hn, by rw [hl]; rfl⟩)
      simp [GateOp.eval, this]
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (Or.inr ⟨hn, ha⟩)

/-- An OR gate listing a true wire is true. -/
theorem qa_or_true (g : Gate) (f : ℕ → Bool) (hop : g.op = GateOp.or) (W : ℕ)
    (hW : W ∈ g.inputs) (hf : f W = true) : g.op.eval (g.inputs.map f) = true := by
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨W, hW, hf⟩

/-- An AND gate listing a false wire is false. -/
theorem qa_and_false (g : Gate) (f : ℕ → Bool) (hop : g.op = GateOp.and) (z : ℕ)
    (hz : z ∈ g.inputs) (hf : f z = false) : g.op.eval (g.inputs.map f) = false := by
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id]
  exact ⟨z, hz, by simp [hf]⟩

theorem qa_ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The common core of P1 and P2: if gate `r` is an OR listing a wire `W` before it that is
true at `x`, and every reader of input `v` is `r`, then flipping `v` keeps every wire other
than `v`. -/
theorem qa_flip_or (n : ℕ) (C : Circuit) (v : Fin n) (r : Fin C.gates.length) (W : ℕ)
    (hop : (C.gates.get r).op = GateOp.or) (hW : W ∈ (C.gates.get r).inputs)
    (hWv : W ≠ v.val) (hWlt : W < n + r.val)
    (hread : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) v.val → j = r)
    (x : Fin n → Bool) (hWx : (C.wires (List.ofFn x)).getD W false = true) :
    ∀ t, t ≠ v.val → (C.wires (List.ofFn x)).getD t false =
      (C.wires (List.ofFn (Function.update x v (!x v)))).getD t false := by
  have hlen : (List.ofFn x).length = n := by simp
  have hlen' : (List.ofFn (Function.update x v (!x v))).length = n := by simp
  intro t ht
  refine qa_agree C.gates _ _ (by simp) (fun i => i = v.val) ?_ ?_ t ht
  · intro i hi hb
    rw [hlen] at hi
    rw [qa_ofFn_getD _ _ hi, qa_ofFn_getD _ _ hi, Function.update_of_ne]
    intro h; apply hb; rw [← h]
  · intro j g hj hgood ih
    rw [hlen] at hgood ih ⊢
    have hjl : j < C.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; exact absurd hj (by simp)
    have hgj : C.gates.get ⟨j, hjl⟩ = g := by
      simp only [List.get_eq_getElem]
      rw [List.getElem?_eq_getElem hjl] at hj; exact Option.some.inj hj
    by_cases hjr : j = r.val
    · subst hjr
      have hgr : C.gates.get r = g := hgj
      rw [← hgr]
      have hW' : (C.wires (List.ofFn (Function.update x v (!x v)))).getD W false = true := by
        rw [← hWx]; exact (ih W hWlt hWv).symm
      rw [qa_or_true _ _ hop W hW (by rw [if_pos hWlt]; exact hWx),
        qa_or_true _ _ hop W hW (by rw [if_pos hWlt]; exact hW')]
    · apply qa_eval_congr
      intro a ha
      by_cases hlt : a < n + j
      · rw [if_pos hlt, if_pos hlt]
        apply ih a hlt
        intro hav
        apply hjr
        have := hread ⟨j, hjl⟩ (by rw [hgj, ← hav]; exact ha)
        rw [← this]
      · rw [if_neg hlt, if_neg hlt]

/-- QA-P2, tool W at an OR: `r = OR(v, W)` with `W` before `r` and `W ≠ v`, every reader of
the input `v` is `r`, the output is not `v`. Wherever the output changes with `x_v`, wire `W`
is false. -/
theorem qa_toolW_or (n : ℕ) (C : Circuit) (v : Fin n) (r : Fin C.gates.length) (W : ℕ)
    (hop : (C.gates.get r).op = GateOp.or) (hW : W ∈ (C.gates.get r).inputs)
    (hWv : W ≠ v.val) (hWlt : W < n + r.val)
    (hread : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) v.val → j = r)
    (hout : C.output ≠ v.val) (x : Fin n → Bool)
    (hch : circuitFun n C (Function.update x v (!x v)) ≠ circuitFun n C x) :
    (C.wires (List.ofFn x)).getD W false = false := by
  by_contra hWx
  rw [Bool.not_eq_false] at hWx
  apply hch
  exact (qa_flip_or n C v r W hop hW hWv hWlt hread x hWx C.output hout).symm

/-- QA-P1, Fact E: `r` is an OR listing the inputs `e` and `q3`, every reader of `q3` is `r`,
the output is not `q3`. At every `x` with `x_e` true the output does not change with `x_q3`. -/
theorem qa_factE (n : ℕ) (C : Circuit) (e q3 : Fin n) (r : Fin C.gates.length)
    (hne : e ≠ q3)
    (hop : (C.gates.get r).op = GateOp.or) (he : e.val ∈ (C.gates.get r).inputs)
    (hread : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) q3.val → j = r)
    (hout : C.output ≠ q3.val) (x : Fin n → Bool) (hx : x e = true) :
    circuitFun n C (Function.update x q3 (!x q3)) = circuitFun n C x := by
  have hev : e.val ≠ q3.val := fun h => hne (Fin.ext h)
  have hWx : (C.wires (List.ofFn x)).getD e.val false = true := by
    rw [wires_eq, getD_wiresFrom _ _ _ (by simp), qa_ofFn_getD _ _ e.isLt]; exact hx
  exact (qa_flip_or n C q3 r e.val hop he hev (by omega) hread x hWx C.output hout).symm

/-- QA-P3, tool W through an OR then an AND: `o = OR(v, W)`, `M = AND(o, z)` with `o < M`,
`z` before `M` and `z ≠ o`; every reader of the input `v` is `o`; every reader of wire `o`
after `o` is `M`; the output is neither `v` nor `o`. Wherever the output changes with `x_v`,
wire `z` is true. -/
theorem qa_toolW_or_and (n : ℕ) (C : Circuit) (v : Fin n) (o M : Fin C.gates.length) (z : ℕ)
    (hoM : o < M)
    (hMop : (C.gates.get M).op = GateOp.and) (hMo : n + o.val ∈ (C.gates.get M).inputs)
    (hMz : z ∈ (C.gates.get M).inputs) (hzo : z ≠ n + o.val) (hzlt : z < n + M.val)
    (hread : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) v.val → j = o)
    (hreado : ∀ j : Fin C.gates.length, o < j → qaReads (C.gates.get j) (n + o.val) → j = M)
    (hout : C.output ≠ v.val) (hout' : C.output ≠ n + o.val) (x : Fin n → Bool)
    (hch : circuitFun n C (Function.update x v (!x v)) ≠ circuitFun n C x) :
    (C.wires (List.ofFn x)).getD z false = true := by
  have hzv : z ≠ v.val := by
    intro h
    have := hread M (Or.inr ⟨(by rw [hMop]; exact fun hh => GateOp.noConfusion hh), h ▸ hMz⟩)
    exact absurd hoM (by rw [this]; exact lt_irrefl _)
  by_contra hzx
  rw [Bool.not_eq_true] at hzx
  apply hch
  have hlen : (List.ofFn x).length = n := by simp
  have key : ∀ t, ¬ (t = v.val ∨ t = n + o.val) → (C.wires (List.ofFn x)).getD t false =
      (C.wires (List.ofFn (Function.update x v (!x v)))).getD t false := by
    intro t ht
    refine qa_agree C.gates _ _ (by simp) (fun i => i = v.val ∨ i = n + o.val) ?_ ?_ t ht
    · intro i hi hb
      rw [hlen] at hi
      rw [qa_ofFn_getD _ _ hi, qa_ofFn_getD _ _ hi, Function.update_of_ne]
      intro h; apply hb; left; rw [← h]
    · intro j g hj hgood ih
      rw [hlen] at hgood ih ⊢
      have hjl : j < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; exact absurd hj (by simp)
      have hgj : C.gates.get ⟨j, hjl⟩ = g := by
        simp only [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hjl] at hj; exact Option.some.inj hj
      by_cases hjM : j = M.val
      · subst hjM
        have hgM : C.gates.get M = g := hgj
        rw [← hgM]
        have hz' : (C.wires (List.ofFn (Function.update x v (!x v)))).getD z false = false := by
          exact (ih z hzlt (by rintro (h | h) <;> contradiction)).symm.trans hzx
        rw [qa_and_false _ _ hMop z hMz (by rw [if_pos hzlt]; exact hzx),
          qa_and_false _ _ hMop z hMz (by rw [if_pos hzlt]; exact hz')]
      · apply qa_eval_congr
        intro a ha
        by_cases hlt : a < n + j
        · rw [if_pos hlt, if_pos hlt]
          apply ih a hlt
          rintro (hav | hao)
          · apply hgood; right
            have := hread ⟨j, hjl⟩ (by rw [hgj, ← hav]; exact ha)
            rw [← this]
          · apply hjM
            have hoj : o < (⟨j, hjl⟩ : Fin C.gates.length) := by
              show o.val < j; omega
            have := hreado ⟨j, hjl⟩ hoj (by rw [hgj, ← hao]; exact ha)
            rw [← this]
        · rw [if_neg hlt, if_neg hlt]
  exact (key C.output (by rintro (h | h) <;> contradiction)).symm

end PEqualNP.MetaComplexity.Helpers.RunFour2
