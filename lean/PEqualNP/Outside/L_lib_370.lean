import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_370_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- Running a list of gates on two wire lists, the second read through `φ`. -/
theorem run (φ : ℕ → ℕ) :
    ∀ (gs : List Gate) (W W' : List Bool),
      (∀ k, k < gs.length → ∀ i, (φ i = W'.length + k ↔ i = W.length + k)) →
      (∀ i, W.getD i false = W'.getD (φ i) false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD i false
        = ((gs.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate)).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD (φ i) false := by
  intro gs
  induction gs with
  | nil => intro W W' _ h; simpa using h
  | cons g gs ih =>
    intro W W' hφ h
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · intro k hk i
      have := hφ (k + 1) (by simp; omega) i
      simp only [List.length_append, List.length_singleton]
      constructor
      · intro hi; exact by have := this.1 (by omega); omega
      · intro hi; exact by have := this.2 (by omega); omega
    · intro i
      rw [getD_snoc, getD_snoc]
      have hb : g.op.eval (g.inputs.map fun i => W.getD i false)
          = g.op.eval ((g.inputs.map φ).map fun i => W'.getD i false) := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro j _; exact h j
      have h0 := hφ 0 (by simp) i
      simp only [Nat.add_zero] at h0
      by_cases hi : i = W.length
      · rw [if_pos hi, if_pos (h0.2 hi)]; exact hb
      · rw [if_neg hi, if_neg (fun h' => hi (h0.1 h'))]; exact h i

theorem main (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (he : Function.Injective e) (hf : Function.Injective f) (hA : RepSizeAtMost A s) :
    RepSizeAtMost (fun u v => A (e u) (f v)) s := by
  classical
  obtain ⟨C, hmono, hsize, hrep⟩ := hA
  set L := C.gates.length with hL
  set BIG := m + m' + L with hBIG
  let φ : ℕ → ℕ := fun i =>
    if h1 : i < n then
      (if h : ∃ u : Fin m, (e u : ℕ) = i then ((Classical.choose h : Fin m) : ℕ) else BIG)
    else if h2 : i < n + n' then
      (if h : ∃ v : Fin m', (f v : ℕ) = i - n then m + ((Classical.choose h : Fin m') : ℕ) else BIG)
    else m + m' + (i - (n + n'))
  refine ⟨⟨C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate), φ C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hmono g0 hg0
    simpa using this
  · simpa [Circuit.size] using hsize
  · intro u v
    have key := run φ C.gates (oneEach (e u) (f v)) (oneEach u v) ?_ ?_ C.output
    · have h1 := hrep (e u) (f v)
      simp only [Circuit.eval, Circuit.wires] at h1 ⊢
      rw [← h1, key]
    · intro k hk i
      simp only [oneEach, List.length_append, List.length_ofFn]
      simp only [φ]
      constructor
      · intro hi
        split_ifs at hi with h1 h3 h2 h4
        · have := (Classical.choose h3).isLt; omega
        · omega
        · have := (Classical.choose h4).isLt; omega
        · omega
        · omega
      · intro hi
        rw [dif_neg (by omega), dif_neg (by omega)]; omega
    · intro i
      simp only [φ]
      by_cases h1 : i < n
      · rw [dif_pos h1]
        have hx : (oneEach (e u) (f v)).getD i false = decide (i = (e u : ℕ)) := by
          simp only [oneEach]
          rw [List.getD_append _ _ _ _ (by simpa using h1)]
          simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
        rw [hx]
        split_ifs with h3
        · have hc := Classical.choose_spec h3
          have hlt := (Classical.choose h3).isLt
          have hy : (oneEach u v).getD ((Classical.choose h3 : Fin _) : ℕ) false
              = decide (((Classical.choose h3 : Fin _) : ℕ) = (u : ℕ)) := by
            simp only [oneEach]
            rw [List.getD_append _ _ _ _ (by simpa using hlt)]
            simp [List.getD_eq_getElem?_getD, hlt, Fin.ext_iff]
          rw [hy]
          apply decide_eq_decide.2
          constructor
          · intro h; exact congrArg Fin.val (he (Fin.ext (hc.trans h)))
          · intro h; rw [← hc, show Classical.choose h3 = u from Fin.ext h]
        · rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]
          simp only [decide_eq_false_iff_not]
          intro h; exact h3 ⟨u, h.symm⟩
      · rw [dif_neg h1]
        by_cases h2 : i < n + n'
        · rw [dif_pos h2]
          have hx : (oneEach (e u) (f v)).getD i false = decide (i - n = (f v : ℕ)) := by
            simp only [oneEach]
            rw [List.getD_append_right _ _ _ _ (by simp; omega)]
            simp only [List.length_ofFn]
            simp [List.getD_eq_getElem?_getD, show i - n < n' by omega, Fin.ext_iff]
          rw [hx]
          split_ifs with h3
          · have hc := Classical.choose_spec h3
            have hlt := (Classical.choose h3).isLt
            have hy : (oneEach u v).getD (m + ((Classical.choose h3 : Fin _) : ℕ)) false
                = decide (((Classical.choose h3 : Fin _) : ℕ) = (v : ℕ)) := by
              simp only [oneEach]
              rw [List.getD_append_right _ _ _ _ (by simp)]
              simp only [List.length_ofFn, Nat.add_sub_cancel_left]
              simp [List.getD_eq_getElem?_getD, hlt, Fin.ext_iff]
            rw [hy]
            apply decide_eq_decide.2
            constructor
            · intro h; exact congrArg Fin.val (hf (Fin.ext (hc.trans h)))
            · intro h; rw [← hc, show Classical.choose h3 = v from Fin.ext h]
          · rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]
            simp only [decide_eq_false_iff_not]
            intro h; exact h3 ⟨v, h.symm⟩
        · rw [dif_neg h2]
          rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega),
            List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]

end PEqualNP.Outside.L_lib_370_aux

theorem PEqualNP.Outside.L_lib_370 :
    ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s :=
  PEqualNP.Outside.L_lib_370_aux.main

