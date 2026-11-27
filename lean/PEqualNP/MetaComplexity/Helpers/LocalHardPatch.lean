import PEqualNP.MetaComplexity.Helpers.Support

/-!
# Patching a circuit at a few points

Helper for the hard-table corollaries of the local reduction chain. Changing the value of a
function at one point costs at most `2 n + 2` gates on `n` inputs: a chain of `2 n + 1` gates
computes the indicator of the point (or its complement) from the input wires, and one more gate
combines it with the old output. Hence the least size of a circuit consistent with a partial
truth table changes by at most `2 n + 2` per changed entry. No locality is involved.

The constant `2 n` would be false at `n = 0`: the constant `true` costs one gate.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalHardPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- One step of the point chain, appended to the wires `v`: a NOT of wire `k`, then the AND
(if `c`) or the OR (if not `c`) of wire `o` with wire `k` (if `t`) or with its negation. -/
theorem chainStep (v : List Bool) (c t : Bool) (k o : ℕ) (hk : k < v.length)
    (ho : o < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩,
      ⟨if c = true then GateOp.and else GateOp.or, [o, if t = true then k else v.length]⟩]
        v).getD (v.length + 1) false
      = (if c = true then
          (v.getD o false && (if t = true then v.getD k false else !v.getD k false))
        else (v.getD o false || (if t = true then v.getD k false else !v.getD k false))) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length →
      (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  cases c <;> cases t <;> simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ ho]

/-- The point chain: `2 k + 1` gates appended after `m` wires. With `c = true` the last wire
says that the first `k` wires agree with `u`; with `c = false` it says that they do not. -/
theorem pointChain (c : Bool) (u : ℕ → Bool) (k : ℕ) : ∀ m : ℕ, k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = 2 * k + 1 ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false
          = (c == decide (∀ i : ℕ, i < k → w.getD i false = u i)) := by
  induction k with
  | zero =>
    intro m _
    refine ⟨[⟨if c = true then GateOp.and else GateOp.or, []⟩], m, ?_, rfl, by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      cases c <;> simp
    · intro w hw
      cases c <;> simp [wiresFrom, ← hw, GateOp.eval]
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.not, [k]⟩, ⟨if c = true then GateOp.and else GateOp.or,
      [out, if (u k == c) = true then k else m + gs.length]⟩], m + gs.length + 1, ?_,
      by simp [len]; omega,
      by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | hg
        · subst hg; simp [Ok]
        · subst hg
          refine ⟨?_, by simp⟩
          cases c <;> simp
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD k false = w.getD k false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      rw [← lv, chainStep v c (u k == c) k out (by omega) (by omega), ev w hw, e1]
      have hsplit : (∀ i : ℕ, i < k + 1 → w.getD i false = u i) ↔
          (∀ i : ℕ, i < k → w.getD i false = u i) ∧ w.getD k false = u k := by
        constructor
        · intro h
          exact ⟨fun i hi => h i (by omega), h k (by omega)⟩
        · rintro ⟨h1, h2⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h1 i h
          · subst h; exact h2
      rw [decide_eq_decide.mpr hsplit, Bool.decide_and]
      generalize decide (∀ i : ℕ, i < k → w.getD i false = u i) = p
      cases c <;> cases u k <;> cases w.getD k false <;> cases p <;> rfl

theorem size_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : HasCircuitSize n f s) (hst : s ≤ t) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, h2.trans hst, h3⟩

/-- Changing the value of a function at one point costs at most `2 n + 2` gates. -/
theorem patch_one (n s : ℕ) (f : (Fin n → Bool) → Bool) (u : Fin n → Bool) (b : Bool)
    (h : HasCircuitSize n f s) : HasCircuitSize n (Function.update f u b) (s + (2 * n + 2)) := by
  classical
  obtain ⟨C, hfan, hsize, hev⟩ := h
  obtain ⟨uN, huN⟩ : ∃ uN : ℕ → Bool, uN = fun i => if h : i < n then u ⟨i, h⟩ else false :=
    ⟨_, rfl⟩
  obtain ⟨cg, out, ok, len, hout, ev⟩ := pointChain b uN n (n + C.gates.length) (by omega)
  obtain ⟨o', ho'⟩ : ∃ o' : ℕ, o' =
      if C.output < n + C.gates.length then C.output else n + C.gates.length + cg.length + 1 :=
    ⟨_, rfl⟩
  refine ⟨⟨C.gates ++ cg ++ [⟨if b = true then GateOp.or else GateOp.and, [o', out]⟩],
    n + C.gates.length + cg.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact hfan g hg
    · exact ok g hg
    · subst hg
      refine ⟨?_, by simp⟩
      cases b <;> simp
  · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hsize ⊢
    omega
  · intro x
    simp only [Circuit.eval, wires_eq]
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom C.gates (List.ofFn x) with hv
    set v2 := wiresFrom cg v with hv2
    have lv : v.length = n + C.gates.length := by rw [hv, length_wiresFrom]; simp
    have lv2 : v2.length = n + C.gates.length + cg.length := by rw [hv2, length_wiresFrom, lv]
    have hf : v.getD C.output false = f x := by
      have := hev x
      simpa only [Circuit.eval, wires_eq] using this
    have e1 : v2.getD o' false = f x := by
      rw [← hf, ho']
      by_cases hc : C.output < n + C.gates.length
      · simp only [hc, ↓reduceIte]
        rw [hv2, getD_wiresFrom _ _ _ (by omega)]
      · simp only [hc, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have e2 : v2.getD out false = (b == decide (x = u)) := by
      rw [hv2, ev v lv]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro hall
        funext i
        have := hall i i.isLt
        rw [hv, getD_wiresFrom _ _ _ (by simp), huN] at this
        simpa using this
      · intro hxu i hi
        rw [hv, getD_wiresFrom _ _ _ (by simpa using hi), huN, hxu]
        simp [hi]
    have step : wiresFrom [⟨if b = true then GateOp.or else GateOp.and, [o', out]⟩] v2
        = v2 ++ [(if b = true then GateOp.or else GateOp.and).eval
            ([o', out].map fun i => v2.getD i false)] := rfl
    rw [step, ← lv2, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, e1, e2]
    by_cases hxu : x = u
    · subst hxu
      cases b <;> simp [GateOp.eval]
    · rw [Function.update_of_ne hxu]
      cases b <;> simp [GateOp.eval, hxu]

/-- Changing the values of a function at `k` points costs at most `(2 n + 2) k` gates. -/
theorem patch_many (n s : ℕ) (g : (Fin n → Bool) → Bool) : ∀ (k : ℕ) (f : (Fin n → Bool) → Bool),
    (Finset.univ.filter fun x : Fin n → Bool => g x ≠ f x).card ≤ k →
    HasCircuitSize n f s → HasCircuitSize n g (s + (2 * n + 2) * k) := by
  classical
  intro k
  induction k generalizing s with
  | zero =>
    intro f hk hf
    have hgf : g = f := by
      funext x
      by_contra hne
      have hx : x ∈ Finset.univ.filter fun x : Fin n → Bool => g x ≠ f x := by simp [hne]
      have := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    rw [hgf]
    exact size_mono hf (by omega)
  | succ k ih =>
    intro f hk hf
    by_cases hD : (Finset.univ.filter fun x : Fin n → Bool => g x ≠ f x) = ∅
    · have h0 := ih s f (by rw [hD]; simp) hf
      exact size_mono h0 (by rw [Nat.mul_succ]; omega)
    · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hD
      have hsub : (Finset.univ.filter fun x : Fin n → Bool => g x ≠ Function.update f u (g u) x)
          ⊆ (Finset.univ.filter fun x : Fin n → Bool => g x ≠ f x).erase u := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        by_cases hxu : x = u
        · subst hxu; simp at hx'
        · rw [Function.update_of_ne hxu] at hx'
          exact Finset.mem_erase.mpr ⟨hxu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hu] at hcard
      have h1 := ih (s + (2 * n + 2)) (Function.update f u (g u)) (by omega)
        (patch_one n s f u (g u) hf)
      exact size_mono h1 (by rw [Nat.mul_succ]; omega)

/-- Partial circuit size is `(2 n' + 2)`-Lipschitz in the number of changed entries. The
changed entries are counted over the inputs `x`, read at position `tableIndex x`. -/
theorem lipschitz : ∀ (n' k s : ℕ) (T T' : List (Option Bool)), (Finset.univ.filter fun x : Fin n' → Bool => T.getD (PEqualNP.MetaComplexity.tableIndex x) none ≠ T'.getD (PEqualNP.MetaComplexity.tableIndex x) none).card ≤ k → (∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T' f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) → ∃ g : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T g ∧ PEqualNP.MetaComplexity.HasCircuitSize n' g (s + (2 * n' + 2) * k) := by
  classical
  rintro n' k s T T' hk ⟨f, hc, hs⟩
  refine ⟨fun x => (T.getD (tableIndex x) none).getD (f x), ?_, ?_⟩
  · intro x b hb
    show (T.getD (tableIndex x) none).getD (f x) = b
    rw [hb]
    rfl
  · refine patch_many n' s _ k f (le_trans (Finset.card_le_card ?_) hk) hs
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => hx' ?_⟩
    cases hT : T.getD (tableIndex x) none with
    | none => simp
    | some b =>
      have := hc x b (by rw [← heq, hT])
      simp [this]

/-- The case of one changed entry. -/
theorem lipschitz_one : ∀ (n' s : ℕ) (T T' : List (Option Bool)), (Finset.univ.filter fun x : Fin n' → Bool => T.getD (PEqualNP.MetaComplexity.tableIndex x) none ≠ T'.getD (PEqualNP.MetaComplexity.tableIndex x) none).card ≤ 1 → (∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T' f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) → ∃ g : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T g ∧ PEqualNP.MetaComplexity.HasCircuitSize n' g (s + (2 * n' + 2)) := by
  intro n' s T T' hk h
  have := lipschitz n' 1 s T T' hk h
  simpa using this

end PEqualNP.MetaComplexity.Helpers.LocalHardPatch
