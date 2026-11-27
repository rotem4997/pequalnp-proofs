import PEqualNP.MetaComplexity.Helpers.Counting
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.MetaComplexity.Helpers.OrChain

/-!
# Circuit size hierarchy

Helper for `L-meta-004`. Adding one minterm to a function costs `2 * n + 2` gates: one literal
gate per input, a chain of AND gates, and one OR gate. Walking from the constant false to a
hard function one minterm at a time, the first function that leaves size `s` has size at most
`s + 2 * n + 2`.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- The gate that compares wire `k` with the bit `b`. -/
def litGate (b : Bool) (k : ℕ) : Gate :=
  if b = true then ⟨GateOp.and, [k]⟩ else ⟨GateOp.not, [k]⟩

theorem litGate_ok (b : Bool) (k : ℕ) : Ok (litGate b k) := by
  cases b <;> simp [litGate, Ok]

theorem litGate_eval (b : Bool) (k : ℕ) (f : ℕ → Bool) :
    (litGate b k).op.eval ((litGate b k).inputs.map f) = decide (f k = b) := by
  cases b <;> cases h : f k <;> simp [litGate, GateOp.eval, h]

/-- A chain of literal and AND gates, built at wire offset `m`, that tests whether the first
`k` wires carry the bits `a 0, ..., a (k - 1)`. -/
theorem andChain (a : ℕ → Bool) (k : ℕ) : ∀ m : ℕ, k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = 2 * k + 1 ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∀ i : ℕ, i < k → w.getD i false = a i) := by
  induction k with
  | zero =>
    intro m _
    refine ⟨[⟨GateOp.and, []⟩], m, ?_, rfl, by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      have step : wiresFrom [⟨GateOp.and, []⟩] w = w ++ [true] := rfl
      rw [step, ← hw, getD_snoc_eq]
      simp
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [litGate (a k) k, ⟨GateOp.and, [out, m + gs.length]⟩], m + gs.length + 1,
      ?_, (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega), ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | hg
        · subst hg; exact litGate_ok _ _
        · subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD k false = w.getD k false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      set e := (litGate (a k) k).op.eval ((litGate (a k) k).inputs.map fun i => v.getD i false)
        with he
      have he' : e = decide (w.getD k false = a k) := by
        rw [he, litGate_eval, e1]
      have step : wiresFrom [litGate (a k) k, ⟨GateOp.and, [out, m + gs.length]⟩] v
          = (v ++ [e]) ++ [GateOp.and.eval ([out, m + gs.length].map
              fun i => (v ++ [e]).getD i false)] := rfl
      have l2 : (v ++ [e]).length = m + gs.length + 1 := by simp [lv]
      rw [step, ← l2, getD_snoc_eq]
      have g1 : (v ++ [e]).getD out false = v.getD out false :=
        getD_snoc_ne _ _ _ _ (by omega)
      have g2 : (v ++ [e]).getD (m + gs.length) false = e := by
        rw [← lv]; exact getD_snoc_eq _ _ _
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id]
      rw [g1, g2, ev w hw, he']
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact h1 i hi
        · subst hi; exact h2
      · intro h
        exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

/-- The bits of `a`, indexed by all numbers. -/
def bitAt {n : ℕ} (a : Fin n → Bool) (i : ℕ) : Bool :=
  if hi : i < n then a ⟨i, hi⟩ else false

theorem decide_bits {n : ℕ} (x a : Fin n → Bool) (w : List Bool)
    (hw : ∀ i : Fin n, w.getD (i : ℕ) false = x i) :
    decide (∀ i : ℕ, i < n → w.getD i false = bitAt a i) = decide (x = a) := by
  apply decide_eq_decide.2
  constructor
  · intro H
    funext i
    have h := H i i.isLt
    rw [hw i] at h
    simpa [bitAt] using h
  · intro H i hi
    have h := hw ⟨i, hi⟩
    simp only at h
    rw [h, H]
    simp [bitAt, hi]

/-- Adding one minterm costs at most `2 * n + 2` gates. -/
theorem add_minterm (n : ℕ) (h : (Fin n → Bool) → Bool) (a : Fin n → Bool) (s : ℕ)
    (H : HasCircuitSize n h s) :
    HasCircuitSize n (fun x => h x || decide (x = a)) (s + 2 * n + 2) := by
  obtain ⟨C, ok, hsz, hev⟩ := H
  have hsz' : C.gates.length ≤ s := hsz
  by_cases ho : C.output < n + C.gates.length
  · obtain ⟨gs, out, okg, len, hout, ev⟩ := andChain (bitAt a) n (n + C.gates.length) (by omega)
    refine ⟨⟨C.gates ++ gs ++ [⟨GateOp.or, [C.output, out]⟩], n + C.gates.length + gs.length⟩,
      ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact ok g hg
      · exact okg g hg
      · subst hg; simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
      omega
    · intro x
      have h0 : (⟨C.gates ++ gs ++ [⟨GateOp.or, [C.output, out]⟩],
            n + C.gates.length + gs.length⟩ : Circuit).eval (List.ofFn x)
          = (wiresFrom (C.gates ++ gs ++ [⟨GateOp.or, [C.output, out]⟩]) (List.ofFn x)).getD
              (n + C.gates.length + gs.length) false := rfl
      rw [h0, wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom C.gates (List.ofFn x) with hw1
      have l1 : w1.length = n + C.gates.length := by rw [hw1, length_wiresFrom]; simp
      set v := wiresFrom gs w1 with hv
      have lv : v.length = n + C.gates.length + gs.length := by rw [hv, length_wiresFrom, l1]
      have step : wiresFrom [⟨GateOp.or, [C.output, out]⟩] v
          = v ++ [GateOp.or.eval ([C.output, out].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      have e1 : v.getD C.output false = h x := by
        rw [hv, getD_wiresFrom _ _ _ (by omega), ← hev x]; rfl
      have e2 : v.getD out false = decide (x = a) := by
        rw [hv, ev w1 l1]
        apply decide_bits
        intro i
        rw [hw1, getD_wiresFrom _ _ _ (by simp), getD_ofFn]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [e1, e2]
  · obtain ⟨gs, out, okg, len, hout, ev⟩ := andChain (bitAt a) n n le_rfl
    refine ⟨⟨gs, out⟩, okg, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hx : h x = false := by
      rw [← hev x]
      have h0 : C.eval (List.ofFn x) = (wiresFrom C.gates (List.ofFn x)).getD C.output false :=
        rfl
      rw [h0]
      exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
    have h0 : (⟨gs, out⟩ : Circuit).eval (List.ofFn x)
        = (wiresFrom gs (List.ofFn x)).getD out false := rfl
    show _ = (h x || decide (x = a))
    rw [h0, ev (List.ofFn x) (by simp), hx, Bool.false_or]
    apply decide_bits
    intro i
    exact getD_ofFn x i

/-- Circuit size hierarchy: between `s` and `5 * s` there is a function, for `n ≤ s` and `s`
at most the counting bound. -/
theorem hierarchy (n : ℕ) (hn : 5 ≤ n) (s : ℕ) (hs : n ≤ s) (hs' : s ≤ 2 ^ n / (4 * n)) :
    ∃ f : (Fin n → Bool) → Bool, HasCircuitSize n f (5 * s) ∧ ¬ HasCircuitSize n f s := by
  obtain ⟨g, hg⟩ := counting n hn
  have hg' : ¬ HasCircuitSize n g s := fun h => hg (hasCircuitSize_mono hs' h)
  by_contra hno
  push Not at hno
  have all : ∀ A : Finset (Fin n → Bool),
      HasCircuitSize n (fun x => g x && decide (x ∈ A)) s := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨⟨[], n⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
      intro x
      have h0 : (⟨[], n⟩ : Circuit).eval (List.ofFn x) = (List.ofFn x).getD n false := rfl
      rw [h0, List.getD_eq_default _ _ (by simp)]
      simp
    | insert a A _ ih =>
      apply hno
      by_cases ha : g a = true
      · have e : (fun x => g x && decide (x ∈ insert a A))
            = (fun x => (g x && decide (x ∈ A)) || decide (x = a)) := by
          funext x
          by_cases hx : x = a
          · subst hx; simp [ha]
          · simp [hx]
        rw [e]
        exact hasCircuitSize_mono (by omega) (add_minterm n _ a s ih)
      · have e : (fun x => g x && decide (x ∈ insert a A))
            = (fun x => g x && decide (x ∈ A)) := by
          funext x
          by_cases hx : x = a
          · subst hx; simp [ha]
          · simp [hx]
        rw [e]
        exact hasCircuitSize_mono (by omega) ih
  apply hg'
  have e : (fun x => g x && decide (x ∈ (Finset.univ : Finset (Fin n → Bool)))) = g := by
    funext x; simp
  rw [← e]
  exact all Finset.univ

end PEqualNP.MetaComplexity.Helpers
