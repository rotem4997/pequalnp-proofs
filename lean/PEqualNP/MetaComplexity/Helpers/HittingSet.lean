import PEqualNP.MetaComplexity.Helpers.OrChain

/-!
# Hitting sets and circuits that separate the zero input from indicators

Helper for `L-meta-015`. A circuit that is false on the all-false input and true on the
indicator of every set of a family reads a hitting set of the family: the support of its
output wire. Conversely the OR of the inputs in a hitting set `H` is such a circuit, with
`|H| - 1` gates.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- A chain of OR gates over the wires listed in `a :: l`, built at wire offset `m`. -/
theorem orList (a : ℕ) (l : List ℕ) : ∀ m : ℕ, (∀ b ∈ a :: l, b < m) →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = l.length ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∃ b ∈ a :: l, w.getD b false = true) := by
  induction l with
  | nil =>
    intro m hm
    refine ⟨[], a, by simp, rfl, ?_, ?_⟩
    · have := hm a List.mem_cons_self
      simp only [List.length_nil]; omega
    · intro w _
      have h0 : wiresFrom [] w = w := rfl
      rw [h0]
      simp
  | cons c l ih =>
    intro m hm
    have hc : c < m := hm c (by simp)
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by
      intro b hb
      rcases List.mem_cons.1 hb with hb | hb
      · exact hm b (by simp [hb])
      · exact hm b (by simp [hb]))
    refine ⟨gs ++ [⟨GateOp.or, [out, c]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD c false = w.getD c false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      have step : wiresFrom [⟨GateOp.or, [out, c]⟩] v
          = v ++ [GateOp.or.eval ([out, c].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [ev w hw, e1]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨b, hb | hb, hx⟩ | hx)
        · exact ⟨b, Or.inl hb, hx⟩
        · exact ⟨b, Or.inr (Or.inr hb), hx⟩
        · exact ⟨c, Or.inr (Or.inl rfl), hx⟩
      · rintro ⟨b, hb | hb | hb, hx⟩
        · exact Or.inl ⟨b, Or.inl hb, hx⟩
        · exact Or.inr (hb ▸ hx)
        · exact Or.inl ⟨b, Or.inr hb, hx⟩

/-- The OR of the inputs in `H` has a circuit with `s` gates when `|H| ≤ s + 1`. -/
theorem orSet_size (n : ℕ) (H : Finset (Fin n)) (s : ℕ) (h : H.card ≤ s + 1) :
    HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i ∈ H, x i = true)) s := by
  rcases hL : H.toList with _ | ⟨a, l⟩
  · have hH : H = ∅ := Finset.toList_eq_nil.1 hL
    subst hH
    refine ⟨⟨[], n⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
    intro x
    have h0 : (⟨[], n⟩ : Circuit).eval (List.ofFn x) = (List.ofFn x).getD n false := rfl
    rw [h0, List.getD_eq_default _ _ (by simp)]
    simp
  · have hlen : l.length + 1 = H.card := by
      have := Finset.length_toList H
      rw [hL] at this
      simpa using this
    obtain ⟨gs, out, ok, len, _, ev⟩ :=
      orList (a : ℕ) (l.map fun i : Fin n => (i : ℕ)) n (by
        intro b hb
        rcases List.mem_cons.1 hb with hb | hb
        · rw [hb]; exact a.isLt
        · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hb
          exact i.isLt)
    refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; rw [len, List.length_map]; omega, ?_⟩
    intro x
    have h1 := ev (List.ofFn x) (by simp)
    have h2 : (⟨gs, out⟩ : Circuit).eval (List.ofFn x)
        = (wiresFrom gs (List.ofFn x)).getD out false := rfl
    rw [h2, h1]
    have key : (∃ b ∈ (a : ℕ) :: l.map (fun i : Fin n => (i : ℕ)),
        (List.ofFn x).getD b false = true) ↔ (∃ i ∈ H, x i = true) := by
      constructor
      · rintro ⟨b, hb, hx⟩
        have hb' : b ∈ (a :: l).map (fun i : Fin n => (i : ℕ)) := by simpa using hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb'
        rw [getD_ofFn] at hx
        exact ⟨i, Finset.mem_toList.1 (hL ▸ hi), hx⟩
      · rintro ⟨i, hi, hx⟩
        have hi' : i ∈ a :: l := hL ▸ Finset.mem_toList.2 hi
        have hb : (i : ℕ) ∈ (a :: l).map (fun i : Fin n => (i : ℕ)) := List.mem_map.2 ⟨i, hi', rfl⟩
        refine ⟨(i : ℕ), by simpa using hb, ?_⟩
        rw [getD_ofFn]; exact hx
    exact decide_eq_decide.2 key

/-- A function that is false on the all-false input and true on the indicator of every set of
`F` has a circuit with `s` gates exactly when `F` has a hitting set of size at most `s + 1`. -/
theorem hitting_iff (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) :
    (∃ f : (Fin n → Bool) → Bool, f (fun _ : Fin n => false) = false ∧
      (∀ S ∈ F, f (fun i : Fin n => decide (i ∈ S)) = true) ∧ HasCircuitSize n f s) ↔
    (∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ s + 1) := by
  constructor
  · rintro ⟨f, hf0, hf1, C, ok, hsz, hev⟩
    have hsz' : C.gates.length ≤ s := hsz
    set H := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hH
    refine ⟨H, ?_, ?_⟩
    · intro S hS
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hag := (agree_wiresFrom (fun _ : Fin n => false) (fun i : Fin n => decide (i ∈ S))
        C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
          intro k hk
          have hkS : k ∉ S := fun hkS => by
            have : k ∈ H ∩ S := Finset.mem_inter.2 ⟨hk, hkS⟩
            rw [hne] at this
            exact absurd this (Finset.notMem_empty k)
          simp [hkS])
      have e0 : C.eval (List.ofFn fun _ : Fin n => false)
          = C.eval (List.ofFn fun i : Fin n => decide (i ∈ S)) := hag
      rw [hev, hev, hf0, hf1 S hS] at e0
      exact Bool.false_ne_true e0
    · have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
      simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
      rw [← hH] at hc
      omega
  · rintro ⟨H, hhit, hcard⟩
    refine ⟨fun x => decide (∃ i ∈ H, x i = true), by simp, ?_, orSet_size n H s hcard⟩
    intro S hS
    obtain ⟨i, hi⟩ := hhit S hS
    obtain ⟨hiH, hiS⟩ := Finset.mem_inter.1 hi
    exact decide_eq_true ⟨i, hiH, by simp [hiS]⟩

end PEqualNP.MetaComplexity.Helpers
