import PEqualNP.MetaComplexity.Helpers.LocalPrivate2
import PEqualNP.MetaComplexity.Helpers.HittingSet

/-!
# A 1-local reduction of parity to partial MCSP has a table about as long as its input, or a
small size bound

Helper for `L-meta-049`. In a 1-local reduction of parity on `n` bits to partial MCSP of fixed
format (size bound `s`, tables of length `N = 2 ^ n'`): `n ≤ N`, and
`s < 1 + (N - n + 1) * (n' + 3)`.

A table entry, as a function of the input, is constant or follows exactly one input position
(`entry_all`, `entry_one`). Every input position is followed by some entry, or flipping it
would not change the instance (`reads`). Take an input `x0` whose table has the fewest entries
`some true`. For every position `i` some entry following `i` is not `some true` at `x0`
(otherwise flipping `i` gives fewer). These entries are distinct for distinct positions, so
`n ≤ N` and at most `N - n` entries are `some true` at `x0`. If `x0` is of odd weight, flip one
of its true positions: at most `N - n + 1` entries are `some true` there. So some input that is
not of odd weight has a table with at most `N - n + 1` entries `some true`; the function that
is true exactly at those points is consistent with the table and is an OR of at most
`N - n + 1` indicators of points, each of `n' + 2` gates (`few_true`). Since the input is not a
member, `s` is below that size.

This file imports neither `LocalPrivate` nor `LocalMajority` (their imports clash with those of
`LocalCore`, which `linear_count` needs): the few facts used from them (`Cert1`, `dep1`,
`same_two`, `mixed`, `two_change`, `flip_odd`) are restated here with the same proofs.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalLinear

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalPrivate2

/-! ## A function with few true points has a small circuit -/

/-- A chain of AND gates over the wires listed in `a :: l`, built at wire offset `m`. -/
theorem andList (a : ℕ) (l : List ℕ) : ∀ m : ℕ, (∀ b ∈ a :: l, b < m) →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = l.length ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∀ b ∈ a :: l, w.getD b false = true) := by
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
    refine ⟨gs ++ [⟨GateOp.and, [out, c]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
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
      have step : wiresFrom [⟨GateOp.and, [out, c]⟩] v
          = v ++ [GateOp.and.eval ([out, c].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id]
      rw [ev w hw, e1]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩ b (hb | hb | hb)
        · exact h1 b (Or.inl hb)
        · rw [hb]; exact h2
        · exact h1 b (Or.inr hb)
      · intro h
        exact ⟨fun b hb => h b (hb.elim Or.inl (fun hb => Or.inr (Or.inr hb))),
          h c (Or.inr (Or.inl rfl))⟩

theorem filter_split {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun a => !p a).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : p a <;> simp [h] <;> omega

/-- The indicator of the point `z`, on the first `n'` wires, built at wire offset `m`, with
`n' + 2` gates: the constant `false`, the OR of the wires where `z` is `false`, its negation,
and the AND of it with the wires where `z` is `true`. -/
theorem point (n' : ℕ) (z : Fin n' → Bool) (m : ℕ) (hm : n' ≤ m) :
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ n' + 2 ∧ out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∀ i : Fin n', w.getD i false = z i) := by
  set Q : List ℕ := ((List.finRange n').filter fun i => !z i).map fun i : Fin n' => (i : ℕ)
    with hQ
  set P : List ℕ := ((List.finRange n').filter fun i => z i).map fun i : Fin n' => (i : ℕ)
    with hP
  have hPQ : P.length + Q.length = n' := by
    have := filter_split (fun i : Fin n' => z i) (List.finRange n')
    simpa [hP, hQ] using this
  have hQlt : ∀ b ∈ Q, b < n' := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hb
    exact i.isLt
  have hPlt : ∀ b ∈ P, b < n' := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hb
    exact i.isLt
  have hQmem : ∀ i : Fin n', z i = false → (i : ℕ) ∈ Q := by
    intro i hi
    exact List.mem_map.2 ⟨i, by simp [hi], rfl⟩
  have hPmem : ∀ i : Fin n', z i = true → (i : ℕ) ∈ P := by
    intro i hi
    exact List.mem_map.2 ⟨i, by simp [hi], rfl⟩
  have hQz : ∀ b ∈ Q, ∃ i : Fin n', (i : ℕ) = b ∧ z i = false := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact ⟨i, rfl, by simpa using (List.mem_filter.1 hi).2⟩
  have hPz : ∀ b ∈ P, ∃ i : Fin n', (i : ℕ) = b ∧ z i = true := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact ⟨i, rfl, by simpa using (List.mem_filter.1 hi).2⟩
  obtain ⟨gs1, out1, ok1, len1, hout1, ev1⟩ := orList m Q (m + 1) (by
    intro b hb
    rcases List.mem_cons.1 hb with hb | hb
    · omega
    · have := hQlt b hb; omega)
  obtain ⟨gs2, out2, ok2, len2, hout2, ev2⟩ :=
    andList (m + 1 + gs1.length) P (m + 1 + gs1.length + 1) (by
      intro b hb
      rcases List.mem_cons.1 hb with hb | hb
      · omega
      · have := hPlt b hb; omega)
  refine ⟨[⟨GateOp.or, []⟩] ++ gs1 ++ [⟨GateOp.not, [out1]⟩] ++ gs2, out2, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | hg) | hg
    · subst hg; simp [Ok]
    · exact ok1 g hg
    · subst hg; simp [Ok]
    · exact ok2 g hg
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_append]
    have e0 : wiresFrom [⟨GateOp.or, []⟩] w = w ++ [false] := rfl
    rw [e0]
    set w2 := wiresFrom gs1 (w ++ [false]) with hw2
    have l2 : w2.length = m + 1 + gs1.length := by
      rw [hw2, length_wiresFrom]; simp [hw]
    have e2 : wiresFrom [⟨GateOp.not, [out1]⟩] w2 = w2 ++ [!(w2.getD out1 false)] := rfl
    rw [e2]
    have old : ∀ b : ℕ, b < m → (w2 ++ [!(w2.getD out1 false)]).getD b false = w.getD b false := by
      intro b hb
      rw [List.getD_append _ _ _ _ (by omega), hw2, getD_wiresFrom _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ (by omega)]
    have hnew : (w2 ++ [!(w2.getD out1 false)]).getD (m + 1 + gs1.length) false =
        !(w2.getD out1 false) := by
      rw [← l2, getD_snoc_eq]
    have h1 := ev1 (w ++ [false]) (by simp [hw])
    rw [← hw2] at h1
    have hm0 : (w ++ [false]).getD m false = false := by
      rw [← hw, getD_snoc_eq]
    have oldw : ∀ b : ℕ, b < m → (w ++ [false]).getD b false = w.getD b false := by
      intro b hb
      rw [List.getD_append _ _ _ _ (by omega)]
    rw [ev2 _ (by simp [l2])]
    apply decide_eq_decide.2
    constructor
    · intro h i
      have hN := h (m + 1 + gs1.length) List.mem_cons_self
      rw [hnew, h1] at hN
      have hno : ¬ ∃ b ∈ m :: Q, (w ++ [false]).getD b false = true := by
        simpa using hN
      cases hz : z i with
      | true =>
        have := h (i : ℕ) (List.mem_cons_of_mem _ (hPmem i hz))
        rw [old _ (by have := i.isLt; omega)] at this
        exact this
      | false =>
        cases hwi : w.getD (i : ℕ) false with
        | false => rfl
        | true =>
          exfalso
          apply hno
          refine ⟨(i : ℕ), List.mem_cons_of_mem _ (hQmem i hz), ?_⟩
          rw [oldw _ (by have := i.isLt; omega)]
          exact hwi
    · intro h b hb
      rcases List.mem_cons.1 hb with hb | hb
      · rw [hb, hnew, h1]
        have hno : ¬ ∃ b ∈ m :: Q, (w ++ [false]).getD b false = true := by
          rintro ⟨c, hc, hv⟩
          rcases List.mem_cons.1 hc with hc | hc
          · rw [hc, hm0] at hv
            exact Bool.false_ne_true hv
          · obtain ⟨i, rfl, hz⟩ := hQz c hc
            rw [oldw _ (by have := i.isLt; omega), h i, hz] at hv
            exact Bool.false_ne_true hv
        simpa using hno
      · obtain ⟨i, rfl, hz⟩ := hPz b hb
        rw [old _ (by have := i.isLt; omega), h i, hz]

/-- The OR of the indicators of the points of `L`, built at wire offset `m`. -/
theorem dnf (n' : ℕ) (m : ℕ) (hm : n' ≤ m) : ∀ L : List (Fin n' → Bool),
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ 1 + L.length * (n' + 3) ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false =
          decide (∃ z ∈ L, ∀ i : Fin n', w.getD i false = z i) := by
  intro L
  induction L with
  | nil =>
    refine ⟨[⟨GateOp.or, []⟩], m, ?_, by simp, by simp, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      simp [Ok]
    · intro w hw
      have e : wiresFrom [⟨GateOp.or, []⟩] w = w ++ [false] := rfl
      rw [e, ← hw, getD_snoc_eq]
      simp
  | cons z L ih =>
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih
    obtain ⟨gs', out', ok', len', hout', ev'⟩ := point n' z (m + gs.length) (by omega)
    refine ⟨gs ++ gs' ++ [⟨GateOp.or, [out, out']⟩], m + gs.length + gs'.length, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact ok g hg
      · exact ok' g hg
      · subst hg; simp [Ok]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      have e : (L.length + 1) * (n' + 3) = L.length * (n' + 3) + (n' + 3) := by ring
      rw [e]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      set v' := wiresFrom gs' v with hv'
      have lv' : v'.length = m + gs.length + gs'.length := by rw [hv', length_wiresFrom, lv]
      have e1 : v'.getD out false = decide (∃ z ∈ L, ∀ i : Fin n', w.getD i false = z i) := by
        rw [hv', getD_wiresFrom _ _ _ (by omega)]
        exact ev w hw
      have e2 : v'.getD out' false = decide (∀ i : Fin n', w.getD i false = z i) := by
        rw [ev' v lv]
        apply decide_eq_decide.2
        have hi : ∀ i : Fin n', v.getD (i : ℕ) false = w.getD (i : ℕ) false := by
          intro i
          rw [hv, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
        simp only [hi]
      have step : wiresFrom [⟨GateOp.or, [out, out']⟩] v'
          = v' ++ [GateOp.or.eval ([out, out'].map fun i => v'.getD i false)] := rfl
      rw [step, ← lv', getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [e1, e2, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨y, hy, h⟩ | h)
        · exact ⟨y, Or.inr hy, h⟩
        · exact ⟨z, Or.inl rfl, h⟩
      · rintro ⟨y, hy | hy, h⟩
        · exact Or.inr (hy ▸ h)
        · exact Or.inl ⟨y, hy, h⟩

/-- A function on `n'` inputs with `c` true points has circuit size `1 + c * (n' + 3)`. -/
theorem few_true (n' : ℕ) (f : (Fin n' → Bool) → Bool) :
    HasCircuitSize n' f
      (1 + (Finset.univ.filter fun z : Fin n' → Bool => f z = true).card * (n' + 3)) := by
  obtain ⟨gs, out, ok, len, _, ev⟩ :=
    dnf n' n' le_rfl (Finset.univ.filter fun z : Fin n' → Bool => f z = true).toList
  rw [Finset.length_toList] at len
  refine ⟨⟨gs, out⟩, ok, len, fun x => ?_⟩
  have h := ev (List.ofFn x) (by simp)
  show (wiresFrom gs (List.ofFn x)).getD out false = f x
  rw [h, Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨z, hz, he⟩
    have hxz : x = z := funext fun i => by rw [← he i, getD_ofFn]
    rw [hxz]
    exact (Finset.mem_filter.1 (Finset.mem_toList.1 hz)).2
  · intro hx
    exact ⟨x, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩),
      fun i => getD_ofFn x i⟩

/-! ## A table entry follows one input position at most, and follows it everywhere -/

/-- Every value of `g` is fixed by at most one input position. -/
def Cert1 {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) : Prop :=
  ∀ x : Fin n → Bool, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
    ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → g y = g x

/-- If `g` changes between two points that differ at position `i` only, the value at one of
them is fixed by position `i`. -/
theorem dep1 {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) (h : Cert1 g) (x z : Fin n → Bool)
    (i : Fin n) (hzx : ∀ k : Fin n, k ≠ i → z k = x k) (hne : g z ≠ g x) :
    ∀ u : Fin n → Bool, u i = z i → g u = g z := by
  obtain ⟨S, c, hS⟩ := h z
  by_cases hi : i ∈ S
  · have hall : ∀ k ∈ S, k = i := fun k hk => Finset.card_le_one.1 c k hk i hi
    intro u hu
    apply hS
    intro k hk
    rw [hall k hk]
    exact hu
  · exfalso
    apply hne
    exact (hS x (fun k hk => (hzx k (fun e => hi (e ▸ hk))).symm)).symm

/-- A function with certificates of size one cannot change under a flip at `i` and also under
a flip at another position `j`. -/
theorem same_two {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) (h : Cert1 g) (x : Fin n → Bool)
    (i j : Fin n) (hij : i ≠ j) (hi : g (Function.update x i (!x i)) ≠ g x)
    (hj : g (Function.update x j (!x j)) ≠ g x) : False :=
  hj (dep1 g h (Function.update x i (!x i)) x i
    (fun k hk => (Function.update_of_ne hk _ x).symm) (fun e => hi e.symm)
    (Function.update x j (!x j)) (Function.update_of_ne hij _ x))

/-- The entry cannot become undefined under a flip at `i` and change value under a flip at
another position `j`: flipping both would give the pair `false, true`, which is no code. -/
theorem mixed {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (b c : Bool) (hx : E x = some b)
    (hi : E (Function.update x i (!x i)) = none)
    (hj : E (Function.update x j (!x j)) = some c) (hcb : c ≠ b) : False := by
  have hDi := dep1 (fun u => (E u).isSome) hD x (Function.update x i (!x i)) i
    (fun k hk => Function.update_of_ne hk _ x) (by simp [hi, hx])
  have hVj := dep1 (fun u => (E u).getD false) hV x (Function.update x j (!x j)) j
    (fun k hk => Function.update_of_ne hk _ x) (by simpa [hj, hx] using hcb)
  have hb : b = false := by
    by_contra hb
    exact same_two (fun u => (E u).getD false) hV x i j hij (by simpa [hi, hx] using Ne.symm hb)
      (by simpa [hj, hx] using hcb)
  have h1 := hDi (Function.update (Function.update x i (!x i)) j (!x j))
    (Function.update_of_ne hij _ _)
  have h2 := hVj (Function.update (Function.update x i (!x i)) j (!x j)) (by simp)
  simp only [hi, hj] at h1 h2
  subst hb
  cases hu : E (Function.update (Function.update x i (!x i)) j (!x j)) with
  | none => rw [hu] at h2; cases c <;> simp_all
  | some d => rw [hu] at h1; simp at h1

/-- An entry defined at `x` keeps its value under a flip at `i` or under a flip at `j`. -/
theorem two_change {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (b : Bool) (hx : E x = some b) :
    E (Function.update x i (!x i)) = some b ∨ E (Function.update x j (!x j)) = some b := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hi, hj⟩ := hcon
  cases ei : E (Function.update x i (!x i)) with
  | none =>
    cases ej : E (Function.update x j (!x j)) with
    | none =>
      exact same_two (fun u => (E u).isSome) hD x i j hij (by simp [ei, hx]) (by simp [ej, hx])
    | some c =>
      exact mixed E hD hV x i j hij b c hx ei ej (fun e => hj (by rw [ej, e]))
  | some c =>
    have hc : c ≠ b := fun e => hi (by rw [ei, e])
    cases ej : E (Function.update x j (!x j)) with
    | none => exact mixed E hD hV x j i (Ne.symm hij) b c hx ej ei hc
    | some c' =>
      have hc' : c' ≠ b := fun e => hj (by rw [ej, e])
      exact same_two (fun u => (E u).getD false) hV x i j hij (by simpa [ei, hx] using hc)
        (by simpa [ej, hx] using hc')

/-- Flipping one position of an input that is not of odd weight gives one of odd weight. -/
theorem flip_odd {n : ℕ} (x : Fin n → Bool) (i : Fin n)
    (hx : ¬ (Finset.univ.filter fun k : Fin n => x k = true).card % 2 = 1) :
    (Finset.univ.filter fun k : Fin n => Function.update x i (!x i) k = true).card % 2 = 1 := by
  cases hxi : x i with
  | false =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!false) k = true) =
        insert i (Finset.univ.filter fun k : Fin n => x k = true) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [hset, Finset.card_insert_of_notMem (by simp [hxi])]
    omega
  | true =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!true) k = true) =
        (Finset.univ.filter fun k : Fin n => x k = true).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hmem : i ∈ Finset.univ.filter fun k : Fin n => x k = true := by simp [hxi]
    have hpos := Finset.card_pos.2 ⟨i, hmem⟩
    rw [hset, Finset.card_erase_of_mem hmem]
    omega

/-- `tableIndex` is injective. -/
theorem tableIndex_inj : ∀ (K : ℕ) (x y : Fin K → Bool), tableIndex x = tableIndex y → x = y
  | 0, x, y, _ => Subsingleton.elim _ _
  | K + 1, x, y, h => by
    have hx := tableIndex_snoc K (Fin.init x) (x (Fin.last K))
    have hy := tableIndex_snoc K (Fin.init y) (y (Fin.last K))
    rw [Fin.snoc_init_self] at hx hy
    have lx := tableIndex_lt K (Fin.init x)
    have ly := tableIndex_lt K (Fin.init y)
    rw [hx, hy] at h
    have hlast : x (Fin.last K) = y (Fin.last K) := by
      cases ex : x (Fin.last K) <;> cases ey : y (Fin.last K) <;> simp [ex, ey] at h ⊢ <;> omega
    have hinit : Fin.init x = Fin.init y := by
      apply tableIndex_inj K
      rw [hlast] at h
      omega
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]

/-- A function with certificates of size one that changes under the flip of `i` at one input
changes under the flip of `i` at every input. -/
theorem change_all {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) (h : Cert1 g)
    (x : Fin n → Bool) (i : Fin n) (hne : g (Function.update x i (!x i)) ≠ g x)
    (u : Fin n → Bool) : g (Function.update u i (!u i)) ≠ g u := by
  have h1 : ∀ v : Fin n → Bool, v i = !x i → g v = g (Function.update x i (!x i)) := by
    intro v hv
    exact dep1 g h x (Function.update x i (!x i)) i (fun k hk => Function.update_of_ne hk _ x)
      hne v (by simp [hv])
  have h2 : ∀ v : Fin n → Bool, v i = x i → g v = g x :=
    dep1 g h (Function.update x i (!x i)) x i
      (fun k hk => (Function.update_of_ne hk _ x).symm) (fun e => hne e.symm)
  by_cases hu : u i = x i
  · rw [h2 u hu, h1 _ (by simp [hu])]
    exact hne
  · have hu' : u i = !x i := by
      cases hui : u i <;> cases hxi : x i <;> simp_all
    rw [h1 u hu', h2 _ (by simp [hu'])]
    exact fun e => hne e.symm

/-- An entry that changes under the flip of `i` at one input changes under it at every
input. -/
theorem entry_all {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x : Fin n → Bool) (i : Fin n) (hne : E (Function.update x i (!x i)) ≠ E x)
    (u : Fin n → Bool) : E (Function.update u i (!u i)) ≠ E u := by
  by_cases hd : (E (Function.update x i (!x i))).isSome = (E x).isSome
  · by_cases hv : (E (Function.update x i (!x i))).getD false = (E x).getD false
    · exfalso
      apply hne
      cases h1 : E (Function.update x i (!x i)) <;> cases h2 : E x <;> simp_all
    · intro e
      exact change_all (fun u => (E u).getD false) hV x i hv u
        (congrArg (fun o : Option Bool => o.getD false) e)
  · intro e
    exact change_all (fun u => (E u).isSome) hD x i hd u
      (congrArg (fun o : Option Bool => o.isSome) e)

/-- An entry changes under the flips of one position at most. -/
theorem entry_one {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x y : Fin n → Bool) (i j : Fin n) (hi : E (Function.update x i (!x i)) ≠ E x)
    (hj : E (Function.update y j (!y j)) ≠ E y) : i = j := by
  by_contra hij
  have hjx := entry_all E hD hV y j hj x
  cases hx : E x with
  | some b =>
    rcases two_change E hD hV x i j hij b hx with h | h
    · exact hi (h.trans hx.symm)
    · exact hjx (h.trans hx.symm)
  | none =>
    cases hx' : E (Function.update x i (!x i)) with
    | none => exact hi (hx'.trans hx.symm)
    | some c =>
      have hback : Function.update (Function.update x i (!x i)) i
          (!(Function.update x i (!x i)) i) = x := by simp
      rcases two_change E hD hV (Function.update x i (!x i)) i j hij c hx' with h | h
      · rw [hback, hx] at h
        simp at h
      · exact entry_all E hD hV y j hj (Function.update x i (!x i)) (h.trans hx'.symm)

/-- Positions sent by an injection to distinct places below `N` outside `A` leave room. -/
theorem count_aux {n N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.range N) (S : Finset (Fin n))
    (κ : Fin n → ℕ) (hinj : Function.Injective κ) (h : ∀ i ∈ S, κ i < N ∧ κ i ∉ A) :
    A.card + S.card ≤ N := by
  have hd : Disjoint A (S.image κ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    exact (h i hi).2 ha
  have hsub : A ∪ S.image κ ⊆ Finset.range N := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hA ha
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact Finset.mem_range.2 (h i hi).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinj,
    Finset.card_range] at hc
  exact hc

/-! ## The statement -/

/-- The sharper form: `n ≤ 2 ^ n'` and `s < 1 + (2 ^ n' - n + 1) * (n' + 3)`. -/
theorem linear_strong (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    n ≤ 2 ^ n' ∧ s < 1 + (2 ^ n' - n + 1) * (n' + 3) := by
  classical
  have hD : ∀ k : ℕ, k < 2 ^ n' → Cert1 fun u : Fin n → Bool => ((T u).getD k none).isSome := by
    intro k hk u
    obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * k) u
    refine ⟨S, c, fun v hv => ?_⟩
    have h := hS v hv
    rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).1,
      (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).1] at h
    exact Option.some.inj h
  have hV : ∀ k : ℕ, k < 2 ^ n' →
      Cert1 fun u : Fin n → Bool => ((T u).getD k none).getD false := by
    intro k hk u
    obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * k + 1) u
    refine ⟨S, c, fun v hv => ?_⟩
    have h := hS v hv
    rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).2,
      (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).2] at h
    exact Option.some.inj h
  -- every position is followed by some entry
  have reads : ∀ (i : Fin n) (x : Fin n → Bool), ∃ k : ℕ, k < 2 ^ n' ∧
      (T (Function.update x i (!x i))).getD k none ≠ (T x).getD k none := by
    intro i x
    by_contra hcon
    have hall : ∀ k : ℕ, k < 2 ^ n' →
        (T (Function.update x i (!x i))).getD k none = (T x).getD k none := by
      intro k hk
      by_contra hne
      exact hcon ⟨k, hk, hne⟩
    have hT : T (Function.update x i (!x i)) = T x := by
      apply List.ext_getElem
      · rw [(hfmt _).2, (hfmt _).2]
      · intro k h1 h2
        have := hall k (by rw [← (hfmt x).2]; exact h2)
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
        exact this
    have hw : w (Function.update x i (!x i)) = w x := by
      rw [(hfmt _).1, (hfmt x).1, hT]
    by_cases hx : (Finset.univ.filter fun k : Fin n => x k = true).card % 2 = 1
    · apply flip_even x i (!x i) (by simp) hx
      rw [hred, hw, ← hred]
      exact hx
    · apply hx
      rw [hred, ← hw, ← hred]
      exact flip_odd x i hx
  -- an input with the fewest entries `some true`
  obtain ⟨x0, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n → Bool))
    (fun x => ((Finset.range (2 ^ n')).filter fun k => (T x).getD k none = some true).card)
    ⟨fun _ => false, Finset.mem_univ _⟩
  have key : ∀ i : Fin n, ∃ k : ℕ, k < 2 ^ n' ∧
      (T (Function.update x0 i (!x0 i))).getD k none ≠ (T x0).getD k none ∧
      (T x0).getD k none ≠ some true := by
    intro i
    by_contra hcon
    have hall : ∀ k : ℕ, k < 2 ^ n' →
        (T (Function.update x0 i (!x0 i))).getD k none ≠ (T x0).getD k none →
        (T x0).getD k none = some true := by
      intro k hk hne
      by_contra ht
      exact hcon ⟨k, hk, hne, ht⟩
    obtain ⟨k0, hk0, hne0⟩ := reads i x0
    have hsub : ((Finset.range (2 ^ n')).filter fun k =>
        (T (Function.update x0 i (!x0 i))).getD k none = some true) ⊆
        ((Finset.range (2 ^ n')).filter fun k => (T x0).getD k none = some true) := by
      intro k hk
      obtain ⟨hkr, hkt⟩ := Finset.mem_filter.1 hk
      refine Finset.mem_filter.2 ⟨hkr, ?_⟩
      by_cases e : (T (Function.update x0 i (!x0 i))).getD k none = (T x0).getD k none
      · rw [← e]; exact hkt
      · exact hall k (Finset.mem_range.1 hkr) e
    have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
      ⟨k0, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk0, hall k0 hk0 hne0⟩, fun hmem =>
        hne0 ((Finset.mem_filter.1 hmem).2.trans (hall k0 hk0 hne0).symm)⟩)
    have := hmin (Function.update x0 i (!x0 i)) (Finset.mem_univ _)
    omega
  choose κ hκN hκne hκt using key
  have hinj : Function.Injective κ := by
    intro i j hij
    exact entry_one (fun u => (T u).getD (κ i) none) (hD _ (hκN i)) (hV _ (hκN i)) x0 x0 i j
      (hκne i) (by rw [hij]; exact hκne j)
  have h0 := count_aux ((Finset.range (2 ^ n')).filter fun k => (T x0).getD k none = some true)
    (Finset.filter_subset _ _) Finset.univ κ hinj
    (fun i _ => ⟨hκN i, fun hmem => hκt i (Finset.mem_filter.1 hmem).2⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h0
  -- an input that is not of odd weight with few entries `some true` bounds `s`
  have close : ∀ (x1 : Fin n → Bool) (c : ℕ),
      ¬ (Finset.univ.filter fun i : Fin n => x1 i = true).card % 2 = 1 →
      ((Finset.range (2 ^ n')).filter fun k => (T x1).getD k none = some true).card ≤ c →
      s < 1 + c * (n' + 3) := by
    intro x1 c hx1 hc
    by_contra hge
    apply hx1
    rw [hred]
    refine ⟨n', s, T x1, (hfmt x1).1, (hfmt x1).2,
      fun z => decide ((T x1).getD (tableIndex z) none = some true), ?_, ?_⟩
    · intro z b hb
      show decide ((T x1).getD (tableIndex z) none = some true) = b
      rw [hb]
      cases b <;> simp
    · refine hasCircuitSize_mono ?_ (few_true n' _)
      have hcard : (Finset.univ.filter fun z : Fin n' → Bool =>
          decide ((T x1).getD (tableIndex z) none = some true) = true).card ≤
          ((Finset.range (2 ^ n')).filter fun k => (T x1).getD k none = some true).card := by
        refine Finset.card_le_card_of_injOn tableIndex ?_ ?_
        · intro z hz
          have hz' := (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).2
          exact Finset.mem_coe.2 (Finset.mem_filter.2
            ⟨Finset.mem_range.2 (tableIndex_lt n' z), of_decide_eq_true hz'⟩)
        · intro a _ b _ hab
          exact tableIndex_inj n' a b hab
      have := Nat.mul_le_mul_right (n' + 3) (hcard.trans hc)
      omega
  refine ⟨by omega, ?_⟩
  by_cases hx : (Finset.univ.filter fun k : Fin n => x0 k = true).card % 2 = 1
  · have hpos : 0 < (Finset.univ.filter fun k : Fin n => x0 k = true).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    have hn : 0 < n := i.pos
    have h1 := count_aux ((Finset.range (2 ^ n')).filter fun k =>
        (T (Function.update x0 i (!x0 i))).getD k none = some true)
      (Finset.filter_subset _ _) (Finset.univ.erase i) κ hinj (by
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.1 hj).1
        refine ⟨hκN j, fun hmem => ?_⟩
        have hsame : (T (Function.update x0 i (!x0 i))).getD (κ j) none =
            (T x0).getD (κ j) none := by
          by_contra e
          exact hji (entry_one (fun u => (T u).getD (κ j) none) (hD _ (hκN j)) (hV _ (hκN j))
            x0 x0 i j e (hκne j)).symm
        exact hκt j (hsame ▸ (Finset.mem_filter.1 hmem).2))
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
    exact close (Function.update x0 i (!x0 i)) (2 ^ n' - n + 1)
      (flip_even x0 i (!x0 i) (by simp) hx) (by omega)
  · have := close x0 (2 ^ n' - n) hx (by omega)
    have hle : (2 ^ n' - n) * (n' + 3) ≤ (2 ^ n' - n + 1) * (n' + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The statement of `L-meta-049`. -/
theorem linear (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    n ≤ 2 ^ n' ∧ s < (2 * (2 ^ n' - n) + 4) * (n' + 1) + 4 := by
  obtain ⟨h1, h2⟩ := linear_strong n n' s w T hq hfmt hred
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  cases n' with
  | zero =>
    have : 2 ^ 0 - n ≤ 1 := by simp
    omega
  | succ k =>
    generalize 2 ^ (k + 1) - n = d
    have e1 : (d + 1) * (k + 1 + 3) = d * k + 4 * d + k + 4 := by ring
    have e2 : (2 * d + 4) * (k + 1 + 1) = 2 * (d * k) + 4 * d + 4 * k + 8 := by ring
    rw [e1, e2]
    omega

/-- The count that follows: a 1-local reduction of parity on `n ≥ 1` bits to partial MCSP with
tables of length `2 ^ n'` needs `2 ^ (n - 1)` to be at most the number of circuits of size
`t = (2 * (2 ^ n' - n) + 4) * (n' + 1) + 4` on `n'` inputs, in the checked bound of
`LocalCore.count_le`. -/
theorem linear_count (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hn : 1 ≤ n) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    2 ^ (n - 1) ≤ ((2 * (2 ^ n' - n) + 4) * (n' + 1) + 4 + 1) *
      ((3 * ((n' + ((2 * (2 ^ n' - n) + 4) * (n' + 1) + 4) + 2) *
        (n' + ((2 * (2 ^ n' - n) + 4) * (n' + 1) + 4) + 2))) ^
          ((2 * (2 ^ n' - n) + 4) * (n' + 1) + 4) *
        (n' + ((2 * (2 ^ n' - n) + 4) * (n' + 1) + 4) + 1)) :=
  (LocalPrivate2.count_explicit n n' s w T hn hq hfmt hred).trans
    (LocalCore.cnt_mono (le_refl n') (le_of_lt (linear n n' s w T hq hfmt hred).2))

end PEqualNP.MetaComplexity.Helpers.LocalLinear
