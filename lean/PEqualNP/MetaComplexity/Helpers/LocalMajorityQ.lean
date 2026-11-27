import Mathlib.Data.Fintype.Fin
import PEqualNP.MetaComplexity.Helpers.LocalMajority

/-!
# Every table of a q-local reduction of parity to partial MCSP is easy

Helper for `L-meta-043`. In a `q`-local reduction of parity to partial MCSP of fixed format, on
at least `m = 4 * q + 1` input bits, EVERY input (odd or even) has a function of circuit size at
most `m * s + 3 * m ^ 2` consistent with its table.

An odd input has a witness of size `s` (the reduction). For an even input `x`, flip one of the
first `m` positions: the `m` neighbours are odd and have witnesses of size `s`. A table entry
defined at `x` is written with two output positions, each fixed by at most `q` input positions;
a neighbour flipped outside these at most `2 * q` positions has the same entry. So at least
`2 * q + 1` of the `m` witnesses agree with the entry, and "at least `2 * q + 1` of the `m`
witnesses are true" is consistent with the table of `x`.

The circuit part is general (`thr_size`): "at least `t` of the functions `fs` are true" has
circuit size `1 + fs.length * (s + 1 + 2 * t)` when every function of `fs` has size `s`. The
circuits are put one after the other (`reloc_wires`), each followed by one gate that copies its
output and by `2 * t` gates that update a unary counter: wire `k` of the counter says "at least
`k + 1` of the functions so far are true".
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalMajorityQ

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalPrivate PEqualNP.MetaComplexity.Helpers.LocalMajority

/-! ## A unary counter -/

/-- The gates that add the wire `A` to a unary counter kept on the wires `row 0`, `row 1`, ...:
appended after `L` wires, for each `k < K` an AND gate (wire `L + 2 * k`) and an OR gate (wire
`L + 2 * k + 1`, the new wire `k` of the counter). -/
def stage (L A : ℕ) (row : ℕ → ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => stage L A row k ++
      [⟨GateOp.and, if k = 0 then [A] else [row (k - 1), A]⟩, ⟨GateOp.or, [row k, L + 2 * k]⟩]

theorem stage_length (L A : ℕ) (row : ℕ → ℕ) : ∀ K : ℕ, (stage L A row K).length = 2 * K
  | 0 => rfl
  | K + 1 => by
    simp only [stage, List.length_append, stage_length L A row K, List.length_cons,
      List.length_nil]
    omega

theorem stage_ok (L A : ℕ) (row : ℕ → ℕ) : ∀ K : ℕ, ∀ g ∈ stage L A row K, Ok g
  | 0 => by simp [stage]
  | K + 1 => by
    intro g hg
    simp only [stage, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact stage_ok L A row K g hg
    · by_cases h : K = 0 <;> simp [Ok, h]
    · simp [Ok]

theorem wires_two (W : List Bool) (g1 g2 : Gate) :
    wiresFrom [g1, g2] W =
      W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)] ++
        [g2.op.eval (g2.inputs.map fun i =>
          (W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]).getD i false)] := rfl

/-- The new counter wire `k` is: the old wire `k`, or the old wire `k - 1` and the wire `A`
(for `k = 0`: or the wire `A`). -/
theorem stage_spec (V : List Bool) (L A : ℕ) (row : ℕ → ℕ) (hL : V.length = L) (hA : A < L) :
    ∀ K : ℕ, (∀ k < K, row k < L) → ∀ k < K,
      (wiresFrom (stage L A row K) V).getD (L + 2 * k + 1) false =
        (V.getD (row k) false ||
          ((decide (k = 0) || V.getD (row (k - 1)) false) && V.getD A false)) := by
  subst hL
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
    intro hrow k hk
    have ih' := ih (fun k hk => hrow k (by omega))
    have hlen := length_wiresFrom (stage V.length A row K) V
    rw [stage_length] at hlen
    have hst : ∀ i, i < V.length →
        (wiresFrom (stage V.length A row K) V).getD i false = V.getD i false :=
      fun i hi => getD_wiresFrom _ _ i hi
    have e : wiresFrom (stage V.length A row (K + 1)) V =
        wiresFrom [⟨GateOp.and, if K = 0 then [A] else [row (K - 1), A]⟩,
          ⟨GateOp.or, [row K, V.length + 2 * K]⟩] (wiresFrom (stage V.length A row K) V) :=
      wiresFrom_append _ _ _
    rw [e]
    generalize wiresFrom (stage V.length A row K) V = W at ih' hlen hst ⊢
    rw [wires_two]
    by_cases hkK : k < K
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
      exact ih' k hkK
    · have hkK' : k = K := by omega
      subst hkK'
      have hrk := hrow k (by omega)
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      have i1 : V.length + 2 * k + 1 - (W ++ [GateOp.and.eval
          ((if k = 0 then [A] else [row (k - 1), A]).map fun i => W.getD i false)]).length = 0 := by
        simp; omega
      rw [i1]
      have a1 : ∀ c : Bool, (W ++ [c]).getD (row k) false = V.getD (row k) false := by
        intro c
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hst _ hrk
      have a2 : ∀ c : Bool, (W ++ [c]).getD (V.length + 2 * k) false = c := by
        intro c
        rw [List.getD_append_right _ _ _ _ (by omega)]
        have : V.length + 2 * k - W.length = 0 := by omega
        rw [this]
        rfl
      simp only [List.getD_cons_zero, List.map_cons, List.map_nil, a1, a2]
      by_cases hk0 : k = 0
      · have hA' := hst A hA
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hA'
        simp [hk0, GateOp.eval, hA']
      · have hA' := hst A hA
        have hrk' := hst _ (hrow (k - 1) (by omega))
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hA' hrk'
        simp [hk0, GateOp.eval, hA', hrk']

/-! ## One more circuit -/

/-- The gates `gs`, then the block `cg` renumbered to run after them, then a copy of the
block's output wire `o`, then the counter update. -/
def step (m : ℕ) (gs cg : List Gate) (o : ℕ) (row : ℕ → ℕ) (K : ℕ) : List Gate :=
  gs ++ cg.map (rel m gs.length) ++
    [⟨GateOp.or, [out m gs.length cg.length (m + gs.length + cg.length) o]⟩] ++
    stage (m + gs.length + cg.length + 1) (m + gs.length + cg.length) row K

theorem step_spec (x : List Bool) (gs cg : List Gate) (o : ℕ) (row : ℕ → ℕ) (K : ℕ)
    (hrow : ∀ k < K, row k < x.length + gs.length) : ∀ k < K,
    (wiresFrom (step x.length gs cg o row K) x).getD
        (x.length + gs.length + cg.length + 1 + 2 * k + 1) false =
      ((wiresFrom gs x).getD (row k) false ||
        ((decide (k = 0) || (wiresFrom gs x).getD (row (k - 1)) false) &&
          (wiresFrom cg x).getD o false)) := by
  intro k hk
  obtain ⟨p, hp, hlp⟩ := wiresFrom_prefix gs x
  obtain ⟨t, ht, hlt⟩ := wiresFrom_prefix cg x
  have r2 : wiresFrom (cg.map (rel x.length gs.length)) (x ++ p) = x ++ p ++ t := by
    have h := reloc_wires x p cg []
    rw [List.append_nil, List.append_nil, ht, List.drop_left, hlp] at h
    exact h
  have hcopy : (x ++ p ++ t).getD (out x.length gs.length cg.length
      (x.length + gs.length + cg.length) o) false = (x ++ t).getD o false :=
    getD_mid _ x p t [] gs.length cg.length _ o (by simp) (by simp [hlp, hlt]; omega)
      hlp.symm hlt.symm
  have hV : (x ++ p ++ t ++ [(x ++ t).getD o false]).length =
      x.length + gs.length + cg.length + 1 := by
    simp [hlp, hlt]
    omega
  have e : wiresFrom (step x.length gs cg o row K) x =
      wiresFrom (stage (x.length + gs.length + cg.length + 1) (x.length + gs.length + cg.length)
        row K) (x ++ p ++ t ++ [(x ++ t).getD o false]) := by
    unfold step
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_append, hp, r2]
    congr 1
    simp only [wiresFrom, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, hcopy]
    simp [GateOp.eval]
  have old : ∀ i, i < x.length + gs.length →
      (x ++ p ++ t ++ [(x ++ t).getD o false]).getD i false = (x ++ p).getD i false := by
    intro i hi
    rw [List.getD_append _ _ _ _ (by simp [hlp, hlt]; omega),
      List.getD_append _ _ _ _ (by simp [hlp]; omega)]
  have hAval : (x ++ p ++ t ++ [(x ++ t).getD o false]).getD
      (x.length + gs.length + cg.length) false = (x ++ t).getD o false := by
    rw [List.getD_append_right _ _ _ _ (by simp [hlp, hlt]; omega)]
    have : x.length + gs.length + cg.length - (x ++ p ++ t).length = 0 := by
      simp [hlp, hlt]
      omega
    rw [this]
    rfl
  rw [e, stage_spec _ _ _ row hV (by omega) K (fun k hk => by have := hrow k hk; omega) k hk,
    old _ (hrow k hk), old _ (hrow (k - 1) (by omega)), hAval, hp, ht]

/-! ## At least `t` of a list of functions -/

/-- The gates of all the circuits of `fs` with a unary counter of height `K`: wire `row k` says
"at least `k + 1` of the functions of `fs` are true". -/
theorem thr_gates (n s K : ℕ) : ∀ fs : List ((Fin n → Bool) → Bool),
    (∀ f ∈ fs, HasCircuitSize n f s) →
    ∃ (gs : List Gate) (row : ℕ → ℕ), (∀ g ∈ gs, Ok g) ∧
      gs.length ≤ 1 + fs.length * (s + 1 + 2 * K) ∧ (∀ k < K, row k < n + gs.length) ∧
      ∀ (z : Fin n → Bool), ∀ k < K, (wiresFrom gs (List.ofFn z)).getD (row k) false =
        decide (k + 1 ≤ (fs.map fun f => f z).count true) := by
  intro fs
  induction fs with
  | nil =>
    intro _
    refine ⟨[⟨GateOp.or, []⟩], fun _ => n, ?_, by simp, fun k _ => by simp, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      simp [Ok]
    · intro z k _
      have e : wiresFrom [⟨GateOp.or, []⟩] (List.ofFn z) = List.ofFn z ++ [false] := rfl
      rw [e, List.getD_append_right _ _ _ _ (by simp)]
      simp
  | cons f fs ih =>
    intro h
    obtain ⟨gs, row, hok, hlen, hrow, hval⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨C, F, S, E⟩ := h f List.mem_cons_self
    refine ⟨step n gs C.gates C.output row K,
      fun k => n + gs.length + C.gates.length + 1 + 2 * k + 1, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [step, List.mem_append, List.mem_map, List.mem_singleton] at hg
      rcases hg with ((hg | ⟨g', hg', rfl⟩) | rfl) | hg
      · exact hok g hg
      · exact ok_rel _ _ _ (F g' hg')
      · simp [Ok]
      · exact stage_ok _ _ _ _ g hg
    · simp only [Circuit.size] at S
      simp only [step, List.length_append, List.length_map, List.length_cons, List.length_nil,
        stage_length]
      have e : (fs.length + 1) * (s + 1 + 2 * K) =
          fs.length * (s + 1 + 2 * K) + (s + 1 + 2 * K) := by ring
      rw [e]
      generalize fs.length * (s + 1 + 2 * K) = X at hlen ⊢
      omega
    · intro k hk
      simp only [step, List.length_append, List.length_map, List.length_cons, List.length_nil,
        stage_length]
      omega
    · intro z k hk
      have hs := step_spec (List.ofFn z) gs C.gates C.output row K
        (by simpa using hrow) k hk
      simp only [List.length_ofFn] at hs
      have e := E z
      simp only [Circuit.eval, wires_eq] at e
      rw [hs, hval z k hk, hval z (k - 1) (by omega), e, List.map_cons, List.count_cons]
      rw [Bool.eq_iff_iff]
      cases f z
      · simp
      · simp
        omega

/-- "At least `t` of the functions of `fs` are true" has circuit size
`1 + fs.length * (s + 1 + 2 * t)` when every function of `fs` has circuit size `s`. -/
theorem thr_size (n s t : ℕ) (fs : List ((Fin n → Bool) → Bool))
    (h : ∀ f ∈ fs, HasCircuitSize n f s) (ht : 1 ≤ t) :
    HasCircuitSize n (fun z => decide (t ≤ (fs.map fun f => f z).count true))
      (1 + fs.length * (s + 1 + 2 * t)) := by
  obtain ⟨gs, row, hok, hlen, _, hval⟩ := thr_gates n s t fs h
  refine ⟨⟨gs, row (t - 1)⟩, hok, hlen, fun z => ?_⟩
  have e := hval z (t - 1) (by omega)
  have e' : t - 1 + 1 = t := by omega
  rw [e'] at e
  simpa only [Circuit.eval, wires_eq] using e

/-! ## The statement -/

/-- An input of odd weight has a witness of size `s` consistent with its table. -/
theorem odd_witness (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool))
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) (hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f s := by
  obtain ⟨m, s', T', hw, hlen, f, hc, hs⟩ := (hred x).1 hx
  rw [(hfmt x).1] at hw
  obtain ⟨e1, e2⟩ := LocalConstruct.split_unique s s' _ _ hw
  have e3 := LocalConstruct.encodePartial_injective _ _ e2
  subst e1
  subst e3
  have e4 : m = n' := Nat.pow_right_injective (Nat.le_refl 2) (hlen.symm.trans (hfmt x).2)
  subst e4
  exact ⟨f, hc, hs⟩

/-- An input whose output agrees with that of `x` at the two positions of entry `k` has the
entry of `x` there, when that entry is defined. -/
theorem entry_same (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool))
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (x y : Fin n → Bool) (k : ℕ) (hk : k < 2 ^ n') (b : Bool)
    (he : (T x).getD k none = some b)
    (h1 : (w y)[s + 1 + 2 * k]? = (w x)[s + 1 + 2 * k]?)
    (h2 : (w y)[s + 1 + 2 * k + 1]? = (w x)[s + 1 + 2 * k + 1]?) :
    (T y).getD k none = some b := by
  rw [(word_pair s (T y) (w y) (hfmt y).1 k (by rw [(hfmt y).2]; exact hk)).1,
    (word_pair s (T x) (w x) (hfmt x).1 k (by rw [(hfmt x).2]; exact hk)).1, he] at h1
  rw [(word_pair s (T y) (w y) (hfmt y).1 k (by rw [(hfmt y).2]; exact hk)).2,
    (word_pair s (T x) (w x) (hfmt x).1 k (by rw [(hfmt x).2]; exact hk)).2, he] at h2
  cases hy : (T y).getD k none with
  | none => rw [hy] at h1; simp at h1
  | some c => rw [hy] at h2; simp at h2; rw [h2]

/-- Every table is easy: the statement of `L-meta-043`. -/
theorem majq_witness (n n' s q : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (_hq0 : 0 < q) (hn : 4 * q + 1 ≤ n)
    (hq : QueryLocal n q w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧
      HasCircuitSize n' f ((4 * q + 1) * s + 3 * (4 * q + 1) ^ 2) := by
  by_cases hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1
  · obtain ⟨f, hc, hs⟩ := odd_witness n n' s w T hfmt hred x hx
    exact ⟨f, hc, hasCircuitSize_mono (by nlinarith [Nat.zero_le (q * s)]) hs⟩
  · have wit : ∀ l : Fin n, ∃ f : (Fin n' → Bool) → Bool,
        Consistent n' (T (Function.update x l (!x l))) f ∧ HasCircuitSize n' f s :=
      fun l => odd_witness n n' s w T hfmt hred _ (flip_odd x l hx)
    choose F hFc hFs using wit
    obtain ⟨G, hG⟩ : ∃ G : Fin (4 * q + 1) → (Fin n' → Bool) → Bool,
        G = fun l => F (Fin.castLE hn l) := ⟨_, rfl⟩
    refine ⟨fun z => decide (2 * q + 1 ≤ ((List.ofFn G).map fun f => f z).count true), ?_, ?_⟩
    · intro e b he
      by_cases hk : tableIndex e < 2 ^ n'
      · obtain ⟨Sd, cd, hSd⟩ := hq (s + 1 + 2 * tableIndex e) x
        obtain ⟨Sv, cv, hSv⟩ := hq (s + 1 + 2 * tableIndex e + 1) x
        have good : ∀ l : Fin (4 * q + 1), Fin.castLE hn l ∉ Sd ∪ Sv → G l e = b := by
          intro l hl
          rw [Finset.mem_union, not_or] at hl
          rw [hG]
          apply hFc
          exact entry_same n n' s w T hfmt x _ _ hk b he
            (hSd _ fun i hi => Function.update_of_ne (by rintro rfl; exact hl.1 hi) _ _)
            (hSv _ fun i hi => Function.update_of_ne (by rintro rfl; exact hl.2 hi) _ _)
        have hbad : (Finset.univ.filter fun l : Fin (4 * q + 1) => ¬ G l e = b).card ≤ 2 * q := by
          calc (Finset.univ.filter fun l : Fin (4 * q + 1) => ¬ G l e = b).card
              ≤ (Sd ∪ Sv).card :=
                Finset.card_le_card_of_injOn (fun l => Fin.castLE hn l)
                  (fun l hl => by
                    by_contra hc
                    exact (Finset.mem_filter.1 hl).2 (good l hc))
                  (fun a _ b _ hab => Fin.castLE_injective hn hab)
            _ ≤ Sd.card + Sv.card := Finset.card_union_le _ _
            _ ≤ 2 * q := by omega
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (4 * q + 1)))) (fun l => G l e = b)
        rw [Finset.card_univ, Fintype.card_fin] at hsum
        show decide (2 * q + 1 ≤ ((List.ofFn G).map fun f => f e).count true) = b
        rw [List.map_ofFn, List.count_ofFn]
        simp only [Function.comp]
        cases b with
        | true =>
          rw [decide_eq_true_eq]
          omega
        | false =>
          have hle : (Finset.univ.filter fun l : Fin (4 * q + 1) => G l e = true).card ≤
              (Finset.univ.filter fun l : Fin (4 * q + 1) => ¬ G l e = false).card :=
            Finset.card_le_card fun l hl => by
              rw [Finset.mem_filter] at hl ⊢
              exact ⟨hl.1, by rw [hl.2]; simp⟩
          rw [decide_eq_false_iff_not]
          omega
      · exfalso
        have hl : (T x).length ≤ tableIndex e := by
          rw [(hfmt _).2]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at he
        simp at he
    · have hsz := thr_size n' s (2 * q + 1) (List.ofFn G)
        (fun f hf => by
          rw [List.mem_ofFn] at hf
          obtain ⟨l, rfl⟩ := hf
          rw [hG]
          exact hFs _) (by omega)
      rw [List.length_ofFn] at hsz
      exact hasCircuitSize_mono (by nlinarith [Nat.zero_le (q * s), Nat.zero_le (q * q)]) hsz

end PEqualNP.MetaComplexity.Helpers.LocalMajorityQ
