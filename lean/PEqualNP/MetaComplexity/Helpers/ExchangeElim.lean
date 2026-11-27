import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.LGP.ExchangeDraft

/-!
# The exchange lemma (E1) through the elimination pass

Helper for `L-meta-123`, `L-meta-124`. The alternative route of the design notes
(`notes/exchange/design.md`, section F6, last paragraph), for E1 only. The gates of `C` up to
and including wire `h` are kept; the pass of `Helpers/Elim.lean` runs on the rest with the
status of wire `h` set to the constant `true`. Its invariant then holds at every input where
wire `h` is true. Every gate that reads `h` simplifies and emits no gate (`elim_count`). The
output status decides the circuit: a constant `true` (one gate `AND []`), a constant `false`
(the kept gates and `NOT h`), or a wire (the new gates, `NOT h`, and an OR).
-/

namespace PEqualNP.MetaComplexity.Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- The gate list of the pass extends the one it starts from. -/
theorem elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]

/-- The counting lemma: if the status of old wire `k` is a constant, every gate reading `k`
saves one gate. -/
theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.contains k)
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons, List.countP_cons]
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega

/-- A reader count over positions from offset `m`: only gates at positions at least
`h + 1 - n` can count. -/
theorem countP_zipIdx_le (n h : ℕ) (f : Gate → Bool) : ∀ (l : List Gate) (m : ℕ),
    (l.zipIdx m).countP (fun p => decide (h < n + p.2) && f p.1)
      ≤ (l.drop (h + 1 - n - m)).countP f := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    rw [List.zipIdx_cons, List.countP_cons]
    have := ih (m + 1)
    by_cases hd : h + 1 - n - m = 0
    · rw [hd, List.drop_zero, List.countP_cons]
      have e : h + 1 - n - (m + 1) = 0 := by omega
      rw [e, List.drop_zero] at this
      have hlt : h < n + m := by omega
      by_cases hfa : f a = true <;> simp [hlt, hfa] <;> omega
    · obtain ⟨d, hd'⟩ : ∃ d, h + 1 - n - m = d + 1 := ⟨h + 1 - n - m - 1, by omega⟩
      rw [hd', List.drop_succ_cons]
      have e : h + 1 - n - (m + 1) = d := by omega
      rw [e] at this
      have hlt : ¬ h < n + m := by omega
      simp [hlt]
      exact this

/-- The effective inputs of a gate are the inputs of its normal form. -/
theorem eff_eq (g : Gate) :
    (match g.op with
     | GateOp.not => g.inputs.take 1
     | _ => g.inputs) = (normGate g).inputs := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

/-- The starting statuses: identity on the wires below `m`, except `h`, set to `true`. -/
def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Stat.const true else Stat.wire i

theorem startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Stat.const false) =
      if i < m then (if i = h then Stat.const true else Stat.wire i) else Stat.const false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩

/-- E1 with the effective-input test of the reader count given as any `f` equal to it. -/
theorem exchange_core (n : ℕ) (C : Circuit) (h : ℕ) (f : Gate → Bool)
    (hf : ∀ g, f g = (normGate g).inputs.contains h) (hC : FanInTwo C)
    (hcov : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) :
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1)
        ≤ C.size + 2 := by
  -- the reader count, bounded by the readers in the gates after `h`
  set r := C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1) with hr
  have hrle : r ≤ (C.gates.drop (h + 1 - n)).countP
      (fun g => (normGate g).inputs.contains h) := by
    have := countP_zipIdx_le n h f C.gates 0
    simp only [Nat.sub_zero] at this
    rw [hr]
    refine le_trans this (le_of_eq ?_)
    apply List.countP_congr
    intro g _
    rw [hf]
  have hrs : r ≤ C.gates.length := by
    refine le_trans hrle (le_trans (List.countP_le_length) ?_)
    simp
  -- the constant `true`
  have hconst : (∀ x : Fin n → Bool, circuitFun n C x = true) →
      ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧ D.size + r ≤ C.size + 2 := by
    intro hT
    refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      subst hg; simp
    · funext x
      rw [hT x]
      show (wiresFrom [⟨GateOp.and, []⟩] (List.ofFn x)).getD n false = true
      simp [wiresFrom, GateOp.eval]
    · simp only [Circuit.size, List.length_cons, List.length_nil]
      omega
  by_cases hex : ∃ x0 : Fin n → Bool, (C.wires (List.ofFn x0)).getD h false = true
  swap
  · apply hconst
    intro x
    apply hcov x
    push Not at hex
    simpa using hex x
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < n + C.size := by
    by_contra hlt
    rw [List.getD_eq_default _ _ (by
      rw [wires_eq, length_wiresFrom]; simp [Circuit.size] at hlt ⊢; omega)] at hx0
    cases hx0
  set k := h + 1 - n with hk
  have hks : k ≤ C.gates.length := by simp [Circuit.size] at hhs; omega
  have hhk : h < n + k := by omega
  set gs := C.gates.map normGate with hgs
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre, hgs]; omega
  have hlpost : post.length = C.gates.length - k := by simp [hpost, hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hokpre : ∀ g ∈ pre, Ok g := fun g hg => (hnok g (List.mem_of_mem_take hg)).1
  have hwC : ∀ y : List Bool, C.wires y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop, hgs, wiresFrom_norm]; rfl
  have hyl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := by simp
  -- wire `h` of `C` is wire `h` of the kept gates
  have hwh : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false
      = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    rw [hwC, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  -- the pass
  set acc := elim n post (startStats (n + pre.length) h, pre) with hacc
  have hinv : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      Inv n (List.ofFn x) (C.wires (List.ofFn x)) acc := by
    intro x hx
    rw [hwC, hacc]
    exact inv_elim n _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_start n h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨t, ht⟩ := elim_prefix n post (startStats (n + pre.length) h, pre)
  rw [← hacc] at ht
  have hcount := elim_count n h post (startStats (n + pre.length) h, pre) hnokpost
    (by simp [startStats]; omega)
    ⟨true, by rw [startStats_getD]; simp [hhk, hlpre]⟩
  rw [← hacc] at hcount
  have hR : post.countP (fun g => g.inputs.contains h)
      = (C.gates.drop k).countP (fun g => (normGate g).inputs.contains h) := by
    rw [hpost, hgs, ← List.map_drop, List.countP_map]; rfl
  have hLk : acc.2.length = k + t.length := by rw [ht]; simp [hlpre]
  have hsize : acc.2.length + r ≤ C.gates.length := by
    change acc.2.length + post.countP (fun g => g.inputs.contains h)
      ≤ pre.length + post.length at hcount
    rw [hlpre, hlpost, hR] at hcount
    omega
  -- wire `h` of the new gates
  have hwhA : ∀ x : Fin n → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false
      = (C.wires (List.ofFn x)).getD h false := by
    intro x
    rw [ht, wiresFrom_append, hwh,
      getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  have hval : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x))
        = circuitFun n C x := by
    intro x hx
    exact ((hinv x hx).2 C.output).2
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) :=
    ((hinv x0 hx0).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    cases c with
    | true =>
      apply hconst
      intro x
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>
      -- `F = NOT h`
      refine ⟨⟨pre ++ [⟨GateOp.not, [h]⟩], n + k⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hokpre g hg
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
          subst hg; simp
      · funext x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (n + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = n + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (n + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : (C.wires (List.ofFn x)).getD h false = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | wire j =>
    rw [hst] at hvalid
    have hj : j < n + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩], n + L + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact elim_ok n post _ hokpre g hg
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
        rcases hg with rfl | rfl <;> simp
    · funext x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩])
        (List.ofFn x)).getD (n + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = n + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = n + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, n + L].map fun i => W'.getD i false)]).getD
        (n + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (n + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : (C.wires (List.ofFn x)).getD h false = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
      omega

/-- E1, proved through the elimination pass. -/
theorem exchange' : StmtExchange := by
  intro n C h hC hcov
  exact exchange_core n C h (fun g => (match g.op with
         | GateOp.not => g.inputs.take 1
         | _ => g.inputs).contains h)
    (fun g => by obtain ⟨op, ins⟩ := g; cases op <;> rfl) hC hcov

/-- E2 from E1. -/
theorem twoReaders' : StmtTwoReaders := twoReaders_of_exchange exchange'

end PEqualNP.MetaComplexity.Exchange
