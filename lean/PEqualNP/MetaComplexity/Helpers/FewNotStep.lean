import PEqualNP.MetaComplexity.Helpers.FewNotPlan

/-!
# The few-NOT conditional: the step `PStepG`

Unverified, a conjecture on paper until a checker accepts a row. From the split `PSplitS` (a
hypothesis, never proved here), the general claim at `s` NOT gates gives the claim at `s + 1`.
Fix `j ≤ K` (no bound by `d` is used). Either the circuit has at most `s` NOT gates (the
claim at `s` on the window at `j ≤ K`), or it has a first NOT gate after an AND/OR prefix. If some input of the
window at `j` makes the wire read by that NOT true, its true set `y'` is a new base: on the
window above `y'` the wire is true (monotone), the NOT is replaced in place by OR of nothing,
and the claim at `s` applies at `b + j`, `K - j`. Otherwise the wire is false on the window at
`j`, the NOT is replaced by AND of nothing, and the claim at `s` applies at `b`, `j`.
-/

namespace PEqualNP.MetaComplexity.FewNot

open PEqualNP.CircuitLowerBounds

/-- The value the NOT gate reads: its first input wire after the prefix `pre`. -/
def fns_hv {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false

/-- `Right` on a smaller window. -/
theorem fns_right_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    {j K : ℕ} (hj : j ≤ K) (gates : List Gate) (out : Fin m → ℕ)
    (h : Right S y K gates out) : Right S y j gates out :=
  fun w x hd h1 h2 => h w x hd h1 (le_trans h2 hj)

/-- `Right` moves to a circuit that agrees on the window. -/
theorem fns_right_congr {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ)
    (hag : ∀ x : Fin n → Bool, Win y K x → ∀ o : ℕ,
      Circuit.eval ⟨gates', o⟩ (List.ofFn x) = Circuit.eval ⟨gates, o⟩ (List.ofFn x))
    (h : Right S y K gates out) : Right S y K gates' out := by
  intro w x hd h1 h2
  rw [hag x ⟨h1, h2⟩ (out w)]
  exact h w x hd h1 h2

/-- The true set of an input in the window at `j` has at most `b + j` points. -/
theorem fns_card_true {n : ℕ} (y : Finset (Fin n)) (b j : ℕ) (hy : y.card ≤ b)
    (x : Fin n → Bool) (hx : Win y j x) :
    (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ b + j := by
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true) ⊆
      y ∪ Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hpy : p ∈ y
    · exact Finset.mem_union_left _ hpy
    · exact Finset.mem_union_right _ (by simp [hp, hpy])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ b + j := Nat.add_le_add hy hx.2

/-- The window above the true set `y'` of an input of `W(y, j)`, at `K - j`, lies in
`W(y, K)`. -/
theorem fns_win_above {n : ℕ} (y : Finset (Fin n)) {j K : ℕ} (hj : j ≤ K)
    (x0 : Fin n → Bool) (hx0 : Win y j x0) (x : Fin n → Bool)
    (hx : Win (Finset.univ.filter (fun p : Fin n => x0 p = true)) (K - j) x) :
    Win y K x := by
  refine ⟨fun p hp => hx.1 p (by simp [hx0.1 p hp]), ?_⟩
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) ⊆
      Finset.univ.filter (fun p : Fin n => x0 p = true ∧ p ∉ y) ∪
      Finset.univ.filter (fun p : Fin n => x p = true ∧
        p ∉ Finset.univ.filter (fun p : Fin n => x0 p = true)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : x0 p = true
    · exact Finset.mem_union_left _ (by simp [h0, hp.2])
    · exact Finset.mem_union_right _ (by simp [h0, hp.1])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ j + (K - j) := Nat.add_le_add hx0.2 hx.2
    _ = K := by omega

/-- Sets missing the new base miss the old one. -/
theorem fns_right_base {n m : ℕ} (S : Fin m → Finset (Fin n)) (y y' : Finset (Fin n))
    (hyy : y ⊆ y') (K K' : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (hwin : ∀ x : Fin n → Bool, Win y' K' x → Win y K x)
    (h : Right S y K gates out) : Right S y' K' gates out := by
  intro w x hd h1 h2
  have hw := hwin x ⟨h1, h2⟩
  exact h w x (Finset.disjoint_of_subset_right hyy hd) hw.1 hw.2

/-- One term of the maximum, in the split case. -/
theorem fns_term_split {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ)
    (ih : ClaimG n m d S kappa s) (b K : ℕ) (y : Finset (Fin n)) (out : Fin m → ℕ)
    (hy : y.card ≤ b) (pre post : List Gate) (ins : List ℕ)
    (hpre : AndOr2 pre)
    (hopsA : OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hopsO : OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hnA : NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hnO : NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hR : Right S y K (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post) out)
    (j : ℕ) (hj : j ≤ K) :
    min (fewNotGenG m d kappa s (b + j) (K - j)) (fewNotGenG m d kappa s b j) ≤
      (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post).length := by
  classical
  by_cases hex : ∃ x0 : Fin n → Bool, Win y j x0 ∧ fns_hv pre ins x0 = true
  · obtain ⟨x0, hx0, hv⟩ := hex
    set y' := Finset.univ.filter (fun p : Fin n => x0 p = true) with hy'
    have hyy : y ⊆ y' := fun p hp => by simp [hy', hx0.1 p hp]
    have hRy := fns_right_base S y y' hyy K (K - j) _ out
      (fun x hx => fns_win_above y hj x0 hx0 x hx) hR
    have hRO : Right S y' (K - j)
        (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y' (K - j) _ _ out ?_ hRy
      intro x hx o
      apply OneNot.on1_piece_u_cheap
      exact OneNot.on1_piece_h n pre ins hpre x0 x
        (fun i hi => hx.1 i (by simp [hy', hi])) hv
    have := ih (b + j) (K - j) y' _ out (fns_card_true y b j hy x0 hx0) hopsO hnO hRO
    rw [fnp_variant_length pre post _ ({ op := GateOp.or, inputs := [] } : Gate)]
    exact le_trans (min_le_left _ _) this
  · have hRA : Right S y j
        (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y j _ _ out ?_ (fns_right_mono S y hj _ out hR)
      intro x hx o
      apply OneNot.on1_piece_d
      have hf : ¬ fns_hv pre ins x = true := fun ht => hex ⟨x, hx, ht⟩
      simpa [fns_hv] using hf
    have := ih b j y _ out hy hopsA hnA hRA
    rw [fnp_variant_length pre post _ ({ op := GateOp.and, inputs := [] } : Gate)]
    exact le_trans (min_le_right _ _) this

/-- THE STEP, `PStepG`. -/
theorem fns_main : PStepG := by
  intro hsplit n m d S kappa _hF s ih b K y gates out hy hops hnot hR
  rw [fnp_genG_succ]
  apply fn_foldr_max_le
  intro j hjr
  have hj : j ≤ K := by
    have := List.mem_range.mp hjr
    omega
  rcases hsplit gates s hops hnot with hle | ⟨pre, post, ins, heq, hpre, hopsA, hopsO, hnA, hnO⟩
  · exact le_trans (min_le_right _ _) (ih b j y gates out hy hops hle (fns_right_mono S y hj _ out hR))
  · subst heq
    exact fns_term_split S kappa s ih b K y out hy pre post ins hpre hopsA hopsO hnA hnO hR j hj

end PEqualNP.MetaComplexity.FewNot
