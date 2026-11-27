import PEqualNP.MetaComplexity.Helpers.FewNotPlan

/-!
# The few-NOT conditional: the base case `PBaseG`

Unverified, a conjecture on paper until a checker accepts a row. The piece `PBaseG` of
`Helpers/FewNotPlan.lean` (no NOT gate left), proved from its own hypotheses L-meta-270
(`H270`), L-meta-669 at the base (`H669at`) and the sub-family statement (`PSub`), which stay
hypotheses: nothing here imports or proves them.

Route: with no NOT gate the gates are AND/OR of fan-in at most two; `H669at` at the base `y`
gives `gates'` (fan-in exactly two, no longer) computing every output that is not constant on
the forced cube; each output of a set missing `y` is non-constant there (empty input gives
`false`, one point of the set gives `true`); `PSub` re-indexes the sets missing `y`; `H270`
with `k = K` and `c = min K (d - 1)` gives `m' * min K (d - 1) ≤ gates'.length`; the kill
bound gives `m - kappa b ≤ m'`.
-/

namespace PEqualNP.MetaComplexity.FewNot

open PEqualNP.CircuitLowerBounds

/-- No NOT gate (an index map from `Fin 0`) and AND/OR/NOT gates: AND/OR gates. -/
theorem fnb_andOr2_of_not0 (gates : List Gate) (hops : OpsOK gates)
    (hn : NotAtMost 0 gates) : AndOr2 gates := by
  intro g hg
  obtain ⟨ι, hι⟩ := hn
  refine ⟨?_, (hops g hg).2⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  rcases (hops _ hg).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨j, _⟩ := hι i h
    exact j.elim0

/-- The kill bound as a lower bound on the number of sets missing `y`. -/
theorem fnb_card_disj {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ)
    (hF : FamG n m d S kappa) (b : ℕ) (y : Finset (Fin n)) (hy : y.card ≤ b) :
    m - kappa b ≤ (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card := by
  have hk := hF.2.2 b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

/-- The forced input of `H669at`: the points of `y` true, the others read from `x`. -/
def fnb_force {n : ℕ} (y : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i

/-- The window lemma: on the forced input of an `x` with at most `K` true points, an output of a
set missing `y` is the OR of the set on `x`. -/
theorem fnb_right_force {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) (hr : Right S y K gates out) (w : Fin m)
    (hw : Disjoint (S w) y) (x : Fin n → Bool)
    (hx : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K) :
    Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) =
      decide (∃ v ∈ S w, x v = true) := by
  have hv : ∀ v ∈ S w, fnb_force y x v = x v := fun v hv => by
    have : v ∉ y := Finset.disjoint_left.mp hw hv
    simp [fnb_force, this]
  rw [hr w (fnb_force y x) hw (fun p hp => by simp [fnb_force, hp]) ?_]
  · simp only [decide_eq_decide]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [← hv v h1]; exact h2⟩,
      fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [hv v h1]; exact h2⟩⟩
  · refine le_trans (Finset.card_le_card ?_) hx
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    simpa [fnb_force, h2] using h1

/-- A single point has one true coordinate. -/
theorem fnb_card_single {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hc
  rw [ha, hc]

/-- THE BASE CASE `PBaseG`. -/
theorem fnb_main : PBaseG := by
  intro h270 h669 hsub n m d S kappa hF b K y gates out hy hops hnot hright
  rw [fnp_genG_zero]
  rcases Nat.eq_zero_or_pos (min K (d - 1)) with h0 | hpos
  · rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  obtain ⟨hK, hd⟩ := Nat.lt_min.mp hpos
  obtain ⟨gates', r, hg', hlen, hcomp⟩ := h669 n gates y (fnb_andOr2_of_not0 gates hops hnot)
  obtain ⟨m', e, hm', _, hiff, hcard', hpair'⟩ :=
    hsub n m (d - 1) S y (fun i => by rw [hF.1 i]; omega) hF.2.1
  have hc : ∀ w : Fin m, Disjoint (S w) y → ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K →
      Circuit.eval ⟨gates', r (out w)⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w hw x hx
    have hne : ∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) ≠
          Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x')) := by
      obtain ⟨p, hp⟩ : (S w).Nonempty := by
        rw [← Finset.card_pos, hF.1 w]
        omega
      refine ⟨fun _ => false, fun q => decide (q = p), ?_⟩
      rw [fnb_right_force S y K gates out hright w hw _ (by simp),
        fnb_right_force S y K gates out hright w hw _ ((fnb_card_single p).trans hK)]
      have h2 : ∃ v ∈ S w, decide (v = p) = true := ⟨p, hp, by simp⟩
      rw [decide_eq_true h2]
      simp
    have h1 := hcomp (out w) hne x
    exact h1.trans (fnb_right_force S y K gates out hright w hw x hx)
  have hdisj : ∀ i : Fin m', Disjoint (S (e i)) y := fun i => (hiff (e i)).mpr ⟨i, rfl⟩
  have key := h270 n m' K (fun i => S (e i)) ⟨gates', 0⟩ (fun i => r (out (e i)))
    (fun _ => min K (d - 1)) hpair' (fun i => by rw [hcard' i]; omega) hg'
    (fun i p => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = true ↔ _
      rw [hc (e i) (hdisj i) _ ((fnb_card_single p).trans hK)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = false
      rw [hc (e i) (hdisj i) x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv
      simp [hz v hv])
    (fun _ => min_le_left _ _) (fun i => by rw [hcard' i]; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at key
  have hm : m - kappa b ≤ m' := hm' ▸ fnb_card_disj S kappa hF b y hy
  calc (m - kappa b) * min K (d - 1) ≤ m' * min K (d - 1) := Nat.mul_le_mul_right _ hm
    _ ≤ gates'.length := key
    _ ≤ gates.length := hlen

end PEqualNP.MetaComplexity.FewNot
