import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class, wire tools: monotone values, propagation, Lemma U, Lemma 2 (first half), Lemma 1(a)

Proofs of the tier 2 pieces `ToolMono`, `ToolZero`, `ToolProp`, `ToolU`, `ToolLower` and
`ToolLemma1a` of `LocPlan.lean` (row `L-meta-115`). None needs another piece.
-/

namespace PEqualNP.MetaComplexity.Loc.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc

/-- A gate of a clean NOT-free list is an AND or an OR of two earlier wires. -/
theorem gate2 {m : ℕ} {gs : List Gate} (h : MClean m gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) : ∃ j k, j < m + p ∧ k < m + p ∧ g.inputs = [j, k] ∧
      ((g.op = GateOp.and ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j && vl gs x k)) ∨
       (g.op = GateOp.or ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j || vl gs x k))) := by
  rcases h.1 p g hp with ⟨hn, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hn (h.2 g (List.mem_of_getElem? hp))
  · refine ⟨j, k, hj, hk, hin, ?_⟩
    rcases hop with hop | hop
    · left
      refine ⟨hop, fun x => ?_⟩
      rw [vl_gate gs h.1 x p g hp, hop, hin]
      simp [GateOp.eval]
    · right
      refine ⟨hop, fun x => ?_⟩
      rw [vl_gate gs h.1 x p g hp, hop, hin]
      simp [GateOp.eval]

theorem ToolMono_proof : ToolMono := by
  intro m gs h x y hxy j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjm : j < m
    · rw [vl_input gs x j hjm] at hj
      rw [vl_input gs y j hjm]
      exact hxy _ hj
    · obtain ⟨p, rfl⟩ : ∃ p, j = m + p := ⟨j - m, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        rw [vl_beyond gs x (m + p) (by omega)] at hj
        cases hj
      | some g =>
        obtain ⟨a, b, ha, hb, _, hc | hc⟩ := gate2 h hp
        · rw [hc.2] at hj ⊢
          simp only [Bool.and_eq_true] at hj ⊢
          exact ⟨ih a ha hj.1, ih b hb hj.2⟩
        · rw [hc.2] at hj ⊢
          simp only [Bool.or_eq_true] at hj ⊢
          rcases hj with h1 | h1
          · exact Or.inl (ih a ha h1)
          · exact Or.inr (ih b hb h1)

/-- Every wire of a clean NOT-free list is false at the zero point. -/
theorem zero_all {m : ℕ} {gs : List Gate} (h : MClean m gs) :
    ∀ j, vl gs (fun _ : Fin m => false) j = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjm : j < m
    · rw [vl_input gs _ j hjm]
    · obtain ⟨p, rfl⟩ : ∃ p, j = m + p := ⟨j - m, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        exact vl_beyond gs _ (m + p) (by omega)
      | some g =>
        obtain ⟨a, b, ha, hb, _, hc | hc⟩ := gate2 h hp
        · rw [hc.2, ih a ha, ih b hb]; rfl
        · rw [hc.2, ih a ha, ih b hb]; rfl

theorem ToolZero_proof : ToolZero := by
  intro m gs h j _
  exact zero_all h j

theorem ToolProp_proof : ToolProp := by
  intro m gs x x' D K hcl hin hg j hj hjD
  refine agree_B gs hcl x x' (fun j => j ∈ D) K ?_ ?_ j hj hjD
  · intro j hjm hjD
    rw [vl_input gs x j hjm, vl_input gs x' j hjm]
    exact hin ⟨j, hjm⟩ hjD
  · intro p g hp hpK hpD hr _
    rcases hg p g hp hpK hpD with h1 | h1
    · obtain ⟨a, ha, haD⟩ := hr
      exact absurd haD (h1 a ha)
    · exact h1

theorem ToolU_proof : ToolU := by
  intro m gs t q h hR p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hpl hv
    obtain ⟨g, hp⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hpl⟩
    obtain ⟨a, b, ha, hb, hin, hc⟩ := gate2 h hp
    have key : ∃ c ∈ g.inputs, vl gs (pt {t}) c = true := by
      rcases hc with hc | hc
      · rw [hc.2] at hv
        simp only [Bool.and_eq_true] at hv
        exact ⟨a, by simp [hin], hv.1⟩
      · rw [hc.2] at hv
        simp only [Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact ⟨a, by simp [hin], hv⟩
        · exact ⟨b, by simp [hin], hv⟩
    obtain ⟨c, hcin, hcv⟩ := key
    have hclt : c < m + p := (h.1 p g hp).lt c hcin
    by_cases hcm : c < m
    · rw [vl_input gs _ c hcm] at hcv
      have hct : (⟨c, hcm⟩ : Fin m) = t := by simpa [pt] using hcv
      left
      have hmem : p ∈ RdSet gs t := mem_rdSet.2 ⟨g, hp, by rw [← hct]; exact hcin⟩
      rw [hR] at hmem
      exact Finset.mem_singleton.1 hmem
    · obtain ⟨p', rfl⟩ : ∃ p', c = m + p' := ⟨c - m, by omega⟩
      rcases ih p' (by omega) (by omega) hcv with e | hex
      · subst e
        right
        exact ⟨p, mem_rdSet.2 ⟨g, hp, hcin⟩, hv⟩
      · right
        exact hex

/-- Two clean lists of one length that differ at most at index `p` agree at `x` on every wire
below `J`, when gate `p` agrees at `x` or lies at or above `J`. -/
theorem agree_set {m : ℕ} {gs gs' : List Gate} (h1 : CleanL m gs) (h2 : CleanL m gs')
    (hl : gs.length = gs'.length) (p : ℕ) (he : ∀ p', p' ≠ p → gs[p']? = gs'[p']?)
    (x : Fin m → Bool) (J : ℕ) (hJ : m + p < J → vl gs x (m + p) = vl gs' x (m + p)) :
    ∀ j, j < J → vl gs x j = vl gs' x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjm : j < m
    · rw [vl_input gs x j hjm, vl_input gs' x j hjm]
    · obtain ⟨p', rfl⟩ : ∃ p', j = m + p' := ⟨j - m, by omega⟩
      by_cases hpp : p' = p
      · subst hpp
        exact hJ hj
      · cases hg : gs[p']? with
        | none =>
          have : gs.length ≤ p' := List.getElem?_eq_none_iff.1 hg
          rw [vl_beyond gs x (m + p') (by omega), vl_beyond gs' x (m + p') (by omega)]
        | some g =>
          have hg' : gs'[p']? = some g := by rw [← he p' hpp, hg]
          rw [vl_gate gs h1 x p' g hg, vl_gate gs' h2 x p' g hg']
          congr 1
          apply List.map_congr_left
          intro a ha
          have := (h1 p' g hg).lt a ha
          exact ih a this (by omega)

theorem ToolLower_proof : ToolLower := by
  intro m gs o P z p W h hp hW hz hpW hWo
  set gs' := gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩ with hgs'
  have hself : gs'[p]? = some ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩ := List.getElem?_set_self hp
  have hcl' : CleanL m gs' := by
    intro p' g hg
    by_cases hpp : p = p'
    · subst hpp
      rw [hself] at hg
      cases hg
      exact Or.inr ⟨Or.inl rfl, z, z, by omega, by omega, rfl⟩
    · rw [hgs', List.getElem?_set_ne hpp] at hg
      exact h.1 p' g hg
  have hnf : NotFree gs' := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | hg
    · exact h.2 g hg
    · rw [hg]
      exact fun e => GateOp.noConfusion e
  have hl : gs.length = gs'.length := (List.length_set ..).symm
  have he : ∀ p', p' ≠ p → gs[p']? = gs'[p']? :=
    fun p' hne => (List.getElem?_set_ne (Ne.symm hne)).symm
  have hval' : ∀ x : Fin m → Bool, vl gs' x (m + p) = x z := by
    intro x
    rw [vl_gate gs' hcl' x p _ hself]
    simp [GateOp.eval, vl_input gs' x z z.isLt]
  refine ⟨⟨hcl', hnf⟩, ?_, ?_⟩
  · intro x hx
    cases hWx : vl gs x W
    · have hpf : vl gs x (m + p) = false := by
        cases hq : vl gs x (m + p)
        · rfl
        · have := hpW x hx hq
          rw [hWx] at this
          cases this
      have := agree_set h.1 hcl' hl p he x (o + 1)
        (fun _ => by rw [hpf, hval', hz x hx]) o (by omega)
      rw [this]
      simp
    · rw [hWo x hx hWx]
      simp
  · intro x j hj
    exact (agree_set h.1 hcl' hl p he x (m + p) (fun h => absurd h (lt_irrefl _)) j hj).symm

theorem ToolLemma1a_proof : ToolLemma1a := by
  intro n G A gs o s t q w hAF hcl hC hR hOr hst z hzt hFz
  have hzs : z s = false := by
    cases h' : z s
    · rfl
    · exfalso
      have : F G A z = true := (F_true G A z).2 (Or.inr ⟨s, t, hst, h', hzt⟩)
      rw [hFz] at this
      cases this
  by_contra hw0
  have hw : vl gs z w = true := by simpa using hw0
  obtain ⟨g, hq, hop, hin⟩ := hOr
  have hos : o ≠ (s : ℕ) := by
    intro hos
    have h1 := hC (pt {s})
    rw [hos, vl_input gs _ s s.isLt] at h1
    have hF : F G A (pt {s}) = false := by
      rw [Bool.eq_false_iff]
      intro hF
      rw [F_true] at hF
      rcases hF with ⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩
      · simp [pt] at hxa
        subst hxa
        exact hAF a t hst ha
      · simp [pt] at hi hj
        subst hi
        subst hj
        exact G.irrefl hij
    rw [hF] at h1
    simp [pt] at h1
  have hw_ne : w ≠ (s : ℕ) := by
    intro e
    rw [e, vl_input gs z s s.isLt] at hw
    simp only [Fin.eta] at hw
    rw [hzs] at hw
    cases hw
  have hag : vl gs z o = vl gs (Function.update z s true) o := by
    refine agree_B gs hcl z (Function.update z s true) (fun j => j = (s : ℕ)) (o + 1) ?_ ?_ o
      (by omega) hos
    · intro j hjn hjs
      rw [vl_input gs _ j hjn, vl_input gs _ j hjn]
      have hne : (⟨j, hjn⟩ : Fin n) ≠ s := fun e => hjs (by rw [← e])
      rw [Function.update_of_ne hne]
    · intro p g' hp _ _ hr hprev
      obtain ⟨a, ha, has⟩ := hr
      have hpq : p = q := by
        have hmem : p ∈ RdSet gs s := mem_rdSet.2 ⟨g', hp, has ▸ ha⟩
        rw [hR] at hmem
        exact Finset.mem_singleton.1 hmem
      subst hpq
      have hg : g' = g := by
        rw [hp] at hq
        exact Option.some.inj hq
      subst hg
      have hwlt : w < n + p := (hcl p g' hp).lt w (by rcases hin with e | e <;> rw [e] <;> simp)
      have hww : vl gs (Function.update z s true) w = true := by
        rw [← hprev w hwlt hw_ne]
        exact hw
      rw [vl_gate gs hcl z p g' hp, vl_gate gs hcl _ p g' hp, hop]
      rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, hw, hww]
  have hFz' : F G A (Function.update z s true) = true :=
    (F_true G A _).2 (Or.inr ⟨s, t, hst, by simp,
      by rw [Function.update_of_ne (G.ne_of_adj hst).symm]; exact hzt⟩)
  have h1 := hC z
  have h2 := hC (Function.update z s true)
  rw [← h1, hag, h2, hFz'] at hFz
  cases hFz

end PEqualNP.MetaComplexity.Loc.Wires
