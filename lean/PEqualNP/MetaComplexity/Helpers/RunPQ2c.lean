import PEqualNP.MetaComplexity.Helpers.RunPQ2b

/-!
# The q2 side, stage 3: the two-fixing save

Conjecture until the checker accepts. Fix input `i` to `b` (the pass `passG`), then the input
`e = i.succAbove j` to `c` in the emitted list: the gates counted at the first fixing and the
gates of `passG` that read a constant at the second are both saved, arity kept.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- The emitted list is shorter than the source by the saved set. -/
theorem pq2_passG_len (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) :
    (passG n gs i b).length + S.card ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simpa [passG] using hcount

/-- The emitted list computes the restriction. -/
theorem pq2_passG_eval (n : ℕ) {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b)) :
    ∃ q, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y q = f (ins i b y) := by
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire q =>
    refine ⟨q, clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp), ?_⟩
    intro y
    rw [← hev, st_val_wire n gs hcl i b o q hst y]

/-- Two fixings: input `i` to `b`, then input `i.succAbove j` to `c`. The set `S1` is counted in
the source list, the set `S2` in the emitted list. -/
theorem pq2_save_two (n : ℕ) (f : (Fin (n + 2) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 2) gs) (hev : ∀ x : Fin (n + 2) → Bool, vl gs x o = f x)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (b c : Bool)
    (hnc1 : ∃ x y : Fin (n + 2) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 2) → Bool,
      f (Function.update (Function.update x i b) (i.succAbove j) c) ≠
        f (Function.update (Function.update y i b) (i.succAbove j) c))
    (S1 S2 : Finset ℕ) (hS1 : ∀ p ∈ S1, RC (n + 1) gs i b p)
    (hS2 : ∀ p ∈ S2, RC n (passG (n + 1) gs i b) j c p) :
    ∃ s', s' + S1.card + S2.card ≤ gs.length ∧ HasCircuitSize (n + 2)
      (fun x => f (Function.update (Function.update x i b) (i.succAbove j) c)) s' := by
  obtain ⟨q, hcl1, hev1⟩ := pq2_passG_eval (n + 1) hcl hev i b hnc1
  have hlen := pq2_passG_len (n + 1) gs hcl i b S1 hS1
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      (fun y : Fin (n + 1) → Bool => f (ins i b y)) (Function.update x j c) ≠
        (fun y : Fin (n + 1) → Bool => f (ins i b y)) (Function.update y j c) := by
    obtain ⟨x, y, h⟩ := hnc2
    refine ⟨fun k => x (i.succAbove k), fun k => y (i.succAbove k), ?_⟩
    have key : ∀ z : Fin (n + 2) → Bool,
        ins i b (Function.update (fun k : Fin (n + 1) => z (i.succAbove k) : Fin (n + 1) → Bool) j c)
          = Function.update (Function.update z i b) (i.succAbove j) c := by
      intro z
      show Fin.insertNth (α := fun _ => Bool) i b (Function.update (fun k : Fin (n + 1) => z (i.succAbove k) : Fin (n + 1) → Bool) j c) = _
      rw [Fin.insertNth_update]
      congr 1
      exact (upd_ins i b z).symm
    simp only [key]
    exact h
  obtain ⟨s', hs', hc⟩ := save n (fun y : Fin (n + 1) → Bool => f (ins i b y)) (passG (n + 1) gs i b) q
    hcl1 hev1 j c hnc' S2 hS2
  refine ⟨s', by omega, ?_⟩
  have h2 := PermInputs.relabel_size i.succAbove _ _ hc
  convert h2 using 1
  funext x
  have key : ins i b (Function.update (fun k : Fin (n + 1) => x (i.succAbove k) : Fin (n + 1) → Bool) j c)
      = Function.update (Function.update x i b) (i.succAbove j) c := by
    show Fin.insertNth (α := fun _ => Bool) i b (Function.update (fun k : Fin (n + 1) => x (i.succAbove k) : Fin (n + 1) → Bool) j c) = _
    rw [Fin.insertNth_update]
    congr 1
    exact (upd_ins i b x).symm
  simp only [Function.comp_def, key]

/-- A clean list for the restriction at `i := b`, of `s` gates, gives `Drop` with that size. -/
theorem pq2_drop_of_clean (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (i : Fin (n + 1)) (b : Bool)
    (gs' : List Gate) (q : ℕ) (hc : CleanL n gs')
    (hev : ∀ y : Fin n → Bool, vl gs' y q = f (ins i b y)) (s : ℕ) :
    ∃ s', s' ≤ gs'.length ∧ HasCircuitSize (n + 1) (fun x => f (Function.update x i b)) s' := by
  refine ⟨gs'.length, le_refl _, ?_⟩
  have h2 := PermInputs.relabel_size i.succAbove _ _ (has_of_clean n gs' q hc)
  convert h2 using 1
  funext x
  simp only [Function.comp_def]
  rw [hev, upd_ins]
  rfl

/-- The cleaning at `i := b` is a least list for the restriction, of exactly four fewer gates,
when four gates are saved and there is no drop of five. -/
theorem pq2_c1_least (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) (hcard : 4 ≤ S.card)
    (h5 : ¬ ∃ s', s' + 5 ≤ gs.length ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x i b)) s') :
    ∃ q, Least n (fun y => f (ins i b y)) (passG n gs i b) q ∧
      (passG n gs i b).length + 4 = gs.length := by
  obtain ⟨q, hcl1, hev1⟩ := pq2_passG_eval n L.hcl L.hev i b hnc
  have hlen := pq2_passG_len n gs L.hcl i b S hS
  have hge : gs.length ≤ (passG n gs i b).length + 4 := by
    by_contra hlt
    obtain ⟨s', hs', hc⟩ := pq2_drop_of_clean n f i b _ q hcl1 hev1 0
    exact h5 ⟨s', by omega, hc⟩
  refine ⟨q, ⟨hcl1, hev1, ?_⟩, by omega⟩
  intro gs' o' hc' hev'
  by_contra hlt
  obtain ⟨s', hs', hc⟩ := pq2_drop_of_clean n f i b gs' o' hc' hev' 0
  exact h5 ⟨s', by omega, hc⟩

/-- Shape (i) at an input `e` read by two OR gates saves four gates at `x_e := 1`: the two OR
readers and the two AND gates that read them. -/
theorem pq2_shape_four (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (e : Fin (n + 1))
    (p1 p2 : ℕ) (g1 g2 : Gate) (a1 a2 : ℕ) (ga1 ga2 : Gate) (u1 u2 : ℕ)
    (h12 : p1 ≠ p2) (h12' : a1 ≠ a2)
    (hg1 : gs[p1]? = some g1) (ho1 : g1.op = GateOp.or)
    (hu1 : g1.inputs = [(e : ℕ), u1] ∨ g1.inputs = [u1, (e : ℕ)])
    (hg2 : gs[p2]? = some g2) (ho2 : g2.op = GateOp.or)
    (hu2 : g2.inputs = [(e : ℕ), u2] ∨ g2.inputs = [u2, (e : ℕ)])
    (hga1 : gs[a1]? = some ga1) (hao1 : ga1.op = GateOp.and) (hin1 : n + 1 + p1 ∈ ga1.inputs)
    (hga2 : gs[a2]? = some ga2) (hao2 : ga2.op = GateOp.and) (hin2 : n + 1 + p2 ∈ ga2.inputs) :
    ∃ S : Finset ℕ, S.card = 4 ∧ (∀ p ∈ S, RC n gs e true p) := by
  have hmem1 : (e : ℕ) ∈ g1.inputs := by rcases hu1 with h | h <;> rw [h] <;> simp
  have hmem2 : (e : ℕ) ∈ g2.inputs := by rcases hu2 with h | h <;> rw [h] <;> simp
  have c1 : IsC n gs e true (n + 1 + p1) :=
    isC_reader hcl e p1 g1 hg1 hmem1 true (Or.inr (by simp [fixBit, ho1]))
  have c2 : IsC n gs e true (n + 1 + p2) :=
    isC_reader hcl e p2 g2 hg2 hmem2 true (Or.inr (by simp [fixBit, ho2]))
  have r1 : RC n gs e true p1 := rc_input true ⟨g1, hg1, hmem1⟩
  have r2 : RC n gs e true p2 := rc_input true ⟨g2, hg2, hmem2⟩
  have r3 : RC n gs e true a1 := rc_of_reads ⟨ga1, hga1, hin1⟩ c1
  have r4 : RC n gs e true a2 := rc_of_reads ⟨ga2, hga2, hin2⟩ c2
  have d13 : p1 ≠ a1 := by
    intro h; rw [h] at hg1; rw [hg1] at hga1; cases hga1; rw [hao1] at ho1; cases ho1
  have d14 : p1 ≠ a2 := by
    intro h; rw [h] at hg1; rw [hg1] at hga2; cases hga2; rw [hao2] at ho1; cases ho1
  have d23 : p2 ≠ a1 := by
    intro h; rw [h] at hg2; rw [hg2] at hga1; cases hga1; rw [hao1] at ho2; cases ho2
  have d24 : p2 ≠ a2 := by
    intro h; rw [h] at hg2; rw [hg2] at hga2; cases hga2; rw [hao2] at ho2; cases ho2
  refine ⟨{p1, p2, a1, a2}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [h12, d13, d14]),
      Finset.card_insert_of_notMem (by simp [d23, d24]),
      Finset.card_pair h12']
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption

end PEqualNP.MetaComplexity.Helpers.RunAsm
