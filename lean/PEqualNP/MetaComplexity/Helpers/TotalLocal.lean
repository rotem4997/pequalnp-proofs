import PEqualNP.MetaComplexity.Helpers.LocalClose

/-!
# The local reduction chain for total MCSP

Helper for `L-meta-039`. The chain of `LocalFormat`, `LocalCoreWf`, `LocalFinite` and
`LocalClose`, redone for the format of total instances: `replicate s true ++ false :: T` with a
table `T` of length `2 ^ n'`, one bit per entry.

* `formed`: a `q`-local map that sends the odd inputs into MCSP sends the all-false input to a
  word of the instance format, as soon as `2 q (log M + 2) < n`.
* `core`: from any decomposition of the image of the all-false input as an instance with size
  field `s`, that instance is not a member and the bound of the partial case holds.
* `finite`, `asymptotic`: the finite and the asymptotic forms.

The total format is simpler: after the separator every word of the right length is a table, and
a word that is not the instance with size field `s` and the table of `f` fails at one position,
so a certificate has `q` input positions where the partial case needs `2 q`. The constants of
the partial case are kept, so that its arithmetic (`LocalClose.key`, `LocalClose.arith`,
`LocalClose.logM_le`) is used as it stands.
-/

namespace PEqualNP.MetaComplexity.Helpers.TotalLocal

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalCore

/-! ## Table positions -/

theorem tableIndex_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem tableIndex_lt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [tableIndex_succ, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

/-! ## The head of an instance -/

/-- The word `u` starts with `s` times `true` and then one `false`. -/
def Head (s : ℕ) (u : List Bool) : Prop :=
  (∀ j : ℕ, j < s → u[j]? = some true) ∧ u[s]? = some false

theorem head_fmt (s : ℕ) (r : List Bool) : Head s (List.replicate s true ++ false :: r) :=
  ⟨(get_fmt s r).1, (get_fmt s r).2.1⟩

/-- A word without the head for `s` stays so whenever one of its positions is kept. -/
theorem head_witness (s : ℕ) (u : List Bool) (h : ¬ Head s u) :
    ∃ j : ℕ, ∀ u' : List Bool, u'[j]? = u[j]? → ¬ Head s u' := by
  by_cases h1 : ∀ j : ℕ, j < s → u[j]? = some true
  · exact ⟨s, fun u' e hf => h ⟨h1, by rw [← e]; exact hf.2⟩⟩
  · rw [not_forall] at h1
    obtain ⟨j, hj⟩ := h1
    rw [Classical.not_imp] at hj
    exact ⟨j, fun u' e hf => hj.2 (by rw [← e]; exact hf.1 j hj.1)⟩

/-! ## Well-formedness at the all-false input -/

/-- A `q`-local map with outputs of length at most `M` that sends every input of odd weight
into MCSP sends the all-false input to a word of the instance format, as soon as
`2 * q * (log M + 2) < n`. -/
theorem formed (n q M : ℕ) (w : (Fin n → Bool) → List Bool)
    (hq : QueryLocal n q w) (hM : ∀ x : Fin n → Bool, (w x).length ≤ M)
    (hodd : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 → w x ∈ MCSP)
    (hn : 2 * q * (Nat.log 2 M + 2) < n) :
    ∃ (n' s : ℕ) (T : List Bool),
      w (fun _ : Fin n => false) = List.replicate s true ++ false :: T ∧ T.length = 2 ^ n' := by
  by_contra hcon
  obtain ⟨S0, hS0c, hS0⟩ := LocalFormat.cert_length hq (fun _ : Fin n => false)
  have key : ∀ k : ℕ, ∃ S : Finset (Fin n), S.card ≤ 2 * q ∧
      ∀ s : ℕ, (w (fun _ : Fin n => false)).length = s + 1 + 2 ^ k →
        ∀ y : Fin n → Bool, (∀ i ∈ S, y i = (fun _ : Fin n => false) i) →
          ¬ Head s (w y) := by
    intro k
    by_cases hk : 1 + 2 ^ k ≤ (w (fun _ : Fin n => false)).length
    · have hnf : ¬ Head ((w (fun _ : Fin n => false)).length - (1 + 2 ^ k))
          (w (fun _ : Fin n => false)) := by
        rintro ⟨g1, g2⟩
        apply hcon
        refine ⟨k, _, _, fmt_of_bits _ _ g1 g2, ?_⟩
        rw [List.length_drop]
        generalize 2 ^ k = P at hk ⊢
        omega
      obtain ⟨j, hj⟩ := head_witness _ _ hnf
      obtain ⟨S, hSc, hS⟩ := hq j (fun _ : Fin n => false)
      refine ⟨S, by omega, fun s hs y hy => ?_⟩
      have es : s = (w (fun _ : Fin n => false)).length - (1 + 2 ^ k) := by omega
      rw [es]
      exact hj (w y) (hS y hy)
    · exact ⟨∅, by simp, fun s hs => (hk (by omega)).elim⟩
  choose S hSc hS using key
  have hU : (S0 ∪ (Finset.range (Nat.log 2 M + 1)).biUnion S).card
      ≤ 2 * q * (Nat.log 2 M + 2) := by
    have h1 := Finset.card_union_le S0 ((Finset.range (Nat.log 2 M + 1)).biUnion S)
    have h2 := Finset.card_biUnion_le_card_mul (Finset.range (Nat.log 2 M + 1)) S (2 * q)
      (fun k _ => hSc k)
    rw [Finset.card_range] at h2
    calc (S0 ∪ (Finset.range (Nat.log 2 M + 1)).biUnion S).card
        ≤ 2 * q + (Nat.log 2 M + 1) * (2 * q) := le_trans h1 (Nat.add_le_add hS0c h2)
      _ = 2 * q * (Nat.log 2 M + 2) := by ring
  obtain ⟨j, hj⟩ := LocalFormat.exists_notMem _ (lt_of_le_of_lt hU hn)
  have hagree := LocalFormat.unit_agree j _ hj
  obtain ⟨n', s, T, hT, hlen, -⟩ := hodd (LocalFormat.unit j) (LocalFormat.unit_odd j)
  have hL : (w (LocalFormat.unit j)).length = (w (fun _ : Fin n => false)).length :=
    hS0 (LocalFormat.unit j) (fun i hi => hagree i (Finset.mem_union_left _ hi))
  have hl : (w (LocalFormat.unit j)).length = s + 1 + 2 ^ n' := by
    rw [hT, List.length_append, List.length_replicate, List.length_cons, hlen]
    omega
  rw [hL] at hl
  have hM0 := hM (fun _ : Fin n => false)
  have hn' : n' < Nat.log 2 M + 1 := by
    have hp : 2 ^ n' ≤ M := by omega
    have hlog := Nat.le_log_of_pow_le (by norm_num) hp
    omega
  refine hS n' s hl (LocalFormat.unit j)
    (fun i hi => hagree i (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨n', Finset.mem_range.2 hn', hi⟩))) ?_
  rw [hT]
  exact head_fmt s T

/-! ## The instance format, one position at a time -/

/-- The string `v` is the instance with size field `s` and the table of `f`, a function on
`nn` inputs. -/
def FmtT (s nn : ℕ) (f : (Fin nn → Bool) → Bool) (v : List Bool) : Prop :=
  ∃ T : List Bool, v = List.replicate s true ++ false :: T ∧ T.length = 2 ^ nn ∧
    tableFun nn T = f

/-- A string of the right length that is not such an instance fails at one position. -/
theorem fmtT_witness (s nn : ℕ) (f : (Fin nn → Bool) → Bool) (v : List Bool)
    (hlen : v.length = s + 1 + 2 ^ nn) (hv : ¬ FmtT s nn f v) :
    ∃ (p : ℕ) (b : Bool), v[p]? = some b ∧
      ∀ v' : List Bool, v'[p]? = some b → ¬ FmtT s nn f v' := by
  by_cases c1 : ∃ j, j < s ∧ v[j]? = some false
  · obtain ⟨j, hj, hjv⟩ := c1
    refine ⟨j, false, hjv, ?_⟩
    rintro v' a1 ⟨T, rfl, -, -⟩
    rw [(get_fmt s _).1 j hj] at a1
    simp at a1
  by_cases c2 : v[s]? = some true
  · refine ⟨s, true, c2, ?_⟩
    rintro v' a1 ⟨T, rfl, -, -⟩
    rw [(get_fmt s _).2.1] at a1
    simp at a1
  have hsv : s + 1 ≤ v.length := by rw [hlen]; exact Nat.le_add_right _ _
  have h1 : ∀ j : ℕ, j < s → v[j]? = some true := by
    intro j hj
    have hj' : j < v.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, v[j]? = some b := ⟨v[j], List.getElem?_eq_getElem hj'⟩
    cases b with
    | false => exact (c1 ⟨j, hj, hb⟩).elim
    | true => exact hb
  have h2 : v[s]? = some false := by
    have hs' : s < v.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, v[s]? = some b := ⟨v[s], List.getElem?_eq_getElem hs'⟩
    cases b with
    | false => exact hb
    | true => exact (c2 hb).elim
  have hv0 := fmt_of_bits s v h1 h2
  obtain ⟨r, hr⟩ : ∃ r, r = v.drop (s + 1) := ⟨_, rfl⟩
  rw [← hr] at hv0
  have hrl : r.length = 2 ^ nn := by rw [hr, List.length_drop, hlen]; exact Nat.add_sub_cancel_left _ _
  have g3 := (get_fmt s r).2.2
  have hne : tableFun nn r ≠ f := fun hc => hv ⟨r, hv0, hrl, hc⟩
  obtain ⟨x, hx⟩ : ∃ x, tableFun nn r x ≠ f x := by
    by_contra hall
    exact hne (funext fun x => Classical.byContradiction fun hx => hall ⟨x, hx⟩)
  have hlt : tableIndex x < r.length := hrl ▸ tableIndex_lt x
  have hget : r[tableIndex x]? = some (!f x) := by
    have e : r[tableIndex x]? = some (tableFun nn r x) := by
      unfold tableFun
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      rfl
    rw [e]
    congr 1
    cases e1 : tableFun nn r x <;> cases e2 : f x <;>
      first | rfl | exact absurd (e1.trans e2.symm) hx
  refine ⟨s + 1 + tableIndex x, !f x, ?_, ?_⟩
  · rw [hv0, g3]; exact hget
  · rintro v' a1 ⟨T', rfl, -, hc'⟩
    rw [(get_fmt s _).2.2] at a1
    have h3 : tableFun nn T' x = !f x := by
      unfold tableFun
      rw [List.getD_eq_getElem?_getD, a1]
      rfl
    rw [hc'] at h3
    cases hf : f x <;> rw [hf] at h3 <;> exact absurd h3 (by decide)

/-! ## The index of the cover -/

/-- The number of inputs of the table in an instance of length `L` with size field `s`. -/
def nn' (L s : ℕ) : ℕ := Nat.log 2 (L - (s + 1))

theorem nn'_le (L s : ℕ) : nn' L s ≤ Nat.log 2 L :=
  Nat.log_mono_right (Nat.sub_le _ _)

theorem nn'_eq (s k : ℕ) : nn' (s + 1 + 2 ^ k) s = k := by
  unfold nn'
  have e : s + 1 + 2 ^ k - (s + 1) = 2 ^ k := Nat.add_sub_cancel_left _ _
  rw [e, Nat.log_pow (by norm_num)]

/-- The pairs: a size field `s ≤ s0` and a function with a circuit of size `s` on the number of
inputs that an instance of length `L` with size field `s` has. -/
abbrev Idx' (L s0 : ℕ) : Type :=
  Σ s : Fin (s0 + 1), {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn' L s) f s}

open Classical in
noncomputable instance (L s0 : ℕ) : Fintype (Idx' L s0) := inferInstance

theorem card_idx' (L s0 D : ℕ) (h : Nat.log 2 L ≤ D) :
    Fintype.card (Idx' L s0) ≤ (s0 + 1) * cnt D s0 := by
  classical
  have hterm : ∀ s : Fin (s0 + 1),
      Fintype.card {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn' L s) f s}
        ≤ cnt D s0 := by
    intro s
    have e : Fintype.card {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn' L s) f s}
        = {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool | HasCircuitSize (nn' L s) f s}.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq
        {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool | HasCircuitSize (nn' L s) f s}
    rw [e]
    exact (count_le _ _).trans (cnt_mono ((nn'_le L s).trans h) (by omega))
  unfold Idx'
  rw [Fintype.card_sigma]
  calc (Finset.univ.sum fun s : Fin (s0 + 1) =>
          Fintype.card {f : (Fin (nn' L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn' L s) f s})
      ≤ Finset.univ.sum fun _ : Fin (s0 + 1) => cnt D s0 :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = (s0 + 1) * cnt D s0 := by simp

/-! ## The core -/

/-- The core of the chain for total MCSP, from any well-formed image of the all-false input. -/
theorem core : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List Bool), w (fun _ : Fin n => false) = List.replicate s true ++ false :: T → T.length = 2 ^ n' → (¬ PEqualNP.MetaComplexity.HasCircuitSize n' (PEqualNP.MetaComplexity.tableFun n' T) s) ∧ 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1)))) := by
  classical
  intro n q M w hq hloc hlen hcor hn n0 s0 T0 hz hT0
  refine ⟨?_, ?_⟩
  · intro hs
    have hmem : w (fun _ : Fin n => false) ∈ MCSP := ⟨n0, s0, T0, hz, hT0, hs⟩
    have := (hcor _).mpr hmem
    simp at this
  -- the all-false input and the length of its image
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → Bool, z = fun _ => false := ⟨_, rfl⟩
  rw [← hzdef] at hz
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (w z).length := ⟨_, rfl⟩
  have hL0' : L0 = s0 + 1 + 2 ^ n0 := by
    rw [hL0, hz]
    simp only [List.length_append, List.length_replicate, List.length_cons, hT0]
    omega
  have hL0M : L0 ≤ M := hL0 ▸ hlen z
  -- the three certificates
  obtain ⟨S1, c1, h1⟩ := hloc (L0 - 1) z
  obtain ⟨S2, c2, h2⟩ := hloc L0 z
  obtain ⟨S3, c3, h3⟩ := hloc s0 z
  have hU : (S1 ∪ S2 ∪ S3).card ≤ 3 * q := by
    have a := Finset.card_union_le (S1 ∪ S2) S3
    have b := Finset.card_union_le S1 S2
    omega
  obtain ⟨m, ext, hm, hextU, hpar, hV⟩ := subcube n (S1 ∪ S2 ∪ S3)
  have hzi : ∀ i : Fin n, z i = false := fun i => by rw [hzdef]
  -- on the subcube: constant length, separator bit false
  have len : ∀ y : Fin m → Bool, (w (ext y)).length = L0 := by
    intro y
    have a1 := h1 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have a2 := h2 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have b1 : L0 ≤ (w (ext y)).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega), eq_comm, List.getElem?_eq_none_iff] at a1
      omega
    have b2 : (w (ext y)).length ≤ L0 := by
      rw [List.getElem?_eq_none (l := w z) (by omega), List.getElem?_eq_none_iff] at a2
      exact a2
    omega
  have sep : ∀ y : Fin m → Bool, (w (ext y))[s0]? = some false := by
    intro y
    have a3 := h3 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    rw [a3, hz]
    exact (get_fmt s0 _).2.1
  -- the cover
  let E : Idx' L0 s0 → Finset (Fin m → Bool) := fun a =>
    Finset.univ.filter (fun y => FmtT a.1 (nn' L0 a.1) a.2.1 (w (ext y)))
  let eqv : Idx' L0 s0 ≃ Fin (Fintype.card (Idx' L0 s0)) := Fintype.equivFin _
  have hm0 : 0 < m := by omega
  have hfin := Coding.parity_cover m (2 * q) (Fintype.card (Idx' L0 s0)) (fun a => E (eqv.symm a)) (by omega) hm0
    (by
      intro a y hy
      obtain ⟨⟨s, f⟩, hsf⟩ : ∃ p, p = eqv.symm a := ⟨_, rfl⟩
      simp only [← hsf] at hy ⊢
      have hy' : ¬ FmtT s (nn' L0 s) f.1 (w (ext y)) :=
        fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      by_cases hl : L0 = (s : ℕ) + 1 + 2 ^ nn' L0 s
      · obtain ⟨p1, b1, e1, hw⟩ :=
          fmtT_witness s (nn' L0 s) f.1 (w (ext y)) ((len y).trans hl) hy'
        obtain ⟨Sa, ca, ha⟩ := hloc p1 (ext y)
        obtain ⟨V, cV, hVV⟩ := hV Sa
        refine ⟨V, by omega, fun y' hy'' hmem => ?_⟩
        have agree := hVV y y' hy''
        exact hw (w (ext y'))
          ((ha (ext y') (fun i hi => agree i hi)).trans e1)
          (Finset.mem_filter.mp hmem).2
      · refine ⟨∅, by simp, fun y' _ hmem => ?_⟩
        obtain ⟨T, e, hTl, -⟩ := (Finset.mem_filter.mp hmem).2
        have hlen' := len y'
        rw [e] at hlen'
        simp only [List.length_append, List.length_replicate, List.length_cons,
          hTl] at hlen'
        omega)
    (by
      intro y
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨T, e, hTl, hc⟩ := (Finset.mem_filter.mp ha).2
        have hmem : w (ext y) ∈ MCSP :=
          ⟨_, _, T, e, hTl, by rw [hc]; exact (eqv.symm a).2.2⟩
        rw [← hpar y]
        exact (hcor _).mpr hmem
      · intro hodd
        obtain ⟨n'', s, T, e, hTl, hs⟩ := (hcor (ext y)).mp (by rw [hpar y]; exact hodd)
        have hs0 : s ≤ s0 := by
          by_contra hgt
          have a := (get_fmt s T).1 s0 (by omega)
          rw [← e, sep y] at a
          simp at a
        have hLs : L0 = s + 1 + 2 ^ n'' := by
          have hlen' := len y
          rw [e] at hlen'
          simp only [List.length_append, List.length_replicate, List.length_cons,
            hTl] at hlen'
          omega
        have hnn : n'' = nn' L0 s := by rw [hLs, nn'_eq]
        subst hnn
        refine ⟨eqv ⟨⟨s, by omega⟩, ⟨tableFun _ T, hs⟩⟩, ?_⟩
        show y ∈ E (eqv.symm (eqv _))
        rw [Equiv.symm_apply_apply]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T, e, hTl, rfl⟩)
  -- the arithmetic
  have hN := card_idx' L0 s0 (Nat.log 2 M) (Nat.log_mono_right hL0M)
  obtain ⟨N, hNdef⟩ : ∃ N, N = Fintype.card (Idx' L0 s0) := ⟨_, rfl⟩
  rw [← hNdef] at hfin hN
  obtain ⟨d, hd⟩ : ∃ d, d = m / (2 * (2 * q)) := ⟨_, rfl⟩
  rw [← hd] at hfin
  have hdm : d ≤ m := hd ▸ Nat.div_le_self _ _
  have h2 : 2 ^ m = 2 ^ (m - d) * 2 ^ d := by
    rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ d ≤ 8 * q * N := by
    have h4 : 2 ^ (m - d) * 2 ^ d ≤ 2 ^ (m - d) * (8 * q * N) := by
      rw [← h2]
      calc 2 ^ m ≤ N * (4 * (2 * q) * 2 ^ (m - d)) := hfin
        _ = 2 ^ (m - d) * (8 * q * N) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have h5 : (n - 3 * q) / (4 * q) ≤ d := by
    rw [hd, show 4 * q = 2 * (2 * q) by ring]
    exact Nat.div_le_div_right (by omega)
  calc 2 ^ ((n - 3 * q) / (4 * q)) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    _ ≤ 8 * q * N := h3
    _ ≤ 8 * q * ((s0 + 1) * cnt (Nat.log 2 M) s0) := Nat.mul_le_mul_left _ hN

/-! ## The finite form -/

/-- The finite form for total MCSP. -/
theorem finite : ∀ (n q M B : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) → (∀ (n' s : ℕ) (T : List Bool), w (fun _ : Fin n => false) = List.replicate s true ++ false :: T → T.length = 2 ^ n' → PEqualNP.MetaComplexity.HasCircuitSize n' (PEqualNP.MetaComplexity.tableFun n' T) B) → 2 * q * (Nat.log 2 M + 2) < n → 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * (B * (B * ((3 * ((Nat.log 2 M + B + 1) * (Nat.log 2 M + B + 1))) ^ (B - 1) * (Nat.log 2 M + B)))) := by
  intro n q M B w hq hloc hlen hcor hsim hn
  obtain ⟨n', s, T, hz, hT⟩ := formed n q M w hloc hlen (fun x hx => (hcor x).mp hx) hn
  have h3q : 3 * q < n := by
    have : 2 * q * 2 ≤ 2 * q * (Nat.log 2 M + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨hno, hb⟩ := core n q M w hq hloc hlen hcor h3q n' s T hz hT
  obtain ⟨C, hf, hs, he⟩ := hsim n' s T hz hT
  have hsB : s + 1 ≤ B := by
    by_contra h
    exact hno ⟨C, hf, by omega, he⟩
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have hsk : s ≤ k := by omega
  refine hb.trans (Nat.mul_le_mul_left _ ?_)
  rw [Nat.add_sub_cancel]
  have hbase : 3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))
      ≤ 3 * ((Nat.log 2 M + (k + 1) + 1) * (Nat.log 2 M + (k + 1) + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hpos : 0 < 3 * ((Nat.log 2 M + (k + 1) + 1) * (Nat.log 2 M + (k + 1) + 1)) := by
    positivity
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul
    ((Nat.pow_le_pow_left hbase s).trans (Nat.pow_le_pow_right hpos hsk)) (by omega)))

/-! ## The asymptotic form -/

/-- The asymptotic form for total MCSP. -/
theorem asymptotic : ∀ (a b c : ℕ), 2 * a < b → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ ∃ (q : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q ∧ q ^ b ≤ n ^ a ∧ PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length ≤ n ^ c + c) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) ∧ ∀ (n' s : ℕ) (T : List Bool), w (fun _ : Fin n => false) = List.replicate s true ++ false :: T → T.length = 2 ^ n' → PEqualNP.MetaComplexity.HasCircuitSize n' (PEqualNP.MetaComplexity.tableFun n' T) (q * (Nat.log 2 n + 1) ^ c) := by
  intro a b c hab
  obtain ⟨n0, h0⟩ := LocalClose.key a b c hab
  refine ⟨n0, fun n hn => ?_⟩
  rintro ⟨q, w, hq, hqb, hloc, hlen, hcor, hsim⟩
  have hK := h0 n hn q hqb
  obtain ⟨g1, g2⟩ := LocalClose.arith n q c (Nat.log 2 n + 1) (Nat.log 2 (n ^ c + c))
    (q * (Nat.log 2 n + 1) ^ c) hq (by omega) (Nat.lt_pow_succ_log_self (by norm_num) n)
    (LocalClose.logM_le n c) rfl hK
  exact absurd (finite n q (n ^ c + c) (q * (Nat.log 2 n + 1) ^ c) w hq hloc hlen hcor hsim g1)
    (not_le.mpr g2)

end PEqualNP.MetaComplexity.Helpers.TotalLocal
