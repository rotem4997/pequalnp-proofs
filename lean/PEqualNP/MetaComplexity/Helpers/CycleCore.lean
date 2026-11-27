import PEqualNP.MetaComplexity.Helpers.CycleUpper

/-!
# The cycle function meets the hypotheses of the reader lemma L-meta-107

Helper for `L-meta-106` (proofs only, no statement may use it). `Stmt107` is the statement of
the reader lemma `L-meta-107`, verbatim. This file proves that the cycle function on `N ≥ 5`
inputs satisfies its three hypotheses (it depends on every input; fixing any input leaves a
non-constant function; no pair funnel), so that `Stmt107` gives `StmtCycCore`, and with
`cyc_exact_of_core` the statement of `L-meta-106`.

`N ≥ 5` is used once: for inputs `p ≠ q` there is a neighbour `r` of `p` with `r ≠ q` and `r`
not adjacent to `q`. Only the second equality of the excluded pair funnel is refuted.
-/

namespace PEqualNP.MetaComplexity.Helpers.CycleSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PathSize

/-- The statement of the reader lemma `L-meta-107`, verbatim. -/
def Stmt107 : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ), (∃ p : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1), (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → (∀ p q : Fin (n + 1), p ≠ q → (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool, f (Function.update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool, f (Function.update (Function.update x p (!a)) q b) = f (Function.update (Function.update x p a) q (!b)) ∧ f (Function.update (Function.update x p a) q (!b)) = f (Function.update (Function.update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s')

/-! ## Points given by a predicate on natural indices -/

/-- The cyclic successor at natural indices. -/
def sc (N i : ℕ) : ℕ := if i + 1 = N then 0 else i + 1

/-- The point whose true inputs are those whose index satisfies `P`. -/
def pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : Fin N → Bool := fun i => decide (P i.val)

theorem cyc_pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    cyc N (pt N P) = true ↔ ∃ i, i < N ∧ P i ∧ P (sc N i) := by
  rw [cyc_iff_ext]
  have e : ∀ j, j < N → ext (pt N P) j = decide (P j) := by
    intro j hj; simp [ext, pt, hj]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hs : sc N i < N := by unfold sc; split_ifs <;> omega
    refine ⟨i, hi, ?_, ?_⟩
    · rw [e i hi] at h1; simpa using h1
    · unfold sc at hs ⊢; rw [e _ hs] at h2; simpa using h2
  · rintro ⟨i, hi, h1, h2⟩
    have hs : sc N i < N := by unfold sc; split_ifs <;> omega
    refine ⟨i, hi, ?_, ?_⟩
    · rw [e i hi]; simpa using h1
    · unfold sc at hs h2; rw [e _ hs]; simpa using h2

theorem cyc_pt_false (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ i, i < N → P i → P (sc N i) → False) : cyc N (pt N P) = false := by
  rw [← Bool.not_eq_true, cyc_pt]
  rintro ⟨i, hi, h1, h2⟩
  exact h i hi h1 h2

theorem upd_pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (p : Fin N) (v : Bool) :
    Function.update (pt N P) p v =
      pt N (fun j => (j = p.val ∧ v = true) ∨ (j ≠ p.val ∧ P j)) := by
  funext i
  by_cases h : i = p
  · subst h; simp [pt]
  · have h' : i.val ≠ p.val := fun e => h (Fin.ext e)
    rw [Function.update_of_ne h]
    simp [pt, h']

/-! ## The three hypotheses for the cycle function -/

/-- The cycle function depends on input `p`: only `p + 1` true, then flip `p`. -/
theorem cyc_dep (N : ℕ) (hN : 3 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, cyc N (Function.update x p (!x p)) ≠ cyc N x := by
  have hp := p.2
  refine ⟨pt N (fun j => j = sc N p.val), ?_⟩
  have hx : pt N (fun j => j = sc N p.val) p = false := by
    simp only [pt, decide_eq_false_iff_not]; unfold sc; split_ifs <;> omega
  have h1 : cyc N (pt N (fun j => j = sc N p.val)) = false :=
    cyc_pt_false N _ (by intro i hi h1 h2; unfold sc at h1 h2; split_ifs at h1 h2 <;> omega)
  have h2 : cyc N (pt N (fun j => (j = p.val ∧ true = true) ∨
      (j ≠ p.val ∧ j = sc N p.val))) = true := by
    rw [cyc_pt]
    exact ⟨p.val, hp, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨by unfold sc; split_ifs <;> omega, rfl⟩⟩
  rw [hx, upd_pt, Bool.not_false, h1, h2]
  decide

/-- Fixing input `p` to either value leaves a non-constant function. -/
theorem cyc_nonconst (N : ℕ) (hN : 3 ≤ N) (p : Fin N) (b : Bool) :
    ∃ x y : Fin N → Bool,
      cyc N (Function.update x p b) ≠ cyc N (Function.update y p b) := by
  have hp := p.2
  refine ⟨pt N (fun _ => False), pt N (fun j => j = sc N p.val ∨ j = sc N (sc N p.val)), ?_⟩
  have h1 : cyc N (pt N (fun j => (j = p.val ∧ b = true) ∨ (j ≠ p.val ∧ False))) = false :=
    cyc_pt_false N _ (by
      intro i hi h1 h2
      simp only [and_false, or_false] at h1 h2
      have a1 := h1.1
      have a2 := h2.1
      unfold sc at a2; split_ifs at a2 <;> omega)
  have h2 : cyc N (pt N (fun j => (j = p.val ∧ b = true) ∨
      (j ≠ p.val ∧ (j = sc N p.val ∨ j = sc N (sc N p.val))))) = true := by
    rw [cyc_pt]
    refine ⟨sc N p.val, by unfold sc; split_ifs <;> omega, ?_, ?_⟩
    · right; exact ⟨by unfold sc; split_ifs <;> omega, Or.inl rfl⟩
    · right; exact ⟨by unfold sc; split_ifs <;> omega, Or.inr rfl⟩
  rw [upd_pt, upd_pt, h1, h2]
  decide

/-- The neighbour used against a pair: adjacent to `p`, not `q`, not adjacent to `q`.
This is where `N ≥ 5` is used. -/
theorem exists_nbr (N : ℕ) (hN : 5 ≤ N) (p q : ℕ) (hp : p < N) (hq : q < N) (hpq : p ≠ q) :
    ∃ r, r < N ∧ r ≠ p ∧ r ≠ q ∧ (sc N p = r ∨ sc N r = p) ∧ sc N q ≠ r ∧ sc N r ≠ q := by
  by_cases h : q = sc N p ∨ q = sc N (sc N p)
  · refine ⟨if p = 0 then N - 1 else p - 1, ?_⟩
    unfold sc at h ⊢
    split_ifs at h ⊢ <;> omega
  · refine ⟨sc N p, ?_⟩
    unfold sc at h ⊢
    split_ifs at h ⊢ <;> omega

/-- Input `p` is sensitive with input `q` fixed to any value. -/
theorem cyc_sens (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) (c : Bool) :
    ∃ x : Fin N → Bool, cyc N (Function.update (Function.update x p true) q c) = true ∧
      cyc N (Function.update (Function.update x p false) q c) = false := by
  have hpq' : p.val ≠ q.val := fun e => hpq (Fin.ext e)
  obtain ⟨r, hr, hrp, hrq, hadj, hn1, hn2⟩ := exists_nbr N hN p.val q.val p.2 q.2 hpq'
  refine ⟨pt N (fun j => j = r), ?_, ?_⟩
  · rw [upd_pt, upd_pt, cyc_pt]
    rcases hadj with h | h
    · refine ⟨p.val, p.2, Or.inr ⟨hpq', Or.inl ⟨rfl, rfl⟩⟩, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩ <;>
        rw [h] <;> assumption
    · refine ⟨r, hr, Or.inr ⟨hrq, Or.inr ⟨hrp, rfl⟩⟩, Or.inr ⟨?_, Or.inl ⟨h, rfl⟩⟩⟩
      rw [h]; exact hpq'
  · rw [upd_pt, upd_pt]
    apply cyc_pt_false
    intro i hi h1 h2
    unfold sc at h2 hn1 hn2
    cases c <;> simp only [Bool.false_eq_true, and_false, false_or, and_true] at h1 h2 <;>
      split_ifs at h2 hn1 hn2 <;> omega

/-- No pair funnel: the second equality of the excluded configuration already fails. -/
theorem cyc_no_funnel (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) :
    ¬ ∃ a b : Bool, ∀ x : Fin N → Bool,
      cyc N (Function.update (Function.update x p (!a)) q b) =
        cyc N (Function.update (Function.update x p a) q (!b)) ∧
      cyc N (Function.update (Function.update x p a) q (!b)) =
        cyc N (Function.update (Function.update x p (!a)) q (!b)) := by
  rintro ⟨a, b, h⟩
  obtain ⟨x, h1, h2⟩ := cyc_sens N hN p q hpq (!b)
  have e := (h x).2
  cases a
  · rw [Bool.not_false, h1, h2] at e; exact absurd e (by decide)
  · rw [Bool.not_true, h1, h2] at e; exact absurd e (by decide)

/-! ## The core from the reader lemma -/

theorem size_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize n f s)
    (hst : s ≤ t) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem cyc_core_of_readers (h107 : Stmt107) : StmtCycCore := by
  intro N s hN hs hc
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rcases h107 n (cyc (n + 1)) s ⟨⟨0, by omega⟩, cyc_dep (n + 1) (by omega) _⟩
      (fun p _ b => cyc_nonconst (n + 1) (by omega) p b)
      (fun p q hpq _ _ => cyc_no_funnel (n + 1) hN p q hpq) hc with
    ⟨y, s', hle, hC⟩ | ⟨y, s', hle, hC⟩
  · exact ⟨y, Or.inl ⟨by omega, size_mono hC (by omega)⟩⟩
  · exact ⟨y, Or.inr ⟨by omega, size_mono hC (by omega)⟩⟩

/-- `L-meta-106` from the reader lemma `L-meta-107`. -/
theorem cyc_exact_of_readers (h107 : Stmt107) :
    ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + (n + 1) / 2 ≤ s + 1) :=
  cyc_exact_of_core (cyc_core_of_readers h107)

end PEqualNP.MetaComplexity.Helpers.CycleSize
