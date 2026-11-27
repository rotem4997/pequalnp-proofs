import PEqualNP.MetaComplexity.Helpers.Elim

/-!
# Hardwiring inputs

Helper for `L-meta-018`. The last `k` inputs of a circuit on `n + k` inputs are fixed to
constants, one at a time, by the pass of `Elim.lean`. Fixing one input never adds a gate,
except that a restriction that is constantly `true` needs one gate (an AND of nothing).
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  exact ⟨C, ok, le_trans hsz hst, hev⟩

/-- Fix the last input of `f` to `b`: the size does not grow, except up to one gate. -/
theorem fix_last (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (h : HasCircuitSize (n + 1) f s) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) (max s 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    have hc : ∀ y : Fin n → Bool, f (Fin.snoc y b) = c := by
      intro y
      rw [← hval y, hst]; rfl
    cases c with
    | false =>
      refine ⟨⟨[], n⟩, ?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · simp [Circuit.size]
      · intro y
        show (List.ofFn y).getD n false = f (Fin.snoc y b)
        rw [hc y]
        exact List.getD_eq_default _ _ (by simp)
    | true =>
      refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        simp
      · simp [Circuit.size]
      · intro y
        show (List.ofFn y ++ [true]).getD n false = f (Fin.snoc y b)
        rw [hc y]
        exact getD_snoc_len _ _ _ _ (by simp)
  | wire j =>
    have hlen : acc.2.length ≤ max s 1 := by
      have := elim_len n gs (initStats n b, [])
      rw [← hacc] at this
      have hl : gs.length = C.gates.length := by simp [hgs]
      simp only [List.length_nil, zero_add] at this
      have := le_max_left s 1
      omega
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem append_nil_eq {n : ℕ} (y : Fin n → Bool) (c : Fin 0 → Bool) :
    (Fin.append y c : Fin (n + 0) → Bool) = y := by
  funext i
  exact Fin.addCases (motive := fun i => Fin.append y c i = y i)
    (fun j => Fin.append_left y c j) (fun j => j.elim0) i

theorem snoc_append_init {n k : ℕ} (y : Fin n → Bool) (c : Fin (k + 1) → Bool) :
    (Fin.snoc (Fin.append y (Fin.init c)) (c (Fin.last k)) : Fin (n + k + 1) → Bool)
      = Fin.append y c := by
  have h := Fin.append_snoc y (Fin.init c) (c (Fin.last k))
  rw [Fin.snoc_init_self] at h
  exact h.symm

/-- Fix the last `k` inputs of `f` to the constants `c`. -/
theorem hardwire_max (n : ℕ) : ∀ (k : ℕ) (f : (Fin (n + k) → Bool) → Bool) (c : Fin k → Bool)
    (s : ℕ), HasCircuitSize (n + k) f s →
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.append y c)) (max s 1) := by
  intro k
  induction k with
  | zero =>
    intro f c s h
    have e : (fun y : Fin n → Bool => f (Fin.append y c)) = f := by
      funext y
      rw [append_nil_eq]
    rw [e]
    exact hasCircuitSize_mono (le_max_left s 1) h
  | succ k ih =>
    intro f c s h
    have h1 := fix_last (n + k) f (c (Fin.last k)) s h
    have h2 := ih _ (Fin.init c) _ h1
    have e : (fun y : Fin n → Bool => f (Fin.append y c))
        = fun y : Fin n → Bool => f (Fin.snoc (Fin.append y (Fin.init c)) (c (Fin.last k))) := by
      funext y
      rw [snoc_append_init]
    rw [e]
    exact hasCircuitSize_mono (by simp) h2

theorem hardwire (n k : ℕ) (f : (Fin (n + k) → Bool) → Bool) (c : Fin k → Bool) (s : ℕ)
    (h : HasCircuitSize (n + k) f s) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.append y c)) (s + 1) :=
  hasCircuitSize_mono (by omega) (hardwire_max n k f c s h)

end PEqualNP.MetaComplexity.Helpers
