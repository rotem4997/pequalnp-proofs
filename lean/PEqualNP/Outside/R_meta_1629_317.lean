import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1629_317
    (h1 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      let D : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨C.gates.map (fun (g : PEqualNP.CircuitLowerBounds.Gate) => if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          g.inputs.all (fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0))
          then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ else g), C.output⟩
      let edge := fun (p l : Fin N) (k : Fin (N + N)) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      ∑ l : Fin N, Fintype.card {p : Fin N // I p l ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = true} ≤ 6 * C.size + 2 * N)
    (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.IsMinimalMonoCircuit (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      let D : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨C.gates.map (fun (g : PEqualNP.CircuitLowerBounds.Gate) => if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          g.inputs.all (fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0))
          then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ else g), C.output⟩
      let edge := fun (p l : Fin N) (k : Fin (N + N)) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      ∀ T : Fin N → Finset (Fin N),
        (∀ l p, p ∈ T l → I p l ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (edge p l) = true ∧
          PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = false) →
        ∑ l, (T l).card ≤ 44 * Fintype.card {j : Fin C.size //
          (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
          ∃ l p, p ∈ T l ∧ (C.wires (List.ofFn (edge p l))).getD (N + N + j.val) false = true}) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  classical
  intro q N I inst C₀ hq hN hcol huniq hmono₀ hpos₀ hsound₀
  let R := fun s : ℕ => ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = s ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C₀
  have hex : ∃ s, R s := ⟨C₀.size, C₀, rfl, hmono₀, rfl⟩
  obtain ⟨C, hcsize, hmono, hfun⟩ := Nat.find_spec hex
  have hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit (N + N) C := by
    refine ⟨hmono, ?_⟩
    intro E hm he
    rw [hcsize]
    exact Nat.find_min' hex ⟨E, rfl, hm, he.trans hfun⟩
  have hle : C.size ≤ C₀.size := hmin.2 C₀ hmono₀ hfun.symm
  suffices N * q ≤ 100 * C.size from this.trans (Nat.mul_le_mul_left _ hle)
  have hpos : ∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k =>
      decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    rw [hfun]
    exact hpos₀
  have hsound : (∀ z : Fin (N + N) → Bool,
        (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) := by
    rw [hfun]
    exact hsound₀
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨C.gates.map (fun (g : PEqualNP.CircuitLowerBounds.Gate) => if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          g.inputs.all (fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0))
          then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ else g), C.output⟩
  let edge := fun (p l : Fin N) (k : Fin (N + N)) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  let A := fun l : Fin N => Finset.univ.filter (fun p => I p l)
  let good := fun l : Fin N => (A l).filter (fun p => PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = true)
  let bad := fun l : Fin N => (A l).filter (fun p => ¬ PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = true)
  have hc := h1 N I C huniq hmono (fun z hz => hsound z (by rw [Fintype.card_subtype] at hz; omega))
  simp only [Fintype.card_subtype] at hc
  change (∑ l : Fin N, (Finset.univ.filter (fun p => I p l ∧ PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = true)).card) ≤ _ at hc
  have hgood : ∑ l, (good l).card ≤ 6 * C.size + 2 * N := by
    simpa only [good, A, Finset.filter_filter] using hc
  have hbad := h2 q N I C hq hN (by simpa only [Fintype.card_subtype] using hcol) huniq hmin
    (fun z hz => hsound z (by simpa only [Fintype.card_subtype] using hz)) bad (by
    intro l p hp
    change p ∈ (A l).filter _ at hp
    obtain ⟨ha, hn⟩ := Finset.mem_filter.mp hp
    have hi : I p l := (Finset.mem_filter.mp ha).2
    refine ⟨hi, hpos p l hi, ?_⟩
    change PEqualNP.MetaComplexity.circuitFun (N + N) D (edge p l) = false
    simpa using hn)
  simp only [Fintype.card_subtype] at hbad
  have hs : ∑ l, (bad l).card ≤ 44 * C.size := hbad.trans (Nat.mul_le_mul_left _ (by
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)))
  have ht : (∑ l, (good l).card) + (∑ l, (bad l).card) = N * (q + 1) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _l : Fin N, (q + 1) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [show (good l).card + (bad l).card = (A l).card from
          Finset.card_filter_add_card_filter_not (s := A l) _]
        exact hcol l
      _ = _ := by simp
  have hsum := Nat.add_le_add hgood hs
  rw [ht] at hsum
  have hNq : 2 * N ≤ N * q := by nlinarith [Nat.mul_le_mul_left N hq]
  rw [Nat.mul_add, Nat.mul_one] at hsum
  omega
