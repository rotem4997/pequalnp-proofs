import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1481_2
    (hmono : ∀ C : Circuit, (∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) →
      Monotone (fun x : Fin 26 → Bool => C.eval (List.ofFn x)))
    (hcert :
      let E := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let Z := fun (y : Fin 13 → Bool) (l : Fin 13) =>
        !(y l || y (l + 1) || y (l + 3) || y (l + 9))
      ∃ C : Circuit, C.size ≤ 64 ∧
        PEqualNP.TopForm.IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l, E p l →
          C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p))
            (fun i => decide (i = l)))) = true) ∧
        (∀ y, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
          C.eval (List.ofFn (Fin.addCases y (Z y))) = false) ∧
        ∀ k : Bool, ∃ d : ℕ → Bool,
          (∀ i < 26, d i = decide (i = if k then 0 else 13)) ∧
          (∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
            let w := C.wires (List.ofFn (fun i : Fin 26 => decide
              (i.val = if k then 13 else 0)))
            (g.op = .and →
              d (26 + j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧
            (g.op = .or → d (26 + j) = (d a || d b))) ∧ d C.output = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  let E (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let Z (y : Fin 13 → Bool) (l : Fin 13) := !(y l || y (l + 1) || y (l + 3) || y (l + 9))
  have hZ (y : Fin 13 → Bool) (l : Fin 13) :
      Z y l = true ↔ ∀ p, E p l → y p = false := by
    constructor
    · intro h p hp
      simp only [Z, Bool.not_eq_true', Bool.or_eq_false_iff] at h
      rcases hp with rfl | rfl | rfl | rfl <;> tauto
    · intro h
      have h0 := h l (.inl rfl)
      have h1 := h (l + 1) (.inr (.inl rfl))
      have h3 := h (l + 3) (.inr (.inr (.inl rfl)))
      have h9 := h (l + 9) (.inr (.inr (.inr rfl)))
      simp [Z, h0, h1, h3, h9]
  obtain ⟨C, hsize, ⟨hops, hback, harity⟩, hdistinct, hedges, hclosed, hmark⟩ := hcert
  have hgates (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
    have hmem := List.mem_iff_getElem?.2 ⟨j, hj⟩
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (harity g hmem)
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = g
      simp only [List.getD_eq_getElem?_getD, hj, Option.getD_some]
    have hprev := hback j (List.getElem?_eq_some_iff.1 hj).1
    rw [hgate, hab] at hprev
    exact ⟨hops g hmem, a, b, hab, by simpa [hab] using hdistinct g hmem,
      hprev a (by simp), hprev b (by simp)⟩
  have hm := hmono C hops
  refine ⟨C, hsize, hgates, ?_, 0, 0, Or.inl rfl, ?_, ?_⟩
  · intro x
    constructor
    · intro hval
      by_contra hno
      -- Close the independent input by filling the compatible lines and then the compatible points.
      let y (p : Fin 13) := x (Fin.castAdd 13 p)
      let Y (p : Fin 13) := decide (∀ l, Z y l = true → ¬ E p l)
      have hyY (p : Fin 13) (hy : y p = true) : Y p = true := by
        simp only [Y, decide_eq_true_eq]
        intro l hl he
        have := (hZ y l).1 hl p he
        simp [hy] at this
      have hYZ (l : Fin 13) (hl : Z y l = true) : Z Y l = true := by
        apply (hZ Y l).2
        intro p hp
        by_contra h
        have h' : Y p = true := Bool.of_not_eq_false h
        exact (of_decide_eq_true h' l hl) hp
      have hZY (l : Fin 13) (hl : Z Y l = true) : Z y l = true := by
        apply (hZ y l).2
        intro p hp
        by_contra h
        have h' : y p = true := Bool.of_not_eq_false h
        have := (hZ Y l).1 hl p hp
        simp [hyY p h'] at this
      have hmax (p : Fin 13) (hp : Y p = false) : ∃ l, E p l ∧ Z Y l = true := by
        have h' : ¬ ∀ l, Z y l = true → ¬ E p l := of_decide_eq_false hp
        obtain ⟨l, hl⟩ := not_forall.mp h'
        obtain ⟨hzl, hel⟩ := not_imp.mp hl
        exact ⟨l, not_not.mp hel, hYZ l hzl⟩
      have hall : x ≤ Fin.addCases (motive := fun _ => Bool) Y (Z Y) := by
        intro i
        refine Fin.addCases (m := 13) (n := 13)
          (motive := fun j => x j ≤ Fin.addCases (motive := fun _ => Bool) Y (Z Y) j)
          ?_ ?_ i
        · intro p
          rw [Fin.addCases_left]
          change y p ≤ Y p
          cases hbit : y p with
          | false => simp
          | true => simp [hyY p hbit]
        · intro l
          rw [Fin.addCases_right]
          cases hbit : x (Fin.natAdd 13 l) with
          | false => exact Bool.false_le _
          | true =>
            have hz : Z y l = true := (hZ y l).2 (by
              intro p hp
              by_contra h
              have h' : y p = true := Bool.of_not_eq_false h
              exact hno ⟨p, l, hp, h', hbit⟩)
            simp only [hYZ l hz, Bool.le_true]
      have hle := hm hall
      dsimp only at hle
      rw [hval, hclosed Y hmax] at hle
      exact (by decide : ¬ true ≤ false) hle
    · rintro ⟨p, l, he, hp, hl⟩
      have hall : Fin.addCases (motive := fun _ => Bool)
          (fun i => decide (i = p)) (fun i => decide (i = l)) ≤ x := by
        intro i
        induction i using Fin.addCases with
        | left j =>
          rw [Fin.addCases_left]
          by_cases hj : j = p
          · simp only [hj, hp, Bool.le_true]
          · simp [hj]
        | right j =>
          rw [Fin.addCases_right]
          by_cases hj : j = l
          · simp only [hj, hl, Bool.le_true]
          · simp [hj]
      have hle := hm hall
      dsimp only at hle
      rw [hedges p l he] at hle
      exact Bool.eq_true_of_true_le hle
  · obtain ⟨v, hv, hgate, hout⟩ := hmark false
    refine ⟨v, ?_, ?_, hout⟩
    · intro i
      have hi := i.isLt
      constructor
      · have hinput : v i.val = decide (i.val = 13) := hv i.val (by omega)
        simpa [show i.val ≠ 13 by omega] using hinput
      · have he : 13 + i.val = 13 ↔ i = 0 :=
          (show 13 + i.val = 13 ↔ i.val = 0 by omega).trans
            (Fin.val_inj (a := i) (b := 0))
        have hinput : v (13 + i.val) = decide (13 + i.val = 13) :=
          hv (13 + i.val) (by omega)
        simpa only [he] using hinput
    · have he : (fun i : Fin 26 => decide (i.val = 0)) =
          (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13))) := by
        funext i
        have heq : i.val = 0 ↔ i = Fin.castAdd 13 (0 : Fin 13) :=
          Fin.val_inj (a := i) (b := Fin.castAdd 13 (0 : Fin 13))
        simp only [heq]
      intro j g a b hj hab
      simpa only [Bool.false_eq_true, ite_false, he] using hgate j g a b hj hab
  · obtain ⟨w, hw, hgate, hout⟩ := hmark true
    refine ⟨w, ?_, ?_, hout⟩
    · intro i
      have hi := i.isLt
      constructor
      · have he : i.val = 0 ↔ i = 0 := Fin.val_inj (a := i) (b := 0)
        have hinput : w i.val = decide (i.val = 0) := hw i.val (by omega)
        simpa only [he] using hinput
      · have hinput : w (13 + i.val) = decide (13 + i.val = 0) :=
          hw (13 + i.val) (by omega)
        simpa [show 13 + i.val ≠ 0 by omega] using hinput
    · have he : (fun i : Fin 26 => decide (i.val = 13)) =
          (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13))) := by
        funext i
        have heq : i.val = 13 ↔ i = Fin.natAdd 13 (0 : Fin 13) :=
          Fin.val_inj (a := i) (b := Fin.natAdd 13 (0 : Fin 13))
        simp only [heq]
      intro j g a b hj hab
      simpa only [ite_true, he] using hgate j g a b hj hab
