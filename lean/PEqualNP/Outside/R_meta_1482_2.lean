import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1482_2 (h63 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) → 63 ≤ C.size) (hB : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, 63 ≤ C.size ∧ C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ (∃ v : ℕ → Bool, (∀ n < 26, v n = decide (n = 13)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy.val = 0)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey.val = 0)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ n < 26, w n = decide (n = 0)) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix.val = 13)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex.val = 13)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false))) : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  have getD_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (e : Fin 26 → Bool) (T : List Bool) (a : ℕ),
      (List.ofFn e ++ T).getD (ρ a) false =
        (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD a false := by
    intro ρ hl hb e T a
    by_cases ha : a < 26
    · have h1 := hl a ha
      rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact h1),
        List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact ha)]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h1),
        List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ha), List.getElem_ofFn,
        List.getElem_ofFn]
    · rw [hb a (by omega)]
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega),
        List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega)]
      rw [List.length_ofFn, List.length_ofFn]
  have fold_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (stp : List Bool → Gate → List Bool)
      (hstp : ∀ w g, stp w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (e : Fin 26 → Bool) (gs : List Gate) (T : List Bool), ∃ T' : List Bool,
      (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl stp (List.ofFn e ++ T) =
        List.ofFn e ++ T' ∧
      gs.foldl stp (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T) =
        List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T' := by
    intro ρ hl hb stp hstp e gs
    induction gs with
    | nil => intro T; exact ⟨T, by simp, by simp⟩
    | cons g gs ih =>
      intro T
      have hval : (Gate.mk g.op (g.inputs.map ρ)).op.eval ((Gate.mk g.op (g.inputs.map ρ)).inputs.map
          fun i => (List.ofFn e ++ T).getD i false) =
          g.op.eval (g.inputs.map fun i =>
            (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false) := by
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact getD_rel ρ hl hb e T a
      obtain ⟨T', h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false)])
      refine ⟨T', ?_, ?_⟩
      · rw [List.map_cons, List.foldl_cons, hstp, hval, List.append_assoc]
        exact h1
      · rw [List.foldl_cons, hstp, List.append_assoc]
        exact h2
  have wires_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
      (C : Circuit) (e : Fin 26 → Bool) (a : ℕ),
      ((Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).wires
        (List.ofFn e)).getD (ρ a) false =
        (C.wires (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩))).getD a false := by
    intro ρ hl hb C e a
    obtain ⟨T', h1, h2⟩ := fold_rel ρ hl hb _ (fun _ _ => rfl) e C.gates []
    simp only [List.append_nil] at h1 h2
    have hw : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := fun _ _ => rfl
    rw [hw, hw]
    rw [h1, h2]
    exact getD_rel ρ hl hb e T' a
  have T : ∀ (σ τ : Fin 13 → Fin 13) (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26),
      (∀ a, 26 ≤ a → ρ a = a) → Function.Injective ρ → (∀ u : Fin 13, ρ u.val = (σ u).val) →
      (∀ t : Fin 13, ρ (13 + t.val) = 13 + (τ t).val) → Function.Bijective σ →
      Function.Bijective τ →
      (∀ u t : Fin 13, (σ u = τ t ∨ σ u = τ t + 1 ∨ σ u = τ t + 3 ∨ σ u = τ t + 9) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9)) →
      ∀ (C C' : Circuit) (p l : Fin 13),
      C' = Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) → (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) →
      C'.size = C.size ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C'.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ((σ p) = (τ l) ∨ (σ p) = (τ l) + 1 ∨ (σ p) = (τ l) + 3 ∨ (σ p) = (τ l) + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = (τ l))) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C'.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C'.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 (σ p))))).getD cy false && v dy) || (v cy && (C'.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 (σ p))))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C'.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = (σ p)) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C'.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C'.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 (τ l))))).getD cx false && w dx) || (w cx && (C'.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 (τ l))))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C'.output = false) := by
    intro σ τ ρ hl hb hinj hσ hτ bσ bτ hcol C C' p l hC' hS hF hI hVW
    subst hC'
    have gate_rel : ∀ (j : ℕ) (g : Gate),
        (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ)))[j]? = some g →
        ∃ g0 : Gate, C.gates[j]? = some g0 ∧ g = Gate.mk g0.op (g0.inputs.map ρ) := by
      intro j g hg
      rw [List.getElem?_map] at hg
      cases h : C.gates[j]? with
      | none => rw [h] at hg; simp at hg
      | some g0 => rw [h] at hg; simp at hg; exact ⟨g0, rfl, hg.symm⟩
    have lt_rel : ∀ a j : ℕ, a < 26 + j → ρ a < 26 + j := by
      intro a j h
      by_cases ha : a < 26
      · have := hl a ha; omega
      · rw [hb a (by omega)]; exact h
    have pi_castAdd : ∀ u : Fin 13,
        (⟨ρ (Fin.castAdd 13 u).val, hl _ (Fin.castAdd 13 u).isLt⟩ : Fin 26) =
          Fin.castAdd 13 (σ u) := by
      intro u; apply Fin.ext; simp [hσ u]
    have pi_natAdd : ∀ t : Fin 13,
        (⟨ρ (Fin.natAdd 13 t).val, hl _ (Fin.natAdd 13 t).isLt⟩ : Fin 26) =
          Fin.natAdd 13 (τ t) := by
      intro t; apply Fin.ext; exact hτ t
    have pi_inj : ∀ i j : Fin 26,
        (⟨ρ i.val, hl _ i.isLt⟩ : Fin 26) = ⟨ρ j.val, hl _ j.isLt⟩ → i = j := by
      intro i j h; apply Fin.ext; apply hinj; exact congrArg Fin.val h
    have deriv_rel : ∀ (e : Fin 26 → Bool) (v v' : ℕ → Bool), (∀ a, v' (ρ a) = v a) →
        (∀ a, 26 ≤ a → v' a = v a) →
        (∀ (ky : ℕ) (hy : Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] →
          (hy.op = GateOp.and → v (26 + ky) =
            (((C.wires (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩))).getD cy false
              && v dy) || (v cy &&
              (C.wires (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩))).getD dy
                false))) ∧
          (hy.op = GateOp.or → v (26 + ky) = (v cy || v dy))) →
        (∀ (ky : ℕ) (hy : Gate) (cy dy : ℕ),
          (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ)))[ky]? = some hy →
          hy.inputs = [cy, dy] →
          (hy.op = GateOp.and → v' (26 + ky) =
            ((((Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).wires
              (List.ofFn e)).getD cy false && v' dy) || (v' cy &&
              ((Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).wires
                (List.ofFn e)).getD dy false))) ∧
          (hy.op = GateOp.or → v' (26 + ky) = (v' cy || v' dy))) := by
      intro e v v' hr hbig h ky hy cy dy hg hin
      obtain ⟨g0, hg0, rfl⟩ := gate_rel ky hy hg
      obtain ⟨_, a, b, hab, _, _, _⟩ := hS ky g0 hg0
      have hin' : [ρ a, ρ b] = [cy, dy] := by simpa [hab] using hin
      simp only [List.cons.injEq, and_true] at hin'
      obtain ⟨rfl, rfl⟩ := hin'
      obtain ⟨h1, h2⟩ := h ky g0 a b hg0 hab
      rw [hbig (26 + ky) (by omega), wires_rel ρ hl hb C e a, wires_rel ρ hl hb C e b, hr, hr]
      exact ⟨fun hop => h1 hop, fun hop => h2 hop⟩
    obtain ⟨v, hv0, hvd, hvo⟩ := hVW.1
    obtain ⟨w, hw0, hwd, hwo⟩ := hVW.2
    have hlow : ∀ a (h1 : a < 13), ρ a = (σ ⟨a, h1⟩).val := fun a h1 => hσ ⟨a, h1⟩
    have hmid : ∀ a (h1 : ¬ a < 13) (h2 : a < 26), ρ a = 13 + (τ ⟨a - 13, by omega⟩).val := by
      intro a h1 h2
      have := hτ ⟨a - 13, by omega⟩
      simp only at this
      rwa [show 13 + (a - 13) = a by omega] at this
    let v' : ℕ → Bool := fun a => if a < 26 then (if a < 13 then false else
        decide (a = 13 + (τ l).val)) else v a
    let w' : ℕ → Bool := fun a => if a < 26 then (if a < 13 then decide (a = (σ p).val)
        else false) else w a
    have hvb : ∀ a, 26 ≤ a → v' a = v a := by
      intro a ha; simp [v', show ¬ a < 26 by omega]
    have hwb : ∀ a, 26 ≤ a → w' a = w a := by
      intro a ha; simp [w', show ¬ a < 26 by omega]
    have hvr : ∀ a, v' (ρ a) = v a := by
      intro a
      by_cases h1 : a < 13
      · have := (hv0 ⟨a, h1⟩).1
        simp only at this
        rw [hlow a h1, this]
        have := (σ ⟨a, h1⟩).isLt
        simp [v', show (σ ⟨a, h1⟩).val < 26 by omega, this]
      · by_cases h2 : a < 26
        · have := (hv0 ⟨a - 13, by omega⟩).2
          simp only [show 13 + (a - 13) = a by omega] at this
          rw [this, hmid a h1 h2]
          have := (τ ⟨a - 13, by omega⟩).isLt
          simp only [v', show 13 + (τ ⟨a - 13, by omega⟩).val < 26 by omega,
            show ¬ 13 + (τ ⟨a - 13, by omega⟩).val < 13 by omega, ite_true, ite_false]
          congr 1
          apply propext
          rw [Nat.add_left_cancel_iff, ← Fin.ext_iff, bτ.1.eq_iff]
        · rw [hb a (by omega)]; exact hvb a (by omega)
    have hwr : ∀ a, w' (ρ a) = w a := by
      intro a
      by_cases h1 : a < 13
      · have := (hw0 ⟨a, h1⟩).1
        simp only at this
        rw [this, hlow a h1]
        have := (σ ⟨a, h1⟩).isLt
        simp only [w', show (σ ⟨a, h1⟩).val < 26 by omega, this, ite_true]
        congr 1
        apply propext
        rw [← Fin.ext_iff, bσ.1.eq_iff]
      · by_cases h2 : a < 26
        · have := (hw0 ⟨a - 13, by omega⟩).2
          simp only [show 13 + (a - 13) = a by omega] at this
          rw [this, hmid a h1 h2]
          have := (τ ⟨a - 13, by omega⟩).isLt
          simp [w', show 13 + (τ ⟨a - 13, by omega⟩).val < 26 by omega]
        · rw [hb a (by omega)]; exact hwb a (by omega)
    refine ⟨(by show (List.map _ C.gates).length = C.gates.length; simp only [List.length_map]), ?_, ?_, (hcol p l).2 hI, ⟨v', ?_, ?_, ?_⟩, ⟨w', ?_, ?_, ?_⟩⟩
    · intro j g hg
      obtain ⟨g0, hg0, rfl⟩ := gate_rel j g hg
      obtain ⟨hop, a, b, hab, hne, ha, hb'⟩ := hS j g0 hg0
      exact ⟨hop, ρ a, ρ b, by simp [hab], fun he => hne (hinj he), lt_rel a j ha, lt_rel b j hb'⟩
    · intro x
      have := wires_rel ρ hl hb C x C.output
      show ((Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).wires
        (List.ofFn x)).getD (ρ C.output) false = true ↔ _
      rw [this]
      rw [show (C.wires (List.ofFn (fun i : Fin 26 => x ⟨ρ i.val, hl i.val i.isLt⟩))).getD
        C.output false = C.eval (List.ofFn (fun i : Fin 26 => x ⟨ρ i.val, hl i.val i.isLt⟩))
        from rfl, hF]
      simp only [pi_castAdd, pi_natAdd]
      constructor
      · rintro ⟨u, t, hI', h1, h2⟩
        exact ⟨σ u, τ t, (hcol u t).2 hI', h1, h2⟩
      · rintro ⟨u', t', hI', h1, h2⟩
        obtain ⟨u, rfl⟩ := bσ.2 u'
        obtain ⟨t, rfl⟩ := bτ.2 t'
        exact ⟨u, t, (hcol u t).1 hI', h1, h2⟩
    · intro my
      have := my.isLt
      refine ⟨by simp [v', this, show my.val < 26 by omega], ?_⟩
      simp [v', show 13 + my.val < 26 by omega, Fin.ext_iff]
    · apply deriv_rel _ v _ hvr hvb
      have : (fun i : Fin 26 =>
          decide ((⟨ρ i.val, hl i.val i.isLt⟩ : Fin 26) = Fin.castAdd 13 (σ p))) =
          (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)) := by
        funext i
        rw [← pi_castAdd p]
        simp only [decide_eq_decide]
        exact ⟨pi_inj _ _, fun h => by rw [h]⟩
      rw [this]; exact hvd
    · show v' (ρ C.output) = false
      rw [hvr]; exact hvo
    · intro mx
      have := mx.isLt
      refine ⟨?_, by simp [w', show 13 + mx.val < 26 by omega]⟩
      simp [w', this, show mx.val < 26 by omega, Fin.ext_iff]
    · apply deriv_rel _ w _ hwr hwb
      have : (fun i : Fin 26 =>
          decide ((⟨ρ i.val, hl i.val i.isLt⟩ : Fin 26) = Fin.natAdd 13 (τ l))) =
          (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)) := by
        funext i
        rw [← pi_natAdd l]
        simp only [decide_eq_decide]
        exact ⟨pi_inj _ _, fun h => by rw [h]⟩
      rw [this]; exact hwd
    · show w' (ρ C.output) = false
      rw [hwr]; exact hwo
  have RH : ∀ σ τ : Fin 13 → Fin 13, Function.Injective σ → Function.Injective τ →
      ∃ ρ : ℕ → ℕ, ∃ hl : (∀ a, a < 26 → ρ a < 26), (∀ a, 26 ≤ a → ρ a = a) ∧
        Function.Injective ρ ∧ (∀ u : Fin 13, ρ u.val = (σ u).val) ∧
        (∀ t : Fin 13, ρ (13 + t.val) = 13 + (τ t).val) := by
    intro σ τ hs hr
    refine ⟨fun a => if h : a < 13 then (σ ⟨a, h⟩).val
      else if h2 : a < 26 then 13 + (τ ⟨a - 13, by omega⟩).val else a, ?_, ?_, ?_, ?_, ?_⟩
    · intro a h
      dsimp only
      split_ifs with h1
      · have := (σ ⟨a, h1⟩).isLt; omega
      · have := (τ ⟨a - 13, by omega⟩).isLt; omega
    · intro a h
      dsimp only
      split_ifs <;> omega
    · intro a b hab
      dsimp only at hab
      split_ifs at hab
      all_goals first
        | omega
        | (have := hs (Fin.ext hab); simp at this; omega)
        | (have h' : (τ ⟨a - 13, by omega⟩).val = (τ ⟨b - 13, by omega⟩).val := by omega
           have := hr (Fin.ext h'); simp at this; omega)
        | (have := (σ ⟨a, by omega⟩).isLt; omega)
        | (have := (σ ⟨b, by omega⟩).isLt; omega)
        | (have := (τ ⟨a - 13, by omega⟩).isLt; omega)
        | (have := (τ ⟨b - 13, by omega⟩).isLt; omega)
    · intro u
      dsimp only
      rw [dif_pos u.isLt]
    · intro t
      dsimp only
      rw [dif_neg (by omega), dif_pos (by omega)]
      simp
  have fin : ∀ (C : Circuit) (σ τ : Fin 13 → Fin 13) (d : Fin 13),
      (∀ u t : Fin 13, (σ u = τ t ∨ σ u = τ t + 1 ∨ σ u = τ t + 3 ∨ σ u = τ t + 9) ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9)) →
      Function.Bijective σ → Function.Bijective τ → σ 0 = 0 → τ d = 0 →
      63 ≤ C.size → C.size ≤ 64 → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
      ((0 : Fin 13) = d ∨ (0 : Fin 13) = d + 1 ∨ (0 : Fin 13) = d + 3 ∨ (0 : Fin 13) = d + 9) →
      (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = d)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 (0 : Fin 13))))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 (0 : Fin 13))))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = (0 : Fin 13)) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 d)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 d)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) → False := by
    intro C σ τ d hc bs br h0 hd h1 h2 hS hF hI hVW
    obtain ⟨ρ, hl, hb, hinj, hσ, hτ⟩ := RH σ τ bs.1 br.1
    obtain ⟨hsz, hS', hF', -, hVW'⟩ :=
      T σ τ ρ hl hb hinj hσ hτ bs br hc C _ 0 d rfl hS hF hI hVW
    rw [h0, hd] at hVW'
    obtain ⟨⟨v, hv0, hvd, hvo⟩, ⟨w, hw0, hwd, hwo⟩⟩ := hVW'
    have e1 : ∀ i : Fin 26, decide (i = Fin.castAdd 13 (0 : Fin 13)) = decide (i.val = 0) := by
      decide
    have e2 : ∀ i : Fin 26, decide (i = Fin.natAdd 13 (0 : Fin 13)) = decide (i.val = 13) := by
      decide
    simp only [e1] at hvd
    simp only [e2] at hwd
    refine hB ⟨Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output),
      by rw [hsz]; exact h1, by rw [hsz]; exact h2, hS', hF', ⟨v, ?_, hvd, hvo⟩,
      ⟨w, ?_, hwd, hwo⟩⟩
    · intro n hn
      by_cases hn13 : n < 13
      · have h3 := (hv0 ⟨n, hn13⟩).1
        simp only at h3
        rw [h3, eq_comm, decide_eq_false_iff_not]
        omega
      · have h3 := (hv0 ⟨n - 13, by omega⟩).2
        simp only [show 13 + (n - 13) = n by omega] at h3
        rw [h3]
        simp only [decide_eq_decide, Fin.ext_iff, Fin.val_zero]
        omega
    · intro n hn
      by_cases hn13 : n < 13
      · have h3 := (hw0 ⟨n, hn13⟩).1
        simp only at h3
        rw [h3]
        simp only [Fin.ext_iff, Fin.val_zero]
      · have h3 := (hw0 ⟨n - 13, by omega⟩).2
        simp only [show 13 + (n - 13) = n by omega] at h3
        rw [h3, eq_comm, decide_eq_false_iff_not]
        omega
  have flag_cases : ∀ a b : Fin 13, (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) →
      b - a = 0 ∨ b - a = 4 ∨ b - a = 10 ∨ b - a = 12 := by decide
  rintro ⟨C, hsz, hS, hF, p, l, hI, hVW⟩
  have tcol : ∀ u t : Fin 13, ((fun u : Fin 13 => u - p) u = (fun u : Fin 13 => u - p) t ∨
      (fun u : Fin 13 => u - p) u = (fun u : Fin 13 => u - p) t + 1 ∨
      (fun u : Fin 13 => u - p) u = (fun u : Fin 13 => u - p) t + 3 ∨
      (fun u : Fin 13 => u - p) u = (fun u : Fin 13 => u - p) t + 9) ↔
      (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) := by
    intro u t
    simp only [sub_add_eq_add_sub, sub_left_inj]
  obtain ⟨ρ, hl, hb, hinj, hσ, hτ⟩ :=
    RH (fun u : Fin 13 => u - p) (fun u : Fin 13 => u - p)
      (Equiv.subRight p).injective (Equiv.subRight p).injective
  obtain ⟨hsz1, hS1, hF1, hI1, hVW1⟩ :=
    T (fun u : Fin 13 => u - p) (fun u : Fin 13 => u - p) ρ hl hb hinj hσ hτ
      (Equiv.subRight p).bijective (Equiv.subRight p).bijective tcol C _ p l rfl hS hF hI hVW
  simp only [sub_self] at hI1 hVW1
  have h63' := h63 C hS hF
  have hs1 : 63 ≤ (Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ)))
      (ρ C.output)).size := by rw [hsz1]; exact h63'
  have hs2 : (Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ)))
      (ρ C.output)).size ≤ 64 := by rw [hsz1]; exact hsz
  rcases flag_cases p l hI with h | h | h | h
  · rw [h] at hI1 hVW1
    exact fin _ id id 0 (fun u t => Iff.rfl) Function.bijective_id Function.bijective_id rfl rfl
      hs1 hs2 hS1 hF1 hI1 hVW1
  · rw [h] at hI1 hVW1
    obtain ⟨σ2, τ2, hc2, bs2, bt2, h02, hd2⟩ : ∃ σ τ : Fin 13 → Fin 13,
        (∀ u t : Fin 13, (σ u = τ t ∨ σ u = τ t + 1 ∨ σ u = τ t + 3 ∨ σ u = τ t + 9) ↔
          (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9)) ∧
        Function.Bijective σ ∧ Function.Bijective τ ∧ σ 0 = 0 ∧ τ 4 = 0 :=
      ⟨![0, 2, 4, 8, 1, 9, 6, 3, 7, 12, 10, 11, 5], ![12, 1, 8, 5, 0, 6, 3, 7, 11, 9, 10, 2, 4],
        by decide, by decide, by decide, by decide, by decide⟩
    exact fin _ σ2 τ2 4 hc2 bs2 bt2 h02 hd2 hs1 hs2 hS1 hF1 hI1 hVW1
  · rw [h] at hI1 hVW1
    obtain ⟨σ2, τ2, hc2, bs2, bt2, h02, hd2⟩ : ∃ σ τ : Fin 13 → Fin 13,
        (∀ u t : Fin 13, (σ u = τ t ∨ σ u = τ t + 1 ∨ σ u = τ t + 3 ∨ σ u = τ t + 9) ↔
          (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9)) ∧
        Function.Bijective σ ∧ Function.Bijective τ ∧ σ 0 = 0 ∧ τ 10 = 0 :=
      ⟨![0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7], ![12, 1, 8, 7, 10, 2, 3, 5, 9, 11, 0, 6, 4],
        by decide, by decide, by decide, by decide, by decide⟩
    exact fin _ σ2 τ2 10 hc2 bs2 bt2 h02 hd2 hs1 hs2 hS1 hF1 hI1 hVW1
  · rw [h] at hI1 hVW1
    obtain ⟨σ2, τ2, hc2, bs2, bt2, h02, hd2⟩ : ∃ σ τ : Fin 13 → Fin 13,
        (∀ u t : Fin 13, (σ u = τ t ∨ σ u = τ t + 1 ∨ σ u = τ t + 3 ∨ σ u = τ t + 9) ↔
          (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9)) ∧
        Function.Bijective σ ∧ Function.Bijective τ ∧ σ 0 = 0 ∧ τ 12 = 0 :=
      ⟨![0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9], ![12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0],
        by decide, by decide, by decide, by decide, by decide⟩
    exact fin _ σ2 τ2 12 hc2 bs2 bt2 h02 hd2 hs1 hs2 hS1 hF1 hI1 hVW1
