import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1482_1 :
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (v : ℕ → Bool),
       (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
       (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, u - t ∈ D ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
       PEqualNP.TopForm.andPairs 26 C = 0 →
       p - l ∈ D →
       (∀ m : Fin 13, v m.val = false ∧ v (13 + m.val) = decide (m = l)) →
       (let P := C.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p)))
        ∀ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate) (c d : ℕ), C.gates[k]? = some h → h.inputs = [c, d] → (h.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + k) = ((P.getD c false && v d) || (v c && P.getD d false))) ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + k) = (v c || v d))) →
       v C.output = true) →
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     let A : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and
     let O : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or
     ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (v w : ℕ → Bool),
       let tr : Fin 26 → ℕ → (ℕ → Bool) → Prop := fun z t u =>
         (∀ i < 26, u i = decide (i = t)) ∧
         let Z := C.wires (List.ofFn (fun i : Fin 26 => decide (i = z)))
         ∀ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate) (c d : ℕ), C.gates[k]? = some h → h.inputs = [c, d] →
           (h.op = A → u (26 + k) = ((Z.getD c false && u d) || (u c && Z.getD d false))) ∧
           (h.op = O → u (26 + k) = (u c || u d))
       C.size ≤ 64 →
       (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = A ∨ g.op = O) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
       (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, u - t ∈ D ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
       0 < PEqualNP.TopForm.andPairs 26 C →
       (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = A → ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true → C.eval (List.ofFn x) = true) →
       p - l ∈ D →
       tr (Fin.castAdd 13 p) (13 + l.val) v →
       tr (Fin.natAdd 13 l) p.val w →
       v C.output = true ∨ w C.output = true) →
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     let A : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and
     let O : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or
     ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (v w : ℕ → Bool),
       let tr : Fin 26 → ℕ → (ℕ → Bool) → Prop := fun z t u =>
         (∀ i < 26, u i = decide (i = t)) ∧
         let Z := C.wires (List.ofFn (fun i : Fin 26 => decide (i = z)))
         ∀ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate) (c d : ℕ), C.gates[k]? = some h → h.inputs = [c, d] →
           (h.op = A → u (26 + k) = ((Z.getD c false && u d) || (u c && Z.getD d false))) ∧
           (h.op = O → u (26 + k) = (u c || u d))
       C.size ≤ 64 →
       (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = A ∨ g.op = O) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
       (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, u - t ∈ D ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) →
       0 < PEqualNP.TopForm.andPairs 26 C →
       (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = A ∧ ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧ C.eval (List.ofFn x) = false) →
       p - l ∈ D →
       tr (Fin.castAdd 13 p) (13 + l.val) v →
       tr (Fin.natAdd 13 l) p.val w →
       v C.output = true ∨ w C.output = true) →
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  classical
  intro c1 c2 c3
  rintro ⟨C, hsz, hgates, heval, p, l, hpl, ⟨v, hv0, hvg, hvf⟩, ⟨w, hw0, hwg, hwf⟩⟩
  have hdiff : ∀ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ↔ u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  have heval' : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, u - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
    intro x
    rw [heval x]
    constructor
    · rintro ⟨u, t, h, h1, h2⟩; exact ⟨u, t, (hdiff u t).mp h, h1, h2⟩
    · rintro ⟨u, t, h, h1, h2⟩; exact ⟨u, t, (hdiff u t).mpr h, h1, h2⟩
  have hpl' : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := (hdiff p l).mp hpl
  have hv_init : ∀ i < 26, v i = decide (i = 13 + l.val) := by
    intro i hi
    by_cases h13 : i < 13
    · have h1 := (hv0 ⟨i, h13⟩).1
      have h2 : ¬ (i = 13 + l.val) := by omega
      simp [h1, h2]
    · have hlt : i - 13 < 13 := by omega
      have h1 := (hv0 ⟨i - 13, hlt⟩).2
      have h2 : 13 + (i - 13) = i := by omega
      rw [show (⟨i - 13, hlt⟩ : Fin 13).val = i - 13 from rfl, h2] at h1
      rw [h1]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Fin.ext_iff]
      show i - 13 = l.val ↔ i = 13 + l.val
      omega
  have hw_init : ∀ i < 26, w i = decide (i = p.val) := by
    intro i hi
    by_cases h13 : i < 13
    · have h1 := (hw0 ⟨i, h13⟩).1
      rw [show (⟨i, h13⟩ : Fin 13).val = i from rfl] at h1
      rw [h1]
      apply Bool.eq_iff_iff.mpr
      simp [Fin.ext_iff]
    · have hlt : i - 13 < 13 := by omega
      have h1 := (hw0 ⟨i - 13, hlt⟩).2
      have h2 : 13 + (i - 13) = i := by omega
      rw [show (⟨i - 13, hlt⟩ : Fin 13).val = i - 13 from rfl, h2] at h1
      have h3 : ¬ (i = p.val) := by have := p.isLt; omega
      simp [h1, h3]
  by_cases hnest : 0 < PEqualNP.TopForm.andPairs 26 C
  · by_cases hdirty : ∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧ C.eval (List.ofFn x) = false
    · rcases c3 C p l v w hsz hgates heval' hnest hdirty hpl' ⟨hv_init, hvg⟩ ⟨hw_init, hwg⟩ with ht | ht
      · rw [hvf] at ht; cases ht
      · rw [hwf] at ht; cases ht
    · have hclean : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true → C.eval (List.ofFn x) = true := by
        intro k hk hop x hkx
        cases hcx : C.eval (List.ofFn x)
        · exfalso; exact hdirty ⟨k, hk, hop, x, hkx, hcx⟩
        · rfl
      rcases c2 C p l v w hsz hgates heval' hnest hclean hpl' ⟨hv_init, hvg⟩ ⟨hw_init, hwg⟩ with ht | ht
      · rw [hvf] at ht; cases ht
      · rw [hwf] at ht; cases ht
  · have hflat : PEqualNP.TopForm.andPairs 26 C = 0 := by omega
    have ht := c1 C p l v hgates heval' hflat hpl' hv0 hvg
    rw [hvf] at ht; cases ht
