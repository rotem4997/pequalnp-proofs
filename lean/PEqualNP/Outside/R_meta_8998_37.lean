import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_8998_37
    (cover : let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
      let thin := fun x : Fin 26 → Bool => ∃ l : Fin 13, ∀ k : Fin 13, x (Fin.natAdd 13 k) = true → k = l
      let form := fun (T : Circuit) (k : ℕ) =>
        ∀ i a b, T.gates[i]? = some ⟨.and,[a,b]⟩ →
          let P : Circuit := ⟨T.gates.take i,0⟩
          let d := P.lineDegrees 26 (Finset.Ico 13 26)
          0 < min (d.getD a 0) (d.getD b 0) →
          ∃ rs : List ℕ, rs.length ≤ k ∧ ∀ x, thin x →
            let w := P.wires (List.ofFn x)
            (w.getD a false && w.getD b false) = rs.any (fun j => w.getD j false)
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
        (∀ P L, IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
          C.eval (incidenceInput P L) = false) →
        ∃ B : Circuit, Monotone2 B ∧ B.size ≤ C.size ∧
          (∀ x, thin x → circuitFun 26 B x = circuitFun 26 C x) ∧ form B (26+B.size))
    (compress : let thin := fun x : Fin 26 → Bool => ∃ l : Fin 13, ∀ k : Fin 13, x (Fin.natAdd 13 k) = true → k = l
      let form := fun (T : Circuit) (k : ℕ) =>
        ∀ i a b, T.gates[i]? = some ⟨.and,[a,b]⟩ →
          let P : Circuit := ⟨T.gates.take i,0⟩
          let d := P.lineDegrees 26 (Finset.Ico 13 26)
          0 < min (d.getD a 0) (d.getD b 0) →
          ∃ rs : List ℕ, rs.length ≤ k ∧ ∀ x, thin x →
            let w := P.wires (List.ofFn x)
            (w.getD a false && w.getD b false) = rs.any (fun j => w.getD j false)
      ∀ B : Circuit, Monotone2 B → B.size ≤ 63 → form B (26+B.size) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ B.size ∧
          (∀ x, thin x → circuitFun 26 D x = circuitFun 26 B x) ∧ form D 2) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x1 : Fin (13 : ℕ)) => {x1, x1 + (1 : Fin (13 : ℕ)), x1 + (3 : Fin (13 : ℕ)), x1 + (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)), ∀ (x4 : Fin (13 : ℕ)), x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true → x4 = x3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     x3.size ≤ (63 : ℕ) →       (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ x1 x7 → x3.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) →         (∀ (x7 x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x1 x7 x8 → ¬PEqualNP.GenericRejection.IsGeneric x1 (0 : ℕ) x7 x8 → x3.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) →           ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.Monotone2 x8 ∧               x8.size ≤ x3.size ∧                 (∀ (x9 : Fin (26 : ℕ) → Bool), x2 x9 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 x9) ∧                   ∀ (x9 x10 x11 : ℕ),                     x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } →                       have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.take x9 x8.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };                       have x14 : List ℕ := x13.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));                       (0 : ℕ) < Min.min (x14.getD x10 (0 : ℕ)) (x14.getD x11 (0 : ℕ)) →                         ∃ (x16 : ℕ) (x17 : ℕ),                           ∀ (x18 : Fin (26 : ℕ) → Bool),                             x2 x18 →                               have x20 : List Bool := x13.wires (List.ofFn x18);                               (x20.getD x10 Bool.false && x20.getD x11 Bool.false) = (x20.getD x16 Bool.false || x20.getD x17 Bool.false)) := by
  dsimp only at cover compress ⊢
  intro C hm hs hp hn
  obtain ⟨B, hb, hbc, eb, fb⟩ := cover C hm hs hp hn
  obtain ⟨D, hd, hdb, ed, fd⟩ := compress B hb (le_trans hbc hs) fb
  refine ⟨D, hd, le_trans hdb hbc, fun x hx => (ed x hx).trans (eb x hx), ?_⟩
  intro i a b hg hdeg
  obtain ⟨rs, hlen, he⟩ := fd i a b hg hdeg
  let P : Circuit := ⟨D.gates.take i, 0⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have wireCount (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  cases rs with
  | nil =>
    refine ⟨26+P.size, 26+P.size, ?_⟩
    intro x hx
    have h := he x hx
    change _ = ((P.wires (List.ofFn x)).getD _ false || (P.wires (List.ofFn x)).getD _ false)
    have sz : (P.wires (List.ofFn x)).length = 26+P.size := by
      change (P.gates.foldl step (List.ofFn x)).length = _
      rw [wireCount, List.length_ofFn]; rfl
    rw [List.getD_eq_default _ _ (le_of_eq sz)]
    exact h
  | cons r rs =>
    cases rs with
    | nil => exact ⟨r,r, fun x hx => by simpa using he x hx⟩
    | cons t ts =>
      have e : ts = [] := by
        cases ts with
        | nil => rfl
        | cons u us => simp at hlen
      subst ts
      exact ⟨r,t,fun x hx => by simpa using he x hx⟩
