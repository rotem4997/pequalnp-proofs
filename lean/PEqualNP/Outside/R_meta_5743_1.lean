import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5743_1 :
  (let F := Fin 13; let V := Fin 26; let B := Finset F; have x1 : B := {(0 : F), (1 : F), (3 : F), (9 : F)}; let x2 : F → F → Prop := fun (x2 x3 : F) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : B → F → Prop := fun (x3 : B) (x4 : F) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : B → Prop := fun (x4 : B) => ∀ x5 ∉ x4, ∃ (x7 : F), x3 x4 x7 ∧ x2 x5 x7; have x5 : B → V → Bool := fun (x5 : B) (x6 : V) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : F), x6 = Fin.natAdd (13 : ℕ) x7 ∧ x3 x5 x7); have x6 : B → Prop := fun (x6 : B) => (∃ (x7 : F), ∀ x8 ∈ x6, x2 x8 x7) ∨ ∃ (x7 : F), ∀ (x8 : F), x3 x6 x8 → x2 x7 x8; let edge := fun (p l : F) (i : V) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l); let seed := fun i : V => (7405575 : ℕ).testBit i.val;
    ∀ S : B, x4 S → ¬x6 S →
    ∃ σ : V → V, (∀ p l, x2 p l → ∃ a b, x2 a b ∧ edge p l ∘ σ = edge a b) ∧
      (∀ T, x4 T → x6 T → ∃ U, x4 U ∧ x6 U ∧ x5 T ∘ σ = x5 U) ∧ seed ∘ σ = x5 S) →
  (let F := Fin 13; let V := Fin 26; let B := Finset F; have x1 : B := {(0 : F), (1 : F), (3 : F), (9 : F)}; let x2 : F → F → Prop := fun (x2 x3 : F) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : B → F → Prop := fun (x3 : B) (x4 : F) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : B → Prop := fun (x4 : B) => ∀ x5 ∉ x4, ∃ (x7 : F), x3 x4 x7 ∧ x2 x5 x7; have x5 : B → V → Bool := fun (x5 : B) (x6 : V) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : F), x6 = Fin.natAdd (13 : ℕ) x7 ∧ x3 x5 x7); have x6 : B → Prop := fun (x6 : B) => (∃ (x7 : F), ∀ x8 ∈ x6, x2 x8 x7) ∨ ∃ (x7 : F), ∀ (x8 : F), x3 x6 x8 → x2 x7 x8; let edge := fun (p l : F) (i : V) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l); let seed := fun i : V => (7405575 : ℕ).testBit i.val;
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    C.size ≤ 63 → (∀ p l, x2 p l → PEqualNP.MetaComplexity.circuitFun 26 C (edge p l) = true) →
    (∀ T, x4 T → x6 T → PEqualNP.MetaComplexity.circuitFun 26 C (x5 T) = false) →
    PEqualNP.MetaComplexity.circuitFun 26 C seed = false) →
  (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7; have x5 : Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ x3 x5 x7); have x6 : Finset (Fin (13 : ℕ)) → Prop := fun (x6 : Finset (Fin (13 : ℕ))) => (∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x6, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x6 x8 → x2 x7 x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x2 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x6 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x5 x11) = Bool.false) → ∀ (x12 : Finset (Fin (13 : ℕ))), (x12.card = (3 : ℕ) ∨ ∃ (x13 : Finset (Fin (13 : ℕ))), x13.card = (3 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), x14 ∈ x13 ↔ x3 x12 x14) → x4 x12 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x5 x12) = Bool.false) := by
  intro orbit fixed
  have transport {n : ℕ} (σ : Fin n → Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (hm : PEqualNP.MetaComplexity.Monotone2 C) :
      ∃ B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 B ∧
        B.size = C.size ∧ ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n B z =
          PEqualNP.MetaComplexity.circuitFun n C (z ∘ σ) := by
    let ρ (i : ℕ) : ℕ := if h : i < n then (σ ⟨i,h⟩).val else i
    let rename (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map ρ⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map rename, ρ C.output⟩
    have mono : PEqualNP.MetaComplexity.Monotone2 C' := by
      intro g hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      exact ⟨(hm a ha).1, by simpa [rename] using (hm a ha).2⟩
    have size : C'.size = C.size := by
      change (C.gates.map rename).length = C.gates.length
      simp only [List.length_map]
    let step (v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
    have fold (gs : List PEqualNP.CircuitLowerBounds.Gate) (v w : List Bool)
        (hlen : n ≤ v.length) (same : w.length = v.length)
        (rel : ∀ i, w.getD (ρ i) false = v.getD i false) :
        ∀ i, ((gs.map rename).foldl step w).getD (ρ i) false =
          (gs.foldl step v).getD i false := by
      induction gs generalizing v w with
      | nil => exact rel
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        have get : (g.inputs.map ρ).map (fun i => w.getD i false) =
            g.inputs.map (fun i => v.getD i false) := by
          rw [List.map_map]
          exact congrArg (fun f : ℕ → Bool => g.inputs.map f) (funext rel)
        have gate : (rename g).op.eval ((rename g).inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => v.getD i false) := by
          exact congrArg g.op.eval get
        apply ih
        · simp [step]; omega
        · simp [step, same]
        · intro i
          change (w ++ [_]).getD (ρ i) false = (v ++ [_]).getD i false
          rw [gate]
          by_cases hi : i < v.length
          · have hi' : ρ i < w.length := by
              by_cases hn : i < n
              · have := (σ ⟨i,hn⟩).isLt
                simpa [ρ,hn,same] using (lt_of_lt_of_le this hlen)
              · simpa [ρ,hn,same] using hi
            simpa only [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi'] using rel i
          · have heq : ρ i = i := by simp [ρ, show ¬ i < n by omega]
            rw [heq, List.getD_append_right _ _ _ _ (show w.length ≤ i by omega),
              List.getD_append_right _ _ _ _ (show v.length ≤ i by omega), same]
    have input_get (v : Fin n → Bool) (i : Fin n) :
        (List.ofFn v).getD i.val false = v i := by simp [List.getD_eq_getElem?_getD]
    have evaluate (z : Fin n → Bool) :
        PEqualNP.MetaComplexity.circuitFun n C' z =
        PEqualNP.MetaComplexity.circuitFun n C (z ∘ σ) := by
      apply fold C.gates (List.ofFn (z ∘ σ)) (List.ofFn z) (by simp) (by simp) _ C.output
      intro i
      by_cases h : i < n
      · rw [show ρ i = (σ ⟨i,h⟩).val by simp [ρ,h],input_get]
        exact (input_get (z ∘ σ) ⟨i,h⟩).symm
      · simp [ρ,h,List.getD_eq_getElem?_getD]
    exact ⟨C',mono,size,evaluate⟩
  intro D inc miss maximal row deg C hm hs hp hn S _ hmax
  let edge := fun (p l : Fin 13) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let seed := fun i : Fin 26 => (7405575 : ℕ).testBit i.val
  by_cases hdeg : deg S
  · exact hn S hmax hdeg
  obtain ⟨σ, hEdge, hNeg, hTarget⟩ := orbit S hmax hdeg
  obtain ⟨C', mono, size, evaluate⟩ := transport σ C hm
  have mapEdge : ∀ p l, inc p l → ∃ a b, inc a b ∧ (edge p l ∘ σ) = edge a b := hEdge
  have mapNeg : ∀ T, maximal T → deg T → ∃ U, maximal U ∧ deg U ∧ (row T ∘ σ) = row U := hNeg
  have mapTarget : seed ∘ σ = row S := hTarget
  have hp' (p l : Fin 13) (h : inc p l) :
      PEqualNP.MetaComplexity.circuitFun 26 C' (edge p l) = true := by
    obtain ⟨a,b,hab,he⟩ := mapEdge p l h
    exact (evaluate (edge p l)).trans ((congrArg (PEqualNP.MetaComplexity.circuitFun 26 C) he).trans (hp a b hab))
  have hn' (T : Finset (Fin 13)) (ht : maximal T) (hd : deg T) :
      PEqualNP.MetaComplexity.circuitFun 26 C' (row T) = false := by
    obtain ⟨U,hu,hd',he⟩ := mapNeg T ht hd
    exact (evaluate (row T)).trans ((congrArg (PEqualNP.MetaComplexity.circuitFun 26 C) he).trans (hn U hu hd'))
  have endrow := fixed C' mono (size.le.trans hs) hp' hn'
  change PEqualNP.MetaComplexity.circuitFun 26 C' (seed) = false at endrow
  exact ((congrArg (PEqualNP.MetaComplexity.circuitFun 26 C) mapTarget).symm.trans
    (evaluate (seed)).symm).trans endrow
