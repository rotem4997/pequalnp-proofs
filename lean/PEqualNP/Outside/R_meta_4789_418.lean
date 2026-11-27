import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4789_418
    (resources :
      let U : Type := Fin 13
      let S : Finset U := {0,1,3,9}
      let I : U → U → Prop := fun p w => ∃ d ∈ S, p = w+d
      let A : Finset U → U → Prop := fun P w => ∀ p ∈ P, ¬ I p w
      let X : Type := Fin 26 → Bool
      let T : U → U → X := fun p w i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
      let F : Finset U → X := fun P i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w, i = Fin.natAdd 13 w ∧ A P w)
      let N : Finset U → Prop := fun P => (∀ p ∉ P, ∃ w, A P w ∧ I p w) ∧ ((∃ w, ∀ p ∈ P, I p w) ∨ ∃ p, ∀ w, A P w → I p w)
      ∀ C : Circuit, Monotone2 C →
      let h := (C.gates.filter (fun g => g.op.eval [])).length
      let V : ℕ → X → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
      let H : (X → Bool) → Prop := fun f => ∀ p w, I p w → f (T p w) = true
      let test : (ℕ × ℕ) → X → Bool := fun e x => V e.1 x || V e.2 x
      let covers : Finset (ℕ × ℕ) → Prop := fun K => ∀ P, N P → ∃ e ∈ K, ¬ test e (F P) = true
      ∀ K : Finset (ℕ × ℕ), (∀ e∈K,H (test e)) → covers K →
        h+11≤C.size ∧ 236≤K.card*2^h)
    (bounded :
      let U : Type := Fin 13
      let S : Finset U := {0,1,3,9}
      let I : U → U → Prop := fun p w => ∃ d ∈ S, p = w+d
      let A : Finset U → U → Prop := fun P w => ∀ p ∈ P, ¬ I p w
      let X : Type := Fin 26 → Bool
      let T : U → U → X := fun p w i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
      let F : Finset U → X := fun P i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w, i = Fin.natAdd 13 w ∧ A P w)
      let N : Finset U → Prop := fun P => (∀ p ∉ P, ∃ w, A P w ∧ I p w) ∧ ((∃ w, ∀ p ∈ P, I p w) ∨ ∃ p, ∀ w, A P w → I p w)
      ∀ C : Circuit, Monotone2 C →
      let h := (C.gates.filter (fun g => g.op.eval [])).length
      let V : ℕ → X → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
      let H : (X → Bool) → Prop := fun f => ∀ p w, I p w → f (T p w) = true
      let test : (ℕ × ℕ) → X → Bool := fun e x => V e.1 x || V e.2 x
      let covers : Finset (ℕ × ℕ) → Prop := fun K => ∀ P, N P → ∃ e ∈ K, ¬ test e (F P) = true
      ∀ K : Finset (ℕ × ℕ), 2≤K.card → K.card≤24 → C.size+2*K.card≤64 →
        h+11≤C.size → 236≤K.card*2^h → (∀ e∈K,e.1<28+C.size ∧ e.2<28+C.size) →
        (∀ e∈K,H (test e) ∧ ¬H (V e.1) ∧ ¬H (V e.2)) →
        covers K → (∀ e∈K,¬covers (K.erase e)) → False) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (∀ x20 ∈ x15, ¬x14 (x15.erase x20)) → False := by
  intro U S I A X T F N C mono V H test covers K low budget good covered minimal
  classical
  let h := (C.gates.filter (fun g => g.op.eval [])).length
  obtain ⟨orBound,andBound⟩ := resources C mono K (fun e he => (good e he).1) covered
  change h+11≤C.size at orBound
  change 236≤K.card*2^h at andBound
  have small : K.card≤24 := by
    by_contra! big
    have few : h≤3 := by omega
    have pow : 2^h≤8 := Nat.pow_le_pow_right (by decide) few
    have top : K.card≤26 := by omega
    have v := Nat.mul_le_mul top pow
    omega
  have live (e) (he : e∈K) : e.1<28+C.size ∧ e.2<28+C.size := by
    obtain ⟨both,left,right⟩ := good e he
    have dead (i : ℕ) (ge : 28 + C.size ≤ i) (x : X) : V i x=false := by
      change (C.wires (List.ofFn x ++ [true,false])).getD i false=false
      apply List.getD_eq_default
      have length (gs : List Gate) (w : List Bool) :
          (gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun j => z.getD j false)]) w).length = w.length+gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons,ih]
          simp only [List.length_append,List.length_cons,List.length_nil]
          omega
      unfold Circuit.wires
      rw [length]
      change 28 + C.gates.length ≤ i at ge
      simpa only [List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using ge
    constructor
    · by_contra! ge
      apply right
      intro p l inc
      have yes := both p l inc
      change (V e.1 (T p l) || V e.2 (T p l))=true at yes
      simpa only [dead e.1 ge,Bool.false_or] using yes
    · by_contra! ge
      apply left
      intro p l inc
      have yes := both p l inc
      change (V e.1 (T p l) || V e.2 (T p l))=true at yes
      simpa only [dead e.2 ge,Bool.or_false] using yes
  exact bounded C mono K low small budget orBound andBound live good covered minimal
