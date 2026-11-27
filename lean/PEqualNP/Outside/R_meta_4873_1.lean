import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4873_1
    (h1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 22 ∧ PEqualNP.TopForm.IsAO2 14 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 14 ≤ C.output ∧
      C.output < 14 + C.size ∧
      ∀ x : Fin 14 → Bool,
        (C.eval (List.ofFn x) = true → ∃ p l : Fin 7,
          (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
        ((∃ p l : Fin 7, l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
            C.eval (List.ofFn x) = true))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      14 ≤ C.output → C.output < 14 + C.size →
      let k := 14 + C.size
      let D : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨C.gates ++ [⟨.or, [1, 2]⟩, ⟨.or, [k, 4]⟩,
          ⟨.or, [C.output, 8]⟩, ⟨.or, [C.output, k + 1]⟩,
          ⟨.and, [k + 2, k + 3]⟩], k + 4⟩
      PEqualNP.TopForm.IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 14 → Bool,
        PEqualNP.BlindGate.wireValue D 14 x (k + 2) =
          (C.eval (List.ofFn x) || x 8) ∧
        PEqualNP.BlindGate.wireValue D 14 x (k + 3) =
          (C.eval (List.ofFn x) || ((x 1 || x 2) || x 4)) ∧
        D.eval (List.ofFn x) =
          ((C.eval (List.ofFn x) || x 8) &&
            (C.eval (List.ofFn x) || ((x 1 || x 2) || x 4)))) : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false := by
  classical
  intro E F
  obtain ⟨C, hs, hao, hnd, hlow, hout, hcorrect⟩ := h1
  let k := 14 + C.size
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates ++ [⟨.or, [1, 2]⟩, ⟨.or, [k, 4]⟩,
      ⟨.or, [C.output, 8]⟩, ⟨.or, [C.output, k + 1]⟩,
      ⟨.and, [k + 2, k + 3]⟩], k + 4⟩
  obtain ⟨hdao, hdnd, hvalues⟩ := h2 C hao hnd hlow hout
  change PEqualNP.TopForm.IsAO2 14 D at hdao
  change (∀ g ∈ D.gates, g.inputs.Nodup) at hdnd
  change ∀ x : Fin 14 → Bool,
    PEqualNP.BlindGate.wireValue D 14 x (k + 2) =
      (C.eval (List.ofFn x) || x 8) ∧
    PEqualNP.BlindGate.wireValue D 14 x (k + 3) =
      (C.eval (List.ofFn x) || ((x 1 || x 2) || x 4)) ∧
    D.eval (List.ofFn x) =
      ((C.eval (List.ofFn x) || x 8) &&
        (C.eval (List.ofFn x) || ((x 1 || x 2) || x 4))) at hvalues
  have hnegative (x : Fin 14 → Bool) (hx : ¬ F x) :
      C.eval (List.ofFn x) = false := by
    cases hv : C.eval (List.ofFn x) with
    | false => rfl
    | true =>
      obtain ⟨p,l,he,hp,hl⟩ := (hcorrect x).1 hv
      exact (hx ⟨p,l,he,hp,hl⟩).elim
  refine ⟨D, C.size + 4, k + 2, k + 3, ?_, hdao, hdnd, ?_, ?_, ?_, ?_, ?_⟩
  · change (C.gates ++ _).length ≤ 27
    rw [List.length_append]
    change C.gates.length + 5 ≤ 27
    change C.gates.length ≤ 22 at hs
    omega
  · change k + 4 = 14 + (C.size + 4)
    dsimp [k]
    omega
  · change (C.gates ++ _)[C.gates.length + 4]? = _
    simp
  · intro p l he
    let x : Fin 14 → Bool := fun i => decide
      (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
    change D.eval (List.ofFn x) = true
    rw [(hvalues x).2.2]
    by_cases hl : l = 1
    · subst l
      have hl8 : x 8 = true := by simp [x]
      have hp : ((x 1 || x 2) || x 4) = true := by
        fin_cases p <;> norm_num [E] at he <;> simp_all [x]
      simp [hl8, hp]
    · have hu : C.eval (List.ofFn x) = true :=
        (hcorrect x).2 ⟨p,l,hl,he,by simp [x],by simp [x]⟩
      rw [hu]
      simp
  · intro x hx
    have hu := hnegative x hx.1
    rw [(hvalues x).2.2, hu]
    simp only [Bool.false_or]
    cases hv : x 8 && ((x 1 || x 2) || x 4) with
    | false => rfl
    | true =>
      obtain ⟨hl, hp⟩ := Bool.and_eq_true_iff.mp hv
      exfalso
      apply hx.1
      rcases Bool.or_eq_true_iff.mp hp with hp | hp
      · rcases Bool.or_eq_true_iff.mp hp with hp | hp
        · exact ⟨1,1,by decide,hp,hl⟩
        · exact ⟨2,1,by decide,hp,hl⟩
      · exact ⟨4,1,by decide,hp,hl⟩
  · intro s hs'
    let x : Fin 14 → Bool := fun i => decide (i = s)
    have hn : ¬ F x := by
      rintro ⟨p,l,_,hp,hl⟩
      have hp' : Fin.castAdd 7 p = s := of_decide_eq_true hp
      have hl' : Fin.natAdd 7 l = s := of_decide_eq_true hl
      have hh := congrArg Fin.val (hp'.trans hl'.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
      omega
    have hu := hnegative x hn
    have ha := (hvalues x).1
    have hb := (hvalues x).2.1
    rw [hu] at ha hb
    rcases List.mem_cons.mp hs' with hzero | hseven
    · subst s
      simpa [x] using And.intro ha hb
    · have hs7 : s = 7 := by simpa using hseven
      subst s
      simpa [x] using And.intro ha hb
