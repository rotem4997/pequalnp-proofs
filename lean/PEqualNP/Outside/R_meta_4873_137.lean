import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

theorem PEqualNP.Outside.R_meta_4873_137
  (extend : ∀ (C : Circuit) (u v : ℕ) (op : GateOp), IsAO2 14 C →
    (∀ g ∈ C.gates, g.inputs.Nodup) → (op = .or ∨ op = .and) →
    u < 14+C.size → v < 14+C.size → u ≠ v →
    ∃ D : Circuit, D.size = C.size+1 ∧ IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.output = 14+C.size ∧ D.gates[C.size]? = some ⟨op,[u,v]⟩ ∧
      ∀ x : Fin 14 → Bool,
        (∀ i < 14+C.size, wireValue D 14 x i = wireValue C 14 x i) ∧
        wireValue D 14 x D.output = op.eval [wireValue C 14 x u,wireValue C 14 x v])
  (core : ∃ (C : Circuit) (h g : ℕ), C.size ≤ 24 ∧ IsAO2 14 C ∧
    (∀ t ∈ C.gates, t.inputs.Nodup) ∧ h < 14+C.size ∧ g < 14+C.size ∧ h ≠ 2 ∧ h ≠ g ∧
    ∀ x : Fin 14 → Bool, let W := wireValue C 14 x;
                          (W h || (W 2 && W g)) = decide (∃ p l : Fin 7,
                            (p = l ∨ p = l+1 ∨ p = l+3) ∧
                            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
                          (∀ k ∈ [(0 : Fin 14),7], x = (fun i => decide (i=k)) →
                            W 2 = false ∧ W g = false)) :
  have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false := by
  classical
  intro I F
  obtain ⟨C,h,g,budget,ao,nd,hh,hg,h2,hg' ,spec⟩ := core
  have raw : 2 < 14+C.size := by omega
  obtain ⟨A,sa,aa,da,oa,_,va⟩ := extend C h 2 .or ao nd (Or.inl rfl) hh raw h2
  obtain ⟨B,sb,ab,db,ob,_,vb⟩ := extend A h g .or aa da (Or.inl rfl) (by omega) (by omega) hg'
  obtain ⟨D,sd,ad,dd,od,gate,vd⟩ := extend B A.output B.output .and ab db (Or.inr rfl)
    (by omega) (by omega) (by omega)
  have vals (x : Fin 14 → Bool) :
      wireValue D 14 x A.output = (wireValue C 14 x h || wireValue C 14 x 2) ∧
      wireValue D 14 x B.output = (wireValue C 14 x h || wireValue C 14 x g) ∧
      D.eval (List.ofFn x) = (wireValue C 14 x h || (wireValue C 14 x 2 && wireValue C 14 x g)) := by
    have a := (va x).2
    have b := (vb x).2
    rw [(va x).1 h hh, (va x).1 g hg] at b
    have keep := (vb x).1 A.output (by omega)
    have d := (vd x).2
    rw [keep,a,b] at d
    have ka := (vd x).1 A.output (by omega)
    have kb := (vd x).1 B.output (by omega)
    rw [keep,a] at ka
    rw [b] at kb
    refine ⟨?_, ?_, ?_⟩
    · rw [ka]
      cases wireValue C 14 x h <;> cases wireValue C 14 x 2 <;> rfl
    · rw [kb]
      cases wireValue C 14 x h <;> cases wireValue C 14 x g <;> rfl
    · change wireValue D 14 x D.output = _
      rw [d]
      cases wireValue C 14 x h <;> cases wireValue C 14 x 2 <;> cases wireValue C 14 x g <;> rfl
  refine ⟨D,B.size,A.output,B.output,by omega,ad,dd,od,gate,?_,?_,?_⟩
  · intro p l inc
    let x := fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
    change D.eval (List.ofFn x) = true
    rw [(vals x).2.2,(spec x).1,decide_eq_true_eq]
    exact ⟨p,l,inc,by simp [x],by simp [x]⟩
  · intro x hx
    rw [(vals x).2.2,(spec x).1,decide_eq_false_iff_not]
    exact hx.1
  · intro k hk
    let x := fun i : Fin 14 => decide (i=k)
    have negative : ¬ ∃ p l : Fin 7, I p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      rintro ⟨p,l,_,hp,hl⟩
      simp only [x, decide_eq_true_eq] at hp hl
      have eqv := congrArg Fin.val (hp.trans hl.symm)
      simp at eqv
      omega
    have no := (spec x).1
    change (_ : Bool) = decide (F x) at no
    rw [decide_eq_false negative] at no
    have off := (spec x).2 k hk rfl
    have offH := (Bool.or_eq_false_iff.mp no).1
    change wireValue D 14 x A.output = false ∧ wireValue D 14 x B.output = false
    rw [(vals x).1,(vals x).2.1,offH,off.1,off.2]
    decide
