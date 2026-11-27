import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2147_574
    (sound :
      let I := fun (a b : Fin 13) => a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9
      let f := fun (C : Circuit) (A B : Finset (Fin 13)) => circuitFun 26 C (fun i =>
        Fin.addCases (fun p => decide (p∈A)) (fun l => decide (l∈B)) i)
      let g := fun (A B : Finset (Fin 13)) =>
        (∀ l, l∈B ↔ ∀ p∈A, ¬I p l) ∧ (∀ p∉A, ∃ l∈B,I p l) ∧
        (¬∃ l, ∀ p∈A,I p l) ∧ (¬∃ p, ∀ l∈B,I p l)
      let hit := fun (A B : Finset (Fin 13)) => ∃ a∈A, ∃ b∈B, I a b
      let low := fun C => HasLineDegree 26 (Finset.range 13) C 2 ∧ HasLineDegree 26 (Finset.Ico 13 26) C 2
      ∀ C, Monotone2 C → low C → (∀ A B, g A B → f C A B=false) →
        ∀ A B, f C A B=true → hit A B)
    (exactLower :
      let I := fun (a b : Fin 13) => a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9
      let f := fun (C : Circuit) (A B : Finset (Fin 13)) => circuitFun 26 C (fun i =>
        Fin.addCases (fun p => decide (p∈A)) (fun l => decide (l∈B)) i)
      let hit := fun (A B : Finset (Fin 13)) => ∃ a∈A, ∃ b∈B, I a b
      ∀ C, Monotone2 C → (∀ p l, I p l → f C {p} {l}=true) → (∀ A B, f C A B=true → hit A B) →
        ¬HasLineDegree 26 (Finset.range 13) C 1 → ¬HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64≤C.size)
    (normalize :
      let V := Fin 13
      let S := Finset V
      let I := fun (a b : V) => a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9
      let f := fun (C : Circuit) (A B : S) => circuitFun 26 C (fun i =>
        Fin.addCases (fun p => decide (p∈A)) (fun l => decide (l∈B)) i)
      let g := fun (A B : S) =>
        (∀ l, l∈B ↔ ∀ p∈A, ¬I p l) ∧ (∀ p∉A, ∃ l∈B,I p l) ∧
        (¬∃ l, ∀ p∈A,I p l) ∧ (¬∃ p, ∀ l∈B,I p l)
      let ok := fun C => (∀ p l, I p l → f C {p} {l}=true) ∧ (∀ A B, g A B → f C A B=false)
      let hard := fun (C : Circuit) =>
        let a := C.lineDeg 26 (Finset.range 13)
        let b := C.lineDeg 26 (Finset.Ico 13 26)
        2 ≤ min a b ∧ 3 ≤ max a b
      let rep := fun C => ∃ k ∈ ([8191,15860,31200,107904] : List Nat),
        circuitFun 26 C (fun i => k.testBit i.val)=true
      ∀ C, Monotone2 C → ok C → hard C →
        (∃ A B : S, (∀ a : V, a∈A → ∀ b : V, b∈B → ¬I a b) ∧ f C A B=true) →
        ∃ D, Monotone2 D ∧ D.size≤C.size ∧ ok D ∧ hard D ∧ rep D)
    (exceptionLower :
      let V := Fin 13
      let S := Finset V
      let I := fun (a b : V) => a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9
      let f := fun (C : Circuit) (A B : S) => circuitFun 26 C (fun i =>
        Fin.addCases (fun p => decide (p∈A)) (fun l => decide (l∈B)) i)
      let g := fun (A B : S) =>
        (∀ l, l∈B ↔ ∀ p∈A, ¬I p l) ∧ (∀ p∉A, ∃ l∈B,I p l) ∧
        (¬∃ l, ∀ p∈A,I p l) ∧ (¬∃ p, ∀ l∈B,I p l)
      let ok := fun C => (∀ p l, I p l → f C {p} {l}=true) ∧ (∀ A B, g A B → f C A B=false)
      let hard := fun (C : Circuit) =>
        let a := C.lineDeg 26 (Finset.range 13)
        let b := C.lineDeg 26 (Finset.Ico 13 26)
        2 ≤ min a b ∧ 3 ≤ max a b
      let rep := fun C => ∃ k ∈ ([8191,15860,31200,107904] : List Nat),
        circuitFun 26 C (fun i => k.testBit i.val)=true
      ∀ D, Monotone2 D → ok D → hard D → rep D → 64≤D.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false := by
  classical
  let I := fun (a b : Fin 13) => a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9
  let f := fun (C : Circuit) (A B : Finset (Fin 13)) => circuitFun 26 C (fun i =>
    Fin.addCases (fun p => decide (p∈A)) (fun l => decide (l∈B)) i)
  let g := fun (A B : Finset (Fin 13)) =>
    (∀ l, l∈B ↔ ∀ p∈A, ¬I p l) ∧ (∀ p∉A, ∃ l∈B,I p l) ∧
    (¬∃ l, ∀ p∈A,I p l) ∧ (¬∃ p, ∀ l∈B,I p l)
  let ok := fun C => (∀ p l, I p l → f C {p} {l}=true) ∧ (∀ A B, g A B → f C A B=false)
  let hit := fun (A B : Finset (Fin 13)) => ∃ a∈A, ∃ b∈B, I a b
  let low := fun C => HasLineDegree 26 (Finset.range 13) C 2 ∧ HasLineDegree 26 (Finset.Ico 13 26) C 2
  let hard := fun (C : Circuit) =>
    let a := C.lineDeg 26 (Finset.range 13)
    let b := C.lineDeg 26 (Finset.Ico 13 26)
    2 ≤ min a b ∧ 3 ≤ max a b
  let rep := fun C => ∃ k ∈ ([8191,15860,31200,107904] : List Nat),
    circuitFun 26 C (fun i => k.testBit i.val)=true
  dsimp only at sound exactLower normalize exceptionLower
  change ¬∃ C : Circuit, _
  rintro ⟨C,hf,sz,lg,pg,hpos,hneg⟩
  have hI (p l : Fin 13) : (∃ d∈({0,1,3,9} : Finset (Fin 13)), p=l+d) ↔ I p l := by simp [I]
  have cross (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro e
    have h := congrArg Fin.val e
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  have back (l p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := (cross p l).symm
  have ci (p q : Fin 13) : Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p=q := by simp [Fin.ext_iff]
  have ni (p q : Fin 13) : Fin.natAdd 13 p = Fin.natAdd 13 q ↔ p=q := by simp [Fin.ext_iff]
  have hp : ∀ p l, I p l → f C {p} {l}=true := by
    intro p l hi
    have h := hpos p l ((hI p l).mpr hi)
    convert h using 2
    funext i
    induction i using Fin.addCases (m := 13) (n := 13)
    · simp only [Fin.addCases_left,ci,ni,cross,back,hI] <;> simp
    · simp only [Fin.addCases_right,ci,ni,cross,back] <;> simp
  have hn : ∀ A B, g A B → f C A B=false := by
    intro A B h
    obtain ⟨hlines,hclosed,hcol,hpencil⟩ := h
    have h' := hneg A (by
      intro p hh
      obtain ⟨l,hl,he⟩ := hclosed p hh
      exact ⟨l, fun q hq hd => (hlines l).mp hl q hq ((hI q l).mp hd), (hI p l).mpr he⟩) (by
      constructor
      · rintro ⟨l,hh⟩
        exact hcol ⟨l,fun p hm => (hI p l).mp (hh p hm)⟩
      · rintro ⟨p,hh⟩
        exact hpencil ⟨p,fun l hl => (hI p l).mp (hh l (fun q hq hd => (hlines l).mp hl q hq ((hI q l).mp hd)))⟩)
    convert h' using 2
    funext i
    induction i using Fin.addCases (m := 13) (n := 13)
    · simp only [Fin.addCases_left,ci,ni,cross,back,hI] <;> simp
    · simp only [Fin.addCases_right,ci,ni,cross,back,hI,hlines] <;> simp
  have okay : ok C := ⟨hp,hn⟩
  by_cases correct : ∀ A B, f C A B=true → hit A B
  · have hh := exactLower C hf hp correct pg lg
    omega
  · have nlow : ¬low C := fun d => correct (sound C hf d hn)
    change ¬(_ ≤ 2 ∧ _ ≤ 2) at nlow
    change ¬C.lineDeg 26 (Finset.range 13) ≤ 1 at pg
    change ¬C.lineDeg 26 (Finset.Ico 13 26) ≤ 1 at lg
    have high : hard C := by dsimp [hard];omega
    push Not at correct
    obtain ⟨A,B,ha,hb⟩ := correct
    have bad : ∀ a∈A,∀ b∈B,¬I a b := fun a aA b bB h => hb ⟨a,aA,b,bB,h⟩
    obtain ⟨D,df,ds,go,hd,hr⟩ := normalize C hf okay high ⟨A,B,bad,ha⟩
    have hh := exceptionLower D df go hd hr
    omega
