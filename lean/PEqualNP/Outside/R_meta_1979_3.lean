import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A suffix sees the two OR-pairs and their union in each selected star.
Each of the nine stars has an independently chosen side, center, and pairing. -/
theorem PEqualNP.Outside.R_meta_1979_3
  (synthesis : let K := ({0,1,3,9} : Finset (Fin 13))
    let fits (G : Fin 9 → Bool × Fin 13 × Fin 3) (P L : Finset (Fin 13)) (z : List Bool) : Prop :=
      z.length = 70 ∧
      (∀ p : Fin 13, z.getD p.val false = decide (p∈P) ∧ z.getD (13+p.val) false = decide (p∈L)) ∧
      ∀ j : Fin 9, let c := (G j).2.1
                   let d : Fin 13 := if (G j).2.2=0 then 1 else if (G j).2.2=1 then 3 else 9
                   let hit (u : Fin 13) := if (G j).1 then c+u∈P else c-u∈L
                   let i := 26+(5*j.val-1)
                   z.getD i false = decide (hit 0 ∨ hit d) ∧
                   z.getD (i+1) false = decide (hit (3*d) ∨ hit (9*d)) ∧
                   z.getD (i+2) false = (z.getD i false || z.getD (i+1) false)
    ∃ (G : Fin 9 → Bool × Fin 13 × Fin 3) (S : Circuit), Monotone2 S ∧ S.size ≤ 18 ∧
      ∀ (P L : Finset (Fin 13)) (z : List Bool), fits G P L z →
        ((∃ p l, P={p} ∧ L={l} ∧ p-l ∈ K ∧ ¬(∃ j : Fin 9, if (G j).1 then (G j).2.1=l else (G j).2.1=p)) → S.eval z = true) ∧
        ((∀ p∈P, ∀ l∈L, p-l ∉ K) →
          (∀ l : Fin 13, (P.filter (fun p => p-l ∈ K)).card ≤ 2) →
          (∀ p : Fin 13, (L.filter (fun l => p-l ∈ K)).card ≤ 2) → S.eval z = false))
  (foundation : let K := ({0,1,3,9} : Finset (Fin 13))
    let fits (G : Fin 9 → Bool × Fin 13 × Fin 3) (P L : Finset (Fin 13)) (z : List Bool) : Prop :=
      z.length = 70 ∧
      (∀ p : Fin 13, z.getD p.val false = decide (p∈P) ∧ z.getD (13+p.val) false = decide (p∈L)) ∧
      ∀ j : Fin 9, let c := (G j).2.1
                   let d : Fin 13 := if (G j).2.2=0 then 1 else if (G j).2.2=1 then 3 else 9
                   let hit (u : Fin 13) := if (G j).1 then c+u∈P else c-u∈L
                   let i := 26+(5*j.val-1)
                   z.getD i false = decide (hit 0 ∨ hit d) ∧
                   z.getD (i+1) false = decide (hit (3*d) ∨ hit (9*d)) ∧
                   z.getD (i+2) false = (z.getD i false || z.getD (i+1) false)
    ∀ G : Fin 9 → Bool × Fin 13 × Fin 3, ∃ B : Circuit, Monotone2 B ∧ B.size=44 ∧ B.output<70 ∧
      ∀ P L : Finset (Fin 13), let x := List.ofFn (fun i : Fin 26 => decide ((∃ p∈P, i=Fin.castAdd 13 p) ∨ ∃ l∈L, i=Fin.natAdd 13 l))
                               fits G P L (B.wires x) ∧
                               B.eval x = decide (∃ p∈P, ∃ l∈L, p-l∈K ∧ (∃ j : Fin 9, if (G j).1 then (G j).2.1=l else (G j).2.1=p)))
  (splice : ∀ (B S : Circuit), Monotone2 B → B.size=44 → B.output<70 → Monotone2 S → S.size≤18 →
    ∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧ ∀ x : List Bool, x.length=26 →
      C.eval x = (B.eval x || S.eval (B.wires x))) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  let K : Finset (Fin 13) := {0,1,3,9}
  obtain ⟨G,S,hmS,hs,Sok⟩ := synthesis
  obtain ⟨B,hmB,hB,ho,Bok⟩ := foundation G
  obtain ⟨C,hmC,hc,eqC⟩ := splice B S hmB hB ho hmS hs
  refine ⟨C,hmC,hc,?_,?_⟩
  · intro p l hpl
    let v (i : Fin 26) := decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
    let x := List.ofFn v
    have hbare (i : Fin 26) :
        ((∃ a∈({p} : Finset (Fin 13)), i=Fin.castAdd 13 a) ∨
          ∃ b∈({l} : Finset (Fin 13)), i=Fin.natAdd 13 b) ↔
        (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l) := by simp
    obtain ⟨hbfit,hbeval⟩ := Bok {p} {l}
    simp only [hbare] at hbfit hbeval
    change C.eval x=true
    rw [eqC x (by simp [x])]
    rw [Bool.or_eq_true]
    by_cases hp : ¬(∃ j : Fin 9, if (G j).1 then (G j).2.1=l else (G j).2.1=p)
    · right
      exact (Sok {p} {l} (B.wires x) hbfit).1 ⟨p,l,rfl,rfl,hpl,hp⟩
    · left
      change B.eval x = _ at hbeval
      rw [hbeval]
      exact decide_eq_true ⟨p,by simp,l,by simp,hpl,Classical.not_not.mp hp⟩
  · intro P L hno hp hl
    let x := List.ofFn (fun i : Fin 26 => decide ((∃ p∈P, i=Fin.castAdd 13 p) ∨ ∃ l∈L, i=Fin.natAdd 13 l))
    obtain ⟨hf,he⟩ := Bok P L
    change C.eval x=false
    rw [eqC x (by simp [x])]
    have hz := (Sok P L (B.wires x) hf).2 hno hp hl
    have hc0 : ¬∃ p∈P, ∃ l∈L, p-l∈K ∧ (∃ j : Fin 9, if (G j).1 then (G j).2.1=l else (G j).2.1=p) := by
      rintro ⟨p,hp,l,hl,he,_⟩
      exact hno p hp l hl he
    change B.eval x = decide (∃ p∈P, ∃ l∈L, p-l∈K ∧ (∃ j : Fin 9, if (G j).1 then (G j).2.1=l else (G j).2.1=p)) at he
    simp [he,hc0,hz]
