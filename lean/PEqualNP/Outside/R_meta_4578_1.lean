import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_4578_1
    (encode : ∀ C : Circuit, Monotone2 C → C.size < 64 →
      ∃ (s : Fin 64) (out : Fin 90) (kind : Fin s.val → Bool)
        (a b : Fin s.val → Option (Fin 90)),
        let D : Circuit := ⟨List.ofFn (fun i =>
          ⟨if kind i then .and else .or, [a i, b i].filterMap (Option.map Fin.val)⟩), out.val⟩
        circuitFun 26 D = circuitFun 26 C ∧ ∀ M, D.lineDeg 26 M = C.lineDeg 26 M)
    (separate : ∀ (s : Fin 64) (out : Fin 90) (kind : Fin s.val → Bool)
        (a b : Fin s.val → Option (Fin 90)),
        let D : Circuit := ⟨List.ofFn (fun i =>
          ⟨if kind i then .and else .or, [a i, b i].filterMap (Option.map Fin.val)⟩), out.val⟩
        (∀ p l, p ∈ singerLines3 l → D.eval (incidenceInput {p} {l}) = true) →
        (∀ X, IsMaximalFalse singerLines3 X (missLines singerLines3 X) →
          D.eval (incidenceInput X (missLines singerLines3 X)) = false) →
        HasLineDegree 26 (Finset.range 13) D 1 ∨ HasLineDegree 26 (Finset.Ico 13 26) D 1) :
    let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let value := fun (C : Circuit) (X Y : Finset (Fin 13)) => circuitFun 26 C
      (fun i => Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y)) i)
    let edge := fun X Y : Finset (Fin 13) => ∃ p ∈ X, ∃ l ∈ Y, I p l
    ∀ C : Circuit, Monotone2 C →
      (∀ p l, I p l → value C {p} {l} = true) →
      (∀ X Y, value C X Y = true → edge X Y) →
      ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64 ≤ C.size := by
  intro I value edge C mono positives sound pointDegree lineDegree
  by_contra! small
  obtain ⟨s, out, kind, a, b, same, degrees⟩ := encode C mono small
  let D : Circuit := ⟨List.ofFn (fun i =>
    ⟨if kind i then .and else .or, [a i, b i].filterMap (Option.map Fin.val)⟩), out.val⟩
  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ I p l := by decide
  have testEq (X Y : Finset (Fin 13)) : D.eval (incidenceInput X Y) = value C X Y := by
    let z : Fin 26 → Bool :=
      fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ X)) (fun l : Fin 13 => decide (l ∈ Y)) i
    have h : List.ofFn z = incidenceInput X Y := by
      change List.ofFn z = List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ Y))
      rw [List.ofFn_add (n := 13) (m := 13)]
      simp [z, Fin.addCases]
    calc
      D.eval (incidenceInput X Y) = circuitFun 26 D z := by
        change D.eval _ = D.eval (List.ofFn z)
        rw [h]
      _ = value C X Y := congrFun same z
  have accept (p l : Fin 13) (hp : p ∈ singerLines3 l) :=
    (testEq {p} {l}).trans (positives p l ((incidence p l).mp hp))
  have reject (X : Finset (Fin 13)) : D.eval (incidenceInput X (missLines singerLines3 X)) = false := by
    rw [testEq]
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨p, hp, l, hl, incident⟩ := sound _ _ yes
    have disjoint : Disjoint (singerLines3 l) X := (Finset.mem_filter.mp hl).2
    exact Finset.disjoint_left.mp disjoint ((incidence p l).mpr incident) hp
  rcases separate s out kind a b accept (fun X _ => reject X) with h | h
  · apply pointDegree
    unfold HasLineDegree at *
    rwa [degrees] at h
  · apply lineDegree
    unfold HasLineDegree at *
    rwa [degrees] at h
