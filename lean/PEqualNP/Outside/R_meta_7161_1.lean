import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7161_1
    (core :
      let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
      let bits := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∃ B : Circuit, Monotone2 B ∧ B.size ≤ 43 ∧ B.output < 21 + B.size ∧
        ∀ s t : Finset (Fin 13), B.eval (ix.map (bits s t)) = true ↔
          ∃ p ∈ s, p.val ∉ ([0, 1, 3, 9] : List ℕ) ∧ ∃ l ∈ t, near p l)
    (extend :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ B : Circuit, Monotone2 B → B.size ≤ 43 → B.output < 21 + B.size →
        ∃ E : Circuit, Monotone2 E ∧ E.size ≤ B.size + 19 ∧
          ∃ a b : ℕ, a < b ∧
            ∀ x : Fin 26 → Bool,
              ((E.wires (List.ofFn x)).getD a false || (E.wires (List.ofFn x)).getD b false) =
                (B.eval (ix.map x) || decide (∃ p ∈ D, ∃ l : Fin 13, near p l ∧
                  x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)))
    :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
      (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
    have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) :=
      fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}
    have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool :=
      fun (x3 x4 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x5 : Fin (26 : ℕ)) =>
        if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3)
        else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4)
    ∃ (x4 : Circuit) (x5 : ℕ) (x6 : ℕ) (x7 : Bool),
      Monotone2 x4 ∧ x4.size ≤ (62 : ℕ) ∧ x5 < x6 ∧
        have x8 : ℕ → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool :=
          fun (x8 : ℕ) (x9 x10 : Finset (Fin (13 : ℕ))) => (x4.wires (x3 x9 x10)).getD x8 Bool.false
        have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool :=
          fun (x9 x10 : Finset (Fin (13 : ℕ))) =>
            (if x7 = Bool.true then GateOp.and else GateOp.or).eval [x8 x5 x9 x10, x8 x6 x9 x10]
        (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 {x10} {x11} = Bool.true) ∧
          ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) →
            x9 x10 (x2 x10) = Bool.false ∧ x9 (x2 x10) x10 = Bool.false) := by
  classical
  obtain ⟨B, hBmono, hBsize, hBoutput, hCore⟩ := core
  obtain ⟨E, hEmono, hEsize, a, b, hab, hExtend⟩ := extend B hBmono hBsize hBoutput
  have hSize : E.size ≤ 62 := by omega
  let relation : Fin 13 → Fin 13 → Prop := fun p l => (p.val + l.val) % 13 ∈ [0, 1, 3, 9]
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ relation p l
  let bit := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let vec := fun (s t : Finset (Fin 13)) => List.ofFn (bit s t)
  have bitLeft (s t : Finset (Fin 13)) (p : Fin 13) :
      bit s t (Fin.castAdd 13 p) = decide (p ∈ s) := by
    simp [bit]
  have bitRight (s t : Finset (Fin 13)) (l : Fin 13) :
      bit s t (Fin.natAdd 13 l) = decide (l ∈ t) := by
    fin_cases l <;> simp [bit]
  let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
  let special := fun (x : Fin 26 → Bool) =>
    decide (∃ p ∈ ({0, 1, 3, 9} : Finset (Fin 13)), ∃ l : Fin 13,
      relation p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  let read := fun s t => GateOp.or.eval
    [(E.wires (vec s t)).getD a false, (E.wires (vec s t)).getD b false]
  have hOrEval (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
    change List.any [u, v] id = (u || v)
    simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq]
  have hRead (s t : Finset (Fin 13)) :
      read s t = (B.eval (ix.map (bit s t)) || special (bit s t)) := by
    dsimp [read, vec]
    rw [hOrEval]
    simpa [special, relation, ix] using hExtend (bit s t)
  have hCoreFalse (s t : Finset (Fin 13))
      (hno : ∀ p ∈ s, ∀ l ∈ t, ¬ relation p l) :
      B.eval (ix.map (bit s t)) = false := by
    cases h : B.eval (ix.map (bit s t)) with
    | false => rfl
    | true =>
      obtain ⟨p, hp, _, l, hl, hpl⟩ := (hCore s t).mp h
      exact (hno p hp l hl hpl).elim
  have hSpecialFalse (s t : Finset (Fin 13))
      (hno : ∀ p ∈ s, ∀ l ∈ t, ¬ relation p l) : special (bit s t) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p, hp, l, hpl, hpv, hlv⟩ := of_decide_eq_true h
    have hp' : p ∈ s := by rw [bitLeft] at hpv; exact of_decide_eq_true hpv
    have hl' : l ∈ t := by rw [bitRight] at hlv; exact of_decide_eq_true hlv
    exact hno p hp' l hl' hpl
  have hSymm (p l : Fin 13) : relation p l ↔ relation l p := by
    simp [relation, Nat.add_comm]
  refine ⟨E, a, b, false, hEmono, hSize, hab, ?_⟩
  change (∀ p l : Fin 13, relation p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 →
      read s (off s) = false ∧ read (off s) s = false)
  constructor
  · intro p l hpl
    rw [hRead]
    by_cases hs : p.val ∈ ([0, 1, 3, 9] : List ℕ)
    · have hp : p ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
        have hs' : p.val = 0 ∨ p.val = 1 ∨ p.val = 3 ∨ p.val = 9 := by simpa using hs
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hs' with h | h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
      have hhit : special (bit {p} {l}) = true := by
        apply decide_eq_true
        exact ⟨p, hp, l, hpl, by rw [bitLeft]; simp, by rw [bitRight]; simp⟩
      simp [hhit]
    · have hcore : B.eval (ix.map (bit {p} {l})) = true := by
        apply (hCore {p} {l}).2
        exact ⟨p, by simp, hs, l, by simp, hpl⟩
      simp [hcore]
  · intro s _
    have hright (p : Fin 13) (hp : p ∈ s) (l : Fin 13) (hl : l ∈ off s) :
        ¬ relation p l := (Finset.mem_filter.mp hl).2 p hp
    have hleft (p : Fin 13) (hp : p ∈ off s) (l : Fin 13) (hl : l ∈ s) :
        ¬ relation p l := by
      intro hpl
      exact (Finset.mem_filter.mp hp).2 l hl ((hSymm p l).1 hpl)
    constructor
    · rw [hRead, hCoreFalse s (off s) (fun p hp l hl => hright p hp l hl),
        hSpecialFalse s (off s) (fun p hp l hl => hright p hp l hl)]
      simp
    · rw [hRead, hCoreFalse (off s) s (fun p hp l hl => hleft p hp l hl),
        hSpecialFalse (off s) s (fun p hp l hl => hleft p hp l hl)]
      simp