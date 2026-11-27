import Mathlib
import PEqualNP.Defs

open PEqualNP.AndCount

-- A disjunction of the four points on line zero is true at every test input.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4684_219
    (replace : ∀ (C : AndCountCircuit 27) (S : Finset (Fin 26)), C.WellFormed →
      ∃ D : AndCountCircuit 26, D.WellFormed ∧ D.size = C.size ∧
        ∀ U : Finset (Fin 26), (∃ s ∈ S, s ∈ U) →
          D.eval U = C.eval (insert 0 (U.image Fin.succ)))
    (lower : ∀ (D : AndCountCircuit 26), D.WellFormed →
      let inc : Fin 13 → Fin 13 → Prop := fun p l =>
        p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let input : Finset (Fin 13) → Finset (Fin 13) → Finset (Fin 26) :=
        fun X Y => {v | ¬ ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
          ∃ l ∈ Y, v = Fin.natAdd 13 l)}
      let opposite : Finset (Fin 13) → Finset (Fin 13) :=
        fun X => {l | ∀ p ∈ X, ¬ inc p l}
      (∀ p l, inc p l → D.eval (input {p} {l}) = false) →
      (∀ X : Finset (Fin 13), (∀ p ∉ X, ∃ l ∈ opposite X, inc p l) →
        (¬ ∃ l, ∀ p ∈ X, inc p l) →
        (¬ ∃ p, ∀ l ∈ opposite X, inc p l) →
        D.eval (input X (opposite X)) = true) →
      51 ≤ D.size) :
    ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x4, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ x7 ∈ x5, x6 = Fin.natAdd (13 : ℕ) x7);     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x5 x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x8 : Fin (26 : ℕ)) => !x4 x5 x6 x8) x7 = Bool.true};     have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x3 x8 x7};     (∀ (x7 x8 : Fin (13 : ℕ)), x3 x7 x8 → x1.eval (x5 {x7} {x8}) = Bool.false) → (∀ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ x11 ∈ x6 x8, x3 x9 x11) → (¬∃ (x10 : Fin (13 : ℕ)), ∀ x11 ∈ x8, x3 x11 x10) → (¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x6 x8, x3 x11 x12) → x1.eval (x5 x8 (x6 x8)) = Bool.true) → (51 : ℕ) ≤ x1.size := by
  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let input (X Y : Finset (Fin 13)) : Finset (Fin 26) :=
    {v | ¬ ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, v = Fin.natAdd 13 l)}
  let opposite (X : Finset (Fin 13)) : Finset (Fin 13) := {l | ∀ p ∈ X, ¬ inc p l}
  let line : Finset (Fin 13) := {0, 1, 3, 9}
  have intersect : ∀ l : Fin 13, ∃ p : Fin 13, p ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) := by decide
  have miss (X Y : Finset (Fin 13)) (p : Fin 13) (hp : p ∉ X) :
      Fin.castAdd 13 p ∈ input X Y := by
    change Fin.castAdd 13 p ∈ Finset.filter _ Finset.univ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (⟨q, hq, he⟩ | ⟨l, _, he⟩)
    · apply hp
      have same : p = q := Fin.ext (congrArg (fun z : Fin 26 => z.val) he)
      exact same ▸ hq
    · have h := congrArg Fin.val he
      change p.val = 13 + l.val at h
      omega
  intro C wf
  dsimp only
  intro negatives positives
  obtain ⟨D, dwf, hsize, heval⟩ := replace C (line.image (Fin.castAdd 13)) wf
  have agreement (X Y : Finset (Fin 13)) (p : Fin 13) (hline : p ∈ line) (hp : p ∉ X) :
      D.eval (input X Y) =
        C.eval {v : Fin 27 | Fin.cases true (fun w : Fin 26 =>
          !decide ((∃ a ∈ X, w = Fin.castAdd 13 a) ∨
            ∃ l ∈ Y, w = Fin.natAdd 13 l)) v = true} := by
    rw [heval _ ⟨Fin.castAdd 13 p, Finset.mem_image_of_mem _ hline, miss X Y p hp⟩]
    congr 1
    ext v
    refine Fin.cases ?_ (fun w => ?_) v
    · simp
    · simp [input, Fin.succ_ne_zero]
  have bound := lower D dwf
  dsimp only at bound
  rw [← hsize]
  apply bound
  · intro p l h
    have missing : ∃ q ∈ line, q ∉ ({p} : Finset (Fin 13)) := by
      by_cases e : p = 0
      · exact ⟨1, by decide, by simp [e]⟩
      · exact ⟨0, by decide, by simpa [eq_comm] using e⟩
    obtain ⟨q, hq, hn⟩ := missing
    exact (agreement {p} {l} q hq hn).trans (negatives p l h)
  · intro X closed nongeneric₁ nongeneric₂
    obtain ⟨l, hl⟩ : ∃ l, l ∈ opposite X := by
      by_contra! none
      apply nongeneric₂
      exact ⟨0, fun l hl => (none l hl).elim⟩
    obtain ⟨p, hp, hinc⟩ := intersect l
    have hn : p ∉ X := by
      intro hm
      exact (Finset.mem_filter.mp hl).2 p hm hinc
    exact (agreement X (opposite X) p hp hn).trans
      (positives X closed nongeneric₁ nongeneric₂)
