import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.Transducer

/-!
# Transducers that write a bounded list of symbols per step

Helper module (proofs only, no statement may use it).

`flatMap h` over a finite alphabet is polynomial time for any `h` (the lengths of the lists
`h c` are bounded since the alphabet is finite): when every list has length at most `2 ^ K`,
replace each symbol by two tagged copies and halve the lists, `K` times, and end with a
transducer writing at most one symbol. A transducer that writes a list per step (`lrun`) is a
one-symbol transducer writing the pair (state, symbol read), followed by such a `flatMap`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines

theorem fm_stateless1 {A B : Type} (x : A → Option B) (l : List A) :
    fstRun (fun (_ : Unit) a => ((), x a)) (fun _ => none) () l =
      l.flatMap (fun a => (x a).toList) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ih]

theorem fm_stateless2 {A B : Type} (x y : A → B) (l : List A) :
    fstRun2 (fun (_ : Unit) a => ((), some (x a), some (y a))) (fun _ => none) () l =
      l.flatMap (fun a => [x a, y a]) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, ih]

theorem cpt_flatMap_pow {B : Type} : ∀ (K : ℕ) (C : Type) [Fintype C] (h : C → List B),
    (∀ c, (h c).length ≤ 2 ^ K) →
    ComputableInPolyTime (fun l : List C => l) (fun l : List B => l)
      (fun l : List C => l.flatMap h)
  | 0, C, _, h, hh => by
    refine fst_polyTime _ _ _ (fun (_ : Unit) c => ((), (h c).head?)) (fun _ => none) () ?_
    intro l
    rw [fm_stateless1]
    congr 1
    funext c
    have := hh c
    simp only [pow_zero] at this
    match e : h c, this with
    | [], _ => rfl
    | [a], _ => rfl
  | K + 1, C, _, h, hh => by
    let h2 : C × Bool → List B := fun p =>
      if p.2 then (h p.1).drop (2 ^ K) else (h p.1).take (2 ^ K)
    have hh2 : ∀ p, (h2 p).length ≤ 2 ^ K := by
      intro p
      have := hh p.1
      rw [pow_succ] at this
      by_cases hp : p.2 <;> simp [h2, hp] <;> omega
    have ih := cpt_flatMap_pow K (C × Bool) h2 hh2
    have hd : ComputableInPolyTime (fun l : List C => l) (fun l : List (C × Bool) => l)
        (fun l : List C => l.flatMap (fun c => [(c, false), (c, true)])) :=
      fst2_polyTime _ _ _ (fun (_ : Unit) c => ((), some (c, false), some (c, true)))
        (fun _ => none) () (fun l => (fm_stateless2 _ _ l).symm)
    have hc := cpt_comp hd ih
    have e : (fun l : List C => (l.flatMap (fun c => [(c, false), (c, true)])).flatMap h2) =
        (fun l : List C => l.flatMap h) := by
      funext l
      rw [List.flatMap_assoc]
      congr 1
      funext c
      simp [h2, List.take_append_drop]
    rw [e] at hc
    exact hc

/-- `flatMap` over a finite alphabet is polynomial time. -/
theorem cpt_flatMap {B C : Type} [Fintype C] (h : C → List B) :
    ComputableInPolyTime (fun l : List C => l) (fun l : List B => l)
      (fun l : List C => l.flatMap h) := by
  classical
  let M : ℕ := Finset.univ.sup (fun c => (h c).length)
  refine cpt_flatMap_pow M C h (fun c => ?_)
  have h1 : (h c).length ≤ M := Finset.le_sup (f := fun c => (h c).length) (Finset.mem_univ c)
  have h2 : M < 2 ^ M := Nat.lt_two_pow_self
  omega

/-- A transducer that writes a list per step and a list at the end. -/
def lrun {A B Q : Type} (δ : Q → A → Q × List B) (fin : Q → List B) : Q → List A → List B
  | q, [] => fin q
  | q, a :: l => (δ q a).2 ++ lrun δ fin (δ q a).1 l

theorem lrun_eq {A B Q : Type} (δ : Q → A → Q × List B) (fin : Q → List B) (q : Q)
    (l : List A) :
    lrun δ fin q l = (fstRun (fun q a => ((δ q a).1, some (Sum.inl (q, a))))
      (fun q => some (Sum.inr q)) q l).flatMap
        (fun c : (Q × A) ⊕ Q => Sum.elim (fun p => (δ p.1 p.2).2) fin c) := by
  induction l generalizing q with
  | nil => simp [lrun, fstRun]
  | cons a l ih => simp [lrun, fstRun, ih]

/-- A list-writing transducer is polynomial time. -/
theorem cpt_lrun {A B Q : Type} [Fintype A] [Fintype Q] (δ : Q → A → Q × List B)
    (fin : Q → List B) (q₀ : Q) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l) (lrun δ fin q₀) := by
  have h1 : ComputableInPolyTime (fun l : List A => l) (fun l : List ((Q × A) ⊕ Q) => l)
      (fstRun (fun q a => ((δ q a).1, some (Sum.inl (q, a)))) (fun q => some (Sum.inr q)) q₀) :=
    fst_polyTime _ _ _ _ _ q₀ (fun _ => rfl)
  have h := cpt_comp h1 (cpt_flatMap (fun c : (Q × A) ⊕ Q => Sum.elim (fun p => (δ p.1 p.2).2) fin c))
  have e : (fun l : List A => (fstRun (fun q a => ((δ q a).1, some (Sum.inl (q, a))))
      (fun q => some (Sum.inr q)) q₀ l).flatMap
        (fun c : (Q × A) ⊕ Q => Sum.elim (fun p => (δ p.1 p.2).2) fin c)) = lrun δ fin q₀ := by
    funext l; rw [lrun_eq]
  rw [e] at h
  exact h

end PEqualNP.MetaComplexity.Helpers.MachinePrint
