import Mathlib
import PEqualNP.Defs

/-!
# Sanity lemmas for the encoding of last-gate instances

About `PEqualNP.Defs.MetaComplexityLgp`: the encoding `encodeLgp` is injective and at least as
long as the number of inputs plus the number of gates; the two sides of the promise are
disjoint and both inhabited; a test as in `LgpInP` decides minimality on near-minimal circuits.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds


namespace LgpEncode

/-- `e` is uniquely decodable from the front of a string. -/
def PF {α : Type} (e : α → List Bool) : Prop :=
  ∀ a b s t, e a ++ s = e b ++ t → a = b ∧ s = t

theorem bits_pf (l₁ l₂ : List Bool) (s t : List Bool)
    (h : (l₁.flatMap (fun b => [true, b]) ++ [false]) ++ s =
      (l₂.flatMap (fun b => [true, b]) ++ [false]) ++ t) : l₁ = l₂ ∧ s = t := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simpa using h
    | cons b l => simp at h
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hab, h⟩ := h
      obtain ⟨hl, hst⟩ := ih l' (by simpa using h)
      exact ⟨by rw [hab, hl], hst⟩

theorem foldr_bits (n : ℕ) : (Nat.bits n).foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]

theorem encodeNat_pf : PF encodeNat := by
  intro a b s t h
  obtain ⟨hb, hst⟩ := bits_pf _ _ s t h
  exact ⟨(Function.LeftInverse.injective foldr_bits) hb, hst⟩

theorem encodeList_pf {α : Type} (e : α → List Bool) (he : PF e) : PF (encodeList e) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ s t h
    cases l₂ with
    | nil => simpa [encodeList] using h
    | cons b l => simp [encodeList] at h
  | cons a l ih =>
    intro l₂ s t h
    cases l₂ with
    | nil => simp [encodeList] at h
    | cons b l' =>
      simp only [encodeList, List.flatMap_cons, List.cons_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      obtain ⟨hab, h⟩ := he a b _ _ h
      obtain ⟨hl, hst⟩ := ih l' s t (by simpa [encodeList] using h)
      exact ⟨by rw [hab, hl], hst⟩

theorem encodeGateOp_pf : PF encodeGateOp := by
  intro a b s t h
  cases a <;> cases b <;> simp [encodeGateOp] at h ⊢ <;> try exact h
  all_goals exact encodeNat_pf _ _ _ _ h

/-- The code of a gate operation is injective (MOD and MAJORITY included). -/
theorem encodeGateOp_injective : Function.Injective encodeGateOp := fun a b h =>
  (encodeGateOp_pf a b [] [] (by simpa using h)).1

theorem encodeGate_pf : PF encodeGate := by
  rintro ⟨o₁, i₁⟩ ⟨o₂, i₂⟩ s t h
  simp only [encodeGate, List.append_assoc] at h
  obtain ⟨ho, h⟩ := encodeGateOp_pf _ _ _ _ h
  obtain ⟨hi, hst⟩ := encodeList_pf encodeNat encodeNat_pf _ _ _ _ h
  exact ⟨by rw [ho, hi], hst⟩

theorem unary_pf (n m : ℕ) (s t : List Bool)
    (h : List.replicate n true ++ false :: s = List.replicate m true ++ false :: t) :
    n = m ∧ s = t := by
  induction n generalizing m with
  | zero => cases m <;> simp_all [List.replicate_succ]
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih m h
      exact ⟨by rw [h1], h2⟩

/-- (a) The code of an instance determines the instance. -/
theorem encodeLgp_injective : Function.Injective encodeLgp := by
  rintro ⟨n₁, ⟨g₁, o₁⟩⟩ ⟨n₂, ⟨g₂, o₂⟩⟩ h
  obtain ⟨hn, h⟩ := unary_pf _ _ _ _ h
  obtain ⟨hg, h⟩ := encodeList_pf encodeGate encodeGate_pf _ _ _ _ h
  obtain ⟨ho, _⟩ := encodeNat_pf o₁ o₂ [] [] (by simpa using h)
  simp only at hn hg ho
  rw [hn, hg, ho]

theorem encodeList_length_ge {α : Type} (e : α → List Bool) (l : List α) :
    l.length ≤ (encodeList e l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [encodeList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-- (b) The code of `(n, C)` has length at least `n` plus the number of gates of `C`. -/
theorem encodeLgp_length_ge (n : ℕ) (C : Circuit) : n + C.size ≤ (encodeLgp (n, C)).length := by
  have := encodeList_length_ge encodeGate C.gates
  simp only [encodeLgp, Circuit.size, List.length_append, List.length_replicate,
    List.length_cons] at this ⊢
  omega

/-- (c) The two sides of the promise are disjoint. -/
theorem lgpYes_lgpNo_disjoint (n : ℕ) (C : Circuit) : ¬ (LgpYes n C ∧ LgpNo n C) :=
  fun ⟨hy, hn⟩ => hn.2 hy

/-- A yes instance: the empty circuit on no inputs. -/
theorem lgpYes_empty : LgpYes 0 ⟨[], 0⟩ :=
  ⟨fun g hg => by simp at hg, fun D _ _ => by simp [Circuit.size]⟩

/-- A no instance: one OR gate reading nothing (constant `false`) on no inputs; the empty
circuit computes the same function. -/
theorem lgpNo_or : LgpNo 0 ⟨[⟨GateOp.or, []⟩], 0⟩ := by
  refine ⟨⟨fun g hg => ?_, fun D _ _ => by simp [Circuit.size]⟩, fun h => ?_⟩
  · simp only [List.mem_singleton] at hg
    subst hg
    simp
  · have hf : circuitFun 0 ⟨[], 0⟩ = circuitFun 0 ⟨[⟨GateOp.or, []⟩], 0⟩ := by
      funext x
      simp [circuitFun, Circuit.eval, Circuit.wires, GateOp.eval]
    have := h.2 ⟨[], 0⟩ (fun g hg => by simp at hg) hf
    simp [Circuit.size] at this

/-- (d) Not vacuous: any test meeting the two clauses of `LgpInP` is non-constant, so neither
constant function is a witness. -/
theorem lgp_test_nonconstant (f : ℕ × Circuit → Bool)
    (hf : ∀ p : ℕ × Circuit, (LgpYes p.1 p.2 → f p = true) ∧ (LgpNo p.1 p.2 → f p = false)) :
    f (0, ⟨[], 0⟩) = true ∧ f (0, ⟨[⟨GateOp.or, []⟩], 0⟩) = false :=
  ⟨(hf (0, ⟨[], 0⟩)).1 lgpYes_empty, (hf (0, ⟨[⟨GateOp.or, []⟩], 0⟩)).2 lgpNo_or⟩

/-- (d) From `LgpInP`: a polynomial-time test that, on every near-minimal instance, answers
`true` exactly when the circuit is minimal. -/
theorem LgpInP.decides_on_promise (h : LgpInP) :
    ∃ f : ℕ × Circuit → Bool,
      PEqualNP.Library.ComputableInPolyTime encodeLgp Computability.encodeBool f ∧
        ∀ p : ℕ × Circuit, NearMinimal p.1 p.2 → (f p = true ↔ IsMinimalCircuit p.1 p.2) := by
  obtain ⟨f, hc, hf⟩ := h
  refine ⟨f, hc, fun p hp => ?_⟩
  by_cases hm : IsMinimalCircuit p.1 p.2
  · exact ⟨fun _ => hm, fun _ => (hf p).1 hm⟩
  · have : f p = false := (hf p).2 ⟨hp, hm⟩
    simp [this, hm]

end LgpEncode

end PEqualNP.MetaComplexity
