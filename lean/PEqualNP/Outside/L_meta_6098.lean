import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6098

open PEqualNP.CircuitLowerBounds

lemma wires_tail (gates : List Gate) (xs : List Bool) :
    ∃ tail : List Bool, (Circuit.wires ⟨gates, 0⟩ xs) = xs ++ tail ∧
      tail.length = gates.length := by
  induction gates generalizing xs with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => xs.getD i false)
    obtain ⟨ys, hy, hlen⟩ := ih (xs ++ [b])
    change gs.foldl (fun zs h => zs ++ [h.op.eval (h.inputs.map fun i => zs.getD i false)])
      (xs ++ [b]) = _ at hy
    refine ⟨b :: ys, ?_, by simp [hlen]⟩
    simp only [Circuit.wires, List.foldl_cons, ← List.cons_append, List.nil_append]
    simpa only [List.append_assoc, List.singleton_append] using hy

def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wire C x i.val = x i := by
  obtain ⟨ys, hy, _⟩ := wires_tail C.gates (List.ofFn x)
  change C.wires (List.ofFn x) = _ at hy
  unfold wire
  rw [hy, List.getD_append _ _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]

lemma wire_outside {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.size ≤ i) : wire C x i = false := by
  obtain ⟨ys, hy, hlen⟩ := wires_tail C.gates (List.ofFn x)
  change C.wires (List.ofFn x) = _ at hy
  unfold wire
  rw [hy]
  apply List.getD_eq_default
  simpa [hlen, Circuit.size] using hi

def singleton (i : Fin 10) (j : Fin 10) : Bool := decide (j = i)

lemma singleton_false : ∀ i : Fin 10,
    (List.finRange 5).any (fun j =>
      singleton i (Fin.castAdd 5 j) && singleton i (Fin.castAdd 5 (j + 1)) ||
      singleton i (Fin.castAdd 5 j) && singleton i (Fin.natAdd 5 j) ||
      singleton i (Fin.natAdd 5 j) && singleton i (Fin.natAdd 5 (j + 2))) = false := by
  decide

lemma no_bad_wire (C : Circuit) (f : (Fin 10 → Bool) → Bool) (a b : ℕ)
    (hs : ∀ i, f (singleton i) = false)
    (ha : 10 ≤ a ∧ a < 10 + C.size ∨ a < 10 ∨ 10 + C.size ≤ a)
    (htrue : ∃ x : Fin 10 → Bool, wire C x a = true)
    (hmatch : ∀ x, f x = false → (wire C x a || wire C x b) = f x) :
    10 ≤ a ∧ a < 10 + C.size := by
  rcases ha with good | small | large
  · exact good
  · let i : Fin 10 := ⟨a, small⟩
    have hw : wire C (singleton i) a = true := by
      simpa [i, singleton] using wire_input C (singleton i) i
    have h := hmatch (singleton i) (hs i)
    simp [hw, hs i] at h
  · obtain ⟨x, hx⟩ := htrue
    rw [wire_outside C x a large] at hx
    contradiction

end PEqualNP.Outside.L_meta_6098

open PEqualNP.Outside.L_meta_6098 in
theorem PEqualNP.Outside.L_meta_6098 :
have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       x3 < (10 : ℕ) ∨ (10 : ℕ) + x2.size ≤ x3 ∨ x4 < (10 : ℕ) ∨ (10 : ℕ) + x2.size ≤ x4 →         have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8)).getD x9 Bool.false;         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x8 x9 x3 || x8 x9 x4;         (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.true ∧ x8 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x8 x11 x3 = Bool.false ∧ x8 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x1 x12 = Bool.false ∨ List.count Bool.true (List.ofFn x12) ≤ (2 : ℕ) → x9 x12 = x1 x12) → ∃ (x13 : Equiv.Perm (Fin (10 : ℕ))) (x14 : Bool) (x15 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x16 : Fin (10 : ℕ) → Bool), x1 (x16 ∘ ⇑x13) = x1 x16) ∧ PEqualNP.MetaComplexity.FanInTwo x15 ∧ (x15.size ≤ if x14 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x16 : Fin (9 : ℕ) → Bool), x15.eval (List.ofFn x16) = x9 ((fun (x17 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x14 x16 x17) ∘ ⇑x13) := by
  intro f C a b _ _ bad _ _ wA wB hmatch
  exfalso
  have hs : ∀ i, f (singleton i) = false := singleton_false
  have step (x : Fin 10 → Bool) (h : f x = false) : (wire C x a || wire C x b) = f x :=
    hmatch x (Or.inl h)
  have ha := no_bad_wire C f a b hs (by omega) (wA.imp fun _ h => h.1) step
  have hb := no_bad_wire C f b a hs (by omega) (wB.imp fun _ h => h.2)
    (fun x h => by rw [Bool.or_comm]; exact step x h)
  omega
