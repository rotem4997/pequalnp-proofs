import Mathlib
import PEqualNP.Defs

-- Cofactor identity for a list of pairs with distinct components: setting the
-- value at v (where x is false) to b adds exactly the pairs through v, gated by b.
namespace PEqualNP.Outside.L_meta_3949

-- One pair with distinct components.
theorem pair_step {A : Type} [DecidableEq A] (v p q : A) (hpq : p ≠ q) (x : A → Bool)
    (hxv : x v = false) (b : Bool) :
    (Function.update x v b p && Function.update x v b q)
      = ((x p && x q) || (b && ((decide (p = v) && x q) || (decide (q = v) && x p)))) := by
  by_cases hp : p = v
  · subst hp
    have hq : q ≠ p := fun h => hpq h.symm
    rw [Function.update_self, Function.update_of_ne hq]
    simp [hxv, hq]
  · by_cases hq : q = v
    · subst hq
      rw [Function.update_self, Function.update_of_ne hp]
      simp [hxv, hp, Bool.and_comm]
    · rw [Function.update_of_ne hp, Function.update_of_ne hq]
      simp [hp, hq]

end PEqualNP.Outside.L_meta_3949

theorem PEqualNP.Outside.L_meta_3949 : ∀ (x1 : Type) [x2 : DecidableEq x1] (x3 : List (x1 × x1)) (x4 : x1), (∀ x5 ∈ x3, x5.1 ≠ x5.2) → ∀ (x6 : x1 → Bool), x6 x4 = Bool.false → ∀ (x8 : Bool), (x3.any fun (x9 : x1 × x1) => Function.update x6 x4 x8 x9.1 && Function.update x6 x4 x8 x9.2) = ((x3.any fun (x9 : x1 × x1) => x6 x9.1 && x6 x9.2) || x8 && x3.any fun (x9 : x1 × x1) => Decidable.decide (x9.1 = x4) && x6 x9.2 || Decidable.decide (x9.2 = x4) && x6 x9.1) := by
  intro A instA E v hE x hxv b
  induction E with
  | nil => simp
  | cons e E ih =>
    have hne : e.1 ≠ e.2 := hE e List.mem_cons_self
    have ih' := ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))
    simp only [List.any_cons]
    rw [ih', PEqualNP.Outside.L_meta_3949.pair_step v e.1 e.2 hne x hxv b]
    generalize (E.any fun e => x e.1 && x e.2) = r1
    generalize (E.any fun e => (decide (e.1 = v) && x e.2) || (decide (e.2 = v) && x e.1)) = r2
    generalize (x e.1 && x e.2) = s1
    generalize ((decide (e.1 = v) && x e.2) || (decide (e.2 = v) && x e.1)) = s2
    cases b <;> cases r1 <;> cases r2 <;> cases s1 <;> cases s2 <;> rfl
