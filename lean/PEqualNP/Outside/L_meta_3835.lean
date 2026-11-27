import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3835_aux

open PEqualNP.CircuitLowerBounds

def P (x1 : ℕ) (v : List Bool → Bool) : Prop :=
  (∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool), ∀ (x8 : List Bool), x8.length = x1 →
    v x8 = (x7 != x8.getD (↑x6) Bool.false)) ∨
  ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧ ∀ (x9 : List Bool), x9.length = x1 →
    v x9 = (if x8 = Bool.true then x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false
      else x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false)

theorem getD_ge (x : List Bool) (a : ℕ) (h : x.length ≤ a) : x[a]?.getD false = false := by
  simp [List.getElem?_eq_none h]

theorem P_congr (x1 : ℕ) (v w : List Bool → Bool)
    (h : ∀ x : List Bool, x.length = x1 → v x = w x) (hw : P x1 w) : P x1 v := by
  rcases hw with ⟨i, b, hb⟩ | ⟨i, j, o, hij, ho⟩
  · exact Or.inl ⟨i, b, fun x hx => by rw [h x hx, hb x hx]⟩
  · exact Or.inr ⟨i, j, o, hij, fun x hx => by rw [h x hx, ho x hx]⟩

theorem pconst (x1 : ℕ) (c : Bool) : P x1 (fun _ => c) := by
  refine Or.inl ⟨⟨x1, by omega⟩, c, fun x hx => ?_⟩
  simp [getD_ge x x1 (by omega)]

theorem psingle (x1 : ℕ) (a : ℕ) (n : Bool) : P x1 (fun x => (n != x.getD a false)) := by
  by_cases h : a < x1
  · exact Or.inl ⟨⟨a, by omega⟩, n, fun x _ => rfl⟩
  · refine Or.inl ⟨⟨x1, by omega⟩, n, fun x hx => ?_⟩
    simp [getD_ge x x1 (by omega), getD_ge x a (by omega)]

theorem ptwo (x1 : ℕ) (a b : ℕ) (o : Bool) :
    P x1 (fun x => if o = true then x.getD a false || x.getD b false
      else x.getD a false && x.getD b false) := by
  by_cases ha : a < x1
  · by_cases hb : b < x1
    · rcases lt_trichotomy a b with hab | hab | hab
      · exact Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, o, hab, fun x _ => rfl⟩
      · subst hab
        refine P_congr x1 _ _ (fun x _ => ?_) (psingle x1 a false)
        cases o <;> simp
      · refine Or.inr ⟨⟨b, hb⟩, ⟨a, ha⟩, o, hab, fun x _ => ?_⟩
        cases o <;> simp [Bool.or_comm, Bool.and_comm]
    · cases o
      · refine P_congr x1 _ _ (fun x hx => ?_) (pconst x1 false)
        simp [getD_ge x b (by omega)]
      · refine P_congr x1 _ _ (fun x hx => ?_) (psingle x1 a false)
        simp [getD_ge x b (by omega)]
  · cases o
    · refine P_congr x1 _ _ (fun x hx => ?_) (pconst x1 false)
      simp [getD_ge x a (by omega)]
    · refine P_congr x1 _ _ (fun x hx => ?_) (psingle x1 b false)
      simp [getD_ge x a (by omega)]

theorem pgate (x1 : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    P x1 (fun x => g.op.eval (g.inputs.map fun i => x.getD i false)) := by
  obtain ⟨op, inputs⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (pconst x1 true)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (pconst x1 false)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (pconst x1 true)
  · rcases hop with rfl | rfl | rfl
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (psingle x1 a false)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (psingle x1 a false)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (psingle x1 a true)
  · rcases hop with rfl | rfl | rfl
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (ptwo x1 a b false)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (ptwo x1 a b true)
    · exact P_congr x1 _ _ (fun x _ => by simp [GateOp.eval]) (psingle x1 a true)
  · simp at hlen

end PEqualNP.Outside.L_meta_3835_aux

theorem PEqualNP.Outside.L_meta_3835 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) = x2.size ∧ ((∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool), ∀ (x8 : List Bool), x8.length = x1 → x2.eval x8 = x5.eval (x8 ++ [x7 != x8.getD (↑x6) Bool.false])) ∨ ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = x5.eval (x9 ++ [if x8 = Bool.true then x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false else x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false])) := by
  intro x1 x2 hF hs
  obtain ⟨gates, out⟩ := x2
  rcases gates with _ | ⟨g, rest⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hs
  · have hg := hF g (by simp)
    have hP := PEqualNP.Outside.L_meta_3835_aux.pgate x1 g hg.1 hg.2
    have key : ∀ x : List Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: rest) out).eval x =
        (PEqualNP.CircuitLowerBounds.Circuit.mk rest out).eval
          (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := fun x => rfl
    refine ⟨⟨rest, out⟩, fun g' hg' => hF g' (by simp [hg']), by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    rcases hP with ⟨i, b, hb⟩ | ⟨i, j, o, hij, ho⟩
    · exact Or.inl ⟨i, b, fun x hx => by rw [key x]; exact congrArg _ (congrArg _ (congrArg (fun t => [t]) (hb x hx)))⟩
    · exact Or.inr ⟨i, j, o, hij, fun x hx => by rw [key x]; exact congrArg _ (congrArg _ (congrArg (fun t => [t]) (ho x hx)))⟩
