import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6660.ByList

open PEqualNP.CircuitLowerBounds

private def Ordered (gates : List Gate) : Prop :=
  ∀ i g, gates[i]? = some g → (g.op = .and ∨ g.op = .or) ∧
    ∃ p q : ℕ, g.inputs = [p,q] ∧ p ≠ q ∧ p < 14+i ∧ q < 14+i

private def nextBit (base : ℕ → Bool) (values : List Bool) (g : Gate) : Bool :=
  match g.inputs, g.op with
  | [p,q], .and => base p && values.getD q false || values.getD p false && base q
  | [p,q], .or => values.getD p false || values.getD q false
  | _, _ => false

private def scan (base : ℕ → Bool) (dir : Fin 14 → Bool) (gates : List Gate) : List Bool :=
  gates.foldl (fun values g => values ++ [nextBit base values g]) (List.ofFn dir)

private theorem earlier {gates : List Gate} (ordered : Ordered gates) {i : ℕ} {g : Gate}
    (hit : gates[i]? = some g) {p q : ℕ} (pins : g.inputs = [p,q]) :
    p < 14+i ∧ q < 14+i := by
  obtain ⟨_,p',q',same,_,hp,hq⟩ := ordered i g hit
  have eq : p=p' ∧ q=q' := by simpa using pins.symm.trans same
  exact ⟨eq.1.symm ▸ hp,eq.2.symm ▸ hq⟩

private theorem scanRules (base : ℕ → Bool) (dir : Fin 14 → Bool) (gates : List Gate)
    (ordered : Ordered gates) :
    let values := scan base dir gates
    values.length = 14+gates.length ∧
      (∀ i : Fin 14, values.getD i.val false = dir i) ∧
      ∀ (i : ℕ) (g : Gate) (p q : ℕ), gates[i]? = some g → g.inputs = [p,q] →
        (g.op = .and → values.getD (14+i) false =
          (base p && values.getD q false || values.getD p false && base q)) ∧
        (g.op = .or → values.getD (14+i) false = (values.getD p false || values.getD q false)) := by
  induction gates using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [scan],?_,?_⟩
    · intro i
      change (List.ofFn dir).getD i.val false = dir i
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    · simp
  | append_singleton gs gate ih =>
    have front : Ordered gs := by
      intro i g hit
      apply ordered i g
      have valid := (List.getElem?_eq_some_iff.mp hit).1
      rwa [List.getElem?_append_left valid]
    obtain ⟨length,inputs,rules⟩ := ih front
    let pre := scan base dir gs
    let added := nextBit base pre gate
    have appended : scan base dir (gs ++ [gate]) = pre ++ [added] := by
      simp [scan,pre,added,List.foldl_append]
    change pre.length = 14+gs.length at length
    have readOld (i : ℕ) (small : i < 14+gs.length) :
        (pre ++ [added]).getD i false = pre.getD i false :=
      List.getD_append _ _ _ _ (by simpa only [length] using small)
    have readNew : (pre ++ [added]).getD (14+gs.length) false = added := by
      rw [←length,List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      simp
    dsimp only
    rw [appended]
    refine ⟨by simp [length,Nat.add_assoc],?_,?_⟩
    · intro i
      rw [readOld i.val (by have := i.isLt; omega)]
      exact inputs i
    · intro i g p q hit pins
      have valid : i < (gs ++ [gate]).length := (List.getElem?_eq_some_iff.mp hit).1
      have bound : i ≤ gs.length := by simp at valid; omega
      have early := earlier ordered hit pins
      have ep : p < 14+gs.length := lt_of_lt_of_le early.1 (Nat.add_le_add_left bound 14)
      have eq : q < 14+gs.length := lt_of_lt_of_le early.2 (Nat.add_le_add_left bound 14)
      rw [readOld p ep,readOld q eq]
      rcases lt_or_eq_of_le bound with old|last
      · have oldHit : gs[i]?=some g := by
          simpa only [List.getElem?_append_left old] using hit
        rw [readOld (14+i) (Nat.add_lt_add_left old 14)]
        exact rules i g p q oldHit pins
      · subst i
        have lastHit : (gs ++ [gate])[gs.length]?=some gate := by
          rw [List.getElem?_append_right (Nat.le_refl _)]
          simp
        have same : g=gate := Option.some.inj (hit.symm.trans lastHit)
        subst g
        rw [readNew]
        exact ⟨fun op=>by simp [added,nextBit,pins,op],fun op=>by simp [added,nextBit,pins,op]⟩

theorem directionalWireRecurrence (C : Circuit)
    (ordered : ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ p q : ℕ,
        g.inputs = [p,q] ∧ p ≠ q ∧ p < 14+i ∧ q < 14+i)
    (x dir : Fin 14 → Bool) (j p q : ℕ)
    (atGate : C.gates[j]? = some {op := .and, inputs := [p,q]})
    (pOff : (C.wires (List.ofFn x)).getD p false = false)
    (qOff : (C.wires (List.ofFn x)).getD q false = false) :
    ∃ D : ℕ → Bool, (∀ v : Fin 14, D v.val = dir v) ∧
      (∀ (i : ℕ) (g : Gate) (a b : ℕ), C.gates[i]?=some g → g.inputs=[a,b] →
        (g.op = .and → D (14+i) =
          ((C.wires (List.ofFn x)).getD a false && D b || D a && (C.wires (List.ofFn x)).getD b false)) ∧
        (g.op = .or → D (14+i) = (D a || D b))) ∧ D (14+j)=false := by
  let base (i : ℕ) := (C.wires (List.ofFn x)).getD i false
  obtain ⟨_,inputs,rules⟩ := scanRules base dir C.gates ordered
  let D (i : ℕ) := (scan base dir C.gates).getD i false
  refine ⟨D,inputs,rules,?_⟩
  have off := (rules j {op := .and, inputs := [p,q]} p q atGate rfl).1 rfl
  change D (14+j) = (base p && D q || D p && base q) at off
  have atP : base p=false := pOff
  have atQ : base q=false := qOff
  simpa only [atP,atQ,Bool.false_and,Bool.and_false,Bool.or_false] using off


end PEqualNP.Outside.L_meta_6660.ByList

theorem PEqualNP.Outside.L_meta_6660 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → ∀ (x3 x4 : Fin (14 : ℕ) → Bool) (x5 x6 x7 : ℕ), x1.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } → (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.false → (x1.wires (List.ofFn x3)).getD x7 Bool.false = Bool.false → ∃ (x11 : ℕ → Bool), (∀ (x12 : Fin (14 : ℕ)), x11 ↑x12 = x4 x12) ∧ (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x1.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x11 ((14 : ℕ) + x12) = ((x1.wires (List.ofFn x3)).getD x14 Bool.false && x11 x15 || x11 x14 && (x1.wires (List.ofFn x3)).getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11 ((14 : ℕ) + x12) = (x11 x14 || x11 x15))) ∧ x11 ((14 : ℕ) + x5) = Bool.false := by
  exact PEqualNP.Outside.L_meta_6660.ByList.directionalWireRecurrence
