import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4099_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem key (C : Circuit) (u v : Fin 26) (hC : PEqualNP.TopForm.IsAO2 26 C) :
    ∀ k : ℕ, val C (fun w : Fin 26 => decide (w = u ∨ w = v)) k = true →
      val C (fun w : Fin 26 => decide (w = u)) k = false →
      val C (fun w : Fin 26 => decide (w = v)) k = false →
      ∃ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
        val C (fun w : Fin 26 => decide (w = u ∨ w = v)) (26 + j) = true ∧
        Relation.ReflTransGen (fun a b : ℕ => ∃ j' : ℕ, b = 26 + j' ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j').op = GateOp.or ∧
          a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j').inputs) (26 + j) k := by
  obtain ⟨hAO, hRB, hlen⟩ := hC
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hp hu hv
    by_cases hk : k < 26
    · exfalso
      have h1 := val_input C (fun w : Fin 26 => decide (w = u ∨ w = v)) ⟨k, hk⟩
      have h2 := val_input C (fun w : Fin 26 => decide (w = u)) ⟨k, hk⟩
      have h3 := val_input C (fun w : Fin 26 => decide (w = v)) ⟨k, hk⟩
      simp only at h1 h2 h3
      rw [h1] at hp
      rw [h2] at hu
      rw [h3] at hv
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hp hu hv
      tauto
    · by_cases hk2 : 26 + C.gates.length ≤ k
      · rw [val_beyond C _ hk2] at hp
        exact absurd hp (by simp)
      · obtain ⟨p, rfl⟩ : ∃ p, k = 26 + p := ⟨k - 26, by omega⟩
        have hp' : p < C.gates.length := by omega
        have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp'
        have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C p = C.gates[p] := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
        have hmem : C.gates[p] ∈ C.gates := List.getElem_mem hp'
        have hin : ∀ i ∈ (C.gates[p]).inputs, i < 26 + p := by
          intro i hi
          exact hRB p hp' i (hgate ▸ hi)
        rcases hAO _ hmem with hand | hor
        · exact ⟨p, hgate ▸ hand, hp, Relation.ReflTransGen.refl⟩
        · obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p]).inputs = [a, b] := by
            have h2 := hlen _ hmem
            match h : (C.gates[p]).inputs, h2 with
            | [a, b], _ => exact ⟨a, b, rfl⟩
          have ha : a < 26 + p := hin a (by simp [hab])
          have hb : b < 26 + p := hin b (by simp [hab])
          have e : ∀ x : Fin 26 → Bool, val C x (26 + p) = (val C x a || val C x b) := by
            intro x
            rw [val_gate C x hg, hor, hab]
            simp [GateOp.eval, operand, ha, hb]
          rw [e] at hp hu hv
          simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at hp hu hv
          have step : ∀ c : ℕ, c ∈ (C.gates[p]).inputs →
              (∃ j' : ℕ, 26 + p = 26 + j' ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j').op = GateOp.or ∧
                c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j').inputs) := by
            intro c hc
            exact ⟨p, rfl, hgate ▸ hor, hgate ▸ hc⟩
          rcases hp with hpa | hpb
          · obtain ⟨j, h1, h2, h3⟩ := ih a ha hpa hu.1 hv.1
            exact ⟨j, h1, h2, h3.tail (step a (by simp [hab]))⟩
          · obtain ⟨j, h1, h2, h3⟩ := ih b hb hpb hu.2 hv.2
            exact ⟨j, h1, h2, h3.tail (step b (by simp [hab]))⟩

end PEqualNP.Outside.L_meta_4099_aux

theorem PEqualNP.Outside.L_meta_4099 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Bool) (x3 : ℕ) => (x1.wires (List.ofFn x2)).getD x3 Bool.false; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) => ∃ (x5 : ℕ), x4 = (26 : ℕ) + x5 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).inputs; have x3 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (26 : ℕ) → Bool) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x1 x3 x4 ((26 : ℕ) + x5) = Bool.true ∧ Relation.ReflTransGen (x2 x3) ((26 : ℕ) + x5) x6; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) (x8 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 → x1 x5 (x4 x6 x7) x8 = Bool.true → x1 x5 (fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = x6)) x8 = Bool.false → x1 x5 (fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x7)) x8 = Bool.false → ∃ (x13 : ℕ), x3 x5 (x4 x6 x7) x13 x8 := by
  exact fun C u v k hC hp hu hv => PEqualNP.Outside.L_meta_4099_aux.key C u v hC k hp hu hv
