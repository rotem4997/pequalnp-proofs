import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8474
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

end PEqualNP.Outside.L_meta_8474

open PEqualNP.Outside.L_meta_8474 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8474 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → (∀ (x5 x6 : Fin x1), x2 x5 x6 = Bool.true → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x5) (Fin.natAdd x1 x6)) = Bool.true) → (∀ (x6 : Finset (Fin x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x7 : Fin (x1 + x1)) => Fin.addCases (fun (x8 : Fin x1) => Decidable.decide (x8 ∈ x6)) (fun (x8 : Fin x1) => Decidable.decide (∀ x9 ∈ x6, x2 x9 x8 = Bool.false)) x7) = Bool.false) → ∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2 x8 x9 = Bool.true ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true) := by
  intro n A C hAO hE hI x
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, le_of_eq (hAO.2.2 g hg)⟩
    have := hAO.1 g hg
    simpa using this
  by_cases hex : ∃ (u : Fin n) (v : Fin n), A u v = true ∧ x (Fin.castAdd n u) = true ∧ x (Fin.natAdd n v) = true
  · rw [decide_eq_true hex]
    obtain ⟨u, v, huv, hu, hv⟩ := hex
    refine cmono C hm (n + n) _ x ?_ (hE u v huv)
    intro w hw
    have hw' : w = Fin.castAdd n u ∨ w = Fin.natAdd n v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hw
    rcases hw' with rfl | rfl
    · exact hu
    · exact hv
  · rw [decide_eq_false hex]
    by_contra hc
    have hc' : C.eval (List.ofFn x) = true := by
      have : PEqualNP.MetaComplexity.circuitFun (n + n) C x = true := by simpa using hc
      exact this
    have h3 := hI (Finset.univ.filter fun u => x (Fin.castAdd n u) = true)
    have h2 := cmono C hm (n + n) x (fun w : Fin (n + n) => Fin.addCases (fun u : Fin n => decide (u ∈ Finset.univ.filter fun u => x (Fin.castAdd n u) = true)) (fun v : Fin n => decide (∀ u ∈ Finset.univ.filter fun u => x (Fin.castAdd n u) = true, A u v = false)) w) (by
      intro w hw
      induction w using Fin.addCases with
      | left u =>
        show Fin.addCases _ _ (Fin.castAdd n u) = true
        rw [Fin.addCases_left]
        simpa using hw
      | right v =>
        show Fin.addCases _ _ (Fin.natAdd n v) = true
        rw [Fin.addCases_right]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff]
        intro u hu
        by_contra huv
        exact hex ⟨u, v, by simpa using huv, hu, hw⟩) hc'
    have h4 : C.eval (List.ofFn _) = false := h3
    rw [h4] at h2
    exact absurd h2 (by simp)
