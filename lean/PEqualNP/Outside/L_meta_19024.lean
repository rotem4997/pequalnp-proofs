import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19024

namespace Dual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pg (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

def pc (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (pg σ), σ C.output⟩

theorem key_getD {α : Type} (d : α) (σ : ℕ → ℕ) (n : ℕ)
    (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
    (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
    (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (t0 : List α) (i : ℕ) :
    (init' ++ t0).getD (σ i) d = (init ++ t0).getD i d := by
  by_cases h : i < n
  · have e1 : (init' ++ t0).getD (σ i) d = init'.getD (σ i) d :=
      List.getD_append init' t0 d (σ i) (by rw [hl']; exact hσ1 i h)
    have e2 : (init ++ t0).getD i d = init.getD i d :=
      List.getD_append init t0 d i (by rw [hl]; exact h)
    rw [e1, e2]
    exact hi i h
  · have h' : n ≤ i := Nat.le_of_not_lt h
    have e1 : (init' ++ t0).getD i d = t0.getD (i - init'.length) d :=
      List.getD_append_right init' t0 d i (by rw [hl']; exact h')
    have e2 : (init ++ t0).getD i d = t0.getD (i - init.length) d :=
      List.getD_append_right init t0 d i (by rw [hl]; exact h')
    rw [hσ2 i h', e1, e2, hl, hl']

theorem perm_fold {α : Type} (d : α) (S : Gate → List α → α) (σ : ℕ → ℕ) (n : ℕ)
    (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i)
    (hS : ∀ (g : Gate) (acc acc' : List α), (∀ i, acc'.getD (σ i) d = acc.getD i d) →
      S (pg σ g) acc' = S g acc)
    (init init' : List α) (hl : init.length = n) (hl' : init'.length = n)
    (hi : ∀ i, i < n → init'.getD (σ i) d = init.getD i d) (gs : List Gate) (t0 : List α) :
    ∃ t, gs.foldl (fun acc g => acc ++ [S g acc]) (init ++ t0) = init ++ t ∧
      (gs.map (pg σ)).foldl (fun acc g => acc ++ [S g acc]) (init' ++ t0) = init' ++ t := by
  induction gs generalizing t0 with
  | nil => exact ⟨t0, rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, h1, h2⟩ := ih (t0 ++ [S g (init ++ t0)])
    refine ⟨t, ?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [List.append_assoc]
      exact h1
    · simp only [List.map_cons, List.foldl_cons]
      rw [hS g (init ++ t0) (init' ++ t0) (key_getD d σ n hσ1 hσ2 init init' hl hl' hi t0),
        List.append_assoc]
      exact h2

theorem pc_eval (σ : ℕ → ℕ) (n : ℕ)
    (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (C : Circuit)
    (x x' : List Bool) (hl : x.length = n) (hl' : x'.length = n)
    (hi : ∀ i, i < n → x'.getD (σ i) false = x.getD i false) :
    (pc σ C).eval x' = C.eval x := by
  have hS : ∀ (g : Gate) (acc acc' : List Bool),
      (∀ i, acc'.getD (σ i) false = acc.getD i false) →
      (pg σ g).op.eval ((pg σ g).inputs.map fun i => acc'.getD i false) =
        g.op.eval (g.inputs.map fun i => acc.getD i false) := by
    intro g acc acc' h
    show g.op.eval ((g.inputs.map σ).map fun i => acc'.getD i false) = _
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => h i)
  obtain ⟨t, h1, h2⟩ := perm_fold false
    (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) σ n hσ1 hσ2 hS x x' hl hl' hi
    C.gates []
  rw [List.append_nil] at h1 h2
  have e1 : C.wires x = x ++ t := h1
  have e2 : (pc σ C).wires x' = x' ++ t := h2
  unfold Circuit.eval
  rw [e1, e2]
  exact key_getD false σ n hσ1 hσ2 x x' hl hl' hi t C.output

theorem init_getD (n : ℕ) (m : Finset ℕ) (i : ℕ) (h : i < n) :
    ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 = if i ∈ m then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem pc_deg (σ : ℕ → ℕ) (n : ℕ)
    (hσ1 : ∀ i, i < n → σ i < n) (hσ2 : ∀ i, n ≤ i → σ i = i) (C : Circuit)
    (m m' : Finset ℕ) (hmk : ∀ i, i < n → (i ∈ m ↔ σ i ∈ m')) :
    (pc σ C).lineDeg n m' = C.lineDeg n m := by
  have hS : ∀ (g : Gate) (acc acc' : List ℕ),
      (∀ i, acc'.getD (σ i) 0 = acc.getD i 0) →
      (pg σ g).lineDegree acc' = g.lineDegree acc := by
    intro g acc acc' h
    have hmm : ((pg σ g).inputs.map fun i => acc'.getD i 0) =
        (g.inputs.map fun i => acc.getD i 0) := by
      show ((g.inputs.map σ).map fun i => acc'.getD i 0) = _
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => h i)
    unfold Gate.lineDegree
    rw [hmm]
    rfl
  have hi : ∀ i, i < n →
      ((List.range n).map fun i => if i ∈ m' then 1 else 0).getD (σ i) 0 =
        ((List.range n).map fun i => if i ∈ m then 1 else 0).getD i 0 := by
    intro i h
    rw [init_getD n m' (σ i) (hσ1 i h), init_getD n m i h]
    by_cases hm : i ∈ m
    · rw [ite_eq_left hm, ite_eq_left ((hmk i h).mp hm)]
    · rw [ite_eq_right hm, ite_eq_right (fun h' => hm ((hmk i h).mpr h'))]
  have hl : ((List.range n).map fun i => if i ∈ m then 1 else 0).length = n := by simp
  have hl' : ((List.range n).map fun i => if i ∈ m' then 1 else 0).length = n := by simp
  obtain ⟨t, h1, h2⟩ := perm_fold 0 (fun g dd => g.lineDegree dd) σ n hσ1 hσ2 hS _ _ hl hl' hi
    C.gates []
  rw [List.append_nil] at h1 h2
  have e1 : C.lineDegrees n m = ((List.range n).map fun i => if i ∈ m then 1 else 0) ++ t := h1
  have e2 : (pc σ C).lineDegrees n m' =
      ((List.range n).map fun i => if i ∈ m' then 1 else 0) ++ t := h2
  unfold Circuit.lineDeg
  rw [e1, e2]
  exact key_getD 0 σ n hσ1 hσ2 _ _ hl hl' hi t C.output

theorem pc_mono (σ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (pc σ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have h0 := h g0 hg0
  refine ⟨h0.1, ?_⟩
  show (g0.inputs.map σ).length ≤ 2
  rw [List.length_map]
  exact h0.2

theorem pc_size (σ : ℕ → ℕ) (C : Circuit) : (pc σ C).size = C.size := by
  exact List.length_map _

def sw (i : ℕ) : ℕ :=
  if i < 13 then 13 + (13 - i) % 13 else if i < 26 then (26 - i) % 13 else i

theorem sw_lt (i : ℕ) (h : i < 26) : sw i < 26 := by
  unfold sw; split_ifs <;> omega

theorem sw_ge (i : ℕ) (h : 26 ≤ i) : sw i = i := by
  unfold sw; split_ifs <;> omega

theorem sw_mark (i : ℕ) (h : i < 26) : (i ∈ Finset.range 13 ↔ sw i ∈ Finset.Ico 13 26) := by
  rw [Finset.mem_range, Finset.mem_Ico]; unfold sw; split_ifs <;> omega

def dualIn (x : Fin 26 → Bool) : Fin 26 → Bool := fun k => x ⟨sw k.val, sw_lt k.val k.isLt⟩

theorem dual_eval (C : Circuit) (x : Fin 26 → Bool) :
    circuitFun 26 (pc sw C) x = circuitFun 26 C (dualIn x) := by
  show (pc sw C).eval (List.ofFn x) = C.eval (List.ofFn (dualIn x))
  refine pc_eval sw 26 sw_lt sw_ge C (List.ofFn (dualIn x)) (List.ofFn x) (by simp) (by simp) ?_
  intro i h
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left (sw_lt i h), dite_eq_left h, Option.getD_some, dualIn]

theorem dual_deg (C : Circuit) (D : ℕ) :
    HasLineDegree 26 (Finset.Ico 13 26) (pc sw C) D ↔
    HasLineDegree 26 (Finset.range 13) C D := by
  unfold HasLineDegree
  rw [pc_deg sw 26 sw_lt sw_ge C (Finset.range 13) (Finset.Ico 13 26) sw_mark]

theorem sw_mark_rev (i : ℕ) (h : i < 26) :
    (i ∈ Finset.Ico 13 26 ↔ sw i ∈ Finset.range 13) := by
  rw [Finset.mem_range, Finset.mem_Ico]
  unfold sw
  split_ifs <;> omega

theorem dual_deg_rev (C : Circuit) (D : ℕ) :
    HasLineDegree 26 (Finset.range 13) (pc sw C) D ↔
    HasLineDegree 26 (Finset.Ico 13 26) C D := by
  unfold HasLineDegree
  rw [pc_deg sw 26 sw_lt sw_ge C (Finset.Ico 13 26) (Finset.range 13) sw_mark_rev]

theorem sw_cast : ∀ q : Fin 13,
    sw (Fin.castAdd 13 q : Fin 26).val = (Fin.natAdd 13 (-q) : Fin 26).val := by decide

theorem sw_nat : ∀ l : Fin 13,
    sw (Fin.natAdd 13 l : Fin 26).val = (Fin.castAdd 13 (-l) : Fin 26).val := by decide

theorem dualIn_cast (z : Fin 26 → Bool) (q : Fin 13) :
    dualIn z (Fin.castAdd 13 q) = z (Fin.natAdd 13 (-q)) := by
  show z ⟨sw (Fin.castAdd 13 q : Fin 26).val, _⟩ = _
  exact congrArg z (Fin.ext (sw_cast q))

theorem dualIn_nat (z : Fin 26 → Bool) (l : Fin 13) :
    dualIn z (Fin.natAdd 13 l) = z (Fin.castAdd 13 (-l)) := by
  show z ⟨sw (Fin.natAdd 13 l : Fin 26).val, _⟩ = _
  exact congrArg z (Fin.ext (sw_nat l))

end Dual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
def turn (T : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter (fun p => -p ∈ T)

def vec (X Y : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

theorem vecInput (X Y : Finset (Fin 13)) : List.ofFn (vec X Y) = incidenceInput X Y := by
  exact List.ofFn_fin_append _ _

theorem flipVec (X Y : Finset (Fin 13)) : Dual.dualIn (vec X Y) = vec (turn Y) (turn X) := by
  funext i
  refine Fin.addCases (m := 13) (n := 13) (fun u => ?_) (fun v => ?_) i
  · rw [Dual.dualIn_cast]
    simp only [vec,Fin.append_left,Fin.append_right,turn,Finset.mem_filter,Finset.mem_univ,true_and]
  · rw [Dual.dualIn_nat]
    simp only [vec,Fin.append_left,Fin.append_right,turn,Finset.mem_filter,Finset.mem_univ,true_and]

theorem turnImage (T : Finset (Fin 13)) : turn T = T.image (fun v => -v) := by
  ext p
  simp only [turn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨-p,h,neg_neg p⟩
  · rintro ⟨v,h,rfl⟩
    simpa using h

end PEqualNP.Outside.L_meta_19024
open PEqualNP.Outside.L_meta_19024

theorem PEqualNP.Outside.L_meta_19024 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size = x1.size ∧ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) = x1.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) ∧ ∀ (x4 x5 : Finset (Fin (13 : ℕ))), x3.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = x1.eval (PEqualNP.GenericRejection.incidenceInput (Finset.image (fun (x6 : Fin (13 : ℕ)) => -x6) x5) (Finset.image (fun (x6 : Fin (13 : ℕ)) => -x6) x4)) := by
  intro C h
  refine ⟨Dual.pc Dual.sw C, Dual.pc_mono _ _ h, Dual.pc_size _ _, ?_, ?_⟩
  · exact Dual.pc_deg _ _ Dual.sw_lt Dual.sw_ge C _ _ Dual.sw_mark
  · intro X Y
    have e := Dual.dual_eval C (vec X Y)
    rw [flipVec] at e
    change (Dual.pc Dual.sw C).eval (List.ofFn (vec X Y)) =
      C.eval (List.ofFn (vec (turn Y) (turn X))) at e
    simpa only [vecInput, turnImage] using e
