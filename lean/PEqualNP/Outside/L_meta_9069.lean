import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9069

open PEqualNP.CircuitLowerBounds

def F (x1 : Fin (9 : ℕ) → Bool) : Bool :=
  [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))

def sm (t : Fin 8 → Fin 8) (i : ℕ) : ℕ := if h : i < 8 then (t ⟨i, h⟩).val else i

def relab (t : Fin 8 → Fin 8) (C : Circuit) : Circuit :=
  { gates := C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (sm t) } : Gate)),
    output := sm t C.output }

theorem sm_lt (t : Fin 8 → Fin 8) (i : ℕ) (h : i < 8) : sm t i < 8 := by
  simp only [sm, h, dite_true]; exact (t ⟨i, h⟩).isLt

theorem sm_ge (t : Fin 8 → Fin 8) (i : ℕ) (h : ¬ i < 8) : sm t i = i := by
  simp only [sm, h, dite_false]

theorem getD_snoc (l : List Bool) (a : Bool) (i : ℕ) :
    (l ++ [a]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

def Inv (t : Fin 8 → Fin 8) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ 8 ≤ w.length ∧ ∀ i, w'.getD (sm t i) false = w.getD i false

theorem step (t : Fin 8 → Fin 8) (g : Gate) (w w' : List Bool) (h : Inv t w w') :
    Inv t (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval ((g.inputs.map (sm t)).map fun i => w'.getD i false)]) := by
  obtain ⟨hl, h8, hi⟩ := h
  have hv : (g.inputs.map (sm t)).map (fun i => w'.getD i false) =
      g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; apply List.map_congr_left; intro i _; exact hi i
  rw [hv]
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rw [getD_snoc, getD_snoc]
  by_cases hi8 : i < 8
  · have := sm_lt t i hi8
    rw [if_pos (by omega), if_pos (by omega)]; exact hi i
  · have := hi i
    rw [sm_ge t i hi8] at this ⊢
    rw [hl]
    split_ifs <;> first | rfl | exact this

theorem fold (t : Fin 8 → Fin 8) : ∀ (gs : List Gate) (w w' : List Bool), Inv t w w' →
    Inv t (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (fun g => ({ op := g.op, inputs := g.inputs.map (sm t) } : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w')
  | [], _, _, h => h
  | g :: gs, w, w', h => by
    simp only [List.foldl_cons, List.map_cons]
    exact fold t gs _ _ (step t g w w' h)

theorem getD_ofFn_lt (y : Fin 8 → Bool) (i : ℕ) (h : i < 8) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem getD_ofFn_ge (y : Fin 8 → Bool) (i : ℕ) (h : ¬ i < 8) :
    (List.ofFn y).getD i false = false := by
  rw [List.getD_eq_default _ _ (by simp; omega)]

theorem init (t : Fin 8 → Fin 8) (y : Fin 8 → Bool) :
    Inv t (List.ofFn fun i => y (t i)) (List.ofFn y) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < 8
  · rw [getD_ofFn_lt _ _ h, getD_ofFn_lt _ _ (sm_lt t i h)]
    simp only [sm, h, dite_true]
  · rw [sm_ge t i h, getD_ofFn_ge _ _ h, getD_ofFn_ge _ _ h]

theorem wires_relab (t : Fin 8 → Fin 8) (C : Circuit) (y : Fin 8 → Bool) (j : ℕ) :
    ((relab t C).wires (List.ofFn y)).getD (sm t j) false =
      (C.wires (List.ofFn fun i => y (t i))).getD j false :=
  (fold t C.gates _ _ (init t y)).2.2 j

theorem eval_relab (t : Fin 8 → Fin 8) (C : Circuit) (y : Fin 8 → Bool) :
    (relab t C).eval (List.ofFn y) = C.eval (List.ofFn fun i => y (t i)) :=
  wires_relab t C y C.output

theorem fan_relab (t : Fin 8 → Fin 8) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (relab t C) := by
  intro g hg
  simp only [relab, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := h g0 hg0
  exact ⟨h1, by simpa using h2⟩

theorem size_relab (t : Fin 8 → Fin 8) (C : Circuit) : (relab t C).size = C.size := by
  simp [relab, Circuit.size]

def t6 : Fin 8 → Fin 8 := ![1, 0, 4, 7, 5, 2, 6, 3]
def t7 : Fin 8 → Fin 8 := ![1, 2, 3, 7, 5, 0, 6, 4]

theorem vec8 (y : Fin 8 → Bool) : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7] := by
  funext i; fin_cases i <;> rfl

set_option maxRecDepth 20000 in
theorem key6 : ∀ (b a0 a1 a2 a3 a4 a5 a6 a7 : Bool),
    F (Fin.insertNth (6 : Fin 9) b (fun i => (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → Bool) (t6 i))) =
      F (Fin.insertNth (4 : Fin 9) b (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → Bool)) := by
  decide

set_option maxRecDepth 20000 in
theorem key7 : ∀ (b a0 a1 a2 a3 a4 a5 a6 a7 : Bool),
    F (Fin.insertNth (7 : Fin 9) b (fun i => (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → Bool) (t7 i))) =
      F (Fin.insertNth (4 : Fin 9) b (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → Bool)) := by
  decide

theorem aut6 (b : Bool) (y : Fin 8 → Bool) :
    F (Fin.insertNth (6 : Fin 9) b (fun i => y (t6 i))) = F (Fin.insertNth (4 : Fin 9) b y) := by
  rw [vec8 y]; exact key6 b _ _ _ _ _ _ _ _

theorem aut7 (b : Bool) (y : Fin 8 → Bool) :
    F (Fin.insertNth (7 : Fin 9) b (fun i => y (t7 i))) = F (Fin.insertNth (4 : Fin 9) b y) := by
  rw [vec8 y]; exact key7 b _ _ _ _ _ _ _ _

theorem general (d : Fin 9) (t : Fin 8 → Fin 8)
    (haut : ∀ b y, F (Fin.insertNth d b (fun i => y (t i))) = F (Fin.insertNth (4 : Fin 9) b y))
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size = 13)
    (hf : PEqualNP.MetaComplexity.circuitFun 8 C = fun x => F (Fin.insertNth d false x)) :
    ∃ (x8 : Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = 13 ∧
      (PEqualNP.MetaComplexity.circuitFun 8 x8 = fun x9 => F (Fin.insertNth (4 : Fin 9) false x9)) ∧
      ∀ (x9 : ℕ), ∃ (x10 : ℕ), ∀ (x11 : Fin 8 → Bool),
        F (Fin.insertNth (4 : Fin 9) false x11) = false ∧ F (Fin.insertNth (4 : Fin 9) true x11) = true ∧
          (x8.wires (List.ofFn x11)).getD x10 false = false →
        ∃ (x13 : Fin 8 → Bool), F (Fin.insertNth d false x13) = false ∧
          F (Fin.insertNth d true x13) = true ∧ (C.wires (List.ofFn x13)).getD x9 false = false := by
  refine ⟨relab t C, fan_relab t C fan, (size_relab t C).trans hs, ?_, ?_⟩
  · funext y
    show (relab t C).eval (List.ofFn y) = _
    rw [eval_relab]
    exact (congrFun hf (fun i => y (t i))).trans (haut false y)
  · intro j
    refine ⟨sm t j, fun y hy => ⟨fun i => y (t i), (haut false y).trans hy.1,
      (haut true y).trans hy.2.1, (wires_relab t C y j).symm.trans hy.2.2⟩⟩

end PEqualNP.Outside.L_meta_9069

theorem PEqualNP.Outside.L_meta_9069 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (13 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x4 = fun (x7 : Fin (8 : ℕ) → Bool) => x1 (x2.insertNth Bool.false x7)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = (13 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = fun (x9 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x9)) ∧ ∀ (x9 : ℕ), ∃ (x10 : ℕ), ∀ (x11 : Fin (8 : ℕ) → Bool), x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x11) = Bool.false ∧ x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.true x11) = Bool.true ∧ (x8.wires (List.ofFn x11)).getD x10 Bool.false = Bool.false → ∃ (x13 : Fin (8 : ℕ) → Bool), x1 (x2.insertNth Bool.false x13) = Bool.false ∧ x1 (x2.insertNth Bool.true x13) = Bool.true ∧ (x4.wires (List.ofFn x13)).getD x9 Bool.false = Bool.false := by
  dsimp only
  intro d hd C fan hs hf
  simp only [List.mem_cons, List.mem_singleton] at hd
  rcases hd with rfl | rfl | hd
  · exact PEqualNP.Outside.L_meta_9069.general 6 PEqualNP.Outside.L_meta_9069.t6 PEqualNP.Outside.L_meta_9069.aut6 C fan hs hf
  · exact PEqualNP.Outside.L_meta_9069.general 7 PEqualNP.Outside.L_meta_9069.t7 PEqualNP.Outside.L_meta_9069.aut7 C fan hs hf
  · simp at hd
