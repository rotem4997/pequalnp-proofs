import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2642_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht, List.length_append, hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

/-! Erasing one gate -/

/-- Where wire `i` of the erased circuit sits in the old one (`k = n + m`). -/
def up (k i : ℕ) : ℕ := if i < k then i else i + 1

/-- The renamed copy of a gate after the erased one. -/
def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
  unfold up eraseRedirect
  split_ifs <;> omega

theorem sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
    (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
    V.length = U.length + 1 →
    ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
      ∀ g ∈ rest, n + m ∉ g.inputs) →
    ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
      (rest.foldl step V).getD (up (n + m) i) false
  | [], U, V, hrel, _, _, _ => by simpa using hrel
  | g :: rest, U, V, hrel, hk, hlen, hS => by
    have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hS with ⟨hS, -⟩ | hS
        · simpa [eraseRedirect] using hS
        · exact absurd hr (hS g (List.mem_cons_self ..))
      · rw [hrel, up_redir n m p r hrk]
    set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
    have hU : step U (ren n m p g) = U ++ [a] := by
      simp only [step, ren, List.map_map]
      congr 3
      exact List.map_congr_left fun r hr => hread r hr
    have hV : step V g = V ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, hU, hV]
    apply sim n m p rest
    · intro i
      rcases lt_trichotomy i U.length with hi | rfl | hi
      · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
      · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
        rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
        simp
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
    · simp; omega
    · simp; omega
    · rcases hS with ⟨hS, hp⟩ | hS
      · left
        refine ⟨?_, ?_⟩
        · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
          rcases hp with hp | hp
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
          · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
            rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
            exact hS
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; simp at hp ⊢; omega
      · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
    (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
    (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval y = C.eval y := by
  obtain ⟨hg, ho⟩ := erase_gates n C m p hm
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set A := (C.gates.take m).foldl step y with hA
  have hAl : A.length = n + m := by
    rw [hA, fold_length, hy, List.length_take]; omega
  set rest := C.gates.drop (m + 1) with hrest
  have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
  have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
    rw [wires_eq, hg, List.foldl_append]
  have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
  have hWl : (C.wires y).length = n + C.gates.length := by
    rw [wires_eq, fold_length, hy]
  have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
    intro i hi
    rw [hW, fold_getD_lt _ _ _ (by omega)]
  have hsim := sim n m p rest A (step A C.gates[m]) (by
      intro i
      by_cases hi : i < n + m
      · simp only [up, if_pos hi, step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [up, if_neg hi]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
    (by omega) hVl (by
      rcases hc with hc | ⟨-, hc⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hstable _ (by omega)]
          rcases hp with hp | hp
          · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
          · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; omega
      · exact Or.inr hc)
  unfold Circuit.eval
  rw [ho, hW', hsim, ← hW]
  by_cases hout : C.output = n + m
  · rcases hc with hc | ⟨hc, -⟩
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout]
      rcases hp with hp | hp
      · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
        rw [hu]; exact hc.symm
      · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
        rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · exact absurd hout hc
  · rw [up_redir n m p _ hout]

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  unfold Circuit.size
  rw [(erase_gates n C m p hm).1]
  simp
  omega

theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (eraseGate n C m p) := by
  intro g hg
  rw [(erase_gates n C m p hm).1, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [ren] using h2⟩

/-! Fixing two inputs to false without new gates -/

/-- Reads of input wires `a` and `b` go to wire `B`, which does not exist. -/
def sub (a b B i : ℕ) : ℕ := if i = a ∨ i = b then B else i

def fixC (a b : ℕ) (C : Circuit) (B : ℕ) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (sub a b B)⟩), sub a b B C.output⟩

/-- The invariant between the fixed circuit's wires `U` and the old wires `V` on the restricted
input, with `k` gates still to come. -/
def Inv (a b B : ℕ) (U V : List Bool) (k : ℕ) : Prop :=
  U.length = V.length ∧ (∀ i, i ≠ a → i ≠ b → U.getD i false = V.getD i false) ∧
    V.getD a false = false ∧ V.getD b false = false ∧ a < V.length ∧ b < V.length ∧
    V.length + k ≤ B ∧ B ≠ a ∧ B ≠ b

theorem inv_read (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V k) (r : ℕ) :
    U.getD (sub a b B r) false = V.getD r false := by
  obtain ⟨-, hrel, hVa, hVb, -, -, hB, hBa, hBb⟩ := h
  unfold sub
  split_ifs with hr
  · rw [hrel B hBa hBb, getD_ge _ _ (by omega)]
    rcases hr with rfl | rfl
    · exact hVa.symm
    · exact hVb.symm
  · push_neg at hr
    exact hrel r hr.1 hr.2

theorem inv_snoc (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V (k + 1)) (v : Bool) :
    Inv a b B (U ++ [v]) (V ++ [v]) k := by
  obtain ⟨hl, hrel, hVa, hVb, ha, hb, hB, hBa, hBb⟩ := h
  refine ⟨by simp [hl], fun i hia hib => ?_, ?_, ?_, by simp; omega, by simp; omega,
    by simp; omega, hBa, hBb⟩
  · rcases lt_trichotomy i V.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi, hrel i hia hib]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl, hl]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
  · rw [List.getD_append _ _ _ _ ha]; exact hVa
  · rw [List.getD_append _ _ _ _ hb]; exact hVb

theorem fix_fold (a b B : ℕ) : ∀ (gs : List Gate) (U V : List Bool), Inv a b B U V gs.length →
    Inv a b B ((gs.map fun g => (⟨g.op, g.inputs.map (sub a b B)⟩ : Gate)).foldl step U)
      (gs.foldl step V) 0
  | [], U, V, h => by simpa using h
  | g :: gs, U, V, h => by
    set v := g.op.eval (g.inputs.map fun i => V.getD i false)
    have hU : step U ⟨g.op, g.inputs.map (sub a b B)⟩ = U ++ [v] := by
      simp only [step, List.map_map]
      congr 3
      exact List.map_congr_left fun r _ => inv_read a b B U V _ h r
    simp only [List.map_cons, List.foldl_cons, hU]
    exact fix_fold a b B gs _ _ (inv_snoc a b B U V gs.length h v)

theorem fix_eval (n : ℕ) (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
    (fixC a b C (n + C.gates.length)).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
  set y := Function.update (Function.update x a false) b false
  have hinit : Inv a b (n + C.gates.length) (List.ofFn x) (List.ofFn y) C.gates.length := by
    refine ⟨by simp, fun i hia hib => ?_, ?_, ?_, by simp, by simp, by simp, by omega, by omega⟩
    · by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn, List.getElem_ofFn]
        have h1 : (⟨i, hi⟩ : Fin n) ≠ b := fun h => hib (by rw [← h])
        have h2 : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (by rw [← h])
        simp only [y, Function.update_of_ne h1, Function.update_of_ne h2]
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      by_cases hab : a = b
      · simp [y, hab]
      · simp [y, Function.update_of_ne hab]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp [y]
  have := fix_fold a b (n + C.gates.length) C.gates _ _ hinit
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact inv_read a b _ _ _ _ this C.output

theorem fix_size (a b B : ℕ) (C : Circuit) : (fixC a b C B).size = C.size := by
  simp [fixC, Circuit.size]

theorem fix_fanin (a b B : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (fixC a b C B) := by
  intro g hg
  simp only [fixC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hC g' hg'
  exact ⟨h1, by simpa using h2⟩

/-! The chain of erasures -/

theorem main : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  intro n k a b Cs h0 hstep
  have chain : ∀ j, j ≤ k → PEqualNP.MetaComplexity.FanInTwo (Cs j) ∧ (Cs j).size + j = (Cs 0).size ∧
      ∀ x : Fin n → Bool,
        (Cs j).eval (List.ofFn (Function.update (Function.update x a false) b false)) =
          (Cs 0).eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, by simp, fun _ => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨hf, hs, he⟩ := ih (by omega)
      obtain ⟨m, p, hm, hp, heq, hc⟩ := hstep j (by omega)
      have hml : m < (Cs j).gates.length := hm
      refine ⟨heq ▸ erase_fanin n _ m p hml hf, ?_, fun x => ?_⟩
      · have := erase_size n (Cs j) m p hml
        rw [heq]; omega
      · rw [heq, ← he x]
        apply erase_eval n (Cs j) m p _ (by simp) hml
        · rcases hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr hp
        · rcases hc with hc | hc
          · exact Or.inl (hc x)
          · exact Or.inr hc
  obtain ⟨hf, hs, he⟩ := chain k le_rfl
  refine ⟨fixC a b (Cs k) (n + (Cs k).gates.length), fix_fanin _ _ _ _ hf, ?_, fun x => ?_⟩
  · rw [fix_size]; exact hs
  · rw [fix_eval, he]

end PEqualNP.Outside.L_meta_2642_aux

theorem PEqualNP.Outside.L_meta_2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  exact PEqualNP.Outside.L_meta_2642_aux.main
