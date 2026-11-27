import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18936_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    exact List.getD_append w _ false i hi

theorem wire_gate_eval (C : Circuit) (x : Fin 26 → Bool) (k : ℕ) (g : Gate)
    (hgk : C.gates[k]? = some g) (hrb : ∀ i ∈ g.inputs, i < 26 + k) :
    (C.wires (List.ofFn x)).getD (26 + k) false =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hlt : k < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgk
    exact absurd hgk (by simp)
  have hsplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = g :: C.gates.drop (k + 1) := by
      have hg' : C.gates[k] = g := by
        have := List.getElem?_eq_getElem hlt; rw [this] at hgk; injection hgk
      rw [← hg']; exact List.drop_eq_getElem_cons hlt
    rw [← h2]; exact h1.symm
  let pre := (C.gates.take k).foldl wstep (List.ofFn x)
  have hpre_len : pre.length = 26 + k := by
    rw [foldl_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hW : C.wires (List.ofFn x) = (C.gates.drop (k + 1)).foldl wstep (wstep pre g) := by
    change C.gates.foldl wstep (List.ofFn x) = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_eq : ∀ i < 26 + k, (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [hW, foldl_prefix _ _ i (by simp [wstep, hpre_len]; omega)]
    exact List.getD_append pre _ false i (by omega)
  have h2 : (C.wires (List.ofFn x)).getD (26 + k) false =
      g.op.eval (g.inputs.map fun i => pre.getD i false) := by
    rw [hW, foldl_prefix _ _ (26 + k) (by simp [wstep, hpre_len])]
    dsimp only [wstep]
    have hlast : (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)]).getD pre.length false =
        g.op.eval (g.inputs.map fun i => pre.getD i false) := by simp [List.getD_eq_getElem?_getD]
    rw [← hpre_len, hlast]
  rw [h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hlt_eq i (hrb i hi)).symm

theorem main_proof :
    let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let V := fun (C : Circuit) =>
      (∀ i g, C.gates[i]? = some g → (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + i ∧ b < 26 + i) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    ∀ C, V C → ∀ p l, I p l →
      ∃ j < C.gates.length, Owns 26 C j (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by
  classical
  intro I V C ⟨hGates, hEval⟩ p l hpl
  let u : Fin 26 := Fin.castAdd 13 p
  let v : Fin 26 := Fin.natAdd 13 l
  have hex : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ gateVal 26 C j (pairInput u v) = true := by
    by_contra hno
    have hwire_split : ∀ w, (C.wires (List.ofFn (pairInput u v))).getD w false = true →
        (C.wires (List.ofFn (pairInput u u))).getD w false = true ∨
        (C.wires (List.ofFn (pairInput v v))).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases h26 : w < 26
        · have hin : ∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD w false = x ⟨w, h26⟩ := by
            intro x
            change (C.gates.foldl wstep (List.ofFn x)).getD w false = _
            rw [foldl_prefix C.gates (List.ofFn x) w (by simp [h26])]
            rw [List.getD_eq_getElem _ _ (by simp [h26]), List.getElem_ofFn]
          rw [hin] at hw
          rw [hin, hin]
          simp only [pairInput, decide_eq_true_eq] at hw ⊢
          rcases hw with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        · by_cases hlt : w < 26 + C.gates.length
          · let k := w - 26
            have hk : k < C.gates.length := by omega
            have hwk : w = 26 + k := by omega
            cases hgk : C.gates[k]? with
            | none =>
              have hne : C.gates[k]? ≠ none := by simp [hk]
              exact absurd hgk hne
            | some g =>
              rcases hGates k g hgk with ⟨hop, a, b, hins, _, ha, hb⟩
              have hrb : ∀ i ∈ g.inputs, i < 26 + k := by
                intro i hi; rw [hins] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl <;> assumption
              have hga : gateAt C k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hgk]
              have hnotand : g.op ≠ GateOp.and := by
                intro hand
                apply hno
                refine ⟨k, hk, hga ▸ hand, ?_⟩
                change (C.wires (List.ofFn (pairInput u v))).getD (26 + k) false = true
                rwa [← hwk]
              have hor : g.op = GateOp.or := hop.resolve_left hnotand
              rw [hwk] at hw ⊢
              rw [wire_gate_eval C (pairInput u v) k g hgk hrb, hor, hins] at hw
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                id, Bool.or_false, Bool.or_eq_true] at hw
              rw [wire_gate_eval C (pairInput u u) k g hgk hrb,
                  wire_gate_eval C (pairInput v v) k g hgk hrb, hor, hins]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                id, Bool.or_false, Bool.or_eq_true]
              rcases hw with ha_t | hb_t
              · rcases ih a (by omega) ha_t with h1 | h2
                · exact Or.inl (Or.inl h1)
                · exact Or.inr (Or.inl h2)
              · rcases ih b (by omega) hb_t with h1 | h2
                · exact Or.inl (Or.inr h1)
                · exact Or.inr (Or.inr h2)
          · have hge : (C.wires (List.ofFn (pairInput u v))).length ≤ w := by
              change (C.gates.foldl wstep (List.ofFn (pairInput u v))).length ≤ w
              rw [foldl_len, List.length_ofFn]; omega
            have h0 : (C.wires (List.ofFn (pairInput u v))).getD w false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
            rw [h0] at hw; exact absurd hw (by decide)
    have huv_true : C.eval (List.ofFn (pairInput u v)) = true := by
      rw [hEval]
      exact ⟨p, l, hpl, by simp [pairInput, u], by simp [pairInput, v]⟩
    rcases hwire_split C.output huv_true with huu | hvv
    · have h := (hEval (pairInput u u)).mp huu
      rcases h with ⟨_, l', _, _, hl'⟩
      simp only [pairInput, decide_eq_true_eq, or_self] at hl'
      have hv := congrArg Fin.val hl'
      simp only [u, Fin.val_natAdd, Fin.val_castAdd] at hv
      have := p.isLt; omega
    · have h := (hEval (pairInput v v)).mp hvv
      rcases h with ⟨p', _, _, hp', _⟩
      simp only [pairInput, decide_eq_true_eq, or_self] at hp'
      have hv := congrArg Fin.val hp'
      simp only [v, Fin.val_natAdd, Fin.val_castAdd] at hv
      have := p'.isLt; omega
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, hj.1, hj.2.1, hj.2.2, ?_⟩
  intro i hij _ hiop
  cases h : gateVal 26 C i (pairInput u v)
  · rfl
  · exfalso
    exact Nat.find_min hex hij ⟨by omega, hiop, h⟩

end PEqualNP.Outside.L_meta_18936_aux

theorem PEqualNP.Outside.L_meta_18936 : (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ x8 < x3.gates.length, PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x8 (Fin.castAdd (13 : ℕ) x5) (Fin.natAdd (13 : ℕ) x6))  := by
  exact PEqualNP.Outside.L_meta_18936_aux.main_proof
