import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7245

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def lpStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or  => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

theorem foldl_len {α β : Type} (f : List α → β → α) (gs : List β) (w : List α) :
    (gs.foldl (fun w g => w ++ [f w g]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih]; omega

theorem gd_left {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_last {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem gd_prefix {α β : Type} (f : List α → β → α) (gs : List β) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (gs.foldl (fun w g => w ++ [f w g]) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega), gd_left _ _ _ _ h]

theorem and_fold_fst (ins : List (Bool × Bool)) (acc : Bool × Bool) :
    (ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) acc).1 =
      (acc.1 && (ins.map Prod.fst).all id) := by
  induction ins generalizing acc with
  | nil => simp
  | cons p ps ih => simp [List.foldl_cons, ih, Bool.and_assoc]

theorem inv_gen (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List (Bool × Bool)) :
    (gs.foldl (fun w g => w ++ [lpStep w g]) w).map Prod.fst =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
        (w.map Prod.fst) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    have hgd : ∀ i, (w.map Prod.fst).getD i false = (w.getD i (false, false)).1 := by
      intro i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases w[i]? <;> simp
    rw [List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rcases hg g (List.mem_cons_self) with h | h
    · simp only [lpStep, h, GateOp.eval]
      rw [and_fold_fst]
      simp [Function.comp_def]
      congr 1; funext i; cases w[i]? <;> rfl
    · simp only [lpStep, h, GateOp.eval]
      simp [List.any_map, Function.comp_def]
      congr 1; funext i; cases w[i]? <;> rfl

theorem lp_eq (C : Circuit) (isL : ℕ → Bool) (x : List Bool) :
    linearParts C isL x =
      C.gates.foldl (fun w g => w ++ [lpStep w g]) (linearParts ⟨[], 0⟩ isL x) := rfl

theorem wires_app (C : Circuit) (g1 g2 : Gate) (out : ℕ) (x : List Bool) :
    (⟨C.gates ++ [g1, g2], out⟩ : Circuit).wires x =
      (C.wires x ++ [g1.op.eval (g1.inputs.map fun i => (C.wires x).getD i false)]) ++
        [g2.op.eval (g2.inputs.map fun i =>
          (C.wires x ++ [g1.op.eval (g1.inputs.map fun i => (C.wires x).getD i false)]).getD i
            false)] := by
  unfold Circuit.wires
  rw [List.foldl_append]
  rfl

theorem lp_app (C : Circuit) (g1 g2 : Gate) (out : ℕ) (isL : ℕ → Bool) (x : List Bool) :
    linearParts (⟨C.gates ++ [g1, g2], out⟩ : Circuit) isL x =
      (linearParts C isL x ++ [lpStep (linearParts C isL x) g1]) ++
        [lpStep (linearParts C isL x ++ [lpStep (linearParts C isL x) g1]) g2] := by
  rw [lp_eq, lp_eq C]
  simp only
  rw [List.foldl_append]
  rfl

theorem lp_fst (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (isL : ℕ → Bool) (x : List Bool) :
    (linearParts C isL x).map Prod.fst =
      C.wires ((linearParts ⟨[], 0⟩ isL x).map Prod.fst) := by
  rw [lp_eq]
  exact inv_gen C.gates hg _

def zz : List Bool := List.ofFn fun (x6 : Fin 14) => decide (x6.val = 0 ∨ x6.val = 7)

def isLf (b : Bool) : ℕ → Bool := fun x6 => decide (x6 = if b = true then 7 else 0)

def yf (b : Bool) : Fin 14 → Bool := fun i => decide (i.val = if b = true then 0 else 7)

theorem init_fst (b : Bool) :
    (linearParts ⟨[], 0⟩ (isLf b) zz).map Prod.fst = List.ofFn (yf b) := by
  cases b <;> decide

theorem init_len (b : Bool) : (linearParts ⟨[], 0⟩ (isLf b) zz).length = 14 := by
  cases b <;> decide

theorem init_small (b : Bool) : ∀ t, t < 3 → t ≠ 0 →
    ((linearParts ⟨[], 0⟩ (isLf b) zz).getD t (false, false)).1 = false := by
  cases b <;> decide

end PEqualNP.Outside.L_meta_7245

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.Outside.L_meta_7245 in
theorem PEqualNP.Outside.L_meta_7245 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Decidable.decide (∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true)) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ x1.size + (2 : ℕ) ∧ (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) ∧ (∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn x5)) ∧ ∀ (x5 : Bool), ((PEqualNP.ReadK.linearParts x4 (fun (x6 : ℕ) => Decidable.decide (x6 = if x5 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (↑x6 = (0 : ℕ) ∨ ↑x6 = (7 : ℕ)))).getD x4.output (Bool.false, Bool.false)).2 = Bool.false := by
  intro C hC hE
  have hlen : ∀ x : List Bool, (C.wires x).length = x.length + C.size := by
    intro x
    unfold Circuit.wires Circuit.size
    exact foldl_len _ _ _
  have hO : C.output < 14 + C.size := by
    by_contra hc
    push_neg at hc
    have h1 := hE (fun _ => true)
    have h2 : C.eval (List.ofFn fun _ : Fin 14 => true) = false := by
      unfold Circuit.eval
      rw [List.getD_eq_default]
      rw [hlen]
      simpa using hc
    rw [h2] at h1
    revert h1
    decide
  have hmem : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
    exact (hC i g hi).1
  have hs3 : (if C.output = 1 then 2 else 1) < 3 := by split_ifs <;> omega
  have hs0 : (if C.output = 1 then 2 else 1) ≠ 0 := by split_ifs <;> omega
  have hso : C.output ≠ (if C.output = 1 then 2 else 1) := by split_ifs <;> omega
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [C.output, if C.output = 1 then 2 else 1]⟩,
      ⟨GateOp.and, [C.output, 14 + C.size]⟩], 14 + C.size + 1⟩, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · intro i g hg
    simp only at hg
    rcases Nat.lt_or_ge i C.gates.length with h | h
    · rw [List.getElem?_append_left h] at hg
      exact hC i g hg
    · rw [List.getElem?_append_right h] at hg
      obtain ⟨k, rfl⟩ : ∃ k, i = C.gates.length + k := ⟨i - C.gates.length, by omega⟩
      rw [Nat.add_sub_cancel_left] at hg
      have hsz : C.size = C.gates.length := rfl
      rcases k with _ | _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        refine ⟨Or.inr rfl, _, _, rfl, hso, by omega, by omega⟩
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        refine ⟨Or.inl rfl, _, _, rfl, by omega, by omega, by omega⟩
      · simp at hg
  · intro y
    unfold Circuit.eval
    rw [wires_app]
    have hW : (C.wires (List.ofFn y)).length = 14 + C.size := by rw [hlen]; simp
    have e1 : 14 + C.size + 1 =
        (C.wires (List.ofFn y) ++ [GateOp.or.eval ([C.output, if C.output = 1 then 2 else 1].map
          fun i => (C.wires (List.ofFn y)).getD i false)]).length := by
      rw [List.length_append, hW]; rfl
    simp only
    rw [e1, gd_last]
    simp only [List.map_cons, List.map_nil]
    rw [gd_left _ _ _ _ (by omega), ← hW, gd_last]
    simp only [GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil, id]
    cases (C.wires (List.ofFn y)).getD C.output false <;> simp
  · intro b
    have hz : (List.ofFn fun (x6 : Fin 14) => decide (x6.val = 0 ∨ x6.val = 7)) = zz := rfl
    have hL : (fun (x6 : ℕ) => decide (x6 = if b = true then 7 else 0)) = isLf b := rfl
    rw [hz, hL]
    simp only
    rw [lp_app]
    have hPl : (linearParts C (isLf b) zz).length = 14 + C.size := by
      rw [lp_eq, foldl_len, init_len]; rfl
    have hfst : ((linearParts C (isLf b) zz).getD C.output (false, false)).1 = false := by
      have h1 := congrArg (fun l => l.getD C.output false) (lp_fst C hmem (isLf b) zz)
      have h3 : ((linearParts C (isLf b) zz).map Prod.fst).getD C.output false =
          ((linearParts C (isLf b) zz).getD C.output (false, false)).1 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (linearParts C (isLf b) zz)[C.output]? <;> simp
      rw [← h3, h1, init_fst]
      have h4 := hE (yf b)
      unfold Circuit.eval at h4
      rw [h4]
      cases b <;> decide
    have hsnd : ((linearParts C (isLf b) zz).getD (if C.output = 1 then 2 else 1)
        (false, false)).1 = false := by
      rw [lp_eq, gd_prefix _ _ _ _ _ (by rw [init_len]; omega)]
      exact init_small b _ hs3 hs0
    have e1 : 14 + C.size + 1 = (linearParts C (isLf b) zz ++
        [lpStep (linearParts C (isLf b) zz) ⟨GateOp.or, [C.output,
          if C.output = 1 then 2 else 1]⟩]).length := by simp [hPl]
    rw [e1, gd_last]
    simp only [lpStep, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [gd_left _ _ _ _ (by omega), ← hPl, gd_last]
    simp only [List.any_cons, List.any_nil, hfst, hsnd]
    simp
