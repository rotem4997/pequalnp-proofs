import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7177

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run {α : Type} (step : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [step g w]) init

theorem run_cons {α : Type} (step : Gate → List α → α) (g : Gate) (gs : List Gate) (init : List α) :
    run step (g :: gs) init = run step gs (init ++ [step g init]) := rfl

theorem run_append {α : Type} (step : Gate → List α → α) (gs1 gs2 : List Gate) (init : List α) :
    run step (gs1 ++ gs2) init = run step gs2 (run step gs1 init) := by
  unfold run; rw [List.foldl_append]

theorem run_length {α : Type} (step : Gate → List α → α) :
    ∀ (gs : List Gate) (init : List α), (run step gs init).length = init.length + gs.length
  | [], init => by simp [run]
  | g :: gs, init => by
    rw [run_cons, run_length step gs]; simp only [List.length_append, List.length_cons,
      List.length_nil]; omega

theorem run_prefix {α : Type} (step : Gate → List α → α) :
    ∀ (gs : List Gate) (init : List α), init <+: run step gs init
  | [], init => by simp [run]
  | g :: gs, init => by
    rw [run_cons]; exact (List.prefix_append init [step g init]).trans (run_prefix step gs _)

theorem gD_out {α : Type} {l : List α} {i : ℕ} (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem gD_pre {α : Type} {l1 l2 : List α} (h : l1 <+: l2) {i : ℕ} (hi : i < l1.length) (d : α) :
    l2.getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (lt_of_lt_of_le hi h.length_le), h.getElem hi]

def Good {α : Type} (step : Gate → List α → α) (d : α) : Prop :=
  ∀ (g g' : Gate) (w w' : List α), g'.op = g.op →
    (g'.inputs.map fun i => w'.getD i d) = (g.inputs.map fun i => w.getD i d) → step g' w' = step g w

def fixG (j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map fun i => if i < 26 + j then i else 89⟩

def fixL : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => fixG j g :: fixL (j + 1) gs

theorem fixL_length : ∀ (j : ℕ) (gs : List Gate), (fixL j gs).length = gs.length
  | _, [] => rfl
  | j, g :: gs => by simp [fixL, fixL_length (j + 1) gs]

theorem run_fixL {α : Type} (step : Gate → List α → α) (d : α) (hs : Good step d) :
    ∀ (gs : List Gate) (j : ℕ) (init : List α), init.length = 26 + j → j + gs.length ≤ 63 →
      run step (fixL j gs) init = run step gs init
  | [], _, _, _, _ => rfl
  | g :: gs, j, init, hl, hle => by
    simp only [List.length_cons] at hle
    have hstep : step (fixG j g) init = step g init := by
      apply hs g (fixG j g) init init rfl
      simp only [fixG, List.map_map]
      apply List.map_congr_left
      intro i _
      dsimp only [Function.comp_apply]
      split_ifs with h
      · rfl
      · rw [gD_out d (by omega), gD_out d (by omega)]
    show run step (fixG j g :: fixL (j + 1) gs) init = run step (g :: gs) init
    rw [run_cons, run_cons, hstep]
    exact run_fixL step d hs gs (j + 1) _ (by simp [hl]; omega) (by omega)

theorem ok_fixL : ∀ (gs : List Gate) (j : ℕ), ∀ p ∈ (fixL j gs).zipIdx j,
    ∀ i ∈ p.1.inputs, i < 26 + p.2 ∨ i = 89
  | [], j => by simp [fixL]
  | g :: gs, j => by
    intro p hp i hi
    simp only [fixL, List.zipIdx_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only [fixG, List.mem_map] at hi
      obtain ⟨a, _, rfl⟩ := hi
      dsimp only
      split_ifs with h
      · left; exact h
      · right; rfl
    · exact ok_fixL gs (j + 1) p hp i hi

theorem mem_fixL : ∀ (gs : List Gate) (j : ℕ) (g' : Gate), g' ∈ fixL j gs →
    ∃ g ∈ gs, g'.op = g.op ∧ g'.inputs.length = g.inputs.length
  | [], _, _, h => by simp [fixL] at h
  | g :: gs, j, g', h => by
    simp only [fixL, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨g, by simp, rfl, by simp [fixG]⟩
    · obtain ⟨g0, hg0, h1, h2⟩ := mem_fixL gs (j + 1) g' h
      exact ⟨g0, List.mem_cons_of_mem _ hg0, h1, h2⟩

def pad : Gate := ⟨GateOp.or, []⟩

theorem key {α : Type} (step : Gate → List α → α) (d : α) (hs : Good step d) (A B : List Gate)
    (g : Gate) (init : List α) (hinit : init.length = 26) (hk : A.length ≤ 62) :
    (run step (fixL 0 A ++ List.replicate (62 - A.length) pad ++ [fixG A.length g]) init).getD 88 d
      = (run step (A ++ g :: B) init).getD (26 + A.length) d := by
  have hR0l : (run step A init).length = 26 + A.length := by rw [run_length, hinit]
  have hfix : run step (fixL 0 A) init = run step A init :=
    run_fixL step d hs A 0 init (by simp [hinit]) (by omega)
  have hRl : (run step (List.replicate (62 - A.length) pad) (run step A init)).length = 88 := by
    rw [run_length, hR0l, List.length_replicate]; omega
  have hpre : run step A init <+: run step (List.replicate (62 - A.length) pad) (run step A init) :=
    run_prefix step _ _
  have hL : run step (fixL 0 A ++ List.replicate (62 - A.length) pad ++ [fixG A.length g]) init
      = run step (List.replicate (62 - A.length) pad) (run step A init) ++
        [step (fixG A.length g) (run step (List.replicate (62 - A.length) pad) (run step A init))] := by
    rw [run_append, run_append, hfix]; rfl
  have hRt : run step (A ++ g :: B) init
      = run step B (run step A init ++ [step g (run step A init)]) := by
    rw [run_append, run_cons]
  rw [hL, hRt]
  have e1 := hRl
  generalize run step (List.replicate (62 - A.length) pad) (run step A init) = R at e1 hpre ⊢
  generalize run step A init = R0 at hR0l hpre ⊢
  have e2 : (run step B (R0 ++ [step g R0])).getD (26 + A.length) d = step g R0 := by
    rw [gD_pre (run_prefix step B _) (by simp [hR0l])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hR0l]
  have e3 : (R ++ [step (fixG A.length g) R]).getD 88 d = step (fixG A.length g) R := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [e1]
  rw [e2, e3]
  apply hs g (fixG A.length g) R0 R rfl
  simp only [fixG, List.map_map]
  apply List.map_congr_left
  intro i _
  dsimp only [Function.comp_apply]
  split_ifs with h
  · exact gD_pre hpre (by omega) d
  · rw [gD_out d (by omega), gD_out d (by omega)]

def stepW : Gate → List Bool → Bool := fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

def stepD : Gate → List ℕ → ℕ := fun g w => g.lineDegree w

theorem goodW : Good stepW false := by
  intro g g' w w' hop hm
  simp only [stepW]
  rw [hop, hm]

theorem goodD : Good stepD 0 := by
  intro g g' w w' hop hm
  simp only [stepD, Gate.lineDegree]
  rw [hop, hm]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run stepW C.gates x := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (m : Finset ℕ) :
    C.lineDegrees n m = run stepD C.gates ((List.range n).map fun i => if i ∈ m then 1 else 0) := rfl

theorem inp : ∀ o : ℕ, o < 26 →
    (List.ofFn (fun x5 : Fin 26 => Fin.addCases (m := 13) (n := 13)
      (fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) (fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) x5)).getD o false = true →
    (List.ofFn (fun x5 : Fin 26 => Fin.addCases (m := 13) (n := 13)
      (fun x6 : Fin 13 => decide (x6 = (1 : Fin 13))) (fun x6 : Fin 13 => decide (x6 = (1 : Fin 13))) x5)).getD o false = true →
    False := by
  decide

end PEqualNP.Outside.L_meta_7177

open PEqualNP.Outside.L_meta_7177 in
theorem PEqualNP.Outside.L_meta_7177 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (63 : ℕ) → (∀ (x4 : Fin (13 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) x5) = Bool.true) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = (63 : ℕ) ∧ x5.output = (88 : ℕ) ∧ (∀ x6 ∈ x5.gates.zipIdx, ∀ x8 ∈ x6.1.inputs, x8 < (26 : ℕ) + x6.2 ∨ x8 = (89 : ℕ)) ∧ (∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x6) ∧ ∀ (x6 : Finset ℕ), x5.lineDeg (26 : ℕ) x6 = x1.lineDeg (26 : ℕ) x6 := by
  intro x1 hmono hsize hpt
  have hout_lt : x1.output < 26 + x1.gates.length := by
    by_contra hc
    push_neg at hc
    have h0 := hpt 0
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval at h0
    rw [gD_out false (by rw [wires_eq, run_length, List.length_ofFn]; omega)] at h0
    exact Bool.false_ne_true h0
  have hout_ge : 26 ≤ x1.output := by
    by_contra hc
    push_neg at hc
    have h0 := hpt 0
    have h1 := hpt 1
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval at h0 h1
    rw [wires_eq, gD_pre (run_prefix _ _ _) (by rw [List.length_ofFn]; omega)] at h0 h1
    exact inp x1.output hc h0 h1
  have hk : x1.output - 26 < x1.gates.length := by omega
  obtain ⟨A, g, B, hsplit, hAl⟩ : ∃ (A : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (B : List PEqualNP.CircuitLowerBounds.Gate),
      x1.gates = A ++ g :: B ∧ A.length = x1.output - 26 := by
    refine ⟨x1.gates.take (x1.output - 26), x1.gates[x1.output - 26],
      x1.gates.drop (x1.output - 26 + 1), ?_, ?_⟩
    · rw [List.getElem_cons_drop_succ_eq_drop, List.take_append_drop]
    · simp only [List.length_take]; omega
  have hout_eq : x1.output = 26 + A.length := by omega
  have hsz : x1.gates.length ≤ 63 := hsize
  have hAle : A.length ≤ 62 := by
    rw [hsplit] at hsz; simp only [List.length_append, List.length_cons] at hsz; omega
  refine ⟨⟨fixL 0 A ++ List.replicate (62 - A.length) pad ++ [fixG A.length g], 88⟩,
    ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hg'
    rcases hg' with (h | ⟨_, rfl⟩) | rfl
    · obtain ⟨g0, hg0, h1, h2⟩ := mem_fixL A 0 g' h
      have := hmono g0 (by rw [hsplit]; simp [hg0])
      rw [h1, h2]; exact this
    · simp [pad]
    · have := hmono g (by rw [hsplit]; simp)
      simp only [fixG, List.length_map]; exact this
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, fixL_length,
      List.length_replicate, List.length_singleton]
    omega
  · intro p hp i hi
    rw [List.zipIdx_append, List.zipIdx_append, List.mem_append, List.mem_append] at hp
    rcases hp with (h | h) | h
    · exact ok_fixL A 0 p h i hi
    · have hp1 := List.fst_mem_of_mem_zipIdx h
      rw [List.mem_replicate] at hp1
      rw [hp1.2] at hi
      simp [pad] at hi
    · simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_singleton] at h
      subst h
      simp only [fixG, List.mem_map] at hi
      obtain ⟨a, _, rfl⟩ := hi
      dsimp only
      split_ifs with h
      · left
        simp only [List.length_append, fixL_length, List.length_replicate]
        omega
      · right; rfl
  · intro x6
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [wires_eq, wires_eq, hsplit, hout_eq]
    exact key stepW false goodW A B g _ (List.length_ofFn) hAle
  · intro m
    unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg
    rw [ld_eq, ld_eq, hsplit, hout_eq]
    exact key stepD 0 goodD A B g _ (by simp) hAle
