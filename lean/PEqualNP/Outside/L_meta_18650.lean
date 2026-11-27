import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18650_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def remapWire (w : ℕ) : ℕ :=
  match w with
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 8
  | 6 => 9
  | 7 => 11
  | 8 => 12
  | 9 => 13
  | 10 => 14
  | 11 => 15
  | 12 => 16
  | 13 => 17
  | 14 => 18
  | 15 => 19
  | 16 => 20
  | n + 17 => n + 21

def remapGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map remapWire⟩

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wstep x

theorem run_len (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run, List.foldl_cons]
    change (run gs (wstep x g)).length = _
    rw [ih]; simp [wstep]; omega

theorem getD_snoc_lt (a : List Bool) (v : Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ [v]).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (a : List Bool) (v : Bool) :
    (a ++ [v]).getD a.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right_add (a b : List Bool) (i : ℕ) :
    (a ++ b).getD (a.length + i) false = b.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem run_remap (gs : List Gate) (xc xb : List Bool)
    (hxc : xc.length = 17) (hxb : xb.length = 21)
    (hmatch : ∀ i < 17, xb.getD (remapWire i) false = xc.getD i false) :
    ∀ w, (run (gs.map remapGate) xb).getD (remapWire w) false = (run gs xc).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, run, List.foldl_nil]
    by_cases hw : w < 17
    · exact hmatch w hw
    · have hge1 : 17 ≤ w := Nat.le_of_not_lt hw
      obtain ⟨k, rfl⟩ : ∃ k, w = k + 17 := ⟨w - 17, by omega⟩
      have hr : remapWire (k + 17) = k + 21 := rfl
      rw [hr, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton]
    have hL : run (gs.map remapGate ++ [remapGate g]) xb = wstep (run (gs.map remapGate) xb) (remapGate g) := by
      simp [run, List.foldl_append]
    have hR : run (gs ++ [g]) xc = wstep (run gs xc) g := by
      simp [run, List.foldl_append]
    rw [hL, hR]
    have hlc : (run gs xc).length = 17 + gs.length := by rw [run_len, hxc]
    have hlb : (run (gs.map remapGate) xb).length = 21 + gs.length := by rw [run_len, hxb, List.length_map]
    have hval : (remapGate g).op.eval ((remapGate g).inputs.map fun i => (run (gs.map remapGate) xb).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs xc).getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hw : w < 17 + gs.length
    · have hrlt : remapWire w < 21 + gs.length := by
        cases w with
        | zero => simp [remapWire]; omega
        | succ w1 =>
          match w1 with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => simp [remapWire]; omega
          | k + 16 =>
            have : remapWire (k + 17) = k + 21 := rfl
            rw [this]; omega
      rw [wstep, wstep, getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = 17 + gs.length
      · subst heq
        have hr : remapWire (17 + gs.length) = 21 + gs.length := by
          have : 17 + gs.length = gs.length + 17 := by omega
          rw [this]; simp [remapWire]; omega
        rw [wstep, wstep, hr, ← hlb, getD_snoc_eq, ← hlc, getD_snoc_eq, hval]
      · have hgt : 17 + gs.length < w := by omega
        obtain ⟨k, rfl⟩ : ∃ k, w = k + 17 := ⟨w - 17, by omega⟩
        have hr : remapWire (k + 17) = k + 21 := rfl
        rw [wstep, wstep, hr,
          List.getD_eq_default _ _ (by simp [hlb]; omega),
          List.getD_eq_default _ _ (by simp [hlc]; omega)]

def extra15 (s cout : ℕ) : List Gate :=
  [ ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [21 + s, 21 + s + 1]⟩,
    ⟨GateOp.and, [0, 21 + s + 2]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [21 + s + 4, 21 + s + 5]⟩,
    ⟨GateOp.and, [2, 21 + s + 6]⟩,
    ⟨GateOp.or, [10, 16]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.or, [21 + s + 8, 21 + s + 9]⟩,
    ⟨GateOp.and, [7, 21 + s + 10]⟩,
    ⟨GateOp.or, [21 + s + 3, 21 + s + 7]⟩,
    ⟨GateOp.or, [21 + s + 12, 21 + s + 11]⟩,
    ⟨GateOp.or, [cout, 21 + s + 13]⟩ ]

theorem eval_extra15 (ws : List Bool) (s cout : ℕ) (hlen : ws.length = 21 + s) (hcout : cout < 21 + s) :
    let v := fun i => ws.getD i false
    (run (extra15 s cout) ws).getD (21 + s + 14) false =
      (v cout || (((v 0 && ((v 9 || v 10) || (v 14 || v 20))) ||
                   (v 2 && ((v 10 || v 12) || (v 13 || v 17)))) ||
                  (v 7 && ((v 10 || v 16) || (v 18 || v 19))))) := by
  dsimp only
  simp only [extra15, run, List.foldl_cons, List.foldl_nil, wstep, GateOp.eval,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append, id_eq]
  have hlt : ∀ (L : List Bool) (i : ℕ), i < 21 + s → (ws ++ L).getD i false = ws.getD i false := by
    intro L i hi; exact getD_append_left_lt ws L i (by omega)
  have hge : ∀ (L : List Bool) (k : ℕ), (ws ++ L).getD (21 + s + k) false = L.getD k false := by
    intro L k; rw [← hlen]; exact getD_append_right_add ws L k
  have hge0 : ∀ (L : List Bool), (ws ++ L).getD (21 + s) false = L.getD 0 false := by
    intro L; simpa using hge L 0
  simp only [hlt _ 0 (by omega), hlt _ 2 (by omega), hlt _ 7 (by omega), hlt _ 9 (by omega),
    hlt _ 10 (by omega), hlt _ 12 (by omega), hlt _ 13 (by omega), hlt _ 14 (by omega),
    hlt _ 16 (by omega), hlt _ 17 (by omega), hlt _ 18 (by omega), hlt _ 19 (by omega),
    hlt _ 20 (by omega), hlt _ cout hcout, hge0, hge, List.getD_cons_zero, List.getD_cons_succ]

theorem run_keep_lt (gs : List Gate) (base : List Bool) (i : ℕ) (hi : i < base.length) :
    (run gs base).getD i false = base.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (wstep (run gs base) g).getD i false = _
    rw [wstep, getD_snoc_lt _ _ i (by rw [run_len]; omega)]
    exact ih

def idxB : List (Fin 26) :=
  List.filter (fun i : Fin 26 => decide (i.val ∉ ([0, 1, 3, 9, 13] : List ℕ))) (List.finRange 26)

def idxC : List (Fin 26) :=
  List.filter (fun i : Fin 26 => decide (i.val ∉ ([0, 1, 2, 3, 5, 9, 11, 13, 15] : List ℕ))) (List.finRange 26)

theorem idxB_eq : idxB = [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by decide
theorem idxC_eq : idxC = [4, 6, 7, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by decide

theorem main_proof :
    ∀ (C : Circuit), Monotone2 C → C.output < 17 + C.size →
      ∃ B : Circuit, Monotone2 B ∧ B.output < 21 + B.size ∧ B.size ≤ C.size + 15 ∧
        ∀ x : Fin 26 → Bool,
          B.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0, 1, 3, 9, 13] : List ℕ))) (List.finRange 26)).map x) =
            (C.eval ((List.filter (fun i : Fin 26 => decide (i.val ∉ ([0, 1, 2, 3, 5, 9, 11, 13, 15] : List ℕ))) (List.finRange 26)).map x) ||
              (((x 2 && ((x 14 || x 15) || (x 19 || x 25))) ||
                (x 5 && ((x 15 || x 17) || (x 18 || x 22)))) ||
               (x 11 && ((x 15 || x 21) || (x 23 || x 24))))) := by
  intro C hmono hout
  set s := C.gates.length with hs_def
  let cout := remapWire C.output
  let B : Circuit := ⟨C.gates.map remapGate ++ extra15 s cout, 21 + s + 14⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · rw [List.mem_map] at hg1
      obtain ⟨g', hg', rfl⟩ := hg1
      obtain ⟨hop, hlen⟩ := hmono g' hg'
      exact ⟨hop, by simpa [remapGate] using hlen⟩
    · simp only [extra15, List.mem_cons, List.not_mem_nil, or_false] at hg2
      rcases hg2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp, by simp⟩
  · simp [B, Circuit.size, extra15, hs_def]; omega
  · simp [B, Circuit.size, extra15, hs_def]
  · intro x
    change (run (C.gates.map remapGate ++ extra15 s cout) (idxB.map x)).getD (21 + s + 14) false = _
    have hfold : run (C.gates.map remapGate ++ extra15 s cout) (idxB.map x) =
        run (extra15 s cout) (run (C.gates.map remapGate) (idxB.map x)) := List.foldl_append
    rw [hfold]
    have hblen : (idxB.map x).length = 21 := by rw [idxB_eq]; rfl
    have hclen : (idxC.map x).length = 17 := by rw [idxC_eq]; rfl
    have hwslen : (run (C.gates.map remapGate) (idxB.map x)).length = 21 + s := by
      rw [run_len, hblen, List.length_map, hs_def]
    have hcout_lt : cout < 21 + s := by
      simp only [Circuit.size] at hout
      dsimp only [cout]
      match hc : C.output with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => simp [remapWire]; omega
      | k + 17 =>
        have : remapWire (k + 17) = k + 21 := rfl
        rw [this]; rw [hc] at hout; omega
    rw [eval_extra15 _ s cout hwslen hcout_lt]
    dsimp only
    have hmatch : ∀ i < 17, (idxB.map x).getD (remapWire i) false = (idxC.map x).getD i false := by
      intro i hi
      rw [idxB_eq, idxC_eq]
      interval_cases i <;> rfl
    have hrem := run_remap C.gates (idxC.map x) (idxB.map x) hclen hblen hmatch C.output
    have hv_cout : (run (C.gates.map remapGate) (idxB.map x)).getD cout false = C.eval (idxC.map x) := hrem
    have hkeep : ∀ i < 21, (run (C.gates.map remapGate) (idxB.map x)).getD i false = (idxB.map x).getD i false :=
      fun i hi => run_keep_lt _ _ i (by omega)
    rw [hv_cout, hkeep 0 (by decide), hkeep 2 (by decide), hkeep 7 (by decide),
      hkeep 9 (by decide), hkeep 10 (by decide), hkeep 12 (by decide), hkeep 13 (by decide),
      hkeep 14 (by decide), hkeep 16 (by decide), hkeep 17 (by decide), hkeep 18 (by decide),
      hkeep 19 (by decide), hkeep 20 (by decide)]
    rw [idxB_eq]
    rfl

end PEqualNP.Outside.L_meta_18650_aux

theorem PEqualNP.Outside.L_meta_18650 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (17 : ℕ) + x1.size → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.output < (21 : ℕ) + x4.size ∧ x4.size ≤ x1.size + (15 : ℕ) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)))) = (x1.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ), (13 : ℕ), (15 : ℕ)])) (List.finRange (26 : ℕ)))) || (x5 (2 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (15 : Fin (26 : ℕ)) || (x5 (19 : Fin (26 : ℕ)) || x5 (25 : Fin (26 : ℕ)))) || x5 (5 : Fin (26 : ℕ)) && (x5 (15 : Fin (26 : ℕ)) || x5 (17 : Fin (26 : ℕ)) || (x5 (18 : Fin (26 : ℕ)) || x5 (22 : Fin (26 : ℕ)))) || x5 (11 : Fin (26 : ℕ)) && (x5 (15 : Fin (26 : ℕ)) || x5 (21 : Fin (26 : ℕ)) || (x5 (23 : Fin (26 : ℕ)) || x5 (24 : Fin (26 : ℕ)))))))  := by
  exact PEqualNP.Outside.L_meta_18650_aux.main_proof
