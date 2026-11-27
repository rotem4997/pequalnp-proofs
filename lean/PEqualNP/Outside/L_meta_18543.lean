import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18543_aux

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

private def evalOne (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem gate_eq {n : Nat} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) (j : Nat) (hj : j < C.gates.length) :
    wval C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have h := fw_getD_gate evalOne C.gates (List.ofFn x) j hj false
  simp only [List.length_ofFn] at h
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  change (fw evalOne C.gates (List.ofFn x)).getD (n+j) false = _
  rw [h]
  unfold evalOne
  rw [← hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_take', if_pos (ao.2.1 j hj i hi)]
  rfl

private theorem input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : Fin n) : wval C x a.val = x a := by
  obtain ⟨r,hr⟩ := fw_prefix evalOne C.gates (List.ofFn x)
  change (fw evalOne C.gates (List.ofFn x)).getD a.val false = _
  rw [hr,getD_append_left' _ _ _ _ (by simpa using a.isLt)]
  simp [List.getD_eq_getElem?_getD,a.isLt]

open PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.HeptadCover

private lemma read_old (D : Circuit) (G : List Gate) (o : ℕ) (x : Fin 26 → Bool) (i : ℕ)
    (hi : i < 26 + D.size) :
    wireValue ⟨D.gates ++ G,o⟩ 26 x i = wireValue D 26 x i := by
  change (fw evalOne (D.gates ++ G) (List.ofFn x)).getD i false = _
  rw [fw_append]
  obtain ⟨t,e⟩ := fw_prefix evalOne G (fw evalOne D.gates (List.ofFn x))
  rw [e,getD_append_left' _ _ _ _ (by simpa [fw_length,Circuit.size] using hi)]
  rfl

private lemma extend (D : Circuit) (G : List Gate) (o : ℕ) (base : IsAO2 26 D)
    (ops : ∀ g ∈ G, g.op = .and ∨ g.op = .or)
    (size : ∀ g ∈ G, g.inputs.length = 2)
    (back : ∀ (j : ℕ) (hj : j < G.length), ∀ i ∈ G[j].inputs, i < 26+D.size+j) :
    IsAO2 26 ⟨D.gates ++ G,o⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (base.1 g) (ops g)
  · intro j hj i hi
    have jgood : j < (D.gates ++ G).length := hj
    rw [show gateAt ⟨D.gates ++ G,o⟩ j = (D.gates ++ G)[j] from by
      change (D.gates ++ G).getD j _ = _
      rw [List.getD_eq_getElem?_getD,getElem?_pos (D.gates ++ G) j jgood,Option.getD_some]] at hi
    by_cases before : j < D.gates.length
    · rw [List.getElem_append_left before] at hi
      apply base.2.1 j before i
      simpa [gateAt,List.getD_eq_getElem?_getD,before] using hi
    · rw [List.getElem_append_right (by omega : D.gates.length ≤ j)] at hi
      have h := back (j-D.gates.length) (by simp at hj; omega) i hi
      simp only [Circuit.size] at h
      omega
  · intro g hg
    exact (List.mem_append.mp hg).elim (base.2.2 g) (size g)

private lemma read_gate (D : Circuit) (G : List Gate) (o j a b : ℕ) (op : GateOp)
    (legal : IsAO2 26 ⟨D.gates ++ G,o⟩) (hj : j < G.length) (e : G[j] = ⟨op,[a,b]⟩)
    (x : Fin 26 → Bool) :
    wireValue ⟨D.gates ++ G,o⟩ 26 x (26+D.size+j) =
      op.eval [wireValue ⟨D.gates ++ G,o⟩ 26 x a,wireValue ⟨D.gates ++ G,o⟩ 26 x b] := by
  let C : Circuit := ⟨D.gates ++ G,o⟩
  have hi : D.size+j < C.gates.length := by simp [C,Circuit.size]; omega
  have hg : gateAt C (D.size+j) = ⟨op,[a,b]⟩ := by
    rw [show gateAt C (D.size+j) = C.gates[D.size+j] from by
      simp [gateAt,List.getD_eq_getElem?_getD,hi]]
    change (D.gates ++ G)[D.size+j] = _
    rw [List.getElem_append_right (show D.gates.length ≤ D.size+j from Nat.le_add_right ..)]
    simpa only [Circuit.size,Nat.add_sub_cancel_left] using e
  have h := gate_eq legal x (D.size+j) hi
  rw [hg] at h
  simpa only [PEqualNP.BlindGate.wireValue,wval,Nat.add_assoc,List.map_cons,List.map_nil] using h

private theorem finish : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →       x1.output < (26 : ℕ) + x1.size →         (∀ x6 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x6 < (26 : ℕ) + x1.size ∧ x2 x6 ≠ ↑x6) →           ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) (x9 : ℕ) (x10 : ℕ),             x7.size ≤ x1.size + (14 : ℕ) ∧               PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧                 (∀ x11 ∈ x7.gates, x11.inputs.Nodup) ∧                   x7.output = (26 : ℕ) + x8 ∧                     x7.gates[x8]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } ∧                       ∀ (x11 : Fin (26 : ℕ) → Bool),                         have x12 : Bool := Decidable.decide (∃ x12 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true);                         have x13 : Bool := Decidable.decide (∃ x13 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 (x2 x13) = Bool.true);                         have x14 : Bool := x1.eval (List.ofFn x11);                         PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x9 = (x14 || x12) ∧ PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x10 = (x14 || x13 || x11 (13 : Fin (26 : ℕ))) := by
  intro D d ao distinct out ports
  have at0 := ports 0 (by decide)
  have at1 := ports 1 (by decide)
  have at3 := ports 3 (by decide)
  have at9 := ports 9 (by decide)
  let k := 26+D.size
  let G : List Gate := [⟨.or,[0,1]⟩, ⟨.or,[3,9]⟩, ⟨.or,[k,k+1]⟩, ⟨.and,[0,d 0]⟩, ⟨.and,[1,d 1]⟩, ⟨.and,[3,d 3]⟩, ⟨.and,[9,d 9]⟩, ⟨.or,[k+3,k+4]⟩, ⟨.or,[k+5,k+6]⟩, ⟨.or,[k+7,k+8]⟩, ⟨.or,[D.output,k+2]⟩, ⟨.or,[D.output,k+9]⟩, ⟨.or,[k+11,13]⟩, ⟨.and,[k+10,k+12]⟩]
  let C : Circuit := ⟨D.gates ++ G,k+13⟩
  have len : G.length = 14 := rfl
  have legal : IsAO2 26 C := by
    apply extend D G _ ao
    · intro g hg
      simp only [G,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro g hg
      simp only [G,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro j hj
      have h : j < 14 := by simpa only [len] using hj
      interval_cases j <;> simp [G,List.mem_cons] <;> omega
  refine ⟨C,D.size+13,k+10,k+12,by simp [C,Circuit.size,len],legal,?_,by simp [C,k,Nat.add_assoc],?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old|new
    · exact distinct g old
    · simp only [G,List.mem_cons,List.not_mem_nil,or_false] at new
      rcases new with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k] <;> omega
  · change (D.gates ++ G)[D.size+13]? = _
    rw [List.getElem?_append_right (show D.gates.length ≤ D.size+13 from Nat.le_add_right ..)]
    simp only [Circuit.size,Nat.add_sub_cancel_left]
    rfl
  · intro x
    have old (i : ℕ) (hi : i < k) : wireValue C 26 x i = wireValue D 26 x i :=
      read_old D G _ x i hi
    have inp (i : Fin 26) : wireValue C 26 x i.val = x i := input C x i
    have g0 : wireValue C 26 x (k+0) = GateOp.or.eval [wireValue C 26 x (0),wireValue C 26 x (1)] :=
      read_gate D G _ 0 (0) (1) .or legal (by rw [len]; decide) rfl x
    have g1 : wireValue C 26 x (k+1) = GateOp.or.eval [wireValue C 26 x (3),wireValue C 26 x (9)] :=
      read_gate D G _ 1 (3) (9) .or legal (by rw [len]; decide) rfl x
    have g2 : wireValue C 26 x (k+2) = GateOp.or.eval [wireValue C 26 x (k),wireValue C 26 x (k+1)] :=
      read_gate D G _ 2 (k) (k+1) .or legal (by rw [len]; decide) rfl x
    have g3 : wireValue C 26 x (k+3) = GateOp.and.eval [wireValue C 26 x (0),wireValue C 26 x (d 0)] :=
      read_gate D G _ 3 (0) (d 0) .and legal (by rw [len]; decide) rfl x
    have g4 : wireValue C 26 x (k+4) = GateOp.and.eval [wireValue C 26 x (1),wireValue C 26 x (d 1)] :=
      read_gate D G _ 4 (1) (d 1) .and legal (by rw [len]; decide) rfl x
    have g5 : wireValue C 26 x (k+5) = GateOp.and.eval [wireValue C 26 x (3),wireValue C 26 x (d 3)] :=
      read_gate D G _ 5 (3) (d 3) .and legal (by rw [len]; decide) rfl x
    have g6 : wireValue C 26 x (k+6) = GateOp.and.eval [wireValue C 26 x (9),wireValue C 26 x (d 9)] :=
      read_gate D G _ 6 (9) (d 9) .and legal (by rw [len]; decide) rfl x
    have g7 : wireValue C 26 x (k+7) = GateOp.or.eval [wireValue C 26 x (k+3),wireValue C 26 x (k+4)] :=
      read_gate D G _ 7 (k+3) (k+4) .or legal (by rw [len]; decide) rfl x
    have g8 : wireValue C 26 x (k+8) = GateOp.or.eval [wireValue C 26 x (k+5),wireValue C 26 x (k+6)] :=
      read_gate D G _ 8 (k+5) (k+6) .or legal (by rw [len]; decide) rfl x
    have g9 : wireValue C 26 x (k+9) = GateOp.or.eval [wireValue C 26 x (k+7),wireValue C 26 x (k+8)] :=
      read_gate D G _ 9 (k+7) (k+8) .or legal (by rw [len]; decide) rfl x
    have g10 : wireValue C 26 x (k+10) = GateOp.or.eval [wireValue C 26 x (D.output),wireValue C 26 x (k+2)] :=
      read_gate D G _ 10 (D.output) (k+2) .or legal (by rw [len]; decide) rfl x
    have g11 : wireValue C 26 x (k+11) = GateOp.or.eval [wireValue C 26 x (D.output),wireValue C 26 x (k+9)] :=
      read_gate D G _ 11 (D.output) (k+9) .or legal (by rw [len]; decide) rfl x
    have g12 : wireValue C 26 x (k+12) = GateOp.or.eval [wireValue C 26 x (k+11),wireValue C 26 x (13)] :=
      read_gate D G _ 12 (k+11) (13) .or legal (by rw [len]; decide) rfl x
    have hpts : singerLines3 (0 : Fin 13) = {0,1,3,9} := by decide
    have oldout : wireValue C 26 x D.output = D.eval (List.ofFn x) := old _ out
    have i0 : wireValue C 26 x 0 = x 0 := inp 0
    have i1 : wireValue C 26 x 1 = x 1 := inp 1
    have i3 : wireValue C 26 x 3 = x 3 := inp 3
    have i9 : wireValue C 26 x 9 = x 9 := inp 9
    have i13 : wireValue C 26 x 13 = x 13 := inp 13
    have gz : wireValue C 26 x k = (x 0 || x 1) := by
      simpa only [Nat.add_zero,i0,i1,GateOp.eval,List.any_cons,List.any_nil,id,Bool.or_false] using g0
    have decFour (f : Fin 13 → Bool) :
        decide (∃ i ∈ singerLines3 (0 : Fin 13), f i = true) = (f 0 || f 1 || f 3 || f 9) := by
      apply Bool.eq_iff_iff.mpr
      simp only [hpts,Finset.mem_insert,Finset.mem_singleton,decide_eq_true_eq,Bool.or_eq_true]
      constructor
      · rintro ⟨i, rfl | rfl | rfl | rfl, h⟩ <;> tauto
      · intro h
        rcases h with ((h|h)|h)|h
        · exact ⟨0,by simp,h⟩
        · exact ⟨1,by simp,h⟩
        · exact ⟨3,by simp,h⟩
        · exact ⟨9,by simp,h⟩
    have dh := decFour (fun i => x (Fin.castAdd 13 i))
    have dy := decFour (fun i => x (Fin.castAdd 13 i) && wireValue D 26 x (d i))
    simp only [Bool.and_eq_true] at dy
    rw [dh,dy]
    simp only [gz,g12,g11,g10,g9,g8,g7,g6,g5,g4,g3,g2,g1,oldout,i0,i1,i3,i9,i13,
      old _ at0.1,old _ at1.1,old _ at3.1,old _ at9.1,GateOp.eval,List.any_cons,List.any_nil,
      List.all_cons,List.all_nil,id,Bool.or_false,Bool.and_true]
    constructor <;> ac_rfl
end PEqualNP.Outside.L_meta_18543_aux

open PEqualNP.Outside.L_meta_18543_aux in
theorem PEqualNP.Outside.L_meta_18543 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →       x1.output < (26 : ℕ) + x1.size →         (∀ x6 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x6 < (26 : ℕ) + x1.size ∧ x2 x6 ≠ ↑x6) →           ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) (x9 : ℕ) (x10 : ℕ),             x7.size ≤ x1.size + (14 : ℕ) ∧               PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧                 (∀ x11 ∈ x7.gates, x11.inputs.Nodup) ∧                   x7.output = (26 : ℕ) + x8 ∧                     x7.gates[x8]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } ∧                       ∀ (x11 : Fin (26 : ℕ) → Bool),                         have x12 : Bool := Decidable.decide (∃ x12 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true);                         have x13 : Bool := Decidable.decide (∃ x13 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 (x2 x13) = Bool.true);                         have x14 : Bool := x1.eval (List.ofFn x11);                         PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x9 = (x14 || x12) ∧ PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x10 = (x14 || x13 || x11 (13 : Fin (26 : ℕ)))) := finish
