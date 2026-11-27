import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.ReadTwo PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_6066_84
    (shared : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      let V := fun A : Finset ℕ => wval C (indW 26 A)
      let M := fun w => V {0,13} w = true ∧ V {0} w = false ∧ V {13} w = false
      let I := fun j => (gateAt C j).inputs
      let path := Relation.ReflTransGen (fun a b : ℕ => ∃ i, b = 26+i ∧ a ∈ I i ∧ V {0,13} a = true ∧ V {0,13} b = true)
      let root := fun i => isAnd C i ∧ M (26+i) ∧ ∀ a ∈ I i, ¬ M a
      let fork := fun z j => isAnd C j ∧ M (26+j) ∧ path (26+j) C.output ∧ ∀ a ∈ I j, V {z} a = false
      ∀ (j k : ℕ), j ≠ k → fork 0 j → fork 13 k → (∃ i, root i ∧ i < j ∧ i < k ∧ path (26+i) (26+j) ∧ path (26+i) (26+k)) → False)
    (separate : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
      PEqualNP.ReadK.lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      let V := fun A : Finset ℕ => wval C (indW 26 A)
      let M := fun w => V {0,13} w = true ∧ V {0} w = false ∧ V {13} w = false
      let I := fun j => (gateAt C j).inputs
      let path := Relation.ReflTransGen (fun a b : ℕ => ∃ i, b = 26+i ∧ a ∈ I i ∧ V {0,13} a = true ∧ V {0,13} b = true)
      let root := fun i => isAnd C i ∧ M (26+i) ∧ ∀ a ∈ I i, ¬ M a
      let fork := fun z j => isAnd C j ∧ M (26+j) ∧ path (26+j) C.output ∧ ∀ a ∈ I j, V {z} a = false
      ∀ (j k : ℕ), j ≠ k → fork 0 j → fork 13 k → (∃ r s, r ≠ s ∧ root r ∧ root s ∧ r < j ∧ s < k ∧ path (26+r) (26+j) ∧ path (26+s) (26+k)) → False) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) = Bool.false ∧ x9 {(0 : ℕ)} ((26 : ℕ) + x13) = Bool.false) → False := by
  let gateStep {α : Type} (op : GateOp → List α → α) (dflt : α)
      (ws : List α) (g : Gate) : List α :=
    ws ++ [op g.op (g.inputs.map fun i => ws.getD i dflt)]

  have gateStep_length {α : Type} (op : GateOp → List α → α) (dflt : α) (ws : List α) (g : Gate) :
      (gateStep op dflt ws g).length = ws.length + 1 := by
    simp [gateStep]

  have prefix_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl (gateStep op dflt) ws).getD i dflt = ws.getD i dflt := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by rw [gateStep_length]; omega)]
      simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have wireCount {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) :
      (gs.foldl (gateStep op dflt) ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, gateStep_length, List.length_cons]
      omega

  have indexed_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
      (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
      (gs.foldl (gateStep op dflt) ws).getD (ws.length + j) dflt =
        op g.op (g.inputs.map fun i => (gs.foldl (gateStep op dflt) ws).getD i dflt) := by
    induction gs generalizing ws j with
    | nil => simp at hj
    | cons g0 gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst g0
        rw [Nat.add_zero, List.foldl_cons, prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        have hstep : (gateStep op dflt ws g).getD ws.length dflt =
            op g.op (g.inputs.map fun i => ws.getD i dflt) := by
          simp only [gateStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlt : i < ws.length := by simpa using hback i hi
        rw [prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hidx : ws.length + (j + 1) = (gateStep op dflt ws g0).length + j := by
          rw [gateStep_length]
          omega
        rw [hidx]
        exact ih (gateStep op dflt ws g0) j hj (by simpa only [hidx] using hback)

  let Valid (n : ℕ) (C : Circuit) : Prop :=
    ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

  let val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD i false

  have val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      val C x i = x ⟨i,hi⟩ := by
    have hi' : i < (List.ofFn x).length := by simpa using hi
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = _
    rw [prefix_value _ _ _ _ _ hi', List.getD_eq_getElem _ _ hi', List.getElem_ofFn]

  have val_outside {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
      (hi : n + C.gates.length ≤ i) : val C x i = false := by
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simpa only [wireCount, List.length_ofFn] using hi

  have val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hj : C.gates[j]? = some g) (a b : ℕ) (hg : g.inputs = [a,b])
      (ha : a < n + j) (hb : b < n + j) :
      (g.op = .and → val C x (n + j) = (val C x a && val C x b)) ∧
      (g.op = .or → val C x (n + j) = (val C x a || val C x b)) := by
    have hback : ∀ i ∈ g.inputs, i < (List.ofFn x).length + j := by
      simp only [hg, List.length_ofFn, List.mem_cons, List.not_mem_nil, or_false]
      rintro i (rfl | rfl) <;> assumption
    have hv := indexed_value GateOp.eval false C.gates (List.ofFn x) j g hj hback
    simp only [List.length_ofFn, hg, List.map_cons, List.map_nil] at hv
    constructor
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a && (val C x b && true)) at hv
      simpa only [Bool.and_true] using hv
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a || (val C x b || false)) at hv
      simpa only [Bool.or_false] using hv

  intro C lower upper ao nd computes read0 read13 V T old
  rintro ⟨j,k,distinct,hj,hk,hLj,hPk⟩
  let I (i : ℕ) := (gateAt C i).inputs
  let M (w : ℕ) := V {0,13} w = true ∧ V {0} w = false ∧ V {13} w = false
  let edge := fun a b : ℕ => ∃ i, b = 26+i ∧ a ∈ I i ∧ V {0,13} a = true ∧ V {0,13} b = true
  let path := Relation.ReflTransGen edge
  let root (i : ℕ) := isAnd C i ∧ M (26+i) ∧ ∀ a ∈ I i, ¬ M a
  let fork (z j : ℕ) := isAnd C j ∧ M (26+j) ∧ path (26+j) C.output ∧ ∀ a ∈ I j, V {z} a = false
  have reads (i : ℕ) (hi : i < C.gates.length) :
      ∃ (g : Gate) (a b : ℕ), C.gates[i]? = some g ∧ gateAt C i = g ∧
      g.inputs = [a,b] ∧ a < 26+i ∧ b < 26+i ∧ (g.op = .and ∨ g.op = .or) := by
    let g := C.gates[i]
    have real : C.gates[i]? = some g := List.getElem?_eq_getElem hi
    have atg : gateAt C i = g := by
      change C.gates.getD i ⟨GateOp.or,[]⟩ = g
      simp only [List.getD_eq_getElem?_getD,real,Option.getD_some]
    have mem : g ∈ C.gates := List.getElem_mem hi
    obtain ⟨a,b,h⟩ := List.length_eq_two.mp (ao.2.2 g mem)
    refine ⟨g,a,b,real,atg,h,ao.2.1 i hi a ?_,ao.2.1 i hi b ?_,ao.1 g mem⟩ <;> simp [atg,h]
  have go (a b) (e : T a b) : edge a b := by
    obtain ⟨i,g,r,s,real,eqw,ins,branch,b0,b1⟩ := e
    have atg : gateAt C i = g := by
      change C.gates.getD i ⟨GateOp.or,[]⟩ = g
      simp only [List.getD_eq_getElem?_getD,real,Option.getD_some]
    refine ⟨i,eqw,?_,b0,b1⟩
    change a ∈ (gateAt C i).inputs
    rw [atg,ins]
    rcases branch with ⟨_,ha | ha⟩ | ⟨_,ha⟩
    · simp [ha]
    · simp [ha]
    · split at ha <;> simp [ha]
  have liftPath {a b} (p : Relation.ReflTransGen T a b) : path a b := by
    induction p with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (go _ _ h)
  have typed (A : Finset ℕ) (i) : V A i = val C (indW 26 A) i := rfl
  have source (w : ℕ) (m : M w) : ∃ r, root r ∧ 26+r ≤ w ∧ path (26+r) w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      obtain ⟨wb,wp,wl⟩ := m
      have bound : 26 ≤ w := by
        by_contra! raw
        rw [typed,val_input _ _ _ raw] at wb wp wl
        change decide (w ∈ ({0,13} : Finset ℕ)) = true at wb
        change decide (w ∈ ({0} : Finset ℕ)) = false at wp
        change decide (w ∈ ({13} : Finset ℕ)) = false at wl
        simp at wb wp wl
        exact wb.elim wp wl
      let i := w-26
      have wi : w = 26+i := by dsimp [i]; omega
      have hi : i < C.gates.length := by
        by_contra! high
        have off := val_outside C (indW 26 {0,13}) w (by omega)
        exact Bool.noConfusion (wb.symm.trans off)
      obtain ⟨g,a,b,real,atg,ins,ba,bb,op⟩ := reads i hi
      have members : I i = [a,b] := by simpa only [I,atg] using ins
      by_cases has : ∃ z ∈ I i, M z
      · obtain ⟨z,hz,mz⟩ := has
        have back := ao.2.1 i hi z hz
        obtain ⟨r,pr,le,pa⟩ := ih z (by omega) mz
        exact ⟨r,pr,by omega,pa.tail ⟨i,wi,hz,mz.1,wb⟩⟩
      · push Not at has
        have must : g.op = .and := by
          rcases op with h | h
          · exact h
          have B := (val_gate C (indW 26 {0,13}) i g real a b ins ba bb).2 h
          have P := (val_gate C (indW 26 {0}) i g real a b ins ba bb).2 h
          have L := (val_gate C (indW 26 {13}) i g real a b ins ba bb).2 h
          change V {0,13} (26+i) = (V {0,13} a || V {0,13} b) at B
          change V {0} (26+i) = (V {0} a || V {0} b) at P
          change V {13} (26+i) = (V {13} a || V {13} b) at L
          rw [wi,B] at wb
          rw [wi,P] at wp
          rw [wi,L] at wl
          obtain ha | hb := Bool.or_eq_true_iff.mp wb
          · exact (has a (by simp [members]) ⟨ha,(Bool.or_eq_false_iff.mp wp).1,(Bool.or_eq_false_iff.mp wl).1⟩).elim
          · exact (has b (by simp [members]) ⟨hb,(Bool.or_eq_false_iff.mp wp).2,(Bool.or_eq_false_iff.mp wl).2⟩).elim
        exact ⟨i,⟨⟨hi,atg ▸ must⟩,wi ▸ (show M w from ⟨wb,wp,wl⟩),has⟩,by omega,wi ▸ .refl⟩
  have endpoint (z other q : ℕ) (both : (z = 0 ∧ other = 13) ∨ (z = 13 ∧ other = 0))
      (hq : old z q) (reject : V {other} (26+q) = false) :
      fork z q ∧ ∃ r, root r ∧ r < q ∧ path (26+r) (26+q) := by
    obtain ⟨live,andq,allIn⟩ := hq
    obtain ⟨g,a,b,real,atg,ins,ba,bb,_⟩ := reads q andq.1
    have op : g.op = .and := atg ▸ andq.2
    have ia : a ∈ I q := by simp [I,atg,ins]
    have ib : b ∈ I q := by simp [I,atg,ins]
    have rule (A : Finset ℕ) : V A (26+q) = (V A a && V A b) :=
      (val_gate C (indW 26 A) q g real a b ins ba bb).1 op
    have pos : V {0,13} (26+q) = true := by rw [rule,(allIn a ia).1,(allIn b ib).1]; rfl
    have zn : V {z} (26+q) = false := by rw [rule,(allIn a ia).2]; rfl
    have mkM (u) (on : V {0,13} u = true) (hz : V {z} u = false) (ho : V {other} u = false) : M u := by
      rcases both with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨on,hz,ho⟩
      · exact ⟨on,ho,hz⟩
    refine ⟨⟨andq,mkM _ pos zn reject,liftPath live,fun u hu => (allIn u hu).2⟩,?_⟩
    have ex : ∃ u ∈ I q, V {other} u = false := by
      rw [rule] at reject
      rcases Bool.and_eq_false_iff.mp reject with h | h
      · exact ⟨a,ia,h⟩
      · exact ⟨b,ib,h⟩
    obtain ⟨u,hu,neg⟩ := ex
    obtain ⟨r,rt,le,pa⟩ := source u (mkM u (allIn u hu).1 (allIn u hu).2 neg)
    exact ⟨r,rt,by have := ao.2.1 q andq.1 u hu; omega,pa.tail ⟨q,rfl,hu,(allIn u hu).1,pos⟩⟩
  obtain ⟨fj,r,hr,rj,rp⟩ := endpoint 0 13 j (Or.inl ⟨rfl,rfl⟩) hj hLj
  obtain ⟨fk,s,hs,sk,sp⟩ := endpoint 13 0 k (Or.inr ⟨rfl,rfl⟩) hk hPk
  have board (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    rw [computes]
    have incidence : ∀ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ↔ p ∈ singerLines3 l := by decide
    simp only [incidence]
  by_cases eq : r = s
  · subst s
    exact shared C lower upper ao nd read0 read13 board j k distinct fj fk ⟨r,hr,rj,sk,rp,sp⟩
  · exact separate C lower upper ao nd read0 read13 board j k distinct fj fk ⟨r,s,eq,hr,hs,rj,sk,rp,sp⟩
