import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadTwo PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8203_218
  (mono : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (x y : Fin n → Bool),
      (∀ i, x i = true → y i = true) → ∀ w, wval C x w = true → wval C y w = true)
  (rest : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun t => (t / 11, t % 11))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 21 → 2 ≤ (junk G C).card →
    2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
    (∀ v : Fin 11, v.val < 4 →
      ((Finset.range C.size).filter fun k => (gateAt C k).inputs.any (fun i => !wval C (fun j : Fin 11 => decide (j ≠ v)) i)).card ≤ 2) →
    ∃ v : Fin 11, v.val < 4 ∧ (let dup := (fun k : ℕ => ∃ j < 11+k, ∀ (x : Fin 11 → Bool), x v = false → wval C x (11+k) = wval C x j);
      ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ dup i ∧ dup j ∧ dup k)) :
  (have x1 : ℕ := (11 : ℕ); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   PEqualNP.TopForm.IsLeastAO x2 x3 →     PEqualNP.TopForm.TopForm x2 x3 →       x3.size ≤ (21 : ℕ) →         x4 ∈ PEqualNP.TopForm.junk x2 x3 →           x5 ∈ PEqualNP.TopForm.junk x2 x3 →             x4 < x5 →               (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card →                 (∀ x13 ∈ [x4, x5], ∀ (x15 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x3 x15 (x1 + x13) = Bool.true ↔ ∀ (x16 : Fin (2 : ℕ)), (∃ x17 ∈ PEqualNP.TopForm.side x3 x13 x16, x15 x17 = Bool.true) ∨ x13 = x5 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x3 (PEqualNP.TopForm.opnd x3 x13 x16) x4 ∧ PEqualNP.ReadTwo.wval x3 x15 (x1 + x4) = Bool.true) →                   ∃ (x14 : Fin (11 : ℕ)),                     ↑x14 < (4 : ℕ) ∧                       have x15 : ℕ → Prop := fun (x15 : ℕ) => ∃ x16 < (11 : ℕ) + x15, ∀ (x17 : Fin (11 : ℕ) → Bool), x17 x14 = Bool.false → PEqualNP.ReadTwo.wval x3 x17 ((11 : ℕ) + x15) = PEqualNP.ReadTwo.wval x3 x17 x16;                       ∃ (x16 : ℕ) (x17 : ℕ) (x18 : ℕ), x16 < x17 ∧ x17 < x18 ∧ x18 < x3.size ∧ x15 x16 ∧ x15 x17 ∧ x15 x18) := by
  classical
  intro n G D a b hm ht sz ha hb ab deficit recGate
  let Z := fun (v : Fin 11) => (Finset.range D.size).filter fun k =>
    (gateAt D k).inputs.any (fun i => !wval D (fun j : Fin 11 => decide (j ≠ v)) i)
  have cardJ : 2 ≤ (junk G D).card := by
    have h : ({a,b} : Finset ℕ) ⊆ junk G D := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      exact hk.elim (fun e => e ▸ ha) (fun e => e ▸ hb)
    calc
      2 = ({a,b} : Finset ℕ).card := (Finset.card_pair_eq_two_iff.mpr (ne_of_lt ab)).symm
      _ ≤ _ := Finset.card_le_card h
  by_cases small : ∀ v : Fin 11, v.val < 4 → (Z v).card ≤ 2
  · exact rest D hm ht sz cardJ deficit small
  push Not at small
  obtain ⟨v,hv,big⟩ := small
  let stepWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt2 (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : PEqualNP.CircuitLowerBounds.Circuit} {j : ℕ} (hj : j < C.gates.length) : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : PEqualNP.CircuitLowerBounds.Circuit} {j : ℕ} (hj : j < C.gates.length) : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

  have val_ge {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have hAO2 := hm.1
  have hRB : ∀ k < D.gates.length, ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, u < 11 + k := hAO2.2.1
  have hops : ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.or := fun k hk => hAO2.1 _ (gateAt_mem hk)
  have hlen2 : ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs.length = 2 :=
    fun k hk => hAO2.2.2 _ (gateAt_mem hk)
  have andE : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have orE : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have gsem : ∀ k < D.gates.length, ∃ p q : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs = [p, q] ∧ p < 11 + k ∧
      q < 11 + k ∧ (∀ x : Fin 11 → Bool,
        PEqualNP.ReadTwo.wval D x (11 + k) = (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op.eval [PEqualNP.ReadTwo.wval D x p, PEqualNP.ReadTwo.wval D x q]) := by
    intro k hk
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 k hk)
    have hp : p < 11 + k := hRB k hk p (by rw [hpq]; simp)
    have hq : q < 11 + k := hRB k hk q (by rw [hpq]; simp)
    refine ⟨p, q, hpq, hp, hq, fun x => ?_⟩
    have hv := val_gate (C := D) (x := List.ofFn x) List.length_ofFn hk
    rw [hpq] at hv
    simp only [List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq] at hv
    exact hv
  have hin : ∀ (v : Fin 11) (x : Fin 11 → Bool), PEqualNP.ReadTwo.wval D x v.val = x v := by
    intro v x
    have hv := val_input (C := D) (x := List.ofFn x) List.length_ofFn v.isLt
    refine hv.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  have zv : ∀ (v : Fin 11) (x : Fin 11 → Bool), x v = false → PEqualNP.ReadTwo.wval D x v.val = false :=
    fun v x hx => (hin v x).trans hx
  have zand : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs → (∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x u = false) →
      ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + k) = false := by
    intro v k u hk hop hu hz x hx
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    rw [hpq, List.mem_pair] at hu
    rw [hs x, hop, andE]
    have hzz := hz x hx
    rcases hu with h | h <;> subst h <;> simp [hzz]
  have rep1 : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs →
      (∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x u = false) →
      ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + k) = PEqualNP.ReadTwo.wval D x w := by
    intro v k u hk hu hz
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    have hu' := hu
    rw [hpq, List.mem_pair] at hu'
    rcases hops k hk with hop | hop
    · refine ⟨u, hRB k hk u hu, fun x hx => ?_⟩
      rw [zand v k u hk hop hu hz x hx, hz x hx]
    · rcases hu' with h | h
      · subst h
        refine ⟨q, hq, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]
      · subst h
        refine ⟨p, hp, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]
  have fin : ∀ (v : Fin 11), v.val < 4 → ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      a < D.gates.length → b < D.gates.length → c < D.gates.length →
      (∃ w < 11 + a, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + a) = PEqualNP.ReadTwo.wval D x w) →
      (∃ w < 11 + b, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + b) = PEqualNP.ReadTwo.wval D x w) →
      (∃ w < 11 + c, ∀ x : Fin 11 → Bool, x v = false → PEqualNP.ReadTwo.wval D x (11 + c) = PEqualNP.ReadTwo.wval D x w) →
      ∃ x8 : Fin 11, x8.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.size ∧
        (∃ w < 11 + i, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + i) = PEqualNP.ReadTwo.wval D x w) ∧
        (∃ w < 11 + j, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + j) = PEqualNP.ReadTwo.wval D x w) ∧
        (∃ w < 11 + k, ∀ x : Fin 11 → Bool, x x8 = false → PEqualNP.ReadTwo.wval D x (11 + k) = PEqualNP.ReadTwo.wval D x w) := by
    intro v hv a b c hab hac hbc ha hb hc ra rb rc
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hab with o1 | o1 <;> rcases lt_or_gt_of_ne hac with o2 | o2 <;>
      rcases lt_or_gt_of_ne hbc with o3 | o3 <;>
      first
      | exact ⟨a, b, c, by omega, by omega, hc, ra, rb, rc⟩
      | exact ⟨a, c, b, by omega, by omega, hb, ra, rc, rb⟩
      | exact ⟨b, a, c, by omega, by omega, hc, rb, ra, rc⟩
      | exact ⟨b, c, a, by omega, by omega, ha, rb, rc, ra⟩
      | exact ⟨c, a, b, by omega, by omega, hb, rc, ra, rb⟩
      | exact ⟨c, b, a, by omega, by omega, ha, rc, rb, ra⟩

  have pay (k : ℕ) (h : k ∈ Z v) :
      ∃ j < 11+k, ∀ x : Fin 11 → Bool, x v = false → wval D x (11+k) = wval D x j := by
    obtain ⟨hk,hit⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,zero⟩ := List.any_eq_true.mp hit
    apply rep1 v k i (Finset.mem_range.mp hk) hi
    intro x hx
    cases he : wval D x i
    · rfl
    · have hh := mono 11 D hm.1 x (fun j => decide (j ≠ v)) (by
        intro j hj
        apply decide_eq_true
        rintro rfl
        rw [hx] at hj
        contradiction) i he
      change (!wval D (fun j : Fin 11 => decide (j ≠ v)) i) = true at zero
      rw [hh] at zero
      contradiction
  obtain ⟨i,j,k,hi,hj,hk,ij,ik,jk⟩ := Finset.two_lt_card_iff.mp big
  exact fin v hv i j k ij ik jk (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    (pay i hi) (pay j hj) (pay k hk)
