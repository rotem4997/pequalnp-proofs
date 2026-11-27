import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A zero input consists of point and line sets with no incidences between them.
-- At least one side of every such rectangle has size at most six.
-- A set of at most six points specifies a clause: some selected point is outside
-- the set, or some selected line meets it. Use the dual clauses for the lines.
-- The first child is the Gram matrix identity for the explicit incidence matrix.
-- Its entire proof is by decide +kernel.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4653_271
    (gram :
      let entry (p l : Fin 21) : ℕ :=
        if (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ) then 1 else 0
      ∀ p q, ∑ l : Fin 21, entry p l * entry q l = 1 + if p = q then 4 else 0)
    (clauses :
      let adj (p l : Fin 21) := (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let passes (a b : Fin 21 → Bool) (E : Fin 21 → Fin 21 → Prop) :=
        ∀ S : Finset (Fin 21), S.card ≤ 6 → (∀ p, a p = true → p ∈ S) →
          ∃ p ∈ S, ∃ l, b l = true ∧ E p l
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 42 → Bool,
          let a (p : Fin 21) := x (Fin.castAdd 21 p)
          let b (l : Fin 21) := x (Fin.natAdd 21 l)
          C.eval (List.ofFn x) = true ↔ passes a b adj ∧ passes b a (fun l p => adj p l)) →
        (∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.or →
          ∀ w ∈ (C.gates.get j).inputs, ∃ x : Fin 42 → Bool,
            ({C with gates := C.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval (List.ofFn x)
              ≠ C.eval (List.ofFn x)) →
        104 ≤ ({j : Fin C.gates.length | (C.gates.get j).op = GateOp.or} : Set _).ncard) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => {x3 : Fin x2.gates.length | (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) => { gates := x3.gates.set x4 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit }; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (42 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true; have x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Fin (42 : ℕ) → Bool := fun (x5 x6 x7 : Fin (42 : ℕ)) => Decidable.decide (x7 = x5 ∨ x7 = x6); have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x7 : Fin x6.gates.length),     (x6.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ x9 ∈ (x6.gates.get x7).inputs,         ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)),           x1 x11 x12 ∧             (x3 x6 (↑x7) x9).eval (List.ofFn (x5 x11 x12)) = Bool.false ∧               have x13 : List Bool := { gates := List.take (↑x7) x6.gates, output := x6.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (x5 x11 x12));               x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x6.gates.get x7).inputs, x13.getD x14 Bool.false = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → x6 x7 → (104 : ℕ) ≤ x2 x7 := by
  classical
  intro edge count bypass computes pair critical C mono correct pins
  let adj (p l : Fin 21) := (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let entry (p l : Fin 21) : ℕ := if adj p l then 1 else 0
  have overlap (p q : Fin 21) :
      ∑ l : Fin 21, entry p l * entry q l = 1 + if p = q then 4 else 0 := gram p q
  have diagonal (p l : Fin 21) : entry p l * entry p l = entry p l := by
    by_cases e : adj p l <;> simp [entry, e]
  have rowSum (p : Fin 21) : ∑ l : Fin 21, entry p l = 5 := by
    simpa [diagonal] using overlap p p
  have emptyBound (P L : Finset (Fin 21))
      (none : ∀ p ∈ P, ∀ l ∈ L, ¬adj p l) : P.card * L.card ≤ 36 := by
    let d (l : Fin 21) := ∑ p ∈ P, entry p l
    have first : ∑ l : Fin 21, d l = 5 * P.card := by
      dsimp [d]
      rw [Finset.sum_comm]
      simp [rowSum, Nat.mul_comm]
    have second : ∑ l : Fin 21, d l ^ 2 = P.card * (P.card + 4) := by
      calc
        ∑ l : Fin 21, d l ^ 2 =
            ∑ l : Fin 21, ∑ p ∈ P, ∑ q ∈ P, entry p l * entry q l := by
              simp only [d, pow_two, Finset.sum_mul, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              apply Finset.sum_congr rfl
              intro p _
              apply Finset.sum_congr rfl
              intro q _
              exact Nat.mul_comm _ _
        _ = ∑ p ∈ P, ∑ q ∈ P, ∑ l : Fin 21, entry p l * entry q l := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro p hp
              rw [Finset.sum_comm]
        _ = ∑ p ∈ P, (P.card + 4) := by
              apply Finset.sum_congr rfl
              intro p hp
              simp [overlap, Finset.sum_add_distrib, hp]
        _ = P.card * (P.card + 4) := by simp
    have zero (l : Fin 21) (hl : l ∈ L) : d l = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [entry, none p hp l hl]
    have restrict (f : ℕ → ℕ) (h : f 0 = 0) :
        ∑ l ∈ Lᶜ, f (d l) = ∑ l : Fin 21, f (d l) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      rw [zero l (by simpa using hl), h]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq (Lᶜ) (fun _ => (1 : ℕ)) d
    simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at cs
    have unrestrict : ∑ l ∈ Lᶜ, d l = ∑ l : Fin 21, d l := restrict id rfl
    have unrestrictSq : ∑ l ∈ Lᶜ, d l ^ 2 = ∑ l : Fin 21, d l ^ 2 :=
      restrict (fun v => v ^ 2) (by decide)
    rw [unrestrict, unrestrictSq, first, second,
      Finset.card_compl, Fintype.card_fin] at cs
    by_cases hP : P.card = 0
    · simp [hP]
    have pp : 0 < P.card := Nat.pos_of_ne_zero hP
    have divided : 25 * P.card ≤ (21 - L.card) * (P.card + 4) := by
      apply Nat.le_of_mul_le_mul_left _ pp
      nlinarith only [cs]
    have smallP : P.card ≤ 21 := by simpa using P.card_le_univ
    have smallL : L.card ≤ 21 := by simpa using L.card_le_univ
    have arithmetic : ∀ s t : Fin 22,
        25 * s.val ≤ (21 - t.val) * (s.val + 4) → s.val * t.val ≤ 36 := by decide +kernel
    exact arithmetic ⟨P.card, by omega⟩ ⟨L.card, by omega⟩ divided
  have geometry (P L : Finset (Fin 21)) (none : ∀ p ∈ P, ∀ l ∈ L, ¬adj p l) :
      P.card ≤ 6 ∨ L.card ≤ 6 := by
    have bound := emptyBound P L none
    by_contra! h
    have many : 7 * 7 ≤ P.card * L.card := Nat.mul_le_mul h.1 h.2
    omega
  have coords (p l : Fin 21) :
      edge (Fin.castAdd 21 p) (Fin.natAdd 21 l) ↔ adj p l := by
    change (_ < 21 ∧ 21 ≤ _ ∧ ((21 + l.val + 21 - p.val) % 21) ∈ _) ↔ _
    have shift : 21 + l.val + 21 - p.val = (l.val + 21 - p.val) + 21 := by omega
    simp [adj, shift, p.isLt]
  have unpair (u v : Fin 42) (h : edge u v) :
      ∃ p l : Fin 21, u = Fin.castAdd 21 p ∧ v = Fin.natAdd 21 l ∧ adj p l := by
    have hu := h.1
    have hv := h.2.1
    let p : Fin 21 := ⟨u.val, hu⟩
    let l : Fin 21 := ⟨v.val - 21, by have := v.isLt; omega⟩
    have eu : u = Fin.castAdd 21 p := Fin.ext rfl
    have ev : v = Fin.natAdd 21 l := Fin.ext (by change v.val = 21 + (v.val-21); omega)
    exact ⟨p,l,eu,ev,(coords p l).mp (eu ▸ ev ▸ h)⟩
  apply clauses C mono
  · intro x
    let a (p : Fin 21) := x (Fin.castAdd 21 p)
    let b (l : Fin 21) := x (Fin.natAdd 21 l)
    constructor
    · intro yes
      obtain ⟨u,v,uv,hu,hv⟩ := (correct x).mp yes
      obtain ⟨p,l,rfl,rfl,e⟩ := unpair u v uv
      exact ⟨fun _ _ holds => ⟨p,holds p hu,l,hv,e⟩,
             fun _ _ holds => ⟨l,holds l hv,p,hu,e⟩⟩
    · rintro ⟨left,right⟩
      apply (correct x).mpr
      by_contra missing
      let P := Finset.univ.filter (fun p => a p = true)
      let L := Finset.univ.filter (fun l => b l = true)
      have hp (p : Fin 21) : p ∈ P ↔ a p = true := by simp [P]
      have hl (l : Fin 21) : l ∈ L ↔ b l = true := by simp [L]
      have none (p) (pm : p ∈ P) (l) (lm : l ∈ L) (e : adj p l) : False :=
        missing ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, (coords p l).mpr e,
          (hp p).mp pm, (hl l).mp lm⟩
      rcases geometry P L none with small | small
      · obtain ⟨p,pm,l,lit,e⟩ := left P small (fun p h => (hp p).mpr h)
        exact none p pm l ((hl l).mpr lit) e
      · obtain ⟨l,lm,p,lit,e⟩ := right L small (fun l h => (hl l).mpr h)
        exact none p ((hp p).mpr lit) l lm e
  · intro j op w mem
    obtain ⟨u,v,uv,lost,_⟩ := pins j op w mem
    have live : C.eval (List.ofFn (pair u v)) = true :=
      (correct _).mpr ⟨u,v,uv,by simp [pair],by simp [pair]⟩
    exact ⟨pair u v, by change (bypass C j.val w).eval _ ≠ C.eval _
                        rw [lost,live]; decide⟩
