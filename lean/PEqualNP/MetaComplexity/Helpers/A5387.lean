import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart2

/-!
# Helpers for L-meta-5387: the true, separating AND below a re-read edge

* `orIn_up`: an input in `orIn` of an operand of an OR gate is in `orIn` of the gate.
* `orIn_val`: an input in `orIn w` makes wire `w` true at its one-hot input.
* `descent`: a wire true at the pair input of `u, v` has `u` or `v` in `orIn`, or reaches through ORs a
  true AND.
* `sep_below`: under the one-hot clause, a true AND has a true AND separating `u, v` at or below it.
* `read_one`: an AND reached from the output through ORs and separating `u, v` gives a read-1 vector.
-/

namespace PEqualNP.MetaComplexity.Helpers.A5387

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.ReadK
open PEqualNP.EdgeOwnership (gateVal pairInput InCone)

variable {n : ℕ} {C : Circuit}

/-- The AND `Y` separates `u` and `v`: its operands reach them through ORs, on different sides. -/
def Sep (n : ℕ) (C : Circuit) (u v : Fin n) (Y : ℕ) : Prop :=
  (u ∈ orIn n C (opnd C Y 0) ∧ v ∈ orIn n C (opnd C Y 1)) ∨
  (v ∈ orIn n C (opnd C Y 0) ∧ u ∈ orIn n C (opnd C Y 1))

theorem mem_orIn (u : Fin n) (w : ℕ) : u ∈ orIn n C w ↔ (u : ℕ) = w ∨ ∃ k < C.gates.length,
    OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (u : ℕ) ∈ (gateAt C k).inputs := by
  simp [orIn]

theorem orIn_up (hC : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or)
    (b : Fin 2) (u : Fin n) (h : u ∈ orIn n C (opnd C k b)) : u ∈ orIn n C (n + k) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨j, hj, hr, hj2, hj3⟩
  · refine ⟨k, hk, (reach_gate C hC k k hk).2 (Or.inl rfl), ho, ?_⟩
    rw [h]; exact LeafBound.opnd_mem hC hk b
  · exact ⟨j, hj, (reach_gate C hC k j hk).2 (Or.inr ⟨ho, b, hr⟩), hj2, hj3⟩

theorem opnd_wires (hC : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) (b : Fin 2) :
    opnd C k b < n + C.gates.length := by
  have := opnd_lt C hC k hk b
  omega

theorem orIn_val (hC : IsAO2 n C) (u : Fin n) (w : ℕ) (hw : w < n + C.gates.length)
    (h : u ∈ orIn n C w) (x : Fin n → Bool) (hx : x u = true) : wireVal n C w x = true := by
  rw [mem_orIn] at h
  rcases h with h | ⟨j, hj, hr, ho, hu⟩
  · rw [← h, wireVal_lt C u u.2]; exact hx
  · refine (reach_le C hC j w hw hr).2 x ?_
    obtain ⟨b, hb⟩ := mem_opnd C hC j hj _ hu
    rw [val_or C hC j hj ho]
    have hv : wireVal n C (opnd C j b) x = true := by
      rw [hb, wireVal_lt C u u.2]; exact hx
    fin_cases b
    · exact Or.inl hv
    · exact Or.inr hv

theorem descent (hC : IsAO2 n C) (u v : Fin n) : ∀ w < n + C.gates.length,
    wireVal n C w (pairInput u v) = true → u ∈ orIn n C w ∨ v ∈ orIn n C w ∨
      ∃ X < C.gates.length, OrReaches n C w X ∧ (gateAt C X).op = GateOp.and ∧
        gateVal n C X (pairInput u v) = true := by
  refine wire_induction C hC _ ?_ ?_
  · intro w hw h
    rw [wireVal_lt C w hw] at h
    unfold pairInput at h
    simp only [decide_eq_true_eq] at h
    rcases h with h | h
    · left; rw [mem_orIn]; left; rw [← h]
    · right; left; rw [mem_orIn]; left; rw [← h]
  · intro k hk ih h
    have hg : gateVal n C k (pairInput u v) = true := h
    rcases LeafBound.ao_op hC hk with ho | ho
    · exact Or.inr (Or.inr ⟨k, hk, (reach_gate C hC k k hk).2 (Or.inl rfl), ho, hg⟩)
    · obtain ⟨b, hb⟩ : ∃ b, wireVal n C (opnd C k b) (pairInput u v) = true := by
        rcases (val_or C hC k hk ho _).1 hg with h0 | h0
        · exact ⟨0, h0⟩
        · exact ⟨1, h0⟩
      rcases ih b hb with h0 | h0 | ⟨X, hX, hr, hX2, hX3⟩
      · exact Or.inl (orIn_up hC hk ho b u h0)
      · exact Or.inr (Or.inl (orIn_up hC hk ho b v h0))
      · exact Or.inr (Or.inr ⟨X, hX, (reach_gate C hC k X hk).2 (Or.inr ⟨ho, b, hr⟩), hX2, hX3⟩)

theorem reach_down (hC : IsAO2 n C) (g : ℕ) : ∀ w < n + C.gates.length, OrReaches n C w g →
    LeafBound.Reach n C w (n + g) := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w g hw)) ?_
  intro k hk ih h
  rcases (reach_gate C hC k g hk).1 h with rfl | ⟨ho, b, hb⟩
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.head (LeafBound.step_opnd hC hk b) (ih b hb)

theorem cone_opnd (hC : IsAO2 n C) {X Z : ℕ} (hX : X < C.gates.length) (b : Fin 2)
    (hr : OrReaches n C (opnd C X b) Z) : InCone n C Z X :=
  (LeafBound.inCone_iff_trans n C hC.2.1 Z X hX).2
    (Relation.TransGen.head' (LeafBound.step_opnd hC hX b)
      (reach_down hC Z _ (opnd_wires hC hX b) hr))

theorem cone_trans (hC : IsAO2 n C) {X Y Z : ℕ} (hX : X < C.gates.length) (hZ : Z < C.gates.length)
    (h1 : InCone n C Y Z) (h2 : InCone n C Z X) : InCone n C Y X :=
  (LeafBound.inCone_iff_trans n C hC.2.1 Y X hX).2
    (((LeafBound.inCone_iff_trans n C hC.2.1 Z X hX).1 h2).trans
      ((LeafBound.inCone_iff_trans n C hC.2.1 Y Z hZ).1 h1))

theorem sep_below (hC : IsAO2 n C)
    (hone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t : Fin n,
      gateVal n C k (fun r => decide (r = t)) = false) (u v : Fin n) :
    ∀ X, X < C.gates.length → (gateAt C X).op = GateOp.and → gateVal n C X (pairInput u v) = true →
      ∃ Y < C.gates.length, (gateAt C Y).op = GateOp.and ∧ gateVal n C Y (pairInput u v) = true ∧
        Sep n C u v Y ∧ (Y = X ∨ InCone n C Y X) := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  intro hX hop hv
  have hv2 := (val_and C hC X hX hop _).1 hv
  have hrec : ∀ b, (∃ Z < C.gates.length, OrReaches n C (opnd C X b) Z ∧ (gateAt C Z).op = GateOp.and ∧
      gateVal n C Z (pairInput u v) = true) → ∃ Y < C.gates.length, (gateAt C Y).op = GateOp.and ∧
        gateVal n C Y (pairInput u v) = true ∧ Sep n C u v Y ∧ (Y = X ∨ InCone n C Y X) := by
    rintro b ⟨Z, hZ, hr, hZ2, hZ3⟩
    have hlt := opnd_lt C hC X hX b
    have hle := (reach_le C hC Z _ (opnd_wires hC hX b) hr).1
    obtain ⟨Y, hY, hY2, hY3, hY4, hY5⟩ := ih Z (by omega) hZ hZ2 hZ3
    have hZX := cone_opnd hC hX b hr
    refine ⟨Y, hY, hY2, hY3, hY4, Or.inr ?_⟩
    rcases hY5 with rfl | hY5
    · exact hZX
    · exact cone_trans hC hX hZ hY5 hZX
  have same : ∀ t : Fin n, t ∈ orIn n C (opnd C X 0) → t ∈ orIn n C (opnd C X 1) → False := by
    intro t h0 h1
    have h2 := hone X hX hop t
    have h3 : gateVal n C X (fun r => decide (r = t)) = true :=
      (val_and C hC X hX hop _).2 ⟨orIn_val hC t _ (opnd_wires hC hX 0) h0 _ (by simp),
        orIn_val hC t _ (opnd_wires hC hX 1) h1 _ (by simp)⟩
    rw [h2] at h3
    exact Bool.false_ne_true h3
  rcases descent hC u v _ (opnd_wires hC hX 0) hv2.1 with h0 | h0 | h0
  · rcases descent hC u v _ (opnd_wires hC hX 1) hv2.2 with h1 | h1 | h1
    · exact (same u h0 h1).elim
    · exact ⟨X, hX, hop, hv, Or.inl ⟨h0, h1⟩, Or.inl rfl⟩
    · exact hrec 1 h1
  · rcases descent hC u v _ (opnd_wires hC hX 1) hv2.2 with h1 | h1 | h1
    · exact ⟨X, hX, hop, hv, Or.inr ⟨h0, h1⟩, Or.inl rfl⟩
    · exact (same v h0 h1).elim
    · exact hrec 1 h1
  · exact hrec 0 h0

theorem vec_up (hC : IsAO2 n C) (k : ℕ) (S : List ℕ) (g : ℕ) (a : List ℕ)
    (ha : a ∈ LeafBound.AV n C k S (n + g)) : ∀ w < n + C.gates.length, OrReaches n C w g →
      a ∈ LeafBound.AV n C k S w := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w g hw)) ?_
  intro j hj ih h
  rcases (reach_gate C hC j g hj).1 h with rfl | ⟨ho, b, hb⟩
  · exact ha
  · refine (LeafBound.gate_vec hC k S hj a).2 (Or.inl ⟨ho, ?_⟩)
    have := ih b hb
    fin_cases b
    · exact Or.inl this
    · exact Or.inr this

theorem vec_orIn (hC : IsAO2 n C) (k : ℕ) (S : List ℕ) (u : Fin n) (a : List ℕ)
    (ha : a ∈ leafVectors S k u) (w : ℕ) (hw : w < n + C.gates.length) (h : u ∈ orIn n C w) :
    a ∈ LeafBound.AV n C k S w := by
  have hu : a ∈ LeafBound.AV n C k S u := by rw [LeafBound.AV_input k S u u.2]; exact ha
  rw [mem_orIn] at h
  rcases h with h | ⟨j, hj, hr, ho, hj2⟩
  · rw [← h]; exact hu
  · refine vec_up hC k S j a ?_ w hw hr
    obtain ⟨b, hb⟩ := mem_opnd C hC j hj _ hj2
    refine (LeafBound.gate_vec hC k S hj a).2 (Or.inl ⟨ho, ?_⟩)
    rw [← hb] at hu
    fin_cases b
    · exact Or.inl hu
    · exact Or.inr hu

theorem read_one (hC : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) (X o : ℕ) (ho : o < C.gates.length)
    (hX : X < C.gates.length) (hop : (gateAt C X).op = GateOp.and) (hr : OrReaches n C (n + o) X)
    (hs : Sep n C u v X) : readsAtMost (PEqualNP.Core.atGate n C o) n [u.val, v.val] 1 = true := by
  have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have lu : [1, 0] ∈ leafVectors [u.val, v.val] 1 u := by simp [leafVectors, huv'.symm]
  have lv : [0, 1] ∈ leafVectors [u.val, v.val] 1 v := by simp [leafVectors, huv']
  have h11 : [1, 1] ∈ LeafBound.AV n C 1 [u.val, v.val] (n + X) := by
    refine (LeafBound.gate_vec hC 1 _ hX _).2 (Or.inr ⟨hop, ?_⟩)
    rcases hs with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨_, vec_orIn hC 1 _ u _ lu _ (opnd_wires hC hX 0) h0, _,
        vec_orIn hC 1 _ v _ lv _ (opnd_wires hC hX 1) h1, by simp [capAdd]⟩
    · exact ⟨_, vec_orIn hC 1 _ v _ lv _ (opnd_wires hC hX 0) h0, _,
        vec_orIn hC 1 _ u _ lu _ (opnd_wires hC hX 1) h1, by simp [capAdd]⟩
  have hout := vec_up hC 1 _ X _ h11 (n + o) (by omega) hr
  show ((readVectors C n [u.val, v.val] 1).getD (n + o) []).any _ = true
  exact List.any_eq_true.2 ⟨_, hout, by simp⟩

end PEqualNP.MetaComplexity.Helpers.A5387
