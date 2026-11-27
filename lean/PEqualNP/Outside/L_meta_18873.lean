import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18873

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]

def circ : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 4] }
      , { op := GateOp.or, inputs := [1, 3] }
      , { op := GateOp.and, inputs := [6, 7] }
      , { op := GateOp.or, inputs := [2, 8] }
      , { op := GateOp.or, inputs := [0, 1] }
      , { op := GateOp.and, inputs := [9, 10] }
      , { op := GateOp.and, inputs := [3, 5] }
      , { op := GateOp.or, inputs := [11, 12] }
      ]
    output := 13 }

def badInput : Fin 6 → Bool
  | ⟨3, _⟩ => true
  | ⟨4, _⟩ => true
  | _ => false

lemma eval_bool (b0 b1 b2 b3 b4 b5 : Bool) :
    circ.eval [b0, b1, b2, b3, b4, b5] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

lemma ofFn_six (x : Fin 6 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

lemma edges_eq_fn_at (x : Fin 6 → Bool) :
    edges.any (fun e => x e.1 && x e.2) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) := by
  simp only [edges, List.any_cons, List.any_nil, Bool.or_false]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

lemma edges_eq_fn :
    (fun x : Fin 6 → Bool => edges.any (fun e => x e.1 && x e.2)) =
    (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) :=
  funext edges_eq_fn_at

lemma circ_eval (x : Fin 6 → Bool) :
    circ.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
  rw [ofFn_six, eval_bool, edges_eq_fn_at]

lemma circ_fanInTwo : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma circ_noNot : ∀ g ∈ circ.gates, g.op ≠ GateOp.not := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => by cases h

lemma edges_irrefl : ∀ e ∈ edges, e.1 ≠ e.2 := by
  intro e he
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def adj (x y : Fin 6) : Bool :=
  edges.any (fun e => (e.1 == x && e.2 == y) || (e.1 == y && e.2 == x))

lemma adj_of_mem (x y : Fin 6) (h : (x, y) ∈ edges ∨ (y, x) ∈ edges) : adj x y = true := by
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
                (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rfl

lemma no_c4_bool :
    (List.finRange 6).all (fun a =>
    (List.finRange 6).all (fun b =>
    (List.finRange 6).all (fun c =>
    (List.finRange 6).all (fun d =>
      !(a != c && b != d && adj a b && adj b c && adj c d && adj d a))))) = true := by
  decide

lemma edges_c4free :
    ∀ a b c d : Fin 6, a ≠ c → b ≠ d →
      ((a, b) ∈ edges ∨ (b, a) ∈ edges) →
      ((b, c) ∈ edges ∨ (c, b) ∈ edges) →
      ((c, d) ∈ edges ∨ (d, c) ∈ edges) →
      ((d, a) ∈ edges ∨ (a, d) ∈ edges) → False := by
  intro a b c d hac hbd hab hbc hcd hda
  have h1 := List.all_eq_true.mp no_c4_bool a (List.mem_finRange a)
  have h2 := List.all_eq_true.mp h1 b (List.mem_finRange b)
  have h3 := List.all_eq_true.mp h2 c (List.mem_finRange c)
  have h4 := List.all_eq_true.mp h3 d (List.mem_finRange d)
  rw [adj_of_mem _ _ hab, adj_of_mem _ _ hbc, adj_of_mem _ _ hcd, adj_of_mem _ _ hda] at h4
  have hne1 : (a != c) = true := bne_iff_ne.mpr hac
  have hne2 : (b != d) = true := bne_iff_ne.mpr hbd
  rw [hne1, hne2] at h4
  simp at h4

lemma edges_deg2 :
    ∀ z : Fin 6, (((2 : Fin 6), z) ∈ edges ∨ (z, (2 : Fin 6)) ∈ edges) → z = 0 ∨ z = 1 := by
  intro z hz
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hz
  rcases hz with (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) |
                 (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

lemma lone_reader :
    ∀ j : Fin circ.gates.length, (2 : Fin 6).val ∈ (circ.gates.get j).inputs → j = ⟨3, by decide⟩ := by
  intro j hj
  rcases j with ⟨j, hlt⟩
  match j with
  | 0 | 1 | 2 | 4 | 5 | 6 | 7 => simp [circ] at hj
  | 3 => rfl
  | n + 8 =>
    exfalso
    have h8 : circ.gates.length = 8 := rfl
    omega

lemma bad_h : (circ.wires (List.ofFn badInput)).getD 8 false = true := by
  rw [ofFn_six]
  decide

lemma bad_y : (circ.wires (List.ofFn badInput)).getD 10 false = false := by
  rw [ofFn_six]
  decide

end PEqualNP.Outside.L_meta_18873

theorem PEqualNP.Outside.L_meta_18873 : (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) t → 8 ≤ t) → ¬ (∀ (n : ℕ) (E : List (Fin n × Fin n)) (v u w : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), (∀ e ∈ E, e.1 ≠ e.2) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ((a, b) ∈ E ∨ (b, a) ∈ E) → ((b, c) ∈ E ∨ (c, b) ∈ E) → ((c, d) ∈ E ∨ (d, c) ∈ E) → ((d, a) ∈ E ∨ (a, d) ∈ E) → False) → u ≠ w → ((v, u) ∈ E ∨ (u, v) ∈ E) → ((v, w) ∈ E ∨ (w, v) ∈ E) → (∀ z : Fin n, ((v, z) ∈ E ∨ (z, v) ∈ E) → z = u ∨ z = w) → (∃ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) → (∃ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ≠ w ∧ e.2 ≠ w) → PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = E.any (fun e => x e.1 && x e.2)) → (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => E.any (fun e => x e.1 && x e.2)) t → C.size ≤ t) → v.val ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, v.val ∈ (C.gates.get j).inputs → j = i) → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → n + i.val ∈ (C.gates.get k).inputs → ∀ h ∈ (C.gates.get i).inputs, h ≠ v.val → ∀ y ∈ (C.gates.get k).inputs, y ≠ n + i.val → ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD h false = true → (C.wires (List.ofFn x)).getD y false = true) := by
  intro hLB hAll
  have hy := hAll 6
    PEqualNP.Outside.L_meta_18873.edges
    2 0 1
    PEqualNP.Outside.L_meta_18873.circ
    ⟨3, by decide⟩ ⟨5, by decide⟩
    PEqualNP.Outside.L_meta_18873.edges_irrefl
    PEqualNP.Outside.L_meta_18873.edges_c4free
    (by decide)
    (by decide)
    (by decide)
    PEqualNP.Outside.L_meta_18873.edges_deg2
    ⟨(3, 5), by decide⟩
    ⟨(3, 5), by decide⟩
    PEqualNP.Outside.L_meta_18873.circ_fanInTwo
    PEqualNP.Outside.L_meta_18873.circ_noNot
    PEqualNP.Outside.L_meta_18873.circ_eval
    (fun t ht => by
      rw [PEqualNP.Outside.L_meta_18873.edges_eq_fn] at ht
      exact hLB t ht)
    (by decide)
    PEqualNP.Outside.L_meta_18873.lone_reader
    rfl
    rfl
    (by decide)
    8 (by decide) (by decide)
    10 (by decide) (by decide)
    PEqualNP.Outside.L_meta_18873.badInput
    rfl
    PEqualNP.Outside.L_meta_18873.bad_h
  rw [PEqualNP.Outside.L_meta_18873.bad_y] at hy
  exact Bool.false_ne_true hy
