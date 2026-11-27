import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3507_1
    (h12 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 1 || x 2]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False)
    (h16 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 1 || x 6]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False)
    (h23 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 2 || x 3]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False)
    (h27 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 2 || x 7]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∈ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by
  let σ : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let edges : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let target (x : Fin 9 → Bool) : Bool := edges.any fun e => x e.1 && x e.2
  have hσ₀ : σ 0 = 0 := rfl
  have hσ₄ : σ 4 = 4 := rfl
  have hσ₂ : ∀ i, σ (σ i) = i := by decide +kernel
  have htarget (x : Fin 9 → Bool) : target (x ∘ σ) = target x := by
    have h : ∀ z : Fin 9 → Bool, target (z ∘ σ) = target z := by
      unfold target σ edges
      decide +kernel
    exact h x
  let index (i : ℕ) : ℕ := if hi : i < 9 then (σ ⟨i, hi⟩).val else i
  let gate (g : Gate) : Gate := ⟨g.op, g.inputs.map index⟩
  let circuit (C : Circuit) : Circuit := ⟨C.gates.map gate, index C.output⟩
  have gate_size (C : Circuit) : (circuit C).size = C.size := by
    change (C.gates.map gate).length = C.gates.length
    exact List.length_map gate
  have gate_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (circuit C) := by
    intro g hg
    change g ∈ C.gates.map gate at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := h g' hg'
    exact ⟨hop, by simpa [gate] using hlen⟩
  have read_index (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
      (List.ofFn x ++ tail).getD (index i) false =
        (List.ofFn (x ∘ σ) ++ tail).getD i false := by
    by_cases hi : i < 9
    · have hσi := (σ ⟨i, hi⟩).isLt
      simp only [index, dite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, ite_eq_left hi, ite_eq_left hσi, List.getElem?_ofFn, dite_eq_left hσi,
        Function.comp_apply]
    · simp only [index, dite_eq_right hi, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, ite_eq_right hi]
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have fold_index (x : Fin 9 → Bool) (gs : List Gate) (tail : List Bool) (i : ℕ) :
      ((gs.map gate).foldl step (List.ofFn x ++ tail)).getD (index i) false =
        (gs.foldl step (List.ofFn (x ∘ σ) ++ tail)).getD i false := by
    induction gs generalizing tail with
    | nil => exact read_index x tail i
    | cons g gs ih =>
      have hbits : (gate g).op.eval ((gate g).inputs.map
          (fun j => (List.ofFn x ++ tail).getD j false)) =
          g.op.eval (g.inputs.map (fun j => (List.ofFn (x ∘ σ) ++ tail).getD j false)) := by
        simp only [gate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact read_index x tail j
      simpa only [List.map_cons, List.foldl_cons, step, List.append_assoc, hbits] using
        ih (tail ++ [g.op.eval (g.inputs.map (fun j =>
          (List.ofFn (x ∘ σ) ++ tail).getD j false))])
  have eval_index (C : Circuit) (x : Fin 9 → Bool) (tail : List Bool) :
      (circuit C).eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ σ) ++ tail) :=
    fold_index x C.gates tail C.output
  let good (u v : Fin 9) : Prop := ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) = target x) → False
  have flip (u v : Fin 9) (h : good u v) : good v u := by
    intro C hf hc he
    exact h C hf hc (fun x => by simpa only [Bool.or_comm (x u) (x v)] using he x)
  have transform (u v : Fin 9) (h : good u v) : good (σ u) (σ v) := by
    intro C hf hc he
    apply h (circuit C) (gate_fan C hf) (by simpa only [gate_size] using hc)
    intro x
    rw [eval_index]
    simpa only [Function.comp_apply, hσ₀, hσ₄, hσ₂, htarget] using he (x ∘ σ)
  have classification : ∀ a b : Fin 9,
      a.val * 10 + b.val ∈ ([12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] : List ℕ) →
      ∃ u v : Fin 9, ((u = 1 ∧ v = 2) ∨ (u = 1 ∧ v = 6) ∨
        (u = 2 ∧ v = 3) ∨ (u = 2 ∧ v = 7)) ∧
      ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
        (a = σ u ∧ b = σ v) ∨ (a = σ v ∧ b = σ u)) := by
    unfold σ
    decide +kernel
  intro a b C _ _ _ _ _ hpair hfan hsize heval
  obtain ⟨u, v, huv, hloc⟩ := classification a b hpair
  have hgood : good u v := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact h16
    · exact h23
    · exact h27
  have hfinal : good a b := by
    rcases hloc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hgood
    · exact flip _ _ hgood
    · exact transform _ _ hgood
    · exact flip _ _ (transform _ _ hgood)
  apply hfinal C hfan hsize
  intro x
  simpa only [target, edges, List.any_cons, List.any_nil, Bool.or_false,
    Prod.fst, Prod.snd, Bool.or_assoc] using heval x
