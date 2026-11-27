import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8911

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8911

theorem PEqualNP.Outside.L_meta_8911 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     have x6 : Set (Set (Fin x1)) := {∅, Set.univ} ∪ Set.range fun (x6 : Fin x2) => {x7 : Fin x1 | x3 x7 x6 = Bool.true};     ∃ (x7 : List (Set (Fin x1))),       x7.length ≤ x4.size ∧         (∀ (x8 : Fin x7.length),             have x9 : Set (Set (Fin x1)) := x6 ∪ {x9 : Set (Fin x1) | x9 ∈ List.take (↑x8) x7};             x7.getD ↑x8 ∅ ∉ x9 ∧ ∃ x10 ∈ x9, ∃ x11 ∈ x9, x7.getD ↑x8 ∅ = x10 ∪ x11 ∨ x7.getD ↑x8 ∅ = x10 ∩ x11) ∧           {x8 : Fin x1 | PEqualNP.MetaComplexity.circuitFun x2 x4 (x3 x8) = Bool.true} ∈ x6 ∪ {x8 : Set (Fin x1) | x8 ∈ x7} := by
  intro r n A C hC
  intro base
  classical
  let V : List PEqualNP.CircuitLowerBounds.Gate → ℕ → Set (Fin r) := fun gs w => {i | (PEqualNP.Outside.L_meta_8911.run gs (List.ofFn (A i))).getD w false = true}
  have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∃ L : List (Set (Fin r)), L.length ≤ gs.length ∧
        (∀ k : Fin L.length, L.getD k ∅ ∉ base ∪ {s | s ∈ List.take k L} ∧ ∃ a ∈ base ∪ {s | s ∈ List.take k L}, ∃ b ∈ base ∪ {s | s ∈ List.take k L}, L.getD k ∅ = a ∪ b ∨ L.getD k ∅ = a ∩ b) ∧
        ∀ w, V gs w ∈ base ∪ {s | s ∈ L} := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨[], by simp, fun k => k.elim0, fun w => Or.inl ?_⟩
      by_cases hw : w < n
      · refine Or.inr ⟨⟨w, hw⟩, ?_⟩
        ext i
        show A i ⟨w, hw⟩ = true ↔ (List.ofFn (A i)).getD w false = true
        rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]
      · refine Or.inl (Or.inl ?_)
        ext i
        show (List.ofFn (A i)).getD w false = true ↔ False
        rw [List.getD_eq_default _ _ (by simp; omega)]
        simp
    | append_singleton gs g ih =>
      intro hg
      obtain ⟨L, h1, h2, h3⟩ := ih fun g' hg' => hg g' (List.mem_append_left _ hg')
      obtain ⟨ho, hl⟩ := hg g (by simp)
      have len : ∀ i, (PEqualNP.Outside.L_meta_8911.run gs (List.ofFn (A i))).length = n + gs.length := fun i => by rw [PEqualNP.Outside.L_meta_8911.run_length, List.length_ofFn]
      have old : ∀ w, w < n + gs.length → V (gs ++ [g]) w = V gs w := by
        intro w hw
        ext i
        show (PEqualNP.Outside.L_meta_8911.run (gs ++ [g]) (List.ofFn (A i))).getD w false = true ↔ _
        rw [PEqualNP.Outside.L_meta_8911.run_snoc, PEqualNP.Outside.L_meta_8911.getD_lt _ _ _ (by rw [len]; exact hw)]
        rfl
      have big : ∀ w, n + gs.length < w → V (gs ++ [g]) w = ∅ := by
        intro w hw
        ext i
        show (PEqualNP.Outside.L_meta_8911.run (gs ++ [g]) (List.ofFn (A i))).getD w false = true ↔ False
        rw [PEqualNP.Outside.L_meta_8911.run_snoc, List.getD_eq_default _ _ (by rw [List.length_append, len]; simp; omega)]
        simp
      let Z : Set (Fin r) := V (gs ++ [g]) (n + gs.length)
      have hZ : ∀ i, i ∈ Z ↔ g.op.eval (g.inputs.map fun w => (PEqualNP.Outside.L_meta_8911.run gs (List.ofFn (A i))).getD w false) = true := by
        intro i
        show (PEqualNP.Outside.L_meta_8911.run (gs ++ [g]) (List.ofFn (A i))).getD (n + gs.length) false = true ↔ _
        rw [PEqualNP.Outside.L_meta_8911.run_snoc, ← len i, PEqualNP.Outside.L_meta_8911.getD_at]
      have hZ2 : ∃ a ∈ base ∪ {s | s ∈ L}, ∃ b ∈ base ∪ {s | s ∈ L}, Z = a ∪ b ∨ Z = a ∩ b := by
        have hE : (∅ : Set (Fin r)) ∈ base ∪ {s | s ∈ L} := Or.inl (Or.inl (Or.inl rfl))
        have hU : (Set.univ : Set (Fin r)) ∈ base ∪ {s | s ∈ L} := Or.inl (Or.inl (Or.inr rfl))
        rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rcases ho with ho | ho
          · refine ⟨_, hU, _, hU, Or.inr ?_⟩
            ext i; rw [hZ, hin, ho]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          · refine ⟨_, hE, _, hE, Or.inl ?_⟩
            ext i; rw [hZ, hin, ho]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        · refine ⟨_, h3 a, _, h3 a, Or.inl ?_⟩
          ext i
          rw [hZ, hin]
          show _ ↔ _ ∨ _
          rcases ho with ho | ho <;> rw [ho] <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval, V]
        · rcases ho with ho | ho
          · refine ⟨_, h3 a, _, h3 b, Or.inr ?_⟩
            ext i
            rw [hZ, hin, ho]
            show _ ↔ _ ∧ _
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval, V]
          · refine ⟨_, h3 a, _, h3 b, Or.inl ?_⟩
            ext i
            rw [hZ, hin, ho]
            show _ ↔ _ ∨ _
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval, V]
        · rw [hin] at hl; simp at hl
      by_cases hmem : Z ∈ base ∪ {s | s ∈ L}
      · refine ⟨L, by simp; omega, h2, fun w => ?_⟩
        rcases Nat.lt_trichotomy w (n + gs.length) with h | h | h
        · rw [old w h]; exact h3 w
        · rw [h]; exact hmem
        · rw [big w h]; exact Or.inl (Or.inl (Or.inl rfl))
      · refine ⟨L ++ [Z], by simp; omega, ?_, fun w => ?_⟩
        · rintro ⟨k, hk⟩
          by_cases hkL : k < L.length
          · have e1 : List.take k (L ++ [Z]) = List.take k L := List.take_append_of_le_length (by omega)
            have e2 : (L ++ [Z]).getD k ∅ = L.getD k ∅ := PEqualNP.Outside.L_meta_8911.getD_ltz ∅ _ _ _ hkL
            have := h2 ⟨k, hkL⟩
            simp only [e1, e2]
            exact this
          · have hk : k = L.length := by simp at hk; omega
            subst hk
            have e1 : List.take L.length (L ++ [Z]) = L := by simp
            have e2 : (L ++ [Z]).getD L.length ∅ = Z := PEqualNP.Outside.L_meta_8911.getD_at' ∅ _ _
            simp only [e1, e2]
            exact ⟨hmem, hZ2⟩
        · have up : ∀ s, s ∈ base ∪ {s | s ∈ L} → s ∈ base ∪ {s | s ∈ L ++ [Z]} := by
            rintro s (h | h)
            · exact Or.inl h
            · exact Or.inr (List.mem_append_left _ h)
          rcases Nat.lt_trichotomy w (n + gs.length) with h | h | h
          · rw [old w h]; exact up _ (h3 w)
          · rw [h]; exact Or.inr (List.mem_append_right _ (by simp [Z]))
          · rw [big w h]; exact Or.inl (Or.inl (Or.inl rfl))
  obtain ⟨L, h1, h2, h3⟩ := key C.gates fun g hg => by simpa using hC g hg
  exact ⟨L, h1, h2, h3 C.output⟩
