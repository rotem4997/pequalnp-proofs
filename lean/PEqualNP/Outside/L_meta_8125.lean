import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8125

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def srt : List ℕ → List ℕ
  | [a, b] => if a < b then [a, b] else if b < a then [b, a] else [a]
  | l => l

def fix (g : Gate) : Gate := ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else srt g.inputs⟩

theorem fix_ok (g : Gate) (hl : g.inputs.length ≤ 2) : (∀ i ∈ (fix g).inputs, i ∈ g.inputs) ∧ List.Pairwise (fun a b : ℕ => a < b) (fix g).inputs ∧
    ((fix g).op = GateOp.not → (fix g).inputs.length ≤ 1) ∧
    ((g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) → ∀ f : ℕ → Bool, (fix g).op.eval ((fix g).inputs.map f) = g.op.eval (g.inputs.map f)) ∧ (fix g).inputs.length ≤ 2 := by
  obtain ⟨o, l⟩ := g
  simp only [fix]
  simp only at hl
  have tk : ∀ i ∈ l.take 1, i ∈ l := fun i hi => List.mem_of_mem_take hi
  have hs : (∀ i ∈ srt l, i ∈ l) ∧ List.Pairwise (fun a b : ℕ => a < b) (srt l) ∧ (srt l).length ≤ 2 ∧ ∀ f : ℕ → Bool, ((srt l).map f).all id = (l.map f).all id ∧ ((srt l).map f).any id = (l.map f).any id := by
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [srt]
    · simp [srt]
    · simp only [srt]
      split_ifs with h1 h2
      · simp [h1]
      · refine ⟨by simp [or_comm], by simp [h2], by simp, fun f => ?_⟩
        simp [Bool.and_comm, Bool.or_comm]
      · have : a = b := by omega
        subst this
        simp
    · simp at hl
  have t1 : List.Pairwise (fun a b : ℕ => a < b) (l.take 1) ∧ (l.take 1).length ≤ 1 := by
    rcases l with _ | ⟨a, l⟩ <;> simp
  split_ifs with h
  · refine ⟨tk, t1.1, fun _ => t1.2, ?_, by have := t1.2; omega⟩
    rintro (rfl | rfl | rfl) f
    · simp [GateOp.eval] at h
    · simp [GateOp.eval] at h
    · rcases l with _ | ⟨a, l⟩ <;> simp [GateOp.eval]
  · refine ⟨hs.1, hs.2.1, ?_, ?_, hs.2.2.1⟩
    · rintro rfl
      simp [GateOp.eval] at h
    · rintro (rfl | rfl | rfl) f
      · exact (hs.2.2.2 f).1
      · exact (hs.2.2.2 f).2
      · simp [GateOp.eval] at h

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8125

theorem PEqualNP.Outside.L_meta_8125 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (29 : ℕ)) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ x4.output = x1.output ∧ (∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (29 : ℕ)) ∧ (∀ x5 ∈ x4.gates, List.Pairwise (fun (x7 x8 : ℕ) => x7 < x8) x5.inputs ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ))) ∧ ∀ (x5 : List Bool), x4.eval x5 = x1.eval x5 := by
  intro C hC hb
  refine ⟨⟨C.gates.map PEqualNP.Outside.L_meta_8125.fix, C.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], rfl, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hC g' hg'
    exact ⟨h1, (PEqualNP.Outside.L_meta_8125.fix_ok g' h2).2.2.2.2⟩
  · intro g hg i hi
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact hb g' hg' i ((PEqualNP.Outside.L_meta_8125.fix_ok g' (hC g' hg').2).1 i hi)
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have h := PEqualNP.Outside.L_meta_8125.fix_ok g' (hC g' hg').2
    exact ⟨h.2.1, h.2.2.1⟩
  · intro x
    have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gs, g ∈ C.gates) → ∀ d : List Bool,
        (gs.map PEqualNP.Outside.L_meta_8125.fix).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d := by
      intro gs
      induction gs with
      | nil => intro _ d; rfl
      | cons g gs ih =>
        intro hg d
        rw [List.map_cons, List.foldl_cons, List.foldl_cons, ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h'))]
        congr 3
        have hgC := hg g List.mem_cons_self
        exact (PEqualNP.Outside.L_meta_8125.fix_ok g (hC g hgC).2).2.2.2.1 (by simpa using (hC g hgC).1) (fun i => d.getD i false)
    change (List.foldl _ x _).getD _ _ = (List.foldl _ x _).getD _ _
    rw [key C.gates (fun g h => h) x]
