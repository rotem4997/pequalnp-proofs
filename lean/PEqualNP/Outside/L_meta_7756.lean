import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7756_aux

open PEqualNP.CircuitLowerBounds

def gateOf (d : Bool × ℕ × ℕ) : Gate :=
  ⟨if d.1 = true then GateOp.or else GateOp.and, [d.2.1, d.2.2]⟩

def step (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) : List ℕ :=
  x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]

theorem hget (acc : List ℕ) (k i : ℕ) :
    (acc.map (fun x => x.testBit k)).getD i false = (acc.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases acc[i]? <;> simp

theorem wires_eq (k : ℕ) : ∀ (l : List (Bool × ℕ × ℕ)) (acc : List ℕ),
    (l.map gateOf).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (acc.map (fun x => x.testBit k)) = (l.foldl step acc).map (fun x => x.testBit k) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons d t ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih (step acc d)]
    congr 1
    obtain ⟨b, i, j⟩ := d
    cases b <;>
      simp [step, gateOf, GateOp.eval] <;>
      cases acc[i]? <;> cases acc[j]? <;> simp

theorem len_eq : ∀ (l : List (Bool × ℕ × ℕ)) (acc : List ℕ),
    (l.foldl step acc).length = acc.length + l.length := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons d t ih =>
    intro acc
    simp only [List.foldl_cons, ih, List.length_cons]
    simp [step]
    omega

theorem last_eq (l : List ℕ) : l.getLastD 0 = l.getD (l.length - 1) 0 := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton t a _ => simp

end PEqualNP.Outside.L_meta_7756_aux

open PEqualNP.Outside.L_meta_7756_aux in
theorem PEqualNP.Outside.L_meta_7756 : ∀ (x1 : List (Bool × ℕ × ℕ)), ∀ x2 ∈ x1.head?, x2 ∈ [(Bool.false, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (1 : ℕ)), (Bool.true, (0 : ℕ), (13 : ℕ)), (Bool.true, (2 : ℕ), (13 : ℕ))] → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x1.length ∧ (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x5.gates.head? = Option.some x6 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ ∀ (x6 : List ℕ) (x7 : ℕ), x6.length = (26 : ℕ) → x5.eval (List.map (fun (x9 : ℕ) => x9.testBit x7) x6) = ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]) x6 x1).getLastD (0 : ℕ)).testBit x7 := by
  intro x1 x2 h2 hmem
  cases x1 with
  | nil => simp at h2
  | cons d t =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h2
    subst h2
    refine ⟨⟨(d :: t).map gateOf, 26 + (d :: t).length - 1⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨e, _, rfl⟩ := hg
      obtain ⟨b, i, j⟩ := e
      cases b <;> simp [gateOf]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · refine ⟨gateOf d, by simp, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> simp [gateOf]
    · intro x6 x7 h6
      have hw := wires_eq x7 (d :: t) x6
      have hl := len_eq (d :: t) x6
      change List.getD (List.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.map (fun (x : ℕ) => x.testBit x7) x6) ((d :: t).map gateOf)) (26 + (d :: t).length - 1) false = ((List.foldl step x6 (d :: t)).getLastD 0).testBit x7
      rw [hw, hget, last_eq, hl, h6]
