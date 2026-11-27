import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2217

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def ext (C : Circuit) (k : ℕ) : Circuit :=
  ⟨C.gates.map (reGate Nat.succ) ++
    [⟨GateOp.and, [0, k + 1]⟩, ⟨GateOp.or, [C.output + 1, 25 + C.gates.length + 1]⟩],
    25 + C.gates.length + 2⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_len (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h; simp

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma step_shift (b : Bool) (w : List Bool) (g : Gate) :
    stepW (b :: w) (reGate Nat.succ g) = b :: stepW w g := by
  have hm : (g.inputs.map Nat.succ).map (fun i => (b :: w).getD i false)
      = g.inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => by simp)
  show (b :: w) ++ [g.op.eval ((g.inputs.map Nat.succ).map fun i => (b :: w).getD i false)] = _
  rw [hm]
  rfl

lemma fold_shift (b : Bool) (gs : List Gate) :
    ∀ w : List Bool, (gs.map (reGate Nat.succ)).foldl stepW (b :: w) = b :: gs.foldl stepW w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_shift, ih]

lemma final (W : List Bool) (b : Bool) (k o L : ℕ) (hL : L = W.length) (ho : o < L) :
    (stepW (stepW (b :: W) ⟨GateOp.and, [0, k + 1]⟩) ⟨GateOp.or, [o + 1, L + 1]⟩).getD (L + 2) false
      = (W.getD o false || b && W.getD k false) := by
  subst hL
  have ha : stepW (b :: W) ⟨GateOp.and, [0, k + 1]⟩ = (b :: W) ++ [b && W.getD k false] := by
    show (b :: W) ++ [GateOp.and.eval [(b :: W).getD 0 false, (b :: W).getD (k + 1) false]] = _
    simp [GateOp.eval]
  rw [ha]
  have h1 : ((b :: W) ++ [b && W.getD k false]).getD (o + 1) false = W.getD o false := by
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp
  have h2 : ((b :: W) ++ [b && W.getD k false]).getD (W.length + 1) false
      = (b && W.getD k false) := getD_snoc_len _ _ _ (by simp)
  have hs : stepW ((b :: W) ++ [b && W.getD k false]) ⟨GateOp.or, [o + 1, W.length + 1]⟩
      = ((b :: W) ++ [b && W.getD k false]) ++ [W.getD o false || b && W.getD k false] := by
    show ((b :: W) ++ [b && W.getD k false]) ++
      [GateOp.or.eval [((b :: W) ++ [b && W.getD k false]).getD (o + 1) false,
        ((b :: W) ++ [b && W.getD k false]).getD (W.length + 1) false]] = _
    rw [h1, h2]
    simp [GateOp.eval]
  rw [hs]
  exact getD_snoc_len _ _ _ (by simp)

lemma main (C : Circuit) (k : ℕ) (b : Bool) (x : Fin 25 → Bool)
    (ho : C.output < 25 + C.gates.length) :
    (ext C k).eval (b :: List.ofFn x)
      = (C.eval (List.ofFn x) || b && (C.wires (List.ofFn x)).getD k false) := by
  have hlen : 25 + C.gates.length = (C.gates.foldl stepW (List.ofFn x)).length := by
    rw [fold_len]; simp
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  unfold ext
  simp only
  rw [List.foldl_append, fold_shift]
  exact final (C.gates.foldl stepW (List.ofFn x)) b k C.output (25 + C.gates.length) hlen ho

lemma mono (C : Circuit) (k : ℕ) (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (ext C k) := by
  intro g hg
  unfold ext at hg
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hg
  rcases hg with ⟨g', hg', rfl⟩ | rfl | rfl
  · have := h g' hg'
    simpa [reGate] using this
  · simp
  · simp

end PEqualNP.Outside.L_meta_2217

theorem PEqualNP.Outside.L_meta_2217 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (2 : ℕ) ∧ ∀ (x7 : Bool) (x8 : Fin (25 : ℕ) → Bool), x6.eval (x7 :: List.ofFn x8) = (x1.eval (List.ofFn x8) || x7 && (x1.wires (List.ofFn x8)).getD x2 Bool.false) := by
  intro C k hC ho _
  refine ⟨PEqualNP.Outside.L_meta_2217.ext C k, PEqualNP.Outside.L_meta_2217.mono C k hC, ?_, ?_⟩
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2217.ext,
      List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  · intro b x
    exact PEqualNP.Outside.L_meta_2217.main C k b x ho
