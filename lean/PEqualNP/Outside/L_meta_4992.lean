import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4992

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stepS (x6 : List (BitVec 24)) (x7 : Bool × ℕ × ℕ) : List (BitVec 24) :=
  x6 ++ [if x7.1 = true then x6.getD x7.2.1 0 ||| x6.getD x7.2.2 0
    else x6.getD x7.2.1 0 &&& x6.getD x7.2.2 0]

def instr (g : Gate) : Bool × ℕ × ℕ :=
  match g.op, g.inputs with
  | GateOp.or, [] => (true, 0, 0)
  | GateOp.or, [a] => (true, a + 2, a + 2)
  | GateOp.or, a :: b :: _ => (true, a + 2, b + 2)
  | _, [] => (false, 1, 1)
  | _, [a] => (false, a + 2, a + 2)
  | _, a :: b :: _ => (false, a + 2, b + 2)

lemma ones_bit (k : Fin 24) : (BitVec.allOnes 24).getLsbD k = true := by
  rw [BitVec.getLsbD_allOnes]; simp

lemma sim_step (k : Fin 24) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (S : List (BitVec 24)) (W : List Bool)
    (hS0 : S.getD 0 0 = 0) (hS1 : S.getD 1 0 = BitVec.allOnes 24)
    (hinv : ∀ i, (S.getD (i + 2) 0).getLsbD k = W.getD i false) :
    (if (instr g).1 = true then S.getD (instr g).2.1 0 ||| S.getD (instr g).2.2 0
      else S.getD (instr g).2.1 0 &&& S.getD (instr g).2.2 0).getLsbD k =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ =>
      show (if (false : Bool) = true then S.getD 1 0 ||| S.getD 1 0
        else S.getD 1 0 &&& S.getD 1 0).getLsbD k = _
      rw [if_neg (by decide), BitVec.getLsbD_and, hS1, ones_bit]
      simp [GateOp.eval]
    | [a], _ =>
      show (if (false : Bool) = true then S.getD (a + 2) 0 ||| S.getD (a + 2) 0
        else S.getD (a + 2) 0 &&& S.getD (a + 2) 0).getLsbD k = _
      rw [if_neg (by decide), BitVec.getLsbD_and, hinv a]
      simp [GateOp.eval]
    | [a, b], _ =>
      show (if (false : Bool) = true then S.getD (a + 2) 0 ||| S.getD (b + 2) 0
        else S.getD (a + 2) 0 &&& S.getD (b + 2) 0).getLsbD k = _
      rw [if_neg (by decide), BitVec.getLsbD_and, hinv a, hinv b]
      simp [GateOp.eval]
  · match ins, hlen with
    | [], _ =>
      show (if (true : Bool) = true then S.getD 0 0 ||| S.getD 0 0
        else S.getD 0 0 &&& S.getD 0 0).getLsbD k = _
      rw [if_pos rfl, BitVec.getLsbD_or, hS0]
      simp [GateOp.eval]
    | [a], _ =>
      show (if (true : Bool) = true then S.getD (a + 2) 0 ||| S.getD (a + 2) 0
        else S.getD (a + 2) 0 &&& S.getD (a + 2) 0).getLsbD k = _
      rw [if_pos rfl, BitVec.getLsbD_or, hinv a]
      simp [GateOp.eval]
    | [a, b], _ =>
      show (if (true : Bool) = true then S.getD (a + 2) 0 ||| S.getD (b + 2) 0
        else S.getD (a + 2) 0 &&& S.getD (b + 2) 0).getLsbD k = _
      rw [if_pos rfl, BitVec.getLsbD_or, hinv a, hinv b]
      simp [GateOp.eval]

lemma sim_fold (k : Fin 24) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (S : List (BitVec 24)) (W : List Bool), S.length = W.length + 2 →
      S.getD 0 0 = 0 → S.getD 1 0 = BitVec.allOnes 24 →
      (∀ i, (S.getD (i + 2) 0).getLsbD k = W.getD i false) →
      ∀ i, (((gs.map instr).foldl stepS S).getD (i + 2) 0).getLsbD k =
        (gs.foldl stepW W).getD i false := by
  induction gs with
  | nil => intro S W _ _ _ hinv i; exact hinv i
  | cons g gs ih =>
    intro S W hl h0 h1 hinv
    obtain ⟨hop, hlen⟩ := hgs g (by simp)
    have hv := sim_step k g hop hlen S W h0 h1 hinv
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · simp [stepS, stepW, hl]
    · simp only [stepS]; rw [List.getD_append _ _ _ _ (by omega)]; exact h0
    · simp only [stepS]; rw [List.getD_append _ _ _ _ (by omega)]; exact h1
    · intro i
      simp only [stepS, stepW]
      by_cases hi : i < W.length
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
        exact hinv i
      · by_cases hie : i = W.length
        · subst hie
          rw [show W.length + 2 = S.length by omega,
            List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
            List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
          simp only [List.getD_cons_zero]
          exact hv
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
          simp

end PEqualNP.Outside.L_meta_4992

theorem PEqualNP.Outside.L_meta_4992 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (BitVec (24 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : List (Bool × ℕ × ℕ)), x4.length = x1.size ∧ ∀ (x5 : Fin (24 : ℕ)), ((List.foldl (fun (x6 : List (BitVec (24 : ℕ))) (x7 : Bool × ℕ × ℕ) => x6 ++ [if x7.1 = Bool.true then x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) ||| x6.getD x7.2.2 (0 : BitVec (24 : ℕ)) else x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) &&& x6.getD x7.2.2 (0 : BitVec (24 : ℕ))]) ((0 : BitVec (24 : ℕ)) :: BitVec.allOnes (24 : ℕ) :: x2) x4).getD (x1.output + (2 : ℕ)) (0 : BitVec (24 : ℕ))).getLsbD ↑x5 = x1.eval (List.map (fun (x6 : BitVec (24 : ℕ)) => x6.getLsbD ↑x5) x2) := by
  intro C xs hM
  refine ⟨C.gates.map PEqualNP.Outside.L_meta_4992.instr, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  intro k
  have hgs : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hM g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have := PEqualNP.Outside.L_meta_4992.sim_fold k C.gates hgs
    ((0 : BitVec 24) :: BitVec.allOnes 24 :: xs) (xs.map fun v => v.getLsbD k)
    (by simp) (by simp) (by simp)
    (by
      intro i
      simp only [List.getD_cons_succ]
      by_cases hi : i < xs.length
      · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simp; exact hi)]
        simp
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
        simp)
    C.output
  exact this
