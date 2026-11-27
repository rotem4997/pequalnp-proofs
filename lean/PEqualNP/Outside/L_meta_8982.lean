import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8982
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def sg (N a i : ℕ) : ℕ := if i < N then i else i + a

def rgS (N a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg N a)⟩

theorem keyS (N : ℕ) (x A G : List Bool) (hx : x.length = N) (i : ℕ) :
    (x ++ G).getD i false = (x ++ A ++ G).getD (sg N A.length i) false := by
  unfold sg
  by_cases hi : i < N
  · rw [if_pos hi, List.getD_append _ _ _ _ (by omega), List.append_assoc,
      List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp
    omega

theorem simSh (N : ℕ) (x A : List Bool) (hx : x.length = N) : ∀ (gs : List Gate) (G : List Bool),
    ∃ G' : List Bool, G'.length = G.length + gs.length ∧ wf gs (x ++ G) = x ++ G' ∧
      wf (gs.map (rgS N A.length)) (x ++ A ++ G) = x ++ A ++ G' := by
  intro gs
  induction gs with
  | nil => intro G; exact ⟨G, rfl, rfl, rfl⟩
  | cons g gs ih =>
    intro G
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (rgS N A.length g).op.eval ((rgS N A.length g).inputs.map fun i => (x ++ A ++ G).getD i false)
        = g.op.eval (g.inputs.map fun i => (x ++ G).getD i false) := by
      show g.op.eval ((g.inputs.map (sg N A.length)).map fun i => (x ++ A ++ G).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (keyS N x A G hx a).symm
    rw [hv, List.append_assoc x G, List.append_assoc (x ++ A) G]
    obtain ⟨G', h1, h2, h3⟩ := ih (G ++ [g.op.eval (g.inputs.map fun i => (x ++ G).getD i false)])
    exact ⟨G', by simp at h1 ⊢; omega, h2, h3⟩

end PEqualNP.Outside.L_meta_8982

open PEqualNP.Outside.L_meta_8982 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8982 : ∀ (N L1 L2 : ℕ) (D : Set (List Bool)) (P Q : List PEqualNP.CircuitLowerBounds.Gate) (w1 : Fin L1 → ℕ) (w2 : Fin L2 → ℕ) (f1 : Fin L1 → List Bool → Bool) (f2 : Fin L2 → List Bool → Bool), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 (⟨Q, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w1 j) false = f1 j x) → (∀ x ∈ D, ∀ j, ((⟨Q, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w2 j) false = f2 j x) → ∃ R : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.MetaComplexity.Monotone2 (⟨R, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ R.length = P.length + Q.length ∧ ∃ (v1 : Fin L1 → ℕ) (v2 : Fin L2 → ℕ), ∀ x ∈ D, (∀ j, ((⟨R, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (v1 j) false = f1 j x) ∧ ∀ j, ((⟨R, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (v2 j) false = f2 j x := by
  intro N L1 L2 D P Q w1 w2 f1 f2 hD hP hQ h1 h2
  refine ⟨P ++ Q.map (rgS N P.length), ?_, by simp, fun j => if w1 j < N + P.length then w1 j else N + P.length + Q.length,
    fun j => if w2 j < N + Q.length then sg N P.length (w2 j) else N + P.length + Q.length, fun x hx => ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hP g h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hQ g0 hg0
      exact ⟨this.1, by simpa [rgS] using this.2⟩
  · have hxl := hD x hx
    obtain ⟨A, hA1, hA2, _⟩ := simSh N x [] hxl P []
    rw [List.append_nil] at hA2
    have hA1' : A.length = P.length := by simpa using hA1
    obtain ⟨B, hB1, hB2, hB3⟩ := simSh N x A hxl Q []
    rw [List.append_nil] at hB2 hB3
    have hB1' : B.length = Q.length := by simpa using hB1
    rw [hA1'] at hB3
    have hR : wf (P ++ Q.map (rgS N P.length)) x = x ++ A ++ B := by
      rw [wf_append, hA2, hB3]
    have hlenR : (x ++ A ++ B).length = N + P.length + Q.length := by simp; omega
    constructor
    · intro j
      show (wf (P ++ Q.map (rgS N P.length)) x).getD _ false = f1 j x
      rw [hR, ← h1 x hx j]
      show _ = (wf P x).getD (w1 j) false
      rw [hA2]
      dsimp only
      by_cases hw : w1 j < N + P.length
      · rw [if_pos hw, List.getD_append _ _ _ _ (by simp; omega)]
      · rw [if_neg hw, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro j
      show (wf (P ++ Q.map (rgS N P.length)) x).getD _ false = f2 j x
      rw [hR, ← h2 x hx j]
      show _ = (wf Q x).getD (w2 j) false
      rw [hB2]
      dsimp only
      by_cases hw : w2 j < N + Q.length
      · rw [if_pos hw]
        have := keyS N x A B hxl (w2 j)
        rw [hA1'] at this
        exact this.symm
      · rw [if_neg hw, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
