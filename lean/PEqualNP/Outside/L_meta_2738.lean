import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2738

open PEqualNP.CircuitLowerBounds

-- Rebuild a ten-input circuit on twelve inputs, input 10 fixed false and input 11 fixed true:
-- gate k reads only earlier wires, a read of a wire that does not exist yet goes to input 10,
-- constant and one-input gates become two-input gates against the fixed inputs.
def mp (k i : ℕ) : ℕ := if i < 10 then i else if i < 10 + k then i + 2 else 10

def ng (k : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.not, [] => ⟨GateOp.not, [10]⟩
  | GateOp.not, a :: _ => ⟨GateOp.not, [mp k a]⟩
  | GateOp.and, [] => ⟨GateOp.or, [10, 11]⟩
  | GateOp.and, [a] => ⟨GateOp.and, [mp k a, 11]⟩
  | GateOp.and, a :: b :: _ =>
      if mp k a = mp k b then ⟨GateOp.and, [mp k a, 11]⟩ else ⟨GateOp.and, [mp k a, mp k b]⟩
  | GateOp.or, [] => ⟨GateOp.and, [10, 11]⟩
  | GateOp.or, [a] => ⟨GateOp.and, [mp k a, 11]⟩
  | GateOp.or, a :: b :: _ =>
      if mp k a = mp k b then ⟨GateOp.and, [mp k a, 11]⟩ else ⟨GateOp.or, [mp k a, mp k b]⟩
  | _, _ => ⟨GateOp.and, [10, 11]⟩

def nl : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => ng k g :: nl (k + 1) gs

theorem nl_length : ∀ (k : ℕ) (gs : List Gate), (nl k gs).length = gs.length
  | _, [] => rfl
  | k, _ :: gs => by simp [nl, nl_length (k + 1) gs]

theorem mp_lt (k i : ℕ) : mp k i < 12 + k := by
  unfold mp; split_ifs <;> omega

theorem mp_ne (k i : ℕ) : mp k i ≠ 11 := by
  unfold mp; split_ifs <;> omega

def Good (j : ℕ) (g : Gate) : Prop :=
  (∀ x ∈ g.inputs, x < 12 + j) ∧ g.inputs.Nodup ∧
    (g.op = GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ GateOp.not ∧ g.inputs.length = 2)

theorem ng_good (j : ℕ) (g : Gate) : Good j (ng j g) := by
  rcases g with ⟨op, ins⟩
  have h1 := mp_lt j
  have h2 := mp_ne j
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [ng, Good] <;>
    (try split_ifs) <;> simp_all <;> omega

theorem ng_fan (j : ℕ) (g : Gate) :
    (ng j g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (ng j g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [ng] <;>
    (try split_ifs) <;> simp

theorem nl_mem : ∀ (k : ℕ) (gs : List Gate) (g' : Gate), g' ∈ nl k gs → ∃ j g, g' = ng j g
  | _, [], _, h => by simp [nl] at h
  | k, g :: gs, g', h => by
    simp only [nl, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, h⟩
    · exact nl_mem (k + 1) gs g' h

theorem nl_good : ∀ (k : ℕ) (gs : List Gate) (i : ℕ) (h : i < (nl k gs).length),
    Good (k + i) ((nl k gs).get ⟨i, h⟩)
  | _, [], i, h => by simp [nl] at h
  | k, g :: gs, 0, h => by simpa [nl] using ng_good k g
  | k, g :: gs, i + 1, h => by
    have h' : i < (nl (k + 1) gs).length := by simp only [nl, List.length_cons] at h; omega
    have := nl_good (k + 1) gs i h'
    rw [show k + 1 + i = k + (i + 1) by omega] at this
    simpa [nl] using this

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (w : List Bool) (b : Bool) (t : ℕ) :
    (w ++ [b]).getD t false =
      if t < w.length then w.getD t false else if t = w.length then b else false := by
  by_cases h1 : t < w.length
  · simp [h1, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · by_cases h2 : t = w.length
    · subst h2; simp
    · have h4 : ¬ t < (w ++ [b]).length := by simp; omega
      rw [List.getD_eq_default _ _ (not_lt.mp h4)]
      simp [h1, h2]

theorem ng_eval (k : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (W W' : List Bool) (hinv : ∀ i, W'.getD (mp k i) false = W.getD i false)
    (h10 : W'.getD 10 false = false) (h11 : W'.getD 11 false = true) :
    (ng k g).op.eval ((ng k g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals try (simp at hlen; done)
  all_goals simp only [ng]
  all_goals (try split_ifs with hab)
  all_goals simp only [GateOp.eval, List.map_cons, List.map_nil, hinv, h10, h11]
  all_goals first
    | (have hb : W.getD b false = W.getD a false := by rw [← hinv b, ← hab, hinv a]
       rw [hb]; simp)
    | simp

theorem fold_inv : ∀ (gs : List Gate) (k : ℕ) (W W' : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    W.length = 10 + k → W'.length = 12 + k →
    (∀ i, W'.getD (mp k i) false = W.getD i false) →
    W'.getD 10 false = false → W'.getD 11 false = true →
    ∀ i, ((nl k gs).foldl step W').getD (mp (k + gs.length) i) false =
      (gs.foldl step W).getD i false := by
  intro gs
  induction gs with
  | nil => intro k W W' _ _ _ hinv _ _ i; simpa [nl] using hinv i
  | cons g gs ih =>
    intro k W W' hg hW hW' hinv h10 h11 i
    have hv := ng_eval k g (hg g (List.mem_cons_self ..)) W W' hinv h10 h11
    simp only [nl, List.foldl_cons, List.length_cons]
    rw [show k + (gs.length + 1) = (k + 1) + gs.length by omega]
    apply ih (k + 1) (step W g) (step W' (ng k g)) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp only [step, List.length_append, List.length_singleton]; omega
    · simp only [step, List.length_append, List.length_singleton]; omega
    · intro j
      simp only [step]
      rw [hv, getD_snoc, getD_snoc, hW, hW']
      by_cases hj1 : j < 10
      · have e : mp (k + 1) j = j := by simp [mp, hj1]
        have e' : mp k j = j := by simp [mp, hj1]
        have h5 := hinv j
        rw [e'] at h5
        rw [e]
        simp only [show j < 12 + k by omega, show j < 10 + k by omega, ↓reduceIte]
        exact h5
      · by_cases hj2 : j < 10 + k
        · have e : mp (k + 1) j = j + 2 := by
            simp [mp, hj1, show j < 10 + (k + 1) by omega]
          have e' : mp k j = j + 2 := by simp [mp, hj1, hj2]
          have h5 := hinv j
          rw [e'] at h5
          rw [e]
          simp only [show j + 2 < 12 + k by omega, hj2, ↓reduceIte]
          exact h5
        · by_cases hj3 : j = 10 + k
          · have e : mp (k + 1) j = 12 + k := by
              simp [mp, hj1, show j < 10 + (k + 1) by omega]; omega
            rw [e]
            simp [hj3]
          · have e : mp (k + 1) j = 10 := by
              simp [mp, hj1, show ¬ j < 10 + (k + 1) by omega]
            rw [e]
            simp only [show (10 : ℕ) < 12 + k by omega, ↓reduceIte, hj2, hj3, h10]
    · simp only [step]
      rw [getD_snoc, hW']
      simp only [show (10 : ℕ) < 12 + k by omega, ↓reduceIte, h10]
    · simp only [step]
      rw [getD_snoc, hW']
      simp only [show (11 : ℕ) < 12 + k by omega, ↓reduceIte, h11]

end PEqualNP.Outside.L_meta_2738

theorem PEqualNP.Outside.L_meta_2738 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     x2 < x3 →       x3 < (10 : ℕ) + x1.length →         ∃ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ) (x9 : ℕ),           x7.length ≤ x1.length ∧             x8 < (12 : ℕ) + x7.length ∧               x9 < (12 : ℕ) + x7.length ∧                 PEqualNP.MetaComplexity.FanInTwo { gates := x7, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧                   (∀ (x10 : Fin x7.length),                       have x11 : PEqualNP.CircuitLowerBounds.Gate := x7.get x10;                       (∀ x12 ∈ x11.inputs, x12 < (12 : ℕ) + ↑x10) ∧ x11.inputs.Nodup ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (1 : ℕ) ∨ x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (2 : ℕ))) ∧                     ∀ (x10 : List Bool), x10.length = (10 : ℕ) → ({ gates := x7, output := x8 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true]) || { gates := x7, output := x9 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true])) = ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10) := by
  intro x1 x2 x3 hfan h23 h3
  have hg : ∀ g ∈ x1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
      Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := fun g hg => hfan g hg
  refine ⟨PEqualNP.Outside.L_meta_2738.nl 0 x1, PEqualNP.Outside.L_meta_2738.mp x1.length x2,
    PEqualNP.Outside.L_meta_2738.mp x1.length x3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_2738.nl_length]
  · rw [PEqualNP.Outside.L_meta_2738.nl_length]; exact PEqualNP.Outside.L_meta_2738.mp_lt _ _
  · rw [PEqualNP.Outside.L_meta_2738.nl_length]; exact PEqualNP.Outside.L_meta_2738.mp_lt _ _
  · intro g hg'
    obtain ⟨j, g0, rfl⟩ := PEqualNP.Outside.L_meta_2738.nl_mem 0 x1 g hg'
    exact PEqualNP.Outside.L_meta_2738.ng_fan j g0
  · intro i
    have := PEqualNP.Outside.L_meta_2738.nl_good 0 x1 i.1 i.2
    rw [Nat.zero_add] at this
    exact this
  · intro x10 hx10
    have hinit : ∀ i, (x10 ++ [false, true]).getD (PEqualNP.Outside.L_meta_2738.mp 0 i) false =
        x10.getD i false := by
      intro i
      by_cases hi : i < 10
      · have e : PEqualNP.Outside.L_meta_2738.mp 0 i = i := by
          simp [PEqualNP.Outside.L_meta_2738.mp, hi]
        rw [e]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < x10.length by omega)]
      · have e : PEqualNP.Outside.L_meta_2738.mp 0 i = 10 := by
          simp [PEqualNP.Outside.L_meta_2738.mp, hi]
        rw [e, List.getD_eq_default x10 false (by omega)]
        simp [List.getD_eq_getElem?_getD, hx10]
    have h10 : (x10 ++ [false, true]).getD 10 false = false := by
      simp [List.getD_eq_getElem?_getD, hx10]
    have h11 : (x10 ++ [false, true]).getD 11 false = true := by
      simp [List.getD_eq_getElem?_getD, hx10]
    have key : ∀ o, ((PEqualNP.Outside.L_meta_2738.nl 0 x1).foldl PEqualNP.Outside.L_meta_2738.step
        (x10 ++ [false, true])).getD (PEqualNP.Outside.L_meta_2738.mp x1.length o) false =
        (x1.foldl PEqualNP.Outside.L_meta_2738.step x10).getD o false := by
      intro o
      have := PEqualNP.Outside.L_meta_2738.fold_inv x1 0 x10 (x10 ++ [false, true]) hg
        (by simp [hx10]) (by simp [hx10]) hinit h10 h11 o
      rwa [Nat.zero_add] at this
    have hw : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool),
        C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_2738.step x := fun _ _ => rfl
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, hw]
    rw [key x2, key x3]
