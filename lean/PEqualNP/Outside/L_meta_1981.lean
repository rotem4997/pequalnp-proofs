import Mathlib
import PEqualNP.Defs

-- Reads of wires that do not exist yet are reads of the constant false.

namespace PEqualNP.Outside.L_meta_1981

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

-- The gate that replaces g when k wires exist.
def T (k : ℕ) (g : Gate) : Gate :=
  if g.op.eval [] = true ∧ g.inputs.any (fun u => decide (k ≤ u)) = true then ⟨GateOp.or, []⟩
  else ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩

def fix : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => T k g :: fix (k + 1) gs

lemma T_cases (k : ℕ) (g : Gate) :
    T k g = ⟨GateOp.or, []⟩ ∨ T k g = ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩ := by
  unfold T
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma T_mon (k : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (T k g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (T k g).inputs.length ≤ 2 := by
  rcases T_cases k g with e | e
  · rw [e]; simp
  · rw [e]; exact ⟨h.1, le_trans (List.length_filter_le _ _) h.2⟩

lemma T_back (k : ℕ) (g : Gate) : ∀ u ∈ (T k g).inputs, u < k := by
  intro u hu
  rcases T_cases k g with e | e
  · rw [e] at hu; simp at hu
  · rw [e] at hu
    simp only [List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2

lemma T_val (w : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hbad : ∀ u, w.length ≤ u → w.getD u false = false := fun u hu =>
    List.getD_eq_default _ _ hu
  rcases hop with h | h
  · by_cases hb : g.inputs.any (fun u => decide (w.length ≤ u)) = true
    · have e : T w.length g = ⟨GateOp.or, []⟩ := by simp [T, h, GateOp.eval, hb]
      rw [e, h]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      rw [List.any_eq_true] at hb
      obtain ⟨u, hu, hk⟩ := hb
      exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by rw [hbad u (by simpa using hk)]; simp⟩
    · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
        simp [T, hb]
      have hall : g.inputs.filter (fun u => decide (u < w.length)) = g.inputs := by
        rw [List.filter_eq_self]
        intro u hu
        by_contra hk
        exact hb (List.any_eq_true.mpr ⟨u, hu, by simpa using hk⟩)
      rw [e]
      simp only [hall]
  · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
      simp [T, h, GateOp.eval]
    rw [e]
    simp only [h, GateOp.eval]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
    · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
      have hlt : u < w.length := by
        by_contra hk
        rw [hbad u (by omega)] at hb
        simp at hb
      exact ⟨_, ⟨u, ⟨hu, hlt⟩, rfl⟩, hb⟩

lemma fix_wires : ∀ (gs : List Gate) (k : ℕ) (w : List Bool), w.length = k →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    wiresFrom (fix k gs) w = wiresFrom gs w := by
  intro gs
  induction gs with
  | nil => intro k w _ _; rfl
  | cons g gs ih =>
    intro k w hk hops
    subst hk
    have h1 : wiresFrom (fix w.length (g :: gs)) w = wiresFrom (fix (w.length + 1) gs)
        (w ++ [(T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)]) := rfl
    have h2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1, h2, T_val w g (hops g (by simp))]
    exact ih _ _ (by simp) (fun g' hg' => hops g' (by simp [hg']))

lemma fix_len : ∀ (gs : List Gate) (k : ℕ), (fix k gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [fix, ih]

lemma fix_mon : ∀ (gs : List Gate) (k : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ g' ∈ fix k gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro k _ g' hg'; simp [fix] at hg'
  | cons g gs ih =>
    intro k hm g' hg'
    simp only [fix, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact T_mon k g (hm g (by simp))
    · exact ih (k + 1) (fun g2 hg2 => hm g2 (by simp [hg2])) g' hg'

lemma fix_back : ∀ (gs : List Gate) (k j : ℕ) (g' : Gate), (fix k gs)[j]? = some g' →
    ∀ u ∈ g'.inputs, u < k + j := by
  intro gs
  induction gs with
  | nil => intro k j g' h; simp [fix] at h
  | cons g gs ih =>
    intro k j g' h u hu
    cases j with
    | zero =>
      simp [fix] at h
      subst h
      exact T_back k g u hu
    | succ j =>
      simp [fix] at h
      have := ih (k + 1) j g' h u hu
      omega

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma main (gs : List Gate) (out : ℕ) (hmon : Monotone2 ⟨gs, out⟩) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ D.size ≤ gs.length ∧
      ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = Circuit.eval ⟨gs, out⟩ (List.ofFn x) := by
  refine ⟨⟨fix 14 gs, out⟩, fix_mon gs 14 hmon, ?_, le_of_eq (fix_len gs 14), ?_⟩
  · intro j hj u hu
    rw [gateAt_eq _ j hj] at hu
    exact fix_back gs 14 j _ (List.getElem?_eq_getElem hj) u hu
  · intro x
    show (wiresFrom (fix 14 gs) (List.ofFn x)).getD out false
      = (wiresFrom gs (List.ofFn x)).getD out false
    rw [fix_wires gs 14 _ (by simp) (fun g hg => by simpa using (hmon g hg).1)]

end PEqualNP.Outside.L_meta_1981

theorem PEqualNP.Outside.L_meta_1981 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x3 ∧ x3.size ≤ x1.size ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x4) = x1.eval (List.ofFn x4) := by
  intro C hmon
  obtain ⟨gs, out⟩ := C
  exact PEqualNP.Outside.L_meta_1981.main gs out hmon
