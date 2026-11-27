import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5633

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- the atoms a wire function needs: a row u is needed when some column v is true at u and
-- false at another row; a column v (atom 4 + v) likewise
def Cov (f : Fin 4 → Fin 4 → Bool) (S : Finset ℕ) : Prop :=
  (∀ u v u' : Fin 4, f u v = true → f u' v = false → (u : ℕ) ∈ S) ∧
  (∀ u v v' : Fin 4, f u v = true → f u v' = false → 4 + (v : ℕ) ∈ S)

lemma cov_mono {f : Fin 4 → Fin 4 → Bool} {S S' : Finset ℕ} (h : Cov f S) (hs : S ⊆ S') :
    Cov f S' :=
  ⟨fun u v u' a b => hs (h.1 u v u' a b), fun u v v' a b => hs (h.2 u v v' a b)⟩

lemma cov_const (b : Bool) : Cov (fun _ _ => b) ∅ := by
  refine ⟨fun u v u' h1 h2 => ?_, fun u v v' h1 h2 => ?_⟩ <;> cases b <;> simp_all

lemma cov_congr {f g : Fin 4 → Fin 4 → Bool} {S : Finset ℕ} (h : ∀ u v, f u v = g u v)
    (hc : Cov g S) : Cov f S := by
  have : f = g := funext fun u => funext fun v => h u v
  rw [this]; exact hc

lemma cov_and {f g : Fin 4 → Fin 4 → Bool} {S T : Finset ℕ} (hf : Cov f S) (hg : Cov g T) :
    Cov (fun u v => f u v && g u v) (S ∪ T) := by
  refine ⟨fun u v u' h1 h2 => ?_, fun u v v' h1 h2 => ?_⟩
  · simp only [Bool.and_eq_true] at h1
    rw [Finset.mem_union]
    cases hfu : f u' v
    · exact Or.inl (hf.1 u v u' h1.1 hfu)
    · simp only [hfu, Bool.true_and] at h2
      exact Or.inr (hg.1 u v u' h1.2 h2)
  · simp only [Bool.and_eq_true] at h1
    rw [Finset.mem_union]
    cases hfu : f u v'
    · exact Or.inl (hf.2 u v v' h1.1 hfu)
    · simp only [hfu, Bool.true_and] at h2
      exact Or.inr (hg.2 u v v' h1.2 h2)

lemma cov_or {f g : Fin 4 → Fin 4 → Bool} {S T : Finset ℕ} (hf : Cov f S) (hg : Cov g T) :
    Cov (fun u v => f u v || g u v) (S ∪ T) := by
  refine ⟨fun u v u' h1 h2 => ?_, fun u v v' h1 h2 => ?_⟩
  · simp only [Bool.or_eq_true] at h1
    simp only [Bool.or_eq_false_iff] at h2
    rw [Finset.mem_union]
    rcases h1 with h1 | h1
    · exact Or.inl (hf.1 u v u' h1 h2.1)
    · exact Or.inr (hg.1 u v u' h1 h2.2)
  · simp only [Bool.or_eq_true] at h1
    simp only [Bool.or_eq_false_iff] at h2
    rw [Finset.mem_union]
    rcases h1 with h1 | h1
    · exact Or.inl (hf.2 u v v' h1 h2.1)
    · exact Or.inr (hg.2 u v v' h1 h2.2)

lemma cov_all (l : List ℕ) (R : ℕ → Fin 4 → Fin 4 → Bool) (F : ℕ → Finset ℕ)
    (h : ∀ i, Cov (R i) (F i)) :
    Cov (fun u v => (l.map fun i => R i u v).all id) (l.toFinset.biUnion F) := by
  induction l with
  | nil =>
    rw [List.toFinset_nil, Finset.biUnion_empty]
    exact cov_const true
  | cons a l ih =>
    rw [List.toFinset_cons, Finset.biUnion_insert]
    exact cov_and (h a) ih

lemma cov_any (l : List ℕ) (R : ℕ → Fin 4 → Fin 4 → Bool) (F : ℕ → Finset ℕ)
    (h : ∀ i, Cov (R i) (F i)) :
    Cov (fun u v => (l.map fun i => R i u v).any id) (l.toFinset.biUnion F) := by
  induction l with
  | nil =>
    rw [List.toFinset_nil, Finset.biUnion_empty]
    exact cov_const false
  | cons a l ih =>
    rw [List.toFinset_cons, Finset.biUnion_insert]
    exact cov_or (h a) ih

lemma cov_gate (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (R : ℕ → Fin 4 → Fin 4 → Bool) (F : ℕ → Finset ℕ) (h : ∀ i, Cov (R i) (F i)) :
    Cov (fun u v => g.op.eval (g.inputs.map fun i => R i u v)) (g.inputs.toFinset.biUnion F) := by
  have hg' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg
  rcases hg' with h1 | h1 <;> rw [h1]
  · exact cov_all g.inputs R F h
  · exact cov_any g.inputs R F h

lemma getD_none (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

def F0 (i : ℕ) : Finset ℕ := if i < 8 then {i} else ∅

lemma cov_inputs : ∀ i : Fin 8, Cov (fun u v => (oneEach u v).getD i.val false) {i.val} := by
  unfold Cov; decide

lemma cov_input (i : ℕ) : Cov (fun u v => (oneEach u v).getD i false) (F0 i) := by
  unfold F0
  by_cases hi : i < 8
  · rw [if_pos hi]; exact cov_inputs ⟨i, hi⟩
  · rw [if_neg hi]
    have h : ∀ u v : Fin 4, (oneEach u v).getD i false = false := fun u v =>
      getD_none _ _ (by simp only [oneEach, List.length_append, List.length_ofFn]; omega)
    simp only [h]
    exact cov_const false

lemma cov_read_append (P : Fin 4 → Fin 4 → List Bool) (e : Fin 4 → Fin 4 → Bool) (n : ℕ)
    (hlen : ∀ u v, (P u v).length = n) (FP : ℕ → Finset ℕ)
    (hP : ∀ i, Cov (fun u v => (P u v).getD i false) (FP i)) (Se : Finset ℕ) (he : Cov e Se)
    (i : ℕ) : Cov (fun u v => (P u v ++ [e u v]).getD i false) (if i = n then Se else FP i) := by
  rcases lt_trichotomy i n with h | h | h
  · rw [if_neg (by omega)]
    have hh : ∀ u v, (P u v ++ [e u v]).getD i false = (P u v).getD i false := fun u v => by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hlen]; exact h)]
    simp only [hh]
    exact hP i
  · rw [if_pos h]
    have hh : ∀ u v, (P u v ++ [e u v]).getD i false = e u v := fun u v => by
      have hl := hlen u v
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      have : i - (P u v).length = 0 := by omega
      rw [this]; rfl
    simp only [hh]
    exact he
  · rw [if_neg (by omega)]
    have hh : ∀ u v, (P u v ++ [e u v]).getD i false = false := fun u v =>
      getD_none _ _ (by simp only [List.length_append, List.length_singleton, hlen]; omega)
    simp only [hh]
    exact cov_mono (cov_const false) (Finset.empty_subset _)

lemma step (P : Fin 4 → Fin 4 → List Bool) (n : ℕ) (hlen : ∀ u v, (P u v).length = n)
    (FP : ℕ → Finset ℕ) (hP : ∀ i, Cov (fun u v => (P u v).getD i false) (FP i))
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (i : ℕ) :
    Cov (fun u v => (P u v ++ [g.op.eval (g.inputs.map fun j => (P u v).getD j false)]).getD i false)
      (if i = n then g.inputs.toFinset.biUnion FP else FP i) :=
  cov_read_append P (fun u v => g.op.eval (g.inputs.map fun j => (P u v).getD j false)) n hlen FP hP
    _ (cov_gate g hg (fun j u v => (P u v).getD j false) FP hP) i

def P1 (g1 : Gate) (u v : Fin 4) : List Bool :=
  oneEach u v ++ [g1.op.eval (g1.inputs.map fun j => (oneEach u v).getD j false)]

def P2 (g1 g2 : Gate) (u v : Fin 4) : List Bool :=
  P1 g1 u v ++ [g2.op.eval (g2.inputs.map fun j => (P1 g1 u v).getD j false)]

def P3 (g1 g2 g3 : Gate) (u v : Fin 4) : List Bool :=
  P2 g1 g2 u v ++ [g3.op.eval (g3.inputs.map fun j => (P2 g1 g2 u v).getD j false)]

def S1 (g1 : Gate) : Finset ℕ := g1.inputs.toFinset.biUnion F0
def F1 (g1 : Gate) (i : ℕ) : Finset ℕ := if i = 8 then S1 g1 else F0 i
def S2 (g1 g2 : Gate) : Finset ℕ := g2.inputs.toFinset.biUnion (F1 g1)
def F2 (g1 g2 : Gate) (i : ℕ) : Finset ℕ := if i = 9 then S2 g1 g2 else F1 g1 i
def S3 (g1 g2 g3 : Gate) : Finset ℕ := g3.inputs.toFinset.biUnion (F2 g1 g2)
def F3 (g1 g2 g3 : Gate) (i : ℕ) : Finset ℕ := if i = 10 then S3 g1 g2 g3 else F2 g1 g2 i

lemma biU2 (l : List ℕ) (hl : l.length ≤ 2) (K : ℕ → Finset ℕ) (P : Finset ℕ → Prop)
    (h0 : P ∅) (h1 : ∀ a, P (K a)) (h2 : ∀ a b, P (K a ∪ K b)) : P (l.toFinset.biUnion K) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rw [List.toFinset_nil, Finset.biUnion_empty]; exact h0
  · rw [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert, Finset.biUnion_empty,
      Finset.union_empty]
    exact h1 a
  · rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert,
      Finset.biUnion_insert, Finset.biUnion_empty, Finset.union_empty]
    exact h2 a b
  · simp only [List.length_cons] at hl; omega

lemma pairA (K : ℕ → Finset ℕ) (S : Finset ℕ) (h1 : S.card ≤ 2)
    (hK : ∀ i, (K i).card ≤ 1 ∨ K i = S) (a b : ℕ) : (K a ∪ K b).card ≤ 3 := by
  have hu := Finset.card_union_le (K a) (K b)
  rcases hK a with ha | ha <;> rcases hK b with hb | hb
  all_goals first
    | omega
    | (rw [ha] at hu ⊢; omega)
    | (rw [hb] at hu ⊢; omega)
    | (rw [ha, hb, Finset.union_self]; omega)

lemma pairB (K : ℕ → Finset ℕ) (S T : Finset ℕ) (h1 : S.card ≤ 2) (h2 : T.card ≤ 3)
    (h12 : (S ∪ T).card ≤ 4) (hK : ∀ i, (K i).card ≤ 1 ∨ K i = S ∨ K i = T) (a b : ℕ) :
    (K a ∪ K b).card ≤ 4 := by
  have hu := Finset.card_union_le (K a) (K b)
  rcases hK a with ha | ha | ha <;> rcases hK b with hb | hb | hb
  all_goals first
    | omega
    | (rw [ha] at hu ⊢; omega)
    | (rw [hb] at hu ⊢; omega)
    | (rw [ha, hb, Finset.union_self]; omega)
    | (rw [ha, hb]; omega)
    | (rw [ha, hb, Finset.union_comm]; omega)

lemma tri (S A B : Finset ℕ) (hS : S.card ≤ 2) (hA : A.card ≤ 1 ∨ A = S)
    (hB : B.card ≤ 1 ∨ B = S) : (S ∪ (A ∪ B)).card ≤ 4 := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · have h1 := Finset.card_union_le S (A ∪ B)
    have h2 := Finset.card_union_le A B
    omega
  · rw [hB, Finset.union_left_comm, Finset.union_self]
    have := Finset.card_union_le A S
    omega
  · rw [hA, ← Finset.union_assoc, Finset.union_self]
    have := Finset.card_union_le S B
    omega
  · rw [hA, hB, Finset.union_self, Finset.union_self]
    omega

lemma core3 (g1 g2 g3 : Gate)
    (h1 : g1.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g1.inputs.length ≤ 2)
    (h2 : g2.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g2.inputs.length ≤ 2)
    (h3 : g3.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g3.inputs.length ≤ 2) (o : ℕ) :
    ∃ S : Finset ℕ, S.card ≤ 4 ∧
      Cov (fun u v => (⟨[g1, g2, g3], o⟩ : Circuit).eval (oneEach u v)) S := by
  have c0 : ∀ i, Cov (fun u v => (oneEach u v).getD i false) (F0 i) := cov_input
  have c1 : ∀ i, Cov (fun u v => (P1 g1 u v).getD i false) (F1 g1 i) :=
    step (fun u v => oneEach u v) 8
      (fun u v => by simp only [oneEach, List.length_append, List.length_ofFn]) F0 c0 g1 h1.1
  have c2 : ∀ i, Cov (fun u v => (P2 g1 g2 u v).getD i false) (F2 g1 g2 i) :=
    step (P1 g1) 9
      (fun u v => by simp only [P1, oneEach, List.length_append, List.length_ofFn,
        List.length_singleton]) (F1 g1) c1 g2 h2.1
  have c3 : ∀ i, Cov (fun u v => (P3 g1 g2 g3 u v).getD i false) (F3 g1 g2 g3 i) :=
    step (P2 g1 g2) 10
      (fun u v => by simp only [P2, P1, oneEach, List.length_append, List.length_ofFn,
        List.length_singleton]) (F2 g1 g2) c2 g3 h3.1
  have hF0 : ∀ i, (F0 i).card ≤ 1 := by
    intro i; unfold F0; split_ifs <;> simp
  have hS1 : (S1 g1).card ≤ 2 :=
    biU2 g1.inputs h1.2 F0 (fun S => S.card ≤ 2) (by simp)
      (fun a => by show (F0 a).card ≤ 2; have := hF0 a; omega)
      (fun a b => by
        show (F0 a ∪ F0 b).card ≤ 2
        have := Finset.card_union_le (F0 a) (F0 b); have := hF0 a; have := hF0 b; omega)
  have hF1 : ∀ i, (F1 g1 i).card ≤ 1 ∨ F1 g1 i = S1 g1 := by
    intro i; unfold F1; split_ifs
    · exact Or.inr rfl
    · exact Or.inl (hF0 i)
  have hS2 : (S2 g1 g2).card ≤ 3 :=
    biU2 g2.inputs h2.2 (F1 g1) (fun S => S.card ≤ 3) (by simp)
      (fun a => by
        show (F1 g1 a).card ≤ 3
        rcases hF1 a with h | h
        · omega
        · rw [h]; omega)
      (fun a b => pairA (F1 g1) (S1 g1) hS1 hF1 a b)
  have h12 : (S1 g1 ∪ S2 g1 g2).card ≤ 4 :=
    biU2 g2.inputs h2.2 (F1 g1) (fun S => (S1 g1 ∪ S).card ≤ 4)
      (by show (S1 g1 ∪ ∅).card ≤ 4; rw [Finset.union_empty]; omega)
      (fun a => by
        show (S1 g1 ∪ F1 g1 a).card ≤ 4
        rcases hF1 a with h | h
        · have := Finset.card_union_le (S1 g1) (F1 g1 a); omega
        · rw [h, Finset.union_self]; omega)
      (fun a b => by
        show (S1 g1 ∪ (F1 g1 a ∪ F1 g1 b)).card ≤ 4
        exact tri (S1 g1) _ _ hS1 (hF1 a) (hF1 b))
  have hF2 : ∀ i, (F2 g1 g2 i).card ≤ 1 ∨ F2 g1 g2 i = S1 g1 ∨ F2 g1 g2 i = S2 g1 g2 := by
    intro i; unfold F2; split_ifs
    · exact Or.inr (Or.inr rfl)
    · rcases hF1 i with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hS3 : (S3 g1 g2 g3).card ≤ 4 :=
    biU2 g3.inputs h3.2 (F2 g1 g2) (fun S => S.card ≤ 4) (by simp)
      (fun a => by
        show (F2 g1 g2 a).card ≤ 4
        rcases hF2 a with h | h | h
        all_goals first | omega | (rw [h]; omega))
      (fun a b => pairB (F2 g1 g2) (S1 g1) (S2 g1 g2) hS1 hS2 h12 hF2 a b)
  have hF3 : (F3 g1 g2 g3 o).card ≤ 4 := by
    unfold F3; split_ifs
    · exact hS3
    · rcases hF2 o with h | h | h
      all_goals first | omega | (rw [h]; omega)
  exact ⟨F3 g1 g2 g3 o, hF3, c3 o⟩

def pad : Gate := ⟨GateOp.or, []⟩

lemma getD_append_false (W : List Bool) (o : ℕ) : (W ++ [false]).getD o false = W.getD o false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge o W.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_eq_none h]
    rcases Nat.eq_zero_or_pos (o - W.length) with h2 | h2
    · rw [h2]; rfl
    · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; omega)]

lemma eval_pad (gs : List Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [pad], o⟩ : Circuit).eval x = (⟨gs, o⟩ : Circuit).eval x := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact getD_append_false _ _

lemma lowerCov (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 3) :
    ∃ S : Finset ℕ, S.card ≤ 4 ∧ Cov (fun u v => C.eval (oneEach u v)) S := by
  obtain ⟨gs, o⟩ := C
  have pad_ok : pad.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ pad.inputs.length ≤ 2 := by
    simp [pad]
  have hm' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hm
  have hs' : gs.length ≤ 3 := hs
  rcases gs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, rest⟩⟩⟩⟩
  · obtain ⟨S, hS, hc⟩ := core3 pad pad pad pad_ok pad_ok pad_ok o
    refine ⟨S, hS, cov_congr (fun u v => ?_) hc⟩
    rw [show [pad, pad, pad] = (([] ++ [pad]) ++ [pad]) ++ [pad] from rfl, eval_pad, eval_pad,
      eval_pad]
  · obtain ⟨S, hS, hc⟩ := core3 g1 pad pad (hm' g1 (by simp)) pad_ok pad_ok o
    refine ⟨S, hS, cov_congr (fun u v => ?_) hc⟩
    rw [show [g1, pad, pad] = ([g1] ++ [pad]) ++ [pad] from rfl, eval_pad, eval_pad]
  · obtain ⟨S, hS, hc⟩ := core3 g1 g2 pad (hm' g1 (by simp)) (hm' g2 (by simp)) pad_ok o
    refine ⟨S, hS, cov_congr (fun u v => ?_) hc⟩
    rw [show [g1, g2, pad] = [g1, g2] ++ [pad] from rfl, eval_pad]
  · exact core3 g1 g2 g3 (hm' g1 (by simp)) (hm' g2 (by simp)) (hm' g3 (by simp)) o
  · simp only [List.length_cons] at hs'; omega

lemma target (S : Finset ℕ) (h : Cov (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) S) :
    5 ≤ S.card := by
  have m0 : (0 : ℕ) ∈ S := h.1 0 0 3 (by decide) (by decide)
  have m1 : (1 : ℕ) ∈ S := h.1 1 0 3 (by decide) (by decide)
  have m2 : (2 : ℕ) ∈ S := h.1 2 0 3 (by decide) (by decide)
  have m4 : (4 : ℕ) ∈ S := h.2 1 0 2 (by decide) (by decide)
  have m5 : (5 : ℕ) ∈ S := h.2 1 1 2 (by decide) (by decide)
  have hsub : ({0, 1, 2, 4, 5} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  have hc : ({0, 1, 2, 4, 5} : Finset ℕ).card = 5 := by rfl
  omega

def C4 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [0, 10] }], output := 11 }

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  refine ⟨C4, ?_, by decide, by decide⟩
  intro g hg
  simp only [C4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

lemma lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨S, hS, hc⟩ := lowerCov C hm hs
  have hc' : Cov (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) S :=
    cov_congr (fun u v => (hr u v).symm) hc
  have := target S hc'
  omega

end PEqualNP.Outside.L_meta_5633

theorem PEqualNP.Outside.L_meta_5633 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (831 : ℕ).testBit (4 * u.val + v.val)) 3 :=
  ⟨PEqualNP.Outside.L_meta_5633.upper, PEqualNP.Outside.L_meta_5633.lower⟩
