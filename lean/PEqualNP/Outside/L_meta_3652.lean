import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3652_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

-- evaluation toolkit (step .. val_gate) copied from the merged L_meta_1406
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

-- cone characterisation (cones_len .. inCone_iff) copied from the merged L_meta_2067
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

structure Good (n : ℕ) (C : Circuit) : Prop where
  ao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma two {n : ℕ} {C : Circuit} (hG : Good n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hG.ao _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  exact ⟨a, b, hab, hG.rb j hj a (by simp [hab]), hG.rb j hj b (by simp [hab]), hop⟩

lemma val_and {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.and) :
    val C.gates x (n + j) = (val C.gates x a && val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

lemma val_or {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.or) :
    val C.gates x (n + j) = (val C.gates x a || val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

-- generic fold over the gate list (run .. rv_gate), from the submitted L_meta_2672
def run {α : Type} (st : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) init

lemma run_length {α : Type} (st : List α → Gate → α) (gs : List Gate) (init : List α) :
    (run st init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [run]
  | cons g gs ih =>
    have h := ih (init ++ [st init g])
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    run st init (gs ++ [g]) = run st init gs ++ [st (run st init gs) g] := by
  simp [run, List.foldl_append]

lemma run_getD_snoc {α : Type} (d : α) (st : List α → Gate → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    (run st init (gs ++ [g])).getD i d =
      if i = init.length + gs.length then st (run st init gs) g
      else (run st init gs).getD i d := by
  rw [run_snoc]
  have hl := run_length st gs init
  rcases lt_trichotomy i (init.length + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- the value of wire `i` in a generic run -/
def rv {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) (i : ℕ) : α :=
  (run (fun w g => G g (g.inputs.map fun i => w.getD i d)) init gs).getD i d

lemma rv_snoc {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    rv d G init (gs ++ [g]) i =
      if i = init.length + gs.length then G g (g.inputs.map fun j => rv d G init gs j)
      else rv d G init gs i := by
  unfold rv
  rw [run_getD_snoc]

lemma rv_ge {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : init.length + gs.length ≤ i) : rv d G init gs i = d := by
  unfold rv
  generalize (fun (w : List α) (g : Gate) => G g (g.inputs.map fun i => w.getD i d)) = st
  have hl := run_length st gs init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma rv_lt {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : i < init.length) : rv d G init gs i = init.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => simp [rv, run]
  | append_singleton gs g ih =>
    rw [rv_snoc, if_neg (by omega)]
    exact ih

lemma rv_gate {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) :
    ∀ (k : ℕ) (hk : k < gs.length), (∀ j ∈ gs[k].inputs, j < init.length + k) →
      rv d G init gs (init.length + k) =
        G gs[k] (gs[k].inputs.map fun j => rv d G init gs j) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk hrb
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl] at hrb ⊢
      rw [rv_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget] at hrb ⊢
      rw [rv_snoc, if_neg (by omega), ih k hk2 hrb]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]


lemma rv_two {α : Type} (d : α) (G : Gate → List α → α) (init : List α) {n : ℕ} {C : Circuit}
    (hn : init.length = n) (hG : Good n C) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) :
    rv d G init C.gates (n + j) =
      G (gateAt C j) [rv d G init C.gates a, rv d G init C.gates b] := by
  subst hn
  have h := rv_gate d G init C.gates j hj (by rw [← gateAt_eq C j hj]; exact hG.rb j hj)
  rw [h, ← gateAt_eq C j hj, hin]
  rfl

/-! linear parts -/

def PP (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C isLine zl).getD w (false, false)

def Gp (g : Gate) (ins : List (Bool × Bool)) : Bool × Bool :=
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def pinit (isLine : ℕ → Bool) (zl : List Bool) : List (Bool × Bool) :=
  (zl.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)

lemma PP_eq (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) :
    PP C isLine zl w = rv (false, false) Gp (pinit isLine zl) C.gates w := rfl

lemma pinit_length (isLine : ℕ → Bool) (zl : List Bool) : (pinit isLine zl).length = zl.length := by
  simp [pinit]

lemma pinit_getD (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    (pinit isLine zl).getD w (false, false) =
      if isLine w then (false, zl.getD w false) else (zl.getD w false, false) := by
  simp [pinit, List.getD_eq_getElem?_getD, hw]

lemma PP_lt (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    PP C isLine zl w = if isLine w then (false, zl.getD w false) else (zl.getD w false, false) := by
  rw [PP_eq, rv_lt _ _ _ _ _ (by rw [pinit_length]; exact hw), pinit_getD _ _ _ hw]

lemma PP_or {n : ℕ} {C : Circuit} (hG : Good n C) (isLine : ℕ → Bool) (zl : List Bool)
    (hzl : zl.length = n) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.or) :
    PP C isLine zl (n + j) =
      ((PP C isLine zl a).1 || (PP C isLine zl b).1,
        (PP C isLine zl a).2 || (PP C isLine zl b).2) := by
  have e : ∀ w, PP C isLine zl w = rv (false, false) Gp (pinit isLine zl) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two (false, false) Gp (pinit isLine zl) (by rw [pinit_length]; exact hzl) hG j hj a b hin]
  simp [Gp, hop]

lemma PP_and {n : ℕ} {C : Circuit} (hG : Good n C) (isLine : ℕ → Bool) (zl : List Bool)
    (hzl : zl.length = n) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.and) :
    PP C isLine zl (n + j) =
      ((PP C isLine zl a).1 && (PP C isLine zl b).1,
        ((PP C isLine zl a).1 && (PP C isLine zl b).2) ||
          ((PP C isLine zl a).2 && (PP C isLine zl b).1)) := by
  have e : ∀ w, PP C isLine zl w = rv (false, false) Gp (pinit isLine zl) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two (false, false) Gp (pinit isLine zl) (by rw [pinit_length]; exact hzl) hG j hj a b hin]
  simp [Gp, hop]

def zin (n p l : ℕ) : List Bool := (List.range n).map fun i => i == p || i == l

lemma zin_length (n p l : ℕ) : (zin n p l).length = n := by simp [zin]

lemma zin_getD (n p l w : ℕ) (hw : w < n) : (zin n p l).getD w false = (w == p || w == l) := by
  simp [zin, List.getD_eq_getElem?_getD, hw]

/-! read vectors -/

def RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

def Gv (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma RV_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) :
    RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w := rfl

lemma RV_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    RV C n S k w = leafVectors S k w := by
  rw [RV_eq, rv_lt _ _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma RV_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    RV C n S k w = [] := by
  rw [RV_eq, rv_ge _ _ _ _ _ (by simpa using hw)]

lemma mem_insertNew (A : List (List ℕ)) (a v : List ℕ) : v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  split
  · constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · assumption
  · simp

lemma mem_fold_insertNew (A : List (List ℕ)) (v : List ℕ) :
    ∀ acc : List (List ℕ), v ∈ A.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ A := by
  induction A with
  | nil => intro acc; simp
  | cons a A ih =>
    intro acc
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ t ∈ B, v = capAdd k u t := by
  unfold andStep
  rw [mem_fold_insertNew]
  constructor
  · rintro (h | h)
    · simp at h
    · rw [List.mem_flatMap] at h
      obtain ⟨u, hu, h⟩ := h
      rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      exact ⟨u, hu, t, ht, rfl⟩
  · rintro ⟨u, hu, t, ht, rfl⟩
    right
    exact List.mem_flatMap.2 ⟨u, hu, List.mem_map.2 ⟨t, ht, rfl⟩⟩

lemma RV_or {n : ℕ} {C : Circuit} (hG : Good n C) (S : List ℕ) (k : ℕ)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ RV C n S k (n + j) ↔ v ∈ RV C n S k a ∨ v ∈ RV C n S k b := by
  have e : ∀ w, RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two [] (Gv S k) _ (by simp) hG j hj a b hin]
  simp only [Gv, hop, List.foldl_cons, List.foldl_nil]
  rw [mem_fold_insertNew, mem_fold_insertNew]
  simp

lemma RV_and {n : ℕ} {C : Circuit} (hG : Good n C) (S : List ℕ) (k : ℕ)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ RV C n S k (n + j) ↔ ∃ u ∈ RV C n S k a, ∃ t ∈ RV C n S k b,
      v = capAdd k (capAdd k (S.map fun _ => 0) u) t := by
  have e : ∀ w, RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two [] (Gv S k) _ (by simp) hG j hj a b hin]
  simp only [Gv, hop, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨u', hu', t, ht, rfl⟩
    rw [mem_andStep] at hu'
    obtain ⟨z, hz, u, hu, rfl⟩ := hu'
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, t, ht, rfl⟩
  · rintro ⟨u, hu, t, ht, rfl⟩
    refine ⟨_, ?_, t, ht, rfl⟩
    rw [mem_andStep]
    exact ⟨_, by simp, u, hu, rfl⟩

/-- the invariant linking count vectors and linear parts (`c` picks the entry of the line side) -/
lemma inv {n : ℕ} {C : Circuit} (hG : Good n C) (s0 s1 : ℕ) (h01 : s0 ≠ s1)
    (isLine : ℕ → Bool) (c : Bool) (h0 : isLine s0 = !c) (h1 : isLine s1 = c) :
    ∀ w, ∀ v ∈ RV C n [s0, s1] 1 w, ∃ a b, v = [a, b] ∧ 1 ≤ a + b ∧
      ((if c then b else a) = 0 → (PP C isLine (zin n s0 s1) w).1 = true) ∧
      ((if c then b else a) = 1 → (PP C isLine (zin n s0 s1) w).2 = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hw : w < n
    · rw [RV_lt _ _ _ _ _ hw] at hv
      rw [PP_lt _ _ _ _ (by rw [zin_length]; exact hw), zin_getD _ _ _ _ hw]
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_singleton] at hv
        subst hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · refine ⟨1, 0, by simp [h01.symm], by omega, ?_, ?_⟩
          · cases c <;> simp_all
          · cases c <;> simp_all
        · refine ⟨0, 1, by simp [h01], by omega, ?_, ?_⟩
          · cases c <;> simp_all
          · cases c <;> simp_all
      · simp at hv
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [RV_ge _ _ _ _ _ hw2] at hv
        simp at hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hin, ha, hb, hop⟩ := two hG j hj
        rcases hop with hop | hop
        · rw [RV_and hG _ _ j hj a b hin hop] at hv
          obtain ⟨u, hu, t, ht, rfl⟩ := hv
          obtain ⟨u0, u1, rfl, hu1, hu2, hu3⟩ := ih a ha u hu
          obtain ⟨t0, t1, rfl, ht1, ht2, ht3⟩ := ih b hb t ht
          rw [PP_and hG isLine _ (zin_length _ _ _) j hj a b hin hop]
          refine ⟨min (min (0 + u0) (1 + 1) + t0) (1 + 1), min (min (0 + u1) (1 + 1) + t1) (1 + 1),
            by simp [capAdd], by omega, ?_, ?_⟩
          · cases c
            · simp only [Bool.false_eq_true, if_false] at hu2 hu3 ht2 ht3 ⊢
              intro h
              rw [hu2 (by omega), ht2 (by omega)]
              rfl
            · simp only [if_true] at hu2 hu3 ht2 ht3 ⊢
              intro h
              rw [hu2 (by omega), ht2 (by omega)]
              rfl
          · cases c
            · simp only [Bool.false_eq_true, if_false] at hu2 hu3 ht2 ht3 ⊢
              intro h
              have hc : (u0 = 1 ∧ t0 = 0) ∨ (u0 = 0 ∧ t0 = 1) := by omega
              rcases hc with ⟨h5, h6⟩ | ⟨h5, h6⟩
              · rw [hu3 h5, ht2 h6]
                simp
              · rw [hu2 h5, ht3 h6]
                simp
            · simp only [if_true] at hu2 hu3 ht2 ht3 ⊢
              intro h
              have hc : (u1 = 1 ∧ t1 = 0) ∨ (u1 = 0 ∧ t1 = 1) := by omega
              rcases hc with ⟨h5, h6⟩ | ⟨h5, h6⟩
              · rw [hu3 h5, ht2 h6]
                simp
              · rw [hu2 h5, ht3 h6]
                simp
        · rw [RV_or hG _ _ j hj a b hin hop] at hv
          rw [PP_or hG isLine _ (zin_length _ _ _) j hj a b hin hop]
          rcases hv with hv | hv
          · obtain ⟨u0, u1, rfl, hu1, hu2, hu3⟩ := ih a ha v hv
            refine ⟨u0, u1, rfl, hu1, ?_, ?_⟩
            · intro h
              rw [hu2 h]
              rfl
            · intro h
              rw [hu3 h]
              rfl
          · obtain ⟨u0, u1, rfl, hu1, hu2, hu3⟩ := ih b hb v hv
            refine ⟨u0, u1, rfl, hu1, ?_, ?_⟩
            · intro h
              rw [hu2 h]
              simp
            · intro h
              rw [hu3 h]
              simp

lemma noread {n : ℕ} {C : Circuit} (hG : Good n C) (s0 s1 : ℕ) (h01 : s0 ≠ s1)
    (isL : ℕ → Bool) (hl0 : isL s0 = false) (hl1 : isL s1 = true) (w : ℕ)
    (hA : (PP C isL (zin n s0 s1) w).2 = false)
    (hB : (PP C (fun i => !isL i) (zin n s0 s1) w).2 = false) :
    ∀ v ∈ RV C n [s0, s1] 1 w, ¬ (v.all fun a => decide (a ≤ 1)) = true := by
  intro v hv hall
  obtain ⟨a, b, rfl, hab, _, h3⟩ := inv hG s0 s1 h01 isL true (by simp [hl0]) hl1 w v hv
  obtain ⟨a', b', he, _, _, h3'⟩ :=
    inv hG s0 s1 h01 (fun i => !isL i) false (by simp [hl0]) (by simp [hl1]) w _ hv
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    at hall
  simp only [if_true] at h3
  simp only [Bool.false_eq_true, if_false] at h3'
  by_cases hb : b = 1
  · rw [h3 hb] at hA
    cases hA
  · rw [h3' (by omega)] at hB
    cases hB

/-! semantics -/

def BW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C.gates x w = true → graphFun G ∅ x = true

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

lemma F_eof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (eof i) = false := by
  simp only [graphFun, eof, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not, decide_eq_true_eq]
  rintro ⟨u, v, h, rfl, rfl⟩
  exact h.ne rfl

lemma F_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (h : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, pairInput, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma ones {n : ℕ} {C : Circuit} (hG : Good n C) :
    ∀ w, w < n + C.gates.length → val C.gates (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_lt _ _ _ h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hin, ha, hb, hop⟩ := two hG j hj
      rcases hop with hop | hop
      · rw [val_and _ j hj a b hin ha hb hop, ih a ha (by omega), ih b hb (by omega)]
        rfl
      · rw [val_or _ j hj a b hin ha hb hop, ih a ha (by omega)]
        rfl

lemma notBW_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ)
    (hw : w < n) : ¬ BW G C w := by
  intro h
  have h2 := h (eof ⟨w, hw⟩) (by rw [val_lt _ _ _ hw]; simp [eof])
  rw [F_eof] at h2
  cases h2

lemma closure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C)
    (h7 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs, ¬ BW G C t)
    (hL : ∀ h < C.gates.length, (gateAt C h).op = GateOp.or → ¬ BW G C (n + h) →
      ∀ t ∈ (gateAt C h).inputs, ¬ BW G C t) :
    ∀ h, h < C.gates.length → ¬ BW G C (n + h) → ∀ j, InCone n C j h → ¬ BW G C (n + j) := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh hnb j hc
    rw [inCone_iff] at hc
    obtain ⟨_, k, hk, hin, hjk⟩ := hc
    have hkb : ¬ BW G C (n + k) := by
      obtain ⟨a, b, _, _, _, hop⟩ := two hG h hh
      rcases hop with hop | hop
      · exact h7 h hh hop _ hin
      · exact hL h hh hop hnb _ hin
    rcases hjk with rfl | hjk
    · exact hkb
    · exact ih k hk (by omega) hkb j hjk

lemma descent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (e : Fin n → Bool) (Q : ℕ → Prop)
    (hQ : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → ∀ a b,
      (gateAt C j).inputs = [a, b] → Q (n + j) → Q a ∧ Q b) :
    ∀ w, val C.gates e w = true → BW G C w → Q w →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ val C.gates e (n + j) = true ∧
        BW G C (n + j) ∧ Q (n + j) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hbw hq
    by_cases h1 : w < n
    · exact absurd hbw (notBW_input G C w h1)
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_ge _ _ _ h2] at hv
        cases hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hin, ha, hb, hop⟩ := two hG j hj
        rcases hop with hop | hop
        · exact ⟨j, hj, hop, hv, hbw, hq⟩
        · rw [val_or _ j hj a b hin ha hb hop, Bool.or_eq_true] at hv
          obtain ⟨hqa, hqb⟩ := hQ j hj hop a b hin hq
          rcases hv with hv | hv
          · refine ih a ha hv (fun x hx => hbw x ?_) hqa
            rw [val_or _ j hj a b hin ha hb hop, hx]
            rfl
          · refine ih b hb hv (fun x hx => hbw x ?_) hqb
            rw [val_or _ j hj a b hin ha hb hop, hx]
            simp

theorem main : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := by
  intro N I _ G _ C hAdj _ hAO hF hLift hOC h7 p1 l1 hmem
  have hG : Good (N + N) C := ⟨fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩, hAO.2.1⟩
  -- unpack the double re-read hypothesis
  unfold doubleReread at hmem
  rw [List.mem_filter] at hmem
  obtain ⟨hE, hls⟩ := hmem
  have hI : I p1 l1 := by
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, Prod.mk.injEq] at hE
    obtain ⟨p5, l6, hI, hp, hl⟩ := hE
    have e1 : p5 = p1 := Fin.ext hp
    have e2 : l6 = l1 := Fin.ext (by omega)
    rw [← e1, ← e2]
    exact hI
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hls
  obtain ⟨hA, hB⟩ := hls
  have hA' : (PP C (fun w => decide (N ≤ w)) (zin (N + N) p1.val (N + l1.val)) C.output).2 = false :=
    hA
  have hB' : (PP C (fun i => !(fun w => decide (N ≤ w)) i) (zin (N + N) p1.val (N + l1.val))
      C.output).2 = false := hB
  have hadj : G.Adj (Fin.castAdd N p1) (Fin.natAdd N l1) :=
    (hAdj _ _).2 ⟨p1, l1, hI, Or.inl ⟨rfl, rfl⟩⟩
  have hout : val C.gates (pairInput (Fin.castAdd N p1) (Fin.natAdd N l1)) C.output = true := by
    have h := congrFun hF (pairInput (Fin.castAdd N p1) (Fin.natAdd N l1))
    rw [F_pair G _ _ hadj] at h
    exact h
  have hbwo : BW G C C.output := by
    intro x hx
    rw [← hF]
    exact hx
  have h7' : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs, ¬ BW G C t := fun k hk hop t ht => h7 k hk hop t ht
  have hL' : ∀ h < C.gates.length, (gateAt C h).op = GateOp.or → ¬ BW G C (N + N + h) →
      ∀ t ∈ (gateAt C h).inputs, ¬ BW G C t := by
    intro h hh hop hnb t ht hbt
    apply hLift
    obtain ⟨a, b, hin, ha, hb, _⟩ := two hG h hh
    rw [hin] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨h, hh, 0, hOC h hh, hop, hnb, ?_⟩
      have e0 : opnd C h 0 = t := by simp [opnd, hin]
      rw [e0]
      exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩
    · refine ⟨h, hh, 1, hOC h hh, hop, hnb, ?_⟩
      have e0 : opnd C h 1 = t := by simp [opnd, hin]
      rw [e0]
      exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩
  -- descend to the first AND gate
  obtain ⟨j, hj, hop, hv, hbw, hPA, hPB⟩ := descent G hG
    (pairInput (Fin.castAdd N p1) (Fin.natAdd N l1))
    (fun w => (PP C (fun w => decide (N ≤ w)) (zin (N + N) p1.val (N + l1.val)) w).2 = false ∧
      (PP C (fun i => !(fun w => decide (N ≤ w)) i) (zin (N + N) p1.val (N + l1.val)) w).2 = false)
    (by
      intro j hj hop a b hin hq
      rw [PP_or hG _ _ (zin_length _ _ _) j hj a b hin hop,
        PP_or hG _ _ (zin_length _ _ _) j hj a b hin hop] at hq
      simp only [Bool.or_eq_false_iff] at hq
      exact ⟨⟨hq.1.1, hq.2.1⟩, ⟨hq.1.2, hq.2.2⟩⟩)
    C.output hout hbwo ⟨hA', hB'⟩
  obtain ⟨a, b, hin, ha, hb, _⟩ := two hG j hj
  have hcore : IsCore G C j := by
    refine ⟨hj, ⟨hbw, _, hv⟩, ?_, Fin.castAdd N p1, Fin.natAdd N l1, hadj, hv, ?_⟩
    · rintro ⟨⟨hn0, hb0, _⟩, _⟩
      have e0 : opnd C j 0 = a := by simp [opnd, hin]
      rw [e0] at hn0 hb0
      have e : N + N + (a - (N + N)) = a := by omega
      have hb0' : BW G C (N + N + (a - (N + N))) := hb0
      rw [e] at hb0'
      exact h7' j hj hop a (by simp [hin]) hb0'
    · unfold ReadTwiceAt readsAtMost
      show (RV C (N + N) [p1.val, N + l1.val] 1 (N + N + j)).any _ = false
      rw [List.any_eq_false]
      intro v hv
      exact noread hG p1.val (N + l1.val) (by omega) (fun w => decide (N ≤ w))
        (by simp) (by simp) (N + N + j) hPA hPB v hv
  refine ⟨j, ?_, ?_⟩
  · unfold maximalCores gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hj, hcore, ?_⟩
    intro i hi hci hcone
    obtain ⟨_, ⟨hbi, _⟩, hnb, _⟩ := hci
    obtain ⟨a2, b2, hin2, ha2, hb2, hopi⟩ := two hG i hi
    rcases hopi with hopi | hopi
    · rw [inCone_iff] at hcone
      obtain ⟨_, k, hk, hkin, hjk⟩ := hcone
      have hkb := h7' i hi hopi _ hkin
      rcases hjk with rfl | hjk
      · exact hkb hbw
      · exact closure G hG h7' hL' k (by omega) hkb j hjk hbw
    · apply hnb
      have hbi' : BW G C (N + N + i) := hbi
      have hba : BW G C a2 := by
        intro x hx
        apply hbi' x
        rw [val_or _ i hi a2 b2 hin2 ha2 hb2 hopi, hx]
        rfl
      have hbb : BW G C b2 := by
        intro x hx
        apply hbi' x
        rw [val_or _ i hi a2 b2 hin2 ha2 hb2 hopi, hx]
        simp
      have hna : N + N ≤ a2 := by
        by_contra hlt
        exact notBW_input G C a2 (by omega) hba
      have hnb2 : N + N ≤ b2 := by
        by_contra hlt
        exact notBW_input G C b2 (by omega) hbb
      have e0 : opnd C i 0 = a2 := by simp [opnd, hin2]
      have e1 : opnd C i 1 = b2 := by simp [opnd, hin2]
      rw [e0, e1]
      have ea : N + N + (a2 - (N + N)) = a2 := by omega
      have eb : N + N + (b2 - (N + N)) = b2 := by omega
      refine ⟨⟨hna, ?_, fun _ => true, ?_⟩, ⟨hnb2, ?_, fun _ => true, ?_⟩⟩
      · show BW G C (N + N + (a2 - (N + N)))
        rw [ea]
        exact hba
      · show val C.gates _ (N + N + (a2 - (N + N))) = true
        rw [ea]
        exact ones hG a2 (by omega)
      · show BW G C (N + N + (b2 - (N + N)))
        rw [eb]
        exact hbb
      · show val C.gates _ (N + N + (b2 - (N + N))) = true
        rw [eb]
        exact ones hG b2 (by omega)
  · simp only [gammaE, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hadj, _, _, rfl, hv⟩

end PEqualNP.Outside.L_meta_3652_aux

theorem PEqualNP.Outside.L_meta_3652 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := by
  intro N I _ G _ C
  exact PEqualNP.Outside.L_meta_3652_aux.main N I G C
