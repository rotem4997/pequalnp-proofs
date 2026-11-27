import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4025

open PEqualNP.CircuitLowerBounds

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def gv {α : Type} (z : α) (A O : α → α → α) (g : Gate) (w : List α) : α :=
  if isAnd g = true then A (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)
  else O (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)

def grun {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [gv z A O g w]) x

theorem grun_snoc {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (g : Gate) (x : List α) :
    grun z A O (gs ++ [g]) x = grun z A O gs x ++ [gv z A O g (grun z A O gs x)] := by
  simp [grun, List.foldl_append]

theorem grun_length {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :
    (grun z A O gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [grun]
  | append_singleton gs g ih => rw [grun_snoc]; simp [ih]; omega

theorem getD_lt {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    ∃ a b, gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j

theorem good_init {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n (gs ++ [g])) :
    Good n gs ∧ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · simpa using h gs.length (by simp)

theorem grun_input {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) (i : ℕ)
    (hi : i < x.length) : (grun z A O gs x).getD i z = x.getD i z := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [grun_snoc, getD_lt _ _ _ _ (by rw [grun_length]; omega), ih]

theorem grun_gate {α : Type} (z : α) (A O : α → α → α) (n : ℕ) (gs : List Gate) (hgs : Good n gs)
    (x : List α) (hx : x.length = n) : ∀ (j : ℕ) (hj : j < gs.length),
      (grun z A O gs x).getD (n + j) z = gv z A O gs[j] (grun z A O gs x) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, ha, hb⟩ := good_init hgs
    have hlen : (grun z A O gs x).length = n + gs.length := by rw [grun_length, hx]
    intro j hj
    have hin : ∀ (g' : Gate) (a b : ℕ), g'.inputs = [a, b] → a < n + gs.length →
        b < n + gs.length → gv z A O g' (grun z A O (gs ++ [g]) x) =
          gv z A O g' (grun z A O gs x) := by
      intro g' a b h ha hb
      unfold gv
      simp only [h, List.getD_cons_zero, List.getD_cons_succ]
      rw [grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; exact ha),
        getD_lt _ _ _ _ (by rw [hlen]; exact hb)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h]
      obtain ⟨-, a', b', h1, h2, h3⟩ := hg0 j h
      rw [hin _ a' b' h1 (by omega) (by omega), grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; omega)]
      exact ih hg0 j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, hin g a b hab ha hb, grun_snoc, ← hlen, getD_at]

theorem fold_congr {α : Type} (f g : List α → Gate → List α) (gs : List Gate)
    (h : ∀ q ∈ gs, ∀ w, f w q = g w q) : ∀ x, gs.foldl f x = gs.foldl g x := by
  induction gs with
  | nil => intro x; rfl
  | cons q gs ih =>
    intro x
    simp only [List.foldl_cons]
    rw [h q (by simp), ih (fun q' hq' => h q' (by simp [hq']))]

theorem wires_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (x : List Bool) :
    C.wires x = grun false (· && ·) (· || ·) C.gates x := by
  unfold Circuit.wires grun
  refine fold_congr _ _ _ (fun q hq w => ?_) x
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨hop, a, b, hab, -, -⟩ := h j hj
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, GateOp.eval]


def bA (p q : Bool × Bool) : Bool × Bool := (p.1 && q.1, (p.1 && q.2) || (p.2 && q.1))
def bO (p q : Bool × Bool) : Bool × Bool := (p.1 || q.1, p.2 || q.2)

theorem mem_good {n : ℕ} {gs : List Gate} (h : Good n gs) {q : Gate} (hq : q ∈ gs) :
    (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ ∃ a b, q.inputs = [a, b] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨h1, a, b, h2, -, -⟩ := h j hj
  exact ⟨h1, a, b, h2⟩

theorem lin_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (L : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C L x = grun (false, false) bA bO C.gates
      ((x.zipIdx).map fun (b, i) => if L i then (false, b) else (b, false)) := by
  unfold PEqualNP.ReadK.linearParts grun
  refine fold_congr _ _ _ (fun q hq w => ?_) _
  obtain ⟨hop, a, b, hab⟩ := mem_good h hq
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, bA, bO]


theorem fst (gs : List Gate) (X : List (Bool × Bool)) (x : List Bool) (hl : X.length = x.length)
    (h0 : ∀ i, (X.getD i (false, false)).1 = x.getD i false) :
    ∀ w, ((grun (false, false) bA bO gs X).getD w (false, false)).1 =
      (grun false (· && ·) (· || ·) gs x).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [grun] using h0
  | append_singleton gs g ih =>
    intro w
    have l1 : (grun (false, false) bA bO gs X).length = X.length + gs.length := grun_length _ _ _ _ _
    have l2 : (grun false (· && ·) (· || ·) gs x).length = x.length + gs.length :=
      grun_length _ _ _ _ _
    rw [grun_snoc, grun_snoc]
    rcases lt_trichotomy w (x.length + gs.length) with h | h | h
    · rw [getD_lt _ _ _ _ (by rw [l1, hl]; exact h), getD_lt _ _ _ _ (by rw [l2]; exact h)]
      exact ih w
    · subst h
      have e1 : ∀ b, (grun (false, false) bA bO gs X ++ [b]).getD (x.length + gs.length)
          (false, false) = b := fun b => by rw [← hl, ← l1, getD_at]
      have e2 : ∀ b, (grun false (· && ·) (· || ·) gs x ++ [b]).getD (x.length + gs.length) false
          = b := fun b => by rw [← l2, getD_at]
      rw [e1, e2]
      unfold gv
      split_ifs
      · simp only [bA]; rw [ih, ih]
      · simp only [bO]; rw [ih, ih]
    · rw [List.getD_eq_default _ _ (by simp [l1, hl]; omega),
        List.getD_eq_default _ _ (by simp [l2]; omega)]

end PEqualNP.Outside.L_meta_4025

theorem PEqualNP.Outside.L_meta_4025 : ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2 < x1 →     x3 < x1 →       x2 ≠ x3 →         PEqualNP.TopForm.IsAO2 x1 x4 →           have x9 : List (Bool × Bool) := PEqualNP.ReadK.linearParts x4 (fun (x9 : ℕ) => Decidable.decide (x9 = x2)) (List.map (fun (x9 : ℕ) => x9 == x2 || x9 == x3) (List.range x1));           have x10 : ℕ → Bool := fun (x10 : ℕ) => (x9.getD x10 (Bool.false, Bool.false)).2;           have x11 : List Bool := x4.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (↑x11 = x3));           ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x4.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x12) = (x11.getD x14 Bool.false && x10 x15 || x10 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x12) = (x10 x14 || x10 x15)) := by
  intro n u v C hu hv huv hAO P Q x11 j g a b hg hin
  obtain ⟨a1, a2, a3⟩ := hAO
  have hG : PEqualNP.Outside.L_meta_4025.Good n C.gates := by
    intro j hj
    have hm := List.getElem_mem hj
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 (a3 _ hm)
    have hr := a2 j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hr
    rw [List.getD_eq_getElem _ _ hj, hpq] at hr
    exact ⟨a1 _ hm, p, q, hpq, hr p (by simp), hr q (by simp)⟩
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hgj : C.gates[j] = g := by
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  set X : List (Bool × Bool) := (((List.range n).map fun i => i == u || i == v).zipIdx).map
    (fun (b, i) => if decide (i = u) = true then (false, b) else (b, false)) with hX
  have hXl : X.length = n := by simp [hX]
  have hP : P = PEqualNP.Outside.L_meta_4025.grun (false, false) PEqualNP.Outside.L_meta_4025.bA PEqualNP.Outside.L_meta_4025.bO C.gates X := PEqualNP.Outside.L_meta_4025.lin_eq C hG _ _
  have hx11 : x11 = PEqualNP.Outside.L_meta_4025.grun false (· && ·) (· || ·) C.gates
      (List.ofFn fun i : Fin n => decide ((i : ℕ) = v)) := PEqualNP.Outside.L_meta_4025.wires_eq C hG _
  have hgate := PEqualNP.Outside.L_meta_4025.grun_gate (false, false) PEqualNP.Outside.L_meta_4025.bA PEqualNP.Outside.L_meta_4025.bO n C.gates hG X hXl j hj
  rw [← hP, hgj] at hgate
  have hfst : ∀ w, (P.getD w (false, false)).1 = x11.getD w false := by
    intro w
    rw [hP, hx11]
    refine PEqualNP.Outside.L_meta_4025.fst C.gates X _ (by rw [hXl]; simp) (fun i => ?_) w
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by rw [hXl]; exact hi),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      simp only [hX, List.getElem_map, List.getElem_zipIdx, List.getElem_range]
      by_cases h : i = u
      · subst h
        simp [huv]
      · have hb : (i == u) = false := by simpa using h
        rw [if_neg (by simpa using h)]
        simp only [hb, Bool.false_or]
        rfl
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  have hQ : ∀ w, Q w = (P.getD w (false, false)).2 := fun w => rfl
  constructor
  · intro ho
    rw [hQ, hgate]
    have e : PEqualNP.Outside.L_meta_4025.isAnd g = true := by simp [PEqualNP.Outside.L_meta_4025.isAnd, ho]
    unfold PEqualNP.Outside.L_meta_4025.gv
    rw [if_pos e, hin]
    simp only [List.getD_cons_zero, List.getD_cons_succ, PEqualNP.Outside.L_meta_4025.bA]
    rw [hfst, hfst, ← hQ, ← hQ]
  · intro ho
    rw [hQ, hgate]
    have e : ¬ PEqualNP.Outside.L_meta_4025.isAnd g = true := by simp [PEqualNP.Outside.L_meta_4025.isAnd, ho]
    unfold PEqualNP.Outside.L_meta_4025.gv
    rw [if_neg e, hin]
    simp only [List.getD_cons_zero, List.getD_cons_succ, PEqualNP.Outside.L_meta_4025.bO]
    rw [← hQ, ← hQ]
