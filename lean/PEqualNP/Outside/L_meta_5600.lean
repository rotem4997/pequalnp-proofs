import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5600

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

abbrev Q := Bool × Bool × Bool × Bool × Bool

def qand (a b : Q) : Q := (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2.1 && b.2.2.2.1, a.2.2.2.2 && b.2.2.2.2)

def qor (a b : Q) : Q := (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2.1 || b.2.2.2.1, a.2.2.2.2 || b.2.2.2.2)

def step (S : List Q) : List Q :=
  (true, true, true, true, true) :: (false, false, false, false, false) ::
    (S ++ (S.flatMap fun a => S.map fun b => qand a b) ++ (S.flatMap fun a => S.map fun b => qor a b))

def ev (W : Fin 5 → List Bool) (i : ℕ) : Q :=
  ((W 0).getD i false, (W 1).getD i false, (W 2).getD i false, (W 3).getD i false, (W 4).getD i false)

def gval (g : Gate) (x : List Bool) : Bool := g.op.eval (g.inputs.map fun i => x.getD i false)

def gv (g : Gate) (W : Fin 5 → List Bool) : Q :=
  (gval g (W 0), gval g (W 1), gval g (W 2), gval g (W 3), gval g (W 4))

def ext (W : Fin 5 → List Bool) (g : Gate) : Fin 5 → List Bool := fun k => W k ++ [gval g (W k)]

theorem mem_step_self {S : List Q} {x : Q} (h : x ∈ S) : x ∈ step S := by
  simp only [step, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (Or.inl h)))

theorem mem_step_and {S : List Q} {a b : Q} (ha : a ∈ S) (hb : b ∈ S) : qand a b ∈ step S := by
  simp only [step, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ha, b, hb, rfl⟩)))

theorem mem_step_or {S : List Q} {a b : Q} (ha : a ∈ S) (hb : b ∈ S) : qor a b ∈ step S := by
  simp only [step, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, rfl⟩))

theorem gate_mem (S : List Q) (W : Fin 5 → List Bool) (hS : ∀ i, ev W i ∈ S) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) : gv g W ∈ step S := by
  obtain ⟨op, l⟩ := g
  simp only at hop hlen
  match l, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · have : gv ⟨GateOp.and, []⟩ W = (true, true, true, true, true) := by
        simp [gv, gval, GateOp.eval]
      rw [this]; simp [step]
    · have : gv ⟨GateOp.or, []⟩ W = (false, false, false, false, false) := by
        simp [gv, gval, GateOp.eval]
      rw [this]; simp [step]
  | [a], _ =>
    rcases hop with rfl | rfl
    · have : gv ⟨GateOp.and, [a]⟩ W = ev W a := by
        simp [gv, gval, GateOp.eval, ev]
      rw [this]; exact mem_step_self (hS a)
    · have : gv ⟨GateOp.or, [a]⟩ W = ev W a := by
        simp [gv, gval, GateOp.eval, ev]
      rw [this]; exact mem_step_self (hS a)
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · have : gv ⟨GateOp.and, [a, b]⟩ W = qand (ev W a) (ev W b) := by
        simp [gv, gval, GateOp.eval, ev, qand]
      rw [this]; exact mem_step_and (hS a) (hS b)
    · have : gv ⟨GateOp.or, [a, b]⟩ W = qor (ev W a) (ev W b) := by
        simp [gv, gval, GateOp.eval, ev, qor]
      rw [this]; exact mem_step_or (hS a) (hS b)
  | _ :: _ :: _ :: _, h => simp at h

theorem ev_ext (W : Fin 5 → List Bool) (L : ℕ) (hL : ∀ k, (W k).length = L) (g : Gate)
    (S : List Q) (hS : ∀ i, ev W i ∈ S) (hz : (false, false, false, false, false) ∈ S) :
    ∀ i, ev (ext W g) i ∈ gv g W :: S := by
  intro i
  rcases lt_trichotomy i L with h | h | h
  · have : ev (ext W g) i = ev W i := by
      simp only [ev, ext, getD_snoc, hL, if_pos h]
    rw [this]; exact List.mem_cons_of_mem _ (hS i)
  · subst h
    have : ev (ext W g) i = gv g W := by
      simp only [ev, ext, getD_snoc, hL, gv, lt_self_iff_false, if_false, if_true, ite_true, ite_false, ↓reduceIte]
    rw [this]; exact List.mem_cons_self
  · have : ev (ext W g) i = (false, false, false, false, false) := by
      have h1 : ¬ i < L := by omega
      have h2 : i ≠ L := by omega
      simp only [ev, ext, getD_snoc, hL, if_neg h1, if_neg h2]
    rw [this]; exact List.mem_cons_of_mem _ hz

def X : Fin 5 → List Bool :=
  ![oneEach (0 : Fin 4) (1 : Fin 4), oneEach (1 : Fin 4) (1 : Fin 4),
    oneEach (2 : Fin 4) (0 : Fin 4), oneEach (2 : Fin 4) (1 : Fin 4), oneEach (3 : Fin 4) (0 : Fin 4)]

def S0 : List Q :=
  [(false, false, false, false, false), (true, false, false, false, false), (false, true, false, false, false),
    (false, false, true, true, false), (false, false, false, false, true), (false, false, true, false, true),
    (true, true, false, true, false)]

theorem hX : ∀ k, (X k).length = 8 := by
  intro k; fin_cases k <;> decide

theorem base : ∀ i, ev X i ∈ S0 := by
  intro i
  by_cases h : i < 8
  · interval_cases i <;> decide
  · have h0 : ∀ k, (X k).getD i false = false := by
      intro k
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hX k]; omega)]
      rfl
    have : ev X i = (false, false, false, false, false) := by
      simp only [ev, h0]
    rw [this]; decide

theorem hz0 : (false, false, false, false, false) ∈ S0 := by decide

def memb (t : Q) : List Q → Bool
  | [] => false
  | a :: l => decide (a = t) || memb t l

theorem memb_of_mem (t : Q) (l : List Q) (h : t ∈ l) : memb t l = true := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    cases h with
    | head => simp [memb]
    | tail _ h' => simp [memb, ih h']

theorem not_mem_of (t : Q) (l : List Q) (h : (!memb t l) = true) : t ∉ l := by
  intro hm
  rw [memb_of_mem t l hm] at h
  exact absurd h (by decide)

set_option maxRecDepth 100000 in
theorem keyb : (step S0).all (fun v1 => (!memb (true, true, true, false, false) (v1 :: S0)) &&
    (step (v1 :: S0)).all (fun v2 => !memb (true, true, true, false, false) (v2 :: v1 :: S0))) = true := by
  decide

theorem key : ∀ v1 ∈ step S0, (true, true, true, false, false) ∉ v1 :: S0 ∧
    ∀ v2 ∈ step (v1 :: S0), (true, true, true, false, false) ∉ v2 :: v1 :: S0 := by
  intro v1 hv1
  have h := List.all_eq_true.1 keyb v1 hv1
  rw [Bool.and_eq_true] at h
  obtain ⟨a, b⟩ := h
  refine ⟨not_mem_of _ _ a, fun v2 hv2 => not_mem_of _ _ (List.all_eq_true.1 b v2 hv2)⟩

theorem key0 : (true, true, true, false, false) ∉ S0 := by decide

theorem mono_of (C : Circuit) (hM : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM g hg
  refine ⟨?_, h2⟩
  simpa using h1

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  rintro ⟨⟨gs, o⟩, hM, hs, hR⟩
  have hM' := mono_of _ hM
  simp only [Circuit.size] at hs hM'
  match gs, hs, hM', hR with
  | [], _, _, hR =>
    have e0 : (X 0).getD o false = true := (hR 0 1).trans (by decide)
    have e1 : (X 1).getD o false = true := (hR 1 1).trans (by decide)
    have e2 : (X 2).getD o false = true := (hR 2 0).trans (by decide)
    have e3 : (X 3).getD o false = false := (hR 2 1).trans (by decide)
    have e4 : (X 4).getD o false = false := (hR 3 0).trans (by decide)
    have hout : ev X o = (true, true, true, false, false) := by
      unfold ev; rw [e0, e1, e2, e3, e4]
    have := base o
    rw [hout] at this
    exact key0 this
  | [g1], _, hM', hR =>
    obtain ⟨o1, l1⟩ := hM' g1 (by simp)
    have e0 : (ext X g1 0).getD o false = true := (hR 0 1).trans (by decide)
    have e1 : (ext X g1 1).getD o false = true := (hR 1 1).trans (by decide)
    have e2 : (ext X g1 2).getD o false = true := (hR 2 0).trans (by decide)
    have e3 : (ext X g1 3).getD o false = false := (hR 2 1).trans (by decide)
    have e4 : (ext X g1 4).getD o false = false := (hR 3 0).trans (by decide)
    have hout : ev (ext X g1) o = (true, true, true, false, false) := by
      unfold ev; rw [e0, e1, e2, e3, e4]
    have hv1 := gate_mem S0 X base g1 o1 l1
    have h1 := ev_ext X 8 hX g1 S0 base hz0 o
    rw [hout] at h1
    exact (key _ hv1).1 h1
  | [g1, g2], _, hM', hR =>
    obtain ⟨o1, l1⟩ := hM' g1 (by simp)
    obtain ⟨o2, l2⟩ := hM' g2 (by simp)
    have e0 : (ext (ext X g1) g2 0).getD o false = true := (hR 0 1).trans (by decide)
    have e1 : (ext (ext X g1) g2 1).getD o false = true := (hR 1 1).trans (by decide)
    have e2 : (ext (ext X g1) g2 2).getD o false = true := (hR 2 0).trans (by decide)
    have e3 : (ext (ext X g1) g2 3).getD o false = false := (hR 2 1).trans (by decide)
    have e4 : (ext (ext X g1) g2 4).getD o false = false := (hR 3 0).trans (by decide)
    have hout : ev (ext (ext X g1) g2) o = (true, true, true, false, false) := by
      unfold ev; rw [e0, e1, e2, e3, e4]
    have hv1 := gate_mem S0 X base g1 o1 l1
    have h1 := ev_ext X 8 hX g1 S0 base hz0
    have hX1 : ∀ k, (ext X g1 k).length = 9 := by
      intro k; simp [ext, hX]
    have hv2 := gate_mem _ _ h1 g2 o2 l2
    have h2 := ev_ext (ext X g1) 9 hX1 g2 _ h1 (List.mem_cons_of_mem _ hz0) o
    rw [hout] at h2
    exact (key _ hv1).2 _ hv2 h2
  | _ :: _ :: _ :: _, h, _, _ => simp at h

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide
  · decide

end PEqualNP.Outside.L_meta_5600

theorem PEqualNP.Outside.L_meta_5600 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 2 :=
  ⟨PEqualNP.Outside.L_meta_5600.upper, PEqualNP.Outside.L_meta_5600.lower⟩
