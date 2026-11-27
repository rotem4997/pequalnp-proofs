import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7551

open PEqualNP.CircuitLowerBounds

def step (x1 : List Bool) (x2 : Fin 32768) : List Bool :=
  x1 ++ [if (x2 : ℕ) < 16384 then x1.getD ((x2 : ℕ) % 128) false && x1.getD ((x2 : ℕ) / 128 % 128) false
    else x1.getD ((x2 : ℕ) % 128) false || x1.getD ((x2 : ℕ) / 128 % 128) false]

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def codeA (i j : ℕ) : Fin 32768 := ⟨i % 128 + 128 * (j % 128), by omega⟩

def codeO (i j : ℕ) : Fin 32768 := ⟨16384 + i % 128 + 128 * (j % 128), by omega⟩

theorem codeA_step (acc : List Bool) (i j : ℕ) (hi : i < 128) (hj : j < 128) :
    step acc (codeA i j) = acc ++ [acc.getD i false && acc.getD j false] := by
  have h1 : (i % 128 + 128 * (j % 128)) % 128 = i := by omega
  have h2 : (i % 128 + 128 * (j % 128)) / 128 % 128 = j := by omega
  have h3 : (i % 128 + 128 * (j % 128)) < 16384 := by omega
  simp only [step, codeA, h1, h2, h3, ite_true]

theorem codeO_step (acc : List Bool) (i j : ℕ) (hi : i < 128) (hj : j < 128) :
    step acc (codeO i j) = acc ++ [acc.getD i false || acc.getD j false] := by
  have h1 : (16384 + i % 128 + 128 * (j % 128)) % 128 = i := by omega
  have h2 : (16384 + i % 128 + 128 * (j % 128)) / 128 % 128 = j := by omega
  have h3 : ¬ (16384 + i % 128 + 128 * (j % 128)) < 16384 := by omega
  simp only [step, codeO, h1, h2, h3, ite_false]

def encOp (op : GateOp) (i j : ℕ) : Fin 32768 :=
  match op with
  | GateOp.and => codeA i j
  | _ => codeO i j

def dflt (op : GateOp) : ℕ :=
  match op with
  | GateOp.and => 1
  | _ => 0

def enc (g : Gate) : Fin 32768 :=
  match g.inputs with
  | [] => encOp g.op (dflt g.op) (dflt g.op)
  | [a] => encOp g.op (a + 1 + 1) (a + 1 + 1)
  | a :: b :: _ => encOp g.op (a + 1 + 1) (b + 1 + 1)

theorem enc_step (g : Gate) (w : List Bool) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hb : ∀ a ∈ g.inputs, a < 126) :
    step (false :: true :: w) (enc g) = false :: true :: wstep w g := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hb
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with h | h <;> subst h
    · simp [enc, encOp, dflt, codeA_step _ _ _ (show 1 < 128 by omega) (show 1 < 128 by omega), wstep, GateOp.eval]
    · simp [enc, encOp, dflt, codeO_step _ _ _ (show 0 < 128 by omega) (show 0 < 128 by omega), wstep, GateOp.eval]
  · have ha : a < 126 := hb a (by simp)
    rcases hop with h | h <;> subst h
    · simp [enc, encOp, codeA_step _ _ _ (show a + 1 + 1 < 128 by omega) (show a + 1 + 1 < 128 by omega),
        wstep, GateOp.eval]
    · simp [enc, encOp, codeO_step _ _ _ (show a + 1 + 1 < 128 by omega) (show a + 1 + 1 < 128 by omega),
        wstep, GateOp.eval]
  · have ha : a < 126 := hb a (by simp)
    have hb' : b < 126 := hb b (by simp)
    rcases hop with h | h <;> subst h
    · simp [enc, encOp, codeA_step _ _ _ (show a + 1 + 1 < 128 by omega) (show b + 1 + 1 < 128 by omega),
        wstep, GateOp.eval]
    · simp [enc, encOp, codeO_step _ _ _ (show a + 1 + 1 < 128 by omega) (show b + 1 + 1 < 128 by omega),
        wstep, GateOp.eval]
  · simp at hlen

theorem sim (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ a ∈ g.inputs, a < 126) :
    ∀ w, List.foldl step (false :: true :: w) (gs.map enc) = false :: true :: List.foldl wstep w gs := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have h := hg g (by simp)
    simp only [List.map_cons, List.foldl_cons]
    rw [enc_step g w h.1 h.2.1 h.2.2]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _

theorem wpre (gs : List Gate) : ∀ w, w <+: List.foldl wstep w gs := by
  induction gs with
  | nil => intro w; exact List.prefix_refl w
  | cons g gs ih =>
    intro w
    exact (List.prefix_append w _).trans (ih _)

theorem wlen (gs : List Gate) : ∀ w, (List.foldl wstep w gs).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

theorem getD_pre {l m : List Bool} (h : l <+: m) {n : ℕ} (hn : n < l.length) :
    m.getD n false = l.getD n false := by
  obtain ⟨r, hr⟩ := h
  rw [← hr]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

theorem rep (k w : ℕ) (hw : w < 128) : ∀ acc : List Bool, w < acc.length →
    List.foldl step acc (List.replicate k (codeA w w)) = acc ++ List.replicate k (acc.getD w false) := by
  induction k with
  | zero => intro acc _; simp
  | succ k ih =>
    intro acc h
    rw [List.replicate_succ, List.foldl_cons, codeA_step _ _ _ hw hw, Bool.and_self,
      ih _ (by simp; omega)]
    have e : (acc ++ [acc.getD w false]).getD w false = acc.getD w false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [e]
    simp [List.replicate_succ]

theorem getD_rep (acc : List Bool) (k n : ℕ) (v : Bool) (h1 : acc.length ≤ n) (h2 : n < acc.length + k) :
    (acc ++ List.replicate k v).getD n false = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h1]
  simp [List.getElem?_replicate, show n - acc.length < k by omega]

theorem gen (gs : List Gate) (x7 : List Bool) (hx : x7.length = 27)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ a ∈ g.inputs, a < 126)
    (t w : ℕ) (ht : t ≤ gs.length) (ht2 : t < 62) (hw : w < 29 + t) :
    (List.foldl step (false :: true :: x7) ((gs.take t).map enc ++ List.replicate (62 - t) (codeA w w))).getD 90 false
      = (false :: true :: List.foldl wstep x7 (gs.take t)).getD w false := by
  have hg' : ∀ g ∈ gs.take t, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ a ∈ g.inputs, a < 126 :=
    fun g hm => hg g (List.mem_of_mem_take hm)
  have hl : (false :: true :: List.foldl wstep x7 (gs.take t)).length = 29 + t := by
    simp [wlen, hx, List.length_take, Nat.min_eq_left ht]
    omega
  rw [List.foldl_append, sim _ hg' x7, rep _ _ (by omega) _ (by omega)]
  exact getD_rep _ _ _ _ (by omega) (by omega)

theorem main (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (hs : C.size ≤ 62)
    (hb : ∀ (x5 : Fin C.gates.length), ∀ x6 ∈ (C.gates.get x5).inputs, x6 < 27 + ↑x5) :
    ∃ codes : List (Fin 32768), codes.length = 62 ∧ ∀ x7 : List Bool, x7.length = 27 →
      (List.foldl step (false :: true :: x7) codes).getD 90 false = C.eval x7 := by
  have hs' : C.gates.length ≤ 62 := hs
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
      ∀ a ∈ g.inputs, a < 126 := by
    intro g hgm
    obtain ⟨h1, h2⟩ := hm g hgm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    refine ⟨h1, h2, ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hgm
    intro a ha
    rw [← hi] at ha
    have := hb i a ha
    have := i.isLt
    omega
  have hW : ∀ x7 : List Bool, ∀ t o, o < x7.length + t → t ≤ C.gates.length →
      (List.foldl wstep x7 (C.gates.take t)).getD o false = (C.wires x7).getD o false := by
    intro x7 t o ho ht
    have e : C.wires x7 = List.foldl wstep (List.foldl wstep x7 (C.gates.take t)) (C.gates.drop t) := by
      rw [← List.foldl_append, List.take_append_drop]
      rfl
    have hn : o < (List.foldl wstep x7 (C.gates.take t)).length := by
      rw [wlen, List.length_take, Nat.min_eq_left ht]
      exact ho
    rw [e]
    exact (getD_pre (wpre _ _) hn).symm
  have heval : ∀ x7, C.eval x7 = (C.wires x7).getD C.output false := fun _ => rfl
  by_cases hA : 27 ≤ C.output ∧ C.output < 27 + C.gates.length
  · by_cases h62 : C.output = 88
    · refine ⟨C.gates.map enc, by simp; omega, ?_⟩
      intro x7 hx
      have htk : C.gates.take 62 = C.gates := List.take_of_length_le (by omega)
      rw [sim _ hg x7, heval, h62, ← hW x7 62 88 (by omega) (by omega), htk]
      show (false :: true :: List.foldl wstep x7 C.gates).getD (88 + 1 + 1) false = _
      simp only [List.getD_cons_succ]
    · refine ⟨(C.gates.take (C.output - 26)).map enc ++
        List.replicate (62 - (C.output - 26)) (codeA (C.output + 2) (C.output + 2)), ?_, ?_⟩
      · simp only [List.length_append, List.length_map, List.length_take, List.length_replicate]
        omega
      intro x7 hx
      rw [gen C.gates x7 hx hg (C.output - 26) (C.output + 2) (by omega) (by omega) (by omega), heval,
        ← hW x7 (C.output - 26) C.output (by omega) (by omega)]
      show (false :: true :: _).getD (C.output + 1 + 1) false = _
      simp only [List.getD_cons_succ]
  · by_cases hB : C.output < 27
    · refine ⟨List.replicate 62 (codeA (C.output + 2) (C.output + 2)), by simp, ?_⟩
      intro x7 hx
      have h := gen C.gates x7 hx hg 0 (C.output + 2) (by omega) (by omega) (by omega)
      simp only [List.take_zero, List.map_nil, List.nil_append, Nat.sub_zero, List.foldl_nil] at h
      rw [h, heval, ← hW x7 0 C.output (by omega) (by omega)]
      simp only [List.take_zero, List.foldl_nil]
      show (false :: true :: x7).getD (C.output + 1 + 1) false = _
      simp only [List.getD_cons_succ]
    · refine ⟨List.replicate 62 (codeA 0 0), by simp, ?_⟩
      intro x7 hx
      have h := gen C.gates x7 hx hg 0 0 (by omega) (by omega) (by omega)
      simp only [List.take_zero, List.map_nil, List.nil_append, Nat.sub_zero, List.foldl_nil] at h
      rw [h, heval]
      have hl : (C.wires x7).length = 27 + C.gates.length := by
        rw [show C.wires x7 = List.foldl wstep x7 C.gates from rfl, wlen, hx]
      rw [List.getD_eq_default (C.wires x7) false (by omega)]
      simp only [List.getD_cons_zero]

end PEqualNP.Outside.L_meta_7551

theorem PEqualNP.Outside.L_meta_7551 : have x1 : List Bool → Fin (32768 : ℕ) → List Bool := fun (x1 : List Bool) (x2 : Fin (32768 : ℕ)) =>   have x3 : Bool := x1.getD (↑x2 % (128 : ℕ)) Bool.false;   have x4 : Bool := x1.getD (↑x2 / (128 : ℕ) % (128 : ℕ)) Bool.false;   x1 ++ [if ↑x2 < (16384 : ℕ) then x3 && x4 else x3 || x4]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (62 : ℕ) → (∀ (x5 : Fin x2.gates.length), ∀ x6 ∈ (x2.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) → ∃ (x6 : List (Fin (32768 : ℕ))), x6.length = (62 : ℕ) ∧ ∀ (x7 : List Bool), x7.length = (27 : ℕ) → (List.foldl x1 (Bool.false :: Bool.true :: x7) x6).getD (90 : ℕ) Bool.false = x2.eval x7 := by
  exact fun C hm hs hb => PEqualNP.Outside.L_meta_7551.main C hm hs hb
