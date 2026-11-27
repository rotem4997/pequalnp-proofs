import Mathlib
import PEqualNP.Defs

-- Circuit normalization adapted from open-goat/pequalnp-proofs, Apache 2.0.
-- Source modules: Shannon for evaluation, Link for normalization, Promise for the input rows.
namespace PEqualNP.Outside.L_meta_6021.Shannon

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_6021.Shannon

namespace PEqualNP.Outside.L_meta_6021.LRAT.Link

open PEqualNP.Outside.L_meta_6021.LRAT

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_6021.Shannon

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

end PEqualNP.Outside.L_meta_6021.LRAT.Link

namespace PEqualNP.Outside.L_meta_6021.LRAT.Promise

open PEqualNP.Represents

def row44 (u v : Fin 4) : ℕ := 2 ^ (u : ℕ) + 2 ^ (4 + (v : ℕ))

theorem row44_eq : ∀ u v : Fin 4,
    (List.ofFn fun i : Fin (4 + 4) => (row44 u v).testBit i) = oneEach u v := by decide

def rows44 : List ℕ :=
  (List.finRange 4).flatMap fun u => (List.finRange 4).map fun v => row44 u v

end PEqualNP.Outside.L_meta_6021.LRAT.Promise

namespace PEqualNP.Outside.L_meta_6021

def targetAt (r : ℕ) : Bool := ([33,65,129,18,66,20,36,24] : List ℕ).contains r

end PEqualNP.Outside.L_meta_6021

-- The upper bound is witnessed by nine explicit gates.

namespace PEqualNP.Outside.L_meta_6021

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [7, 9]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [8, 12]⟩,
    ⟨.or, [6, 13]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [10, 15]⟩], 16⟩

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (4958 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide

end PEqualNP.Outside.L_meta_6021

-- Exclude eight gates by checking a closed table of possible sets of live signals.

namespace PEqualNP.Outside.L_meta_6021.RepFront

inductive Run : Bool → Multiset Nat → Prop
  | done {budget s} (h : 4958 ∈ s) : Run budget s
  | merge {budget a b r v} (hop : v = (a &&& b) ∨ v = (a ||| b))
      (next : Run budget (v ::ₘ r)) : Run budget (a ::ₘ b ::ₘ r)
  | reuse {a b r v} (hop : v = (a &&& b) ∨ v = (a ||| b))
      (next : Run false (v ::ₘ a ::ₘ r)) : Run true (a ::ₘ b ::ₘ r)

end PEqualNP.Outside.L_meta_6021.RepFront

namespace PEqualNP.Outside.L_meta_6021.RepFront

def distinguishes (x p q : Nat) : Bool := x.testBit p && !(x.testBit q)

theorem distinguish_inputs {a b v p q : Nat}
    (op : v = (a &&& b) ∨ v = (a ||| b)) (h : distinguishes v p q = true) :
    distinguishes a p q = true ∨ distinguishes b p q = true := by
  rcases op with rfl | rfl <;>
    cases h1 : a.testBit p <;> cases h2 : a.testBit q <;>
    cases h3 : b.testBit p <;> cases h4 : b.testBit q <;>
    simp_all [distinguishes, Nat.testBit_and, Nat.testBit_or]

theorem Run.distinction {budget s} (h : Run budget s) (p q : Nat)
    (pq : distinguishes 4958 p q = true) : ∃ x ∈ s, distinguishes x p q = true := by
  induction h with
  | done mem => exact ⟨4958, mem, pq⟩
  | @merge budget a b r v op _ ih =>
    obtain ⟨x, mem, good⟩ := ih
    rcases Multiset.mem_cons.mp mem with rfl | mem
    · rcases distinguish_inputs op good with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · exact ⟨x, by simp [mem], good⟩
  | @reuse a b r v op _ ih =>
    obtain ⟨x, mem, good⟩ := ih
    rcases Multiset.mem_cons.mp mem with rfl | mem
    · rcases distinguish_inputs op good with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · rcases Multiset.mem_cons.mp mem with rfl | mem
      · exact ⟨x, by simp, good⟩
      · exact ⟨x, by simp [mem], good⟩

theorem remove_two (xs : List Nat) (a b : Nat) (r : Multiset Nat)
    (eq : (xs : Multiset Nat) = a ::ₘ b ::ₘ r) :
    a ∈ xs ∧ b ∈ xs.erase a ∧ (((xs.erase a).erase b : List Nat) : Multiset Nat) = r := by
  have left : ((xs.erase a : List Nat) : Multiset Nat) = b ::ₘ r := by
    rw [← Multiset.coe_erase, eq, Multiset.erase_cons_head]
  refine ⟨Multiset.mem_coe.mp (eq ▸ Multiset.mem_cons_self _ _), ?_, ?_⟩
  · apply Multiset.mem_coe.mp
    rw [left]
    exact Multiset.mem_cons_self _ _
  · rw [← Multiset.coe_erase, left, Multiset.erase_cons_head]


end PEqualNP.Outside.L_meta_6021.RepFront
namespace PEqualNP.Outside.L_meta_6021.RepFront

abbrev State := Bool × List Nat

def children (budget : Bool) (xs : List Nat) : List State :=
  xs.flatMap fun a => (xs.erase a).flatMap fun b =>
    let tail := (xs.erase a).erase b
    [a &&& b, a ||| b].flatMap fun v =>
      if budget then [(true,v :: tail),(false,v :: a :: tail)]
      else [(false,v :: tail)]

lemma merge_child (bgt : Bool) (xs : List Nat) {a b v : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs.erase a) (hop : v = (a &&& b) ∨ v = (a ||| b)) :
    (bgt, v :: (xs.erase a).erase b) ∈ children bgt xs := by
  unfold children
  refine List.mem_flatMap.mpr ⟨a, ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
  refine List.mem_flatMap.mpr ⟨v, by simpa using hop, ?_⟩
  cases bgt <;> simp

lemma reuse_child (xs : List Nat) {a b v : Nat} (ha : a ∈ xs) (hb : b ∈ xs.erase a)
    (hop : v = (a &&& b) ∨ v = (a ||| b)) :
    (false, v :: a :: (xs.erase a).erase b) ∈ children true xs := by
  unfold children
  refine List.mem_flatMap.mpr ⟨a, ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
  refine List.mem_flatMap.mpr ⟨v, by simpa using hop, ?_⟩
  simp

def marked (rows : Nat → State) (count : Nat) (st : State) (code : Nat) : Bool :=
  if code < 256 then
    distinguishes 4958 (code / 16) (code % 16) &&
    !(st.2.any fun x => distinguishes x (code / 16) (code % 16))
  else
    decide (code - 256 < count) && decide ((rows (code-256)).1 = st.1) &&
    decide (((rows (code-256)).2 : Multiset Nat) = (st.2 : Multiset Nat))

def checkMarks (rows : Nat → State) (count : Nat) : List State → List Nat → Bool
  | [], [] => true
  | s :: ss, m :: ms => marked rows count s m && checkMarks rows count ss ms
  | _, _ => false

lemma check_mem {rows count ss ms} (valid : checkMarks rows count ss ms = true)
    {s : State} (hmem : s ∈ ss) : ∃ m, marked rows count s m = true := by
  induction ss generalizing ms with
  | nil => simp at hmem
  | cons t ts ih =>
    cases ms with
    | nil => simp [checkMarks] at valid
    | cons m ms =>
      rw [checkMarks, Bool.and_eq_true] at valid
      rcases List.mem_cons.mp hmem with rfl | h
      · exact ⟨_,valid.1⟩
      · exact ih valid.2 h

def Seen (rows : Nat → State) (count : Nat) (budget : Bool) (s : Multiset Nat) : Prop :=
  ∃ i < count, (rows i).1 = budget ∧ ((rows i).2 : Multiset Nat) = s

lemma next_seen {rows count st code} (ok : marked rows count st code = true)
    (run : Run st.1 (st.2 : Multiset Nat)) : Seen rows count st.1 (st.2 : Multiset Nat) := by
  unfold marked at ok
  split at ok
  · rw [Bool.and_eq_true] at ok
    obtain ⟨x,hx,bit⟩ := run.distinction _ _ ok.1
    have yes : (st.2.any fun t => distinguishes t (code / 16) (code % 16)) = true :=
      List.any_eq_true.mpr ⟨x,Multiset.mem_coe.mp hx, bit⟩
    simp [yes] at ok
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
    exact ⟨_, ok.1.1, ok.1.2, ok.2⟩

def checkedRow (rows : Nat → State) (count : Nat) (marks : Nat → List Nat) (i : Nat) : Bool :=
  !((rows i).2.contains 4958) && checkMarks rows count (children (rows i).1 (rows i).2) (marks i)

theorem impossible_seen (rows : Nat → State) (count : Nat) (marks : Nat → List Nat)
    (table : ∀ i < count, checkedRow rows count marks i = true)
    {s : Multiset Nat} {bgt : Bool} (h : Run bgt s) : ¬ Seen rows count bgt s := by
  induction h with
  | @done bgt s mem =>
    rintro ⟨i,hi,_,eq⟩
    have target : 4958 ∈ (rows i).2 := Multiset.mem_coe.mp (eq ▸ mem)
    have ok := table i hi
    simp [checkedRow, target] at ok
  | @merge bgt a b r v op hnext ih =>
    rintro ⟨i,hi,eb,eq⟩
    obtain ⟨ha,hb,tail⟩ := remove_two (rows i).2 a b r eq
    let child : State := (bgt,v :: (((rows i).2.erase a).erase b))
    have cm : child ∈ children (rows i).1 (rows i).2 := by
      rw [eb]
      exact merge_child _ _ ha hb op
    have z := table i hi
    rw [checkedRow, Bool.and_eq_true] at z
    obtain ⟨m,ok⟩ := check_mem z.2 cm
    have eqnext : (child.2 : Multiset Nat) = v ::ₘ r :=
      congrArg (fun t : Multiset Nat => v ::ₘ t) tail
    have childRun : Run child.1 (child.2 : Multiset Nat) := eqnext.symm ▸ hnext
    have seen := next_seen ok childRun
    exact ih (eqnext ▸ seen)
  | @reuse a b r v op hnext ih =>
    rintro ⟨i,hi,eb,eq⟩
    obtain ⟨ha,hb,tail⟩ := remove_two (rows i).2 a b r eq
    let child : State := (false,v :: a :: (((rows i).2.erase a).erase b))
    have cm : child ∈ children (rows i).1 (rows i).2 := by
      rw [eb]
      exact reuse_child _ ha hb op
    have z := table i hi
    rw [checkedRow, Bool.and_eq_true] at z
    obtain ⟨m,ok⟩ := check_mem z.2 cm
    have eqnext : (child.2 : Multiset Nat) = v ::ₘ a ::ₘ r :=
      congrArg (fun t : Multiset Nat => v ::ₘ a ::ₘ t) tail
    have childRun : Run child.1 (child.2 : Multiset Nat) := eqnext.symm ▸ hnext
    have seen := next_seen ok childRun
    exact ih (eqnext ▸ seen)

end PEqualNP.Outside.L_meta_6021.RepFront

namespace PEqualNP.Outside.L_meta_6021.RepFront
def tabrowChunk0 : Array (State) := #[(true,[15,240,3840,4369,8738,17476,34952,61440]),
(true,[240,3840,4383,8738,17476,34952,61440]),
(false,[15,240,3840,4383,8738,17476,34952,61440]),
(false,[8,15,240,3840,4369,8738,17476,61440]),
(true,[15,3840,4369,8946,17476,34952,61440]),
(false,[15,240,3840,4369,8946,17476,34952,61440]),
(true,[15,3840,4369,8738,17476,35064,61440]),
(false,[15,240,3840,4369,8738,17476,35064,61440]),
(false,[15,240,3840,4369,8738,17476,34952,61680]),
(true,[15,240,4369,8738,20292,34952,61440]),
(false,[15,240,3840,4369,8738,20292,34952,61440]),
(true,[15,240,4369,8738,17476,36744,61440]),
(false,[15,240,3840,4369,8738,17476,36744,61440]),
(false,[15,240,3840,4369,8738,17476,34952,65280]),
(false,[240,3840,4369,4383,8738,17476,34952,61440]),
(false,[15,240,3840,4096,4369,8738,17476,34952])]

def tabrowChunk1 : Array (State) := #[(false,[15,3840,4369,8738,8946,17476,34952,61440]),
(false,[15,240,3840,4369,8738,17476,43690,61440]),
(true,[15,240,3840,4369,17476,34952,61986]),
(false,[15,240,3840,4369,8738,17476,34952,61986]),
(false,[15,240,4369,8738,17476,20292,34952,61440]),
(false,[15,240,3840,4369,8738,17476,52428,61440]),
(true,[15,240,3840,4369,8738,34952,62532]),
(false,[15,240,3840,4369,8738,17476,34952,62532]),
(false,[15,3840,4369,8738,17476,34952,35064,61440]),
(false,[15,240,4369,8738,17476,34952,36744,61440]),
(true,[15,240,3840,4369,8738,17476,63624]),
(false,[15,240,3840,4369,8738,17476,34952,63624]),
(false,[15,240,3840,4369,17476,34952,61440,61986]),
(false,[15,240,3840,4369,8738,34952,61440,62532]),
(false,[15,240,3840,4369,8738,17476,61440,63624]),
(true,[3840,4383,8946,17476,34952,61440])]

def tabrowChunk2 : Array (State) := #[(false,[240,3840,4383,8946,17476,34952,61440]),
(true,[3840,4383,8738,17476,35064,61440]),
(false,[240,3840,4383,8738,17476,35064,61440]),
(false,[240,3840,4383,8738,17476,34952,61680]),
(true,[240,4383,8738,20292,34952,61440]),
(false,[240,3840,4383,8738,20292,34952,61440]),
(true,[240,4383,8738,17476,36744,61440]),
(false,[240,3840,4383,8738,17476,36744,61440]),
(false,[240,3840,4383,8738,17476,34952,65280]),
(false,[8,240,3840,4383,8738,17476,61440]),
(false,[240,3840,4096,4383,8738,17476,34952]),
(false,[3840,4383,8738,8946,17476,34952,61440]),
(false,[240,3840,4383,8738,17476,43690,61440]),
(true,[240,3840,4383,17476,34952,61986]),
(false,[240,3840,4383,8738,17476,34952,61986]),
(false,[240,4383,8738,17476,20292,34952,61440])]

def tabrowChunk3 : Array (State) := #[(false,[240,3840,4383,8738,17476,52428,61440]),
(true,[240,3840,4383,8738,34952,62532]),
(false,[240,3840,4383,8738,17476,34952,62532]),
(false,[3840,4383,8738,17476,34952,35064,61440]),
(false,[240,4383,8738,17476,34952,36744,61440]),
(true,[240,3840,4383,8738,17476,63624]),
(false,[240,3840,4383,8738,17476,34952,63624]),
(false,[240,3840,4383,17476,34952,61440,61986]),
(false,[240,3840,4383,8738,34952,61440,62532]),
(false,[240,3840,4383,8738,17476,61440,63624]),
(false,[240,3840,4383,8738,17476,34952,61440]),
(false,[15,3840,4383,8946,17476,34952,61440]),
(false,[15,3840,4383,8738,17476,35064,61440]),
(false,[15,240,4383,8738,20292,34952,61440]),
(false,[15,240,4383,8738,17476,36744,61440]),
(false,[15,240,3840,4383,17476,34952,61986])]

def tabrowChunk4 : Array (State) := #[(false,[15,240,3840,4383,8738,34952,62532]),
(false,[15,240,3840,4383,8738,17476,63624]),
(false,[15,248,3840,4369,8738,17476,61440]),
(false,[15,240,3848,4369,8738,17476,61440]),
(false,[15,240,3840,4369,8746,17476,61440]),
(false,[15,240,3840,4369,8738,17484,61440]),
(false,[15,240,3840,4369,8738,17476,61448]),
(false,[8,15,3840,4369,8946,17476,61440]),
(false,[8,15,240,4369,8738,20292,61440]),
(false,[8,15,240,3840,4369,17476,61986]),
(false,[8,15,240,3840,4369,8738,62532]),
(true,[15,4369,8946,20292,34952,61440]),
(false,[15,3840,4369,8946,20292,34952,61440]),
(false,[15,3840,4369,8946,17476,36744,61440]),
(false,[15,3840,4369,8946,17476,34952,65280]),
(false,[3840,4369,4383,8946,17476,34952,61440])]

def tabrowChunk5 : Array (State) := #[(false,[15,3840,4096,4369,8946,17476,34952]),
(false,[15,3840,4369,8946,17476,43770,61440]),
(false,[15,3840,4369,8946,17476,34952,62194]),
(false,[15,4369,8946,17476,20292,34952,61440]),
(false,[15,3840,4369,8946,17476,52428,61440]),
(false,[15,3840,4369,8946,17476,34952,62532]),
(true,[15,3840,4369,8946,17476,63624]),
(false,[15,3840,4369,8946,17476,34952,63624]),
(false,[15,3840,4369,8946,17476,61440,63624]),
(false,[15,3840,4369,8946,17476,34952,61440]),
(false,[15,3840,4369,8946,17476,35064,61440]),
(false,[15,3840,4369,8946,17476,34952,61680]),
(false,[15,240,4369,8946,20292,34952,61440]),
(false,[15,240,3840,4369,17476,34952,62194]),
(false,[15,240,3840,4369,8946,34952,62532]),
(false,[15,240,3840,4369,8946,17476,63624])]

def tabrowChunk6 : Array (State) := #[(false,[15,3840,4369,8738,17476,35064,65280]),
(false,[3840,4369,4383,8738,17476,35064,61440]),
(false,[15,3840,4096,4369,8738,17476,35064]),
(false,[15,3840,4369,8738,17476,43770,61440]),
(true,[15,3840,4369,17476,35064,61986]),
(false,[15,3840,4369,8738,17476,35064,61986]),
(false,[15,4369,8738,17476,20292,35064,61440]),
(false,[15,3840,4369,8738,17476,35064,62532]),
(false,[15,3840,4369,8738,17476,35064,63736]),
(false,[15,3840,4369,17476,35064,61440,61986]),
(false,[15,3840,4369,8738,17476,35064,61440]),
(false,[15,3840,4369,8738,17476,35064,61680]),
(false,[15,240,4369,8738,20292,35064,61440]),
(false,[15,240,3840,4369,17476,35064,61986]),
(false,[15,240,3840,4369,8738,35064,62532]),
(false,[15,240,3840,4369,8738,17476,63736])]

def tabrowChunk7 : Array (State) := #[(false,[15,240,4369,8738,20292,34952,61680]),
(false,[15,240,4369,8738,17476,36744,61680]),
(false,[240,4369,4383,8738,20292,34952,61440]),
(false,[15,240,4096,4369,8738,20292,34952]),
(false,[15,4369,8738,8946,20292,34952,61440]),
(false,[15,240,4369,8738,20292,43690,61440]),
(false,[15,240,4369,8738,20292,34952,61986]),
(false,[15,240,4369,8738,20292,53196,61440]),
(false,[15,240,4369,8738,20292,34952,65348]),
(true,[15,240,4369,8738,20292,63624]),
(false,[15,240,4369,8738,20292,34952,63624]),
(false,[15,240,4369,8738,20292,61440,63624]),
(false,[15,240,4369,8738,20292,34952,61440]),
(false,[15,240,4369,8738,20292,36744,61440]),
(false,[15,240,4369,8738,20292,34952,65280]),
(false,[15,240,3840,4369,20292,34952,61986])]

def tabrowChunk8 : Array (State) := #[(false,[15,240,3840,4369,8738,34952,65348]),
(false,[15,240,3840,4369,8738,20292,63624]),
(false,[240,4369,4383,8738,17476,36744,61440]),
(false,[15,240,4096,4369,8738,17476,36744]),
(false,[15,4369,8738,8946,17476,36744,61440]),
(false,[15,240,4369,8738,17476,36744,61986]),
(false,[15,240,4369,8738,17476,53196,61440]),
(true,[15,240,4369,8738,36744,62532]),
(false,[15,240,4369,8738,17476,36744,62532]),
(false,[15,240,4369,8738,17476,36744,65416]),
(false,[15,240,4369,8738,36744,61440,62532]),
(false,[15,240,4369,8738,17476,36744,61440]),
(false,[15,240,4369,8738,17476,36744,65280]),
(false,[15,240,3840,4369,17476,36744,61986]),
(false,[15,240,3840,4369,8738,36744,62532]),
(false,[15,240,3840,4369,8738,17476,65416])]

def tabrowChunk9 : Array (State) := #[(false,[240,3840,4369,4383,17476,34952,61986]),
(false,[240,3840,4369,4383,8738,34952,62532]),
(false,[240,3840,4369,4383,8738,17476,63624]),
(false,[15,3840,4336,4369,8738,17476,34952]),
(false,[15,240,4369,7936,8738,17476,34952]),
(false,[15,240,3840,4369,12834,17476,34952]),
(false,[15,240,3840,4369,8738,21572,34952]),
(false,[15,240,3840,4369,8738,17476,39048]),
(false,[15,3840,4369,8946,17476,43690,61440]),
(false,[15,3840,4369,8946,17476,34952,61986]),
(false,[15,3840,4369,8738,8946,17476,63624]),
(false,[15,240,3840,4369,17476,43690,61986]),
(false,[15,240,3840,4369,8738,43690,62532]),
(false,[15,240,3840,4369,8738,17476,64170]),
(false,[15,240,3840,4369,17476,52428,61986]),
(false,[15,3840,4369,17476,34952,35064,61986])]

def tabrowChunk10 : Array (State) := #[(false,[15,240,3840,4369,17476,61986,64170]),
(false,[15,240,3840,4369,17476,34952,61986]),
(false,[15,240,4369,8738,20292,52428,61440]),
(false,[15,240,4369,8738,20292,34952,62532]),
(false,[15,240,4369,8738,17476,20292,63624]),
(false,[15,240,3840,4369,8738,52428,62532]),
(false,[15,240,3840,4369,8738,17476,64716]),
(false,[15,240,4369,8738,34952,36744,62532]),
(false,[15,240,3840,4369,8738,62532,64716]),
(false,[15,240,3840,4369,8738,34952,62532]),
(false,[15,4369,8738,17476,35064,36744,61440]),
(false,[15,3840,4369,8738,17476,35064,63624]),
(false,[15,240,4369,8738,17476,36744,63624]),
(false,[15,240,3840,4369,8738,17476,63624]),
(false,[15,240,3840,4369,34952,61986,62532]),
(false,[15,240,3840,4369,17476,61986,63624])]

def tabrowChunk11 : Array (State) := #[(false,[15,240,3840,4369,8738,62532,63624]),
(true,[4383,8946,20292,34952,61440]),
(false,[3840,4383,8946,20292,34952,61440]),
(false,[3840,4383,8946,17476,36744,61440]),
(false,[3840,4383,8946,17476,34952,65280]),
(false,[8,3840,4383,8946,17476,61440]),
(false,[3840,4096,4383,8946,17476,34952]),
(false,[3840,4383,8946,17476,43770,61440]),
(false,[3840,4383,8946,17476,34952,62194]),
(false,[4383,8946,17476,20292,34952,61440]),
(false,[3840,4383,8946,17476,52428,61440]),
(false,[3840,4383,8946,17476,34952,62532]),
(true,[3840,4383,8946,17476,63624]),
(false,[3840,4383,8946,17476,34952,63624]),
(false,[3840,4383,8946,17476,61440,63624]),
(false,[3840,4383,8946,17476,34952,61440])]

def tabrowChunk12 : Array (State) := #[(false,[3840,4383,8946,17476,35064,61440]),
(false,[3840,4383,8946,17476,34952,61680]),
(false,[240,4383,8946,20292,34952,61440]),
(false,[240,3840,4383,17476,34952,62194]),
(false,[240,3840,4383,8946,34952,62532]),
(false,[240,3840,4383,8946,17476,63624]),
(false,[3840,4383,8738,17476,35064,65280]),
(false,[3840,4096,4383,8738,17476,35064]),
(false,[3840,4383,8738,17476,43770,61440]),
(true,[3840,4383,17476,35064,61986]),
(false,[3840,4383,8738,17476,35064,61986]),
(false,[4383,8738,17476,20292,35064,61440]),
(false,[3840,4383,8738,17476,35064,62532]),
(false,[3840,4383,8738,17476,35064,63736]),
(false,[3840,4383,17476,35064,61440,61986]),
(false,[3840,4383,8738,17476,35064,61440])]

def tabrowChunk13 : Array (State) := #[(false,[3840,4383,8738,17476,35064,61680]),
(false,[240,4383,8738,20292,35064,61440]),
(false,[240,3840,4383,17476,35064,61986]),
(false,[240,3840,4383,8738,35064,62532]),
(false,[240,3840,4383,8738,17476,63736]),
(false,[240,4383,8738,20292,34952,61680]),
(false,[240,4383,8738,17476,36744,61680]),
(false,[8,240,4383,8738,20292,61440]),
(false,[240,4096,4383,8738,20292,34952]),
(false,[4383,8738,8946,20292,34952,61440]),
(false,[240,4383,8738,20292,43690,61440]),
(false,[240,4383,8738,20292,34952,61986]),
(false,[240,4383,8738,20292,53196,61440]),
(false,[240,4383,8738,20292,34952,65348]),
(true,[240,4383,8738,20292,63624]),
(false,[240,4383,8738,20292,34952,63624])]

def tabrowChunk14 : Array (State) := #[(false,[240,4383,8738,20292,61440,63624]),
(false,[240,4383,8738,20292,34952,61440]),
(false,[240,4383,8738,20292,36744,61440]),
(false,[240,4383,8738,20292,34952,65280]),
(false,[240,3840,4383,20292,34952,61986]),
(false,[240,3840,4383,8738,34952,65348]),
(false,[240,3840,4383,8738,20292,63624]),
(false,[240,4096,4383,8738,17476,36744]),
(false,[4383,8738,8946,17476,36744,61440]),
(false,[240,4383,8738,17476,36744,61986]),
(false,[240,4383,8738,17476,53196,61440]),
(true,[240,4383,8738,36744,62532]),
(false,[240,4383,8738,17476,36744,62532]),
(false,[240,4383,8738,17476,36744,65416]),
(false,[240,4383,8738,36744,61440,62532]),
(false,[240,4383,8738,17476,36744,61440])]

def tabrowChunk15 : Array (State) := #[(false,[240,4383,8738,17476,36744,65280]),
(false,[240,3840,4383,17476,36744,61986]),
(false,[240,3840,4383,8738,36744,62532]),
(false,[240,3840,4383,8738,17476,65416]),
(false,[248,3840,4383,8738,17476,61440]),
(false,[240,3848,4383,8738,17476,61440]),
(false,[240,3840,4383,8746,17476,61440]),
(false,[240,3840,4383,8738,17484,61440]),
(false,[240,3840,4383,8738,17476,61448]),
(false,[8,240,3840,4383,17476,61986]),
(false,[8,240,3840,4383,8738,62532]),
(false,[3840,4336,4383,8738,17476,34952]),
(false,[240,4383,7936,8738,17476,34952]),
(false,[240,3840,4383,12834,17476,34952]),
(false,[240,3840,4383,8738,21572,34952]),
(false,[240,3840,4383,8738,17476,39048])]

def tabrowChunk16 : Array (State) := #[(false,[3840,4383,8946,17476,43690,61440]),
(false,[3840,4383,8946,17476,34952,61986]),
(false,[3840,4383,8738,8946,17476,63624]),
(false,[240,3840,4383,17476,43690,61986]),
(false,[240,3840,4383,8738,43690,62532]),
(false,[240,3840,4383,8738,17476,64170]),
(false,[240,3840,4383,17476,52428,61986]),
(false,[3840,4383,17476,34952,35064,61986]),
(false,[240,3840,4383,17476,61986,64170]),
(false,[240,3840,4383,17476,34952,61986]),
(false,[240,4383,8738,20292,52428,61440]),
(false,[240,4383,8738,20292,34952,62532]),
(false,[240,4383,8738,17476,20292,63624]),
(false,[240,3840,4383,8738,52428,62532]),
(false,[240,3840,4383,8738,17476,64716]),
(false,[240,4383,8738,34952,36744,62532])]

def tabrowChunk17 : Array (State) := #[(false,[240,3840,4383,8738,62532,64716]),
(false,[240,3840,4383,8738,34952,62532]),
(false,[4383,8738,17476,35064,36744,61440]),
(false,[3840,4383,8738,17476,35064,63624]),
(false,[240,4383,8738,17476,36744,63624]),
(false,[240,3840,4104,4383,8738,17476]),
(false,[240,3840,4383,8738,17476,63624]),
(false,[240,3840,4383,34952,61986,62532]),
(false,[240,3840,4383,17476,61986,63624]),
(false,[240,3840,4383,8738,62532,63624]),
(false,[15,4383,8946,20292,34952,61440]),
(false,[15,3840,4383,8946,17476,63624]),
(false,[15,3840,4383,17476,35064,61986]),
(false,[15,240,4383,8738,20292,63624]),
(false,[15,240,4383,8738,36744,62532]),
(false,[15,3840,4369,8954,17476,61440])]

def tabrowChunk18 : Array (State) := #[(false,[15,248,4369,8738,20292,61440]),
(false,[15,248,3840,4369,17476,61986]),
(false,[15,248,3840,4369,8738,62532]),
(false,[15,3848,4369,8946,17476,61440]),
(false,[15,240,4369,8738,20300,61440]),
(false,[15,240,3848,4369,17476,61986]),
(false,[15,240,3848,4369,8738,62532]),
(false,[15,240,4369,8746,20292,61440]),
(false,[15,240,3840,4369,17476,61994]),
(false,[15,240,3840,4369,8746,62532]),
(false,[15,3840,4369,8946,17484,61440]),
(false,[15,240,3840,4369,17484,61986]),
(false,[15,240,3840,4369,8738,62540]),
(false,[15,3840,4369,8946,17476,61448]),
(false,[15,240,4369,8738,20292,61448]),
(false,[8,15,4369,8946,20292,61440])]

def tabrowChunk19 : Array (State) := #[(false,[4369,4383,8946,20292,34952,61440]),
(false,[15,4096,4369,8946,20292,34952]),
(false,[15,4369,8946,20292,43770,61440]),
(false,[15,4369,8946,20292,34952,62194]),
(false,[15,4369,8946,20292,53196,61440]),
(false,[15,4369,8946,20292,34952,65348]),
(true,[15,4369,8946,20292,63624]),
(false,[15,4369,8946,20292,34952,63624]),
(false,[15,4369,8946,20292,61440,63624]),
(false,[15,4369,8946,20292,34952,61440]),
(false,[15,4369,8946,20292,36744,61440]),
(false,[15,4369,8946,20292,34952,65280]),
(false,[15,3840,4369,8946,20292,63624]),
(false,[15,4369,8946,17476,36744,65280]),
(false,[15,3840,4369,8946,17476,65416]),
(false,[3840,4369,4383,8946,17476,63624])]

def tabrowChunk20 : Array (State) := #[(false,[15,4369,7936,8946,17476,34952]),
(false,[15,3840,4369,13042,17476,34952]),
(false,[15,3840,4369,8946,21572,34952]),
(false,[15,3840,4369,8946,17476,39048]),
(false,[15,3840,4369,17476,43770,62194]),
(false,[15,3840,4369,8946,17476,64250]),
(false,[15,4369,8946,20292,52428,61440]),
(false,[15,4369,8946,20292,34952,62532]),
(false,[15,4369,8946,17476,20292,63624]),
(false,[15,3840,4369,8946,52428,62532]),
(false,[15,3840,4369,8946,17476,64716]),
(false,[15,3840,4369,8946,17476,63624]),
(false,[15,4369,8946,20292,35064,61440]),
(false,[15,3840,4369,17476,35064,62194]),
(false,[15,3840,4369,8946,35064,62532]),
(false,[15,3840,4369,8946,17476,63736])]

def tabrowChunk21 : Array (State) := #[(false,[15,4369,8946,20292,34952,61680]),
(false,[15,240,4369,8946,20292,63624]),
(false,[3840,4369,4383,17476,35064,61986]),
(false,[15,4369,7936,8738,17476,35064]),
(false,[15,3840,4369,12834,17476,35064]),
(false,[15,3840,4369,8738,21572,35064]),
(false,[15,3840,4369,8738,17476,39160]),
(false,[15,3840,4369,17476,43770,61986]),
(false,[15,3840,4369,17476,35064,61986]),
(false,[15,4369,8738,20292,35064,62532]),
(false,[15,4369,8738,20292,35064,61680]),
(false,[15,240,4369,8738,20292,63736]),
(false,[240,4369,4383,8738,20292,63624]),
(false,[15,4336,4369,8738,20292,34952]),
(false,[15,240,4369,12834,20292,34952]),
(false,[15,240,4369,8738,24388,34952])]

def tabrowChunk22 : Array (State) := #[(false,[15,240,4369,8738,20292,39048]),
(false,[15,4369,8946,20292,43690,61440]),
(false,[15,4369,8946,20292,34952,61986]),
(false,[15,4369,8738,8946,20292,63624]),
(false,[15,240,4369,20292,43690,61986]),
(false,[15,240,4369,8738,20292,64170]),
(false,[15,240,4369,8738,53196,65348]),
(false,[15,240,4369,8738,20292,65484]),
(false,[15,240,4369,8738,20292,63624]),
(false,[15,240,4369,20292,36744,61986]),
(false,[15,240,4369,8738,36744,65348]),
(false,[15,240,4369,8738,20292,65416]),
(false,[240,4369,4383,8738,36744,62532]),
(false,[15,4336,4369,8738,17476,36744]),
(false,[15,240,4369,12834,17476,36744]),
(false,[15,240,4369,8738,21572,36744])]

def tabrowChunk23 : Array (State) := #[(false,[15,240,4369,8738,17476,40840]),
(false,[15,4369,8946,17476,36744,61986]),
(false,[15,240,4369,8738,53196,62532]),
(false,[15,240,4369,8738,36744,62532]),
(false,[15,3840,4369,8946,17476,64170]),
(false,[15,240,4369,8738,20292,64716]),
(false,[8,4383,8946,20292,61440]),
(false,[4096,4383,8946,20292,34952]),
(false,[4383,8946,20292,43770,61440]),
(false,[4383,8946,20292,34952,62194]),
(false,[4383,8946,20292,53196,61440]),
(false,[4383,8946,20292,34952,65348]),
(true,[4383,8946,20292,63624]),
(false,[4383,8946,20292,34952,63624]),
(false,[4383,8946,20292,61440,63624]),
(false,[4383,8946,20292,34952,61440])]

def tabrowChunk24 : Array (State) := #[(false,[4383,8946,20292,36744,61440]),
(false,[4383,8946,20292,34952,65280]),
(false,[3840,4383,8946,20292,63624]),
(false,[4383,8946,17476,36744,65280]),
(false,[3840,4383,8946,17476,65416]),
(false,[3848,4383,8946,17476,61440]),
(false,[3840,4383,8954,17476,61440]),
(false,[3840,4383,8946,17484,61440]),
(false,[3840,4383,8946,17476,61448]),
(false,[4383,7936,8946,17476,34952]),
(false,[3840,4383,13042,17476,34952]),
(false,[3840,4383,8946,21572,34952]),
(false,[3840,4383,8946,17476,39048]),
(false,[3840,4383,17476,43770,62194]),
(false,[3840,4383,8946,17476,64250]),
(false,[4383,8946,20292,52428,61440])]

def tabrowChunk25 : Array (State) := #[(false,[4383,8946,20292,34952,62532]),
(false,[4383,8946,17476,20292,63624]),
(false,[3840,4383,8946,52428,62532]),
(false,[3840,4383,8946,17476,64716]),
(false,[3840,4104,4383,8946,17476]),
(false,[3840,4383,8946,17476,63624]),
(false,[4383,8946,20292,35064,61440]),
(false,[3840,4383,17476,35064,62194]),
(false,[3840,4383,8946,35064,62532]),
(false,[3840,4383,8946,17476,63736]),
(false,[4383,8946,20292,34952,61680]),
(false,[240,4383,8946,20292,63624]),
(false,[4383,7936,8738,17476,35064]),
(false,[3840,4383,12834,17476,35064]),
(false,[3840,4383,8738,21572,35064]),
(false,[3840,4383,8738,17476,39160])]

def tabrowChunk26 : Array (State) := #[(false,[3840,4383,17476,43770,61986]),
(false,[3840,4383,17476,35064,61986]),
(false,[4383,8738,20292,35064,62532]),
(false,[4383,8738,20292,35064,61680]),
(false,[240,4383,8738,20292,63736]),
(false,[248,4383,8738,20292,61440]),
(false,[240,4383,8746,20292,61440]),
(false,[240,4383,8738,20300,61440]),
(false,[240,4383,8738,20292,61448]),
(false,[4336,4383,8738,20292,34952]),
(false,[240,4383,12834,20292,34952]),
(false,[240,4383,8738,24388,34952]),
(false,[240,4383,8738,20292,39048]),
(false,[4383,8946,20292,43690,61440]),
(false,[4383,8946,20292,34952,61986]),
(false,[4383,8738,8946,20292,63624])]

def tabrowChunk27 : Array (State) := #[(false,[240,4383,20292,43690,61986]),
(false,[240,4383,8738,20292,64170]),
(false,[240,4383,8738,53196,65348]),
(false,[240,4383,8738,20292,65484]),
(false,[240,4104,4383,8738,20292]),
(false,[240,4383,8738,20292,63624]),
(false,[240,4383,20292,36744,61986]),
(false,[240,4383,8738,36744,65348]),
(false,[240,4383,8738,20292,65416]),
(false,[4336,4383,8738,17476,36744]),
(false,[240,4383,12834,17476,36744]),
(false,[240,4383,8738,21572,36744]),
(false,[240,4383,8738,17476,40840]),
(false,[4383,8946,17476,36744,61986]),
(false,[240,4383,8738,53196,62532]),
(false,[240,4383,8738,36744,62532])]

def tabrowChunk28 : Array (State) := #[(false,[248,3840,4383,17476,61986]),
(false,[248,3840,4383,8738,62532]),
(false,[240,3848,4383,17476,61986]),
(false,[240,3848,4383,8738,62532]),
(false,[240,3840,4383,17476,61994]),
(false,[240,3840,4383,8746,62532]),
(false,[240,3840,4383,17484,61986]),
(false,[240,3840,4383,8738,62540]),
(false,[3840,4383,8946,17476,64170]),
(false,[240,4383,8738,20292,64716]),
(false,[3840,4344,4383,8738,17476]),
(false,[240,4383,7944,8738,17476]),
(false,[240,3840,4383,12842,17476]),
(false,[240,3840,4383,8738,21580]),
(false,[15,4383,8946,20292,63624]),
(false,[15,4369,8954,20292,61440])]

def tabrowChunk29 : Array (State) := #[(false,[15,4369,8946,20300,61440]),
(false,[15,4369,8946,20292,61448]),
(false,[4369,4383,8946,20292,63624]),
(false,[15,4369,13042,20292,34952]),
(false,[15,4369,8946,24388,34952]),
(false,[15,4369,8946,20292,39048]),
(false,[15,4369,20292,43770,62194]),
(false,[15,4369,8946,20292,64250]),
(false,[15,4369,8946,53196,65348]),
(false,[15,4369,8946,20292,65484]),
(false,[15,4369,8946,20292,63624]),
(false,[15,4369,8946,20292,65416]),
(false,[15,4369,8946,20292,64716]),
(false,[15,4369,8946,20292,63736]),
(false,[15,4369,8946,20292,64170]),
(false,[4383,8954,20292,61440])]

def tabrowChunk30 : Array (State) := #[(false,[4383,8946,20300,61440]),
(false,[4383,8946,20292,61448]),
(false,[4383,13042,20292,34952]),
(false,[4383,8946,24388,34952]),
(false,[4383,8946,20292,39048]),
(false,[4383,20292,43770,62194]),
(false,[4383,8946,20292,64250]),
(false,[4383,8946,53196,65348]),
(false,[4383,8946,20292,65484]),
(false,[4104,4383,8946,20292]),
(false,[4383,8946,20292,63624]),
(false,[4383,8946,20292,65416]),
(false,[4383,8946,20292,64716]),
(false,[4383,7944,8946,17476]),
(false,[3840,4383,13050,17476]),
(false,[3840,4383,8946,21580])]

def tabrowChunk31 : Array (State) := #[(false,[4383,8946,20292,63736]),
(false,[4383,8946,20292,64170]),
(false,[4344,4383,8738,20292]),
(false,[240,4383,12842,20292]),
(false,[240,4383,8738,24396]),
(false,[4383,13050,20292]),
(false,[4383,8946,24396])]

def tabrow (i : Nat) : State :=
  let a := match i / 16 with
    | 0 => tabrowChunk0
    | 1 => tabrowChunk1
    | 2 => tabrowChunk2
    | 3 => tabrowChunk3
    | 4 => tabrowChunk4
    | 5 => tabrowChunk5
    | 6 => tabrowChunk6
    | 7 => tabrowChunk7
    | 8 => tabrowChunk8
    | 9 => tabrowChunk9
    | 10 => tabrowChunk10
    | 11 => tabrowChunk11
    | 12 => tabrowChunk12
    | 13 => tabrowChunk13
    | 14 => tabrowChunk14
    | 15 => tabrowChunk15
    | 16 => tabrowChunk16
    | 17 => tabrowChunk17
    | 18 => tabrowChunk18
    | 19 => tabrowChunk19
    | 20 => tabrowChunk20
    | 21 => tabrowChunk21
    | 22 => tabrowChunk22
    | 23 => tabrowChunk23
    | 24 => tabrowChunk24
    | 25 => tabrowChunk25
    | 26 => tabrowChunk26
    | 27 => tabrowChunk27
    | 28 => tabrowChunk28
    | 29 => tabrowChunk29
    | 30 => tabrowChunk30
    | 31 => tabrowChunk31
    | _ => #[]
  a[i % 16]?.getD (false, [])

def tabmarkChunk0 : Array (List Nat) := #[[21,64,21,64,21,128,42,128,21,69,257,258,42,154,16,16,21,101,32,32,21,259,48,48,21,192,29,192,21,21,21,21,64,128,106,149,106,138,64,69,16,16,260,261,32,32,101,101,48,48,262,263,64,192,110,264,21,21,42,42,64,64,106,106,69,69,128,138,16,16,149,154,32,32,265,266,48,48,267,268,128,192,157,269,21,21,257,270,106,106,64,64,69,149,128,128,16,16,16,16,32,32,32,32,48,48,48,48,69,271,192,192,42,42,16,21,16,64,260,272,16,128,149,149,16,69,16,69,16,32,101,101,16,48,155,273,16,192,274,275,21,21,32,42,32,64,101,106,32,128,265,276,32,69,32,138,16,16,101,154,32,48,103,277,32,192,278,279,21,21,48,55,48,64,262,280,48,128,267,281,48,69,48,71,16,16,155,155,32,32,103,103,48,192,282,283,21,21,29,29,64,64,110,110,128,128,157,157,69,69,192,205,16,16,274,284,32,32,278,285,48,48,282,286],
[64,128,106,149,21,21,21,21,16,16,287,288,32,32,101,101,48,48,289,290,64,192,110,291,64,64,106,106,21,21,42,42,16,16,149,154,32,32,292,293,48,48,294,295,128,192,157,296,21,106,21,64,21,149,42,128,42,154,16,16,21,101,32,32,21,297,48,48,21,298,29,192,16,64,287,299,16,128,149,149,42,42,16,21,16,32,101,101,16,48,155,300,16,192,301,302,32,64,101,106,32,128,292,303,21,21,32,42,16,16,101,154,32,48,103,304,32,192,305,306,48,64,289,307,48,128,294,308,21,21,48,55,16,16,155,155,32,32,103,103,48,192,309,310,64,64,110,110,128,128,157,157,21,21,29,29,16,16,301,311,32,32,305,312,48,48,309,313],
[64,64,128,128,69,314,154,16,101,32,297,48,192,192,64,64,64,106,106,64,16,315,32,101,48,316,64,110,128,128,64,106,69,128,16,149,32,317,48,318,128,157,69,314,106,64,69,128,69,16,69,32,69,48,69,192,154,16,16,315,16,149,69,16,16,101,16,155,16,319,101,32,32,101,32,317,69,32,16,101,32,103,32,320,297,48,48,316,48,318,69,48,16,155,32,103,48,321,192,192,64,110,128,157,69,192,16,319,32,320,48,321],
[21,48,48,322,48,323,48,48,16,324,32,325,48,326,21,48,21,21,21,42,21,297,42,16,21,32,21,29,48,322,21,21,64,106,106,64,16,327,32,101,64,110,48,323,21,42,64,106,69,128,16,149,32,328,128,157,48,48,21,297,106,64,69,128,16,16,32,32,69,192,16,324,42,16,16,327,16,149,16,16,16,101,16,329,32,325,21,32,32,101,32,328,32,32,16,101,32,330,48,326,21,29,64,110,128,157,69,192,16,329,32,330],
[21,128,42,128,21,69,287,315,42,64,16,16,21,101,32,32,21,327,23,48,21,192,29,192,21,21,42,42,69,69,128,138,16,16,106,106,32,32,331,332,48,48,151,333,128,192,157,334,21,21,287,335,69,149,128,128,16,16,16,16,32,32,32,32,48,48,48,48,69,336,77,192,42,42,16,21,16,128,106,149,16,138,16,69,16,32,101,101,16,48,155,337,16,192,110,338,21,21,32,42,32,128,331,339,32,69,32,138,16,16,101,106,32,48,103,340,32,192,109,341,21,21,23,23,48,128,151,151,48,69,48,71,16,16,155,155,32,32,103,103,48,192,342,343,21,21,29,29,128,128,157,157,69,69,77,77,16,16,110,110,32,32,109,109,48,48,342,344],
[21,21,21,42,21,288,42,16,21,32,21,23,21,29,21,21,128,149,138,69,16,345,32,101,48,346,192,347,21,42,128,149,69,128,16,149,32,348,48,151,128,157,21,288,138,69,69,128,16,16,32,32,48,48,69,192,42,16,16,345,16,149,16,16,16,101,16,155,16,349,21,32,32,101,32,348,32,32,16,101,32,103,32,350,21,23,48,346,48,151,48,48,16,155,32,103,48,351,21,29,192,347,128,157,69,192,16,349,32,350,48,351],
[21,128,42,128,21,69,289,316,42,154,16,16,21,101,32,32,21,64,21,48,21,192,29,192,21,21,42,42,69,69,75,75,16,16,149,154,32,32,107,107,48,48,106,106,128,192,157,352,21,21,289,353,69,149,75,128,16,16,16,16,32,32,32,32,48,48,48,48,69,354,79,192,42,42,16,21,16,128,149,149,16,69,16,69,16,32,101,101,16,48,155,355,16,192,356,357,21,21,32,42,32,128,107,358,32,69,32,138,16,16,101,154,32,48,101,106,32,192,111,359,21,21,21,21,48,128,106,149,48,138,48,69,16,16,155,155,32,32,101,101,48,192,110,360,21,21,29,29,128,128,157,157,69,69,79,79,16,16,356,361,32,32,111,111,48,48,110,110],
[21,21,21,42,21,290,42,16,21,32,21,21,21,29,21,21,128,149,138,69,16,346,32,101,48,362,192,363,21,42,128,149,69,128,16,149,32,364,48,149,128,157,21,290,138,69,69,128,16,16,32,32,48,48,69,192,42,16,16,346,16,149,16,16,16,101,16,155,16,365,21,32,32,101,32,364,32,32,16,101,32,101,32,366,21,21,48,362,48,149,48,48,16,155,32,101,48,367,21,29,192,363,128,157,69,192,16,365,32,366,48,367],
[21,21,21,42,21,291,42,16,21,32,21,48,21,21,21,21,110,149,110,69,16,347,32,101,48,363,192,110,21,42,110,149,69,128,16,149,32,368,48,369,128,149,21,291,110,69,69,128,16,16,32,32,48,48,138,69,42,16,16,347,16,149,16,16,16,101,16,155,16,349,21,32,32,101,32,368,32,32,16,101,32,103,32,101,21,48,48,363,48,369,48,48,16,155,32,103,48,367,21,21,192,110,128,149,138,69,16,349,32,101,48,367],
[21,64,21,64,21,69,292,317,42,154,16,16,21,101,32,32,21,328,43,48,21,192,29,192,21,21,21,21,106,138,64,69,16,16,331,348,32,32,101,101,48,48,107,364,64,192,110,368,21,21,292,370,106,106,64,64,16,16,16,16,32,32,32,32,48,48,48,48,69,371,142,192,42,42,16,21,16,64,331,372,16,69,16,69,16,32,101,101,16,48,155,373,16,192,158,374,21,21,32,42,32,64,101,106,32,69,32,138,16,16,101,154,32,48,103,375,32,192,157,376,21,21,43,43,48,64,107,107,48,69,48,71,16,16,155,155,32,32,103,103,48,192,377,378,21,21,29,29,64,64,110,110,69,69,142,142,16,16,158,158,32,32,157,157,48,48,377,379],
[21,21,21,42,21,293,42,16,21,32,21,43,21,29,21,21,64,106,106,64,16,332,32,101,48,107,64,110,21,42,64,106,69,138,16,154,32,380,48,381,192,382,21,293,106,64,69,138,16,16,32,32,48,48,69,192,42,16,16,332,16,154,16,16,16,101,16,155,16,383,21,32,32,101,32,380,32,32,16,101,32,103,32,384,21,43,48,107,48,381,48,48,16,155,32,103,48,385,21,29,64,110,192,382,69,192,16,383,32,384,48,385],
[21,64,21,64,21,69,294,318,42,151,16,16,21,101,32,32,21,128,42,48,21,192,29,192,21,21,21,21,106,135,64,69,16,16,151,151,32,32,101,101,48,48,106,149,64,192,110,369,21,21,294,386,106,106,64,64,16,16,16,16,32,32,32,32,48,48,48,48,69,387,143,192,42,42,16,21,16,64,151,388,16,69,16,69,16,32,101,101,16,48,149,149,16,192,159,389,21,21,32,42,32,64,101,106,32,69,32,138,16,16,101,154,32,48,103,390,32,192,391,392,21,21,42,42,48,64,106,106,48,69,48,71,16,16,149,151,32,32,103,103,48,192,157,393,21,21,29,29,64,64,110,110,69,69,143,143,16,16,159,159,32,32,391,394,48,48,157,157],
[21,21,21,42,21,295,42,16,21,32,21,42,21,29,21,21,64,106,106,64,16,333,32,101,48,106,64,110,21,42,64,106,69,138,16,154,32,381,48,395,192,396,21,295,106,64,69,138,16,16,32,32,48,48,69,192,42,16,16,333,16,154,16,16,16,101,16,154,16,397,21,32,32,101,32,381,32,32,16,101,32,103,32,398,21,42,48,106,48,395,48,48,16,154,32,103,48,399,21,29,64,110,192,396,69,192,16,397,32,398,48,399],
[21,21,21,42,21,296,42,16,21,32,21,48,21,29,21,21,64,106,106,64,16,334,32,101,48,352,64,106,21,42,64,106,69,138,16,154,32,382,48,396,192,157,21,296,106,64,69,138,16,16,32,32,48,48,69,138,42,16,16,334,16,154,16,16,16,101,16,155,16,154,21,32,32,101,32,382,32,32,16,101,32,103,32,384,21,48,48,352,48,396,48,48,16,155,32,103,48,399,21,29,64,106,192,157,69,138,16,154,32,384,48,399],
[64,106,106,64,21,21,16,335,32,101,48,353,64,110,64,106,149,128,21,42,16,149,32,370,48,386,128,157,106,64,149,128,21,314,16,16,32,32,48,48,298,192,21,21,21,42,21,314,42,16,21,32,21,48,21,29,16,335,16,149,16,16,42,16,16,101,16,155,16,400,32,101,32,370,32,32,21,32,16,101,32,103,32,401,48,353,48,386,48,48,21,48,16,155,32,103,48,402,64,110,128,157,298,192,21,29,16,400,32,401,48,402],
[21,21,21,42,21,192,21,298,42,16,21,32,21,48,21,21,64,106,64,403,106,64,16,336,32,101,48,354,21,42,64,106,128,404,69,128,16,149,32,371,48,387,21,192,64,403,128,404,69,192,16,405,32,406,48,407,21,298,106,64,69,128,69,192,16,16,32,32,48,48,42,16,16,336,16,149,16,405,16,16,16,101,16,155,21,32,32,101,32,371,32,406,32,32,16,101,32,103,21,48,48,354,48,387,48,407,48,48,16,155,32,103]]

def tabmarkChunk1 : Array (List Nat) := #[[21,42,21,299,42,21,42,21,21,32,21,48,21,29,21,42,69,128,128,149,64,106,32,372,48,388,128,157,21,299,69,128,69,69,106,64,32,32,48,48,69,77,42,21,128,149,69,69,64,345,32,101,48,408,192,409,42,21,64,106,106,64,64,345,32,101,48,355,64,110,21,32,32,372,32,32,32,101,32,101,32,103,32,109,21,48,48,388,48,48,48,408,48,355,32,103,48,410,21,29,128,157,69,77,192,409,64,110,32,109,48,410],
[21,21,21,42,21,300,42,21,21,32,42,21,21,29,21,21,64,106,106,64,64,408,32,101,48,355,64,110,21,42,64,106,69,128,128,149,32,373,48,149,128,157,21,300,106,64,69,128,69,69,32,32,48,48,69,192,42,21,64,408,128,149,69,69,32,101,48,155,155,411,21,32,32,101,32,373,32,32,32,101,32,101,32,412,42,21,48,355,48,149,48,48,48,155,32,101,48,413,21,29,64,110,128,157,69,192,155,411,32,412,48,413],
[21,64,21,64,21,128,42,128,21,69,301,319,21,101,30,32,21,329,31,48,42,154,16,16,21,21,21,21,64,128,106,149,106,138,64,69,32,32,101,101,48,48,356,365,16,16,110,349,21,21,42,42,64,64,106,106,69,69,128,138,32,32,158,383,48,48,159,397,16,16,149,154,21,21,301,400,106,106,64,64,69,149,128,128,32,32,32,32,48,48,48,48,16,16,16,16,21,21,30,30,32,64,101,106,32,128,158,158,32,69,32,138,32,48,103,414,16,16,101,154,21,21,31,31,48,64,356,415,48,128,159,159,48,69,48,71,32,32,103,103,16,16,155,155,42,42,16,21,16,64,110,110,16,128,149,149,16,69,16,69,16,32,101,101,16,48,155,416],
[21,21,21,42,21,302,42,21,21,32,21,48,42,21,21,21,64,106,106,64,64,409,32,101,48,357,64,110,21,42,64,106,69,128,128,149,32,374,48,389,128,149,21,302,106,64,69,128,69,69,32,32,48,48,69,69,42,21,64,409,128,149,69,69,32,101,48,411,192,417,21,32,32,101,32,374,32,32,32,101,32,103,32,101,21,48,48,357,48,389,48,48,48,411,32,103,48,413,42,21,64,110,128,149,69,69,192,417,32,101,48,413],
[21,21,21,303,42,16,21,42,21,42,21,48,21,29,21,21,106,64,16,339,64,106,64,106,48,358,64,110,21,303,106,64,16,16,69,138,69,128,48,48,69,142,42,16,16,339,16,16,16,154,16,149,16,155,16,158,21,42,64,106,69,138,16,154,128,380,48,418,192,419,21,42,64,106,69,128,16,149,128,380,48,390,128,157,21,48,48,358,48,48,16,155,48,418,48,390,48,420,21,29,64,110,69,142,16,158,192,419,128,157,48,420],
[21,21,21,42,21,304,42,16,21,42,21,42,21,29,21,21,64,106,106,64,16,340,64,103,48,106,64,110,21,42,64,106,69,128,16,149,103,418,48,390,128,157,21,304,106,64,69,128,16,16,69,138,48,48,69,192,42,16,16,340,16,149,16,16,16,154,16,154,16,414,21,42,64,103,103,418,69,138,16,154,48,103,103,421,21,42,48,106,48,390,48,48,16,154,48,103,48,422,21,29,64,110,128,157,69,192,16,414,103,421,48,422],
[21,64,21,64,21,128,42,128,21,69,305,320,42,154,16,16,21,330,47,48,21,101,29,32,21,21,21,21,64,128,106,149,106,138,64,69,16,16,109,350,48,48,111,366,32,32,101,101,21,21,42,42,64,64,106,106,69,69,128,138,16,16,149,154,48,48,391,398,32,32,157,384,21,21,305,401,106,106,64,64,69,149,128,128,16,16,16,16,48,48,48,48,32,32,32,32,42,42,16,21,16,64,109,109,16,128,149,149,16,69,16,69,16,48,155,412,16,32,101,101,21,21,47,47,48,64,111,111,48,128,391,423,48,69,48,71,16,16,155,155,32,32,103,103,21,21,29,29,32,64,101,106,32,128,157,157,32,69,32,138,16,16,101,154,32,48,103,424],
[21,21,21,42,21,306,42,16,21,42,21,48,21,29,21,21,64,106,106,64,16,341,64,106,48,359,64,106,21,42,64,106,69,128,16,149,128,419,48,392,128,157,21,306,106,64,69,128,16,16,69,138,48,48,69,138,42,16,16,341,16,149,16,16,16,154,16,155,16,154,21,42,64,106,128,419,69,138,16,154,48,421,192,425,21,48,48,359,48,392,48,48,16,155,48,421,48,422,21,29,64,106,128,157,69,138,16,154,192,425,48,422],
[21,42,21,307,42,16,21,32,21,55,21,21,21,29,21,42,69,75,16,149,32,107,128,426,64,106,128,157,21,307,69,75,16,16,32,32,69,71,106,64,69,79,42,16,16,149,16,16,16,101,16,155,16,155,16,415,21,32,32,107,32,32,16,101,32,103,32,101,32,111,21,55,128,426,69,71,16,155,32,103,64,362,192,427,21,21,64,106,106,64,16,155,32,101,64,362,64,110,21,29,128,157,69,79,16,415,32,111,192,427,64,110],
[21,21,21,308,42,16,21,32,21,55,21,42,21,29,21,21,106,64,16,151,32,101,64,426,64,106,64,110,21,308,106,64,16,16,32,32,69,71,69,71,69,143,42,16,16,151,16,16,16,101,16,151,16,149,16,159,21,32,32,101,32,32,16,101,32,103,32,103,32,423,21,55,64,426,69,71,16,151,32,103,128,395,192,428,21,42,64,106,69,71,16,149,32,103,128,395,128,157,21,29,64,110,69,143,16,159,32,423,192,428,128,157],
[21,64,21,64,21,128,42,128,21,69,309,321,42,154,16,16,21,101,32,32,21,192,29,48,21,21,21,21,64,128,106,149,106,138,64,69,16,16,342,351,32,32,101,101,48,48,110,367,21,21,42,42,64,64,106,106,69,69,128,138,16,16,149,154,32,32,377,385,48,48,157,399,21,21,309,402,106,106,64,64,69,149,128,128,16,16,16,16,32,32,32,32,48,48,48,48,42,42,16,21,16,64,342,410,16,128,149,149,16,69,16,69,16,32,101,101,16,48,155,413,21,21,32,42,32,64,101,106,32,128,377,420,32,69,32,138,16,16,101,154,32,48,103,422,21,21,29,29,48,64,110,110,48,128,157,157,48,69,48,71,16,16,155,155,32,32,103,103],
[21,21,21,42,21,310,42,16,21,32,21,55,21,29,21,21,64,106,106,64,16,343,32,101,64,427,64,110,21,42,64,106,69,128,16,149,32,378,128,428,128,157,21,310,106,64,69,128,16,16,32,32,69,71,69,71,42,16,16,343,16,149,16,16,16,101,16,155,16,155,21,32,32,101,32,378,32,32,16,101,32,103,32,103,21,55,64,427,128,428,69,71,16,155,32,103,192,429,21,29,64,110,128,157,69,71,16,155,32,103,192,429],
[21,21,21,42,21,311,21,30,21,31,21,29,42,16,21,21,64,106,106,64,32,101,48,361,64,110,16,110,21,42,64,106,69,128,32,158,48,159,128,157,16,149,21,311,106,64,69,128,32,32,48,48,69,205,16,16,21,30,32,101,32,158,32,32,32,103,32,430,16,101,21,31,48,361,48,159,48,48,32,103,48,431,16,155,21,29,64,110,128,157,69,205,32,430,48,431,16,417,42,16,16,110,16,149,16,16,16,101,16,155,16,417],
[21,21,21,42,21,312,42,16,21,47,21,29,21,29,21,21,64,106,106,64,16,109,48,111,64,109,32,101,21,42,64,106,69,128,16,149,48,394,128,157,32,157,21,312,106,64,69,128,16,16,48,48,69,205,32,32,42,16,16,109,16,149,16,16,16,155,16,430,16,101,21,47,48,111,48,394,48,48,16,155,48,432,32,103,21,29,64,109,128,157,69,205,16,430,48,432,32,425,21,29,32,101,32,157,32,32,16,101,32,103,32,425],
[21,21,21,42,21,313,42,16,21,32,21,29,21,29,21,21,64,106,106,64,16,344,32,101,64,110,48,110,21,42,64,106,69,128,16,149,32,379,128,157,48,157,21,313,106,64,69,128,16,16,32,32,69,205,48,48,42,16,16,344,16,149,16,16,16,101,16,431,16,155,21,32,32,101,32,379,32,32,16,101,32,432,32,103,21,29,64,110,128,157,69,205,16,431,32,432,48,429,21,29,48,110,48,157,48,48,16,155,32,103,48,429],
[21,21,42,42,16,16,106,106,32,32,433,434,48,48,151,435,128,192,157,436,21,149,42,128,42,106,16,16,21,101,32,32,21,437,23,48,21,438,29,192,16,128,106,149,42,42,16,21,16,32,101,101,16,48,155,439,16,192,110,440,32,128,433,441,21,21,32,42,16,16,101,106,32,48,103,442,32,192,109,443,48,128,151,151,21,21,23,23,16,16,155,155,32,32,103,103,48,192,444,445,128,128,157,157,21,21,29,29,16,16,110,110,32,32,109,109,48,48,444,446]]

def tabmarkChunk2 : Array (List Nat) := #[[128,149,21,21,16,447,32,101,48,448,192,449,128,149,21,42,16,149,32,450,48,151,128,157,21,21,21,42,42,16,21,32,21,23,21,29,16,447,16,149,42,16,16,101,16,155,16,451,32,101,32,450,21,32,16,101,32,103,32,452,48,448,48,151,21,23,16,155,32,103,48,453,192,449,128,157,21,29,16,451,32,452,48,453],
[21,21,42,42,16,16,149,154,32,32,107,107,48,48,106,106,128,192,157,454,21,149,42,128,42,154,16,16,21,101,32,32,21,106,21,48,21,455,29,192,16,128,149,149,42,42,16,21,16,32,101,101,16,48,155,456,16,192,457,458,32,128,107,459,21,21,32,42,16,16,101,154,32,48,101,106,32,192,111,460,48,128,106,149,21,21,21,21,16,16,155,155,32,32,101,101,48,192,110,461,128,128,157,157,21,21,29,29,16,16,457,462,32,32,111,111,48,48,110,110],
[128,149,21,21,16,448,32,101,48,463,192,464,128,149,21,42,16,149,32,465,48,149,128,157,21,21,21,42,42,16,21,32,21,21,21,29,16,448,16,149,42,16,16,101,16,155,16,466,32,101,32,465,21,32,16,101,32,101,32,467,48,463,48,149,21,21,16,155,32,101,48,468,192,464,128,157,21,29,16,466,32,467,48,468],
[110,149,21,21,16,449,32,101,48,464,192,110,110,149,21,42,16,149,32,469,48,470,128,149,21,21,21,42,42,16,21,32,21,48,21,21,16,449,16,149,42,16,16,101,16,155,16,451,32,101,32,469,21,32,16,101,32,103,32,101,48,464,48,470,21,48,16,155,32,103,48,468,192,110,128,149,21,21,16,451,32,101,48,468],
[21,21,21,21,16,16,433,450,32,32,101,101,48,48,107,465,64,192,110,469,21,106,21,64,42,154,16,16,21,101,32,32,21,471,43,48,21,472,29,192,16,64,433,473,42,42,16,21,16,32,101,101,16,48,155,474,16,192,158,475,32,64,101,106,21,21,32,42,16,16,101,154,32,48,103,476,32,192,157,477,48,64,107,107,21,21,43,43,16,16,155,155,32,32,103,103,48,192,478,479,64,64,110,110,21,21,29,29,16,16,158,158,32,32,157,157,48,48,478,480],
[64,106,21,21,16,434,32,101,48,107,64,110,64,106,21,42,16,154,32,481,48,482,192,483,21,21,21,42,42,16,21,32,21,43,21,29,16,434,16,154,42,16,16,101,16,155,16,484,32,101,32,481,21,32,16,101,32,103,32,485,48,107,48,482,21,43,16,155,32,103,48,486,64,110,192,483,21,29,16,484,32,485,48,486],
[21,21,21,21,16,16,151,151,32,32,101,101,48,48,106,149,64,192,110,470,21,106,21,64,42,151,16,16,21,101,32,32,21,149,42,48,21,487,29,192,16,64,151,488,42,42,16,21,16,32,101,101,16,48,149,149,16,192,159,489,32,64,101,106,21,21,32,42,16,16,101,154,32,48,103,490,32,192,491,492,48,64,106,106,21,21,42,42,16,16,149,151,32,32,103,103,48,192,157,493,64,64,110,110,21,21,29,29,16,16,159,159,32,32,491,494,48,48,157,157],
[64,106,21,21,16,435,32,101,48,106,64,110,64,106,21,42,16,154,32,482,48,495,192,496,21,21,21,42,42,16,21,32,21,42,21,29,16,435,16,154,42,16,16,101,16,154,16,497,32,101,32,482,21,32,16,101,32,103,32,498,48,106,48,495,21,42,16,154,32,103,48,499,64,110,192,496,21,29,16,497,32,498,48,499],
[64,106,21,21,16,436,32,101,48,454,64,106,64,106,21,42,16,154,32,483,48,496,192,157,21,21,21,42,42,16,21,32,21,48,21,29,16,436,16,154,42,16,16,101,16,155,16,154,32,101,32,483,21,32,16,101,32,103,32,485,48,454,48,496,21,48,16,155,32,103,48,499,64,106,192,157,21,29,16,154,32,485,48,499],
[48,500,48,501,21,48,16,502,32,503,48,504,48,500,64,106,21,21,16,437,32,101,64,110,48,501,64,106,21,42,16,149,32,471,128,157,21,48,21,21,21,42,42,16,21,32,21,29,16,502,16,437,16,149,42,16,16,101,16,505,32,503,32,101,32,471,21,32,16,101,32,506,48,504,64,110,128,157,21,29,16,505,32,506],
[64,106,64,507,21,21,16,438,32,101,48,455,64,106,128,508,21,42,16,149,32,472,48,487,64,507,128,508,21,192,16,509,32,510,48,511,21,21,21,42,21,192,42,16,21,32,21,48,16,438,16,149,16,509,42,16,16,101,16,155,32,101,32,472,32,510,21,32,16,101,32,103,48,455,48,487,48,511,21,48,16,155,32,103],
[21,42,128,149,64,106,32,473,48,488,128,157,21,42,42,21,42,21,21,32,21,48,21,29,128,149,42,21,64,447,32,101,48,512,192,513,64,106,42,21,64,447,32,101,48,456,64,110,32,473,21,32,32,101,32,101,32,103,32,109,48,488,21,48,48,512,48,456,32,103,48,514,128,157,21,29,192,513,64,110,32,109,48,514],
[64,106,21,21,64,512,32,101,48,456,64,110,64,106,21,42,128,149,32,474,48,149,128,157,21,21,21,42,42,21,21,32,42,21,21,29,64,512,128,149,42,21,32,101,48,155,155,515,32,101,32,474,21,32,32,101,32,101,32,516,48,456,48,149,42,21,48,155,32,101,48,517,64,110,128,157,21,29,155,515,32,516,48,517],
[64,128,106,149,21,21,21,21,32,32,101,101,48,48,457,466,16,16,110,451,64,64,106,106,21,21,42,42,32,32,158,484,48,48,159,497,16,16,149,154,21,106,21,64,21,149,42,128,21,101,30,32,21,505,31,48,42,154,16,16,32,64,101,106,32,128,158,158,21,21,30,30,32,48,103,518,16,16,101,154,48,64,457,519,48,128,159,159,21,21,31,31,32,32,103,103,16,16,155,155,16,64,110,110,16,128,149,149,42,42,16,21,16,32,101,101,16,48,155,520],
[64,106,21,21,64,513,32,101,48,458,64,110,64,106,21,42,128,149,32,475,48,489,128,149,21,21,21,42,42,21,21,32,21,48,42,21,64,513,128,149,42,21,32,101,48,515,192,521,32,101,32,475,21,32,32,101,32,103,32,101,48,458,48,489,21,48,48,515,32,103,48,517,64,110,128,149,42,21,192,521,32,101,48,517],
[21,21,16,441,64,106,64,106,48,459,64,110,21,21,42,16,21,42,21,42,21,48,21,29,16,441,42,16,16,154,16,149,16,155,16,158,64,106,21,42,16,154,128,481,48,522,192,523,64,106,21,42,16,149,128,481,48,490,128,157,48,459,21,48,16,155,48,522,48,490,48,524,64,110,21,29,16,158,192,523,128,157,48,524]]

def tabmarkChunk3 : Array (List Nat) := #[[64,106,21,21,16,442,64,103,48,106,64,110,64,106,21,42,16,149,103,522,48,490,128,157,21,21,21,42,42,16,21,42,21,42,21,29,16,442,16,149,42,16,16,154,16,154,16,518,64,103,103,522,21,42,16,154,48,103,103,525,48,106,48,490,21,42,16,154,48,103,48,526,64,110,128,157,21,29,16,518,103,525,48,526],
[64,128,106,149,21,21,21,21,16,16,109,452,48,48,111,467,32,32,101,101,64,64,106,106,21,21,42,42,16,16,149,154,48,48,491,498,32,32,157,485,21,106,21,64,21,149,42,128,42,154,16,16,21,506,47,48,21,101,29,32,16,64,109,109,16,128,149,149,42,42,16,21,16,48,155,516,16,32,101,101,48,64,111,111,48,128,491,527,21,21,47,47,16,16,155,155,32,32,103,103,32,64,101,106,32,128,157,157,21,21,29,29,16,16,101,154,32,48,103,528],
[64,106,21,21,16,443,64,106,48,460,64,106,64,106,21,42,16,149,128,523,48,492,128,157,21,21,21,42,42,16,21,42,21,48,21,29,16,443,16,149,42,16,16,154,16,155,16,154,64,106,128,523,21,42,16,154,48,525,192,529,48,460,48,492,21,48,16,155,48,525,48,526,64,106,128,157,21,29,16,154,192,529,48,526],
[21,42,16,149,32,107,128,530,64,106,128,157,21,42,42,16,21,32,21,55,21,21,21,29,16,149,42,16,16,101,16,155,16,155,16,519,32,107,21,32,16,101,32,103,32,101,32,111,128,530,21,55,16,155,32,103,64,463,192,531,64,106,21,21,16,155,32,101,64,463,64,110,128,157,21,29,16,519,32,111,192,531,64,110],
[21,21,16,151,32,101,64,530,64,106,64,110,21,21,42,16,21,32,21,55,21,42,21,29,16,151,42,16,16,101,16,151,16,149,16,159,32,101,21,32,16,101,32,103,32,103,32,527,64,530,21,55,16,151,32,103,128,495,192,532,64,106,21,42,16,149,32,103,128,495,128,157,64,110,21,29,16,159,32,527,192,532,128,157],
[64,128,106,149,21,21,21,21,16,16,444,453,32,32,101,101,48,48,110,468,64,64,106,106,21,21,42,42,16,16,149,154,32,32,478,486,48,48,157,499,21,106,21,64,21,149,42,128,42,154,16,16,21,101,32,32,21,533,29,48,16,64,444,514,16,128,149,149,42,42,16,21,16,32,101,101,16,48,155,517,32,64,101,106,32,128,478,524,21,21,32,42,16,16,101,154,32,48,103,526,48,64,110,110,48,128,157,157,21,21,29,29,16,16,155,155,32,32,103,103],
[64,106,21,21,16,445,32,101,64,531,64,110,64,106,21,42,16,149,32,479,128,532,128,157,21,21,21,42,42,16,21,32,21,55,21,29,16,445,16,149,42,16,16,101,16,155,16,155,32,101,32,479,21,32,16,101,32,103,32,103,64,531,128,532,21,55,16,155,32,103,192,534,64,110,128,157,21,29,16,155,32,103,192,534],
[64,106,21,21,32,101,48,462,64,110,16,110,64,106,21,42,32,158,48,159,128,157,16,149,21,21,21,42,21,30,21,31,21,29,42,16,32,101,32,158,21,30,32,103,32,535,16,101,48,462,48,159,21,31,32,103,48,536,16,155,64,110,128,157,21,29,32,535,48,536,16,521,16,110,16,149,42,16,16,101,16,155,16,521],
[64,106,21,21,16,109,48,111,64,109,32,101,64,106,21,42,16,149,48,494,128,157,32,157,21,21,21,42,42,16,21,47,21,29,21,29,16,109,16,149,42,16,16,155,16,535,16,101,48,111,48,494,21,47,16,155,48,537,32,103,64,109,128,157,21,29,16,535,48,537,32,529,32,101,32,157,21,29,16,101,32,103,32,529],
[64,106,21,21,16,446,32,101,64,110,48,110,64,106,21,42,16,149,32,480,128,157,48,157,21,21,21,42,42,16,21,32,21,29,21,29,16,446,16,149,42,16,16,101,16,536,16,155,32,101,32,480,21,32,16,101,32,537,32,103,64,110,128,157,21,29,16,536,32,537,48,534,48,110,48,157,21,29,16,155,32,103,48,534],
[64,106,21,21,16,447,32,101,48,463,64,110,64,106,21,42,16,149,32,481,48,495,128,157,21,21,21,42,42,16,21,32,21,48,21,29,16,447,16,149,42,16,16,101,16,155,16,521,32,101,32,481,21,32,16,101,32,103,32,529,48,463,48,495,21,48,16,155,32,103,48,534,64,110,128,157,21,29,16,521,32,529,48,534],
[128,128,69,447,64,16,101,32,437,48,192,192,128,128,69,128,16,106,32,538,48,151,128,157,69,447,69,128,106,16,69,32,69,48,69,77,64,16,16,106,106,16,16,101,16,155,16,110,101,32,32,538,69,32,16,101,32,103,32,109,437,48,48,151,69,48,16,155,32,103,48,539,192,192,128,157,69,77,16,110,32,109,48,539],
[128,128,69,463,154,16,101,32,64,48,192,192,128,128,69,75,16,149,32,107,48,106,128,157,69,463,69,75,69,16,69,32,106,48,69,79,154,16,16,149,69,16,16,101,16,155,16,540,101,32,32,107,69,32,16,101,32,101,32,111,64,48,48,106,106,48,16,155,32,101,48,110,192,192,128,157,69,79,16,540,32,111,48,110],
[64,64,69,481,154,16,101,32,471,48,192,192,64,64,106,64,16,538,32,101,48,107,64,110,69,481,106,64,69,16,69,32,69,48,69,142,154,16,16,538,69,16,16,101,16,155,16,158,101,32,32,101,69,32,16,101,32,103,32,157,471,48,48,107,69,48,16,155,32,103,48,541,192,192,64,110,69,142,16,158,32,157,48,541],
[64,64,69,495,151,16,101,32,128,48,192,192,64,64,106,64,16,151,32,101,48,106,64,110,69,495,106,64,69,16,69,32,69,48,69,143,151,16,16,151,69,16,16,101,16,149,16,159,101,32,32,101,69,32,16,101,32,103,32,542,128,48,48,106,69,48,16,149,32,103,48,157,192,192,64,110,69,143,16,159,32,542,48,157],
[64,64,128,128,69,521,101,32,505,48,154,16,64,64,64,106,106,64,32,101,48,540,16,110,128,128,64,106,69,128,32,158,48,159,16,149,69,521,106,64,69,128,69,32,69,48,69,16,101,32,32,101,32,158,69,32,32,103,16,101,505,48,48,540,48,159,69,48,32,103,16,155,154,16,16,110,16,149,69,16,16,101,16,155]]

def tabmarkChunk4 : Array (List Nat) := #[[64,64,128,128,69,529,154,16,506,48,101,32,64,64,64,106,106,64,16,109,48,111,32,101,128,128,64,106,69,128,16,149,48,542,32,157,69,529,106,64,69,128,69,16,69,48,69,32,154,16,16,109,16,149,69,16,16,155,16,101,506,48,48,111,48,542,69,48,16,155,32,103,101,32,32,101,32,157,69,32,16,101,32,103],
[64,64,128,128,69,534,154,16,101,32,192,48,64,64,64,106,106,64,16,539,32,101,48,110,128,128,64,106,69,128,16,149,32,541,48,157,69,534,106,64,69,128,69,16,69,32,69,48,154,16,16,539,16,149,69,16,16,101,16,155,101,32,32,101,32,541,69,32,16,101,32,103,192,48,48,110,48,157,69,48,16,155,32,103],
[21,21,21,42,21,500,42,16,21,32,21,29,21,21,48,106,48,48,16,543,32,101,48,110,21,42,48,106,69,128,16,149,32,544,128,157,21,500,48,48,69,128,16,16,32,32,69,192,42,16,16,543,16,149,16,16,16,101,16,545,21,32,32,101,32,544,32,32,16,101,32,546,21,29,48,110,128,157,69,192,16,545,32,546],
[21,21,21,42,21,501,42,16,21,32,21,29,21,21,48,106,106,64,16,547,32,101,64,110,21,42,48,106,48,48,16,149,32,548,48,157,21,501,106,64,48,48,16,16,32,32,69,192,42,16,16,547,16,149,16,16,16,101,16,549,21,32,32,101,32,548,32,32,16,101,32,550,21,29,64,110,48,157,69,192,16,549,32,550],
[21,21,21,42,21,502,42,16,21,32,21,29,21,21,64,106,106,64,16,543,32,101,64,110,21,42,64,106,69,128,16,149,32,551,128,157,21,502,106,64,69,128,16,16,32,32,69,192,42,16,16,543,16,149,16,16,16,101,16,552,21,32,32,101,32,551,32,32,16,101,32,553,21,29,64,110,128,157,69,192,16,552,32,553],
[21,21,21,42,21,503,42,16,21,32,21,29,21,21,64,106,106,64,16,554,32,101,64,110,21,42,64,106,69,128,16,149,32,548,128,157,21,503,106,64,69,128,16,16,32,32,69,192,42,16,16,554,16,149,16,16,16,101,16,555,21,32,32,101,32,548,32,32,16,101,32,556,21,29,64,110,128,157,69,192,16,555,32,556],
[21,21,21,42,21,504,42,16,21,32,21,29,21,21,64,106,106,64,16,557,32,101,48,110,21,42,64,106,69,128,16,149,32,558,48,157,21,504,106,64,69,128,16,16,32,32,48,48,42,16,16,557,16,149,16,16,16,101,16,552,21,32,32,101,32,558,32,32,16,101,32,556,21,29,48,110,48,157,48,48,16,552,32,556],
[21,48,48,547,48,48,16,543,32,554,48,557,21,48,21,42,21,437,42,16,21,32,21,29,48,547,21,42,69,128,16,106,32,559,128,157,48,48,21,437,69,128,16,16,32,32,69,77,16,543,42,16,16,106,16,16,16,101,16,110,32,554,21,32,32,559,32,32,16,101,32,109,48,557,21,29,128,157,69,77,16,110,32,109],
[21,48,48,544,48,48,16,551,32,548,48,558,21,48,21,21,21,471,42,16,21,32,21,29,48,544,21,21,106,64,16,559,32,101,64,110,48,48,21,471,106,64,16,16,32,32,69,142,16,551,42,16,16,559,16,16,16,101,16,158,32,548,21,32,32,101,32,32,16,101,32,157,48,558,21,29,64,110,69,142,16,158,32,157],
[21,48,48,545,48,549,48,48,32,555,16,552,21,48,21,21,21,42,21,505,21,30,42,16,48,545,21,21,64,106,106,64,32,101,16,110,48,549,21,42,64,106,69,128,32,158,16,149,48,48,21,505,106,64,69,128,32,32,16,16,32,555,21,30,32,101,32,158,32,32,16,101,16,552,42,16,16,110,16,149,16,16,16,101],
[21,48,48,546,48,550,48,48,16,553,32,556,21,48,21,21,21,42,21,506,42,16,21,29,48,546,21,21,64,106,106,64,16,109,32,101,48,550,21,42,64,106,69,128,16,149,32,157,48,48,21,506,106,64,69,128,16,16,32,32,16,553,42,16,16,109,16,149,16,16,16,101,32,556,21,29,32,101,32,157,32,32,16,101],
[21,69,433,538,42,64,16,16,21,101,32,32,21,559,23,48,21,192,29,192,21,21,433,560,16,16,16,16,32,32,32,32,48,48,48,48,69,561,77,192,42,42,16,21,16,138,16,69,16,32,101,101,16,48,107,562,16,192,110,563,21,21,32,42,32,69,32,138,16,16,101,106,32,48,103,564,32,192,109,565,21,21,23,23,48,69,48,71,16,16,107,107,32,32,103,103,48,192,566,567,21,21,29,29,69,69,77,77,16,16,110,110,32,32,109,109,48,48,566,568],
[21,42,21,434,42,16,21,32,21,23,21,29,21,42,69,138,16,106,32,569,48,570,192,571,21,434,69,138,16,16,32,32,48,48,69,77,42,16,16,106,16,16,16,101,16,107,16,110,21,32,32,569,32,32,16,101,32,103,32,109,21,23,48,570,48,48,16,107,32,103,48,572,21,29,192,571,69,77,16,110,32,109,48,572],
[21,42,21,435,42,16,21,32,21,23,21,29,21,42,69,138,16,106,32,570,48,151,151,573,21,435,69,138,16,16,32,32,48,48,69,77,42,16,16,106,16,16,16,101,16,106,16,110,21,32,32,570,32,32,16,101,32,103,32,109,21,23,48,151,48,48,16,106,32,103,48,574,21,29,151,573,69,77,16,110,32,109,48,574],
[21,42,21,436,42,16,21,32,21,23,21,29,21,42,69,138,16,106,32,571,48,573,192,157,21,436,69,138,16,16,32,32,48,48,69,77,42,16,16,106,16,16,16,101,16,155,16,106,21,32,32,571,32,32,16,101,32,103,32,109,21,23,48,573,48,48,16,155,32,103,48,574,21,29,192,157,69,77,16,106,32,109,48,574],
[149,128,21,42,16,106,32,560,48,151,128,157,149,128,21,447,16,16,32,32,48,48,438,192,21,42,21,447,42,16,21,32,21,23,21,29,16,106,16,16,42,16,16,101,16,155,16,110,32,560,32,32,21,32,16,101,32,103,32,109,48,151,48,48,21,23,16,155,32,103,48,575,128,157,438,192,21,29,16,110,32,109,48,575]]

def tabmarkChunk5 : Array (List Nat) := #[[21,42,21,192,21,438,42,16,21,32,21,23,21,42,128,576,69,128,16,106,32,561,48,151,21,192,128,576,69,192,16,577,32,578,48,579,21,438,69,128,69,192,16,16,32,32,48,48,42,16,16,106,16,577,16,16,16,101,16,155,21,32,32,561,32,578,32,32,16,101,32,103,21,23,48,151,48,579,48,48,16,155,32,103],
[21,42,21,439,42,21,21,32,42,21,21,29,21,42,69,128,128,149,32,562,48,149,128,157,21,439,69,128,138,69,32,32,48,48,69,77,42,21,128,149,138,69,32,101,48,155,155,580,21,32,32,562,32,32,32,101,32,101,32,109,42,21,48,149,48,48,48,155,32,101,48,581,21,29,128,157,69,77,155,580,32,109,48,581],
[21,42,21,440,42,21,21,32,21,23,42,21,21,42,69,128,110,149,32,563,48,151,128,149,21,440,69,128,110,69,32,32,48,48,138,69,42,21,110,149,110,69,32,101,48,580,192,110,21,32,32,563,32,32,32,101,32,103,32,101,21,23,48,151,48,48,48,580,32,103,48,581,42,21,128,149,138,69,192,110,32,101,48,581],
[21,441,42,16,21,42,21,42,21,23,21,29,21,441,16,16,69,138,69,128,48,48,69,77,42,16,16,16,16,106,16,106,16,155,16,110,21,42,69,138,16,106,128,569,48,582,192,583,21,42,69,128,16,106,128,569,48,151,128,157,21,23,48,48,16,155,48,582,48,151,48,584,21,29,69,77,16,110,192,583,128,157,48,584],
[21,42,21,442,42,16,21,42,21,23,21,29,21,42,69,128,16,106,103,582,48,151,128,157,21,442,69,128,16,16,69,138,48,48,69,77,42,16,16,106,16,16,16,103,16,106,16,110,21,42,103,582,69,138,16,103,48,103,103,585,21,23,48,151,48,48,16,106,48,103,48,586,21,29,128,157,69,77,16,110,103,585,48,586],
[21,42,21,443,42,16,21,42,21,23,21,29,21,42,69,128,16,106,109,583,48,151,128,157,21,443,69,128,16,16,69,138,48,48,69,77,42,16,16,106,16,16,16,106,16,155,16,106,21,42,109,583,69,138,16,106,48,585,192,109,21,23,48,151,48,48,16,155,48,585,48,586,21,29,128,157,69,77,16,106,192,109,48,586],
[21,128,42,128,21,69,444,539,42,64,16,16,21,101,32,32,21,192,23,48,21,21,42,42,69,69,128,138,16,16,106,106,32,32,566,572,48,48,151,574,21,21,444,575,69,149,128,128,16,16,16,16,32,32,32,32,48,48,48,48,42,42,16,21,16,128,106,149,16,138,16,69,16,32,101,101,16,48,110,581,21,21,32,42,32,128,566,584,32,69,32,138,16,16,101,106,32,48,103,586,21,21,23,23,48,128,151,151,48,69,48,71,16,16,110,110,32,32,103,103],
[21,42,21,445,42,16,21,32,21,23,21,23,21,42,69,128,16,106,32,567,128,151,128,151,21,445,69,128,16,16,32,32,69,71,69,71,42,16,16,106,16,16,16,101,16,155,16,110,21,32,32,567,32,32,16,101,32,103,32,103,21,23,128,151,69,71,16,155,32,103,192,587,21,23,128,151,69,71,16,110,32,103,192,587],
[21,42,21,446,42,16,21,32,21,29,21,23,21,42,69,128,16,106,32,568,128,157,48,151,21,446,69,128,16,16,32,32,69,77,48,48,42,16,16,106,16,16,16,101,16,110,16,110,21,32,32,568,32,32,16,101,32,109,32,103,21,29,128,157,69,77,16,110,32,109,48,587,21,23,48,151,48,48,16,110,32,103,48,587],
[21,42,21,447,42,16,21,32,21,23,21,29,21,42,69,128,16,106,32,569,48,151,128,157,21,447,69,128,16,16,32,32,48,48,69,77,42,16,16,106,16,16,16,101,16,155,16,110,21,32,32,569,32,32,16,101,32,103,32,109,21,23,48,151,48,48,16,155,32,103,48,587,21,29,128,157,69,77,16,110,32,109,48,587],
[21,42,21,448,42,16,21,32,21,21,21,29,21,42,69,128,16,149,32,588,48,149,128,157,21,448,69,128,16,16,32,32,48,48,69,192,42,16,16,149,16,16,16,101,16,155,16,589,21,32,32,588,32,32,16,101,32,101,32,590,21,21,48,149,48,48,16,155,32,101,48,591,21,29,128,157,69,192,16,589,32,590,48,591],
[21,42,21,449,42,16,21,32,21,23,21,21,21,42,69,128,16,149,32,592,48,151,128,149,21,449,69,128,16,16,32,32,48,48,138,69,42,16,16,149,16,16,16,101,16,155,16,110,21,32,32,592,32,32,16,101,32,103,32,101,21,23,48,151,48,48,16,155,32,103,48,591,21,21,128,149,138,69,16,110,32,101,48,591],
[21,21,21,450,42,16,21,32,21,23,21,29,21,21,138,69,16,569,32,101,48,588,192,592,21,450,138,69,16,16,32,32,48,48,69,142,42,16,16,569,16,16,16,101,16,155,16,158,21,32,32,101,32,32,16,101,32,103,32,157,21,23,48,588,48,48,16,155,32,103,48,593,21,29,192,592,69,142,16,158,32,157,48,593],
[21,21,21,42,21,451,21,30,21,23,42,16,21,21,110,149,110,69,32,101,48,589,16,110,21,42,110,149,69,128,32,158,48,151,16,149,21,451,110,69,69,128,32,32,48,48,16,16,21,30,32,101,32,158,32,32,32,103,16,101,21,23,48,589,48,151,48,48,32,103,16,155,42,16,16,110,16,149,16,16,16,101,16,155],
[21,21,21,42,21,452,42,16,21,23,21,29,21,21,109,149,109,69,16,109,48,590,32,101,21,42,109,149,69,128,16,149,48,151,32,157,21,452,109,69,69,128,16,16,48,48,32,32,42,16,16,109,16,149,16,16,16,155,16,101,21,23,48,590,48,151,48,48,16,155,32,103,21,29,32,101,32,157,32,32,16,101,32,103],
[21,21,21,42,21,453,42,16,21,32,21,23,21,21,128,149,138,69,16,587,32,101,48,591,21,42,128,149,69,128,16,149,32,593,48,151,21,453,138,69,69,128,16,16,32,32,48,48,42,16,16,587,16,149,16,16,16,101,16,155,21,32,32,101,32,593,32,32,16,101,32,103,21,23,48,591,48,151,48,48,16,155,32,103]]

def tabmarkChunk6 : Array (List Nat) := #[[21,42,21,454,42,16,21,32,21,21,21,29,21,42,69,75,16,154,32,107,48,106,192,157,21,454,69,75,16,16,32,32,48,48,69,75,42,16,16,154,16,16,16,101,16,155,16,154,21,32,32,107,32,32,16,101,32,101,32,107,21,21,48,106,48,48,16,155,32,101,48,106,21,29,192,157,69,75,16,154,32,107,48,106],
[149,128,21,42,16,149,32,107,48,106,128,157,149,128,21,463,16,16,32,32,48,48,455,192,21,42,21,463,42,16,21,32,21,21,21,29,16,149,16,16,42,16,16,101,16,155,16,594,32,107,32,32,21,32,16,101,32,101,32,111,48,106,48,48,21,21,16,155,32,101,48,110,128,157,455,192,21,29,16,594,32,111,48,110],
[21,42,21,192,21,455,42,16,21,32,21,21,21,42,128,595,69,75,16,149,32,107,48,106,21,192,128,595,69,192,16,596,32,597,48,598,21,455,69,75,69,192,16,16,32,32,48,48,42,16,16,149,16,596,16,16,16,101,16,155,21,32,32,107,32,597,32,32,16,101,32,101,21,21,48,106,48,598,48,48,16,155,32,101],
[21,42,21,456,42,21,21,32,42,21,21,29,21,42,69,75,128,149,32,107,48,106,128,157,21,456,69,75,69,69,32,32,48,48,69,77,42,21,128,149,69,69,32,101,48,155,155,599,21,32,32,107,32,32,32,101,32,101,32,109,42,21,48,106,48,48,48,155,32,101,48,110,21,29,128,157,69,77,155,599,32,109,48,110],
[21,128,42,128,21,69,457,540,21,101,30,32,21,64,21,48,42,154,16,16,21,21,42,42,69,69,75,75,32,32,107,107,48,48,106,106,16,16,149,154,21,21,457,594,69,149,75,128,32,32,32,32,48,48,48,48,16,16,16,16,21,21,30,30,32,128,107,158,32,69,32,138,32,48,101,106,16,16,101,154,21,21,21,21,48,128,106,149,48,138,48,69,32,32,101,101,16,16,110,155,42,42,16,21,16,128,149,149,16,69,16,69,16,32,101,101,16,48,110,110],
[21,42,21,458,42,21,21,32,21,21,42,21,21,42,69,75,128,149,32,107,48,106,128,149,21,458,69,75,69,69,32,32,48,48,69,69,42,21,128,149,69,69,32,101,48,599,192,600,21,32,32,107,32,32,32,101,32,101,32,101,21,21,48,106,48,48,48,599,32,101,48,110,42,21,128,149,69,69,192,600,32,101,48,110],
[21,459,42,16,21,42,21,42,21,21,21,29,21,459,16,16,69,138,69,75,48,48,69,79,42,16,16,16,16,154,16,149,16,155,16,158,21,42,69,138,16,154,128,107,48,106,107,601,21,42,69,75,16,149,128,107,48,106,128,157,21,21,48,48,16,155,48,106,48,106,48,110,21,29,69,79,16,158,107,601,128,157,48,110],
[21,42,21,460,42,16,21,42,21,21,21,29,21,42,69,75,16,149,111,601,48,106,128,157,21,460,69,75,16,16,69,138,48,48,69,79,42,16,16,149,16,16,16,154,16,155,16,154,21,42,111,601,69,138,16,154,48,106,192,111,21,21,48,106,48,48,16,155,48,106,48,106,21,29,128,157,69,79,16,154,192,111,48,106],
[21,42,21,461,42,16,21,32,21,21,21,21,21,42,69,75,16,149,32,107,110,149,128,149,21,461,69,75,16,16,32,32,110,69,138,69,42,16,16,149,16,16,16,101,16,155,16,155,21,32,32,107,32,32,16,101,32,101,32,101,21,21,110,149,110,69,16,155,32,101,192,110,21,21,128,149,138,69,16,155,32,101,192,110],
[21,42,21,462,21,30,21,21,21,29,42,16,21,42,69,75,32,107,48,106,128,157,16,149,21,462,69,75,32,32,48,48,69,79,16,16,21,30,32,107,32,32,32,101,32,111,16,101,21,21,48,106,48,48,32,101,48,110,16,110,21,29,128,157,69,79,32,111,48,110,16,600,42,16,16,149,16,16,16,101,16,110,16,600],
[21,42,21,463,42,16,21,32,21,21,21,29,21,42,69,75,16,149,32,107,48,106,128,157,21,463,69,75,16,16,32,32,48,48,69,79,42,16,16,149,16,16,16,101,16,155,16,600,21,32,32,107,32,32,16,101,32,101,32,111,21,21,48,106,48,48,16,155,32,101,48,110,21,29,128,157,69,79,16,600,32,111,48,110],
[21,42,21,464,42,16,21,32,21,21,21,21,21,42,69,128,16,149,32,602,48,149,128,149,21,464,69,128,16,16,32,32,48,48,138,69,42,16,16,149,16,16,16,101,16,155,16,589,21,32,32,602,32,32,16,101,32,101,32,101,21,21,48,149,48,48,16,155,32,101,48,110,21,21,128,149,138,69,16,589,32,101,48,110],
[21,21,21,465,42,16,21,32,21,21,21,29,21,21,107,69,16,588,32,101,48,107,107,602,21,465,107,69,16,16,32,32,48,48,69,142,42,16,16,588,16,16,16,101,16,155,16,158,21,32,32,101,32,32,16,101,32,101,32,157,21,21,48,107,48,48,16,155,32,101,48,603,21,29,107,602,69,142,16,158,32,157,48,603],
[21,21,21,42,21,466,21,30,21,21,42,16,21,21,128,149,138,69,32,101,48,600,16,589,21,42,128,149,69,128,32,158,48,149,16,149,21,466,138,69,69,128,32,32,48,48,16,16,21,30,32,101,32,158,32,32,32,101,16,101,21,21,48,600,48,149,48,48,32,101,16,155,42,16,16,589,16,149,16,16,16,101,16,155],
[21,21,21,42,21,467,42,16,21,21,21,29,21,21,111,149,111,69,16,590,48,111,32,101,21,42,111,149,69,128,16,149,48,149,32,157,21,467,111,69,69,128,16,16,48,48,32,32,42,16,16,590,16,149,16,16,16,155,16,101,21,21,48,111,48,149,48,48,16,155,32,101,21,29,32,101,32,157,32,32,16,101,32,101],
[21,21,21,42,21,468,42,16,21,32,21,21,21,21,110,149,110,69,16,591,32,101,48,110,21,42,110,149,69,128,16,149,32,603,48,149,21,468,110,69,69,128,16,16,32,32,48,48,42,16,16,591,16,149,16,16,16,101,16,155,21,32,32,101,32,603,32,32,16,101,32,101,21,21,48,110,48,149,48,48,16,155,32,101]]

def tabmarkChunk7 : Array (List Nat) := #[[21,21,21,469,42,16,21,32,21,43,21,21,21,21,110,69,16,592,32,101,48,602,192,110,21,469,110,69,16,16,32,32,48,48,138,69,42,16,16,592,16,16,16,101,16,155,16,158,21,32,32,101,32,32,16,101,32,103,32,101,21,43,48,602,48,48,16,155,32,103,48,603,21,21,192,110,138,69,16,158,32,101,48,603],
[21,21,21,470,42,16,21,32,21,42,21,21,21,21,110,69,16,151,32,101,48,149,192,110,21,470,110,69,16,16,32,32,48,48,135,69,42,16,16,151,16,16,16,101,16,149,16,151,21,32,32,101,32,32,16,101,32,103,32,101,21,42,48,149,48,48,16,149,32,103,48,149,21,21,192,110,135,69,16,151,32,101,48,149],
[106,64,21,21,16,560,32,101,48,107,64,110,106,64,21,481,16,16,32,32,48,48,472,192,21,21,21,481,42,16,21,32,21,43,21,29,16,560,16,16,42,16,16,101,16,155,16,158,32,101,32,32,21,32,16,101,32,103,32,157,48,107,48,48,21,43,16,155,32,103,48,604,64,110,472,192,21,29,16,158,32,157,48,604],
[21,21,21,192,21,472,42,16,21,32,21,43,21,21,64,605,106,64,16,561,32,101,48,107,21,192,64,605,69,192,16,606,32,607,48,608,21,472,106,64,69,192,16,16,32,32,48,48,42,16,16,561,16,606,16,16,16,101,16,155,21,32,32,101,32,607,32,32,16,101,32,103,21,43,48,107,48,608,48,48,16,155,32,103],
[21,473,42,21,42,21,21,32,21,43,21,29,21,473,69,69,106,64,32,32,48,48,69,77,42,21,69,69,64,569,32,101,48,609,192,610,42,21,106,64,64,569,32,101,48,107,64,110,21,32,32,32,32,101,32,101,32,103,32,109,21,43,48,48,48,609,48,107,32,103,48,611,21,29,69,77,192,610,64,110,32,109,48,611],
[21,21,21,474,42,21,21,32,42,21,21,29,21,21,106,64,64,609,32,101,48,107,64,110,21,474,106,64,69,69,32,32,48,48,69,142,42,21,64,609,69,69,32,101,48,155,155,612,21,32,32,101,32,32,32,101,32,101,32,157,42,21,48,107,48,48,48,155,32,101,48,613,21,29,64,110,69,142,155,612,32,157,48,613],
[21,21,21,475,42,21,21,32,21,43,42,21,21,21,106,64,64,610,32,101,48,107,64,110,21,475,106,64,69,69,32,32,48,48,69,69,42,21,64,610,69,69,32,101,48,612,192,158,21,32,32,101,32,32,32,101,32,103,32,101,21,43,48,107,48,48,48,612,32,103,48,613,42,21,64,110,69,69,192,158,32,101,48,613],
[21,21,21,476,42,16,21,42,21,42,21,29,21,21,106,64,16,564,64,103,48,106,64,110,21,476,106,64,16,16,69,138,48,48,69,142,42,16,16,564,16,16,16,154,16,154,16,158,21,42,64,103,69,138,16,154,48,103,103,614,21,42,48,106,48,48,16,154,48,103,48,615,21,29,64,110,69,142,16,158,103,614,48,615],
[21,21,21,477,42,16,21,42,21,43,21,29,21,21,106,64,16,565,64,106,48,107,64,106,21,477,106,64,16,16,69,138,48,48,69,138,42,16,16,565,16,16,16,154,16,155,16,154,21,42,64,106,69,138,16,154,48,614,192,157,21,43,48,107,48,48,16,155,48,614,48,615,21,29,64,106,69,138,16,154,192,157,48,615],
[21,64,21,64,21,69,478,541,42,154,16,16,21,101,32,32,21,192,29,48,21,21,21,21,106,138,64,69,16,16,566,593,32,32,101,101,48,48,107,603,21,21,478,604,106,106,64,64,16,16,16,16,32,32,32,32,48,48,48,48,42,42,16,21,16,64,566,611,16,69,16,69,16,32,101,101,16,48,155,613,21,21,32,42,32,64,101,106,32,69,32,138,16,16,101,154,32,48,103,615,21,21,29,29,48,64,107,107,48,69,48,71,16,16,155,155,32,32,103,103],
[21,21,21,479,42,16,21,32,21,43,21,29,21,21,106,64,16,567,32,101,64,107,64,107,21,479,106,64,16,16,32,32,69,71,69,71,42,16,16,567,16,16,16,101,16,155,16,155,21,32,32,101,32,32,16,101,32,103,32,103,21,43,64,107,69,71,16,155,32,103,192,616,21,29,64,107,69,71,16,155,32,103,192,616],
[21,21,21,480,42,16,21,32,21,29,21,29,21,21,106,64,16,568,32,101,64,110,48,107,21,480,106,64,16,16,32,32,69,142,48,48,42,16,16,568,16,16,16,101,16,158,16,155,21,32,32,101,32,32,16,101,32,157,32,103,21,29,64,110,69,142,16,158,32,157,48,616,21,29,48,107,48,48,16,155,32,103,48,616],
[21,21,21,481,42,16,21,32,21,43,21,29,21,21,106,64,16,569,32,101,48,107,64,110,21,481,106,64,16,16,32,32,48,48,69,142,42,16,16,569,16,16,16,101,16,155,16,158,21,32,32,101,32,32,16,101,32,103,32,157,21,43,48,107,48,48,16,155,32,103,48,616,21,29,64,110,69,142,16,158,32,157,48,616],
[21,21,21,482,42,16,21,32,21,42,21,29,21,21,106,64,16,570,32,101,48,106,64,110,21,482,106,64,16,16,32,32,48,48,69,192,42,16,16,570,16,16,16,101,16,154,16,617,21,32,32,101,32,32,16,101,32,103,32,618,21,42,48,106,48,48,16,154,32,103,48,619,21,29,64,110,69,192,16,617,32,618,48,619],
[21,21,21,483,42,16,21,32,21,43,21,29,21,21,106,64,16,571,32,101,48,107,64,106,21,483,106,64,16,16,32,32,48,48,69,138,42,16,16,571,16,16,16,101,16,155,16,154,21,32,32,101,32,32,16,101,32,103,32,157,21,43,48,107,48,48,16,155,32,103,48,619,21,29,64,106,69,138,16,154,32,157,48,619],
[21,21,21,42,21,484,21,30,21,31,42,16,21,21,64,106,106,64,32,101,48,107,16,110,21,42,64,106,69,138,32,158,48,617,16,154,21,484,106,64,69,138,32,32,48,48,16,16,21,30,32,101,32,158,32,32,32,103,16,101,21,31,48,107,48,617,48,48,32,103,16,155,42,16,16,110,16,154,16,16,16,101,16,155]]

def tabmarkChunk8 : Array (List Nat) := #[[21,21,21,42,21,485,42,16,21,43,21,29,21,21,64,106,106,64,16,109,48,107,32,101,21,42,64,106,69,138,16,154,48,618,32,157,21,485,106,64,69,138,16,16,48,48,32,32,42,16,16,109,16,154,16,16,16,155,16,101,21,43,48,107,48,618,48,48,16,155,32,103,21,29,32,101,32,157,32,32,16,101,32,103],
[21,21,21,42,21,486,42,16,21,32,21,29,21,21,64,106,106,64,16,572,32,101,48,107,21,42,64,106,69,138,16,154,32,616,48,619,21,486,106,64,69,138,16,16,32,32,48,48,42,16,16,572,16,154,16,16,16,101,16,155,21,32,32,101,32,616,32,32,16,101,32,103,21,29,48,107,48,619,48,48,16,155,32,103],
[106,64,21,21,16,151,32,101,48,106,64,110,106,64,21,495,16,16,32,32,48,48,487,192,21,21,21,495,42,16,21,32,21,42,21,29,16,151,16,16,42,16,16,101,16,149,16,159,32,101,32,32,21,32,16,101,32,103,32,620,48,106,48,48,21,42,16,149,32,103,48,157,64,110,487,192,21,29,16,159,32,620,48,157],
[21,21,21,192,21,487,42,16,21,32,21,42,21,21,64,621,106,64,16,151,32,101,48,106,21,192,64,621,69,192,16,622,32,623,48,624,21,487,106,64,69,192,16,16,32,32,48,48,42,16,16,151,16,622,16,16,16,101,16,149,21,32,32,101,32,623,32,32,16,101,32,103,21,42,48,106,48,624,48,48,16,149,32,103],
[21,488,42,21,42,21,21,32,21,42,21,29,21,488,69,69,106,64,32,32,48,48,69,77,42,21,69,69,64,151,32,101,48,149,151,625,42,21,106,64,64,151,32,101,48,106,64,110,21,32,32,32,32,101,32,101,32,103,32,109,21,42,48,48,48,149,48,106,32,103,48,157,21,29,69,77,151,625,64,110,32,109,48,157],
[21,21,21,489,42,21,21,32,21,42,42,21,21,21,106,64,64,625,32,101,48,106,64,110,21,489,106,64,69,69,32,32,48,48,69,69,42,21,64,625,69,69,32,101,48,149,192,159,21,32,32,101,32,32,32,101,32,103,32,101,21,42,48,106,48,48,48,149,32,103,48,149,42,21,64,110,69,69,192,159,32,101,48,149],
[21,21,21,490,42,16,21,42,21,42,21,29,21,21,106,64,16,151,64,103,48,106,64,110,21,490,106,64,16,16,69,138,48,48,69,142,42,16,16,151,16,16,16,154,16,149,16,158,21,42,64,103,69,138,16,154,48,103,103,626,21,42,48,106,48,48,16,149,48,103,48,157,21,29,64,110,69,142,16,158,103,626,48,157],
[21,64,21,64,21,69,491,542,42,151,16,16,21,128,42,48,21,101,29,32,21,21,21,21,106,135,64,69,16,16,109,151,48,48,106,149,32,32,101,101,21,21,491,620,106,106,64,64,16,16,16,16,48,48,48,48,32,32,32,32,42,42,16,21,16,64,109,109,16,69,16,69,16,48,149,149,16,32,101,101,21,21,42,42,48,64,106,106,48,69,48,71,16,16,149,151,32,32,103,103,21,21,29,29,32,64,101,106,32,69,32,138,16,16,101,154,32,48,103,157],
[21,21,21,492,42,16,21,42,21,42,21,29,21,21,106,64,16,151,64,106,48,106,64,106,21,492,106,64,16,16,69,138,48,48,69,138,42,16,16,151,16,16,16,154,16,149,16,154,21,42,64,106,69,138,16,154,48,626,192,627,21,42,48,106,48,48,16,149,48,626,48,157,21,29,64,106,69,138,16,154,192,627,48,157],
[21,21,21,493,42,16,21,32,21,42,21,29,21,21,106,64,16,151,32,101,64,106,64,106,21,493,106,64,16,16,32,32,69,71,69,71,42,16,16,151,16,16,16,101,16,151,16,151,21,32,32,101,32,32,16,101,32,103,32,103,21,42,64,106,69,71,16,151,32,103,192,157,21,29,64,106,69,71,16,151,32,103,192,157],
[21,21,21,494,42,16,21,42,21,29,21,29,21,21,106,64,16,109,48,106,64,109,32,101,21,494,106,64,16,16,48,48,69,143,32,32,42,16,16,109,16,16,16,149,16,159,16,101,21,42,48,106,48,48,16,149,48,157,32,103,21,29,64,109,69,143,16,159,48,157,32,627,21,29,32,101,32,32,16,101,32,103,32,627],
[21,21,21,495,42,16,21,32,21,42,21,29,21,21,106,64,16,151,32,101,48,106,64,110,21,495,106,64,16,16,32,32,48,48,69,143,42,16,16,151,16,16,16,101,16,149,16,159,21,32,32,101,32,32,16,101,32,103,32,627,21,42,48,106,48,48,16,149,32,103,48,157,21,29,64,110,69,143,16,159,32,627,48,157],
[21,21,21,496,42,16,21,32,21,42,21,29,21,21,106,64,16,573,32,101,48,106,64,106,21,496,106,64,16,16,32,32,48,48,69,138,42,16,16,573,16,16,16,101,16,154,16,154,21,32,32,101,32,32,16,101,32,103,32,618,21,42,48,106,48,48,16,154,32,103,48,157,21,29,64,106,69,138,16,154,32,618,48,157],
[21,21,21,42,21,497,21,30,21,31,42,16,21,21,64,106,106,64,32,101,48,106,16,110,21,42,64,106,69,138,32,617,48,159,16,154,21,497,106,64,69,138,32,32,48,48,16,16,21,30,32,101,32,617,32,32,32,103,16,101,21,31,48,106,48,159,48,48,32,103,16,154,42,16,16,110,16,154,16,16,16,101,16,154],
[21,21,21,42,21,498,42,16,21,42,21,29,21,21,64,106,106,64,16,109,48,106,32,101,21,42,64,106,69,138,16,154,48,627,32,618,21,498,106,64,69,138,16,16,48,48,32,32,42,16,16,109,16,154,16,16,16,154,16,101,21,42,48,106,48,627,48,48,16,154,32,103,21,29,32,101,32,618,32,32,16,101,32,103],
[21,21,21,42,21,499,42,16,21,32,21,29,21,21,64,106,106,64,16,574,32,101,48,106,21,42,64,106,69,138,16,154,32,619,48,157,21,499,106,64,69,138,16,16,32,32,48,48,42,16,16,574,16,154,16,16,16,101,16,154,21,32,32,101,32,619,32,32,16,101,32,103,21,29,48,106,48,157,48,48,16,154,32,103]]

def tabmarkChunk9 : Array (List Nat) := #[[64,106,106,64,21,21,32,101,48,594,16,110,64,106,149,128,21,42,32,158,48,159,16,149,106,64,149,128,21,521,32,32,48,48,16,16,21,21,21,42,21,521,21,30,21,31,42,16,32,101,32,158,32,32,21,30,32,103,16,101,48,594,48,159,48,48,21,31,32,103,16,155,16,110,16,149,16,16,42,16,16,101,16,155],
[64,106,106,64,21,21,16,109,48,111,32,101,64,106,149,128,21,42,16,149,48,620,32,157,106,64,149,128,21,529,16,16,48,48,32,32,21,21,21,42,21,529,42,16,21,47,21,29,16,109,16,149,16,16,42,16,16,155,16,101,48,111,48,620,48,48,21,47,16,155,32,103,32,101,32,157,32,32,21,29,16,101,32,103],
[64,106,106,64,21,21,16,575,32,101,48,110,64,106,149,128,21,42,16,149,32,604,48,157,106,64,149,128,21,534,16,16,32,32,48,48,21,21,21,42,21,534,42,16,21,32,21,29,16,575,16,149,16,16,42,16,16,101,16,155,32,101,32,604,32,32,21,32,16,101,32,103,48,110,48,157,48,48,21,29,16,155,32,103],
[21,42,21,21,21,507,42,16,21,32,21,48,21,42,64,106,69,128,16,149,32,605,48,621,21,21,64,106,106,64,16,577,32,101,48,598,21,507,69,128,106,64,16,16,32,32,48,48,42,16,16,149,16,577,16,16,16,101,16,155,21,32,32,605,32,101,32,32,16,101,32,103,21,48,48,621,48,598,48,48,16,155,32,103],
[21,21,21,508,21,42,42,16,21,32,21,48,21,21,106,64,64,106,16,576,32,101,48,595,21,508,106,64,69,128,16,16,32,32,48,48,21,42,64,106,69,128,16,149,32,607,48,624,42,16,16,576,16,16,16,149,16,101,16,155,21,32,32,101,32,32,32,607,16,101,32,103,21,48,48,595,48,48,48,624,16,155,32,103],
[21,21,21,42,21,509,42,16,21,32,21,48,21,21,64,106,106,64,16,577,32,101,48,596,21,42,64,106,69,128,16,149,32,606,48,622,21,509,106,64,69,128,16,16,32,32,48,48,42,16,16,577,16,149,16,16,16,101,16,155,21,32,32,101,32,606,32,32,16,101,32,103,21,48,48,596,48,622,48,48,16,155,32,103],
[21,21,21,42,21,510,42,16,21,32,21,48,21,21,64,106,106,64,16,578,32,101,48,597,21,42,64,106,69,128,16,149,32,607,48,623,21,510,106,64,69,128,16,16,32,32,48,48,42,16,16,578,16,149,16,16,16,101,16,155,21,32,32,101,32,607,32,32,16,101,32,103,21,48,48,597,48,623,48,48,16,155,32,103],
[21,21,21,42,21,511,42,16,21,32,21,48,21,21,64,106,106,64,16,579,32,101,48,598,21,42,64,106,69,128,16,149,32,608,48,624,21,511,106,64,69,128,16,16,32,32,48,48,42,16,16,579,16,149,16,16,16,101,16,155,21,32,32,101,32,608,32,32,16,101,32,103,21,48,48,598,48,624,48,48,16,155,32,103],
[21,42,21,512,42,21,21,32,42,21,21,29,21,42,69,128,64,106,32,609,48,149,128,157,21,512,69,128,106,64,32,32,48,48,69,77,42,21,64,106,106,64,32,101,48,155,64,110,21,32,32,609,32,32,32,101,32,101,32,109,42,21,48,149,48,48,48,155,32,101,48,628,21,29,128,157,69,77,64,110,32,109,48,628],
[21,42,21,513,42,21,21,32,21,48,42,21,21,42,69,128,64,106,32,610,48,625,128,149,21,513,69,128,106,64,32,32,48,48,69,69,42,21,64,106,106,64,32,101,48,599,64,110,21,32,32,610,32,32,32,101,32,103,32,101,21,48,48,625,48,48,48,599,32,103,48,628,42,21,128,149,69,69,64,110,32,101,48,628],
[21,42,21,514,42,21,42,21,21,32,21,29,21,42,69,128,128,149,64,106,32,611,48,157,21,514,69,128,69,69,106,64,32,32,48,48,42,21,128,149,69,69,64,587,32,101,48,628,42,21,64,106,106,64,64,587,32,101,48,110,21,32,32,611,32,32,32,101,32,101,32,103,21,29,48,157,48,48,48,628,48,110,32,103],
[21,21,21,42,21,515,21,32,42,21,42,21,21,21,64,106,106,64,32,101,48,599,64,110,21,42,64,106,69,128,32,612,48,149,128,149,21,515,106,64,69,128,32,32,48,48,69,69,21,32,32,101,32,612,32,32,32,101,32,101,42,21,48,599,48,149,48,48,32,101,48,155,42,21,64,110,128,149,69,69,32,101,48,155],
[21,21,21,42,21,516,42,21,42,21,21,29,21,21,64,106,106,64,64,109,48,109,32,101,21,42,64,106,69,128,128,149,48,149,32,157,21,516,106,64,69,128,69,69,48,48,32,32,42,21,64,109,128,149,69,69,48,155,32,101,42,21,48,109,48,149,48,48,48,155,32,101,21,29,32,101,32,157,32,32,32,101,32,101],
[21,21,21,42,21,517,42,21,21,32,42,21,21,21,64,106,106,64,64,628,32,101,48,110,21,42,64,106,69,128,128,149,32,613,48,149,21,517,106,64,69,128,69,69,32,32,48,48,42,21,64,628,128,149,69,69,32,101,48,155,21,32,32,101,32,613,32,32,32,101,32,101,42,21,48,110,48,149,48,48,48,155,32,101],
[21,21,21,42,21,518,21,30,21,30,42,16,21,21,64,106,106,64,64,103,48,106,16,110,21,42,64,106,69,128,103,158,48,158,16,149,21,518,106,64,69,128,69,138,48,48,16,16,21,30,64,103,103,158,69,138,48,103,16,154,21,30,48,106,48,158,48,48,48,103,16,154,42,16,16,110,16,149,16,16,16,154,16,154],
[21,42,21,519,21,30,21,31,21,21,42,16,21,42,69,75,32,107,128,159,64,106,16,149,21,519,69,75,32,32,69,71,106,64,16,16,21,30,32,107,32,32,32,103,32,101,16,101,21,31,128,159,69,71,32,103,64,600,16,155,21,21,64,106,106,64,32,101,64,600,16,110,42,16,16,149,16,16,16,101,16,155,16,110]]

def tabmarkChunk10 : Array (List Nat) := #[[21,21,21,42,21,520,21,30,42,21,42,21,21,21,64,106,106,64,32,101,64,110,48,110,21,42,64,106,69,128,32,158,128,149,48,149,21,520,106,64,69,128,32,32,69,69,48,48,21,30,32,101,32,158,32,32,32,101,32,101,42,21,64,110,128,149,69,69,32,101,48,155,42,21,48,110,48,149,48,48,32,101,48,155],
[21,21,21,42,21,521,21,30,21,31,42,16,21,21,64,106,106,64,32,101,48,600,16,110,21,42,64,106,69,128,32,158,48,159,16,149,21,521,106,64,69,128,32,32,48,48,16,16,21,30,32,101,32,158,32,32,32,103,16,101,21,31,48,600,48,159,48,48,32,103,16,155,42,16,16,110,16,149,16,16,16,101,16,155],
[21,21,21,522,42,16,21,42,21,42,21,29,21,21,106,64,16,582,64,103,48,106,64,110,21,522,106,64,16,16,69,128,48,48,69,142,42,16,16,582,16,16,16,149,16,154,16,158,21,42,64,103,69,128,16,149,48,103,103,157,21,42,48,106,48,48,16,154,48,103,48,629,21,29,64,110,69,142,16,158,103,157,48,629],
[21,21,21,523,42,16,21,42,21,48,21,29,21,21,106,64,16,583,64,106,48,601,64,106,21,523,106,64,16,16,69,128,48,48,69,138,42,16,16,583,16,16,16,149,16,155,16,154,21,42,64,106,69,128,16,149,48,626,128,157,21,48,48,601,48,48,16,155,48,626,48,629,21,29,64,106,69,138,16,154,128,157,48,629],
[21,21,21,524,42,16,21,42,21,42,21,29,21,21,106,64,16,584,64,106,64,106,48,110,21,524,106,64,16,16,69,138,69,128,48,48,42,16,16,584,16,16,16,154,16,149,16,155,21,42,64,106,69,138,16,154,128,616,48,629,21,42,64,106,69,128,16,149,128,616,48,157,21,29,48,110,48,48,16,155,48,629,48,157],
[21,21,21,42,21,525,42,16,21,42,21,29,21,21,64,106,106,64,16,585,48,106,64,103,21,42,64,106,69,128,16,149,48,626,103,157,21,525,106,64,69,128,16,16,48,48,69,138,42,16,16,585,16,149,16,16,16,154,16,154,21,42,48,106,48,626,48,48,16,154,48,103,21,29,64,103,103,157,69,138,16,154,48,103],
[21,21,21,42,21,526,42,16,21,42,21,29,21,21,64,106,106,64,16,586,64,103,48,106,21,42,64,106,69,128,16,149,103,629,48,157,21,526,106,64,69,128,16,16,69,138,48,48,42,16,16,586,16,149,16,16,16,154,16,154,21,42,64,103,103,629,69,138,16,154,48,103,21,29,48,106,48,157,48,48,16,154,48,103],
[21,21,21,527,42,16,21,47,21,42,21,29,21,21,106,64,16,109,64,111,64,106,32,101,21,527,106,64,16,16,69,71,69,71,32,32,42,16,16,109,16,16,16,151,16,149,16,101,21,47,64,111,69,71,16,151,128,627,32,103,21,42,64,106,69,71,16,149,128,627,32,103,21,29,32,101,32,32,16,101,32,103,32,103],
[21,21,21,42,21,528,42,16,21,29,21,29,21,21,64,106,106,64,16,109,64,103,48,106,21,42,64,106,69,128,16,149,103,157,48,157,21,528,106,64,69,128,16,16,69,138,48,48,42,16,16,109,16,149,16,16,16,154,16,154,21,29,64,103,103,157,69,138,16,154,48,103,21,29,48,106,48,157,48,48,16,154,48,103],
[21,21,21,42,21,529,42,16,21,47,21,29,21,21,64,106,106,64,16,109,48,111,32,101,21,42,64,106,69,128,16,149,48,627,32,157,21,529,106,64,69,128,16,16,48,48,32,32,42,16,16,109,16,149,16,16,16,155,16,101,21,47,48,111,48,627,48,48,16,155,32,103,21,29,32,101,32,157,32,32,16,101,32,103],
[21,530,42,16,21,32,21,21,21,42,21,29,21,530,16,16,32,32,106,64,69,71,69,79,42,16,16,16,16,101,16,151,16,149,16,159,21,32,32,32,16,101,32,101,32,103,32,111,21,21,106,64,16,151,32,101,64,106,64,110,21,42,69,71,16,149,32,103,64,106,128,157,21,29,69,79,16,159,32,111,64,110,128,157],
[21,42,21,531,42,16,21,32,21,21,21,29,21,42,69,75,16,149,32,107,64,106,128,157,21,531,69,75,16,16,32,32,106,64,69,71,42,16,16,149,16,16,16,101,16,155,16,155,21,32,32,107,32,32,16,101,32,101,32,103,21,21,64,106,106,64,16,155,32,101,64,110,21,29,128,157,69,71,16,155,32,103,64,110],
[21,21,21,532,42,16,21,32,21,42,21,29,21,21,106,64,16,151,32,101,64,106,64,110,21,532,106,64,16,16,32,32,69,71,69,71,42,16,16,151,16,16,16,101,16,149,16,151,21,32,32,101,32,32,16,101,32,103,32,103,21,42,64,106,69,71,16,149,32,103,128,157,21,29,64,110,69,71,16,151,32,103,128,157],
[21,21,21,42,21,534,42,16,21,32,21,29,21,21,64,106,106,64,16,587,32,101,48,110,21,42,64,106,69,128,16,149,32,616,48,157,21,534,106,64,69,128,16,16,32,32,48,48,42,16,16,587,16,149,16,16,16,101,16,155,21,32,32,101,32,616,32,32,16,101,32,103,21,29,48,110,48,157,48,48,16,155,32,103],
[21,21,21,42,21,535,21,31,42,16,21,29,21,21,64,106,106,64,48,111,16,109,32,101,21,42,64,106,69,128,48,159,16,149,32,157,21,535,106,64,69,128,48,48,16,16,32,32,21,31,48,111,48,159,48,48,16,155,32,103,42,16,16,109,16,149,16,16,16,155,16,101,21,29,32,101,32,157,32,32,32,103,16,101],
[21,21,21,42,21,536,21,30,42,16,21,29,21,21,64,106,106,64,32,101,16,110,48,110,21,42,64,106,69,128,32,158,16,149,48,157,21,536,106,64,69,128,32,32,16,16,48,48,21,30,32,101,32,158,32,32,16,101,32,103,42,16,16,110,16,149,16,16,16,101,16,155,21,29,48,110,48,157,48,48,32,103,16,155]]

def tabmarkChunk11 : Array (List Nat) := #[[21,21,21,42,21,537,42,16,21,29,21,29,21,21,64,106,106,64,16,109,32,101,48,109,21,42,64,106,69,128,16,149,32,157,48,157,21,537,106,64,69,128,16,16,32,32,48,48,42,16,16,109,16,149,16,16,16,101,16,155,21,29,32,101,32,157,32,32,16,101,32,103,21,29,48,109,48,157,48,48,16,155,32,103],
[42,106,16,16,21,101,32,32,21,630,23,48,21,631,29,192,42,42,16,21,16,32,101,101,16,48,107,632,16,192,110,633,21,21,32,42,16,16,101,106,32,48,103,634,32,192,109,635,21,21,23,23,16,16,107,107,32,32,103,103,48,192,636,637,21,21,29,29,16,16,110,110,32,32,109,109,48,48,636,638],
[21,42,16,106,32,639,48,640,192,641,21,42,42,16,21,32,21,23,21,29,16,106,42,16,16,101,16,107,16,110,32,639,21,32,16,101,32,103,32,109,48,640,21,23,16,107,32,103,48,642,192,641,21,29,16,110,32,109,48,642],
[21,42,16,106,32,640,48,151,151,643,21,42,42,16,21,32,21,23,21,29,16,106,42,16,16,101,16,106,16,110,32,640,21,32,16,101,32,103,32,109,48,151,21,23,16,106,32,103,48,644,151,643,21,29,16,110,32,109,48,644],
[21,42,16,106,32,641,48,643,192,157,21,42,42,16,21,32,21,23,21,29,16,106,42,16,16,101,16,155,16,106,32,641,21,32,16,101,32,103,32,109,48,643,21,23,16,155,32,103,48,644,192,157,21,29,16,106,32,109,48,644],
[48,645,21,48,16,646,32,647,48,648,48,645,21,42,16,106,32,630,128,157,21,48,21,42,42,16,21,32,21,29,16,646,16,106,42,16,16,101,16,110,32,647,32,630,21,32,16,101,32,109,48,648,128,157,21,29,16,110,32,109],
[128,649,21,42,16,106,32,631,48,151,128,649,21,192,16,650,32,651,48,652,21,42,21,192,42,16,21,32,21,23,16,106,16,650,42,16,16,101,16,155,32,631,32,651,21,32,16,101,32,103,48,151,48,652,21,23,16,155,32,103],
[21,42,128,149,32,632,48,149,128,157,21,42,42,21,21,32,42,21,21,29,128,149,42,21,32,101,48,155,155,653,32,632,21,32,32,101,32,101,32,109,48,149,42,21,48,155,32,101,48,654,128,157,21,29,155,653,32,109,48,654],
[21,42,110,149,32,633,48,151,128,149,21,42,42,21,21,32,21,23,42,21,110,149,42,21,32,101,48,653,192,110,32,633,21,32,32,101,32,103,32,101,48,151,21,23,48,653,32,103,48,654,128,149,42,21,192,110,32,101,48,654],
[42,16,21,42,21,42,21,23,21,29,42,16,16,106,16,106,16,155,16,110,21,42,16,106,128,639,48,655,192,656,21,42,16,106,128,639,48,151,128,157,21,23,16,155,48,655,48,151,48,657,21,29,16,110,192,656,128,157,48,657],
[21,42,16,106,103,655,48,151,128,157,21,42,42,16,21,42,21,23,21,29,16,106,42,16,16,103,16,106,16,110,103,655,21,42,16,103,48,103,103,658,48,151,21,23,16,106,48,103,48,659,128,157,21,29,16,110,103,658,48,659],
[21,42,16,106,109,656,48,151,128,157,21,42,42,16,21,42,21,23,21,29,16,106,42,16,16,106,16,155,16,106,109,656,21,42,16,106,48,658,192,109,48,151,21,23,16,155,48,658,48,659,128,157,21,29,16,106,192,109,48,659],
[21,21,42,42,16,16,106,106,32,32,636,642,48,48,151,644,21,149,42,128,42,106,16,16,21,101,32,32,21,660,23,48,16,128,106,149,42,42,16,21,16,32,101,101,16,48,110,654,32,128,636,657,21,21,32,42,16,16,101,106,32,48,103,659,48,128,151,151,21,21,23,23,16,16,110,110,32,32,103,103],
[21,42,16,106,32,637,128,151,128,151,21,42,42,16,21,32,21,23,21,23,16,106,42,16,16,101,16,155,16,110,32,637,21,32,16,101,32,103,32,103,128,151,21,23,16,155,32,103,192,661,128,151,21,23,16,110,32,103,192,661],
[21,42,16,106,32,638,128,157,48,151,21,42,42,16,21,32,21,29,21,23,16,106,42,16,16,101,16,110,16,110,32,638,21,32,16,101,32,109,32,103,128,157,21,29,16,110,32,109,48,661,48,151,21,23,16,110,32,103,48,661],
[21,42,16,106,32,639,48,151,128,157,21,42,42,16,21,32,21,23,21,29,16,106,42,16,16,101,16,155,16,110,32,639,21,32,16,101,32,103,32,109,48,151,21,23,16,155,32,103,48,661,128,157,21,29,16,110,32,109,48,661]]

def tabmarkChunk12 : Array (List Nat) := #[[21,42,16,149,32,662,48,149,128,157,21,42,42,16,21,32,21,21,21,29,16,149,42,16,16,101,16,155,16,663,32,662,21,32,16,101,32,101,32,664,48,149,21,21,16,155,32,101,48,665,128,157,21,29,16,663,32,664,48,665],
[21,42,16,149,32,666,48,151,128,149,21,42,42,16,21,32,21,23,21,21,16,149,42,16,16,101,16,155,16,110,32,666,21,32,16,101,32,103,32,101,48,151,21,23,16,155,32,103,48,665,128,149,21,21,16,110,32,101,48,665],
[21,21,16,639,32,101,48,662,192,666,21,21,42,16,21,32,21,23,21,29,16,639,42,16,16,101,16,155,16,158,32,101,21,32,16,101,32,103,32,157,48,662,21,23,16,155,32,103,48,667,192,666,21,29,16,158,32,157,48,667],
[110,149,21,21,32,101,48,663,16,110,110,149,21,42,32,158,48,151,16,149,21,21,21,42,21,30,21,23,42,16,32,101,32,158,21,30,32,103,16,101,48,663,48,151,21,23,32,103,16,155,16,110,16,149,42,16,16,101,16,155],
[109,149,21,21,16,109,48,664,32,101,109,149,21,42,16,149,48,151,32,157,21,21,21,42,42,16,21,23,21,29,16,109,16,149,42,16,16,155,16,101,48,664,48,151,21,23,16,155,32,103,32,101,32,157,21,29,16,101,32,103],
[128,149,21,21,16,661,32,101,48,665,128,149,21,42,16,149,32,667,48,151,21,21,21,42,42,16,21,32,21,23,16,661,16,149,42,16,16,101,16,155,32,101,32,667,21,32,16,101,32,103,48,665,48,151,21,23,16,155,32,103],
[21,42,16,154,32,107,48,106,192,157,21,42,42,16,21,32,21,21,21,29,16,154,42,16,16,101,16,155,16,154,32,107,21,32,16,101,32,101,32,107,48,106,21,21,16,155,32,101,48,106,192,157,21,29,16,154,32,107,48,106],
[128,668,21,42,16,149,32,107,48,106,128,668,21,192,16,669,32,670,48,671,21,42,21,192,42,16,21,32,21,21,16,149,16,669,42,16,16,101,16,155,32,107,32,670,21,32,16,101,32,101,48,106,48,671,21,21,16,155,32,101],
[21,42,128,149,32,107,48,106,128,157,21,42,42,21,21,32,42,21,21,29,128,149,42,21,32,101,48,155,155,672,32,107,21,32,32,101,32,101,32,109,48,106,42,21,48,155,32,101,48,110,128,157,21,29,155,672,32,109,48,110],
[21,21,42,42,32,32,107,107,48,48,106,106,16,16,149,154,21,149,42,128,21,101,30,32,21,106,21,48,42,154,16,16,32,128,107,158,21,21,30,30,32,48,101,106,16,16,101,154,48,128,106,149,21,21,21,21,32,32,101,101,16,16,110,155,16,128,149,149,42,42,16,21,16,32,101,101,16,48,110,110],
[21,42,128,149,32,107,48,106,128,149,21,42,42,21,21,32,21,21,42,21,128,149,42,21,32,101,48,672,192,673,32,107,21,32,32,101,32,101,32,101,48,106,21,21,48,672,32,101,48,110,128,149,42,21,192,673,32,101,48,110],
[42,16,21,42,21,42,21,21,21,29,42,16,16,154,16,149,16,155,16,158,21,42,16,154,128,107,48,106,107,674,21,42,16,149,128,107,48,106,128,157,21,21,16,155,48,106,48,106,48,110,21,29,16,158,107,674,128,157,48,110],
[21,42,16,149,111,674,48,106,128,157,21,42,42,16,21,42,21,21,21,29,16,149,42,16,16,154,16,155,16,154,111,674,21,42,16,154,48,106,192,111,48,106,21,21,16,155,48,106,48,106,128,157,21,29,16,154,192,111,48,106],
[21,42,16,149,32,107,110,149,128,149,21,42,42,16,21,32,21,21,21,21,16,149,42,16,16,101,16,155,16,155,32,107,21,32,16,101,32,101,32,101,110,149,21,21,16,155,32,101,192,110,128,149,21,21,16,155,32,101,192,110],
[21,42,32,107,48,106,128,157,16,149,21,42,21,30,21,21,21,29,42,16,32,107,21,30,32,101,32,111,16,101,48,106,21,21,32,101,48,110,16,110,128,157,21,29,32,111,48,110,16,673,16,149,42,16,16,101,16,110,16,673],
[21,42,16,149,32,107,48,106,128,157,21,42,42,16,21,32,21,21,21,29,16,149,42,16,16,101,16,155,16,673,32,107,21,32,16,101,32,101,32,111,48,106,21,21,16,155,32,101,48,110,128,157,21,29,16,673,32,111,48,110]]

def tabmarkChunk13 : Array (List Nat) := #[[21,42,16,149,32,675,48,149,128,149,21,42,42,16,21,32,21,21,21,21,16,149,42,16,16,101,16,155,16,663,32,675,21,32,16,101,32,101,32,101,48,149,21,21,16,155,32,101,48,110,128,149,21,21,16,663,32,101,48,110],
[21,21,16,662,32,101,48,107,107,675,21,21,42,16,21,32,21,21,21,29,16,662,42,16,16,101,16,155,16,158,32,101,21,32,16,101,32,101,32,157,48,107,21,21,16,155,32,101,48,676,107,675,21,29,16,158,32,157,48,676],
[128,149,21,21,32,101,48,673,16,663,128,149,21,42,32,158,48,149,16,149,21,21,21,42,21,30,21,21,42,16,32,101,32,158,21,30,32,101,16,101,48,673,48,149,21,21,32,101,16,155,16,663,16,149,42,16,16,101,16,155],
[111,149,21,21,16,664,48,111,32,101,111,149,21,42,16,149,48,149,32,157,21,21,21,42,42,16,21,21,21,29,16,664,16,149,42,16,16,155,16,101,48,111,48,149,21,21,16,155,32,101,32,101,32,157,21,29,16,101,32,101],
[110,149,21,21,16,665,32,101,48,110,110,149,21,42,16,149,32,676,48,149,21,21,21,42,42,16,21,32,21,21,16,665,16,149,42,16,16,101,16,155,32,101,32,676,21,32,16,101,32,101,48,110,48,149,21,21,16,155,32,101],
[21,21,16,666,32,101,48,675,192,110,21,21,42,16,21,32,21,43,21,21,16,666,42,16,16,101,16,155,16,158,32,101,21,32,16,101,32,103,32,101,48,675,21,43,16,155,32,103,48,676,192,110,21,21,16,158,32,101,48,676],
[21,21,16,151,32,101,48,149,192,110,21,21,42,16,21,32,21,42,21,21,16,151,42,16,16,101,16,149,16,151,32,101,21,32,16,101,32,103,32,101,48,149,21,42,16,149,32,103,48,149,192,110,21,21,16,151,32,101,48,149],
[48,677,21,48,16,678,32,679,48,680,48,677,21,21,16,630,32,101,64,110,21,48,21,21,42,16,21,32,21,29,16,678,16,630,42,16,16,101,16,158,32,679,32,101,21,32,16,101,32,157,48,680,64,110,21,29,16,158,32,157],
[64,681,21,21,16,631,32,101,48,107,64,681,21,192,16,682,32,683,48,684,21,21,21,192,42,16,21,32,21,43,16,631,16,682,42,16,16,101,16,155,32,101,32,683,21,32,16,101,32,103,48,107,48,684,21,43,16,155,32,103],
[42,21,42,21,21,32,21,43,21,29,42,21,64,639,32,101,48,685,192,686,42,21,64,639,32,101,48,107,64,110,21,32,32,101,32,101,32,103,32,109,21,43,48,685,48,107,32,103,48,687,21,29,192,686,64,110,32,109,48,687],
[21,21,64,685,32,101,48,107,64,110,21,21,42,21,21,32,42,21,21,29,64,685,42,21,32,101,48,155,155,688,32,101,21,32,32,101,32,101,32,157,48,107,42,21,48,155,32,101,48,689,64,110,21,29,155,688,32,157,48,689],
[21,21,64,686,32,101,48,107,64,110,21,21,42,21,21,32,21,43,42,21,64,686,42,21,32,101,48,688,192,158,32,101,21,32,32,101,32,103,32,101,48,107,21,43,48,688,32,103,48,689,64,110,42,21,192,158,32,101,48,689],
[21,21,16,634,64,103,48,106,64,110,21,21,42,16,21,42,21,42,21,29,16,634,42,16,16,154,16,154,16,158,64,103,21,42,16,154,48,103,103,690,48,106,21,42,16,154,48,103,48,691,64,110,21,29,16,158,103,690,48,691],
[21,21,16,635,64,106,48,107,64,106,21,21,42,16,21,42,21,43,21,29,16,635,42,16,16,154,16,155,16,154,64,106,21,42,16,154,48,690,192,157,48,107,21,43,16,155,48,690,48,691,64,106,21,29,16,154,192,157,48,691],
[21,21,21,21,16,16,636,667,32,32,101,101,48,48,107,676,21,106,21,64,42,154,16,16,21,101,32,32,21,692,29,48,16,64,636,687,42,42,16,21,16,32,101,101,16,48,155,689,32,64,101,106,21,21,32,42,16,16,101,154,32,48,103,691,48,64,107,107,21,21,29,29,16,16,155,155,32,32,103,103],
[21,21,16,637,32,101,64,107,64,107,21,21,42,16,21,32,21,43,21,29,16,637,42,16,16,101,16,155,16,155,32,101,21,32,16,101,32,103,32,103,64,107,21,43,16,155,32,103,192,693,64,107,21,29,16,155,32,103,192,693]]

def tabmarkChunk14 : Array (List Nat) := #[[21,21,16,638,32,101,64,110,48,107,21,21,42,16,21,32,21,29,21,29,16,638,42,16,16,101,16,158,16,155,32,101,21,32,16,101,32,157,32,103,64,110,21,29,16,158,32,157,48,693,48,107,21,29,16,155,32,103,48,693],
[21,21,16,639,32,101,48,107,64,110,21,21,42,16,21,32,21,43,21,29,16,639,42,16,16,101,16,155,16,158,32,101,21,32,16,101,32,103,32,157,48,107,21,43,16,155,32,103,48,693,64,110,21,29,16,158,32,157,48,693],
[21,21,16,640,32,101,48,106,64,110,21,21,42,16,21,32,21,42,21,29,16,640,42,16,16,101,16,154,16,694,32,101,21,32,16,101,32,103,32,695,48,106,21,42,16,154,32,103,48,696,64,110,21,29,16,694,32,695,48,696],
[21,21,16,641,32,101,48,107,64,106,21,21,42,16,21,32,21,43,21,29,16,641,42,16,16,101,16,155,16,154,32,101,21,32,16,101,32,103,32,157,48,107,21,43,16,155,32,103,48,696,64,106,21,29,16,154,32,157,48,696],
[64,106,21,21,32,101,48,107,16,110,64,106,21,42,32,158,48,694,16,154,21,21,21,42,21,30,21,31,42,16,32,101,32,158,21,30,32,103,16,101,48,107,48,694,21,31,32,103,16,155,16,110,16,154,42,16,16,101,16,155],
[64,106,21,21,16,109,48,107,32,101,64,106,21,42,16,154,48,695,32,157,21,21,21,42,42,16,21,43,21,29,16,109,16,154,42,16,16,155,16,101,48,107,48,695,21,43,16,155,32,103,32,101,32,157,21,29,16,101,32,103],
[64,106,21,21,16,642,32,101,48,107,64,106,21,42,16,154,32,693,48,696,21,21,21,42,42,16,21,32,21,29,16,642,16,154,42,16,16,101,16,155,32,101,32,693,21,32,16,101,32,103,48,107,48,696,21,29,16,155,32,103],
[64,697,21,21,16,151,32,101,48,106,64,697,21,192,16,698,32,699,48,700,21,21,21,192,42,16,21,32,21,42,16,151,16,698,42,16,16,101,16,149,32,101,32,699,21,32,16,101,32,103,48,106,48,700,21,42,16,149,32,103],
[42,21,42,21,21,32,21,42,21,29,42,21,64,151,32,101,48,149,151,701,42,21,64,151,32,101,48,106,64,110,21,32,32,101,32,101,32,103,32,109,21,42,48,149,48,106,32,103,48,157,21,29,151,701,64,110,32,109,48,157],
[21,21,64,701,32,101,48,106,64,110,21,21,42,21,21,32,21,42,42,21,64,701,42,21,32,101,48,149,192,159,32,101,21,32,32,101,32,103,32,101,48,106,21,42,48,149,32,103,48,149,64,110,42,21,192,159,32,101,48,149],
[21,21,16,151,64,103,48,106,64,110,21,21,42,16,21,42,21,42,21,29,16,151,42,16,16,154,16,149,16,158,64,103,21,42,16,154,48,103,103,702,48,106,21,42,16,149,48,103,48,157,64,110,21,29,16,158,103,702,48,157],
[21,21,21,21,16,16,109,151,48,48,106,149,32,32,101,101,21,106,21,64,42,151,16,16,21,149,42,48,21,101,29,32,16,64,109,109,42,42,16,21,16,48,149,149,16,32,101,101,48,64,106,106,21,21,42,42,16,16,149,151,32,32,103,103,32,64,101,106,21,21,29,29,16,16,101,154,32,48,103,157],
[21,21,16,151,64,106,48,106,64,106,21,21,42,16,21,42,21,42,21,29,16,151,42,16,16,154,16,149,16,154,64,106,21,42,16,154,48,702,192,703,48,106,21,42,16,149,48,702,48,157,64,106,21,29,16,154,192,703,48,157],
[21,21,16,151,32,101,64,106,64,106,21,21,42,16,21,32,21,42,21,29,16,151,42,16,16,101,16,151,16,151,32,101,21,32,16,101,32,103,32,103,64,106,21,42,16,151,32,103,192,157,64,106,21,29,16,151,32,103,192,157],
[21,21,16,109,48,106,64,109,32,101,21,21,42,16,21,42,21,29,21,29,16,109,42,16,16,149,16,159,16,101,48,106,21,42,16,149,48,157,32,103,64,109,21,29,16,159,48,157,32,703,32,101,21,29,16,101,32,103,32,703],
[21,21,16,151,32,101,48,106,64,110,21,21,42,16,21,32,21,42,21,29,16,151,42,16,16,101,16,149,16,159,32,101,21,32,16,101,32,103,32,703,48,106,21,42,16,149,32,103,48,157,64,110,21,29,16,159,32,703,48,157]]

def tabmarkChunk15 : Array (List Nat) := #[[21,21,16,643,32,101,48,106,64,106,21,21,42,16,21,32,21,42,21,29,16,643,42,16,16,101,16,154,16,154,32,101,21,32,16,101,32,103,32,695,48,106,21,42,16,154,32,103,48,157,64,106,21,29,16,154,32,695,48,157],
[64,106,21,21,32,101,48,106,16,110,64,106,21,42,32,694,48,159,16,154,21,21,21,42,21,30,21,31,42,16,32,101,32,694,21,30,32,103,16,101,48,106,48,159,21,31,32,103,16,154,16,110,16,154,42,16,16,101,16,154],
[64,106,21,21,16,109,48,106,32,101,64,106,21,42,16,154,48,703,32,695,21,21,21,42,42,16,21,42,21,29,16,109,16,154,42,16,16,154,16,101,48,106,48,703,21,42,16,154,32,103,32,101,32,695,21,29,16,101,32,103],
[64,106,21,21,16,644,32,101,48,106,64,106,21,42,16,154,32,696,48,157,21,21,21,42,42,16,21,32,21,29,16,644,16,154,42,16,16,101,16,154,32,101,32,696,21,32,16,101,32,103,48,106,48,157,21,29,16,154,32,103],
[48,106,21,21,16,646,32,101,48,110,48,106,21,42,16,149,32,677,128,157,21,21,21,42,42,16,21,32,21,29,16,646,16,149,42,16,16,101,16,704,32,101,32,677,21,32,16,101,32,705,48,110,128,157,21,29,16,704,32,705],
[48,106,21,21,16,645,32,101,64,110,48,106,21,42,16,149,32,679,48,157,21,21,21,42,42,16,21,32,21,29,16,645,16,149,42,16,16,101,16,706,32,101,32,679,21,32,16,101,32,707,64,110,48,157,21,29,16,706,32,707],
[64,106,21,21,16,646,32,101,64,110,64,106,21,42,16,149,32,678,128,157,21,21,21,42,42,16,21,32,21,29,16,646,16,149,42,16,16,101,16,708,32,101,32,678,21,32,16,101,32,709,64,110,128,157,21,29,16,708,32,709],
[64,106,21,21,16,647,32,101,64,110,64,106,21,42,16,149,32,679,128,157,21,21,21,42,42,16,21,32,21,29,16,647,16,149,42,16,16,101,16,710,32,101,32,679,21,32,16,101,32,711,64,110,128,157,21,29,16,710,32,711],
[64,106,21,21,16,648,32,101,48,110,64,106,21,42,16,149,32,680,48,157,21,21,21,42,42,16,21,32,21,29,16,648,16,149,42,16,16,101,16,708,32,101,32,680,21,32,16,101,32,711,48,110,48,157,21,29,16,708,32,711],
[48,704,48,706,21,48,32,710,16,708,48,704,64,106,21,21,32,101,16,110,48,706,64,106,21,42,32,158,16,149,21,48,21,21,21,42,21,30,42,16,32,710,32,101,32,158,21,30,16,101,16,708,16,110,16,149,42,16,16,101],
[48,705,48,707,21,48,16,709,32,711,48,705,64,106,21,21,16,109,32,101,48,707,64,106,21,42,16,149,32,157,21,48,21,21,21,42,42,16,21,29,16,709,16,109,16,149,42,16,16,101,32,711,32,101,32,157,21,29,16,101],
[64,106,21,42,16,149,32,681,48,697,64,106,21,21,16,650,32,101,48,671,21,42,21,21,42,16,21,32,21,48,16,149,16,650,42,16,16,101,16,155,32,681,32,101,21,32,16,101,32,103,48,697,48,671,21,48,16,155,32,103],
[21,21,64,106,16,649,32,101,48,668,21,21,21,42,42,16,21,32,21,48,64,106,21,42,16,149,32,683,48,700,16,649,42,16,16,149,16,101,16,155,32,101,21,32,32,683,16,101,32,103,48,668,21,48,48,700,16,155,32,103],
[64,106,21,21,16,650,32,101,48,669,64,106,21,42,16,149,32,682,48,698,21,21,21,42,42,16,21,32,21,48,16,650,16,149,42,16,16,101,16,155,32,101,32,682,21,32,16,101,32,103,48,669,48,698,21,48,16,155,32,103],
[64,106,21,21,16,651,32,101,48,670,64,106,21,42,16,149,32,683,48,699,21,21,21,42,42,16,21,32,21,48,16,651,16,149,42,16,16,101,16,155,32,101,32,683,21,32,16,101,32,103,48,670,48,699,21,48,16,155,32,103],
[64,106,21,21,16,652,32,101,48,671,64,106,21,42,16,149,32,684,48,700,21,21,21,42,42,16,21,32,21,48,16,652,16,149,42,16,16,101,16,155,32,101,32,684,21,32,16,101,32,103,48,671,48,700,21,48,16,155,32,103]]

def tabmarkChunk16 : Array (List Nat) := #[[21,42,64,106,32,685,48,149,128,157,21,42,42,21,21,32,42,21,21,29,64,106,42,21,32,101,48,155,64,110,32,685,21,32,32,101,32,101,32,109,48,149,42,21,48,155,32,101,48,712,128,157,21,29,64,110,32,109,48,712],
[21,42,64,106,32,686,48,701,128,149,21,42,42,21,21,32,21,48,42,21,64,106,42,21,32,101,48,672,64,110,32,686,21,32,32,101,32,103,32,101,48,701,21,48,48,672,32,103,48,712,128,149,42,21,64,110,32,101,48,712],
[21,42,128,149,64,106,32,687,48,157,21,42,42,21,42,21,21,32,21,29,128,149,42,21,64,661,32,101,48,712,64,106,42,21,64,661,32,101,48,110,32,687,21,32,32,101,32,101,32,103,48,157,21,29,48,712,48,110,32,103],
[64,106,21,21,32,101,48,672,64,110,64,106,21,42,32,688,48,149,128,149,21,21,21,42,21,32,42,21,42,21,32,101,32,688,21,32,32,101,32,101,48,672,48,149,42,21,32,101,48,155,64,110,128,149,42,21,32,101,48,155],
[64,106,21,21,64,109,48,109,32,101,64,106,21,42,128,149,48,149,32,157,21,21,21,42,42,21,42,21,21,29,64,109,128,149,42,21,48,155,32,101,48,109,48,149,42,21,48,155,32,101,32,101,32,157,21,29,32,101,32,101],
[64,106,21,21,64,712,32,101,48,110,64,106,21,42,128,149,32,689,48,149,21,21,21,42,42,21,21,32,42,21,64,712,128,149,42,21,32,101,48,155,32,101,32,689,21,32,32,101,32,101,48,110,48,149,42,21,48,155,32,101],
[64,106,21,21,64,103,48,106,16,110,64,106,21,42,103,158,48,158,16,149,21,21,21,42,21,30,21,30,42,16,64,103,103,158,21,30,48,103,16,154,48,106,48,158,21,30,48,103,16,154,16,110,16,149,42,16,16,154,16,154],
[21,42,32,107,128,159,64,106,16,149,21,42,21,30,21,31,21,21,42,16,32,107,21,30,32,103,32,101,16,101,128,159,21,31,32,103,64,673,16,155,64,106,21,21,32,101,64,673,16,110,16,149,42,16,16,101,16,155,16,110],
[64,106,21,21,32,101,64,110,48,110,64,106,21,42,32,158,128,149,48,149,21,21,21,42,21,30,42,21,42,21,32,101,32,158,21,30,32,101,32,101,64,110,128,149,42,21,32,101,48,155,48,110,48,149,42,21,32,101,48,155],
[64,106,21,21,32,101,48,673,16,110,64,106,21,42,32,158,48,159,16,149,21,21,21,42,21,30,21,31,42,16,32,101,32,158,21,30,32,103,16,101,48,673,48,159,21,31,32,103,16,155,16,110,16,149,42,16,16,101,16,155],
[21,21,16,655,64,103,48,106,64,110,21,21,42,16,21,42,21,42,21,29,16,655,42,16,16,149,16,154,16,158,64,103,21,42,16,149,48,103,103,157,48,106,21,42,16,154,48,103,48,713,64,110,21,29,16,158,103,157,48,713],
[21,21,16,656,64,106,48,674,64,106,21,21,42,16,21,42,21,48,21,29,16,656,42,16,16,149,16,155,16,154,64,106,21,42,16,149,48,702,128,157,48,674,21,48,16,155,48,702,48,713,64,106,21,29,16,154,128,157,48,713],
[21,21,16,657,64,106,64,106,48,110,21,21,42,16,21,42,21,42,21,29,16,657,42,16,16,154,16,149,16,155,64,106,21,42,16,154,128,693,48,713,64,106,21,42,16,149,128,693,48,157,48,110,21,29,16,155,48,713,48,157],
[64,106,21,21,16,658,48,106,64,103,64,106,21,42,16,149,48,702,103,157,21,21,21,42,42,16,21,42,21,29,16,658,16,149,42,16,16,154,16,154,48,106,48,702,21,42,16,154,48,103,64,103,103,157,21,29,16,154,48,103],
[64,106,21,21,16,659,64,103,48,106,64,106,21,42,16,149,103,713,48,157,21,21,21,42,42,16,21,42,21,29,16,659,16,149,42,16,16,154,16,154,64,103,103,713,21,42,16,154,48,103,48,106,48,157,21,29,16,154,48,103],
[21,21,16,109,64,111,64,106,32,101,21,21,42,16,21,47,21,42,21,29,16,109,42,16,16,151,16,149,16,101,64,111,21,47,16,151,128,703,32,103,64,106,21,42,16,149,128,703,32,103,32,101,21,29,16,101,32,103,32,103]]

def tabmarkChunk17 : Array (List Nat) := #[[64,106,21,21,16,109,64,103,48,106,64,106,21,42,16,149,103,157,48,157,21,21,21,42,42,16,21,29,21,29,16,109,16,149,42,16,16,154,16,154,64,103,103,157,21,29,16,154,48,103,48,106,48,157,21,29,16,154,48,103],
[64,106,21,21,16,109,48,111,32,101,64,106,21,42,16,149,48,703,32,157,21,21,21,42,42,16,21,47,21,29,16,109,16,149,42,16,16,155,16,101,48,111,48,703,21,47,16,155,32,103,32,101,32,157,21,29,16,101,32,103],
[42,16,21,32,21,21,21,42,21,29,42,16,16,101,16,151,16,149,16,159,21,32,16,101,32,101,32,103,32,111,21,21,16,151,32,101,64,106,64,110,21,42,16,149,32,103,64,106,128,157,21,29,16,159,32,111,64,110,128,157],
[21,42,16,149,32,107,64,106,128,157,21,42,42,16,21,32,21,21,21,29,16,149,42,16,16,101,16,155,16,155,32,107,21,32,16,101,32,101,32,103,64,106,21,21,16,155,32,101,64,110,128,157,21,29,16,155,32,103,64,110],
[21,21,16,151,32,101,64,106,64,110,21,21,42,16,21,32,21,42,21,29,16,151,42,16,16,101,16,149,16,151,32,101,21,32,16,101,32,103,32,103,64,106,21,42,16,149,32,103,128,157,64,110,21,29,16,151,32,103,128,157],
[64,106,48,714,21,21,16,660,32,101,64,106,48,715,21,42,16,149,32,692,48,714,48,715,21,48,16,716,32,717,21,21,21,42,21,48,42,16,21,32,16,660,16,149,16,716,42,16,16,101,32,101,32,692,32,717,21,32,16,101],
[64,106,21,21,16,661,32,101,48,110,64,106,21,42,16,149,32,693,48,157,21,21,21,42,42,16,21,32,21,29,16,661,16,149,42,16,16,101,16,155,32,101,32,693,21,32,16,101,32,103,48,110,48,157,21,29,16,155,32,103],
[64,106,21,21,48,111,16,109,32,101,64,106,21,42,48,159,16,149,32,157,21,21,21,42,21,31,42,16,21,29,48,111,48,159,21,31,16,155,32,103,16,109,16,149,42,16,16,155,16,101,32,101,32,157,21,29,32,103,16,101],
[64,106,21,21,32,101,16,110,48,110,64,106,21,42,32,158,16,149,48,157,21,21,21,42,21,30,42,16,21,29,32,101,32,158,21,30,16,101,32,103,16,110,16,149,42,16,16,101,16,155,48,110,48,157,21,29,32,103,16,155],
[64,106,21,21,16,109,32,101,48,109,64,106,21,42,16,149,32,157,48,157,21,21,21,42,42,16,21,29,21,29,16,109,16,149,42,16,16,101,16,155,32,101,32,157,21,29,16,101,32,103,48,109,48,157,21,29,16,155,32,103],
[69,639,64,16,101,32,630,48,192,192,69,639,106,16,69,32,69,48,69,77,64,16,106,16,16,101,16,107,16,110,101,32,69,32,16,101,32,103,32,109,630,48,69,48,16,107,32,103,48,718,192,192,69,77,16,110,32,109,48,718],
[128,128,69,661,64,16,101,32,192,48,128,128,69,128,16,106,32,718,48,151,69,661,69,128,106,16,69,32,69,48,64,16,16,106,106,16,16,101,16,110,101,32,32,718,69,32,16,101,32,103,192,48,48,151,69,48,16,110,32,103],
[128,128,69,673,101,32,64,48,154,16,128,128,69,75,32,107,48,106,16,149,69,673,69,75,69,32,106,48,69,16,101,32,32,107,69,32,32,101,16,101,64,48,48,106,106,48,32,101,16,110,154,16,16,149,69,16,16,101,16,110],
[64,64,69,693,154,16,101,32,192,48,64,64,106,64,16,718,32,101,48,107,69,693,106,64,69,16,69,32,69,48,154,16,16,718,69,16,16,101,16,155,101,32,32,101,69,32,16,101,32,103,192,48,48,107,69,48,16,155,32,103],
[64,64,69,703,151,16,128,48,101,32,64,64,106,64,16,109,48,106,32,101,69,703,106,64,69,16,69,48,69,32,151,16,16,109,69,16,16,149,16,101,128,48,48,106,69,48,16,149,32,103,101,32,32,101,69,32,16,101,32,103],
[21,42,21,646,42,16,21,32,21,29,21,42,69,128,16,106,32,719,128,157,21,646,69,128,16,16,32,32,69,77,42,16,16,106,16,16,16,101,16,110,21,32,32,719,32,32,16,101,32,109,21,29,128,157,69,77,16,110,32,109]]

def tabmarkChunk18 : Array (List Nat) := #[[21,21,21,677,42,16,21,32,21,29,21,21,48,48,16,719,32,101,48,110,21,677,48,48,16,16,32,32,69,142,42,16,16,719,16,16,16,101,16,158,21,32,32,101,32,32,16,101,32,157,21,29,48,110,69,142,16,158,32,157],
[21,21,21,42,21,704,21,30,42,16,21,21,48,106,48,48,32,101,16,110,21,42,48,106,69,128,32,158,16,149,21,704,48,48,69,128,32,32,16,16,21,30,32,101,32,158,32,32,16,101,42,16,16,110,16,149,16,16,16,101],
[21,21,21,42,21,705,42,16,21,29,21,21,48,106,48,48,16,109,32,101,21,42,48,106,69,128,16,149,32,157,21,705,48,48,69,128,16,16,32,32,42,16,16,109,16,149,16,16,16,101,21,29,32,101,32,157,32,32,16,101],
[21,42,21,645,42,16,21,32,21,29,21,42,48,48,16,106,32,720,48,157,21,645,48,48,16,16,32,32,69,77,42,16,16,106,16,16,16,101,16,110,21,32,32,720,32,32,16,101,32,109,21,29,48,157,69,77,16,110,32,109],
[21,21,21,679,42,16,21,32,21,29,21,21,106,64,16,720,32,101,64,110,21,679,106,64,16,16,32,32,69,142,42,16,16,720,16,16,16,101,16,158,21,32,32,101,32,32,16,101,32,157,21,29,64,110,69,142,16,158,32,157],
[21,21,21,42,21,706,21,30,42,16,21,21,48,106,106,64,32,101,16,110,21,42,48,106,48,48,32,158,16,149,21,706,106,64,48,48,32,32,16,16,21,30,32,101,32,158,32,32,16,101,42,16,16,110,16,149,16,16,16,101],
[21,21,21,42,21,707,42,16,21,29,21,21,48,106,106,64,16,109,32,101,21,42,48,106,48,48,16,149,32,157,21,707,106,64,48,48,16,16,32,32,42,16,16,109,16,149,16,16,16,101,21,29,32,101,32,157,32,32,16,101],
[21,21,21,678,42,16,21,32,21,29,21,21,106,64,16,719,32,101,64,110,21,678,106,64,16,16,32,32,69,142,42,16,16,719,16,16,16,101,16,158,21,32,32,101,32,32,16,101,32,157,21,29,64,110,69,142,16,158,32,157],
[21,21,21,42,21,708,21,30,42,16,21,21,64,106,106,64,32,101,16,110,21,42,64,106,69,128,32,158,16,149,21,708,106,64,69,128,32,32,16,16,21,30,32,101,32,158,32,32,16,101,42,16,16,110,16,149,16,16,16,101],
[21,21,21,42,21,709,42,16,21,29,21,21,64,106,106,64,16,109,32,101,21,42,64,106,69,128,16,149,32,157,21,709,106,64,69,128,16,16,32,32,42,16,16,109,16,149,16,16,16,101,21,29,32,101,32,157,32,32,16,101],
[21,42,21,647,42,16,21,32,21,29,21,42,69,128,16,106,32,720,128,157,21,647,69,128,16,16,32,32,69,77,42,16,16,106,16,16,16,101,16,110,21,32,32,720,32,32,16,101,32,109,21,29,128,157,69,77,16,110,32,109],
[21,21,21,42,21,710,21,30,42,16,21,21,64,106,106,64,32,101,16,110,21,42,64,106,69,128,32,158,16,149,21,710,106,64,69,128,32,32,16,16,21,30,32,101,32,158,32,32,16,101,42,16,16,110,16,149,16,16,16,101],
[21,21,21,42,21,711,42,16,21,29,21,21,64,106,106,64,16,109,32,101,21,42,64,106,69,128,16,149,32,157,21,711,106,64,69,128,16,16,32,32,42,16,16,109,16,149,16,16,16,101,21,29,32,101,32,157,32,32,16,101],
[21,42,21,648,42,16,21,32,21,29,21,42,69,128,16,106,32,721,48,157,21,648,69,128,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,110,21,32,32,721,32,32,16,101,32,109,21,29,48,157,48,48,16,110,32,109],
[21,21,21,680,42,16,21,32,21,29,21,21,106,64,16,721,32,101,48,110,21,680,106,64,16,16,32,32,48,48,42,16,16,721,16,16,16,101,16,158,21,32,32,101,32,32,16,101,32,157,21,29,48,110,48,48,16,158,32,157],
[21,48,48,48,16,719,32,720,48,721,21,48,21,630,42,16,21,32,21,29,48,48,21,630,16,16,32,32,69,77,16,719,42,16,16,16,16,101,16,110,32,720,21,32,32,32,16,101,32,109,48,721,21,29,69,77,16,110,32,109]]

def tabmarkChunk19 : Array (List Nat) := #[[21,639,16,16,32,32,48,48,631,192,21,639,42,16,21,32,21,23,21,29,16,16,42,16,16,101,16,107,16,110,32,32,21,32,16,101,32,103,32,109,48,48,21,23,16,107,32,103,48,722,631,192,21,29,16,110,32,109,48,722],
[21,192,21,631,42,16,21,32,21,23,21,192,69,192,16,723,32,724,48,725,21,631,69,192,16,16,32,32,48,48,42,16,16,723,16,16,16,101,16,107,21,32,32,724,32,32,16,101,32,103,21,23,48,725,48,48,16,107,32,103],
[21,632,42,21,21,32,42,21,21,29,21,632,107,69,32,32,48,48,69,77,42,21,107,69,32,101,48,107,107,726,21,32,32,32,32,101,32,101,32,109,42,21,48,48,48,107,32,101,48,727,21,29,69,77,107,726,32,109,48,727],
[21,633,42,21,21,32,21,23,42,21,21,633,110,69,32,32,48,48,138,69,42,21,110,69,32,101,48,726,192,110,21,32,32,32,32,101,32,103,32,101,21,23,48,48,48,726,32,103,48,727,42,21,138,69,192,110,32,101,48,727],
[21,634,42,16,21,42,21,23,21,29,21,634,16,16,69,138,48,48,69,77,42,16,16,16,16,103,16,106,16,110,21,42,69,138,16,103,48,103,103,728,21,23,48,48,16,106,48,103,48,729,21,29,69,77,16,110,103,728,48,729],
[21,635,42,16,21,42,21,23,21,29,21,635,16,16,69,138,48,48,69,77,42,16,16,16,16,106,16,107,16,106,21,42,69,138,16,106,48,728,192,109,21,23,48,48,16,107,48,728,48,729,21,29,69,77,16,106,192,109,48,729],
[21,69,636,718,42,64,16,16,21,101,32,32,21,192,23,48,21,21,636,722,16,16,16,16,32,32,32,32,48,48,48,48,42,42,16,21,16,138,16,69,16,32,101,101,16,48,107,727,21,21,32,42,32,69,32,138,16,16,101,106,32,48,103,729,21,21,23,23,48,69,48,71,16,16,107,107,32,32,103,103],
[21,637,42,16,21,32,21,23,21,23,21,637,16,16,32,32,69,71,69,71,42,16,16,16,16,101,16,107,16,107,21,32,32,32,16,101,32,103,32,103,21,23,69,71,16,107,32,103,192,730,21,23,69,71,16,107,32,103,192,730],
[21,638,42,16,21,32,21,29,21,23,21,638,16,16,32,32,69,77,48,48,42,16,16,16,16,101,16,110,16,107,21,32,32,32,16,101,32,109,32,103,21,29,69,77,16,110,32,109,48,730,21,23,48,48,16,107,32,103,48,730],
[21,639,42,16,21,32,21,23,21,29,21,639,16,16,32,32,48,48,69,77,42,16,16,16,16,101,16,107,16,110,21,32,32,32,16,101,32,103,32,109,21,23,48,48,16,107,32,103,48,730,21,29,69,77,16,110,32,109,48,730],
[21,640,42,16,21,32,21,23,21,29,21,640,16,16,32,32,48,48,69,77,42,16,16,16,16,101,16,106,16,110,21,32,32,32,16,101,32,103,32,109,21,23,48,48,16,106,32,103,48,731,21,29,69,77,16,110,32,109,48,731],
[21,641,42,16,21,32,21,23,21,29,21,641,16,16,32,32,48,48,69,77,42,16,16,16,16,101,16,107,16,106,21,32,32,32,16,101,32,103,32,109,21,23,48,48,16,107,32,103,48,731,21,29,69,77,16,106,32,109,48,731],
[21,42,21,642,42,16,21,32,21,23,21,42,69,138,16,106,32,730,48,731,21,642,69,138,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,107,21,32,32,730,32,32,16,101,32,103,21,23,48,731,48,48,16,107,32,103],
[21,643,42,16,21,32,21,23,21,29,21,643,16,16,32,32,48,48,69,77,42,16,16,16,16,101,16,106,16,106,21,32,32,32,16,101,32,103,32,109,21,23,48,48,16,106,32,103,48,151,21,29,69,77,16,106,32,109,48,151],
[21,42,21,644,42,16,21,32,21,23,21,42,69,138,16,106,32,731,48,151,21,644,69,138,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,106,21,32,32,731,32,32,16,101,32,103,21,23,48,151,48,48,16,106,32,103],
[149,128,21,42,16,106,32,722,48,151,149,128,21,661,16,16,32,32,48,48,21,42,21,661,42,16,21,32,21,23,16,106,16,16,42,16,16,101,16,110,32,722,32,32,21,32,16,101,32,103,48,151,48,48,21,23,16,110,32,103]]

def tabmarkChunk20 : Array (List Nat) := #[[21,649,21,42,42,16,21,32,21,23,21,649,69,128,16,16,32,32,48,48,21,42,69,128,16,106,32,724,48,151,42,16,16,16,16,106,16,101,16,155,21,32,32,32,32,724,16,101,32,103,21,23,48,48,48,151,16,155,32,103],
[21,42,21,650,42,16,21,32,21,23,21,42,69,128,16,106,32,723,48,151,21,650,69,128,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,155,21,32,32,723,32,32,16,101,32,103,21,23,48,151,48,48,16,155,32,103],
[21,42,21,651,42,16,21,32,21,23,21,42,69,128,16,106,32,724,48,151,21,651,69,128,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,155,21,32,32,724,32,32,16,101,32,103,21,23,48,151,48,48,16,155,32,103],
[21,42,21,652,42,16,21,32,21,23,21,42,69,128,16,106,32,725,48,151,21,652,69,128,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,155,21,32,32,725,32,32,16,101,32,103,21,23,48,151,48,48,16,155,32,103],
[21,42,21,653,21,32,42,21,42,21,21,42,69,128,32,726,48,149,128,149,21,653,69,128,32,32,48,48,138,69,21,32,32,726,32,32,32,101,32,101,42,21,48,149,48,48,32,101,48,110,42,21,128,149,138,69,32,101,48,110],
[21,42,21,654,42,21,21,32,42,21,21,42,69,128,110,149,32,727,48,149,21,654,69,128,110,69,32,32,48,48,42,21,110,149,110,69,32,101,48,110,21,32,32,727,32,32,32,101,32,101,42,21,48,149,48,48,48,110,32,101],
[21,655,42,16,21,42,21,23,21,29,21,655,16,16,69,128,48,48,69,77,42,16,16,16,16,103,16,106,16,110,21,42,69,128,16,103,48,103,103,157,21,23,48,48,16,106,48,103,48,732,21,29,69,77,16,110,103,157,48,732],
[21,656,42,16,21,42,21,23,21,29,21,656,16,16,69,128,48,48,69,77,42,16,16,16,16,106,16,155,16,106,21,42,69,128,16,106,48,151,128,109,21,23,48,48,16,155,48,151,48,732,21,29,69,77,16,106,128,109,48,732],
[21,657,42,16,21,42,21,42,21,23,21,657,16,16,69,138,69,128,48,48,42,16,16,16,16,106,16,106,16,110,21,42,69,138,16,106,128,730,48,732,21,42,69,128,16,106,128,730,48,151,21,23,48,48,16,110,48,732,48,151],
[21,42,21,658,42,16,21,23,21,29,21,42,69,128,16,106,48,151,103,157,21,658,69,128,16,16,48,48,69,77,42,16,16,106,16,16,16,106,16,103,21,23,48,151,48,48,16,106,48,103,21,29,103,157,69,77,16,103,48,103],
[21,42,21,659,42,16,21,42,21,23,21,42,69,128,16,106,103,732,48,151,21,659,69,128,16,16,69,138,48,48,42,16,16,106,16,16,16,103,16,106,21,42,103,732,69,138,16,103,48,103,21,23,48,151,48,48,16,106,48,103],
[21,42,21,661,42,16,21,32,21,23,21,42,69,128,16,106,32,730,48,151,21,661,69,128,16,16,32,32,48,48,42,16,16,106,16,16,16,101,16,110,21,32,32,730,32,32,16,101,32,103,21,23,48,151,48,48,16,110,32,103],
[21,662,42,16,21,32,21,21,21,29,21,662,16,16,32,32,48,48,69,142,42,16,16,16,16,101,16,107,16,158,21,32,32,32,16,101,32,101,32,157,21,21,48,48,16,107,32,101,48,733,21,29,69,142,16,158,32,157,48,733],
[21,42,21,663,21,30,21,21,42,16,21,42,69,128,32,158,48,149,16,149,21,663,69,128,32,32,48,48,16,16,21,30,32,158,32,32,32,101,16,101,21,21,48,149,48,48,32,101,16,110,42,16,16,149,16,16,16,101,16,110],
[21,42,21,664,42,16,21,21,21,29,21,42,69,128,16,149,48,149,32,157,21,664,69,128,16,16,48,48,32,32,42,16,16,149,16,16,16,109,16,101,21,21,48,149,48,48,16,109,32,101,21,29,32,157,32,32,16,101,32,101],
[21,42,21,665,42,16,21,32,21,21,21,42,69,128,16,149,32,733,48,149,21,665,69,128,16,16,32,32,48,48,42,16,16,149,16,16,16,101,16,110,21,32,32,733,32,32,16,101,32,101,21,21,48,149,48,48,16,110,32,101]]

def tabmarkChunk21 : Array (List Nat) := #[[21,666,42,16,21,32,21,23,21,21,21,666,16,16,32,32,48,48,138,69,42,16,16,16,16,101,16,155,16,110,21,32,32,32,16,101,32,103,32,101,21,23,48,48,16,155,32,103,48,733,21,21,138,69,16,110,32,101,48,733],
[21,21,21,667,42,16,21,32,21,23,21,21,138,69,16,730,32,101,48,733,21,667,138,69,16,16,32,32,48,48,42,16,16,730,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,23,48,733,48,48,16,155,32,103],
[149,128,21,42,32,107,48,106,16,149,149,128,21,673,32,32,48,48,16,16,21,42,21,673,21,30,21,21,42,16,32,107,32,32,21,30,32,101,16,101,48,106,48,48,21,21,32,101,16,110,16,149,16,16,42,16,16,101,16,110],
[21,668,21,42,42,16,21,32,21,21,21,668,69,75,16,16,32,32,48,48,21,42,69,75,16,149,32,107,48,106,42,16,16,16,16,149,16,101,16,155,21,32,32,32,32,107,16,101,32,101,21,21,48,48,48,106,16,155,32,101],
[21,42,21,669,42,16,21,32,21,21,21,42,69,75,16,149,32,107,48,106,21,669,69,75,16,16,32,32,48,48,42,16,16,149,16,16,16,101,16,155,21,32,32,107,32,32,16,101,32,101,21,21,48,106,48,48,16,155,32,101],
[21,42,21,670,42,16,21,32,21,21,21,42,69,75,16,149,32,107,48,106,21,670,69,75,16,16,32,32,48,48,42,16,16,149,16,16,16,101,16,155,21,32,32,107,32,32,16,101,32,101,21,21,48,106,48,48,16,155,32,101],
[21,42,21,671,42,16,21,32,21,21,21,42,69,75,16,149,32,107,48,106,21,671,69,75,16,16,32,32,48,48,42,16,16,149,16,16,16,101,16,155,21,32,32,107,32,32,16,101,32,101,21,21,48,106,48,48,16,155,32,101],
[21,42,21,672,21,32,42,21,42,21,21,42,69,75,32,107,48,106,128,149,21,672,69,75,32,32,48,48,69,69,21,32,32,107,32,32,32,101,32,101,42,21,48,106,48,48,32,101,48,110,42,21,128,149,69,69,32,101,48,110],
[21,42,21,673,21,30,21,21,42,16,21,42,69,75,32,107,48,106,16,149,21,673,69,75,32,32,48,48,16,16,21,30,32,107,32,32,32,101,16,101,21,21,48,106,48,48,32,101,16,110,42,16,16,149,16,16,16,101,16,110],
[21,674,42,16,21,42,21,21,21,29,21,674,16,16,69,75,48,48,69,79,42,16,16,16,16,149,16,155,16,154,21,42,69,75,16,149,48,106,128,107,21,21,48,48,16,155,48,106,48,106,21,29,69,79,16,154,128,107,48,106],
[21,675,42,16,21,32,21,21,21,21,21,675,16,16,32,32,48,48,107,69,42,16,16,16,16,101,16,155,16,158,21,32,32,32,16,101,32,101,32,101,21,21,48,48,16,155,32,101,48,107,21,21,107,69,16,158,32,101,48,107],
[21,21,21,676,42,16,21,32,21,21,21,21,107,69,16,733,32,101,48,107,21,676,107,69,16,16,32,32,48,48,42,16,16,733,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,101,21,21,48,107,48,48,16,155,32,101],
[106,64,21,21,16,722,32,101,48,107,106,64,21,693,16,16,32,32,48,48,21,21,21,693,42,16,21,32,21,29,16,722,16,16,42,16,16,101,16,155,32,101,32,32,21,32,16,101,32,103,48,107,48,48,21,29,16,155,32,103],
[21,21,21,681,42,16,21,32,21,43,21,21,106,64,16,723,32,101,48,107,21,681,106,64,16,16,32,32,48,48,42,16,16,723,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,43,48,107,48,48,16,155,32,103],
[21,21,21,682,42,16,21,32,21,43,21,21,106,64,16,723,32,101,48,107,21,682,106,64,16,16,32,32,48,48,42,16,16,723,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,43,48,107,48,48,16,155,32,103],
[21,21,21,683,42,16,21,32,21,43,21,21,106,64,16,724,32,101,48,107,21,683,106,64,16,16,32,32,48,48,42,16,16,724,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,43,48,107,48,48,16,155,32,103]]

def tabmarkChunk22 : Array (List Nat) := #[[21,21,21,684,42,16,21,32,21,43,21,21,106,64,16,725,32,101,48,107,21,684,106,64,16,16,32,32,48,48,42,16,16,725,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,43,48,107,48,48,16,155,32,103],
[21,685,42,21,21,32,42,21,21,29,21,685,106,64,32,32,48,48,69,77,42,21,106,64,32,101,48,107,64,110,21,32,32,32,32,101,32,101,32,109,42,21,48,48,48,107,32,101,48,734,21,29,69,77,64,110,32,109,48,734],
[21,686,42,21,21,32,21,43,42,21,21,686,106,64,32,32,48,48,69,69,42,21,106,64,32,101,48,107,64,110,21,32,32,32,32,101,32,103,32,101,21,43,48,48,48,107,32,103,48,734,42,21,69,69,64,110,32,101,48,734],
[21,687,42,21,42,21,21,32,21,29,21,687,69,69,106,64,32,32,48,48,42,21,69,69,64,730,32,101,48,734,42,21,106,64,64,730,32,101,48,107,21,32,32,32,32,101,32,101,32,103,21,29,48,48,48,734,48,107,32,103],
[21,21,21,688,21,32,42,21,42,21,21,21,106,64,32,101,48,107,64,110,21,688,106,64,32,32,48,48,69,69,21,32,32,101,32,32,32,101,32,101,42,21,48,107,48,48,32,101,48,155,42,21,64,110,69,69,32,101,48,155],
[21,21,21,689,42,21,21,32,42,21,21,21,106,64,64,734,32,101,48,107,21,689,106,64,69,69,32,32,48,48,42,21,64,734,69,69,32,101,48,155,21,32,32,101,32,32,32,101,32,101,42,21,48,107,48,48,48,155,32,101],
[21,21,21,690,42,16,21,42,21,29,21,21,106,64,16,728,48,106,64,103,21,690,106,64,16,16,48,48,69,138,42,16,16,728,16,16,16,154,16,154,21,42,48,106,48,48,16,154,48,103,21,29,64,103,69,138,16,154,48,103],
[21,21,21,691,42,16,21,42,21,29,21,21,106,64,16,729,64,103,48,106,21,691,106,64,16,16,69,138,48,48,42,16,16,729,16,16,16,154,16,154,21,42,64,103,69,138,16,154,48,103,21,29,48,106,48,48,16,154,48,103],
[21,21,21,693,42,16,21,32,21,29,21,21,106,64,16,730,32,101,48,107,21,693,106,64,16,16,32,32,48,48,42,16,16,730,16,16,16,101,16,155,21,32,32,101,32,32,16,101,32,103,21,29,48,107,48,48,16,155,32,103],
[21,21,21,694,21,30,21,31,42,16,21,21,106,64,32,101,48,106,16,110,21,694,106,64,32,32,48,48,16,16,21,30,32,101,32,32,32,103,16,101,21,31,48,106,48,48,32,103,16,154,42,16,16,110,16,16,16,101,16,154],
[21,21,21,695,42,16,21,42,21,29,21,21,106,64,16,109,48,106,32,101,21,695,106,64,16,16,48,48,32,32,42,16,16,109,16,16,16,154,16,101,21,42,48,106,48,48,16,154,32,103,21,29,32,101,32,32,16,101,32,103],
[21,21,21,696,42,16,21,32,21,29,21,21,106,64,16,731,32,101,48,106,21,696,106,64,16,16,32,32,48,48,42,16,16,731,16,16,16,101,16,154,21,32,32,101,32,32,16,101,32,103,21,29,48,106,48,48,16,154,32,103],
[106,64,21,21,16,109,48,106,32,101,106,64,21,703,16,16,48,48,32,32,21,21,21,703,42,16,21,42,21,29,16,109,16,16,42,16,16,149,16,101,48,106,48,48,21,42,16,149,32,103,32,101,32,32,21,29,16,101,32,103],
[21,21,21,697,42,16,21,32,21,42,21,21,106,64,16,151,32,101,48,106,21,697,106,64,16,16,32,32,48,48,42,16,16,151,16,16,16,101,16,149,21,32,32,101,32,32,16,101,32,103,21,42,48,106,48,48,16,149,32,103],
[21,21,21,698,42,16,21,32,21,42,21,21,106,64,16,151,32,101,48,106,21,698,106,64,16,16,32,32,48,48,42,16,16,151,16,16,16,101,16,149,21,32,32,101,32,32,16,101,32,103,21,42,48,106,48,48,16,149,32,103],
[21,21,21,699,42,16,21,32,21,42,21,21,106,64,16,151,32,101,48,106,21,699,106,64,16,16,32,32,48,48,42,16,16,151,16,16,16,101,16,149,21,32,32,101,32,32,16,101,32,103,21,42,48,106,48,48,16,149,32,103]]

def tabmarkChunk23 : Array (List Nat) := #[[21,21,21,700,42,16,21,32,21,42,21,21,106,64,16,151,32,101,48,106,21,700,106,64,16,16,32,32,48,48,42,16,16,151,16,16,16,101,16,149,21,32,32,101,32,32,16,101,32,103,21,42,48,106,48,48,16,149,32,103],
[21,701,42,21,21,32,21,42,42,21,21,701,106,64,32,32,48,48,69,69,42,21,106,64,32,101,48,106,64,110,21,32,32,32,32,101,32,103,32,101,21,42,48,48,48,106,32,103,48,149,42,21,69,69,64,110,32,101,48,149],
[21,21,21,702,42,16,21,42,21,29,21,21,106,64,16,151,48,106,64,103,21,702,106,64,16,16,48,48,69,138,42,16,16,151,16,16,16,149,16,154,21,42,48,106,48,48,16,149,48,103,21,29,64,103,69,138,16,154,48,103],
[21,21,21,703,42,16,21,42,21,29,21,21,106,64,16,109,48,106,32,101,21,703,106,64,16,16,48,48,32,32,42,16,16,109,16,16,16,149,16,101,21,42,48,106,48,48,16,149,32,103,21,29,32,101,32,32,16,101,32,103],
[21,42,21,712,42,21,21,32,42,21,21,42,69,128,64,106,32,734,48,149,21,712,69,128,106,64,32,32,48,48,42,21,64,106,106,64,32,101,48,110,21,32,32,734,32,32,32,101,32,101,42,21,48,149,48,48,48,110,32,101],
[21,21,21,713,42,16,21,42,21,29,21,21,106,64,16,732,64,103,48,106,21,713,106,64,16,16,69,128,48,48,42,16,16,732,16,16,16,149,16,154,21,42,64,103,69,128,16,149,48,103,21,29,48,106,48,48,16,154,48,103],
[21,48,16,735,32,736,48,737,21,48,42,16,21,32,21,29,16,735,42,16,16,101,16,110,32,736,21,32,16,101,32,109,48,737,21,29,16,110,32,109],
[21,192,16,738,32,739,48,740,21,192,42,16,21,32,21,23,16,738,42,16,16,101,16,107,32,739,21,32,16,101,32,103,48,740,21,23,16,107,32,103],
[42,21,21,32,42,21,21,29,42,21,32,101,48,107,107,741,21,32,32,101,32,101,32,109,42,21,48,107,32,101,48,742,21,29,107,741,32,109,48,742],
[42,21,21,32,21,23,42,21,42,21,32,101,48,741,192,110,21,32,32,101,32,103,32,101,21,23,48,741,32,103,48,742,42,21,192,110,32,101,48,742],
[42,16,21,42,21,23,21,29,42,16,16,103,16,106,16,110,21,42,16,103,48,103,103,743,21,23,16,106,48,103,48,744,21,29,16,110,103,743,48,744],
[42,16,21,42,21,23,21,29,42,16,16,106,16,107,16,106,21,42,16,106,48,743,192,109,21,23,16,107,48,743,48,744,21,29,16,106,192,109,48,744],
[42,106,16,16,21,101,32,32,21,745,23,48,42,42,16,21,16,32,101,101,16,48,107,742,21,21,32,42,16,16,101,106,32,48,103,744,21,21,23,23,16,16,107,107,32,32,103,103],
[42,16,21,32,21,23,21,23,42,16,16,101,16,107,16,107,21,32,16,101,32,103,32,103,21,23,16,107,32,103,192,746,21,23,16,107,32,103,192,746],
[42,16,21,32,21,29,21,23,42,16,16,101,16,110,16,107,21,32,16,101,32,109,32,103,21,29,16,110,32,109,48,746,21,23,16,107,32,103,48,746],
[42,16,21,32,21,23,21,29,42,16,16,101,16,107,16,110,21,32,16,101,32,103,32,109,21,23,16,107,32,103,48,746,21,29,16,110,32,109,48,746]]

def tabmarkChunk24 : Array (List Nat) := #[[42,16,21,32,21,23,21,29,42,16,16,101,16,106,16,110,21,32,16,101,32,103,32,109,21,23,16,106,32,103,48,747,21,29,16,110,32,109,48,747],
[42,16,21,32,21,23,21,29,42,16,16,101,16,107,16,106,21,32,16,101,32,103,32,109,21,23,16,107,32,103,48,747,21,29,16,106,32,109,48,747],
[21,42,16,106,32,746,48,747,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,107,32,746,21,32,16,101,32,103,48,747,21,23,16,107,32,103],
[42,16,21,32,21,23,21,29,42,16,16,101,16,106,16,106,21,32,16,101,32,103,32,109,21,23,16,106,32,103,48,151,21,29,16,106,32,109,48,151],
[21,42,16,106,32,747,48,151,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,106,32,747,21,32,16,101,32,103,48,151,21,23,16,106,32,103],
[21,42,16,106,32,736,48,157,21,42,42,16,21,32,21,29,16,106,42,16,16,101,16,110,32,736,21,32,16,101,32,109,48,157,21,29,16,110,32,109],
[21,42,16,106,32,735,128,157,21,42,42,16,21,32,21,29,16,106,42,16,16,101,16,110,32,735,21,32,16,101,32,109,128,157,21,29,16,110,32,109],
[21,42,16,106,32,736,128,157,21,42,42,16,21,32,21,29,16,106,42,16,16,101,16,110,32,736,21,32,16,101,32,109,128,157,21,29,16,110,32,109],
[21,42,16,106,32,737,48,157,21,42,42,16,21,32,21,29,16,106,42,16,16,101,16,110,32,737,21,32,16,101,32,109,48,157,21,29,16,110,32,109],
[21,42,42,16,21,32,21,23,21,42,16,106,32,739,48,151,42,16,16,106,16,101,16,155,21,32,32,739,16,101,32,103,21,23,48,151,16,155,32,103],
[21,42,16,106,32,738,48,151,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,155,32,738,21,32,16,101,32,103,48,151,21,23,16,155,32,103],
[21,42,16,106,32,739,48,151,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,155,32,739,21,32,16,101,32,103,48,151,21,23,16,155,32,103],
[21,42,16,106,32,740,48,151,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,155,32,740,21,32,16,101,32,103,48,151,21,23,16,155,32,103],
[21,42,32,741,48,149,128,149,21,42,21,32,42,21,42,21,32,741,21,32,32,101,32,101,48,149,42,21,32,101,48,110,128,149,42,21,32,101,48,110],
[21,42,110,149,32,742,48,149,21,42,42,21,21,32,42,21,110,149,42,21,32,101,48,110,32,742,21,32,32,101,32,101,48,149,42,21,48,110,32,101],
[42,16,21,42,21,23,21,29,42,16,16,103,16,106,16,110,21,42,16,103,48,103,103,157,21,23,16,106,48,103,48,748,21,29,16,110,103,157,48,748]]

def tabmarkChunk25 : Array (List Nat) := #[[42,16,21,42,21,23,21,29,42,16,16,106,16,155,16,106,21,42,16,106,48,151,128,109,21,23,16,155,48,151,48,748,21,29,16,106,128,109,48,748],
[42,16,21,42,21,42,21,23,42,16,16,106,16,106,16,110,21,42,16,106,128,746,48,748,21,42,16,106,128,746,48,151,21,23,16,110,48,748,48,151],
[21,42,16,106,48,151,103,157,21,42,42,16,21,23,21,29,16,106,42,16,16,106,16,103,48,151,21,23,16,106,48,103,103,157,21,29,16,103,48,103],
[21,42,16,106,103,748,48,151,21,42,42,16,21,42,21,23,16,106,42,16,16,103,16,106,103,748,21,42,16,103,48,103,48,151,21,23,16,106,48,103],
[48,749,21,42,16,106,32,745,48,749,21,48,16,750,32,751,21,42,21,48,42,16,21,32,16,106,16,750,42,16,16,101,32,745,32,751,21,32,16,101],
[21,42,16,106,32,746,48,151,21,42,42,16,21,32,21,23,16,106,42,16,16,101,16,110,32,746,21,32,16,101,32,103,48,151,21,23,16,110,32,103],
[42,16,21,32,21,21,21,29,42,16,16,101,16,107,16,158,21,32,16,101,32,101,32,157,21,21,16,107,32,101,48,752,21,29,16,158,32,157,48,752],
[21,42,32,158,48,149,16,149,21,42,21,30,21,21,42,16,32,158,21,30,32,101,16,101,48,149,21,21,32,101,16,110,16,149,42,16,16,101,16,110],
[21,42,16,149,48,149,32,157,21,42,42,16,21,21,21,29,16,149,42,16,16,109,16,101,48,149,21,21,16,109,32,101,32,157,21,29,16,101,32,101],
[21,42,16,149,32,752,48,149,21,42,42,16,21,32,21,21,16,149,42,16,16,101,16,110,32,752,21,32,16,101,32,101,48,149,21,21,16,110,32,101],
[42,16,21,32,21,23,21,21,42,16,16,101,16,155,16,110,21,32,16,101,32,103,32,101,21,23,16,155,32,103,48,752,21,21,16,110,32,101,48,752],
[21,21,16,746,32,101,48,752,21,21,42,16,21,32,21,23,16,746,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,752,21,23,16,155,32,103],
[21,42,42,16,21,32,21,21,21,42,16,149,32,107,48,106,42,16,16,149,16,101,16,155,21,32,32,107,16,101,32,101,21,21,48,106,16,155,32,101],
[21,42,16,149,32,107,48,106,21,42,42,16,21,32,21,21,16,149,42,16,16,101,16,155,32,107,21,32,16,101,32,101,48,106,21,21,16,155,32,101],
[21,42,16,149,32,107,48,106,21,42,42,16,21,32,21,21,16,149,42,16,16,101,16,155,32,107,21,32,16,101,32,101,48,106,21,21,16,155,32,101],
[21,42,16,149,32,107,48,106,21,42,42,16,21,32,21,21,16,149,42,16,16,101,16,155,32,107,21,32,16,101,32,101,48,106,21,21,16,155,32,101]]

def tabmarkChunk26 : Array (List Nat) := #[[21,42,32,107,48,106,128,149,21,42,21,32,42,21,42,21,32,107,21,32,32,101,32,101,48,106,42,21,32,101,48,110,128,149,42,21,32,101,48,110],
[21,42,32,107,48,106,16,149,21,42,21,30,21,21,42,16,32,107,21,30,32,101,16,101,48,106,21,21,32,101,16,110,16,149,42,16,16,101,16,110],
[42,16,21,42,21,21,21,29,42,16,16,149,16,155,16,154,21,42,16,149,48,106,128,107,21,21,16,155,48,106,48,106,21,29,16,154,128,107,48,106],
[42,16,21,32,21,21,21,21,42,16,16,101,16,155,16,158,21,32,16,101,32,101,32,101,21,21,16,155,32,101,48,107,21,21,16,158,32,101,48,107],
[21,21,16,752,32,101,48,107,21,21,42,16,21,32,21,21,16,752,42,16,16,101,16,155,32,101,21,32,16,101,32,101,48,107,21,21,16,155,32,101],
[21,21,16,735,32,101,48,110,21,21,42,16,21,32,21,29,16,735,42,16,16,101,16,158,32,101,21,32,16,101,32,157,48,110,21,29,16,158,32,157],
[21,21,16,735,32,101,64,110,21,21,42,16,21,32,21,29,16,735,42,16,16,101,16,158,32,101,21,32,16,101,32,157,64,110,21,29,16,158,32,157],
[21,21,16,736,32,101,64,110,21,21,42,16,21,32,21,29,16,736,42,16,16,101,16,158,32,101,21,32,16,101,32,157,64,110,21,29,16,158,32,157],
[21,21,16,737,32,101,48,110,21,21,42,16,21,32,21,29,16,737,42,16,16,101,16,158,32,101,21,32,16,101,32,157,48,110,21,29,16,158,32,157],
[21,21,16,738,32,101,48,107,21,21,42,16,21,32,21,43,16,738,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,107,21,43,16,155,32,103],
[21,21,16,738,32,101,48,107,21,21,42,16,21,32,21,43,16,738,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,107,21,43,16,155,32,103],
[21,21,16,739,32,101,48,107,21,21,42,16,21,32,21,43,16,739,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,107,21,43,16,155,32,103],
[21,21,16,740,32,101,48,107,21,21,42,16,21,32,21,43,16,740,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,107,21,43,16,155,32,103],
[42,21,21,32,42,21,21,29,42,21,32,101,48,107,64,110,21,32,32,101,32,101,32,109,42,21,48,107,32,101,48,753,21,29,64,110,32,109,48,753],
[42,21,21,32,21,43,42,21,42,21,32,101,48,107,64,110,21,32,32,101,32,103,32,101,21,43,48,107,32,103,48,753,42,21,64,110,32,101,48,753],
[42,21,42,21,21,32,21,29,42,21,64,746,32,101,48,753,42,21,64,746,32,101,48,107,21,32,32,101,32,101,32,103,21,29,48,753,48,107,32,103]]

def tabmarkChunk27 : Array (List Nat) := #[[21,21,32,101,48,107,64,110,21,21,21,32,42,21,42,21,32,101,21,32,32,101,32,101,48,107,42,21,32,101,48,155,64,110,42,21,32,101,48,155],
[21,21,64,753,32,101,48,107,21,21,42,21,21,32,42,21,64,753,42,21,32,101,48,155,32,101,21,32,32,101,32,101,48,107,42,21,48,155,32,101],
[21,21,16,743,48,106,64,103,21,21,42,16,21,42,21,29,16,743,42,16,16,154,16,154,48,106,21,42,16,154,48,103,64,103,21,29,16,154,48,103],
[21,21,16,744,64,103,48,106,21,21,42,16,21,42,21,29,16,744,42,16,16,154,16,154,64,103,21,42,16,154,48,103,48,106,21,29,16,154,48,103],
[48,754,21,21,16,745,32,101,48,754,21,48,16,755,32,756,21,21,21,48,42,16,21,32,16,745,16,755,42,16,16,101,32,101,32,756,21,32,16,101],
[21,21,16,746,32,101,48,107,21,21,42,16,21,32,21,29,16,746,42,16,16,101,16,155,32,101,21,32,16,101,32,103,48,107,21,29,16,155,32,103],
[21,21,32,101,48,106,16,110,21,21,21,30,21,31,42,16,32,101,21,30,32,103,16,101,48,106,21,31,32,103,16,154,16,110,42,16,16,101,16,154],
[21,21,16,109,48,106,32,101,21,21,42,16,21,42,21,29,16,109,42,16,16,154,16,101,48,106,21,42,16,154,32,103,32,101,21,29,16,101,32,103],
[21,21,16,747,32,101,48,106,21,21,42,16,21,32,21,29,16,747,42,16,16,101,16,154,32,101,21,32,16,101,32,103,48,106,21,29,16,154,32,103],
[21,21,16,151,32,101,48,106,21,21,42,16,21,32,21,42,16,151,42,16,16,101,16,149,32,101,21,32,16,101,32,103,48,106,21,42,16,149,32,103],
[21,21,16,151,32,101,48,106,21,21,42,16,21,32,21,42,16,151,42,16,16,101,16,149,32,101,21,32,16,101,32,103,48,106,21,42,16,149,32,103],
[21,21,16,151,32,101,48,106,21,21,42,16,21,32,21,42,16,151,42,16,16,101,16,149,32,101,21,32,16,101,32,103,48,106,21,42,16,149,32,103],
[21,21,16,151,32,101,48,106,21,21,42,16,21,32,21,42,16,151,42,16,16,101,16,149,32,101,21,32,16,101,32,103,48,106,21,42,16,149,32,103],
[42,21,21,32,21,42,42,21,42,21,32,101,48,106,64,110,21,32,32,101,32,103,32,101,21,42,48,106,32,103,48,149,42,21,64,110,32,101,48,149],
[21,21,16,151,48,106,64,103,21,21,42,16,21,42,21,29,16,151,42,16,16,149,16,154,48,106,21,42,16,149,48,103,64,103,21,29,16,154,48,103],
[21,21,16,109,48,106,32,101,21,21,42,16,21,42,21,29,16,109,42,16,16,149,16,101,48,106,21,42,16,149,32,103,32,101,21,29,16,101,32,103]]

def tabmarkChunk28 : Array (List Nat) := #[[48,106,21,21,32,101,16,110,48,106,21,42,32,158,16,149,21,21,21,42,21,30,42,16,32,101,32,158,21,30,16,101,16,110,16,149,42,16,16,101],
[48,106,21,21,16,109,32,101,48,106,21,42,16,149,32,157,21,21,21,42,42,16,21,29,16,109,16,149,42,16,16,101,32,101,32,157,21,29,16,101],
[48,106,21,21,32,101,16,110,48,106,21,42,32,158,16,149,21,21,21,42,21,30,42,16,32,101,32,158,21,30,16,101,16,110,16,149,42,16,16,101],
[48,106,21,21,16,109,32,101,48,106,21,42,16,149,32,157,21,21,21,42,42,16,21,29,16,109,16,149,42,16,16,101,32,101,32,157,21,29,16,101],
[64,106,21,21,32,101,16,110,64,106,21,42,32,158,16,149,21,21,21,42,21,30,42,16,32,101,32,158,21,30,16,101,16,110,16,149,42,16,16,101],
[64,106,21,21,16,109,32,101,64,106,21,42,16,149,32,157,21,21,21,42,42,16,21,29,16,109,16,149,42,16,16,101,32,101,32,157,21,29,16,101],
[64,106,21,21,32,101,16,110,64,106,21,42,32,158,16,149,21,21,21,42,21,30,42,16,32,101,32,158,21,30,16,101,16,110,16,149,42,16,16,101],
[64,106,21,21,16,109,32,101,64,106,21,42,16,149,32,157,21,21,21,42,42,16,21,29,16,109,16,149,42,16,16,101,32,101,32,157,21,29,16,101],
[21,42,64,106,32,753,48,149,21,42,42,21,21,32,42,21,64,106,42,21,32,101,48,110,32,753,21,32,32,101,32,101,48,149,42,21,48,110,32,101],
[21,21,16,748,64,103,48,106,21,21,42,16,21,42,21,29,16,748,42,16,16,149,16,154,64,103,21,42,16,149,48,103,48,106,21,29,16,154,48,103],
[48,106,21,42,16,149,32,754,48,106,21,21,16,750,32,101,21,42,21,21,42,16,21,32,16,149,16,750,42,16,16,101,32,754,32,101,21,32,16,101],
[21,21,48,106,16,749,32,101,21,21,21,42,42,16,21,32,48,106,21,42,16,149,32,756,16,749,42,16,16,149,16,101,32,101,21,32,32,756,16,101],
[64,106,21,21,16,750,32,101,64,106,21,42,16,149,32,755,21,21,21,42,42,16,21,32,16,750,16,149,42,16,16,101,32,101,32,755,21,32,16,101],
[64,106,21,21,16,751,32,101,64,106,21,42,16,149,32,756,21,21,21,42,42,16,21,32,16,751,16,149,42,16,16,101,32,101,32,756,21,32,16,101],
[69,746,64,16,101,32,192,48,69,746,106,16,69,32,69,48,64,16,106,16,16,101,16,107,101,32,69,32,16,101,32,103,192,48,69,48,16,107,32,103],
[21,735,42,16,21,32,21,29,21,735,16,16,32,32,69,77,42,16,16,16,16,101,16,110,21,32,32,32,16,101,32,109,21,29,69,77,16,110,32,109]]

def tabmarkChunk29 : Array (List Nat) := #[[21,736,42,16,21,32,21,29,21,736,16,16,32,32,69,77,42,16,16,16,16,101,16,110,21,32,32,32,16,101,32,109,21,29,69,77,16,110,32,109],
[21,737,42,16,21,32,21,29,21,737,16,16,32,32,48,48,42,16,16,16,16,101,16,110,21,32,32,32,16,101,32,109,21,29,48,48,16,110,32,109],
[21,746,16,16,32,32,48,48,21,746,42,16,21,32,21,23,16,16,42,16,16,101,16,107,32,32,21,32,16,101,32,103,48,48,21,23,16,107,32,103],
[21,738,42,16,21,32,21,23,21,738,16,16,32,32,48,48,42,16,16,16,16,101,16,107,21,32,32,32,16,101,32,103,21,23,48,48,16,107,32,103],
[21,739,42,16,21,32,21,23,21,739,16,16,32,32,48,48,42,16,16,16,16,101,16,107,21,32,32,32,16,101,32,103,21,23,48,48,16,107,32,103],
[21,740,42,16,21,32,21,23,21,740,16,16,32,32,48,48,42,16,16,16,16,101,16,107,21,32,32,32,16,101,32,103,21,23,48,48,16,107,32,103],
[21,741,21,32,42,21,42,21,21,741,32,32,48,48,107,69,21,32,32,32,32,101,32,101,42,21,48,48,32,101,48,107,42,21,107,69,32,101,48,107],
[21,742,42,21,21,32,42,21,21,742,107,69,32,32,48,48,42,21,107,69,32,101,48,107,21,32,32,32,32,101,32,101,42,21,48,48,48,107,32,101],
[21,743,42,16,21,23,21,29,21,743,16,16,48,48,69,77,42,16,16,16,16,106,16,103,21,23,48,48,16,106,48,103,21,29,69,77,16,103,48,103],
[21,744,42,16,21,42,21,23,21,744,16,16,69,138,48,48,42,16,16,16,16,103,16,106,21,42,69,138,16,103,48,103,21,23,48,48,16,106,48,103],
[21,746,42,16,21,32,21,23,21,746,16,16,32,32,48,48,42,16,16,16,16,101,16,107,21,32,32,32,16,101,32,103,21,23,48,48,16,107,32,103],
[21,747,42,16,21,32,21,23,21,747,16,16,32,32,48,48,42,16,16,16,16,101,16,106,21,32,32,32,16,101,32,103,21,23,48,48,16,106,32,103],
[21,748,42,16,21,42,21,23,21,748,16,16,69,128,48,48,42,16,16,16,16,103,16,106,21,42,69,128,16,103,48,103,21,23,48,48,16,106,48,103],
[21,752,42,16,21,32,21,21,21,752,16,16,32,32,48,48,42,16,16,16,16,101,16,107,21,32,32,32,16,101,32,101,21,21,48,48,16,107,32,101],
[21,753,42,21,21,32,42,21,21,753,106,64,32,32,48,48,42,21,106,64,32,101,48,107,21,32,32,32,32,101,32,101,42,21,48,48,48,107,32,101],
[42,16,21,32,21,29,42,16,16,101,16,110,21,32,16,101,32,109,21,29,16,110,32,109]]

def tabmarkChunk30 : Array (List Nat) := #[[42,16,21,32,21,29,42,16,16,101,16,110,21,32,16,101,32,109,21,29,16,110,32,109],
[42,16,21,32,21,29,42,16,16,101,16,110,21,32,16,101,32,109,21,29,16,110,32,109],
[42,16,21,32,21,23,42,16,16,101,16,107,21,32,16,101,32,103,21,23,16,107,32,103],
[42,16,21,32,21,23,42,16,16,101,16,107,21,32,16,101,32,103,21,23,16,107,32,103],
[42,16,21,32,21,23,42,16,16,101,16,107,21,32,16,101,32,103,21,23,16,107,32,103],
[21,32,42,21,42,21,21,32,32,101,32,101,42,21,32,101,48,107,42,21,32,101,48,107],
[42,21,21,32,42,21,42,21,32,101,48,107,21,32,32,101,32,101,42,21,48,107,32,101],
[42,16,21,23,21,29,42,16,16,106,16,103,21,23,16,106,48,103,21,29,16,103,48,103],
[42,16,21,42,21,23,42,16,16,103,16,106,21,42,16,103,48,103,21,23,16,106,48,103],
[21,48,16,757,32,758,21,48,42,16,21,32,16,757,42,16,16,101,32,758,21,32,16,101],
[42,16,21,32,21,23,42,16,16,101,16,107,21,32,16,101,32,103,21,23,16,107,32,103],
[42,16,21,32,21,23,42,16,16,101,16,106,21,32,16,101,32,103,21,23,16,106,32,103],
[42,16,21,42,21,23,42,16,16,103,16,106,21,42,16,103,48,103,21,23,16,106,48,103],
[21,42,42,16,21,32,21,42,16,106,32,758,42,16,16,106,16,101,21,32,32,758,16,101],
[21,42,16,106,32,757,21,42,42,16,21,32,16,106,42,16,16,101,32,757,21,32,16,101],
[21,42,16,106,32,758,21,42,42,16,21,32,16,106,42,16,16,101,32,758,21,32,16,101]]

def tabmarkChunk31 : Array (List Nat) := #[[42,16,21,32,21,21,42,16,16,101,16,107,21,32,16,101,32,101,21,21,16,107,32,101],
[42,21,21,32,42,21,42,21,32,101,48,107,21,32,32,101,32,101,42,21,48,107,32,101],
[21,21,16,757,32,101,21,21,42,16,21,32,16,757,42,16,16,101,32,101,21,32,16,101],
[21,21,16,757,32,101,21,21,42,16,21,32,16,757,42,16,16,101,32,101,21,32,16,101],
[21,21,16,758,32,101,21,21,42,16,21,32,16,758,42,16,16,101,32,101,21,32,16,101],
[42,16,21,32,42,16,16,101,21,32,16,101],
[42,16,21,32,42,16,16,101,21,32,16,101]]

def tabmark (i : Nat) : List Nat :=
  let a := match i / 16 with
    | 0 => tabmarkChunk0
    | 1 => tabmarkChunk1
    | 2 => tabmarkChunk2
    | 3 => tabmarkChunk3
    | 4 => tabmarkChunk4
    | 5 => tabmarkChunk5
    | 6 => tabmarkChunk6
    | 7 => tabmarkChunk7
    | 8 => tabmarkChunk8
    | 9 => tabmarkChunk9
    | 10 => tabmarkChunk10
    | 11 => tabmarkChunk11
    | 12 => tabmarkChunk12
    | 13 => tabmarkChunk13
    | 14 => tabmarkChunk14
    | 15 => tabmarkChunk15
    | 16 => tabmarkChunk16
    | 17 => tabmarkChunk17
    | 18 => tabmarkChunk18
    | 19 => tabmarkChunk19
    | 20 => tabmarkChunk20
    | 21 => tabmarkChunk21
    | 22 => tabmarkChunk22
    | 23 => tabmarkChunk23
    | 24 => tabmarkChunk24
    | 25 => tabmarkChunk25
    | 26 => tabmarkChunk26
    | 27 => tabmarkChunk27
    | 28 => tabmarkChunk28
    | 29 => tabmarkChunk29
    | 30 => tabmarkChunk30
    | 31 => tabmarkChunk31
    | _ => #[]
  a[i % 16]?.getD []

def okRow (i : Nat) : Bool := checkedRow tabrow 503 tabmark i
def blockOK (j : Nat) : Bool := (List.range 8).all fun k => decide (8*j+k ≥ 503) || okRow (8*j+k)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk0 : blockOK 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk1 : blockOK 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk2 : blockOK 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk3 : blockOK 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk4 : blockOK 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk5 : blockOK 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk6 : blockOK 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk7 : blockOK 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk8 : blockOK 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk9 : blockOK 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk10 : blockOK 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk11 : blockOK 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk12 : blockOK 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk13 : blockOK 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk14 : blockOK 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk15 : blockOK 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk16 : blockOK 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk17 : blockOK 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk18 : blockOK 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk19 : blockOK 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk20 : blockOK 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk21 : blockOK 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk22 : blockOK 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk23 : blockOK 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk24 : blockOK 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk25 : blockOK 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk26 : blockOK 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk27 : blockOK 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk28 : blockOK 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk29 : blockOK 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk30 : blockOK 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk31 : blockOK 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk32 : blockOK 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk33 : blockOK 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk34 : blockOK 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk35 : blockOK 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk36 : blockOK 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk37 : blockOK 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk38 : blockOK 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk39 : blockOK 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk40 : blockOK 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk41 : blockOK 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk42 : blockOK 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk43 : blockOK 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk44 : blockOK 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk45 : blockOK 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk46 : blockOK 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk47 : blockOK 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk48 : blockOK 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk49 : blockOK 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk50 : blockOK 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk51 : blockOK 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk52 : blockOK 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk53 : blockOK 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk54 : blockOK 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk55 : blockOK 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk56 : blockOK 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk57 : blockOK 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk58 : blockOK 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk59 : blockOK 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk60 : blockOK 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk61 : blockOK 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tabOk62 : blockOK 62 = true := by decide +kernel

lemma allBlocks (i : Fin 63) : blockOK i.val = true := by
  obtain ⟨x,hx⟩ := i
  change blockOK x = true
  match x, hx with
  | 0, _ => exact tabOk0
  | 1, _ => exact tabOk1
  | 2, _ => exact tabOk2
  | 3, _ => exact tabOk3
  | 4, _ => exact tabOk4
  | 5, _ => exact tabOk5
  | 6, _ => exact tabOk6
  | 7, _ => exact tabOk7
  | 8, _ => exact tabOk8
  | 9, _ => exact tabOk9
  | 10, _ => exact tabOk10
  | 11, _ => exact tabOk11
  | 12, _ => exact tabOk12
  | 13, _ => exact tabOk13
  | 14, _ => exact tabOk14
  | 15, _ => exact tabOk15
  | 16, _ => exact tabOk16
  | 17, _ => exact tabOk17
  | 18, _ => exact tabOk18
  | 19, _ => exact tabOk19
  | 20, _ => exact tabOk20
  | 21, _ => exact tabOk21
  | 22, _ => exact tabOk22
  | 23, _ => exact tabOk23
  | 24, _ => exact tabOk24
  | 25, _ => exact tabOk25
  | 26, _ => exact tabOk26
  | 27, _ => exact tabOk27
  | 28, _ => exact tabOk28
  | 29, _ => exact tabOk29
  | 30, _ => exact tabOk30
  | 31, _ => exact tabOk31
  | 32, _ => exact tabOk32
  | 33, _ => exact tabOk33
  | 34, _ => exact tabOk34
  | 35, _ => exact tabOk35
  | 36, _ => exact tabOk36
  | 37, _ => exact tabOk37
  | 38, _ => exact tabOk38
  | 39, _ => exact tabOk39
  | 40, _ => exact tabOk40
  | 41, _ => exact tabOk41
  | 42, _ => exact tabOk42
  | 43, _ => exact tabOk43
  | 44, _ => exact tabOk44
  | 45, _ => exact tabOk45
  | 46, _ => exact tabOk46
  | 47, _ => exact tabOk47
  | 48, _ => exact tabOk48
  | 49, _ => exact tabOk49
  | 50, _ => exact tabOk50
  | 51, _ => exact tabOk51
  | 52, _ => exact tabOk52
  | 53, _ => exact tabOk53
  | 54, _ => exact tabOk54
  | 55, _ => exact tabOk55
  | 56, _ => exact tabOk56
  | 57, _ => exact tabOk57
  | 58, _ => exact tabOk58
  | 59, _ => exact tabOk59
  | 60, _ => exact tabOk60
  | 61, _ => exact tabOk61
  | 62, _ => exact tabOk62
  | x+63, hx => omega

lemma allRows (i : Nat) (hi : i < 503) : checkedRow tabrow 503 tabmark i = true := by
  let j : Fin 63 := ⟨i/8, by omega⟩
  have ok := List.all_eq_true.mp (allBlocks j) (i % 8) (List.mem_range.mpr (by omega))
  have ar : 8*j.val + i % 8 = i := by dsimp [j]; omega
  simpa [ar, Nat.not_le.mpr hi, okRow] using ok

theorem closed_table_excludes : ¬ Run true (↑([15,240,3840,61440,4369,8738,17476,34952] : List Nat)) := by
  intro h
  apply impossible_seen tabrow 503 tabmark allRows h
  refine ⟨0,by decide,by decide,?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_6021.RepFront

-- At most one signal can be read twice when all eight inputs are needed.

namespace PEqualNP.Outside.L_meta_6021.RepFront

def active (a b : Nat → Nat) (out : Nat) : List Nat → Finset Nat
  | [] => {out}
  | j :: tail => insert (a j) (insert (b j) ((active a b out tail).erase (8+j)))

def Wired (a b : Nat → Nat) (out : Nat) : List Nat → Prop
  | [] => True
  | j :: tail => (8+j) ∈ active a b out tail ∧ a j ≠ b j ∧ a j ≠ 8+j ∧ b j ≠ 8+j ∧ Wired a b out tail

def truthBag (f : Nat → Nat) (s : Finset Nat) : Multiset Nat := s.val.map f

lemma truth_insert {f : Nat → Nat} {x : Nat} {s : Finset Nat} (h : x ∉ s) :
    truthBag f (insert x s) = f x ::ₘ truthBag f s := by
  simp only [truthBag,Finset.insert_val_of_notMem h,Multiset.map_cons]

lemma active_card {a b : Nat → Nat} {out : Nat} {s : List Nat} (h : Wired a b out s) :
    (active a b out s).card ≤ s.length+1 := by
  induction s with
  | nil => simp [active]
  | cons j s ih =>
    obtain ⟨hw,_,_,_,ht⟩ := h
    have hpos := Finset.card_pos.mpr ⟨_,hw⟩
    have h1 := Finset.card_insert_le (a j) (insert (b j) ((active a b out s).erase (8+j)))
    have h2 := Finset.card_insert_le (b j) ((active a b out s).erase (8+j))
    have hn := Finset.card_erase_of_mem hw
    have ready := ih ht
    simp only [active, List.length_cons]
    omega

def allowance : Bool → Nat | true => 1 | false => 0

lemma merge_back {f : Nat → Nat} {w a b : Nat} {s : Finset Nat} {m : Nat} {budget : Bool}
    (hw : w ∉ s) (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (gate : f w = (f a &&& f b) ∨ f w = (f a ||| f b))
    (bound : (insert w s).card ≤ m+1)
    (coins : m+2 ≤ (insert a (insert b s)).card + allowance budget)
    (rest : ∀ q, m+1 ≤ (insert w s).card + allowance q → Run q (truthBag f (insert w s))) :
    Run budget (truthBag f (insert a (insert b s))) := by
  let t := (s.erase a).erase b
  have at' : a ∉ t := by simp [t]
  have bt : b ∉ t := by simp [t]
  have abt : a ∉ insert b t := by simp [hab,at']
  have old : insert a (insert b s) = insert a (insert b t) := by
    ext z; simp only [t,Finset.mem_insert,Finset.mem_erase]; tauto
  rw [old] at coins ⊢
  simp only [Finset.card_insert_of_notMem abt,Finset.card_insert_of_notMem bt] at coins
  rw [truth_insert abt,truth_insert bt]
  have cs := Finset.card_insert_of_notMem hw
  rw [cs] at bound
  have revgate : f w = (f b &&& f a) ∨ f w = (f b ||| f a) := by
    simpa only [Nat.and_comm (f b) (f a),Nat.or_comm (f b) (f a)] using gate
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · have st : s = insert a (insert b t) := by
        ext z; simp only [t,Finset.mem_insert,Finset.mem_erase]; grind
      rw [st,Finset.card_insert_of_notMem abt,Finset.card_insert_of_notMem bt] at bound
      cases budget <;> simp [allowance] at coins <;> omega
    · have st : s = insert a t := by
        ext z; simp only [t,Finset.mem_insert,Finset.mem_erase]; grind
      have how : s.card=t.card+1 := by rw [st,Finset.card_insert_of_notMem at']
      cases budget with
      | false => simp [allowance] at coins; omega
      | true =>
        have next := rest false (by rw [cs,how]; simp [allowance] at coins ⊢; omega)
        rw [truth_insert hw,st,truth_insert at'] at next
        exact .reuse gate next
  · by_cases hb : b ∈ s
    · have st : s = insert b t := by
        ext z; simp only [t,Finset.mem_insert,Finset.mem_erase]; grind
      have how : s.card=t.card+1 := by rw [st,Finset.card_insert_of_notMem bt]
      cases budget with
      | false => simp [allowance] at coins; omega
      | true =>
        have next := rest false (by rw [cs,how]; simp [allowance] at coins ⊢; omega)
        rw [truth_insert hw,st,truth_insert bt] at next
        rw [Multiset.cons_swap (f a) (f b)]
        exact .reuse revgate next
    · have st : s = t := by simp [t, Finset.erase_eq_of_notMem ha, Finset.erase_eq_of_notMem hb]
      have next := rest budget (by rw [cs,st]; omega)
      rw [truth_insert hw,st] at next
      exact .merge gate next

lemma active_run {a b f : Nat → Nat} {out : Nat} (result : f out = 4958) {s : List Nat}
    (wires : Wired a b out s)
    (ops : ∀ j ∈ s, f (8+j) = (f (a j) &&& f (b j)) ∨ f (8+j) = (f (a j) ||| f (b j))) :
    ∀ budget, s.length+1 ≤ (active a b out s).card + allowance budget →
      Run budget (truthBag f (active a b out s)) := by
  induction s with
  | nil => intro budget _; apply Run.done; simp [truthBag,active,result]
  | cons j s ih =>
    obtain ⟨hw,hab,haw,hbw,ht⟩ := wires
    have step := Finset.insert_erase hw
    have rest := ih ht (fun t h => ops t (List.mem_cons_of_mem j h))
    intro budget coins
    apply merge_back (w:=8+j) (m:=s.length) (s:=(active a b out s).erase (8+j))
      (by simp) hab haw hbw (ops j (by simp))
    · rw [step]; exact active_card ht
    · simpa only [active,List.length_cons] using coins
    · rw [step]; exact rest

lemma active_mem {a b : Nat → Nat} {out x : Nat} {s : List Nat}
    (outside : ∀ j ∈ s, x ≠ 8+j)
    (used : x = out ∨ ∃ j ∈ s, x = a j ∨ x = b j) : x ∈ active a b out s := by
  induction s with
  | nil => simpa [active] using used
  | cons j s ih =>
    simp only [active,Finset.mem_insert,Finset.mem_erase]
    by_cases ha : x=a j
    · exact Or.inl ha
    by_cases hb : x=b j
    · exact Or.inr (Or.inl hb)
    refine Or.inr (Or.inr ⟨outside j (by simp),ih (fun i hi => outside i (List.mem_cons_of_mem _ hi)) ?_⟩)
    rcases used with rfl | ⟨t,ht,eq⟩
    · exact Or.inl rfl
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (eq.elim ha hb).elim
    · exact Or.inr ⟨t,ht,eq⟩

lemma wired_of_order {a b : Nat → Nat} {out : Nat} {s : List Nat}
    (inc : s.Pairwise (·<·)) (valid : ∀ j ∈ s, a j < 8+j ∧ b j < 8+j ∧ a j ≠ b j)
    (later : ∀ j ∈ s, 8+j=out ∨ ∃ t ∈ s, j<t ∧ (8+j=a t ∨ 8+j=b t)) : Wired a b out s := by
  induction s with
  | nil => trivial
  | cons j s ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp inc
    obtain ⟨ha,hb,hab⟩ := valid j (by simp)
    have narrow (i : Nat) (hi : i∈s) : 8+i=out ∨ ∃ t ∈ s, i<t ∧ (8+i=a t ∨ 8+i=b t) := by
      rcases later i (List.mem_cons_of_mem _ hi) with h | ⟨t,ht,hlt,hsource⟩
      · exact Or.inl h
      rcases List.mem_cons.mp ht with rfl | ht
      · have := head i hi; omega
      · exact Or.inr ⟨t,ht,hlt,hsource⟩
    refine ⟨active_mem (fun i hi => by have := head i hi; omega) ?_,hab,ha.ne,hb.ne,
      ih tail (fun i hi => valid i (List.mem_cons_of_mem _ hi)) narrow⟩
    rcases later j (by simp) with h | ⟨t,ht,hlt,hsource⟩
    · exact Or.inl h
    rcases List.mem_cons.mp ht with rfl | ht
    · omega
    · exact Or.inr ⟨t,ht,hsource⟩

lemma active_subset {a b : Nat → Nat} {out : Nat} {s : List Nat} (inc : s.Pairwise (·<·)) :
    ∀ avail : Finset Nat,
    (∀ j ∈ s, ∀ x, (x=a j ∨ x=b j) → x∈avail ∨ ∃ t ∈ s, t<j ∧ x=8+t) →
    (out∈avail ∨ ∃ t ∈ s, out=8+t) → active a b out s ⊆ avail := by
  induction s with
  | nil => intro avail _ hout; simpa [active] using hout
  | cons j s ih =>
    intro avail src final
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp inc
    have atHead (x : Nat) (hx : x=a j ∨ x=b j) : x∈avail := by
      rcases src j (by simp) x hx with h | ⟨t,ht,lt,_⟩
      · exact h
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := head t ht; omega
    have sub := ih tail (insert (8+j) avail) (by
      intro i hi x hx
      rcases src i (List.mem_cons_of_mem _ hi) x hx with h | ⟨t,ht,lt,val⟩
      · exact Or.inl (Finset.mem_insert_of_mem h)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl val))
      · exact Or.inr ⟨t,ht,lt,val⟩) (by
      rcases final with h | ⟨t,ht,val⟩
      · exact Or.inl (Finset.mem_insert_of_mem h)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl val))
      · exact Or.inr ⟨t,ht,val⟩)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact atHead _ (Or.inl rfl)
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact atHead _ (Or.inr rfl)
    obtain ⟨ne,hm⟩ := Finset.mem_erase.mp hx
    exact (Finset.mem_insert.mp (sub hm)).resolve_left ne

lemma execution {a b f : Nat → Nat} {out : Nat} {s : List Nat}
    (inc : s.Pairwise (·<·)) (len : s.length ≤ 8)
    (valid : ∀ j ∈ s, a j < 8+j ∧ b j < 8+j ∧ a j ≠ b j)
    (src : ∀ j ∈ s, ∀ x, (x=a j ∨ x=b j) → x<8 ∨ ∃ t ∈ s, t<j ∧ x=8+t)
    (inputs : ∀ x<8, ∃ j ∈ s, x=a j ∨ x=b j)
    (later : ∀ j ∈ s, 8+j=out ∨ ∃ t ∈ s, j<t ∧ (8+j=a t ∨ 8+j=b t))
    (outOn : ∃ t ∈ s, out=8+t) (result : f out=4958)
    (ops : ∀ j ∈ s, f (8+j) = (f (a j) &&& f (b j)) ∨ f (8+j) = (f (a j) ||| f (b j))) :
    Run true (truthBag f (Finset.range 8)) := by
  have id : active a b out s = Finset.range 8 := by
    apply Finset.Subset.antisymm
    · apply active_subset inc (Finset.range 8) _ (Or.inr outOn)
      simpa only [Finset.mem_range] using src
    · intro x hx
      have lt := Finset.mem_range.mp hx
      exact active_mem (fun j _ => by omega) (Or.inr (inputs x lt))
  rw [← id]
  apply active_run result (wired_of_order inc valid later) ops true
  rw [id,Finset.card_range]; simp [allowance]; omega

end PEqualNP.Outside.L_meta_6021.RepFront

namespace PEqualNP.Outside.L_meta_6021

def packRows : List ℕ → (ℕ → Bool) → ℕ
  | [], _ => 0
  | r :: rs, f => Nat.bit (f r) (packRows rs f)

theorem packRows_congr (rs : List ℕ) {f g : ℕ → Bool} (h : ∀ r ∈ rs, f r = g r) :
    packRows rs f = packRows rs g := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg₂ Nat.bit (h _ List.mem_cons_self)
      (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem packRows_and (rs : List ℕ) (f g : ℕ → Bool) :
    packRows rs (fun i => f i && g i) = packRows rs f &&& packRows rs g := by
  induction rs with
  | nil => simp [packRows]
  | cons r rs ih => simp only [packRows, Nat.land_bit, ih]

theorem packRows_or (rs : List ℕ) (f g : ℕ → Bool) :
    packRows rs (fun i => f i || g i) = packRows rs f ||| packRows rs g := by
  induction rs with
  | nil => simp [packRows]
  | cons r rs ih => simp only [packRows, Nat.lor_bit, ih]

end PEqualNP.Outside.L_meta_6021

namespace PEqualNP.Outside.L_meta_6021

open LRAT.Link LRAT.Promise

abbrev Represents4958 := PEqualNP.Represents.RepSizeAtMost
  (fun (u v : Fin 4) => (4958 : ℕ).testBit (4 * u.val + v.val)) 8
abbrev ModelOK (M : Model) := Valid 8 8 targetAt (· ∈ rows44) M
abbrev ModelNF (M : Model) := NF 8 8 M

theorem model_from_rep (h : Represents4958) : ∃ M, ModelOK M ∧ ModelNF M := by
  obtain ⟨C, hm, hs, correct⟩ := h
  apply LRAT.Link.exists_nf
  refine ⟨_, valid_ofCirc 8 8 targetAt (· ∈ rows44) C hm hs ?_⟩
  intro r hr
  simp only [rows44, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hr
  obtain ⟨u,v,rfl⟩ := hr
  have eq : ∀ i j : Fin 4, (4958 : ℕ).testBit (4*i.val+j.val) = targetAt (row44 i j) := by
    decide +kernel
  exact (congrArg C.eval (row44_eq u v)).trans ((correct u v).trans (eq u v))

def activeSteps (M : Model) : List ℕ := (List.range 8).filter fun j => decide (¬M.pad 8 j)

theorem active_iff {M : Model} {j : ℕ} :
    j ∈ activeSteps M ↔ j < 8 ∧ ¬ M.pad 8 j := by simp [activeSteps]

theorem active_sorted (M : Model) : (activeSteps M).Pairwise (· < ·) :=
  (show (List.range 8).Pairwise (· < ·) from by decide).filter _

theorem active_short (M : Model) : (activeSteps M).length ≤ 8 := by
  simpa [activeSteps] using List.length_filter_le (fun j => decide (¬ M.pad 8 j)) (List.range 8)

theorem active_operands {M : Model} (hv : ModelOK M) (hn : ModelNF M) {j : ℕ}
    (h : j ∈ activeSteps M) :
    M.s1 j < 8+j ∧ M.s2 j < 8+j ∧ M.s1 j ≠ M.s2 j := by
  obtain ⟨hj,hnp⟩ := active_iff.mp h
  have hl := hv.s1_le j hj
  have hr := hv.s2_le j hj
  have hf := hn.noF j hj hnp
  have ho := hn.ord j hj hnp
  omega

theorem active_source {M : Model} (hv : ModelOK M) (hn : ModelNF M) {j u : ℕ}
    (hj : j ∈ activeSteps M) (hu : u = M.s1 j ∨ u = M.s2 j) (h8 : 8 ≤ u) :
    u-8 ∈ activeSteps M := by
  have hl := active_operands hv hn hj
  have hlt : u < 8 + j := by rcases hu with rfl|rfl <;> omega
  obtain ⟨hj',_⟩ := active_iff.mp hj
  refine active_iff.mpr ⟨by omega, ?_⟩
  intro hp
  have hbad := hn.noPadRd j hj' (u-8) (by omega) hp
  rcases hu with hu | hu <;> omega

theorem active_pad_desc {M : Model} (hn : ModelNF M) {a b : ℕ} :
    b < 8 → a ≤ b → M.pad 8 b → M.pad 8 a := by
  induction b with
  | zero => intro hb hab h; simpa [show a=0 by omega] using h
  | succ b ih =>
    intro hb hab h
    by_cases eq : a=b+1
    · simpa [eq] using h
    · exact ih (by omega) (by omega) (hn.pre b hb h)

theorem active_final {M : Model} (hn : ModelNF M) {j : ℕ} (hj : j ∈ activeSteps M) :
    M.so = 15 ∧ 7 ∈ activeSteps M := by
  obtain ⟨hj',hjp⟩ := active_iff.mp hj
  have h7 : ¬ M.pad 8 7 := fun h => hjp (active_pad_desc hn (by decide) (by omega) h)
  exact ⟨(hn.out (by decide)).resolve_right h7, active_iff.mpr ⟨by decide,h7⟩⟩

theorem active_later {M : Model} (_hv : ModelOK M) (hn : ModelNF M) {j : ℕ}
    (hj : j ∈ activeSteps M) :
    8+j = M.so ∨ ∃ i ∈ activeSteps M, j < i ∧ (M.s1 i = 8+j ∨ M.s2 i = 8+j) := by
  obtain ⟨hj',hnp⟩ := active_iff.mp hj
  by_cases last : j=7
  · left; rw [(active_final hn hj).1, last]
  right
  obtain ⟨i,hji,hi,read⟩ := hn.used j (by omega) hnp
  refine ⟨i, active_iff.mpr ⟨hi,?_⟩,hji,read⟩
  intro hp
  obtain ⟨_,h1,h2⟩ := hp
  rcases read with h | h <;> omega

def rawRow (w r : ℕ) : Bool := r.testBit w
def wireRow (M : Model) (w r : ℕ) : Bool := if w < 8 then rawRow w r else M.w (w-8) r
def wireMask (M : Model) (w : ℕ) : ℕ := packRows rows44 (wireRow M w)

theorem source_eq_wire (M : Model) (j k r : ℕ) (hk : k < 8 + j) :
    M.sv 8 j k r = wireRow M k r := by simp [Model.sv,wireRow,rawRow,hk]

theorem active_mask {M : Model} (hv : ModelOK M) (hn : ModelNF M) {j : ℕ}
    (hj : j ∈ activeSteps M) :
    wireMask M (8+j) = wireMask M (M.s1 j) &&& wireMask M (M.s2 j) ∨
    wireMask M (8+j) = wireMask M (M.s1 j) ||| wireMask M (M.s2 j) := by
  obtain ⟨jlt,np⟩ := active_iff.mp hj
  obtain ⟨h1,h2,_⟩ := active_operands hv hn hj
  have ho := hv.op_lt j jlt
  have hne : M.op j ≠ 2 := fun he => np (hn.padOp j jlt he)
  have eq (r : ℕ) (hr : r ∈ rows44) :
      wireRow M (8+j) r = gfun (M.op j) (wireRow M (M.s1 j) r) (wireRow M (M.s2 j) r) := by
    rw [← source_eq_wire M j _ r h1, ← source_eq_wire M j _ r h2, ← hv.w_eq j jlt r hr]
    simp [wireRow]
  rcases (show M.op j = 0 ∨ M.op j = 1 by omega) with hop | hop
  · left; unfold wireMask; rw [← packRows_and]; apply packRows_congr
    intro r hr; simpa [hop, gfun] using eq r hr
  · right; unfold wireMask; rw [← packRows_or]; apply packRows_congr
    intro r hr; simpa [hop, gfun] using eq r hr

theorem active_output {M : Model} (hv : ModelOK M) (hn : ModelNF M) {j : ℕ}
    (hj : j ∈ activeSteps M) : wireMask M M.so = 4958 := by
  have ho := (active_final hn hj).1
  calc
    _ = packRows rows44 targetAt := by
      apply packRows_congr
      intro r hr
      rw [← source_eq_wire M 8 M.so r (by omega)]
      exact hv.out_eq r hr
    _ = _ := by decide +kernel

theorem raw_multiset (M : Model) : (Finset.range 8).val.map (wireMask M) =
    (([15,240,3840,61440,4369,8738,17476,34952] : List ℕ) : Multiset ℕ) := by
  calc
    _ = (Finset.range 8).val.map (fun i => packRows rows44 (rawRow i)) := by
      apply Multiset.map_congr rfl
      intro i hi
      have h : i < 8 := Finset.mem_range.mp hi
      apply packRows_congr
      intro r _
      simp [wireRow,h]
    _ = _ := by decide +kernel

end PEqualNP.Outside.L_meta_6021

-- Each raw input has two promised rows that force its use.

namespace PEqualNP.Outside.L_meta_6021

open LRAT.Link

def rawRows (i : Fin 8) : ℕ × ℕ :=
  ![(33,34),(18,17),(20,17),(24,17),(18,34),(33,17),(65,17),(129,17)] i

lemma rawRows_spec : ∀ i : Fin 8, (rawRows i).1 ∈ LRAT.Promise.rows44 ∧
    (rawRows i).2 ∈ LRAT.Promise.rows44 ∧ targetAt (rawRows i).1 = true ∧
    targetAt (rawRows i).2 = false ∧ ∀ k : Fin 8, k ≠ i →
    (rawRows i).1.testBit k.val = true → (rawRows i).2.testBit k.val = true := by decide

lemma positive_without : ∀ i : Fin 8, ∃ r ∈ LRAT.Promise.rows44,
    targetAt r = true ∧ r.testBit i.val = false := by decide

lemma gfun_imp (t : ℕ) (a b c d : Bool) (ac : a=true → c=true) (bd : b=true → d=true) :
    gfun t a b = true → gfun t c d = true := by
  by_cases ht : t = 0
  · cases a <;> cases b <;> cases c <;> cases d <;> simp_all [gfun]
  · by_cases ho : t = 1
    · cases a <;> cases b <;> cases c <;> cases d <;> simp_all [gfun]
    · simp [gfun, ht, ho]

theorem normal_reads_every_raw (M : Model)
    (good : Valid 8 8 targetAt (· ∈ LRAT.Promise.rows44) M) :
    ∀ i : Fin 8, ∃ j < 8, ¬ M.pad 8 j ∧ (M.s1 j = i.val ∨ M.s2 j = i.val) := by
  intro i
  by_contra no
  have absent (j : ℕ) (hj : j < 8) : M.s1 j ≠ i.val ∧ M.s2 j ≠ i.val := by
    by_cases pad : M.pad 8 j
    · obtain ⟨_,e,f⟩ := pad
      rw [e,f]
      have hi := i.isLt
      omega
    · exact ⟨fun eq => no ⟨j,hj,pad,Or.inl eq⟩, fun eq => no ⟨j,hj,pad,Or.inr eq⟩⟩
  have hout : M.so ≠ i.val := by
    intro e
    obtain ⟨r,hr,hot,cold⟩ := positive_without i
    have eq := good.out_eq r hr
    rw [e, Model.sv, ite_eq_left i.isLt, cold, hot] at eq
    cases eq
  let u := (rawRows i).1
  let v := (rawRows i).2
  obtain ⟨ru,rv,one,zero,comp⟩ := rawRows_spec i
  have mono : ∀ j ≤ 8, ∀ k ≠ i.val, M.sv 8 j k u = true → M.sv 8 j k v = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro j8 k ki
      by_cases kr : k < 8
      · simpa only [Model.sv, ite_eq_left kr] using
          comp ⟨k,kr⟩ (fun e => ki (congrArg Fin.val e))
      · by_cases old : k < 8+j
        · simp only [Model.sv, ite_eq_right kr, ite_eq_left old]
          have kj : k-8<j := by omega
          have k8 := kj.trans_le j8
          rw [good.w_eq (k-8) k8 u ru, good.w_eq (k-8) k8 v rv]
          apply gfun_imp
          · exact ih _ kj k8.le _ (absent _ k8).1
          · exact ih _ kj k8.le _ (absent _ k8).2
        · simp only [Model.sv, ite_eq_right kr, ite_eq_right old, imp_self]
  have impossible := mono 8 (by decide) M.so hout
    ((good.out_eq u ru).trans one)
  rw [good.out_eq v rv] at impossible
  exact Bool.noConfusion (impossible.symm.trans zero)

end PEqualNP.Outside.L_meta_6021

namespace PEqualNP.Outside.L_meta_6021

open LRAT.Link

theorem frontier_from_rep4958 (h : Represents4958) :
    RepFront.Run true (([15,240,3840,61440,4369,8738,17476,34952] : List ℕ) : Multiset ℕ) := by
  obtain ⟨M,hv,hn⟩ := model_from_rep h
  have inputs : ∀ x<8, ∃ j ∈ activeSteps M, x=M.s1 j ∨ x=M.s2 j := by
    intro x hx
    obtain ⟨j,hj,np,r⟩ := normal_reads_every_raw M hv ⟨x,hx⟩
    exact ⟨j, active_iff.mpr ⟨hj,np⟩, r.imp Eq.symm Eq.symm⟩
  obtain ⟨j, hj, _⟩ := inputs 0 (by decide)
  have fin := active_final hn hj
  rw [← raw_multiset M]
  apply RepFront.execution (a:=M.s1) (b:=M.s2) (out:=M.so) (f:=wireMask M)
    (active_sorted M) (active_short M) (fun j hj => active_operands hv hn hj)
  · intro j hj u hu
    by_cases raw : u < 8
    · exact Or.inl raw
    have bounds := active_operands hv hn hj
    have bound : u < 8+j := by rcases hu with rfl|rfl <;> omega
    exact Or.inr ⟨u-8, active_source hv hn hj hu (by omega), by omega, by omega⟩
  · exact inputs
  · intro j hj
    rcases active_later hv hn hj with r | ⟨t,ht,lt,h⟩
    · exact Or.inl r
    · exact Or.inr ⟨t,ht,lt,h.imp Eq.symm Eq.symm⟩
  · exact ⟨7, fin.2, fin.1⟩
  · exact active_output hv hn hj
  · exact fun j h => active_mask hv hn h

end PEqualNP.Outside.L_meta_6021

theorem PEqualNP.Outside.L_meta_6021 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4958 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4958 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_6021.upper, fun small =>
    PEqualNP.Outside.L_meta_6021.RepFront.closed_table_excludes (PEqualNP.Outside.L_meta_6021.frontier_from_rep4958 small)⟩
