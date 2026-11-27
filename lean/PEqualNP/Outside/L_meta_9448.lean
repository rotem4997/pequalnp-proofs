import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9448_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gL {V l : List Bool} {i : ℕ} (h : i < V.length) :
    (V ++ l).getD i false = V.getD i false := List.getD_append _ _ _ _ h

def chain (op : GateOp) : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | c, acc, y :: ys => ⟨op, [acc, y]⟩ :: chain op (c + 1) c ys

def fin : ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => acc
  | c, _, _ :: ys => fin (c + 1) c ys

theorem chain_len (op : GateOp) (ys : List ℕ) : ∀ c acc, (chain op c acc ys).length = ys.length := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih => intro c acc; simp [chain, ih]

theorem fin_cons (y : ℕ) (ys : List ℕ) : ∀ c acc, fin c acc (y :: ys) = c + ys.length := by
  induction ys generalizing y with
  | nil => intro c acc; simp [fin]
  | cons z zs ih => intro c acc; rw [fin, ih]; simp; omega

theorem chain_op (op : GateOp) (ys : List ℕ) : ∀ c acc, ∀ g ∈ chain op c acc ys,
    g.op = op ∧ g.inputs.length = 2 := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_nd (op : GateOp) (R : ℕ) (ys : List ℕ) : ∀ c acc, R ≤ c → (∀ y ∈ ys, y < R) → acc ∉ ys →
    ∀ g ∈ chain op c acc ys, g.inputs.Nodup := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc hR hy ha g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [List.mem_cons, not_or] at ha
      simp [ha.1]
    · exact ih (c + 1) c (by omega) (fun z hz => hy z (by simp [hz]))
        (fun hc => by have := hy c (by simp [hc]); omega) g hg

theorem chain_rb (op : GateOp) (ys : List ℕ) : ∀ c acc, acc < c → (∀ y ∈ ys, y < c) →
    ∀ j < (chain op c acc ys).length, ∀ i ∈ ((chain op c acc ys).getD j ⟨GateOp.or, []⟩).inputs, i < c + j := by
  induction ys with
  | nil => simp [chain]
  | cons y ys ih =>
    intro c acc ha hy j hj i hi
    cases j with
    | zero =>
      simp [chain] at hi
      rcases hi with rfl | rfl
      · omega
      · have := hy i (by simp); omega
    | succ j =>
      simp only [chain, List.length_cons] at hj
      simp only [chain, List.getD_cons_succ] at hi
      have := ih (c + 1) c (by omega) (fun z hz => by have := hy z (by simp [hz]); omega) j (by omega) i hi
      omega

theorem chain_val (op : GateOp) (R : ℕ) (f : ℕ → Bool) (ys : List ℕ) (hys : ∀ y ∈ ys, y < R) :
    ∀ c acc (v : Bool) (V : List Bool), V.length = c → R ≤ c → (∀ i < R, V.getD i false = f i) →
      acc < c → V.getD acc false = v →
      ((chain op c acc ys).foldl stp V).getD (fin c acc ys) false =
        ys.foldl (fun b y => op.eval [b, f y]) v := by
  induction ys with
  | nil => intro c acc v V _ _ _ _ h0; simpa [chain, fin] using h0
  | cons y ys ih =>
    intro c acc v V hV hR hf hac h0
    have hy := hys y (by simp)
    simp only [chain, fin, List.foldl_cons]
    set a := op.eval ([acc, y].map fun i => V.getD i false) with ha
    have hs : stp V ⟨op, [acc, y]⟩ = V ++ [a] := rfl
    rw [hs]
    have hav : a = op.eval [v, f y] := by
      rw [ha]; simp only [List.map_cons, List.map_nil]; rw [h0, hf y hy]
    rw [← hav]
    apply ih (fun z hz => hys z (by simp [hz])) (c + 1) c a (V ++ [a]) (by simp [hV]) (by omega)
      (fun i hi => by rw [gL (by omega)]; exact hf i hi) (by omega)
    simp [List.getD_eq_getElem?_getD, hV]

theorem fold_or (g : ℕ → Bool) (l : List ℕ) : ∀ v, l.foldl (fun b y => GateOp.or.eval [b, g y]) v = (v || l.any g) := by
  induction l with
  | nil => simp
  | cons y ys ih => intro v; rw [List.foldl_cons, ih]; simp [GateOp.eval, Bool.or_assoc]

theorem fold_and (g : ℕ → Bool) (l : List ℕ) : ∀ v, l.foldl (fun b y => GateOp.and.eval [b, g y]) v = (v && l.all g) := by
  induction l with
  | nil => simp
  | cons y ys ih => intro v; rw [List.foldl_cons, ih]; simp [GateOp.eval, Bool.and_assoc]

theorem ev (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

end PEqualNP.Outside.L_meta_9448_aux

open PEqualNP.Outside.L_meta_9448_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9448 : ∀ (x1 : ℕ) (x2 : Bool) (x3 : Fin x1) (x4 : List (Fin x1)), x4 ≠ [] → (x3 :: x4).Nodup → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.size = x4.length ∧ x7.output = x1 + x7.size - (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x8 ∈ x7.gates, x8.inputs.Nodup) ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = if x2 = Bool.true then (x3 :: x4).any fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false else (x3 :: x4).all fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false := by
  intro x1 x2 x3 x4 hne hnd
  let op : GateOp := if x2 = true then GateOp.or else GateOp.and
  let ys : List ℕ := x4.map Fin.val
  have hys : ∀ y ∈ ys, y < x1 := by
    intro y hy; simp only [ys, List.mem_map] at hy; obtain ⟨q, _, rfl⟩ := hy; exact q.isLt
  have hyne : ys ≠ [] := by simpa [ys] using hne
  obtain ⟨y0, ys0, hy0⟩ := List.exists_cons_of_ne_nil hyne
  have hx3 : x3.val ∉ ys := by
    intro h; simp only [ys, List.mem_map] at h; obtain ⟨q, hq, hqe⟩ := h
    have := (List.nodup_cons.mp hnd).1; rw [Fin.ext hqe] at hq; exact this hq
  refine ⟨⟨chain op x1 x3.val ys, fin x1 x3.val ys⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size, chain_len, ys]
  · simp only [Circuit.size, chain_len]; rw [hy0, fin_cons]; simp
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg; have := (chain_op op ys _ _ g hg).1; rw [this]; simp only [op]; split_ifs <;> simp
    · intro j hj i hi
      exact chain_rb op ys x1 x3.val x3.isLt (fun y hy => hys y hy) j hj i hi
    · intro g hg; exact (chain_op op ys _ _ g hg).2
  · exact chain_nd op x1 ys x1 x3.val le_rfl hys hx3
  · intro x8 hx8
    rw [ev]
    rw [chain_val op x1 (fun i => x8.getD i false) ys hys x1 x3.val _ x8 hx8 le_rfl (fun i _ => rfl) x3.isLt rfl]
    simp only [op]
    split_ifs with h
    · rw [fold_or]; simp [ys, List.any_map, Function.comp_def]
    · rw [fold_and]; simp [ys, List.all_map, Function.comp_def]
