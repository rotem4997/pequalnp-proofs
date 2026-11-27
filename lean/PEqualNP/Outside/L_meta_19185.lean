import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19185_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def chain (b a : ℕ) : List ℕ → List Gate
  | [] => []
  | c :: L => ⟨GateOp.or, [a, c]⟩ :: chain (b + 1) b L

def last (b a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => last (b + 1) b L

theorem chain_good (b a : ℕ) (L : List ℕ) :
    ∀ g ∈ chain b a L, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction L generalizing b a with
  | nil => simp [chain]
  | cons c L ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_len (b a : ℕ) (L : List ℕ) : (chain b a L).length = L.length := by
  induction L generalizing b a with
  | nil => rfl
  | cons c L ih => simp [chain, ih]

theorem pre_stp (x : List Bool) (g : Gate) (w : ℕ) (h : w < x.length) :
    (stp x g).getD w false = x.getD w false := by
  rw [stp, getD_snoc, if_pos h]

theorem anyc {f g : ℕ → Bool} : ∀ (L : List ℕ), (∀ c ∈ L, f c = g c) → L.any f = L.any g
  | [], _ => rfl
  | c :: L, h => by
    rw [List.any_cons, List.any_cons, h c (by simp), anyc L fun c' h' => h c' (by simp [h'])]

theorem chain_val (L : List ℕ) : ∀ (x : List Bool) (a : ℕ), (∀ c ∈ L, c < x.length) →
    a < x.length →
    ((chain x.length a L).foldl stp x).getD (last x.length a L) false =
      (x.getD a false || L.any fun c => x.getD c false) := by
  induction L with
  | nil => intro x a _ ha; simp [chain, last]
  | cons c L ih =>
    intro x a hc ha
    have hl : (stp x ⟨GateOp.or, [a, c]⟩).length = x.length + 1 := by simp [stp]
    have hc' : ∀ c' ∈ L, c' < (stp x ⟨GateOp.or, [a, c]⟩).length := fun c' h => by
      have := hc c' (by simp [h]); omega
    have h2 := ih (stp x ⟨GateOp.or, [a, c]⟩) x.length hc' (by omega)
    simp only [chain, last, List.foldl_cons]
    rw [hl] at h2
    have : ∀ c' ∈ L, (stp x ⟨GateOp.or, [a, c]⟩).getD c' false = x.getD c' false :=
      fun c' h => pre_stp _ _ _ (hc c' (by simp [h]))
    rw [h2, anyc L this, stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
    simp [GateOp.eval, Bool.or_assoc]

def ev (x : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => x.getD i false)

theorem lay : ∀ (gs : List Gate) (x : List Bool), (∀ g ∈ gs, ∀ i ∈ g.inputs, i < x.length) →
    gs.foldl stp x = x ++ gs.map (ev x)
  | [], x, _ => by simp
  | g :: gs, x, h => by
    rw [List.foldl_cons, lay gs (stp x g) fun g' hg' i hi => by
      have := h g' (by simp [hg']) i hi; simp [stp]; omega]
    have : gs.map (ev (stp x g)) = gs.map (ev x) := List.map_congr_left fun g' hg' => by
      unfold ev; congr 1
      exact List.map_congr_left fun i hi => pre_stp _ _ _ (h g' (by simp [hg']) i hi)
    rw [this]; simp [stp, ev]

def G1 (n : ℕ) : List Gate := (List.range n).map fun i => ⟨GateOp.or, [n + i, n + (i + 1) % n]⟩
def G2 (n : ℕ) : List Gate := (List.range n).map fun i => ⟨GateOp.and, [i, n + n + i]⟩
def L (n : ℕ) : List ℕ := (List.range (n - 1)).map (n + n + n + 1 + ·)
def X1 {n : ℕ} (u v : Fin n) : List Bool := oneEach u v ++ (G1 n).map (ev (oneEach u v))
def X2 {n : ℕ} (u v : Fin n) : List Bool := X1 u v ++ (G2 n).map (ev (X1 u v))

theorem hx {n : ℕ} (u v : Fin n) : (oneEach u v).length = n + n := by simp [oneEach]
theorem hx1 {n : ℕ} (u v : Fin n) : (X1 u v).length = n + n + n := by simp [X1, G1, hx]
theorem hx2 {n : ℕ} (u v : Fin n) : (X2 u v).length = n + n + n + n := by simp [X2, G2, hx1]

theorem wires_eq {n : ℕ} (u v : Fin n) (ch : List Gate) :
    (G1 n ++ G2 n ++ ch).foldl stp (oneEach u v) = ch.foldl stp (X2 u v) := by
  rw [List.foldl_append, List.foldl_append, lay (G1 n) _ ?_, lay (G2 n) _ ?_]
  · rfl
  · intro g hg i hi
    simp only [G2, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    change i < (X1 u v).length
    rw [hx1]; omega
  · intro g hg i hi
    simp only [G1, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have := Nat.mod_lt (k + 1) (by omega : n > 0)
    rw [hx]; omega

theorem hg {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (X2 u v).getD (n + n + n + i) false = true ↔ (i = u.val ∧ (v.val = i ∨ v.val = (i + 1) % n)) := by
  have e2 : (X2 u v).getD (n + n + n + i) false =
      ((X1 u v).getD i false && (X1 u v).getD (n + n + i) false) := by
    rw [X2, List.getD_append_right _ _ _ _ (by rw [hx1]; omega), hx1]
    simp [G2, ev, GateOp.eval, List.getD_eq_getElem?_getD, hi]
  have e1a : (X1 u v).getD i false = (oneEach u v).getD i false :=
    List.getD_append _ _ _ _ (by rw [hx]; omega)
  have e1b : (X1 u v).getD (n + n + i) false =
      ((oneEach u v).getD (n + i) false || (oneEach u v).getD (n + (i + 1) % n) false) := by
    rw [X1, List.getD_append_right _ _ _ _ (by rw [hx]; omega), hx]
    simp [G1, ev, GateOp.eval, List.getD_eq_getElem?_getD, hi]
  rw [e2, e1a, e1b, Bool.and_eq_true, Bool.or_eq_true, oe, oe, oe]
  have := Nat.mod_lt (i + 1) (by omega : n > 0)
  have := u.2
  have := v.2
  generalize (i + 1) % n = t at *
  omega

theorem main (n : ℕ) (hn : 3 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => decide (v.val = u.val ∨ v.val = (u.val + 1) % n)) (3 * n - 1) := by
  refine ⟨⟨G1 n ++ G2 n ++ chain (n + n + n + n) (n + n + n) (L n), last (n + n + n + n) (n + n + n) (L n)⟩,
    fun g hg => ?_, ?_, fun u v => ?_⟩
  · simp only [List.mem_append, G1, G2, List.mem_map] at hg
    rcases hg with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hg
    · simp
    · simp
    · have := chain_good _ _ _ g hg; simp [this.1, this.2]
  · simp only [Circuit.size, List.length_append, chain_len, G1, G2, L, List.length_map, List.length_range]
    omega
  · have h2 := chain_val (L n) (X2 u v) (n + n + n)
      (fun c hc => by
        simp only [L, List.mem_map, List.mem_range] at hc
        obtain ⟨k, hk, rfl⟩ := hc; rw [hx2]; omega) (by rw [hx2]; omega)
    rw [hx2] at h2
    simp only [Circuit.eval, Circuit.wires]
    change (List.foldl stp _ _).getD _ _ = _
    rw [wires_eq, h2]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨c, hc, h⟩)
      · obtain ⟨h1, h3⟩ := (hg u v 0 (by omega)).1 (by simpa using h)
        rw [← h1]; exact h3
      · simp only [L, List.mem_map, List.mem_range] at hc
        obtain ⟨k, hk, rfl⟩ := hc
        obtain ⟨h1, h3⟩ := (hg u v (k + 1) (by omega)).1
          (by rw [show n + n + n + (k + 1) = n + n + n + 1 + k by omega]; exact h)
        rw [← h1]; exact h3
    · intro h
      by_cases h0 : u.val = 0
      · left
        have := (hg u v 0 (by omega)).2 ⟨h0.symm, by rw [h0] at h; exact h⟩
        simpa using this
      · right
        refine ⟨_, List.mem_map.2 ⟨u.val - 1, List.mem_range.2 (by omega), rfl⟩, ?_⟩
        rw [show n + n + n + 1 + (u.val - 1) = n + n + n + u.val by omega]
        exact (hg u v u.val u.2).2 ⟨rfl, h⟩

end PEqualNP.Outside.L_meta_19185_aux

theorem PEqualNP.Outside.L_meta_19185 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (v.val = u.val ∨ v.val = (u.val + 1) % n)) (3 * n - 1) :=
  PEqualNP.Outside.L_meta_19185_aux.main
