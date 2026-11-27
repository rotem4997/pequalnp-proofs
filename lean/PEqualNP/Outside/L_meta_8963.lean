import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8963_aux

def ev (l : List ℕ) (g : Bool × Fin 32 × Fin 32) : List ℕ := l ++ [if g.1 = true then l.getD g.2.1 0 &&& l.getD g.2.2 0 else l.getD g.2.1 0 ||| l.getD g.2.2 0]

theorem evpre (l : List ℕ) (g : Bool × Fin 32 × Fin 32) (i : ℕ) (hi : i < l.length) : (ev l g).getD i 0 = l.getD i 0 := by
  simp [ev, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem lastAt (l : List ℕ) (g : Bool × Fin 32 × Fin 32) (i : ℕ) (hi : i = l.length) : (ev l g).getD i 0 = (if g.1 = true then l.getD g.2.1 0 &&& l.getD g.2.2 0 else l.getD g.2.1 0 ||| l.getD g.2.2 0) := by
  subst hi
  simp [ev, List.getD_eq_getElem?_getD]

theorem len (gs : List (Bool × Fin 32 × Fin 32)) : ∀ l : List ℕ, (gs.foldl ev l).length = l.length + gs.length := by
  induction gs with
  | nil => intro l; simp
  | cons g gs ih => intro l; simp only [List.foldl_cons, ih, ev, List.length_append, List.length_cons, List.length_nil]; omega

theorem pre (gs : List (Bool × Fin 32 × Fin 32)) : ∀ l : List ℕ, ∀ i, i < l.length → (gs.foldl ev l).getD i 0 = l.getD i 0 := by
  induction gs with
  | nil => intro l i _; simp
  | cons g gs ih =>
    intro l i hi
    rw [List.foldl_cons, ih _ i (by simp [ev]; omega), evpre _ _ _ hi]

theorem ands (L : List (Fin 32 × Fin 32)) : ∀ y : List ℕ, (∀ p ∈ L, (p.1 : ℕ) < y.length ∧ (p.2 : ℕ) < y.length) → ∀ j (hj : j < L.length), ((L.map (fun p => (true, p))).foldl ev y).getD (y.length + j) 0 = y.getD L[j].1 0 &&& y.getD L[j].2 0 := by
  induction L with
  | nil => intro y _ j hj; simp at hj
  | cons p L ih =>
    intro y hy j hj
    rw [List.map_cons, List.foldl_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, pre _ _ _ (by simp [ev]), lastAt _ _ _ rfl]
      simp
    | succ j =>
      have hl : (ev y (true, p)).length = y.length + 1 := by simp [ev]
      have h2 : ∀ q ∈ L, (q.1 : ℕ) < (ev y (true, p)).length ∧ (q.2 : ℕ) < (ev y (true, p)).length := by
        intro q hq
        have := hy q (by simp [hq])
        rw [hl]; omega
      have := ih (ev y (true, p)) h2 j (by simp at hj; omega)
      rw [hl] at this
      rw [show y.length + (j+1) = y.length + 1 + j by omega, this]
      have hjL : j < L.length := by simp at hj; omega
      have hq := hy L[j] (by simp)
      simp only [List.getElem_cons_succ]
      rw [evpre _ _ _ hq.1, evpre _ _ _ hq.2]

def O (W : List ℕ) (t : ℕ) : ℕ := (W.take (t+1)).foldl (fun a b => a ||| b) 0

theorem Otake (W : List ℕ) (t : ℕ) (h : t < W.length) : (W.take (t+1)).foldl (fun a b => a ||| b) 0 = (W.take t).foldl (fun a b => a ||| b) 0 ||| W.getD t 0 := by
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD]

theorem step (W : List ℕ) (n k : ℕ) (hW : W.length = n) (hn : 1 ≤ n) : O W (min k (n-1)) ||| W.getD (min (k+1) (n-1)) 0 = O W (min (k+1) (n-1)) := by
  by_cases hk : k + 1 ≤ n - 1
  · rw [Nat.min_eq_left hk, Nat.min_eq_left (by omega)]
    unfold O
    rw [Otake W (k+1) (by omega)]
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    unfold O
    rw [Otake W (n-1) (by omega), Nat.lor_assoc]
    simp

theorem O0 (W : List ℕ) (h : 0 < W.length) : O W 0 = W.getD 0 0 := by
  unfold O
  rw [Otake W 0 h]
  simp

theorem Ofull (W : List ℕ) (n : ℕ) (hW : W.length = n) (hn : 1 ≤ n) : O W (n-1) = W.foldl (fun a b => a ||| b) 0 := by
  unfold O
  rw [List.take_of_length_le (by omega)]

def gt (b n k : ℕ) : Bool × Fin 32 × Fin 32 := (false, Fin.ofNat 32 (if k = 0 then b else b + n + k - 1), Fin.ofNat 32 (b + min (k+1) (n-1)))

theorem chain (z W : List ℕ) (b n m : ℕ) (hz : z.length = b + n) (hW : W.length = n) (hn : 1 ≤ n) (hm : b + n + m ≤ 32) (hzW : ∀ j < n, z.getD (b + j) 0 = W.getD j 0) : ∀ k, k < m → (((List.range (k+1)).map (gt b n)).foldl ev z).getD (b + n + k) 0 = O W (min (k+1) (n-1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [lastAt _ _ _ (by simp [len, hz])]
    simp only [gt, Bool.false_eq_true, ite_false, ite_true, Fin.val_ofNat, List.range_zero, List.map_nil, List.foldl_nil]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have e1 := hzW 0 (by omega)
    have e2 := hzW (min (0+1) (n-1)) (by omega)
    rw [Nat.add_zero] at e1
    rw [e1, e2, ← O0 W (by omega), ← step W n 0 hW hn, Nat.zero_min]
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [lastAt _ _ _ (by simp [len, hz] <;> omega)]
    simp only [gt, Bool.false_eq_true, ite_false, Fin.val_ofNat, Nat.add_one_ne_zero, ite_false]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [show b + n + (k + 1) - 1 = b + n + k by omega, ih (by omega), pre _ _ _ (by rw [hz]; omega), hzW _ (by omega)]
    exact step W n (k+1) hW hn

end PEqualNP.Outside.L_meta_8963_aux

open PEqualNP.Outside.L_meta_8963_aux in
theorem PEqualNP.Outside.L_meta_8963 : ∀ (x1 : List ℕ) (x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x3 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),   have x4 : List ℕ → Bool × Fin (32 : ℕ) × Fin (32 : ℕ) → List ℕ := fun (x4 : List ℕ) (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x4 ++ [if x5.1 = Bool.true then x4.getD ↑x5.2.1 (0 : ℕ) &&& x4.getD ↑x5.2.2 (0 : ℕ) else x4.getD ↑x5.2.1 (0 : ℕ) ||| x4.getD ↑x5.2.2 (0 : ℕ)];   have x5 : List ℕ := List.foldl x4 x1 x2;   x1.length = (11 : ℕ) → x2.length + (2 : ℕ) * x3.length ≤ (22 : ℕ) → x3 ≠ [] → (∀ (x9 : Fin x2.length), ↑(x2.get x9).2.1 < (11 : ℕ) + ↑x9 ∧ ↑(x2.get x9).2.2 < (11 : ℕ) + ↑x9) → (∀ x10 ∈ x3, ↑x10.1 < (11 : ℕ) + x2.length ∧ ↑x10.2 < (11 : ℕ) + x2.length) → ∃ (x11 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x12 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)), List.ofFn x12 = x2 ++ List.map (fun (x13 : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.true, x13)) x3 ++ x11 ∧ (∀ x13 ∈ x11, x13.1 = Bool.false) ∧ (∀ (x13 : Fin (21 : ℕ)), ↑(x12 x13).2.1 < (11 : ℕ) + ↑x13 ∧ ↑(x12 x13).2.2 < (11 : ℕ) + ↑x13) ∧ (List.foldl x4 x1 (List.ofFn x12)).getD (31 : ℕ) (0 : ℕ) = List.foldl (fun (x13 : ℕ) (x14 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x13 ||| x5.getD ↑x14.1 (0 : ℕ) &&& x5.getD ↑x14.2 (0 : ℕ)) (0 : ℕ) x3 := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5
  have hx4 : x4 = ev := rfl
  have hn : 1 ≤ x3.length := by
    cases x3 with
    | nil => exact absurd rfl h3
    | cons _ _ => simp
  let m := 21 - x2.length - x3.length
  let A := x3.map (fun p => ((true : Bool), p))
  let x11 := (List.range m).map (gt (11 + x2.length) x3.length)
  let L := x2 ++ A ++ x11
  have hL : L.length = 21 := by simp [L, A, x11, m]; omega
  have hof : List.ofFn (fun i : Fin 21 => L.getD i (false, 0, 0)) = L := by
    apply List.ext_getElem (by simp [hL])
    intro i ha hb
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hb
  refine ⟨x11, fun i => L.getD i (false, 0, 0), hof, ?_, ?_, ?_⟩
  · intro q hq
    simp only [x11, List.mem_map] at hq
    obtain ⟨k, _, rfl⟩ := hq
    rfl
  · intro i
    have hi : (i : ℕ) < L.length := by omega
    simp only [List.getD_eq_getElem _ _ hi]
    simp only [L, A, x11, List.getElem_append, List.length_append, List.length_map, List.length_range]
    split_ifs with ha hb
    · exact h4 ⟨i, hb⟩
    · simp only [List.getElem_map]
      have := h5 x3[(i : ℕ) - x2.length] (List.getElem_mem _)
      omega
    · simp only [List.getElem_map, List.getElem_range, gt, Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (by split_ifs <;> omega), Nat.mod_eq_of_lt (by omega)]
      split_ifs <;> omega
  · rw [hof, hx4]
    have hy : x5 = List.foldl ev x1 x2 := rfl
    rw [hy]
    simp only [L, List.foldl_append]
    have hylen : (List.foldl ev x1 x2).length = 11 + x2.length := by rw [len]; omega
    generalize List.foldl ev x1 x2 = y at hylen ⊢
    have hyb : ∀ p ∈ x3, (p.1 : ℕ) < y.length ∧ (p.2 : ℕ) < y.length := by
      intro p hp
      have := h5 p hp
      omega
    have hzlen : (List.foldl ev y A).length = 11 + x2.length + x3.length := by
      rw [len]; simp [A, hylen]
    generalize hz : List.foldl ev y A = z at hzlen ⊢
    let W := x3.map (fun p => y.getD p.1 0 &&& y.getD p.2 0)
    have hW : W.length = x3.length := by simp [W]
    have hzW : ∀ j < x3.length, z.getD (11 + x2.length + j) 0 = W.getD j 0 := by
      intro j hj
      rw [← hz, ← hylen, ands x3 y hyb j hj]
      simp [W, List.getD_eq_getElem?_getD, hj]
    have hR : List.foldl (fun (x13 : ℕ) (x14 : Fin 32 × Fin 32) => x13 ||| y.getD x14.1 0 &&& y.getD x14.2 0) 0 x3 = W.foldl (fun a b => a ||| b) 0 := by
      simp only [W, List.foldl_map]
    rw [hR, ← Ofull W x3.length hW hn]
    by_cases hm0 : m = 0
    · have e : x11 = [] := by simp [x11, hm0]
      rw [e, List.foldl_nil, show (31 : ℕ) = 11 + x2.length + 0 by omega, hzW 0 (by omega), show x3.length - 1 = 0 by omega, O0 W (by omega)]
    · have e : x11 = (List.range (m - 1 + 1)).map (gt (11 + x2.length) x3.length) := by
        simp only [x11]
        rw [Nat.sub_add_cancel (by omega)]
      rw [e, show (31 : ℕ) = 11 + x2.length + x3.length + (m - 1) by omega]
      rw [chain z W (11 + x2.length) x3.length m hzlen hW hn (by omega) hzW (m - 1) (by omega)]
      rw [Nat.min_eq_right (by omega)]
