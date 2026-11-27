import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8967

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i h
    rw [inCone_iff n C i k hk] at h
    obtain ⟨w, _, hn, hlt, h⟩ := h
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma inCone_lt_bound (n : ℕ) (C : Circuit) (k m : ℕ) (hk : k < C.gates.length)
    (hb : ∀ w ∈ (gateAt C k).inputs, w < n + m) (i : ℕ) (h : InCone n C i k) : i < m := by
  rw [inCone_iff n C i k hk] at h
  obtain ⟨w, hw, hn, hlt, h⟩ := h
  have := hb w hw
  rcases h with h | h
  · omega
  · have := inCone_lt n C (w - n) (by omega) i h
    omega

lemma main (x1 x2 : List (Bool × Fin 32 × Fin 32)) (x3 : List (Fin 32 × Fin 32))
    (x4 : Fin 21 → Bool × Fin 32 × Fin 32)
    (hEq : List.ofFn x4 = x1 ++ List.map (fun (x5 : Fin 32 × Fin 32) => (true, x5)) x3 ++ x2)
    (hx2 : ∀ x6 ∈ x2, x6.1 = false)
    (hx3 : ∀ x8 ∈ x3, (x8.1 : ℕ) < 11 + x1.length ∧ (x8.2 : ℕ) < 11 + x1.length)
    (C : Circuit)
    (hC : C.gates = List.map (fun (x9 : Bool × Fin 32 × Fin 32) =>
      ({ op := if x9.1 = true then GateOp.and else GateOp.or,
         inputs := [(x9.2.1 : ℕ), (x9.2.2 : ℕ)] } : Gate)) (List.ofFn x4))
    (x10 x11 : Fin 21) (hlen : x1.length ≤ (x10 : ℕ)) (hand : (x4 x11).1 = true) :
    ¬ InCone 11 C x10 x11 := by
  intro hc
  have hlen21 : C.gates.length = 21 := by rw [hC]; simp
  have hk : (x11 : ℕ) < C.gates.length := by rw [hlen21]; exact x11.isLt
  have hin : (gateAt C x11).inputs = [((x4 x11).2.1 : ℕ), ((x4 x11).2.2 : ℕ)] := by
    rw [gateAt_eq C x11 hk]
    simp only [hC, List.getElem_map, List.getElem_ofFn, Fin.eta]
  by_cases h1 : (x11 : ℕ) < x1.length
  · have := inCone_lt 11 C x11 hk x10 hc
    omega
  · have hmem : x4 x11 ∈ List.map (fun (x5 : Fin 32 × Fin 32) => (true, x5)) x3 ++ x2 := by
      have h0 : (List.ofFn x4)[(x11 : ℕ)]? = some (x4 x11) := by
        simp only [List.getElem?_ofFn, x11.isLt, dite_true, Fin.eta]
      rw [hEq, List.append_assoc, List.getElem?_append_right (by omega)] at h0
      exact List.mem_iff_getElem?.mpr ⟨_, h0⟩
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
      have hb := hx3 p hp
      have hbound : ∀ w ∈ (gateAt C x11).inputs, w < 11 + x1.length := by
        intro w hw
        rw [hin, ← hpe] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with hw | hw
        · rw [hw]; exact hb.1
        · rw [hw]; exact hb.2
      have := inCone_lt_bound 11 C x11 x1.length hk hbound x10 hc
      omega
    · have := hx2 _ h
      rw [this] at hand
      exact absurd hand (by decide)

end PEqualNP.Outside.L_meta_8967

theorem PEqualNP.Outside.L_meta_8967 : ∀ (x1 x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x3 : List (Fin (32 : ℕ) × Fin (32 : ℕ))) (x4 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   List.ofFn x4 = x1 ++ List.map (fun (x5 : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.true, x5)) x3 ++ x2 →     (∀ x6 ∈ x2, x6.1 = Bool.false) →       (∀ (x7 : Fin (21 : ℕ)), ↑(x4 x7).2.1 < (11 : ℕ) + ↑x7 ∧ ↑(x4 x7).2.2 < (11 : ℕ) + ↑x7) →         (∀ x8 ∈ x3, ↑x8.1 < (11 : ℕ) + x1.length ∧ ↑x8.2 < (11 : ℕ) + x1.length) →           have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x9 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x9.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x9.2.1, ↑x9.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x4), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };           ∀ (x10 x11 : Fin (21 : ℕ)), x1.length ≤ ↑x10 → (x4 x11).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x9 ↑x10 ↑x11 := by
  intro x1 x2 x3 x4 hEq hx2 _ hx3
  exact fun x10 x11 hlen hand =>
    PEqualNP.Outside.L_meta_8967.main x1 x2 x3 x4 hEq hx2 hx3 _ rfl x10 x11 hlen hand
