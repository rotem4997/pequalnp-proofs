import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6967

open PEqualNP.CircuitLowerBounds

theorem any_iff (l : List ℕ) (a b : ℕ) :
    (l.any fun x => x == a || x == b) = true ↔ (a ∈ l ∨ b ∈ l) := by
  simp only [List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h | h)
    · exact ⟨a, h, Or.inl rfl⟩
    · exact ⟨b, h, Or.inr rfl⟩

theorem short_one {n : ℕ} (l : List ℕ) (hl : l.length ≤ 2) (v : Fin n) (T : Finset (Fin n))
    (hv : v ∉ T) (hvl : (v : ℕ) ∈ l) :
    (T.filter fun u : Fin n => (u : ℕ) ∈ l).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have hav : (a : ℕ) ≠ (v : ℕ) := fun h => hv (by rw [← Fin.ext h]; exact ha.1)
  have hbv : (b : ℕ) ≠ (v : ℕ) := fun h => hv (by rw [← Fin.ext h]; exact hb.1)
  have ha2 := ha.2
  have hb2 := hb.2
  apply Fin.ext
  match l, hl with
  | [], _ => simp at hvl
  | [p], _ =>
    simp only [List.mem_singleton] at hvl ha2 hb2
    omega
  | [p, q], _ =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hvl ha2 hb2
    omega
  | _ :: _ :: _ :: _, h => simp at h

theorem per_gate {n : ℕ} (l : List ℕ) (hl : l.length ≤ 2) (v : Fin n) (T : Finset (Fin n))
    (hv : v ∉ T) :
    ∑ u ∈ T, ((if l.contains (u : ℕ) = true then 1 else 0) + (if l.contains (v : ℕ) = true then 1 else 0))
      ≤ ∑ u ∈ T, (if (l.any fun x => x == (u : ℕ) || x == (v : ℕ)) = true then 1 else 0)
        + (if l.contains (v : ℕ) = true then 1 else 0) := by
  by_cases hvl : (v : ℕ) ∈ l
  · have h1 : ∑ u ∈ T, (if (l.any fun x => x == (u : ℕ) || x == (v : ℕ)) = true then 1 else 0) = T.card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro u _
      rw [if_pos ((any_iff l _ _).mpr (Or.inr hvl))]
    have h2 : ∑ u ∈ T, (if l.contains (u : ℕ) = true then 1 else 0) ≤ 1 := by
      have := short_one l hl v T hv hvl
      rw [Finset.card_filter] at this
      simpa [List.contains_iff_mem] using this
    have h3 : l.contains (v : ℕ) = true := by simpa using hvl
    rw [Finset.sum_add_distrib, h1, if_pos h3]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    omega
  · have h3 : ¬ (l.contains (v : ℕ) = true) := by simpa using hvl
    rw [if_neg h3, add_zero]
    apply Finset.sum_le_sum
    intro u _
    rw [add_zero]
    by_cases hu : (u : ℕ) ∈ l
    · rw [if_pos ((any_iff l _ _).mpr (Or.inl hu))]
      split_ifs <;> omega
    · have h4 : ¬ (l.contains (u : ℕ) = true) := by simpa using hu
      rw [if_neg h4]
      exact Nat.zero_le _

theorem key {n : ℕ} (f : Gate → List ℕ) (hf : ∀ g, (f g).length ≤ 2) (v : Fin n)
    (T : Finset (Fin n)) (hv : v ∉ T) (gs : List Gate) :
    ∑ u ∈ T, (gs.countP (fun g => (f g).contains (u : ℕ)) + gs.countP (fun g => (f g).contains (v : ℕ)))
      ≤ ∑ u ∈ T, gs.countP (fun g => (f g).any fun x => x == (u : ℕ) || x == (v : ℕ))
        + gs.countP (fun g => (f g).contains (v : ℕ)) := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have hp := per_gate (f g) (hf g) v T hv
    simp only [List.countP_cons]
    simp only [Finset.sum_add_distrib] at ih hp ⊢
    omega

theorem take_len (b : Bool) (l : List ℕ) : (List.take (bif b then 1 else 2) l).length ≤ 2 := by
  cases b <;> simp [List.length_take] <;> omega

theorem arith (t c m : ℕ) (N : ℕ) (h : t * (m + c) ≤ t * 7 + c) : (t - 1) * c + t * m ≤ t * 7 := by
  cases t with
  | zero => simp
  | succ s =>
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard ≤ 3)
    (h7 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      List.countP (fun g : Gate => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).any
        fun x => x == (a : ℕ) || x == (b : ℕ)) C.gates ≤ 7)
    (v : Fin n) (S : Finset (Fin n)) (m : ℕ)
    (hm : ∀ u ∈ S, m ≤ List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (u : ℕ)) C.gates) :
    ∃ t : ℕ, S.card ≤ t + 4 ∧ (t - 1) * List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (v : ℕ)) C.gates + t * m ≤ t * 7 := by
  classical
  let T : Finset (Fin n) := S.filter fun u => u ≠ v ∧ ¬ G.Adj u v
  let Nb : Finset (Fin n) := Finset.univ.filter fun u => G.Adj v u
  have hNb : Nb.card ≤ 3 := by
    have e : G.neighborSet v = (Nb : Set (Fin n)) := by
      ext u; simp [Nb]
    have := hdeg v
    rw [e, Set.ncard_coe_finset] at this
    exact this
  have hS : S ⊆ T ∪ (Nb ∪ {v}) := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, T, Nb]
    by_cases h1 : u = v
    · exact Or.inr (Or.inr h1)
    · by_cases h2 : G.Adj u v
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inl ⟨hu, h1, h2⟩
  have hcard : S.card ≤ T.card + 4 := by
    have h1 := Finset.card_le_card hS
    have h2 := Finset.card_union_le T (Nb ∪ {v})
    have h3 := Finset.card_union_le Nb {v}
    have h4 : ({v} : Finset (Fin n)).card = 1 := Finset.card_singleton v
    omega
  have hvT : v ∉ T := by simp [T]
  refine ⟨T.card, hcard, ?_⟩
  have hk := key (fun g : Gate => List.take (bif g.op.eval [false] then 1 else 2) g.inputs)
    (fun g => take_len _ _) v T hvT C.gates
  apply arith _ _ _ 0
  have hl : T.card * (m + List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (v : ℕ)) C.gates)
      ≤ ∑ u ∈ T, (C.gates.countP (fun g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (u : ℕ))
        + C.gates.countP (fun g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (v : ℕ))) := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro u hu
    have := hm u (Finset.mem_filter.mp hu).1
    omega
  have hr : ∑ u ∈ T, C.gates.countP (fun g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).any
      fun x => x == (u : ℕ) || x == (v : ℕ)) ≤ T.card * 7 := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    exact h7 u v h.1 h.2
  omega

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (hn : 12 ≤ n)
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard ≤ 3)
    (h1 : ∀ u : Fin n, 1 ≤ List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (u : ℕ)) C.gates)
    (h7 : ∀ a b : Fin n, a ≠ b → ¬ G.Adj a b →
      List.countP (fun g : Gate => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).any
        fun x => x == (a : ℕ) || x == (b : ℕ)) C.gates ≤ 7) :
    (∀ v : Fin n, List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (v : ℕ)) C.gates ≤ 6) ∧
    ∀ S : Finset (Fin n), (∀ u ∈ S, 4 ≤ List.countP (fun g : Gate =>
      (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains (u : ℕ)) C.gates) → S.card ≤ 8 := by
  constructor
  · intro v
    obtain ⟨t, ht, hb⟩ := bound G C hdeg h7 v Finset.univ 1 (fun u _ => h1 u)
    rw [Finset.card_univ, Fintype.card_fin] at ht
    by_contra hc
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
    have e : s + 8 - 1 = s + 7 := by omega
    rw [e] at hb
    nlinarith
  · intro S hS
    by_contra hc
    obtain ⟨v, hv⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨t, ht, hb⟩ := bound G C hdeg h7 v S 4 hS
    have h4 := hS v hv
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 5 := ⟨t - 5, by omega⟩
    have e : s + 5 - 1 = s + 4 := by omega
    rw [e] at hb
    nlinarith

end PEqualNP.Outside.L_meta_6967

theorem PEqualNP.Outside.L_meta_6967 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (12 : ℕ) ≤ x1 →     (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard ≤ (3 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;         have x8 : Fin x1 → ℕ := fun (x8 : Fin x1) => List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).contains ↑x8) x3.gates;         (∀ (x9 : Fin x1), (1 : ℕ) ≤ x8 x9) → (∀ (x10 x11 : Fin x1), x10 ≠ x11 → ¬x2.Adj x10 x11 → List.countP (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x14).any fun (x15 : ℕ) => x15 == ↑x10 || x15 == ↑x11) x3.gates ≤ (7 : ℕ)) → (∀ (x11 : Fin x1), x8 x11 ≤ (6 : ℕ)) ∧ ∀ (x11 : Finset (Fin x1)), (∀ x12 ∈ x11, (4 : ℕ) ≤ x8 x12) → x11.card ≤ (8 : ℕ) := by
  intro n G C hn hdeg _
  exact PEqualNP.Outside.L_meta_6967.main n G C hn hdeg
