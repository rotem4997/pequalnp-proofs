import PEqualNP.MetaComplexity.Helpers.RunQAB2

/-!
# Theorem QA, cases B1 and B2: agreement and kept-gate bricks

* `qa_agreeF`, `qa_gate_agree`: agreement of two points outside a bad set of wires, gate by
  gate (a gate whose earlier read wires are all good agrees).
* `qa_kept_read`: a kept gate of `C` reading an earlier wire `a` becomes, in `qaL`, a gate with
  the same operation reading the image of `a`.
* `qa_H_const`: `x_last OR H` is not constantly true when `H` is not constant.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc.Removal

theorem qa_agreeF (N : ℕ) (C : Circuit) (x x' : Fin N → Bool) (Bad : ℕ → Prop)
    (hx : ∀ i : Fin N, ¬ Bad i.val → x i = x' i)
    (hg : ∀ j : Fin C.gates.length, ¬ Bad (N + j.val) →
      (∀ i, i < N + j.val → ¬ Bad i →
        (wiresFrom C.gates (List.ofFn x)).getD i false =
          (wiresFrom C.gates (List.ofFn x')).getD i false) →
      (wiresFrom C.gates (List.ofFn x)).getD (N + j.val) false =
        (wiresFrom C.gates (List.ofFn x')).getD (N + j.val) false) :
    ∀ t, ¬ Bad t → (wiresFrom C.gates (List.ofFn x)).getD t false =
      (wiresFrom C.gates (List.ofFn x')).getD t false := by
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  have hlen' : (List.ofFn x').length = N := List.length_ofFn
  refine qa_agree C.gates (List.ofFn x) (List.ofFn x') (by simp) Bad ?_ ?_
  · intro i hi hB
    rw [hlen] at hi
    rw [qa_ofFn_getD _ _ hi, qa_ofFn_getD _ _ hi]
    exact hx ⟨i, hi⟩ hB
  · intro j g hj hB ih
    have hjl : j < C.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; exact absurd hj (by simp)
    rw [← qa_val_gate C.gates (List.ofFn x) j g hj]
    have e2 := qa_val_gate C.gates (List.ofFn x') j g hj
    rw [hlen'] at e2
    rw [hlen] at hB ih ⊢
    rw [← e2]
    exact hg ⟨j, hjl⟩ hB ih

theorem qa_gate_agree (N : ℕ) (C : Circuit) (x x' : Fin N → Bool) (Bad : ℕ → Prop)
    (j : Fin C.gates.length)
    (hread : ∀ a, qaReads (C.gates.get j) a → a < N + j.val → ¬ Bad a)
    (ih : ∀ i, i < N + j.val → ¬ Bad i →
        (wiresFrom C.gates (List.ofFn x)).getD i false =
          (wiresFrom C.gates (List.ofFn x')).getD i false) :
    (wiresFrom C.gates (List.ofFn x)).getD (N + j.val) false =
      (wiresFrom C.gates (List.ofFn x')).getD (N + j.val) false := by
  rw [qa_val_fin N C x j, qa_val_fin N C x' j]
  apply qa_eval_congr
  intro a ha
  by_cases hlt : a < N + j.val
  · rw [if_pos hlt, if_pos hlt]
    exact ih a hlt (hread a ha hlt)
  · rw [if_neg hlt, if_neg hlt]

theorem qa_kept_read (N : ℕ) (C : Circuit) (g1 g2 o2 jM u1 u2 z : ℕ) (q : Fin C.gates.length)
    (hqS : q.val ∉ qaS g1 g2 o2 jM) :
    ∃ hq' : cnt (qaS g1 g2 o2 jM) q.val < (qaL N C g1 g2 o2 jM u1 u2 z).gates.length,
      ((qaL N C g1 g2 o2 jM u1 u2 z).gates.get ⟨_, hq'⟩).op = (C.gates.get q).op ∧
      ((qaL N C g1 g2 o2 jM u1 u2 z).gates.get ⟨_, hq'⟩).inputs =
        (C.gates.get q).inputs.map (fun i => qaRho N (qaS g1 g2 o2 jM)
          (qaTgt g1 g2 jM u1 u2 z) (N + cnt (qaS g1 g2 o2 jM) C.gates.length)
          (if i < N + q.val then i else N + C.gates.length)) ∧
      (∀ a, qaReads (C.gates.get q) a → a < N + q.val →
        qaReads ((qaL N C g1 g2 o2 jM u1 u2 z).gates.get ⟨_, hq'⟩)
          (qaRho N (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
            (N + cnt (qaS g1 g2 o2 jM) C.gates.length) a)) := by
  have h := qa_L_get N C g1 g2 o2 jM u1 u2 z q.val q.isLt hqS
  have hlt : cnt (qaS g1 g2 o2 jM) q.val < (qaL N C g1 g2 o2 jM u1 u2 z).gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  refine ⟨hlt, ?_⟩
  rw [List.getElem?_eq_getElem hlt] at h
  have h' := Option.some.inj h
  have hg : C.gates.getD q.val g0 = C.gates.get q := by
    simp [List.getD_eq_getElem?_getD]
  rw [hg] at h'
  simp only [List.get_eq_getElem]
  rw [h']
  refine ⟨rfl, rfl, ?_⟩
  intro a ha hlt'
  rcases ha with ⟨hn, hh⟩ | ⟨hn, hm⟩
  · left
    refine ⟨hn, ?_⟩
    show ((C.gates.get q).inputs.map _).head? = _
    simp only [List.get_eq_getElem] at hh ⊢
    rw [List.head?_map, hh]
    simp [hlt']
  · right
    refine ⟨hn, ?_⟩
    show _ ∈ (C.gates.get q).inputs.map _
    exact List.mem_map.mpr ⟨a, hm, by simp [hlt']⟩

theorem qa_H_const (n : ℕ) (H : (Fin n → Bool) → Bool) (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (h : ∀ x : Fin (n + 1) → Bool, (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) = true) :
    False := by
  obtain ⟨y, y', hy⟩ := hH
  have h1 := h (Fin.snoc y false)
  have h2 := h (Fin.snoc y' false)
  simp at h1 h2
  exact hy (by rw [h1, h2])

end PEqualNP.MetaComplexity.Helpers.RunFour2
