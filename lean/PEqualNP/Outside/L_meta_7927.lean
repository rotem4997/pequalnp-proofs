import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7927

open PEqualNP.Defs.LratEncoding

theorem litP (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  have h1 : (2 * v + 2) / 2 = v + 1 := by omega
  have h2 : (2 * v + 2) % 2 = 0 := by omega
  simp only [litVal, P, h1, h2]
  cases a (v + 1) <;> rfl

theorem litQ (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  have h1 : (2 * v + 3) / 2 = v + 1 := by omega
  have h2 : (2 * v + 3) % 2 = 1 := by omega
  simp only [litVal, Q, h1, h2]
  cases a (v + 1) <;> rfl

theorem litL (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> cases h : a (v + 1) <;> simp [L, litP, litQ, h]

theorem gen (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hsat : FormulaSat (enc2 n s g rows)) :
    ∃ (x4 : ℕ → ℕ → Bool),
      have x5 : ℕ → ℕ → ℕ → Bool := fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else Bool.false;
      (∀ x6 < s, (∀ x8 ∈ rows, x4 x6 x8 = Bool.true) ∨ ∃ (x8 : ℕ) (x9 : ℕ), (∀ x10 ∈ rows, x4 x6 x10 = (x5 x6 x8 x10 && x5 x6 x9 x10)) ∨ ∀ x10 ∈ rows, x4 x6 x10 = (x5 x6 x8 x10 || x5 x6 x9 x10)) ∧ ∃ (x6 : ℕ), ∀ x7 ∈ rows, x5 s x6 x7 = g x7 := by
  obtain ⟨a, ha⟩ := hsat
  have mem : ∀ c, (c ∈ fOp n s ∨ c ∈ fSrcAlo n s ∨ c ∈ fSrcEq n s rows ∨ c ∈ fGate n s rows ∨
      c ∈ fOutAlo n s ∨ c ∈ fOutEq n s g rows) → ClauseSat a c := by
    intro c hc
    apply ha
    simp only [enc2, enc, List.mem_append]
    tauto
  have hOp : ∀ j < s, a (ix n s 0 j 0 + 1) = true ∨ a (ix n s 0 j 1 + 1) = true ∨
      a (ix n s 0 j 2 + 1) = true := by
    intro j hj
    have := mem [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]
      (Or.inl (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
    simpa [ClauseSat, litP] using this
  have hAlo : ∀ e ∈ [1, 2], ∀ j < s, ∃ k < n + j + 1, a (ix n s e j k + 1) = true := by
    intro e he j hj
    obtain ⟨l, hl, hv⟩ := mem ((List.range (n + j + 1)).map fun k => P (ix n s e j k))
      (Or.inr (Or.inl (List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    exact ⟨k, List.mem_range.1 hk, by rw [litP] at hv; exact hv⟩
  have hSrc : ∀ e ∈ [1, 2], ∀ j < s, ∀ r ∈ rows, ∀ k < n + j + 1, ∀ c ∈ srcEq n s e j k r,
      ClauseSat a c :=
    fun e he j hj r hr k hk c hc => mem c (Or.inr (Or.inr (Or.inl (List.mem_flatMap.2 ⟨e, he,
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr,
        List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hc⟩⟩⟩⟩))))
  have hG : ∀ j < s, ∀ r ∈ rows, ∀ c ∈ gateCl n s j r, ClauseSat a c :=
    fun j hj r hr c hc => mem c (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatMap.2 ⟨j,
      List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr, hc⟩⟩)))))
  have hOA : ∃ k < n + s + 1, a (ix n s 6 0 k + 1) = true := by
    obtain ⟨l, hl, hv⟩ := mem ((List.range (n + s + 1)).map fun k => P (ix n s 6 0 k))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_singleton.2 rfl))))))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    exact ⟨k, List.mem_range.1 hk, by rw [litP] at hv; exact hv⟩
  have hOE : ∀ r ∈ rows, ∀ k < n + s + 1, ∀ c ∈ outEq n s g k r, ClauseSat a c :=
    fun r hr k hk c hc => mem c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_flatMap.2 ⟨r,
      hr, List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hc⟩⟩))))))
  have src : ∀ e ∈ [1, 2], ∀ j < s, ∀ k < n + j + 1, a (ix n s e j k + 1) = true → ∀ r ∈ rows,
      a (ix n s (e + 3) j r + 1) = (if k < n then r.testBit k else if k < n + j then
        a (ix n s 3 (k - n) r + 1) else false) := by
    intro e he j hj k hk hsel r hr
    have H := hSrc e he j hj r hr k hk
    by_cases h1 : k < n
    · have := H [Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)] (by simp [srcEq, h1])
      simp [ClauseSat, litQ, litL, hsel] at this
      rw [if_pos h1]
      exact this
    · by_cases h2 : k < n + j
      · have c1 := H [Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)]
          (by simp [srcEq, h1, h2])
        have c2 := H [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]
          (by simp [srcEq, h1, h2])
        simp [ClauseSat, litQ, litP, hsel] at c1 c2
        rw [if_neg h1, if_pos h2]
        revert c1 c2
        cases a (ix n s (e + 3) j r + 1) <;> cases a (ix n s 3 (k - n) r + 1) <;> simp
      · have := H [Q (ix n s e j k), Q (ix n s (e + 3) j r)] (by simp [srcEq, h1, h2])
        simp [ClauseSat, litQ, hsel] at this
        rw [if_neg h1, if_neg h2]
        exact this
  refine ⟨fun j r => a (ix n s 3 j r + 1), ?_⟩
  dsimp only
  refine ⟨fun j hj => ?_, ?_⟩
  · obtain ⟨k1, hk1, hs1⟩ := hAlo 1 (by simp) j hj
    obtain ⟨k2, hk2, hs2⟩ := hAlo 2 (by simp) j hj
    have e1 : ∀ r ∈ rows, a (ix n s 4 j r + 1) = (if k1 < n then r.testBit k1 else
        if k1 < n + j then a (ix n s 3 (k1 - n) r + 1) else false) :=
      src 1 (by simp) j hj k1 hk1 hs1
    have e2 : ∀ r ∈ rows, a (ix n s 5 j r + 1) = (if k2 < n then r.testBit k2 else
        if k2 < n + j then a (ix n s 3 (k2 - n) r + 1) else false) :=
      src 2 (by simp) j hj k2 hk2 hs2
    rcases hOp j hj with hop | hop | hop
    · right
      refine ⟨k1, k2, Or.inl fun r hr => ?_⟩
      have key : a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) && a (ix n s 5 j r + 1)) := by
        have hc := hG j hj r hr
        simp [gateCl, ClauseSat, litP, litQ, hop] at hc
        revert hc
        cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
          cases a (ix n s 5 j r + 1) <;> simp
      rw [key, e1 r hr, e2 r hr]
    · right
      refine ⟨k1, k2, Or.inr fun r hr => ?_⟩
      have key : a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) || a (ix n s 5 j r + 1)) := by
        have hc := hG j hj r hr
        simp [gateCl, ClauseSat, litP, litQ, hop] at hc
        revert hc
        cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
          cases a (ix n s 5 j r + 1) <;> simp
      rw [key, e1 r hr, e2 r hr]
    · left
      intro r hr
      have hc := hG j hj r hr
      simp [gateCl, ClauseSat, litP, litQ, hop] at hc
      revert hc
      cases a (ix n s 3 j r + 1) <;> simp
  · obtain ⟨k, hk, hsel⟩ := hOA
    refine ⟨k, fun r hr => ?_⟩
    have H := hOE r hr k hk
    by_cases h1 : k < n
    · rw [if_pos h1]
      by_contra h2
      have := H [Q (ix n s 6 0 k)] (by simp [outEq, h1, h2])
      simp [ClauseSat, litQ, hsel] at this
    · rw [if_neg h1]
      by_cases h2 : k < n + s
      · rw [if_pos h2]
        have := H [Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)] (by simp [outEq, h1, h2])
        simpa [ClauseSat, litQ, litL, hsel] using this
      · rw [if_neg h2]
        cases hg : g r
        · rfl
        · have := H [Q (ix n s 6 0 k)] (by simp [outEq, h1, h2, hg])
          simp [ClauseSat, litQ, hsel] at this

end PEqualNP.Outside.L_meta_7927

theorem PEqualNP.Outside.L_meta_7927 : ∀ (x1 : ℕ → Bool) (x2 : List ℕ),   PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (14 : ℕ) (26 : ℕ) x1 x2) →     ∃ (x4 : ℕ → ℕ → Bool),       have x5 : ℕ → ℕ → ℕ → Bool := fun (x5 x6 x7 : ℕ) => if x6 < (14 : ℕ) then x7.testBit x6 else if x6 < (14 : ℕ) + x5 then x4 (x6 - (14 : ℕ)) x7 else Bool.false;       (∀ x6 < (26 : ℕ), (∀ x8 ∈ x2, x4 x6 x8 = Bool.true) ∨ ∃ (x8 : ℕ) (x9 : ℕ), (∀ x10 ∈ x2, x4 x6 x10 = (x5 x6 x8 x10 && x5 x6 x9 x10)) ∨ ∀ x10 ∈ x2, x4 x6 x10 = (x5 x6 x8 x10 || x5 x6 x9 x10)) ∧ ∃ (x6 : ℕ), ∀ x7 ∈ x2, x5 (26 : ℕ) x6 x7 = x1 x7 := by
  intro x1 x2 h
  exact PEqualNP.Outside.L_meta_7927.gen 14 26 x1 x2 h
