import PEqualNP.MetaComplexity.Helpers.EdgeFnPlan

/-!
# The model layer of the edge function plan: pieces C1 and C2

Piece C1 (`stmtRD`): deleting gate `p` and letting its readers read an earlier wire `a` keeps
the list clean, removes one gate, keeps every earlier wire, and where gate `p` agrees with `a`
keeps every wire up to the renaming `rd`. The proof is a strong induction on the wire index
with `vl_input`, `vl_gate` and `vl_beyond`.

Piece C2: facts on the tail potential `TailGE` and on least lists. From the plan: the tail is
at most the length (`TailGE.le`), a gate that is not a tail gate lies before the tail
(`TailGE.lt_of_not`), the tail of a move "delete and redirect, then append" grows by the number
of appended gates (`tailGE_rdel_app`), and a clean list of least length is `Least` (`least_of`).
Added here: `TailGE.zero`, `TailGE.mono`, and the wire facts `vl_append_lt`, `rdel_get_lt`,
`rdel_get_ge`, `rdel_length`.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-! ## The shape of `rdel` (added) -/

theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega

theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

/-- Wires of a prefix keep their values when gates are appended (added). -/
theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]

/-! ## Piece C1 -/

theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]

theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]

theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩

theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)

theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]

/-- Piece C1, exactly as stated in the plan module. -/
theorem stmtRD : StmtRD := by
  intro N gs p a hcl hp ha
  exact ⟨rdel_clean N p a gs hcl hp ha, rdel_length N p a gs hp,
    fun x w hw => rdel_prefix N p a gs hcl hp ha x w hw,
    fun x hx w => rdel_all N p a gs hcl hp ha x hx w⟩

/-! ## Piece C2: the tail potential -/

/-- Added: every list has tail at least zero. -/
theorem TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩

/-- Added: a tail of length `t` contains every shorter tail. -/
theorem TailGE.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t t' : ℕ}
    (h : TailGE N F gs t) (ht : t' ≤ t) : TailGE N F gs t' :=
  ⟨le_trans ht h.1, fun j h1 h2 => h.2 j (by omega) h2⟩

/-- From the plan: the tail is at most the length. -/
theorem TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1

/-- From the plan: a position that is not a tail gate lies before the tail. -/
theorem TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)

/-- From the plan: the tail of a move. Gate `p` lies before a tail of length `t`; on a set `S`
of inputs gate `p` agrees with wire `a`, and off `S` the function is true; the appended gates
are tail gates of the new list. Then the new list has tail `t + new.length`. -/
theorem tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx

/-- From the plan: a clean list for `F` no longer than a least one is least. -/
theorem least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩

end PEqualNP.MetaComplexity.EdgeFn
