import PEqualNP.MetaComplexity.Helpers.RunQATools
import PEqualNP.MetaComplexity.Helpers.LocRemoval

/-!
# Theorem QA, step C1: the removal of o2, M, g1, g2 at x_q2 := 1, x_e := 0

Root circuits. From the shape hypotheses of the row (no leastness used), the gates `o2`
(constant `1` there), `M` (alias of `z`), `g1`, `g2` (aliases of `u1`, `u2`) are removed and
the circuit `qaL` that is left, with `|C| - 4` gates, computes the double restriction on all
inputs. The wire map `qaRho` sends an input to itself, a kept gate `p` to `N + cnt p`, an alias
to the image of its target, and the orphan `o2` (and an alias of a later wire) to the first
wire past the new list, which reads `false`. Before the map, every listed wire at or after the
gate's own position is sent to the wire `N + |C|` (it reads `false` there too): `qaNorm`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc.Removal

/-- The wire map of the removal, with fallback wire `d`. -/
def qaRho (N : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (d : ℕ) (j : ℕ) : ℕ :=
  if j < N then j
  else if j - N ∈ S then
    match tgt (j - N) with
    | some i => if _h : i < j then qaRho N S tgt d i else d
    | none => d
  else N + cnt S (j - N)
termination_by j

/-- Every listed wire at or after the gate's position goes to wire `N + |gs|`. -/
def qaNorm (N : ℕ) (gs : List Gate) : List Gate :=
  gs.mapIdx fun p g => ⟨g.op, g.inputs.map fun i => if i < N + p then i else N + gs.length⟩

/-- The removed set and its targets for Theorem QA. -/
def qaS (g1 g2 o2 jM : ℕ) : Finset ℕ := {g1, g2, o2, jM}

def qaTgt (g1 g2 jM u1 u2 z : ℕ) (p : ℕ) : Option ℕ :=
  if p = g1 then some u1 else if p = g2 then some u2 else if p = jM then some z else none

/-- The circuit left after the removal. -/
def qaL (N : ℕ) (C : Circuit) (g1 g2 o2 jM u1 u2 z : ℕ) : Circuit :=
  let S := qaS g1 g2 o2 jM
  let r := qaRho N S (qaTgt g1 g2 jM u1 u2 z) (N + cnt S C.gates.length)
  ⟨build S r (qaNorm N C.gates) C.gates.length, r C.output⟩

section rho
variable (N : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (d : ℕ)

theorem qaRho_lt {j : ℕ} (h : j < N) : qaRho N S tgt d j = j := by
  rw [qaRho]; simp [h]

theorem qaRho_keep {p : ℕ} (h : p ∉ S) : qaRho N S tgt d (N + p) = N + cnt S p := by
  rw [qaRho]; simp [h]

theorem qaRho_alias {p i : ℕ} (h : p ∈ S) (ht : tgt p = some i) (hi : i < N + p) :
    qaRho N S tgt d (N + p) = qaRho N S tgt d i := by
  rw [qaRho]; simp [h, ht, hi]

theorem qaRho_alias_ge {p i : ℕ} (h : p ∈ S) (ht : tgt p = some i) (hi : N + p ≤ i) :
    qaRho N S tgt d (N + p) = d := by
  rw [qaRho]; simp [h, ht, show ¬ i < N + p by omega]

theorem qaRho_none {p : ℕ} (h : p ∈ S) (ht : tgt p = none) : qaRho N S tgt d (N + p) = d := by
  rw [qaRho]; simp [h, ht]

/-- Below a kept position, the image is below its new position or the fallback. -/
theorem qaRho_bound (p : ℕ) : ∀ a, a < N + p → qaRho N S tgt d a < N + cnt S p ∨
    qaRho N S tgt d a = d := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    by_cases h1 : a < N
    · left; rw [qaRho_lt N S tgt d h1]; omega
    · obtain ⟨q, rfl⟩ : ∃ q, a = N + q := ⟨a - N, by omega⟩
      by_cases hq : q ∈ S
      · cases ht : tgt q with
        | none => right; exact qaRho_none N S tgt d hq ht
        | some i =>
          by_cases hi : i < N + q
          · rw [qaRho_alias N S tgt d hq ht hi]; exact ih i hi (by omega)
          · right; exact qaRho_alias_ge N S tgt d hq ht (by omega)
      · left
        rw [qaRho_keep N S tgt d hq]
        have h2 := cnt_mono S (show q + 1 ≤ p by omega)
        rw [cnt_succ_keep S hq] at h2
        omega

end rho

theorem qaNorm_getD (N : ℕ) (gs : List Gate) (p : ℕ) (hp : p < gs.length) :
    (qaNorm N gs).getD p g0 =
      ⟨(gs.getD p g0).op, (gs.getD p g0).inputs.map fun i =>
        if i < N + p then i else N + gs.length⟩ := by
  simp [qaNorm, List.getD_eq_getElem?_getD, List.getElem?_mapIdx, hp]

theorem qa_len_norm (N : ℕ) (gs : List Gate) : (qaNorm N gs).length = gs.length := by
  simp [qaNorm]

/-- A two-element list holding two distinct wires is one of their two orders. -/
theorem qa_two (l : List ℕ) (hl : l.length = 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [c, d], _ =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · left; rfl
    · right; rfl
    · exact absurd rfl hab

theorem qa_or2 (l : List ℕ) (hl : l.length = 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) (f : ℕ → Bool) : GateOp.or.eval (l.map f) = (f a || f b) := by
  rcases qa_two l hl a b ha hb hab with rfl | rfl <;> simp [GateOp.eval, Bool.or_comm]

theorem qa_and2 (l : List ℕ) (hl : l.length = 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) (f : ℕ → Bool) : GateOp.and.eval (l.map f) = (f a && f b) := by
  rcases qa_two l hl a b ha hb hab with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm]

/-- The value of gate `r` of a root circuit on `N` inputs. -/
theorem qa_val_fin (N : ℕ) (C : Circuit) (y : Fin N → Bool) (r : Fin C.gates.length) :
    (wiresFrom C.gates (List.ofFn y)).getD (N + r.val) false =
      (C.gates.get r).op.eval ((C.gates.get r).inputs.map fun i =>
        if i < N + r.val then (wiresFrom C.gates (List.ofFn y)).getD i false else false) := by
  have h := qa_val_gate C.gates (List.ofFn y) r.val (C.gates.get r) (by simp)
  simpa using h

/-- C1, the values: every wire of `C` other than `e`, `q2`, `o2` has, at the double
restriction of `x`, the value of its image in `qaL` at `x`. -/
theorem qa_remove_val (n : ℕ) (C : Circuit) (e q2 : Fin (n + 1))
    (g1 g2 o2 jM : Fin C.gates.length) (u1 u2 z : ℕ)
    (heq : e ≠ q2) (hg12 : g1 ≠ g2) (ho1 : o2 ≠ g1) (ho2 : o2 ≠ g2) (hoM : o2 < jM)
    (hg1 : (C.gates.get g1).op = GateOp.or ∧ (C.gates.get g1).inputs.length = 2 ∧
      e.val ∈ (C.gates.get g1).inputs ∧ u1 ∈ (C.gates.get g1).inputs ∧ e.val ≠ u1)
    (hg2 : (C.gates.get g2).op = GateOp.or ∧ (C.gates.get g2).inputs.length = 2 ∧
      e.val ∈ (C.gates.get g2).inputs ∧ u2 ∈ (C.gates.get g2).inputs ∧ e.val ≠ u2)
    (hre : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) e.val → j = g1 ∨ j = g2)
    (ho : (C.gates.get o2).op = GateOp.or ∧ q2.val ∈ (C.gates.get o2).inputs)
    (hrq : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) q2.val → j = o2)
    (hM : (C.gates.get jM).op = GateOp.and ∧ (C.gates.get jM).inputs.length = 2 ∧
      n + 1 + o2.val ∈ (C.gates.get jM).inputs ∧ z ∈ (C.gates.get jM).inputs ∧
      n + 1 + o2.val ≠ z)
    (hro : ∀ j : Fin C.gates.length, o2 < j → qaReads (C.gates.get j) (n + 1 + o2.val) →
      j = jM)
    (x : Fin (n + 1) → Bool) :
    ∀ t, ¬ (t = e.val ∨ t = q2.val ∨ t = n + 1 + o2.val) →
      (wiresFrom (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates (List.ofFn x)).getD
          (qaRho (n + 1) (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
            (n + 1 + cnt (qaS g1 g2 o2 jM) C.gates.length) t) false =
        (wiresFrom C.gates (List.ofFn
          (Function.update (Function.update x q2 true) e false))).getD t false := by
  -- names
  have hLdef : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates =
      build (qaS g1.val g2.val o2.val jM.val)
        (qaRho (n + 1) (qaS g1.val g2.val o2.val jM.val) (qaTgt g1.val g2.val jM.val u1 u2 z)
          (n + 1 + cnt (qaS g1.val g2.val o2.val jM.val) C.gates.length))
        (qaNorm (n + 1) C.gates) C.gates.length := by
    unfold qaL; rfl
  rw [hLdef]
  set S := qaS g1.val g2.val o2.val jM.val with hS
  set tgt := qaTgt g1.val g2.val jM.val u1 u2 z with htgt
  set d := (n + 1) + cnt S C.gates.length with hd
  set xs := Function.update (Function.update x q2 true) e false with hxs
  set L := build S (qaRho (n + 1) S tgt d) (qaNorm (n + 1) C.gates) C.gates.length with hL
  obtain ⟨hg1op, hg1l, hg1e, hg1u, hg1ne⟩ := hg1
  obtain ⟨hg2op, hg2l, hg2e, hg2u, hg2ne⟩ := hg2
  obtain ⟨hMop, hMl, hMo, hMz, hMne⟩ := hM
  have hMg1 : jM ≠ g1 := by intro h; rw [h, hg1op] at hMop; cases hMop
  have hMg2 : jM ≠ g2 := by intro h; rw [h, hg2op] at hMop; cases hMop
  have hvne : ∀ a b : Fin C.gates.length, a ≠ b → a.val ≠ b.val := fun a b h h' => h (Fin.ext h')
  have hmemS : ∀ p, p ∈ S ↔ p = g1.val ∨ p = g2.val ∨ p = o2.val ∨ p = jM.val := by
    intro p; simp [hS, qaS]
  have htg1 : tgt g1.val = some u1 := by simp [htgt, qaTgt]
  have htg2 : tgt g2.val = some u2 := by
    simp [htgt, qaTgt, hvne g2 g1 (Ne.symm hg12)]
  have htM : tgt jM.val = some z := by
    simp [htgt, qaTgt, hvne jM g1 hMg1, hvne jM g2 hMg2]
  have hto : tgt o2.val = none := by
    simp [htgt, qaTgt, hvne o2 g1 ho1, hvne o2 g2 ho2, hvne o2 jM (ne_of_lt hoM)]
  have hSlt : ∀ p ∈ S, p < C.gates.length := by
    intro p hp; rw [hmemS] at hp; rcases hp with rfl | rfl | rfl | rfl <;> exact Fin.isLt _
  have hLlen : L.length = cnt S C.gates.length := len_build S (qaRho (n + 1) S tgt d) _ C.gates.length
  have hxN : (List.ofFn x).length = (n + 1) := by simp
  have hxsN : (List.ofFn xs).length = (n + 1) := by simp
  have hVLbig : ∀ k, (n + 1) + cnt S C.gates.length ≤ k → (wiresFrom L (List.ofFn x)).getD k false = false := by
    intro k hk
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom, hLlen, hxN]; omega)
  have hVCbig : ∀ k, (n + 1) + C.gates.length ≤ k → (wiresFrom C.gates (List.ofFn xs)).getD k false = false := by
    intro k hk
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom, hxsN]; omega)
  have hVCin : ∀ k (hk : k < (n + 1)), (wiresFrom C.gates (List.ofFn xs)).getD k false = xs ⟨k, hk⟩ := by
    intro k hk; rw [getD_wiresFrom _ _ _ (by rw [hxsN]; exact hk), qa_ofFn_getD _ _ hk]
  have hVLin : ∀ k (hk : k < (n + 1)), (wiresFrom L (List.ofFn x)).getD k false = x ⟨k, hk⟩ := by
    intro k hk; rw [getD_wiresFrom _ _ _ (by rw [hxN]; exact hk), qa_ofFn_getD _ _ hk]
  have hxse : xs e = false := by simp [hxs]
  have hxsq : xs q2 = true := by simp [hxs, Function.update_of_ne (Ne.symm heq)]
  -- o2 is true at the restriction
  have hVo : (wiresFrom C.gates (List.ofFn xs)).getD ((n + 1) + o2.val) false = true := by
    rw [qa_val_fin (n + 1) C xs o2]
    apply qa_or_true _ _ ho.1 q2.val ho.2
    rw [if_pos (by omega), hVCin q2.val q2.isLt]; exact hxsq
  -- readers excluded for kept gates
  have hkeep_reads : ∀ (p : Fin C.gates.length), p.val ∉ S → ∀ a, qaReads (C.gates.get p) a →
      a < (n + 1) + p.val → ¬ (a = e.val ∨ a = q2.val ∨ a = (n + 1) + o2.val) := by
    intro p hp a ha hlt hbad
    apply hp; rw [hmemS]
    rcases hbad with rfl | rfl | rfl
    · rcases hre p ha with h | h
      · left; rw [h]
      · right; left; rw [h]
    · right; right; left; rw [hrq p ha]
    · right; right; right
      have hop : o2 < p := by show o2.val < p.val; omega
      rw [hro p hop ha]
  have hdge : ∀ p, p ≤ C.gates.length → ¬ d < (n + 1) + cnt S p := by
    intro p hp; have := cnt_mono S hp; omega
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hbad
    by_cases h1 : t < (n + 1)
    · -- an input
      rw [qaRho_lt (n + 1) S tgt d h1, hVLin t h1, hVCin t h1, hxs]
      have hte : (⟨t, h1⟩ : Fin (n + 1)) ≠ e := fun h => hbad (Or.inl (by rw [← h]))
      have htq : (⟨t, h1⟩ : Fin (n + 1)) ≠ q2 := fun h => hbad (Or.inr (Or.inl (by rw [← h])))
      rw [Function.update_of_ne hte, Function.update_of_ne htq]
    obtain ⟨p, rfl⟩ : ∃ p, t = (n + 1) + p := ⟨t - (n + 1), by omega⟩
    by_cases hpl : C.gates.length ≤ p
    · -- past the circuit
      have hpS : p ∉ S := fun h => by have := hSlt p h; omega
      rw [qaRho_keep (n + 1) S tgt d hpS, hVCbig _ (by omega),
        hVLbig _ (by have := cnt_mono S hpl; omega)]
    push_neg at hpl
    by_cases hpS : p ∈ S
    · have hcases := (hmemS p).1 hpS
      rcases hcases with hp1 | hp2 | hpo | hpM
      · -- alias case
        subst hp1
        have hVg : (wiresFrom C.gates (List.ofFn xs)).getD (n + 1 + g1.val) false =
            (if u1 < n + 1 + g1.val then (wiresFrom C.gates (List.ofFn xs)).getD u1 false
              else false) := by
          rw [qa_val_fin (n + 1) C xs g1, hg1op, qa_or2 _ hg1l _ _ hg1e hg1u hg1ne,
            if_pos (by have := e.isLt; omega), hVCin e.val e.isLt]
          simp [hxse]
        rw [hVg]
        by_cases hu : u1 < n + 1 + g1.val
        · rw [if_pos hu, qaRho_alias (n + 1) S tgt d hpS htg1 hu]
          apply ih u1 hu
          rintro (h | h | h)
          · exact hg1ne h.symm
          · have := hrq g1 (Or.inr ⟨by rw [hg1op]; exact fun hh => GateOp.noConfusion hh, h ▸ hg1u⟩)
            exact ho1 this.symm
          · have hlt : o2 < g1 := by show o2.val < g1.val; omega
            have := hro g1 hlt (Or.inr ⟨by rw [hg1op]; exact fun hh => GateOp.noConfusion hh, h ▸ hg1u⟩)
            exact hMg1 this.symm
        · rw [if_neg hu, qaRho_alias_ge (n + 1) S tgt d hpS htg1 (by omega)]
          exact hVLbig _ le_rfl
      · -- alias case
        subst hp2
        have hVg : (wiresFrom C.gates (List.ofFn xs)).getD (n + 1 + g2.val) false =
            (if u2 < n + 1 + g2.val then (wiresFrom C.gates (List.ofFn xs)).getD u2 false
              else false) := by
          rw [qa_val_fin (n + 1) C xs g2, hg2op, qa_or2 _ hg2l _ _ hg2e hg2u hg2ne,
            if_pos (by have := e.isLt; omega), hVCin e.val e.isLt]
          simp [hxse]
        rw [hVg]
        by_cases hu : u2 < n + 1 + g2.val
        · rw [if_pos hu, qaRho_alias (n + 1) S tgt d hpS htg2 hu]
          apply ih u2 hu
          rintro (h | h | h)
          · exact hg2ne h.symm
          · have := hrq g2 (Or.inr ⟨by rw [hg2op]; exact fun hh => GateOp.noConfusion hh, h ▸ hg2u⟩)
            exact ho2 this.symm
          · have hlt : o2 < g2 := by show o2.val < g2.val; omega
            have := hro g2 hlt (Or.inr ⟨by rw [hg2op]; exact fun hh => GateOp.noConfusion hh, h ▸ hg2u⟩)
            exact hMg2 this.symm
        · rw [if_neg hu, qaRho_alias_ge (n + 1) S tgt d hpS htg2 (by omega)]
          exact hVLbig _ le_rfl
      · exact absurd (Or.inr (Or.inr (by rw [hpo]))) hbad
      · -- alias case
        subst hpM
        have hVg : (wiresFrom C.gates (List.ofFn xs)).getD (n + 1 + jM.val) false =
            (if z < n + 1 + jM.val then (wiresFrom C.gates (List.ofFn xs)).getD z false
              else false) := by
          rw [qa_val_fin (n + 1) C xs jM, hMop, qa_and2 _ hMl _ _ hMo hMz hMne,
            if_pos (by have : o2.val < jM.val := hoM; omega), hVo]
          simp
        rw [hVg]
        by_cases hu : z < n + 1 + jM.val
        · rw [if_pos hu, qaRho_alias (n + 1) S tgt d hpS htM hu]
          apply ih z hu
          rintro (h | h | h)
          · rcases hre jM (Or.inr ⟨by rw [hMop]; exact fun hh => GateOp.noConfusion hh, h ▸ hMz⟩)
              with h' | h'
            · exact hMg1 h'
            · exact hMg2 h'
          · have := hrq jM (Or.inr ⟨by rw [hMop]; exact fun hh => GateOp.noConfusion hh, h ▸ hMz⟩)
            rw [this] at hoM; exact lt_irrefl _ hoM
          · exact hMne h.symm
        · rw [if_neg hu, qaRho_alias_ge (n + 1) S tgt d hpS htM (by omega)]
          exact hVLbig _ le_rfl
    · -- a kept gate
      set P : Fin C.gates.length := ⟨p, hpl⟩ with hP
      have hPv : P.val = p := rfl
      rw [qaRho_keep (n + 1) S tgt d hpS]
      have hgb := get_build S (qaRho (n + 1) S tgt d) (qaNorm (n + 1) C.gates) hpS hpl
      have hVL := qa_val_gate L (List.ofFn x) (cnt S p) _ hgb
      rw [hxN] at hVL
      rw [hVL, ← hPv, qa_val_fin (n + 1) C xs P, hPv]
      have hgP : C.gates.getD p g0 = C.gates.get P := by
        simp [List.getD_eq_getElem?_getD, hpl, hP]
      rw [qaNorm_getD (n + 1) C.gates p hpl, hgP]
      simp only [rg, List.map_map]
      apply qa_eval_congr
      intro a ha
      simp only [Function.comp_apply]
      by_cases hlt : a < (n + 1) + p
      · rw [if_pos hlt, if_pos hlt]
        have hnb := hkeep_reads P hpS a ha hlt
        have hih := ih a hlt hnb
        rcases qaRho_bound (n + 1) S tgt d p a hlt with hb | hb
        · rw [if_pos hb]; exact hih
        · rw [hb, if_neg (hdge p hpl.le), ← hih, hb, hVLbig _ le_rfl]
      · rw [if_neg hlt, if_neg hlt]
        have hbig : qaRho (n + 1) S tgt d ((n + 1) + C.gates.length) = d := by
          have : C.gates.length ∉ S := fun h => by have := hSlt C.gates.length h; omega
          rw [qaRho_keep (n + 1) S tgt d this]
        rw [hbig, if_neg (hdge p hpl.le)]

/-- QA-C1, the removal: under the shape hypotheses of the row, the fan-in-two circuit `qaL`, with
four gates fewer than `C`, computes, on all inputs, what `C` computes at `x_q2 := 1, x_e := 0`,
provided that function is not constant. -/
theorem qa_remove (n : ℕ) (C : Circuit) (hC : FanInTwo C) (e q2 : Fin (n + 1))
    (g1 g2 o2 jM : Fin C.gates.length) (u1 u2 z : ℕ)
    (heq : e ≠ q2) (hg12 : g1 ≠ g2) (ho1 : o2 ≠ g1) (ho2 : o2 ≠ g2) (hoM : o2 < jM)
    (hg1 : (C.gates.get g1).op = GateOp.or ∧ (C.gates.get g1).inputs.length = 2 ∧
      e.val ∈ (C.gates.get g1).inputs ∧ u1 ∈ (C.gates.get g1).inputs ∧ e.val ≠ u1)
    (hg2 : (C.gates.get g2).op = GateOp.or ∧ (C.gates.get g2).inputs.length = 2 ∧
      e.val ∈ (C.gates.get g2).inputs ∧ u2 ∈ (C.gates.get g2).inputs ∧ e.val ≠ u2)
    (hre : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) e.val → j = g1 ∨ j = g2)
    (ho : (C.gates.get o2).op = GateOp.or ∧ q2.val ∈ (C.gates.get o2).inputs)
    (hrq : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) q2.val → j = o2)
    (hM : (C.gates.get jM).op = GateOp.and ∧ (C.gates.get jM).inputs.length = 2 ∧
      n + 1 + o2.val ∈ (C.gates.get jM).inputs ∧ z ∈ (C.gates.get jM).inputs ∧
      n + 1 + o2.val ≠ z)
    (hro : ∀ j : Fin C.gates.length, o2 < j → qaReads (C.gates.get j) (n + 1 + o2.val) →
      j = jM)
    (G : (Fin (n + 1) → Bool) → Bool)
    (hG : ∀ x, circuitFun (n + 1) C (Function.update (Function.update x q2 true) e false) = G x)
    (hnc : ∃ y y' : Fin (n + 1) → Bool, G y ≠ G y') :
    FanInTwo (qaL (n + 1) C g1 g2 o2 jM u1 u2 z) ∧
      (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).size + 4 = C.size ∧
      ∀ x : Fin (n + 1) → Bool, (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).eval (List.ofFn x) = G x := by
  have hMg1 : jM ≠ g1 := by intro h; have := hM.1; rw [h, hg1.1] at this; cases this
  have hMg2 : jM ≠ g2 := by intro h; have := hM.1; rw [h, hg2.1] at this; cases this
  have hvne : ∀ a b : Fin C.gates.length, a ≠ b → a.val ≠ b.val := fun a b h h' => h (Fin.ext h')
  set S := qaS g1.val g2.val o2.val jM.val with hS
  have hmemS : ∀ p, p ∈ S ↔ p = g1.val ∨ p = g2.val ∨ p = o2.val ∨ p = jM.val := by
    intro p; simp [hS, qaS]
  have hSlt : ∀ p ∈ S, p < C.gates.length := by
    intro p hp; rw [hmemS] at hp; rcases hp with rfl | rfl | rfl | rfl <;> exact Fin.isLt _
  have hcard : S.card = 4 := by
    rw [hS, qaS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact hvne o2 jM (ne_of_lt hoM)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvne g2 o2 (Ne.symm ho2), hvne g2 jM (Ne.symm hMg2)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvne g1 g2 hg12, hvne g1 o2 (Ne.symm ho1), hvne g1 jM (Ne.symm hMg1)⟩
  refine ⟨?_, ?_, ?_⟩
  · -- fan-in two
    intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have hk' : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates[k]? = some g := by
      rw [List.getElem?_eq_getElem hk, hkg]
    obtain ⟨q, hq, _, _, rfl⟩ := mem_build _ _ _ _ k g hk'
    rw [qaNorm_getD _ _ q hq]
    have hmem : C.gates.getD q g0 ∈ C.gates := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; simp
    have := hC _ hmem
    simpa [rg] using this
  · -- size
    show (build _ _ _ _).length + 4 = C.gates.length
    rw [len_build, ← hcard]
    have h := cnt_card S C.gates.length
    have hf : (Finset.range C.gates.length).filter (· ∈ S) = S := by
      ext p; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨hSlt p h, h⟩⟩
    rw [hf] at h; exact h
  · intro x
    have hval := qa_remove_val n C e q2 g1 g2 o2 jM u1 u2 z heq hg12 ho1 ho2 hoM hg1 hg2 hre
      ho hrq hM hro x
    have hxs : ∀ y : Fin (n + 1) → Bool,
        (Function.update (Function.update y q2 true) e false) e = false := by intro y; simp
    have hxq : ∀ y : Fin (n + 1) → Bool,
        (Function.update (Function.update y q2 true) e false) q2 = true := by
      intro y; simp [Function.update_of_ne (Ne.symm heq)]
    have hbad : ¬ (C.output = e.val ∨ C.output = q2.val ∨ C.output = n + 1 + o2.val) := by
      obtain ⟨y, y', hyy⟩ := hnc
      intro hob
      apply hyy
      rw [← hG y, ← hG y']
      have hconst : ∀ b : Bool, (∀ w : Fin (n + 1) → Bool, circuitFun (n + 1) C
          (Function.update (Function.update w q2 true) e false) = b) →
          circuitFun (n + 1) C (Function.update (Function.update y q2 true) e false) =
          circuitFun (n + 1) C (Function.update (Function.update y' q2 true) e false) := by
        intro b hb; rw [hb y, hb y']
      rcases hob with h | h | h
      · apply hconst false; intro w
        show (C.wires _).getD C.output false = false
        rw [wires_eq, h, getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; exact e.isLt),
          qa_ofFn_getD _ _ e.isLt]
        exact hxs w
      · apply hconst true; intro w
        show (C.wires _).getD C.output false = true
        rw [wires_eq, h, getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; exact q2.isLt),
          qa_ofFn_getD _ _ q2.isLt]
        exact hxq w
      · apply hconst true; intro w
        show (C.wires _).getD C.output false = true
        rw [wires_eq, h, qa_val_fin (n + 1) C _ o2]
        apply qa_or_true _ _ ho.1 q2.val ho.2
        rw [if_pos (by have := q2.isLt; omega),
          getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; exact q2.isLt),
          qa_ofFn_getD _ _ q2.isLt]
        exact hxq w
    rw [← hG x]
    exact hval C.output hbad

end PEqualNP.MetaComplexity.Helpers.RunFour2
