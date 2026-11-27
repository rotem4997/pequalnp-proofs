import PEqualNP.MetaComplexity.Helpers.RunPOO

/-!
# Run-of-four assembly, (P-OO) part 2: a dead gate counted

`poo_dead`: if the operand `u_1 = G_j` of the OR gate `p1` is read by `p1` only, then at `e := 1`
the gates `p1, p2, R1, R2` and the dead `j` are five: delete gate `j` (readers redirected to `e`,
`rdel`), the list is shorter by one and agrees at `e = 1`; `save` counts four in it.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- The position of gate `q` after gate `j` is deleted. -/
def pooS (j q : ℕ) : ℕ := if q < j then q else q - 1

theorem poo_rdel_gate {N : ℕ} {gs : List Gate} (hcl : CleanL N gs) (j a : ℕ) (hj : j < gs.length)
    (q : ℕ) (hq : q ≠ j) (g : Gate) (hg : gs[q]? = some g) :
    (rdel N j a gs)[pooS j q]? = some ⟨g.op, g.inputs.map (rd N j a)⟩ := by
  unfold pooS
  by_cases hqj : q < j
  · simp only [hqj, if_true]
    rw [rdel_get_lt N j a gs hj q hqj, hg]
    have : g.inputs.map (rd N j a) = g.inputs := by
      conv_rhs => rw [← List.map_id g.inputs]
      apply List.map_congr_left
      intro i hi
      have := (hcl q g hg).lt i hi
      exact rd_lt N j a i (by omega)
    rw [this]
  · simp only [hqj, if_false]
    rw [rdel_get_ge N j a gs hj (q - 1) (by omega), show q - 1 + 1 = q by omega, hg]
    rfl

theorem poo_rd_wire {N : ℕ} (j a p : ℕ) (hp : p ≠ j) : rd N j a (N + p) = N + pooS j p := by
  unfold rd pooS
  split_ifs <;> omega

theorem poo_rdel_reads {N : ℕ} {gs : List Gate} (hcl : CleanL N gs) (j a : ℕ)
    (hj : j < gs.length) {q w : ℕ} (hq : q ≠ j) (h : Reads gs q w) :
    Reads (rdel N j a gs) (pooS j q) (rd N j a w) := by
  obtain ⟨g, hg, hw⟩ := h
  exact ⟨_, poo_rdel_gate hcl j a hj q hq g hg, List.mem_map.2 ⟨w, hw, rfl⟩⟩

/-- A dead operand gate `j` of the OR gate `p1`: with `p1, p2, R1, R2` it is the fifth gate. -/
theorem poo_dead {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc1 : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e true) ≠ f (Function.update y e true))
    (j p1 p2 R1 R2 : ℕ) (g1 g2 : Gate)
    (hg1 : gs[p1]? = some g1) (ho1 : g1.op = GateOp.or)
    (hin1 : g1.inputs = [(e : ℕ), n + 1 + j] ∨ g1.inputs = [n + 1 + j, (e : ℕ)])
    (hg2 : gs[p2]? = some g2) (ho2 : g2.op = GateOp.or) (he2 : (e : ℕ) ∈ g2.inputs)
    (hjsole : ∀ t, Reads gs t (n + 1 + j) → t = p1)
    (hR1 : Reads gs R1 (n + 1 + p1)) (hR2 : Reads gs R2 (n + 1 + p2))
    (hjp1 : j < p1) (hjp2 : j ≠ p2) (hjR2 : j ≠ R2)
    (h12 : p1 ≠ p2) (h1R1 : p1 ≠ R1) (h1R2 : p1 ≠ R2) (h2R1 : p2 ≠ R1) (h2R2 : p2 ≠ R2)
    (hRR : R1 ≠ R2) : Drop f e true 5 gs.length := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hjlen : j < gs.length := by
    have := reads_len (show Reads gs p1 (n + 1 + j) from
      ⟨g1, hg1, by rcases hin1 with h | h <;> rw [h] <;> simp⟩)
    omega
  have hea : (e : ℕ) < n + 1 + j := by have := e.isLt; omega
  have hR1p : p1 < R1 := by have := reads_lt hcl hR1; omega
  have hR2p : p2 < R2 := by have := reads_lt hcl hR2; omega
  have hjo : o ≠ n + 1 + j := poo_out_ne L hfnc
    (show Reads gs p1 (n + 1 + j) from ⟨g1, hg1, by rcases hin1 with h | h <;> rw [h] <;> simp⟩)
  set gs'' := rdel (n + 1) j e gs with hgs''
  have hcl'' : CleanL (n + 1) gs'' := rdel_clean (n + 1) j e gs hcl hjlen hea
  have hlen'' : gs''.length + 1 = gs.length := rdel_length (n + 1) j e gs hjlen
  -- values at e = 1
  have hV : ∀ x : Fin (n + 1) → Bool, x e = true → ∀ w, w ≠ n + 1 + j →
      vl gs'' x (rd (n + 1) j e w) = vl gs x w := by
    intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases lt_or_gt_of_ne hw with hlt | hgt
      · rw [rd_lt _ _ _ _ hlt]
        exact rdel_prefix (n + 1) j e gs hcl hjlen hea x w hlt
      · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
        have hrj : j < r := by omega
        rw [rd_gt _ _ _ _ hgt]
        have e1 : n + 1 + r - 1 = n + 1 + (r - 1) := by omega
        rw [e1]
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs'' x _ (by omega), vl_beyond gs x _ (by omega)]
        | some g =>
          have hg'' : gs''[r - 1]? = some ⟨g.op, g.inputs.map (rd (n + 1) j e)⟩ := by
            have := poo_rdel_gate hcl j e hjlen r (by omega) g hr
            unfold pooS at this
            rwa [if_neg (by omega)] at this
          rw [vl_gate gs'' hcl'' x (r - 1) _ hg'', vl_gate gs hcl x r g hr]
          by_cases hrp : r = p1
          · subst hrp
            have egg : g = g1 := Option.some.inj (hr.symm.trans hg1)
            subst egg
            have hxe : vl gs x e = true := by
              rw [vl_input gs x e e.isLt]; simpa using hx
            have hxe'' : vl gs'' x e = true := by
              rw [vl_input gs'' x e e.isLt]; simpa using hx
            show GateOp.eval g.op (List.map (vl gs'' x) (List.map (rd (n + 1) j e) g.inputs)) =
              GateOp.eval g.op (List.map (vl gs x) g.inputs)
            rw [ho1]
            rcases hin1 with h | h <;> rw [h] <;>
              simp [GateOp.eval, rd_lt _ _ _ _ hea, rd_eq, hxe'', hxe]
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro a' ha'
            have hlt := (hcl r g hr).lt a' ha'
            have hne : a' ≠ n + 1 + j := by
              intro h
              exact hrp (hjsole r ⟨g, hr, h ▸ ha'⟩)
            exact ih a' hlt hne
  have hfeq : ∀ x : Fin (n + 1) → Bool,
      vl gs'' (Function.update x e true) (rd (n + 1) j e o) = f (Function.update x e true) := by
    intro x
    rw [hV (Function.update x e true) (by simp) o hjo, L.hev]
  have hnc'' : ∃ x y : Fin (n + 1) → Bool,
      vl gs'' (Function.update x e true) (rd (n + 1) j e o) ≠
        vl gs'' (Function.update y e true) (rd (n + 1) j e o) := by
    obtain ⟨x, y, h⟩ := hnc1
    exact ⟨x, y, by rw [hfeq, hfeq]; exact h⟩
  have hp1j : p1 ≠ j := by omega
  have hp2j : p2 ≠ j := fun h => hjp2 h.symm
  have hR1j : R1 ≠ j := by omega
  have hR2j : R2 ≠ j := fun h => hjR2 h.symm
  have hee : rd (n + 1) j e (e : ℕ) = e := rd_lt _ _ _ _ hea
  have hrd1 : Reads gs'' (pooS j p1) e := by
    have := poo_rdel_reads hcl j e hjlen hp1j
      (show Reads gs p1 e from ⟨g1, hg1, by rcases hin1 with h | h <;> rw [h] <;> simp⟩)
    rwa [hee] at this
  have hrd2 : Reads gs'' (pooS j p2) e := by
    have := poo_rdel_reads hcl j e hjlen hp2j (show Reads gs p2 e from ⟨g2, hg2, he2⟩)
    rwa [hee] at this
  have hg1'' := poo_rdel_gate hcl j e hjlen p1 hp1j g1 hg1
  have hg2'' := poo_rdel_gate hcl j e hjlen p2 hp2j g2 hg2
  have hC1 : IsC n gs'' e true (n + 1 + pooS j p1) := by
    obtain ⟨g, hg, hi⟩ := hrd1
    have e1 : g = ⟨g1.op, g1.inputs.map (rd (n + 1) j e)⟩ := by
      rw [hg1''] at hg; exact (Option.some.inj hg).symm
    refine isC_reader hcl'' e (pooS j p1) g hg hi true (Or.inr ?_)
    rw [e1]; simp [fixBit, ho1]
  have hC2 : IsC n gs'' e true (n + 1 + pooS j p2) := by
    obtain ⟨g, hg, hi⟩ := hrd2
    have e1 : g = ⟨g2.op, g2.inputs.map (rd (n + 1) j e)⟩ := by
      rw [hg2''] at hg; exact (Option.some.inj hg).symm
    refine isC_reader hcl'' e (pooS j p2) g hg hi true (Or.inr ?_)
    rw [e1]; simp [fixBit, ho2]
  have hrdR1 : Reads gs'' (pooS j R1) (n + 1 + pooS j p1) := by
    have := poo_rdel_reads hcl j e hjlen hR1j hR1
    rwa [poo_rd_wire j e p1 hp1j] at this
  have hrdR2 : Reads gs'' (pooS j R2) (n + 1 + pooS j p2) := by
    have := poo_rdel_reads hcl j e hjlen hR2j hR2
    rwa [poo_rd_wire j e p2 hp2j] at this
  have hS := save n (fun x => vl gs'' x (rd (n + 1) j e o)) gs'' (rd (n + 1) j e o) hcl''
    (fun x => rfl) e true hnc''
    {pooS j p1, pooS j p2, pooS j R1, pooS j R2} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact rc_input true hrd1
      · exact rc_input true hrd2
      · exact rc_of_reads hrdR1 hC1
      · exact rc_of_reads hrdR2 hC2)
  have hcard : ({pooS j p1, pooS j p2, pooS j R1, pooS j R2} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; unfold pooS; split_ifs <;> omega),
      Finset.card_eq_three.2 ⟨pooS j p2, pooS j R1, pooS j R2, by unfold pooS; split_ifs <;> omega,
        by unfold pooS; split_ifs <;> omega, by unfold pooS; split_ifs <;> omega, rfl⟩]
  rw [hcard] at hS
  obtain ⟨s', hs', hcs⟩ := hS
  refine ⟨s', by omega, ?_⟩
  have e1 : (fun x : Fin (n + 1) → Bool => f (Function.update x e true)) =
      fun x => vl gs'' (Function.update x e true) (rd (n + 1) j e o) := by
    funext x; rw [hfeq]
  rw [e1]
  exact hcs

end PEqualNP.MetaComplexity.Helpers.RunAsm
