import PEqualNP.MetaComplexity.Helpers.EdgeFnPlan

/-!
# Piece C6 of the edge function plan: an unshared AND partner pays

`stmtAnd : StmtAnd` (FULL-PROOF 3.5, plan piece C6, P-AND). The proof is the in-place change of
the plan: the partner gate `ph` is replaced by `not [y]`. At every input where the literal `l` is
false, gate `p` is false before and after, and `p` is the only reader of `ph`, so every other wire
keeps its value and the new list still computes `F` there. In the new list, at `y := b`, the
positions `ph`, `p`, the NOT gate on `y` (second case) and a later reader of `p` all read a wire of
constant status, and `Readers.save` counts them.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- The partner gate `ph` replaced by `not [y]`. -/
def andSwap (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) : List Gate :=
  gs.set ph ⟨GateOp.not, [(y : ℕ)]⟩

theorem andSwap_length (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) :
    (andSwap gs ph y).length = gs.length := by
  simp [andSwap]

theorem andSwap_get_ne (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (r : ℕ) (hr : r ≠ ph) :
    (andSwap gs ph y)[r]? = gs[r]? := by
  simp [andSwap, Ne.symm hr]

theorem andSwap_get_eq (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (hph : ph < gs.length) :
    (andSwap gs ph y)[ph]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
  simp [andSwap, hph]

theorem andSwap_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (y : Fin N) (hcl : CleanL N gs)
    (hph : ph < gs.length) : CleanL N (andSwap gs ph y) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [andSwap_get_eq gs r y hph] at hr'
    cases hr'
    exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [andSwap_get_ne gs ph y r hrp] at hr'
    exact hcl r g' hr'

/-- Wire agreement: where the literal `l` is false, every wire other than the partner keeps its
value. -/
theorem andSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = false) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = false := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

theorem andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x

/-- The core count: on the swapped list, every set of positions reading a constant-status wire at
`y := b` is saved for `F`, as long as the literal is false at `y = b`. -/
theorem and_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = false)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [andSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc

/-- Piece C6 (FULL-PROOF 3.5). -/
theorem stmtAnd : StmtAnd := by
  intro n F gs o p ph l g y L hnc _hdep hgp hop hin hlit hph hone ho1 ho2
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < n + 1 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ n + 1 + ph := by
    intro e
    apply L.no_alias hfnc p hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  refine ⟨fun hly => ?_, fun hly => ?_⟩
  · -- the literal `y`: positions `ph`, `p`, `S` at `y := false`
    subst hly
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = false → vl gs x y = false := by
      intro x hx
      rw [vl_input gs x y y.isLt]
      exact hx
    have hcp : IsC n (andSwap gs ph y) y false (n + 1 + p) :=
      isC_reader hcl' y p g hgp' hlmem false (Or.inr (by simp [fixBit, hop]))
    have h3 := and_core n F gs o p ph y g y L false (hnc false) hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  · -- the literal `not y`: positions `ph`, `pn`, `p`, `S` at `y := true`
    rcases hlit with e | ⟨pn, rfl, hpn⟩
    · exact absurd e hly
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x (n + 1 + pn) = false := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) true (Or.inl rfl)
    have hc0 : c = false := by
      have h1 := st_val_const n _ hcl' y true _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc0
    have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
      const_read n _ hcl' y true p g hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := and_core n F gs o p ph (n + 1 + pn) g y L true (hnc true) hgp hop hin hlne hph
      hone ho2 hlx {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpnR
        · exact rc_of_reads hpR ⟨false, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4

end PEqualNP.MetaComplexity.EdgeFn
