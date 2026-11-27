import PEqualNP.MetaComplexity.Helpers.EdgeFnAnd
import PEqualNP.MetaComplexity.Helpers.ReadersPat

/-!
# Run of four, (P-NA): the NOT state at an end either drops five gates or is the NA state

Paper: the run-of-four argument in direct form, section 4 case II.3 and section 5 (P-NA).
Let `gs` be a least list for `F` on `n + 1` inputs, in the NOT state at input `e`: `x_e` is read
only by the NOT gate `pn`, that gate only by the AND gate `pm = AND(pn, ph)`, the gate `ph` only by
`pm`, and `pm` is not the output. If `F` at `x_e := 1` is not constant, then either the
restriction has a circuit five gates smaller, or `pm` has exactly one reader and it is an OR gate
`OR(pm, s)` with `s ≠ pm`.

Proof: the swap device of `EdgeFn.and_core` (the private partner `ph` becomes `NOT x_e`), then at
`x_e := 1` the positions `ph`, `pn`, `pm` read a wire of constant status, and so do two readers of
`pm`, or its single reader `r` (an AND or a NOT gate, constant) and a reader of `r`.
`Least.no_alias` excludes `OR(pm, pm)`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunPNA

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.EdgeFn

/-- In a least list, the AND gate `AND(pn, ph)` has two different operands. -/
theorem pna_ne {m : ℕ} {F : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m F gs o) (hfnc : ∃ x y : Fin m → Bool, F x ≠ F y) (pn pm ph : ℕ) (gm : Gate)
    (hpm : gs[pm]? = some gm) (hmop : gm.op = GateOp.and)
    (hmin : gm.inputs = [m + pn, m + ph] ∨ gm.inputs = [m + ph, m + pn]) : pn ≠ ph := by
  rintro rfl
  have hp : pm < gs.length := (List.getElem?_eq_some_iff.1 hpm).1
  have hmem : m + pn ∈ gm.inputs := by rcases hmin with h | h <;> simp [h]
  apply L.no_alias hfnc pm hp (m + pn) ((L.hcl pm gm hpm).lt _ hmem)
  intro u
  rw [vl_gate gs L.hcl u pm gm hpm, hmop]
  rcases hmin with h | h <;> rw [h] <;> simp [GateOp.eval]

/-- The output of a least list with a gate is its last gate. -/
theorem pna_out_last {m : ℕ} {F : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m F gs o) (hfnc : ∃ x y : Fin m → Bool, F x ≠ F y) (hlen : 0 < gs.length) :
    o = m + (gs.length - 1) := by
  by_contra ho
  obtain ⟨q, hq, hr⟩ := L.live hfnc (gs.length - 1) (by omega) ho
  have := reads_len hr
  omega

theorem pna_card5 (a b c d e : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ({a, b, c, d, e} : Finset ℕ).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_eq_three.2 ⟨c, d, e, hcd, hce, hde, rfl⟩]

/-- (P-NA), core form: the hypotheses the proof reads. -/
theorem pna_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o pn pm ph : ℕ)
    (gm : Gate) (e : Fin (n + 1)) (L : Least (n + 1) F gs o)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x e true) ≠ F (Function.update x' e true))
    (hpn : gs[pn]? = some ⟨GateOp.not, [(e : ℕ)]⟩)
    (hpm : gs[pm]? = some gm) (hmop : gm.op = GateOp.and)
    (hmin : gm.inputs = [n + 1 + pn, n + 1 + ph] ∨ gm.inputs = [n + 1 + ph, n + 1 + pn])
    (hph : ph < gs.length) (hh1 : ∀ t, Reads gs t (n + 1 + ph) → t = pm)
    (ho : o ≠ n + 1 + pm) :
    Drop F e true 5 gs.length ∨
      ∃ (pS : ℕ) (gS : Gate) (s : ℕ), gs[pS]? = some gS ∧ gS.op = GateOp.or ∧
        (gS.inputs = [n + 1 + pm, s] ∨ gS.inputs = [s, n + 1 + pm]) ∧ s ≠ n + 1 + pm ∧
        ∀ t, Reads gs t (n + 1 + pm) → t = pS := by
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨_, _, h⟩
  have hlmem : n + 1 + pn ∈ gm.inputs := by rcases hmin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ gm.inputs := by rcases hmin with h | h <;> simp [h]
  have hp : pm < gs.length := (List.getElem?_eq_some_iff.1 hpm).1
  have hphp : n + 1 + ph < n + 1 + pm := (L.hcl pm gm hpm).lt _ hhmem
  have hpnp : n + 1 + pn < n + 1 + pm := (L.hcl pm gm hpm).lt _ hlmem
  have hlne : n + 1 + pn ≠ n + 1 + ph := by
    intro e'
    apply L.no_alias hfnc pm hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u pm gm hpm, hmop]
    rcases hmin with h | h <;> rw [h, e'] <;> simp [GateOp.eval]
  have hpnph : pn ≠ ph := fun e' => hlne (by rw [e'])
  have ho2 : o ≠ n + 1 + ph := by
    rw [pna_out_last L hfnc (by omega)]
    omega
  -- values in `gs` at `x_e = 1`
  have hpnv : ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x (n + 1 + pn) = false := by
    intro x hx
    rw [vl_not gs L.hcl x pn _ hpn (e : ℕ) rfl rfl, vl_input gs x e e.isLt]
    simp [hx]
  have hpmv : ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x (n + 1 + pm) = false := by
    intro x hx
    rw [vl_gate gs L.hcl x pm gm hpm, hmop]
    rcases hmin with h | h <;> rw [h] <;> simp [GateOp.eval, hpnv x hx]
  have hnot_out : ∀ (r : ℕ) (c : Bool), (∀ x : Fin (n + 1) → Bool, x e = true →
      vl gs x (n + 1 + r) = c) → o ≠ n + 1 + r := by
    intro r c hc e'
    obtain ⟨x, x', hxx⟩ := hnc
    apply hxx
    rw [← L.hev, ← L.hev, e', hc _ (Function.update_self e true x),
      hc _ (Function.update_self e true x')]
  -- the swapped list
  have hcl' := andSwap_clean gs ph e L.hcl hph
  have hgp' : (andSwap gs ph e)[pm]? = some gm := by
    rw [andSwap_get_ne gs ph e pm (by omega)]; exact hpm
  have hpn' : (andSwap gs ph e)[pn]? = some ⟨GateOp.not, [(e : ℕ)]⟩ := by
    rw [andSwap_get_ne gs ph e pn hpnph]; exact hpn
  have hphR : Reads (andSwap gs ph e) ph e := ⟨_, andSwap_get_eq gs ph e hph, by simp⟩
  have hpnR : Reads (andSwap gs ph e) pn e := ⟨_, hpn', by simp⟩
  have hpR : Reads (andSwap gs ph e) pm (n + 1 + pn) := ⟨gm, hgp', hlmem⟩
  have hreads' : ∀ r w, ph < r → Reads gs r w → Reads (andSwap gs ph e) r w := by
    intro r w hr h
    obtain ⟨g', hg', hm⟩ := h
    exact ⟨g', by rw [andSwap_get_ne gs ph e r (by omega)]; exact hg', hm⟩
  obtain ⟨c, hc⟩ := isC_reader hcl' e pn _ hpn' (by simp) true (Or.inl rfl)
  have hc0 : c = false := by
    have h1 := st_val_const n _ hcl' e true _ c hc (fun _ => false)
    rw [vl_not _ hcl' _ pn _ hpn' (e : ℕ) rfl rfl, vl_input _ _ e e.isLt] at h1
    simp [ins] at h1
    exact h1
  subst hc0
  have hcp : IsC n (andSwap gs ph e) e true (n + 1 + pm) :=
    const_read n _ hcl' e true pm gm hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hmop])
  -- the status of `pm` in the swapped list is the constant false
  have hcpf : stF n (andSwap gs ph e) e true (n + 1 + pm) = Stat.const false := by
    obtain ⟨c', hc'⟩ := hcp
    have h1 := st_val_const n _ hcl' e true _ c' hc' (fun _ => false)
    have hv : vl (andSwap gs ph e) (ins e true (fun _ => false)) (n + 1 + pn) = false := by
      rw [vl_not _ hcl' _ pn _ hpn' (e : ℕ) rfl rfl, vl_input _ _ e e.isLt]
      simp [ins]
    rw [vl_gate _ hcl' _ pm gm hgp', hmop] at h1
    have : c' = false := by
      rcases hmin with h | h <;> rw [h] at h1 <;> simp [GateOp.eval, hv] at h1 <;> exact h1
    rw [hc', this]
  have hlx : ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x (n + 1 + pn) = false := hpnv
  have hcore := and_core n F gs o pm ph (n + 1 + pn) gm e L true hnc hpm hmop hmin hlne hph
    hh1 ho2 hlx
  have hbase : ∀ q ∈ ({ph, pn, pm} : Finset ℕ), RC n (andSwap gs ph e) e true q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact rc_input true hphR
    · exact rc_input true hpnR
    · exact rc_of_reads hpR ⟨false, hc⟩
  -- a reader of `pm`
  obtain ⟨r1, hr1p, hr1⟩ := L.live hfnc pm hp ho
  have hr1R := hreads' r1 _ (by omega) hr1
  by_cases htwo : ∃ r2, r2 ≠ r1 ∧ Reads gs r2 (n + 1 + pm)
  · -- two readers of `pm`
    obtain ⟨r2, hr21, hr2⟩ := htwo
    have hr2p : pm < r2 := by have := reads_lt L.hcl hr2; omega
    have hr2R := hreads' r2 _ (by omega) hr2
    left
    have h5 := hcore {ph, pn, pm, r1, r2} (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact hbase _ (by simp)
      · exact hbase _ (by simp)
      · exact hbase _ (by simp)
      · exact rc_of_reads hr1R hcp
      · exact rc_of_reads hr2R hcp)
    rwa [pna_card5 _ _ _ _ _ hpnph.symm (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (Ne.symm hr21)] at h5
  · have hone : ∀ t, Reads gs t (n + 1 + pm) → t = r1 := by
      intro t ht
      by_contra h'
      exact htwo ⟨t, h', ht⟩
    obtain ⟨g1, hg1, hm1⟩ := hr1
    have hg1' : (andSwap gs ph e)[r1]? = some g1 := by
      rw [andSwap_get_ne gs ph e r1 (by omega)]; exact hg1
    have hr1len : r1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    -- a constant single reader: five positions with a reader of it
    have hfive : IsC n (andSwap gs ph e) e true (n + 1 + r1) →
        (∃ c : Bool, ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x (n + 1 + r1) = c) →
        Drop F e true 5 gs.length := by
      intro hcr ⟨c1, hc1⟩
      obtain ⟨r', hr'p, hr'⟩ := L.live hfnc r1 hr1len (hnot_out r1 c1 hc1)
      have hr'R := hreads' r' _ (by omega) hr'
      have h5 := hcore {ph, pn, pm, r1, r'} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact hbase _ (by simp)
        · exact hbase _ (by simp)
        · exact hbase _ (by simp)
        · exact rc_of_reads hr1R hcp
        · exact rc_of_reads hr'R hcr)
      rwa [pna_card5 _ _ _ _ _ hpnph.symm (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)] at h5
    rcases L.hcl r1 g1 hg1 with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
    · -- a NOT reader
      left
      rw [hin, List.mem_singleton] at hm1
      subst hm1
      refine hfive (st_allconst n _ hcl' e true r1 g1 hg1' (by
        intro a ha
        rw [hin, List.mem_singleton] at ha
        subst ha
        exact hcp)) ⟨true, fun x hx => ?_⟩
      rw [vl_gate gs L.hcl x r1 g1 hg1, hop, hin]
      simp [GateOp.eval, hpmv x hx]
    · -- an AND reader
      left
      refine hfive (const_read n _ hcl' e true r1 g1 hg1' (n + 1 + pm) hm1
        (by simp [hcpf, fixBit, hop])) ⟨false, fun x hx => ?_⟩
      rw [vl_gate gs L.hcl x r1 g1 hg1, hop, hin]
      rw [hin] at hm1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
      rcases hm1 with rfl | rfl <;> simp [GateOp.eval, hpmv x hx]
    · -- an OR reader: the NA state
      right
      have hnal : ¬ (j = n + 1 + pm ∧ k = n + 1 + pm) := by
        rintro ⟨rfl, rfl⟩
        apply L.no_alias hfnc r1 hr1len (n + 1 + pm) (by omega)
        intro u
        rw [vl_gate gs L.hcl u r1 g1 hg1, hop, hin]
        simp [GateOp.eval]
      rw [hin] at hm1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
      rcases hm1 with rfl | rfl
      · exact ⟨r1, g1, k, hg1, hop, Or.inl hin, fun h => hnal ⟨rfl, h⟩, hone⟩
      · exact ⟨r1, g1, j, hg1, hop, Or.inr hin, fun h => hnal ⟨h, rfl⟩, hone⟩

/-- (P-NA). A least list for `F` on `n + 1` inputs, in the NOT state at input `e`: `x_e` is read
only by the NOT gate at `pn`, that gate only by the AND gate `gm` at `pm` whose inputs are the NOT
gate and the gate at `ph`, the gate at `ph` only by `pm`, and `pm` is not the output. If `F` at
`x_e := 1` is not constant, then either the restriction has a circuit five gates smaller, or `pm`
has exactly one reader, at `pS`, and it is an OR gate reading `pm` and a wire `s ≠ pm`. -/
theorem pna_main (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o pn pm ph : ℕ)
    (gm : Gate) (e : Fin (n + 1)) (L : Least (n + 1) F gs o)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x e true) ≠ F (Function.update x' e true))
    (hpn : gs[pn]? = some ⟨GateOp.not, [(e : ℕ)]⟩) (_he1 : ∀ t, Reads gs t e → t = pn)
    (hpm : gs[pm]? = some gm) (hmop : gm.op = GateOp.and)
    (hmin : gm.inputs = [n + 1 + pn, n + 1 + ph] ∨ gm.inputs = [n + 1 + ph, n + 1 + pn])
    (_hn1 : ∀ t, Reads gs t (n + 1 + pn) → t = pm)
    (hph : ph < gs.length) (hh1 : ∀ t, Reads gs t (n + 1 + ph) → t = pm)
    (ho : o ≠ n + 1 + pm) :
    Drop F e true 5 gs.length ∨
      ∃ (pS : ℕ) (gS : Gate) (s : ℕ), gs[pS]? = some gS ∧ gS.op = GateOp.or ∧
        (gS.inputs = [n + 1 + pm, s] ∨ gS.inputs = [s, n + 1 + pm]) ∧ s ≠ n + 1 + pm ∧
        ∀ t, Reads gs t (n + 1 + pm) → t = pS :=
  pna_core n F gs o pn pm ph gm e L hnc hpn hpm hmop hmin hph hh1 ho

/-- A position that reads `w` in the sense of `L-meta-588` (a NOT gate by its first input, any
other gate by any input) reads it in the sense of `Readers.Reads`. -/
theorem pna_rd (gs : List Gate) (o w : ℕ) (j : Fin (Circuit.mk gs o).gates.length)
    (h : ((Circuit.mk gs o).gates.get j).op = GateOp.not ∧
        ((Circuit.mk gs o).gates.get j).inputs.head? = some w ∨
      ((Circuit.mk gs o).gates.get j).op ≠ GateOp.not ∧ w ∈ ((Circuit.mk gs o).gates.get j).inputs) :
    Reads gs j.val w := by
  refine ⟨(Circuit.mk gs o).gates.get j, by simp, ?_⟩
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact List.mem_of_mem_head? h
  · exact h

/-- The gate at a position, read through `List.get`. -/
theorem pna_get (gs : List Gate) (o p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ q : Fin (Circuit.mk gs o).gates.length, q.val = p ∧ (Circuit.mk gs o).gates.get q = g := by
  obtain ⟨hl, hg⟩ := List.getElem?_eq_some_iff.1 hp
  exact ⟨⟨p, hl⟩, rfl, by simpa using hg⟩

/-- The second disjunct of `pna_main` (with the NOT state) supplies the structural hypotheses of
`L-meta-588` for the circuit `Circuit.mk gs o`: fan-in two, the NOT gate on `e`, the AND gate
reading it, the OR gate reading that, the three single-reader clauses in the reader form of
`L-meta-588`, and the private partner `ph` with its single reader. The hypothesis `pn ≠ ph` holds
at a least list (`pna_ne`). -/
theorem pna_to_588 (n : ℕ) (gs : List Gate) (o : ℕ) (e : Fin (n + 1)) (pn pm ph pS : ℕ)
    (gm gS : Gate) (hcl : CleanL (n + 1) gs) (hpnph : pn ≠ ph)
    (hpn : gs[pn]? = some ⟨GateOp.not, [(e : ℕ)]⟩) (he1 : ∀ t, Reads gs t e → t = pn)
    (hpm : gs[pm]? = some gm) (hmop : gm.op = GateOp.and)
    (hmin : gm.inputs = [n + 1 + pn, n + 1 + ph] ∨ gm.inputs = [n + 1 + ph, n + 1 + pn])
    (hn1 : ∀ t, Reads gs t (n + 1 + pn) → t = pm)
    (hph : ph < gs.length) (hh1 : ∀ t, Reads gs t (n + 1 + ph) → t = pm)
    (hpS : gs[pS]? = some gS) (hSop : gS.op = GateOp.or) (hSin : n + 1 + pm ∈ gS.inputs)
    (hm1 : ∀ t, Reads gs t (n + 1 + pm) → t = pS) :
    FanInTwo (Circuit.mk gs o) ∧
    ∃ pn' pm' pS' ph' : Fin (Circuit.mk gs o).gates.length,
      pn'.val = pn ∧ pm'.val = pm ∧ pS'.val = pS ∧ ph'.val = ph ∧
      ((Circuit.mk gs o).gates.get pn').op = GateOp.not ∧
      ((Circuit.mk gs o).gates.get pn').inputs.head? = some e.val ∧
      ((Circuit.mk gs o).gates.get pm').op = GateOp.and ∧
      n + 1 + pn'.val ∈ ((Circuit.mk gs o).gates.get pm').inputs ∧
      ((Circuit.mk gs o).gates.get pS').op = GateOp.or ∧
      n + 1 + pm'.val ∈ ((Circuit.mk gs o).gates.get pS').inputs ∧
      (∀ j : Fin (Circuit.mk gs o).gates.length,
        (((Circuit.mk gs o).gates.get j).op = GateOp.not ∧
            ((Circuit.mk gs o).gates.get j).inputs.head? = some (e.val) ∨
          ((Circuit.mk gs o).gates.get j).op ≠ GateOp.not ∧
            (e.val) ∈ ((Circuit.mk gs o).gates.get j).inputs) → j = pn') ∧
      (∀ j : Fin (Circuit.mk gs o).gates.length,
        (((Circuit.mk gs o).gates.get j).op = GateOp.not ∧
            ((Circuit.mk gs o).gates.get j).inputs.head? = some (n + 1 + pn'.val) ∨
          ((Circuit.mk gs o).gates.get j).op ≠ GateOp.not ∧
            (n + 1 + pn'.val) ∈ ((Circuit.mk gs o).gates.get j).inputs) → j = pm') ∧
      (∀ j : Fin (Circuit.mk gs o).gates.length,
        (((Circuit.mk gs o).gates.get j).op = GateOp.not ∧
            ((Circuit.mk gs o).gates.get j).inputs.head? = some (n + 1 + pm'.val) ∨
          ((Circuit.mk gs o).gates.get j).op ≠ GateOp.not ∧
            (n + 1 + pm'.val) ∈ ((Circuit.mk gs o).gates.get j).inputs) → j = pS') ∧
      ph' ≠ pn' ∧ n + 1 + ph'.val ∈ ((Circuit.mk gs o).gates.get pm').inputs ∧
      (∀ j : Fin (Circuit.mk gs o).gates.length,
        (((Circuit.mk gs o).gates.get j).op = GateOp.not ∧
            ((Circuit.mk gs o).gates.get j).inputs.head? = some (n + 1 + ph'.val) ∨
          ((Circuit.mk gs o).gates.get j).op ≠ GateOp.not ∧
            (n + 1 + ph'.val) ∈ ((Circuit.mk gs o).gates.get j).inputs) → j = pm') := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact ⟨by rw [hop]; simp, by rw [hin]; simp⟩
    · refine ⟨?_, by rw [hin]; simp⟩
      rcases hop with hop | hop <;> rw [hop] <;> simp
  obtain ⟨pn', rfl, hgn⟩ := pna_get gs o pn _ hpn
  obtain ⟨pm', rfl, hgm⟩ := pna_get gs o pm gm hpm
  obtain ⟨pS', rfl, hgS⟩ := pna_get gs o pS gS hpS
  have hphl : ph < (Circuit.mk gs o).gates.length := hph
  refine ⟨pn', pm', pS', ⟨ph, hphl⟩, rfl, rfl, rfl, rfl, by rw [hgn], by rw [hgn]; rfl,
    by rw [hgm]; exact hmop, by rw [hgm]; rcases hmin with h | h <;> simp [h],
    by rw [hgS]; exact hSop, by rw [hgS]; exact hSin,
    fun j hj => Fin.ext (he1 _ (pna_rd gs o _ j hj)),
    fun j hj => Fin.ext (hn1 _ (pna_rd gs o _ j hj)),
    fun j hj => Fin.ext (hm1 _ (pna_rd gs o _ j hj)), ?_,
    by rw [hgm]; rcases hmin with h | h <;> simp [h],
    fun j hj => Fin.ext (hh1 _ (pna_rd gs o _ j hj))⟩
  intro h
  exact hpnph (congrArg Fin.val h).symm

end PEqualNP.MetaComplexity.Helpers.RunPNA
