import PEqualNP.MetaComplexity.Helpers.MachineOwnBlk

/-!
# Helper module (proofs only): the owner lists in rounds are polynomial-time computable

The input code is `encL t ++ encodeCNF ψ`: the code of `ψ` is `dropL` of it, `E` and `k` are the
first two entries of `takeL` of it. The rounds are a loop over the clauses `i`, inside it a loop
over the items `j ≤ w i`, each writing `blkO` (`ICtx.blk`); then the fixed tail. The whole list
is written as `flatS (ownO E k ψ) ++ [false]`, its code.
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.CircuitLowerBounds

/-- The input type of the row. -/
abbrev InO : Type :=
  List ℕ × {φ : CNF // ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : Clause => c.length + 1)).sum}

/-- The input code of the row. -/
def eaO : InO → List Bool := fun p =>
  encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ encodeCNF p.2.1

theorem eaO_eq (p : InO) : eaO p = encNs p.1 ++ false :: encodeCNF p.2.1 := by
  simp [eaO, encodeList_unary, encL]

theorem sp0_x : SP (fun _ => True) eaO (fun p => encodeCNF p.2.1) :=
  (sp_id.post cpt_dropL).congr (fun p _ => by rw [eaO_eq, dropL_encNs])

theorem sp0_E : SP (fun _ => True) eaO (fun p => un (p.1.getD 0 0)) :=
  (((sp_id.post cpt_takeL).post cpt_hd).post cpt_tail).congr (fun p _ => by
    rw [eaO_eq, takeL_encNs]
    have := lookup_spec 0 p.1
    simpa using this)

theorem sp0_K : SP (fun _ => True) eaO (fun p => un (p.1.getD 1 0)) :=
  ((((sp_id.post cpt_takeL).post cpt_dropN).post cpt_hd).post cpt_tail).congr (fun p _ => by
    rw [eaO_eq, takeL_encNs]
    have := lookup_spec 1 p.1
    simpa using this)

theorem sp0_rounds : SP (fun _ => True) eaO (fun p => flatS ((List.range p.2.1.length).flatMap
    (fun i : ℕ => (List.range (wO p.2.1 i + 1)).flatMap
      (fun j : ℕ => blkO (p.1.getD 0 0) (p.1.getD 1 0) p.2.1 i j)))) := by
  let D1 : InO × ℕ → Prop := fun q => True ∧ q.2 < q.1.2.1.length
  let D2 : (InO × ℕ) × ℕ → Prop := fun r => D1 r.1 ∧ r.2 < wO r.1.1.2.1 r.1.2 + 1
  have up2 : ∀ {F : InO → List Bool}, SP (fun _ => True) eaO F →
      SP D2 (ext (ext eaO)) (fun r => F r.1.1) :=
    fun h => (h.up (D' := D1) (fun _ _ => trivial)).up (fun r hr => hr.1)
  have c : ICtx D2 (ext (ext eaO)) (fun r => r.1.1.2.1) (fun r => r.1.1.1.getD 0 0)
      (fun r => r.1.1.1.getD 1 0) (fun r => r.1.2) (fun r => r.2) :=
    ⟨up2 sp0_x, up2 sp0_E, up2 sp0_K, sp_idx.up (fun r hr => hr.1), sp_idx,
      fun r hr => ⟨hr.1.2, by have := hr.2; omega, r.1.1.2.2⟩⟩
  have hblk : SP D2 (ext (ext eaO)) (fun r => flatS (blkO (r.1.1.1.getD 0 0) (r.1.1.1.getD 1 0)
      r.1.1.2.1 r.1.2 r.2)) := c.blk
  have hN : SP D1 (ext eaO) (fun q => un (wO q.1.2.1 q.2 + 1)) :=
    (sp_w (sp0_x.up (fun _ _ => trivial)) sp_idx).add (sp_num 1)
  have h2 : SP D1 (ext eaO) (fun q => (List.range (wO q.1.2.1 q.2 + 1)).flatMap
      (fun j => flatS (blkO (q.1.1.getD 0 0) (q.1.1.getD 1 0) q.1.2.1 q.2 j))) :=
    SP.loop (D := D1) (ea := ext eaO) (N := fun q => wO q.1.2.1 q.2 + 1)
      (B := fun q j => flatS (blkO (q.1.1.getD 0 0) (q.1.1.getD 1 0) q.1.2.1 q.2 j)) hN hblk
  have h1 : SP (fun _ => True) eaO (fun p => (List.range p.2.1.length).flatMap (fun i =>
      (List.range (wO p.2.1 i + 1)).flatMap
        (fun j => flatS (blkO (p.1.getD 0 0) (p.1.getD 1 0) p.2.1 i j)))) :=
    SP.loop (D := fun _ => True) (ea := eaO) (N := fun p => p.2.1.length)
      (B := fun p i => (List.range (wO p.2.1 i + 1)).flatMap
        (fun j => flatS (blkO (p.1.getD 0 0) (p.1.getD 1 0) p.2.1 i j))) (sp_ncl sp0_x) h2
  refine h1.congr (fun p _ => ?_)
  simp only [flatS_flatMap]

theorem sp0_tail : SP (fun _ => True) eaO
    (fun p => flatS (tailO (p.1.getD 0 0) (p.1.getD 1 0) p.2.1)) := by
  have hE := sp0_E
  have hK := sp0_K
  have h2E : SP (fun _ => True) eaO (fun p => un (2 * p.1.getD 0 0)) := (sp_num 2).mul hE
  have h2E1 : SP (fun _ => True) eaO (fun p => un (2 * p.1.getD 0 0 + 1)) := h2E.add (sp_num 1)
  have h3E2 : SP (fun _ => True) eaO (fun p => un (3 * p.1.getD 0 0 + 2)) :=
    ((sp_num 3).mul hE).add (sp_num 2)
  have h2K : SP (fun _ => True) eaO (fun p => un (2 * p.1.getD 1 0)) := (sp_num 2).mul hK
  have i1 := sp_inner (B := fun _ => false) hE hK h2E h2E1 (sp_const (bflag false))
  have i2 := sp_inner (B := fun _ => false) hE hK h2E h3E2 (sp_const (bflag false))
  let D1 : InO × ℕ → Prop := fun q => True ∧ q.2 < q.1.2.1.length
  have up1 : ∀ {F : InO → List Bool}, SP (fun _ => True) eaO F → SP D1 (ext eaO) (fun q => F q.1) :=
    fun h => h.up (fun _ _ => trivial)
  have hb : SP D1 (ext eaO) (fun q => encN (XO (q.1.1.getD 0 0) (q.1.1.getD 1 0)
      (2 * q.1.1.getD 0 0 + 1) (posO (q.1.1.getD 0 0) q.1.2.1 q.2 (wO q.1.2.1 q.2)) 1)) :=
    (sp_X (up1 hE) (up1 hK) (up1 h2E1)
      (sp_pos (up1 hE) (sp_off (up1 sp0_x) sp_idx (fun q hq => hq.2.le))
        (sp_w (up1 sp0_x) sp_idx)) (sp_num 1)).encN
  have hl : SP (fun _ => True) eaO (fun p => encNs ((List.range p.2.1.length).map
      (fun i : ℕ => XO (p.1.getD 0 0) (p.1.getD 1 0) (2 * p.1.getD 0 0 + 1)
        (posO (p.1.getD 0 0) p.2.1 i (wO p.2.1 i)) 1))) :=
    (SP.loop (B := fun p i => encN (XO (p.1.getD 0 0) (p.1.getD 1 0) (2 * p.1.getD 0 0 + 1)
        (posO (p.1.getD 0 0) p.2.1 i (wO p.2.1 i)) 1)) (sp_ncl sp0_x) hb).congr
      (fun p _ => by rw [encNs_map])
  have l3 : SP (fun _ => True) eaO (fun p => flatS [(2 * p.1.getD 0 0 + 1) ::
      XO (p.1.getD 0 0) (p.1.getD 1 0) (2 * p.1.getD 0 0) (2 * p.1.getD 0 0 + 1) (2 * p.1.getD 1 0) ::
      (List.range p.2.1.length).map (fun i : ℕ => XO (p.1.getD 0 0) (p.1.getD 1 0)
        (2 * p.1.getD 0 0 + 1) (posO (p.1.getD 0 0) p.2.1 i (wO p.2.1 i)) 1)]) :=
    ((sp_const [true]).app ((h2E1.encN.app ((sp_X hE hK h2E h2E1 h2K).encN.app hl)).app
      (sp_const [false]))).congr (fun p _ => by
        rw [flatS_single]; simp only [encNs_cons, List.append_assoc, List.cons_append,
          List.singleton_append, List.nil_append])
  have l4 : SP (fun _ => True) eaO (fun p => flatS [[3 * p.1.getD 0 0 + 2,
      XO (p.1.getD 0 0) (p.1.getD 1 0) (2 * p.1.getD 0 0) (3 * p.1.getD 0 0 + 2) (2 * p.1.getD 1 0)]]) :=
    ((sp_const [true]).app ((h3E2.encN.app (sp_X hE hK h2E h3E2 h2K).encN).app
      (sp_const [false]))).congr (fun p _ => by
        rw [flatS_single]; simp only [encNs_cons, encNs_nil, List.append_assoc, List.cons_append,
          List.singleton_append, List.nil_append, List.append_nil])
  refine (((i1.app i2).app l3).app l4).congr (fun p _ => ?_)
  simp only [tailO, flatS_append]

/-- The row, with the function named `ownO` (it unfolds to the statement's function). -/
theorem own_main : ComputableInPolyTime eaO
    (encodeList (encodeList (fun a : ℕ => List.replicate a true ++ [false])))
    (fun p : InO => ownO (p.1.getD 0 0) (p.1.getD 1 0) p.2.1) := by
  refine cpt_of_SP ((sp0_rounds.app sp0_tail).app (sp_const [false]) |>.congr (fun p _ => ?_))
  rw [encodeList_LL, ownO_eq, flatS_append]

end PEqualNP.MetaComplexity.MachineOwn
