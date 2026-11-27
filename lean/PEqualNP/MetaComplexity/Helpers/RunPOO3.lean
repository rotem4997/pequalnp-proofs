import PEqualNP.MetaComplexity.Helpers.RunPOO2

/-!
# Run-of-four assembly, (P-OO) part 3: the u-condition and `poo_main`
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- A wire of constant status that is true at every point with `x_e = 1` has status `true`. -/
theorem poo_stT {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) (e : Fin (n + 1)) (a : ℕ)
    (hc : IsC n gs e true a) (hv : ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x a = true) :
    stF n gs e true a = Stat.const true := by
  obtain ⟨c, hc⟩ := hc
  have h1 := st_val_const n gs hcl e true a c hc (fun _ => false)
  have h2 := hv (Fin.insertNth e true (fun _ : Fin n => false)) (by simp)
  rw [hc] at *
  have : c = true := by rw [← h1]; exact h2
  rw [this]

/-- The operand condition of shape (i) at `p`: `u` is an input or has a second reader, else
a chain (not least) or a fifth gate. -/
theorem poo_ucond {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc1 : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e true) ≠ f (Function.update y e true))
    (h5 : ¬ Drop f e true 5 gs.length)
    (p q R R' : ℕ) (gp gq : Gate) (u u' : ℕ)
    (hgp : gs[p]? = some gp) (hop : gp.op = GateOp.or)
    (hinp : gp.inputs = [(e : ℕ), u] ∨ gp.inputs = [u, (e : ℕ)])
    (hgq : gs[q]? = some gq) (hoq : gq.op = GateOp.or)
    (hinq : gq.inputs = [(e : ℕ), u'] ∨ gq.inputs = [u', (e : ℕ)]) (hpq : p ≠ q)
    (hR : Reads gs R (n + 1 + p)) (honly : ∀ t, Reads gs t (n + 1 + p) → t = R)
    (hR' : Reads gs R' (n + 1 + q)) (honly' : ∀ t, Reads gs t (n + 1 + q) → t = R')
    (hRR : R ≠ R') : u < n + 1 ∨ ∃ t, t ≠ p ∧ Reads gs t u := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  by_contra hn
  push Not at hn
  obtain ⟨hge, hnone⟩ := hn
  have hep : Reads gs p e := ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  have heq : Reads gs q e := ⟨gq, hgq, by rcases hinq with h | h <;> rw [h] <;> simp⟩
  have hup : u < n + 1 + p :=
    (hcl p gp hgp).lt u (by rcases hinp with h | h <;> rw [h] <;> simp)
  obtain ⟨j, rfl⟩ : ∃ j, u = n + 1 + j := ⟨u - (n + 1), by omega⟩
  have hjsole : ∀ t, Reads gs t (n + 1 + j) → t = p := by
    intro t ht
    by_contra htp
    exact hnone t htp ht
  have hpR : p < R := by have := reads_lt hcl hR; omega
  have hqR' : q < R' := by have := reads_lt hcl hR'; omega
  have hpu : Reads gs p (n + 1 + j) :=
    ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  by_cases hjq : j = q
  · subst hjq
    exact L.no_tri hfnc j p e heq hep hpu
  by_cases hjR' : j = R'
  · subst hjR'
    exact poo_chain L hfnc e q p j gq gp u' hgq hoq hinq hgp hop hinp hR' honly' hjsole
  have hRq : R ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p R e hep heq hR
  have hR'p : R' ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q R' e heq hep hR'
  exact h5 (poo_dead L e hnc1 j p q R R' gp gq hgp hop hinp hgq hoq
    (by rcases hinq with h | h <;> rw [h] <;> simp) hjsole hR hR' (by omega) hjq
    hjR' hpq (by omega) (Ne.symm hR'p) (Ne.symm hRq) (by omega) hRR)

/-- Case B: with no common reader, the reader of `G_p` is unique (else a fifth gate). -/
theorem poo_sole {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc1 : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e true) ≠ f (Function.update y e true))
    (h5 : ¬ Drop f e true 5 gs.length)
    (p q J J' : ℕ) (gp gq : Gate) (u u' : ℕ)
    (hgp : gs[p]? = some gp) (hop : gp.op = GateOp.or)
    (hinp : gp.inputs = [(e : ℕ), u] ∨ gp.inputs = [u, (e : ℕ)])
    (hgq : gs[q]? = some gq) (hoq : gq.op = GateOp.or)
    (hinq : gq.inputs = [(e : ℕ), u'] ∨ gq.inputs = [u', (e : ℕ)]) (hpq : p ≠ q)
    (hJ : Reads gs J (n + 1 + p)) (hJrc : RC n gs e true J)
    (hJ' : Reads gs J' (n + 1 + q)) (hJ'rc : RC n gs e true J') (hJJ' : J ≠ J')
    (hcom : ∀ S, Reads gs S (n + 1 + p) → ¬ Reads gs S (n + 1 + q)) :
    ∀ t, Reads gs t (n + 1 + p) → t = J := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hep : Reads gs p e := ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  have heq : Reads gs q e := ⟨gq, hgq, by rcases hinq with h | h <;> rw [h] <;> simp⟩
  have hrcp : RC n gs e true p := rc_input true hep
  have hrcq : RC n gs e true q := rc_input true heq
  have hcp : IsC n gs e true (n + 1 + p) := isC_reader hcl e p gp hgp
    (by rcases hinp with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hop]))
  have hpJ : p < J := by have := reads_lt hcl hJ; omega
  have hqJ' : q < J' := by have := reads_lt hcl hJ'; omega
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J e hep heq hJ
  have hJ'p : J' ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J' e heq hep hJ'
  intro t ht
  by_contra htJ
  have hpt : p < t := by have := reads_lt hcl ht; omega
  have htq : t ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p t e hep heq ht
  have htJ' : t ≠ J' := by
    rintro rfl
    exact hcom t ht hJ'
  exact h5 (poo_save5 L e true hnc1 p q J J' t hpq (by omega) (Ne.symm hJ'p) (by omega)
    (Ne.symm hJq) (by omega) (Ne.symm htq) hJJ' (Ne.symm htJ) (Ne.symm htJ')
    hrcp hrcq hJrc hJ'rc (rc_of_reads ht hcp))

/-- The unique reader of `G_p` is an AND gate (a NOT or OR reader is a constant: `poo_route`). -/
theorem poo_andR {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc1 : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e true) ≠ f (Function.update y e true))
    (h5 : ¬ Drop f e true 5 gs.length)
    (p q R R' : ℕ) (gp gq : Gate) (u u' : ℕ)
    (hgp : gs[p]? = some gp) (hop : gp.op = GateOp.or)
    (hinp : gp.inputs = [(e : ℕ), u] ∨ gp.inputs = [u, (e : ℕ)])
    (hgq : gs[q]? = some gq) (hoq : gq.op = GateOp.or)
    (hinq : gq.inputs = [(e : ℕ), u'] ∨ gq.inputs = [u', (e : ℕ)]) (hpq : p ≠ q)
    (hR : Reads gs R (n + 1 + p)) (honly : ∀ t, Reads gs t (n + 1 + p) → t = R)
    (hR' : Reads gs R' (n + 1 + q)) (hRR' : R ≠ R') :
    ∃ g w, gs[R]? = some g ∧ g.op = GateOp.and ∧
      (g.inputs = [n + 1 + p, w] ∨ g.inputs = [w, n + 1 + p]) := by
  have hcl := L.hcl
  have hep : Reads gs p e := ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  have hcp : IsC n gs e true (n + 1 + p) := isC_reader hcl e p gp hgp
    (by rcases hinp with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hop]))
  have hvp : ∀ x : Fin (n + 1) → Bool, x e = true → vl gs x (n + 1 + p) = true := by
    intro x hx
    rw [poo_vl_or hcl x hgp hop hinp, vl_input gs x e e.isLt]
    simp [hx]
  obtain ⟨gR, hgR, hinR⟩ := hR
  rcases gate_cases gs hcl R gR hgR (n + 1 + p) hinR with ⟨hnot, hin1, -⟩ | ⟨w, hin1, hcase⟩
  · exfalso
    refine poo_route L e hnc1 h5 p q R R' gp gq u u' hgp hop hinp hgq hoq hinq hpq
      ⟨gR, hgR, hinR⟩ honly hR' hRR' ?_
    exact st_allconst n gs hcl e true R gR hgR (fun a ha => by
      rw [hin1] at ha; simp at ha; rw [ha]; exact hcp)
  · rcases hcase with ⟨hand, -⟩ | ⟨hor, -⟩
    · exact ⟨gR, w, hgR, hand, hin1⟩
    · exfalso
      refine poo_route L e hnc1 h5 p q R R' gp gq u u' hgp hop hinp hgq hoq hinq hpq
        ⟨gR, hgR, hinR⟩ honly hR' hRR' ?_
      exact const_read n gs hcl e true R gR hgR (n + 1 + p) hinR (by
        rw [poo_stT hcl e _ hcp hvp]; simp [fixBit, hor])

/-- (P-OO): Lemma OO4 in direct form on a least list. -/
theorem poo_main : AsmPOO := by
  intro n f gs o e p1 p2 g1 g2 u1 u2 L hnc1 hg1 ho1 hu1 hg2 ho2 hu2 h12 hall
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h5, hS⟩ := hcon
  have hcl := L.hcl
  have hep : Reads gs p1 e := ⟨g1, hg1, by rcases hu1 with h | h <;> rw [h] <;> simp⟩
  have heq : Reads gs p2 e := ⟨g2, hg2, by rcases hu2 with h | h <;> rw [h] <;> simp⟩
  have hrcp : RC n gs e true p1 := rc_input true hep
  have hrcq : RC n gs e true p2 := rc_input true heq
  have hcp : IsC n gs e true (n + 1 + p1) := isC_reader hcl e p1 g1 hg1
    (by rcases hu1 with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, ho1]))
  have hcq : IsC n gs e true (n + 1 + p2) := isC_reader hcl e p2 g2 hg2
    (by rcases hu2 with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, ho2]))
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  by_cases hcom : ∃ S, Reads gs S (n + 1 + p1) ∧ Reads gs S (n + 1 + p2)
  · obtain ⟨S, hS1, hS2⟩ := hcom
    exact poo_caseA L e hnc1 h5 p1 p2 S g1 g2 u1 u2 hg1 ho1 hu1 hg2 ho2 hu2 h12 hS1 hS2
  push Not at hcom
  obtain ⟨J1, hp1J1, hJ1r, hJ1rc⟩ := L.next e true hnc1 p1
    (List.getElem?_eq_some_iff.1 hg1).1 hcp
  obtain ⟨J2, hp2J2, hJ2r, hJ2rc⟩ := L.next e true hnc1 p2
    (List.getElem?_eq_some_iff.1 hg2).1 hcq
  have hJJ : J1 ≠ J2 := fun h => hcom J1 hJ1r (h ▸ hJ2r)
  have hsole1 := poo_sole L e hnc1 h5 p1 p2 J1 J2 g1 g2 u1 u2 hg1 ho1 hu1 hg2 ho2 hu2 h12
    hJ1r hJ1rc hJ2r hJ2rc hJJ hcom
  have hsole2 := poo_sole L e hnc1 h5 p2 p1 J2 J1 g2 g1 u2 u1 hg2 ho2 hu2 hg1 ho1 hu1 (Ne.symm h12)
    hJ2r hJ2rc hJ1r hJ1rc (Ne.symm hJJ) (fun S h1 h2 => hcom S h2 h1)
  obtain ⟨gJ1, w1, hgJ1, hand1, hin1⟩ := poo_andR L e hnc1 h5 p1 p2 J1 J2 g1 g2 u1 u2 hg1 ho1 hu1
    hg2 ho2 hu2 h12 hJ1r hsole1 hJ2r hJJ
  obtain ⟨gJ2, w2, hgJ2, hand2, hin2⟩ := poo_andR L e hnc1 h5 p2 p1 J2 J1 g2 g1 u2 u1 hg2 ho2 hu2
    hg1 ho1 hu1 (Ne.symm h12) hJ2r hsole2 hJ1r (Ne.symm hJJ)
  have hc1 := poo_ucond L e hnc1 h5 p1 p2 J1 J2 g1 g2 u1 u2 hg1 ho1 hu1 hg2 ho2 hu2 h12 hJ1r hsole1
    hJ2r hsole2 hJJ
  have hc2 := poo_ucond L e hnc1 h5 p2 p1 J2 J1 g2 g1 u2 u1 hg2 ho2 hu2 hg1 ho1 hu1 (Ne.symm h12)
    hJ2r hsole2 hJ1r hsole1 (Ne.symm hJJ)
  exact hS ⟨J1, J2, gJ1, gJ2, w1, w2, hJJ, hp1J1, hp2J2, hgJ1, hand1, hin1, hgJ2, hand2, hin2,
    hsole1, hsole2, hc1, hc2⟩

end PEqualNP.MetaComplexity.Helpers.RunAsm
