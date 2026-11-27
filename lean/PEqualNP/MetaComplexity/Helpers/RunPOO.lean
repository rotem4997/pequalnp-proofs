import PEqualNP.MetaComplexity.Helpers.RunAsm6

/-!
# Run-of-four assembly, (P-OO) part 1: tools

* `poo_out_ne`: a wire that some gate reads is not the output of a least list.
* `poo_swap`: replace gate `a` (its value may change) and its only reader `s` (its value is kept),
  and a gate `d` loses all readers: not least.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- The output of a least list is its last gate, which nobody reads. -/
theorem poo_out_ne {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {q a : ℕ}
    (h : Reads gs q (m + a)) : o ≠ m + a := by
  intro ho
  have hq := reads_len h
  have hlt := reads_lt L.hcl h
  have hl : a < q := by omega
  obtain ⟨q', hq', hr⟩ := L.live hnc (gs.length - 1) (by omega) (by omega)
  have := reads_len hr
  omega

/-- Replace gate `a` (value may change) and its only reader `s` (value kept); gate `d` loses
all its readers: contradiction with least. -/
theorem poo_swap {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (a s d : ℕ) (has : a < s)
    (ga' gs' : Gate) (hsr : Reads gs s (m + a))
    (hread : ∀ r, r ≠ s → ¬ Reads gs r (m + a))
    (hca : CleanGate (m + a) ga') (hcs : CleanGate (m + s) gs')
    (hval : ∀ x : Fin m → Bool, ∀ v : ℕ → Bool, (∀ w, w < m + s → w ≠ m + a → v w = vl gs x w) →
      v (m + a) = ga'.op.eval (ga'.inputs.map v) →
      gs'.op.eval (gs'.inputs.map v) = vl gs x (m + s))
    (hd : d < gs.length) (hdo : o ≠ m + d) (hda : d ≠ a) (hds : d ≠ s)
    (hdr : ∀ r, r ≠ a → r ≠ s → ¬ Reads gs r (m + d))
    (hda' : (m + d) ∉ ga'.inputs) (hds' : (m + d) ∉ gs'.inputs) : False := by
  classical
  have hslen := reads_len hsr
  obtain ⟨gsa, hgsa⟩ : ∃ g, gs[a]? = some g := ⟨gs[a], List.getElem?_eq_getElem (by omega)⟩
  let gs1 := (gs.set a ga').set s gs'
  have hlen1 : gs1.length = gs.length := by simp [gs1]
  have get_s : gs1[s]? = some gs' := by simp [gs1, hslen]
  have get_a : gs1[a]? = some ga' := by
    simp only [gs1]
    rw [List.getElem?_set_ne (by omega)]
    simp [show a < gs.length by omega]
  have get_r : ∀ r, r ≠ a → r ≠ s → gs1[r]? = gs[r]? := by
    intro r h1 h2
    simp only [gs1]
    rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
  have hcl1 : CleanL m gs1 := by
    intro r g hr
    by_cases h1 : r = s
    · subst h1; rw [get_s] at hr; cases hr; exact hcs
    · by_cases h2 : r = a
      · subst h2; rw [get_a] at hr; cases hr; exact hca
      · rw [get_r r h2 h1] at hr; exact L.hcl r g hr
  have hag : ∀ x : Fin m → Bool, ∀ w, w ≠ m + a → vl gs1 x w = vl gs x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < m
      · rw [vl_input gs1 x w hwk, vl_input gs x w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = m + r := ⟨w - m, by omega⟩
        have hra : r ≠ a := fun e => hw (by rw [e])
        by_cases hrs : r = s
        · subst hrs
          rw [vl_gate gs1 hcl1 x r gs' get_s]
          have hv := hval x (vl gs1 x) (fun w' hw' hne => ih w' hw' hne) (by
            rw [vl_gate gs1 hcl1 x a ga' get_a])
          rw [hv]
        · cases hr : gs[r]? with
          | none =>
            have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
            rw [vl_beyond gs1 x _ (by omega), vl_beyond gs x _ (by omega)]
          | some g' =>
            have hr' : gs1[r]? = some g' := by rw [get_r r hra hrs]; exact hr
            rw [vl_gate gs1 hcl1 x r g' hr', vl_gate gs L.hcl x r g' hr]
            congr 1
            apply List.map_congr_left
            intro a' ha'
            have hlt := (L.hcl r g' hr).lt a' ha'
            exact ih a' hlt (fun e => hread r hrs ⟨g', hr, e ▸ ha'⟩)
  have hoa : o ≠ m + a := poo_out_ne L hnc (show Reads gs s (m + a) from hsr)
  have hdead : ∀ q, ¬ Reads gs1 q (m + d) := by
    rintro q ⟨g, hg, hin⟩
    by_cases h1 : q = s
    · subst h1; rw [get_s] at hg; cases hg; exact hds' hin
    · by_cases h2 : q = a
      · subst h2; rw [get_a] at hg; cases hg; exact hda' hin
      · rw [get_r q h2 h1] at hg; exact hdr q h2 h1 ⟨g, hg, hin⟩
  have hnc1 : ∃ y y' : Fin m → Bool, vl gs1 y o ≠ vl gs1 y' o := by
    obtain ⟨y, y', h⟩ := L.ncv hnc
    exact ⟨y, y', by rw [hag y o hoa, hag y' o hoa]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_dead m gs1 hcl1 o d (by omega) hdo hdead hnc1
  have := L.hmin gs'' o'' hc'' (fun x => by rw [he'' x, hag x o hoa]; exact L.hev x)
  omega

theorem poo_vl_or {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (x : Fin m → Bool) {p : ℕ}
    {g : Gate} (hg : gs[p]? = some g) (hop : g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    vl gs x (m + p) = (vl gs x a || vl gs x b) := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with h | h <;> rw [h]
  · simp [GateOp.eval]
  · simp [GateOp.eval, Bool.or_comm]

theorem poo_vl_and {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (x : Fin m → Bool) {p : ℕ}
    {g : Gate} (hg : gs[p]? = some g) (hop : g.op = GateOp.and) {a b : ℕ}
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    vl gs x (m + p) = (vl gs x a && vl gs x b) := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with h | h <;> rw [h]
  · simp [GateOp.eval]
  · simp [GateOp.eval, Bool.and_comm]

/-- A chain: `R` is the only reader of `G_p`, `q = OR(e, R)` is the only reader of `R`:
not least. -/
theorem poo_chain {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (e : Fin (n + 1)) (p q R : ℕ) (gp gq : Gate) (u : ℕ)
    (hgp : gs[p]? = some gp) (hop : gp.op = GateOp.or)
    (hinp : gp.inputs = [(e : ℕ), u] ∨ gp.inputs = [u, (e : ℕ)])
    (hgq : gs[q]? = some gq) (hoq : gq.op = GateOp.or)
    (hinq : gq.inputs = [(e : ℕ), n + 1 + R] ∨ gq.inputs = [n + 1 + R, (e : ℕ)])
    (hR : Reads gs R (n + 1 + p)) (honly : ∀ t, Reads gs t (n + 1 + p) → t = R)
    (hq : ∀ t, Reads gs t (n + 1 + R) → t = q) : False := by
  have hcl := L.hcl
  have hqR : Reads gs q (n + 1 + R) := by
    obtain ⟨g', hg', hi⟩ : ∃ g', gs[q]? = some g' ∧ (n + 1 + R) ∈ g'.inputs :=
      ⟨gq, hgq, by rcases hinq with h | h <;> rw [h] <;> simp⟩
    exact ⟨g', hg', hi⟩
  have hpR : p < R := by
    have := reads_lt hcl hR; omega
  have hRq : R < q := by
    have := reads_lt hcl hqR; omega
  have hup : u < n + 1 + p := by
    have := (hcl p gp hgp).lt u (by rcases hinp with h | h <;> rw [h] <;> simp); exact this
  have he : (e : ℕ) < n + 1 := e.isLt
  obtain ⟨gR, hgR, hinR⟩ := hR
  have hpo := poo_out_ne L hfnc (show Reads gs R (n + 1 + p) from ⟨gR, hgR, hinR⟩)
  have hVp : ∀ x : Fin (n + 1) → Bool,
      vl gs x (n + 1 + p) = (vl gs x e || vl gs x u) :=
    fun x => poo_vl_or hcl x hgp hop hinp
  have hVq : ∀ x : Fin (n + 1) → Bool,
      vl gs x (n + 1 + q) = (vl gs x e || vl gs x (n + 1 + R)) :=
    fun x => poo_vl_or hcl x hgq hoq hinq
  have hrd : ∀ r, r ≠ q → ¬ Reads gs r (n + 1 + R) := fun r hr h => hr (hq r h)
  have hdr : ∀ r, r ≠ R → r ≠ q → ¬ Reads gs r (n + 1 + p) := fun r hr _ h => hr (honly r h)
  have hpq : p ≠ q := by omega
  rcases gate_cases gs hcl R gR hgR (n + 1 + p) hinR with ⟨hnot, hin1, hval⟩ | ⟨w, hin1, hcase⟩
  · -- NOT
    refine poo_swap L hfnc R q p hRq ⟨GateOp.not, [u]⟩ gq ⟨gq, hgq, ?_⟩ hrd
      (Or.inl ⟨rfl, u, by omega, rfl⟩) (hcl q gq hgq) ?_ (reads_len ⟨gR, hgR, hinR⟩ |> fun h => by omega)
      hpo (by omega) hpq hdr ?_ ?_
    · rcases hinq with h | h <;> rw [h] <;> simp
    · intro x v hv hva
      have e1 : v e = vl gs x e := hv e (by omega) (by omega)
      have e2 : v u = vl gs x u := hv u (by omega) (by omega)
      have e3 : v (n + 1 + R) = !(v u) := by rw [hva]; simp [GateOp.eval]
      have e4 := hval x
      rw [hVp x] at e4
      rcases hinq with h | h <;> rw [h] <;> simp only [GateOp.eval] <;>
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil] <;>
        rw [hoq] <;> rw [hVq x, e4] <;> rw [e3, e2, e1] <;> cases vl gs x e <;> cases vl gs x u <;> rfl
    · simp; omega
    · rcases hinq with h | h <;> rw [h] <;> simp <;> omega
  · have hwlt : w < n + 1 + R := (hcl R gR hgR).lt w (by rcases hin1 with h | h <;> rw [h] <;> simp)
    rcases hcase with ⟨hand, hvR⟩ | ⟨hor, hvR⟩
    · by_cases hwp : w = n + 1 + p
      · exact Least.no_alias L hfnc R (reads_len ⟨gR, hgR, hinR⟩) (n + 1 + p) (by omega)
          (fun x => by rw [hvR x, hwp]; cases vl gs x (n + 1 + p) <;> rfl)
      refine poo_swap L hfnc R q p hRq ⟨GateOp.and, [u, w]⟩ gq ⟨gq, hgq, ?_⟩ hrd
        (Or.inr ⟨Or.inl rfl, u, w, by omega, hwlt, rfl⟩) (hcl q gq hgq) ?_
        (reads_len ⟨gR, hgR, hinR⟩ |> fun h => by omega)
        hpo (by omega) hpq hdr ?_ ?_
      · rcases hinq with h | h <;> rw [h] <;> simp
      · intro x v hv hva
        have e1 : v e = vl gs x e := hv e (by omega) (by omega)
        have e2 : v u = vl gs x u := hv u (by omega) (by omega)
        have e5 : v w = vl gs x w := hv w (by omega) (by omega)
        have e3 : v (n + 1 + R) = (v u && v w) := by rw [hva]; simp [GateOp.eval]
        have e4 := hvR x
        rw [hVp x] at e4
        rcases hinq with h | h <;> rw [h] <;> simp only [GateOp.eval] <;>
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil] <;>
          rw [hoq] <;> rw [hVq x, e4] <;> rw [e3, e2, e1, e5] <;> cases vl gs x e <;>
          cases vl gs x u <;> cases vl gs x w <;> rfl
      · simp; omega
      · rcases hinq with h | h <;> rw [h] <;> simp <;> omega
    · exact Least.no_alias L hfnc q (reads_len hqR |> fun _ => (reads_len (⟨gq, hgq, by
          rcases hinq with h | h <;> rw [h] <;> simp⟩ : Reads gs q (n + 1 + R)))) (n + 1 + R)
        (by omega) (fun x => by
          rw [hVq x, hvR x, hVp x]
          cases vl gs x e <;> cases vl gs x u <;> cases vl gs x w <;> rfl)

/-- Five positions of constant status or reading one: Drop 5. -/
theorem poo_save5 {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 p5 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h15 : p1 ≠ p5)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5) (h34 : p3 ≠ p4) (h35 : p3 ≠ p5)
    (h45 : p4 ≠ p5)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4)
    (h5 : RC n gs i b p5) : Drop f i b 5 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4, p5} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4, p5} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
      Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
      Finset.card_eq_three.2 ⟨p3, p4, p5, h34, h35, h45, rfl⟩] <;> rfl
  rwa [hcard] at this

theorem poo_in_form {gq : Gate} {e u' w : ℕ}
    (hinq : gq.inputs = [e, u'] ∨ gq.inputs = [u', e]) (hw : w ∈ gq.inputs) (hwe : w ≠ e) :
    u' = w := by
  rcases hinq with h | h <;> rw [h] at hw <;> simp at hw <;> omega

/-- `R` reads `G_p` and is of constant status; `R'` reads `G_q`; the rest of the table. -/
theorem poo_route {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
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
    (hR' : Reads gs R' (n + 1 + q)) (hRR' : R ≠ R')
    (hRC : IsC n gs e true (n + 1 + R)) : False := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hep : Reads gs p e := ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  have heq : Reads gs q e := ⟨gq, hgq, by rcases hinq with h | h <;> rw [h] <;> simp⟩
  have hrcp : RC n gs e true p := rc_input true hep
  have hrcq : RC n gs e true q := rc_input true heq
  have hcp : IsC n gs e true (n + 1 + p) := isC_reader hcl e p gp hgp
    (by rcases hinp with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hop]))
  have hcq : IsC n gs e true (n + 1 + q) := isC_reader hcl e q gq hgq
    (by rcases hinq with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hoq]))
  have hpR : p < R := by have := reads_lt hcl hR; omega
  have hqR' : q < R' := by have := reads_lt hcl hR'; omega
  have hRq : R ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p R e hep heq hR
  have hR'p : R' ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q R' e heq hep hR'
  have hrcR : RC n gs e true R := by
    obtain ⟨g, hg⟩ : ∃ g, gs[R]? = some g := by
      obtain ⟨g, hg, _⟩ := hR; exact ⟨g, hg⟩
    exact rc_of_const n gs hcl e true R g hg hRC
  have hrcR' : RC n gs e true R' := rc_of_reads hR' hcq
  by_cases h1 : ∃ T, Reads gs T (n + 1 + R) ∧ T ≠ q ∧ T ≠ R'
  · obtain ⟨T, hT, hTq, hTR'⟩ := h1
    have hRT : R < T := by have := reads_lt hcl hT; omega
    exact h5 (poo_save5 L e true hnc1 p q R R' T hpq (by omega) (by omega) (by omega)
      (Ne.symm hRq) (by omega) (by omega) (by omega) (by omega) (by omega)
      hrcp hrcq hrcR hrcR' (rc_of_reads hT hRC))
  push Not at h1
  by_cases h2 : Reads gs R' (n + 1 + R)
  · have hRR'lt : R < R' := by have := reads_lt hcl h2; omega
    obtain ⟨gR', hgR', hin1⟩ := hR'
    obtain ⟨gR'', hgR'', hin2⟩ := h2
    have ee : gR'' = gR' := gate_eq hgR'' hgR' rfl
    subst ee
    have hcR' : IsC n gs e true (n + 1 + R') := st_allconst n gs hcl e true R' gR'' hgR' (fun a ha => by
      rcases two_inputs (hcl R' gR'' hgR') (n + 1 + q) (n + 1 + R) a hin1 hin2 (by omega) ha
        with ee | ee
      · rw [ee]; exact hcq
      · rw [ee]; exact hRC)
    obtain ⟨T', hT'1, hT'r, hT'rc⟩ := L.next e true hnc1 R' (List.getElem?_eq_some_iff.1 hgR').1 hcR'
    exact h5 (poo_save5 L e true hnc1 p q R R' T' hpq (by omega) (by omega) (by omega)
      (Ne.symm hRq) (by omega) (by omega) (by omega) (by omega) (by omega)
      hrcp hrcq hrcR hrcR' hT'rc)
  · have hq0 : ∀ t, Reads gs t (n + 1 + R) → t = q := by
      intro t ht
      by_cases htq : t = q
      · exact htq
      · exact absurd (h1 t ht htq ▸ ht) h2
    obtain ⟨T0, hT0, hT0r, -⟩ := L.next e true hnc1 R (reads_len hR) hRC
    have hqeq := hq0 T0 hT0r
    subst hqeq
    have hu' : u' = n + 1 + R := poo_in_form hinq (by
      obtain ⟨g, hg, hi⟩ := hT0r
      rw [hgq] at hg; cases hg; exact hi) (by have := reads_lt hcl hR; omega)
    subst hu'
    exact poo_chain L hfnc e p T0 R gp gq u hgp hop hinp hgq hoq hinq hR honly hq0

/-- Surgery for a common reader `S = op(G_pe, G_pl)` of both OR gates, read by nobody else. -/
theorem poo_surg {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (e : Fin (n + 1)) (pe pl S : ℕ) (ge gl gS : Gate) (ue ul : ℕ)
    (hge : gs[pe]? = some ge) (hoe : ge.op = GateOp.or)
    (hine : ge.inputs = [(e : ℕ), ue] ∨ ge.inputs = [ue, (e : ℕ)])
    (hgl : gs[pl]? = some gl) (hol : gl.op = GateOp.or)
    (hinl : gl.inputs = [(e : ℕ), ul] ∨ gl.inputs = [ul, (e : ℕ)]) (hle : pe < pl)
    (hgS : gs[S]? = some gS) (hSop : gS.op = GateOp.and ∨ gS.op = GateOp.or)
    (hSin : gS.inputs = [n + 1 + pe, n + 1 + pl] ∨ gS.inputs = [n + 1 + pl, n + 1 + pe])
    (honlye : ∀ t, Reads gs t (n + 1 + pe) → t = S)
    (honlyl : ∀ t, Reads gs t (n + 1 + pl) → t = S) : False := by
  have hcl := L.hcl
  have hSe : Reads gs S (n + 1 + pe) :=
    ⟨gS, hgS, by rcases hSin with h | h <;> rw [h] <;> simp⟩
  have hSl : Reads gs S (n + 1 + pl) :=
    ⟨gS, hgS, by rcases hSin with h | h <;> rw [h] <;> simp⟩
  have hlS : pl < S := by have := reads_lt hcl hSl; omega
  have hue : ue < n + 1 + pe := (hcl pe ge hge).lt ue (by rcases hine with h | h <;> rw [h] <;> simp)
  have hul : ul < n + 1 + pl := (hcl pl gl hgl).lt ul (by rcases hinl with h | h <;> rw [h] <;> simp)
  have hulne : ul ≠ n + 1 + pe := by
    intro h
    have : Reads gs pl (n + 1 + pe) :=
      ⟨gl, hgl, by rcases hinl with h' | h' <;> rw [h'] <;> simp [h]⟩
    have := honlye pl this
    omega
  have he : (e : ℕ) < n + 1 := e.isLt
  have hVe : ∀ x : Fin (n + 1) → Bool,
      vl gs x (n + 1 + pe) = (vl gs x e || vl gs x ue) :=
    fun x => poo_vl_or hcl x hge hoe hine
  have hVl : ∀ x : Fin (n + 1) → Bool,
      vl gs x (n + 1 + pl) = (vl gs x e || vl gs x ul) :=
    fun x => poo_vl_or hcl x hgl hol hinl
  have hpo := poo_out_ne L hfnc hSe
  refine poo_swap L hfnc pl S pe hlS ⟨gS.op, [ue, ul]⟩ ⟨GateOp.or, [(e : ℕ), n + 1 + pl]⟩ hSl
    (fun r hr h => hr (honlyl r h)) ?hca ?hcs ?hval (by have := reads_len hSe; omega) hpo
    (by omega) (by omega) (fun r _ hr2 h => hr2 (honlye r h)) ?hda' ?hds'
  case hca =>
    rcases hSop with h | h
    · exact Or.inr ⟨Or.inl h, ue, ul, by omega, by omega, rfl⟩
    · exact Or.inr ⟨Or.inr h, ue, ul, by omega, by omega, rfl⟩
  case hcs => exact Or.inr ⟨Or.inr rfl, e, n + 1 + pl, by omega, by omega, rfl⟩
  case hval =>
    intro x v hv hva
    have e1 : v e = vl gs x e := hv e (by omega) (by omega)
    have e2 : v ue = vl gs x ue := hv ue (by omega) (by omega)
    have e3 : v ul = vl gs x ul := hv ul (by omega) (by omega)
    rcases hSop with hop | hop
    · have e4 : v (n + 1 + pl) = (v ue && v ul) := by rw [hva]; simp [GateOp.eval, hop]
      have e5 := poo_vl_and hcl x hgS hop hSin
      rw [hVe x, hVl x] at e5
      rw [e5]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [e4, e1, e2, e3]
      cases vl gs x e <;> cases vl gs x ue <;> cases vl gs x ul <;> rfl
    · have e4 : v (n + 1 + pl) = (v ue || v ul) := by rw [hva]; simp [GateOp.eval, hop]
      have e5 := poo_vl_or hcl x hgS hop hSin
      rw [hVe x, hVl x] at e5
      rw [e5]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [e4, e1, e2, e3]
      cases vl gs x e <;> cases vl gs x ue <;> cases vl gs x ul <;> rfl
  case hda' => simp; omega
  case hds' => simp; omega

/-- Case A: some gate reads both `G_p` and `G_q`. -/
theorem poo_caseA {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc1 : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e true) ≠ f (Function.update y e true))
    (h5 : ¬ Drop f e true 5 gs.length)
    (p q S : ℕ) (gp gq : Gate) (u u' : ℕ)
    (hgp : gs[p]? = some gp) (hop : gp.op = GateOp.or)
    (hinp : gp.inputs = [(e : ℕ), u] ∨ gp.inputs = [u, (e : ℕ)])
    (hgq : gs[q]? = some gq) (hoq : gq.op = GateOp.or)
    (hinq : gq.inputs = [(e : ℕ), u'] ∨ gq.inputs = [u', (e : ℕ)]) (hpq : p ≠ q)
    (hSp : Reads gs S (n + 1 + p)) (hSq : Reads gs S (n + 1 + q)) : False := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hep : Reads gs p e := ⟨gp, hgp, by rcases hinp with h | h <;> rw [h] <;> simp⟩
  have heq : Reads gs q e := ⟨gq, hgq, by rcases hinq with h | h <;> rw [h] <;> simp⟩
  have hrcp : RC n gs e true p := rc_input true hep
  have hrcq : RC n gs e true q := rc_input true heq
  have hcp : IsC n gs e true (n + 1 + p) := isC_reader hcl e p gp hgp
    (by rcases hinp with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hop]))
  have hcq : IsC n gs e true (n + 1 + q) := isC_reader hcl e q gq hgq
    (by rcases hinq with h | h <;> rw [h] <;> simp) true (Or.inr (by simp [fixBit, hoq]))
  have hpS : p < S := by have := reads_lt hcl hSp; omega
  have hqS : q < S := by have := reads_lt hcl hSq; omega
  obtain ⟨gS, hgS, hinS⟩ := hSp
  obtain ⟨gS', hgS', hinS'⟩ := hSq
  have ee : gS' = gS := gate_eq hgS' hgS rfl
  subst ee
  have hSp : Reads gs S (n + 1 + p) := ⟨gS', hgS, hinS⟩
  have hSq : Reads gs S (n + 1 + q) := ⟨gS', hgS, hinS'⟩
  have hcS : IsC n gs e true (n + 1 + S) := st_allconst n gs hcl e true S gS' hgS (fun a ha => by
    rcases two_inputs (hcl S gS' hgS) (n + 1 + p) (n + 1 + q) a hinS hinS' (by omega) ha
      with ee | ee
    · rw [ee]; exact hcp
    · rw [ee]; exact hcq)
  obtain ⟨t, hSt, htS, htrc⟩ := L.next e true hnc1 S (reads_len hSp) hcS
  by_cases hx : ∃ T, T ≠ S ∧ T ≠ t ∧ (Reads gs T (n + 1 + p) ∨ Reads gs T (n + 1 + q) ∨
      Reads gs T (n + 1 + S))
  · obtain ⟨T, hTS, hTt, hT⟩ := hx
    have key : T ≠ p ∧ T ≠ q ∧ RC n gs e true T := by
      rcases hT with hT | hT | hT
      · have hpT : p < T := by have := reads_lt hcl hT; omega
        refine ⟨by omega, ?_, rc_of_reads hT hcp⟩
        rintro rfl
        exact L.no_tri hfnc p T e hep heq hT
      · have hpT : q < T := by have := reads_lt hcl hT; omega
        refine ⟨?_, by omega, rc_of_reads hT hcq⟩
        rintro rfl
        exact L.no_tri hfnc q T e heq hep hT
      · have hpT : S < T := by have := reads_lt hcl hT; omega
        exact ⟨by omega, by omega, rc_of_reads hT hcS⟩
    obtain ⟨hTp, hTq, hTrc⟩ := key
    exact h5 (poo_save5 L e true hnc1 p q S t T hpq (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (Ne.symm hTS) (Ne.symm hTt)
      hrcp hrcq (rc_of_const n gs hcl e true S gS' hgS hcS) htrc hTrc)
  · push Not at hx
    have hall : ∀ w, (w = p ∨ w = q) → ∀ T, Reads gs T (n + 1 + w) → T = S := by
      intro w hw T hT
      by_cases hTS : T = S
      · exact hTS
      have hTt : T = t := by
        by_contra hTt
        rcases hw with rfl | rfl
        · exact absurd hT (hx T hTS hTt).1
        · exact absurd hT (hx T hTS hTt).2.1
      subst hTt
      rcases hw with hw | hw
      · rw [hw] at hT; exact (L.no_tri hfnc S T (n + 1 + p) hSp hT htS).elim
      · rw [hw] at hT; exact (L.no_tri hfnc S T (n + 1 + q) hSq hT htS).elim
    have hSin : gS'.inputs = [n + 1 + p, n + 1 + q] ∨ gS'.inputs = [n + 1 + q, n + 1 + p] := by
      rcases hcl S gS' hgS with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩
      · rw [hin] at hinS hinS'; simp at hinS hinS'; omega
      · rw [hin] at hinS hinS' ⊢
        simp at hinS hinS' ⊢
        omega
    have hSop : gS'.op = GateOp.and ∨ gS'.op = GateOp.or := by
      rcases hcl S gS' hgS with ⟨_, j, _, hin⟩ | ⟨h, _⟩
      · rw [hin] at hinS hinS'; simp at hinS hinS'; omega
      · exact h
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact poo_surg L hfnc e p q S gp gq gS' u u' hgp hop hinp hgq hoq hinq hlt hgS hSop hSin
        (hall p (Or.inl rfl)) (hall q (Or.inr rfl))
    · exact poo_surg L hfnc e q p S gq gp gS' u' u hgq hoq hinq hgp hop hinp hgt hgS hSop
        hSin.symm (hall q (Or.inr rfl)) (hall p (Or.inl rfl))

end PEqualNP.MetaComplexity.Helpers.RunAsm
