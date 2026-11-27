import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Cell A of the case table (`L-meta-115`): the reader of `x_s` is an OR gate

`PCellA_proof`: in a counterexample at a run, the single reader `qs` of the input `s` is an OR
gate. If it were `AND(s, w)`: `w` is true at `e_a` and `e_t` (A0), so `w` is a gate; if `qs` is
its only reader, three gates go at `x_s := 0` (A1); else a second reader `R'` of `w` and the reader
`qt` of `t` give four aliases at `x_t := 1` (A2), unless `qt` is `w`; then `w = OR(t, w')` and either
four aliases at `x_a := 1` or `w' = a` and the circuit ignores `x_a` on `{x_t = 1}` (A3).
Paper: `routes/lifting/lgp/FO1-monotone-direct.md` section 5, cell A.
-/

namespace PEqualNP.MetaComplexity.Loc.CellA

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

theorem vin {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (i : Fin m) :
    vl gs x (i : ℕ) = x i := by
  rw [vl_input gs x i i.isLt]

theorem pt_true {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : pt S i = true ↔ i ∈ S := by
  simp [pt]

/-- The shape of a gate of a clean NOT-free list that reads `v`. -/
theorem shape {m : ℕ} {gs : List Gate} (hc : MClean m gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) {v : ℕ} (hv : v ∈ g.inputs) :
    ∃ y, y < m + p ∧ v < m + p ∧ (g.inputs = [v, y] ∨ g.inputs = [y, v]) ∧
      ((g.op = GateOp.and ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x v && vl gs x y)) ∨
       (g.op = GateOp.or ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x v || vl gs x y))) := by
  rcases hc.1 p g hp with ⟨hnot, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hnot (hc.2 g (List.mem_of_getElem? hp))
  · have hval : ∀ x : Fin m → Bool, vl gs x (m + p) =
        g.op.eval [vl gs x j, vl gs x k] := by
      intro x
      rw [vl_gate gs hc.1 x p g hp, hin]
      rfl
    rw [hin] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · refine ⟨k, hk, hj, Or.inl hin, ?_⟩
      rcases hop with h | h
      · exact Or.inl ⟨h, fun x => by rw [hval x, h]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨h, fun x => by rw [hval x, h]; simp [GateOp.eval]⟩
    · refine ⟨j, hj, hk, Or.inr hin, ?_⟩
      rcases hop with h | h
      · exact Or.inl ⟨h, fun x => by rw [hval x, h]; simp [GateOp.eval, Bool.and_comm]⟩
      · exact Or.inr ⟨h, fun x => by rw [hval x, h]; simp [GateOp.eval, Bool.or_comm]⟩

/-- Gate `p` is an alias of the earlier wire `j` on `P`. -/
def Al (m : ℕ) (gs : List Gate) (P : Set (Fin m → Bool)) (p j : ℕ) : Prop :=
  p < gs.length ∧ j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j

/-- Four distinct aliases go. -/
theorem rem4 (hRem : ToolRemoval) {m : ℕ} {gs : List Gate} {o : ℕ} (hc : MClean m gs)
    (ho : o < m + gs.length) (P : Set (Fin m → Bool)) (p1 p2 p3 p4 j1 j2 j3 j4 : ℕ)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4)
    (h34 : p3 ≠ p4) (a1 : Al m gs P p1 j1) (a2 : Al m gs P p2 j2) (a3 : Al m gs P p3 j3)
    (a4 : Al m gs P p4 j4) :
    ∃ (gs' : List Gate) (o' : ℕ), MClean m gs' ∧ gs'.length + 4 ≤ gs.length ∧
      ∀ x ∈ P, vl gs' x o' = vl gs x o := by
  classical
  let tgt : ℕ → Option ℕ := fun p =>
    if p = p1 then some j1 else if p = p2 then some j2 else if p = p3 then some j3 else some j4
  have hS : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  have hR : Removable m gs o P {p1, p2, p3, p4} tgt := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨a1.1, Or.inl ⟨j1, by simp [tgt], a1.2.1, a1.2.2⟩⟩
    · exact ⟨a2.1, Or.inl ⟨j2, by simp [tgt, Ne.symm h12], a2.2.1, a2.2.2⟩⟩
    · exact ⟨a3.1, Or.inl ⟨j3, by simp [tgt, Ne.symm h13, Ne.symm h23], a3.2.1, a3.2.2⟩⟩
    · exact ⟨a4.1, Or.inl ⟨j4, by simp [tgt, Ne.symm h14, Ne.symm h24, Ne.symm h34],
        a4.2.1, a4.2.2⟩⟩
  obtain ⟨gs', r, hcl', hnf, hlen, _, hval⟩ := hRem m gs o P _ tgt hc.1 hR
  refine ⟨gs', r o, ⟨hcl', hnf hc.2⟩, by rw [hS] at hlen; exact hlen, ?_⟩
  have := hval o ho (fun p _ hp => by
    simp only [tgt] at hp
    split_ifs at hp)
  exact this.2

/-- Two aliases and an orphan go. -/
theorem rem3 (hRem : ToolRemoval) {m : ℕ} {gs : List Gate} {o : ℕ} (hc : MClean m gs)
    (ho : o < m + gs.length) (P : Set (Fin m → Bool)) (p1 p2 p3 j1 j2 : ℕ)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (a1 : Al m gs P p1 j1)
    (a2 : Al m gs P p2 j2) (hl3 : p3 < gs.length) (ho3 : o ≠ m + p3)
    (hrd : ∀ q, Reads gs q (m + p3) → q = p1 ∨ q = p2) (hj1 : j1 ≠ m + p3)
    (hj2 : j2 ≠ m + p3) :
    ∃ (gs' : List Gate) (o' : ℕ), MClean m gs' ∧ gs'.length + 3 ≤ gs.length ∧
      ∀ x ∈ P, vl gs' x o' = vl gs x o := by
  classical
  let tgt : ℕ → Option ℕ := fun p =>
    if p = p1 then some j1 else if p = p2 then some j2 else none
  have hS : ({p1, p2, p3} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hR : Removable m gs o P {p1, p2, p3} tgt := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨a1.1, Or.inl ⟨j1, by simp [tgt], a1.2.1, a1.2.2⟩⟩
    · exact ⟨a2.1, Or.inl ⟨j2, by simp [tgt, Ne.symm h12], a2.2.1, a2.2.2⟩⟩
    · refine ⟨hl3, Or.inr ⟨by simp [tgt, Ne.symm h13, Ne.symm h23], ho3, ?_, ?_⟩⟩
      · intro q hq
        rcases hrd q hq with rfl | rfl <;> simp
      · intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · simp [tgt, hj1]
        · simp [tgt, Ne.symm h12, hj2]
        · simp [tgt, Ne.symm h13, Ne.symm h23]
  obtain ⟨gs', r, hcl', hnf, hlen, _, hval⟩ := hRem m gs o P _ tgt hc.1 hR
  refine ⟨gs', r o, ⟨hcl', hnf hc.2⟩, by rw [hS] at hlen; exact hlen, ?_⟩
  have := hval o ho (fun p hp hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · simp [tgt] at hn
    · simp [tgt, Ne.symm h12] at hn
    · exact ho3)
  exact this.2

theorem Fpt {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    F G ∅ (pt S) = true ↔ ∃ i j, G.Adj i j ∧ i ∈ S ∧ j ∈ S := by
  rw [F_true]
  simp [pt]

/-- PIECE (cell A). The reader of `x_s` is an OR gate. -/
theorem PCellA_proof (hRem : ToolRemoval) (hNA : ToolNoAlias) (hLive : ToolLive)
    (hPay0 : ToolPay0) (hPay1 : ToolPay1) (hProp : ToolProp) (hMono : ToolMono) : PCellA := by
  intro n G A gs o a' a s t b b' qa qs qt qb hctx hfan
  have hc := hctx.cex
  have hrun := hctx.run
  have hA0 := hctx.hA
  subst hA0
  have hL := hc.least
  have hmc : MClean n gs := hL.clean
  have hcomp : Computes n gs o (F G ∅) := hL.2.2.1
  have nd := hrun.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := nd
  have adj_sa : G.Adj s a := (hrun.hs a).2 (Or.inl rfl)
  have adj_st : G.Adj s t := (hrun.hs t).2 (Or.inr rfl)
  have adj_tb : G.Adj t b := (hrun.ht b).2 (Or.inr rfl)
  have adj_aa' : G.Adj a a' := (hrun.ha a').2 (Or.inl rfl)
  have hnc : ∃ x y : Fin n → Bool, F G ∅ x ≠ F G ∅ y := F_nc G ∅ (Or.inr ⟨s, t, adj_st⟩)
  have hlive := hLive n (F G ∅) gs o hL hnc
  -- the reader of `s`
  have hqsm : qs ∈ RdSet gs s := by rw [hfan.fs]; exact Finset.mem_singleton_self _
  have hqsr : Reads gs qs s := mem_rdSet.1 hqsm
  have hrs : ∀ q, Reads gs q s → q = qs := by
    intro q hq
    have := mem_rdSet.2 hq
    rw [hfan.fs] at this
    exact Finset.mem_singleton.1 this
  have hqsL : qs < gs.length := reads_len hqsr
  obtain ⟨g, hg, hsin⟩ := hqsr
  obtain ⟨w, hw, _, hin, hop⟩ := shape hmc hg hsin
  rcases hop with ⟨hand, hval⟩ | ⟨hor, _⟩
  swap
  · exact ⟨w, g, hg, hor, hin⟩
  exfalso
  -- the output is the last gate and is unread
  have hout : o = n + (gs.length - 1) := by
    by_contra hne
    obtain ⟨q, hq⟩ := hlive.2 (gs.length - 1) (by omega) hne
    have hq' := mem_rdSet.1 hq
    have := reads_lt hmc.1 hq'
    have := reads_len hq'
    omega
  have hunread : ∀ q, ¬ Reads gs q o := by
    intro q hq
    have := reads_lt hmc.1 hq
    have := reads_len hq
    omega
  have hoL : o < n + gs.length := hlive.1
  -- A0
  have hws : w ≠ (s : ℕ) := by
    intro hws
    refine hNA n (F G ∅) gs o hL hnc qs hqsL s (by omega) (fun x => ?_)
    rw [hval x, hws, Bool.and_self]
  have hD : ∀ (D : Fin n), ∀ i : Fin n, (i : ℕ) ∉ ({(D : ℕ)} : Set ℕ) → i ≠ D := by
    intro D i hi he
    exact hi (by rw [he]; rfl)
  have flip : ∀ z z' : Fin n → Bool, z s = false → z' s = true → (∀ i, i ≠ s → z i = z' i) →
      F G ∅ z = false → F G ∅ z' = true → vl gs z w = true := by
    intro z z' hz hz' hag hF hF'
    have hx : ∀ i : Fin n, (i : ℕ) ∉ ({(s : ℕ)} : Set ℕ) → z i = z' i :=
      fun i hi => hag i (hD s i hi)
    have hbelow : vl gs z w = vl gs z' w := by
      refine hProp n gs z z' {(s : ℕ)} (n + qs) hmc.1 hx ?_ w hw hws
      intro p g' hp hpK _
      left
      intro v hv hvD
      have hvs : v = (s : ℕ) := hvD
      have := hrs p ⟨g', hp, hvs ▸ hv⟩
      omega
    by_contra hwf
    have hwf' : vl gs z w = false := by simpa using hwf
    have hall := hProp n gs z z' {(s : ℕ)} (n + gs.length) hmc.1 hx (by
      intro p g' hp _ _
      by_cases hpq : p = qs
      · right
        subst hpq
        rw [hval z, hval z', ← hbelow, hwf']
        simp
      · left
        intro v hv hvD
        have hvs : v = (s : ℕ) := hvD
        exact hpq (hrs p ⟨g', hp, hvs ▸ hv⟩)) o hoL (by
          intro h
          have : o = (s : ℕ) := h
          omega)
    have e1 := hcomp z
    have e2 := hcomp z'
    rw [hall, e2, hF'] at e1
    rw [hF] at e1
    exact Bool.false_ne_true e1.symm
  have hwa : vl gs (pt {a}) w = true := by
    refine flip (pt {a}) (pt {a, s}) (by simp [pt, Ne.symm h6]) (by simp [pt])
      (fun i hi => by simp [pt, hi]) ?_ ?_
    · rw [Bool.eq_false_iff, ne_eq, Fpt]
      rintro ⟨i, j, h, hi, hj⟩
      simp at hi hj
      subst hi hj
      exact h.ne rfl
    · rw [Fpt]
      exact ⟨a, s, adj_sa.symm, by simp, by simp⟩
  have hwt : vl gs (pt {t}) w = true := by
    refine flip (pt {t}) (pt {t, s}) (by simp [pt, h10]) (by simp [pt])
      (fun i hi => by simp [pt, hi]) ?_ ?_
    · rw [Bool.eq_false_iff, ne_eq, Fpt]
      rintro ⟨i, j, h, hi, hj⟩
      simp at hi hj
      subst hi hj
      exact h.ne rfl
    · rw [Fpt]
      exact ⟨t, s, adj_st.symm, by simp, by simp⟩
  have hmonoAt : ∀ (v : Fin n) (j : ℕ), vl gs (pt {v}) j = true →
      ∀ x : Fin n → Bool, x v = true → vl gs x j = true := by
    intro v j hj x hx
    refine hMono n gs hmc (pt {v}) x (fun i hi => ?_) j hj
    have : i = v := by simpa [pt] using hi
    rw [this]; exact hx
  -- w is a gate
  have hwn : n ≤ w := by
    by_contra hlt
    rw [not_le] at hlt
    have e1 := hwa
    have e2 := hwt
    rw [vl_input gs _ w hlt] at e1 e2
    have ea : (⟨w, hlt⟩ : Fin n) = a := by simpa [pt] using e1
    have et : (⟨w, hlt⟩ : Fin n) = t := by simpa [pt] using e2
    exact h7 (ea.symm.trans et)
  obtain ⟨pw, rfl⟩ : ∃ pw, w = n + pw := ⟨w - n, by omega⟩
  have hpwq : pw < qs := by omega
  have hpwL : pw < gs.length := by omega
  have hsn : (s : ℕ) < n := s.isLt
  have htn : (t : ℕ) < n := t.isLt
  have han : (a : ℕ) < n := a.isLt
  by_cases hR' : ∃ R', Reads gs R' (n + pw) ∧ R' ≠ qs
  swap
  · -- A1: `qs` is the only reader of `w`; three gates go at `x_s := 0`
    have hrw : ∀ q, Reads gs q (n + pw) → q = qs := by
      intro q hq
      by_contra hne
      exact hR' ⟨q, hq, hne⟩
    have hoqs : o ≠ n + qs := by
      intro h
      have e := hcomp (pt {t, b})
      rw [h, hval, vin] at e
      have hF : F G ∅ (pt {t, b}) = true := by
        rw [Fpt]; exact ⟨t, b, adj_tb, by simp, by simp⟩
      have hs0 : pt {t, b} s = false := by simp [pt, h10, h11]
      rw [hs0, hF] at e
      simp at e
    obtain ⟨R, hRm⟩ := hlive.2 qs hqsL hoqs
    have hRr := mem_rdSet.1 hRm
    have hRlt := reads_lt hmc.1 hRr
    have hRL := reads_len hRr
    obtain ⟨gR, hgR, hqin⟩ := hRr
    obtain ⟨y, hy, _, hinR, hopR⟩ := shape hmc hgR hqin
    let P : Set (Fin n → Bool) := {x | x s = false}
    have hqsP : ∀ x ∈ P, vl gs x (n + qs) = false := by
      intro x hx
      have hx' : x s = false := hx
      rw [hval, vin, hx']
      simp
    have a1 : Al n gs P qs s := ⟨hqsL, by omega, fun x hx => by
      rw [hqsP x hx, vin]; exact hx.symm⟩
    obtain ⟨j2, a2, hj2⟩ : ∃ j2, Al n gs P R j2 ∧ j2 ≠ n + pw := by
      rcases hopR with ⟨_, hv⟩ | ⟨_, hv⟩
      · refine ⟨s, ⟨hRL, by omega, fun x hx => ?_⟩, by omega⟩
        rw [hv, hqsP x hx, vin]
        exact hx.symm
      · refine ⟨y, ⟨hRL, hy, fun x hx => ?_⟩, ?_⟩
        · rw [hv, hqsP x hx]
          simp
        · intro hyw
          have hyin : y ∈ gR.inputs := by
            rcases hinR with h | h <;> rw [h] <;> simp
          have := hrw R ⟨gR, hgR, hyw ▸ hyin⟩
          omega
    obtain ⟨gs', o', hmc', hlen', heq⟩ := rem3 hRem hmc hoL P qs R pw s j2
      (by omega) (by omega) (by omega) a1 a2 hpwL
      (fun h => hunread qs (h ▸ ⟨g, hg, by rcases hin with h' | h' <;> rw [h'] <;> simp⟩))
      (fun q hq => Or.inl (hrw q hq)) (by omega) hj2
    exact hPay0 n G ∅ gs o s a t gs' o' hc adj_sa (fun v h => (hrun.hs v).1 h)
      (Or.inr ⟨t, b, adj_tb, Ne.symm h10, fun e => h11 e.symm⟩) hmc' (by omega)
      (fun x hx => by rw [heq x hx]; exact hcomp x)
  obtain ⟨R', hR'r, hR'ne⟩ := hR'
  have hR'lt := reads_lt hmc.1 hR'r
  have hR'L := reads_len hR'r
  obtain ⟨gR', hgR', hwin⟩ := hR'r
  obtain ⟨y', hy', _, hinR', hopR'⟩ := shape hmc hgR' hwin
  have hqtm : qt ∈ RdSet gs t := by rw [hfan.ft]; exact Finset.mem_singleton_self _
  have hqtr : Reads gs qt t := mem_rdSet.1 hqtm
  have hqtL := reads_len hqtr
  obtain ⟨gt, hgt, htin⟩ := hqtr
  by_cases hqtw : qt = pw
  swap
  · -- A2: four aliases at `x_t := 1`
    let P : Set (Fin n → Bool) := {x | x t = true}
    have hwP : ∀ x ∈ P, vl gs x (n + pw) = true := fun x hx => hmonoAt t _ hwt x hx
    have a1 : Al n gs P pw t := ⟨hpwL, by omega, fun x hx => by
      rw [hwP x hx, vin]; exact hx.symm⟩
    have a2 : Al n gs P qs s := ⟨hqsL, by omega, fun x hx => by
      rw [hval, hwP x hx]; simp⟩
    obtain ⟨j3, a3⟩ : ∃ j3, Al n gs P R' j3 := by
      rcases hopR' with ⟨_, hv⟩ | ⟨_, hv⟩
      · exact ⟨y', hR'L, hy', fun x hx => by rw [hv, hwP x hx]; simp⟩
      · exact ⟨t, hR'L, by omega, fun x hx => by
          rw [hv, hwP x hx, vin]; exact hx.symm⟩
    obtain ⟨yt, hyt, _, _, hopt⟩ := shape hmc hgt htin
    obtain ⟨j4, a4⟩ : ∃ j4, Al n gs P qt j4 := by
      rcases hopt with ⟨_, hv⟩ | ⟨_, hv⟩
      · exact ⟨yt, hqtL, hyt, fun x hx => by
          have hx' : x t = true := hx
          rw [hv, vin, hx']; simp⟩
      · exact ⟨t, hqtL, by omega, fun x hx => by
          have hx' : x t = true := hx
          rw [hv, vin, hx']; simp⟩
    have hqsqt : qs ≠ qt := by
      intro h
      subst h
      have := gate_eq hg hgt rfl
      subst this
      rcases hin with h' | h' <;> rw [h'] at htin <;> simp at htin <;> omega
    have hR'qt : R' ≠ qt := by
      intro h
      subst h
      have := gate_eq hgR' hgt rfl
      subst this
      have hyt' : y' = (t : ℕ) := by
        rcases hinR' with h' | h' <;> rw [h'] at htin <;> simp at htin <;> omega
      subst hyt'
      rcases hopR' with ⟨_, hv⟩ | ⟨_, hv⟩
      · refine hNA n (F G ∅) gs o hL hnc R' hR'L t (by omega) (fun x => ?_)
        rw [hv, vin]
        cases hx : x t
        · simp
        · rw [hmonoAt t _ hwt x hx]; rfl
      · refine hNA n (F G ∅) gs o hL hnc R' hR'L (n + pw) (by omega) (fun x => ?_)
        rw [hv, vin]
        cases hx : x t
        · simp
        · rw [hmonoAt t _ hwt x hx]; rfl
    obtain ⟨gs', o', hmc', hlen', heq⟩ := rem4 hRem hmc hoL P pw qs R' qt t s j3 j4
      (by omega) (by omega) (Ne.symm hqtw) hR'ne.symm hqsqt hR'qt a1 a2 a3 a4
    exact hPay1 n G ∅ gs o t gs' o' hc hrun.deep_t hmc' (by omega)
      (fun x hx => by rw [heq x hx]; exact hcomp x)
  -- A3: `qt = pw`, so `w = OR(t, w')`
  rw [hqtw] at hgt
  obtain ⟨w', hw', _, hinw, hopw⟩ := shape hmc hgt htin
  have hta : pt {a} t = false := by simp [pt, Ne.symm h7]
  rcases hopw with ⟨_, hv⟩ | ⟨_, hvalw⟩
  · rw [hv, vin, hta] at hwa
    simp at hwa
  have hw'a : vl gs (pt {a}) w' = true := by
    rw [hvalw, vin, hta] at hwa
    simpa using hwa
  have hw'in : w' ∈ gt.inputs := by rcases hinw with h | h <;> rw [h] <;> simp
  by_cases hw'n : w' < n
  · -- `w' = a`: on `{x_t = 1}` the circuit ignores `x_a`
    have ha' : (⟨w', hw'n⟩ : Fin n) = a := by
      rw [vl_input gs _ w' hw'n] at hw'a
      simpa [pt] using hw'a
    have hw'eq : w' = (a : ℕ) := by rw [← ha']
    have hra : ∀ q, Reads gs q a → q = pw := by
      have hmem : ∀ q, Reads gs q a → q = qa := by
        intro q hq
        have := mem_rdSet.2 hq
        rw [hfan.fa] at this
        exact Finset.mem_singleton.1 this
      intro q hq
      rw [hmem q hq, hmem pw ⟨gt, hgt, hw'eq ▸ hw'in⟩]
    have hall := hProp n gs (pt {t, a, a'}) (pt {t, a'}) {(a : ℕ)} (n + gs.length) hmc.1
      (fun i hi => by have := hD a i hi; simp [pt, this]) (by
        intro p g' hp _ _
        by_cases hpq : p = pw
        · right
          subst hpq
          rw [hvalw, hvalw, vin, vin]
          simp [pt]
        · left
          intro v hv hvD
          have hva : v = (a : ℕ) := hvD
          exact hpq (hra p ⟨g', hp, hva ▸ hv⟩)) o hoL (by
          intro h
          have : o = (a : ℕ) := h
          omega)
    have hF1 : F G ∅ (pt {t, a, a'}) = true := by
      rw [Fpt]; exact ⟨a, a', adj_aa', by simp, by simp⟩
    have hF2 : F G ∅ (pt {t, a'}) = false := by
      rw [Bool.eq_false_iff, ne_eq, Fpt]
      rintro ⟨i, j, h, hi, hj⟩
      simp at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact h.ne rfl
      · rcases (hrun.ht _).1 h with e | e
        · exact h2 e
        · exact h4 e
      · rcases (hrun.ht _).1 h.symm with e | e
        · exact h2 e
        · exact h4 e
      · exact h.ne rfl
    have e1 := hcomp (pt {t, a, a'})
    have e2 := hcomp (pt {t, a'})
    rw [hall, e2, hF1, hF2] at e1
    exact Bool.false_ne_true e1
  · -- `w'` a gate: four aliases at `x_a := 1`
    obtain ⟨pw', rfl⟩ : ∃ pw', w' = n + pw' := ⟨w' - n, by omega⟩
    let P : Set (Fin n → Bool) := {x | x a = true}
    have hw'P : ∀ x ∈ P, vl gs x (n + pw') = true := fun x hx => hmonoAt a _ hw'a x hx
    have hwP : ∀ x ∈ P, vl gs x (n + pw) = true := fun x hx => by
      rw [hvalw, hw'P x hx]; simp
    have a1 : Al n gs P pw' a := ⟨by omega, by omega, fun x hx => by
      rw [hw'P x hx, vin]; exact hx.symm⟩
    have a2 : Al n gs P pw a := ⟨hpwL, by omega, fun x hx => by
      rw [hwP x hx, vin]; exact hx.symm⟩
    have a3 : Al n gs P qs s := ⟨hqsL, by omega, fun x hx => by
      rw [hval, hwP x hx]; simp⟩
    obtain ⟨j4, a4⟩ : ∃ j4, Al n gs P R' j4 := by
      rcases hopR' with ⟨_, hv⟩ | ⟨_, hv⟩
      · exact ⟨y', hR'L, hy', fun x hx => by rw [hv, hwP x hx]; simp⟩
      · exact ⟨a, hR'L, by omega, fun x hx => by
          rw [hv, hwP x hx, vin]; exact hx.symm⟩
    obtain ⟨gs', o', hmc', hlen', heq⟩ := rem4 hRem hmc hoL P pw' pw qs R' a a s j4
      (by omega) (by omega) (by omega) (by omega) (by omega) hR'ne.symm a1 a2 a3 a4
    exact hPay1 n G ∅ gs o a gs' o' hc hrun.deep_a hmc' (by omega)
      (fun x hx => by rw [heq x hx]; exact hcomp x)

end PEqualNP.MetaComplexity.Loc.CellA
