import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class, fan-out cells (`L-meta-115`): PFanLow, PFanTwo, ToolCons, PReadFew, PReadTwo

Builder b7 of the plan `LocPlan.lean`. Each piece is proved from the tools it needs, taken as
explicit hypotheses (their statements are fixed in `LocPlan.lean`).

Every death counted here is an ALIAS on the subcube: a gate reading a wire that is constant `c` on
the subcube is equal there to that wire or to its other operand. No orphan is used. The removal
is `ToolRemoval`; the count is refuted by `ToolPay0` or `ToolPay1`.

Paper: `routes/lifting/lgp/FO1-monotone-direct.md` sections 3 and 5; planner's note section H.
-/

namespace PEqualNP.MetaComplexity.Loc.Fan

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-! ## Aliases and constant wires on a set of points -/

/-- Gate `p` is equal on `P` to an earlier wire. -/
def IsAl (m : ℕ) (gs : List Gate) (P : Set (Fin m → Bool)) (p : ℕ) : Prop :=
  p < gs.length ∧ ∃ j, j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j

/-- Wire `w` is constant `c` on `P`. -/
def Cst (m : ℕ) (gs : List Gate) (P : Set (Fin m → Bool)) (w : ℕ) (c : Bool) : Prop :=
  ∀ x ∈ P, vl gs x w = c

theorem removable_of_alias {m : ℕ} {gs : List Gate} {o : ℕ} {P : Set (Fin m → Bool)}
    {S : Finset ℕ} (h : ∀ p ∈ S, IsAl m gs P p) : ∃ tgt, Removable m gs o P S tgt := by
  classical
  refine ⟨fun p => if hp : ∃ j, j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j
    then some hp.choose else none, ?_⟩
  intro p hpS
  obtain ⟨hlen, hex⟩ := h p hpS
  refine ⟨hlen, Or.inl ⟨hex.choose, ?_, hex.choose_spec.1, hex.choose_spec.2⟩⟩
  simp only [dif_pos hex]

theorem gate_shape {m : ℕ} {gs : List Gate} (h : MClean m gs) {q : ℕ} {g : Gate}
    (hg : gs[q]? = some g) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ j k, j < m + q ∧ k < m + q ∧ g.inputs = [j, k] := by
  rcases h.1 q g hg with ⟨hn, _⟩ | h2
  · exact absurd hn (h.2 g (List.mem_of_getElem? hg))
  · exact h2

/-- The binary operation of an AND or OR gate (OR for every other op). -/
def bop : GateOp → Bool → Bool → Bool
  | GateOp.and, a, b => a && b
  | _, a, b => a || b

@[simp] theorem bop_and (a b : Bool) : bop GateOp.and a b = (a && b) := rfl
@[simp] theorem bop_or (a b : Bool) : bop GateOp.or a b = (a || b) := rfl

theorem vl_bin {m : ℕ} {gs : List Gate} (h : MClean m gs) {q : ℕ} {g : Gate}
    (hg : gs[q]? = some g) {j k : ℕ} (hin : g.inputs = [j, k]) (x : Fin m → Bool) :
    vl gs x (m + q) = bop g.op (vl gs x j) (vl gs x k) := by
  rw [vl_gate gs h.1 x q g hg, hin]
  rcases (gate_shape h hg).1 with hop | hop
  · rw [hop]; simp [GateOp.eval]
  · rw [hop]; simp [GateOp.eval]

theorem vl_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    vl gs x (v : ℕ) = x v :=
  vl_input gs x v v.isLt

theorem cst_in {n : ℕ} (gs : List Gate) (v : Fin n) (c : Bool) :
    Cst n gs {x | x v = c} v c := fun x hx => by rw [vl_in]; exact hx

/-- A gate reading a wire constant on `P` is an alias on `P`. -/
theorem al_read {m : ℕ} {gs : List Gate} (h : MClean m gs) {P : Set (Fin m → Bool)} {q w : ℕ}
    {c : Bool} (hr : Reads gs q w) (hw : Cst m gs P w c) : IsAl m gs P q := by
  obtain ⟨g, hg, hwin⟩ := hr
  refine ⟨(List.getElem?_eq_some_iff.1 hg).1, ?_⟩
  obtain ⟨hop, j, k, hj, hk, hin⟩ := gate_shape h hg
  have e := vl_bin h hg hin
  rw [hin] at hwin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
  rcases hop with hop | hop <;> rcases hwin with rfl | rfl <;> cases c
  · exact ⟨w, hj, fun x hx => by rw [e x, hop, hw x hx]; rfl⟩
  · exact ⟨k, hk, fun x hx => by rw [e x, hop, hw x hx]; rfl⟩
  · exact ⟨w, hk, fun x hx => by rw [e x, hop, hw x hx]; cases vl gs x j <;> rfl⟩
  · exact ⟨j, hj, fun x hx => by rw [e x, hop, hw x hx]; cases vl gs x j <;> rfl⟩
  · exact ⟨k, hk, fun x hx => by rw [e x, hop, hw x hx]; rfl⟩
  · exact ⟨w, hj, fun x hx => by rw [e x, hop, hw x hx]; rfl⟩
  · exact ⟨j, hj, fun x hx => by rw [e x, hop, hw x hx]; cases vl gs x j <;> rfl⟩
  · exact ⟨w, hk, fun x hx => by rw [e x, hop, hw x hx]; cases vl gs x j <;> rfl⟩

/-- An AND reading a wire false on `P`, or an OR reading a wire true on `P`, is constant. -/
theorem cst_abs {m : ℕ} {gs : List Gate} (h : MClean m gs) {P : Set (Fin m → Bool)} {q w : ℕ}
    {g : Gate} {c : Bool} (hg : gs[q]? = some g) (hwin : w ∈ g.inputs)
    (hop : (g.op = GateOp.and ∧ c = false) ∨ (g.op = GateOp.or ∧ c = true))
    (hw : Cst m gs P w c) : Cst m gs P (m + q) c := by
  obtain ⟨_, j, k, _, _, hin⟩ := gate_shape h hg
  have e := vl_bin h hg hin
  rw [hin] at hwin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
  intro x hx
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ <;> rcases hwin with rfl | rfl <;>
    simp [e x, hop, hw x hx]

/-- A gate reading two distinct wires constant `c` on `P` is constant `c` on `P`. -/
theorem cst_two {m : ℕ} {gs : List Gate} (h : MClean m gs) {P : Set (Fin m → Bool)}
    {q w1 w2 : ℕ} {g : Gate} {c : Bool} (hg : gs[q]? = some g) (h1 : w1 ∈ g.inputs)
    (h2 : w2 ∈ g.inputs) (hne : w1 ≠ w2) (hw1 : Cst m gs P w1 c) (hw2 : Cst m gs P w2 c) :
    Cst m gs P (m + q) c := by
  obtain ⟨_, j, k, _, _, hin⟩ := gate_shape h hg
  have e := vl_bin h hg hin
  rw [hin] at h1 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  intro x hx
  have hjk : vl gs x j = c ∧ vl gs x k = c := by
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨hw1 x hx, hw2 x hx⟩
    · exact ⟨hw2 x hx, hw1 x hx⟩
    · exact absurd rfl hne
  rw [e x, hjk.1, hjk.2]
  rcases (gate_shape h hg).1 with hop | hop <;> rw [hop] <;> cases c <;> rfl

/-- A gate constant `c` on a subcube `{x_v = c}` is an alias of the input `v`. -/
theorem al_cst {n : ℕ} {gs : List Gate} {q : ℕ} (hq : q < gs.length) (v : Fin n) (c : Bool)
    (h : Cst n gs {x | x v = c} (n + q) c) : IsAl n gs {x | x v = c} q :=
  ⟨hq, v, by have := v.isLt; omega, fun x hx => by rw [h x hx, vl_in]; exact hx.symm⟩

/-- Two gates reading one wire, the second also reading the first, make the second an alias. -/
theorem absorb {m : ℕ} {gs : List Gate} (h : MClean m gs) {q1 q2 w : ℕ} {g1 g2 : Gate}
    (h1 : gs[q1]? = some g1) (h2 : gs[q2]? = some g2) (hw1 : w ∈ g1.inputs)
    (hw2 : w ∈ g2.inputs) (hq : m + q1 ∈ g2.inputs) (hne : w ≠ m + q1) :
    ∃ j, j < m + q2 ∧ ∀ x : Fin m → Bool, vl gs x (m + q2) = vl gs x j := by
  obtain ⟨hop1, j1, k1, _, _, hin1⟩ := gate_shape h h1
  obtain ⟨hop2, j2, k2, hj2, hk2, hin2⟩ := gate_shape h h2
  have e1 := vl_bin h h1 hin1
  have e2 := vl_bin h h2 hin2
  rw [hin1] at hw1
  rw [hin2] at hw2 hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2 hq
  have hwl : w < m + q2 := by rcases hw2 with rfl | rfl <;> assumption
  have hql : m + q1 < m + q2 := by rcases hq with h | h <;> rw [h] <;> assumption
  -- the value of g2 as op2 (w, g1)
  have v2 : ∀ x : Fin m → Bool, vl gs x (m + q2) = bop g2.op (vl gs x w) (vl gs x (m + q1)) := by
    intro x
    rw [e2 x]
    rcases hw2 with rfl | rfl <;> rcases hq with hq | hq
    · exact (hne (by omega)).elim
    · rw [hq]
    · rw [hq]; rcases hop2 with hop2 | hop2 <;> simp [hop2, Bool.and_comm, Bool.or_comm]
    · exact (hne (by omega)).elim
  -- the value of g1 as op1 (w, y)
  obtain ⟨y, v1⟩ : ∃ y, ∀ x : Fin m → Bool, vl gs x (m + q1) = bop g1.op (vl gs x w) (vl gs x y) := by
    rcases hw1 with rfl | rfl
    · exact ⟨k1, e1⟩
    · refine ⟨j1, fun x => ?_⟩
      rw [e1 x]; rcases hop1 with hop1 | hop1 <;> simp [hop1, Bool.and_comm, Bool.or_comm]
  rcases hop1 with hop1 | hop1 <;> rcases hop2 with hop2 | hop2
  · refine ⟨m + q1, hql, fun x => ?_⟩
    rw [v2 x, v1 x, hop1, hop2]
    cases vl gs x w <;> cases vl gs x y <;> rfl
  · refine ⟨w, hwl, fun x => ?_⟩
    rw [v2 x, v1 x, hop1, hop2]
    cases vl gs x w <;> cases vl gs x y <;> rfl
  · refine ⟨w, hwl, fun x => ?_⟩
    rw [v2 x, v1 x, hop1, hop2]
    cases vl gs x w <;> cases vl gs x y <;> rfl
  · refine ⟨m + q1, hql, fun x => ?_⟩
    rw [v2 x, v1 x, hop1, hop2]
    cases vl gs x w <;> cases vl gs x y <;> rfl

/-! ## Points and the function -/

theorem pt_mem {m : ℕ} {S : Finset (Fin m)} {i : Fin m} : pt S i = true ↔ i ∈ S := by
  simp [pt]

theorem F_pt_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (S : Finset (Fin n))
    (hA : ∀ a ∈ A, a ∉ S) (hE : ∀ i j, G.Adj i j → i ∈ S → j ∈ S → False) :
    F G A (pt S) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  rintro (⟨a, ha, hx⟩ | ⟨i, j, h, hi, hj⟩)
  · exact hA a ha (pt_mem.1 hx)
  · exact hE i j h (pt_mem.1 hi) (pt_mem.1 hj)

theorem F_pt_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (S : Finset (Fin n))
    {i j : Fin n} (h : G.Adj i j) (hi : i ∈ S) (hj : j ∈ S) : F G A (pt S) = true := by
  rw [F_true]; exact Or.inr ⟨i, j, h, pt_mem.2 hi, pt_mem.2 hj⟩

theorem F_single {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {v u : Fin n} (h : G.Adj v u) : F G A (pt {v}) = false :=
  F_pt_false G A {v} (fun a ha hm => by
      rw [Finset.mem_singleton] at hm; subst hm; exact hinv a u h ha)
    (fun i j hij hi hj => by
      rw [Finset.mem_singleton] at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij)

/-! ## The kill lemmas -/

theorem kill {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hRem : ToolRemoval) (hLive : ToolLive) (hc : Cex G A gs o)
    (hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y) (P : Set (Fin n → Bool)) (S : Finset ℕ)
    (hal : ∀ p ∈ S, IsAl n gs P p) :
    ∃ (gs' : List Gate) (o' : ℕ), MClean n gs' ∧ gs'.length + S.card ≤ gs.length ∧
      ∀ x ∈ P, vl gs' x o' = F G A x := by
  obtain ⟨tgt, htgt⟩ := removable_of_alias (o := o) hal
  obtain ⟨gs', r, hcl', hnf', hlen, _, hval⟩ := hRem n gs o P S tgt hc.least.1 htgt
  have ho := (hLive n (F G A) gs o hc.least hnc).1
  have hno : ∀ p ∈ S, tgt p = none → o ≠ n + p := by
    intro p hp hn
    rcases htgt p hp with ⟨_, ⟨j, hj, _⟩ | ⟨_, h2, _⟩⟩
    · rw [hj] at hn; cases hn
    · exact h2
  obtain ⟨_, hv⟩ := hval o ho hno
  exact ⟨gs', r o, ⟨hcl', hnf' hc.least.2.1⟩, hlen, fun x hx => by
    rw [hv x hx]; exact hc.least.2.2.1 x⟩

theorem deep_nc {n : ℕ} {G : SimpleGraph (Fin n)} (A : Finset (Fin n)) {v : Fin n}
    (hd : Deep G v) : ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  obtain ⟨_, _, _, _, _, _, _, _, i, j, hij, _, _⟩ := hd
  exact F_nc G A (Or.inr ⟨i, j, hij⟩)

/-- Three aliases on `{x_v = 0}` at a deep `v` are refuted. -/
theorem kill0 {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hRem : ToolRemoval) (hLive : ToolLive) (hPay0 : ToolPay0) (hc : Cex G A gs o) {v : Fin n}
    (hd : Deep G v) (S : Finset ℕ) (hS : 3 ≤ S.card)
    (hal : ∀ p ∈ S, IsAl n gs {x | x v = false} p) : False := by
  have hnc := deep_nc A hd
  obtain ⟨u1, u2, _, _, _, hadj, _, _, i, j, hij, hi, hj⟩ := hd
  obtain ⟨gs', o', hcl', hlen, hval⟩ := kill hRem hLive hc hnc _ S hal
  exact hPay0 n G A gs o v u1 u2 gs' o' hc ((hadj u1).2 (Or.inl rfl))
    (fun w hw => (hadj w).1 hw) (Or.inr ⟨i, j, hij, hi, hj⟩) hcl' (by omega)
    (fun x hx => hval x hx)

/-- Four aliases on `{x_v = 1}` at a deep `v` are refuted. -/
theorem kill1 {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hRem : ToolRemoval) (hLive : ToolLive) (hPay1 : ToolPay1) (hc : Cex G A gs o) {v : Fin n}
    (hd : Deep G v) (S : Finset ℕ) (hS : 4 ≤ S.card)
    (hal : ∀ p ∈ S, IsAl n gs {x | x v = true} p) : False := by
  obtain ⟨gs', o', hcl', hlen, hval⟩ := kill hRem hLive hc (deep_nc A hd) _ S hal
  exact hPay1 n G A gs o v gs' o' hc hd hcl' (by omega) (fun x hx => hval x hx)

/-- A gate that is not the output of a counterexample is read. -/
theorem read_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hLive : ToolLive) (hc : Cex G A gs o) (hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y)
    {q : ℕ} (hq : q < gs.length) (ho : o ≠ n + q) : ∃ r, Reads gs r (n + q) := by
  obtain ⟨r, hr⟩ := (hLive n (F G A) gs o hc.least hnc).2 q hq ho
  exact ⟨r, mem_rdSet.1 hr⟩

/-- A wire constant `c` on `P` is not the output if `F` is not `c` at some point of `P`. -/
theorem not_out {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hc : Cex G A gs o) {P : Set (Fin n → Bool)} {w : ℕ} {c : Bool} (hw : Cst n gs P w c)
    {x : Fin n → Bool} (hx : x ∈ P) (hF : F G A x ≠ c) : o ≠ w := by
  rintro rfl
  exact hF ((hc.least.2.2.1 x).symm.trans (hw x hx))

/-- No two readers of one wire, the second reading the first (`ToolNoAlias`). -/
theorem noread {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hNA : ToolNoAlias) (hc : Cex G A gs o) (hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y)
    {q1 q2 w : ℕ} (h1 : Reads gs q1 w) (h2 : Reads gs q2 w) (h12 : Reads gs q2 (n + q1))
    (hne : w ≠ n + q1) : False := by
  obtain ⟨g1, hg1, hw1⟩ := h1
  obtain ⟨g2, hg2, hw2⟩ := h2
  obtain ⟨g2', hg2', hq⟩ := h12
  rw [hg2] at hg2'
  cases hg2'
  obtain ⟨j, hj, hv⟩ := absorb hc.least.clean hg1 hg2 hw1 hw2 hq hne
  exact hNA n (F G A) gs o hc.least hnc q2 (List.getElem?_eq_some_iff.1 hg2).1 j hj hv

theorem reads_lt' {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate}
    {o : ℕ} (hc : Cex G A gs o) {q w : ℕ} (h : Reads gs q w) : w < n + q :=
  reads_lt hc.least.1 h

theorem card4 {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]

theorem run_nab {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : ¬ G.Adj a b := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  intro hab
  rcases (h.ha b).1 hab with e | e
  · exact nd.1.2.2.2.1 e.symm
  · exact nd.2.2.1.2.1 e.symm

theorem run_st {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : s ≠ t := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  exact nd.2.2.1.1

/-! ## PFanLow -/

/-- FO2, fan-out 0 and fan-out at least 3. -/
theorem PFanLow_proof (hRem : ToolRemoval) (hLive : ToolLive) (hPay0 : ToolPay0) : PFanLow := by
  intro n G A gs o v hc hd
  have hcl := hc.least.clean
  constructor
  · by_contra h0
    have hE : RdSet gs v = ∅ := Finset.card_eq_zero.1 (by omega)
    have hno : ∀ q, ¬ Reads gs q v := fun q hq => by
      have := mem_rdSet.2 hq
      rw [hE] at this
      exact Finset.notMem_empty _ this
    obtain ⟨u1, u2, c1, c2, _, hadj, _, _, _⟩ := hd
    have hvu : G.Adj v u1 := (hadj u1).2 (Or.inl rfl)
    have hov : o ≠ v := by
      intro hov
      have h1 := hc.least.2.2.1 (pt {v})
      rw [hov, vl_in, F_single hc.inv hvu] at h1
      simp [pt] at h1
    obtain ⟨x, hx⟩ := F_dep G A v u1 hvu (hc.inv u1 v hvu.symm)
    apply hx
    have key := agree_B gs hcl.1 (Function.update x v (!x v)) x (fun j => j = (v : ℕ)) (o + 1)
      ?_ ?_ o (by omega) hov
    · rw [← hc.least.2.2.1, ← hc.least.2.2.1]; exact key
    · intro j hj hjv
      rw [vl_input gs _ j hj, vl_input gs _ j hj, Function.update_of_ne]
      intro h
      apply hjv
      rw [← h]
    · rintro p g hg _ _ ⟨a, ha, hav⟩ _
      exact absurd ⟨g, hg, hav ▸ ha⟩ (hno p)
  · by_contra h3
    exact kill0 hRem hLive hPay0 hc hd (RdSet gs v) (by omega)
      (fun p hp => al_read hcl (mem_rdSet.1 hp) (cst_in gs v false))

/-! ## PFanTwo -/

/-- Two readers of a deep input, the first an AND: three aliases at `x_v := 0`. -/
theorem fan_and {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hRem : ToolRemoval) (hLive : ToolLive) (hPay0 : ToolPay0) (hc : Cex G A gs o) {v : Fin n}
    (hd : Deep G v) {q1 q2 : ℕ} (r1 : Reads gs q1 v) (r2 : Reads gs q2 v) (hne : q1 ≠ q2)
    {g1 : Gate} (hg1 : gs[q1]? = some g1) (hop : g1.op = GateOp.and)
    (nr : ¬ Reads gs q2 (n + q1)) : False := by
  have hcl := hc.least.clean
  have hnc := deep_nc A hd
  have hv1 : (v : ℕ) ∈ g1.inputs := by
    obtain ⟨g, hg, h⟩ := r1
    rw [hg1] at hg
    cases hg
    exact h
  have hc1 : Cst n gs {x | x v = false} (n + q1) false :=
    cst_abs hcl hg1 hv1 (Or.inl ⟨hop, rfl⟩) (cst_in gs v false)
  obtain ⟨_, _, _, _, _, _, _, _, i, j, hij, hi, hj⟩ := id hd
  have hpt : pt {i, j} ∈ {x : Fin n → Bool | x v = false} := by
    show pt {i, j} v = false
    simp [pt, Ne.symm hi, Ne.symm hj]
  have ho : o ≠ n + q1 := not_out hc hc1 hpt (by
    rw [F_pt_true G A {i, j} hij (by simp) (by simp)]; simp)
  obtain ⟨R, hR⟩ := read_of hLive hc hnc (List.getElem?_eq_some_iff.1 hg1).1 ho
  have hR1 : q1 < R := by have := reads_lt' hc hR; omega
  have hR2 : R ≠ q2 := fun h => nr (h ▸ hR)
  refine kill0 hRem hLive hPay0 hc hd {q1, q2, R}
    (Finset.card_eq_three.2 ⟨q1, q2, R, hne, by omega, Ne.symm hR2, rfl⟩).ge ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact al_read hcl r1 (cst_in gs v false)
  · exact al_read hcl r2 (cst_in gs v false)
  · exact al_read hcl hR hc1

/-- Two OR readers of a deep input: four aliases at `x_v := 1`. -/
theorem fan_or {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    (hRem : ToolRemoval) (hLive : ToolLive) (hPay1 : ToolPay1) (hc : Cex G A gs o) {v : Fin n}
    (hd : Deep G v) {q1 q2 : ℕ} (r1 : Reads gs q1 v) (r2 : Reads gs q2 v) (hne : q1 ≠ q2)
    {g1 g2 : Gate} (hg1 : gs[q1]? = some g1) (hop1 : g1.op = GateOp.or)
    (hg2 : gs[q2]? = some g2) (hop2 : g2.op = GateOp.or)
    (nr12 : ¬ Reads gs q2 (n + q1)) (nr21 : ¬ Reads gs q1 (n + q2)) : False := by
  have hcl := hc.least.clean
  have hnc := deep_nc A hd
  have hv1 : (v : ℕ) ∈ g1.inputs := by
    obtain ⟨g, hg, h⟩ := r1
    rw [hg1] at hg
    cases hg
    exact h
  have hv2 : (v : ℕ) ∈ g2.inputs := by
    obtain ⟨g, hg, h⟩ := r2
    rw [hg2] at hg
    cases hg
    exact h
  have hc1 : Cst n gs {x | x v = true} (n + q1) true :=
    cst_abs hcl hg1 hv1 (Or.inr ⟨hop1, rfl⟩) (cst_in gs v true)
  have hc2 : Cst n gs {x | x v = true} (n + q2) true :=
    cst_abs hcl hg2 hv2 (Or.inr ⟨hop2, rfl⟩) (cst_in gs v true)
  obtain ⟨u1, _, _, _, _, hadj, _, _, _⟩ := id hd
  have hvu : G.Adj v u1 := (hadj u1).2 (Or.inl rfl)
  have hpt : pt {v} ∈ {x : Fin n → Bool | x v = true} := pt_mem.2 (Finset.mem_singleton_self v)
  have hF : F G A (pt {v}) ≠ true := by rw [F_single hc.inv hvu]; simp
  obtain ⟨R1, hR1⟩ := read_of hLive hc hnc (List.getElem?_eq_some_iff.1 hg1).1
    (not_out hc hc1 hpt hF)
  obtain ⟨R2, hR2⟩ := read_of hLive hc hnc (List.getElem?_eq_some_iff.1 hg2).1
    (not_out hc hc2 hpt hF)
  have a1 : q1 < R1 := by have := reads_lt' hc hR1; omega
  have a2 : R1 ≠ q2 := fun h => nr12 (h ▸ hR1)
  have b1 : q2 < R2 := by have := reads_lt' hc hR2; omega
  have b2 : R2 ≠ q1 := fun h => nr21 (h ▸ hR2)
  by_cases hR : R1 = R2
  · subst hR
    obtain ⟨gR, hgR, hin1⟩ := id hR1
    obtain ⟨gR', hgR', hin2⟩ := id hR2
    rw [hgR] at hgR'
    cases hgR'
    have hcR : Cst n gs {x | x v = true} (n + R1) true :=
      cst_two hcl hgR hin1 hin2 (by omega) hc1 hc2
    obtain ⟨R', hR'⟩ := read_of hLive hc hnc (List.getElem?_eq_some_iff.1 hgR).1
      (not_out hc hcR hpt hF)
    have c1 : R1 < R' := by have := reads_lt' hc hR'; omega
    refine kill1 hRem hLive hPay1 hc hd {q1, q2, R1, R'}
      (card4 hne (by omega) (by omega) (by omega) (by omega) (by omega)).ge ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact al_read hcl r1 (cst_in gs v true)
    · exact al_read hcl r2 (cst_in gs v true)
    · exact al_read hcl hR1 hc1
    · exact al_read hcl hR' hcR
  · refine kill1 hRem hLive hPay1 hc hd {q1, q2, R1, R2}
      (card4 hne (by omega) (Ne.symm b2) (Ne.symm a2) (by omega) hR).ge ?_
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact al_read hcl r1 (cst_in gs v true)
    · exact al_read hcl r2 (cst_in gs v true)
    · exact al_read hcl hR1 hc1
    · exact al_read hcl hR2 hc2

/-- FO2, fan-out 2: the death table. -/
theorem PFanTwo_proof (hRem : ToolRemoval) (hLive : ToolLive) (hNA : ToolNoAlias)
    (hPay0 : ToolPay0) (hPay1 : ToolPay1) : PFanTwo := by
  intro n G A gs o v hc hd h2
  have hnc := deep_nc A hd
  obtain ⟨q1, q2, hne, hS⟩ := Finset.card_eq_two.1 h2
  have r1 : Reads gs q1 v := mem_rdSet.1 (by rw [hS]; simp)
  have r2 : Reads gs q2 v := mem_rdSet.1 (by rw [hS]; simp)
  have hvlt : ∀ q, (v : ℕ) ≠ n + q := fun q => by have := v.isLt; omega
  have nr12 : ¬ Reads gs q2 (n + q1) := fun h => noread hNA hc hnc r1 r2 h (hvlt q1)
  have nr21 : ¬ Reads gs q1 (n + q2) := fun h => noread hNA hc hnc r2 r1 h (hvlt q2)
  obtain ⟨g1, hg1, _⟩ := id r1
  obtain ⟨g2, hg2, _⟩ := id r2
  rcases (gate_shape hc.least.clean hg1).1 with h1 | h1
  · exact fan_and hRem hLive hPay0 hc hd r1 r2 hne hg1 h1 nr12
  rcases (gate_shape hc.least.clean hg2).1 with h2' | h2'
  · exact fan_and hRem hLive hPay0 hc hd r2 r1 (Ne.symm hne) hg2 h2' nr21
  exact fan_or hRem hLive hPay1 hc hd r1 r2 hne hg1 h1 hg2 h2' nr12 nr21

/-! ## ToolCons -/

/-- Consequences of Lemma 1(a): the two OR readers are distinct and `ws` is false at `e_a`, `e_t`,
`e_b`. -/
theorem ToolCons_proof (hL1a : ToolLemma1a) (hMono : ToolMono) : ToolCons := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hc := hctx.cex
  have hrun := hctx.run
  have hA0 := hctx.hA
  have hsa : G.Adj s a := (hrun.hs a).2 (Or.inl rfl)
  have hst : G.Adj s t := (hrun.hs t).2 (Or.inr rfl)
  have L1 : ∀ t', G.Adj s t' → ∀ z : Fin n → Bool, z t' = true → F G A z = false →
      vl gs z ws = false := fun t' h z hz hF =>
    hL1a n G A gs o s t' qs ws hc.inv hc.least.1 hc.least.2.2.1 hfan.fs hws h z hz hF
  have et : vl gs (pt {t}) ws = false :=
    L1 t hst _ (pt_mem.2 (Finset.mem_singleton_self t)) (F_single hc.inv hst.symm)
  have ea : vl gs (pt {a}) ws = false :=
    L1 a hsa _ (pt_mem.2 (Finset.mem_singleton_self a)) (F_single hc.inv hsa.symm)
  have eb : vl gs (pt {b}) ws = false := by
    by_contra hb
    have hb' : vl gs (pt {b}) ws = true := by simpa using hb
    have hm := hMono n gs hc.least.clean (pt {b}) (pt {a, b}) (fun i hi => by
      rw [pt_mem, Finset.mem_singleton] at hi
      rw [pt_mem, hi]
      simp) ws hb'
    have hF : F G A (pt {a, b}) = false := by
      refine F_pt_false G A _ (by rw [hA0]; simp) ?_
      intro i j hij hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact G.loopless.irrefl _ hij
      · exact run_nab hrun hij
      · exact run_nab hrun hij.symm
      · exact G.loopless.irrefl _ hij
    rw [L1 a hsa _ (pt_mem.2 (by simp)) hF] at hm
    cases hm
  refine ⟨?_, ea, et, eb⟩
  intro heq
  obtain ⟨g, hg, _, hin⟩ := hws
  obtain ⟨g', hg', _, hin'⟩ := hwt
  rw [heq, hg'] at hg
  cases hg
  have hst' : (s : ℕ) ≠ t := fun h => run_st hrun (Fin.ext h)
  have hwt : ws = t := by
    rcases hin with h | h <;> rcases hin' with h' | h' <;> rw [h] at h' <;>
      simp only [List.cons.injEq, and_true] at h' <;> omega
  rw [hwt, vl_in] at et
  simp [pt] at et

/-! ## PReadFew and PReadTwo -/

/-- The reader `e_t` of `x_t` has one or two readers. -/
theorem PReadFew_proof (hRem : ToolRemoval) (hLive : ToolLive) (hPay1 : ToolPay1) :
    PReadFew := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hc := hctx.cex
  have hcl := hc.least.clean
  have hd := hctx.run.deep_t
  have hnc := deep_nc A hd
  have hts : G.Adj t s := (hctx.run.ht s).2 (Or.inl rfl)
  obtain ⟨g, hg, hop, hin⟩ := hwt
  have htin : (t : ℕ) ∈ g.inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hct : Cst n gs {x | x t = true} (n + qt) true :=
    cst_abs hcl hg htin (Or.inr ⟨hop, rfl⟩) (cst_in gs t true)
  have hpt : pt {t} ∈ {x : Fin n → Bool | x t = true} := pt_mem.2 (Finset.mem_singleton_self t)
  have hF : F G A (pt {t}) ≠ true := by rw [F_single hc.inv hts]; simp
  have ho := not_out hc hct hpt hF
  have hqt : qt < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hrt : Reads gs qt t := ⟨g, hg, htin⟩
  constructor
  · obtain ⟨r, hr⟩ := read_of hLive hc hnc hqt ho
    exact Finset.card_pos.2 ⟨r, mem_rdSet.2 hr⟩
  · by_contra h3
    have hnot : qt ∉ RdSet gs (n + qt) := fun h => by
      have := reads_lt' hc (mem_rdSet.1 h); omega
    refine kill1 hRem hLive hPay1 hc hd (insert qt (RdSet gs (n + qt)))
      (by rw [Finset.card_insert_of_notMem hnot]; omega) ?_
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact al_read hcl hrt (cst_in gs t true)
    · exact al_read hcl (mem_rdSet.1 hp) hct

/-- If `e_t` has exactly two readers, both are false at `e_t`. -/
theorem PReadTwo_proof (hRem : ToolRemoval) (hLive : ToolLive) (hNA : ToolNoAlias)
    (hMono : ToolMono) (hPay1 : ToolPay1) : PReadTwo := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt h2 u hu
  have hc := hctx.cex
  have hcl := hc.least.clean
  have hd := hctx.run.deep_t
  have hnc := deep_nc A hd
  have hts : G.Adj t s := (hctx.run.ht s).2 (Or.inl rfl)
  obtain ⟨g, hg, hop, hin⟩ := hwt
  have htin : (t : ℕ) ∈ g.inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hct : Cst n gs {x | x t = true} (n + qt) true :=
    cst_abs hcl hg htin (Or.inr ⟨hop, rfl⟩) (cst_in gs t true)
  have hpt : pt {t} ∈ {x : Fin n → Bool | x t = true} := pt_mem.2 (Finset.mem_singleton_self t)
  have hF : F G A (pt {t}) ≠ true := by rw [F_single hc.inv hts]; simp
  have hrt : Reads gs qt t := ⟨g, hg, htin⟩
  by_contra hne
  have hu1 : vl gs (pt {t}) (n + u) = true := by simpa using hne
  have hru : Reads gs u (n + qt) := mem_rdSet.1 hu
  have hul : u < gs.length := reads_len hru
  have hcu : Cst n gs {x | x t = true} (n + u) true := fun x hx =>
    hMono n gs hcl (pt {t}) x (fun i hi => by
      rw [pt_mem, Finset.mem_singleton] at hi
      rw [hi]
      exact hx) _ hu1
  obtain ⟨v, hv⟩ := read_of hLive hc hnc hul (not_out hc hcu hpt hF)
  obtain ⟨x1, x2, hx12, hS⟩ := Finset.card_eq_two.1 h2
  obtain ⟨u2, hu2, hne2⟩ : ∃ u2 ∈ RdSet gs (n + qt), u2 ≠ u := by
    rw [hS] at hu ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨x2, by simp, Ne.symm hx12⟩
    · exact ⟨x1, by simp, hx12⟩
  have hru2 : Reads gs u2 (n + qt) := mem_rdSet.1 hu2
  have l1 : qt < u := by have := reads_lt' hc hru; omega
  have l2 : qt < u2 := by have := reads_lt' hc hru2; omega
  have l3 : u < v := by have := reads_lt' hc hv; omega
  have hvu2 : v ≠ u2 := by
    intro h
    subst h
    exact noread hNA hc hnc hru hru2 hv (by omega)
  refine kill1 hRem hLive hPay1 hc hd {qt, u, u2, v}
    (card4 (by omega) (by omega) (by omega) (Ne.symm hne2) (by omega) (Ne.symm hvu2)).ge ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact al_read hcl hrt (cst_in gs t true)
  · exact al_cst hul t true hcu
  · exact al_read hcl hru2 hct
  · exact al_read hcl hv hcu

end PEqualNP.MetaComplexity.Loc.Fan
