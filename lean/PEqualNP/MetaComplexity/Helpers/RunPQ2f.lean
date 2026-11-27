import PEqualNP.MetaComplexity.Helpers.RunPQ2e
import PEqualNP.MetaComplexity.Helpers.RunPQ2d

/-!
# The q2 side, item F: no repeated operand, and the chain on the cleaned list (item A)

Conjecture until the checker accepts.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.EdgeFn PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Loc

/-- In a least list no AND or OR gate lists the same wire twice. -/
theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]

/-- Either order of the two operands: they differ. -/
theorem pq2f_ne_pair {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) : a ≠ b := by
  rcases hin with h | h
  · exact pq2f_nodup L hnc hg hop h
  · exact (pq2f_nodup L hnc hg hop h).symm

theorem pq2f_ne_u1 {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y) {p1 : ℕ} {g1 : Gate}
    (hg1 : gs[p1]? = some g1) (ho1 : g1.op = GateOp.or) {q1 : Fin (n + 1)} {u1 : ℕ}
    (hu1 : g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, q1]) : u1 ≠ q1 :=
  (pq2f_ne_pair L hnc hg1 (Or.inr ho1) hu1).symm

theorem pq2f_ne_w1 {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y) {p1 a1 : ℕ}
    {ga1 : Gate} (hga1 : gs[a1]? = some ga1) (hgaop1 : ga1.op = GateOp.and) {w1 : ℕ}
    (hgain1 : ga1.inputs = [n + 1 + p1, w1] ∨ ga1.inputs = [w1, n + 1 + p1]) :
    w1 ≠ n + 1 + p1 :=
  (pq2f_ne_pair L hnc hga1 (Or.inl hgaop1) hgain1).symm

theorem pq2f_ne_W2 {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y) {o2 : ℕ}
    {go2 : Gate} (hgo2 : gs[o2]? = some go2) (hoo2 : go2.op = GateOp.or) {q2 : Fin (n + 1)}
    {W2 : ℕ} (hoin2 : go2.inputs = [(q2 : ℕ), W2] ∨ go2.inputs = [W2, q2]) : W2 ≠ q2 :=
  (pq2f_ne_pair L hnc hgo2 (Or.inr hoo2) hoin2).symm

theorem pq2f_ne_z {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y) {o2 jM : ℕ}
    {gM : Gate} (hgM : gs[jM]? = some gM) (hMop : gM.op = GateOp.and) {z : ℕ}
    (hMin : gM.inputs = [n + 1 + o2, z] ∨ gM.inputs = [z, n + 1 + o2]) : z ≠ n + 1 + o2 :=
  (pq2f_ne_pair L hnc hgM (Or.inl hMop) hMin).symm


/-! ## Item A: the chain on a least list with `F1 = x_j OR H`, unwrapped -/

/-- One step of the cone of a wire: gate `t` reads `a`, and `b` is the wire of gate `t`. -/
def pq2fStep (N : ℕ) (gs : List Gate) (a b : ℕ) : Prop := ∃ t, Reads gs t a ∧ b = N + 1 + t

/-- The cone above wire `a`: the wires reached by a chain of readers. -/
def pq2fCone (N : ℕ) (gs : List Gate) (a b : ℕ) : Prop :=
  Relation.TransGen (pq2fStep N gs) a b

theorem pq2f_step_ge {N : ℕ} {gs : List Gate} {a b : ℕ}
    (h : Relation.TransGen (pq2fStep N gs) a b) : N + 1 ≤ b := by
  cases h with
  | single h => obtain ⟨t, -, rfl⟩ := h; omega
  | tail _ h => obtain ⟨t, -, rfl⟩ := h; omega

theorem pq2f_step_iff {N : ℕ} {gs : List Gate} (hcl : CleanL (N + 1) gs) (a b : ℕ) :
    (∃ j : Fin gs.length, b = N + 1 + j.val ∧
      (((gs.get j).op = GateOp.not ∧ (gs.get j).inputs.head? = some a) ∨
        ((gs.get j).op ≠ GateOp.not ∧ a ∈ (gs.get j).inputs))) ↔ pq2fStep N gs a b := by
  constructor
  · rintro ⟨j, hb, hd⟩
    have hg : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
    exact ⟨j.val, ⟨gs.get j, hg, (pq2e_qaReads_iff (hcl j.val _ hg) a).1 hd⟩, hb⟩
  · rintro ⟨t, ⟨g, hg, hin⟩, hb⟩
    obtain ⟨hp, hgt⟩ := pq2e_get hg
    refine ⟨⟨t, hp⟩, hb, ?_⟩
    rw [hgt]
    exact (pq2e_qaReads_iff (hcl t g hg) a).2 hin

theorem pq2f_cone_iff {N : ℕ} (σ : Equiv.Perm (Fin (N + 1))) (hσ : ∀ i, σ (σ i) = i)
    (gs : List Gate) (a b : ℕ) :
    Relation.TransGen (pq2fStep N (asmG σ gs)) a b ↔
      Relation.TransGen (pq2fStep N gs) (asmW σ a) b := by
  have hs : ∀ a b, pq2fStep N (asmG σ gs) a b ↔ pq2fStep N gs (asmW σ a) b := by
    intro a b
    constructor
    · rintro ⟨t, h, hb⟩; exact ⟨t, (asm_reads σ hσ gs t a).1 h, hb⟩
    · rintro ⟨t, h, hb⟩; exact ⟨t, (asm_reads σ hσ gs t a).2 h, hb⟩
  constructor
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((hs _ _).1 h)
    | tail h1 h2 ih =>
      rename_i m b
      have hm := pq2f_step_ge (gs := asmG σ gs) h1
      exact Relation.TransGen.tail ih (by
        have := (hs m b).1 h2
        rwa [asmW_ge σ hm] at this)
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((hs _ _).2 h)
    | tail h1 h2 ih =>
      rename_i m b
      have hm := pq2f_step_ge (gs := gs) h1
      exact Relation.TransGen.tail ih ((hs m b).2 (by rwa [asmW_ge σ hm]))


theorem pq2f_snoc_eq {N : ℕ} (σ : Equiv.Perm (Fin (N + 1))) (hσ : ∀ i, σ (σ i) = i)
    (j : Fin (N + 1)) (hj : σ j = Fin.last N) (Y : Fin (N + 1) → Bool) (hY : Y j = false) :
    (Fin.snoc (α := fun _ => Bool) (fun k : Fin N => (Y ∘ σ) k.castSucc) false :
      Fin (N + 1) → Bool) = Y ∘ σ := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last, Function.comp]
    rw [← hj, hσ, hY]
  | cast k => simp [Fin.snoc_castSucc]

/-- The facts the chain law gives on a list `gs` with output `o` for an input `j` (`N + 1`
inputs): `c` is the chain of OR gates above `x_j`, the cone of `x_j` is exactly the chain, and
every gate of the chain has an operand outside the cone. -/
def Pq2fChain (N : ℕ) (gs : List Gate) (o : ℕ) (j : ℕ) : Prop :=
  ∃ (k : ℕ) (c : Fin (k + 1) → ℕ), StrictMono c ∧ c (Fin.last k) + 1 = gs.length ∧
      o = N + 1 + c (Fin.last k) ∧
      (∀ i, ∃ g, gs[c i]? = some g ∧ g.op = GateOp.or ∧ g.inputs.length = 2) ∧
      Reads gs (c 0) j ∧ (∀ i : Fin k, Reads gs (c i.succ) (N + 1 + c i.castSucc)) ∧
      (∀ t, Reads gs t j → t = c 0) ∧
      (∀ i : Fin k, ∀ t, Reads gs t (N + 1 + c i.castSucc) → t = c i.succ) ∧
      (∀ t, t < gs.length → (pq2fCone N gs j (N + 1 + t) ↔ ∃ i, c i = t)) ∧
      (∃ w, Reads gs (c 0) w ∧ w ≠ j ∧ w < N + 1 + c 0 ∧ ¬ pq2fCone N gs j w) ∧
      (∀ i : Fin k, ∃ w, Reads gs (c i.succ) w ∧ w ≠ N + 1 + c i.castSucc ∧ w ≠ j ∧
        w < N + 1 + c i.succ ∧ ¬ pq2fCone N gs j w)

/-- The chain law on a least list for `x_j OR H`, unwrapped along the swap of `j` and the last
input. The facts are stated on the list itself (unrelabelled): `x_j` has the single reader
`c 0`, an OR gate of two operands; `c (i+1)` is the single reader of the wire of `c i`; the
cone of `x_j` is exactly the chain; every gate of the chain has an operand outside the cone. -/
theorem pq2f_chain_gen (hch : asmChain) (N : ℕ) (f1 : (Fin (N + 1) → Bool) → Bool)
    (gs : List Gate) (o : ℕ) (L : Least (N + 1) f1 gs o) (j : Fin (N + 1))
    (H : (Fin N → Bool) → Bool) (hH : ∃ y y' : Fin N → Bool, H y ≠ H y')
    (hF : ∀ x : Fin (N + 1) → Bool, f1 x = (x j || H (fun i => x (j.succAbove i)))) :
    Pq2fChain N gs o j := by
  set σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap j (Fin.last N) with hσdef
  have hσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  have hσj : σ j = Fin.last N := by rw [hσdef]; exact Equiv.swap_apply_left _ _
  have hσl : σ (Fin.last N) = j := by rw [hσdef]; exact Equiv.swap_apply_right _ _
  have L' := asm_least σ hσ L
  set gs' := asmG σ gs with hgs'
  set o' := asmW σ o with ho'
  set H' : (Fin N → Bool) → Bool := fun z =>
    f1 ((Fin.snoc (α := fun _ => Bool) z false) ∘ σ) with hH'
  -- the point where H is read
  obtain ⟨y, y', hyy⟩ := hH
  have hpt : ∀ y : Fin N → Bool, ∃ x : Fin (N + 1) → Bool, x (Fin.last N) = false ∧
      f1 (x ∘ σ) = H y := by
    intro y
    refine ⟨(Fin.insertNth (α := fun _ => Bool) j false y) ∘ σ, ?_, ?_⟩
    · simp [hσl]
    · have : ((Fin.insertNth (α := fun _ => Bool) j false y) ∘ σ) ∘ σ =
          Fin.insertNth (α := fun _ => Bool) j false y := by
        funext i; simp [hσ]
      rw [this, hF]
      simp
  have hF1 : ∀ x : Fin (N + 1) → Bool,
      circuitFun (N + 1) (Circuit.mk gs' o') x = (x (Fin.last N) || H' (fun i : Fin N => x i.castSucc)) := by
    intro x
    have h0 : circuitFun (N + 1) (Circuit.mk gs' o') x = f1 (x ∘ σ) := L'.hev x
    rw [h0]
    cases hx : x (Fin.last N)
    · have : (Fin.snoc (α := fun _ => Bool) (fun i : Fin N => x i.castSucc) false) = x := by
        rw [← hx]; exact Fin.snoc_init_self x
      simp only [Bool.false_or, hH', this]
    · rw [hF]
      simp [Function.comp, hσj, hx]
  have hH'nc : ∃ z z' : Fin N → Bool, H' z ≠ H' z' := by
    obtain ⟨x, hx, hv⟩ := hpt y
    obtain ⟨x', hx', hv'⟩ := hpt y'
    refine ⟨fun i => x i.castSucc, fun i => x' i.castSucc, ?_⟩
    have e1 : (Fin.snoc (α := fun _ => Bool) (fun i : Fin N => x i.castSucc) false) = x := by
      rw [← hx]; exact Fin.snoc_init_self x
    have e2 : (Fin.snoc (α := fun _ => Bool) (fun i : Fin N => x' i.castSucc) false) = x' := by
      rw [← hx']; exact Fin.snoc_init_self x'
    simp only [hH', e1, e2, hv, hv']
    exact hyy
  have hnc : ∃ x x' : Fin (N + 1) → Bool, (fun x => f1 (x ∘ σ)) x ≠ (fun x => f1 (x ∘ σ)) x' := by
    obtain ⟨x, -, hv⟩ := hpt y
    obtain ⟨x', -, hv'⟩ := hpt y'
    exact ⟨x, x', by simp only [hv, hv']; exact hyy⟩
  have hmin := asm_least_min L' hnc
  obtain ⟨k, c, hmono, hlast, hout, hops, hin0, hstep, hsing0, hsingi, hcone, hside0, hsidei⟩ :=
    hch N (Circuit.mk gs' o') H' hmin hH'nc hF1
  have hlen : gs'.length = gs.length := asmG_len σ gs
  have hcl' : CleanL (N + 1) gs' := L'.hcl
  have hge : ∀ i : Fin gs'.length, gs'[i.val]? = some (gs'.get i) := fun i =>
    List.getElem?_eq_getElem i.isLt
  -- reads of the relabelled list
  have hrd : ∀ t w, Reads gs' t w ↔ Reads gs t (asmW σ w) := fun t w => asm_reads σ hσ gs t w
  have hrdge : ∀ t w, N + 1 ≤ w → (Reads gs' t w ↔ Reads gs t w) := by
    intro t w hw; rw [hrd, asmW_ge σ hw]
  have hrdN : ∀ t, Reads gs' t N ↔ Reads gs t j := by
    intro t; rw [hrd]
    have : asmW σ N = j := by
      have := asmW_fin σ (Fin.last N); simpa [hσl] using this
    rw [this]
  have hreadiff : ∀ (i : Fin gs'.length) (a : ℕ),
      (((gs'.get i).op = GateOp.not ∧ (gs'.get i).inputs.head? = some a) ∨
        ((gs'.get i).op ≠ GateOp.not ∧ a ∈ (gs'.get i).inputs)) ↔ Reads gs' i.val a := by
    intro i a
    rw [pq2e_qaReads_iff (hcl' i.val _ (hge i))]
    exact ⟨fun h => ⟨_, hge i, h⟩, fun ⟨g, hg, h⟩ => by rw [hge i] at hg; cases hg; exact h⟩
  have hasN : asmW σ N = j := by
    have := asmW_fin σ (Fin.last N); simpa [hσl] using this
  have hconeR : ∀ w, Relation.TransGen (fun a b : ℕ => ∃ j : Fin (Circuit.mk gs' o').gates.length,
        b = N + 1 + j.val ∧ (((Circuit.mk gs' o').gates.get j).op = GateOp.not ∧
          ((Circuit.mk gs' o').gates.get j).inputs.head? = some a ∨
          ((Circuit.mk gs' o').gates.get j).op ≠ GateOp.not ∧
            a ∈ ((Circuit.mk gs' o').gates.get j).inputs)) N w ↔ pq2fCone N gs j w := by
    intro w
    have : (fun a b : ℕ => ∃ j : Fin (Circuit.mk gs' o').gates.length,
        b = N + 1 + j.val ∧ (((Circuit.mk gs' o').gates.get j).op = GateOp.not ∧
          ((Circuit.mk gs' o').gates.get j).inputs.head? = some a ∨
          ((Circuit.mk gs' o').gates.get j).op ≠ GateOp.not ∧
            a ∈ ((Circuit.mk gs' o').gates.get j).inputs)) = pq2fStep N gs' := by
      funext a b
      exact propext (pq2f_step_iff hcl' a b)
    rw [this]
    unfold pq2fCone
    rw [pq2f_cone_iff σ hσ gs N, hasN]
  -- an operand outside the cone, moved back
  have hside : ∀ (p : ℕ) (w : ℕ), Reads gs' p w → w ≠ N →
      ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin (Circuit.mk gs' o').gates.length,
        b = N + 1 + j.val ∧ (((Circuit.mk gs' o').gates.get j).op = GateOp.not ∧
          ((Circuit.mk gs' o').gates.get j).inputs.head? = some a ∨
          ((Circuit.mk gs' o').gates.get j).op ≠ GateOp.not ∧
            a ∈ ((Circuit.mk gs' o').gates.get j).inputs)) N w →
      Reads gs p (asmW σ w) ∧ asmW σ w ≠ j ∧ ¬ pq2fCone N gs j (asmW σ w) := by
    intro p w hr hwn hnt
    refine ⟨(hrd p w).1 hr, ?_, ?_⟩
    · intro h; apply hwn
      exact pq2e_asmW_inj σ hσ (h.trans hasN.symm)
    · intro h
      apply hnt
      rw [hconeR]
      have hge' := pq2f_step_ge h
      have hw : asmW σ w = w := by
        have := asmW_inv σ hσ w
        rwa [asmW_ge σ hge'] at this
      rwa [hw] at h
  unfold Pq2fChain
  refine ⟨k, fun i => (c i).val, fun a b h => hmono h, by simpa [hlen] using hlast, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- output
    have h1 : o' = N + 1 + (c (Fin.last k)).val := hout
    have h2 : o = asmW σ o' := (asmW_inv σ hσ o).symm
    rw [h2, h1, asmW_ge σ (by omega)]
  · intro i
    have hg : (asmG σ gs)[(c i).val]? = some (gs'.get (c i)) := hge (c i)
    rw [asmG_get] at hg
    obtain ⟨g, hg0, hgr⟩ := Option.map_eq_some_iff.1 hg
    refine ⟨g, hg0, ?_, ?_⟩
    · have := (hops i).1
      change (gs'.get (c i)).op = GateOp.or at this
      rw [← hgr] at this
      simpa [relGate] using this
    · have := (hops i).2
      change (gs'.get (c i)).inputs.length = 2 at this
      rw [← hgr] at this
      simpa [relGate] using this
  · have h := hin0
    exact (hrdN _).1 ⟨_, hge (c 0), h⟩
  · intro i
    have h := hstep i
    exact (hrdge _ _ (by omega)).1 ⟨_, hge (c i.succ), h⟩
  · intro t ht
    have hlt : t < gs'.length := by rw [hlen]; exact reads_len ht
    have := hsing0 ⟨t, hlt⟩ ((hreadiff ⟨t, hlt⟩ N).2 ((hrdN t).2 ht))
    exact congrArg Fin.val this
  · intro i t ht
    have hlt : t < gs'.length := by rw [hlen]; exact reads_len ht
    have := hsingi i ⟨t, hlt⟩ ((hreadiff ⟨t, hlt⟩ _).2 ((hrdge _ _ (by omega)).2 ht))
    exact congrArg Fin.val this
  · intro t ht
    have hlt : t < gs'.length := by rw [hlen]; exact ht
    have key := hcone ⟨t, hlt⟩
    rw [← hconeR]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := key.1 h
      exact ⟨i, by simpa using congrArg Fin.val hi⟩
    · rintro ⟨i, hi⟩
      exact key.2 ⟨i, Fin.ext hi⟩
  · obtain ⟨w, hw, hwn, hwlt, hnt⟩ := hside0
    obtain ⟨h1, h2, h3⟩ := hside _ w ⟨_, hge (c 0), hw⟩ hwn hnt
    exact ⟨asmW σ w, h1, h2, asmW_mono_lt σ (by omega) hwlt, h3⟩
  · intro i
    obtain ⟨w, hw, hwa, hwn, hwlt, hnt⟩ := hsidei i
    obtain ⟨h1, h2, h3⟩ := hside _ w ⟨_, hge (c i.succ), hw⟩ hwn hnt
    refine ⟨asmW σ w, h1, ?_, h2, asmW_mono_lt σ (by omega) hwlt, h3⟩
    intro h
    apply hwa
    have := congrArg (asmW σ) h
    rwa [asmW_inv σ hσ, asmW_ge σ (by omega)] at this


/-- With the end `q1` of a run of four set to one, the function is `x_q2 OR H` with `H` not
constant: `H` is the function with `x_q2 := 0`. -/
theorem pq2f_F1 {N : ℕ} (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (j : Fin (N + 1)) (hj : q1.succAbove j = q2) :
    (∀ x : Fin (N + 1) → Bool, F G ∅ (ins q1 true x) =
      (x j || F G ∅ (ins q1 true (Fin.insertNth (α := fun _ => Bool) j false
        (fun i => x (j.succAbove i)))))) ∧
    ∃ y y' : Fin N → Bool, F G ∅ (ins q1 true (Fin.insertNth (α := fun _ => Bool) j false y)) ≠
      F G ∅ (ins q1 true (Fin.insertNth (α := fun _ => Bool) j false y')) := by
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have A10 : G.Adj q1 q0 := (r.h1 q0).2 (Or.inl rfl)
  have nd := r.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  have o0 := r.out0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o0
  obtain ⟨h01, h02, -, -⟩ := o0
  constructor
  · intro x
    cases hx : x j
    · have : x = Fin.insertNth (α := fun _ => Bool) j false (fun i => x (j.succAbove i)) := by
        rw [← hx]; exact (Fin.insertNth_self_removeNth j x).symm
      conv_lhs => rw [this]
      simp
    · simp only [Bool.true_or]
      apply F_true_of q1 q2 A12
      · simp
      · rw [← hj]; simp [hx]
  · -- two points
    have hq0 : q0 ≠ q1 := h01
    obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hq0
    have huj : u ≠ j := by
      intro h; apply h02; rw [← hj, ← hu, h]
    obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq huj
    refine ⟨fun _ => false, fun i => decide (i = v), ?_⟩
    have hT : F G ∅ (ins q1 true (Fin.insertNth (α := fun _ => Bool) j false
        (fun i => decide (i = v)))) = true := by
      apply F_true_of q1 q0 A10
      · simp
      · rw [← hu]; simp only [Fin.insertNth_apply_succAbove]; rw [← hv]; simp
    have hF : F G ∅ (ins q1 true (Fin.insertNth (α := fun _ => Bool) j false
        (fun _ : Fin N => false))) = false := by
      apply F_false_of {q1}
      · intro i hi
        induction i using Fin.succAboveCases q1 with
        | x => simp
        | p i' =>
          exfalso
          simp only [Fin.insertNth_apply_succAbove] at hi
          induction i' using Fin.succAboveCases j with
          | x => simp at hi
          | p i'' => simp at hi
      · simp
      · intro a b hab ha hb
        simp at ha hb
        subst ha; subst hb
        exact G.loopless.irrefl _ hab
    rw [hF, hT]; simp

/-- ITEM A. The chain on `C_1`: the cleaning at `x_q1 := 1` of a least list of a run of four,
when four gates are saved and there is no drop of five, is a least list for `x_q2 OR H` with
`H` not constant (`q2` is the input `j` of the `N + 1` remaining ones), and the chain law holds
on it, unwrapped: see `Pq2fChain`. -/
theorem pq2f_chain (hch : asmChain) (N : ℕ) (G : SimpleGraph (Fin (N + 2)))
    (q0 q1 q2 q3 q4 q5 : Fin (N + 2)) (r : r4Run G q0 q1 q2 q3 q4 q5)
    (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC (N + 1) gs q1 true p) (hcard : 4 ≤ S.card)
    (h5 : ¬ Drop (F G ∅) q1 true 5 gs.length) :
    ∃ (j : Fin (N + 1)) (q : ℕ), q1.succAbove j = q2 ∧
      Least (N + 1) (fun y => F G ∅ (ins q1 true y)) (passG (N + 1) gs q1 true) q ∧
      (passG (N + 1) gs q1 true).length + 4 = gs.length ∧
      Pq2fChain N (passG (N + 1) gs q1 true) q j := by
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have A10 : G.Adj q1 q0 := (r.h1 q0).2 (Or.inl rfl)
  have hnc : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q1 true) ≠ F G ∅ (Function.update y q1 true) := by
    obtain ⟨h1, h2⟩ := asm_dep1 G q1 q0 A10 (fun w h => h.ne.symm)
    exact ⟨fun _ => false, Function.update (fun _ => false) q0 true, by rw [h1, h2]; simp⟩
  obtain ⟨q, hL, hlen⟩ := pq2_c1_least (N + 1) (F G ∅) gs o L q1 true hnc S hS hcard h5
  have hq21 : q2 ≠ q1 := A12.ne.symm
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq21
  obtain ⟨hF, hH⟩ := pq2f_F1 G q0 q1 q2 q3 q4 q5 r j hj
  exact ⟨j, q, hj, hL, hlen, pq2f_chain_gen hch N _ _ q hL j _ hH hF⟩

end PEqualNP.MetaComplexity.Helpers.RunAsm
