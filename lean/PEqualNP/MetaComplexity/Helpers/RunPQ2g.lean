import PEqualNP.MetaComplexity.Helpers.RunPQ2f
import PEqualNP.MetaComplexity.Helpers.RunPOO2

/-!
# The q2 side, items B and C: the reader of `x_q2` back in `C`, and Lemma AP at `q2`

Conjecture until the checker accepts.

* `pq2g_ap` (item C, Lemma AP, direct form (q-a)): in a least list, an AND gate `R` reading the
  input `e` and a gate `G_j` that has no other reader gives `Drop f e false 3`: at `x_e := 0`,
  `R` and its reader read a constant, and `G_j` is dead (`rdel` deletes it, as in `poo_dead`).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- Lemma AP in direct form. An AND gate `R = AND(x_e, G_j)` with `G_j` read by `R` only, in a
least list, with `f` not constant at `x_e := 0`: three gates are saved at `x_e := 0`. -/
theorem pq2g_ap {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (e : Fin (n + 1))
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x e false) ≠ f (Function.update y e false))
    (j r : ℕ) (gR : Gate) (hgR : gs[r]? = some gR) (hop : gR.op = GateOp.and)
    (hin : gR.inputs = [(e : ℕ), n + 1 + j] ∨ gR.inputs = [n + 1 + j, (e : ℕ)])
    (hsole : ∀ t, Reads gs t (n + 1 + j) → t = r) : Drop f e false 3 gs.length := by
  have hcl := L.hcl
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc; exact ⟨_, _, h⟩
  have hRj : Reads gs r (n + 1 + j) :=
    ⟨gR, hgR, by rcases hin with h | h <;> rw [h] <;> simp⟩
  have hRe : Reads gs r e := ⟨gR, hgR, by rcases hin with h | h <;> rw [h] <;> simp⟩
  have hjr : j < r := by have := reads_lt hcl hRj; omega
  have hjlen : j < gs.length := by have := reads_len hRj; omega
  have hrlen : r < gs.length := reads_len hRj
  have hea : (e : ℕ) < n + 1 + j := by have := e.isLt; omega
  have hjo : o ≠ n + 1 + j := poo_out_ne L hfnc hRj
  -- the value of R at x_e = false
  have hRval : ∀ x : Fin (n + 1) → Bool, x e = false → vl gs x (n + 1 + r) = false := by
    intro x hx
    have hxe : vl gs x e = false := by rw [vl_input gs x e e.isLt]; simpa using hx
    rw [vl_gate gs hcl x r gR hgR, hop]
    rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hxe]
  have hro : o ≠ n + 1 + r := by
    intro ho
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← L.hev, ← L.hev, ho, hRval _ (by simp), hRval _ (by simp)]
  obtain ⟨q, hrq, hqr⟩ := L.live hfnc r hrlen (by omega)
  have hqlen : q < gs.length := reads_len hqr
  set gs'' := rdel (n + 1) j e gs with hgs''
  have hcl'' : CleanL (n + 1) gs'' := rdel_clean (n + 1) j e gs hcl hjlen hea
  have hlen'' : gs''.length + 1 = gs.length := rdel_length (n + 1) j e gs hjlen
  have hV : ∀ x : Fin (n + 1) → Bool, x e = false → ∀ w, w ≠ n + 1 + j →
      vl gs'' x (rd (n + 1) j e w) = vl gs x w := by
    intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases lt_or_gt_of_ne hw with hlt | hgt
      · rw [rd_lt _ _ _ _ hlt]
        exact rdel_prefix (n + 1) j e gs hcl hjlen hea x w hlt
      · obtain ⟨s, rfl⟩ : ∃ s, w = n + 1 + s := ⟨w - (n + 1), by omega⟩
        have hrj : j < s := by omega
        rw [rd_gt _ _ _ _ hgt]
        have e1 : n + 1 + s - 1 = n + 1 + (s - 1) := by omega
        rw [e1]
        cases hr : gs[s]? with
        | none =>
          have hl : gs.length ≤ s := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs'' x _ (by omega), vl_beyond gs x _ (by omega)]
        | some g =>
          have hg'' : gs''[s - 1]? = some ⟨g.op, g.inputs.map (rd (n + 1) j e)⟩ := by
            have := poo_rdel_gate hcl j e hjlen s (by omega) g hr
            unfold pooS at this
            rwa [if_neg (by omega)] at this
          rw [vl_gate gs'' hcl'' x (s - 1) _ hg'', vl_gate gs hcl x s g hr]
          by_cases hrp : s = r
          · subst hrp
            have egg : g = gR := Option.some.inj (hr.symm.trans hgR)
            subst egg
            have hxe : vl gs x e = false := by
              rw [vl_input gs x e e.isLt]; simpa using hx
            have hxe'' : vl gs'' x e = false := by
              rw [vl_input gs'' x e e.isLt]; simpa using hx
            show GateOp.eval g.op (List.map (vl gs'' x) (List.map (rd (n + 1) j e) g.inputs)) =
              GateOp.eval g.op (List.map (vl gs x) g.inputs)
            rw [hop]
            rcases hin with h | h <;> rw [h] <;>
              simp [GateOp.eval, rd_lt _ _ _ _ hea, rd_eq, hxe'', hxe]
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro a' ha'
            have hlt := (hcl s g hr).lt a' ha'
            have hne : a' ≠ n + 1 + j := by
              intro h
              exact hrp (hsole s ⟨g, hr, h ▸ ha'⟩)
            exact ih a' hlt hne
  have hfeq : ∀ x : Fin (n + 1) → Bool,
      vl gs'' (Function.update x e false) (rd (n + 1) j e o) = f (Function.update x e false) := by
    intro x
    rw [hV (Function.update x e false) (by simp) o hjo, L.hev]
  have hnc'' : ∃ x y : Fin (n + 1) → Bool,
      vl gs'' (Function.update x e false) (rd (n + 1) j e o) ≠
        vl gs'' (Function.update y e false) (rd (n + 1) j e o) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfeq, hfeq]; exact h⟩
  have hrj' : r ≠ j := by omega
  have hqj' : q ≠ j := by omega
  have hee : rd (n + 1) j e (e : ℕ) = e := rd_lt _ _ _ _ hea
  have hrd1 : Reads gs'' (pooS j r) e := by
    have := poo_rdel_reads hcl j e hjlen hrj' hRe
    rwa [hee] at this
  have hgR'' := poo_rdel_gate hcl j e hjlen r hrj' gR hgR
  have hC1 : IsC n gs'' e false (n + 1 + pooS j r) := by
    obtain ⟨g, hg, hi⟩ := hrd1
    have e1 : g = ⟨gR.op, gR.inputs.map (rd (n + 1) j e)⟩ := by
      rw [hgR''] at hg; exact (Option.some.inj hg).symm
    refine isC_reader hcl'' e (pooS j r) g hg hi false (Or.inr ?_)
    rw [e1]; simp [fixBit, hop]
  have hrdq : Reads gs'' (pooS j q) (n + 1 + pooS j r) := by
    have := poo_rdel_reads hcl j e hjlen hqj' hqr
    rwa [poo_rd_wire j e r hrj'] at this
  have hS := save n (fun x => vl gs'' x (rd (n + 1) j e o)) gs'' (rd (n + 1) j e o) hcl''
    (fun x => rfl) e false hnc'' {pooS j r, pooS j q} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact rc_input false hrd1
      · exact rc_of_reads hrdq hC1)
  have hcard : ({pooS j r, pooS j q} : Finset ℕ).card = 2 := by
    rw [Finset.card_pair]; unfold pooS; split_ifs <;> omega
  rw [hcard] at hS
  obtain ⟨s', hs', hcs⟩ := hS
  refine ⟨s', by omega, ?_⟩
  have e1 : (fun x : Fin (n + 1) → Bool => f (Function.update x e false)) =
      fun x => vl gs'' (Function.update x e false) (rd (n + 1) j e o) := by
    funext x; rw [hfeq]
  rw [e1]
  exact hcs


/-! ## Item B: the reader of a wire of `C_1` back in `C` -/

/-- The final status of the old input `i.succAbove k` is the wire `k`. -/
theorem pq2g_stF_succAbove (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    stF n gs i b (i.succAbove k) = Stat.wire k := by
  show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
  rw [elim_getD n _ _ gs _ (by
    show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact (i.succAbove k).isLt)]
  exact statAt_above n i b k

/-- An old input of final status the wire `j` is `i.succAbove j`. -/
theorem pq2g_input_of_wire (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ)
    (ha : a < n + 1) (j : Fin n) (h : stF n gs i b a = Stat.wire j) :
    a = ((i.succAbove j : Fin (n + 1)) : ℕ) := by
  rcases Fin.eq_self_or_eq_succAbove i ⟨a, ha⟩ with e | ⟨k, e⟩
  · exfalso
    have : a = (i : ℕ) := congrArg Fin.val e
    rw [this, stF_self] at h
    cases h
  · have hk : a = ((i.succAbove k : Fin (n + 1)) : ℕ) := congrArg Fin.val e
    rw [hk, pq2g_stF_succAbove] at h
    have : k = j := by
      simp only [Stat.wire.injEq] at h
      exact Fin.ext h
    rw [hk, this]

/-- One OR reader `p` of the end `i` with an AND reader `a` of it: the pair data. -/
def Pq2gA (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (p a w : ℕ) : Prop :=
  ∃ (g ga : Gate) (u : ℕ), gs[p]? = some g ∧ g.op = GateOp.or ∧
    (g.inputs = [(i : ℕ), u] ∨ g.inputs = [u, (i : ℕ)]) ∧
    gs[a]? = some ga ∧ ga.op = GateOp.and ∧
    (ga.inputs = [n + 1 + p, w] ∨ ga.inputs = [w, n + 1 + p])

/-- The OR reader has constant status one at `x_i := 1`. -/
theorem pq2g_A_true {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) {i : Fin (n + 1)}
    {p a w : ℕ} (h : Pq2gA n gs i p a w) : stF n gs i true (n + 1 + p) = Stat.const true := by
  obtain ⟨g, ga, u, hg, hop, hin, -⟩ := h
  obtain ⟨he1, -⟩ := pq2_emit n gs hcl i true p g hg
  rw [he1]
  rcases hin with h | h <;> rw [h, hop] <;>
    rcases hs : stF n gs i true u with d | k <;>
    simp [simplify, simpOr, stF_self, hs]

/-- The AND reader is an alias of its partner. -/
theorem pq2g_A_alias {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) {i : Fin (n + 1)}
    {p a w : ℕ} (h : Pq2gA n gs i p a w) :
    stF n gs i true (n + 1 + a) = stF n gs i true w := by
  have ht := pq2g_A_true hcl h
  obtain ⟨g, ga, u, hg, hop, hin, hga, haop, hain⟩ := h
  obtain ⟨he1, -⟩ := pq2_emit n gs hcl i true a ga hga
  rw [he1]
  rcases hain with h | h <;> rw [h, haop] <;>
    rcases hs : stF n gs i true w with d | k <;>
    simp [simplify, simpAnd, ht, hs]

theorem pq2g_A_lt {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) {i : Fin (n + 1)}
    {p a w : ℕ} (h : Pq2gA n gs i p a w) : w < n + 1 + a ∧ a < gs.length := by
  obtain ⟨g, ga, u, hg, hop, hin, hga, haop, hain⟩ := h
  refine ⟨(hcl a ga hga).lt w (by rcases hain with h | h <;> rw [h] <;> simp),
    (List.getElem?_eq_some_iff.1 hga).1⟩

/-- An AND reader is not the source of a reader of `C_1` reading a wire below `n`. -/
theorem pq2g_A_nosrc {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) {i : Fin (n + 1)}
    {p a w : ℕ} (h : Pq2gA n gs i p a w) (g : Gate) (hg : gs[a]? = some g) (a' : ℕ)
    (ha' : a' ∈ g.inputs) (j m : ℕ) (hj : j < n) (hs : stF n gs i true a' = Stat.wire j)
    (hm : n ≤ m) (hst : stF n gs i true (n + 1 + a) = Stat.wire m) : False := by
  have ht := pq2g_A_true hcl h
  have hal := pq2g_A_alias hcl h
  obtain ⟨g0, ga, u, hg0, hop, hin, hga, haop, hain⟩ := h
  have : ga = g := Option.some.inj (hga.symm.trans hg)
  subst this
  rw [hal] at hst
  rcases hain with h | h <;> rw [h] at ha' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' <;>
    rcases ha' with rfl | rfl
  · rw [ht] at hs; cases hs
  · rw [hst] at hs; simp only [Stat.wire.injEq] at hs; omega
  · rw [hst] at hs; simp only [Stat.wire.injEq] at hs; omega
  · rw [ht] at hs; cases hs

/-- A partner of the cleaned list: if the first AND reader is an alias of the wire `j`, then one of
the two partners is the input `i.succAbove j` itself. -/
theorem pq2g_pair {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) {i : Fin (n + 1)}
    {p1 p2 a1 a2 w1 w2 : ℕ} (hA1 : Pq2gA n gs i p1 a1 w1) (hA2 : Pq2gA n gs i p2 a2 w2)
    (hmem : ∀ t, RC n gs i true t → t = p1 ∨ t = p2 ∨ t = a1 ∨ t = a2)
    (j : Fin n) (hs : stF n gs i true (n + 1 + a1) = Stat.wire j) :
    w1 = ((i.succAbove j : Fin (n + 1)) : ℕ) ∨ w2 = ((i.succAbove j : Fin (n + 1)) : ℕ) := by
  have t1 := pq2g_A_true hcl hA1
  have t2 := pq2g_A_true hcl hA2
  have l1 := pq2g_A_lt hcl hA1
  have l2 := pq2g_A_lt hcl hA2
  have al1 := pq2g_A_alias hcl hA1
  have al2 := pq2g_A_alias hcl hA2
  have s1 : stF n gs i true w1 = Stat.wire j := by rw [← al1]; exact hs
  by_cases hw1 : w1 < n + 1
  · exact Or.inl (pq2g_input_of_wire n gs i true w1 hw1 j s1)
  · obtain ⟨t, rfl⟩ : ∃ t, w1 = n + 1 + t := ⟨w1 - (n + 1), by omega⟩
    obtain ⟨gt, hgt⟩ : ∃ gt, gs[t]? = some gt :=
      ⟨gs[t]'(by have := l1.1; have := l1.2; omega), List.getElem?_eq_getElem _⟩
    have hrc := pq2_wire_low n gs hcl i true t gt hgt j j.isLt s1
    rcases hmem t hrc with rfl | rfl | rfl | rfl
    · rw [t1] at s1; cases s1
    · rw [t2] at s1; cases s1
    · omega
    · -- t = a2
      have s2 : stF n gs i true w2 = Stat.wire j := by rw [← al2]; exact s1
      by_cases hw2 : w2 < n + 1
      · exact Or.inr (pq2g_input_of_wire n gs i true w2 hw2 j s2)
      · obtain ⟨t', rfl⟩ : ∃ t', w2 = n + 1 + t' := ⟨w2 - (n + 1), by omega⟩
        obtain ⟨gt', hgt'⟩ : ∃ gt', gs[t']? = some gt' :=
          ⟨gs[t']'(by have := l2.1; have := l2.2; omega), List.getElem?_eq_getElem _⟩
        have hrc' := pq2_wire_low n gs hcl i true t' gt' hgt' j j.isLt s2
        rcases hmem t' hrc' with rfl | rfl | rfl | rfl
        · rw [t1] at s2; cases s2
        · rw [t2] at s2; cases s2
        · omega
        · omega

/-- ITEM B, generic form. A gate of `passG` at `x_i := 1` that reads the input wire `j` comes from
a source gate `p` of `C` (not one of the four saved gates, operation kept, status the new wire)
which reads either the old input `i.succAbove j` itself, or one of the two AND readers
`A_1`, `A_2` of shape (i), one of whose partners is that input. -/
theorem pq2g_back_gen (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (p1 p2 a1 a2 w1 w2 : ℕ) (hA1 : Pq2gA n gs i p1 a1 w1) (hA2 : Pq2gA n gs i p2 a2 w2)
    (hmem : ∀ t, RC n gs i true t → t = p1 ∨ t = p2 ∨ t = a1 ∨ t = a2)
    (k : ℕ) (g' : Gate) (hk : (passG n gs i true)[k]? = some g') (j : Fin n)
    (hj : (j : ℕ) ∈ g'.inputs) :
    ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ p ≠ p1 ∧ p ≠ p2 ∧ p ≠ a1 ∧ p ≠ a2 ∧
      pq2E n gs i true p = k ∧ g'.op = g.op ∧
      stF n gs i true (n + 1 + p) = Stat.wire (n + k) ∧
      (((i.succAbove j : Fin (n + 1)) : ℕ) ∈ g.inputs ∨
        ((n + 1 + a1 ∈ g.inputs ∨ n + 1 + a2 ∈ g.inputs) ∧
          (w1 = ((i.succAbove j : Fin (n + 1)) : ℕ) ∨ w2 = ((i.succAbove j : Fin (n + 1)) : ℕ)))) := by
  obtain ⟨p, g, hp, hE, hop, hst, a, ha, hsa⟩ := pq2_reader n gs hcl i true k g' hk j hj
  have t1 := pq2g_A_true hcl hA1
  have t2 := pq2g_A_true hcl hA2
  have hnot1 : p ≠ p1 := by rintro rfl; rw [t1] at hst; cases hst
  have hnot2 : p ≠ p2 := by rintro rfl; rw [t2] at hst; cases hst
  have hnot3 : p ≠ a1 := by
    rintro rfl
    exact pq2g_A_nosrc hcl hA1 g hp a ha j (n + k) j.isLt hsa (by omega) hst
  have hnot4 : p ≠ a2 := by
    rintro rfl
    exact pq2g_A_nosrc hcl hA2 g hp a ha j (n + k) j.isLt hsa (by omega) hst
  refine ⟨p, g, hp, hnot1, hnot2, hnot3, hnot4, hE, hop, hst, ?_⟩
  by_cases ha1 : a < n + 1
  · left
    rw [pq2g_input_of_wire n gs i true a ha1 j hsa] at ha
    exact ha
  · right
    obtain ⟨t, rfl⟩ : ∃ t, a = n + 1 + t := ⟨a - (n + 1), by omega⟩
    have hlt := (hcl p g hp).lt _ ha
    have hpl := (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨gt, hgt⟩ : ∃ gt, gs[t]? = some gt :=
      ⟨gs[t]'(by omega), List.getElem?_eq_getElem _⟩
    have hrc := pq2_wire_low n gs hcl i true t gt hgt j j.isLt hsa
    rcases hmem t hrc with rfl | rfl | rfl | rfl
    · rw [t1] at hsa; cases hsa
    · rw [t2] at hsa; cases hsa
    · exact ⟨Or.inl ha, pq2g_pair hcl hA1 hA2 hmem j hsa⟩
    · refine ⟨Or.inr ha, ?_⟩
      have := pq2g_pair hcl hA2 hA1 (by
        intro t ht; rcases hmem t ht with h | h | h | h <;> simp [h]) j hsa
      exact this.symm

/-- At a run end the restriction `x_q2 := 0` is not constant. -/
theorem pq2g_nc_q2 {N : ℕ} (G : SimpleGraph (Fin N)) (q0 q1 q2 q3 q4 q5 : Fin N)
    (r : r4Run G q0 q1 q2 q3 q4 q5) :
    ∃ x y : Fin N → Bool, F G ∅ (Function.update x q2 false) ≠ F G ∅ (Function.update y q2 false) := by
  have A10 : G.Adj q1 q0 := (r.h1 q0).2 (Or.inl rfl)
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have hq21 : q2 ≠ q1 := A12.ne.symm
  have o0 := r.out0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o0
  obtain ⟨h01, h02, -, -⟩ := o0
  refine ⟨fun _ => false, fun i => decide (i = q0 ∨ i = q1), ?_⟩
  have h1 : F G ∅ (Function.update (fun _ => false) q2 false) = false := by
    apply F_false_of ∅
    · intro i hi
      by_cases h : i = q2
      · subst h; simp at hi
      · simp [Function.update_of_ne h] at hi
    · simp
    · intro a b _ ha; simp at ha
  have h2 : F G ∅ (Function.update (fun i => decide (i = q0 ∨ i = q1)) q2 false) = true := by
    apply F_true_of q1 q0 A10
    · rw [Function.update_of_ne (Ne.symm hq21)]; simp
    · rw [Function.update_of_ne h02]; simp
  rw [h1, h2]; simp

/-- Lemma AP at `q2` on a shape (i) list: `A_k = AND(G_(p_k), x_q2)` with `G_(p_k)` read by `A_k`
only gives `Drop (F G ∅) q2 false 3`. -/
theorem pq2g_ap_q2 {N : ℕ} (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) {gs : List Gate} {o : ℕ} (L : Least (N + 2) (F G ∅) gs o)
    (p a : ℕ) (ga : Gate) (hga : gs[a]? = some ga) (hop : ga.op = GateOp.and)
    (hin : ga.inputs = [N + 2 + p, (q2 : ℕ)] ∨ ga.inputs = [(q2 : ℕ), N + 2 + p])
    (hsole : ∀ t, Reads gs t (N + 2 + p) → t = a) : Drop (F G ∅) q2 false 3 gs.length :=
  pq2g_ap (n := N + 1) L q2 (pq2g_nc_q2 G q0 q1 q2 q3 q4 q5 r) p a ga hga hop
    (by rcases hin with h | h
        · exact Or.inr h
        · exact Or.inl h) hsole

/-- ITEM B. At the end `q1` of a run of four, in shape (i), with no drop of five at `x_q1 := 1`:
`C_1` is a least list with the chain on it (item A), and every reader of the input wire `j` of
`x_q2` in `C_1` comes from a gate `p` of `C`, outside `{p1, p2, a1, a2}`, of the same operation,
with the status the new wire; and either `p` reads `x_q2` itself (case R: the reader of `x_q2`
in `C`), or `p` reads `A_1` or `A_2` and one of the partners `w_1`, `w_2` is `x_q2` (case Q1, to which
`pq2g_ap_q2` applies). -/
theorem pq2g_back (hch : asmChain) (N : ℕ) (G : SimpleGraph (Fin (N + 2)))
    (q0 q1 q2 q3 q4 q5 : Fin (N + 2)) (r : r4Run G q0 q1 q2 q3 q4 q5)
    (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (p1 p2 : ℕ) (g1 g2 : Gate) (u1 u2 : ℕ)
    (hg1 : gs[p1]? = some g1) (ho1 : g1.op = GateOp.or)
    (hu1 : g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, (q1 : ℕ)])
    (hg2 : gs[p2]? = some g2) (ho2 : g2.op = GateOp.or)
    (hu2 : g2.inputs = [(q1 : ℕ), u2] ∨ g2.inputs = [u2, (q1 : ℕ)])
    (h12 : p1 ≠ p2)
    (a1 a2 : ℕ) (ga1 ga2 : Gate) (w1 w2 : ℕ) (h12' : a1 ≠ a2)
    (hga1 : gs[a1]? = some ga1) (hao1 : ga1.op = GateOp.and)
    (hai1 : ga1.inputs = [N + 2 + p1, w1] ∨ ga1.inputs = [w1, N + 2 + p1])
    (hga2 : gs[a2]? = some ga2) (hao2 : ga2.op = GateOp.and)
    (hai2 : ga2.inputs = [N + 2 + p2, w2] ∨ ga2.inputs = [w2, N + 2 + p2])
    (h5 : ¬ Drop (F G ∅) q1 true 5 gs.length) :
    ∃ (j : Fin (N + 1)) (q : ℕ), q1.succAbove j = q2 ∧
      Least (N + 1) (fun y => F G ∅ (ins q1 true y)) (passG (N + 1) gs q1 true) q ∧
      (passG (N + 1) gs q1 true).length + 4 = gs.length ∧
      Pq2fChain N (passG (N + 1) gs q1 true) q j ∧
      ∀ (k : ℕ) (g' : Gate), (passG (N + 1) gs q1 true)[k]? = some g' → (j : ℕ) ∈ g'.inputs →
        ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ p ≠ p1 ∧ p ≠ p2 ∧ p ≠ a1 ∧ p ≠ a2 ∧
          pq2E (N + 1) gs q1 true p = k ∧ g'.op = g.op ∧
          stF (N + 1) gs q1 true (N + 2 + p) = Stat.wire (N + 1 + k) ∧
          ((q2 : ℕ) ∈ g.inputs ∨
            ((N + 2 + a1 ∈ g.inputs ∨ N + 2 + a2 ∈ g.inputs) ∧
              (w1 = (q2 : ℕ) ∨ w2 = (q2 : ℕ)))) := by
  have hcl := L.hcl
  have hmem1 : (q1 : ℕ) ∈ g1.inputs := by rcases hu1 with h | h <;> rw [h] <;> simp
  have hmem2 : (q1 : ℕ) ∈ g2.inputs := by rcases hu2 with h | h <;> rw [h] <;> simp
  have hin1 : N + 2 + p1 ∈ ga1.inputs := by rcases hai1 with h | h <;> rw [h] <;> simp
  have hin2 : N + 2 + p2 ∈ ga2.inputs := by rcases hai2 with h | h <;> rw [h] <;> simp
  have c1 : IsC (N + 1) gs q1 true (N + 2 + p1) :=
    isC_reader hcl q1 p1 g1 hg1 hmem1 true (Or.inr (by simp [fixBit, ho1]))
  have c2 : IsC (N + 1) gs q1 true (N + 2 + p2) :=
    isC_reader hcl q1 p2 g2 hg2 hmem2 true (Or.inr (by simp [fixBit, ho2]))
  have r1 : RC (N + 1) gs q1 true p1 := rc_input true ⟨g1, hg1, hmem1⟩
  have r2 : RC (N + 1) gs q1 true p2 := rc_input true ⟨g2, hg2, hmem2⟩
  have r3 : RC (N + 1) gs q1 true a1 := rc_of_reads ⟨ga1, hga1, hin1⟩ c1
  have r4 : RC (N + 1) gs q1 true a2 := rc_of_reads ⟨ga2, hga2, hin2⟩ c2
  have d13 : p1 ≠ a1 := by
    intro h; rw [h] at hg1; rw [hg1] at hga1; cases hga1; rw [hao1] at ho1; cases ho1
  have d14 : p1 ≠ a2 := by
    intro h; rw [h] at hg1; rw [hg1] at hga2; cases hga2; rw [hao2] at ho1; cases ho1
  have d23 : p2 ≠ a1 := by
    intro h; rw [h] at hg2; rw [hg2] at hga1; cases hga1; rw [hao1] at ho2; cases ho2
  have d24 : p2 ≠ a2 := by
    intro h; rw [h] at hg2; rw [hg2] at hga2; cases hga2; rw [hao2] at ho2; cases ho2
  have hcard : ({p1, p2, a1, a2} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, d13, d14]),
      Finset.card_insert_of_notMem (by simp [d23, d24]), Finset.card_pair h12']
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have A10 : G.Adj q1 q0 := (r.h1 q0).2 (Or.inl rfl)
  have hnc : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q1 true) ≠ F G ∅ (Function.update y q1 true) := by
    obtain ⟨h1, h2⟩ := asm_dep1 G q1 q0 A10 (fun w h => h.ne.symm)
    exact ⟨fun _ => false, Function.update (fun _ => false) q0 true, by rw [h1, h2]; simp⟩
  have hmem : ∀ t, RC (N + 1) gs q1 true t → t = p1 ∨ t = p2 ∨ t = a1 ∨ t = a2 := by
    intro t ht
    have := pq2_rc_mem (N + 1) (F G ∅) gs o L q1 true hnc h5 {p1, p2, a1, a2} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption) hcard t ht
    simpa using this
  have hA1 : Pq2gA (N + 1) gs q1 p1 a1 w1 := ⟨g1, ga1, u1, hg1, ho1, hu1, hga1, hao1, hai1⟩
  have hA2 : Pq2gA (N + 1) gs q1 p2 a2 w2 := ⟨g2, ga2, u2, hg2, ho2, hu2, hga2, hao2, hai2⟩
  obtain ⟨j, q, hj, hL, hlen, hch'⟩ :=
    pq2f_chain hch N G q0 q1 q2 q3 q4 q5 r gs o L {p1, p2, a1, a2}
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> assumption) (by rw [hcard]) h5
  refine ⟨j, q, hj, hL, hlen, hch', ?_⟩
  intro k g' hk hjin
  obtain ⟨p, g, hp, n1, n2, n3, n4, hE, hop, hst, hr⟩ :=
    pq2g_back_gen (N + 1) gs hcl q1 p1 p2 a1 a2 w1 w2 hA1 hA2 hmem k g' hk j hjin
  refine ⟨p, g, hp, n1, n2, n3, n4, hE, hop, hst, ?_⟩
  rw [hj] at hr
  exact hr

end PEqualNP.MetaComplexity.Helpers.RunAsm
