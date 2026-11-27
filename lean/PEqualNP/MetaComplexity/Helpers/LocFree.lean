import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Monotone local-class bound (`L-meta-115`): base, free steps, and the pay tools

Builder file of the plan `LocPlan.lean`. Proves the pieces `PBase`, `PS1`, `PTwin`, `PLeafLow`
and the tools `ToolPay0`, `ToolPay1`, `ToolPayPair`, each from the first-wave tools it needs
(taken as explicit hypotheses, statements fixed in `LocPlan.lean`).

The free steps follow `ForestBound.claimQ` with `HasMonoSize` in place of `HasCircuitSize`:
instead of the full-basis gate elimination, a reader of the fixed input is an alias of an earlier
wire on the subcube, so `ToolRemoval` drops it, `ToolRestrict` gives a circuit of the restricted
function, and the induction hypothesis bounds it.
-/

namespace PEqualNP.MetaComplexity.Loc.Free

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-! ## Circuit helpers -/

/-- A gate of a clean NOT-free list is a binary AND or OR of two earlier wires. -/
theorem vl_bin {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) : ∃ j k, j < m + p ∧ k < m + p ∧ g.inputs = [j, k] ∧
      ((∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j && vl gs x k)) ∨
        (∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j || vl gs x k))) := by
  rcases hcl p g hp with ⟨hnot, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hnot (hnf g (List.mem_of_getElem? hp))
  refine ⟨j, k, hj, hk, hin, ?_⟩
  rcases hop with hop | hop
  · left
    intro x
    rw [vl_gate gs hcl x p g hp, hop, hin]
    simp [GateOp.eval]
  · right
    intro x
    rw [vl_gate gs hcl x p g hp, hop, hin]
    simp [GateOp.eval]

/-- A gate reading a wire that is constant on `P` is an alias of an earlier wire on `P`. -/
theorem alias_of_rd {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p w : ℕ}
    (hr : Reads gs p w) (P : Set (Fin m → Bool)) (c : Bool) (hc : ∀ x ∈ P, vl gs x w = c) :
    ∃ t, t < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x t := by
  obtain ⟨g, hg, hw⟩ := hr
  obtain ⟨j, k, hj, hk, hin, hv⟩ := vl_bin hcl hnf hg
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> rcases hv with hv | hv <;> cases c
  · exact ⟨w, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨k, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨k, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨j, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨j, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hk, fun x hx => by rw [hv, hc x hx]; simp⟩

/-- A reader of a wire `w` is constant, at some value `c`, wherever `w` has the value `c`. -/
theorem abs_rd {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p w : ℕ}
    (hr : Reads gs p w) : ∃ c : Bool, ∀ x : Fin m → Bool, vl gs x w = c → vl gs x (m + p) = c := by
  obtain ⟨g, hg, hw⟩ := hr
  obtain ⟨j, k, _, _, hin, hv⟩ := vl_bin hcl hnf hg
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hv with hv | hv
  · refine ⟨false, fun x hx => ?_⟩
    rw [hv]
    rcases hw with rfl | rfl <;> simp [hx]
  · refine ⟨true, fun x hx => ?_⟩
    rw [hv]
    rcases hw with rfl | rfl <;> simp [hx]

/-- The output wire of a list computing a function that is not constant is a wire of the list. -/
theorem out_lt {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) : o < m + gs.length := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]

/-- The output is not the input `i` when the function differs from `x_i` somewhere. -/
theorem out_ne {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (i : Fin m) (x : Fin m → Bool) (h : f x ≠ x i) : o ≠ (i : ℕ) := by
  intro e
  apply h
  rw [← hev x, e, vl_input gs x i i.isLt]

/-- An input the function depends on, other than the output, is read (copy of
`Readers.Least.dep_read`, which uses only the evaluation). -/
theorem read_of_dep {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (i : Fin m)
    (hd : ∃ x : Fin m → Bool, f (Function.update x i (!x i)) ≠ f x) (hoi : o ≠ (i : ℕ)) :
    ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← hev, ← hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Liveness from the removal tool: in a least NOT-free list every gate other than the output
is read. -/
theorem live (hRem : ToolRemoval) {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} (hp : p < gs.length)
    (ho : o ≠ m + p) : ∃ q, Reads gs q (m + p) := by
  by_contra hno
  have hrem : Removable m gs o Set.univ {p} (fun _ => none) := by
    intro p' hp'
    rw [Finset.mem_singleton] at hp'
    subst hp'
    refine ⟨hp, Or.inr ⟨rfl, ho, fun q hq => absurd ⟨q, hq⟩ hno, fun _ _ => by simp⟩⟩
  obtain ⟨gs', r, hcl', hnf', hlen, _, hval⟩ := hRem m gs o Set.univ {p} _ hL.1 hrem
  have hol := out_lt hL.2.2.1 hnc
  obtain ⟨_, hv⟩ := hval o hol (fun p' hp' _ => by
    rw [Finset.mem_singleton] at hp'
    subst hp'
    exact ho)
  have := hL.2.2.2 gs' (r o) hcl' (hnf' hL.2.1) (fun x => by
    rw [hv x (Set.mem_univ x)]
    exact hL.2.2.1 x)
  rw [Finset.card_singleton] at hlen
  omega

/-- Removing a set of aliases on `P` from a least NOT-free list. -/
theorem elimAl (hRem : ToolRemoval) {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (P : Set (Fin m → Bool))
    (S : Finset ℕ) (tgt : ℕ → ℕ)
    (hS : ∀ p ∈ S, p < gs.length ∧ tgt p < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x (tgt p)) :
    ∃ (gs' : List Gate) (o' : ℕ), MClean m gs' ∧ gs'.length + S.card ≤ gs.length ∧
      ∀ x ∈ P, vl gs' x o' = f x := by
  have hrem : Removable m gs o P S (fun p => some (tgt p)) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    exact ⟨h1, Or.inl ⟨tgt p, rfl, h2, h3⟩⟩
  obtain ⟨gs', r, hcl', hnf', hlen, _, hval⟩ := hRem m gs o P S _ hL.1 hrem
  obtain ⟨_, hv⟩ := hval o (out_lt hL.2.2.1 hnc) (fun p _ h => by simp at h)
  exact ⟨gs', r o, ⟨hcl', hnf' hL.2.1⟩, hlen, fun x hx => by rw [hv x hx]; exact hL.2.2.1 x⟩

/-! ## Graph helpers -/

theorem afree_del {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (h : AFree G A)
    (X : Finset (Fin n)) : AFree (delV G X) A :=
  fun i j hij => h i j ((delV_adj G X i j).1 hij).1

/-- A NOT-free list computing `F G A` on `{x_i = b}`, where the restriction is `F G' A'` and the
induction hypothesis covers `(G', A')`: `Phi1 G' A'` is at most its length plus one. -/
theorem payR (hR : ToolRestrict) {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    (hih : IH G A) {G' : SimpleGraph (Fin n)} {A' : Finset (Fin n)} (hle : G' ≤ G)
    (hfree : AFree G' A')
    (hlt : G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) (i : Fin n)
    (b : Bool) (hres : ∀ x, F G A (Function.update x i b) = F G' A' x)
    (hnc : A'.Nonempty ∨ ∃ i j, G'.Adj i j) {gs' : List Gate} {o' : ℕ} (hcl : MClean n gs')
    (hcomp : ∀ x : Fin n → Bool, x i = b → vl gs' x o' = F G A x) :
    Phi1 G' A' ≤ gs'.length + 1 := by
  have hf : ∀ x, vl gs' (Function.update x i b) o' = F G' A' x := by
    intro x
    rw [hcomp _ (by simp), hres]
  have hnc' : ∃ x y : Fin n → Bool,
      vl gs' (Function.update x i b) o' ≠ vl gs' (Function.update y i b) o' := by
    obtain ⟨x, y, h⟩ := F_nc G' A' hnc
    exact ⟨x, y, by rw [hf, hf]; exact h⟩
  have hM := hR n gs' o' i b hcl hnc'
  have e : (fun x => vl gs' (Function.update x i b) o') = F G' A' := funext hf
  rw [e] at hM
  exact hih G' A' hle hfree hlt _ hM

theorem pt_eq {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : pt S i = decide (i ∈ S) := rfl

/-! ## The pay tools -/

theorem ToolPay0_proof (hR : ToolRestrict) (hRes0 : ToolRes0) (hD0 : ToolDrop0) : ToolPay0 := by
  intro n G A gs o v u1 u2 gs' o' hc hvu hN hne hcl hlen hcomp
  have hvA : v ∉ A := hc.inv v u1 hvu
  have h0 := hD0 n G A v u1 u2 hvu hN
  have hnc : A.Nonempty ∨ ∃ i j, (delV G {v}).Adj i j := by
    rcases hne with h | ⟨i, j, h, hi, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, j, (delV_adj G {v} i j).2 ⟨h, by simpa using hi, by simpa using hj⟩⟩
  have := payR hR hc.ih (delV_le G {v}) (afree_del hc.inv {v}) (Or.inl h0.2) v false
    (fun x => hRes0 n G A v x hvA) hnc hcl hcomp
  have := hc.small
  omega

theorem ToolPay1_proof (hR : ToolRestrict) (hRes1 : ToolRes1) (hD1 : ToolDrop1) : ToolPay1 := by
  intro n G A gs o v gs' o' hc hd hcl hlen hcomp
  obtain ⟨u1, u2, c1, c2, _, hN, h1, h2, _⟩ := hd
  have hvu : G.Adj v u1 := (hN u1).2 (Or.inl rfl)
  have hvA : v ∉ A := hc.inv v u1 hvu
  have hu1 : u1 ∉ A := hc.inv u1 v hvu.symm
  have hu2 : u2 ∉ A := hc.inv u2 v ((hN u2).2 (Or.inr rfl)).symm
  have hN' : ∀ w, G.Adj v w ↔ w ∈ ({u1, u2} : Finset (Fin n)) := by
    intro w
    rw [hN]
    simp
  have h0 := hD1 n G A v u1 u2 c1 c2 hN h1 h2 hu1 hu2
  have hfree : AFree (delV G (insert v {u1, u2})) (A ∪ {u1, u2}) := by
    intro i j hij hi
    rw [delV_adj] at hij
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hc.inv i j hij.1 hi
    · exact hij.2.1 (Finset.mem_insert_of_mem hi)
  have := payR hR hc.ih (delV_le G _) hfree (Or.inl h0.2) v true
    (fun x => hRes1 n G A v {u1, u2} x hvA hN') (Or.inl ⟨u1, by simp⟩) hcl hcomp
  have := hc.small
  omega

theorem ToolPayPair_proof (hR : ToolRestrict) (hLeast : ToolLeast) (hResP : ToolResPair)
    (hDP : ToolDropPair) : ToolPayPair := by
  intro n G A gs o a' a s t b b' gs' o' hc hrun hcl hlen hcomp
  have nd := hrun.nd
  have hst : s ≠ t := by rintro rfl; simp at nd
  have hbs : b ≠ s := by rintro rfl; simp at nd
  have hstb : [s, t, b].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at nd ⊢
    tauto
  have hadj_st : G.Adj s t := (hrun.hs t).2 (Or.inr rfl)
  have hadj_tb : G.Adj t b := (hrun.ht b).2 (Or.inr rfl)
  have hsA : s ∉ A := hc.inv s t hadj_st
  have htA : t ∉ A := hc.inv t s hadj_st.symm
  have hbA : b ∉ A := hc.inv b t hadj_tb.symm
  have h0 := hDP n G A a s t b b' hstb (fun w hw => (hrun.hs w).1 hw) hrun.ht
    (fun w hw => (hrun.hb w).1 hw) hbA
  set G2 := delV G {s, t, b} with hG2
  have hfree : AFree G2 (insert b A) := by
    intro i j hij hi
    rw [hG2, delV_adj] at hij
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hij.2.1 (by simp)
    · exact hc.inv i j hij.1 hi
  have hkey : ∀ x, vl gs' (Function.update (Function.update x s false) t true) o' =
      F G2 (insert b A) x := by
    intro x
    rw [hcomp _ (by simp) (by rw [Function.update_of_ne hst]; simp),
      Function.update_comm hst]
    exact hResP n G A s t b x hst hbs hsA htA hbA hrun.ht
  obtain ⟨x0, y0, hxy⟩ := F_nc G2 (insert b A) (Or.inl (Finset.insert_nonempty _ _))
  have hnc1 : ∃ x y : Fin n → Bool,
      vl gs' (Function.update x t true) o' ≠ vl gs' (Function.update y t true) o' :=
    ⟨Function.update x0 s false, Function.update y0 s false, by rw [hkey, hkey]; exact hxy⟩
  have hM1 := hR n gs' o' t true hcl hnc1
  obtain ⟨x1, y1, hxy1⟩ := hnc1
  obtain ⟨gs2, o2, hL2, hlen2⟩ := hLeast n _ _ ⟨x1, y1, hxy1⟩ hM1
  have hev2 : ∀ x, vl gs2 (Function.update x s false) o2 = F G2 (insert b A) x := by
    intro x
    rw [hL2.2.2.1]
    exact hkey x
  have hnc2 : ∃ x y : Fin n → Bool,
      vl gs2 (Function.update x s false) o2 ≠ vl gs2 (Function.update y s false) o2 :=
    ⟨x0, y0, by rw [hev2, hev2]; exact hxy⟩
  have hM2 := hR n gs2 o2 s false hL2.clean hnc2
  have e : (fun x => vl gs2 (Function.update x s false) o2) = F G2 (insert b A) := funext hev2
  rw [e] at hM2
  have := hc.ih G2 (insert b A) (delV_le G _) hfree (Or.inl h0.2) _ hM2
  have := hc.small
  omega

/-! ## The base -/

theorem PBase_proof : PBase := by
  intro n G A hE s hM
  have hdep := PermInputs.dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hM.has
  have he := noedge_ncard G hE
  have ht := tau_le G ∅ (fun i j h => absurd h (hE i j))
  rw [Finset.card_empty] at ht
  unfold Phi1
  omega

/-! ## Free step S1 -/

theorem PS1_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hResA : ToolResA) : PS1 := by
  intro n G A hinv hih hA hE s hM
  by_contra hlt
  have hnc := F_nc G A (Or.inl hA)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G A) s hnc hM
  obtain ⟨a, ha⟩ := hA
  obtain ⟨i, j, hij⟩ := hE
  have hia : i ≠ a := fun e => hinv i j hij (e ▸ ha)
  have hja : j ≠ a := fun e => hinv j i hij.symm (e ▸ ha)
  have hoa : o ≠ (a : ℕ) := out_ne hL.2.2.1 a (pt {i, j}) (by
    rw [pt_eq]
    have : F G A (pt {i, j}) = true := by
      rw [F_true]
      exact Or.inr ⟨i, j, hij, by simp [pt], by simp [pt]⟩
    rw [this]
    simp [hia.symm, hja.symm])
  obtain ⟨q, hq⟩ := read_of_dep hL.2.2.1 a (F_dep_A G A a ha) hoa
  obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hq {x | x a = false} false (fun x hx => by
    rw [vl_input gs x a a.isLt]
    exact hx)
  obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc {x | x a = false} {q} (fun _ => t)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨reads_len hq, ht, hal⟩)
  have hfree : AFree G (A.erase a) := fun i j h hi => hinv i j h (Finset.mem_of_mem_erase hi)
  have := payR hR hih (le_refl G) hfree (Or.inr ⟨rfl, Finset.card_erase_lt_of_mem ha⟩) a false
    (fun x => hResA n G A a x hinv ha) (Or.inr ⟨i, j, hij⟩) hcl' (fun x hx => hcomp x hx)
  rw [Finset.card_singleton] at hlen'
  have hc := Finset.card_erase_add_one ha
  unfold Phi1 at this hlt
  omega

/-! ## Graph identities at a leaf -/

theorem del_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n)
    (hleaf : ∀ w, G.Adj l w → w = p) : delV G {l} = G.deleteEdges {s(l, p)} := by
  ext i j
  rw [delV_adj, deleteEdges_adj]
  simp only [Finset.mem_singleton, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hi rfl
    · exact hj rfl
  · rintro ⟨h, hne⟩
    refine ⟨h, ?_, ?_⟩
    · rintro rfl
      exact hne (Or.inl ⟨rfl, hleaf j h⟩)
    · rintro rfl
      exact hne (Or.inr ⟨hleaf i h.symm, rfl⟩)

theorem del_leaf2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q) :
    delV G (insert l {p}) = G.deleteEdges {s(p, l), s(p, q)} := by
  ext i j
  rw [delV_adj, deleteEdges_adj]
  constructor
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, fun he => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp at hi hj
  · rintro ⟨h, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, not_or] at hne
    refine ⟨h, ?_, ?_⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    · refine ⟨fun e => ?_, fun e => ?_⟩
      · subst e
        have := hleaf j h
        subst this
        simp at hne
      · subst e
        rcases hp j h with rfl | rfl <;> simp at hne
    · refine ⟨fun e => ?_, fun e => ?_⟩
      · subst e
        have := hleaf i h.symm
        subst this
        simp at hne
      · subst e
        rcases hp i h.symm with rfl | rfl <;> simp at hne

/-- Drop at a leaf set to `0`: at most 2 (one edge, the cover drops by at most one). -/
theorem drop_leaf0 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (hlp : G.Adj l p)
    (hleaf : ∀ w, G.Adj l w → w = p) :
    Phi1 G ∅ ≤ Phi1 (delV G {l}) ∅ + 2 ∧ (delV G {l}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [del_leaf G l p hleaf]
  have he := ncard_del1 G l p hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(l, p)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  constructor <;> omega

/-- Drop at a leaf set to `1`: at most 2 (two edges and the cover, one free input gained). -/
theorem drop_leaf1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (hlp : G.Adj l p)
    (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q) :
    Phi1 G ∅ ≤ Phi1 (delV G (insert l {p})) (∅ ∪ {p}) + 2 ∧
      (delV G (insert l {p})).edgeSet.ncard < G.edgeSet.ncard := by
  rw [del_leaf2 G l p q hleaf hp]
  obtain ⟨he1, he2⟩ := ncard_del2 G l p q hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(p, l), s(p, q)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rcases he with rfl | he
    · exact Sym2.mem_mk_left _ _
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact Sym2.mem_mk_left _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  simp only [Finset.empty_union, Finset.card_singleton, Finset.card_empty]
  constructor <;> omega

/-! ## Free step S2 (twin leaves) -/

theorem PTwin_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hRes0 : ToolRes0) : PTwin := by
  intro n G A l p l' hinv hih hA0 hlp hleaf hpl' hl'l hleaf' s hM
  subst hA0
  by_contra hlt
  have hnc := F_nc G ∅ (Or.inr ⟨l, p, hlp⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G ∅) s hnc hM
  have hpl : p ≠ l := hlp.ne.symm
  have hpl'0 : (delV G {l}).Adj p l' := (delV_adj G {l} p l').2 ⟨hpl', by simpa using hpl,
    by simpa using hl'l⟩
  have hol : o ≠ (l : ℕ) := out_ne hL.2.2.1 l (pt {p, l'}) (by
    rw [pt_eq]
    have : F G ∅ (pt {p, l'}) = true := by
      rw [F_true]
      exact Or.inr ⟨p, l', hpl', by simp [pt], by simp [pt]⟩
    rw [this]
    simp [hpl.symm, hl'l.symm])
  obtain ⟨q, hq⟩ := read_of_dep hL.2.2.1 l (F_dep G ∅ l p hlp (by simp)) hol
  obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hq {x | x l = false} false (fun x hx => by
    rw [vl_input gs x l l.isLt]
    exact hx)
  obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc {x | x l = false} {q} (fun _ => t)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨reads_len hq, ht, hal⟩)
  have hdel := del_leaf G l p hleaf
  have he := ncard_del1 G l p hlp
  rw [← hdel] at he
  have := payR hR hih (delV_le G {l}) (afree_del hinv {l}) (Or.inl (by omega)) l false
    (fun x => hRes0 n G ∅ l x (by simp)) (Or.inr ⟨p, l', hpl'0⟩) hcl' (fun x hx => hcomp x hx)
  have htau : tau G ≤ tau (delV G {l}) := by
    obtain ⟨T, hT, hTc⟩ := tau_attained (delV G {l})
    rw [← hTc]
    rw [hdel] at hT
    exact cov_swap G l p l' (tau G) hl'l hpl' hleaf' (fun T h => tau_le G T h) T hT
  rw [Finset.card_singleton] at hlen'
  unfold Phi1 at this hlt
  omega

/-! ## Free steps S3, S4 (a leaf at a vertex of low degree) -/

theorem PLeafLow_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hRes0 : ToolRes0) (hRes1 : ToolRes1) : PLeafLow := by
  intro n G A l p q hinv hih hA0 hlp hleaf hp s hM
  subst hA0
  by_contra hlt
  have hpl : p ≠ l := hlp.ne.symm
  obtain ⟨d0, d0e⟩ := drop_leaf0 G l p hlp hleaf
  obtain ⟨d1, d1e⟩ := drop_leaf1 G l p q hlp hleaf hp
  by_cases hE0 : ∃ i j, (delV G {l}).Adj i j
  swap
  · -- the one-edge graph: two inputs the function depends on
    have hE0' : ∀ i j, ¬ (delV G {l}).Adj i j := fun i j h => hE0 ⟨i, j, h⟩
    have he := noedge_ncard _ hE0'
    have ht := tau_le (delV G {l}) ∅ (fun i j h => absurd h (hE0' i j))
    have hdep := PermInputs.dep_lower_set n (F G ∅) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact F_dep G ∅ i p hlp (by simp)
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact F_dep G ∅ i l hlp.symm (by simp)) s hM.has
    rw [Finset.card_pair hlp.ne] at hdep
    unfold Phi1 at d0 hlt
    rw [Finset.card_empty] at ht d0 hlt
    omega
  obtain ⟨i, j, hij⟩ := hE0
  obtain ⟨hijG, hil, hjl⟩ := (delV_adj G {l} i j).1 hij
  have hil' : i ≠ l := by simpa using hil
  have hjl' : j ≠ l := by simpa using hjl
  have hnc := F_nc G ∅ (Or.inr ⟨l, p, hlp⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G ∅) s hnc hM
  have hFij : F G ∅ (pt {i, j}) = true := by
    rw [F_true]
    exact Or.inr ⟨i, j, hijG, by simp [pt], by simp [pt]⟩
  have hFl : F G ∅ (pt {l}) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩)
    · simp at ha
    · simp [pt] at ha hb
      subst ha
      subst hb
      exact hab.ne rfl
  have hptl : pt {i, j} l = false := by
    rw [pt_eq]
    simp [hil'.symm, hjl'.symm]
  have hol : o ≠ (l : ℕ) := out_ne hL.2.2.1 l (pt {i, j}) (by rw [hFij, hptl]; simp)
  -- the key count: two aliases on `{x_l = c}` contradict the induction hypothesis
  have key : ∀ (c : Bool) (S : Finset ℕ) (tgt : ℕ → ℕ), 2 ≤ S.card →
      (∀ r ∈ S, r < gs.length ∧ tgt r < n + r ∧
        ∀ x ∈ {x : Fin n → Bool | x l = c}, vl gs x (n + r) = vl gs x (tgt r)) → False := by
    intro c S tgt hS2 hS
    obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc _ S tgt hS
    cases c
    · have := payR hR hih (delV_le G {l}) (afree_del hinv {l}) (Or.inl d0e) l false
        (fun x => hRes0 n G ∅ l x (by simp)) (Or.inr ⟨i, j, hij⟩) hcl'
        (fun x hx => hcomp x hx)
      omega
    · have hN : ∀ w, G.Adj l w ↔ w ∈ ({p} : Finset (Fin n)) := by
        intro w
        rw [Finset.mem_singleton]
        exact ⟨hleaf w, fun h => h ▸ hlp⟩
      have hfree : AFree (delV G (insert l {p})) (∅ ∪ {p}) := by
        intro a b hab ha
        rw [delV_adj] at hab
        rw [Finset.empty_union] at ha
        exact hab.2.1 (Finset.mem_insert_of_mem ha)
      have := payR hR hih (delV_le G _) hfree (Or.inl d1e) l true
        (fun x => hRes1 n G ∅ l {p} x (by simp) hN) (Or.inl ⟨p, by simp⟩) hcl'
        (fun x hx => hcomp x hx)
      omega
  obtain ⟨r, hr⟩ := read_of_dep hL.2.2.1 l (F_dep G ∅ l p hlp (by simp)) hol
  by_cases h2 : ∃ r', r' ≠ r ∧ Reads gs r' l
  · -- two readers of `x_l`: two aliases at `x_l := 0`
    obtain ⟨r', hr'r, hr'⟩ := h2
    have hc0 : ∀ x ∈ {x : Fin n → Bool | x l = false}, vl gs x l = false := fun x hx => by
      rw [vl_input gs x l l.isLt]
      exact hx
    obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hr _ false hc0
    obtain ⟨t', ht', hal'⟩ := alias_of_rd hL.1 hL.2.1 hr' _ false hc0
    refine key false {r, r'} (fun z => if z = r then t else t') (by
      rw [Finset.card_pair hr'r.symm]) ?_
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨reads_len hr, by simp [ht], fun x hx => by simp [hal x hx]⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact ⟨reads_len hr', by simp [hr'r, ht'], fun x hx => by simp [hr'r, hal' x hx]⟩
  · -- a single reader `r`: constant `c` at `x_l := c`, so it has a reader `r2`
    obtain ⟨c, hcst⟩ := abs_rd hL.1 hL.2.1 hr
    have hcst' : ∀ x : Fin n → Bool, x l = c → vl gs x (n + r) = c := fun x hx =>
      hcst x (by rw [vl_input gs x l l.isLt]; exact hx)
    have hor : o ≠ n + r := by
      intro e
      cases c
      · have := hcst' (pt {i, j}) hptl
        rw [← e, hL.2.2.1, hFij] at this
        exact Bool.noConfusion this
      · have := hcst' (pt {l}) (by simp [pt])
        rw [← e, hL.2.2.1, hFl] at this
        exact Bool.noConfusion this
    obtain ⟨r2, hr2⟩ := live hRem hL hnc (reads_len hr) hor
    have hr2r : r2 ≠ r := by
      intro e
      have := reads_lt hL.1 hr2
      omega
    obtain ⟨t2, ht2, hal2⟩ := alias_of_rd hL.1 hL.2.1 hr2 {x | x l = c} c
      (fun x hx => hcst' x hx)
    refine key c {r, r2} (fun z => if z = r then (l : ℕ) else t2) (by
      rw [Finset.card_pair hr2r.symm]) ?_
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · refine ⟨reads_len hr, by simp; omega, fun x hx => ?_⟩
      simp only [ite_true]
      rw [hcst' x hx, vl_input gs x l l.isLt]
      exact hx.symm
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact ⟨reads_len hr2, by simp [hr2r, ht2], fun x hx => by simp [hr2r, hal2 x hx]⟩

end PEqualNP.MetaComplexity.Loc.Free
