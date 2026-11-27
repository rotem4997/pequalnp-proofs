import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3477

open PEqualNP.CircuitLowerBounds

def lval (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or  => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lstep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  w ++ [lval g.op (g.inputs.map fun i => w.getD i (false, false))]

def linit (isLine : ℕ → Bool) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)

theorem lp_eq (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x = C.gates.foldl lstep (linit isLine x) := rfl

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem getD_snoc {α : Type} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_append_left h, if_pos h]
  · rw [List.getElem?_append_right (by omega), if_neg h]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

theorem linit_getD (isLine : ℕ → Bool) (x : List Bool) (i : ℕ) :
    (linit isLine x).getD i (false, false) =
      if isLine i then (false, x.getD i false) else (x.getD i false, false) := by
  unfold linit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_zipIdx]
  cases x[i]? <;> simp

theorem linit_length (isLine : ℕ → Bool) (x : List Bool) : (linit isLine x).length = x.length := by
  simp [linit]

theorem unread (j : ℕ) : ∀ (gs : List Gate) (w w' : List (Bool × Bool)), w.length = w'.length →
    (∀ i, i ≠ j → w.getD i (false, false) = w'.getD i (false, false)) → (∀ g ∈ gs, j ∉ g.inputs) →
    ∀ i, i ≠ j → (gs.foldl lstep w).getD i (false, false) = (gs.foldl lstep w').getD i (false, false) := by
  intro gs
  induction gs with
  | nil => intro w w' _ h _ i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hl h hg i hi
    simp only [List.foldl_cons]
    have hins : g.inputs.map (fun i => w.getD i (false, false)) =
        g.inputs.map (fun i => w'.getD i (false, false)) :=
      List.map_congr_left (fun k hk => h k (fun e => hg g List.mem_cons_self (e ▸ hk)))
    apply ih
    · simp [lstep, hl]
    · intro k hk
      unfold lstep
      rw [hins, getD_snoc, getD_snoc, hl]
      split_ifs
      · exact h k hk
      · rfl
      · rfl
    · intro g' hg'; exact hg g' (List.mem_cons_of_mem _ hg')
    · exact hi

def Inv (w : List (Bool × Bool)) (v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, ((w.getD i (false, false)).1 = true → v.getD i false = true) ∧
    ((w.getD i (false, false)).2 = true → v.getD i false = true)

theorem inv_step (w : List (Bool × Bool)) (v : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h2 : g.inputs.length = 2) (h : Inv w v) :
    Inv (lstep w g) (wstep v g) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  obtain ⟨hl, hi⟩ := h
  refine ⟨by simp [lstep, wstep, hl], ?_⟩
  intro i
  unfold lstep wstep
  rw [getD_snoc, getD_snoc, hl]
  split_ifs with h1 h3
  · exact hi i
  · obtain ⟨ha1, ha2⟩ := hi a
    obtain ⟨hb1, hb2⟩ := hi b
    rw [hab]
    simp only [List.map_cons, List.map_nil]
    clear hi
    revert ha1 ha2 hb1 hb2
    generalize w.getD a (false, false) = A
    generalize w.getD b (false, false) = B
    generalize v.getD a false = va
    generalize v.getD b false = vb
    obtain ⟨A1, A2⟩ := A
    obtain ⟨B1, B2⟩ := B
    rcases hop with hop | hop <;> rw [hop] <;>
      cases A1 <;> cases A2 <;> cases B1 <;> cases B2 <;> cases va <;> cases vb <;>
      simp [lval, GateOp.eval]
  · simp

theorem inv_fold : ∀ (gs : List Gate) (w : List (Bool × Bool)) (v : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) → Inv w v →
    Inv (gs.foldl lstep w) (gs.foldl wstep v) := by
  intro gs
  induction gs with
  | nil => intro w v _ h; exact h
  | cons g gs ih =>
    intro w v hg h
    simp only [List.foldl_cons]
    exact ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (inv_step w v g (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2 h)

theorem inv_init (isLine : ℕ → Bool) (x : List Bool) : Inv (linit isLine x) x := by
  refine ⟨linit_length _ _, fun i => ?_⟩
  rw [linit_getD]
  split_ifs <;> simp

def Nop (w : List (Bool × Bool)) : Prop := ∀ i, (w.getD i (false, false)).2 = false

theorem nop_fold : ∀ (gs : List Gate) (w : List (Bool × Bool)),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) → Nop w →
    Nop (gs.foldl lstep w) := by
  intro gs
  induction gs with
  | nil => intro w _ h; exact h
  | cons g gs ih =>
    intro w hg h
    simp only [List.foldl_cons]
    apply ih _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro i
    obtain ⟨hop, h2⟩ := hg g List.mem_cons_self
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
    unfold lstep
    rw [getD_snoc]
    split_ifs
    · exact h i
    · have ha := h a
      have hb := h b
      rw [hab]
      simp only [List.map_cons, List.map_nil]
      revert ha hb
      generalize w.getD a (false, false) = A
      generalize w.getD b (false, false) = B
      obtain ⟨A1, A2⟩ := A
      obtain ⟨B1, B2⟩ := B
      intro ha hb
      simp only at ha hb
      subst ha hb
      rcases hop with hop | hop <;> rw [hop] <;> simp [lval]
    · rfl

theorem flat_len : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length = 2) →
    (gs.flatMap (·.inputs)).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro _; simp
  | cons g gs ih =>
    intro h
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')), h g List.mem_cons_self]
    ring

theorem deg_le (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1) (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  set T := Finset.univ.filter (fun l => I p l)
  let A : Fin N → Finset (Fin N) := fun l => (Finset.univ.filter (fun p' => I p' l)).erase p
  have hA : ∀ l ∈ T, (A l).card = q := by
    intro l hl
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    have hc : (Finset.univ.filter (fun p' => I p' l)).card = q + 1 := by
      rw [← hL l, Fintype.card_subtype]
    simp only [A]
    rw [Finset.card_erase_of_mem (by simp [hpl]), hc]
    rfl
  have hdis : ∀ l ∈ T, ∀ l' ∈ T, l ≠ l' → Disjoint (A l) (A l') := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro p' h1 h2
    simp only [A, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    have hpl' : I p l' := (Finset.mem_filter.mp hl').2
    obtain ⟨m, _, hm⟩ := hU p p' (Ne.symm h1.1)
    exact hne ((hm l ⟨hpl, h1.2⟩).trans (hm l' ⟨hpl', h2.2⟩).symm)
  have hsub : T.biUnion A ⊆ Finset.univ.erase p := by
    intro p' hp'
    simp only [Finset.mem_biUnion, A, Finset.mem_erase] at hp'
    obtain ⟨l, _, hne, _⟩ := hp'
    simp [hne]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis, Finset.sum_congr rfl hA, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  have h2 : T.card * q ≤ (q + 1) * q := by
    calc T.card * q ≤ N - 1 := hcard
      _ = (q + 1) * q := by rw [hN]; ring_nf; omega
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

theorem ofFn_eq (n j : ℕ) (f : Fin n) (hf : (f : ℕ) = j) :
    List.ofFn (fun k : Fin n => decide (k = f)) = (List.range n).map (fun i => i == j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hij : i = j <;> simp [Fin.ext_iff, hf, hij]

end PEqualNP.Outside.L_meta_3477

theorem PEqualNP.Outside.L_meta_3477 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (9 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I _ C hq hq9 hN hL hU hAO hSound
  have hg : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  let isLine : ℕ → Bool := fun i => decide (i < N)
  let R : Finset ℕ := (C.gates.flatMap (·.inputs)).toFinset ∪ {C.output}
  have hR : R.card ≤ 2 * C.size + 1 := by
    refine (Finset.card_union_le _ _).trans ?_
    have := List.toFinset_card_le (C.gates.flatMap (·.inputs))
    rw [PEqualNP.Outside.L_meta_3477.flat_len _ (fun g hg => hAO.2.2 g hg)] at this
    simp only [Finset.card_singleton]
    unfold PEqualNP.CircuitLowerBounds.Circuit.size
    omega
  have hnotread : ∀ j, j ∉ R → (∀ g ∈ C.gates, j ∉ g.inputs) ∧ j ≠ C.output := by
    intro j hj
    simp only [R, Finset.mem_union, List.mem_toFinset, List.mem_flatMap, Finset.mem_singleton,
      not_or, not_exists, not_and] at hj
    exact ⟨fun g hg hm => hj.1 g hg hm, hj.2⟩
  -- the key membership fact
  have key : ∀ p l : Fin N, I p l →
      PEqualNP.ReadK.lineSingle C (N + N) isLine p (N + l) = true →
      (p : ℕ) ∈ R ∧ N + (l : ℕ) ∈ R := by
    intro p l _ hs
    unfold PEqualNP.ReadK.lineSingle at hs
    rw [PEqualNP.Outside.L_meta_3477.lp_eq] at hs
    constructor
    · by_contra hp
      obtain ⟨hg1, hout⟩ := hnotread _ hp
      have he := PEqualNP.Outside.L_meta_3477.unread (p : ℕ) C.gates
        (PEqualNP.Outside.L_meta_3477.linit isLine
          ((List.range (N + N)).map fun i => i == (p : ℕ) || i == N + (l : ℕ)))
        (PEqualNP.Outside.L_meta_3477.linit isLine
          ((List.range (N + N)).map fun i => i == N + (l : ℕ)))
        (by simp [PEqualNP.Outside.L_meta_3477.linit_length])
        (by
          intro i hi
          rw [PEqualNP.Outside.L_meta_3477.linit_getD, PEqualNP.Outside.L_meta_3477.linit_getD]
          have : ((List.range (N + N)).map fun i => i == (p : ℕ) || i == N + (l : ℕ)).getD i false =
              ((List.range (N + N)).map fun i => i == N + (l : ℕ)).getD i false := by
            by_cases hn : i < N + N <;> simp [List.getD_eq_getElem?_getD, hi, Ne.symm hi, hn]
          rw [this])
        hg1 C.output (Ne.symm hout)
      rw [he] at hs
      have hn := PEqualNP.Outside.L_meta_3477.nop_fold C.gates (PEqualNP.Outside.L_meta_3477.linit isLine ((List.range (N + N)).map fun i => i == N + (l : ℕ))) hg (by
        intro i
        rw [PEqualNP.Outside.L_meta_3477.linit_getD]
        by_cases hi : i < N
        · have hx : ((List.range (N + N)).map fun i => i == N + (l : ℕ)).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map]
            by_cases hn : i < N + N
            · rw [List.getElem?_range hn]
              simp
              omega
            · rw [List.getElem?_eq_none (by simp; omega)]
              rfl
          rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hx
          simp [isLine, hi, hx]
        · simp [isLine, hi])
        C.output
      rw [hn] at hs
      exact Bool.false_ne_true hs
    · by_contra hl
      obtain ⟨hg1, hout⟩ := hnotread _ hl
      have he := PEqualNP.Outside.L_meta_3477.unread (N + (l : ℕ)) C.gates
        (PEqualNP.Outside.L_meta_3477.linit isLine
          ((List.range (N + N)).map fun i => i == (p : ℕ) || i == N + (l : ℕ)))
        (PEqualNP.Outside.L_meta_3477.linit isLine
          ((List.range (N + N)).map fun i => i == (p : ℕ)))
        (by simp [PEqualNP.Outside.L_meta_3477.linit_length])
        (by
          intro i hi
          rw [PEqualNP.Outside.L_meta_3477.linit_getD, PEqualNP.Outside.L_meta_3477.linit_getD]
          have : ((List.range (N + N)).map fun i => i == (p : ℕ) || i == N + (l : ℕ)).getD i false =
              ((List.range (N + N)).map fun i => i == (p : ℕ)).getD i false := by
            by_cases hn : i < N + N <;> simp [List.getD_eq_getElem?_getD, hi, Ne.symm hi, hn]
          rw [this])
        hg1 C.output (Ne.symm hout)
      rw [he] at hs
      have hinv := PEqualNP.Outside.L_meta_3477.inv_fold C.gates _ _ hg
        (PEqualNP.Outside.L_meta_3477.inv_init isLine ((List.range (N + N)).map fun i => i == (p : ℕ)))
      have hv := (hinv.2 C.output).2 hs
      rw [← PEqualNP.Outside.L_meta_3477.wires_eq] at hv
      have hz := hSound (fun k => decide (k = Fin.castAdd N p))
        (by
          rw [Fintype.card_eq_zero_iff.mpr]
          · omega
          · constructor
            rintro ⟨x, hx⟩
            simp [Fin.ext_iff] at hx
            omega)
        (by
          rintro ⟨a, b, _, _, hb⟩
          simp [Fin.ext_iff] at hb
          omega)
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval at hz
      rw [PEqualNP.Outside.L_meta_3477.ofFn_eq (N + N) p (Fin.castAdd N p) rfl] at hz
      rw [hz] at hv
      exact Bool.false_ne_true hv
  -- counting
  let P' := Finset.univ.filter (fun p : Fin N => (p : ℕ) ∈ R)
  let L' := Finset.univ.filter (fun l : Fin N => N + (l : ℕ) ∈ R)
  have hPL : P'.card + L'.card ≤ 2 * C.size + 1 := by
    have hsub : P'.image (fun p : Fin N => (p : ℕ)) ∪ L'.image (fun l : Fin N => N + (l : ℕ)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_image, P', L', Finset.mem_filter,
        Finset.mem_univ, true_and] at hx
      rcases hx with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · exact hp
      · exact hl
    have hdis : Disjoint (P'.image (fun p : Fin N => (p : ℕ))) (L'.image (fun l : Fin N => N + (l : ℕ))) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨p, _, rfl⟩ := h1
      obtain ⟨l, _, hl⟩ := h2
      have := p.isLt
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at this
    omega
  let S := Finset.univ.filter (fun x : Fin N × Fin N =>
    I x.1 x.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) isLine x.1 (N + x.2) = true)
  have hS : Fintype.card { x13 : Fin N × Fin N // I x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun (x14 : ℕ) => Decidable.decide (x14 < N)) (↑x13.1) (N + ↑x13.2) = Bool.true } = S.card := by
    rw [Fintype.card_subtype]
  rw [hS]
  have hS1 : S.card ≤ L'.card * (q + 1) := by
    have hsub : S ⊆ (Finset.univ ×ˢ L').filter (fun x => I x.1 x.2) := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have := (key x.1 x.2 hx.1 hx.2).2
      simp [L', this, hx.1]
    refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
    rw [Finset.card_filter, Finset.sum_product_right]
    rw [Finset.sum_congr rfl (fun l _ => (show (∑ p : Fin N, if I (p, l).1 (p, l).2 then 1 else 0) = q + 1 by
      rw [← Finset.card_filter, ← hL l, Fintype.card_subtype]))]
    rw [Finset.sum_const, smul_eq_mul]
  have hS2 : S.card ≤ P'.card * (q + 1) := by
    have hsub : S ⊆ (P' ×ˢ Finset.univ).filter (fun x => I x.1 x.2) := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have := (key x.1 x.2 hx.1 hx.2).1
      simp [P', this, hx.1]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_filter, Finset.sum_product]
    refine (Finset.sum_le_card_nsmul _ _ (q + 1) ?_).trans (le_of_eq (smul_eq_mul _ _))
    intro p _
    rw [← Finset.card_filter]
    exact PEqualNP.Outside.L_meta_3477.deg_le q N I hq hN hL hU p
  by_cases h : L'.card ≤ C.size
  · calc S.card ≤ L'.card * (q + 1) := hS1
      _ ≤ C.size * 10 := Nat.mul_le_mul h (by omega)
      _ = 10 * C.size := by ring
  · calc S.card ≤ P'.card * (q + 1) := hS2
      _ ≤ C.size * 10 := Nat.mul_le_mul (by omega) (by omega)
      _ = 10 * C.size := by ring
