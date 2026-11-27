import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4687

-- The backward support count follows the argument in L_meta_1942.
private def supportRun (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

private lemma supportRun_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    supportRun (gs ++ [g]) x = supportRun gs x ++
      [g.op.eval (g.inputs.map fun i => (supportRun gs x).getD i false)] := by
  simp [supportRun, Circuit.wires, List.foldl_append]

private lemma supportRun_length (gs : List Gate) (x : List Bool) :
    (supportRun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [supportRun, Circuit.wires]
  | append_singleton gs g ih => simp [supportRun_snoc, ih, Nat.add_assoc]

private lemma gateSupports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (supportRun gs x).getD i false = (supportRun gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (supportRun gs x).length = j := by simp [supportRun_length, hx, j]
    have ey : (supportRun gs y).length = j := by simp [supportRun_length, hy, j]
    rw [supportRun_snoc, supportRun_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma outputSupport {n : ℕ} (C : Circuit) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → circuitFun n C x = circuitFun n C y := by
  obtain ⟨S, hcard, hs⟩ := gateSupports n C.gates fan {C.output}
  let T := S.preimage (Fin.val : Fin n → ℕ) Fin.val_injective.injOn
  have bound : T.card ≤ S.card :=
    Finset.card_le_card_of_injOn Fin.val (fun _ h => Finset.mem_preimage.mp h) Fin.val_injective.injOn
  refine ⟨T, bound.trans (by simpa [Circuit.size, Nat.add_comm] using hcard), ?_⟩
  intro x y hxy
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro i hi
  by_cases hn : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ (by simpa using hn)]
    simpa only [List.getElem_ofFn] using hxy ⟨i, hn⟩ (Finset.mem_preimage.mpr hi)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

open Finset

-- The off-diagonal injection adapts the degree-square argument of L-meta-904.
private theorem incidenceSquare {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) := by
  classical
  let neighbors (l : Fin N) := P.filter fun p => (p, l) ∈ E
  have count : E.card = ∑ l ∈ L, (neighbors l).card := by
    rw [← Finset.card_sigma]
    apply Finset.card_nbij' (fun e => ⟨e.2, e.1⟩) (fun e => (e.2, e.1))
    · intro e he
      exact mem_sigma.mpr ⟨(ends e he).2, mem_filter.mpr ⟨(ends e he).1, he⟩⟩
    · exact fun e he => (mem_filter.mp (mem_sigma.mp he).2).2
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
  let triples := L.sigma fun l => (neighbors l).offDiag
  have pairs_le : triples.card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp (mem_sigma.mp ht).2
      exact mem_offDiag.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp hb).1, hab⟩
    · intro ⟨u, a, b⟩ hu ⟨v, c, d⟩ hv heq
      change (a, b) = (c, d) at heq
      cases heq
      obtain ⟨hau, hbu, hab⟩ := mem_offDiag.mp (mem_sigma.mp hu).2
      obtain ⟨hav, hbv, _⟩ := mem_offDiag.mp (mem_sigma.mp hv).2
      cases unique a b u v hab (mem_filter.mp hau).2 (mem_filter.mp hbu).2
        (mem_filter.mp hav).2 (mem_filter.mp hbv).2
      rfl
  have squares : (∑ l ∈ L, (neighbors l).card ^ 2) = triples.card + E.card := by
    rw [count]
    simp only [triples, card_sigma, offDiag_card, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by rw [Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => 1 : Fin N → ℕ)
    (fun l => (neighbors l).card)
  simp only [one_mul, one_pow, sum_const, Nat.nsmul_eq_mul, mul_one, ← count, squares] at cauchy
  rw [pow_two] at cauchy
  rw [offDiag_card, ← Nat.mul_sub_one] at pairs_le
  exact cauchy.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right pairs_le _))

private theorem incidenceBounds {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card ≤ P.card * L.card ∧
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) ∧
    E.card * E.card ≤ P.card * (L.card * (L.card - 1) + E.card) := by
  refine ⟨?_, incidenceSquare E P L ends unique, ?_⟩
  · rw [← card_product]
    exact card_le_card fun e he => mem_product.mpr (ends e he)
  · let rev := E.map (Equiv.prodComm _ _).toEmbedding
    have mem_rev (a b : Fin N) : (a, b) ∈ rev ↔ (b, a) ∈ E := mem_map_equiv
    have swapEnds : ∀ e ∈ rev, e.1 ∈ L ∧ e.2 ∈ P := by
      rintro ⟨a, b⟩ he
      exact (ends _ ((mem_rev a b).mp he)).symm
    have swapUnique (a b u v : Fin N) (hab : a ≠ b) (hau : (a, u) ∈ rev)
        (hbu : (b, u) ∈ rev) (hav : (a, v) ∈ rev) (hbv : (b, v) ∈ rev) : u = v := by
      by_contra hne
      exact hab (unique u v a b hne ((mem_rev _ _).mp hau) ((mem_rev _ _).mp hav)
        ((mem_rev _ _).mp hbu) ((mem_rev _ _).mp hbv))
    simpa only [rev, card_map] using incidenceSquare rev L P swapEnds swapUnique

private lemma sides_distinct {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have e := congrArg Fin.val h
  change p.val = N + l.val at e
  omega

end PEqualNP.Outside.L_meta_4687

open PEqualNP.Outside.L_meta_4687

theorem PEqualNP.Outside.L_meta_4687 :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 1 ≤ q →
      (∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) →
      let accepted : Circuit → Finset (Fin N × Fin N) := fun C => {e : Fin N × Fin N | I e.1 e.2 ∧
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true}
      let sound := fun C : Circuit => ∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false
      ∀ C : Circuit, (∀ g ∈ C.gates, g.inputs.length ≤ 2) → sound C → C.size ≤ 4512 →
        let e := (accepted C).card
        ∃ a b : ℕ, a + b ≤ C.size + 1 ∧ e ≤ a * b ∧
          e * e ≤ b * (a * (a - 1) + e) ∧ e * e ≤ a * (b * (b - 1) + e) := by
  intro q N I _ hq unique accepted sound C fan safe _ e
  obtain ⟨S, hsize, stable⟩ := outputSupport (n := N + N) C fan
  have single (w : Fin (N + N)) :
      circuitFun (N + N) C (fun i => decide (i = w)) = false := by
    apply safe
    · refine le_trans (Fintype.card_le_one_iff.mpr ?_) hq
      intro a b
      exact Subtype.ext (Fin.natAdd_injective N N ((of_decide_eq_true a.2).trans (of_decide_eq_true b.2).symm))
    · rintro ⟨p, l, _, hp, hl⟩
      exact sides_distinct p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have needed (u v : Fin (N + N))
      (h : circuitFun (N + N) C (fun i => decide (i = u ∨ i = v)) = true) : u ∈ S := by
    by_contra hu
    have eq := stable (fun i => decide (i = u ∨ i = v)) (fun i => decide (i = v))
      (fun i hi => by simp [show i ≠ u from fun he => hu (he ▸ hi)])
    rw [h, single] at eq
    contradiction
  let E := accepted C
  let sides : Finset (Fin N ⊕ Fin N) := S.map finSumFinEquiv.symm.toEmbedding
  have ends (t : Fin N × Fin N) (ht : t ∈ E) : t.1 ∈ sides.toLeft ∧ t.2 ∈ sides.toRight := by
    have on := (Finset.mem_filter.mp ht).2.2
    simp only [sides, Finset.mem_toLeft, Finset.mem_toRight, Finset.mem_map_equiv,
      Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    exact ⟨needed _ _ on, needed (Fin.natAdd N t.2) (Fin.castAdd N t.1) (by simpa only [or_comm] using on)⟩
  refine ⟨sides.toLeft.card, sides.toRight.card, ?_, incidenceBounds E _ _ ends ?_⟩
  · simpa only [Finset.card_toLeft_add_card_toRight, sides, Finset.card_map] using hsize
  · intro a b u v hne hau hbu hav hbv
    have inc {p l : Fin N} (h : (p, l) ∈ E) : I p l := (Finset.mem_filter.mp h).2.1
    exact (unique a b hne).unique ⟨inc hau, inc hbu⟩ ⟨inc hav, inc hbv⟩
