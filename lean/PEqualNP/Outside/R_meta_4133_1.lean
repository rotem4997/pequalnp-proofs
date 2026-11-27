import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Erase the OR gates below the graph function and pay for the output OR
-- separately. The remaining gates need only supply a top for each edge.
-- Every exceptional mask contains five fixed edges and omits the first six.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4133_1
    (compress : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      let bill := fun D : Circuit => 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
      ∃ D : Circuit, IsAO2 n D ∧ TopForm G D ∧ (orT G D).card = 0 ∧
        D.size + (tops G D).card ≤ C.size + 1 ∧ Ustar G D = Ustar G C ∧
        (junk G D).card = (junk G C).card ∧ bill D = bill C ∧
        (∀ j < D.size, ∃ a ∈ tops G D, j = a ∨ InCone n D j a) ∧
        (∀ u v, G.Adj u v → ∃ a ∈ tops G D, gateVal n D a (pairInput u v) = true))
    (exclude :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ D : Circuit, IsAO2 11 D → TopForm G D → (orT G D).card = 0 →
        D.size + (tops G D).card ≤ 22 →
        (∀ j < D.size, ∃ a ∈ tops G D, j = a ∨ InCone 11 D j a) →
        (∀ u v, G.Adj u v → ∃ a ∈ tops G D, gateVal 11 D a (pairInput u v) = true) →
        2 ≤ (junk G D).card →
        let U := Ustar G D
        let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
        U.card ≤ B → B < 2 * U.card →
        (∀ u v : Fin 11, G.Adj u v → u.val < 3 ∨ v.val < 3 → s(u,v) ∉ U) →
        ({s(4,8),s(4,10),s(5,8),s(5,9),s(8,9)} : Finset (Sym2 (Fin 11))) ⊆ U →
        False) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; have x3 : Finset (Sym2 (Fin (11 : ℕ))) → BitVec (16 : ℕ) := fun (x3 : Finset (Sym2 (Fin (11 : ℕ)))) =>   BitVec.ofNat (16 : ℕ)     (PEqualNP.MetaComplexity.tableIndex fun (x4 : Fin (16 : ℕ)) =>       have x5 : ℕ × ℕ := x1.getD ↑x4 ((0 : ℕ), (0 : ℕ));       Decidable.decide (s(Fin.ofNat (11 : ℕ) x5.1, Fin.ofNat (11 : ℕ) x5.2) ∈ x3)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x4 →       PEqualNP.TopForm.TopForm x2 x4 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →           have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;           have x10 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;           x9.card ≤ x10 → x10 < (2 : ℕ) * x9.card → x3 x9 ∉ [(36608 : BitVec (16 : ℕ)), (44800 : BitVec (16 : ℕ)), (44864 : BitVec (16 : ℕ)), (44992 : BitVec (16 : ℕ)), (48960 : BitVec (16 : ℕ)), (52992 : BitVec (16 : ℕ)), (53120 : BitVec (16 : ℕ)), (53184 : BitVec (16 : ℕ)), (57216 : BitVec (16 : ℕ)), (61184 : BitVec (16 : ℕ)), (61248 : BitVec (16 : ℕ)), (61312 : BitVec (16 : ℕ)), (61376 : BitVec (16 : ℕ)), (65280 : BitVec (16 : ℕ)), (65344 : BitVec (16 : ℕ)), (65408 : BitVec (16 : ℕ)), (65472 : BitVec (16 : ℕ))] := by
  dsimp only
  intro C short least top junkCount low high rare
  let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let G := edgeGraph 11 es
  let U := Ustar G C
  let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  let masks : List (BitVec 16) := [36608,44800,44864,44992,48960,52992,53120,53184,57216,61184,61248,61312,61376,65280,65344,65408,65472]
  let edge (i : Fin 16) : Sym2 (Fin 11) :=
    let e := es.getD i.val (0,0)
    s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2)
  let code := BitVec.ofNat 16 (tableIndex fun i : Fin 16 => decide (edge i ∈ U))
  change code ∈ masks at rare
  have tableBit : ∀ (n : ℕ) (f : Fin n → Bool) (i : Fin n),
      (tableIndex f).testBit i.val = f i := by
    intro n
    induction n with
    | zero => intros f i; exact Fin.elim0 i
    | succ n ih =>
      intro f i
      have split : tableIndex f = 2 * tableIndex (fun j : Fin n => f j.succ) + (f 0).toNat := by
        unfold tableIndex
        rw [Fin.sum_univ_succ, Finset.mul_sum, Nat.add_comm]
        simp only [Fin.val_zero, pow_zero]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          split <;> simp [Fin.val_succ, pow_succ']
        · cases f 0 <;> simp
      rw [split]
      have small : (f 0).toNat < 2 ^ 1 := by cases f 0 <;> decide
      change ((2 ^ 1) * tableIndex (fun j : Fin n => f j.succ) + (f 0).toNat).testBit i.val = f i
      rw [Nat.testBit_two_pow_mul_add _ small]
      refine Fin.cases ?_ (fun j => ?_) i
      · cases f 0 <;> simp
      · simpa using ih (fun j : Fin n => f j.succ) j
  have read (i : Fin 16) : code.getLsbD i.val = decide (edge i ∈ U) := by
    simp only [code, BitVec.getLsbD_ofNat, i.isLt, decide_true, Bool.true_and]
    exact tableBit 16 _ i
  have maskByIndex : ∀ (j : Fin 17) (i : Fin 16),
      let k := masks.get (Fin.cast (show 17 = masks.length from rfl) j)
      (i.val < 6 → k.getLsbD i.val = false) ∧
      ((36608 : BitVec 16).getLsbD i.val = true → k.getLsbD i.val = true) := by
    dsimp [masks]
    decide +kernel
  have maskSpec (i : Fin 16) : (i.val < 6 → code.getLsbD i.val = false) ∧
      ((36608 : BitVec 16).getLsbD i.val = true → code.getLsbD i.val = true) := by
    obtain ⟨j, hj⟩ := List.get_of_mem rare
    have same : masks.get (Fin.cast (show 17 = masks.length from rfl) (Fin.cast (show masks.length = 17 from rfl) j)) = code := by simpa using hj
    simpa only [same] using maskByIndex (Fin.cast (show masks.length = 17 from rfl) j) i
  have starredSpec : ∀ u v : Fin 11, G.Adj u v → u.val < 3 ∨ v.val < 3 →
      ∃ i : Fin 16, i.val < 6 ∧ edge i = s(u,v) := by
    dsimp [G, edge, es]
    decide +kernel
  have unstarredSpec : ∀ e ∈ ({s(4,8),s(4,10),s(5,8),s(5,9),s(8,9)} : Finset (Sym2 (Fin 11))),
      ∃ i : Fin 16, (36608 : BitVec 16).getLsbD i.val = true ∧ edge i = e := by
    dsimp [edge, es]
    decide +kernel
  have starred (u v : Fin 11) (adj : G.Adj u v) (small : u.val < 3 ∨ v.val < 3) : s(u,v) ∉ U := by
    obtain ⟨i, first, same⟩ := starredSpec u v adj small
    have off := (maskSpec i).1 first
    rw [read i, same] at off
    exact of_decide_eq_false off
  have unstarred : ({s(4,8),s(4,10),s(5,8),s(5,9),s(8,9)} : Finset (Sym2 (Fin 11))) ⊆ U := by
    intro e he
    obtain ⟨i, bit, same⟩ := unstarredSpec e he
    have on := (maskSpec i).2 bit
    rw [read i, same] at on
    exact of_decide_eq_true on
  have nonempty : G.edgeFinset.Nonempty := by
    refine ⟨s((0 : Fin 11), (9 : Fin 11)), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    dsimp [G, es]
    decide +kernel
  obtain ⟨D, ao, topD, noOutputOR, budget, hU, hJ, hB, live, covers⟩ := compress 11 G C nonempty least top
  have size : D.size + (tops G D).card ≤ 22 := by omega
  let newBill := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
  change newBill = B at hB
  change _ = U at hU
  change U.card ≤ B at low
  change B < 2 * U.card at high
  exact exclude D ao topD noOutputOR size live covers (hJ ▸ junkCount)
    (show (Ustar G D).card ≤ newBill by rw [hU, hB]; exact low)
    (show newBill < 2 * (Ustar G D).card by rw [hU, hB]; exact high)
    (by rw [hU]; exact starred) (by rw [hU]; exact unstarred)
