import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Abel
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2341_417
    (flat : ∀ (C : Circuit) (r s : Fin 13) (c : Bool), Monotone2 C → ReadsBack 27 C →
      andPairs 27 C = 0 →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let X := fun (P L : Finset (Fin 13)) =>
        (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [c]
      (∀ p l : Fin 13, p - l ∈ D → p ≠ r ∨ l ≠ s → C.eval (X {p} {l}) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
        C.eval (X Q (Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D))) = false) →
      (∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
        C.eval (X {p,a} {l,b}) = false) → 63 ≤ C.size)
    (single : ∀ (C : Circuit) (r s : Fin 13) (c : Bool), Monotone2 C → ReadsBack 27 C →
      andPairs 27 C = 1 →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let X := fun (P L : Finset (Fin 13)) =>
        (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [c]
      (∀ p l : Fin 13, p - l ∈ D → p ≠ r ∨ l ≠ s → C.eval (X {p} {l}) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
        C.eval (X Q (Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D))) = false) →
      (∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
        C.eval (X {p,a} {l,b}) = false) → 63 ≤ C.size)
    (several : ∀ (C : Circuit) (r s : Fin 13) (c : Bool), Monotone2 C → ReadsBack 27 C →
      2 ≤ andPairs 27 C →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let X := fun (P L : Finset (Fin 13)) =>
        (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [c]
      (∀ p l : Fin 13, p - l ∈ D → p ≠ r ∨ l ≠ s → C.eval (X {p} {l}) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
        C.eval (X Q (Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D))) = false) →
      (∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
        C.eval (X {p,a} {l,b}) = false) → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C r s c mono backward diff oldPositive oldNegative oldGood positives negatives
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let X (P L : Finset (Fin 13)) : List Bool :=
    (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [c]
  let Good (Q : Finset (Fin 13)) := Q.card = 4 ∧
    ∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2
  let disjointLines (Q : Finset (Fin 13)) : Finset (Fin 13) :=
    Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D)
  have back : ReadsBack 27 C := by
    intro j hj w hw
    change w ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at hw
    exact backward ⟨j,hj⟩ w hw
  have yes : ∀ p l : Fin 13, p - l ∈ D → p ≠ r ∨ l ≠ s → C.eval (X {p} {l}) = true := by
    intro p l inc required
    simpa only [X, Finset.mem_singleton] using positives p l inc required
  have no : ∀ Q, Good Q → C.eval (X Q (disjointLines Q)) = false := by
    intro Q good
    simpa only [X, disjointLines, Finset.mem_filter, Finset.mem_univ, true_and] using negatives Q good
  -- With the first point translated to zero, store the point and line masks of the quadrangles.
  let masks : List (List (ℕ × ℕ)) := [
    [(29, 2592), (39, 392), (71, 896), (77, 2816), (83, 644), (85, 2688), (101, 2432), (105, 2306), (135, 776), (141, 800), (195, 772), (201, 770), (275, 580), (281, 2624), (297, 2114), (329, 2562), (337, 2564), (387, 524), (449, 518), (533, 2208), (549, 2184), (593, 2180), (609, 2178), (801, 2058), (833, 2054), (897, 14), (1037, 2336), (1049, 2144), (1059, 328), (1061, 2312), (1065, 2368), (1155, 268), (1157, 296), (1283, 76), (1297, 2116), (1313, 2120), (1541, 2088), (1553, 2084), (1665, 44), (1793, 2060), (2055, 648), (2067, 704), (2069, 672), (2073, 608), (2083, 200), (2181, 552), (2185, 546), (2307, 584), (2313, 578), (2337, 74), (2433, 522), (2565, 168), (2593, 138), (2689, 42), (4115, 196), (4131, 448), (4137, 322), (4163, 388), (4193, 386), (4233, 290), (4289, 262), (4625, 164), (4673, 134), (4737, 38), (5123, 324), (5129, 352), (5137, 100), (5249, 292), (6153, 98), (6161, 224), (6177, 194), (6657, 162)],
    [(39, 392), (71, 896), (83, 644), (135, 776), (195, 772), (275, 580), (387, 524), (1059, 328), (1155, 268), (1283, 76), (2055, 648), (2067, 704), (2083, 200), (2307, 584), (4115, 196), (4131, 448), (4163, 388), (5123, 324)],
    [(29, 2592), (39, 392), (71, 896), (77, 2816), (85, 2688), (101, 2432), (135, 776), (141, 800), (533, 2208), (549, 2184), (1037, 2336), (1061, 2312), (1157, 296), (1541, 2088), (2055, 648), (2069, 672), (2181, 552), (2565, 168)],
    [(29, 2592), (77, 2816), (105, 2306), (141, 800), (201, 770), (281, 2624), (297, 2114), (329, 2562), (1037, 2336), (1049, 2144), (1065, 2368), (2073, 608), (2185, 546), (2313, 578), (4137, 322), (4233, 290), (5129, 352), (6153, 98)],
    [(29, 2592), (83, 644), (85, 2688), (275, 580), (281, 2624), (337, 2564), (533, 2208), (593, 2180), (1049, 2144), (1297, 2116), (1553, 2084), (2067, 704), (2069, 672), (2073, 608), (4115, 196), (4625, 164), (5137, 100), (6161, 224)],
    [(39, 392), (101, 2432), (105, 2306), (297, 2114), (549, 2184), (609, 2178), (801, 2058), (1059, 328), (1061, 2312), (1065, 2368), (1313, 2120), (2083, 200), (2337, 74), (2593, 138), (4131, 448), (4137, 322), (4193, 386), (6177, 194)],
    [(71, 896), (77, 2816), (83, 644), (85, 2688), (101, 2432), (105, 2306), (195, 772), (201, 770), (329, 2562), (337, 2564), (449, 518), (593, 2180), (609, 2178), (833, 2054), (4163, 388), (4193, 386), (4289, 262), (4673, 134)],
    [(135, 776), (141, 800), (195, 772), (201, 770), (387, 524), (449, 518), (897, 14), (1155, 268), (1157, 296), (1665, 44), (2181, 552), (2185, 546), (2433, 522), (2689, 42), (4233, 290), (4289, 262), (4737, 38), (5249, 292)],
    [(275, 580), (281, 2624), (297, 2114), (329, 2562), (337, 2564), (387, 524), (449, 518), (801, 2058), (833, 2054), (897, 14), (1283, 76), (1297, 2116), (1313, 2120), (1793, 2060), (2307, 584), (2313, 578), (2337, 74), (2433, 522)],
    [(533, 2208), (549, 2184), (593, 2180), (609, 2178), (801, 2058), (833, 2054), (897, 14), (1541, 2088), (1553, 2084), (1665, 44), (1793, 2060), (2565, 168), (2593, 138), (2689, 42), (4625, 164), (4673, 134), (4737, 38), (6657, 162)],
    [(1037, 2336), (1049, 2144), (1059, 328), (1061, 2312), (1065, 2368), (1155, 268), (1157, 296), (1283, 76), (1297, 2116), (1313, 2120), (1541, 2088), (1553, 2084), (1665, 44), (1793, 2060), (5123, 324), (5129, 352), (5137, 100), (5249, 292)],
    [(2055, 648), (2067, 704), (2069, 672), (2073, 608), (2083, 200), (2181, 552), (2185, 546), (2307, 584), (2313, 578), (2337, 74), (2433, 522), (2565, 168), (2593, 138), (2689, 42), (6153, 98), (6161, 224), (6177, 194), (6657, 162)],
    [(4115, 196), (4131, 448), (4137, 322), (4163, 388), (4193, 386), (4233, 290), (4289, 262), (4625, 164), (4673, 134), (4737, 38), (5123, 324), (5129, 352), (5137, 100), (5249, 292), (6153, 98), (6161, 224), (6177, 194), (6657, 162)]]
  let pick (a l b : Fin 13) : Finset (Fin 13) :=
    let pair := ((masks.getD a.val []).find? (fun pr => pr.2.testBit l.val && pr.2.testBit b.val)).getD (0,0)
    Finset.univ.filter (fun x => pair.1.testBit x.val)
  have normalized : ∀ (a l b : Fin 13), 0 - l ∉ D → 0 - b ∉ D → a - l ∉ D → a - b ∉ D →
      Good (pick a l b) ∧ 0 ∈ pick a l b ∧ a ∈ pick a l b ∧
      l ∈ disjointLines (pick a l b) ∧ b ∈ disjointLines (pick a l b) := by decide +kernel
  have cover (p a l b : Fin 13) (pl : p - l ∉ D) (pb : p - b ∉ D)
      (al : a - l ∉ D) (ab : a - b ∉ D) :
      ∃ Q, Good Q ∧ p ∈ Q ∧ a ∈ Q ∧ l ∈ disjointLines Q ∧ b ∈ disjointLines Q := by
    let Q := pick (a-p) (l-p) (b-p)
    have origin (v : Fin 13) : 0 - (v-p) = p-v := by abel
    have difference (u v : Fin 13) : (u-p) - (v-p) = u-v := by abel
    obtain ⟨good, p₀, a₀, l₀, b₀⟩ := normalized (a-p) (l-p) (b-p)
      (by rwa [origin]) (by rwa [origin]) (by rwa [difference]) (by rwa [difference])
    let shift : Fin 13 ↪ Fin 13 := ⟨fun z => z+p, fun _ _ h => add_right_cancel h⟩
    have diff (u v : Fin 13) : shift u - v = u - (v-p) := by change (u+p)-v = _; abel
    have line (v : Fin 13) (avoid : v-p ∈ disjointLines Q) : v ∈ disjointLines (Q.map shift) := by
      have dis : ∀ q ∈ Q, q-(v-p) ∉ D := (Finset.mem_filter.mp avoid).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro q hq
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hq
      rw [diff]
      exact dis u hu
    have shiftedGood : Good (Q.map shift) := by
      refine ⟨by rw [Finset.card_map]; exact good.1, ?_⟩
      intro v
      rw [Finset.filter_map, Finset.card_map]
      simpa only [Function.comp_apply, diff] using good.2 (v-p)
    refine ⟨Q.map shift, shiftedGood, ?_, ?_, line l l₀, line b b₀⟩
    · exact Finset.mem_map.mpr ⟨0,p₀,by change 0+p = p; simp⟩
    · exact Finset.mem_map.mpr ⟨a-p,a₀,by change (a-p)+p = a; exact sub_add_cancel _ _⟩
  let R (v w : Bool) : Prop := v = true → w = true
  have read {xs ys : List Bool} (h : List.Forall₂ R xs ys) (i : ℕ) :
      R (xs.getD i false) (ys.getD i false) := by
    induction h generalizing i with
    | nil => exact id
    | cons ha ht ih => cases i with | zero => exact ha | succ i => exact ih i
  have liftEval (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ x y : List Bool, List.Forall₂ R x y →
        List.Forall₂ R ((Circuit.mk gs 0).wires x) ((Circuit.mk gs 0).wires y) := by
    induction gs with
    | nil => intro x y rel; exact rel
    | cons g gs ih =>
      intro x y rel
      apply ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
      apply List.rel_append rel
      apply List.Forall₂.cons _ List.Forall₂.nil
      intro hv
      rcases ops g (by simp) with hg | hg
      · rw [hg] at hv ⊢
        change ((g.inputs.map fun i => x.getD i false).all id) = true at hv
        change ((g.inputs.map fun i => y.getD i false).all id) = true
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv ⊢
        exact fun i hi => read rel i (hv i hi)
      · rw [hg] at hv ⊢
        change ((g.inputs.map fun i => x.getD i false).any id) = true at hv
        change ((g.inputs.map fun i => y.getD i false).any id) = true
        simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv ⊢
        obtain ⟨i, hi, hv⟩ := hv
        exact ⟨i, hi, read rel i hv⟩
  have ofFnRel (x y : Fin 13 → Bool) (h : ∀ i, R (x i) (y i)) :
      List.Forall₂ R (List.ofFn x) (List.ofFn y) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have lt : i < 13 := by simpa using hi
    simpa only [List.get_eq_getElem, List.getElem_ofFn] using h ⟨i,lt⟩
  have avoidRectangle : ∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
      C.eval (X {p,a} {l,b}) = false := by
    intro p a l b pl pb al ab
    obtain ⟨Q, good, qp, qa, ql, qb⟩ := cover p a l b pl pb al ab
    have rel (S T : Finset (Fin 13)) (sub : S ⊆ T) :
        List.Forall₂ R (List.ofFn (fun i => decide (i ∈ S))) (List.ofFn (fun i => decide (i ∈ T))) :=
      ofFnRel _ _ (fun i h => decide_eq_true (sub (of_decide_eq_true h)))
    have Psub : ({p,a} : Finset (Fin 13)) ⊆ Q := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact qp
      · exact qa
    have Lsub : ({l,b} : Finset (Fin 13)) ⊆ disjointLines Q := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact ql
      · exact qb
    have start : List.Forall₂ R (X {p,a} {l,b}) (X Q (disjointLines Q)) :=
      List.rel_append (List.rel_append (rel _ _ Psub) (rel _ _ Lsub)) (.cons id .nil)
    have operations : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1
    have hm : R (C.eval (X {p,a} {l,b})) (C.eval (X Q (disjointLines Q))) :=
      read (liftEval C.gates operations _ _ start) C.output
    have hn := no Q good
    cases hv : C.eval (X {p,a} {l,b}) with
    | false => rfl
    | true => exact (Bool.noConfusion (hn.symm.trans (hm hv)))
  have reject : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
        C.eval (X Q (disjointLines Q)) = false := fun Q hc hl => no Q ⟨hc,hl⟩
  by_cases h₀ : andPairs 27 C = 0
  · exact flat C r s c mono back h₀ yes reject avoidRectangle
  by_cases h₁ : andPairs 27 C = 1
  · exact single C r s c mono back h₁ yes reject avoidRectangle
  exact several C r s c mono back (by omega) yes reject avoidRectangle
