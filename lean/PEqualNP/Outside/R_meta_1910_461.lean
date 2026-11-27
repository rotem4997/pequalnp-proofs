import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1910_461
    (small : have f : (Fin 9 → Bool) → Bool := fun x => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)); ¬ HasCircuitSize 9 f 14)
    (andOr : ∀ D : Circuit, Monotone2 D → D.size ≤ 14 →
      (∀ v ∈ ([4,6] : List ℕ), ∃! j : Fin D.gates.length, v ∈ (D.gates.get j).inputs) →
      (∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ) ++ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ),
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        D.eval (List.ofFn x ++ [x 4 || x 6]) = decide (r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ))) → False)
    (withNot : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      (∃ g ∈ D.gates, g.op = GateOp.not) →
      (∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) ≠ D.eval (List.ofFn x ++ [true])) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro C fan first computes readers
  by_contra! short
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have impossible := first (fun _ => true)
    change false = true at impossible
    contradiction
  | cons g gs =>
    let D : Circuit := ⟨gs,out⟩
    let F : (Fin 9 → Bool) → Bool := fun x => ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fd : FanInTwo D := fun q hq => fan q (List.mem_cons_of_mem _ hq)
    have hsize : D.size ≤ 14 := by
      change (g :: gs).length < 16 at short
      simp only [List.length_cons] at short
      change gs.length ≤ 14
      omega
    have keep (t : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
        (t.foldl step w).getD j false = w.getD j false := by
      induction t generalizing w with
      | nil => rfl
      | cons q t ih =>
        rw [List.foldl_cons, ih (step w q) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hj
    have run (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = F x := by
      let v := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      have h := first x
      change (gs.foldl step (List.ofFn x ++ [v])).getD 9 false = _ at h
      rw [keep _ _ _ (by simp)] at h
      have hv : v = (x 4 || x 6) := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using h
      have target := congrFun computes x
      change D.eval (List.ofFn x ++ [v]) = F x at target
      simpa only [hv] using target
    by_cases hnot : ∃ g ∈ D.gates, g.op = GateOp.not
    · by_cases relevant : ∃ x : Fin 9 → Bool,
          D.eval (List.ofFn x ++ [false]) ≠ D.eval (List.ofFn x ++ [true])
      · exact withNot D fd hsize hnot relevant run
      · push Not at relevant
        let wire (i : ℕ) := if i < 9 then i else if i = 9 then 9 + gs.length else i - 1
        let rename (q : Gate) : Gate := ⟨q.op, q.inputs.map wire⟩
        let E : Circuit := ⟨gs.map rename, wire out⟩
        have fanE : FanInTwo E := by
          intro q hq
          change q ∈ gs.map rename at hq
          obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
          simpa [rename] using fd a ha
        have ev (x : Fin 9 → Bool) : E.eval (List.ofFn x) = F x := by
          let xs := List.ofFn x
          have hx : xs.length = 9 := List.length_ofFn
          have read (l : List Bool) (hl : l.length ≤ gs.length) (i : ℕ) :
              (xs ++ false :: l).getD i false = (xs ++ l).getD (wire i) false := by
            by_cases before : i < 9
            · simp only [wire, ite_eq_left before]
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            · rw [List.getD_append_right _ _ _ _ (by omega)]
              by_cases equal : i = 9
              · subst i
                simp only [wire, Nat.lt_irrefl, ↓reduceIte]
                rw [hx, Nat.sub_self]
                change false = (xs ++ l).getD (9 + gs.length) false
                rw [List.getD_eq_default _ _ (by simp [hx]; omega)]
              · have after : 9 < i := by omega
                simp only [wire, ite_eq_right before, ite_eq_right equal]
                rw [List.getD_append_right _ _ _ _ (by omega), hx]
                have index : i - 9 = (i - 1 - 9) + 1 := by omega
                rw [index]
                simp [List.getD_eq_getElem?_getD]
          have commute (t : List Gate) (l : List Bool) (len : l.length + t.length ≤ gs.length) :
              (t.foldl step (xs ++ false :: l)).getD out false =
                ((t.map rename).foldl step (xs ++ l)).getD (wire out) false := by
            induction t generalizing l with
            | nil => exact read l (by simp at len; omega) out
            | cons q t ih =>
              have hl : l.length ≤ gs.length := by omega
              have ops : q.op.eval (q.inputs.map fun i => (xs ++ false :: l).getD i false) =
                  q.op.eval ((rename q).inputs.map fun i => (xs ++ l).getD i false) := by
                congr 1
                simp only [rename, List.map_map]
                exact List.map_congr_left (fun i _ => read l hl i)
              let b := q.op.eval ((rename q).inputs.map fun i => (xs ++ l).getD i false)
              simp only [List.foldl_cons, List.map_cons, step, ops]
              change (t.foldl step ((xs ++ false :: l) ++ [b])).getD out false =
                ((t.map rename).foldl step ((xs ++ l) ++ [b])).getD (wire out) false
              simp only [List.append_assoc, List.cons_append]
              apply ih
              simp only [List.length_append, List.length_cons, List.length_nil] at len ⊢
              omega
          have replay : D.eval (xs ++ [false]) = E.eval xs := by
            change (gs.foldl step (xs ++ [false])).getD out false =
              ((gs.map rename).foldl step xs).getD (wire out) false
            simpa only [List.append_nil] using commute gs [] (by simp)
          rw [← replay]
          cases h : x 4 || x 6
          · simpa only [h] using run x
          · rw [relevant x]
            simpa only [h] using run x
        apply small
        refine ⟨E, fanE, ?_, ?_⟩
        · change (gs.map rename).length ≤ 14
          rw [List.length_map]
          exact hsize
        · intro x
          rw [ev]
          have eq : F = (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by decide +kernel
          exact congrFun eq x
    · have mono : Monotone2 D := by
        intro q hq
        obtain ⟨hop,hinputs⟩ := fd q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
        exact ⟨hop.elim Or.inl (fun h => Or.inr (h.resolve_right (fun e => hnot ⟨q,hq,e⟩))),hinputs⟩
      apply andOr D mono hsize
      · intro v hv
        have hd (j : Fin gs.length) : (gs.get j).op ≠ GateOp.not :=
          fun h => hnot ⟨gs.get j, List.get_mem gs j, h⟩
        obtain ⟨j,hj,unique⟩ := readers v hv
        refine ⟨j, ?_, ?_⟩
        · exact hj.elim (fun h => List.mem_of_getElem? h) And.right
        · exact fun k hk => unique k (Or.inr ⟨hd k,hk⟩)
      · intro r hr
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        change D.eval (List.ofFn x ++ [x 4 || x 6]) = _
        rw [run]
        have table : ∀ s ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ) ++ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ),
            F (fun i => s.testBit i.val) = decide (s ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ)) := by
          intro s hs
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with hs | hs
          · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact table r hr
