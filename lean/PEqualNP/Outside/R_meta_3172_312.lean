import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_3172_312
    (small : ∀ (a b : Fin 9) (B : BinaryCircuit) (P : Finset ℕ) (q : Bool), ((a = 2 ∧ (b = 2 ∨ b = 3 ∨ b = 8)) ∨ (a = 3 ∧ b = 3)) → B.size ≤ 11 →
      (q = true → B.output ∈ P) →
      (∀ g ∈ B.gates, ∃ a b : Bool, (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
        (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))) →
      ¬ (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x a || x b, false]) != q) =
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))))
    (middle : ∀ (a b : Fin 9) (B : BinaryCircuit) (P : Finset ℕ) (q : Bool), ((a = 2 ∧ (b = 2 ∨ b = 3 ∨ b = 8)) ∨ (a = 3 ∧ b = 3)) → B.size = 12 → 0 ∈ P → 10 ∈ P → P.card ≤ 3 →
      (q = true → B.output ∈ P) →
      (∀ g ∈ B.gates, ∃ a b : Bool, (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
        (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))) →
      ¬ (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x a || x b, false]) != q) =
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))))
    (tight : ∀ (a b : Fin 9) (B : BinaryCircuit) (P : Finset ℕ) (q : Bool), ((a = 2 ∧ (b = 2 ∨ b = 3 ∨ b = 8)) ∨ (a = 3 ∧ b = 3)) → B.size = 13 → 0 ∈ P → 10 ∈ P → P.card ≤ 2 →
      (q = true → B.output ∈ P) →
      (∀ g ∈ B.gates, ∃ a b : Bool, (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
        (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))) →
      ¬ (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x a || x b, false]) != q) =
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins two _ pinSet C fan sizeC
  obtain ⟨i,j,rfl⟩ := List.length_eq_two.mp two
  have hi := pinSet i (by simp (config := {congrConsts := false}))
  have hj := pinSet j (by simp (config := {congrConsts := false}))
  let u : Fin 9 := ⟨i,by rcases hi with h | h | h <;> omega⟩
  let v : Fin 9 := ⟨j,by rcases hj with h | h | h <;> omega⟩
  let perm := fun swap (k : Fin 9) =>
    bif swap then ([0,5,8,3,4,1,7,6,2] : List (Fin 9)).getD k.val k else k
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have remap : ∀ p q : Fin 9, (p.val = 2 ∨ p.val = 3 ∨ p.val = 8) →
      (q.val = 2 ∨ q.val = 3 ∨ q.val = 8) → ∃ swap : Bool, ∃ a b : Fin 9,
      ((a = 2 ∧ (b = 2 ∨ b = 3 ∨ b = 8)) ∨ (a = 3 ∧ b = 3)) ∧
      ((perm swap p = a ∧ perm swap q = b) ∨ (perm swap p = b ∧ perm swap q = a)) := by
    decide +kernel
  obtain ⟨swap,a,b,canonical,anchors⟩ := remap u v hi hj
  have permZero : perm swap 0 = 0 := by cases swap <;> decide +kernel
  have sameTarget : ∀ (s : Bool) (x : Fin 9 → Bool), f (fun k => x (perm s k)) = f x := by
    intro s x
    cases s
    · rfl
    · change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || ((x 2 && x 1) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))
      simp (config := {congrConsts := false}) only [Bool.or_false,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm,Bool.and_comm]
  let lift := fun w : List Bool =>
    List.ofFn (fun k : Fin 9 => w.getD (perm swap k).val false) ++ [!(w.getD 0 false),w.getD 9 false]
  have liftLen (w : List Bool) (_ : w.length = 10) : (lift w).length = 11 := by simp (config := {congrConsts := false}) [lift]

  let form := fun g : Gate => g = ⟨.and, []⟩ ∨ (∃ a, g = ⟨.not, [a]⟩) ∨
    ∃ a b, g = ⟨.and, [a,b]⟩ ∨ g = ⟨.or, [a,b]⟩
  let notG := fun g : Gate => g.op.eval [false]
  let raw := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let bit := fun (w : List Bool) (g : BinaryGate) =>
    w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  let describe := fun (rs : List (ℕ × Bool)) (j : ℕ) => rs.getD j (10,false)
  let read := fun (w : List Bool) (t : ℕ × Bool) => w.getD t.1 false != t.2
  let allowed := fun (P : Finset ℕ) (g : BinaryGate) => ∃ a b : Bool,
    (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
    (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))
  let link := fun (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ) =>
    rs.length = 11 + old.length ∧ (0 ∈ P ∧ 10 ∈ P) ∧
    (∀ t ∈ rs, t.1 < 11 + bs.length ∧ (t.2 = true → t.1 ∈ P)) ∧
    (∀ g ∈ bs, allowed P g) ∧
    ∀ (w : List Bool), w.length = 10 → ∀ i,
      read (bs.foldl bit (w ++ [false])) (describe rs i) = (old.foldl raw (lift w)).getD i false
  have rLen (gs : List Gate) (w : List Bool) : (gs.foldl raw w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp (config := {congrConsts := false}) only [List.foldl_cons, ih, raw, List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega
  have bLen (gs : List BinaryGate) (w : List Bool) : (gs.foldl bit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp (config := {congrConsts := false}) only [List.foldl_cons, ih, bit, List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega
  have keep (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl bit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp (config := {congrConsts := false}) [bit]; omega)]
      exact List.getD_append _ _ _ _ hi
  have last {α : Type} (w : List α) (r d : α) : (w ++ [r]).getD w.length d = r := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
  have dummy (bs : List BinaryGate) (w : List Bool) (hw : w.length = 10) :
      (bs.foldl bit (w ++ [false])).getD 10 false = false := by
    rw [keep _ _ _ (by simp (config := {congrConsts := false}) [hw]), ← hw]
    exact last w false false
  have described (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ)
      (h : link old rs bs P) (i : ℕ) :
      (describe rs i).1 < 11 + bs.length ∧ ((describe rs i).2 = true → (describe rs i).1 ∈ P) := by
    dsimp only [describe]
    by_cases hi : i < rs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h.2.2.1 _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨by dsimp; omega, fun _ => h.2.1.2⟩
  have extend (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P T : Finset ℕ)
      (g : Gate) (tail : List BinaryGate) (q : ℕ × Bool) (h : link old rs bs P)
      (hPT : P ⊆ T) (hq : q.1 < 11 + (bs++tail).length) (hqP : q.2 = true → q.1 ∈ T)
      (hTail : ∀ g ∈ tail, allowed T g)
      (newEq : ∀ w : List Bool, w.length = 10 →
        read ((bs++tail).foldl bit (w++[false])) q =
          g.op.eval (g.inputs.map fun i => (old.foldl raw (lift w)).getD i false)) :
      link (old++[g]) (rs++[q]) (bs++tail) T := by
    refine ⟨by simp (config := {congrConsts := false}) [h.1]; omega, ⟨hPT h.2.1.1,hPT h.2.1.2⟩, ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with hi | hi
      · obtain ⟨h0,h1⟩ := h.2.2.1 t hi
        exact ⟨by simp (config := {congrConsts := false}); omega, fun hh => hPT (h1 hh)⟩
      · have htq : t = q := List.mem_singleton.mp hi
        subst t
        exact ⟨hq,hqP⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨a,b,ha,hb,hop⟩ := h.2.2.2.1 e he
        exact ⟨a,b,fun h => hPT (ha h),fun h => hPT (hb h),hop⟩
      · exact hTail e he
    · intro w hw i
      have hl : (old.foldl raw (lift w)).length = rs.length := by rw [rLen, liftLen _ hw, h.1]
      have rawLast : (old++[g]).foldl raw (lift w) = raw (old.foldl raw (lift w)) g := by
        simp (config := {congrConsts := false}) only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [rawLast]
      change read ((bs++tail).foldl bit (w++[false])) ((rs++[q]).getD i (10,false)) =
        ((old.foldl raw (lift w)) ++ [_]).getD i false
      by_cases hi : i < rs.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
        change read ((bs++tail).foldl bit (w++[false])) (describe rs i) = _
        have hv := (described old rs bs P h i).1
        change (((bs++tail).foldl bit (w++[false])).getD (describe rs i).1 false != (describe rs i).2) = _
        rw [List.foldl_append, keep _ _ _ (by rw [bLen]; simp (config := {congrConsts := false}) [hw]; omega)]
        exact h.2.2.2.2 w hw i
      · by_cases he : i = rs.length
        · rw [he, last, ← hl, last]
          exact newEq w hw
        · rw [List.getD_eq_default _ _ (by simp (config := {congrConsts := false}); omega), List.getD_eq_default _ _ (by simp (config := {congrConsts := false}) [hl]; omega)]
          change (((bs++tail).foldl bit (w++[false])).getD 10 false != false) = false
          rw [dummy _ _ hw]
          rfl
  have emit (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ)
      (h : link old rs bs P) (g : Gate) (hg : form g) : ∃ rs' bs' T,
      link (old++[g]) rs' bs' T ∧
      bs'.length ≤ bs.length + (if notG g then 0 else 1) ∧
      T.card ≤ P.card + (if notG g then 1 else 0) := by
    rcases hg with rfl | ⟨a,rfl⟩ | ⟨a,b,hop⟩
    · refine ⟨rs++[(10,true)],bs,P,?_,?_,?_⟩
      · have z := extend old rs bs P P ⟨.and,[]⟩ [] (10,true) h (fun _ h => h)
          (by simp (config := {congrConsts := false}); omega) (fun _ => h.2.1.2) (by simp (config := {congrConsts := false})) ?_
        · simpa (config := {congrConsts := false}) only [List.append_nil] using z
        · intro w hw
          change (((bs++[]).foldl bit (w++[false])).getD 10 false != true) = true
          rw [dummy _ _ hw]
          rfl
      · change bs.length ≤ bs.length + 1
        omega
      · change P.card ≤ P.card + 0
        omega
    · let q := describe rs a
      let T := insert q.1 P
      refine ⟨rs++[(q.1,!q.2)],bs,T,?_,?_,?_⟩
      · have z := extend old rs bs P T ⟨.not,[a]⟩ [] (q.1,!q.2) h
          (fun _ h => Finset.mem_insert_of_mem h) (by simp (config := {congrConsts := false}); exact (described old rs bs P h a).1)
          (fun _ => Finset.mem_insert_self _ _) (by simp (config := {congrConsts := false})) ?_
        · simpa (config := {congrConsts := false}) only [List.append_nil] using z
        · intro w hw
          have oldEq := h.2.2.2.2 w hw a
          rw [List.append_nil]
          change ((bs.foldl bit (w++[false])).getD q.1 false != (!q.2)) =
            !((old.foldl raw (lift w)).getD a false)
          rw [← oldEq]
          change ((bs.foldl bit (w++[false])).getD q.1 false != (!q.2)) =
            !((bs.foldl bit (w++[false])).getD q.1 false != q.2)
          cases (bs.foldl bit (w++[false])).getD q.1 false <;> cases q.2 <;> rfl
      · exact Nat.le_refl _
      · change (insert q.1 P).card ≤ P.card + 1
        exact Finset.card_insert_le _ _
    · have bin (isOr : Bool) : ∃ rs' bs' T,
          link (old++[⟨if isOr then .or else .and,[a,b]⟩]) rs' bs' T ∧
          bs'.length ≤ bs.length+1 ∧ T.card ≤ P.card := by
        let l := describe rs a
        let r := describe rs b
        let op := fun u v : Bool => if isOr then (u != l.2) || (v != r.2) else (u != l.2) && (v != r.2)
        let bp : BinaryGate := ⟨op,l.1,r.1⟩
        let out : ℕ × Bool := (11+bs.length,false)
        refine ⟨rs++[out],bs++[bp],P,?_,by simp (config := {congrConsts := false}),le_rfl⟩
        refine extend old rs bs P P _ [bp] out h (fun _ h => h) (by simp (config := {congrConsts := false}) [out]) (by simp (config := {congrConsts := false}) [out]) ?_ ?_
        · intro bg hbg
          obtain rfl := List.mem_singleton.mp hbg
          exact ⟨l.2,r.2,(described old rs bs P h a).2,(described old rs bs P h b).2,
            by cases isOr <;> first | exact Or.inl rfl | exact Or.inr rfl⟩
        · intro w hw
          let W := bs.foldl bit (w++[false])
          have hW : W.length = 11+bs.length := by dsimp [W]; rw [bLen]; simp (config := {congrConsts := false}) [hw]
          have ea := h.2.2.2.2 w hw a
          have eb := h.2.2.2.2 w hw b
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          change ((W ++ [op (W.getD l.1 false) (W.getD r.1 false)]).getD (11+bs.length) false != false) = _
          rw [← hW,last]
          change (op (W.getD l.1 false) (W.getD r.1 false) != false) =
            (if isOr then GateOp.or else GateOp.and).eval
              [(old.foldl raw (lift w)).getD a false,(old.foldl raw (lift w)).getD b false]
          rw [← ea,← eb]
          change (op (W.getD l.1 false) (W.getD r.1 false) != false) =
            (if isOr then GateOp.or else GateOp.and).eval [W.getD l.1 false != l.2,W.getD r.1 false != r.2]
          dsimp only [op]
          cases isOr <;> cases (W.getD l.1 false != l.2) <;> cases (W.getD r.1 false != r.2) <;> rfl
      rcases hop with rfl | rfl
      · exact bin false
      · exact bin true
  have compile (gs : List Gate) (hg : ∀ g ∈ gs, form g) :
      ∀ (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ),
        link old rs bs P → ∃ rs' bs' T, link (old++gs) rs' bs' T ∧
          bs'.length + gs.countP notG ≤ bs.length + gs.length ∧ T.card ≤ P.card + gs.countP notG := by
    induction gs with
    | nil =>
      intro old rs bs P h
      exact ⟨rs,bs,P,by simpa (config := {congrConsts := false}) only [List.append_nil] using h,by simp (config := {congrConsts := false}),by simp (config := {congrConsts := false})⟩
    | cons g gs ih =>
      intro old rs bs P h
      obtain ⟨mid,bm,M,hm,hbm,hM⟩ := emit old rs bs P h g (hg g (List.mem_cons_self))
      obtain ⟨rs',bs',T,h',hb,hT⟩ := ih (fun e he => hg e (List.mem_cons_of_mem _ he))
        (old++[g]) mid bm M hm
      refine ⟨rs',bs',T,by simpa (config := {congrConsts := false}) only [List.append_assoc,List.singleton_append] using h',?_,?_⟩
      · rw [List.countP_cons, List.length_cons]
        cases hg' : notG g <;> simp (config := {congrConsts := false}) only [hg',Bool.false_eq_true,ite_false,ite_true, ↓reduceIte] at hbm ⊢ <;> omega
      · rw [List.countP_cons]
        cases hg' : notG g <;> simp (config := {congrConsts := false}) only [hg',Bool.false_eq_true,ite_false,ite_true, ↓reduceIte] at hM ⊢ <;> omega

  let start : List (ℕ × Bool) :=
    List.ofFn (fun k : Fin 9 => ((perm swap k).val,false)) ++ [(0,true),(9,false)]
  have hStart : link [] start [] {0,10} := by
    refine ⟨by simp (config := {congrConsts := false}) [start],by simp (config := {congrConsts := false}),?_,by simp (config := {congrConsts := false}),?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨k,hk⟩ := List.mem_ofFn.mp ht
        rw [← hk]
        exact ⟨by have := (perm swap k).isLt; dsimp; omega, by simp (config := {congrConsts := false})⟩
      · simp (config := {congrConsts := false}) only [List.mem_cons,List.mem_nil_iff,or_false] at ht
        rcases ht with rfl | rfl <;> simp (config := {congrConsts := false})
    · intro w hw k
      change read (w ++ [false]) (start.getD k (10,false)) = (lift w).getD k false
      by_cases hk : k < 9
      · let t : Fin 9 := ⟨k,hk⟩
        have ha : start.getD k (10,false) = ((perm swap t).val,false) := by
          unfold start
          rw [List.getD_append _ _ _ _ (by simp (config := {congrConsts := false}) [hk])]
          rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hk]),List.getElem_ofFn]
        have hb : (lift w).getD k false = w.getD (perm swap t).val false := by
          unfold lift
          rw [List.getD_append _ _ _ _ (by simp (config := {congrConsts := false}) [hk])]
          rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hk]),List.getElem_ofFn]
        have h : (perm swap t).val < w.length := by have := (perm swap t).isLt; omega
        rw [ha,hb]
        change ((w++[false]).getD (perm swap t).val false != false) = w.getD (perm swap t).val false
        rw [List.getD_append _ _ _ _ h]
        cases w.getD (perm swap t).val false <;> rfl
      · by_cases k9 : k = 9
        · subst k
          have ha : start.getD 9 (10,false) = (0,true) := by simp (config := {congrConsts := false}) [start,List.getD_eq_getElem?_getD]
          have hb : (lift w).getD 9 false = !(w.getD 0 false) := by simp (config := {congrConsts := false}) [lift,List.getD_eq_getElem?_getD]
          rw [ha,hb]
          change ((w++[false]).getD 0 false != true) = !(w.getD 0 false)
          rw [List.getD_append _ _ _ _ (by omega)]
          cases w.getD 0 false <;> rfl
        · by_cases k10 : k = 10
          · subst k
            have ha : start.getD 10 (10,false) = (9,false) := by simp (config := {congrConsts := false}) [start,List.getD_eq_getElem?_getD]
            have hb : (lift w).getD 10 false = w.getD 9 false := by simp (config := {congrConsts := false}) [lift,List.getD_eq_getElem?_getD]
            rw [ha,hb]
            change ((w++[false]).getD 9 false != false) = w.getD 9 false
            rw [List.getD_append _ _ _ _ (by omega)]
            cases w.getD 9 false <;> rfl
          · have ha : start.getD k (10,false) = (10,false) :=
              List.getD_eq_default _ _ (by simp (config := {congrConsts := false}) [start]; omega)
            rw [ha,List.getD_eq_default (lift w) false (by rw [liftLen w hw]; omega)]
            exact (congrArg (fun b : Bool => b != false) (dummy [] w hw)).trans rfl
  let normalized := fun g : Gate =>
    bif g.op.eval [false] then ⟨GateOp.not,[g.inputs.headD 24]⟩
    else if g.inputs.length = 1 then ⟨g.op,[g.inputs.headD 24,g.inputs.headD 24]⟩
    else if g.inputs.length = 0 then bif g.op.eval [] then g else ⟨.or,[24,24]⟩ else g
  let good := fun g : Gate => (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  have hGood (g : Gate) (hg : g ∈ C.gates) : good g := by
    simpa (config := {congrConsts := false}) only [good,Set.mem_insert_iff,Set.mem_singleton_iff] using fan g hg
  have normGate (g : Gate) (hg : good g) : form (normalized g) ∧
      ∀ w : List Bool, w.length ≤ 24 → raw w (normalized g) = raw w g := by
    obtain ⟨op,ins⟩ := g
    obtain ⟨hop,hins⟩ := hg
    change op = .and ∨ op = .or ∨ op = .not at hop
    change ins.length ≤ 2 at hins
    have off (w : List Bool) (hw : w.length ≤ 24) : w.getD 24 false = false := List.getD_eq_default _ _ hw
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨p,_ | ⟨q,_ | ⟨r,rs⟩⟩⟩
      · exact ⟨Or.inl rfl,fun _ _ => rfl⟩
      · refine ⟨Or.inr (Or.inr ⟨p,p,Or.inl rfl⟩),?_⟩
        intro w _
        change w ++ [w.getD p false && (w.getD p false && true)] = w ++ [w.getD p false && true]
        cases w.getD p false <;> rfl
      · exact ⟨Or.inr (Or.inr ⟨p,q,Or.inl rfl⟩),fun _ _ => rfl⟩
      · simp (config := {congrConsts := false}) at hins
    · rcases ins with _ | ⟨p,_ | ⟨q,_ | ⟨r,rs⟩⟩⟩
      · refine ⟨Or.inr (Or.inr ⟨24,24,Or.inr rfl⟩),?_⟩
        intro w hw
        change w ++ [w.getD 24 false || (w.getD 24 false || false)] = w ++ [false]
        rw [off w hw]
        rfl
      · refine ⟨Or.inr (Or.inr ⟨p,p,Or.inr rfl⟩),?_⟩
        intro w _
        change w ++ [w.getD p false || (w.getD p false || false)] = w ++ [w.getD p false || false]
        cases w.getD p false <;> rfl
      · exact ⟨Or.inr (Or.inr ⟨p,q,Or.inr rfl⟩),fun _ _ => rfl⟩
      · simp (config := {congrConsts := false}) at hins
    · cases ins with
      | nil =>
        refine ⟨Or.inr (Or.inl ⟨24,rfl⟩),?_⟩
        intro w hw
        change w ++ [!(w.getD 24 false)] = w ++ [true]
        rw [off w hw]
        rfl
      | cons p _ => exact ⟨Or.inr (Or.inl ⟨p,rfl⟩),fun _ _ => rfl⟩
  have normFold (gs : List Gate) : ∀ w : List Bool,
      (∀ g ∈ gs, good g) → w.length+gs.length ≤ 24 →
      (gs.map normalized).foldl raw w = gs.foldl raw w := by
    induction gs with
    | nil => intro w _ _; rfl
    | cons g gs ih =>
      intro w hg hw
      have eq := (normGate g (hg g List.mem_cons_self)).2 w (by omega)
      change (gs.map normalized).foldl raw (raw w (normalized g)) = gs.foldl raw (raw w g)
      rw [eq]
      apply ih
      · exact fun g h => hg g (List.mem_cons_of_mem _ h)
      · simp (config := {congrConsts := false}) [raw] at ⊢
        simp (config := {congrConsts := false}) only [List.length_cons] at hw
        omega
  let gs := C.gates.map normalized
  have gForm : ∀ g ∈ gs, form g := by
    intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    exact (normGate g' (hGood g' hg')).1
  change C.gates.length ≤ 13 at sizeC
  have gCount : gs.length ≤ 13 := by simpa (config := {congrConsts := false}) only [gs,List.length_map] using sizeC
  obtain ⟨rs,bs,P,hs,hb,hP⟩ := compile gs gForm [] start [] {0,10} hStart
  have linked : link gs rs bs P := by simpa (config := {congrConsts := false}) only [List.nil_append] using hs
  have containsZero : 0 ∈ P := linked.2.1.1
  let q := describe rs C.output
  let B : BinaryCircuit := ⟨bs,q.1⟩
  have sign : q.2 = true → B.output ∈ P := (described _ _ _ _ linked C.output).2
  have gatesOK : ∀ g ∈ B.gates, allowed P g := linked.2.2.2.1
  by_contra fails
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [!x 0] ++
      [GateOp.or.eval ([i,j].map (fun k => (List.ofFn x ++ [!x 0]).getD k false))]) = f x := by
    have target : ∀ t : Fin 9 → Bool, f t = ((t 0 && t 1) || (t 1 && t 2) ||
      (t 2 && t 3) || (t 3 && t 4) || (t 4 && t 0) || (t 0 && t 5) || (t 1 && t 6) ||
      (t 2 && t 7) || (t 3 && t 8) || (t 5 && t 7) || (t 6 && t 8) || (t 8 && t 5)) := by
      intro t
      simp (config := {congrConsts := false}) only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
      rfl
    rw [target x]
    by_contra disagree
    exact fails ⟨x,disagree⟩
  have compiled (x : Fin 9 → Bool) : (B.eval (List.ofFn x ++ [x a || x b,false]) != q.2) = f x := by
    let w := List.ofFn x ++ [x a || x b]
    let y : Fin 9 → Bool := fun k => x (perm swap k)
    have wlen : w.length = 10 := by simp (config := {congrConsts := false}) [w]
    have input (k : Fin 9) : w.getD k.val false = x k := by
      unfold w
      rw [List.getD_append _ _ _ _ (by simp (config := {congrConsts := false})),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
    have source (k : Fin 9) : (List.ofFn y ++ [!y 0]).getD k.val false = y k := by
      rw [List.getD_append _ _ _ _ (by simp (config := {congrConsts := false})),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
    have f0 : w.getD 0 false = y 0 := by
      change w.getD 0 false = x (perm swap 0)
      rw [permZero]
      exact input 0
    have fa : w.getD 9 false = (x a || x b) := by simp (config := {congrConsts := false}) [w,List.getD_eq_getElem?_getD]
    have forAnchor : GateOp.or.eval ([i,j].map (fun k => (List.ofFn y ++ [!y 0]).getD k false)) =
        (x a || x b) := by
      change ((List.ofFn y ++ [!y 0]).getD i false ||
        ((List.ofFn y ++ [!y 0]).getD j false || false)) = _
      rw [Bool.or_false]
      change ((List.ofFn y ++ [!y 0]).getD u.val false || (List.ofFn y ++ [!y 0]).getD v.val false) = _
      rw [source u,source v]
      change (x (perm swap u) || x (perm swap v)) = _
      rcases anchors with h | h
      · rw [h.1,h.2]
      · rw [h.1,h.2,Bool.or_comm]
    have hLift : lift w = List.ofFn y ++ [!y 0] ++
        [GateOp.or.eval ([i,j].map (fun k => (List.ofFn y ++ [!y 0]).getD k false))] := by
      unfold lift
      have rows : List.ofFn (fun k : Fin 9 => w.getD (perm swap k).val false) = List.ofFn y :=
        congrArg List.ofFn (funext fun k => input (perm swap k))
      rw [rows,f0,fa,forAnchor]
      simp (config := {congrConsts := false}) only [List.append_assoc,List.singleton_append]
    have eq := linked.2.2.2.2 w wlen C.output
    have normEq := normFold C.gates (lift w) hGood (by rw [liftLen _ wlen]; omega)
    change read (bs.foldl bit (w++[false])) q = (gs.foldl raw (lift w)).getD C.output false at eq
    rw [normEq] at eq
    change read (bs.foldl bit (w++[false])) q = C.eval (lift w) at eq
    rw [hLift,computes y,sameTarget swap x] at eq
    change ((bs.foldl bit (List.ofFn x ++ [x a || x b,false])).getD q.1 false != q.2) = f x
    simpa (config := {congrConsts := false}) only [read,w,List.append_assoc,List.singleton_append] using eq
  simp (config := {congrConsts := false}) only [List.length_nil,Nat.zero_add] at hb
  have hP' : P.card ≤ 2 + gs.countP notG := by simpa (config := {congrConsts := false}) using hP
  have sizeB : B.size ≤ 13 := by change bs.length ≤ 13; omega
  by_cases short : B.size ≤ 11
  · exact small a b B P q.2 canonical short sign gatesOK compiled
  by_cases twelve : B.size = 12
  · have e : bs.length = 12 := twelve
    exact middle a b B P q.2 canonical twelve containsZero linked.2.1.2 (by omega) sign gatesOK compiled
  have thirteen : B.size = 13 := by omega
  have e : bs.length = 13 := thirteen
  exact tight a b B P q.2 canonical thirteen containsZero linked.2.1.2 (by omega) sign gatesOK compiled
