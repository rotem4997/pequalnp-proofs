import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.GenericRejection

set_option maxRecDepth 16400 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5777_638
    (shareMeet : ∀ (C : Circuit) (p l : Fin 7), C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence fanoLines C → p ∈ fanoLines l →
      2 ≤ C.lineDeg 14 {p.val} → 2 ≤ C.lineDeg 14 {7+l.val} →
      (∃ j < C.gates.length, (gateAt C j).op = .and ∧
        2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count (14+j)) → False)
    (shareJoin : ∀ (C : Circuit) (p l : Fin 7), C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence fanoLines C → p ∈ fanoLines l →
      2 ≤ C.lineDeg 14 {p.val} → 2 ≤ C.lineDeg 14 {7+l.val} →
      (∃ j < C.gates.length, (gateAt C j).op = .or ∧
        2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count (14+j)) → False)
    : (have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x4 → x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x14 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x14 ∧ x14.leaves ≤ (28 : ℕ) ∧ (∀ (x15 : Fin (14 : ℕ) → Bool), x14.eval x15 = x4.eval (List.ofFn x15)) ∧ (2 : ℕ) ≤ x3 (↑x5) x14 ∧ (2 : ℕ) ≤ x3 ((7 : ℕ) + ↑x6) x14) := by
  have wireFold (C : Circuit) (w : List Bool) : C.wires w =
      C.gates.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) w := rfl

  have degFold (C : Circuit) (n : ℕ) (mark : Finset ℕ) : C.lineDegrees n mark =
      C.gates.foldl (fun s g => s ++ [g.lineDegree s]) ((List.range n).map fun i => if i ∈ mark then 1 else 0) := rfl

  have evalAnd (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have evalOr (w : List Bool) : GateOp.or.eval w = w.any id := rfl

  have wAnd (d args : List ℕ) : (Gate.mk .and args).lineDegree d = (args.map fun j => d.getD j 0).sum := rfl
  have wOr (d args : List ℕ) : (Gate.mk .or args).lineDegree d = (args.map fun j => d.getD j 0).foldr max 0 := rfl

  have leavesL {n} (i : Fin n) (b : Bool) : (DMFormula.lit i b).leaves = 1 := rfl
  have leavesA {n} (a b : DMFormula n) : (DMFormula.and a b).leaves = a.leaves+b.leaves := rfl
  have leavesO {n} (a b : DMFormula n) : (DMFormula.or a b).leaves = a.leaves+b.leaves := rfl
  have evL {n} (i : Fin n) (x : Fin n → Bool) : (DMFormula.lit i true).eval x = x i := rfl
  have evA {n} (a b : DMFormula n) (x : Fin n → Bool) : (DMFormula.and a b).eval x = (a.eval x && b.eval x) := rfl
  have evO {n} (a b : DMFormula n) (x : Fin n → Bool) : (DMFormula.or a b).eval x = (a.eval x || b.eval x) := rfl
  have cSize (C : Circuit) : C.size = C.gates.length := rfl

  let degree {n : ℕ} (i : Fin n) (F : DMFormula n) : ℕ :=
    DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j.val = i.val then 1 else 0)
      (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

  let normal {n : ℕ} (F : DMFormula n) : Prop :=
    let both := fun (A B : DMFormula n) (pa pb : Prop) => pa ∧ pb ∧
      ¬∃ i : Fin n, A=DMFormula.lit i true ∧ B=DMFormula.lit i true
    DMFormula.rec (motive := fun _ => Prop) (fun _ b => b=true) both both F

  let shaped (n : ℕ) (gs : List Gate) : Prop :=
    ∀ j g, gs[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

  let leafAt {n : ℕ} (T : List (DMFormula n)) (i : ℕ) : ℕ :=
    (T[i]?.map DMFormula.leaves).getD 0

  let leafSum {n : ℕ} (T : List (DMFormula n)) (R : List ℕ) : ℕ :=
    (R.map (leafAt T)).sum

  have leafSum_append {n : ℕ} (T : List (DMFormula n)) (R S : List ℕ) :
      leafSum T (R ++ S) = leafSum T R + leafSum T S := by
    simp [leafSum]

  have leafSum_old {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n)
      (R : List ℕ) (h : ∀ i ∈ R, i < T.length) :
      leafSum (T ++ [F]) R = leafSum T R := by
    change (R.map (leafAt (T ++ [F]))).sum = (R.map (leafAt T)).sum
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [leafAt, List.getElem?_append_left (h i hi)]

  have leafAt_last {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n) :
      leafAt (T ++ [F]) T.length = F.leaves := by
    simp [leafAt]

  have getMap {n : ℕ} {α : Type} {T : List (DMFormula n)} {i : ℕ} {F : DMFormula n}
      (h : T[i]? = some F) (f : DMFormula n → α) (base : α) :
      (T.map f).getD i base = f F := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

  -- For several queried wires, count the leaves of their expansions together.
  -- A final gate may be expanded at most once because its wire has one use.
  have snocBudget {n : ℕ} (gs : List Gate) (g : Gate)
      (T : List (DMFormula n)) (F : DMFormula n) (a b : ℕ)
      (len : T.length = n + gs.length) (inputs : g.inputs = [a,b])
      (oldA : a < T.length) (oldB : b < T.length)
      (newLeaves : F.leaves = leafAt T a + leafAt T b)
      (earlier : ∀ R : List ℕ,
        ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
        (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length) :
      ∀ R : List ℕ,
        ((R ++ (gs ++ [g]).flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
        (∀ r ∈ R, r < (T ++ [F]).length) →
        leafSum (T ++ [F]) R ≤ R.length + (gs ++ [g]).length := by
    intro R unique valid
    let p := fun i : ℕ => decide (n ≤ i)
    let prev := (gs.flatMap Gate.inputs).filter p
    let pair := ([a,b] : List ℕ).filter p
    have packed : (R.filter p ++ (prev ++ pair)).Nodup := by
      simpa only [p, prev, pair, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, inputs, List.filter_append] using unique
    by_cases hR : T.length ∈ R
    · obtain ⟨L, S, rfl⟩ := List.append_of_mem hR
      have pop : p T.length = true := by simp [p, len]
      have packSplit : (L.filter p ++ T.length :: (S.filter p ++ (prev ++ pair))).Nodup := by
        simpa only [List.filter_append, List.filter_cons, pop, ite_true, List.append_assoc, List.cons_append] using packed
      have htail := (List.nodup_append.mp packSplit).2.1
      have noLeft : T.length ∉ L := by
        intro h
        have disjoint := (List.nodup_append.mp packSplit).2.2
        exact disjoint _ (List.mem_filter.mpr ⟨h,pop⟩) _ (by simp) rfl
      have noRight : T.length ∉ S := by
        intro h
        have miss := (List.nodup_cons.mp htail).1
        exact miss (List.mem_append_left _ (List.mem_filter.mpr ⟨h,pop⟩))
      have validL : ∀ i ∈ L, i < T.length := by
        intro i hi
        have inR : i ∈ L ++ T.length :: S := List.mem_append_left _ hi
        have bound := valid i inR
        have different : i ≠ T.length := fun he => noLeft (he ▸ hi)
        simp at bound
        omega
      have validS : ∀ i ∈ S, i < T.length := by
        intro i hi
        have inR : i ∈ L ++ T.length :: S := List.mem_append_right _
          (List.mem_cons_of_mem _ hi)
        have bound := valid i inR
        have different : i ≠ T.length := fun he => noRight (he ▸ hi)
        simp at bound
        omega
      let R' := (L ++ S) ++ [a,b]
      have deleted : ((L.filter p ++ S.filter p) ++ (prev ++ pair)).Nodup := by
        rw [List.append_assoc]
        exact ((List.sublist_cons_self _ _).append_left _).nodup packSplit
      have swapped : ((L.filter p ++ S.filter p) ++ (pair ++ prev)).Nodup :=
        (List.Perm.append_left _ List.perm_append_comm).nodup_iff.mp deleted
      have earlierNodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
        simpa only [R', prev, pair, List.filter_append, List.append_assoc] using swapped
      have earlierValid : ∀ i ∈ R', i < T.length := by
        intro i hi
        simp only [R', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with (h | h) | rfl | rfl
        · exact validL i h
        · exact validS i h
        · exact oldA
        · exact oldB
      have earlierBound := earlier R' earlierNodup earlierValid
      have comparison : leafSum (T ++ [F]) (L ++ T.length :: S) = leafSum T R' := by
        rw [leafSum_append, leafSum_old _ _ _ validL]
        have one : (T.length :: S) = [T.length] ++ S := rfl
        rw [one, leafSum_append, leafSum_old _ _ _ validS]
        simp only [R', leafSum_append]
        have hsingle : leafSum (T ++ [F]) [T.length] = F.leaves := by
          simpa [leafSum] using leafAt_last T F
        rw [hsingle, newLeaves]
        simp [leafSum]
        omega
      rw [comparison]
      simp only [R', List.length_append, List.length_cons, List.length_nil] at earlierBound ⊢
      omega
    · have validOld : ∀ i ∈ R, i < T.length := by
        intro i hi
        have bound := valid i hi
        have different : i ≠ T.length := fun he => hR (he ▸ hi)
        simp at bound
        omega
      have simpler : ((R ++ gs.flatMap Gate.inputs).filter p).Nodup := by
        have initialPart : ((R.filter p ++ prev) ++ pair).Nodup := by
          simpa only [List.append_assoc] using packed
        simpa only [prev, List.filter_append] using (List.nodup_append.mp initialPart).1
      rw [leafSum_old _ _ _ validOld]
      have bound := earlier R simpler validOld
      simp
      omega

  have expandAll (n : ℕ) (gs : List Gate) (ok : shaped n gs) :
      ∃ T : List (DMFormula n), T.length = n + gs.length ∧
        (∀ (i : ℕ) (F : DMFormula n), T[i]? = some F → normal F) ∧
        (∀ i F, T[i]? = some F → ∀ j b, F = DMFormula.lit j b → i=j.val) ∧
        (∀ x, T.map (fun F => F.eval x) = (Circuit.mk gs 0).wires (List.ofFn x)) ∧
        (∀ i : Fin n, T.map (degree i) = (Circuit.mk gs 0).lineDegrees n {i.val}) ∧
        ∀ R : List ℕ, ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
          (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil =>
      let T := List.ofFn (fun i : Fin n => DMFormula.lit i true)
      refine ⟨T, by simp [T], ?_, ?_, ?_, ?_, ?_⟩
      · intro i F hi
        obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp hi
        have payload : T[i] = DMFormula.lit ⟨i, by simpa [T] using bound⟩ true := by simp [T]
        rw [payload]
      · intro i F found j b eq
        subst F
        obtain ⟨bound,heq⟩ := List.getElem?_eq_some_iff.mp found
        have payload : T[i]'bound = DMFormula.lit ⟨i, by simpa [T] using bound⟩ true := by simp [T]
        rw [payload] at heq
        injection heq with indices signs
        exact congrArg Fin.val indices
      · intro x
        simp [T, wireFold, Function.comp_def, evL]
      · intro i
        apply List.ext_getElem
        · simp [degFold, T]
        · intro j hj hj'
          simp only [degFold, List.foldl_nil]
          rw [List.getElem_map, List.getElem_map]
          have jT : j < T.length := by simpa using hj
          have eqn : T[j]'jT = DMFormula.lit ⟨j, by simpa [T] using jT⟩ true := by simp [T]
          rw [eqn]
          simp [degree, List.getElem_range]
      · intro R _ valid
        have single (r : ℕ) (hr : r ∈ R) : leafAt T r = 1 := by
          have br := valid r hr
          have eqn : T[r] = DMFormula.lit ⟨r, by simpa [T] using br⟩ true := by simp [T]
          simp [leafAt, List.getElem?_eq_getElem br, eqn, leavesL]
        have eqn : R.map (leafAt T) = R.map (fun _ => 1) := List.map_congr_left single
        simp [leafSum, eqn]
    | append_singleton gs g ih =>
      have early : shaped n gs := by
        intro j h atj
        have bound := (List.getElem?_eq_some_iff.mp atj).choose
        apply ok j h
        rwa [List.getElem?_append_left bound]
      obtain ⟨T, len, pos, literals, evals, degs, budget⟩ := ih early
      have gateAt : (gs ++ [g])[gs.length]? = some g := by simp
      obtain ⟨operator, a, b, inputs, distinct, ha, hb⟩ := ok gs.length g gateAt
      have ba : a < T.length := len.symm ▸ ha
      have bb : b < T.length := len.symm ▸ hb
      let A := T[a]
      let B := T[b]
      have aAt : T[a]? = some A := List.getElem?_eq_getElem ba
      have bAt : T[b]? = some B := List.getElem?_eq_getElem bb
      let F := bif g.op.eval [] then DMFormula.and A B else DMFormula.or A B
      have noPair : ¬∃ i : Fin n, A=DMFormula.lit i true ∧ B=DMFormula.lit i true := by
        rintro ⟨i,ha,hb⟩
        exact distinct ((literals a A aAt i true ha).trans (literals b B bAt i true hb).symm)
      have posF : normal F := by
        rcases operator with op | op
        · have e : F = DMFormula.and A B := by simp [F,op,evalAnd]
          rw [e]
          exact ⟨pos a A aAt,pos b B bAt,noPair⟩
        · have e : F = DMFormula.or A B := by simp [F,op,evalOr]
          rw [e]
          exact ⟨pos a A aAt,pos b B bAt,noPair⟩
      have leafF : F.leaves = leafAt T a + leafAt T b := by
        rcases operator with op | op <;> simp [F, op, evalAnd, evalOr, leavesA, leavesO, leafAt, aAt, bAt]
      refine ⟨T ++ [F], by simp [len, Nat.add_assoc], ?_, ?_, ?_, ?_,
        snocBudget gs g T F a b len inputs ba bb leafF budget⟩
      · intro j H h
        by_cases before : j < T.length
        · rw [List.getElem?_append_left before] at h
          exact pos j H h
        · have inside := (List.getElem?_eq_some_iff.mp h).choose
          have equality : j = T.length := by simp at inside; omega
          subst j
          simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact h ▸ posF
      · intro j H hj i sign eq
        by_cases before : j < T.length
        · rw [List.getElem?_append_left before] at hj
          exact literals j H hj i sign eq
        · have inside := (List.getElem?_eq_some_iff.mp hj).choose
          have equality : j = T.length := by simp at inside; omega
          subst j
          simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.some.injEq] at hj
          have impossible := hj.trans eq
          rcases operator with op | op <;> simp [F,op,evalAnd,evalOr] at impossible
      · intro x
        simp only [List.map_append, List.map_cons, List.map_nil]
        have unfoldStep :
            (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
              (Circuit.mk gs 0).wires (List.ofFn x) ++
                [g.op.eval (g.inputs.map fun j => ((Circuit.mk gs 0).wires (List.ofFn x)).getD j false)] := by
          simp [wireFold, List.foldl_append]
        rw [unfoldStep, ← evals x, inputs]
        simp only [List.map_cons, List.map_nil, getMap aAt, getMap bAt]
        rcases operator with op | op <;> simp [F, op, evA, evO, evalAnd, evalOr]
      · intro i
        simp only [List.map_append, List.map_cons, List.map_nil]
        have unfoldStep :
            (Circuit.mk (gs ++ [g]) 0).lineDegrees n {i.val} =
              (Circuit.mk gs 0).lineDegrees n {i.val} ++
                [g.lineDegree ((Circuit.mk gs 0).lineDegrees n {i.val})] := by
          simp [degFold, List.foldl_append]
        rw [unfoldStep, ← degs i]
        have hg : g = ⟨g.op,[a,b]⟩ := by
          cases g with
          | mk kind pins => exact congrArg (Gate.mk kind) inputs
        rcases operator with op | op
        all_goals
          rw [hg,op]
          simp [F, op, evalAnd, evalOr, degree, wAnd, wOr, List.getD_eq_getElem?_getD, aAt, bAt]

  have unfoldTree (n : ℕ) (C : Circuit) (shape : shaped n C.gates)
      (single : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup)
      (accepts : C.eval (List.ofFn (fun _ : Fin n => true)) = true) :
      ∃ F : DMFormula n, normal F ∧ F.leaves ≤ C.size + 1 ∧
        (∀ x, F.eval x = C.eval (List.ofFn x)) ∧
        (∀ i : Fin n, degree i F = C.lineDeg n {i.val}) := by
    obtain ⟨T, len, pos, literals, evals, degs, budget⟩ := expandAll n C.gates shape
    have bound : C.output < T.length := by
      by_contra hn
      change (C.wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
      change ((Circuit.mk C.gates 0).wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
      rw [← evals, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hn)] at accepts
      cases accepts
    let F := T[C.output]
    have found : T[C.output]? = some F := List.getElem?_eq_getElem bound
    have b := budget [C.output] single (by simpa using bound)
    have small : F.leaves ≤ C.size + 1 := by
      simpa [leafSum, leafAt, found, cSize, Nat.add_comm] using b
    refine ⟨F, pos _ _ found, small, ?_, ?_⟩
    · intro x
      change F.eval x = ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD C.output false
      rw [← evals, getMap found]
    · intro i
      change degree i F = ((Circuit.mk C.gates 0).lineDegrees n {i.val}).getD C.output 0
      rw [← degs, getMap found]
  intro combine good count C p l small legal distinct computes flag readP readL
  let uses := C.output :: C.gates.flatMap Gate.inputs
  let picked := uses.filter (fun i => decide (14 ≤ i))
  by_cases single : picked.Nodup
  · have allEq : incidenceInput (Finset.univ : Finset (Fin 7)) (Finset.univ : Finset (Fin 7)) =
        List.ofFn (fun _ : Fin 14 => true) := by decide +kernel
    have goodPair : incidenceFun fanoLines (Finset.univ : Finset (Fin 7)) (Finset.univ : Finset (Fin 7)) = true := by
      decide +kernel
    have on := (computes (Finset.univ : Finset (Fin 7)) (Finset.univ : Finset (Fin 7))).trans goodPair
    rw [allEq] at on
    have shape : shaped 14 C.gates := by
      intro j g entry
      have lt := (List.getElem?_eq_some_iff.mp entry).1
      have el : gateAt C j=g := by
        change C.gates.getD j ⟨.or,[]⟩ = g
        simp [List.getD_eq_getElem?_getD,entry]
      have hg : g ∈ C.gates := List.mem_of_getElem? entry
      obtain ⟨a,b,pair⟩ := List.length_eq_two.mp (legal.2.2 g hg)
      have ne : a≠b := by simpa [pair] using distinct g hg
      refine ⟨legal.1 g hg,a,b,pair,ne,?_,?_⟩
      · exact legal.2.1 j lt a (by rw [el,pair]; simp)
      · exact legal.2.1 j lt b (by rw [el,pair]; simp)
    obtain ⟨F,normalF,nleaves,eval,deg⟩ := unfoldTree 14 C shape single on
    refine ⟨F,normalF,by omega,eval,?_,?_⟩
    · change 2 ≤ degree (Fin.castAdd 7 p) F
      rw [deg]
      exact readP
    · change 2 ≤ degree (Fin.natAdd 7 l) F
      rw [deg]
      exact readL
  · exfalso
    have witness : ∃ w : ℕ, 2 ≤ picked.count w := by
      by_contra! h
      exact single (List.nodup_iff_count.mpr (fun w => by have hw := h w; omega))
    obtain ⟨w,hw⟩ := witness
    have used : w ∈ picked := List.count_pos_iff.mp (by omega)
    have above : 14 ≤ w := of_decide_eq_true (List.mem_filter.mp used).2
    have countEq : picked.count w = uses.count w := List.count_filter (decide_eq_true above)
    have twice : 2 ≤ uses.count w := countEq ▸ hw
    have operand : w ∈ C.gates.flatMap Gate.inputs := by
      by_contra missing
      have none : (C.gates.flatMap Gate.inputs).count w = 0 := List.count_eq_zero_of_not_mem missing
      change 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count w at twice
      rw [List.count_cons,none] at twice
      split at twice <;> omega
    obtain ⟨g,gMem,wi⟩ := List.mem_flatMap.mp operand
    obtain ⟨k,entry⟩ := List.getElem?_of_mem gMem
    have ksize := (List.getElem?_eq_some_iff.mp entry).1
    have gat : gateAt C k = g := by
      change C.gates.getD k ⟨.or,[]⟩ = g
      simp [List.getD_eq_getElem?_getD,entry]
    have back := legal.2.1 k ksize w (gat.symm ▸ wi)
    let j := w-14
    have jsize : j < C.gates.length := by omega
    have index : 14+j = w := by omega
    have thisGate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ jsize
    have op := legal.1 C.gates[j] (List.getElem_mem jsize)
    rw [← thisGate] at op
    rcases op with meet | join
    · exact shareMeet C p l small legal distinct computes flag readP readL ⟨j,jsize,meet,index.symm ▸ twice⟩
    · exact shareJoin C p l small legal distinct computes flag readP readL ⟨j,jsize,join,index.symm ▸ twice⟩
