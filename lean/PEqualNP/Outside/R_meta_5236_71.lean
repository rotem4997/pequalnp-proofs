import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_5236_71
    (three : ∀ D : Circuit, ReadsBack 13 D → D.size = 18 → D.output < 31 →
      (∀ g ∈ D.gates,
          (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) → notCount D = 3 →
      ∃ x9 : Fin 10 → Bool,
        D.eval (List.ofFn x9 ++ [x9 0 || x9 2, false, true]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))))
    (four : ∀ D : Circuit, ReadsBack 13 D → D.size = 18 → D.output < 31 →
      (∀ g ∈ D.gates,
          (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) → notCount D = 4 →
      ∃ x9 : Fin 10 → Bool,
        D.eval (List.ofFn x9 ++ [x9 0 || x9 2, false, true]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (3 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (4 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  let bump (i : ℕ) : ℕ := if i < 11 then i else i + 2

  let pins (xs empty : List ℕ) : List ℕ :=
    List.casesOn xs empty (fun a tail =>
      List.casesOn tail [bump a, bump a] (fun b rest => (a :: b :: rest).map bump))
  let norm (g : Gate) : Gate :=
    GateOp.casesOn g.op
      ⟨GateOp.and, pins g.inputs [12,12]⟩
      ⟨GateOp.or, pins g.inputs [11,11]⟩
      ⟨GateOp.not, [List.casesOn g.inputs 11 (fun a _ => bump a)]⟩
      (fun m => ⟨GateOp.mod m, pins g.inputs []⟩)
      ⟨GateOp.maj, pins g.inputs []⟩
  have andEval : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have notEval : ∀ xs : List Bool, GateOp.not.eval xs = !(xs.headD false) := fun _ => rfl

  have bump_eq (i : ℕ) (h : 11 ≤ i) : bump i = i + 2 := by
    simp [bump, show ¬ i < 11 by omega]

  have bump_inj : Function.Injective bump := by
    intro a b h
    unfold bump at h
    split_ifs at h <;> omega

  have op_same (g : Gate) : (norm g).op = g.op := by
    cases g with
    | mk op inputs => cases op <;> cases inputs with
      | nil => rfl
      | cons a tail => cases tail <;> rfl

  have gate_sound (g : Gate)
      (ok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2)
      (w v : List Bool)
      (rel : ∀ i, v.getD (bump i) false = w.getD i false)
      (zero : v.getD 11 false = false) (one : v.getD 12 false = true) :
      (norm g).op.eval ((norm g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [List.getD_eq_getElem?_getD] at rel zero one
    obtain ⟨op, inputs⟩ := g
    rcases ok with ⟨opok, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at opok
    rcases opok with rfl | rfl | rfl
    all_goals
      cases inputs with
      | nil => simp [norm, pins, andEval, orEval, notEval, zero, one]
      | cons a tail =>
        cases tail with
        | nil => simp [norm, pins, andEval, orEval, notEval, rel]
        | cons b rest =>
          cases rest with
          | nil => simp [norm, pins, andEval, orEval, notEval, rel]
          | cons c tail => simp at len

  have snoc_rel (w v : List Bool) (hw : 11 ≤ w.length)
      (hv : v.length = w.length + 2)
      (rel : ∀ i, v.getD (bump i) false = w.getD i false) (b : Bool) :
      ∀ i, (v ++ [b]).getD (bump i) false = (w ++ [b]).getD i false := by
    intro i
    by_cases hit : i = w.length
    · subst i
      rw [bump_eq _ hw, ← hv]
      simp
    · have hnew : bump i ≠ v.length := by
        rw [hv]
        unfold bump
        split_ifs <;> omega
      have getne (xs : List Bool) (j : ℕ) (hj : j ≠ xs.length) :
          (xs ++ [b]).getD j false = xs.getD j false := by
        by_cases hl : j < xs.length
        · exact List.getD_append _ _ _ _ hl
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by omega)]
      rw [getne v _ hnew, getne w _ hit, rel]

  have wires_sound (gs : List Gate)
      (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) :
      ∀ (w v : List Bool), 11 ≤ w.length → v.length = w.length + 2 →
        (∀ i, v.getD (bump i) false = w.getD i false) →
        v.getD 11 false = false → v.getD 12 false = true →
        ∀ i,
          ((gs.map norm).foldl (fun ws g => ws ++ [g.op.eval
            (g.inputs.map fun j => ws.getD j false)]) v).getD (bump i) false =
          (gs.foldl (fun ws g => ws ++ [g.op.eval
            (g.inputs.map fun j => ws.getD j false)]) w).getD i false := by
    induction gs with
    | nil => intro w v hw hv rel zero one i; exact rel i
    | cons g gs ih =>
      intro w v hw hv rel zero one i
      have ge := gate_sound g (ok g (by simp)) w v rel zero one
      simp only [List.map_cons, List.foldl_cons]
      rw [ge]
      apply ih (fun g hg => ok g (by simp [hg]))
      · simp; omega
      · simp; omega
      · exact snoc_rel w v hw hv rel _
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact zero
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact one

  have shape (g : Gate)
      (ok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) :
      ((norm g).op = GateOp.not ∧ (norm g).inputs.length = 1) ∨
      (((norm g).op = GateOp.and ∨ (norm g).op = GateOp.or) ∧
        (norm g).inputs.length = 2) := by
    obtain ⟨op, inputs⟩ := g
    rcases ok with ⟨opok, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at opok
    rcases opok with rfl | rfl | rfl
    all_goals
      cases inputs with
      | nil => simp [norm, pins]
      | cons a tail =>
        cases tail with
        | nil => simp [norm, pins]
        | cons b rest =>
          cases rest with
          | nil => simp [norm, pins]
          | cons c tail => simp at len

  have source (g : Gate) (i : ℕ) (hi : i ∈ (norm g).inputs) :
      i = 11 ∨ i = 12 ∨ ∃ j ∈ g.inputs, i = bump j := by
    have mapped (xs : List ℕ) (hm : i ∈ xs.map bump) :
        ∃ j ∈ xs, i = bump j := by
      obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
      exact ⟨j,hj,h.symm⟩
    obtain ⟨op, inputs⟩ := g
    cases op <;> cases inputs with
    | nil =>
      simp [norm, pins] at hi
      all_goals first | exact Or.inl hi | exact Or.inr (Or.inl hi)
    | cons a tail =>
      cases tail with
      | nil =>
        have h : i = bump a := by simpa [norm, pins] using hi
        exact Or.inr (Or.inr ⟨a, by simp, h⟩)
      | cons b rest =>
        first
        | exact Or.inr (Or.inr (mapped _ hi))
        | have h : i = bump a := by simpa [norm, pins] using hi
          exact Or.inr (Or.inr ⟨a, by simp, h⟩)

  have norm_not_count (gs : List Gate) :
      notCount ⟨gs.map norm, 0⟩ = notCount ⟨gs, 0⟩ := by
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    unfold notCount
    simp only [List.filter_map, Function.comp_def, op_same]
    rw [List.length_map]

  have initial_rel (y : Fin 11 → Bool) :
      ∀ i, (List.ofFn y ++ [false, true]).getD (bump i) false =
        (List.ofFn y).getD i false := by
    intro i
    by_cases hi : i < 11
    · rw [show bump i = i by simp [bump, hi]]
      exact List.getD_append _ _ _ _ (by simpa)
    · rw [bump_eq _ (by omega), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have norm_eval (C : Circuit) (ok : FanInTwo C) (y : Fin 11 → Bool) :
      Circuit.eval ⟨C.gates.map norm, bump C.output⟩
          (List.ofFn y ++ [false, true]) = C.eval (List.ofFn y) := by
    exact wires_sound C.gates ok _ _ (by simp) (by simp)
      (initial_rel y) (by simp) (by simp) C.output

  have prefix_get (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
      i < w.length →
      (gs.foldl (fun ws g => ws ++ [g.op.eval
        (g.inputs.map fun j => ws.getD j false)]) w).getD i false = w.getD i false := by
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp; omega)]
      exact List.getD_append _ _ _ _ hi

  have normalize (C : Circuit) (fan : FanInTwo C) (back : ReadsBack 11 C)
      (size : C.size ≤ 18) (output : C.output < 11 + C.size) :
      ∃ D : Circuit, ReadsBack 13 D ∧ D.size = 18 ∧ D.output < 31 ∧
        notCount D = notCount C ∧
        (∀ g ∈ D.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) ∧
        ∀ y : Fin 11 → Bool,
          D.eval (List.ofFn y ++ [false, true]) = C.eval (List.ofFn y) := by
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    change C.gates.length ≤ 18 at size
    change C.output < 11 + C.gates.length at output
    let G := C.gates.map norm
    let P := List.replicate (18 - C.size) (⟨GateOp.or, [0,0]⟩ : Gate)
    let D : Circuit := ⟨G ++ P, bump C.output⟩
    have len : D.size = 18 := by
      change (G ++ P).length = 18
      simp only [G, P, List.length_append, List.length_map, List.length_replicate]
      change C.gates.length + (18 - C.gates.length) = 18
      omega
    have out : D.output < 31 := by
      change bump C.output < 31
      unfold bump
      split_ifs <;> omega
    have clean : ReadsBack 13 D := by
      intro j hj i hi
      change i ∈ ((G ++ P).getD j ⟨GateOp.or, []⟩).inputs at hi
      by_cases first : j < G.length
      · rw [List.getD_append _ _ _ _ first, List.getD_eq_getElem _ _ first] at hi
        have old : j < C.gates.length := by simpa [G] using first
        simp only [G, List.getElem_map] at hi
        rcases source _ _ hi with rfl | rfl | ⟨a,ha,rfl⟩
        · omega
        · omega
        · have hb := back j old a
          change a ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs → a < 11 + j at hb
          rw [List.getD_eq_getElem _ _ old] at hb
          have bound := hb ha
          unfold bump
          split_ifs <;> omega
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have hp : j - G.length < 18 - C.size := by
          change j < (G ++ P).length at hj
          simp only [List.length_append] at hj
          dsimp [P] at hj ⊢
          simp only [List.length_replicate] at hj
          omega
        dsimp [P] at hi
        rw [List.getD_replicate _ hp] at hi
        have hzero : i = 0 := by simpa using hi
        omega
    have counts : notCount D = notCount C := by
      change ((G ++ P).filter (fun g => decide (g.op = GateOp.not))).length = _
      rw [List.filter_append, List.length_append]
      have nc := norm_not_count C.gates
      change (G.filter (fun g => decide (g.op = GateOp.not))).length = notCount C at nc
      rw [nc]
      simp [P]
    have canonical : ∀ g ∈ D.gates,
        (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) := by
      intro g hg
      change g ∈ G ++ P at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
        exact shape a (fan a ha)
      · have h := List.mem_replicate.mp hg
        rcases h with ⟨_, rfl⟩
        simp
    refine ⟨D, clean, len, out, counts, canonical, ?_⟩
    intro y
    rw [← norm_eval C fan y]
    change ((G ++ P).foldl _ (List.ofFn y ++ [false,true])).getD (bump C.output) false =
      (G.foldl _ (List.ofFn y ++ [false,true])).getD (bump C.output) false
    rw [List.foldl_append]
    apply prefix_get
    have length_fold (gs : List Gate) : ∀ w : List Bool,
        (gs.foldl (fun ws g => ws ++ [g.op.eval
          (g.inputs.map fun j => ws.getD j false)]) w).length = w.length + gs.length := by
      induction gs with
      | nil => intro w; simp
      | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp; omega
    rw [length_fold]
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil,
      List.length_map]
    dsimp [G]
    simp only [List.length_map]
    change bump C.output < 13 + C.gates.length
    unfold bump
    split_ifs <;> change C.gates.length ≤ 18 at size <;> change C.output < 11 + C.gates.length at output <;> omega
  intro C fan back size _ outputBound notLower notUpper
  obtain ⟨D, dback, dsize, dout, dcount, dcanonical, same⟩ :=
    normalize C fan back size outputBound
  have evalSame (x : Fin 10 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 2, false, true]) =
        C.eval (List.ofFn x ++ [x 0 || x 2]) := by
    let y : Fin 11 → Bool := Fin.append x (fun _ : Fin 1 => x 0 || x 2)
    have inputs : List.ofFn y = List.ofFn x ++ [x 0 || x 2] := by
      rw [show y = Fin.append x (fun _ : Fin 1 => x 0 || x 2) from rfl,
        List.ofFn_fin_append]
      rfl
    have h := same y
    rw [inputs] at h
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  have cases : notCount D = 3 ∨ notCount D = 4 := by omega
  rcases cases with hthree | hfour
  · obtain ⟨x, hx⟩ := three D dback dsize dout dcanonical hthree
    exact ⟨x, by rwa [evalSame x] at hx⟩
  · obtain ⟨x, hx⟩ := four D dback dsize dout dcanonical hfour
    exact ⟨x, by rwa [evalSame x] at hx⟩
