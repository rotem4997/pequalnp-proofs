import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count paths to the observed wires after cutting the incoming reads of wire 9.
theorem PEqualNP.Outside.R_meta_3360_6
    (without : ∀ (C : Circuit), FanInTwo C → C.size = 8 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      let path (u v : ℕ) := Relation.ReflTransGen
        (fun a b : ℕ => 10 ≤ b ∧ b < 17 ∧ a < b ∧ a ∈ (gateAt C (b-9)).inputs) u v
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ S ⊆ Finset.range 17, S.card = 6 →
        9 ∉ S →
        (∀ i < 9, ∃ w ∈ S, path i w) →
        (∃ J : Finset ℕ, 3 ≤ J.card ∧ ∀ j ∈ J, 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path j w) →
        ∃ p n : Fin 9 → Bool, f p ≠ f n ∧ ∀ w ∈ S,
          (C.wires (List.ofFn p)).getD w false = (C.wires (List.ofFn n)).getD w false)
    (withSeed : ∀ (C : Circuit), FanInTwo C → C.size = 8 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      let path (u v : ℕ) := Relation.ReflTransGen
        (fun a b : ℕ => 10 ≤ b ∧ b < 17 ∧ a < b ∧ a ∈ (gateAt C (b-9)).inputs) u v
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ S ⊆ Finset.range 17, S.card = 6 →
        9 ∈ S → ¬ (0 ∈ S ∧ 2 ∈ S) →
        (∀ i < 9, ∃ w ∈ S, path i w) →
        (∃ J : Finset ℕ, 4 ≤ J.card ∧ ∀ j ∈ J, 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path j w) →
        ∃ p n : Fin 9 → Bool, f p ≠ f n ∧ ∀ w ∈ S,
          (C.wires (List.ofFn p)).getD w false = (C.wires (List.ofFn n)).getD w false) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  classical
  let row (r : Fin 512) (i : Fin 9) : Bool := r.val.testBit i.val

  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let pos : Fin 9 → Fin 512 := ![21,3,133,24,17,33,66,132,264]
  let neg : Fin 9 → Fin 512 := ![20,1,129,16,1,1,2,4,8]

  have rows (i : Fin 9) : ∃ p n : Fin 512,
      target (row p) ≠ target (row n) ∧
      (∀ j : Fin 9, j ≠ i → row p j = row n j) ∧
      (row p 0 || row p 2) = (row n 0 || row n 2) := by
    refine ⟨pos i, neg i, ?_⟩
    fin_cases i <;> decide +kernel

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let path (C : Circuit) (x y : ℕ) : Prop :=
    Relation.ReflTransGen
      (fun u v : ℕ => 10 ≤ v ∧ v < 17 ∧ u < v ∧ u ∈ (gateAt C (v-9)).inputs) x y

  let observe (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
    val C (List.ofFn x) w

  let collision (C : Circuit) (S : Finset ℕ) : Prop :=
    ∃ p n : Fin 9 → Bool, target p ≠ target n ∧
      ∀ w ∈ S, observe C p w = observe C n w

  have reads_raw (C : Circuit) (x : Fin 9 → Bool) {w : ℕ} (hw : w < 9) :
      observe C x w = x ⟨w,hw⟩ := by
    have len : (List.ofFn x).length = 9 := List.length_ofFn
    have h : w < (List.ofFn x).length := by rw [len]; exact hw
    change val C (List.ofFn x) w = _
    rw [val_input len hw,List.getD_eq_getElem _ _ h,List.getElem_ofFn]

  have missing (C : Circuit) (size : C.size = 8)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17)
      (absent : ¬ ∀ i < 9, ∃ w ∈ S, path C i w) : collision C S := by
    classical
    push Not at absent
    obtain ⟨i,hi,absent⟩ := absent
    let j : Fin 9 := ⟨i,hi⟩
    obtain ⟨p,n,diff,oneBit,seedSame⟩ := rows j
    let p' := row p
    let n' := row n
    have agree (w : ℕ) (valid : w < 17) (no : ¬ path C i w) :
        observe C p' w = observe C n' w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases raw : w < 9
        · rw [reads_raw C p' raw,reads_raw C n' raw]
          have ne : (⟨w,raw⟩ : Fin 9) ≠ j := by
            intro eq
            have same : w = i := congrArg Fin.val eq
            subst w
            exact no Relation.ReflTransGen.refl
          exact oneBit _ ne
        · by_cases s : w = 9
          · subst w
            rw [seed,seed]
            exact seedSame
          let k := w-9
          have off : 9+k = w := by dsimp [k]; omega
          have gvalid : k < C.gates.length := by
            change C.gates.length = 8 at size
            dsimp [k]
            omega
          have eqp := val_gate (n := 9) (C := C) (x := List.ofFn p') List.length_ofFn gvalid
          have eqn := val_gate (n := 9) (C := C) (x := List.ofFn n') List.length_ofFn gvalid
          rw [off] at eqp eqn
          change val C (List.ofFn p') w = val C (List.ofFn n') w
          rw [eqp,eqn]
          congr 1
          apply List.map_congr_left
          intro u hu
          by_cases lo : u < w
          · rw [ite_eq_left lo,ite_eq_left lo]
            exact ih u lo (by omega) (fun h => no (h.tail ⟨by omega,valid,lo,hu⟩))
          · rw [ite_eq_right lo,ite_eq_right lo]
    exact ⟨p',n',diff,fun w hw => agree w (Finset.mem_range.mp (bounded hw)) (absent w hw)⟩

  have canonical (C : Circuit)
      (seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2))
      (without : ∀ B : Finset ℕ, B ⊆ Finset.range 17 → B.card = 6 → 9 ∉ B → collision C B)
      (withSeed : ∀ B : Finset ℕ, B ⊆ Finset.range 17 → B.card = 6 → 9 ∈ B →
        ¬ (0 ∈ B ∧ 2 ∈ B) → collision C B)
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17) (size : S.card ≤ 6) : collision C S := by
    classical
    have capacity : 6 ≤ (Finset.range 17).card := by decide
    obtain ⟨B,subB,rangeB,eqB⟩ := Finset.exists_subsuperset_card_eq bounded size capacity
    have restrict (h : collision C B) : collision C S := by
      obtain ⟨p,n,d,obs⟩ := h
      exact ⟨p,n,d,fun w hw => obs w (subB hw)⟩
    by_cases sel : 9 ∈ B
    · by_cases pair : 0 ∈ B ∧ 2 ∈ B
      · have within : B.erase 9 ⊆ (Finset.range 17).erase 9 := by
          intro w hw
          obtain ⟨ne,here⟩ := Finset.mem_erase.mp hw
          exact Finset.mem_erase.mpr ⟨ne,rangeB here⟩
        have budget : (B.erase 9).card ≤ 6 :=
          (Finset.card_le_card (Finset.erase_subset 9 B)).trans_eq eqB
        have cap : 6 ≤ ((Finset.range 17).erase 9).card := by decide
        obtain ⟨U,subU,rangeU,eqU⟩ := Finset.exists_subsuperset_card_eq within budget cap
        have no : 9 ∉ U := fun h => (Finset.mem_erase.mp (rangeU h)).1 rfl
        obtain ⟨p,n,d,obs⟩ := without U
          (rangeU.trans (Finset.erase_subset 9 _)) eqU no
        apply restrict
        refine ⟨p,n,d,?_⟩
        intro w hw
        by_cases sel9 : w = 9
        · subst w
          have h0 := obs 0 (subU (Finset.mem_erase.mpr ⟨by decide,pair.1⟩))
          have h2 := obs 2 (subU (Finset.mem_erase.mpr ⟨by decide,pair.2⟩))
          rw [reads_raw C p (show 0<9 by decide),reads_raw C n (show 0<9 by decide)] at h0
          rw [reads_raw C p (show 2<9 by decide),reads_raw C n (show 2<9 by decide)] at h2
          rw [seed,seed]
          change (p ⟨0,by decide⟩ || p ⟨2,by decide⟩) = (n ⟨0,by decide⟩ || n ⟨2,by decide⟩)
          rw [h0,h2]
        · exact obs w (subU (Finset.mem_erase.mpr ⟨sel9,hw⟩))
      · exact restrict (withSeed B rangeB eqB sel pair)
    · exact restrict (without B rangeB eqB sel)

  have budget (C : Circuit) (size : C.size = 8) (fan : FanInTwo C)
      (S : Finset ℕ) (bounded : S ⊆ Finset.range 17)
      (cover : ∀ i < 9, ∃ w ∈ S, path C i w) :
      ∃ J : Finset ℕ, (∀ j ∈ J, 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path C j w) ∧
        9 + (if 9 ∈ S then 1 else 0) ≤ S.card + J.card := by
    classical
    let A := (Finset.range 17).filter (fun i => ∃ w ∈ S, path C i w)
    let J := A.filter fun j => 10 ≤ j
    let base := if 9 ∈ S then Finset.range 10 else Finset.range 9
    have baseSize : base.card = 9 + (if 9 ∈ S then 1 else 0) := by
      by_cases sel : 9 ∈ S <;> simp [base,sel]
    have inA {i : ℕ} (hi : i < 17) (h : ∃ w ∈ S, path C i w) : i ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,h⟩
    have reachable {j : ℕ} (hj : j ∈ J) : 10 ≤ j ∧ j < 17 ∧ ∃ w ∈ S, path C j w := by
      obtain ⟨ha,hj⟩ := Finset.mem_filter.mp hj
      obtain ⟨hr,h⟩ := Finset.mem_filter.mp ha
      exact ⟨hj,Finset.mem_range.mp hr,h⟩
    have base_condition {v : ℕ} (hv : v ∈ base) : v < 9 ∨ v = 9 ∧ 9 ∈ S := by
      unfold base at hv
      by_cases seed : 9 ∈ S
      · rw [ite_eq_left seed] at hv
        have h := Finset.mem_range.mp hv
        by_cases small : v < 9
        · exact Or.inl small
        · exact Or.inr ⟨by omega,seed⟩
      · rw [ite_eq_right seed] at hv
        exact Or.inl (Finset.mem_range.mp hv)
    have disjoint : Disjoint base J := by
      apply Finset.disjoint_left.mpr
      intro v hb hj
      have lo := (reachable hj).1
      rcases base_condition hb with h | ⟨h,_⟩ <;> omega
    have lo : base ∪ J ⊆ A := by
      intro v h
      rcases Finset.mem_union.mp h with h | h
      · rcases base_condition h with h | ⟨rfl,sel⟩
        · exact inA (by omega) (cover v h)
        · exact inA (by decide) ⟨9,sel,Relation.ReflTransGen.refl⟩
      · exact (Finset.mem_filter.mp h).1
    let pins (j : ℕ) := (gateAt C (j-9)).inputs.toFinset
    have hi : A ⊆ S ∪ J.biUnion pins := by
      intro v hv
      obtain ⟨w,hw,p⟩ := (Finset.mem_filter.mp hv).2
      rcases p.cases_head with rfl | ⟨j,⟨late,jlt,_,reads⟩,rest⟩
      · exact Finset.mem_union_left _ hw
      · have hj : j ∈ J := Finset.mem_filter.mpr ⟨inA jlt ⟨w,hw,rest⟩,late⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,List.mem_toFinset.mpr reads⟩)
    have cap : (J.biUnion pins).card ≤ J.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      obtain ⟨late,jlt,_⟩ := reachable hj
      have gvalid : j-9 < C.gates.length := by
        change C.gates.length = 8 at size
        omega
      exact Nat.le_trans (List.toFinset_card_le _) (fan _ (gateAt_mem gvalid)).2
    have left := Finset.card_le_card lo
    rw [Finset.card_union_of_disjoint disjoint,baseSize] at left
    have right := (Finset.card_le_card hi).trans (Finset.card_union_le S (J.biUnion pins))
    exact ⟨J,fun _ hj => reachable hj,by omega⟩

  dsimp only
  intro C fan size noNot first selected bounded width
  have seed : ∀ x : Fin 9 → Bool, observe C x 9 = (x 0 || x 2) := first
  have off (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (sz : S.card = 6) (no : 9 ∉ S) :
      collision C S := by
    by_cases coverage : ∀ i < 9, ∃ w ∈ S, path C i w
    · obtain ⟨J,live,cnt⟩ := budget C size fan S bound coverage
      rw [ite_eq_right no,sz] at cnt
      exact without C fan size noNot first S bound sz no coverage ⟨J,by omega,live⟩
    · exact missing C size seed S bound coverage
  have on_ (S : Finset ℕ) (bound : S ⊆ Finset.range 17) (sz : S.card = 6) (yes : 9 ∈ S)
      (essential : ¬ (0 ∈ S ∧ 2 ∈ S)) : collision C S := by
    by_cases coverage : ∀ i < 9, ∃ w ∈ S, path C i w
    · obtain ⟨J,live,cnt⟩ := budget C size fan S bound coverage
      rw [ite_eq_left yes,sz] at cnt
      exact withSeed C fan size noNot first S bound sz yes essential coverage ⟨J,by omega,live⟩
    · exact missing C size seed S bound coverage
  exact canonical C seed off on_ selected bounded width
