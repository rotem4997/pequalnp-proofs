import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

-- A pair of outputs is valid when its accepted quadrangles are nonempty and disjoint.
-- Lowering a wire preserves disjointness. Bypassing an AND preserves all positive tests
-- and keeps at least one accepted quadrangle at each output.
set_option maxHeartbeats 2300000 in
theorem PEqualNP.Outside.R_meta_5258_706
    (lower : ∀ (n : ℕ) (C : Circuit) (j : ℕ), Monotone2 C → ReadsBack n C → j < C.size →
      let E : Circuit := ⟨C.gates.set j ⟨.or,[]⟩, C.output⟩
      ∃ D : Circuit, ∃ f : ℕ → ℕ, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ (x : List Bool) (w : ℕ), x.length = n →
          (D.wires x).getD (f w) false = (E.wires x).getD w false ∧
          ((D.wires x).getD (f w) false = true → (C.wires x).getD w false = true))
    (raise : ∀ (n : ℕ) (C : Circuit) (j p : ℕ), Monotone2 C → ReadsBack n C →
      j < C.size → (gateAt C j).op = .and → p ∈ (gateAt C j).inputs →
      let D := eraseGate n C j p
      Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ (x : List Bool) (w : ℕ), x.length = n → (C.wires x).getD w false = true →
          (D.wires x).getD (eraseRedirect n j p w) false = true)
    (remaining :
      let T := Circuit
      let n := 26
      let H : T → Finset (Finset (Fin 13)) := fun C => (quadrangles singerLines3).filter
        (fun Q => C.eval (incidenceInput Q (missLines singerLines3 Q)) = true)
      let good : T → Prop := fun C => RightOnIncidentPairs singerLines3 C ∧ (H C).Nonempty
      let cut : T → ℕ → T := fun C j => ⟨C.gates.set j ⟨.or,[]⟩, C.output⟩
      let andGate : T → ℕ → Prop := fun C j => (gateAt C j).op = .and
      ∀ (C D : T), C.gates = D.gates → Monotone2 C → ReadsBack n C → C.size < 63 →
      (∃ j k, andGate C j ∧ andGate C k ∧ InCone n C j k) →
      good C → good D → Disjoint (H C) (H D) →
      (∀ j < C.size, ¬ (good (cut C j) ∧ good (cut D j)) ∧
        (andGate C j → ∀ p ∈ (gateAt C j).inputs,
          ¬ Disjoint (H (eraseGate n C j p)) (H (eraseGate n D j p)))) → False) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) =>   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), x5 x6 x7 x8 → x6.size < (63 : ℕ) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x5 x12 x13 x14 ∧ x12.size < x6.size := by

  intro dif posRaw negRaw quad Form C u v valid small nested
  classical
  let pos (D : Circuit) (a b : ℕ) :=
    ∀ w ∈ [a,b], RightOnIncidentPairs singerLines3 ⟨D.gates,w⟩
  let Qs := quadrangles singerLines3
  let sample (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  let hit (D : Circuit) (w : ℕ) := Qs.filter
    (fun Q => (Circuit.mk D.gates w).eval (sample Q) = true)
  let live (D : Circuit) (a b : ℕ) := (hit D a).Nonempty ∧ (hit D b).Nonempty
  let val (D : Circuit) (w : ℕ) (xs : List Bool) := (D.wires xs).getD w false
  have incidence (p l : Fin 13) : p-l ∈ dif ↔ p ∈ singerLines3 l := by
    change p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l
    revert p l
    decide +kernel
  have incidenceRow (p l : Fin 13) : incidenceInput {p} {l} = posRaw p l := by
    change (List.ofFn (fun x : Fin 13 => decide (x ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun x : Fin 13 => decide (x ∈ ({l} : Finset (Fin 13))))) = _
    simp only [Finset.mem_singleton]
    rfl
  have quadrangle (Q : Finset (Fin 13)) : Q ∈ Qs ↔ quad Q := by
    have cross (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun x => x-l ∈ dif) := by
      ext x
      simp [incidence x l]
    change Q ∈ (Finset.univ.powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,cross]
    rfl
  have quadrangleRow (Q : Finset (Fin 13)) : sample Q = negRaw Q := by
    have tail : List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ dif)) := by
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      change l ∈ Finset.univ.filter (fun k => Disjoint (singerLines3 k) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,← incidence]
      exact ⟨fun h p hp hi => h hi hp, fun h p hp hi => h p hi hp⟩
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ Q))) ++ _ = _
    rw [tail]
  have inputLength (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ L))).length = 26
    simp
  have memHit (D : Circuit) (a : ℕ) (Q : Finset (Fin 13)) :
      Q ∈ hit D a ↔ Q ∈ Qs ∧ val D a (sample Q) = true := by
    change Q ∈ Qs.filter (fun X => val D a (sample X) = true) ↔ _
    exact Finset.mem_filter
  have strict : ∀ a b : Bool, a < b ↔ a = false ∧ b = true := by decide
  have compact (D : Circuit) (a b : ℕ) :
      Form D a b ↔ Monotone2 D ∧ ReadsBack 26 D ∧ pos D a b ∧
        Disjoint (hit D a) (hit D b) ∧ live D a b := by
    constructor
    · rintro ⟨hm,hb,hpos,hneg,hab,hba⟩
      refine ⟨hm,hb,?_,?_,?_⟩
      · intro w hw l p hinc
        have h := Bool.and_eq_true_iff.mp (hpos p l ((incidence p l).mpr hinc))
        change val D w (incidenceInput {p} {l}) = true
        rw [incidenceRow]
        rcases (show w=a ∨ w=b by simpa using hw) with rfl | rfl
        · exact h.1
        · exact h.2
      · apply Finset.disjoint_left.mpr
        intro Q ha hb
        obtain ⟨hq,ha⟩ := (memHit D a Q).mp ha
        have hb := ((memHit D b Q).mp hb).2
        rw [quadrangleRow] at ha hb
        have impossible := hneg Q ((quadrangle Q).mp hq)
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false at impossible
        simp [ha,hb] at impossible
      · obtain ⟨A,hA,hAB⟩ := hab
        obtain ⟨B,hB,hBA⟩ := hba
        refine ⟨⟨B,(memHit D a B).mpr ⟨(quadrangle B).mpr hB,?_⟩⟩,
          ⟨A,(memHit D b A).mpr ⟨(quadrangle A).mpr hA,?_⟩⟩⟩
        · rw [quadrangleRow]
          exact (strict _ _).mp hBA |>.2
        · rw [quadrangleRow]
          exact (strict _ _).mp hAB |>.2
    · rintro ⟨hm,hb,positive,disjoint,liveA,liveB⟩
      refine ⟨hm,hb,?_,?_,?_,?_⟩
      · intro p l hinc
        apply Bool.and_eq_true_iff.mpr
        have pa := positive a (by simp) l p ((incidence p l).mp hinc)
        have pb := positive b (by simp) l p ((incidence p l).mp hinc)
        change val D a (incidenceInput {p} {l}) = true at pa
        change val D b (incidenceInput {p} {l}) = true at pb
        rw [incidenceRow] at pa pb
        exact ⟨pa,pb⟩
      · intro Q hQ
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false
        rw [← quadrangleRow]
        cases h : (val D a (sample Q) && val D b (sample Q)) with
        | false => rfl
        | true =>
          have bits := Bool.and_eq_true_iff.mp h
          have hq := (quadrangle Q).mpr hQ
          exact (Finset.disjoint_left.mp disjoint ((memHit D a Q).mpr ⟨hq,bits.1⟩)
            ((memHit D b Q).mpr ⟨hq,bits.2⟩)).elim
      · obtain ⟨Q, hQ⟩ := liveB
        obtain ⟨hq, bt⟩ := (memHit D b Q).mp hQ
        have af : val D a (sample Q) = false := by
          cases h : val D a (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp disjoint ((memHit D a Q).mpr ⟨hq,h⟩) hQ).elim
        refine ⟨Q,(quadrangle Q).mp hq,(strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨af,bt⟩
      · obtain ⟨Q, hQ⟩ := liveA
        obtain ⟨hq, atrue⟩ := (memHit D a Q).mp hQ
        have bf : val D b (sample Q) = false := by
          cases h : val D b (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp disjoint hQ ((memHit D b Q).mpr ⟨hq,h⟩)).elim
        refine ⟨Q,(quadrangle Q).mp hq,(strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨bf,atrue⟩
  let flow (D : Circuit) (a : ℕ) (E : Circuit) (b : ℕ) :=
    ∀ x : List Bool, x.length = 26 → val D a x = true → val E b x = true
  have posFlow {D E : Circuit} {a b c d : ℕ}
      (ha : flow D a E c) (hb : flow D b E d) : pos D a b → pos E c d := by
    intro original w hw l p edge
    change val E w (incidenceInput {p} {l}) = true
    rcases (show w=c ∨ w=d by simpa using hw) with rfl | rfl
    · exact ha _ (inputLength {p} {l}) (original a (by simp) l p edge)
    · exact hb _ (inputLength {p} {l}) (original b (by simp) l p edge)
  have hitFlow {D E : Circuit} {a b : ℕ} (h : flow D a E b) : hit D a ⊆ hit E b := by
    intro Q hQ
    obtain ⟨quad,hit⟩ := (memHit D a Q).mp hQ
    exact (memHit E b Q).mpr ⟨quad,h _ (inputLength Q (missLines singerLines3 Q)) hit⟩
  obtain ⟨hm,hb,hpos,hdisj,hLive⟩ := (compact C u v).mp valid
  let zero (j : ℕ) : Circuit := ⟨C.gates.set j ⟨.or,[]⟩, C.output⟩
  by_cases canLower : ∃ j < C.size, pos (zero j) u v ∧ live (zero j) u v
  · obtain ⟨j,hj,hpos',hlive'⟩ := canLower
    obtain ⟨D,f,hmD,hbD,smaller,hsem⟩ := lower 26 C j hm hb hj
    have fromZero (w : ℕ) : flow (zero j) w D (f w) :=
      fun x len bit => (hsem x w len).1.trans bit
    have below (w : ℕ) : flow D (f w) C w := fun x len => (hsem x w len).2
    have newPos := posFlow (fromZero u) (fromZero v) hpos'
    have newDisj : Disjoint (hit D (f u)) (hit D (f v)) :=
      Finset.disjoint_left.mpr (fun _ hu hv => Finset.disjoint_left.mp hdisj
        (hitFlow (below u) hu) (hitFlow (below v) hv))
    have newLive : live D (f u) (f v) :=
      ⟨hlive'.1.mono (hitFlow (fromZero u)), hlive'.2.mono (hitFlow (fromZero v))⟩
    exact ⟨D,f u,f v,(compact _ _ _).mpr ⟨hmD,hbD,newPos,newDisj,newLive⟩,smaller⟩
  by_cases canRaise : ∃ j < C.size, (gateAt C j).op = .and ∧
      ∃ p ∈ (gateAt C j).inputs,
      Disjoint (hit (eraseGate 26 C j p) (eraseRedirect 26 j p u))
        (hit (eraseGate 26 C j p) (eraseRedirect 26 j p v))
  · obtain ⟨j,hj,hop,p,hp,newDisj⟩ := canRaise
    let D := eraseGate 26 C j p
    let f := eraseRedirect 26 j p
    obtain ⟨hmD,hbD,smaller,hsem⟩ := raise 26 C j p hm hb hj hop hp
    have above (w : ℕ) : flow C w D (f w) := fun x len => hsem x w len
    have newPos := posFlow (above u) (above v) hpos
    have newLive : live D (f u) (f v) :=
      ⟨hLive.1.mono (hitFlow (above u)), hLive.2.mono (hitFlow (above v))⟩
    exact ⟨D,f u,f v,(compact _ _ _).mpr ⟨hmD,hbD,newPos,newDisj,newLive⟩,smaller⟩
  have blockedLower (j : ℕ) (hj : j < C.size) : ¬ (pos (zero j) u v ∧ live (zero j) u v) :=
    fun h => canLower ⟨j,hj,h⟩
  have blockedRaise (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = .and)
      (p : ℕ) (hp : p ∈ (gateAt C j).inputs) :
      ¬ Disjoint (hit (eraseGate 26 C j p) (eraseRedirect 26 j p u))
        (hit (eraseGate 26 C j p) (eraseRedirect 26 j p v)) :=
    fun h => canRaise ⟨j,hj,hop,p,hp,h⟩
  let A : Circuit := ⟨C.gates,u⟩
  let B : Circuit := ⟨C.gates,v⟩
  refine (remaining A B rfl hm hb small nested
    ⟨hpos u (by simp),hLive.1⟩ ⟨hpos v (by simp),hLive.2⟩ hdisj ?_).elim
  intro j hj
  constructor
  · rintro ⟨⟨pa,la⟩,⟨pb,lb⟩⟩
    refine blockedLower j hj ⟨?_,la,lb⟩
    intro w hw
    rcases (show w=u ∨ w=v by simpa using hw) with rfl | rfl
    · exact pa
    · exact pb
  · intro hop p hp h
    have route (w : ℕ) : eraseGate 26 ⟨C.gates,w⟩ j p =
        ⟨(eraseGate 26 C j p).gates,eraseRedirect 26 j p w⟩ := by
      change j < C.gates.length at hj
      let gs := C.gates.take j ++ (C.gates.drop (j+1)).map
        (fun g => (⟨g.op,g.inputs.map (eraseRedirect 26 j p)⟩ : Gate))
      change (if j < C.gates.length then (⟨gs,eraseRedirect 26 j p w⟩ : Circuit) else ⟨C.gates,w⟩) =
        ⟨(if j < C.gates.length then (⟨gs,eraseRedirect 26 j p C.output⟩ : Circuit) else C).gates,
          eraseRedirect 26 j p w⟩
      rw [if_pos hj,if_pos hj]
    change Disjoint (hit (eraseGate 26 A j p) (eraseGate 26 A j p).output)
      (hit (eraseGate 26 B j p) (eraseGate 26 B j p).output) at h
    change Disjoint (hit (eraseGate 26 ⟨C.gates,u⟩ j p) (eraseGate 26 ⟨C.gates,u⟩ j p).output)
      (hit (eraseGate 26 ⟨C.gates,v⟩ j p) (eraseGate 26 ⟨C.gates,v⟩ j p).output) at h
    rw [route u,route v] at h
    exact blockedRaise j hj hop p hp h
