import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Separate coverage by a singleton from consistency of its endpoint across active AND gates.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2069_1 :
  (∀ (C : Circuit), C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.inputs.Nodup) →
    let edge (p l : Fin 13) := p-l = 0 ∨ p-l = 1 ∨ p-l = 3 ∨ p-l = 9
    let val (x : Fin 26 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
    (∀ x, val x C.output = true ↔ ∃ p l, edge p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) →
    (∀ j, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
      ∀ x, val x (26+j) = true → val x C.output = true) →
    ∀ p l, edge p l →
    let p0 := Fin.castAdd 13 p
    let l0 := Fin.natAdd 13 l
    let yes (j a b : ℕ) := C.gates[j]? = some ⟨GateOp.and,[a,b]⟩ ∧
      val (fun i => decide (i=p0 ∨ i=l0)) (26+j) = true
    let hit (i : Fin 26) (a b : ℕ) :=
      (val (fun j => decide (j=i)) a || val (fun j => decide (j=i)) b) = true
    ∀ j a b, yes j a b → hit p0 a b ∨ hit l0 a b) →
  (∀ (C : Circuit), C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.inputs.Nodup) →
    let edge (p l : Fin 13) := p-l = 0 ∨ p-l = 1 ∨ p-l = 3 ∨ p-l = 9
    let val (x : Fin 26 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
    (∀ x, val x C.output = true ↔ ∃ p l, edge p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) →
    (∀ j, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
      ∀ x, val x (26+j) = true → val x C.output = true) →
    ∀ p l, edge p l →
    let p0 := Fin.castAdd 13 p
    let l0 := Fin.natAdd 13 l
    let yes (j a b : ℕ) := C.gates[j]? = some ⟨GateOp.and,[a,b]⟩ ∧
      val (fun i => decide (i=p0 ∨ i=l0)) (26+j) = true
    let hit (i : Fin 26) (a b : ℕ) :=
      (val (fun j => decide (j=i)) a || val (fun j => decide (j=i)) b) = true
    ∀ j a b k u v, yes j a b → yes k u v → hit p0 a b → ¬hit l0 a b →
      hit l0 u v → hit p0 u v) →
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 → ∀ (x17 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x17)).getD ((26 : ℕ) + x14) Bool.false = Bool.true → x4.eval (List.ofFn x17) = Bool.true) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  intro activeCover activeConsistent
  dsimp only
  intro C p l dP dL size gates correct _ clean incidence traceP traceL
  classical
  let P : Fin 26 := Fin.castAdd 13 p
  let L : Fin 26 := Fin.natAdd 13 l
  let one (x : Fin 26) (i : Fin 26) : Bool := decide (i=x)
  let both (i : Fin 26) : Bool := decide (i=P ∨ i=L)
  let val (x : Fin 26 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
  let hit (i : Fin 26) (a b : ℕ) := (val (one i) a || val (one i) b) = true
  let yes (j a b : ℕ) := C.gates[j]? = some ⟨GateOp.and,[a,b]⟩ ∧
    val both (26+j) = true
  have fan : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      exact (gates j g hj).1
    · intro j hj a ha
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
      have hg : C.gates[j]? = some g := by
        change C.gates[j]? = some (C.gates.getD j ⟨.or,[]⟩)
        rw [List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
      change a ∈ g.inputs at ha
      obtain ⟨u,v,pins,_,h₁,h₂⟩ := (gates j g hg).2
      simp [pins] at ha
      rcases ha with rfl | rfl
      · exact h₁
      · exact h₂
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a,b,he,_⟩ := (gates j g hj).2
      simp [he]
  have distinct (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) : g.inputs.Nodup := by
    obtain ⟨a,b,he,hn,_,_⟩ := (gates j g hg).2
    simp [he, hn]
  have cleanAll (j : ℕ) (hg : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and)
      (x : Fin 26 → Bool) (hx : val x (26+j) = true) : val x C.output = true := by
    have hj : j < C.gates.length := by
      by_contra! h
      have hnone := List.getElem?_eq_none (l := C.gates) (i := j) h
      change (C.gates[j]?.getD ⟨.or,[]⟩).op = .and at hg
      rw [hnone] at hg
      cases hg
    exact clean j hj hg x hx
  have incidenceEq : p-l=0 ∨ p-l=1 ∨ p-l=3 ∨ p-l=9 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using incidence
  have correctEq (x : Fin 26 → Bool) : val x C.output = true ↔
      ∃ u v : Fin 13, (u-v=0 ∨ u-v=1 ∨ u-v=3 ∨ u-v=9) ∧
        x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true := by
    change C.eval (List.ofFn x) = true ↔ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using correct x
  have cover (j a b : ℕ) (h : yes j a b) : hit P a b ∨ hit L a b :=
    activeCover C size fan distinct correctEq cleanAll p l incidenceEq j a b h
  have consistent (j a b k u v : ℕ) (hj : yes j a b) (hk : yes k u v)
      (pHit : hit P a b) (lMiss : ¬ hit L a b) (lHit : hit L u v) : hit P u v :=
    activeConsistent C size fan distinct correctEq cleanAll p l incidenceEq j a b k u v hj hk pHit lMiss lHit
  have oneSide : (∀ j a b, yes j a b → hit P a b) ∨ (∀ j a b, yes j a b → hit L a b) := by
    by_cases lp : ∀ j a b, yes j a b → hit P a b
    · exact .inl lp
    · push Not at lp
      obtain ⟨k,u,v,hk,hp⟩ := lp
      refine .inr fun j a b hj => ?_
      by_contra hL
      exact hp (consistent j a b k u v hj hk ((cover j a b hj).resolve_right hL)
        hL ((cover k u v hk).resolve_left hp))
  have singleOut (i : Fin 26) : val (one i) C.output = false := by
    by_contra hf
    have ht : C.eval (List.ofFn (one i)) = true := by
      change val (one i) C.output = true
      exact Bool.eq_true_of_not_eq_false hf
    obtain ⟨u,v,_,hu,hv⟩ := (correct _).mp ht
    have h₁ : Fin.castAdd 13 u = i := of_decide_eq_true hu
    have h₂ : Fin.natAdd 13 v = i := of_decide_eq_true hv
    have equal := congrArg Fin.val (h₁.trans h₂.symm)
    change u.val = 13 + v.val at equal
    omega
  have pairOut : val both C.output = true := (correct _).mpr
    ⟨p,l,incidence,by simp [both,P,L],by simp [both,P,L]⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  have extend (gs : List Gate) (w : List Bool) :
      ∃ e, run gs w = w ++ e ∧ e.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      obtain ⟨rest, he, hlen⟩ := ih (step w g)
      refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: rest, ?_, by simp [hlen]⟩
      change run gs (step w g) = _
      rw [he]
      simp [step, List.append_assoc]
  have lengthRun (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    obtain ⟨e,he,hl⟩ := extend gs w
    simp [he,hl]
  have beforeRun (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    obtain ⟨e,he,_⟩ := extend gs w
    rw [he,List.getD_append _ _ _ _ h]
  have evalGate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (a b : ℕ)
      (hg : gs[j]? = some g) (hi : g.inputs = [a,b]) (ha : a < w.length+j) (hb : b < w.length+j) :
      (run gs w).getD (w.length+j) false =
        g.op.eval [(run gs w).getD a false,(run gs w).getD b false] := by
    induction gs generalizing w j with
    | nil => simp at hg
    | cons head rest ih =>
      change (run rest (step w head)).getD (w.length+j) false =
        g.op.eval [(run rest (step w head)).getD a false,(run rest (step w head)).getD b false]
      cases j with
      | zero =>
        have same : head = g := Option.some.inj hg
        subst head
        have hw : (step w g).length = w.length + 1 := by simp [step]
        rw [Nat.add_zero] at ha hb ⊢
        rw [beforeRun rest (step w g) w.length (by omega),
          beforeRun rest (step w g) a (by omega), beforeRun rest (step w g) b (by omega)]
        simp only [step, hi, List.map_cons, List.map_nil]
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self,
          List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ hb]
        rfl
      | succ j =>
        have he : (step w head).length + j = w.length + (j+1) := by simp [step]; omega
        rw [← he] at ha hb ⊢
        exact ih (step w head) j hg ha hb
  have evalAt (x : Fin 26 → Bool) (j : ℕ) (g : Gate) (a b : ℕ)
      (hg : C.gates[j]? = some g) (hi : g.inputs = [a,b]) (ha : a < 26+j) (hb : b < 26+j) :
      val x (26+j) = g.op.eval [val x a,val x b] := by
    have hl : (List.ofFn x).length = 26 := List.length_ofFn
    have h := evalGate C.gates (List.ofFn x) j g a b hg hi (by rwa [hl]) (by rwa [hl])
    rwa [hl] at h
  have evalInput (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26) :
      val x i = x ⟨i,hi⟩ := by
    change (run C.gates (List.ofFn x)).getD i false = _
    rw [beforeRun _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_ofFn]
  have ANDsingle (u : Fin 26) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
      (hop : g.op = .and) : val (one u) (26+j) = false := by
    by_contra hf
    have h : val (one u) (26+j) = true := Bool.eq_true_of_not_eq_false hf
    have hh : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and := by
      change (C.gates[j]?.getD ⟨.or,[]⟩).op = .and
      rw [hg]
      exact hop
    have bad := cleanAll j hh _ h
    rw [singleOut u] at bad
    contradiction
  have outValid : C.output < 26 + C.gates.length := by
    by_contra! h
    change (run C.gates (List.ofFn both)).getD C.output false = true at pairOut
    rw [List.getD_eq_default _ _ (by rw [lengthRun,List.length_ofFn]; exact h)] at pairOut
    contradiction
  have traces (seed other : Fin 26) (d : ℕ → Bool)
      (starts : ∀ i < 26, d i = decide (i = other.val))
      (propagate : ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (26+j) = ((val (one seed) a && d b) || (d a && val (one seed) b))) ∧
        (g.op = .or → d (26+j) = (d a || d b)))
      (endpoints : ∀ i, both i = true → i = seed ∨ i = other)
      (everyHit : ∀ j a b, yes j a b → hit seed a b) : d C.output = true := by
    have inputTrace (i : ℕ) (hi : i<26) (h : (⟨i,hi⟩ : Fin 26) = other) : d i = true := by
      rw [starts i hi]
      exact decide_eq_true (congrArg Fin.val h)
    have coveredSingle : ∀ i < 26+C.gates.length, val (one other) i = true → d i = true := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro bound actual
        by_cases hi : i < 26
        · rw [evalInput _ _ hi] at actual
          exact inputTrace i hi (of_decide_eq_true actual)
        let j := i-26
        have eq : i = 26+j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        obtain ⟨hop,a,b,pins,_,ha,hb⟩ := gates j g hg
        have he := evalAt (one other) j g a b hg pins ha hb
        rw [eq] at actual ⊢
        rcases hop with h | h
        · rw [ANDsingle other j g hg h] at actual
          contradiction
        · rw [h] at he
          change val (one other) (26+j) = (val (one other) a || (val (one other) b || false)) at he
          simp only [Bool.or_false] at he
          rw [he,Bool.or_eq_true] at actual
          rw [(propagate j g a b hg pins).2 h, Bool.or_eq_true]
          exact actual.imp (ih a (by omega) (by omega)) (ih b (by omega) (by omega))
    have coveredPair : ∀ i < 26+C.gates.length, val both i = true →
        val (one seed) i = true ∨ val (one other) i = true ∨ d i = true := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro bound actual
        by_cases hi : i < 26
        · rw [evalInput _ _ hi] at actual
          rcases endpoints ⟨i,hi⟩ actual with h | h
          · exact .inl (by rw [evalInput _ _ hi]; exact decide_eq_true h)
          · exact .inr (.inr (inputTrace i hi h))
        let j := i-26
        have eq : i = 26+j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        obtain ⟨hop,a,b,pins,_,ha,hb⟩ := gates j g hg
        have eP := evalAt both j g a b hg pins ha hb
        have eS := evalAt (one seed) j g a b hg pins ha hb
        have eO := evalAt (one other) j g a b hg pins ha hb
        rw [eq] at actual ⊢
        rcases hop with h | h
        · have hg' : C.gates[j]? = some ⟨GateOp.and,[a,b]⟩ := by
            have he : g = ⟨GateOp.and,[a,b]⟩ := by
              rw [← h, ← pins]
            rwa [he] at hg
          have side := everyHit j a b ⟨hg',actual⟩
          change (val (one seed) a || val (one seed) b) = true at side
          rw [Bool.or_eq_true] at side
          rw [h] at eP eS
          change val both (26+j) = (val both a && (val both b && true)) at eP
          change val (one seed) (26+j) = (val (one seed) a && (val (one seed) b && true)) at eS
          simp only [Bool.and_true] at eP eS
          have ab := eP.symm.trans actual
          rw [Bool.and_eq_true] at ab
          have hs := ANDsingle seed j g hg h
          rw [eS] at hs
          have emit (k : ℕ) (earlier : k < i) (hact : val both k = true)
              (miss : val (one seed) k = false) : d k = true := by
            rcases ih k earlier (by omega) hact with hK | hK | hK
            · rw [miss] at hK
              contradiction
            · exact coveredSingle k (by omega) hK
            · exact hK
          refine .inr (.inr ?_)
          rw [(propagate j g a b hg pins).1 h]
          rcases side with hsA | hsB
          · have mB : val (one seed) b = false := by simpa [hsA] using hs
            simp [hsA, emit b (by omega) ab.2 mB]
          · have mA : val (one seed) a = false := by simpa [hsB] using hs
            simp [hsB, emit a (by omega) ab.1 mA]
        · rw [h] at eP eS eO
          change val both (26+j) = (val both a || (val both b || false)) at eP
          change val (one seed) (26+j) = (val (one seed) a || (val (one seed) b || false)) at eS
          change val (one other) (26+j) = (val (one other) a || (val (one other) b || false)) at eO
          simp only [Bool.or_false] at eP eS eO
          rw [eP,Bool.or_eq_true] at actual
          rw [eS,eO,(propagate j g a b hg pins).2 h]
          simp only [Bool.or_eq_true]
          rcases actual with aa | bb
          · have ha' := ih a (by omega) (by omega) aa
            tauto
          · have hb' := ih b (by omega) (by omega) bb
            tauto
    have h := coveredPair C.output outValid pairOut
    simpa only [singleOut, Bool.false_eq_true, false_or] using h
  rcases oneSide with points | lines
  · left
    apply traces P L dP ?_ ?_ ?_ points
    · intro i hi
      simpa [L,Nat.add_comm] using traceP.1 i hi
    · exact traceP.2
    · intro i h
      exact of_decide_eq_true h
  · right
    apply traces L P dL ?_ ?_ ?_ lines
    · intro i hi
      simpa [P] using traceL.1 i hi
    · exact traceL.2
    · intro i h
      exact (of_decide_eq_true (p := i=P ∨ i=L) h).symm
