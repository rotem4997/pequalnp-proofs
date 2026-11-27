import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_5064_724
    (peel :
    ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (u v : Fin n ↪ Fin (n+n)) (C : Circuit) (p : Fin n) (rev : Bool),
      let eval := fun (F : Finset (Fin n × Fin n)) (D : Circuit) =>
        ∀ z, circuitFun (n+n) D z = decide (∃ i j, (i,j) ∈ F ∧ z (u i) = true ∧ z (v j) = true)
      let A := fun i j : Fin n => if rev then (j,i) ∈ E else (i,j) ∈ E
      let B := Finset.univ.filter (fun i => i ≠ p ∧ A i p)
      let F := E.filter (fun e => e.1 ≠ p ∧ e.2 ≠ p)
      (∀ i j, u i ≠ v j) →
      (∀ i j, (i,j) ∈ E → (i,i) ∈ E ∧ (j,j) ∈ E) →
      (∀ i j a b, i ≠ j → a ≠ b → ¬ ((i,a) ∈ E ∧ (i,b) ∈ E ∧ (j,a) ∈ E ∧ (j,b) ∈ E)) →
      (p,p) ∈ E → (∃ i j, i ≠ j ∧ (i,i) ∈ F ∧ (j,j) ∈ F) → (∀ j, A p j → j = p) →
      (∀ i ∈ B, ∀ j ∈ B, A i j ↔ i = j) →
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ t, t ≠ p → ¬ (A i t ∧ A j t)) →
      IsAO2 (n+n) C → eval E C →
      ∃ D : Circuit, IsAO2 (n+n) D ∧ eval F D ∧ D.size + B.card + 2 ≤ C.size)
    (core :
    ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (u v : Fin n ↪ Fin (n+n)) (C : Circuit),
      let eval := fun (F : Finset (Fin n × Fin n)) (D : Circuit) =>
        ∀ z, circuitFun (n+n) D z = decide (∃ i j, (i,j) ∈ F ∧ z (u i) = true ∧ z (v j) = true)
      (∀ i j, u i ≠ v j) →
      (∀ i j, (i,j) ∈ E → (i,i) ∈ E ∧ (j,j) ∈ E) →
      (∀ i j a b, i ≠ j → a ≠ b → ¬ ((i,a) ∈ E ∧ (i,b) ∈ E ∧ (j,a) ∈ E ∧ (j,b) ∈ E)) →
      let V := Finset.univ.filter (fun i => (i,i) ∈ E)
      3 ≤ V.card → V.card < n → 2*V.card ≤ E.card →
      (∀ i, (i,i) ∈ E → (∃ j, j ≠ i ∧ (i,j) ∈ E) ∧ (∃ j, j ≠ i ∧ (j,i) ∈ E)) →
      IsAO2 (n+n) C → eval E C →
      E.card + V.card ≤ C.size+1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n original π C _ _ noRect matched hao computes postedLeaf
  -- Index each column by its partner in the specified matching.
  let rename : (Fin n × Fin n) ≃ (Fin n × Fin n) := Equiv.prodCongr (Equiv.refl _) π.symm
  let R := original.map rename.toEmbedding
  have memR (i j : Fin n) : (i,j) ∈ R ↔ (i,π j) ∈ original := by
    change (i,j) ∈ original.map rename.toEmbedding ↔ _
    rw [Finset.mem_map_equiv]
    rfl
  let u : Fin n ↪ Fin (n+n) := ⟨Fin.castAdd n, Fin.castAdd_injective n n⟩
  let v : Fin n ↪ Fin (n+n) := π.toEmbedding.trans ⟨Fin.natAdd n, Fin.natAdd_injective n n⟩
  have sep (i j : Fin n) : u i ≠ v j := by
    intro he
    have k := congrArg Fin.val he
    change i.val = n + (π j).val at k
    have := i.isLt
    omega
  let eval := fun (F : Finset (Fin n × Fin n)) (D : Circuit) =>
    ∀ z, circuitFun (n+n) D z = decide (∃ i j, (i,j) ∈ F ∧ z (u i) = true ∧ z (v j) = true)
  -- The six bit positions are the six two-element subsets of four active inputs.
  let bank : List (BitVec 6) := [0,11,21,38,56]
  let choices := fun (w : List (BitVec 6)) => (w.flatMap fun a => w.flatMap fun b => [a &&& b,a ||| b]).eraseDups
  let reachable : ℕ → List (BitVec 6) → BitVec 6 → Bool :=
    Nat.rec (fun w t => w.contains t) (fun _ prev w t => w.contains t ||
      (choices w).any (fun a => prev (a::w) t))
  have excluded : reachable 2 bank 33 = false ∧ reachable 3 bank 37 = false ∧
      reachable 3 bank 41 = false := by decide +kernel
  -- Every gate extends the pool by one pairwise conjunction or disjunction.
  have tiny (m : ℕ) (D : Circuit) (ao : IsAO2 m D) (signal : Fin m → BitVec 6)
      (hsig : ∀ j, signal j ∈ bank) (tgt : BitVec 6) (cap : ℕ)
      (hout : ∀ t : Fin 6, circuitFun m D (fun j => (signal j).getLsbD t.val) = tgt.getLsbD t.val)
      (forbid : reachable cap bank tgt = false) : cap < D.size := by
    let combine (op : GateOp) (a b : BitVec 6) := if op = .and then a &&& b else a ||| b
    have andBits (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have orBits (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    let step := fun (w : List (BitVec 6)) (g : Gate) =>
      w ++ [combine g.op (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0)]
    let bstep := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have good (g : Gate) (hg : g ∈ D.gates) :
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] :=
      ⟨ao.1 _ hg,List.length_eq_two.mp (ao.2.2 _ hg)⟩
    have access (w : List (BitVec 6)) (j t : ℕ) :
        (w.map (fun a => a.getLsbD t)).getD j false = (w.getD j 0).getLsbD t := by
      simpa using List.getD_map w (0 : BitVec 6) (n := j) (fun a => a.getLsbD t)
    have trans (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ D.gates) (w : List (BitVec 6)) (t : ℕ) :
        (gs.foldl step w).map (fun a => a.getLsbD t) = gs.foldl bstep (w.map (fun a => a.getLsbD t)) := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,List.foldl_cons,ih (fun v hv => sub _ (List.mem_cons_of_mem _ hv))]
        congr 1
        obtain ⟨ops,a,b,ins⟩ := good g (sub _ List.mem_cons_self)
        rcases ops with h | h <;> simp [step,bstep,combine,h,ins,andBits,orBits] <;> cases w[a]? <;> cases w[b]? <;> simp
    have eqOut : (D.gates.foldl step (List.ofFn signal)).getD D.output 0 = tgt := by
      apply BitVec.eq_of_getLsbD_eq
      intro t ht
      rw [← access, trans D.gates (fun _ h => h)]
      have hh := hout ⟨t,ht⟩
      change (D.gates.foldl bstep _).getD D.output false = _ at hh
      simpa [List.map_ofFn,Function.comp_def] using hh
    have reach (limit : ℕ) (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ D.gates)
        (sz : gs.length ≤ limit) (w pool : List (BitVec 6)) (hz : 0 ∈ pool)
        (ws : ∀ a ∈ w, a ∈ pool) :
        reachable limit pool ((gs.foldl step w).getD D.output 0) = true := by
      have get (w pool : List (BitVec 6)) (ws : ∀ a ∈ w, a ∈ pool) (hz : 0 ∈ pool) (j : ℕ) : w.getD j 0 ∈ pool := by
        by_cases hj : j < w.length
        · rw [List.getD_eq_getElem _ _ hj]
          exact ws _ (List.getElem_mem _)
        · rwa [List.getD_eq_default _ _ (by omega)]
      induction limit generalizing gs w pool with
      | zero =>
        have nil : gs = [] := List.length_eq_zero_iff.mp (by omega)
        subst gs
        exact List.contains_iff_mem.mpr (get w pool ws hz _)
      | succ k ih =>
        change (_ || _) = true
        apply Bool.or_eq_true_iff.mpr
        cases gs with
        | nil => exact Or.inl (List.contains_iff_mem.mpr (get w pool ws hz _))
        | cons g gs =>
          right
          apply List.any_eq_true.mpr
          obtain ⟨ops,a,b,ins⟩ := good g (sub _ List.mem_cons_self)
          let y := combine g.op (w.getD a 0) (w.getD b 0)
          refine ⟨y, ?_,?_⟩
          · apply List.mem_eraseDups.mpr
            refine List.mem_flatMap.mpr ⟨_,get w pool ws hz a,List.mem_flatMap.mpr ⟨_,get w pool ws hz b,?_⟩⟩
            rcases ops with h | h <;> simp [y,combine,h]
          · apply ih gs (fun v hv => sub _ (List.mem_cons_of_mem _ hv)) (by simpa using sz) (step w g) (y::pool) (List.mem_cons_of_mem _ hz)
            intro x hx
            change x ∈ w ++ [combine g.op (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0)] at hx
            rw [ins] at hx
            change x ∈ w ++ [y] at hx
            have hx' : x ∈ w ∨ x = y := by simpa using hx
            exact hx'.elim (fun h => List.mem_cons_of_mem _ (ws _ h)) (fun h => h ▸ List.mem_cons_self)
    by_contra! small
    have r := reach cap D.gates (fun _ h => h) small (List.ofFn signal) bank (by simp [bank])
      (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact hsig i)
    rw [eqOut,forbid] at r
    contradiction
  have exactTwo (E : Finset (Fin n × Fin n)) (D : Circuit) (model : IsAO2 (n+n) D)
      (ev : eval E D) (p r : Fin n) (ne : p ≠ r) (hpp : (p,p) ∈ E) (hrr : (r,r) ∈ E)
      (span : ∀ i j, (i,j) ∈ E → (i=p ∨ i=r) ∧ (j=p ∨ j=r))
      (noBoth : ¬ ((p,r) ∈ E ∧ (r,p) ∈ E)) : E.card + 2 ≤ D.size+1 := by
    let signal (j : Fin (n+n)) : BitVec 6 :=
      if j=u p then 11 else if j=v p then 21 else if j=u r then 38 else if j=v r then 56 else 0
    have member (i : Fin (n+n)) : signal i ∈ bank := by
      dsimp [signal]
      repeat' split
      all_goals decide
    have aa : signal (u p) = 11 := by simp [signal]
    have bb : signal (v p) = 21 := by simp [signal,(sep p p).symm]
    have cc : signal (u r) = 38 := by simp [signal,ne.symm,sep r p]
    have dd : signal (v r) = 56 := by simp [signal,ne.symm,(sep p r).symm,(sep r r).symm]
    let edgeBits (e : Fin n × Fin n) := signal (u e.1) &&& signal (v e.2)
    let table := fun (es : List (Fin n × Fin n)) => (es.map edgeBits).foldr (· ||| ·) 0
    have sound (es : List (Fin n × Fin n)) (he : ∀ i j, (i,j) ∈ E ↔ (i,j) ∈ es) (t : Fin 6) :
        circuitFun (n+n) D (fun j => (signal j).getLsbD t.val) = (table es).getLsbD t.val := by
      have bits (l : List (Fin n × Fin n)) : (table l).getLsbD t.val = true ↔
          ∃ e ∈ l, (signal (u e.1)).getLsbD t.val = true ∧ (signal (v e.2)).getLsbD t.val = true := by
        induction l with
        | nil => simp [table]
        | cons e l ih =>
          change ((edgeBits e) ||| (table l)).getLsbD t.val = true ↔ _
          rw [BitVec.getLsbD_or,Bool.or_eq_true_iff,ih,BitVec.getLsbD_and,Bool.and_eq_true_iff]
          simp only [List.mem_cons]
          constructor
          · rintro (h | ⟨a,ha,h⟩)
            · exact ⟨e,Or.inl rfl,h⟩
            · exact ⟨a,Or.inr ha,h⟩
          · rintro ⟨a,(rfl | ha),h⟩
            · exact Or.inl h
            · exact Or.inr ⟨a,ha,h⟩
      rw [ev]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq,bits]
      constructor
      · rintro ⟨i,j,h,hi,hj⟩
        exact ⟨(i,j),(he _ _).mp h,hi,hj⟩
      · rintro ⟨⟨i,j⟩,h,hi,hj⟩
        exact ⟨i,j,(he _ _).mpr h,hi,hj⟩
    have rows (i j : Fin n) : (i,j) ∈ E ↔
        (i=p ∧ j=p) ∨ (i=r ∧ j=r) ∨ (i=p ∧ j=r ∧ (p,r) ∈ E) ∨ (i=r ∧ j=p ∧ (r,p) ∈ E) := by
      constructor
      · intro h
        obtain ⟨ha,hb⟩ := span i j h
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl ⟨ha,hb⟩
        · exact Or.inr (Or.inr (Or.inl ⟨ha,hb,ha ▸ hb ▸ h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ha,hb,ha ▸ hb ▸ h⟩))
        · exact Or.inr (Or.inl ⟨ha,hb⟩)
      · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,h⟩ | ⟨rfl,rfl,h⟩) <;> assumption
    have counting (es : List (Fin n × Fin n)) (he : ∀ i j, (i,j) ∈ E ↔ (i,j) ∈ es) :
        E = es.toFinset := by ext ⟨i,j⟩; simpa using he i j
    by_cases forward : (p,r) ∈ E <;> by_cases back : (r,p) ∈ E
    · exact (noBoth ⟨forward,back⟩).elim
    · let es := [(p,p),(r,r),(p,r)]
      have he (i j : Fin n) : (i,j) ∈ E ↔ (i,j) ∈ es := by rw [rows]; simp [es,forward,back]
      have ht : table es = 41 := by simp [table,es,edgeBits,aa,bb,cc,dd]
      have g := tiny _ D model signal member 41 3 (fun t => ht ▸ sound es he t) excluded.2.2
      have hc : E.card = 3 := by rw [counting es he]; simp [es,ne,ne.symm]
      omega
    · let es := [(p,p),(r,r),(r,p)]
      have he (i j : Fin n) : (i,j) ∈ E ↔ (i,j) ∈ es := by rw [rows]; simp [es,forward,back]
      have ht : table es = 37 := by simp [table,es,edgeBits,aa,bb,cc,dd]
      have g := tiny _ D model signal member 37 3 (fun t => ht ▸ sound es he t) excluded.2.1
      have hc : E.card = 3 := by rw [counting es he]; simp [es,ne,ne.symm]
      omega
    · let es := [(p,p),(r,r)]
      have he (i j : Fin n) : (i,j) ∈ E ↔ (i,j) ∈ es := by rw [rows]; simp [es,forward,back]
      have ht : table es = 33 := by simp [table,es,edgeBits,aa,bb,cc,dd]
      have g := tiny _ D model signal member 33 2 (fun t => ht ▸ sound es he t) excluded.1
      have hc : E.card = 2 := by rw [counting es he]; simp [es,ne]
      omega
  let active := fun F : Finset (Fin n × Fin n) => Finset.univ.filter (fun i => (i,i) ∈ F)
  let thick := fun E : Finset (Fin n × Fin n) => ∀ i, (i,i) ∈ E → (∃ j, j ≠ i ∧ (i,j) ∈ E) ∧ (∃ j, j ≠ i ∧ (j,i) ∈ E)
  have finish (E : Finset (Fin n × Fin n)) (D : Circuit)
      (closed : ∀ i j, (i,j) ∈ E → (i,i) ∈ E ∧ (j,j) ∈ E)
      (rect : ∀ i j a b, i ≠ j → a ≠ b → ¬ ((i,a) ∈ E ∧ (i,b) ∈ E ∧ (j,a) ∈ E ∧ (j,b) ∈ E))
      (model : IsAO2 (n+n) D) (ev : eval E D) (terminal : thick E → (active E).card < n) :
      E.card + (active E).card ≤ D.size+1 := by
    induction hN : (active E).card using Nat.strong_induction_on generalizing E D with
    | ind k ih =>
      by_cases all : ∀ i, (i,i) ∈ E → (∃ j, j ≠ i ∧ (i,j) ∈ E) ∧ (∃ j, j ≠ i ∧ (j,i) ∈ E)
      · by_cases empty : E = ∅
        · subst E
          simp [active] at hN ⊢
          omega
        obtain ⟨⟨p,q⟩,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        have hp := (closed p q he).1
        obtain ⟨j,hjp,hpj⟩ := (all p hp).1
        obtain ⟨l,hlp,hlp'⟩ := (all p hp).2
        have hj := (closed _ _ hpj).2
        have hl := (closed _ _ hlp').1
        have hjl : j ≠ l := by
          rintro rfl
          exact rect p j p j hjp.symm hjp.symm ⟨hp,hpj,hlp',hj⟩
        have memAct (i : Fin n) : i ∈ active E ↔ (i,i) ∈ E := by simp [active]
        have three : 3 ≤ (active E).card := Finset.two_lt_card_iff.mpr
          ⟨p,j,l,(memAct _).mpr hp,(memAct _).mpr hj,(memAct _).mpr hl,hjp.symm,hlp.symm,hjl⟩
        let other (i : Fin n) := if hi : (i,i) ∈ E then Classical.choose (all i hi).1 else i
        have spec (i : Fin n) (hi : i ∈ active E) : other i ≠ i ∧ (i,other i) ∈ E := by
          have hii := (memAct i).mp hi
          simpa [other,hii] using Classical.choose_spec (all i hii).1
        let witness := fun e : Fin n × Bool => (e.1,if e.2 then other e.1 else e.1)
        have twice := Finset.card_le_card_of_injOn
          (s := active E ×ˢ (Finset.univ : Finset Bool)) (t := E) witness (by
            rintro ⟨i,b⟩ h
            have hi := (Finset.mem_product.mp h).1
            cases b
            · exact (memAct _).mp hi
            · exact (spec i hi).2) (by
              rintro ⟨i,b⟩ h ⟨r,c⟩ _ heq
              have hir : i=r := congrArg Prod.fst heq
              subst r
              have hne := (spec i (Finset.mem_product.mp h).1).1
              have hsec := congrArg Prod.snd heq
              cases b <;> cases c <;> first | rfl | exact (hne hsec).elim | exact (hne hsec.symm).elim)
        have dense : 2*(active E).card ≤ E.card := by simpa [Nat.mul_comm] using twice
        simpa [active,hN] using core n E u v D sep closed rect three (terminal all) dense all model ev
      push Not at all
      obtain ⟨p,hp,hbad⟩ := all
      have leaf : ∃ rev : Bool, ∀ j : Fin n,
          (if rev then (j,p) ∈ E else (p,j) ∈ E) → j = p := by
        by_cases hr : ∃ j, j ≠ p ∧ (p,j) ∈ E
        · refine ⟨true,fun j hj => ?_⟩
          by_contra ne
          exact (hbad hr j ne) hj
        · exact ⟨false,fun j hj => by by_contra ne; exact hr ⟨j,ne,hj⟩⟩
      obtain ⟨rev,hpLeaf⟩ := leaf
      let A := fun i j : Fin n => if rev then (j,i) ∈ E else (i,j) ∈ E
      let B := Finset.univ.filter (fun i => i ≠ p ∧ A i p)
      let F := E.filter (fun e => e.1 ≠ p ∧ e.2 ≠ p)
      have Bmem (i : Fin n) : i ∈ B ↔ i ≠ p ∧ A i p := by simp [B]
      have Amatch (i j : Fin n) (h : A i j) : A i i ∧ A j j := by
        cases rev <;> simp [A] at h ⊢
        · exact closed _ _ h
        · exact (closed _ _ h).symm
      have Arect (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b) :
          ¬ (A i a ∧ A i b ∧ A j a ∧ A j b) := by
        cases rev <;> simp only [A, Bool.false_eq_true, ite_false, ite_true]
        · exact rect _ _ _ _ hij hab
        · rintro ⟨h₁,h₂,h₃,h₄⟩
          exact rect _ _ _ _ hab hij ⟨h₁,h₃,h₂,h₄⟩
      -- Two arms already have the partner as a common neighbor.
      have privateArm (i : Fin n) (hi : i ∈ B) (j : Fin n) (hj : j ∈ B) (hne : i ≠ j)
          (t : Fin n) (ht : t ≠ p) : ¬ (A i t ∧ A j t) := by
        rintro ⟨hit,hjt⟩
        exact Arect i j p t hne ht.symm ⟨((Bmem i).mp hi).2,hit,((Bmem j).mp hj).2,hjt⟩
      have induced (i : Fin n) (hi : i ∈ B) (j : Fin n) (hj : j ∈ B) : A i j ↔ i = j := by
        have hdiag := (Amatch j p ((Bmem j).mp hj).2).1
        constructor
        · intro hij
          by_contra ne
          exact privateArm i hi j hj ne j ((Bmem j).mp hj).1 ⟨hij,hdiag⟩
        · rintro rfl
          exact hdiag
      have Fmem (i j : Fin n) : (i,j) ∈ F ↔ (i,j) ∈ E ∧ i ≠ p ∧ j ≠ p := by simp [F]
      have aEq : active F = (active E).erase p := by
        ext i
        simp [active,F,and_comm]
      have hpAct : p ∈ active E := by simpa [active] using hp
      have dec := Finset.card_erase_add_one hpAct
      rw [← aEq,hN] at dec
      have Frs (i j : Fin n) (he : (i,j) ∈ F) := (Fmem _ _).mp he
      by_cases survives : ∃ i, (i,i) ∈ F
      · by_cases many : ∃ i j, i ≠ j ∧ (i,i) ∈ F ∧ (j,j) ∈ F
        · obtain ⟨D',model',ev',cost⟩ := peel n E u v D p rev sep closed rect hp many hpLeaf induced privateArm model ev
          have smaller := ih (active F).card (by omega) F D' (fun i j hij => by
            obtain ⟨he,hip,hjp⟩ := Frs i j hij
            exact ⟨(Fmem i i).mpr ⟨(closed i j he).1,hip,hip⟩,
              (Fmem j j).mpr ⟨(closed i j he).2,hjp,hjp⟩⟩)
            (fun i j a b hij hab h => rect i j a b hij hab
              ⟨(Frs _ _ h.1).1,(Frs _ _ h.2.1).1,(Frs _ _ h.2.2.1).1,(Frs _ _ h.2.2.2).1⟩)
            model' ev' (fun _ => by
              have cap : (active E).card ≤ n := by simpa using (active E).card_le_univ
              omega) rfl
          let arm := fun i : Fin n => if rev then (p,i) else (i,p)
          have inj : Function.Injective arm := by
            intro i j he
            cases rev
            · exact congrArg Prod.fst he
            · exact congrArg Prod.snd he
          -- The deleted edges are the diagonal edge and one edge per arm.
          have rem : E \ F = insert (p,p) (B.image arm) := by
            ext e
            obtain ⟨i,j⟩ := e
            simp only [Finset.mem_sdiff,Fmem,Finset.mem_insert,Finset.mem_image]
            constructor
            · rintro ⟨he,hf⟩
              by_cases hip : i=p <;> by_cases hjp : j=p
              · exact Or.inl (Prod.ext hip hjp)
              · subst i
                right
                cases rev
                · exact (hjp (hpLeaf j he)).elim
                · exact ⟨j,(Bmem _).mpr ⟨hjp,he⟩,rfl⟩
              · subst j
                right
                cases rev
                · exact ⟨i,(Bmem _).mpr ⟨hip,he⟩,rfl⟩
                · exact (hip (hpLeaf i he)).elim
              · exact (hf ⟨he,hip,hjp⟩).elim
            · rintro (he | ⟨t,ht,he⟩)
              · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
                exact ⟨hp,by simp⟩
              · have ht' := (Bmem _).mp ht
                cases rev <;> simp only [arm, Bool.false_eq_true, ite_false, ite_true, Prod.mk.injEq] at he
                all_goals obtain ⟨rfl,rfl⟩ := he
                all_goals exact ⟨ht'.2,by simp⟩
          have hnot : (p,p) ∉ B.image arm := by
            rintro h
            obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
            apply ((Bmem i).mp hi).1
            cases rev <;> simpa [arm] using he
          have count := Finset.card_sdiff_add_card_eq_card (show F ⊆ E from Finset.filter_subset _ _)
          rw [rem,Finset.card_insert_of_notMem hnot,Finset.card_image_of_injective _ inj] at count
          change D'.size + B.card + 2 ≤ D.size at cost
          omega
        · obtain ⟨r,hr⟩ := survives
          have hrr := (Frs _ _ hr).1
          have hpr := ((Frs _ _ hr).2.1).symm
          have two (i : Fin n) (hi : (i,i) ∈ E) : i=p ∨ i=r := by
            by_cases h : i=p
            · exact Or.inl h
            · right
              by_contra hir
              exact many ⟨i,r,hir,(Fmem _ _).mpr ⟨hi,h,h⟩,hr⟩
          have hAct : active E = {p,r} := by
            ext i
            simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
            exact ⟨two i,fun h => h.elim (fun e => e ▸ hp) (fun e => e ▸ hrr)⟩
          rw [hAct,Finset.card_pair hpr] at hN
          have ex := exactTwo E D model ev p r hpr hp hrr (fun i j h =>
            ⟨two i (closed _ _ h).1,two j (closed _ _ h).2⟩)
            (fun h => rect p r p r hpr hpr ⟨hp,h.1,h.2,hrr⟩)
          omega
      · have only (i : Fin n) (hii : (i,i) ∈ E) : i=p := by
          by_contra h
          exact survives ⟨i,(Fmem _ _).mpr ⟨hii,h,h⟩⟩
        have Eeq : E = {(p,p)} := by
          ext ⟨i,j⟩
          constructor
          · intro hij
            obtain ⟨hi,hj⟩ := closed i j hij
            simp [only i hi,only j hj]
          · intro hij
            have hh := Finset.mem_singleton.mp hij
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
            exact hp
        have actEq : active E = {p} := by ext i; simp [active,Eeq]
        have pos : 0 < D.size := by
          by_contra! hzero
          have hg : D.gates = [] := List.length_eq_zero_iff.mp (by change D.size = 0; omega)
          let both := fun t : Fin (n+n) => decide (t=u p ∨ t=v p)
          let one := fun t : Fin (n+n) => decide (t = u p)
          let two := fun t : Fin (n+n) => decide (t = v p)
          have yes : circuitFun (n+n) D both = true := by rw [ev]; simp [Eeq,both]
          have no1 : circuitFun (n+n) D one = false := by rw [ev]; simp [Eeq,one,(sep p p).symm]
          have no2 : circuitFun (n+n) D two = false := by rw [ev]; simp [Eeq,two,sep p p]
          have wire (z : Fin (n+n) → Bool) : circuitFun (n+n) D z = (List.ofFn z).getD D.output false := by
            change (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn z)).getD D.output false = _
            rw [hg]
            rfl
          rw [wire] at yes no1 no2
          by_cases valid : D.output < n+n
          · let i : Fin (n+n) := ⟨_,valid⟩
            have atI (z : Fin (n+n) → Bool) : (List.ofFn z).getD D.output false = z i := by
              rw [List.getD_eq_getElem _ _ (by simpa)]
              exact List.getElem_ofFn _
            rw [atI] at yes no1 no2
            simp [both,one,two] at yes no1 no2
            exact yes.elim no1 no2
          · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid)] at yes
            contradiction
        rw [actEq] at hN
        simp [Eeq] at hN ⊢
        omega
  have allDiag (i : Fin n) : (i,i) ∈ R := (memR i i).mpr (matched i)
  have r := finish R C (fun i j _ => ⟨allDiag i,allDiag j⟩)
    (fun i j a b hij hab h => noRect i j (π a) (π b) hij (fun e => hab (π.injective e))
      ⟨(memR _ _).mp h.1,(memR _ _).mp h.2.1,(memR _ _).mp h.2.2.1,(memR _ _).mp h.2.2.2⟩) hao (by
        intro z
        rw [computes]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨i,l,hil,hi,hl⟩
          refine ⟨i,π.symm l,(memR _ _).mpr (by simpa using hil),hi,?_⟩
          simpa [v] using hl
        · rintro ⟨i,j,hij,hi,hj⟩
          exact ⟨i,π j,(memR _ _).mp hij,hi,hj⟩) (by
      intro all
      exfalso
      rcases postedLeaf with ⟨p,hp⟩ | ⟨l,hl⟩
      · obtain ⟨j,hj,hpj⟩ := (all p (allDiag p)).1
        exact hj (π.injective (hp _ ((memR _ _).mp hpj)))
      · obtain ⟨i,hi,hil⟩ := (all (π.symm l) (allDiag _)).2
        exact hi (π.injective (by simpa using hl i (by simpa using (memR _ _).mp hil))) )
  have hact : active R = Finset.univ := by ext i; simp [active,allDiag]
  rw [hact,Finset.card_univ,Fintype.card_fin] at r
  simpa [R] using r
