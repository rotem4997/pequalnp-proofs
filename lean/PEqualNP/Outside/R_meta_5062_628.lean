import PEqualNP.Defs

open PEqualNP.AndCount

set_option maxRecDepth 18000 in
set_option maxHeartbeats 9000000 in
theorem PEqualNP.Outside.R_meta_5062_628 :
    (let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        let R (v : Fin 42) := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
        (∀ v, (R v).card ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → (R p ∪ R l).card ≤ 6) →
        let born (i : Fin C.size) (p l : Fin 42) :=
          (p ∈ C.leftVars i ∧ l ∈ C.rightVars i) ∨ (l ∈ C.leftVars i ∧ p ∈ C.rightVars i)
        (∃ i, born i 0 21 ∧ born i 1 22) → False) →
    (let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat);
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        let R (v : Fin 42) := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
        (∀ v, (R v).card ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → (R p ∪ R l).card ≤ 6) →
        let born (i : Fin C.size) (p l : Fin 42) :=
          (p ∈ C.leftVars i ∧ l ∈ C.rightVars i) ∨ (l ∈ C.leftVars i ∧ p ∈ C.rightVars i)
        (∃ i, born i 0 21 ∧ born i 2 23) → False) →
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → False := by
  intro hOne hTwo
  let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
  let uses (C : AndCountCircuit 42) (v : Fin 42) :=
    Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
  let eligible (C : AndCountCircuit 42) : Prop :=
    C.WellFormed ∧ C.Computes G ∧ C.outVars = ∅ ∧
    (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) ∧ C.size = 20 ∧
    (∀ v, (uses C v).card ≤ 4) ∧
    ∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l → (uses C p ∪ uses C l).card ≤ 6
  let crosses (C : AndCountCircuit 42) (i : Fin C.size) (s : Fin 42 × Fin 42) : Prop :=
    (s.1 ∈ C.leftVars i ∧ s.2 ∈ C.rightVars i) ∨ (s.2 ∈ C.leftVars i ∧ s.1 ∈ C.rightVars i)
  let Bad (q : (Fin 42 × Fin 42) × (Fin 42 × Fin 42)) : Prop :=
    ∃ C, eligible C ∧ ∃ i : Fin C.size, crosses C i q.1 ∧ crosses C i q.2
  let one : (Fin 42 × Fin 42) × (Fin 42 × Fin 42) := ((0,21),(1,22))
  let two : (Fin 42 × Fin 42) × (Fin 42 × Fin 42) := ((0,21),(2,23))
  have noOne : ¬Bad one := by
    rintro ⟨C,⟨hw,he,ho,hd,hs,hv,hp⟩,hi⟩
    exact hOne C hw he ho hd hs hv hp hi
  have noTwo : ¬Bad two := by
    rintro ⟨C,⟨hw,he,ho,hd,hs,hv,hp⟩,hi⟩
    exact hTwo C hw he ho hd hs hv hp hi
  have swapBad (q) : Bad q.swap → Bad q := by
    rintro ⟨C,hC,i,hf,hg⟩
    exact ⟨C,hC,i,hg,hf⟩
  let flag (i : Fin 21) : Fin 42 × Fin 42 :=
    (Fin.ofNat 42 i.val,Fin.ofNat 42 (21+i.val))
  let related (a b : Fin 42) := decide ((a.val < 21 ∧ 21 ≤ b.val ∧
    (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∨
    (b.val < 21 ∧ 21 ≤ a.val ∧ (a.val + 21 - b.val) % 21 ∈ ([0,5,7,17,20] : List Nat)))
  have adjSpec (a b : Fin 42) : G.Adj a b ↔ related a b = true := by
    rw [SimpleGraph.fromRel_adj]
    dsimp only [related]
    rw [decide_eq_true_eq]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_,h⟩
      rintro rfl
      rcases h with ⟨ha,hb,_⟩ | ⟨ha,hb,_⟩ <;> omega
  have flagsAdj : ∀ i : Fin 21, related (flag i).1 (flag i).2 = true := by decide
  have birth (C : AndCountCircuit 42) (he : C.Computes G) (ho : C.outVars = ∅)
      (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (a b : Fin 42) (hab : G.Adj a b) :
      ∃ i, crosses C i (a,b) := by
    let U : Finset (Fin 42) := {a,b}
    have on : C.eval U = true := (he U).mpr
      ⟨a,by simp [U],b,by simp [U],hab⟩
    change decide ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) = true at on
    have hop := decide_eq_true_eq.mp on
    simp only [ho,Finset.notMem_empty,false_and,exists_false,false_or] at hop
    obtain ⟨j,_,hj⟩ := hop
    have raw (d : Nat) (i : Fin C.size) (h : C.gateValFuel U d i = true) : ∃ z, crosses C z (a,b) := by
      induction d generalizing i with
      | zero => exact Bool.noConfusion h
      | succ d ih =>
        change (decide ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ z ∈ C.leftGates i, z < i ∧ C.gateValFuel U d z = true) &&
          decide ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ z ∈ C.rightGates i, z < i ∧ C.gateValFuel U d z = true)) = true at h
        obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
        rcases decide_eq_true_eq.mp hl with ⟨u,hu,huU⟩ | ⟨z,_,_,hz⟩
        · rcases decide_eq_true_eq.mp hr with ⟨v,hv,hvU⟩ | ⟨z,_,_,hz⟩
          · simp only [U,Finset.mem_insert,Finset.mem_singleton] at huU hvU
            refine ⟨i,?_⟩
            rcases huU with rfl | rfl <;> rcases hvU with h | h
            · exact (Finset.disjoint_left.mp (hd i) hu (h ▸ hv)).elim
            · exact Or.inl ⟨hu,h ▸ hv⟩
            · exact Or.inr ⟨hu,h ▸ hv⟩
            · exact (Finset.disjoint_left.mp (hd i) hu (h ▸ hv)).elim
          · exact ih z hz
        · exact ih z hz
    exact raw C.size j hj
  let relabelAcross (C : AndCountCircuit 42)
      (f : Finset (Fin 42) → Finset (Fin 42)) : AndCountCircuit 42 :=
    ⟨C.size, fun i => f (C.leftVars i), C.leftGates, fun i => f (C.rightVars i),
      C.rightGates, f C.outVars, C.outGates⟩

  let bareHit {s : ℕ} (U B : Finset (Fin s)) : Prop := ∃ v ∈ B, v ∈ U

  have eval_across (C : AndCountCircuit 42) (f : Finset (Fin 42) → Finset (Fin 42))
      (U : Finset (Fin 42)) (V : Finset (Fin 42))
      (l : ∀ i, bareHit U (f (C.leftVars i)) ↔ bareHit V (C.leftVars i))
      (r : ∀ i, bareHit U (f (C.rightVars i)) ↔ bareHit V (C.rightVars i))
      (o : bareHit U (f C.outVars) ↔ bareHit V C.outVars) :
      (relabelAcross C f).eval U = C.eval V := by
    have fuel (d : ℕ) (i : Fin C.size) :
        (relabelAcross C f).gateValFuel U d i = C.gateValFuel V d i := by
      induction d generalizing i with
      | zero => rfl
      | succ d ih =>
        change
          (AndCountCircuit.sideTrue U (f (C.leftVars i)) (C.leftGates i) i
            ((relabelAcross C f).gateValFuel U d) &&
          AndCountCircuit.sideTrue U (f (C.rightVars i)) (C.rightGates i) i
            ((relabelAcross C f).gateValFuel U d)) = _
        rw [show (relabelAcross C f).gateValFuel U d = C.gateValFuel V d from funext ih]
        have side (B : Finset (Fin 42)) (S : Finset (Fin C.size))
            (h : bareHit U (f B) ↔ bareHit V B) :
            AndCountCircuit.sideTrue U (f B) S i (C.gateValFuel V d) =
            AndCountCircuit.sideTrue V B S i (C.gateValFuel V d) := by
          unfold AndCountCircuit.sideTrue
          exact decide_eq_decide.mpr (or_congr h Iff.rfl)
        rw [side _ _ (l i), side _ _ (r i)]
        rfl
    unfold AndCountCircuit.eval
    rw [decide_eq_decide]
    change (bareHit U (f C.outVars) ∨
        ∃ j ∈ C.outGates, (relabelAcross C f).gateValFuel U C.size j = true) ↔
      (bareHit V C.outVars ∨ ∃ j ∈ C.outGates, C.gateValFuel V C.size j = true)
    exact or_congr o (by simp only [fuel])

  let transport (C : AndCountCircuit 42) (e : Fin 42 ≃ Fin 42) : AndCountCircuit 42 :=
    relabelAcross C (fun B => B.map e.toEmbedding)

  have transport_size (C : AndCountCircuit 42) (e : Fin 42 ≃ Fin 42) :
      (transport C e).size = C.size := rfl

  have transport_wf (C : AndCountCircuit 42) (e : Fin 42 ≃ Fin 42) (wf : C.WellFormed) :
      (transport C e).WellFormed := wf

  have hit_transport (e : Fin 42 ≃ Fin 42) (U : Finset (Fin 42)) (B : Finset (Fin 42)) :
      bareHit U (B.map e.toEmbedding) ↔ bareHit (U.map e.symm.toEmbedding) B := by
    constructor
    · rintro ⟨v, vb, vu⟩
      exact ⟨e.symm v, Finset.mem_map_equiv.mp vb,
        Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using vu)⟩
    · rintro ⟨v, vb, vu⟩
      exact ⟨e v, Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_apply_apply] using vb),
        by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using vu⟩

  have transport_eval (C : AndCountCircuit 42) (e : Fin 42 ≃ Fin 42) (U : Finset (Fin 42)) :
      (transport C e).eval U = C.eval (U.map e.symm.toEmbedding) :=
    eval_across C (fun B => B.map e.toEmbedding) U _ (fun _ => hit_transport e U _)
      (fun _ => hit_transport e U _) (hit_transport e U _)

  have transport_computes (C : AndCountCircuit 42)
      (G : SimpleGraph (Fin 42)) (H : SimpleGraph (Fin 42)) (e : Fin 42 ≃ Fin 42)
      (adj : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b) (comp : C.Computes G) :
      (transport C e).Computes H := by
    intro U
    rw [transport_eval, comp (U.map e.symm.toEmbedding)]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨e a, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using ha,
        e b, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hb, (adj a b).mpr hab⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have ha' : e.symm a ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨a, ha, rfl⟩
      have hb' : e.symm b ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨b, hb, rfl⟩
      exact ⟨e.symm a, ha', e.symm b, hb', (adj _ _).mp
        (by simpa only [Equiv.apply_symm_apply] using hab)⟩
  let generators : List (List (Fin 42)) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 21], [0, 3, 8, 10, 20, 9, 19, 7, 11, 5, 4, 2, 14, 18, 13, 12, 15, 1, 16, 6, 17, 41, 29, 36, 27, 37, 26, 24, 28, 31, 25, 30, 40, 35, 39, 33, 32, 22, 21, 23, 34, 38]]
  let perm (t : Fin 2) (i : Fin 42) := (generators.getD t.val []).getD i.val 0
  have bij (t : Fin 2) : Function.Bijective (perm t) := by
    have h : ∀ (s : Fin 2) (a b : Fin 42), perm s a = perm s b → a = b := by decide
    exact Finite.injective_iff_bijective.mp (h t)
  let E (t : Fin 2) : Fin 42 ≃ Fin 42 := Equiv.ofBijective (perm t) (bij t)
  have respects : ∀ (t : Fin 2) (a b : Fin 42), related (perm t a) (perm t b) = related a b := by decide
  have sides : ∀ (t : Fin 2) (a : Fin 42), (perm t a).val < 21 ↔ a.val < 21 := by decide
  let move (t : Fin 2) (q : (Fin 42 × Fin 42) × (Fin 42 × Fin 42)) :=
    ((perm t q.1.1,perm t q.1.2),(perm t q.2.1,perm t q.2.2))
  have moveBad (t q) (bad : Bad q) : Bad (move t q) := by
    obtain ⟨C,⟨hw,he,ho,hd,hs,hv,hp⟩,i,h₁,h₂⟩ := bad
    let e := E t
    let D := transport C e
    have adj (a b : Fin 42) : G.Adj (e a) (e b) ↔ G.Adj a b := by
      rw [adjSpec,adjSpec]
      exact (respects t a b) ▸ Iff.rfl
    have readUses (v : Fin 42) : uses D (e v) = uses C v := by
      ext j
      simp only [uses,Finset.mem_filter,Finset.mem_univ,true_and]
      change (e v ∈ (C.leftVars j).map e.toEmbedding ∨ e v ∈ (C.rightVars j).map e.toEmbedding) ↔ _
      simp
    have transportCross (s : Fin 42 × Fin 42) (h : crosses C i s) : crosses D i (e s.1,e s.2) := by
      change (_ ∈ (C.leftVars i).map e.toEmbedding ∧ _ ∈ (C.rightVars i).map e.toEmbedding) ∨
        (_ ∈ (C.leftVars i).map e.toEmbedding ∧ _ ∈ (C.rightVars i).map e.toEmbedding)
      simpa only [Finset.mem_map_equiv,Equiv.symm_apply_apply] using h
    refine ⟨D,⟨hw,transport_computes C G G e adj he,?_,?_,hs,?_,?_⟩,i,transportCross _ h₁,transportCross _ h₂⟩
    · change C.outVars.map e.toEmbedding = ∅
      rw [ho,Finset.map_empty]
    · intro j
      change Disjoint ((C.leftVars j).map e.toEmbedding) ((C.rightVars j).map e.toEmbedding)
      exact Finset.disjoint_left.mpr (fun _ hl hr =>
        Finset.disjoint_left.mp (hd j) (Finset.mem_map_equiv.mp hl) (Finset.mem_map_equiv.mp hr))
    · intro v
      obtain ⟨u,rfl⟩ := e.surjective v
      rw [readUses]
      exact hv u
    · intro a b
      obtain ⟨u,rfl⟩ := e.surjective a
      obtain ⟨v,rfl⟩ := e.surjective b
      intro hu hl hn
      rw [readUses,readUses]
      exact hp u v ((sides t u).mp hu)
        (by have h := sides t v; change 21 ≤ (perm t v).val at hl; omega) (fun h => hn ((adj u v).mpr h))
  let words : List (List (Fin 2)) := [[], [], [], [0, 0, 1, 0, 1, 0, 1, 0, 0, 1], [1, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0], [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1], [1, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0, 1, 1, 1, 0], [1, 1, 0, 0, 0, 1, 1, 1, 0, 0], [1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0], [0]]
  let path (a b : Fin 21) : List (Fin 2) :=
    List.replicate ((21-a.val)%21) 0 ++ words.getD ((b.val+21-a.val)%21) []
  let dest (a b : Fin 21) := (path a b).foldl (fun q t => move t q) (flag a,flag b)
  have check : ∀ a b : Fin 21, a ≠ b → dest a b = one ∨ dest a b = two ∨ dest a b = one.swap ∨ dest a b = two.swap := by decide
  have walkBad (w : List (Fin 2)) (q) (h : Bad q) : Bad (w.foldl (fun z t => move t z) q) := by
    induction w generalizing q with
    | nil => exact h
    | cons t w ih => exact ih _ (moveBad t q h)
  dsimp only
  intro C hw he ho _ hd hs hcap hpair
  have hc : eligible C := by
    refine ⟨hw,he,ho,hd,hs,?_,?_⟩
    · intro v
      have h := hcap v
      rw [← Set.ncard_coe_finset] at *
      convert h using 2
      ext i
      simp [uses]
    · intro a b ha hb hn
      have h := hpair a b ha hb hn
      rw [← Set.ncard_coe_finset] at *
      convert h using 2
      ext i
      simp [uses]
      tauto
  choose gate hgate using fun t : Fin 21 => birth C he ho hd (flag t).1 (flag t).2 ((adjSpec _ _).mpr (flagsAdj t))
  obtain ⟨a,_,b,_,hab,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin 21))) (t := (Finset.univ : Finset (Fin C.size))) (f := gate)
    (by simp [hs]) (fun _ _ => Finset.mem_univ _)
  have bad : Bad (flag a,flag b) := ⟨C,hc,gate a,hgate a,heq ▸ hgate b⟩
  have finalBad : Bad (dest a b) := walkBad (path a b) _ bad
  rcases check a b hab with h | h | h | h
  · exact noOne (h ▸ finalBad)
  · exact noTwo (h ▸ finalBad)
  · exact noOne (swapBad one (h ▸ finalBad))
  · exact noTwo (swapBad two (h ▸ finalBad))
