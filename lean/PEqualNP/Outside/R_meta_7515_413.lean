import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_7515_413 :
    (∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = GateOp.or →
      min (opnd C 0 0) (opnd C 0 1) = 0 → max (opnd C 0 0) (opnd C 0 1) = 7 →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∃ t : Bool, lineSingle C 14 (fun w => w == if t then 7 else 0) 0 7 = true) →
    (∀ (a b : Fin 14) (D : Circuit), a ≠ b →
      Nat.testBit 365118556550 (14 * min a.val b.val + max a.val b.val) = true →
      ¬ (min a.val b.val = 0 ∧ max a.val b.val = 7) →
      D.size ≤ 26 → IsAO2 15 D → (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x ++ [x a || x b]) = true ↔ (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∃ t : Bool, (List.getD
        (linearParts D
          (fun w => w == (if t then 7 else 0) ||
            (w == 14 && (a.val == (if t then 7 else 0) || b.val == (if t then 7 else 0))))
          ((List.range 14).map (fun i => i == 0 || i == 7) ++
             [(a.val == 0 || a.val == 7) || (b.val == 0 || b.val == 7)]))
          D.output (false, false)).2 = true) →

    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               ∃ (x8 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x8 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true) := by
  intro onPair tail C hsize hshape hne hop hEval selected
  by_cases both : min (opnd C 0 0) (opnd C 0 1) = 0 ∧ max (opnd C 0 0) (opnd C 0 1) = 7
  · exact onPair C hsize hshape hne hop both.1 both.2 hEval
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil =>
    have allTrue := (hEval (fun _ => true)).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
    have outLt : o < 14 := by
      by_contra bad
      change (List.ofFn (fun _ : Fin 14 => true)).getD o false = true at allTrue
      rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt bad)] at allTrue
      contradiction
    let y : Fin 14 → Bool := fun i => decide (i.val = o)
    have outYes : (⟨[],o⟩ : Circuit).eval (List.ofFn y) = true := by
      change (List.ofFn y).getD o false = true
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using outLt),
        List.getElem_ofFn]
      exact decide_eq_true rfl
    obtain ⟨p,l,_,hp,hl⟩ := (hEval y).mp outYes
    have point : p.val = o := by simpa [y] using hp
    have line : l.val + 7 = o := by simpa [y, Nat.add_comm] using hl
    omega
  | cons g gs =>
    have gh : g ∈ (⟨g :: gs, o⟩ : Circuit).gates := List.mem_cons_self
    obtain ⟨a,b,hinputs⟩ := List.length_eq_two.mp (hshape.2.2 g gh)
    have hop' : g.op = GateOp.or := hop
    have hg : g = ⟨GateOp.or, [a,b]⟩ := by
      cases g with
      | mk op ins =>
        change op = GateOp.or at hop'
        change ins = [a,b] at hinputs
        rw [hop', hinputs]
    subst g
    let H : Circuit := ⟨⟨GateOp.or,[a,b]⟩ :: gs,o⟩
    let D : Circuit := ⟨gs,o⟩
    have pos : 0 < H.gates.length := by simp [H]
    have ha : a < 14 := hshape.2.1 0 pos a List.mem_cons_self
    have hb : b < 14 := hshape.2.1 0 pos b (List.mem_cons_of_mem _ List.mem_cons_self)
    let a' : Fin 14 := ⟨a,ha⟩
    let b' : Fin 14 := ⟨b,hb⟩
    have different : a' ≠ b' := fun eq => hne 0 pos (congrArg Fin.val eq)
    have restSize : D.size ≤ 26 := by
      change gs.length + 1 ≤ 27 at hsize
      change gs.length ≤ 26
      omega
    have stat (j : ℕ) : gateAt D j = gateAt H (j+1) := rfl
    have bigger (j : ℕ) (hj : j < D.gates.length) : j+1 < H.gates.length := by
      simpa [D,H] using hj
    have ds : IsAO2 15 D := by
      refine ⟨fun g hg => hshape.1 g (List.mem_cons_of_mem _ hg), ?_,
        fun g hg => hshape.2.2 g (List.mem_cons_of_mem _ hg)⟩
      intro j hj i hi
      rw [stat j] at hi
      have enough := hshape.2.1 (j+1) (bigger j hj) i hi
      omega
    have dDistinct : ∀ j < D.size, opnd D j 0 ≠ opnd D j 1 := by
      intro j hj
      exact hne (j+1) (bigger j hj)
    have evalShift (x : Fin 14 → Bool) :
        H.eval (List.ofFn x) = D.eval (List.ofFn x ++ [x a' || x b']) := by
      unfold H D Circuit.eval Circuit.wires
      rw [List.foldl_cons]
      change ((gs.foldl _ (List.ofFn x ++
        [(List.ofFn x).getD a false || ((List.ofFn x).getD b false || false)])).getD o false) =
         (gs.foldl _ (List.ofFn x ++ [x a' || x b'])).getD o false
      simp only [Bool.or_false]
      have atInput (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
          List.getElem_ofFn]
      rw [atInput a', atInput b']
    have evalD (x : Fin 14 → Bool) :
        D.eval (List.ofFn x ++ [x a' || x b']) = true ↔
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      rw [← evalShift x]
      exact hEval x
    obtain ⟨t, ht⟩ := tail a' b' D different selected both restSize ds dDistinct evalD
    refine ⟨t, ?_⟩
    let base := (List.range 14).map (fun i => i == 0 || i == 7)
    let mark (q : Bool) : ℕ := if q then 7 else 0
    let active (i : ℕ) : Bool := i == 0 || i == 7
    let pack (q : Bool) (i : ℕ) : Bool × Bool :=
      if i == mark q then (false, active i) else (active i, false)
    let initialWires (q : Bool) := (base.zipIdx).map (fun w =>
      if w.2 == mark q then (false,w.1) else (w.1,false))
    have readPrefix : ∀ (q : Bool) (i : Fin 14),
        (initialWires q).getD i.val (false,false) = pack q i.val := by decide +kernel
    have initLaw : ∀ (q e v : Bool),
        ((base ++ [v]).zipIdx).map (fun w =>
          if (w.2 == mark q || (w.2 == 14 && e)) then (false,w.1) else (w.1,false)) =
          initialWires q ++ [if e then (false,v) else (v,false)] := by decide +kernel
    have pairLaw : ∀ (i j : Fin 14) (q : Bool), i ≠ j →
        ¬ (min i.val j.val = 0 ∧ max i.val j.val = 7) →
        ((pack q i.val).1 || (pack q j.val).1, (pack q i.val).2 || (pack q j.val).2) =
        (if (i.val == mark q || j.val == mark q) then
          (false, active i.val || active j.val) else (active i.val || active j.val, false)) := by
      decide +kernel
    have prefixPair :
        (((initialWires t).getD a (false,false)).1 || ((initialWires t).getD b (false,false)).1,
          ((initialWires t).getD a (false,false)).2 || ((initialWires t).getD b (false,false)).2) =
        (if (a == mark t || b == mark t) then (false, active a || active b) else
          (active a || active b, false)) := by
      rw [readPrefix t a', readPrefix t b']
      exact pairLaw a' b' t different both
    change ((linearParts H (fun w => w == mark t) base).getD H.output (false,false)).2 = true
    change ((linearParts D (fun w => w == mark t || (w == 14 && (a == mark t || b == mark t)))
        (base ++ [active a || active b])).getD D.output (false,false)).2 = true at ht
    unfold D at ht
    unfold H
    delta linearParts at ht ⊢
    rw [List.foldl_cons]
    change ((gs.foldl _ (initialWires t ++
      [(((initialWires t).getD a (false,false)).1 ||
           (((initialWires t).getD b (false,false)).1 || false),
        ((initialWires t).getD a (false,false)).2 ||
           (((initialWires t).getD b (false,false)).2 || false))])).getD o (false,false)).2 = true
    rw [Bool.or_false, Bool.or_false, prefixPair]
    rw [initLaw t (a == mark t || b == mark t) (active a || active b)] at ht
    exact ht

