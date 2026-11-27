import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17136_12
    (normalize : ∀ (x1 : ℕ) (x2 : List (BitVec x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → have x5 : List (BitVec x1) → List ℕ → BitVec x1 := fun (x5 : List (BitVec x1)) (x6 : List ℕ) => List.foldr (fun (x7 : ℕ) (x8 : BitVec x1) => x5.getD x7 (0 : BitVec x1) &&& x8) (~~~(0 : BitVec x1)) x6; ∃ (x6 : List (BitVec x1)), x6.length = List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x3.gates ∧ (∀ (x7 : Fin x6.length), have x8 : List (BitVec x1) := (0 : BitVec x1) :: x2 ++ List.take (↑x7) x6; ∃ (x9 : List ℕ) (x10 : List ℕ), (∀ x11 ∈ x9 ++ x10, x11 < x8.length) ∧ x6.get x7 = x5 x8 x9 ||| x5 x8 x10) ∧ ∃ (x7 : List ℕ), (∀ x8 ∈ x7, x8 < ((0 : BitVec x1) :: x2 ++ x6).length) ∧ ∀ (x8 : Fin x1), (x5 ((0 : BitVec x1) :: x2 ++ x6) x7).getLsbD ↑x8 = x3.eval (List.map (fun (x9 : BitVec x1) => x9.getLsbD ↑x8) x2))
    (obstruction : ∀ a ∈ ([[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]] : List (List (BitVec 32))),
      have and : List (BitVec 32) → List ℕ → BitVec 32 := fun w l => l.foldr (fun i y => w.getD i 0 &&& y) (~~~0)
      ∀ s : List (BitVec 32), s.length ≤ 12 →
        (∀ j : Fin s.length, have w := 0 :: a ++ s.take j
          ∃ p q : List ℕ, s.get j = and w p ||| and w q) →
        ∀ l : List ℕ, and (0 :: a ++ s) l ≠ 16383) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (13 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  intro G v C hv hao agree
  by_contra! few

  have mono : PEqualNP.MetaComplexity.Monotone2 C := fun g hg =>
    ⟨by simpa using hao.1 g hg, (hao.2.2 g hg).le⟩

  let A : Fin 4 → List (BitVec 32) := ![[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]]
  let x (i : Fin 4) (k : Fin 32) (j : Fin 11) : Bool := ((A i).getD j.val 0).getLsbD k.val
  let i : Fin 4 := ⟨v.val, hv⟩
  have rows : ∀ j k, (A j).map (fun w => w.getLsbD k.val) = List.ofFn (x j k) := by decide +kernel
  have off : ∀ (j : Fin 4) (k : Fin 32), x j k ⟨j.val, Nat.lt_trans j.isLt (by decide : 4 < 11)⟩ = false := by
    decide +kernel
  have targets : ∀ (j : Fin 4) (k : Fin 32),
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (x j k) = (16383 : BitVec 32).getLsbD k.val := by
    decide +kernel
  have choice : ∀ q : Fin 4, A q ∈ ([[0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752], [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578], [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962], [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]] : List (List (BitVec 32))) := by
    intro q
    fin_cases q <;> simp [A]

  obtain ⟨s, len, steps, l, -, out⟩ := normalize 32 (A i) C mono
  refine obstruction (A i) (choice i) s (len ▸ Nat.le_of_lt_succ few)
    (fun j => Exists.imp (fun _ hp => Exists.imp (fun _ hq => hq.2) hp) (steps j)) l
    (BitVec.eq_of_getLsbD_eq fun r hr => ?_)
  rw [out ⟨r, hr⟩, rows i ⟨r, hr⟩]
  exact (agree _ (off i ⟨r, hr⟩)).trans (targets i ⟨r, hr⟩)
