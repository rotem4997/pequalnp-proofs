import Mathlib.Data.List.GetD
import PEqualNP.Defs

-- The posted truth table splits into a fourteen-gate core and a twelve-gate extension.
theorem PEqualNP.Outside.R_meta_4930_1
    (hCore : let I : List (BitVec 58) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]
      let step (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) :=
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      ∃ gs : List (Bool × ℕ × ℕ), gs.length = 14 ∧
        (∀ j : Fin gs.length, let g := gs.getD j.val (false, 0, 0)
          g.2.1 < g.2.2 ∧ g.2.2 < 14 + j.val) ∧
        (gs.foldl step (I)).getD 27 0 = 953051)
    (hShell : let I : List (BitVec 58) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]
      let step (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) :=
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      ∃ gs : List (Bool × ℕ × ℕ), gs.length = 12 ∧
        (∀ j : Fin gs.length, let g := gs.getD j.val (false, 0, 0)
          g.2.1 < g.2.2 ∧ g.2.2 < 15 + j.val) ∧
        (gs.foldl step (I ++ [953051])).getD 26 0 = 2097151) :
    have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∃ (x2 : List (Bool × ℕ × ℕ)), x2.length = (26 : ℕ) ∧ (∀ (x3 : Fin x2.length), (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧ (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑x3) ∧ (2097151 : BitVec (58 : ℕ)) ∈ List.foldl (fun (x3 : List (BitVec (58 : ℕ))) (x4 : Bool × ℕ × ℕ) => x3 ++ [if x4.1 = Bool.true then x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x3.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x3.getD x4.2.2 (0 : BitVec (58 : ℕ))]) x1 x2 := by
  intro I
  let out (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) :=
    if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
      else w.getD g.2.1 0 ||| w.getD g.2.2 0
  let step (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) := w ++ [out w g]
  let law (n : ℕ) (gs : List (Bool × ℕ × ℕ)) :=
    ∀ j : Fin gs.length, let g := gs.getD j.val (false, 0, 0)
      g.2.1 < g.2.2 ∧ g.2.2 < n + j.val
  have inputLen : I.length = 14 := rfl
  obtain ⟨core, coreLen, coreLaw, coreOut⟩ := hCore
  obtain ⟨shell, shellLen, shellLaw, shellOut⟩ := hShell
  change law 14 core at coreLaw
  change law 15 shell at shellLaw
  let W := core.foldl step I
  let U := I ++ [(953051 : BitVec 58)]
  change W.getD 27 0 = 953051 at coreOut
  change (shell.foldl step U).getD 26 0 = 2097151 at shellOut
  let shift (i : ℕ) := if i < 14 then i else i + 13
  let move (g : Bool × ℕ × ℕ) := (g.1, shift g.2.1, shift g.2.2)
  have shiftMono : StrictMono shift := by
    intro a b hab
    dsimp [shift]
    split_ifs <;> omega
  have foldLen : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List (BitVec 58)),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [step]; omega
  have initialRead : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List (BitVec 58)) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i 0 = w.getD i 0 := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have uLen : U.length = 15 := by simp [U, inputLen]
  have wLen : W.length = 28 := by simp [W, foldLen, inputLen, coreLen]
  have agrees : ∀ k < U.length, W.getD (shift k) 0 = U.getD k 0 := by
    intro k hk
    by_cases small : k < 14
    · rw [show shift k = k by simp [shift, small]]
      rw [show W.getD k 0 = I.getD k 0 from initialRead core I k (by simpa [inputLen] using small)]
      exact (List.getD_append _ _ _ _ (by simpa [inputLen] using small)).symm
    · have eq : k = 14 := by omega
      subst k
      change W.getD 27 0 = U.getD 14 0
      rw [coreOut]
      rfl
  have simulate : ∀ (gs : List (Bool × ℕ × ℕ)) (u v : List (BitVec 58)),
      law u.length gs → 14 ≤ u.length → v.length = u.length + 13 →
      (∀ i < u.length, v.getD (shift i) 0 = u.getD i 0) →
      ∀ i < (gs.foldl step u).length,
        ((gs.map move).foldl step v).getD (shift i) 0 = (gs.foldl step u).getD i 0 := by
    intro gs
    induction gs with
    | nil =>
      intro u v valid atLeast lengths cmp i hi
      exact cmp i hi
    | cons g gs ih =>
      intro u v valid atLeast lengths cmp
      have upper : g.2.2 < u.length := by
        have h := (valid ⟨0, by simp⟩).2
        change g.2.2 < u.length + 0 at h
        simpa only [Nat.add_zero] using h
      have lower : g.2.1 < u.length := by
        have h := (valid ⟨0, by simp⟩).1
        change g.2.1 < g.2.2 at h
        exact h.trans upper
      have value : out v (move g) = out u g := by
        simp only [out, move]
        rw [cmp _ lower, cmp _ upper]
      simp only [List.map_cons, List.foldl_cons]
      apply ih (step u g) (step v (move g))
      · intro j
        have h := valid ⟨j.val + 1, by simpa using Nat.succ_lt_succ j.isLt⟩
        change (gs.getD j.val (false, 0, 0)).2.1 < (gs.getD j.val (false, 0, 0)).2.2 ∧
          (gs.getD j.val (false, 0, 0)).2.2 < u.length + (j.val + 1) at h
        simpa [law, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [step]; omega
      · simp [step]; omega
      · intro i hi
        change (v ++ [out v (move g)]).getD (shift i) 0 =
          (u ++ [out u g]).getD i 0
        by_cases earlier : i < u.length
        · have sh : shift i < v.length := by
            have next : shift u.length = v.length := by simp [shift, Nat.not_lt.mpr atLeast, lengths]
            rw [← next]
            exact shiftMono earlier
          rw [List.getD_append _ _ _ _ sh, List.getD_append _ _ _ _ earlier]
          exact cmp i earlier
        · have eq : i = u.length := by
            have hi' : i < u.length + 1 := by simpa [step] using hi
            omega
          subst i
          rw [show shift u.length = v.length by simp [shift, Nat.not_lt.mpr atLeast, lengths]]
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),
            List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, Nat.sub_self, value]
  have combinedLaw : law 14 (core ++ shell.map move) := by
    intro j
    dsimp only
    by_cases h : j.val < core.length
    · rw [List.getD_append _ _ _ _ h]
      exact coreLaw ⟨j.val, h⟩
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
      let k := j.val - core.length
      have hk : k < shell.length := by
        have hj := j.isLt
        simp only [List.length_append, List.length_map] at hj
        dsimp [k]
        omega
      change ((shell.map move).getD k (false, 0, 0)).2.1 <
          ((shell.map move).getD k (false, 0, 0)).2.2 ∧
        ((shell.map move).getD k (false, 0, 0)).2.2 < 14 + j.val
      rw [show (shell.map move).getD k (false, 0, 0) =
        move (shell.getD k (false, 0, 0)) from List.getD_map shell (false, 0, 0) move]
      have hvalid := shellLaw ⟨k, hk⟩
      have endWire : shift (15 + k) = 14 + j.val := by
        have sum : core.length + k = j.val := by
          dsimp [k]
          omega
        simp only [shift, if_neg (by omega : ¬ 15 + k < 14)]
        omega
      exact ⟨shiftMono hvalid.1, endWire ▸ shiftMono hvalid.2⟩
  refine ⟨core ++ shell.map move, by simp [coreLen, shellLen], combinedLaw, ?_⟩
  change (2097151 : BitVec 58) ∈ ((core ++ shell.map move).foldl step I)
  rw [List.foldl_append]
  change (2097151 : BitVec 58) ∈ ((shell.map move).foldl step W)
  have cmp := simulate shell U W (by simpa [uLen] using shellLaw) (by omega) (by omega)
    agrees 26 (by rw [foldLen, uLen, shellLen]; decide)
  rw [shellOut] at cmp
  have hi : shift 26 < ((shell.map move).foldl step W).length := by
    rw [foldLen, List.length_map, wLen, shellLen]
    decide
  rw [List.getD_eq_getElem _ _ hi] at cmp
  rw [← cmp]
  exact List.getElem_mem hi
