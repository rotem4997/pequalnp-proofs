import Mathlib
import PEqualNP.Defs

-- Work backward from the target. Each step replaces a demanded value with its two operands.
-- The same computed operand must occur twice because the least formula has twenty-seven gates.
theorem PEqualNP.Outside.R_meta_4614_829
    (compile : let adv := fun (U : Finset ℕ) (z : ℕ × ℕ × ℕ) => insert z.2.1 (insert z.2.2 (U.erase z.1))
    let path := fun (U : Finset ℕ) (S : List (ℕ × ℕ × ℕ)) => ∀ i : Fin S.length,
      let z := S.get i
      z.1 ∈ (S.take i.val).foldl adv U ∧ (z.1 = z.2.1 &&& z.2.2 ∨ z.1 = z.2.1 ||| z.2.2)
    let legal := fun (B S : List ℕ) => ∀ i : Fin S.length,
      ∃ a ∈ B ++ S.take i.val, ∃ b ∈ B ++ S.take i.val,
        S.get i = a &&& b ∨ S.get i = a ||| b
    ∀ (B : List ℕ) (U : Finset ℕ) (S : List (ℕ × ℕ × ℕ)),
      path U S → (∀ w ∈ S.foldl adv U, w ∈ B) →
      (S.foldl adv U).card ≤ U.card + S.length ∧
      ∃ G : List ℕ, G.length ≤ S.length ∧ legal B G ∧ ∀ w ∈ U, w ∈ B ++ G)
    (mask : ∀ (B : List ℕ) (t : ℕ), ∃ m : ℕ,
    (∀ j : ℕ, ∃ i : ℕ, m.testBit i = true ∧ t.testBit i = t.testBit j ∧
      ∀ w ∈ B, w.testBit i = w.testBit j) ∧ (∀ w ∈ B, w &&& m = w) ∧ t &&& m = t)
    (search : let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
    let adv := fun (U : Finset ℕ) (z : ℕ × ℕ × ℕ) => insert z.2.1 (insert z.2.2 (U.erase z.1))
    let path := fun (U : Finset ℕ) (S : List (ℕ × ℕ × ℕ)) => ∀ i : Fin S.length,
      let z := S.get i
      z.1 ∈ (S.take i.val).foldl adv U ∧ (z.1 = z.2.1 &&& z.2.2 ∨ z.1 = z.2.1 ||| z.2.2)
    ∃ T P : List (ℕ × ℕ × ℕ),
      let D := T.foldl adv {2097151}
      T.length ≤ 12 ∧ P.length ≤ 14 ∧ path {2097151} T ∧ path D P ∧
      (∀ w ∈ P.foldl adv D, w ∈ A) ∧
      (∀ z ∈ T ++ P, z.2.1 ||| z.2.2 < 2^58 ∧ z.1 ≠ z.2.1 ∧ z.1 ≠ z.2.2) ∧
      ¬ (((T ++ P).flatMap (fun z => [z.2.1,z.2.2])).filter (fun w => w ∉ A)).Nodup)
    : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; have x3 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x4 : List ℕ) (x5 : List ℕ) (x6 : ℕ) (x7 : List ℕ), x4.length ≤ (14 : ℕ) ∧ x5.length ≤ (13 : ℕ) ∧ x7.length ≤ (12 : ℕ) ∧ x1 x3 x4 ∧ (∀ x8 ∈ x5, x8 ∈ x3 ++ x4) ∧ x2 x5 x6 (2097151 : ℕ) ∧ x1 (List.map (fun (x8 : ℕ) => x8 &&& x6) x5) x7 ∧ (2097151 : ℕ) &&& x6 ∈ List.map (fun (x8 : ℕ) => x8 &&& x6) x5 ++ x7 := by
  classical
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let adv := fun (U : Finset ℕ) (z : ℕ × ℕ × ℕ) => insert z.2.1 (insert z.2.2 (U.erase z.1))
  obtain ⟨T,P,ht,hp,traceT,traceP,terminal,_,_⟩ := search
  let D : Finset ℕ := T.foldl adv {2097151}
  obtain ⟨_,F,hF,validF,front⟩ := compile A D P traceP terminal
  obtain ⟨hd,G,hG,validG,output⟩ := compile D.toList {2097151} T traceT (by
    intro w hw; exact Finset.mem_toList.mpr hw)
  obtain ⟨m,rows,mb,mt⟩ := mask D.toList 2097151
  have mapped : D.toList.map (fun w => w &&& m) = D.toList := by
    simpa only [List.map_id_fun,id_eq] using List.map_congr_left (g := id) (fun w hw => mb w hw)
  refine ⟨F,D.toList,m,G,by omega,?_,by omega,validF,?_,?_,?_,?_⟩
  · change D.toList.length ≤ 13
    have h : D.card ≤ 1 + T.length := by simpa [D] using hd
    simpa using (show D.card ≤ 13 by omega)
  · intro w hw; exact front w (Finset.mem_toList.mp hw)
  · intro j
    obtain ⟨i,hi,ht,hh⟩ := rows j
    refine ⟨i,hi,ht,?_⟩
    intro w hw
    rw [hh w hw]
    split <;> exact id
  · simpa only [mapped] using validG
  · rw [mapped,mt]
    exact output _ (Finset.mem_singleton_self _)
