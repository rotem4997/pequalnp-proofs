import PEqualNP.Defs

-- A cut after fourteen gates supplies at most thirteen signals to the final twelve gates.
theorem PEqualNP.Outside.R_meta_3004_120 :
  (let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
    ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
  let cover := fun (K : List ℕ) (q t : ℕ) => ∀ i : ℕ, ∃ j : ℕ,
    q.testBit j = true ∧ t.testBit j = t.testBit i ∧ ∀ a ∈ K,
      (if t.testBit i then (a.testBit j = true → a.testBit i = true)
       else (a.testBit i = true → a.testBit j = true))
  ∀ (K : List ℕ) (q t : ℕ) (U : List ℕ), cover K q t →
    let B := K.map (fun a => a &&& q)
    legal B U → t &&& q ∈ B ++ U → ∃ V : List ℕ, V.length ≤ U.length ∧ legal K V ∧ t ∈ K ++ V) →
  (let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
    ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
  ∀ (A F K V : List ℕ) (t : ℕ), t ∉ A → legal A F →
    (∀ k ∈ K, k ∈ A ++ F) → legal K V → t ∈ K ++ V →
    ∃ W : List ℕ, W.length ≤ F.length + V.length ∧ W.Nodup ∧ (∀ w ∈ W, w ∉ A) ∧ t ∈ W ∧ legal A W) →
  (let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
    ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
  let cover := fun (K : List ℕ) (q t : ℕ) => ∀ i : ℕ, ∃ j : ℕ,
    q.testBit j = true ∧ t.testBit j = t.testBit i ∧ ∀ a ∈ K,
      (if t.testBit i then (a.testBit j = true → a.testBit i = true)
       else (a.testBit i = true → a.testBit j = true))
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  ∃ (F K : List ℕ) (q : ℕ) (U : List ℕ),
    F.length ≤ 14 ∧ K.length ≤ 13 ∧ U.length ≤ 12 ∧ legal A F ∧ (∀ k ∈ K, k ∈ A ++ F) ∧
    cover K q 2097151 ∧ legal (K.map (fun a => a &&& q)) U ∧
    2097151 &&& q ∈ K.map (fun a => a &&& q) ++ U) →
  (have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5) := by
  intro lift glue cut
  dsimp only at cut ⊢
  obtain ⟨F,K,q,U,frontBound,_,backBound,front,ports,cover,back,contains⟩ := cut
  obtain ⟨V,small,leg,goal⟩ := lift K q 2097151 U cover back contains
  obtain ⟨W,len,distinct,fresh,target,alg⟩ := glue _ F K V 2097151 (by decide) front ports leg goal
  exact ⟨W, by omega, distinct, fresh, target, alg⟩
