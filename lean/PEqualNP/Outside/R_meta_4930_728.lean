import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4930_728
    (search :
      let inputs : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let step := fun (ws : List (BitVec 58)) (g : Bool × ℕ × ℕ) =>
        ws ++ [if g.1 = true then ws.getD g.2.1 0 &&& ws.getD g.2.2 0
          else ws.getD g.2.1 0 ||| ws.getD g.2.2 0]
      ∃ w ∈ [95274182876594239, 284526031944024591, 241600541374316567, 1], ∃ gs : List (Bool × ℕ × ℕ), gs.length = 25 ∧
        (∀ j : Fin gs.length,
          (gs.getD j.val (false, 0, 0)).2.1 < (gs.getD j.val (false, 0, 0)).2.2 ∧
          (gs.getD j.val (false, 0, 0)).2.2 < 15 + j.val) ∧
        (2097151 : BitVec 58) ∈ gs.foldl step (inputs ++ [w]))
    (firstWire : let inputs : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      ∀ w : BitVec 58, w ∈ [95274182876594239, 284526031944024591, 241600541374316567, 1] →
        ∃ g : Bool × ℕ × ℕ, g.2.1 < g.2.2 ∧ g.2.2 < 14 ∧
          (if g.1 = true then inputs.getD g.2.1 0 &&& inputs.getD g.2.2 0
            else inputs.getD g.2.1 0 ||| inputs.getD g.2.2 0) = w) :
    have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∃ (x2 : List (Bool × ℕ × ℕ)), x2.length = (26 : ℕ) ∧ (∀ (x3 : Fin x2.length), (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧ (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑x3) ∧ (2097151 : BitVec (58 : ℕ)) ∈ List.foldl (fun (x3 : List (BitVec (58 : ℕ))) (x4 : Bool × ℕ × ℕ) => x3 ++ [if x4.1 = Bool.true then x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x3.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x3.getD x4.2.2 (0 : BitVec (58 : ℕ))]) x1 x2 := by
  obtain ⟨w, hw, gs, hlen, hvalid, hout⟩ := search
  obtain ⟨g, horder, hbound, hwire⟩ := firstWire w hw
  refine ⟨g :: gs, by simp [hlen], ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using And.intro horder hbound
    · have shift : 14 + (k.val + 1) = 15 + k.val := by omega
      simpa [List.getD_cons_succ, shift] using hvalid k
  · rw [List.foldl_cons, hwire]
    exact hout
