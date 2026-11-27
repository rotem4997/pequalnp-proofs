import PEqualNP.Defs

-- Removing point 0 leaves 18 edge rows and 30 maximal independent rows.
-- A discarded independent row is coordinatewise below a retained one on
-- every remaining input. AND and OR preserve this order through both stages.
theorem PEqualNP.Outside.R_meta_4532_732
    (liftProgram : let build := fun (s l : List ℕ) => ∀ i : Fin l.length, ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = a &&& b ∨ l.get i = a ||| b;
    ∀ (s t : List ℕ) (r : ℕ → ℕ → Prop),
      (∀ a ∈ s, ∃ b ∈ t, r a b) →
      (∀ a b c d, r a c → r b d → r (a &&& b) (c &&& d) ∧ r (a ||| b) (c ||| d)) →
      ∀ l : List ℕ, build s l → ∃ m : List ℕ, m.length = l.length ∧ build t m ∧ ∀ a ∈ l, ∃ b ∈ m, r a b)
    (decode : let builds := fun (S L : List Nat) => ∀ i : Fin L.length,
      ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val, L.get i = a &&& b ∨ L.get i = a ||| b
    ∀ (W : Finset Nat) (ops : List (Bool × Nat × Nat)), ∃ t : List Nat,
      t.length ≤ ops.length ∧ builds W.toList t ∧
      ∀ z ∈ ops.foldl (fun (A : Finset Nat) (g : Bool × Nat × Nat) =>
      let a := g.2.1
      let b := g.2.2
      if a ∈ A ∧ b ∈ A ∧ a ≠ b then
        insert (if g.1 then a ||| b else a &&& b)
          (if W.card = 8 then (A.erase a).erase b else A)
      else A) W, z ∈ W.toList ++ t)
    (frontierSearch : let s : List ℕ := [917681471495, 14877982776, 31886295695808, 257731333632, 42884715540480, 82789891276800, 248671168364609, 198670308900872, 158476001153026, 238332533547520, 176488259388544, 212188564308240, 280375465084964, 271282175770697, 280357743665737];
    let build := fun (s l : List ℕ) => ∀ i : Fin l.length, ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = a &&& b ∨ l.get i = a ||| b;
    ∃ a : List ℕ, a.length ≤ 15 ∧ build s a ∧
      ∃ W : Finset Nat, W.card ≤ 8 ∧ (∀ v ∈ W, v ∈ s ++ a) ∧
        ∃ ops : List (Bool × Nat × Nat), ops.length ≤ 7 ∧
          (262143 : Nat) ∈ ops.foldl (fun (A : Finset Nat) (g : Bool × Nat × Nat) =>
      let a := g.2.1
      let b := g.2.2
      if a ∈ A ∧ b ∈ A ∧ a ≠ b then
        insert (if g.1 then a ||| b else a &&& b)
          (if W.card = 8 then (A.erase a).erase b else A)
      else A) W) : have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), ∃ x5 ∈ x2 ++ List.take (↑x4) x3, ∃ x6 ∈ x2 ++ List.take (↑x4) x3, x3.get x4 = x5 &&& x6 ∨ x3.get x4 = x5 ||| x6; ∃ (x3 : List ℕ), x3.length ≤ (15 : ℕ) ∧ x2 x1 x3 ∧ ∃ (x4 : List ℕ) (x5 : List ℕ), x4.length ≤ (8 : ℕ) ∧ (∀ x6 ∈ x4, x6 ∈ x1 ++ x3) ∧ x5.length ≤ (7 : ℕ) ∧ x2 x4 x5 ∧ ∃ x6 ∈ x4 ++ x5, x6 ||| (7 : ℕ) = (2097151 : ℕ) := by
  let s : List ℕ := [917681471495, 14877982776, 31886295695808, 257731333632, 42884715540480, 82789891276800, 248671168364609, 198670308900872, 158476001153026, 238332533547520, 176488259388544, 212188564308240, 280375465084964, 271282175770697, 280357743665737]
  let t : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407, 7]
  let idx : List ℕ := [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 32, 33, 34, 35, 36, 37, 37, 38, 39, 39, 40, 41, 42, 44, 43, 44, 45, 45, 46, 46, 47, 47]
  let build := fun (s l : List ℕ) => ∀ i : Fin l.length, ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = a &&& b ∨ l.get i = a ||| b
  let r := fun (a b : ℕ) => b < 2^58 ∧
    (∀ i : Fin 58, 3 ≤ i.val → i.val < 21 → b.testBit i.val = a.testBit (idx.getD i.val 0)) ∧
    (∀ i : Fin 58, 21 ≤ i.val → b.testBit i.val = true → a.testBit (idx.getD i.val 0) = true)
  have start : ∀ a ∈ s, ∃ b ∈ t, r a b := by decide +kernel
  have ops : ∀ a b c d, r a c → r b d → r (a &&& b) (c &&& d) ∧ r (a ||| b) (c ||| d) := by
    intro a b c d hc hd
    constructor
    · refine ⟨Nat.and_lt_two_pow _ hd.1,?_,?_⟩
      · intro i h3 h21
        simp only [Nat.testBit_and,hc.2.1 i h3 h21,hd.2.1 i h3 h21]
      · intro i h21 h
        simp only [Nat.testBit_and,Bool.and_eq_true] at h ⊢
        exact ⟨hc.2.2 i h21 h.1,hd.2.2 i h21 h.2⟩
    · refine ⟨Nat.or_lt_two_pow hc.1 hd.1,?_,?_⟩
      · intro i h3 h21
        simp only [Nat.testBit_or,hc.2.1 i h3 h21,hd.2.1 i h3 h21]
      · intro i h21 h
        simp only [Nat.testBit_or,Bool.or_eq_true] at h ⊢
        exact h.imp (hc.2.2 i h21) (hd.2.2 i h21)
  have output (v : ℕ) (pair : r 262143 v) : v ||| 7 = 2097151 := by
    have positive : ∀ i : Fin 58, 3 ≤ i.val → i.val < 21 →
        (262143 : ℕ).testBit (idx.getD i.val 0) = true := by decide +kernel
    have negative : ∀ i : Fin 58, 21 ≤ i.val →
        (262143 : ℕ).testBit (idx.getD i.val 0) = false := by decide +kernel
    have before : ∀ i : Fin 3, (7 : ℕ).testBit i.val = true ∧ (2097151 : ℕ).testBit i.val = true := by decide +kernel
    have between : ∀ i : Fin 21, (2097151 : ℕ).testBit i.val = true := by decide +kernel
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or]
    by_cases hj : j < 3
    · obtain ⟨a,b⟩ := before ⟨j,hj⟩
      simp [a,b]
    · by_cases h21 : j < 21
      · let i : Fin 58 := ⟨j,by omega⟩
        have yes := (pair.2.1 i (by change 3 ≤ j; omega) h21).trans (positive i (by change 3 ≤ j; omega) h21)
        change v.testBit j = true at yes
        have yes' := between ⟨j,h21⟩
        change (2097151:ℕ).testBit j = true at yes'
        simp [yes,yes']
      · have pw : 2^21 ≤ (2:ℕ)^j := Nat.pow_le_pow_right (by decide) (by omega)
        have b7 : (7:ℕ).testBit j = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 7 < 2^21) pw)
        have bout : (2097151:ℕ).testBit j = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 2097151 < 2^21) pw)
        have bval : v.testBit j = false := by
          by_cases h58 : j < 58
          · let i : Fin 58 := ⟨j,h58⟩
            have no := negative i (by change 21 ≤ j; omega)
            cases hv : v.testBit j with
            | false => rfl
            | true => exact False.elim (Bool.false_ne_true (no.symm.trans (pair.2.2 i (by change 21 ≤ j; omega) hv)))
          · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le pair.1 (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [b7,bval,bout]
  obtain ⟨a,asz,ag,W,wid,available,oplist,limit,hit⟩ := frontierSearch
  obtain ⟨c,clen,cg,reachable⟩ := decode W oplist
  let b := W.toList
  have bsz : b.length ≤ 8 := by simpa [b] using wid
  have bmem : ∀ x ∈ b, x ∈ s ++ a := fun x hx => available x (by simpa [b] using hx)
  have csz := clen.trans limit
  have accepted : 262143 ∈ b ++ c := reachable _ hit
  obtain ⟨a',asz',ag',mapA⟩ := liftProgram s t r start ops a ag
  have env : ∀ x ∈ s ++ a, ∃ y ∈ t ++ a', r x y := by
    intro x member
    rcases List.mem_append.mp member with h | h
    · obtain ⟨y,hy,hr⟩ := start x h
      exact ⟨y,List.mem_append_left _ hy,hr⟩
    · obtain ⟨y,hy,hr⟩ := mapA x h
      exact ⟨y,List.mem_append_right _ hy,hr⟩
  have boundary : ∀ l : List ℕ, (∀ x ∈ l, x ∈ s ++ a) →
      ∃ l' : List ℕ, l'.length = l.length ∧ (∀ y ∈ l', y ∈ t ++ a') ∧ (∀ x ∈ l, ∃ y ∈ l', r x y) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[],rfl,by simp,by simp⟩
    | cons x l ih =>
      intro hl
      obtain ⟨y,hy,hr⟩ := env x (hl _ (by simp))
      obtain ⟨l',len,all,rel⟩ := ih (fun z hz => hl z (by simp [hz]))
      refine ⟨y::l',by simp [len],?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | h
        · exact hy
        · exact all z h
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | h
        · exact ⟨y,by simp,hr⟩
        · obtain ⟨u,hu,hru⟩ := rel z h
          exact ⟨u,by simp [hu],hru⟩
  obtain ⟨b',bsz',bmem',mapB⟩ := boundary b bmem
  obtain ⟨c',csz',cg',mapC⟩ := liftProgram b b' r mapB ops c cg
  refine ⟨a',by omega,ag',b',c',by omega,bmem',by omega,cg',?_⟩
  rcases List.mem_append.mp accepted with h | h
  · obtain ⟨v,hv,hr⟩ := mapB _ h
    exact ⟨v,List.mem_append_left _ hv,output v hr⟩
  · obtain ⟨v,hv,hr⟩ := mapC _ h
    exact ⟨v,List.mem_append_right _ hv,output v hr⟩
