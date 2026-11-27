import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import PEqualNP.Defs

-- A pair records required and permitted one-bits. Reconverging consumers can
-- share a wire whenever the accumulated lower and upper requirements agree.
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_4614_717
    (compile : let sub := fun (x y : ℕ) => x &&& y = x
      let fits := fun (z : ℕ × ℕ) (x : ℕ) => sub z.1 x ∧ sub x z.2
      let compatible := fun (z a b : ℕ × ℕ) =>
        (sub z.1 (a.1 &&& b.1) ∧ sub (a.2 &&& b.2) z.2) ∨
        (sub z.1 (a.1 ||| b.1) ∧ sub (a.2 ||| b.2) z.2)
      let program := fun (A S : List (ℕ × ℕ)) => ∀ i : Fin S.length,
        ∃ a ∈ A ++ S.take i.val, ∃ b ∈ A ++ S.take i.val, compatible (S.get i) a b
      let legal := fun (A S : List ℕ) => ∀ i : Fin S.length,
        ∃ a ∈ A ++ S.take i.val, ∃ b ∈ A ++ S.take i.val,
          S.get i = a &&& b ∨ S.get i = a ||| b
      ∀ (A : List (ℕ × ℕ)) (B : List ℕ) (S : List (ℕ × ℕ)),
      (∀ z ∈ A, ∃ x ∈ B, fits z x) → program A S →
      ∃ T : List ℕ, T.length = S.length ∧ legal B T ∧ ∀ z ∈ A ++ S, ∃ x ∈ B ++ T, fits z x)
    (padding : ∀ (L : List ℕ) (t : ℕ), ∃ m : ℕ, t &&& m = t ∧ (∀ a ∈ L, a &&& m = a) ∧
      ∀ j : ℕ, ∃ k : ℕ, m.testBit k = true ∧ t.testBit k = t.testBit j ∧
        ∀ a ∈ L, a.testBit k = a.testBit j)
    (synthesize : let sub := fun (x y : ℕ) => x &&& y = x
      let compatible := fun (z a b : ℕ × ℕ) =>
        (sub z.1 (a.1 &&& b.1) ∧ sub (a.2 &&& b.2) z.2) ∨
        (sub z.1 (a.1 ||| b.1) ∧ sub (a.2 ||| b.2) z.2)
      let program := fun (A S : List (ℕ × ℕ)) => ∀ i : Fin S.length,
        ∃ a ∈ A ++ S.take i.val, ∃ b ∈ A ++ S.take i.val, compatible (S.get i) a b
      let A := ([(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] : List ℕ).map (fun x => (x,x))
      ∃ P K S : List (ℕ × ℕ), P.length ≤ 14 ∧ K.length ≤ 13 ∧ S.length ≤ 12 ∧
        program A P ∧ (∀ z ∈ K, z ∈ A ++ P) ∧ program K S ∧
        (2097151,2097151) ∈ K ++ S) :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; have x3 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x4 : List ℕ) (x5 : List ℕ) (x6 : ℕ) (x7 : List ℕ), x4.length ≤ (14 : ℕ) ∧ x5.length ≤ (13 : ℕ) ∧ x7.length ≤ (12 : ℕ) ∧ x1 x3 x4 ∧ (∀ x8 ∈ x5, x8 ∈ x3 ++ x4) ∧ x2 x5 x6 (2097151 : ℕ) ∧ x1 (List.map (fun (x8 : ℕ) => x8 &&& x6) x5) x7 ∧ (2097151 : ℕ) &&& x6 ∈ List.map (fun (x8 : ℕ) => x8 &&& x6) x5 ++ x7 := by
  classical
  let A : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]
  let box := fun x : ℕ => (x,x)
  obtain ⟨P,K,S,hp,hk,hs,preOK,cut,tail,hit⟩ := synthesize
  obtain ⟨U,hu,legalU,lookup⟩ := compile (A.map box) A P (by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact ⟨x,hx,Nat.and_self _,Nat.and_self _⟩) preOK
  let pick (z : ℕ × ℕ) := if h : ∃ x ∈ A ++ U, z.1 &&& x = z.1 ∧ x &&& z.2 = x
    then h.choose else 0
  have chosen (z) (hz : z ∈ K) : pick z ∈ A ++ U ∧
      z.1 &&& pick z = z.1 ∧ pick z &&& z.2 = pick z := by
    have ex := lookup z (cut z hz)
    simpa only [pick,dif_pos ex] using ex.choose_spec
  let B := K.map pick
  obtain ⟨V,hv,legalV,seen⟩ := compile K B S (by
    intro z hz
    exact ⟨pick z,List.mem_map.mpr ⟨z,hz,rfl⟩,(chosen z hz).2⟩) tail
  obtain ⟨v,mem,lo,hi⟩ := seen _ hit
  change 2097151 &&& v = 2097151 at lo
  change v &&& 2097151 = v at hi
  rw [Nat.and_comm] at hi
  have eq : v = 2097151 := hi.symm.trans lo
  subst v
  obtain ⟨m,mt,fixed,rep⟩ := padding (B ++ V) 2097151
  have ident : B.map (fun a => a &&& m) = B := List.map_congr_left (fun a ha => fixed a (List.mem_append_left _ ha)) |>.trans (by simp)
  refine ⟨U,B,m,V,hu.le.trans hp,?_,hv.le.trans hs,legalU,?_,?_,?_,?_⟩
  · simpa [B] using hk
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    exact (chosen z hz).1
  · intro j
    obtain ⟨k,hm,ht,agree⟩ := rep j
    refine ⟨k,hm,ht,?_⟩
    intro a ha
    rw [agree a (List.mem_append_left _ ha)]
    split <;> exact id
  · rwa [ident]
  · rwa [ident,mt]
