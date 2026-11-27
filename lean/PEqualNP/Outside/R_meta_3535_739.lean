import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3535_739
    (program : let run := fun (b : List Nat) (p : List (Bool × Nat × Nat)) (o : Nat) =>
      let d := b.headD 0;
      (p.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => let r := fun k => w.getD k d;
                            w ++ [if g.1 then r g.2.1 ||| r g.2.2 else r g.2.1 &&& r g.2.2]) b).getD o d;
    let b : List Nat := [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480, 82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200, 176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591];
    ∃ p : List (Bool × Nat × Nat), p.length ≤ 22 ∧ ∃ o : Nat, run b p o = 262143)
    (transport : let run := fun (b : List Nat) (p : List (Bool × Nat × Nat)) (o : Nat) =>
      let d := b.headD 0;
      (p.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => let r := fun k => w.getD k d;
                            w ++ [if g.1 then r g.2.1 ||| r g.2.2 else r g.2.1 &&& r g.2.2]) b).getD o d;
    let a : List Nat := [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480, 82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200, 176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591];
    let b : List Nat := [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407];
    ∀ (p : List (Bool × Nat × Nat)) (o : Nat), run a p o = 262143 → run b p o ||| 7 = 2097151) : have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (22 : ℕ) ∧ (∃ x3 ∈ x1 ++ x2, x3 ||| (7 : ℕ) = (2097151 : ℕ)) ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  intro original
  let b : List Nat := [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407]
  let step (d : Nat) (w : List Nat) (g : Bool × Nat × Nat) :=
    let r (i : Nat) := w.getD i d
    w ++ [if g.1 then r g.2.1 ||| r g.2.2 else r g.2.1 &&& r g.2.2]
  have readMem (w : List Nat) (d i : Nat) (hd : d ∈ w) : w.getD i d ∈ w := by
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem ..
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)] using hd
  have replay (p : List (Bool × Nat × Nat)) (w : List Nat) (d : Nat) (hd : d ∈ w) :
      ∃ xs : List Nat, p.foldl (step d) w = w ++ xs ∧ xs.length = p.length ∧
        ∀ i : Fin xs.length, ∃ x ∈ w ++ xs.take i.val, ∃ y ∈ w ++ xs.take i.val,
          xs.get i = x &&& y ∨ xs.get i = x ||| y := by
    induction p generalizing w with
    | nil =>
      exact ⟨[], by simp, rfl, fun i => Fin.elim0 i⟩
    | cons g p ih =>
      let x := w.getD g.2.1 d
      let y := w.getD g.2.2 d
      let z := if g.1 then x ||| y else x &&& y
      obtain ⟨xs, hw, hl, hp⟩ := ih (w ++ [z]) (by simp [hd])
      refine ⟨z :: xs, ?_, by simp [hl], ?_⟩
      · change p.foldl (step d) (w ++ [z]) = _
        simpa [List.append_assoc] using hw
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · refine ⟨x, by simpa [x] using readMem w d g.2.1 hd, y, by simpa [y] using readMem w d g.2.2 hd, ?_⟩
          change z = x &&& y ∨ z = x ||| y
          cases h : g.1 <;> simp [z,h]
        · simpa [List.append_assoc] using hp j
  obtain ⟨p, hlen, o, hit⟩ := program
  have transported := transport p o hit
  change (p.foldl (step (b.headD 0)) b).getD o (b.headD 0) ||| 7 = 2097151 at transported
  have hd : b.headD 0 ∈ b := by decide +kernel
  obtain ⟨xs, hw, hl, hp⟩ := replay p b (b.headD 0) hd
  rw [hw] at transported
  have rel : b ⊆ original := by decide +kernel
  have includeList (s : List Nat) : b ++ s ⊆ original ++ s := by
    intro v hv
    exact List.mem_append.mpr ((List.mem_append.mp hv).imp (fun h => rel h) id)
  refine ⟨xs, hl ▸ hlen, ⟨_, includeList xs (readMem (b ++ xs) (b.headD 0) o (List.mem_append_left _ hd)), transported⟩, ?_⟩
  intro j
  obtain ⟨x,hx,y,hy,eq⟩ := hp j
  exact ⟨x, includeList _ hx, y, includeList _ hy, eq⟩
