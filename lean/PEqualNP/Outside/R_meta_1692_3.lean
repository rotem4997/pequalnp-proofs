import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Removing the first gate exposes one extra input to the suffix and preserves wire indices.
-- A binary AND of distinct input bits can recognize at most one incident singleton.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1692_3
    (punctured : ∀ (C : Circuit) (m n : Fin 13) (c : Bool), Monotone2 C →
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      (∀ p l : Fin 13, p - l ∈ D → (p ≠ m ∨ l ≠ n) →
        C.eval (P p l ++ [c]) = true) →
      (∀ Q, good Q → C.eval (N Q ++ [c]) = false) →
      63 ≤ C.size)
    (freeOr : ∀ (C : Circuit) (s : List ℕ), s.length ≤ 2 → Monotone2 C →
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
      (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) →
      (∀ Q, good Q → C.eval (extend (N Q)) = false) →
      63 ≤ C.size) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let P (p l : Fin 13) := List.ofFn (fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
  let good (Q : Finset (Fin 13)) := Q.card = 4 ∧
    ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
  have andValue (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have orValue (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
  intro gs out hops hback hp hn
  change ∀ p l : Fin 13, p - l ∈ D → (Circuit.mk gs out).eval (P p l) = true at hp
  change ∀ Q, Q.card = 4 → _ → (Circuit.mk gs out).eval (N Q) = false at hn
  cases gs with
  | nil =>
    have h0 := hp 0 0 (by decide)
    have h1 := hp 1 1 (by decide)
    change (P 0 0).getD out false = true at h0
    change (P 1 1).getD out false = true at h1
    by_cases h : out < 26
    · have disj : ∀ i : Fin 26, ¬ ((P 0 0).getD i.val false = true ∧
          (P 1 1).getD i.val false = true) := by decide
      exact False.elim (disj ⟨out,h⟩ ⟨h0,h1⟩)
    · have hlen : (P 0 0).length ≤ out := by simpa [P] using (Nat.le_of_not_gt h)
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h0
  | cons g gs =>
    let C : Circuit := ⟨gs, out⟩
    let first (x : List Bool) := g.op.eval (g.inputs.map (fun i => x.getD i false))
    have pos : ∀ p l : Fin 13, p - l ∈ D →
        C.eval (P p l ++ [first (P p l)]) = true := hp
    have neg : ∀ Q, good Q → C.eval (N Q ++ [first (N Q)]) = false :=
      fun Q h => hn Q h.1 h.2
    have mono : Monotone2 C := by
      intro k hk
      obtain ⟨op, ar⟩ := hops k (List.mem_cons_of_mem _ hk)
      exact ⟨op, ar⟩
    have back : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < 27 + i.val := by
      intro i w hw
      have h := hback i.succ w hw
      change w < 26 + (i.val + 1) at h
      omega
    have lowerBit (x : List Bool) (v : Bool) :
        C.eval (x ++ [false]) = true → C.eval (x ++ [v]) = true := by
      let R := fun a b : Bool => a = true → b = true
      have readWire {s t : List Bool} (rel : List.Forall₂ R s t) (i : ℕ) :
          R (s.getD i false) (t.getD i false) := by
        induction rel generalizing i with
        | nil => exact id
        | cons head tail ih =>
          cases i with
          | zero => exact head
          | succ i => exact ih i
      have fold (ks : List Gate) (ops : ∀ k ∈ ks, k.op = GateOp.and ∨ k.op = GateOp.or) :
          ∀ s t : List Bool, List.Forall₂ R s t →
            List.Forall₂ R ((Circuit.mk ks 0).wires s) ((Circuit.mk ks 0).wires t) := by
        induction ks with
        | nil => intro s t h; exact h
        | cons k ks ih =>
          intro s t rel
          apply ih (fun g hg => ops g (List.mem_cons_of_mem _ hg))
          apply List.rel_append rel
          apply List.Forall₂.cons _ List.Forall₂.nil
          intro hit
          rcases ops k (by simp) with op | op
          · simp [op, andValue, List.all_map] at hit ⊢
            exact fun j hj => readWire rel j (hit j hj)
          · simp [op, orValue, List.any_map] at hit ⊢
            obtain ⟨i, hi, hval⟩ := hit
            exact ⟨i, hi, readWire rel i hval⟩
      have same : List.Forall₂ R x x := List.forall₂_of_length_eq_of_get rfl fun _ _ _ => id
      have start : List.Forall₂ R (x ++ [false]) (x ++ [v]) :=
        List.rel_append same (.cons (by intro impossible; contradiction) .nil)
      exact readWire (fold gs (fun k hk => (mono k hk).1) _ _ start) out
    have reduceOr (s : List ℕ) (hs : s.length ≤ 2)
        (he : ∀ x, first x = s.any (fun i => x.getD i false)) : 63 ≤ C.size := by
      apply freeOr C s hs mono back
      · intro p l hi
        simpa only [← he] using pos p l hi
      · intro Q hQ
        simpa only [← he] using neg Q hQ
    obtain ⟨op, ar⟩ := hops g (by simp)
    suffices size : 63 ≤ C.size by exact Nat.succ_le_succ size
    rcases op with ha | ho
    · cases he : g.inputs with
      | nil =>
        apply punctured C 0 0 true mono back
        · intro p l h _
          change C.eval (P p l ++ [true]) = true
          simpa [first, ha, he, andValue] using pos p l h
        · intro Q h
          change C.eval (N Q ++ [true]) = false
          simpa [first, ha, he, andValue] using neg Q h
      | cons a rest =>
        cases rest with
        | nil =>
          apply reduceOr [a] (by simp)
          intro x
          simp [first, ha, he, andValue]
        | cons b tail =>
          have ht : tail = [] := by
            rw [he] at ar
            simpa using ar
          subst tail
          by_cases hab : a = b
          · subst b
            apply reduceOr [a] (by simp)
            intro x
            simp [first, ha, he, andValue]
          · have hw : ∀ j ∈ [a,b], j < 26 := by
              intro j hj
              have h := hback ⟨0, by simp⟩ j (by simpa [he] using hj)
              simpa using h
            let a' : Fin 26 := ⟨a, hw a (by simp)⟩
            let b' : Fin 26 := ⟨b, hw b (by simp)⟩
            let exceptP (i j : Fin 26) : Fin 13 := Fin.ofNat 13 (if i.val < 13 then i.val else j.val)
            let exceptL (i j : Fin 26) : Fin 13 := Fin.ofNat 13 ((if i.val < 13 then j.val else i.val) - 13)
            have support : ∀ (i : Fin 26) (p l : Fin 13),
                (P p l).getD i.val false = true → i.val = p.val ∨ i.val = 13 + l.val := by
              decide +kernel
            have uniquePair (i j : Fin 26) (hne : i ≠ j) (p l : Fin 13)
                (exc : p ≠ exceptP i j ∨ l ≠ exceptL i j) :
                ((P p l).getD i.val false && (P p l).getD j.val false) = false := by
              by_contra h
              have hits : (P p l).getD i.val false = true ∧ (P p l).getD j.val false = true := by
                simpa only [Bool.not_eq_false, Bool.and_eq_true] using h
              have hvals : i.val ≠ j.val := fun e => hne (Fin.ext e)
              rcases support i p l hits.1 with ip | il <;> rcases support j p l hits.2 with jp | jl
              · exact hvals (ip.trans jp.symm)
              · have cp : exceptP i j = p := by
                  apply Fin.ext
                  simp [exceptP, ip, p.isLt, Fin.ofNat, Nat.mod_eq_of_lt p.isLt]
                have cl : exceptL i j = l := by
                  apply Fin.ext
                  simp [exceptL, ip, jl, p.isLt, Fin.ofNat, Nat.mod_eq_of_lt l.isLt]
                exact exc.elim (fun h => h cp.symm) (fun h => h cl.symm)
              · have hi : ¬ i.val < 13 := by omega
                have cp : exceptP i j = p := by
                  apply Fin.ext
                  simp [exceptP, hi, jp, Fin.ofNat, Nat.mod_eq_of_lt p.isLt]
                have cl : exceptL i j = l := by
                  apply Fin.ext
                  simp [exceptL, il, Fin.ofNat, Nat.mod_eq_of_lt l.isLt]
                exact exc.elim (fun h => h cp.symm) (fun h => h cl.symm)
              · exact hvals (il.trans jl.symm)
            apply punctured C (exceptP a' b') (exceptL a' b') false mono back
            · intro p l h hexc
              change C.eval (P p l ++ [false]) = true
              have no := uniquePair a' b' (fun eq => hab (congrArg Fin.val eq)) p l hexc
              change ((P p l).getD a false && (P p l).getD b false) = false at no
              simp only [List.getD_eq_getElem?_getD] at no
              simpa [first, ha, he, andValue, no] using pos p l h
            · intro Q h
              change C.eval (N Q ++ [false]) = false
              by_contra bad
              have ans : C.eval (N Q ++ [false]) = true := by simpa using bad
              have wrong := lowerBit (N Q) (first (N Q)) ans
              rw [neg Q h] at wrong
              contradiction
    · apply reduceOr g.inputs ar
      intro x
      simp [first, ho, orValue, List.any_map]