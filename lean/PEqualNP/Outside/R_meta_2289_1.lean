import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2289_1 :
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
         (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
     let w : List Gate → ℕ → (Fin 9 → Bool) → Bool := fun gs a x =>
       (⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])
     ∀ (gs : List Gate) (a : ℕ), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 13 →
       10 ≤ a → a < 9 + gs.length →
       (∀ i : Fin 9, ∃ g ∈ gs.take (a - 9), i.val ∈ g.inputs) →
       (fun x => w gs a x && w gs (9 + gs.length) x) ≠ f) →
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
         (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
     let w : List Gate → ℕ → (Fin 9 → Bool) → Bool := fun gs a x =>
       (⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])
     ∀ (gs : List Gate) (a : ℕ), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 13 →
       10 ≤ a → a < 9 + gs.length →
       (∀ i : Fin 9, ∃ g ∈ gs, i.val ∈ g.inputs) →
       (∃ i : Fin 9, (∀ g ∈ gs.take (a - 9), i.val ∉ g.inputs) ∧
         ∀ x : Fin 9 → Bool, let y := Function.update x i true
           f x = false → f y = true → (x 0 && x 6) = (y 0 && y 6) →
           w gs (9 + gs.length) x = false) →
       (fun x => w gs a x && w gs (9 + gs.length) x) ≠ f) →
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) && { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  intro firstCase secondCase gs a b fanin bound order valid alleged
  let f : (Fin 9 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let z : (Fin 9 → Bool) → Bool := fun x => x 0 && x 6
  let word : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [z x]
  let w : List Gate → ℕ → (Fin 9 → Bool) → Bool := fun gs a x =>
    (⟨gs, a⟩ : Circuit).eval (word x)
  have target (x : Fin 9 → Bool) : f x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
      (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 ||
      (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
    simp only [Bool.or_false, Bool.or_assoc]
  have exactOrig (x : Fin 9 → Bool) : (w gs a x && w gs b x) = f x :=
    (congrFun alleged x).trans (target x).symm
  have wordLen (x : Fin 9 → Bool) : (word x).length = 10 := by simp [word]
  let step : List Bool → Gate → List Bool := fun xs g =>
    xs ++ [g.op.eval (g.inputs.map fun j => xs.getD j false)]
  have wireLen (gs : List Gate) (xs : List Bool) :
      (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
  have prefixIn (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
  have evalTake (gs : List Gate) (x : Fin 9 → Bool) (a n : ℕ) (h : n ≤ gs.length)
      (inside : a < 10 + n) : w gs a x = w (gs.take n) a x := by
    change (gs.foldl step (word x)).getD a false =
      ((gs.take n).foldl step (word x)).getD a false
    rw (occs := [1]) [← List.take_append_drop n gs]
    rw [List.foldl_append]
    apply prefixIn
    simpa only [wireLen, wordLen, List.length_take, Nat.min_eq_left h] using inside
  have dropped (gs : List Gate) (i : ℕ)
      (miss : ∀ g ∈ gs, i ∉ g.inputs)
      (xs ys : List Bool) (len : xs.length = ys.length)
      (agree : ∀ j, j ≠ i → xs.getD j false = ys.getD j false) :
      ∀ j, j ≠ i → (gs.foldl step xs).getD j false = (gs.foldl step ys).getD j false := by
    induction gs generalizing xs ys with
    | nil => exact agree
    | cons g gs ih =>
        have gmiss := miss g (by simp)
        have operandsAgree : (g.inputs.map fun j => xs.getD j false) =
            (g.inputs.map fun j => ys.getD j false) := by
          apply List.map_congr_left
          intro j occurs
          apply agree j
          intro eq
          exact gmiss (eq ▸ occurs)
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun k hk => miss k (List.mem_cons_of_mem _ hk))
        · simp [step, len]
        · intro j different
          by_cases before : j < xs.length
          · rw [show (step xs g).getD j false = xs.getD j false from List.getD_append _ _ _ _ before,
                show (step ys g).getD j false = ys.getD j false from
                  List.getD_append _ _ _ _ (by simpa [len] using before)]
            exact agree j different
          · change (xs ++ [_]).getD j false = (ys ++ [_]).getD j false
            rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), len, operandsAgree]
  have wordAgree (x : Fin 9 → Bool) (i : Fin 9) (hz : z x = z (Function.update x i true))
      (j : ℕ) (different : j ≠ i.val) :
      (word x).getD j false = (word (Function.update x i true)).getD j false := by
    by_cases below : j < 9
    · have leftLen : j < (List.ofFn x).length := by simpa
      have rightLen : j < (List.ofFn (Function.update x i true)).length := by simpa
      change (List.ofFn x ++ [_]).getD j false = (List.ofFn (Function.update x i true) ++ [_]).getD j false
      rw [List.getD_append _ _ _ _ leftLen, List.getD_append _ _ _ _ rightLen,
        List.getD_eq_getElem _ _ leftLen, List.getD_eq_getElem _ _ rightLen]
      simp only [List.getElem_ofFn]
      symm
      exact Function.update_of_ne (fun eq : (⟨j, below⟩ : Fin 9) = i =>
        different (congrArg Fin.val eq)) true x
    · change (List.ofFn x ++ [_]).getD j false = (List.ofFn (Function.update x i true) ++ [_]).getD j false
      rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega), hz]
      simp
  have invariant (gs : List Gate) (a : ℕ) (input : Fin 9) (strict : 10 ≤ a)
      (miss : ∀ g ∈ gs, input.val ∉ g.inputs) (x : Fin 9 → Bool)
      (sameExtra : z x = z (Function.update x input true)) :
      w gs a x = w gs a (Function.update x input true) := by
    exact dropped gs input.val miss (word x) (word (Function.update x input true))
      (by rw [wordLen, wordLen]) (wordAgree x input sameExtra) a (by omega)
  let pr : Fin 4 → Fin 9 → Bool := fun k i => (![5, 42, 208, 276] k : Nat).testBit i.val
  have probes : ∀ i j : Fin 9, ∃ k : Fin 4, f (pr k) = false ∧
      f (Function.update (pr k) i true) = true ∧ f (Function.update (pr k) j true) = true ∧
      z (pr k) = z (Function.update (pr k) i true) ∧
      z (pr k) = z (Function.update (pr k) j true) := by
    dsimp only [f, pr, z]
    decide
  let kept := gs.take (b - 9)
  have keepLen : kept.length = b - 9 := by
    simp [kept, Nat.min_eq_left (show b - 9 ≤ gs.length by omega)]
  have aGate : 10 ≤ a := by
    by_contra! raw
    have edge : ∀ i : Fin 10, ∃ k : Fin 2,
        let x : Fin 9 → Bool := fun v => (![3, 12] k : Nat).testBit v.val
        f x = true ∧ (word x).getD i false = false := by
      dsimp only [f, word, z]
      decide
    obtain ⟨k, positive, low⟩ := edge ⟨a, raw⟩
    let x : Fin 9 → Bool := fun v => (![3, 12] k : Nat).testBit v.val
    have accepts := (Bool.and_eq_true_iff.mp ((exactOrig x).trans positive)).1
    have readsRaw : w gs a x = (word x).getD a false := by
      exact prefixIn gs (word x) a (by rw [wordLen]; omega)
    exact Bool.noConfusion ((readsRaw.trans low).symm.trans accepts)
  have lastIndex : 9 + kept.length = b := by omega
  have aKept (x : Fin 9 → Bool) : w gs a x = w kept a x :=
    evalTake gs x a (b - 9) (by omega) (by omega)
  have bKept (x : Fin 9 → Bool) : w gs b x = w kept (9 + kept.length) x := by
    rw [lastIndex]
    exact evalTake gs x b (b - 9) (by omega) (by omega)
  have exactKept (x : Fin 9 → Bool) :
      (w kept a x && w kept (9 + kept.length) x) = f x := by
    rw [← aKept, ← bKept, exactOrig]
  have keptFanin : FanInTwo ⟨kept, 0⟩ := fun g hg =>
    fanin g (List.mem_of_mem_take hg)
  have keptBound : kept.length ≤ 13 := by omega
  have aInside : a < 9 + kept.length := by omega
  have aPrefixLen : a - 9 ≤ kept.length := by omega
  have sameEarlier (i : Fin 9) (miss : ∀ g ∈ kept.take (a - 9), i.val ∉ g.inputs)
      (x : Fin 9 → Bool) (sameExtra : z x = z (Function.update x i true)) :
      w kept a x = w kept a (Function.update x i true) := by
    rw [evalTake kept x a (a - 9) aPrefixLen (by omega),
      evalTake kept (Function.update x i true) a (a - 9) aPrefixLen (by omega)]
    exact invariant _ a i aGate miss x sameExtra
  classical
  by_cases earlierAll : ∀ i : Fin 9, ∃ g ∈ kept.take (a - 9), i.val ∈ g.inputs
  · exact firstCase kept a keptFanin keptBound aGate aInside earlierAll (funext exactKept)
  · push Not at earlierAll
    obtain ⟨i, miss⟩ := earlierAll
    have laterReject (x : Fin 9 → Bool) (negative : f x = false)
        (positive : f (Function.update x i true) = true)
        (sameExtra : z x = z (Function.update x i true)) :
        w kept (9 + kept.length) x = false := by
      have yes := (Bool.and_eq_true_iff.mp ((exactKept (Function.update x i true)).trans positive)).1
      have left : w kept a x = true := (sameEarlier i miss x sameExtra).trans yes
      simpa only [left, Bool.true_and, negative] using exactKept x
    have laterAll (j : Fin 9) : ∃ g ∈ kept, j.val ∈ g.inputs := by
      by_contra noRead
      push Not at noRead
      obtain ⟨k, negative, posI, posJ, zI, zJ⟩ := probes i j
      have no := laterReject (pr k) negative posI zI
      have yes := (Bool.and_eq_true_iff.mp ((exactKept (Function.update (pr k) j true)).trans posJ)).2
      have same := invariant kept (9 + kept.length) j (by omega) noRead (pr k) zJ
      exact Bool.noConfusion (no.symm.trans (same.trans yes))
    exact secondCase kept a keptFanin keptBound aGate aInside laterAll
      ⟨i, miss, laterReject⟩ (funext exactKept)
