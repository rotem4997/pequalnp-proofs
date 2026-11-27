import Mathlib
import PEqualNP.Defs

-- The ordinary trace lower bound is the checked statement L-meta-2183.
-- On each fixed-input-zero fiber, an inverted output detects an opposed pair.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2964_317
    (ordinary : have x1 : List ((Fin (9 : ℕ) → Bool) → Bool) := (List.ofFn fun (x1 : Fin (9 : ℕ)) (x2 : Fin (9 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ))]; ∀ (x2 : List ((Fin (9 : ℕ) → Bool) → Bool)),   (∀ (x3 : Fin x2.length),       have x4 : List ((Fin (9 : ℕ) → Bool) → Bool) := (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x3) x2);       ∃ x5 ∈ x4, ∃ x6 ∈ x4, (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 && x6 x7) ∨ (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 || x6 x7) ∨ x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => !x5 x7) →     (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) ∈ (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (x1 ++ x2) → (15 : ℕ) ≤ x2.length)
    (small : ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool)
      (o : ℕ) (v : (Fin 8 → Bool) → ℕ → Bool), n ≤ 11 →
      (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → o < 10+n →
      (∀ x i, v x (i : Fin 8).val = x i) →
      (∀ x, v x 8 = false ∧ v x 9 = false) →
      (∀ x j, let s := fun u : ℕ × Bool => v x u.1 ^^ u.2
              v x (10+j.val) = if op j then s (a j) && s (b j) else s (a j) || s (b j)) →
      ∃ x, (!(v x o)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 5 && x 7))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.true →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  classical
  intro n op a b out marked v hcard budget order outLt phase allowed inputs zero gates
  let F (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  by_contra! correct
  have raw (x : Fin 9 → Bool) : v x out.1 = !(F x) := by
    have hh := correct x
    change (v x out.1 ^^ out.2) = F x at hh
    rw [phase] at hh
    exact (show ∀ p q : Bool, (p ^^ true) = q → p = !q by decide) _ _ hh
  by_cases hs : n ≤ 11
  · let put (x : Fin 8 → Bool) (i : Fin 9) := if h : i.val < 8 then x ⟨i.val,h⟩ else false
    obtain ⟨x,bad⟩ := small n op a b out.1 (fun x => v (put x)) hs order outLt
      (fun x i => (inputs _ ⟨i.val,by omega⟩).trans (by simp [put,i.isLt]))
      (fun x => ⟨(inputs _ 8).trans (by simp [put]),zero _⟩) (fun x j => gates (put x) j)
    apply bad
    rw [raw,Bool.not_not]
    simp [F,put]
  have markOut := allowed.1 phase
  have high : 10 ≤ out.1 := by
    by_contra! low
    let x : Fin 9 → Bool := fun _ => false
    have hv : v x out.1 = false := by
      by_cases h : out.1 < 9
      · exact inputs x ⟨out.1,h⟩
      · rw [show out.1 = 9 by omega,zero]
    have hr := raw x
    simp [hv,F,x] at hr
  have hm : out.1 ∈ marked := by rcases markOut with h | h | h <;> first | exact h | omega
  have sz : (marked.erase out.1).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hm]
    omega
  obtain ⟨s,only⟩ : ∃ s : ℕ, ∀ u ∈ marked, u ≠ out.1 → u = s := by
    by_cases h : (marked.erase out.1).Nonempty
    · obtain ⟨s,mem⟩ := h
      exact ⟨s,fun u hu hne => Finset.card_le_one.mp sz u (Finset.mem_erase.mpr ⟨hne,hu⟩) s mem⟩
    · exact ⟨0,fun u hu hne => False.elim (h ⟨u,Finset.mem_erase.mpr ⟨hne,hu⟩⟩)⟩
  let follows (x y : Fin 9 → Bool) := ∀ i, x i ≤ y i
  have propagate (x y : Fin 9 → Bool) (le : follows x y) (same : x 0 = y 0)
      (exception : s < out.1 → v y s ≤ v x s) :
      ∀ w ≤ out.1, v x w ≤ v y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases init : w < 9
      · simpa only [inputs x ⟨w,init⟩,inputs y ⟨w,init⟩] using le ⟨w,init⟩
      by_cases c : w = 9
      · simp [c,zero]
      let j : Fin n := ⟨w-10,by omega⟩
      have eq : 10+j.val = w := by dsimp [j]; omega
      have lit (t : ℕ × Bool) (ht : t.1 < w)
          (perm : t.2 = true → t.1 = 0 ∨ t.1 = 9 ∨ t.1 ∈ marked) :
          (v x t.1 ^^ t.2) ≤ (v y t.1 ^^ t.2) := by
        cases ph : t.2 with
        | false => simpa using ih _ ht (by omega)
        | true =>
          have rev : v y t.1 ≤ v x t.1 := by
            rcases perm ph with z | z | m
            · rw [z,show v x 0 = x 0 from inputs x 0,show v y 0 = y 0 from inputs y 0,same]
            · simp [z,zero]
            · have he := only _ m (by omega)
              exact he ▸ exception (by omega)
          exact (show ∀ a b : Bool, b ≤ a → (a ^^ true) ≤ (b ^^ true) by decide) _ _ rev
      have la := lit (a j) (by have := (order j).1; omega) (allowed.2 j).1
      have lb := lit (b j) (by have := (order j).2; omega) (allowed.2 j).2
      rw [← eq,gates,gates]
      split
      · exact (show ∀ p q r s : Bool, p ≤ r → q ≤ s → (p && q) ≤ (r && s) by decide) _ _ _ _ la lb
      · exact (show ∀ p q r s : Bool, p ≤ r → q ≤ s → (p || q) ≤ (r || s) by decide) _ _ _ _ la lb
  let bot (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then x 0 else false
  let top (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then x 0 else true
  have botF (x : Fin 9 → Bool) : F (bot x) = false := (show ∀ z : Bool, F (fun i => if i=0 then z else false) = false by decide) (x 0)
  have topF (x : Fin 9 → Bool) : F (top x) = true := (show ∀ z : Bool, F (fun i => if i=0 then z else true) = true by decide) (x 0)
  have descent (x y : Fin 9 → Bool) (le : follows x y) (same : x 0 = y 0)
      (lo : F x = false) (hi : F y = true) : s < out.1 ∧ v x s = false ∧ v y s = true := by
    by_contra! nope
    have p := propagate x y le same (by
      intro h
      specialize nope h
      exact (show ∀ a b : Bool, (a = false → b ≠ true) → b ≤ a by decide) _ _ nope)
    have q := p _ (Nat.le_refl _)
    rw [raw,raw,lo,hi] at q
    contradiction
  have sEq (x : Fin 9 → Bool) : v x s = F x := by
    cases f : F x with
    | false => exact (descent x (top x) (fun i => by by_cases h : i=0 <;> simp [top,h])
        (by simp [top]) f (topF x)).2.1
    | true => exact (descent (bot x) x (fun i => by by_cases h : i=0 <;> simp [bot,h])
        (by simp [bot]) (botF x) f).2.2
  have earlier := (descent (bot (fun _ => false)) (top (fun _ => false))
    (fun i => by by_cases h : i=0 <;> simp [bot,top,h]) (by simp [bot,top]) (botF (fun _ => false)) (topF (fun _ => false))).1
  have sHigh : 10 ≤ s := by
    by_contra! low
    by_cases c : s=9
    · have bad := sEq (fun _ => true)
      simp [c,zero,F] at bad
    · let i : Fin 9 := ⟨s,by omega⟩
      let single : Fin 9 → Bool := fun j => decide (i=j)
      have aux : ∀ k : Fin 9, F (fun j => decide (k=j)) = false := by decide
      have noedge := aux i
      have hit := inputs single i
      change v single s = decide (i=i) at hit
      rw [sEq,noedge] at hit
      simp at hit
  let X := Fin 9 → Bool
  let roots : List (X → Bool) := (List.ofFn fun (i : Fin 9) (x : X) => x i) ++ [fun x => x 0 && x 4]
  let len := s-9
  have lenLe : len ≤ n := by dsimp [len]; omega
  let seqG : List (X → Bool) := (fun x => !(x 0)) ::
    List.ofFn (fun j : Fin len => fun x : X => v x (10+j.val))
  have ht : seqG.length = 1+len := by simp [seqG,Nat.add_comm]
  have positive := Finset.card_pos.mpr (show marked.Nonempty from ⟨_,hm⟩)
  have hordinary := ordinary seqG
  apply Nat.not_le_of_gt (show seqG.length < 15 by rw [ht]; dsimp [len]; omega)
  apply hordinary
  · intro j
    let pool : List (X → Bool) := (fun _ => false) :: (fun _ => true) :: (roots ++ seqG.take j.val)
    change ∃ u ∈ pool, ∃ w ∈ pool, _
    have inroot (i : Fin 9) : (fun x : X => x i) ∈ pool := by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))
    by_cases first : j.val = 0
    · refine ⟨_,inroot 0,_,inroot 0,Or.inr (Or.inr ?_)⟩
      change seqG[j.val] = _
      simp [seqG,first] <;> rfl
    let k := j.val-1
    have hk : k < len := by have := j.isLt; omega
    let g : Fin n := ⟨k,by omega⟩
    have pred : j.val = k+1 := by dsimp [k]; omega
    have value : seqG.get j = fun x : X => v x (10+k) := by
      change seqG[j.val] = _
      simp [seqG,pred]
    have liftLit (t : ℕ × Bool) (bound : t.1 < 10+k)
        (perm : t.2 = true → t.1 = 0 ∨ t.1 = 9 ∨ t.1 ∈ marked) :
        (fun x : X => v x t.1 ^^ t.2) ∈ pool := by
      cases ph : t.2 with
      | true =>
        rcases perm ph with z | z | m
        · have ident : (fun x : X => v x t.1 ^^ true) = (fun x => !(x 0)) := by
            funext x; simp [z,show v x 0 = x 0 from inputs x 0]
          rw [ident]
          simp [pool,seqG,pred]
        · simp [z,zero,pool]
        · have below : t.1 < s := by dsimp [len] at hk; omega
          have he := only _ m (by omega)
          omega
      | false =>
        simp only [Bool.xor_false]
        by_cases inp : t.1 < 9
        · have ident : (fun x : X => v x t.1) = (fun x => x ⟨t.1,inp⟩) :=
            funext (fun x => inputs x ⟨t.1,inp⟩)
          rw [ident]; exact inroot _
        by_cases z : t.1 = 9
        · simp [z,zero,pool]
        let m := t.1-10
        have hm' : m < k := by dsimp [m]; omega
        have htake : m < ((List.ofFn (fun u : Fin len => fun x : X => v x (10+u.val))).take k).length := by
          simp; omega
        have mem := List.getElem_mem (l := (List.ofFn (fun u : Fin len => fun x : X => v x (10+u.val))).take k) htake
        have eq : 10+m=t.1 := by dsimp [m]; omega
        simp only [List.getElem_take,List.getElem_ofFn,eq] at mem
        simp only [pool,seqG,pred,List.take_succ_cons,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inr (Or.inr (Or.inr mem)))
    refine ⟨_,liftLit (a g) (order g).1 (allowed.2 g).1,
      _,liftLit (b g) (order g).2 (allowed.2 g).2,?_⟩
    rw [value]
    cases hop : op g
    · exact Or.inr (Or.inl (funext (fun x => by simpa [hop] using gates x g)))
    · exact Or.inl (funext (fun x => by simpa [hop] using gates x g))
  · let i : Fin len := ⟨s-10,by dsimp [len]; omega⟩
    have eq : 10+i.val = s := by dsimp [i]; omega
    have mem : F ∈ List.ofFn (fun j : Fin len => fun x : X => v x (10+j.val)) :=
      List.mem_ofFn.mpr ⟨i,funext (by intro x; rw [eq,sEq])⟩
    change F ∈ (fun _ => false) :: (roots ++ seqG)
    simp only [seqG,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr mem))
