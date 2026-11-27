import Mathlib

-- Restrict vertex zero to false. Twelve distinct new functions are necessary on that slice.
-- The full search can discard a pool as soon as the number of remaining gates is too small
-- to obtain twenty-two different restricted functions, counting the eight inputs and constants.
theorem PEqualNP.Outside.R_meta_2966_12
    (slice : ∀ s : Finset ((Fin 8 → Bool) → Bool),
      Relation.ReflTransGen (fun s t => ∃ a ∈ s, ∃ b ∈ s,
        t = insert (fun x => a x && b x) s ∨
        t = insert (fun x => a x || b x) s ∨
        t = insert (fun x => !(a x)) s)
        (insert (fun _ => false) (insert (fun _ => true)
        (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i)))) s →
      (fun x => ([(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2)) ∈ s → 22 ≤ s.card)
    (search : ∀ s : Finset ((Fin 9 → Bool) → Bool),
      Relation.ReflTransGen (fun s t => ∃ a ∈ s, ∃ b ∈ s,
        t = insert (fun x => a x && b x) s ∨
        t = insert (fun x => a x || b x) s ∨
        t = insert (fun x => !(a x)) s)
        (insert (fun _ => false) (insert (fun _ => true) (insert (fun x => !(x 0))
        (Finset.univ.image (fun (i : Fin 9) (x : Fin 9 → Bool) => x i))))) s →
      s.card ≤ 26 →
      22 ≤ (s.image (fun f (x : Fin 8 → Bool) => f (Fin.cons false x))).card →
      (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) ∉ s) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.false →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  classical
  intro n op l r out paid ev hpaid budget reads hout hphase signs inputs const gates
  by_contra! correct
  let BF := (Fin 9 → Bool) → Bool
  let src (i : ℕ) : BF := fun x => ev x i
  let signed (p : ℕ × Bool) : BF := fun x => ev x p.1 ^^ p.2
  let init : Finset BF := (insert (fun _ => false) (insert (fun _ => true) (insert (fun x => !(x 0))
        (Finset.univ.image (fun (i : Fin 9) (x : Fin 9 → Bool) => x i)))))
  let cut (f : BF) (x : Fin 8 → Bool) := f (Fin.cons false x)
  let edge : BF := (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
  let gen {α : Type} [DecidableEq (α → Bool)] (s t : Finset (α → Bool)) : Prop :=
    ∃ a ∈ s, ∃ b ∈ s, t = insert (fun x => a x && b x) s ∨
      t = insert (fun x => a x || b x) s ∨ t = insert (fun x => !(a x)) s
  have startCard : init.card ≤ 12 := by
    dsimp only [init]
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 9)))
      (f := fun (i : Fin 9) (x : Fin 9 → Bool) => x i)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    grw [Finset.card_insert_le, Finset.card_insert_le, Finset.card_insert_le, h]
  have startCut : init.image cut = (insert (fun _ => false) (insert (fun _ => true)
        (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i)))) := by
    ext f
    simp only [init, Finset.image_insert, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | rfl | rfl | ⟨g, ⟨i, rfl⟩, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inl (by funext x; simp [cut]))
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact Or.inl (by funext x; simp [cut])
        · exact Or.inr (Or.inr ⟨j, by funext x; simp [cut]⟩)
    · rintro (rfl | rfl | ⟨i, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨_, ⟨i.succ, rfl⟩, by funext x; simp [cut]⟩))
  have liftCut {s t : Finset BF} (h : gen s t) : gen (s.image cut) (t.image cut) := by
    obtain ⟨a, ha, b, hb, h⟩ := h
    refine ⟨cut a, Finset.mem_image_of_mem _ ha, cut b, Finset.mem_image_of_mem _ hb, ?_⟩
    rcases h with rfl | rfl | rfl
    · exact Or.inl (Finset.image_insert ..)
    · exact Or.inr (Or.inl (Finset.image_insert ..))
    · exact Or.inr (Or.inr (Finset.image_insert ..))
  have addNeg {s : Finset BF} (i : Nat) (hi : src i ∈ s) :
      gen s (insert (fun x => !(src i x)) s) :=
    ⟨src i, hi, src i, hi, Or.inr (Or.inr rfl)⟩
  let credits (i : ℕ) := (paid.filter (· < i)).card
  have seedIn {s : Finset BF} (h : Relation.ReflTransGen gen init s) : init ⊆ s := by
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ step prev =>
      obtain ⟨_, _, _, _, eq | eq | eq⟩ := step <;> rw [eq] <;> exact prev.trans (Finset.subset_insert ..)
  have buildPool (k : ℕ) (hk : k ≤ 10 + n) :
      ∃ s : Finset BF, Relation.ReflTransGen gen init s ∧ s.card ≤ 12 + (k - 10) + credits k ∧
        (∀ i < k, src i ∈ s) ∧
        (∀ i < k, i = 0 ∨ i = 9 ∨ i ∈ paid → (fun x => !(src i x)) ∈ s) := by
    induction k with
    | zero => exact ⟨init, .refl, by simpa [credits] using startCard, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs, hsize, hpos, hneg⟩ := ih (by omega)
      have source (p : Nat × Bool) (hp : p.1 < k)
          (allowed : p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid) : signed p ∈ s := by
        rcases p with ⟨i, phase⟩
        cases phase
        · simpa [signed, src] using hpos i hp
        · simpa [signed, src] using hneg i hp (allowed rfl)
      obtain ⟨t, ht, hsub, htSize, hnew⟩ :
          ∃ t : Finset BF, Relation.ReflTransGen gen init t ∧ s ⊆ t ∧
            t.card ≤ 12 + (k + 1 - 10) + credits k ∧ src k ∈ t := by
        by_cases raw : k < 10
        · refine ⟨s, hs, Finset.Subset.refl _, by omega, ?_⟩
          apply seedIn hs
          by_cases i : k < 9
          · have eq : src k = fun x => x (⟨k,i⟩ : Fin 9) := funext fun x => inputs x ⟨k,i⟩
            rw [eq]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨k,i⟩ : Fin 9)))))
          · have eq : k = 9 := by omega
            subst k
            have eq : src 9 = fun _ => false := funext const
            rw [eq]
            exact Finset.mem_insert_self ..
        · let j : Fin n := ⟨k - 10, by omega⟩
          have hj : 10 + j.val = k := by dsimp [j]; omega
          obtain ⟨hl, hr⟩ := reads j
          rw [hj] at hl hr
          refine ⟨insert (src k) s, hs.tail ?_, Finset.subset_insert .., ?_, Finset.mem_insert_self ..⟩
          · refine ⟨signed (l j), source _ hl (signs.2 j).1,
                    signed (r j), source _ hr (signs.2 j).2, ?_⟩
            cases hop : op j
            · right; left; congr 1; funext x
              simpa [src, signed, hop, hj] using gates x j
            · left; congr 1; funext x
              simpa [src, signed, hop, hj] using gates x j
          · have hc := Finset.card_insert_le (src k) s
            omega
      let u := if k ∈ paid then insert (fun x => !(src k x)) t else t
      have tu : t ⊆ u := by
        dsimp [u]; split <;> first | exact Finset.subset_insert .. | exact Finset.Subset.refl _
      have paidStep (hp : k ∈ paid) :
          paid.filter (· < k + 1) = insert k (paid.filter (· < k)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
        · intro member
          have hi := member.1
          have hlt := member.2
          by_cases h : i = k
          · exact Or.inl h
          · exact Or.inr ⟨hi, by omega⟩
        · rintro (rfl | ⟨hi,hlt⟩)
          · exact ⟨hp, by omega⟩
          · exact ⟨hi, by omega⟩
      refine ⟨u, ?_, ?_, ?_, ?_⟩
      · dsimp [u]; split
        · exact ht.tail (addNeg k hnew)
        · exact ht
      · dsimp [u]; split
        next hp =>
          have eq : credits (k+1) = credits k + 1 := by
            change (paid.filter (· < k+1)).card = (paid.filter (· < k)).card + 1
            rw [paidStep hp, Finset.card_insert_of_notMem (by simp)]
          have h := Finset.card_insert_le (fun x => !(src k x)) t
          omega
        next hp =>
          have mono : credits k ≤ credits (k+1) := Finset.card_le_card
            (fun i hi => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, Nat.lt_succ_of_lt (Finset.mem_filter.mp hi).2⟩)
          omega
      · intro i hi
        by_cases h : i = k
        · exact h ▸ tu hnew
        · exact tu (hsub (hpos i (by omega)))
      · intro i hi hallow
        by_cases h : i = k
        · subst i
          by_cases hp : k ∈ paid
          · simp [u, hp]
          apply tu; apply seedIn ht
          rcases hallow with rfl | rfl | hbad
          · have e : (fun x => !(src 0 x)) = fun (x : Fin 9 → Bool) => !(x 0) :=
              funext fun x => congrArg Bool.not (inputs x 0)
            rw [e]; simp [init]
          · have e : (fun x => !(src 9 x)) = fun _ => true := by funext x; simp [src, const]
            rw [e]; simp [init]
          · exact False.elim (hp hbad)
        · exact tu (hsub (hneg i (by omega) hallow))
  obtain ⟨s, reach, size, pos, _⟩ := buildPool (10+n) (by omega)
  have hcard : credits (10+n) ≤ paid.card := Finset.card_le_card (Finset.filter_subset ..)
  have mem : edge ∈ s := by
    have eq : src out.1 = edge := by
      funext x
      simpa only [src, edge, hphase, Bool.xor_false, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_assoc] using correct x
    exact eq ▸ pos out.1 hout
  have projectPool {u v : Finset BF} (path : Relation.ReflTransGen gen u v) :
      Relation.ReflTransGen gen (u.image cut) (v.image cut) := by
    induction path with
    | refl => exact .refl
    | tail _ step prev => exact prev.tail (liftCut step)
  have proj := projectPool reach
  rw [startCut] at proj
  have same : cut edge = (fun x => ([(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2)) := by
    funext x
    have h0 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 0 = false := rfl
    have h1 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 1 = x 0 := rfl
    have h2 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 2 = x 1 := rfl
    have h3 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 3 = x 2 := rfl
    have h4 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 4 = x 3 := rfl
    have h5 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 5 = x 4 := rfl
    have h6 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 6 = x 5 := rfl
    have h7 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 7 = x 6 := rfl
    have h8 : Fin.cons (α := fun _ : Fin 9 => Bool) false x 8 = x 7 := rfl
    simp only [cut, edge, List.any_cons, List.any_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
  have lower := slice _ proj (same ▸ Finset.mem_image_of_mem cut mem)
  exact search s reach (by omega) lower mem
