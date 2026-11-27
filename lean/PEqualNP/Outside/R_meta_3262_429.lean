import PEqualNP.Defs
import Mathlib.Logic.Equiv.Fin.Basic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Attach two disjoint cubic incidence graphs to each original point and each original line.
-- Each of the four graphs per index contributes 22 edges including its bridge and seven centres.
-- The circuit gains at most 116 gates per index and the lower-bound expression grows by 116.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32000 in
theorem PEqualNP.Outside.R_meta_3262_429
    (dense : let good := fun (n : ℕ) (E : Finset (Fin n × Fin n)) (C : Circuit) =>
       (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c)∈E ∧ (a,d)∈E ∧ (b,c)∈E ∧ (b,d)∈E)) ∧
       (∃ p : Equiv.Perm (Fin n), ∀ i,(i,p i)∈E) ∧ IsAO2 (n+n) C ∧
       (∀ x, circuitFun (n+n) C x = decide (∃ a b,(a,b)∈E ∧ x (Fin.castAdd n a)=true ∧ x (Fin.natAdd n b)=true))
    ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : Circuit), good n E C → (∀ i, 3 ≤ (E.filter (fun e => e.1 = i)).card ∧ 3 ≤ (E.filter (fun e => e.2 = i)).card) →
      E.card + n ≤ C.size + 1)
    (extend : ∀ {n N : ℕ} (φ : Fin n → Fin N) (C : Circuit), IsAO2 n C →
      ∀ stars : List (Fin N × List (Fin N)), (∀ t ∈ stars, t.2 ≠ []) → ∃ D : Circuit, IsAO2 N D ∧
      D.size ≤ C.size + (stars.map (fun t => t.2.length + 1)).sum ∧
      ∀ x, circuitFun N D x = (circuitFun n C (x ∘ φ) || stars.any (fun t => x t.1 && t.2.any x))) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  let Label := Fin 29

  let flag (a b : Label) : Bool :=
    if a = 0 then b == 1 || b == 8
    else if b = 0 then a == 15 || a == 22
    else let i := a.val - 1; let j := b.val - 1
         i / 7 == j / 7 && ((j % 7 == i % 7) || (j % 7 == (i+1) % 7) || (j % 7 == (i+3) % 7))

  let F : Finset (Label × Label) := Finset.univ.filter fun t => flag t.1 t.2

  let free {α : Type} (R : α → α → Prop) := ∀ a b c d, a ≠ b → c ≠ d → ¬ (R a c ∧ R a d ∧ R b c ∧ R b d)
  let triple {α : Type} (P : α → Prop) := ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ P a ∧ P b ∧ P c

  have flag_mem (a b : Label) : (a,b) ∈ F ↔ flag a b = true := by simp [F]
  have flag_count : F.card = 88 := by decide +kernel
  have flag_diag : ∀ a : Label, a ≠ 0 → flag a a = true := by decide +kernel
  let neighboursRow (a : Label) : Label × Label × Label :=
    ([(0,0,0), (1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3), (8,9,11), (9,10,12), (10,11,13), (11,12,14), (12,13,8), (13,14,9), (14,8,10), (15,16,18), (16,17,19), (17,18,20), (18,19,21), (19,20,15), (20,21,16), (21,15,17), (22,23,25), (23,24,26), (24,25,27), (25,26,28), (26,27,22), (27,28,23), (28,22,24)] : List (Label × Label × Label)).getD a.val (0,0,0)

  have flag_row (a : Label) (ha : a ≠ 0) : triple (fun b => flag a b = true) := by
    have certified : ∀ a : Label, a ≠ 0 → let t := neighboursRow a
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        flag a t.1 = true ∧ flag a t.2.1 = true ∧ flag a t.2.2 = true := by decide +kernel
    exact ⟨_,_,_,certified a ha⟩

  let neighboursCol (a : Label) : Label × Label × Label :=
    ([(0,0,0), (1,7,5), (2,1,6), (3,2,7), (4,3,1), (5,4,2), (6,5,3), (7,6,4), (8,14,12), (9,8,13), (10,9,14), (11,10,8), (12,11,9), (13,12,10), (14,13,11), (15,21,19), (16,15,20), (17,16,21), (18,17,15), (19,18,16), (20,19,17), (21,20,18), (22,28,26), (23,22,27), (24,23,28), (25,24,22), (26,25,23), (27,26,24), (28,27,25)] : List (Label × Label × Label)).getD a.val (0,0,0)

  have flag_col (a : Label) (ha : a ≠ 0) : triple (fun b => flag b a = true) := by
    have certified : ∀ a : Label, a ≠ 0 → let t := neighboursCol a
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        flag t.1 a = true ∧ flag t.2.1 a = true ∧ flag t.2.2 a = true := by decide +kernel
    exact ⟨_,_,_,certified a ha⟩

  let full (a b : Label) : Bool := (a == 0 && b == 0) || flag a b

  have full_free : free (fun a b => full a b = true) := by
    have hits : ∀ a b : Label, a ≠ b → (Finset.univ.filter (fun c => full a c && full b c)).card ≤ 1 := by decide +kernel
    intro a b c d hab hcd square
    have ac := square.1
    have ad := square.2.1
    have bc := square.2.2.1
    have bd := square.2.2.2
    apply hcd
    apply Finset.card_le_one.mp (hits a b hab)
    · simp [ac,bc]
    · simp [ad,bd]

  have upper_zero : flag 0 0 = false := by rfl
  let Vertex (n : ℕ) := Fin n × Label

  let lift {n} (E : Finset (Fin n × Fin n)) (a b : Vertex n) : Prop :=
    (a.2 = 0 ∧ b.2 = 0 ∧ (a.1,b.1) ∈ E) ∨ (a.1 = b.1 ∧ flag a.2 b.2 = true)

  let edges {n} (E : Finset (Fin n × Fin n)) : Finset (Vertex n × Vertex n) :=
    E.image (fun p => ((p.1,0),(p.2,0))) ∪
    (Finset.univ.product F).image (fun t => ((t.1,t.2.1),(t.1,t.2.2)))

  have mem_edges {n} (E : Finset (Fin n × Fin n)) (a b : Vertex n) : (a,b) ∈ edges E ↔ lift E a b := by
    rcases a with ⟨i,r⟩
    rcases b with ⟨j,s⟩
    simp only [edges, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and, lift,
      Prod.mk.injEq, Prod.exists, flag_mem]
    aesop (add simp flag_mem)

  have edges_card {n} (E : Finset (Fin n × Fin n)) : (edges E).card = E.card + n * 88 := by
    classical
    let l (p : Fin n × Fin n) : Vertex n × Vertex n := ((p.1,0),(p.2,0))
    let r (t : Fin n × (Label × Label)) : Vertex n × Vertex n := ((t.1,t.2.1),(t.1,t.2.2))
    have linj : Function.Injective l := by intro a b h; exact Prod.ext (congrArg (fun q => q.1.1) h) (congrArg (fun q => q.2.1) h)
    have rinj : Function.Injective r := by
      intro a b h
      exact Prod.ext (congrArg (fun q => q.1.1) h) (Prod.ext (congrArg (fun q => q.1.2) h) (congrArg (fun q => q.2.2) h))
    have dis : Disjoint (E.image l) ((Finset.univ.product F).image r) := by
      rw [Finset.disjoint_left]
      intro q h₁ h₂
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨⟨i,a,b⟩,h,eq⟩ := Finset.mem_image.mp h₂
      have ha : a = 0 := congrArg (fun q => q.1.2) eq
      have hb : b = 0 := congrArg (fun q => q.2.2) eq
      have hf := (flag_mem a b).mp (Finset.mem_product.mp h).2
      rw [ha,hb,upper_zero] at hf
      contradiction
    change (E.image l ∪ (Finset.univ.product F).image r).card = _
    rw [Finset.card_union_of_disjoint dis, Finset.card_image_of_injective _ linj, Finset.card_image_of_injective _ rinj]
    rw [show ((Finset.univ : Finset (Fin n)).product F).card = Finset.univ.card * F.card from Finset.card_product _ _, flag_count]
    simp

  have lift_free {n} (E : Finset (Fin n × Fin n)) (old : free (fun i j => (i,j) ∈ E)) : free (lift E) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ ⟨l,d⟩ hab hcd ⟨ac,ad,bc,bd⟩
    have cross {i j : Fin n} {a b : Label} (h : lift E (i,a) (j,b)) (ne : i ≠ j) : a = 0 ∧ b = 0 := by
      rcases h with ⟨ha,hb,_⟩ | ⟨rfl,_⟩
      · exact ⟨ha,hb⟩
      · exact (ne rfl).elim
    have rootEdge {i j : Fin n} (h : lift E (i,0) (j,0)) : (i,j) ∈ E := by
      rcases h with ⟨_,_,h⟩ | ⟨_,h⟩
      · exact h
      · exact Bool.noConfusion (upper_zero.symm.trans h)
    have localEdge {i j : Fin n} {a b : Label} (h : lift E (i,a) (j,b)) : full a b = true := by
      rcases h with ⟨ha,hb,_⟩ | ⟨_,h⟩
      · change a = 0 at ha
        change b = 0 at hb
        simp [full,ha,hb]
      · simp [full,h]
    have pairRow : i ≠ j → c = 0 ∧ d = 0 := by
      intro hij
      constructor
      · by_cases h : i = k
        · exact (cross bc (fun e => hij (h.trans e.symm))).2
        · exact (cross ac h).2
      · by_cases h : i = l
        · exact (cross bd (fun e => hij (h.trans e.symm))).2
        · exact (cross ad h).2
    have pairCol : k ≠ l → a = 0 ∧ b = 0 := by
      intro hkl
      constructor
      · by_cases h : i = k
        · exact (cross ad (fun e => hkl (h.symm.trans e))).1
        · exact (cross ac h).1
      · by_cases h : j = k
        · exact (cross bd (fun e => hkl (h.symm.trans e))).1
        · exact (cross bc h).1
    by_cases h : i = j
    · subst j
      have ab : a ≠ b := fun e => hab (by cases e; rfl)
      have kl : k = l := by
        by_contra ne
        exact ab ((pairCol ne).1.trans (pairCol ne).2.symm)
      subst l
      exact full_free a b c d ab (fun e => hcd (by cases e; rfl))
        ⟨localEdge ac, localEdge ad, localEdge bc, localEdge bd⟩
    · obtain ⟨rfl,rfl⟩ := pairRow h
      have kl : k ≠ l := fun e => hcd (by cases e; rfl)
      obtain ⟨rfl,rfl⟩ := pairCol kl
      exact old i j k l h kl ⟨rootEdge ac,rootEdge ad,rootEdge bc,rootEdge bd⟩

  let matching {n} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Vertex n) := {
    toFun x := (if x.2 = 0 then p x.1 else x.1, x.2)
    invFun x := (if x.2 = 0 then p.symm x.1 else x.1, x.2)
    left_inv := by rintro ⟨i,a⟩; by_cases h : a=0 <;> simp [h]
    right_inv := by rintro ⟨i,a⟩; by_cases h : a=0 <;> simp [h] }

  have lift_match {n} (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (old : ∀ i,(i,p i)∈E) :
      ∀ a, lift E a (matching p a) := by
    rintro ⟨i,a⟩
    by_cases h : a=0
    · exact Or.inl ⟨h,h,by simpa [matching,h] using old i⟩
    · exact Or.inr ⟨by simp [matching,h],flag_diag a h⟩

  have lift_thick {n} (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (old : ∀ i,(i,p i)∈E) :
      (∀ a,triple (lift E a)) ∧ (∀ b,triple (fun a => lift E a b)) := by
    constructor
    · rintro ⟨i,a⟩
      by_cases h : a=0
      · subst a
        refine ⟨(p i,0),(i,1),(i,8),?_,?_,?_,.inl ⟨rfl,rfl,old i⟩,.inr ⟨rfl,rfl⟩,.inr ⟨rfl,rfl⟩⟩
        all_goals intro h; exact (by dsimp; decide : ¬ _ = _) (congrArg (fun v : Vertex n => v.2) h)
      · obtain ⟨b,c,d,bc,bd,cd,hb,hc,hd⟩ := flag_row a h
        exact ⟨(i,b),(i,c),(i,d),fun e=>bc (congrArg Prod.snd e),fun e=>bd (congrArg Prod.snd e),
          fun e=>cd (congrArg Prod.snd e),.inr ⟨rfl,hb⟩,.inr ⟨rfl,hc⟩,.inr ⟨rfl,hd⟩⟩
    · rintro ⟨i,a⟩
      by_cases h : a=0
      · subst a
        refine ⟨(p.symm i,0),(i,15),(i,22),?_,?_,?_,.inl ⟨rfl,rfl,by simpa using old (p.symm i)⟩,
          .inr ⟨rfl,rfl⟩,.inr ⟨rfl,rfl⟩⟩
        all_goals intro h; exact (by dsimp; decide : ¬ _ = _) (congrArg (fun v : Vertex n => v.2) h)
      · obtain ⟨b,c,d,bc,bd,cd,hb,hc,hd⟩ := flag_col a h
        exact ⟨(i,b),(i,c),(i,d),fun e=>bc (congrArg Prod.snd e),fun e=>bd (congrArg Prod.snd e),
          fun e=>cd (congrArg Prod.snd e),.inr ⟨rfl,hb⟩,.inr ⟨rfl,hc⟩,.inr ⟨rfl,hd⟩⟩
  let LocalStar := Bool × Label × List Label
  let table : List LocalStar := [
    (true,1,[1, 7, 5, 0]),
    (true,2,[2, 1, 6]),
    (true,3,[3, 2, 7]),
    (true,4,[4, 3, 1]),
    (true,5,[5, 4, 2]),
    (true,6,[6, 5, 3]),
    (true,7,[7, 6, 4]),
    (true,8,[8, 14, 12, 0]),
    (true,9,[9, 8, 13]),
    (true,10,[10, 9, 14]),
    (true,11,[11, 10, 8]),
    (true,12,[12, 11, 9]),
    (true,13,[13, 12, 10]),
    (true,14,[14, 13, 11]),
    (false,15,[15, 16, 18, 0]),
    (false,16,[16, 17, 19]),
    (false,17,[17, 18, 20]),
    (false,18,[18, 19, 21]),
    (false,19,[19, 20, 15]),
    (false,20,[20, 21, 16]),
    (false,21,[21, 15, 17]),
    (false,22,[22, 23, 25, 0]),
    (false,23,[23, 24, 26]),
    (false,24,[24, 25, 27]),
    (false,25,[25, 26, 28]),
    (false,26,[26, 27, 22]),
    (false,27,[27, 28, 23]),
    (false,28,[28, 22, 24])]

  have table_ne : ∀ t ∈ table, t.2.2 ≠ [] := by decide +kernel
  have table_cost : (table.map (fun t => t.2.2.length+1)).sum = 116 := by decide +kernel
  have table_flag : ∀ a b : Label, flag a b = true ↔ ∃ t ∈ table,
      (t.1 = false ∧ t.2.1 = a ∧ b ∈ t.2.2) ∨ (t.1 = true ∧ t.2.1 = b ∧ a ∈ t.2.2) := by decide +kernel

  let tag {n : ℕ} : Vertex n ≃ Fin (n*29) := finProdFinEquiv

  let pin {n : ℕ} (right : Bool) (i : Fin n) (a : Label) : Fin (n*29+n*29) :=
    if right then Fin.natAdd (n*29) (tag (i,a)) else Fin.castAdd (n*29) (tag (i,a))

  let oldPin {n : ℕ} : Fin (n+n) → Fin (n*29+n*29) :=
    Fin.addCases (fun i => pin false i 0) (fun i => pin true i 0)

  let star {n} (i : Fin n) (t : LocalStar) : Fin (n*29+n*29) × List (Fin (n*29+n*29)) :=
    (pin t.1 i t.2.1, t.2.2.map (pin (!t.1) i))

  let stars (n : ℕ) := (List.finRange n).flatMap fun i => table.map (star i)

  have stars_ne (n : ℕ) : ∀ t ∈ stars n, t.2 ≠ [] := by
    intro t ht
    obtain ⟨i,_,s,hs,rfl⟩ : ∃ i : Fin n, i ∈ List.finRange n ∧ ∃ s ∈ table, star i s = t := by
      simpa [stars] using ht
    exact fun e => table_ne s hs (List.map_eq_nil_iff.mp e)

  have stars_cost (n : ℕ) : ((stars n).map (fun t => t.2.length+1)).sum = n*116 := by
    have aux (l : List (Fin n)) : ((l.flatMap (fun i => table.map (star i))).map (fun t => t.2.length+1)).sum = l.length*116 := by
      induction l with
      | nil => rfl
      | cons i l ih =>
        simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,List.length_cons]
        have he : ((table.map (star i)).map (fun t => t.2.length+1)).sum = 116 := by
          simpa [star, List.map_map, Function.comp_def] using table_cost
        rw [he]
        omega
    simpa [stars] using aux (List.finRange n)

  have fires {n} (z : Fin (n*29+n*29) → Bool) :
      (stars n).any (fun t => z t.1 && t.2.any z) = true ↔
        ∃ (i : Fin n) (a b : Label), flag a b = true ∧ z (pin false i a) = true ∧ z (pin true i b) = true := by
    have memRange (i : Fin n) : i ∈ List.finRange n := List.mem_finRange i
    simp only [stars,List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true]
    constructor
    · rintro ⟨t,⟨i,_,s,hs,rfl⟩,hc,v,hv,hz⟩
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      rcases s with ⟨right,c,vs⟩
      cases right
      · exact ⟨i,c,u,(table_flag c u).2 ⟨_,hs,.inl ⟨rfl,rfl,hu⟩⟩,hc,hz⟩
      · exact ⟨i,u,c,(table_flag u c).2 ⟨_,hs,.inr ⟨rfl,rfl,hu⟩⟩,hz,hc⟩
    · rintro ⟨i,a,b,hf,ha,hb⟩
      obtain ⟨⟨right,c,vs⟩,hs,h|h⟩ := (table_flag a b).1 hf
      · obtain ⟨rfl,rfl,hu⟩ := h
        exact ⟨_,⟨i,memRange i,_,hs,rfl⟩,ha,_,List.mem_map_of_mem hu,hb⟩
      · obtain ⟨rfl,rfl,hu⟩ := h
        exact ⟨_,⟨i,memRange i,_,hs,rfl⟩,hb,_,List.mem_map_of_mem hu,ha⟩
  let Matrix (n : ℕ) := Finset (Fin n × Fin n)

  let computes {n} (E : Matrix n) (C : Circuit) : Prop := ∀ x, circuitFun (n+n) C x =
    decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)

  let valid (n : ℕ) (E : Matrix n) (C : Circuit) : Prop :=
    free (fun i j => (i,j) ∈ E) ∧ (∃ p : Equiv.Perm (Fin n), ∀ i, (i,p i) ∈ E) ∧ IsAO2 (n+n) C ∧ computes E C

  let thick {n} (E : Matrix n) : Prop := ∀ i, 3 ≤ (E.filter (fun e => e.1 = i)).card ∧
    3 ≤ (E.filter (fun e => e.2 = i)).card

  let packed {n} (E : Matrix n) : Matrix (n*29) := (edges E).image (fun q => (tag q.1, tag q.2))

  have pack_mem {n} (E : Matrix n) (a b : Vertex n) : (tag a, tag b) ∈ packed E ↔ lift E a b := by
    rw [← mem_edges]
    constructor
    · intro h
      obtain ⟨⟨u,v⟩,huv,eq⟩ := Finset.mem_image.mp h
      have e₁ : u = a := tag.injective (congrArg Prod.fst eq)
      have e₂ : v = b := tag.injective (congrArg Prod.snd eq)
      simpa [e₁,e₂] using huv
    · exact fun h => Finset.mem_image.mpr ⟨(a,b),h,rfl⟩

  have pack_count {n} (E : Matrix n) : (packed E).card = E.card + n*88 := by
    dsimp only [packed]
    rw [Finset.card_image_of_injective]
    · exact edges_card E
    · exact fun a b h => Prod.ext (tag.injective (congrArg Prod.fst h)) (tag.injective (congrArg Prod.snd h))

  have pack_free {n} (E : Matrix n) (old : free fun i j => (i,j)∈E) : free (fun i j => (i,j)∈packed E) := by
    intro a b c d
    obtain ⟨a,rfl⟩ := tag.surjective a
    obtain ⟨b,rfl⟩ := tag.surjective b
    obtain ⟨c,rfl⟩ := tag.surjective c
    obtain ⟨d,rfl⟩ := tag.surjective d
    intro ab cd h
    simp only [pack_mem] at h
    exact lift_free E old a b c d (fun e => ab (congrArg tag e)) (fun e => cd (congrArg tag e)) h

  have pack_matching {n} (E : Matrix n) (p : Equiv.Perm (Fin n)) (old : ∀ i, (i,p i)∈E) :
      ∃ q : Equiv.Perm (Fin (n*29)), ∀ j, (j,q j)∈packed E := by
    refine ⟨tag.symm.trans ((matching p).trans tag),?_⟩
    intro j
    obtain ⟨a,rfl⟩ := tag.surjective j
    simpa using (pack_mem E a (matching p a)).2 (lift_match E p old a)

  have card_three {α : Type} [DecidableEq α] (S : Finset α) (h : triple fun x => x ∈ S) : 3 ≤ S.card := by
    obtain ⟨a,b,c,ab,ac,bc,ma,mb,mc⟩ := h
    have card : ({a,b,c} : Finset α).card = 3 := by simp [ab,ac,bc]
    rw [←card]
    exact Finset.card_le_card (Finset.insert_subset_iff.2 ⟨ma,Finset.insert_subset_iff.2 ⟨mb,Finset.singleton_subset_iff.2 mc⟩⟩)

  have pack_thick {n} (E : Matrix n) (p : Equiv.Perm (Fin n)) (old : ∀ i, (i,p i)∈E) : thick (packed E) := by
    intro i
    obtain ⟨v,rfl⟩ := tag.surjective i
    obtain ⟨forward,reverse⟩ := lift_thick E p old
    constructor
    · apply card_three
      obtain ⟨a,b,c,ab,ac,bc,ma,mb,mc⟩ := forward v
      refine ⟨(tag v,tag a),(tag v,tag b),(tag v,tag c),fun e => ab (tag.injective (congrArg Prod.snd e)),
        fun e => ac (tag.injective (congrArg Prod.snd e)),fun e => bc (tag.injective (congrArg Prod.snd e)),?_,?_,?_⟩
      all_goals simp [pack_mem, ma, mb, mc]
    · apply card_three
      obtain ⟨a,b,c,ab,ac,bc,ma,mb,mc⟩ := reverse v
      refine ⟨(tag a,tag v),(tag b,tag v),(tag c,tag v),fun e => ab (tag.injective (congrArg Prod.fst e)),
        fun e => ac (tag.injective (congrArg Prod.fst e)),fun e => bc (tag.injective (congrArg Prod.fst e)),?_,?_,?_⟩
      all_goals simp [pack_mem, ma, mb, mc]

  have pin_old_left {n} (i : Fin n) : oldPin (Fin.castAdd n i) = pin false i 0 := by
    simp only [oldPin,Fin.addCases_left]

  have pin_old_right {n} (i : Fin n) : oldPin (Fin.natAdd n i) = pin true i 0 := by
    simp only [oldPin,Fin.addCases_right]

  have semantics {n} (E : Matrix n) (C D : Circuit) (old : computes E C)
      (ev : ∀ z, circuitFun (n*29+n*29) D z = (circuitFun (n+n) C (z ∘ oldPin) ||
        (stars n).any (fun t => z t.1 && t.2.any z))) : computes (packed E) D := by
    intro z
    apply Bool.eq_iff_iff.mpr
    rw [ev, Bool.or_eq_true, old, decide_eq_true_iff, fires, decide_eq_true_iff]
    constructor
    · rintro (⟨i,j,he,hp,hl⟩ | ⟨i,a,b,hf,hp,hl⟩)
      · refine ⟨tag (i,0),tag (j,0),(pack_mem E _ _).2 (.inl ⟨rfl,rfl,he⟩),?_,?_⟩
        · simpa only [Function.comp_apply,pin_old_left,pin,Bool.false_eq_true,↓reduceIte] using hp
        · simpa only [Function.comp_apply,pin_old_right,pin,↓reduceIte] using hl
      · exact ⟨tag (i,a),tag (i,b),(pack_mem E _ _).2 (.inr ⟨rfl,hf⟩),hp,hl⟩
    · rintro ⟨v,w,he,hp,hl⟩
      obtain ⟨⟨i,a⟩,rfl⟩ := tag.surjective v
      obtain ⟨⟨j,b⟩,rfl⟩ := tag.surjective w
      rcases (pack_mem E _ _).1 he with ⟨ha,hb,he⟩ | ⟨hij,hf⟩
      · change a = 0 at ha
        change b = 0 at hb
        subst a
        subst b
        left
        refine ⟨i,j,he,?_,?_⟩
        · simpa only [Function.comp_apply,pin_old_left,pin,Bool.false_eq_true,↓reduceIte] using hp
        · simpa only [Function.comp_apply,pin_old_right,pin,↓reduceIte] using hl
      · change i = j at hij
        subst j
        exact Or.inr ⟨i,a,b,hf,hp,hl⟩

  have pad {n} (E : Matrix n) (C : Circuit) (hyp : valid n E C) :
      ∃ (E' : Matrix (n*29)) (D : Circuit), valid (n*29) E' D ∧ thick E' ∧
        E'.card = E.card + n*88 ∧ D.size ≤ C.size + n*116 := by
    obtain ⟨square,⟨p,mp⟩,ao,old⟩ := hyp
    obtain ⟨D,ok,bound,ev⟩ := extend oldPin C ao (stars n) (stars_ne n)
    exact ⟨packed E,D,⟨pack_free E square,pack_matching E p mp,ok,semantics E C D old ev⟩,
      pack_thick E p mp,pack_count E,by rwa [stars_cost] at bound⟩
  intro n E p C square matched ao equation
  obtain ⟨G,D,ok,high,edges,cost⟩ := pad E C ⟨square,⟨p,matched⟩,ao,equation⟩
  have lower := dense (n*29) G D ok high
  omega
