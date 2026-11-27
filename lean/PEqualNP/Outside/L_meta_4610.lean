import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610_aux.WordLift

def Legal (base xs : List Nat) : Prop :=
  ∀ i : Fin xs.length, ∃ a ∈ base ++ xs.take i.val, ∃ b ∈ base ++ xs.take i.val,
    xs.get i = a &&& b ∨ xs.get i = a ||| b

def Cover (K : List Nat) (q t : Nat) : Prop :=
  ∀ i : Nat, ∃ j : Nat, q.testBit j = true ∧ t.testBit j = t.testBit i ∧
    ∀ a∈K, (if t.testBit i then (a.testBit j = true → a.testBit i = true)
      else (a.testBit i = true → a.testBit j = true))

def Step (available : List Nat) (v : Nat) : Prop :=
  ∃ a∈available, ∃ b∈available, v = a &&& b ∨ v = a ||| b

theorem legal_snoc (base xs : List Nat) (x : Nat) :
    Legal base (xs ++ [x]) ↔ Legal base xs ∧ Step (base ++ xs) x := by
  constructor
  · intro h
    constructor
    · intro i
      have hi : i.val < (xs ++ [x]).length := by simp
      have h' := h ⟨i.val,hi⟩
      change Step (base ++ (xs ++ [x]).take i.val) (xs ++ [x])[i.val] at h'
      rwa [List.take_append_of_le_length i.isLt.le,List.getElem_append_left i.isLt] at h'
    · have hi : xs.length < (xs ++ [x]).length := by simp
      have h' := h ⟨xs.length,hi⟩
      change Step (base ++ (xs ++ [x]).take xs.length) (xs ++ [x])[xs.length] at h'
      simpa using h'
  · rintro ⟨h,hs⟩ i
    change Step (base ++ (xs ++ [x]).take i.val) (xs ++ [x])[i.val]
    by_cases hi : i.val < xs.length
    · rw [List.take_append_of_le_length hi.le,List.getElem_append_left hi]
      exact h ⟨i.val,hi⟩
    · have eq : i.val = xs.length := by have := i.isLt; simp at this; omega
      simp [eq,hs]

def monotoneColumn (K : List Nat) (v : Nat) : Prop :=
  ∀ i j : Nat, (∀ a∈K, a.testBit i = true → a.testBit j = true) →
    v.testBit i = true → v.testBit j = true

theorem monotone_step {K as : List Nat} {v : Nat} (hs : Step as v)
    (mono : ∀ a∈as, monotoneColumn K a) : monotoneColumn K v := by
  obtain ⟨a,ha,b,hb,h|h⟩ := hs
  · subst v
    intro i j hdir hval
    simp only [Nat.testBit_and,Bool.and_eq_true] at hval ⊢
    exact ⟨mono a ha i j hdir hval.1,mono b hb i j hdir hval.2⟩
  · subst v
    intro i j hdir hval
    simp only [Nat.testBit_or,Bool.or_eq_true] at hval ⊢
    exact hval.imp (mono a ha i j hdir) (mono b hb i j hdir)

theorem legal_monotone (K V : List Nat) (h : Legal K V) : ∀ v∈K++V, monotoneColumn K v := by
  induction V using List.reverseRecOn with
  | nil =>
    intro v hv i j hd
    exact hd v (by simpa using hv)
  | append_singleton V v ih =>
    obtain ⟨hV,hs⟩ := (legal_snoc _ _ _).mp h
    intro u hu
    rw [←List.append_assoc] at hu
    rcases List.mem_append.mp hu with hu|hu
    · exact ih hV u hu
    · obtain rfl := List.mem_singleton.mp hu
      exact monotone_step hs (ih hV)

private theorem mask_and (a b q : Nat) : (a &&& q) &&& (b &&& q) = (a &&& b) &&& q := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_and,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

private theorem mask_or (a b q : Nat) : (a &&& q) ||| (b &&& q) = (a ||| b) &&& q := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases q.testBit i <;> decide

theorem lift_program (K : List Nat) (q : Nat) (U : List Nat) (h : Legal (K.map (· &&& q)) U) :
    ∃ V : List Nat, V.map (· &&& q) = U ∧ Legal K V := by
  induction U using List.reverseRecOn with
  | nil => exact ⟨[],rfl,fun i=>Fin.elim0 i⟩
  | append_singleton U v ih =>
    obtain ⟨hU,hs⟩ := (legal_snoc _ _ _).mp h
    obtain ⟨V,hmap,hleg⟩ := ih hU
    obtain ⟨a,ha,b,hb,op⟩ := hs
    rw [←hmap,←List.map_append] at ha hb
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    rcases op with rfl | rfl
    · refine ⟨V++[u &&& w],by simp [hmap,mask_and],(legal_snoc _ _ _).mpr ?_⟩
      exact ⟨hleg,u,hu,w,hw,Or.inl rfl⟩
    · refine ⟨V++[u ||| w],by simp [hmap,mask_or],(legal_snoc _ _ _).mpr ?_⟩
      exact ⟨hleg,u,hu,w,hw,Or.inr rfl⟩

theorem masked_eq (K : List Nat) (q t u : Nat) (hc : Cover K q t) (hm : monotoneColumn K u)
    (he : u &&& q = t &&& q) : u=t := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨j,hq,ht,order⟩ := hc i
  have hu := congrArg (fun v : Nat=>v.testBit j) he
  simp only [Nat.testBit_and,hq,Bool.and_true] at hu
  cases hti : t.testBit i
  · rw [hti] at ht order
    have hno : u.testBit j = false := hu.trans ht
    cases hui : u.testBit i with
    | false => rfl
    | true =>
      have bad := hm i j order hui
      rw [hno] at bad
      contradiction
  · rw [hti] at ht order
    exact hm j i order (hu.trans ht)

theorem lift_suffix (K : List Nat) (q t : Nat) (U : List Nat)
    (hc : Cover K q t) (h : Legal (K.map (· &&& q)) U)
    (ht : (t &&& q) ∈ (K.map (· &&& q)) ++ U) :
    ∃ V : List Nat, V.length ≤ U.length ∧ Legal K V ∧ t ∈ K ++ V := by
  obtain ⟨V,hmap,hV⟩ := lift_program K q U h
  rw [←hmap,←List.map_append] at ht
  obtain ⟨u,hu,he⟩ := List.mem_map.mp ht
  obtain rfl := masked_eq K q t u hc (legal_monotone K V hV u hu) he
  exact ⟨V, by rw [←hmap,List.length_map],hV,hu⟩

end PEqualNP.Outside.L_meta_4610_aux.WordLift


theorem PEqualNP.Outside.L_meta_4610 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := PEqualNP.Outside.L_meta_4610_aux.WordLift.lift_suffix
