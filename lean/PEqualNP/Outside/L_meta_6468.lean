import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6468
def Legal (base xs : List Nat) : Prop :=
  ∀ i : Fin xs.length, ∃ a ∈ base ++ xs.take i.val, ∃ b ∈ base ++ xs.take i.val,
    xs.get i = a &&& b ∨ xs.get i = a ||| b


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

theorem legal_bounded (K V : List Nat) (h : Legal K V) (hK : ∀ a ∈ K, a < 2 ^ 59) :
    ∀ v ∈ K ++ V, v < 2 ^ 59 := by
  induction V using List.reverseRecOn with
  | nil => intro v hv; exact hK v (by simpa using hv)
  | append_singleton V v ih =>
    obtain ⟨hV, hs⟩ := (legal_snoc _ _ _).mp h
    intro u hu
    rw [← List.append_assoc] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ih hV u hu
    · obtain rfl := List.mem_singleton.mp hu
      obtain ⟨a, ha, b, hb, e | e⟩ := hs
      · subst e; exact lt_of_le_of_lt Nat.and_le_right (ih hV b hb)
      · subst e; exact Nat.or_lt_two_pow (ih hV a ha) (ih hV b hb)

theorem c21 : (2097151 : Nat) = 2 ^ 21 - 1 := by norm_num

theorem main (K : List Nat) (q a b : Nat) (U : List Nat) (x8 x9 : Nat)
    (hK : ∀ x ∈ K, x < 2 ^ 59)
    (hx2 : q.testBit a = true ∧ q.testBit b = true ∧ ∀ x6 < (59 : Nat), ∃ x8 < (59 : Nat),
      q.testBit x8 = true ∧ (x8 < 21 ↔ x6 < 21) ∧ ∀ x9 ∈ K, if x6 < 21 then
        (x9.testBit x8 = true → x9.testBit x6 = true) else (x9.testBit x6 = true → x9.testBit x8 = true))
    (hU : Legal (K.map (· &&& q)) U)
    (h8 : x8 ∈ K.map (· &&& q) ++ U) (h9 : x9 ∈ K.map (· &&& q) ++ U)
    (heq : (if a < 21 then x8 ||| x9 else x8 &&& x9) = 2097151 &&& q)
    (hne : x8.testBit a ≠ x9.testBit a) (h1 : x8.testBit a = x9.testBit b)
    (h2 : x9.testBit a = x8.testBit b) :
    ∃ V : List Nat, V.length ≤ U.length ∧ Legal K V ∧ ∃ x21 ∈ K ++ V, ∃ x22 ∈ K ++ V,
      (if a < 21 then x21 ||| x22 else x21 &&& x22) = 2097151 ∧ x21.testBit a ≠ x22.testBit a ∧
      x21.testBit a = x22.testBit b ∧ x22.testBit a = x21.testBit b := by
  obtain ⟨hqa, hqb, hcov⟩ := hx2
  obtain ⟨V, hmap, hV⟩ := lift_program K q U hU
  have hmem : ∀ x ∈ K.map (· &&& q) ++ U, ∃ u ∈ K ++ V, u &&& q = x := by
    intro x hx
    have : x ∈ (K ++ V).map (· &&& q) := by rw [List.map_append, hmap]; exact hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp this
    exact ⟨u, hu, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hmem x8 h8
  obtain ⟨w, hw, rfl⟩ := hmem x9 h9
  simp only [Nat.testBit_and, hqa, hqb, Bool.and_true] at hne h1 h2
  refine ⟨V, by rw [← hmap, List.length_map], hV, u, hu, w, hw, ?_, hne, h1, h2⟩
  have hub := legal_bounded K V hV hK u hu
  have hwb := legal_bounded K V hV hK w hw
  have mu := legal_monotone K V hV u hu
  have mw := legal_monotone K V hV w hw
  have h21 : ∀ j, Nat.testBit 2097151 j = decide (j < 21) := by
    intro j; rw [c21, Nat.testBit_two_pow_sub_one]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 59
  · obtain ⟨k, hk59, hqk, hside, hord⟩ := hcov j hj
    have hk := congrArg (fun v => Nat.testBit v k) heq
    by_cases hj21 : j < 21
    · have hk21 : k < 21 := hside.mpr hj21
      have hd : ∀ x ∈ K, x.testBit k = true → x.testBit j = true := by
        intro x hx; have := hord x hx; simpa [hj21] using this
      have mu' := mu k j hd
      have mw' := mw k j hd
      by_cases ha : a < 21
      · simp only [ha, if_true] at hk ⊢
        have hk' : u.testBit k = true ∨ w.testBit k = true := by
          simpa [Nat.testBit_or, Nat.testBit_and, h21, hqk, hk21] using hk
        simp only [Nat.testBit_or, h21, hj21, decide_true]
        rcases hk' with h | h
        · simp [mu' h]
        · simp [mw' h]
      · simp only [ha, if_false] at hk ⊢
        have hk' : u.testBit k = true ∧ w.testBit k = true := by
          simpa [Nat.testBit_and, h21, hqk, hk21] using hk
        simp only [Nat.testBit_and, h21, hj21, decide_true]
        simp [mu' hk'.1, mw' hk'.2]
    · have hk21 : ¬ k < 21 := fun h => hj21 (hside.mp h)
      have hd : ∀ x ∈ K, x.testBit j = true → x.testBit k = true := by
        intro x hx; have := hord x hx; simpa [hj21] using this
      have mu' := mu j k hd
      have mw' := mw j k hd
      have nu : u.testBit k = false → u.testBit j = false := by
        intro h; cases e : u.testBit j
        · rfl
        · have := mu' e; rw [h] at this; exact absurd this (by decide)
      have nw : w.testBit k = false → w.testBit j = false := by
        intro h; cases e : w.testBit j
        · rfl
        · have := mw' e; rw [h] at this; exact absurd this (by decide)
      by_cases ha : a < 21
      · simp only [ha, if_true] at hk ⊢
        have hk' : u.testBit k = false ∧ w.testBit k = false := by
          simpa [Nat.testBit_or, Nat.testBit_and, h21, hqk, hk21] using hk
        simp [Nat.testBit_or, h21, hj21, nu hk'.1, nw hk'.2]
      · simp only [ha, if_false] at hk ⊢
        have hk' : u.testBit k = false ∨ w.testBit k = false := by
          have hk2 : (u.testBit k && w.testBit k) = false := by
            simpa [Nat.testBit_and, h21, hqk, hk21] using hk
          cases e1 : u.testBit k
          · exact Or.inl rfl
          · right; simpa [e1] using hk2
        rcases hk' with h | h
        · simp [Nat.testBit_and, h21, hj21, nu h]
        · simp [Nat.testBit_and, h21, hj21, nw h]
  · have hp : 2 ^ 59 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : u.testBit j = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hub hp)
    have e2 : w.testBit j = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hwb hp)
    have hj21 : ¬ j < 21 := by omega
    split_ifs <;> simp [Nat.testBit_or, Nat.testBit_and, h21, hj21, e1, e2]

end PEqualNP.Outside.L_meta_6468

theorem PEqualNP.Outside.L_meta_6468 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 x5 : ℕ) => x3.testBit x4 = Bool.true ∧ x3.testBit x5 = Bool.true ∧ ∀ x6 < (59 : ℕ), ∃ x8 < (59 : ℕ), x3.testBit x8 = Bool.true ∧ (x8 < (21 : ℕ) ↔ x6 < (21 : ℕ)) ∧ ∀ x9 ∈ x2, if x6 < (21 : ℕ) then x9.testBit x8 = Bool.true → x9.testBit x6 = Bool.true else x9.testBit x6 = Bool.true → x9.testBit x8 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 x6 : ℕ) (x7 : List ℕ) (x8 x9 : ℕ),   (∀ x10 ∈ x3, x10 < (2 : ℕ) ^ (59 : ℕ)) →     x2 x3 x4 x5 x6 →       have x12 : List ℕ := List.map (fun (x12 : ℕ) => x12 &&& x4) x3;       x1 x12 x7 → x8 ∈ x12 ++ x7 → x9 ∈ x12 ++ x7 → (if x5 < (21 : ℕ) then x8 ||| x9 else x8 &&& x9) = (2097151 : ℕ) &&& x4 → x8.testBit x5 ≠ x9.testBit x5 → x8.testBit x5 = x9.testBit x6 → x9.testBit x5 = x8.testBit x6 → ∃ (x20 : List ℕ), x20.length ≤ x7.length ∧ x1 x3 x20 ∧ ∃ x21 ∈ x3 ++ x20, ∃ x22 ∈ x3 ++ x20, (if x5 < (21 : ℕ) then x21 ||| x22 else x21 &&& x22) = (2097151 : ℕ) ∧ x21.testBit x5 ≠ x22.testBit x5 ∧ x21.testBit x5 = x22.testBit x6 ∧ x22.testBit x5 = x21.testBit x6 := PEqualNP.Outside.L_meta_6468.main
