import PEqualNP.Library.SearchHelpers.Encoding
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate

/-!
# Helpers: a criterion for the satisfiability of a 2-CNF formula

Helper module (proofs only, no statement may use it).

A clause `[a]` forces `a` from the negation of `a`; a clause `[a, b]` forces `b` from the
negation of `a` and `a` from the negation of `b` (`forced`). The closure of a literal is computed
by a bounded procedure: the formula is rotated, one clause at a time, and the literals forced by
the clause in front from the list so far are appended to the list (`rot`, `clos`). The main
result is `sat_iff` (Krom 1967): a formula whose clauses have one or two literals is satisfiable
exactly when no literal `l` of it has the negation of `l` in the closure of `l` and `l` in the
closure of its negation, for any number of rotations at least the number of clauses times the
number of literal occurrences plus one.
-/

namespace PEqualNP.Library.SearchHelpers.TwoSat

open PEqualNP.Search

/-- The negation of a literal. -/
def neg (l : Literal) : Literal := (l.1, !l.2)

@[simp] theorem neg_neg (l : Literal) : neg (neg l) = l := by simp [neg]

theorem eval_neg (σ : Assignment) (l : Literal) :
    Literal.eval σ (neg l) = !Literal.eval σ l := by
  obtain ⟨v, b⟩ := l
  simp only [neg, Literal.eval]
  cases σ v <;> cases b <;> rfl

/-- The literals a clause of one or two literals forces from the literals of `L`. -/
def forced : Clause → List Literal → List Literal
  | [a], L => if neg a ∈ L then [a] else []
  | [a, b], L => (if neg a ∈ L then [b] else []) ++ (if neg b ∈ L then [a] else [])
  | _, _ => []

theorem mem_forced_single (c : Clause) (u x : Literal) :
    x ∈ forced c [u] ↔
      (c = [x] ∧ u = neg x) ∨ ∃ y, (c = [y, x] ∨ c = [x, y]) ∧ u = neg y := by
  match c with
  | [] => simp [forced]
  | [a] =>
    by_cases h : neg a = u
    · subst h
      simp [forced]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, -⟩; rfl
    · have h' : ¬ (u = neg a) := fun e => h e.symm
      simp [forced, h]
      rintro rfl
      exact h'
  | [a, b] =>
    simp only [forced, List.mem_singleton, List.mem_append]
    constructor
    · rintro (h | h)
      · split_ifs at h with h1
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨a, Or.inl rfl, h1.symm⟩
        · simp at h
      · split_ifs at h with h1
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨b, Or.inr rfl, h1.symm⟩
        · simp at h
    · rintro (⟨h, -⟩ | ⟨y, h | h, rfl⟩)
      · simp at h
      · simp only [List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        left; simp
      · simp only [List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        right; simp
  | _ :: _ :: _ :: _ => simp [forced]

theorem mem_forced (c : Clause) (L : List Literal) (x : Literal) :
    x ∈ forced c L ↔ ∃ u ∈ L, x ∈ forced c [u] := by
  match c with
  | [] => simp [forced]
  | [a] =>
    by_cases h : neg a ∈ L
    · simp only [forced, h, ite_true, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨neg x, h, by simp⟩
      · rintro ⟨u, -, hu⟩
        split_ifs at hu
        · simpa using hu
        · simp at hu
    · simp only [forced, h, ite_false, List.mem_singleton, List.not_mem_nil, false_iff]
      rintro ⟨u, hu, hx⟩
      split_ifs at hx with h1
      · exact h (h1 ▸ hu)
      · simp at hx
  | [a, b] =>
    simp only [forced, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · split_ifs at h with h1
        · exact ⟨neg a, h1, Or.inl (by simpa using h)⟩
        · simp at h
      · split_ifs at h with h1
        · exact ⟨neg b, h1, Or.inr (by simpa using h)⟩
        · simp at h
    · rintro ⟨u, hu, h | h⟩
      · split_ifs at h with h1
        · left; rw [ite_eq_left (h1 ▸ hu)]; exact h
        · simp at h
      · split_ifs at h with h1
        · right; rw [ite_eq_left (h1 ▸ hu)]; exact h
        · simp at h
  | _ :: _ :: _ :: _ => simp [forced]

theorem forced_mono (c : Clause) {L L' : List Literal} (h : L ⊆ L') :
    forced c L ⊆ forced c L' := by
  intro x hx
  obtain ⟨u, hu, hx⟩ := (mem_forced c L x).1 hx
  exact (mem_forced c L' x).2 ⟨u, h hu, hx⟩

theorem forced_sub (c : Clause) (L : List Literal) : forced c L ⊆ c := by
  intro x hx
  obtain ⟨u, -, hx⟩ := (mem_forced c L x).1 hx
  rcases (mem_forced_single c u x).1 hx with ⟨rfl, -⟩ | ⟨y, rfl | rfl, -⟩ <;> simp

/-- An edge of the implication graph of `φ`. -/
def Edge (φ : CNF) (u v : Literal) : Prop := ∃ c ∈ φ, v ∈ forced c [u]

/-- Reachability in the implication graph of `φ`. -/
abbrev Reach (φ : CNF) : Literal → Literal → Prop := Relation.ReflTransGen (Edge φ)

theorem forced_skew {c : Clause} {u v : Literal} (h : v ∈ forced c [u]) :
    neg u ∈ forced c [neg v] := by
  rcases (mem_forced_single c u v).1 h with ⟨rfl, rfl⟩ | ⟨y, rfl | rfl, rfl⟩ <;>
    simp [forced]

theorem reach_neg {φ : CNF} {u v : Literal} (h : Reach φ u v) : Reach φ (neg v) (neg u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨c, hc, hv⟩ := hbc
    exact Relation.ReflTransGen.head ⟨c, hc, forced_skew hv⟩ ih

theorem forced_sound {σ : Assignment} {c : Clause} {u v : Literal}
    (hc : Clause.eval σ c = true) (h : v ∈ forced c [u]) (hu : Literal.eval σ u = true) :
    Literal.eval σ v = true := by
  rcases (mem_forced_single c u v).1 h with ⟨rfl, rfl⟩ | ⟨y, rfl | rfl, rfl⟩ <;>
    simp_all [Clause.eval, eval_neg]

theorem reach_sound {σ : Assignment} {φ : CNF} (hσ : CNF.eval σ φ = true) {u v : Literal}
    (h : Reach φ u v) (hu : Literal.eval σ u = true) : Literal.eval σ v = true := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih =>
    obtain ⟨c, hc, hv⟩ := hbc
    exact forced_sound (List.all_eq_true.1 hσ c hc) hv ih

theorem not_both {φ : CNF} (hs : Satisfiable φ) (l : Literal) :
    ¬ (Reach φ l (neg l) ∧ Reach φ (neg l) l) := by
  rintro ⟨h1, h2⟩
  obtain ⟨σ, hσ⟩ := hs
  cases hl : Literal.eval σ l with
  | true =>
    have := reach_sound hσ h1 hl
    rw [eval_neg, hl] at this
    exact absurd this (by simp)
  | false =>
    have h3 : Literal.eval σ (neg l) = true := by rw [eval_neg, hl]; rfl
    have := reach_sound hσ h2 h3
    rw [hl] at this
    exact absurd this (by simp)

/-! ### The assignment, built one variable at a time -/

/-- A set of literals closed under the edges and without a complementary pair. -/
structure Good (φ : CNF) (S : Set Literal) : Prop where
  closed : ∀ u v, u ∈ S → Edge φ u v → v ∈ S
  cons : ∀ u, u ∈ S → neg u ∉ S

theorem Good.reach {φ : CNF} {S : Set Literal} (hS : Good φ S) {u v : Literal} (hu : u ∈ S)
    (h : Reach φ u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hS.closed _ _ ih hbc

theorem extend_core {φ : CNF} {S : Set Literal} (hS : Good φ S) (a : Literal)
    (hna : ¬ Reach φ a (neg a)) (hnS : neg a ∉ S) : Good φ (S ∪ {x | Reach φ a x}) := by
  refine ⟨?_, ?_⟩
  · rintro u v (hu | hu) he
    · exact Or.inl (hS.closed u v hu he)
    · exact Or.inr (Relation.ReflTransGen.tail hu he)
  · rintro u (hu | hu) (hv | hv)
    · exact hS.cons u hu hv
    · have h := reach_neg hv
      rw [neg_neg] at h
      exact hnS (hS.reach hu h)
    · exact hnS (hS.reach hv (reach_neg hu))
    · have h := reach_neg hv
      rw [neg_neg] at h
      exact hna (Relation.ReflTransGen.trans hu h)

theorem extend {φ : CNF} {S : Set Literal} (hS : Good φ S) (l : Literal)
    (hl : ¬ (Reach φ l (neg l) ∧ Reach φ (neg l) l)) :
    ∃ S', S ⊆ S' ∧ Good φ S' ∧ (l ∈ S' ∨ neg l ∈ S') := by
  by_cases h1 : l ∈ S
  · exact ⟨S, subset_rfl, hS, Or.inl h1⟩
  by_cases h2 : neg l ∈ S
  · exact ⟨S, subset_rfl, hS, Or.inr h2⟩
  by_cases hr : Reach φ l (neg l)
  · have hr' : ¬ Reach φ (neg l) (neg (neg l)) := by
      rw [neg_neg]; exact fun h => hl ⟨hr, h⟩
    refine ⟨_, Set.subset_union_left, extend_core hS (neg l) hr' (by rwa [neg_neg]), ?_⟩
    exact Or.inr (Or.inr Relation.ReflTransGen.refl)
  · refine ⟨_, Set.subset_union_left, extend_core hS l hr h2, ?_⟩
    exact Or.inl (Or.inr Relation.ReflTransGen.refl)

theorem exists_good (φ : CNF) : ∀ ls : List Literal,
    (∀ l ∈ ls, ¬ (Reach φ l (neg l) ∧ Reach φ (neg l) l)) →
    ∃ S, Good φ S ∧ ∀ l ∈ ls, l ∈ S ∨ neg l ∈ S := by
  intro ls
  induction ls with
  | nil =>
    intro _
    exact ⟨∅, ⟨fun u v hu _ => absurd hu (Set.notMem_empty u),
      fun u hu => absurd hu (Set.notMem_empty u)⟩, by simp⟩
  | cons l ls ih =>
    intro h
    obtain ⟨S, hS, hls⟩ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨S', hsub, hS', hl⟩ := extend hS l (h l List.mem_cons_self)
    refine ⟨S', hS', ?_⟩
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact hl
    · rcases hls l' hl' with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (hsub h)

theorem sat_of_good {φ : CNF} (hw : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2) {S : Set Literal}
    (hS : Good φ S) (hT : ∀ c ∈ φ, ∀ l ∈ c, l ∈ S ∨ neg l ∈ S) : Satisfiable φ := by
  classical
  refine ⟨fun v => decide ((v, true) ∈ S), ?_⟩
  have key : ∀ l ∈ S, Literal.eval (fun v => decide ((v, true) ∈ S)) l = true := by
    rintro ⟨v, b⟩ hl
    cases b with
    | true => simp [Literal.eval, hl]
    | false =>
      have h : (v, true) ∉ S := hS.cons _ hl
      simp [Literal.eval, h]
  refine List.all_eq_true.2 (fun c hc => ?_)
  match c, hw c hc with
  | [a], _ =>
    have ha : a ∈ S := by
      rcases hT _ hc a (by simp) with h | h
      · exact h
      · exact hS.closed _ _ h ⟨_, hc, by simp [forced]⟩
    simp [Clause.eval, key a ha]
  | [a, b], _ =>
    rcases hT _ hc a (by simp) with h | h
    · simp [Clause.eval, key a h]
    · have hb : b ∈ S := hS.closed _ _ h ⟨_, hc, by simp [forced]⟩
      simp [Clause.eval, key b hb]
  | [], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h

/-! ### The closure by rotation -/

/-- One rotation: the clause in front goes to the back, and the literals it forces from the
list are appended to the list. -/
def rot : CNF × List Literal → CNF × List Literal
  | ([], L) => ([], L)
  | (c :: F, L) => (F ++ [c], L ++ forced c L)

/-- One sweep over the clauses of `F`. -/
def sweep : CNF → List Literal → List Literal
  | [], L => L
  | c :: F, L => sweep F (L ++ forced c L)

/-- The closure of the literal `a` after `N` rotations. -/
def clos (N : ℕ) (φ : CNF) (a : Literal) : List Literal := (rot^[N] (φ, [a])).2

theorem rot_iter_append : ∀ (F1 F2 : CNF) (L : List Literal),
    rot^[F1.length] (F1 ++ F2, L) = (F2 ++ F1, sweep F1 L)
  | [], F2, L => by simp [sweep]
  | c :: F1, F2, L => by
    rw [List.length_cons, Function.iterate_succ_apply, List.cons_append, rot,
      List.append_assoc, rot_iter_append F1 (F2 ++ [c]) _, sweep]
    simp

theorem rot_sweep_iter (φ : CNF) (k : ℕ) : ∀ L : List Literal,
    rot^[φ.length * k] (φ, L) = (φ, (sweep φ)^[k] L) := by
  induction k with
  | zero => intro L; rfl
  | succ k ih =>
    intro L
    have h := rot_iter_append φ [] L
    simp only [List.append_nil, List.nil_append] at h
    rw [Nat.mul_succ, Function.iterate_add_apply, h, ih, Function.iterate_succ_apply]

theorem rot_mono (s : CNF × List Literal) : s.2 ⊆ (rot s).2 := by
  obtain ⟨F, L⟩ := s
  cases F with
  | nil => exact List.Subset.refl _
  | cons c F => exact List.subset_append_left _ _

theorem rot_iter_mono (r : ℕ) : ∀ s : CNF × List Literal, s.2 ⊆ (rot^[r] s).2 := by
  induction r with
  | zero => intro s; exact List.Subset.refl _
  | succ r ih =>
    intro s
    rw [Function.iterate_succ_apply]
    exact List.Subset.trans (rot_mono s) (ih (rot s))

theorem rot_inv (φ : CNF) (a : Literal) (s : CNF × List Literal)
    (h : (∀ c ∈ s.1, c ∈ φ) ∧ ∀ x ∈ s.2, Reach φ a x) :
    (∀ c ∈ (rot s).1, c ∈ φ) ∧ ∀ x ∈ (rot s).2, Reach φ a x := by
  obtain ⟨F, L⟩ := s
  cases F with
  | nil => exact h
  | cons c F =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro c' hc'
      simp only [rot, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · exact h1 c' (List.mem_cons_of_mem _ hc')
      · exact h1 c' List.mem_cons_self
    · intro x hx
      simp only [rot, List.mem_append] at hx
      rcases hx with hx | hx
      · exact h2 x hx
      · obtain ⟨u, hu, hx⟩ := (mem_forced c L x).1 hx
        exact Relation.ReflTransGen.tail (h2 u hu) ⟨c, h1 c List.mem_cons_self, hx⟩

theorem clos_sound {N : ℕ} {φ : CNF} {a x : Literal} (h : x ∈ clos N φ a) : Reach φ a x := by
  have key : ∀ n : ℕ, (∀ c ∈ (rot^[n] (φ, [a])).1, c ∈ φ) ∧
      ∀ x ∈ (rot^[n] (φ, [a])).2, Reach φ a x := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun c hc => hc, fun x hx => ?_⟩
      simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hx
      subst hx
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact rot_inv φ a _ ih
  exact (key N).2 x h

theorem sweep_sub : ∀ (F : CNF) (L : List Literal), L ⊆ sweep F L
  | [], L => List.Subset.refl _
  | c :: F, L => List.Subset.trans (List.subset_append_left _ _) (sweep_sub F _)

theorem forced_sweep : ∀ (F : CNF) (L : List Literal) (c : Clause), c ∈ F →
    forced c L ⊆ sweep F L
  | [], L, c, h => by simp at h
  | c' :: F, L, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.Subset.trans (List.subset_append_right _ _) (sweep_sub F _)
    · exact List.Subset.trans (forced_mono c (List.subset_append_left _ _)) (forced_sweep F _ c h)

theorem sweep_mem : ∀ (F : CNF) (L : List Literal) (x : Literal), x ∈ sweep F L →
    x ∈ L ∨ x ∈ F.flatMap id
  | [], L, x, h => Or.inl h
  | c :: F, L, x, h => by
    rcases sweep_mem F _ x h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [forced_sub c L h])
    · exact Or.inr (by simp at h ⊢; exact Or.inr h)

theorem closed_reach {φ : CNF} {L : List Literal} (hL : ∀ c ∈ φ, forced c L ⊆ L)
    {u v : Literal} (hu : u ∈ L) (h : Reach φ u v) : v ∈ L := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih =>
    obtain ⟨c, hc, hv⟩ := hbc
    exact hL c hc ((mem_forced c L _).2 ⟨_, ih, hv⟩)

theorem sweep_iter_sub (φ : CNF) (a : Literal) (k : ℕ) :
    (sweep φ)^[k] [a] ⊆ a :: φ.flatMap id := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro x hx
    rcases sweep_mem φ _ x hx with h | h
    · exact ih h
    · exact List.mem_cons_of_mem _ h

theorem sweep_grow (φ : CNF) (a : Literal) (k : ℕ) :
    (∃ j < k, sweep φ ((sweep φ)^[j] [a]) ⊆ (sweep φ)^[j] [a]) ∨
      k + 1 ≤ ((sweep φ)^[k] [a]).toFinset.card := by
  induction k with
  | zero => right; simp
  | succ k ih =>
    rcases ih with ⟨j, hj, h⟩ | ih
    · exact Or.inl ⟨j, by omega, h⟩
    by_cases hs : sweep φ ((sweep φ)^[k] [a]) ⊆ (sweep φ)^[k] [a]
    · exact Or.inl ⟨k, by omega, hs⟩
    right
    rw [Function.iterate_succ_apply']
    have hss : ((sweep φ)^[k] [a]).toFinset ⊂ (sweep φ ((sweep φ)^[k] [a])).toFinset := by
      rw [Finset.ssubset_iff_of_subset]
      · obtain ⟨x, hx, hnx⟩ : ∃ x, x ∈ sweep φ ((sweep φ)^[k] [a]) ∧ x ∉ (sweep φ)^[k] [a] := by
          by_contra hc
          push Not at hc
          exact hs (fun x hx => hc x hx)
        exact ⟨x, by simpa using hx, by simpa using hnx⟩
      · intro x hx
        rw [List.mem_toFinset] at hx ⊢
        exact sweep_sub φ _ hx
    have := Finset.card_lt_card hss
    omega

theorem clos_complete {N : ℕ} {φ : CNF} (hN : φ.length * ((φ.flatMap id).length + 1) ≤ N)
    {a x : Literal} (h : Reach φ a x) : x ∈ clos N φ a := by
  rcases sweep_grow φ a ((φ.flatMap id).length + 1) with ⟨j, hj, hst⟩ | hc
  · have hcl : ∀ c ∈ φ, forced c ((sweep φ)^[j] [a]) ⊆ (sweep φ)^[j] [a] :=
      fun c hc => List.Subset.trans (forced_sweep φ _ c hc) hst
    have ha : a ∈ (sweep φ)^[j] [a] := by
      have := rot_iter_mono (φ.length * j) (φ, [a])
      rw [rot_sweep_iter] at this
      exact this (by simp)
    have hx := closed_reach hcl ha h
    have hle : φ.length * j ≤ N := (Nat.mul_le_mul_left _ (by omega)).trans hN
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [clos, Function.iterate_add_apply, rot_sweep_iter]
    exact rot_iter_mono r _ hx
  · exfalso
    have h1 : ((sweep φ)^[(φ.flatMap id).length + 1] [a]).toFinset ⊆
        (a :: φ.flatMap id).toFinset := by
      intro y hy
      rw [List.mem_toFinset] at hy ⊢
      exact sweep_iter_sub φ a _ hy
    have h2 := Finset.card_le_card h1
    have h3 := List.toFinset_card_le (a :: φ.flatMap id)
    simp only [List.length_cons] at h3
    omega

/-- The criterion (Krom 1967): a formula whose clauses have one or two literals is satisfiable
exactly when no literal of it has its negation in its closure and itself in the closure of its
negation. -/
theorem sat_iff {φ : CNF} (hw : ∀ c ∈ φ, c.length = 1 ∨ c.length = 2) {N : ℕ}
    (hN : φ.length * ((φ.flatMap id).length + 1) ≤ N) :
    Satisfiable φ ↔
      ∀ c ∈ φ, ∀ l ∈ c, ¬ (neg l ∈ clos N φ l ∧ l ∈ clos N φ (neg l)) := by
  constructor
  · rintro hs c - l - ⟨h1, h2⟩
    exact not_both hs l ⟨clos_sound h1, clos_sound h2⟩
  · intro h
    have hls : ∀ l ∈ φ.flatMap id, ¬ (Reach φ l (neg l) ∧ Reach φ (neg l) l) := by
      intro l hl
      obtain ⟨c, hc, hlc⟩ := List.mem_flatMap.1 hl
      rintro ⟨h1, h2⟩
      exact h c hc l hlc ⟨clos_complete hN h1, clos_complete hN h2⟩
    obtain ⟨S, hS, hT⟩ := exists_good φ _ hls
    exact sat_of_good hw hS
      (fun c hc l hl => hT l (List.mem_flatMap.2 ⟨c, hc, hl⟩))

end PEqualNP.Library.SearchHelpers.TwoSat
