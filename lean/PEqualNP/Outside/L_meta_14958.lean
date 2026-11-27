import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14958

namespace Reused_L_meta_11601

namespace Foundation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Sig := Nat × Nat

def top : Nat := 0x7ffffffffffffff
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (top ^^^ a.1, top ^^^ a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (allowNot : Bool) (a : Sig) : Nat :=
  if allowNot then a.1 ^^^ a.2 else a.1 &&& (top ^^^ a.2)
def cuts (allowNot : Bool) (ws : List Sig) : Nat :=
  ws.foldr (fun w v => sep allowNot w ||| v) 0

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def bounded (n : Nat) : Prop := ∀ i, 59 ≤ i → n.testBit i = false
def valid (a : Sig) : Prop := bounded a.1 ∧ bounded a.2

def rawInputs : List Sig :=
  [(0x3c3c2919e1653bb, 0x4444000100410ba),
   (0x03fcd696469a2c7, 0x088884944412205),
   (0x43c318e798e3cc4, 0x5556184390e18c0),
   (0x7c03e0f81f03f08, 0x2aa9e0b80f02700),
   (0x0003ff001ffc010, 0x33337b001bac000),
   (0x0003ffffe000020, 0x3bbbfffee000000)]

theorem testBit_top (i : Nat) : top.testBit i = decide (i < 59) := by
  have h : top = 2 ^ 59 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

theorem bounded_of_lt {n : Nat} (h : n < 2 ^ 59) : bounded n := fun i hi =>
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))

theorem bounded_zero : bounded 0 := fun i _ => by simp
theorem bounded_top : bounded top := fun i hi => by rw [testBit_top]; simp [Nat.not_lt.mpr hi]
theorem bounded_and {x y : Nat} (hx : bounded x) : bounded (x &&& y) := fun i hi => by
  simp [Nat.testBit_and, hx i hi]
theorem bounded_or {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ||| y) := fun i hi => by
  simp [Nat.testBit_or, hx i hi, hy i hi]
theorem bounded_xor {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ^^^ y) := fun i hi => by
  simp [Nat.testBit_xor, hx i hi, hy i hi]

theorem nat_eq_of_testBit {x y : Nat} (hx : bounded x) (hy : bounded y)
    (h : ∀ i < 59, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 59
  · exact h i hi
  · rw [hx i (by omega), hy i (by omega)]

theorem valid_zero : valid zero := ⟨bounded_zero, bounded_zero⟩
theorem valid_one : valid one := ⟨bounded_top, bounded_top⟩
theorem valid_target : valid target := ⟨bounded_top, bounded_zero⟩
theorem valid_neg {a : Sig} (ha : valid a) : valid (neg a) :=
  ⟨bounded_xor bounded_top ha.1, bounded_xor bounded_top ha.2⟩
theorem valid_bin {d : Bool} {a b : Sig} (ha : valid a) (hb : valid b) : valid (bin d a b) := by
  cases d
  · exact ⟨bounded_and ha.1, bounded_and ha.2⟩
  · exact ⟨bounded_or ha.1 hb.1, bounded_or ha.2 hb.2⟩

theorem valid_sep {allowNot : Bool} {a : Sig} (ha : valid a) : bounded (sep allowNot a) := by
  cases allowNot
  · exact bounded_and ha.1
  · exact bounded_xor ha.1 ha.2

theorem bounded_cuts {allowNot : Bool} {ws : List Sig} (hw : ∀ w ∈ ws, valid w) :
    bounded (cuts allowNot ws) := by
  induction ws with
  | nil => exact bounded_zero
  | cons a rest ih =>
    exact bounded_or (valid_sep (hw a (by simp))) (ih fun w h => hw w (by simp [h]))

theorem neg_neg {a : Sig} (ha : valid a) : neg (neg a) = a := by
  apply Prod.ext
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.1)) ha.1
    intro i _; simp
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.2)) ha.2
    intro i _; simp

theorem neg_zero : neg zero = one := by decide
theorem neg_one : neg one = zero := by decide

theorem proper_neg {a : Sig} (ha : valid a) (hp : proper a) : proper (neg a) := by
  constructor
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_one] at this
    exact hp.1 this

theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, Nat.and_comm, Nat.or_comm]

theorem bin_zero_left (d : Bool) (a : Sig) : bin d zero a = if d then a else zero := by
  cases d <;> simp [bin, zero]

theorem bin_zero_right (d : Bool) (a : Sig) : bin d a zero = if d then a else zero := by
  rw [bin_comm, bin_zero_left]

theorem bin_one_left (d : Bool) {a : Sig} (ha : valid a) : bin d one a = if d then one else a := by
  cases d
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.1
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.2
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.1) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.2) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]

theorem bin_one_right (d : Bool) {a : Sig} (ha : valid a) : bin d a one = if d then one else a := by
  rw [bin_comm, bin_one_left d ha]

theorem bin_self (d : Bool) (a : Sig) : bin d a a = a := by
  cases d <;> simp [bin, Nat.and_self, Nat.or_self]

def build : ℕ → Finset Sig → Prop
  | 0, av => target ∈ av
  | k+1, av =>
      build k av ∨
      (∃ a ∈ av, proper a ∧ build k (insert (neg a) av)) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ build k (insert (bin d a b) av))

def live : ℕ → ℕ → Finset Sig → Prop
  | 0, t, s => t = 0 ∧ s = {target}
  | k+1, t, s =>
      live k t s ∨
      (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
        ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
          ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest))

theorem compress {k : ℕ} {av : Finset Sig} (h : build k av) :
    ∃ t, ∃ s ⊆ av, live k t s := by
  induction k generalizing av with
  | zero =>
    exact ⟨0, {target}, Finset.singleton_subset_iff.mpr h, rfl, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, hpa, tail⟩ | ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, tail⟩
    · obtain ⟨t, s, hs, hrun⟩ := ih skip
      exact ⟨t, s, hs, Or.inl hrun⟩
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : neg a ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : neg a ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (neg a)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨t + 1, s, hs, Or.inr (Or.inl ⟨by omega, a, by simp [s], hpa,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : bin d a b ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : bin d a b ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (bin d a b)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨t, s, hs, Or.inr (Or.inr ⟨a, by simp [s], b, by simp [s], hab, hpa, hpb, d, hpz,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {k t : ℕ} {s : Finset Sig} (h : live k t s) : s.card + t ≤ k + 1 := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ k ih =>
    rcases h with skip | ⟨ht, a, _, _, hout, rest, rfl, tail⟩ |
        ⟨a, _, b, _, _, _, _, d, _, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : neg a ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega
    · have hzrest : bin d a b ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

def differs (allowNot : Bool) (i : Fin 59) (w : Sig) : Prop :=
  if allowNot then w.1.testBit i.val ≠ w.2.testBit i.val
  else w.1.testBit i.val = true ∧ w.2.testBit i.val = false

theorem differs_mono {b : Bool} {i : Fin 59} {w : Sig} (h : differs b i w) :
    differs true i w := by
  cases b
  · simp only [differs, ite_true] at h ⊢
    rw [h.1, h.2]; decide
  · exact h

theorem differs_target (allowNot : Bool) (i : Fin 59) : differs allowNot i target := by
  cases allowNot <;> simp [differs, target, testBit_top, i.isLt]

theorem differs_neg {b : Bool} {i : Fin 59} {a : Sig} (h : differs b i (neg a)) :
    differs true i a := by
  have h' := differs_mono h
  simp only [differs, ite_true, neg, Nat.testBit_xor, testBit_top, i.isLt, decide_true] at h' ⊢
  cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;> simp_all

theorem differs_bin {b d : Bool} {i : Fin 59} {a c : Sig} (h : differs b i (bin d a c)) :
    differs b i a ∨ differs b i c := by
  cases b <;> cases d <;>
    simp only [differs, bin, Bool.false_eq_true, ite_true, ite_false] at h ⊢ <;>
    (try simp only [Nat.testBit_and] at h) <;>
    (try simp only [Nat.testBit_or] at h) <;>
    cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;>
    cases hc1 : c.1.testBit i.val <;> cases hc2 : c.2.testBit i.val <;> simp_all

theorem live_separates (i : Fin 59) {k t : ℕ} {s : Finset Sig} (h : live k t s) :
    ∃ w ∈ s, differs (decide (0 < t)) i w := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨target, by simp, differs_target false i⟩
  | succ k ih =>
    rcases h with skip | ⟨ht, a, ha, _, _, rest, rfl, tail⟩ |
        ⟨a, ha, b, hb, _, _, _, d, _, _, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      have hdt : decide (0 < t) = true := by simp [ht]
      rw [hdt]
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, differs_neg hD⟩
      · exact ⟨w, by simp [hw], differs_mono hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases differs_bin hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {k t : ℕ} {s : Finset Sig} (h : live (k+1) t s) :
    (t = 0 ∧ s = {target}) ∨
    (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
      ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
      ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
        ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest)) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step1 | step2
    · rcases ih skip with done | ⟨ht, a, ha, hpa, hn, r, hs, tail⟩ |
          ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, tail⟩
      · exact Or.inl done
      · exact Or.inr (Or.inl ⟨ht, a, ha, hpa, hn, r, hs, Or.inl tail⟩)
      · exact Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, Or.inl tail⟩)
    · exact Or.inr (Or.inl step1)
    · exact Or.inr (Or.inr step2)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) ha'
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha' hb'
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

theorem testBit_sep (allowNot : Bool) (w : Sig) (i : Fin 59) :
    (sep allowNot w).testBit i.val = true ↔ differs allowNot i w := by
  cases allowNot
  · simp only [sep, differs, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_xor,
      testBit_top, i.isLt, decide_true]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp
  · simp only [sep, differs, ite_true, Nat.testBit_xor]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp

theorem cuts_spec (allowNot : Bool) (ws : List Sig) (i : Fin 59) :
    (cuts allowNot ws).testBit i.val = true ↔ ∃ w ∈ ws, differs allowNot i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep allowNot a ||| cuts allowNot rest).testBit i.val = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, testBit_sep]
    simp

theorem cuts_full {k t : ℕ} {ws : List Sig} (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : cuts (decide (0 < t)) ws = top := by
  apply nat_eq_of_testBit (bounded_cuts hv) bounded_top
  intro j hj
  have hw := live_separates ⟨j, hj⟩ h
  have hbit := (cuts_spec (decide (0 < t)) ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [hbit, testBit_top]
  simp [hj]

theorem recover_kept1 {ws r : List Sig} {a : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : v ∈ insert a r.toFinset ↔ v ∈ insert a needed := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

def keepChoices (a b : Sig) (r : List Sig) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept2 {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : v ∈ insert a (insert b r.toFinset) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List Sig} (hn : ws.Nodup) (hs : ws.toFinset = {target}) :
    ws = [target] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchUnary (extra : ℕ) (tNext : ℕ) (ws : List Sig) (next : List Sig → Bool)
    (a : Sig) (rest : List Sig) : Bool :=
  let na := neg a
  if na == zero || na == one || ws.contains na then false
  else
    let allowNext := tNext != 0
    let base := cuts allowNext rest
    let v := sep allowNext na ||| base
    ((v == top) && next (na :: rest)) ||
    ((extra != 0) && (v ||| sep allowNext a == top) && next (na :: a :: rest))

def dispatchBin (extra : ℕ) (allowNot : Bool) (ws : List Sig) (next : List Sig → Bool)
    (a b : Sig) (rest : List Sig) : Bool :=
  let base := cuts allowNot rest
  let sa := sep allowNot a
  let sb := sep allowNot b
  let tryZ (z : Sig) : Bool :=
    if z == zero || z == one || ws.contains z then false
    else
      let v := sep allowNot z ||| base
      ((v == top) && next (z :: rest)) ||
      ((extra != 0) && (((v ||| sa == top) && next (z :: a :: rest)) ||
                        ((v ||| sb == top) && next (z :: b :: rest)))) ||
      ((extra ≥ 2) && (v ||| sa ||| sb == top) && next (z :: a :: b :: rest))
  tryZ (bin false a b) || tryZ (bin true a b)

def search : ℕ → ℕ → List Sig → Bool
  | 0, t, ws => (t == 0) && (ws == [target])
  | k+1, t, ws =>
      ((t == 0) && (ws == [target])) ||
      (if t == 0 then false
       else
         let extra := k + 2 - ws.length - t
         (singles ws).any (fun (a, rest) => dispatchUnary extra (t - 1) ws (search k (t - 1)) a rest)) ||
      (let extra := k + 2 - ws.length - t
       let allowNot := t != 0
       (pairs ws).any (fun (a, b, rest) => dispatchBin extra allowNot ws (search k t) a b rest))

theorem dispatchUnary_complete {k tNext : ℕ} {ws r kept : List Sig} {a : Sig}
    (next : List Sig → Bool)
    (hp : proper (neg a)) (hout : neg a ∉ ws)
    (hk : kept ∈ [r, a :: r])
    (he : k + 2 - ws.length - (tNext + 1) = k + 1 - r.length - (tNext + 1))
    (hlen : kept.length + tNext ≤ k)
    (hc : cuts (decide (0 < tNext)) (neg a :: kept) = top)
    (ht : next (neg a :: kept) = true) :
    dispatchUnary (k + 2 - ws.length - (tNext + 1)) tNext ws next a r = true := by
  have hcond : (neg a == zero || neg a == one || ws.contains (neg a)) = false := by
    simp [hp.1, hp.2, hout]
  dsimp only [dispatchUnary]
  rw [hcond]
  simp only [Bool.false_eq_true, ite_false]
  have hallow : (tNext != 0) = decide (0 < tNext) := by cases tNext <;> rfl
  rw [hallow]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · simp only [cuts, List.foldr_cons] at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact Or.inl ⟨hc, ht⟩
  · simp only [cuts, List.foldr_cons] at hc
    simp only [List.length_cons] at hlen
    have hex : (k + 2 - ws.length - (tNext + 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; omega
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    refine Or.inr ⟨⟨hex, ?_⟩, ht⟩
    calc (sep (decide (0 < tNext)) (neg a) ||| cuts (decide (0 < tNext)) r) ||| sep (decide (0 < tNext)) a
        = sep (decide (0 < tNext)) (neg a) ||| (sep (decide (0 < tNext)) a ||| cuts (decide (0 < tNext)) r) := by
          ac_rfl
      _ = top := hc

theorem dispatchBin_complete {k t : ℕ} {ws r kept : List Sig} {a b : Sig} {d : Bool}
    (next : List Sig → Bool)
    (hpz : proper (bin d a b)) (hout : bin d a b ∉ ws)
    (hk : kept ∈ keepChoices a b r)
    (he : k + 2 - ws.length - t = k - r.length - t)
    (hlen : kept.length + t ≤ k)
    (hc : cuts (decide (0 < t)) (bin d a b :: kept) = top)
    (ht : next (bin d a b :: kept) = true) :
    dispatchBin (k + 2 - ws.length - t) (t != 0) ws next a b r = true := by
  have hallow : (t != 0) = decide (0 < t) := by cases t <;> rfl
  dsimp only [dispatchBin]
  rw [hallow]
  have hcond : (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = false := by
    simp [hpz.1, hpz.2, hout]
  have htry : (if (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = true then false else
      let v := sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r
      ((v == top) && next (bin d a b :: r)) ||
      ((k + 2 - ws.length - t != 0) &&
        (((v ||| sep (decide (0 < t)) a == top) && next (bin d a b :: a :: r)) ||
         ((v ||| sep (decide (0 < t)) b == top) && next (bin d a b :: b :: r)))) ||
      ((k + 2 - ws.length - t ≥ 2) &&
        (v ||| sep (decide (0 < t)) a ||| sep (decide (0 < t)) b == top) &&
        next (bin d a b :: a :: b :: r))) = true := by
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [cuts, List.foldr_cons] at hc <;>
      (try simp only [List.length_cons] at hlen) <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
    · exact Or.inl (Or.inl ⟨hc, ht⟩)
    · refine Or.inl (Or.inr ⟨by omega, Or.inl ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inl (Or.inr ⟨by omega, Or.inr ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inr ⟨⟨by omega, ?_⟩, ht⟩
      calc ((sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r)) := by ac_rfl
        _ = top := hc
  cases d
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inl htry)
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inr htry)

theorem search_complete (k t : ℕ) (ws : List Sig) (hn : ws.Nodup) (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : search k t ws = true := by
  induction k generalizing t ws with
  | zero =>
    obtain ⟨rfl, hs⟩ := h
    simp [search, singleton_list hn hs]
  | succ k ih =>
    rcases first_live h with ⟨rfl, hs⟩ |
        ⟨ht, a, ha, hpa, hout, needed, hs, tail⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hout, needed, hs, tail⟩
    · simp [search, singleton_list hn hs]
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
      have hznew : neg a ∉ kept := by
        intro hu
        apply hout
        rw [hs]
        exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)
      have hnd : (neg a :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live k (t - 1) (neg a :: kept).toFinset := by
        simpa [hfin] using tail
      have hv_kept : ∀ w ∈ neg a :: kept, valid w := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact valid_neg (hv a (List.mem_toFinset.mp ha))
        · apply hv w
          apply List.mem_toFinset.mp
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw)
      have hcard := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
      have hlen_ws : ws.length = r.length + 1 := by
        have := hp.length_eq; simp at this; exact this
      cases t with
      | zero => omega
      | succ t' =>
        simp only [Nat.add_sub_cancel] at hl hcard
        have hrec := ih t' (neg a :: kept) hnd hv_kept hl
        have hcut := cuts_full hv_kept hl
        have hdisp := dispatchUnary_complete (k := k) (tNext := t') (ws := ws) (r := r) (kept := kept)
          (a := a) (search k t') (proper_neg (hv a (List.mem_toFinset.mp ha)) hpa)
          (fun hmem => hout (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega) hcut hrec
        simp only [search, Bool.or_eq_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          beq_iff_eq, ite_false, Nat.add_sub_cancel]
        exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨(a, r), hm, hdisp⟩))
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : Sig} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed))
          (ha' : a ∈ ws) (hb' : b ∈ ws)
          (hpz' : proper (bin d a b)) (hout' : bin d a b ∉ ws.toFinset)
          (htail : live k t (insert (bin d a b) needed)) :
          dispatchBin (k + 2 - ws.length - t) (t != 0) ws (search k t) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept2 perm hn hset
        have hznew : bin d a b ∉ kept := by
          intro hu
          apply hout'
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
        have hnd : (bin d a b :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live k t (bin d a b :: kept).toFinset := by
          simpa [hfin] using htail
        have hv_kept : ∀ w ∈ bin d a b :: kept, valid w := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact valid_bin (hv a ha') (hv b hb')
          · apply hv w
            apply List.mem_toFinset.mp
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw))
        have hcard := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
        have hlen_ws : ws.length = r.length + 2 := by
          have := perm.length_eq; simp at this; exact this
        exact dispatchBin_complete (k := k) (t := t) (ws := ws) (r := r) (kept := kept)
          (a := a) (b := b) (d := d) (search k t) hpz'
          (fun hmem => hout' (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega)
          (cuts_full hv_kept hl) (ih t (bin d a b :: kept) hnd hv_kept hl)
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hpz hout tail⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha)
          (bin_comm d a b ▸ hpz) (bin_comm d a b ▸ hout) (bin_comm d a b ▸ tail)⟩

private def possible (w : List Sig) (z : Sig) : Bool :=
  z == zero || z == one || w.any (fun u => z == u || z == neg u ||
    w.any (fun v => z == bin false u v || z == bin true u v))

private def bit (k : Fin 118) (z : Sig) : Bool :=
  if k.val < 59 then z.2.testBit k.val else z.1.testBit (k.val - 59)

private theorem read_bit (w : List Sig) (i : ℕ) (k : Fin 118) :
    (w.map (bit k)).getD i false = bit k (w.getD i zero) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit, zero]

private theorem read_wire (w : List Sig) (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem bit_zero (k : Fin 118) : bit k zero = false := by
  unfold bit zero; split <;> simp

private theorem bit_one (k : Fin 118) : bit k one = true := by
  unfold bit one
  by_cases h : k.val < 59
  · simp [h, testBit_top]
  · simp [h, testBit_top, show k.val - 59 < 59 by omega]

private theorem bit_neg (k : Fin 118) (z : Sig) : bit k (neg z) = !(bit k z) := by
  unfold bit neg
  by_cases h : k.val < 59
  · simp [h, Nat.testBit_xor, testBit_top]
  · simp [h, Nat.testBit_xor, testBit_top, show k.val - 59 < 59 by omega]

private theorem bit_and (k : Fin 118) (x y : Sig) : bit k (bin false x y) = (bit k x && bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_and]

private theorem bit_or (k : Fin 118) (x y : Sig) : bit k (bin true x y) = (bit k x || bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_or]

private theorem atom {ws : List Sig} {x : Sig} (hx : x = zero ∨ x ∈ ws) :
    possible ws x ∧ possible ws (neg x) := by
  rcases hx with rfl | hx
  · simp [possible, neg_zero]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_possible {ws : List Sig} {x y : Sig} (hx : x = zero ∨ x ∈ ws) (hy : y = zero ∨ y ∈ ws) :
    possible ws (bin false x y) ∧ possible ws (bin true x y) := by
  rcases hx with rfl | hx
  · simpa [bin_zero_left] using (show possible ws zero ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [bin_zero_right] using (show possible ws zero ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w : List Sig) (hwv : ∀ u ∈ w, valid u) (g : Gate) (hg : legal g) :
    ∃ z, valid z ∧ possible w z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := read_wire w i
  have vmem (i : ℕ) : valid (w.getD i zero) := by
    rcases mem i with h | h
    · rw [h]; exact valid_zero
    · exact hwv _ h
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
    · exact ⟨zero, valid_zero, by simp [possible], by intro k; simp [step, GateOp.eval, bit_zero]⟩
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).1,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_and]⟩
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_or]⟩
        · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩

def represents (av : Finset Sig) (w : List Sig) : Prop :=
  ∀ u ∈ w, u = zero ∨ u = one ∨ u ∈ av

theorem classify {av : Finset Sig} {ws : List Sig}
    (hav : ∀ u ∈ av, proper u ∧ valid u)
    (hw : represents av ws) {z : Sig} (hz : possible ws z) :
    z = zero ∨ z = one ∨ z ∈ av ∨
      (∃ a ∈ av, proper a ∧ z = neg a) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d : Bool, proper z ∧ z = bin d a b) := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((rfl | rfl) | ⟨x, hx, (rfl | rfl) | ⟨y, hy, hh⟩⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rcases hw z hx with rfl | rfl | hxm
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl hxm))
  · rcases hw x hx with rfl | rfl | hxm
    · exact Or.inr (Or.inl neg_zero)
    · exact Or.inl neg_one
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hxm, (hav x hxm).1, rfl⟩)))
  · have binCase (d : Bool) :
        bin d x y = zero ∨ bin d x y = one ∨ bin d x y ∈ av ∨
        (∃ a ∈ av, proper a ∧ bin d x y = neg a) ∨
        (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d' : Bool, proper (bin d x y) ∧ bin d x y = bin d' a b) := by
      have hvx : valid x := by
        rcases hw x hx with rfl | rfl | hxm
        · exact valid_zero
        · exact valid_one
        · exact (hav x hxm).2
      have hvy : valid y := by
        rcases hw y hy with rfl | rfl | hym
        · exact valid_zero
        · exact valid_one
        · exact (hav y hym).2
      rcases hw x hx with rfl | rfl | hxm
      · rw [bin_zero_left]; cases d
        · exact Or.inl rfl
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
      · rw [bin_one_left d hvy]; cases d
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
        · exact Or.inr (Or.inl rfl)
      rcases hw y hy with rfl | rfl | hym
      · rw [bin_zero_right]; cases d
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hxm))
      · rw [bin_one_right d hvx]; cases d
        · exact Or.inr (Or.inr (Or.inl hxm))
        · exact Or.inr (Or.inl rfl)
      by_cases hxy : x = y
      · subst hxy; rw [bin_self]; exact Or.inr (Or.inr (Or.inl hxm))
      · by_cases hz0 : bin d x y = zero
        · exact Or.inl hz0
        · by_cases hz1 : bin d x y = one
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hxm, y, hym, hxy, (hav x hxm).1, (hav y hym).1, d, ⟨hz0, hz1⟩, rfl⟩)))
    rcases hh with rfl | rfl
    · exact binCase false
    · exact binCase true

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List Sig) (av : Finset Sig)
    (hwv : ∀ u ∈ w, valid u) (hav : ∀ u ∈ av, proper u ∧ valid u) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) :
    build gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hvout : valid (w.getD out zero) := by
      rcases read_wire w out with h | h
      · rw [h]; exact valid_zero
      · exact hwv _ h
    have hval : w.getD out zero = target := by
      apply Prod.ext
      · apply nat_eq_of_testBit hvout.1 valid_target.1
        intro i hi
        have hk := he ⟨59 + i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, show ¬(59 + i < 59) by omega, ite_false,
          Nat.add_sub_cancel_left] at hk
        exact hk
      · apply nat_eq_of_testBit hvout.2 valid_target.2
        intro i hi
        have hk := he ⟨i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, hi, ite_true] at hk
        exact hk
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : target ≠ zero) hz)
    · rcases hw target hm with hz | ho | hmem
      · exact False.elim ((by decide : target ≠ zero) hz)
      · exact False.elim ((by decide : target ≠ one) ho)
      · exact hmem
  | cons g gs ih =>
    obtain ⟨z, hvz, hz, hstep⟩ := gate_table w hwv g (hg g (by simp))
    have hwv' : ∀ u ∈ w ++ [z], valid u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hwv u h
      · rw [List.mem_singleton.mp h]; exact hvz
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k target := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = zero ∨ z = one ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw u old
      · rw [List.mem_singleton.mp fresh]; exact h
    rcases classify hav hw hz with h0 | h1 | hmem | ⟨a, ha, hpa, rfl⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, rfl⟩
    · exact Or.inl (fn av hwv' hav (appendOK (.inl h0)) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inl h1))) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inr hmem))) he')
    · refine Or.inr (Or.inl ⟨a, ha, hpa, fn (insert (neg a) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨proper_neg (hav a ha).2 hpa, valid_neg (hav a ha).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · refine Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, fn (insert (bin d a b) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨hpz, valid_bin (hav a ha).2 (hav b hb).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))

def graph (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)

def assignment (k : Fin 118) (i : Fin 6) : Bool := bit k (rawInputs.getD i.val zero)

theorem rawInputs_valid : ∀ u ∈ rawInputs, valid u := by
  have h : rawInputs.all (fun u => decide (u.1 < 2 ^ 59) && decide (u.2 < 2 ^ 59)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨bounded_of_lt h'.1, bounded_of_lt h'.2⟩

theorem rawInputs_proper : ∀ u ∈ rawInputs, proper u := by
  have h : rawInputs.all (fun u => (u != zero) && (u != one)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, bne_iff_ne] at h'
  exact h'

theorem full_inputs {s : Finset Sig} {k t : ℕ} (hs : s ⊆ rawInputs.toFinset)
    (hr : live k t s) : s = rawInputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 59) := [0, 1, 2, 3, 4, 5]
  have necessary : rawInputs.all (fun a => sites.any (fun i => rawInputs.all (fun b =>
      (b.1.testBit i.val == b.2.testBit i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : Sig) (hb : b ∈ rawInputs) (hd : differs (decide (0 < t)) i b) : b = a := by
    have hd' := differs_mono hd
    simp only [differs, ite_true] at hd'
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd'
  obtain ⟨b, hb, hd⟩ := live_separates i hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 118) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 118) : graph (assignment k) = bit k target := by
  let x := fun (i : Nat) => rawInputs.getD i zero
  have hp : (x 0).1 &&& (x 1).1 ||| (x 0).1 &&& (x 3).1 ||| (x 0).1 &&& (x 4).1 ||| (x 0).1 &&& (x 5).1 ||| (x 1).1 &&& (x 2).1 ||| (x 1).1 &&& (x 4).1 ||| (x 2).1 &&& (x 3).1 = top := by decide
  have hn : (x 0).2 &&& (x 1).2 ||| (x 0).2 &&& (x 3).2 ||| (x 0).2 &&& (x 4).2 ||| (x 0).2 &&& (x 5).2 ||| (x 1).2 &&& (x 2).2 ||| (x 1).2 &&& (x 4).2 ||| (x 2).2 &&& (x 3).2 = 0 := by decide
  unfold graph assignment bit target
  by_cases hk : k.val < 59
  · simp only [hk, ite_true]
    change _ = (0 : Nat).testBit k.val
    rw [← hn]
    simp only [Nat.testBit_or, Nat.testBit_and]
    rfl
  · simp only [hk, ite_false]
    change _ = top.testBit (k.val - 59)
    rw [← hp]
    simp only [Nat.testBit_or, Nat.testBit_and]
    rfl

theorem rows_eval (C : Circuit) (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 118) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k target := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents rawInputs.toFinset rawInputs := by
  intro u hu
  exact Or.inr (Or.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    build C.gates.length rawInputs.toFinset :=
  compile C.gates C.output hg rawInputs rawInputs.toFinset rawInputs_valid
    (fun u hu => ⟨rawInputs_proper u (List.mem_toFinset.mp hu), rawInputs_valid u (List.mem_toFinset.mp hu)⟩)
    initial_rep (rows_eval C he)

theorem extend_live {m n t : ℕ} (le : m ≤ n) (h : live m t rawInputs.toFinset) :
    live n t rawInputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t0 : search 7 0 rawInputs = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t1 : search 7 1 rawInputs = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t2 : search 7 2 rawInputs = false := by decide +kernel

theorem main_proof (t : ℕ) (h : HasCircuitSize 6 graph t) : 8 ≤ t := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hl : C.gates.length ≤ 7 := by change C.gates.length ≤ t at hsize; omega
  obtain ⟨kNot, s, hsub, hLive⟩ := compress (get_build C hg he)
  have hsEq := full_inputs hsub hLive
  subst hsEq
  have hLive7 := extend_live hl hLive
  have hcard := live_card hLive7
  have hrawCard : rawInputs.toFinset.card = 6 := by decide
  rw [hrawCard] at hcard
  have hnodup : rawInputs.Nodup := by decide
  have hsearched := search_complete 7 kNot rawInputs hnodup rawInputs_valid hLive7
  have hkLe : kNot ≤ 2 := by omega
  interval_cases kNot
  · exact Bool.noConfusion (check_t0.symm.trans hsearched)
  · exact Bool.noConfusion (check_t1.symm.trans hsearched)
  · exact Bool.noConfusion (check_t2.symm.trans hsearched)

theorem lower :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)) t → 8 ≤ t :=
  PEqualNP.Outside.L_meta_14958.Reused_L_meta_11601.Foundation.main_proof

end Foundation

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

def g0 : (Fin 7 → Bool) → Bool := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def g1 : (Fin 7 → Bool) → Bool := fun x => g0 (Function.update x 2 false)
theorem dep0 : ∃ x : Fin 7 → Bool, g0 (Function.update x 2 (!x 2)) ≠ g0 x :=
  ⟨fun i => decide (i = 5), by decide +kernel⟩
theorem keep0 : ∃ x y : Fin 7 → Bool, g0 (Function.update x 2 false) ≠ g0 (Function.update y 2 false) :=
  ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), by decide +kernel⟩
def identify (i : Fin 7) : Fin 6 := match i.val with
  | 0 => 2
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 1
  | 5 => 3
  | _ => 0
def small : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)
theorem image : (fun x : Fin 6 → Bool => g1 (x ∘ identify)) = small := by decide +kernel

theorem lower (t : ℕ) (h0 : HasCircuitSize 7 g0 t) : 9 ≤ t := by
  obtain ⟨s1, c1, h1⟩ := one_gate_at 6 g0 2 false t dep0 keep0 h0
  change HasCircuitSize 7 g1 s1 at h1
  have r := relabel_size identify g1 s1 h1
  rw [image] at r
  have hl := Foundation.lower s1 r
  omega

end Transfer
end Reused_L_meta_11601

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def edges : List ℕ :=
  [0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7]

private def edgeFunction (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

private def smallerInput (i : Fin 8) : Fin 7 :=
  Fin.ofNat 7 (([6, 6, 0, 2, 1, 3, 5, 4] : List ℕ).getD i.val 0)

private theorem dependsOnTwin :
    ∃ x : Fin 8 → Bool, edgeFunction (Function.update x 1 (!x 1)) ≠ edgeFunction x :=
  ⟨fun i => decide (i = 4), by decide +kernel⟩

private theorem restrictionNonconstant :
    ∃ x y : Fin 8 → Bool, edgeFunction (Function.update x 1 false) ≠
      edgeFunction (Function.update y 1 false) :=
  ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), by decide +kernel⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem restrictionRelabel :
    (fun x : Fin 7 → Bool => edgeFunction (Function.update (x ∘ smallerInput) 1 false)) =
      Reused_L_meta_11601.Transfer.g0 := by
  decide +kernel

private theorem lowerBound (s : ℕ) (h : HasCircuitSize 8 edgeFunction s) : 10 ≤ s := by
  obtain ⟨t, headroom, smaller⟩ :=
    Reused_L_meta_11601.Transfer.one_gate_at 7 edgeFunction 1 false s dependsOnTwin
      restrictionNonconstant h
  have relabeled := Reused_L_meta_11601.Transfer.relabel_size smallerInput
    (fun x => edgeFunction (Function.update x 1 false)) t smaller
  rw [restrictionRelabel] at relabeled
  have h9 := Reused_L_meta_11601.Transfer.lower t relabeled
  omega

private def witnessGates : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [9, 4]⟩,
   ⟨.and, [12, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 15]⟩]

private theorem witnessLegal :
    ∀ g ∈ witnessGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem witnessComputes :
    ∀ x : Fin 8 → Bool, Circuit.eval ⟨witnessGates, 17⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

end PEqualNP.Outside.L_meta_14958

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14958

theorem PEqualNP.Outside.L_meta_14958 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _ computes
  have sized : HasCircuitSize 8 edgeFunction gates.length :=
    ⟨⟨gates, o⟩, legal, le_rfl, computes⟩
  exact ⟨witnessGates, 17, witnessLegal, lowerBound gates.length sized, witnessComputes⟩
