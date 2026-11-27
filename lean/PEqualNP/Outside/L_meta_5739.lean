import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5739

def F13 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem mem_F13 : ∀ p : Fin 13, p ∈ F13 := by decide

theorem nodup_F13 : F13.Nodup := by decide

def Rb (p l : Fin 13) : Bool := (523 : ℕ).testBit ((p.val + 13 - l.val) % 13)

theorem Rb_iff : ∀ p l : Fin 13, Rb p l = true ↔ (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4) := by decide +kernel

def missB (s : ℕ) (l : Fin 13) : Bool := F13.all fun q => !(s.testBit q.val) || !(Rb q l)

def c1 (s : ℕ) : Bool := F13.all fun p => s.testBit p.val || F13.any fun l => missB s l && Rb p l

def xa (s : ℕ) : Bool := F13.any fun l => F13.all fun q => !(s.testBit q.val) || Rb q l

def xb (s : ℕ) : Bool := F13.any fun p => F13.all fun l => !(missB s l) || Rb p l

def cardS (s : ℕ) : Bool := (F13.filter fun p => s.testBit p.val).length == 3

def cardM (s : ℕ) : Bool := (F13.filter fun l => missB s l).length == 3

def chk (s : ℕ) : Bool := cardS s || xa s || !(c1 s) || xb s || cardM s

set_option maxRecDepth 1000000 in
theorem chk_all : (List.range 8192).all chk = true := by decide +kernel

theorem cardF (g : Fin 13 → Bool) (T : Finset (Fin 13)) (hg : ∀ p, g p = true ↔ p ∈ T) :
    (F13.filter g).length = T.card := by
  rw [← List.toFinset_card_of_nodup (nodup_F13.filter g)]
  congr 1
  ext p
  rw [List.mem_toFinset, List.mem_filter]
  constructor
  · intro h
    exact (hg p).1 h.2
  · intro h
    exact ⟨mem_F13 p, (hg p).2 h⟩

theorem miss_iff (S : Finset (Fin 13)) (s : ℕ) (hs : ∀ p : Fin 13, s.testBit p.val = decide (p ∈ S))
    (l : Fin 13) : missB s l = true ↔ ∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4) := by
  unfold missB
  rw [List.all_eq_true]
  constructor
  · intro h q hq hr
    have h2 := h q (mem_F13 q)
    rw [hs q, decide_eq_true hq, (Rb_iff q l).2 hr] at h2
    exact absurd h2 (by decide)
  · intro h q _
    by_cases hq : q ∈ S
    · have hr : Rb q l = false := by
        rw [Bool.eq_false_iff]
        exact fun e => h q hq ((Rb_iff q l).1 e)
      rw [hr]
      simp
    · rw [hs q, decide_eq_false hq]
      rfl

theorem c1_of (S : Finset (Fin 13)) (s : ℕ) (hs : ∀ p : Fin 13, s.testBit p.val = decide (p ∈ S))
    (h : ∀ p, p ∉ S → ∃ l : Fin 13, (∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4)) ∧ (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4)) : c1 s = true := by
  unfold c1
  rw [List.all_eq_true]
  intro p _
  by_cases hp : p ∈ S
  · rw [hs p, decide_eq_true hp]
    rfl
  · obtain ⟨l, hl1, hl2⟩ := h p hp
    have e : (F13.any fun l => missB s l && Rb p l) = true := by
      rw [List.any_eq_true]
      refine ⟨l, mem_F13 l, ?_⟩
      rw [(miss_iff S s hs l).2 hl1, (Rb_iff p l).2 hl2]
      rfl
    rw [e]
    simp

theorem xa_to (S : Finset (Fin 13)) (s : ℕ) (hs : ∀ p : Fin 13, s.testBit p.val = decide (p ∈ S))
    (h : xa s = true) : ∃ l : Fin 13, ∀ q ∈ S, (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4) := by
  unfold xa at h
  rw [List.any_eq_true] at h
  obtain ⟨l, _, h⟩ := h
  rw [List.all_eq_true] at h
  refine ⟨l, fun q hq => ?_⟩
  have h2 := h q (mem_F13 q)
  rw [hs q, decide_eq_true hq] at h2
  exact (Rb_iff q l).1 (by simpa using h2)

theorem xb_to (S : Finset (Fin 13)) (s : ℕ) (hs : ∀ p : Fin 13, s.testBit p.val = decide (p ∈ S))
    (h : xb s = true) : ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4)) → (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4) := by
  unfold xb at h
  rw [List.any_eq_true] at h
  obtain ⟨p, _, h⟩ := h
  rw [List.all_eq_true] at h
  refine ⟨p, fun l hl => ?_⟩
  have h2 := h l (mem_F13 l)
  rw [(miss_iff S s hs l).2 hl] at h2
  exact (Rb_iff p l).1 (by simpa using h2)

theorem main (S : Finset (Fin 13))
    (h1 : ∀ p, p ∉ S → ∃ l : Fin 13, (∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4)) ∧ (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4))
    (h2 : ¬((∃ l : Fin 13, ∀ q ∈ S, (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4)) ∨
      ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4)) → (∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + x4))) :
    S.card = 3 ∨ ∃ T : Finset (Fin 13), T.card = 3 ∧ ∀ l : Fin 13, l ∈ T ↔ ∀ q ∈ S, ¬(∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + x4) := by
  have hs : ∀ p : Fin 13, (Nat.ofBits (fun p : Fin 13 => decide (p ∈ S))).testBit p.val = decide (p ∈ S) :=
    fun p => Nat.testBit_ofBits_lt (fun p : Fin 13 => decide (p ∈ S)) p.val p.isLt
  have hlt : Nat.ofBits (fun p : Fin 13 => decide (p ∈ S)) < 8192 :=
    Nat.ofBits_lt_two_pow (fun p : Fin 13 => decide (p ∈ S))
  generalize Nat.ofBits (fun p : Fin 13 => decide (p ∈ S)) = s at hs hlt
  have hc := List.all_eq_true.1 chk_all s (List.mem_range.2 hlt)
  unfold chk at hc
  simp only [Bool.or_eq_true] at hc
  rcases hc with (((h | h) | h) | h) | h
  · left
    unfold cardS at h
    rw [beq_iff_eq] at h
    rw [← cardF (fun p => s.testBit p.val) S (fun p => by rw [hs p, decide_eq_true_eq])]
    exact h
  · exact absurd (Or.inl (xa_to S s hs h)) h2
  · rw [c1_of S s hs h1] at h
    exact absurd h (by decide)
  · exact absurd (Or.inr (xb_to S s hs h)) h2
  · right
    refine ⟨Finset.univ.filter (fun l => missB s l = true), ?_, ?_⟩
    · unfold cardM at h
      rw [beq_iff_eq] at h
      rw [← cardF (fun l => missB s l) _ (fun p => by rw [Finset.mem_filter]; simp)]
      exact h
    · intro l
      rw [Finset.mem_filter, ← miss_iff S s hs l]
      simp

end PEqualNP.Outside.L_meta_5739

theorem PEqualNP.Outside.L_meta_5739 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7; have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => (∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x5 x7 → x2 x6 x7; ∀ (x6 : Finset (Fin (13 : ℕ))), x4 x6 → ¬x5 x6 → x6.card = (3 : ℕ) ∨ ∃ (x9 : Finset (Fin (13 : ℕ))), x9.card = (3 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), x10 ∈ x9 ↔ x3 x6 x10 := by
  dsimp only
  intro x6 h1 h2
  exact PEqualNP.Outside.L_meta_5739.main x6 h1 h2
