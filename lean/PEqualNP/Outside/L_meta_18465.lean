import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18465

abbrev Input := Fin 9 → Bool

def probe (m : ℕ) : Input := fun i => m.testBit (i.val + 1)
def edges : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (0, 5), (1, 6), (4, 6), (2, 7), (4, 7), (5, 7), (3, 8), (5, 8), (6, 8)]
def graph (x : Input) : Bool := edges.any fun e => x e.1 && x e.2
def broad (x : Input) : Bool := x 0 || x 3 || x 4 || graph x
def triA (x : Input) : Bool := x 2 && x 5 && x 6
def triB (x : Input) : Bool := x 1 && x 7 && x 8
def yes : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def no : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def quiet : List ℕ := [50, 104, 116, 138, 208, 276, 402, 548, 554, 770]
def yesEven := yes.filter fun m => !m.testBit 0
def noOdd := no.filter fun m => m.testBit 0
def lower (items : List ℕ) (x : Input) := items.any fun m => decide (probe m ≤ x)
def upper (items : List ℕ) (x : Input) := items.any fun m => decide (x ≤ probe m)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 40000000 in
theorem finiteFacts (x : Input) :
    (broad x = true → lower yes x = true) ∧
    (broad x = false → upper noOdd x = true) ∧
    (graph x = false → upper no x = true) ∧
    (graph x = true → lower yesEven x = true) ∧
    (graph x = false → x = probe 200 ∨ x = probe 772 ∨
      upper quiet x = true ∧ triA x = false ∧ triB x = false) := by
  exact (by decide +kernel : ∀ z : Input,
    (broad z = true → lower yes z = true) ∧
    (broad z = false → upper noOdd z = true) ∧
    (graph z = false → upper no z = true) ∧
    (graph z = true → lower yesEven z = true) ∧
    (graph z = false → z = probe 200 ∨ z = probe 772 ∨
      upper quiet z = true ∧ triA z = false ∧ triB z = false)) x

theorem lower_mem {items : List ℕ} {x : Input} (h : lower items x = true) :
    ∃ m ∈ items, probe m ≤ x := by
  obtain ⟨m, hm, ok⟩ := List.any_eq_true.mp h
  exact ⟨m, hm, of_decide_eq_true ok⟩

theorem upper_mem {items : List ℕ} {x : Input} (h : upper items x = true) :
    ∃ m ∈ items, x ≤ probe m := by
  obtain ⟨m, hm, ok⟩ := List.any_eq_true.mp h
  exact ⟨m, hm, of_decide_eq_true ok⟩

theorem trueUp {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) h

theorem falseDown {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  cases a <;> cases b <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) h

def mix (f g h : Input → Bool) (m : ℕ) : Bool :=
  bif m.testBit 0 || h (probe m) then g (probe m) else f (probe m)

end PEqualNP.Outside.L_meta_18465

open PEqualNP.Outside.L_meta_18465 in
theorem PEqualNP.Outside.L_meta_18465 : ∀ (x1 x2 x3 : (Fin (9 : ℕ) → Bool) → Bool),   Monotone x1 →     Monotone x2 →       Monotone x3 →         (∀ (x7 : Fin (9 : ℕ) → Bool), x1 x7 ≤ x2 x7) →           have x8 : ℕ → Fin (9 : ℕ) → Bool := fun (x8 : ℕ) (x9 : Fin (9 : ℕ)) => x8.testBit (↑x9 + (1 : ℕ));           have x9 : (Fin (9 : ℕ) → Bool) → Bool := fun (x9 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9 x10.1 && x9 x10.2;           have x10 : ℕ → Bool := fun (x10 : ℕ) => bif x10.testBit (0 : ℕ) || x3 (x8 x10) then x2 (x8 x10) else x1 (x8 x10);           (∀ x11 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x3 (x8 x11) = Bool.false) → (∀ x12 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x10 x12 = Bool.true) → (∀ x13 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x10 x13 = Bool.false) → ∀ (x14 : Fin (9 : ℕ) → Bool), x2 x14 = (x14 (0 : Fin (9 : ℕ)) || x14 (3 : Fin (9 : ℕ)) || x14 (4 : Fin (9 : ℕ)) || x9 x14) ∧ (x1 x14 = Bool.true → x9 x14 = Bool.true) ∧ (x1 x14 || x3 x14) = (x9 x14 || x3 (x8 (200 : ℕ)) && (x14 (2 : Fin (9 : ℕ)) && x14 (5 : Fin (9 : ℕ)) && x14 (6 : Fin (9 : ℕ))) || x3 (x8 (772 : ℕ)) && (x14 (1 : Fin (9 : ℕ)) && x14 (7 : Fin (9 : ℕ)) && x14 (8 : Fin (9 : ℕ)))) := by
  intro f g h mf mg mh bounds
  change (∀ m ∈ quiet, h (probe m) = false) →
    (∀ m ∈ yes, mix f g h m = true) →
    (∀ m ∈ no, mix f g h m = false) → ∀ x : Input, _
  intro hquiet hy hn x
  change g x = broad x ∧ (f x = true → graph x = true) ∧
    (f x || h x) = (graph x || h (probe 200) && triA x || h (probe 772) && triB x)
  obtain ⟨lt, uf, fn, ot, hz⟩ := finiteFacts x
  have gPos (m : ℕ) (mem : m ∈ yes) : g (probe m) = true := by
    have yesM := hy m mem
    cases bit : m.testBit 0 || h (probe m) <;> rw [mix, bit] at yesM
    · exact trueUp (bounds _) yesM
    · exact yesM
  have fNeg (m : ℕ) (mem : m ∈ no) : f (probe m) = false := by
    have noM := hn m mem
    cases bit : m.testBit 0 || h (probe m) <;> rw [mix, bit] at noM
    · exact noM
    · exact falseDown (bounds _) noM
  have gExact : g x = broad x := by
    cases e : broad x
    · obtain ⟨m, mem, le⟩ := upper_mem (uf e)
      obtain ⟨inNo, odd⟩ := List.mem_filter.mp mem
      have ng : g (probe m) = false := by simpa [mix, odd] using hn m inNo
      exact falseDown (mg le) ng
    · obtain ⟨m, mem, le⟩ := lower_mem (lt e)
      exact trueUp (mg le) (gPos m mem)
  have fZero (missing : graph x = false) : f x = false := by
    obtain ⟨m, mem, le⟩ := upper_mem (fn missing)
    exact falseDown (mf le) (fNeg m mem)
  refine ⟨gExact, ?_, ?_⟩
  · intro hit
    cases e : graph x
    · cases (fZero e).symm.trans hit
    · rfl
  · cases e : graph x
    · have f0 := fZero e
      rcases hz e with ea | eb | ⟨limits, ta, tb⟩
      · subst x
        have t1 : triA (probe 200) = true := by decide
        have t2 : triB (probe 200) = false := by decide
        simp [f0, t1, t2]
      · subst x
        have t1 : triA (probe 772) = false := by decide
        have t2 : triB (probe 772) = true := by decide
        simp [f0, t1, t2]
      · obtain ⟨m, mem, le⟩ := upper_mem limits
        have h0 := falseDown (mh le) (hquiet m mem)
        simp [f0, h0, ta, tb]
    · obtain ⟨m, mem, le⟩ := lower_mem (ot e)
      obtain ⟨inYes, even⟩ := List.mem_filter.mp mem
      have parity : m.testBit 0 = false := by simpa using even
      have yesM := hy m inYes
      cases eh : h (probe m)
      · have ef : f (probe m) = true := by simpa [mix, parity, eh] using yesM
        simp [trueUp (mf le) ef]
      · simp [trueUp (mh le) eh]
