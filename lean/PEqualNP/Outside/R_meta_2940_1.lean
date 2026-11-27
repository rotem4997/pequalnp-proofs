import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2940_1
    (pos : ∀ (D : BinaryCircuit), D.size = 13 → D.output < 24 → (∀ (j : ℕ) (g : BinaryGate), D.gates[j]? = some g → g.left < 11+j ∧ g.right < 11+j ∧ ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) → ∃ x4 : Fin 9 → Bool, (D.eval (List.ofFn x4 ++ [x4 0 || x4 4, false]) != false) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))))
    (neg : ∀ (D : BinaryCircuit), D.size = 13 → D.output < 24 → (∀ (j : ℕ) (g : BinaryGate), D.gates[j]? = some g → g.left < 11+j ∧ g.right < 11+j ∧ ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) → ∃ x4 : Fin 9 → Bool, (D.eval (List.ofFn x4 ++ [x4 0 || x4 4, false]) != true) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))))
    : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C polarity hops heval
  by_contra hsize
  have hsmall : C.size ≤ 13 := by omega
  let step (w : List Bool) (g : BinaryGate) : List Bool :=
    w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  let run (gs : List BinaryGate) (w : List Bool) := gs.foldl step w
  have step_len (w : List Bool) (g : BinaryGate) :
      (step w g).length = w.length + 1 := by simp [step]
  have step_keep (w : List Bool) (g : BinaryGate) (i : ℕ) (hi : i < w.length) :
      (step w g).getD i false = w.getD i false := by
    exact List.getD_append _ _ _ _ hi
  have run_len : ∀ (gs : List BinaryGate) (w : List Bool),
      (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
      intro w
      change (run gs (step w g)).length = w.length + (g :: gs).length
      rw [ih, step_len]
      simp only [List.length_cons]
      omega
  have run_keep : ∀ (gs : List BinaryGate) (w : List Bool) (i : ℕ),
      i < w.length → (run gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      change (run gs (step w g)).getD i false = w.getD i false
      rw [ih _ _ (by rw [step_len]; omega), step_keep w g i hi]
  let pin (j i : ℕ) := if i < 11 + j then i else 10
  let fixed (j : ℕ) (g : BinaryGate) : BinaryGate :=
    { op := g.op, left := pin j g.left, right := pin j g.right }
  let norm (j : ℕ) (gs : List BinaryGate) : List BinaryGate :=
    (gs.zipIdx j).map (fun p => fixed p.2 p.1)
  have norm_nil (j : ℕ) : norm j [] = [] := by simp [norm]
  have norm_cons (j : ℕ) (g : BinaryGate) (gs : List BinaryGate) :
      norm j (g :: gs) = fixed j g :: norm (j+1) gs := by
    simp only [norm, List.zipIdx_cons, List.map_cons]
  have pin_lt (j i : ℕ) : pin j i < 11 + j := by
    dsimp [pin]
    split <;> omega
  have pin_eq (j i : ℕ) (w : List Bool) (hlen : w.length = 11+j)
      (hz : w.getD 10 false = false) :
      w.getD (pin j i) false = w.getD i false := by
    dsimp [pin]
    split
    · rfl
    · rw [hz, List.getD_eq_default _ _ (by omega)]
  have norm_len : ∀ (gs : List BinaryGate) (j : ℕ), (norm j gs).length = gs.length := by
    intro gs
    induction gs with
    | nil => intro j; rw [norm_nil]
    | cons g gs ih => intro j; rw [norm_cons]; simp [ih]
  have norm_run : ∀ (gs : List BinaryGate) (j : ℕ) (w : List Bool),
      w.length = 11+j → w.getD 10 false = false →
      run (norm j gs) w = run gs w := by
    intro gs
    induction gs with
    | nil => intro j w hlen hz; rw [norm_nil]
    | cons g gs ih =>
      intro j w hlen hz
      have he : step w (fixed j g) = step w g := by
        simp only [step, fixed]
        rw [pin_eq j g.left w hlen hz, pin_eq j g.right w hlen hz]
      rw [norm_cons]
      change run (norm (j+1) gs) (step w (fixed j g)) = run gs (step w g)
      rw [he]
      apply ih
      · rw [step_len, hlen]; omega
      · rw [step_keep w g 10 (by omega), hz]
  have norm_index : ∀ (gs : List BinaryGate) (j i : ℕ) (g : BinaryGate),
      (norm j gs)[i]? = some g →
      g.left < 11+j+i ∧ g.right < 11+j+i ∧ ∃ h ∈ gs, g.op = h.op := by
    intro gs
    induction gs with
    | nil => intro j i g hg; rw [norm_nil] at hg; simp at hg
    | cons h gs ih =>
      intro j i g hg
      rw [norm_cons] at hg
      cases i with
      | zero =>
        change some (fixed j h) = some g at hg
        have hg' := Option.some.inj hg
        subst g
        exact ⟨by simpa [fixed] using pin_lt j h.left,
          by simpa [fixed] using pin_lt j h.right, h, by simp, rfl⟩
      | succ i =>
        change (norm (j+1) gs)[i]? = some g at hg
        obtain ⟨hl, hr, k, hk, hop⟩ := ih (j+1) i g hg
        exact ⟨by omega, by omega, k, by simp [hk], hop⟩
  let dummy : BinaryGate :=
    { op := fun a b => (a == false) && (b == false), left := 10, right := 10 }
  let core := norm 0 C.gates
  have hcore : core.length = C.size := norm_len C.gates 0
  let D : BinaryCircuit :=
    { gates := core ++ List.replicate (13-C.size) dummy,
      output := if C.output < 11+C.size then C.output else 10 }
  have hdsize : D.size = 13 := by
    change (core ++ List.replicate (13-C.size) dummy).length = 13
    simp only [List.length_append, List.length_replicate, hcore]
    omega
  have hdout : D.output < 24 := by
    change (if C.output < 11+C.size then C.output else 10) < 24
    split <;> omega
  have hdgate : ∀ (j : ℕ) (g : BinaryGate), D.gates[j]? = some g →
      g.left < 11+j ∧ g.right < 11+j ∧
        ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b) := by
    intro j g hg
    change (core ++ List.replicate (13-C.size) dummy)[j]? = some g at hg
    by_cases hj : j < core.length
    · rw [List.getElem?_append_left hj] at hg
      obtain ⟨hl, hr, k, hk, hop⟩ := norm_index C.gates 0 j g hg
      obtain ⟨a,b,hab⟩ := hops k hk
      exact ⟨by omega, by omega, a,b,hop.trans hab⟩
    · rw [List.getElem?_append_right (by omega)] at hg
      have hmem : g ∈ List.replicate (13-C.size) dummy := List.mem_of_getElem? hg
      have he : g = dummy := (List.mem_replicate.mp hmem).2
      subst g
      exact ⟨by simp [dummy]; omega, by simp [dummy]; omega, false, false, rfl⟩
  have hsame (w : List Bool) (hlen : w.length = 11)
      (hz : w.getD 10 false = false) : D.eval w = C.eval w := by
    have hnorm : run core w = run C.gates w := norm_run C.gates 0 w (by omega) hz
    have hlen' : (run C.gates w).length = 11+C.size := by
      rw [run_len, hlen]; rfl
    change (run (core ++ List.replicate (13-C.size) dummy) w).getD D.output false =
      (run C.gates w).getD C.output false
    have happ : run (core ++ List.replicate (13-C.size) dummy) w =
        run (List.replicate (13-C.size) dummy) (run core w) := by
      simp only [run, List.foldl_append]
    rw [happ]
    rw [hnorm]
    by_cases h : C.output < 11+C.size
    · have ho : D.output = C.output := by simp [D,h]
      rw [ho, run_keep _ _ _ (by omega)]
    · have ho : D.output = 10 := by simp [D,h]
      rw [ho, run_keep _ _ _ (by omega), run_keep _ _ _ (by omega), hz,
        List.getD_eq_default _ _ (by omega)]
  have agree (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 4, false]) =
      C.eval (List.ofFn x ++ [x 0 || x 4, false]) := by
    apply hsame
    · simp
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  cases polarity
  · obtain ⟨x,hx⟩ := pos D hdsize hdout hdgate
    apply hx
    rw [agree x]
    exact heval x
  · obtain ⟨x,hx⟩ := neg D hdsize hdout hdgate
    apply hx
    rw [agree x]
    exact heval x
