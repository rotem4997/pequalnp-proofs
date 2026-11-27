import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4127_aux

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def stL2 (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def stL (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  stL2 g.op (g.inputs.map fun i => w.getD i (false, false))

def ini (isL : ℕ → Bool) (xs : List Bool) : List (Bool × Bool) :=
  (xs.zipIdx).map fun (b, i) => if isL i then (false, b) else (b, false)

def lpv (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) : Bool × Bool :=
  (fd stL gs (ini isL xs)).getD w (false, false)

theorem lp_eq (C : Circuit) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ) :
    (linearParts C isL xs).getD w (false, false) = lpv C.gates isL xs w := rfl

theorem ini_len (isL : ℕ → Bool) (xs : List Bool) : (ini isL xs).length = xs.length := by
  simp [ini]

theorem lp_input (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length) :
    lpv gs isL xs w = if isL w then (false, xs.getD w false) else (xs.getD w false, false) := by
  rw [lpv, fd_keep stL (false, false) gs _ w (by rw [ini_len]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

theorem lp_big (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (w : ℕ)
    (hw : xs.length + gs.length ≤ w) : lpv gs isL xs w = (false, false) := by
  rw [lpv, List.getD_eq_default _ _ (by rw [fd_len, ini_len]; exact hw)]

theorem lp_gate (gs : List Gate) (isL : ℕ → Bool) (xs : List Bool) (k : ℕ)
    (hk : k < gs.length) (hin : ∀ i ∈ gs[k].inputs, i < xs.length + k) :
    lpv gs isL xs (xs.length + k) = stL2 gs[k].op (gs[k].inputs.map (lpv gs isL xs)) := by
  have h := fd_gate stL (false, false) gs (ini isL xs) k hk
  rw [ini_len] at h
  rw [lpv, h]
  show stL2 gs[k].op _ = _
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [lpv]
  exact (fd_take stL (false, false) gs (ini isL xs) k i (by rw [ini_len]; exact hin i hi)
    (Nat.le_of_lt hk)).symm

theorem map_fst_getD (w : List (Bool × Bool)) (i : Nat) :
    (w.map Prod.fst).getD i false = (w.getD i (false, false)).1 := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem stL_fst (w : List (Bool × Bool)) (g : Gate)
    (ho : g.op = .and ∨ g.op = .or) (a b : Nat) (hi : g.inputs = [a,b]) :
    (stL w g).1 = stB (w.map Prod.fst) g := by
  simp only [stB, map_fst_getD]
  rcases ho with ho | ho <;>
    simp [stL, stL2, hi, ho, GateOp.eval]

theorem fd_fst (gs : List Gate)
    (hl : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b])
    (w : List (Bool × Bool)) :
    (fd stL gs w).map Prod.fst = fd stB gs (w.map Prod.fst) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop,a,b,hins⟩ := hl g (by simp)
    have htail : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] := by
      intro q hq
      exact hl q (by simp [hq])
    change (fd stL gs (w ++ [stL w g])).map Prod.fst =
      fd stB gs ((w.map Prod.fst) ++ [stB (w.map Prod.fst) g])
    rw [ih htail, List.map_append, List.map_singleton, stL_fst w g hop a b hins]

def pairInput : List Bool :=
  List.ofFn fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7)

def mark (s : Bool) : Nat → Bool :=
  fun i => decide (i = if s = true then 7 else 0)

def baseInput (s : Bool) : List Bool :=
  List.ofFn fun i : Fin 14 => decide
    (i = if s = true then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))

theorem pairInput_length : pairInput.length = 14 := by
  simp [pairInput]

theorem initial_base (s : Bool) :
    (ini (mark s) pairInput).map Prod.fst = baseInput s := by
  cases s <;> decide

theorem initial_marks (s : Bool) : ∀ i : Fin 7,
    ((ini (mark s) pairInput).getD i.val (false,false)).2 =
      (if s = true then false else decide (i = 0)) ∧
    ((ini (mark s) pairInput).getD (7 + i.val) (false,false)).2 =
      (if s = true then decide (i = 0) else false) := by
  cases s <;> decide

end PEqualNP.Outside.L_meta_4127_aux

theorem PEqualNP.Outside.L_meta_4127 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) →     ∀ (x3 : Bool),       ((PEqualNP.ReadK.linearParts x1 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x1.output (Bool.false, Bool.false)).2 = Bool.false →         ∃ (x5 : ℕ → Bool),           (∀ (x6 : Fin (7 : ℕ)), (x5 ↑x6 = if x3 = Bool.true then Bool.false else Decidable.decide (x6 = (0 : Fin (7 : ℕ)))) ∧ x5 ((7 : ℕ) + ↑x6) = if x3 = Bool.true then Decidable.decide (x6 = (0 : Fin (7 : ℕ))) else Bool.false) ∧             (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                 x1.gates[x6]? = Option.some x7 →                   x7.inputs = [x8, x9] →                     have x12 : List Bool := x1.wires (List.ofFn fun (x12 : Fin (14 : ℕ)) => Decidable.decide (x12 = if x3 = Bool.true then Fin.castAdd (7 : ℕ) (0 : Fin (7 : ℕ)) else Fin.natAdd (7 : ℕ) (0 : Fin (7 : ℕ))));                     (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((14 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((14 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧               x5 x1.output = Bool.false := by
  intro C hlegal s hzero
  let d (w : Nat) :=
    (PEqualNP.Outside.L_meta_4127_aux.lpv C.gates
      (PEqualNP.Outside.L_meta_4127_aux.mark s)
      PEqualNP.Outside.L_meta_4127_aux.pairInput w).2
  have hl : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] := by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨ho,a,b,hab,_,_,_⟩ := hlegal j g hj
    exact ⟨ho,a,b,hab⟩
  have hfst (i : Nat) :
      (PEqualNP.Outside.L_meta_4127_aux.lpv C.gates
        (PEqualNP.Outside.L_meta_4127_aux.mark s)
        PEqualNP.Outside.L_meta_4127_aux.pairInput i).1 =
      (C.wires (PEqualNP.Outside.L_meta_4127_aux.baseInput s)).getD i false := by
    have he := PEqualNP.Outside.L_meta_4127_aux.fd_fst C.gates hl
      (PEqualNP.Outside.L_meta_4127_aux.ini
        (PEqualNP.Outside.L_meta_4127_aux.mark s)
        PEqualNP.Outside.L_meta_4127_aux.pairInput)
    rw [PEqualNP.Outside.L_meta_4127_aux.initial_base] at he
    have hh := congrArg (fun w : List Bool => w.getD i false) he
    rw [PEqualNP.Outside.L_meta_4127_aux.map_fst_getD] at hh
    exact hh
  refine ⟨d, ?_, ?_, hzero⟩
  · intro i
    have hin (j : Nat) (hj : j < 14) : d j =
        ((PEqualNP.Outside.L_meta_4127_aux.ini
          (PEqualNP.Outside.L_meta_4127_aux.mark s)
          PEqualNP.Outside.L_meta_4127_aux.pairInput).getD j (false,false)).2 := by
      change ((PEqualNP.Outside.L_meta_4127_aux.fd
        PEqualNP.Outside.L_meta_4127_aux.stL C.gates
        (PEqualNP.Outside.L_meta_4127_aux.ini
          (PEqualNP.Outside.L_meta_4127_aux.mark s)
          PEqualNP.Outside.L_meta_4127_aux.pairInput)).getD j (false,false)).2 = _
      rw [PEqualNP.Outside.L_meta_4127_aux.fd_keep
        PEqualNP.Outside.L_meta_4127_aux.stL (false,false) C.gates _ j
        (by simpa [PEqualNP.Outside.L_meta_4127_aux.ini_len,
          PEqualNP.Outside.L_meta_4127_aux.pairInput_length] using hj)]
    rw [hin i.val (by omega), hin (7+i.val) (by omega)]
    exact PEqualNP.Outside.L_meta_4127_aux.initial_marks s i
  · intro j g a b hj hab
    obtain ⟨ho,c,e,hce,hne,hc,he⟩ := hlegal j g hj
    rw [hab] at hce
    have heq : a = c ∧ b = e := by simpa using hce
    rcases heq with ⟨rfl,rfl⟩
    have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.1 hj).1
    have hgj : C.gates[j] = g := (List.getElem?_eq_some_iff.1 hj).2
    have hp := PEqualNP.Outside.L_meta_4127_aux.lp_gate C.gates
      (PEqualNP.Outside.L_meta_4127_aux.mark s)
      PEqualNP.Outside.L_meta_4127_aux.pairInput j hjlt
      (by
        rw [hgj,hab,PEqualNP.Outside.L_meta_4127_aux.pairInput_length]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hc
        · exact he)
    rw [PEqualNP.Outside.L_meta_4127_aux.pairInput_length,hgj,hab,
      List.map_cons,List.map_cons,List.map_nil] at hp
    have hs := congrArg Prod.snd hp
    constructor
    · intro hop
      rw [hop] at hs
      simpa [PEqualNP.Outside.L_meta_4127_aux.stL2, d, hfst,
        PEqualNP.Outside.L_meta_4127_aux.baseInput] using hs
    · intro hop
      rw [hop] at hs
      simpa [PEqualNP.Outside.L_meta_4127_aux.stL2, d] using hs
