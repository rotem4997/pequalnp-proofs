import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

private lemma fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega)]
    exact step_lt w g i hi

private lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  rw [W, fold_len]
  simp

private lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

private def Comp {n : ℕ} (gs : List Gate) (t : ℕ) (φ : (Fin n → Bool) → Bool) : Prop :=
  t < n + gs.length ∧ ∀ x : Fin n → Bool, (W gs x).getD t false = φ x

private lemma comp_input {n : ℕ} (gs : List Gate) (u : Fin n) :
    Comp gs u.val (fun x => x u) := by
  refine ⟨by have := u.isLt; omega, fun x => ?_⟩
  rw [W, fold_lt gs _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma comp_snoc {n : ℕ} {gs : List Gate} {t : ℕ} {φ : (Fin n → Bool) → Bool}
    (h : Comp gs t φ) (g : Gate) (gs' : List Gate) (hgs : gs' = gs ++ [g]) : Comp gs' t φ := by
  subst hgs
  refine ⟨by rw [List.length_append, List.length_singleton]; have := h.1; omega, fun x => ?_⟩
  rw [W_snoc, step_lt _ _ _ (by rw [W_len]; exact h.1)]
  exact h.2 x

private lemma comp_gate {n : ℕ} {gs : List Gate} (g : Gate) (gs' : List Gate)
    (hgs : gs' = gs ++ [g]) (ψ : (Fin n → Bool) → Bool)
    (hval : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => (W gs x).getD i false) = ψ x) :
    Comp gs' (n + gs.length) ψ := by
  subst hgs
  refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
  rw [W_snoc, step_last _ _ _ (by rw [W_len])]
  exact hval x

private lemma comp_and {n : ℕ} {gs : List Gate} {a b : ℕ} {φ ψ : (Fin n → Bool) → Bool}
    (ha : Comp gs a φ) (hb : Comp gs b ψ) (gs' : List Gate)
    (hgs : gs' = gs ++ [⟨GateOp.and, [a, b]⟩]) :
    Comp gs' (n + gs.length) (fun x => φ x && ψ x) :=
  comp_gate _ gs' hgs _ (fun x => by
    show GateOp.and.eval [(W gs x).getD a false, (W gs x).getD b false] = _
    rw [ha.2 x, hb.2 x]
    simp [GateOp.eval])

private lemma comp_or {n : ℕ} {gs : List Gate} {a b : ℕ} {φ ψ : (Fin n → Bool) → Bool}
    (ha : Comp gs a φ) (hb : Comp gs b ψ) (gs' : List Gate)
    (hgs : gs' = gs ++ [⟨GateOp.or, [a, b]⟩]) :
    Comp gs' (n + gs.length) (fun x => φ x || ψ x) :=
  comp_gate _ gs' hgs _ (fun x => by
    show GateOp.or.eval [(W gs x).getD a false, (W gs x).getD b false] = _
    rw [ha.2 x, hb.2 x]
    simp [GateOp.eval])

private lemma comp_not {n : ℕ} {gs : List Gate} {a : ℕ} {φ : (Fin n → Bool) → Bool}
    (ha : Comp gs a φ) (gs' : List Gate) (hgs : gs' = gs ++ [⟨GateOp.not, [a]⟩]) :
    Comp gs' (n + gs.length) (fun x => !(φ x)) :=
  comp_gate _ gs' hgs _ (fun x => by
    show GateOp.not.eval [(W gs x).getD a false] = _
    rw [ha.2 x]
    simp [GateOp.eval])

private lemma comp_copy {n : ℕ} {gs : List Gate} {o : ℕ} {φ : (Fin n → Bool) → Bool}
    (h : ∀ x : Fin n → Bool, (W gs x).getD o false = φ x) (gs' : List Gate)
    (hgs : gs' = gs ++ [⟨GateOp.or, [o, o]⟩]) : Comp gs' (n + gs.length) φ :=
  comp_gate _ gs' hgs _ (fun x => by
    show GateOp.or.eval [(W gs x).getD o false, (W gs x).getD o false] = _
    rw [h x]
    simp [GateOp.eval])

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma ok_and (a b : ℕ) : Ok ⟨GateOp.and, [a, b]⟩ := ⟨Or.inl rfl, by simp⟩

private lemma ok_or (a b : ℕ) : Ok ⟨GateOp.or, [a, b]⟩ := ⟨Or.inr (Or.inl rfl), by simp⟩

private lemma ok_not (a : ℕ) : Ok ⟨GateOp.not, [a]⟩ := ⟨Or.inr (Or.inr rfl), by simp⟩

private lemma fan_snoc {gs : List Gate} (h : ∀ g ∈ gs, Ok g) (g' : Gate) (hg' : Ok g')
    (gs' : List Gate) (hgs : gs' = gs ++ [g']) : ∀ g ∈ gs', Ok g := by
  subst hgs
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · rw [List.mem_singleton] at hg
    rw [hg]
    exact hg'

private lemma len_snoc (gs : List Gate) (g : Gate) (gs' : List Gate) (hgs : gs' = gs ++ [g]) :
    gs'.length = gs.length + 1 := by
  subst hgs
  simp

private lemma finish {n s' : ℕ} {F : (Fin n → Bool) → Bool} (gs : List Gate) (t : ℕ)
    (φ : (Fin n → Bool) → Bool) (hfan : ∀ g ∈ gs, Ok g) (hlen : gs.length ≤ s')
    (hc : Comp gs t φ) (hφ : ∀ x, φ x = F x) : HasCircuitSize n F s' :=
  ⟨⟨gs, t⟩, hfan, hlen, fun x => (hc.2 x).trans (hφ x)⟩

end PEqualNP.Outside.L_meta_627

theorem PEqualNP.Outside.L_meta_627 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  intro n s F u v h
  obtain ⟨C, hfan, hsz, o1, o2, hw⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hfan0 : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_627.Ok g := hfan
  have hw1 : ∀ x : Fin n → Bool, (PEqualNP.Outside.L_meta_627.W C.gates x).getD o1 false =
      F (Function.update x u (x v)) := fun x => (hw x).1
  have hw2 : ∀ x : Fin n → Bool, (PEqualNP.Outside.L_meta_627.W C.gates x).getD o2 false =
      F (Function.update x u (!(x v))) := fun x => (hw x).2
  have hlenW : ∀ x : Fin n → Bool, (PEqualNP.Outside.L_meta_627.W C.gates x).length =
      n + C.gates.length := fun x => PEqualNP.Outside.L_meta_627.W_len C.gates x
  have hid : ∀ x : Fin n → Bool, F x =
      ((((x u && x v) || !(x u || x v)) && F (Function.update x u (x v))) ||
        (!((x u && x v) || !(x u || x v)) && F (Function.update x u (!(x v))))) := by
    intro x
    by_cases hx : x u = x v
    · have hup : Function.update x u (x v) = x := by
        rw [← hx]
        exact Function.update_eq_self u x
      have he : ((x u && x v) || !(x u || x v)) = true := by
        rw [hx]
        cases x v <;> rfl
      rw [hup, he]
      simp
    · have hx' : x u = !(x v) := by
        cases hu : x u <;> cases hv : x v <;> simp_all
      have hup : Function.update x u (!(x v)) = x := by
        rw [← hx']
        exact Function.update_eq_self u x
      have he : ((x u && x v) || !(x u || x v)) = false := by
        rw [hx']
        cases x v <;> rfl
      rw [hup, he]
      simp
  have iu := fun gs : List PEqualNP.CircuitLowerBounds.Gate =>
    PEqualNP.Outside.L_meta_627.comp_input (n := n) gs u
  have iv := fun gs : List PEqualNP.CircuitLowerBounds.Gate =>
    PEqualNP.Outside.L_meta_627.comp_input (n := n) gs v
  by_cases h1 : o1 < n + C.gates.length
  · have c01 : PEqualNP.Outside.L_meta_627.Comp C.gates o1 (fun x => F (Function.update x u (x v))) :=
      ⟨h1, hw1⟩
    obtain ⟨P1, hP1⟩ : ∃ P1, P1 = C.gates ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [(u : ℕ), (v : ℕ)]⟩] := ⟨_, rfl⟩
    have c1 := PEqualNP.Outside.L_meta_627.comp_and (iu C.gates) (iv C.gates) P1 hP1
    obtain ⟨P2, hP2⟩ : ∃ P2, P2 = P1 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(u : ℕ), (v : ℕ)]⟩] := ⟨_, rfl⟩
    have c2 := PEqualNP.Outside.L_meta_627.comp_or (iu P1) (iv P1) P2 hP2
    obtain ⟨P3, hP3⟩ : ∃ P3, P3 = P2 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n + P1.length]⟩] := ⟨_, rfl⟩
    have c3 := PEqualNP.Outside.L_meta_627.comp_not c2 P3 hP3
    obtain ⟨P4, hP4⟩ : ∃ P4, P4 = P3 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [n + C.gates.length, n + P2.length]⟩] := ⟨_, rfl⟩
    have c1' := PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc c1 _ P2 hP2) _ P3 hP3
    have c4 := PEqualNP.Outside.L_meta_627.comp_or c1' c3 P4 hP4
    have f1 := PEqualNP.Outside.L_meta_627.fan_snoc hfan0 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P1 hP1
    have f2 := PEqualNP.Outside.L_meta_627.fan_snoc f1 _ (PEqualNP.Outside.L_meta_627.ok_or _ _) P2 hP2
    have f3 := PEqualNP.Outside.L_meta_627.fan_snoc f2 _ (PEqualNP.Outside.L_meta_627.ok_not _) P3 hP3
    have f4 := PEqualNP.Outside.L_meta_627.fan_snoc f3 _ (PEqualNP.Outside.L_meta_627.ok_or _ _) P4 hP4
    have l1 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P1 hP1
    have l2 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P2 hP2
    have l3 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P3 hP3
    have l4 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P4 hP4
    have c01' := PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc
      (PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc c01 _ P1 hP1) _ P2 hP2)
      _ P3 hP3) _ P4 hP4
    by_cases h2 : o2 < n + C.gates.length
    · have c02 : PEqualNP.Outside.L_meta_627.Comp C.gates o2
          (fun x => F (Function.update x u (!(x v)))) := ⟨h2, hw2⟩
      have c02' := PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc
        (PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc c02 _ P1 hP1) _ P2 hP2)
        _ P3 hP3) _ P4 hP4
      obtain ⟨P5, hP5⟩ : ∃ P5, P5 = P4 ++
        [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n + P3.length]⟩] := ⟨_, rfl⟩
      have c5 := PEqualNP.Outside.L_meta_627.comp_not c4 P5 hP5
      obtain ⟨P6, hP6⟩ : ∃ P6, P6 = P5 ++
        [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + P3.length, o1]⟩] := ⟨_, rfl⟩
      have c6 := PEqualNP.Outside.L_meta_627.comp_and (PEqualNP.Outside.L_meta_627.comp_snoc c4 _ P5 hP5)
        (PEqualNP.Outside.L_meta_627.comp_snoc c01' _ P5 hP5) P6 hP6
      obtain ⟨P7, hP7⟩ : ∃ P7, P7 = P6 ++
        [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + P4.length, o2]⟩] := ⟨_, rfl⟩
      have c7 := PEqualNP.Outside.L_meta_627.comp_and (PEqualNP.Outside.L_meta_627.comp_snoc c5 _ P6 hP6)
        (PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc c02' _ P5 hP5) _ P6 hP6)
        P7 hP7
      obtain ⟨P8, hP8⟩ : ∃ P8, P8 = P7 ++
        [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [n + P5.length, n + P6.length]⟩] := ⟨_, rfl⟩
      have c8 := PEqualNP.Outside.L_meta_627.comp_or (PEqualNP.Outside.L_meta_627.comp_snoc c6 _ P7 hP7) c7
        P8 hP8
      have f5 := PEqualNP.Outside.L_meta_627.fan_snoc f4 _ (PEqualNP.Outside.L_meta_627.ok_not _) P5 hP5
      have f6 := PEqualNP.Outside.L_meta_627.fan_snoc f5 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P6 hP6
      have f7 := PEqualNP.Outside.L_meta_627.fan_snoc f6 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P7 hP7
      have f8 := PEqualNP.Outside.L_meta_627.fan_snoc f7 _ (PEqualNP.Outside.L_meta_627.ok_or _ _) P8 hP8
      have l5 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P5 hP5
      have l6 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P6 hP6
      have l7 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P7 hP7
      have l8 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P8 hP8
      exact PEqualNP.Outside.L_meta_627.finish P8 _ _ f8 (by omega) c8 (fun x => (hid x).symm)
    · have hF2 : ∀ x : Fin n → Bool, F (Function.update x u (!(x v))) = false := by
        intro x
        rw [← hw2 x]
        exact List.getD_eq_default _ _ (by rw [hlenW x]; omega)
      obtain ⟨P5, hP5⟩ : ∃ P5, P5 = P4 ++
        [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + P3.length, o1]⟩] := ⟨_, rfl⟩
      have c5 := PEqualNP.Outside.L_meta_627.comp_and c4 c01' P5 hP5
      have f5 := PEqualNP.Outside.L_meta_627.fan_snoc f4 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P5 hP5
      have l5 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P5 hP5
      refine PEqualNP.Outside.L_meta_627.finish P5 _ _ f5 (by omega) c5 (fun x => ?_)
      rw [hid x, hF2 x]
      simp
  · have hF1 : ∀ x : Fin n → Bool, F (Function.update x u (x v)) = false := by
      intro x
      rw [← hw1 x]
      exact List.getD_eq_default _ _ (by rw [hlenW x]; omega)
    obtain ⟨P1, hP1⟩ : ∃ P1, P1 = C.gates ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [o2, o2]⟩] := ⟨_, rfl⟩
    have c1 := PEqualNP.Outside.L_meta_627.comp_copy hw2 P1 hP1
    obtain ⟨P2, hP2⟩ : ∃ P2, P2 = P1 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [(u : ℕ), (v : ℕ)]⟩] := ⟨_, rfl⟩
    have c2 := PEqualNP.Outside.L_meta_627.comp_and (iu P1) (iv P1) P2 hP2
    obtain ⟨P3, hP3⟩ : ∃ P3, P3 = P2 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(u : ℕ), (v : ℕ)]⟩] := ⟨_, rfl⟩
    have c3 := PEqualNP.Outside.L_meta_627.comp_or (iu P2) (iv P2) P3 hP3
    obtain ⟨P4, hP4⟩ : ∃ P4, P4 = P3 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n + P1.length]⟩] := ⟨_, rfl⟩
    have c4 := PEqualNP.Outside.L_meta_627.comp_not (PEqualNP.Outside.L_meta_627.comp_snoc c2 _ P3 hP3) P4 hP4
    obtain ⟨P5, hP5⟩ : ∃ P5, P5 = P4 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + P2.length, n + P3.length]⟩] := ⟨_, rfl⟩
    have c5 := PEqualNP.Outside.L_meta_627.comp_and (PEqualNP.Outside.L_meta_627.comp_snoc c3 _ P4 hP4) c4
      P5 hP5
    obtain ⟨P6, hP6⟩ : ∃ P6, P6 = P5 ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + P4.length, n + C.gates.length]⟩] := ⟨_, rfl⟩
    have c1' := PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc
      (PEqualNP.Outside.L_meta_627.comp_snoc (PEqualNP.Outside.L_meta_627.comp_snoc c1 _ P2 hP2) _ P3 hP3)
      _ P4 hP4) _ P5 hP5
    have c6 := PEqualNP.Outside.L_meta_627.comp_and c5 c1' P6 hP6
    have f1 := PEqualNP.Outside.L_meta_627.fan_snoc hfan0 _ (PEqualNP.Outside.L_meta_627.ok_or _ _) P1 hP1
    have f2 := PEqualNP.Outside.L_meta_627.fan_snoc f1 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P2 hP2
    have f3 := PEqualNP.Outside.L_meta_627.fan_snoc f2 _ (PEqualNP.Outside.L_meta_627.ok_or _ _) P3 hP3
    have f4 := PEqualNP.Outside.L_meta_627.fan_snoc f3 _ (PEqualNP.Outside.L_meta_627.ok_not _) P4 hP4
    have f5 := PEqualNP.Outside.L_meta_627.fan_snoc f4 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P5 hP5
    have f6 := PEqualNP.Outside.L_meta_627.fan_snoc f5 _ (PEqualNP.Outside.L_meta_627.ok_and _ _) P6 hP6
    have l1 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P1 hP1
    have l2 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P2 hP2
    have l3 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P3 hP3
    have l4 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P4 hP4
    have l5 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P5 hP5
    have l6 := PEqualNP.Outside.L_meta_627.len_snoc _ _ P6 hP6
    refine PEqualNP.Outside.L_meta_627.finish P6 _ _ f6 (by omega) c6 (fun x => ?_)
    rw [hid x, hF1 x]
    cases x u <;> cases x v <;> simp
