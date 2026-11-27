import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_143

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 4 × Fin 3

def par (a : VV → Bool) (f : Finset VV) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset VV) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : VV → Bool) (s t : Finset VV) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

def sdl : List (LinEq VV) → Finset VV
  | [] => ∅
  | e :: l => symmDiff e.1 (sdl l)

def xbl : List (LinEq VV) → Bool
  | [] => false
  | e :: l => xor (!e.2) (xbl l)

theorem par_sdl (a : VV → Bool) (L : List (LinEq VV)) (h : ∀ e ∈ L, ¬ LinEqSat a e) :
    (par a (sdl L) ↔ xbl L = true) := by
  induction L with
  | nil => simp [par, sdl, xbl]
  | cons e l ih =>
    obtain ⟨f, b⟩ := e
    have he := h (f, b) (List.mem_cons_self ..)
    have hl := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he2 : par a f ↔ ¬ (b = true) := by
      unfold LinEqSat at he; unfold par; simp only at he; tauto
    simp only [sdl, xbl]
    rw [par_sd, hl, he2]
    cases b <;> cases xbl l <;> simp

def okB (q : LinEq VV) (D : LinClause VV) (L : List (LinEq VV)) : Bool :=
  L.all (fun e => decide (e ∈ D)) && decide (q.1 = sdl L) && (q.2 == !(xbl L))

theorem weak_cert (C D : LinClause VV) (certs : List (List (LinEq VV)))
    (h : ∀ q ∈ C, ∃ L ∈ certs, okB q D L = true) :
    ∀ a : VV → Bool, LinClauseSat a C → LinClauseSat a D := by
  intro a ⟨q, hq, hs⟩
  obtain ⟨L, _, hok⟩ := h q hq
  simp only [okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hD, h1⟩, h2⟩ := hok
  by_contra hn
  have hn' : ∀ e ∈ L, ¬ LinEqSat a e := fun e he hse => hn ⟨e, hD e he, hse⟩
  have hp := par_sdl a L hn'
  unfold LinEqSat at hs
  rw [h1] at hs
  change par a (sdl L) ↔ q.2 = true at hs
  rw [hp, h2] at hs
  cases xbl L <;> simp at hs


def l0 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(0, 2)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l1 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true)} : LinClause VV)

def l2 : LinClause VV := ({(({(2, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l3 : LinClause VV := ({(({(3, 0)} : Finset VV), true), (({(3, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l4 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(1, 0)} : Finset VV), false)} : LinClause VV)

def l5 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l6 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : LinClause VV)

def l7 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l8 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : LinClause VV)

def l9 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l10 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l11 : LinClause VV := ({(({(2, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l12 : LinClause VV := ({(({(3, 1)} : Finset VV), false), (({(0, 1)} : Finset VV), false)} : LinClause VV)

def l13 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false)} : LinClause VV)

def l14 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def l15 : LinClause VV := ({(({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def l16 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), false)} : LinClause VV)

def l17 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), false)} : LinClause VV)

def l18 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : LinClause VV)

def l19 : LinClause VV := ({(({(2, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), false)} : LinClause VV)

def l20 : LinClause VV := ({(({(3, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), false)} : LinClause VV)

def l21 : LinClause VV := ({(({(2, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : LinClause VV)

def l22 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), false)} : LinClause VV)

def l23 : LinClause VV := ({(({(3, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(1, 2)} : Finset VV), false)} : LinClause VV)

def l24 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)

def l25 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)

def l26 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)

def l27 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l28 : LinClause VV := ({(({(3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l29 : LinClause VV := ({(({(3, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false)} : LinClause VV)

def l30 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l31 : LinClause VV := ({(({(2, 0)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true)} : LinClause VV)

def l32 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(3, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l33 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l34 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l35 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l36 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l37 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l38 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l39 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true)} : LinClause VV)

def l40 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(1, 0)} : Finset VV), true), (({(3, 2)} : Finset VV), true), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l41 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true), (({(2, 0)} : Finset VV), false)} : LinClause VV)

def l42 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l43 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 2)} : Finset VV), true)} : LinClause VV)

def l44 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), true)} : LinClause VV)

def l45 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)

def l46 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true)} : LinClause VV)

def l47 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)

def l48 : LinClause VV := ({(({(0, 0)} : Finset VV), false)} : LinClause VV)

def l49 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l50 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)

def l51 : LinClause VV := ({(({(0, 1)} : Finset VV), false)} : LinClause VV)

def l52 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)

def l53 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), true)} : LinClause VV)

def l54 : LinClause VV := ({(({(0, 2)} : Finset VV), false)} : LinClause VV)

def l55 : LinClause VV := ({(({(0, 2)} : Finset VV), true), (({(0, 1)} : Finset VV), true)} : LinClause VV)

def l56 : LinClause VV := ({(({(0, 2)} : Finset VV), true)} : LinClause VV)

def l57 : LinClause VV := (∅ : LinClause VV)

def p0 : List (LinClause VV) := [l0]

def p1 : List (LinClause VV) := l1 :: p0

def p2 : List (LinClause VV) := l2 :: p1

def p3 : List (LinClause VV) := l3 :: p2

def p4 : List (LinClause VV) := l4 :: p3

def p5 : List (LinClause VV) := l5 :: p4

def p6 : List (LinClause VV) := l6 :: p5

def p7 : List (LinClause VV) := l7 :: p6

def p8 : List (LinClause VV) := l8 :: p7

def p9 : List (LinClause VV) := l9 :: p8

def p10 : List (LinClause VV) := l10 :: p9

def p11 : List (LinClause VV) := l11 :: p10

def p12 : List (LinClause VV) := l12 :: p11

def p13 : List (LinClause VV) := l13 :: p12

def p14 : List (LinClause VV) := l14 :: p13

def p15 : List (LinClause VV) := l15 :: p14

def p16 : List (LinClause VV) := l16 :: p15

def p17 : List (LinClause VV) := l17 :: p16

def p18 : List (LinClause VV) := l18 :: p17

def p19 : List (LinClause VV) := l19 :: p18

def p20 : List (LinClause VV) := l20 :: p19

def p21 : List (LinClause VV) := l21 :: p20

def p22 : List (LinClause VV) := l22 :: p21

def p23 : List (LinClause VV) := l23 :: p22

def p24 : List (LinClause VV) := l24 :: p23

def p25 : List (LinClause VV) := l25 :: p24

def p26 : List (LinClause VV) := l26 :: p25

def p27 : List (LinClause VV) := l27 :: p26

def p28 : List (LinClause VV) := l28 :: p27

def p29 : List (LinClause VV) := l29 :: p28

def p30 : List (LinClause VV) := l30 :: p29

def p31 : List (LinClause VV) := l31 :: p30

def p32 : List (LinClause VV) := l32 :: p31

def p33 : List (LinClause VV) := l33 :: p32

def p34 : List (LinClause VV) := l34 :: p33

def p35 : List (LinClause VV) := l35 :: p34

def p36 : List (LinClause VV) := l36 :: p35

def p37 : List (LinClause VV) := l37 :: p36

def p38 : List (LinClause VV) := l38 :: p37

def p39 : List (LinClause VV) := l39 :: p38

def p40 : List (LinClause VV) := l40 :: p39

def p41 : List (LinClause VV) := l41 :: p40

def p42 : List (LinClause VV) := l42 :: p41

def p43 : List (LinClause VV) := l43 :: p42

def p44 : List (LinClause VV) := l44 :: p43

def p45 : List (LinClause VV) := l45 :: p44

def p46 : List (LinClause VV) := l46 :: p45

def p47 : List (LinClause VV) := l47 :: p46

def p48 : List (LinClause VV) := l48 :: p47

def p49 : List (LinClause VV) := l49 :: p48

def p50 : List (LinClause VV) := l50 :: p49

def p51 : List (LinClause VV) := l51 :: p50

def p52 : List (LinClause VV) := l52 :: p51

def p53 : List (LinClause VV) := l53 :: p52

def p54 : List (LinClause VV) := l54 :: p53

def p55 : List (LinClause VV) := l55 :: p54

def p56 : List (LinClause VV) := l56 :: p55

def p57 : List (LinClause VV) := l57 :: p56

set_option maxRecDepth 100000 in
theorem d0 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p0 :=
  IsLinDerivation.ax IsLinDerivation.nil ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((0 : Fin 4), j), true))), Set.mem_union_left _ ⟨0, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d1 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p1 :=
  IsLinDerivation.ax d0 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((1 : Fin 4), j), true))), Set.mem_union_left _ ⟨1, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d2 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p2 :=
  IsLinDerivation.ax d1 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((2 : Fin 4), j), true))), Set.mem_union_left _ ⟨2, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d3 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p3 :=
  IsLinDerivation.ax d2 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((3 : Fin 4), j), true))), Set.mem_union_left _ ⟨3, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d4 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p4 :=
  IsLinDerivation.ax d3 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((1 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d5 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p5 :=
  IsLinDerivation.ax d4 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((2 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d6 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p6 :=
  IsLinDerivation.ax d5 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d7 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p7 :=
  IsLinDerivation.ax d6 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (0 : Fin 3)), false), (((2 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d8 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p8 :=
  IsLinDerivation.ax d7 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d9 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p9 :=
  IsLinDerivation.ax d8 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d10 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p10 :=
  IsLinDerivation.ax d9 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((1 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d11 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p11 :=
  IsLinDerivation.ax d10 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((2 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d12 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p12 :=
  IsLinDerivation.ax d11 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d13 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p13 :=
  IsLinDerivation.ax d12 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (1 : Fin 3)), false), (((2 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d14 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p14 :=
  IsLinDerivation.ax d13 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d15 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p15 :=
  IsLinDerivation.ax d14 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d16 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p16 :=
  IsLinDerivation.ax d15 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((1 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d17 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p17 :=
  IsLinDerivation.ax d16 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((2 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d18 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p18 :=
  IsLinDerivation.ax d17 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d19 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p19 :=
  IsLinDerivation.ax d18 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (2 : Fin 3)), false), (((2 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d20 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p20 :=
  IsLinDerivation.ax d19 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d21 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p21 :=
  IsLinDerivation.ax d20 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d22 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p22 :=
  IsLinDerivation.res (C := l14) (D := l1) d21 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d23 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p23 :=
  IsLinDerivation.res (C := l20) (D := l3) d22 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d24 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p24 :=
  IsLinDerivation.res (C := l22) (D := l3) d23 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d25 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p25 :=
  IsLinDerivation.res (C := l21) (D := l24) d24 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d26 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p26 :=
  IsLinDerivation.res (C := l19) (D := l25) d25 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.head _) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d27 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p27 :=
  IsLinDerivation.res (C := l23) (D := l1) d26 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d28 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p28 :=
  IsLinDerivation.res (C := l13) (D := l27) d27 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) (List.Mem.head _) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d29 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p29 :=
  IsLinDerivation.res (C := l15) (D := l28) d28 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))) (List.Mem.head _) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d30 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p30 :=
  IsLinDerivation.res (C := l26) (D := l2) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d31 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p31 :=
  IsLinDerivation.res (C := l29) (D := l30) d30 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d32 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p32 :=
  IsLinDerivation.res (C := l8) (D := l3) d31 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d33 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p33 :=
  IsLinDerivation.res (C := l7) (D := l27) d32 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d34 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p34 :=
  IsLinDerivation.res (C := l9) (D := l33) d33 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) (List.Mem.head _) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d35 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p35 :=
  IsLinDerivation.res (C := l32) (D := l1) d34 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d36 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p36 :=
  IsLinDerivation.res (C := l21) (D := l35) d35 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) (List.Mem.head _) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d37 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p37 :=
  IsLinDerivation.res (C := l19) (D := l36) d36 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) (List.Mem.head _) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d38 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p38 :=
  IsLinDerivation.res (C := l34) (D := l2) d37 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d39 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p39 :=
  IsLinDerivation.res (C := l37) (D := l38) d38 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d40 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p40 :=
  IsLinDerivation.res (C := l9) (D := l24) d39 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d41 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p41 :=
  IsLinDerivation.res (C := l7) (D := l40) d40 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d42 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p42 :=
  IsLinDerivation.res (C := l13) (D := l35) d41 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d43 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p43 :=
  IsLinDerivation.res (C := l15) (D := l42) d42 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d44 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p44 :=
  IsLinDerivation.res (C := l41) (D := l2) d43 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d45 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p45 :=
  IsLinDerivation.res (C := l43) (D := l44) d44 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d46 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p46 :=
  IsLinDerivation.res (C := l4) (D := l31) d45 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d47 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p47 :=
  IsLinDerivation.res (C := l5) (D := l46) d46 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d48 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p48 :=
  IsLinDerivation.res (C := l6) (D := l47) d47 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d49 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p49 :=
  IsLinDerivation.res (C := l10) (D := l39) d48 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d50 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p50 :=
  IsLinDerivation.res (C := l11) (D := l49) d49 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d51 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p51 :=
  IsLinDerivation.res (C := l12) (D := l50) d50 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d52 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p52 :=
  IsLinDerivation.res (C := l16) (D := l45) d51 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d53 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p53 :=
  IsLinDerivation.res (C := l17) (D := l52) d52 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d54 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p54 :=
  IsLinDerivation.res (C := l18) (D := l53) d53 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d55 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p55 :=
  IsLinDerivation.res (C := l48) (D := l0) d54 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d56 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p56 :=
  IsLinDerivation.res (C := l51) (D := l55) d55 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.head _) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d57 : IsLinDerivation ((fun C => linOfClause C) '' PHP 4 3) p57 :=
  IsLinDerivation.res (C := l54) (D := l56) d56 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({(0, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem main_aux : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 62 :=
  ⟨p57, ⟨d57, List.Mem.head _⟩, by decide +kernel⟩

end PEqualNP.Outside.L_pcx_143

theorem PEqualNP.Outside.L_pcx_143 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 62 :=
  PEqualNP.Outside.L_pcx_143.main_aux
