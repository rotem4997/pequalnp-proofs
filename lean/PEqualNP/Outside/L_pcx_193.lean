import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_193

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 4 × Fin 3


def l0 : Clause VV := ({((0, 0), true), ((0, 1), true), ((0, 2), true)} : Clause VV)

def l1 : Clause VV := ({((1, 0), true), ((1, 1), true), ((1, 2), true)} : Clause VV)

def l2 : Clause VV := ({((2, 0), true), ((2, 1), true), ((2, 2), true)} : Clause VV)

def l3 : Clause VV := ({((3, 0), true), ((3, 1), true), ((3, 2), true)} : Clause VV)

def l4 : Clause VV := ({((0, 0), false), ((1, 0), false)} : Clause VV)

def l5 : Clause VV := ({((0, 0), false), ((2, 0), false)} : Clause VV)

def l6 : Clause VV := ({((0, 0), false), ((3, 0), false)} : Clause VV)

def l7 : Clause VV := ({((1, 0), false), ((2, 0), false)} : Clause VV)

def l8 : Clause VV := ({((1, 0), false), ((3, 0), false)} : Clause VV)

def l9 : Clause VV := ({((2, 0), false), ((3, 0), false)} : Clause VV)

def l10 : Clause VV := ({((0, 1), false), ((1, 1), false)} : Clause VV)

def l11 : Clause VV := ({((0, 1), false), ((2, 1), false)} : Clause VV)

def l12 : Clause VV := ({((0, 1), false), ((3, 1), false)} : Clause VV)

def l13 : Clause VV := ({((1, 1), false), ((2, 1), false)} : Clause VV)

def l14 : Clause VV := ({((1, 1), false), ((3, 1), false)} : Clause VV)

def l15 : Clause VV := ({((2, 1), false), ((3, 1), false)} : Clause VV)

def l16 : Clause VV := ({((0, 2), false), ((1, 2), false)} : Clause VV)

def l17 : Clause VV := ({((0, 2), false), ((2, 2), false)} : Clause VV)

def l18 : Clause VV := ({((0, 2), false), ((3, 2), false)} : Clause VV)

def l19 : Clause VV := ({((1, 2), false), ((2, 2), false)} : Clause VV)

def l20 : Clause VV := ({((1, 2), false), ((3, 2), false)} : Clause VV)

def l21 : Clause VV := ({((2, 2), false), ((3, 2), false)} : Clause VV)

def l22 : Clause VV := ({((1, 0), true), ((1, 2), true), ((3, 1), false)} : Clause VV)

def l23 : Clause VV := ({((1, 2), false), ((3, 0), true), ((3, 1), true)} : Clause VV)

def l24 : Clause VV := ({((1, 0), true), ((1, 2), true), ((3, 0), true), ((3, 2), true)} : Clause VV)

def l25 : Clause VV := ({((1, 0), true), ((1, 2), true), ((2, 2), false), ((3, 0), true)} : Clause VV)

def l26 : Clause VV := ({((1, 0), true), ((2, 2), false), ((3, 0), true)} : Clause VV)

def l27 : Clause VV := ({((1, 0), true), ((1, 1), true), ((3, 0), true), ((3, 1), true)} : Clause VV)

def l28 : Clause VV := ({((1, 0), true), ((2, 1), false), ((3, 0), true), ((3, 1), true)} : Clause VV)

def l29 : Clause VV := ({((1, 0), true), ((2, 1), false), ((3, 0), true)} : Clause VV)

def l30 : Clause VV := ({((1, 0), true), ((2, 0), true), ((2, 1), true), ((3, 0), true)} : Clause VV)

def l31 : Clause VV := ({((1, 0), true), ((2, 0), true), ((3, 0), true)} : Clause VV)

def l32 : Clause VV := ({((1, 0), false), ((3, 1), true), ((3, 2), true)} : Clause VV)

def l33 : Clause VV := ({((1, 1), true), ((2, 0), false), ((3, 0), true), ((3, 1), true)} : Clause VV)

def l34 : Clause VV := ({((1, 1), true), ((2, 0), false), ((3, 1), true)} : Clause VV)

def l35 : Clause VV := ({((1, 1), true), ((1, 2), true), ((3, 1), true), ((3, 2), true)} : Clause VV)

def l36 : Clause VV := ({((1, 1), true), ((1, 2), true), ((2, 2), false), ((3, 1), true)} : Clause VV)

def l37 : Clause VV := ({((1, 1), true), ((2, 2), false), ((3, 1), true)} : Clause VV)

def l38 : Clause VV := ({((1, 1), true), ((2, 1), true), ((2, 2), true), ((3, 1), true)} : Clause VV)

def l39 : Clause VV := ({((1, 1), true), ((2, 1), true), ((3, 1), true)} : Clause VV)

def l40 : Clause VV := ({((1, 0), true), ((1, 2), true), ((2, 0), false), ((3, 2), true)} : Clause VV)

def l41 : Clause VV := ({((1, 2), true), ((2, 0), false), ((3, 2), true)} : Clause VV)

def l42 : Clause VV := ({((1, 2), true), ((2, 1), false), ((3, 1), true), ((3, 2), true)} : Clause VV)

def l43 : Clause VV := ({((1, 2), true), ((2, 1), false), ((3, 2), true)} : Clause VV)

def l44 : Clause VV := ({((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 2), true)} : Clause VV)

def l45 : Clause VV := ({((1, 2), true), ((2, 2), true), ((3, 2), true)} : Clause VV)

def l46 : Clause VV := ({((0, 0), false), ((2, 0), true), ((3, 0), true)} : Clause VV)

def l47 : Clause VV := ({((0, 0), false), ((3, 0), true)} : Clause VV)

def l48 : Clause VV := ({((0, 0), false)} : Clause VV)

def l49 : Clause VV := ({((0, 1), false), ((2, 1), true), ((3, 1), true)} : Clause VV)

def l50 : Clause VV := ({((0, 1), false), ((3, 1), true)} : Clause VV)

def l51 : Clause VV := ({((0, 1), false)} : Clause VV)

def l52 : Clause VV := ({((0, 2), false), ((2, 2), true), ((3, 2), true)} : Clause VV)

def l53 : Clause VV := ({((0, 2), false), ((3, 2), true)} : Clause VV)

def l54 : Clause VV := ({((0, 2), false)} : Clause VV)

def l55 : Clause VV := ({((0, 1), true), ((0, 2), true)} : Clause VV)

def l56 : Clause VV := ({((0, 2), true)} : Clause VV)

def l57 : Clause VV := (∅ : Clause VV)

def p0 : List (Clause VV) := [l0]

def p1 : List (Clause VV) := l1 :: p0

def p2 : List (Clause VV) := l2 :: p1

def p3 : List (Clause VV) := l3 :: p2

def p4 : List (Clause VV) := l4 :: p3

def p5 : List (Clause VV) := l5 :: p4

def p6 : List (Clause VV) := l6 :: p5

def p7 : List (Clause VV) := l7 :: p6

def p8 : List (Clause VV) := l8 :: p7

def p9 : List (Clause VV) := l9 :: p8

def p10 : List (Clause VV) := l10 :: p9

def p11 : List (Clause VV) := l11 :: p10

def p12 : List (Clause VV) := l12 :: p11

def p13 : List (Clause VV) := l13 :: p12

def p14 : List (Clause VV) := l14 :: p13

def p15 : List (Clause VV) := l15 :: p14

def p16 : List (Clause VV) := l16 :: p15

def p17 : List (Clause VV) := l17 :: p16

def p18 : List (Clause VV) := l18 :: p17

def p19 : List (Clause VV) := l19 :: p18

def p20 : List (Clause VV) := l20 :: p19

def p21 : List (Clause VV) := l21 :: p20

def p22 : List (Clause VV) := l22 :: p21

def p23 : List (Clause VV) := l23 :: p22

def p24 : List (Clause VV) := l24 :: p23

def p25 : List (Clause VV) := l25 :: p24

def p26 : List (Clause VV) := l26 :: p25

def p27 : List (Clause VV) := l27 :: p26

def p28 : List (Clause VV) := l28 :: p27

def p29 : List (Clause VV) := l29 :: p28

def p30 : List (Clause VV) := l30 :: p29

def p31 : List (Clause VV) := l31 :: p30

def p32 : List (Clause VV) := l32 :: p31

def p33 : List (Clause VV) := l33 :: p32

def p34 : List (Clause VV) := l34 :: p33

def p35 : List (Clause VV) := l35 :: p34

def p36 : List (Clause VV) := l36 :: p35

def p37 : List (Clause VV) := l37 :: p36

def p38 : List (Clause VV) := l38 :: p37

def p39 : List (Clause VV) := l39 :: p38

def p40 : List (Clause VV) := l40 :: p39

def p41 : List (Clause VV) := l41 :: p40

def p42 : List (Clause VV) := l42 :: p41

def p43 : List (Clause VV) := l43 :: p42

def p44 : List (Clause VV) := l44 :: p43

def p45 : List (Clause VV) := l45 :: p44

def p46 : List (Clause VV) := l46 :: p45

def p47 : List (Clause VV) := l47 :: p46

def p48 : List (Clause VV) := l48 :: p47

def p49 : List (Clause VV) := l49 :: p48

def p50 : List (Clause VV) := l50 :: p49

def p51 : List (Clause VV) := l51 :: p50

def p52 : List (Clause VV) := l52 :: p51

def p53 : List (Clause VV) := l53 :: p52

def p54 : List (Clause VV) := l54 :: p53

def p55 : List (Clause VV) := l55 :: p54

def p56 : List (Clause VV) := l56 :: p55

def p57 : List (Clause VV) := l57 :: p56

set_option maxRecDepth 100000 in
theorem d0 : IsDerivation (PHP 4 3) p0 :=
  IsDerivation.ax IsDerivation.nil (Set.mem_union_left _ ⟨0, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d1 : IsDerivation (PHP 4 3) p1 :=
  IsDerivation.ax d0 (Set.mem_union_left _ ⟨1, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d2 : IsDerivation (PHP 4 3) p2 :=
  IsDerivation.ax d1 (Set.mem_union_left _ ⟨2, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d3 : IsDerivation (PHP 4 3) p3 :=
  IsDerivation.ax d2 (Set.mem_union_left _ ⟨3, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d4 : IsDerivation (PHP 4 3) p4 :=
  IsDerivation.ax d3 (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d5 : IsDerivation (PHP 4 3) p5 :=
  IsDerivation.ax d4 (Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d6 : IsDerivation (PHP 4 3) p6 :=
  IsDerivation.ax d5 (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d7 : IsDerivation (PHP 4 3) p7 :=
  IsDerivation.ax d6 (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d8 : IsDerivation (PHP 4 3) p8 :=
  IsDerivation.ax d7 (Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d9 : IsDerivation (PHP 4 3) p9 :=
  IsDerivation.ax d8 (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d10 : IsDerivation (PHP 4 3) p10 :=
  IsDerivation.ax d9 (Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d11 : IsDerivation (PHP 4 3) p11 :=
  IsDerivation.ax d10 (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d12 : IsDerivation (PHP 4 3) p12 :=
  IsDerivation.ax d11 (Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d13 : IsDerivation (PHP 4 3) p13 :=
  IsDerivation.ax d12 (Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d14 : IsDerivation (PHP 4 3) p14 :=
  IsDerivation.ax d13 (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d15 : IsDerivation (PHP 4 3) p15 :=
  IsDerivation.ax d14 (Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d16 : IsDerivation (PHP 4 3) p16 :=
  IsDerivation.ax d15 (Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d17 : IsDerivation (PHP 4 3) p17 :=
  IsDerivation.ax d16 (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d18 : IsDerivation (PHP 4 3) p18 :=
  IsDerivation.ax d17 (Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d19 : IsDerivation (PHP 4 3) p19 :=
  IsDerivation.ax d18 (Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d20 : IsDerivation (PHP 4 3) p20 :=
  IsDerivation.ax d19 (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d21 : IsDerivation (PHP 4 3) p21 :=
  IsDerivation.ax d20 (Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d22 : IsDerivation (PHP 4 3) p22 :=
  IsDerivation.res (C := l1) (D := l14) d21 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d23 : IsDerivation (PHP 4 3) p23 :=
  IsDerivation.res (C := l3) (D := l20) d22 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d24 : IsDerivation (PHP 4 3) p24 :=
  IsDerivation.res (C := l3) (D := l22) d23 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) (List.Mem.tail _ (List.Mem.head _)) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d25 : IsDerivation (PHP 4 3) p25 :=
  IsDerivation.res (C := l24) (D := l21) d24 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d26 : IsDerivation (PHP 4 3) p26 :=
  IsDerivation.res (C := l25) (D := l19) d25 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d27 : IsDerivation (PHP 4 3) p27 :=
  IsDerivation.res (C := l1) (D := l23) d26 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d28 : IsDerivation (PHP 4 3) p28 :=
  IsDerivation.res (C := l27) (D := l13) d27 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d29 : IsDerivation (PHP 4 3) p29 :=
  IsDerivation.res (C := l28) (D := l15) d28 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d30 : IsDerivation (PHP 4 3) p30 :=
  IsDerivation.res (C := l2) (D := l26) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d31 : IsDerivation (PHP 4 3) p31 :=
  IsDerivation.res (C := l30) (D := l29) d30 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d32 : IsDerivation (PHP 4 3) p32 :=
  IsDerivation.res (C := l3) (D := l8) d31 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d33 : IsDerivation (PHP 4 3) p33 :=
  IsDerivation.res (C := l27) (D := l7) d32 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d34 : IsDerivation (PHP 4 3) p34 :=
  IsDerivation.res (C := l33) (D := l9) d33 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d35 : IsDerivation (PHP 4 3) p35 :=
  IsDerivation.res (C := l1) (D := l32) d34 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d36 : IsDerivation (PHP 4 3) p36 :=
  IsDerivation.res (C := l35) (D := l21) d35 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d37 : IsDerivation (PHP 4 3) p37 :=
  IsDerivation.res (C := l36) (D := l19) d36 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d38 : IsDerivation (PHP 4 3) p38 :=
  IsDerivation.res (C := l2) (D := l34) d37 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d39 : IsDerivation (PHP 4 3) p39 :=
  IsDerivation.res (C := l38) (D := l37) d38 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d40 : IsDerivation (PHP 4 3) p40 :=
  IsDerivation.res (C := l24) (D := l9) d39 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d41 : IsDerivation (PHP 4 3) p41 :=
  IsDerivation.res (C := l40) (D := l7) d40 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d42 : IsDerivation (PHP 4 3) p42 :=
  IsDerivation.res (C := l35) (D := l13) d41 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d43 : IsDerivation (PHP 4 3) p43 :=
  IsDerivation.res (C := l42) (D := l15) d42 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d44 : IsDerivation (PHP 4 3) p44 :=
  IsDerivation.res (C := l2) (D := l41) d43 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d45 : IsDerivation (PHP 4 3) p45 :=
  IsDerivation.res (C := l44) (D := l43) d44 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d46 : IsDerivation (PHP 4 3) p46 :=
  IsDerivation.res (C := l31) (D := l4) d45 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d47 : IsDerivation (PHP 4 3) p47 :=
  IsDerivation.res (C := l46) (D := l5) d46 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d48 : IsDerivation (PHP 4 3) p48 :=
  IsDerivation.res (C := l47) (D := l6) d47 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d49 : IsDerivation (PHP 4 3) p49 :=
  IsDerivation.res (C := l39) (D := l10) d48 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d50 : IsDerivation (PHP 4 3) p50 :=
  IsDerivation.res (C := l49) (D := l11) d49 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d51 : IsDerivation (PHP 4 3) p51 :=
  IsDerivation.res (C := l50) (D := l12) d50 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d52 : IsDerivation (PHP 4 3) p52 :=
  IsDerivation.res (C := l45) (D := l16) d51 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d53 : IsDerivation (PHP 4 3) p53 :=
  IsDerivation.res (C := l52) (D := l17) d52 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d54 : IsDerivation (PHP 4 3) p54 :=
  IsDerivation.res (C := l53) (D := l18) d53 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d55 : IsDerivation (PHP 4 3) p55 :=
  IsDerivation.res (C := l0) (D := l48) d54 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ⟨(0, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d56 : IsDerivation (PHP 4 3) p56 :=
  IsDerivation.res (C := l55) (D := l51) d55 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ⟨(0, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem d57 : IsDerivation (PHP 4 3) p57 :=
  IsDerivation.res (C := l56) (D := l54) d56 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ⟨(0, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem res_aux : ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 59 :=
  ⟨p57, ⟨d57, List.Mem.head _⟩, by decide +kernel⟩


theorem kline_inj {V : Type} [DecidableEq V] :
    Function.Injective (fun l : Literal V => ({l} : KTerm V)) :=
  fun _ _ h => Finset.singleton_injective h

theorem sim {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)}
    (h : IsDerivation F π) :
    IsResKDerivation 2 ((fun C => kLineOfClause C) '' F) (π.map kLineOfClause) := by
  induction h with
  | nil => exact IsResKDerivation.nil
  | @ax π C _ hC ih =>
    refine IsResKDerivation.ax ih ⟨C, hC, rfl⟩ ?_
    intro T hT
    simp only [kLineOfClause, Finset.mem_image] at hT
    obtain ⟨l, _, rfl⟩ := hT
    simp
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨v, hv1, hv2, rfl⟩ := hR
    refine IsResKDerivation.cut (C := kLineOfClause C) (D := kLineOfClause D) ih
      (List.mem_map.2 ⟨C, hC, rfl⟩) (List.mem_map.2 ⟨D, hD, rfl⟩) ?_
    refine ⟨{(v, true)}, ?_, Finset.singleton_nonempty _, ?_, ?_⟩
    · exact Finset.mem_image_of_mem _ hv1
    · intro l hl
      rw [Finset.mem_singleton] at hl
      subst hl
      exact Finset.mem_image_of_mem _ hv2
    · simp only [kLineOfClause, Finset.image_union, Finset.image_singleton]
      rw [Finset.image_erase kline_inj, Finset.image_erase kline_inj,
        Finset.sdiff_singleton_eq_erase]
      rfl

theorem main_aux : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 62 := by
  obtain ⟨π, ⟨hd, he⟩, hl⟩ := res_aux
  have e0 : kLineOfClause (∅ : Clause (Fin 4 × Fin 3)) = ∅ := by simp [kLineOfClause]
  refine ⟨π.map kLineOfClause, ⟨sim hd, List.mem_map.2 ⟨∅, he, e0⟩⟩, ?_⟩
  rw [List.length_map]
  omega

end PEqualNP.Outside.L_pcx_193

theorem PEqualNP.Outside.L_pcx_193 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 62 :=
  PEqualNP.Outside.L_pcx_193.main_aux
