import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_137
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 2
abbrev LC := LinClause V
abbrev F := ((fun C => linOfClause C) '' BPHP 5 2)
def inputClause (i j : Fin 5) (h : Nat) : Clause V :=
  Finset.univ.image (fun b : Fin 2 => ((i,b), !h.testBit b.val)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j,b), !h.testBit b.val))
theorem inputMem (i j : Fin 5) (h : Nat) (hd : i ≠ j) : linOfClause (inputClause i j h) ∈ F :=
  ⟨inputClause i j h, ⟨i, j, fun b => h.testBit b.val, hd, rfl⟩, rfl⟩
theorem lineAt (l : List LC) (k : Nat) (bound : k < l.length) : l[k] ∈ l := List.getElem_mem bound

def l0 : LC := linOfClause (inputClause 1 3 2)
def p0 : List LC := l0 :: []
theorem d0 : IsLinDerivation F p0 :=
  IsLinDerivation.ax IsLinDerivation.nil (inputMem 1 3 2 (by decide))

def l1 : LC := linOfClause (inputClause 2 3 0)
def p1 : List LC := l1 :: p0
theorem d1 : IsLinDerivation F p1 :=
  IsLinDerivation.ax d0 (inputMem 2 3 0 (by decide))

def l2 : LC := linOfClause (inputClause 0 3 3)
def p2 : List LC := l2 :: p1
theorem d2 : IsLinDerivation F p2 :=
  IsLinDerivation.ax d1 (inputMem 0 3 3 (by decide))

def l3 : LC := linOfClause (inputClause 2 3 2)
def p3 : List LC := l3 :: p2
theorem d3 : IsLinDerivation F p3 :=
  IsLinDerivation.ax d2 (inputMem 2 3 2 (by decide))

def l4 : LC := linOfClause (inputClause 2 4 1)
def p4 : List LC := l4 :: p3
theorem d4 : IsLinDerivation F p4 :=
  IsLinDerivation.ax d3 (inputMem 2 4 1 (by decide))

def l5 : LC := linOfClause (inputClause 0 1 2)
def p5 : List LC := l5 :: p4
theorem d5 : IsLinDerivation F p5 :=
  IsLinDerivation.ax d4 (inputMem 0 1 2 (by decide))

def l6 : LC := linOfClause (inputClause 2 4 0)
def p6 : List LC := l6 :: p5
theorem d6 : IsLinDerivation F p6 :=
  IsLinDerivation.ax d5 (inputMem 2 4 0 (by decide))

def l7 : LC := linOfClause (inputClause 0 1 1)
def p7 : List LC := l7 :: p6
theorem d7 : IsLinDerivation F p7 :=
  IsLinDerivation.ax d6 (inputMem 0 1 1 (by decide))

def l8 : LC := linOfClause (inputClause 1 4 3)
def p8 : List LC := l8 :: p7
theorem d8 : IsLinDerivation F p8 :=
  IsLinDerivation.ax d7 (inputMem 1 4 3 (by decide))

def l9 : LC := linOfClause (inputClause 0 2 1)
def p9 : List LC := l9 :: p8
theorem d9 : IsLinDerivation F p9 :=
  IsLinDerivation.ax d8 (inputMem 0 2 1 (by decide))

def l10 : LC := linOfClause (inputClause 0 4 3)
def p10 : List LC := l10 :: p9
theorem d10 : IsLinDerivation F p10 :=
  IsLinDerivation.ax d9 (inputMem 0 4 3 (by decide))

def l11 : LC := linOfClause (inputClause 0 2 0)
def p11 : List LC := l11 :: p10
theorem d11 : IsLinDerivation F p11 :=
  IsLinDerivation.ax d10 (inputMem 0 2 0 (by decide))

def l12 : LC := linOfClause (inputClause 1 2 2)
def p12 : List LC := l12 :: p11
theorem d12 : IsLinDerivation F p12 :=
  IsLinDerivation.ax d11 (inputMem 1 2 2 (by decide))

def l13 : LC := linOfClause (inputClause 0 4 0)
def p13 : List LC := l13 :: p12
theorem d13 : IsLinDerivation F p13 :=
  IsLinDerivation.ax d12 (inputMem 0 4 0 (by decide))

def l14 : LC := linOfClause (inputClause 3 4 3)
def p14 : List LC := l14 :: p13
theorem d14 : IsLinDerivation F p14 :=
  IsLinDerivation.ax d13 (inputMem 3 4 3 (by decide))

def l15 : LC := linOfClause (inputClause 2 4 3)
def p15 : List LC := l15 :: p14
theorem d15 : IsLinDerivation F p15 :=
  IsLinDerivation.ax d14 (inputMem 2 4 3 (by decide))

def l16 : LC := linOfClause (inputClause 1 2 1)
def p16 : List LC := l16 :: p15
theorem d16 : IsLinDerivation F p16 :=
  IsLinDerivation.ax d15 (inputMem 1 2 1 (by decide))

def l17 : LC := linOfClause (inputClause 2 3 1)
def p17 : List LC := l17 :: p16
theorem d17 : IsLinDerivation F p17 :=
  IsLinDerivation.ax d16 (inputMem 2 3 1 (by decide))

def l18 : LC := linOfClause (inputClause 1 4 2)
def p18 : List LC := l18 :: p17
theorem d18 : IsLinDerivation F p18 :=
  IsLinDerivation.ax d17 (inputMem 1 4 2 (by decide))

def l19 : LC := linOfClause (inputClause 1 4 1)
def p19 : List LC := l19 :: p18
theorem d19 : IsLinDerivation F p19 :=
  IsLinDerivation.ax d18 (inputMem 1 4 1 (by decide))

def l20 : LC := linOfClause (inputClause 1 4 0)
def p20 : List LC := l20 :: p19
theorem d20 : IsLinDerivation F p20 :=
  IsLinDerivation.ax d19 (inputMem 1 4 0 (by decide))

def l21 : LC := linOfClause (inputClause 1 3 0)
def p21 : List LC := l21 :: p20
theorem d21 : IsLinDerivation F p21 :=
  IsLinDerivation.ax d20 (inputMem 1 3 0 (by decide))

def l22 : LC := linOfClause (inputClause 2 3 3)
def p22 : List LC := l22 :: p21
theorem d22 : IsLinDerivation F p22 :=
  IsLinDerivation.ax d21 (inputMem 2 3 3 (by decide))

def l23 : LC := linOfClause (inputClause 3 4 0)
def p23 : List LC := l23 :: p22
theorem d23 : IsLinDerivation F p23 :=
  IsLinDerivation.ax d22 (inputMem 3 4 0 (by decide))

def l24 : LC := linOfClause (inputClause 2 4 2)
def p24 : List LC := l24 :: p23
theorem d24 : IsLinDerivation F p24 :=
  IsLinDerivation.ax d23 (inputMem 2 4 2 (by decide))

def l25 : LC := linOfClause (inputClause 0 1 3)
def p25 : List LC := l25 :: p24
theorem d25 : IsLinDerivation F p25 :=
  IsLinDerivation.ax d24 (inputMem 0 1 3 (by decide))

def l26 : LC := linOfClause (inputClause 1 2 3)
def p26 : List LC := l26 :: p25
theorem d26 : IsLinDerivation F p26 :=
  IsLinDerivation.ax d25 (inputMem 1 2 3 (by decide))

def l27 : LC := linOfClause (inputClause 0 3 0)
def p27 : List LC := l27 :: p26
theorem d27 : IsLinDerivation F p27 :=
  IsLinDerivation.ax d26 (inputMem 0 3 0 (by decide))

def l28 : LC := linOfClause (inputClause 0 4 2)
def p28 : List LC := l28 :: p27
theorem d28 : IsLinDerivation F p28 :=
  IsLinDerivation.ax d27 (inputMem 0 4 2 (by decide))

def l29 : LC := linOfClause (inputClause 0 4 1)
def p29 : List LC := l29 :: p28
theorem d29 : IsLinDerivation F p29 :=
  IsLinDerivation.ax d28 (inputMem 0 4 1 (by decide))

def l30 : LC := linOfClause (inputClause 0 2 2)
def p30 : List LC := l30 :: p29
theorem d30 : IsLinDerivation F p30 :=
  IsLinDerivation.ax d29 (inputMem 0 2 2 (by decide))

def l31 : LC := linOfClause (inputClause 0 1 0)
def p31 : List LC := l31 :: p30
theorem d31 : IsLinDerivation F p31 :=
  IsLinDerivation.ax d30 (inputMem 0 1 0 (by decide))

def l32 : LC := linOfClause (inputClause 0 2 3)
def p32 : List LC := l32 :: p31
theorem d32 : IsLinDerivation F p32 :=
  IsLinDerivation.ax d31 (inputMem 0 2 3 (by decide))

def l33 : LC := linOfClause (inputClause 0 3 2)
def p33 : List LC := l33 :: p32
theorem d33 : IsLinDerivation F p33 :=
  IsLinDerivation.ax d32 (inputMem 0 3 2 (by decide))

def l34 : LC := linOfClause (inputClause 3 4 2)
def p34 : List LC := l34 :: p33
theorem d34 : IsLinDerivation F p34 :=
  IsLinDerivation.ax d33 (inputMem 3 4 2 (by decide))

def l35 : LC := linOfClause (inputClause 1 3 1)
def p35 : List LC := l35 :: p34
theorem d35 : IsLinDerivation F p35 :=
  IsLinDerivation.ax d34 (inputMem 1 3 1 (by decide))

def l36 : LC := linOfClause (inputClause 0 3 1)
def p36 : List LC := l36 :: p35
theorem d36 : IsLinDerivation F p36 :=
  IsLinDerivation.ax d35 (inputMem 0 3 1 (by decide))

def l37 : LC := linOfClause (inputClause 3 4 1)
def p37 : List LC := l37 :: p36
theorem d37 : IsLinDerivation F p37 :=
  IsLinDerivation.ax d36 (inputMem 3 4 1 (by decide))

def l38 : LC := linOfClause (inputClause 1 3 3)
def p38 : List LC := l38 :: p37
theorem d38 : IsLinDerivation F p38 :=
  IsLinDerivation.ax d37 (inputMem 1 3 3 (by decide))

def l39 : LC := linOfClause (inputClause 1 2 0)
def p39 : List LC := l39 :: p38
theorem d39 : IsLinDerivation F p39 :=
  IsLinDerivation.ax d38 (inputMem 1 2 0 (by decide))

def l40 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p40 : List LC := l40 :: p39
theorem d40 : IsLinDerivation F p40 :=
  IsLinDerivation.res (C := l17) (D := l27) d39
    (lineAt p39 22 (by decide +kernel)) (lineAt p39 12 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l41 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p41 : List LC := l41 :: p40
theorem d41 : IsLinDerivation F p41 :=
  IsLinDerivation.res (C := l16) (D := l31) d40
    (lineAt p40 24 (by decide +kernel)) (lineAt p40 9 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l42 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p42 : List LC := l42 :: p41
theorem d42 : IsLinDerivation F p42 :=
  IsLinDerivation.res (C := l4) (D := l13) d41
    (lineAt p41 37 (by decide +kernel)) (lineAt p41 28 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l43 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p43 : List LC := l43 :: p42
theorem d43 : IsLinDerivation F p43 :=
  IsLinDerivation.res (C := l8) (D := l34) d42
    (lineAt p42 34 (by decide +kernel)) (lineAt p42 8 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l44 : LC := {(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p44 : List LC := l44 :: p43
theorem d44 : IsLinDerivation F p44 :=
  IsLinDerivation.res (C := l43) (D := l0) d43
    (lineAt p43 0 (by decide +kernel)) (lineAt p43 43 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l45 : LC := {(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p45 : List LC := l45 :: p44
theorem d45 : IsLinDerivation F p45 :=
  IsLinDerivation.res (C := l38) (D := l18) d44
    (lineAt p44 6 (by decide +kernel)) (lineAt p44 26 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l46 : LC := {(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p46 : List LC := l46 :: p45
theorem d46 : IsLinDerivation F p46 :=
  IsLinDerivation.res (C := l14) (D := l45) d45
    (lineAt p45 31 (by decide +kernel)) (lineAt p45 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l47 : LC := {(({(1,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p47 : List LC := l47 :: p46
theorem d47 : IsLinDerivation F p47 :=
  IsLinDerivation.res (C := l46) (D := l44) d46
    (lineAt p46 0 (by decide +kernel)) (lineAt p46 2 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l48 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p48 : List LC := l48 :: p47
theorem d48 : IsLinDerivation F p48 :=
  IsLinDerivation.res (C := l47) (D := l42) d47
    (lineAt p47 0 (by decide +kernel)) (lineAt p47 5 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l49 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p49 : List LC := l49 :: p48
theorem d49 : IsLinDerivation F p49 :=
  IsLinDerivation.res (C := l48) (D := l41) d48
    (lineAt p48 0 (by decide +kernel)) (lineAt p48 7 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l50 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p50 : List LC := l50 :: p49
theorem d50 : IsLinDerivation F p50 :=
  IsLinDerivation.res (C := l49) (D := l40) d49
    (lineAt p49 0 (by decide +kernel)) (lineAt p49 9 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l51 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p51 : List LC := l51 :: p50
theorem d51 : IsLinDerivation F p51 :=
  IsLinDerivation.res (C := l9) (D := l50) d50
    (lineAt p50 41 (by decide +kernel)) (lineAt p50 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l52 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p52 : List LC := l52 :: p51
theorem d52 : IsLinDerivation F p52 :=
  IsLinDerivation.res (C := l36) (D := l1) d51
    (lineAt p51 15 (by decide +kernel)) (lineAt p51 50 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l53 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p53 : List LC := l53 :: p52
theorem d53 : IsLinDerivation F p53 :=
  IsLinDerivation.res (C := l47) (D := l52) d52
    (lineAt p52 5 (by decide +kernel)) (lineAt p52 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l54 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true)}
def p54 : List LC := l54 :: p53
theorem d54 : IsLinDerivation F p54 :=
  IsLinDerivation.res (C := l7) (D := l39) d53
    (lineAt p53 46 (by decide +kernel)) (lineAt p53 14 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l55 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p55 : List LC := l55 :: p54
theorem d55 : IsLinDerivation F p55 :=
  IsLinDerivation.res (C := l53) (D := l54) d54
    (lineAt p54 1 (by decide +kernel)) (lineAt p54 0 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l56 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p56 : List LC := l56 :: p55
theorem d56 : IsLinDerivation F p56 :=
  IsLinDerivation.res (C := l29) (D := l6) d55
    (lineAt p55 26 (by decide +kernel)) (lineAt p55 49 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l57 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true)}
def p57 : List LC := l57 :: p56
theorem d57 : IsLinDerivation F p57 :=
  IsLinDerivation.res (C := l55) (D := l56) d56
    (lineAt p56 1 (by decide +kernel)) (lineAt p56 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l58 : LC := {(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true)}
def p58 : List LC := l58 :: p57
theorem d58 : IsLinDerivation F p58 :=
  IsLinDerivation.res (C := l57) (D := l11) d57
    (lineAt p57 0 (by decide +kernel)) (lineAt p57 46 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l59 : LC := {(({(0,1)} : Finset V),true),(({(2,1)} : Finset V),true)}
def p59 : List LC := l59 :: p58
theorem d59 : IsLinDerivation F p59 :=
  IsLinDerivation.res (C := l51) (D := l58) d58
    (lineAt p58 7 (by decide +kernel)) (lineAt p58 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l60 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p60 : List LC := l60 :: p59
theorem d60 : IsLinDerivation F p60 :=
  IsLinDerivation.res (C := l38) (D := l5) d59
    (lineAt p59 21 (by decide +kernel)) (lineAt p59 54 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l61 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p61 : List LC := l61 :: p60
theorem d61 : IsLinDerivation F p61 :=
  IsLinDerivation.res (C := l2) (D := l60) d60
    (lineAt p60 58 (by decide +kernel)) (lineAt p60 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l62 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p62 : List LC := l62 :: p61
theorem d62 : IsLinDerivation F p62 :=
  IsLinDerivation.res (C := l37) (D := l6) d61
    (lineAt p61 24 (by decide +kernel)) (lineAt p61 55 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l63 : LC := {(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p63 : List LC := l63 :: p62
theorem d63 : IsLinDerivation F p63 :=
  IsLinDerivation.res (C := l17) (D := l62) d62
    (lineAt p62 45 (by decide +kernel)) (lineAt p62 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l64 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p64 : List LC := l64 :: p63
theorem d64 : IsLinDerivation F p64 :=
  IsLinDerivation.res (C := l61) (D := l63) d63
    (lineAt p63 2 (by decide +kernel)) (lineAt p63 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l65 : LC := {(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p65 : List LC := l65 :: p64
theorem d65 : IsLinDerivation F p65 :=
  IsLinDerivation.res (C := l4) (D := l1) d64
    (lineAt p64 60 (by decide +kernel)) (lineAt p64 63 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l66 : LC := {(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p66 : List LC := l66 :: p65
theorem d66 : IsLinDerivation F p66 :=
  IsLinDerivation.res (C := l65) (D := l23) d65
    (lineAt p65 0 (by decide +kernel)) (lineAt p65 42 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l67 : LC := {(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p67 : List LC := l67 :: p66
theorem d67 : IsLinDerivation F p67 :=
  IsLinDerivation.res (C := l25) (D := l33) d66
    (lineAt p66 41 (by decide +kernel)) (lineAt p66 33 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l68 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p68 : List LC := l68 :: p67
theorem d68 : IsLinDerivation F p68 :=
  IsLinDerivation.res (C := l67) (D := l0) d67
    (lineAt p67 0 (by decide +kernel)) (lineAt p67 67 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l69 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p69 : List LC := l69 :: p68
theorem d69 : IsLinDerivation F p69 :=
  IsLinDerivation.res (C := l68) (D := l66) d68
    (lineAt p68 0 (by decide +kernel)) (lineAt p68 2 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l70 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p70 : List LC := l70 :: p69
theorem d70 : IsLinDerivation F p70 :=
  IsLinDerivation.res (C := l64) (D := l69) d69
    (lineAt p69 5 (by decide +kernel)) (lineAt p69 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l71 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p71 : List LC := l71 :: p70
theorem d71 : IsLinDerivation F p71 :=
  IsLinDerivation.res (C := l16) (D := l6) d70
    (lineAt p70 54 (by decide +kernel)) (lineAt p70 64 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l72 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p72 : List LC := l72 :: p71
theorem d72 : IsLinDerivation F p72 :=
  IsLinDerivation.res (C := l19) (D := l71) d71
    (lineAt p71 52 (by decide +kernel)) (lineAt p71 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l73 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p73 : List LC := l73 :: p72
theorem d73 : IsLinDerivation F p73 :=
  IsLinDerivation.res (C := l4) (D := l39) d72
    (lineAt p72 68 (by decide +kernel)) (lineAt p72 33 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l74 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p74 : List LC := l74 :: p73
theorem d74 : IsLinDerivation F p74 :=
  IsLinDerivation.res (C := l73) (D := l20) d73
    (lineAt p73 0 (by decide +kernel)) (lineAt p73 53 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l75 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p75 : List LC := l75 :: p74
theorem d75 : IsLinDerivation F p75 :=
  IsLinDerivation.res (C := l72) (D := l74) d74
    (lineAt p74 2 (by decide +kernel)) (lineAt p74 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l76 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p76 : List LC := l76 :: p75
theorem d76 : IsLinDerivation F p76 :=
  IsLinDerivation.res (C := l70) (D := l75) d75
    (lineAt p75 5 (by decide +kernel)) (lineAt p75 0 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l77 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p77 : List LC := l77 :: p76
theorem d77 : IsLinDerivation F p77 :=
  IsLinDerivation.res (C := l8) (D := l5) d76
    (lineAt p76 68 (by decide +kernel)) (lineAt p76 71 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l78 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p78 : List LC := l78 :: p77
theorem d78 : IsLinDerivation F p78 :=
  IsLinDerivation.res (C := l77) (D := l28) d77
    (lineAt p77 0 (by decide +kernel)) (lineAt p77 49 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l79 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p79 : List LC := l79 :: p78
theorem d79 : IsLinDerivation F p79 :=
  IsLinDerivation.res (C := l10) (D := l18) d78
    (lineAt p78 68 (by decide +kernel)) (lineAt p78 60 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l80 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p80 : List LC := l80 :: p79
theorem d80 : IsLinDerivation F p80 :=
  IsLinDerivation.res (C := l25) (D := l79) d79
    (lineAt p79 54 (by decide +kernel)) (lineAt p79 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l81 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p81 : List LC := l81 :: p80
theorem d81 : IsLinDerivation F p81 :=
  IsLinDerivation.res (C := l80) (D := l78) d80
    (lineAt p80 0 (by decide +kernel)) (lineAt p80 2 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l82 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p82 : List LC := l82 :: p81
theorem d82 : IsLinDerivation F p82 :=
  IsLinDerivation.res (C := l10) (D := l34) d81
    (lineAt p81 71 (by decide +kernel)) (lineAt p81 47 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l83 : LC := {(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p83 : List LC := l83 :: p82
theorem d83 : IsLinDerivation F p83 :=
  IsLinDerivation.res (C := l82) (D := l33) d82
    (lineAt p82 0 (by decide +kernel)) (lineAt p82 49 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l84 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p84 : List LC := l84 :: p83
theorem d84 : IsLinDerivation F p84 :=
  IsLinDerivation.res (C := l16) (D := l1) d83
    (lineAt p83 67 (by decide +kernel)) (lineAt p83 82 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l85 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p85 : List LC := l85 :: p84
theorem d85 : IsLinDerivation F p85 :=
  IsLinDerivation.res (C := l84) (D := l21) d84
    (lineAt p84 0 (by decide +kernel)) (lineAt p84 63 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l86 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p86 : List LC := l86 :: p85
theorem d86 : IsLinDerivation F p86 :=
  IsLinDerivation.res (C := l83) (D := l85) d85
    (lineAt p85 2 (by decide +kernel)) (lineAt p85 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l87 : LC := {(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p87 : List LC := l87 :: p86
theorem d87 : IsLinDerivation F p87 :=
  IsLinDerivation.res (C := l2) (D := l28) d86
    (lineAt p86 84 (by decide +kernel)) (lineAt p86 58 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l88 : LC := {(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p88 : List LC := l88 :: p87
theorem d88 : IsLinDerivation F p88 :=
  IsLinDerivation.res (C := l14) (D := l87) d87
    (lineAt p87 73 (by decide +kernel)) (lineAt p87 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l89 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p89 : List LC := l89 :: p88
theorem d89 : IsLinDerivation F p89 :=
  IsLinDerivation.res (C := l17) (D := l39) d88
    (lineAt p88 71 (by decide +kernel)) (lineAt p88 49 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l90 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p90 : List LC := l90 :: p89
theorem d90 : IsLinDerivation F p90 :=
  IsLinDerivation.res (C := l35) (D := l89) d89
    (lineAt p89 54 (by decide +kernel)) (lineAt p89 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l91 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p91 : List LC := l91 :: p90
theorem d91 : IsLinDerivation F p91 :=
  IsLinDerivation.res (C := l88) (D := l90) d90
    (lineAt p90 2 (by decide +kernel)) (lineAt p90 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l92 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p92 : List LC := l92 :: p91
theorem d92 : IsLinDerivation F p92 :=
  IsLinDerivation.res (C := l91) (D := l86) d91
    (lineAt p91 0 (by decide +kernel)) (lineAt p91 5 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l93 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p93 : List LC := l93 :: p92
theorem d93 : IsLinDerivation F p93 :=
  IsLinDerivation.res (C := l81) (D := l92) d92
    (lineAt p92 11 (by decide +kernel)) (lineAt p92 0 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l94 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p94 : List LC := l94 :: p93
theorem d94 : IsLinDerivation F p94 :=
  IsLinDerivation.res (C := l93) (D := l76) d93
    (lineAt p93 0 (by decide +kernel)) (lineAt p93 17 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l95 : LC := {(({(2,1)} : Finset V),true)}
def p95 : List LC := l95 :: p94
theorem d95 : IsLinDerivation F p95 :=
  IsLinDerivation.res (C := l94) (D := l59) d94
    (lineAt p94 0 (by decide +kernel)) (lineAt p94 35 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l96 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p96 : List LC := l96 :: p95
theorem d96 : IsLinDerivation F p96 :=
  IsLinDerivation.res (C := l26) (D := l18) d95
    (lineAt p95 69 (by decide +kernel)) (lineAt p95 77 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l97 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p97 : List LC := l97 :: p96
theorem d97 : IsLinDerivation F p97 :=
  IsLinDerivation.res (C := l96) (D := l24) d96
    (lineAt p96 0 (by decide +kernel)) (lineAt p96 72 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l98 : LC := {(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p98 : List LC := l98 :: p97
theorem d98 : IsLinDerivation F p98 :=
  IsLinDerivation.res (C := l8) (D := l12) d97
    (lineAt p97 89 (by decide +kernel)) (lineAt p97 85 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l99 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p99 : List LC := l99 :: p98
theorem d99 : IsLinDerivation F p99 :=
  IsLinDerivation.res (C := l15) (D := l98) d98
    (lineAt p98 83 (by decide +kernel)) (lineAt p98 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l100 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p100 : List LC := l100 :: p99
theorem d100 : IsLinDerivation F p100 :=
  IsLinDerivation.res (C := l99) (D := l97) d99
    (lineAt p99 0 (by decide +kernel)) (lineAt p99 2 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l101 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p101 : List LC := l101 :: p100
theorem d101 : IsLinDerivation F p101 :=
  IsLinDerivation.res (C := l32) (D := l12) d100
    (lineAt p100 68 (by decide +kernel)) (lineAt p100 88 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l102 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p102 : List LC := l102 :: p101
theorem d102 : IsLinDerivation F p102 :=
  IsLinDerivation.res (C := l25) (D := l101) d101
    (lineAt p101 76 (by decide +kernel)) (lineAt p101 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l103 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p103 : List LC := l103 :: p102
theorem d103 : IsLinDerivation F p103 :=
  IsLinDerivation.res (C := l26) (D := l5) d102
    (lineAt p102 76 (by decide +kernel)) (lineAt p102 97 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l104 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p104 : List LC := l104 :: p103
theorem d104 : IsLinDerivation F p104 :=
  IsLinDerivation.res (C := l103) (D := l30) d103
    (lineAt p103 0 (by decide +kernel)) (lineAt p103 73 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l105 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p105 : List LC := l105 :: p104
theorem d105 : IsLinDerivation F p105 :=
  IsLinDerivation.res (C := l102) (D := l104) d104
    (lineAt p104 2 (by decide +kernel)) (lineAt p104 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l106 : LC := {(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p106 : List LC := l106 :: p105
theorem d106 : IsLinDerivation F p106 :=
  IsLinDerivation.res (C := l29) (D := l27) d105
    (lineAt p105 76 (by decide +kernel)) (lineAt p105 78 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l107 : LC := {(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p107 : List LC := l107 :: p106
theorem d107 : IsLinDerivation F p107 :=
  IsLinDerivation.res (C := l106) (D := l23) d106
    (lineAt p106 0 (by decide +kernel)) (lineAt p106 83 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l108 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p108 : List LC := l108 :: p107
theorem d108 : IsLinDerivation F p108 :=
  IsLinDerivation.res (C := l26) (D := l3) d107
    (lineAt p107 81 (by decide +kernel)) (lineAt p107 104 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l109 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p109 : List LC := l109 :: p108
theorem d109 : IsLinDerivation F p109 :=
  IsLinDerivation.res (C := l108) (D := l0) d108
    (lineAt p108 0 (by decide +kernel)) (lineAt p108 108 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l110 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p110 : List LC := l110 :: p109
theorem d110 : IsLinDerivation F p110 :=
  IsLinDerivation.res (C := l109) (D := l107) d109
    (lineAt p109 0 (by decide +kernel)) (lineAt p109 2 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l111 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p111 : List LC := l111 :: p110
theorem d111 : IsLinDerivation F p111 :=
  IsLinDerivation.res (C := l37) (D := l13) d110
    (lineAt p110 73 (by decide +kernel)) (lineAt p110 97 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l112 : LC := {(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p112 : List LC := l112 :: p111
theorem d112 : IsLinDerivation F p112 :=
  IsLinDerivation.res (C := l36) (D := l111) d111
    (lineAt p111 75 (by decide +kernel)) (lineAt p111 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l113 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p113 : List LC := l113 :: p112
theorem d113 : IsLinDerivation F p113 :=
  IsLinDerivation.res (C := l22) (D := l12) d112
    (lineAt p112 90 (by decide +kernel)) (lineAt p112 100 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l114 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p114 : List LC := l114 :: p113
theorem d114 : IsLinDerivation F p114 :=
  IsLinDerivation.res (C := l38) (D := l113) d113
    (lineAt p113 75 (by decide +kernel)) (lineAt p113 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l115 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p115 : List LC := l115 :: p114
theorem d115 : IsLinDerivation F p115 :=
  IsLinDerivation.res (C := l114) (D := l112) d114
    (lineAt p114 0 (by decide +kernel)) (lineAt p114 2 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l116 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p116 : List LC := l116 :: p115
theorem d116 : IsLinDerivation F p116 :=
  IsLinDerivation.res (C := l115) (D := l110) d115
    (lineAt p115 0 (by decide +kernel)) (lineAt p115 5 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l117 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p117 : List LC := l117 :: p116
theorem d117 : IsLinDerivation F p117 :=
  IsLinDerivation.res (C := l105) (D := l116) d116
    (lineAt p116 11 (by decide +kernel)) (lineAt p116 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l118 : LC := {(({(1,1)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p118 : List LC := l118 :: p117
theorem d118 : IsLinDerivation F p118 :=
  IsLinDerivation.res (C := l100) (D := l117) d117
    (lineAt p117 17 (by decide +kernel)) (lineAt p117 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l119 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p119 : List LC := l119 :: p118
theorem d119 : IsLinDerivation F p119 :=
  IsLinDerivation.res (C := l7) (D := l20) d118
    (lineAt p118 111 (by decide +kernel)) (lineAt p118 98 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l120 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p120 : List LC := l120 :: p119
theorem d120 : IsLinDerivation F p120 :=
  IsLinDerivation.res (C := l119) (D := l13) d119
    (lineAt p119 0 (by decide +kernel)) (lineAt p119 106 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l121 : LC := {(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p121 : List LC := l121 :: p120
theorem d121 : IsLinDerivation F p121 :=
  IsLinDerivation.res (C := l22) (D := l24) d120
    (lineAt p120 98 (by decide +kernel)) (lineAt p120 96 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l122 : LC := {(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p122 : List LC := l122 :: p121
theorem d122 : IsLinDerivation F p122 :=
  IsLinDerivation.res (C := l121) (D := l34) d121
    (lineAt p121 0 (by decide +kernel)) (lineAt p121 87 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l123 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p123 : List LC := l123 :: p122
theorem d123 : IsLinDerivation F p123 :=
  IsLinDerivation.res (C := l122) (D := l120) d122
    (lineAt p122 0 (by decide +kernel)) (lineAt p122 2 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l124 : LC := {(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p124 : List LC := l124 :: p123
theorem d124 : IsLinDerivation F p124 :=
  IsLinDerivation.res (C := l29) (D := l31) d123
    (lineAt p123 94 (by decide +kernel)) (lineAt p123 92 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l125 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p125 : List LC := l125 :: p124
theorem d125 : IsLinDerivation F p125 :=
  IsLinDerivation.res (C := l19) (D := l124) d124
    (lineAt p124 105 (by decide +kernel)) (lineAt p124 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l126 : LC := {(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p126 : List LC := l126 :: p125
theorem d126 : IsLinDerivation F p126 :=
  IsLinDerivation.res (C := l14) (D := l3) d125
    (lineAt p125 111 (by decide +kernel)) (lineAt p125 122 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l127 : LC := {(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p127 : List LC := l127 :: p126
theorem d127 : IsLinDerivation F p127 :=
  IsLinDerivation.res (C := l15) (D := l126) d126
    (lineAt p126 111 (by decide +kernel)) (lineAt p126 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l128 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p128 : List LC := l128 :: p127
theorem d128 : IsLinDerivation F p128 :=
  IsLinDerivation.res (C := l127) (D := l125) d127
    (lineAt p127 0 (by decide +kernel)) (lineAt p127 2 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l129 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p129 : List LC := l129 :: p128
theorem d129 : IsLinDerivation F p129 :=
  IsLinDerivation.res (C := l128) (D := l123) d128
    (lineAt p128 0 (by decide +kernel)) (lineAt p128 5 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l130 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p130 : List LC := l130 :: p129
theorem d130 : IsLinDerivation F p130 :=
  IsLinDerivation.res (C := l2) (D := l30) d129
    (lineAt p129 127 (by decide +kernel)) (lineAt p129 99 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l131 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p131 : List LC := l131 :: p130
theorem d131 : IsLinDerivation F p131 :=
  IsLinDerivation.res (C := l130) (D := l3) d130
    (lineAt p130 0 (by decide +kernel)) (lineAt p130 127 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l132 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p132 : List LC := l132 :: p131
theorem d132 : IsLinDerivation F p132 :=
  IsLinDerivation.res (C := l32) (D := l33) d131
    (lineAt p131 99 (by decide +kernel)) (lineAt p131 98 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l133 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p133 : List LC := l133 :: p132
theorem d133 : IsLinDerivation F p133 :=
  IsLinDerivation.res (C := l22) (D := l132) d132
    (lineAt p132 110 (by decide +kernel)) (lineAt p132 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l134 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p134 : List LC := l134 :: p133
theorem d134 : IsLinDerivation F p134 :=
  IsLinDerivation.res (C := l133) (D := l131) d133
    (lineAt p133 0 (by decide +kernel)) (lineAt p133 2 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l135 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p135 : List LC := l135 :: p134
theorem d135 : IsLinDerivation F p135 :=
  IsLinDerivation.res (C := l134) (D := l129) d134
    (lineAt p134 0 (by decide +kernel)) (lineAt p134 5 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l136 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p136 : List LC := l136 :: p135
theorem d136 : IsLinDerivation F p136 :=
  IsLinDerivation.res (C := l36) (D := l21) d135
    (lineAt p135 99 (by decide +kernel)) (lineAt p135 114 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l137 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p137 : List LC := l137 :: p136
theorem d137 : IsLinDerivation F p137 :=
  IsLinDerivation.res (C := l7) (D := l136) d136
    (lineAt p136 129 (by decide +kernel)) (lineAt p136 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l138 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p138 : List LC := l138 :: p137
theorem d138 : IsLinDerivation F p138 :=
  IsLinDerivation.res (C := l35) (D := l27) d137
    (lineAt p137 102 (by decide +kernel)) (lineAt p137 110 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l139 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p139 : List LC := l139 :: p138
theorem d139 : IsLinDerivation F p139 :=
  IsLinDerivation.res (C := l138) (D := l31) d138
    (lineAt p138 0 (by decide +kernel)) (lineAt p138 107 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l140 : LC := {(({(0,1)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p140 : List LC := l140 :: p139
theorem d140 : IsLinDerivation F p140 :=
  IsLinDerivation.res (C := l137) (D := l139) d139
    (lineAt p139 2 (by decide +kernel)) (lineAt p139 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l141 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p141 : List LC := l141 :: p140
theorem d141 : IsLinDerivation F p141 :=
  IsLinDerivation.res (C := l37) (D := l21) d140
    (lineAt p140 103 (by decide +kernel)) (lineAt p140 119 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l142 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p142 : List LC := l142 :: p141
theorem d142 : IsLinDerivation F p142 :=
  IsLinDerivation.res (C := l141) (D := l20) d141
    (lineAt p141 0 (by decide +kernel)) (lineAt p141 121 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l143 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p143 : List LC := l143 :: p142
theorem d143 : IsLinDerivation F p143 :=
  IsLinDerivation.res (C := l35) (D := l23) d142
    (lineAt p142 107 (by decide +kernel)) (lineAt p142 119 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l144 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p144 : List LC := l144 :: p143
theorem d144 : IsLinDerivation F p144 :=
  IsLinDerivation.res (C := l19) (D := l143) d143
    (lineAt p143 124 (by decide +kernel)) (lineAt p143 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l145 : LC := {(({(1,1)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p145 : List LC := l145 :: p144
theorem d145 : IsLinDerivation F p145 :=
  IsLinDerivation.res (C := l144) (D := l142) d144
    (lineAt p144 0 (by decide +kernel)) (lineAt p144 2 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l146 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p146 : List LC := l146 :: p145
theorem d146 : IsLinDerivation F p146 :=
  IsLinDerivation.res (C := l15) (D := l28) d145
    (lineAt p145 130 (by decide +kernel)) (lineAt p145 117 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l147 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p147 : List LC := l147 :: p146
theorem d147 : IsLinDerivation F p147 :=
  IsLinDerivation.res (C := l32) (D := l146) d146
    (lineAt p146 114 (by decide +kernel)) (lineAt p146 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l148 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p148 : List LC := l148 :: p147
theorem d148 : IsLinDerivation F p148 :=
  IsLinDerivation.res (C := l10) (D := l30) d147
    (lineAt p147 137 (by decide +kernel)) (lineAt p147 117 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l149 : LC := {(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p149 : List LC := l149 :: p148
theorem d149 : IsLinDerivation F p149 :=
  IsLinDerivation.res (C := l148) (D := l24) d148
    (lineAt p148 0 (by decide +kernel)) (lineAt p148 124 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l150 : LC := {(({(0,1)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p150 : List LC := l150 :: p149
theorem d150 : IsLinDerivation F p150 :=
  IsLinDerivation.res (C := l147) (D := l149) d149
    (lineAt p149 2 (by decide +kernel)) (lineAt p149 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l151 : LC := {(({(0,1)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p151 : List LC := l151 :: p150
theorem d151 : IsLinDerivation F p151 :=
  IsLinDerivation.res (C := l150) (D := l145) d150
    (lineAt p150 0 (by decide +kernel)) (lineAt p150 5 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l152 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p152 : List LC := l152 :: p151
theorem d152 : IsLinDerivation F p152 :=
  IsLinDerivation.res (C := l151) (D := l140) d151
    (lineAt p151 0 (by decide +kernel)) (lineAt p151 11 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l153 : LC := {(({(1,1)} : Finset V),true),(({(2,1)} : Finset V),false)}
def p153 : List LC := l153 :: p152
theorem d153 : IsLinDerivation F p153 :=
  IsLinDerivation.res (C := l135) (D := l152) d152
    (lineAt p152 17 (by decide +kernel)) (lineAt p152 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l154 : LC := {(({(2,1)} : Finset V),false)}
def p154 : List LC := l154 :: p153
theorem d154 : IsLinDerivation F p154 :=
  IsLinDerivation.res (C := l118) (D := l153) d153
    (lineAt p153 35 (by decide +kernel)) (lineAt p153 0 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l155 : LC := ∅
def p155 : List LC := l155 :: p154
theorem d155 : IsLinDerivation F p155 :=
  IsLinDerivation.res (C := l154) (D := l95) d154
    (lineAt p154 0 (by decide +kernel)) (lineAt p154 59 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_pcx_137

open PEqualNP.Outside.L_pcx_137 in
theorem PEqualNP.Outside.L_pcx_137 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 158 :=
  ⟨p155, ⟨d155, List.Mem.head _⟩, by decide +kernel⟩
