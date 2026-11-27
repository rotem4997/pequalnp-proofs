import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19034_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def mask32 : ℕ := 4294967295

def mask1024 : ℕ := 2 ^ 1024 - 1

def colPat : ℕ := 41855804977958881238216860293671333616475814839523861211015363775367857790754367812411590743534994955327154331653972084008334635948471552329445020986934924815945052132199177846429263578652254701150892687317891618273230805205109921907778604060552511649183701335864607145965996450848344889395800702977

def rowTbl : List ℕ :=
  [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402,
   0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e,
   0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082,
   0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

def target1024 : ℕ := 11894091776269682970387250588567856694786699436473888321862965324626965826759294648384072579756651424259062913826774901955139974033463014694680370493143296229643302249798350668386596825192617925157254869749015872192539970226916805517455596984424962209623826131092607951746011038347394925554503133516711884147

def cktGates : List Gate := [
  ⟨GateOp.or, [24, 19]⟩,
  ⟨GateOp.or, [0, 4]⟩,
  ⟨GateOp.or, [65, 14]⟩,
  ⟨GateOp.or, [10, 6]⟩,
  ⟨GateOp.or, [66, 67]⟩,
  ⟨GateOp.or, [13, 8]⟩,
  ⟨GateOp.or, [1, 69]⟩,
  ⟨GateOp.or, [68, 70]⟩,
  ⟨GateOp.or, [64, 71]⟩,
  ⟨GateOp.or, [3, 2]⟩,
  ⟨GateOp.or, [73, 23]⟩,
  ⟨GateOp.or, [11, 74]⟩,
  ⟨GateOp.or, [75, 26]⟩,
  ⟨GateOp.or, [22, 7]⟩,
  ⟨GateOp.or, [25, 0]⟩,
  ⟨GateOp.or, [77, 78]⟩,
  ⟨GateOp.or, [10, 79]⟩,
  ⟨GateOp.or, [9, 15]⟩,
  ⟨GateOp.or, [81, 28]⟩,
  ⟨GateOp.or, [82, 65]⟩,
  ⟨GateOp.or, [80, 83]⟩,
  ⟨GateOp.or, [76, 84]⟩,
  ⟨GateOp.or, [21, 25]⟩,
  ⟨GateOp.or, [86, 14]⟩,
  ⟨GateOp.or, [6, 87]⟩,
  ⟨GateOp.or, [16, 8]⟩,
  ⟨GateOp.or, [26, 22]⟩,
  ⟨GateOp.or, [89, 90]⟩,
  ⟨GateOp.or, [28, 86]⟩,
  ⟨GateOp.or, [92, 1]⟩,
  ⟨GateOp.or, [91, 93]⟩,
  ⟨GateOp.or, [70, 15]⟩,
  ⟨GateOp.or, [94, 95]⟩,
  ⟨GateOp.or, [88, 96]⟩,
  ⟨GateOp.or, [4, 3]⟩,
  ⟨GateOp.or, [26, 98]⟩,
  ⟨GateOp.or, [24, 99]⟩,
  ⟨GateOp.or, [100, 27]⟩,
  ⟨GateOp.or, [101, 21]⟩,
  ⟨GateOp.or, [93, 9]⟩,
  ⟨GateOp.or, [102, 103]⟩,
  ⟨GateOp.or, [30, 11]⟩,
  ⟨GateOp.or, [28, 24]⟩,
  ⟨GateOp.or, [105, 106]⟩,
  ⟨GateOp.or, [107, 17]⟩,
  ⟨GateOp.or, [108, 81]⟩,
  ⟨GateOp.or, [104, 109]⟩,
  ⟨GateOp.or, [105, 12]⟩,
  ⟨GateOp.or, [31, 19]⟩,
  ⟨GateOp.or, [17, 112]⟩,
  ⟨GateOp.or, [113, 0]⟩,
  ⟨GateOp.or, [114, 13]⟩,
  ⟨GateOp.or, [115, 66]⟩,
  ⟨GateOp.or, [111, 116]⟩,
  ⟨GateOp.or, [20, 5]⟩,
  ⟨GateOp.or, [104, 118]⟩,
  ⟨GateOp.or, [117, 119]⟩,
  ⟨GateOp.or, [68, 89]⟩,
  ⟨GateOp.or, [102, 121]⟩,
  ⟨GateOp.or, [27, 18]⟩,
  ⟨GateOp.or, [2, 123]⟩,
  ⟨GateOp.or, [115, 124]⟩,
  ⟨GateOp.or, [23, 13]⟩,
  ⟨GateOp.or, [126, 2]⟩,
  ⟨GateOp.or, [127, 24]⟩,
  ⟨GateOp.or, [128, 94]⟩,
  ⟨GateOp.or, [106, 118]⟩,
  ⟨GateOp.or, [130, 27]⟩,
  ⟨GateOp.or, [16, 29]⟩,
  ⟨GateOp.or, [131, 132]⟩,
  ⟨GateOp.or, [4, 10]⟩,
  ⟨GateOp.or, [133, 134]⟩,
  ⟨GateOp.or, [129, 135]⟩,
  ⟨GateOp.or, [18, 67]⟩,
  ⟨GateOp.or, [81, 137]⟩,
  ⟨GateOp.or, [138, 78]⟩,
  ⟨GateOp.or, [87, 64]⟩,
  ⟨GateOp.or, [139, 140]⟩,
  ⟨GateOp.or, [29, 18]⟩,
  ⟨GateOp.or, [142, 9]⟩,
  ⟨GateOp.or, [143, 134]⟩,
  ⟨GateOp.or, [1, 64]⟩,
  ⟨GateOp.or, [130, 145]⟩,
  ⟨GateOp.or, [146, 87]⟩,
  ⟨GateOp.or, [144, 147]⟩,
  ⟨GateOp.or, [13, 148]⟩,
  ⟨GateOp.or, [108, 88]⟩,
  ⟨GateOp.or, [79, 143]⟩,
  ⟨GateOp.or, [16, 151]⟩,
  ⟨GateOp.or, [150, 152]⟩,
  ⟨GateOp.or, [138, 3]⟩,
  ⟨GateOp.or, [143, 2]⟩,
  ⟨GateOp.or, [154, 155]⟩,
  ⟨GateOp.or, [156, 70]⟩,
  ⟨GateOp.or, [107, 157]⟩,
  ⟨GateOp.or, [67, 86]⟩,
  ⟨GateOp.or, [114, 159]⟩,
  ⟨GateOp.or, [160, 77]⟩,
  ⟨GateOp.or, [139, 12]⟩,
  ⟨GateOp.or, [162, 8]⟩,
  ⟨GateOp.or, [146, 163]⟩,
  ⟨GateOp.or, [160, 81]⟩,
  ⟨GateOp.and, [141, 165]⟩,
  ⟨GateOp.or, [166, 73]⟩,
  ⟨GateOp.or, [69, 137]⟩,
  ⟨GateOp.or, [111, 168]⟩,
  ⟨GateOp.or, [169, 28]⟩,
  ⟨GateOp.or, [134, 124]⟩,
  ⟨GateOp.or, [86, 171]⟩,
  ⟨GateOp.or, [170, 172]⟩,
  ⟨GateOp.or, [128, 26]⟩,
  ⟨GateOp.or, [173, 174]⟩,
  ⟨GateOp.or, [95, 128]⟩,
  ⟨GateOp.or, [172, 176]⟩,
  ⟨GateOp.or, [126, 15]⟩,
  ⟨GateOp.or, [142, 178]⟩,
  ⟨GateOp.or, [20, 179]⟩,
  ⟨GateOp.or, [80, 180]⟩,
  ⟨GateOp.or, [89, 98]⟩,
  ⟨GateOp.or, [118, 0]⟩,
  ⟨GateOp.or, [182, 183]⟩,
  ⟨GateOp.or, [103, 184]⟩,
  ⟨GateOp.or, [100, 111]⟩,
  ⟨GateOp.or, [165, 89]⟩,
  ⟨GateOp.or, [186, 187]⟩,
  ⟨GateOp.or, [91, 116]⟩,
  ⟨GateOp.or, [173, 154]⟩,
  ⟨GateOp.or, [31, 190]⟩,
  ⟨GateOp.or, [133, 183]⟩,
  ⟨GateOp.or, [192, 113]⟩,
  ⟨GateOp.or, [88, 193]⟩,
  ⟨GateOp.or, [99, 1]⟩,
  ⟨GateOp.or, [83, 132]⟩,
  ⟨GateOp.or, [156, 76]⟩,
  ⟨GateOp.or, [95, 182]⟩,
  ⟨GateOp.or, [131, 198]⟩,
  ⟨GateOp.or, [162, 66]⟩,
  ⟨GateOp.or, [23, 31]⟩,
  ⟨GateOp.or, [195, 201]⟩,
  ⟨GateOp.or, [200, 202]⟩,
  ⟨GateOp.or, [170, 192]⟩,
  ⟨GateOp.or, [129, 139]⟩,
  ⟨GateOp.or, [155, 183]⟩,
  ⟨GateOp.and, [32, 72]⟩,
  ⟨GateOp.and, [33, 85]⟩,
  ⟨GateOp.and, [34, 97]⟩,
  ⟨GateOp.and, [35, 110]⟩,
  ⟨GateOp.and, [36, 120]⟩,
  ⟨GateOp.and, [37, 122]⟩,
  ⟨GateOp.and, [38, 125]⟩,
  ⟨GateOp.and, [39, 136]⟩,
  ⟨GateOp.and, [40, 141]⟩,
  ⟨GateOp.and, [41, 149]⟩,
  ⟨GateOp.and, [42, 153]⟩,
  ⟨GateOp.and, [43, 158]⟩,
  ⟨GateOp.and, [44, 161]⟩,
  ⟨GateOp.and, [45, 164]⟩,
  ⟨GateOp.and, [46, 167]⟩,
  ⟨GateOp.and, [47, 175]⟩,
  ⟨GateOp.and, [48, 177]⟩,
  ⟨GateOp.and, [49, 155]⟩,
  ⟨GateOp.and, [50, 181]⟩,
  ⟨GateOp.and, [51, 185]⟩,
  ⟨GateOp.and, [52, 188]⟩,
  ⟨GateOp.and, [53, 189]⟩,
  ⟨GateOp.and, [54, 191]⟩,
  ⟨GateOp.and, [55, 194]⟩,
  ⟨GateOp.and, [56, 195]⟩,
  ⟨GateOp.and, [57, 196]⟩,
  ⟨GateOp.and, [58, 197]⟩,
  ⟨GateOp.and, [59, 199]⟩,
  ⟨GateOp.and, [60, 203]⟩,
  ⟨GateOp.and, [61, 204]⟩,
  ⟨GateOp.and, [62, 205]⟩,
  ⟨GateOp.and, [63, 206]⟩,
  ⟨GateOp.or, [207, 208]⟩,
  ⟨GateOp.or, [239, 209]⟩,
  ⟨GateOp.or, [240, 210]⟩,
  ⟨GateOp.or, [241, 211]⟩,
  ⟨GateOp.or, [242, 212]⟩,
  ⟨GateOp.or, [243, 213]⟩,
  ⟨GateOp.or, [244, 214]⟩,
  ⟨GateOp.or, [245, 215]⟩,
  ⟨GateOp.or, [246, 216]⟩,
  ⟨GateOp.or, [247, 217]⟩,
  ⟨GateOp.or, [248, 218]⟩,
  ⟨GateOp.or, [249, 219]⟩,
  ⟨GateOp.or, [250, 220]⟩,
  ⟨GateOp.or, [251, 221]⟩,
  ⟨GateOp.or, [252, 222]⟩,
  ⟨GateOp.or, [253, 223]⟩,
  ⟨GateOp.or, [254, 224]⟩,
  ⟨GateOp.or, [255, 225]⟩,
  ⟨GateOp.or, [256, 226]⟩,
  ⟨GateOp.or, [257, 227]⟩,
  ⟨GateOp.or, [258, 228]⟩,
  ⟨GateOp.or, [259, 229]⟩,
  ⟨GateOp.or, [260, 230]⟩,
  ⟨GateOp.or, [261, 231]⟩,
  ⟨GateOp.or, [262, 232]⟩,
  ⟨GateOp.or, [263, 233]⟩,
  ⟨GateOp.or, [264, 234]⟩,
  ⟨GateOp.or, [265, 235]⟩,
  ⟨GateOp.or, [266, 236]⟩,
  ⟨GateOp.or, [267, 237]⟩,
  ⟨GateOp.or, [268, 238]⟩
]

def ckt : Circuit := ⟨cktGates, 269⟩

def getRev (rw : List ℕ) (n i : ℕ) : ℕ :=
  if i < n then rw.getD (n - 1 - i) 0 else 0

def stepRev (st : ℕ × List ℕ) (g : Gate) : ℕ × List ℕ :=
  let n := st.1
  let rw := st.2
  let v :=
    match g.op, g.inputs with
    | GateOp.and, [a, b] => (getRev rw n a) &&& (getRev rw n b)
    | GateOp.or, [a, b] => (getRev rw n a) ||| (getRev rw n b)
    | GateOp.not, [a] => mask1024 ^^^ (getRev rw n a)
    | _, _ => 0
  (n + 1, v :: rw)

def initList : List ℕ :=
  List.ofFn (fun i : Fin 32 => mask32 <<< (32 * i.val)) ++
  List.ofFn (fun j : Fin 32 => colPat <<< j.val)

def initRev : List ℕ := initList.reverse

def goodGate (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | GateOp.not, [_] => true
  | _, _ => false

theorem mask1024_bit (k : ℕ) (hk : k < 1024) : mask1024.testBit k = true := by
  have h : mask1024 = 2 ^ 1024 - 1 := rfl
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

theorem mask32_bit (k : ℕ) (hk : k < 32) : mask32.testBit k = true := by
  have h : mask32 = 2 ^ 32 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

theorem mask32_bit_ge (k : ℕ) (hk : 32 ≤ k) : mask32.testBit k = false := by
  have h : mask32 = 2 ^ 32 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

theorem colPat_bit (u : Fin 32) (v : Fin 32) (j : Fin 32) :
    (colPat <<< j.val).testBit (32 * u.val + v.val) = decide (j = v) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : j.val ≤ 32 * u.val + v.val
  · simp only [decide_eq_true hle, Bool.true_and]
    have hmod : (32 * u.val + v.val - j.val) % 32 = (32 + v.val - j.val) % 32 := by omega
    have hlt : 32 * u.val + v.val - j.val < 1024 := by omega
    have hcp : ∀ k : Fin 1024, colPat.testBit k.val = decide (k.val % 32 = 0) := by decide +kernel
    rw [hcp ⟨32 * u.val + v.val - j.val, hlt⟩]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hm
      apply Fin.ext
      omega
    · rintro rfl
      omega
  · simp only [decide_eq_false hle, Bool.false_and]
    symm
    apply decide_eq_false
    intro heq
    subst heq
    omega

theorem rowMask_bit (i u v : Fin 32) :
    (mask32 <<< (32 * i.val)).testBit (32 * u.val + v.val) = decide (i = u) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : 32 * i.val ≤ 32 * u.val + v.val
  · simp only [decide_eq_true hle, Bool.true_and]
    by_cases heq : i = u
    · subst heq
      have h1 : 32 * i.val + v.val - 32 * i.val = v.val := by omega
      rw [h1, mask32_bit v.val v.isLt]
      simp
    · have hlt : i.val < u.val := by
        have hne : i.val ≠ u.val := fun h => heq (Fin.ext h)
        omega
      have hge : 32 ≤ 32 * u.val + v.val - 32 * i.val := by omega
      rw [mask32_bit_ge _ hge]
      simp [heq]
  · simp only [decide_eq_false hle, Bool.false_and]
    symm
    apply decide_eq_false
    intro heq
    subst heq
    omega

theorem initList_len : initList.length = 64 := by simp [initList]

theorem oneEach_len (u v : Fin 32) : (oneEach u v).length = 64 := by simp [oneEach]

theorem getRev_reverse (l : List ℕ) (i : ℕ) :
    getRev l.reverse l.length i = l.getD i 0 := by
  unfold getRev
  by_cases hi : i < l.length
  · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD]
    have h1 : l.length - 1 - i < l.reverse.length := by simp; omega
    rw [List.getElem?_eq_getElem h1, List.getElem_reverse, List.getElem?_eq_getElem hi]
    have hidx : l.length - 1 - (l.length - 1 - i) = i := by omega
    simp [hidx]
  · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem initRev_bit (u v : Fin 32) (i : ℕ) :
    (getRev initRev 64 i).testBit (32 * u.val + v.val) = (oneEach u v).getD i false := by
  have h1 : getRev initRev 64 i = initList.getD i 0 := by
    rw [← initList_len]
    exact getRev_reverse initList i
  rw [h1]
  by_cases hi : i < 64
  · by_cases h32 : i < 32
    · have hl1 : (List.ofFn (fun k : Fin 32 => mask32 <<< (32 * k.val))).length = 32 := by simp
      have hl2 : (List.ofFn (fun k : Fin 32 => decide (k = u))).length = 32 := by simp
      simp only [initList, oneEach, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [List.getElem?_ofFn, h32, dite_true, Option.getD_some]
      exact rowMask_bit ⟨i, h32⟩ u v
    · have hj : i - 32 < 32 := by omega
      have hl1 : (List.ofFn (fun k : Fin 32 => mask32 <<< (32 * k.val))).length = 32 := by simp
      have hl2 : (List.ofFn (fun k : Fin 32 => decide (k = u))).length = 32 := by simp
      simp only [initList, oneEach, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp only [hl1, hl2, List.getElem?_ofFn, hj, dite_true, Option.getD_some]
      exact colPat_bit u v ⟨i - 32, hj⟩
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [initList_len]; omega), List.getElem?_eq_none (by rw [oneEach_len]; omega)]
    simp

theorem getRev_cons (v : ℕ) (rw : List ℕ) (n i : ℕ) :
    getRev (v :: rw) (n + 1) i = if i = n then v else getRev rw n i := by
  unfold getRev
  by_cases heq : i = n
  · subst heq
    simp
  · by_cases hi : i < n
    · have h1 : i < n + 1 := by omega
      have h2 : n - i = (n - 1 - i) + 1 := by omega
      simp only [heq, hi, h1, ↓reduceIte, Nat.add_sub_cancel]
      rw [h2]
      rfl
    · have h1 : ¬(i < n + 1) := by omega
      simp [heq, hi, h1]

theorem step_sim (u v : Fin 32) (st : ℕ × List ℕ) (wb : List Bool) (g : Gate)
    (hlen : st.1 = wb.length)
    (hsim : ∀ i, (getRev st.2 st.1 i).testBit (32 * u.val + v.val) = wb.getD i false)
    (hg : goodGate g = true) :
    (stepRev st g).1 = (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).length ∧
    ∀ i, (getRev (stepRev st g).2 (stepRev st g).1 i).testBit (32 * u.val + v.val) =
      (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).getD i false := by
  have hk : 32 * u.val + v.val < 1024 := by omega
  constructor
  · simp [stepRev, hlen]
  · intro i
    simp only [stepRev]
    rw [getRev_cons]
    by_cases heq : i = st.1
    · subst heq
      simp only [↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      rcases g with ⟨op, ins⟩
      cases op with
      | and =>
        rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp [goodGate] at hg
        · simp [goodGate] at hg
        · simp only [GateOp.eval, List.map, List.all, id, Bool.and_true, Nat.testBit_and]
          rw [← hlen, hsim a, hsim b]
          simp [List.getD_eq_getElem?_getD]
        · simp [goodGate] at hg
      | or =>
        rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp [goodGate] at hg
        · simp [goodGate] at hg
        · simp only [GateOp.eval, List.map, List.any, id, Bool.or_false, Nat.testBit_or]
          rw [← hlen, hsim a, hsim b]
          simp [List.getD_eq_getElem?_getD]
        · simp [goodGate] at hg
      | not =>
        rcases ins with _ | ⟨a, _ | _⟩
        · simp [goodGate] at hg
        · simp only [GateOp.eval, List.map, List.headD, Nat.testBit_xor, mask1024_bit _ hk, Bool.true_bne]
          rw [← hlen, hsim a]
          simp [List.getD_eq_getElem?_getD]
        · simp [goodGate] at hg
      | mod m => simp [goodGate] at hg
      | maj => simp [goodGate] at hg
    · simp only [heq, ↓reduceIte]
      by_cases hlt : i < wb.length
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hlt]
        simpa [List.getD_eq_getElem?_getD] using hsim i
      · have hge : ¬(i < st.1) := by omega
        have hgt : wb.length + 1 ≤ i := by omega
        simp only [getRev, hge, ↓reduceIte, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        simp

theorem foldl_sim (u v : Fin 32) (gs : List Gate) (st : ℕ × List ℕ) (wb : List Bool)
    (hlen : st.1 = wb.length)
    (hsim : ∀ i, (getRev st.2 st.1 i).testBit (32 * u.val + v.val) = wb.getD i false)
    (hgs : ∀ g ∈ gs, goodGate g = true) :
    ∀ i, (getRev (gs.foldl stepRev st).2 (gs.foldl stepRev st).1 i).testBit (32 * u.val + v.val) =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb).getD i false := by
  induction gs generalizing st wb with
  | nil => exact hsim
  | cons g gs ih =>
    have h1 := step_sim u v st wb g hlen hsim (hgs g (List.mem_cons_self ..))
    exact ih (stepRev st g) _ h1.1 h1.2 (fun q hq => hgs q (List.mem_cons_of_mem _ hq))

theorem good_imp_fanin (g : Gate) (hg : goodGate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [goodGate] at hg ⊢
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [goodGate] at hg ⊢
  | not =>
    rcases ins with _ | ⟨a, _ | _⟩ <;> simp [goodGate] at hg ⊢
  | mod m => simp [goodGate] at hg
  | maj => simp [goodGate] at hg

theorem hgood : cktGates.all goodGate = true := by decide +kernel

theorem hfan : FanInTwo ckt := by
  intro g hg
  exact good_imp_fanin g (List.all_eq_true.mp hgood g hg)

theorem hsz : ckt.size ≤ 207 := by decide +kernel

theorem hval :
    let st := cktGates.foldl stepRev (64, initRev)
    getRev st.2 st.1 269 = target1024 := by
  decide +kernel

theorem htarget_bit (u v : Fin 32) :
    target1024.testBit (32 * u.val + v.val) = (rowTbl.getD u.val 0).testBit v.val := by
  have hslice : ∀ u : Fin 32, (target1024 >>> (32 * u.val)) &&& mask32 = rowTbl.getD u.val 0 := by
    decide +kernel
  rw [← hslice u, Nat.testBit_and, mask32_bit v.val v.isLt, Bool.and_true, Nat.testBit_shiftRight]

theorem hrep : Represents (fun u v : Fin 32 => (rowTbl.getD u.val 0).testBit v.val) ckt := by
  intro u v
  have hgs : ∀ g ∈ cktGates, goodGate g = true := List.all_eq_true.mp hgood
  have hf := foldl_sim u v cktGates (64, initRev) (oneEach u v)
    (by rw [oneEach_len]) (initRev_bit u v) hgs 269
  have hv : getRev (cktGates.foldl stepRev (64, initRev)).2 (cktGates.foldl stepRev (64, initRev)).1 269 = target1024 := hval
  rw [hv, htarget_bit u v] at hf
  exact hf.symm

end PEqualNP.Outside.L_meta_19034_aux

theorem PEqualNP.Outside.L_meta_19034 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 207 ∧ PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_19034_aux.ckt, PEqualNP.Outside.L_meta_19034_aux.hfan,
   PEqualNP.Outside.L_meta_19034_aux.hsz, PEqualNP.Outside.L_meta_19034_aux.hrep⟩
