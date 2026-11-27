import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17145

-- The packed gate evaluator is adapted from GravityLizard, L-meta-17106.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

theorem hcsWitnessEval {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r = f (fun j : Fin n => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits := hcsFoldBits raw ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

theorem hcsWitness {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Nat) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hsz : C.size ≤ s)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  exact ⟨C, hfan, hsz, hcsWitnessEval raw goal C f hfan hRaw hGoal hEval⟩


def gateOf (t : ℕ × ℕ × ℕ) : Gate :=
  match t.1 with
  | 0 => ⟨.and, [t.2.1, t.2.2]⟩
  | 1 => ⟨.or, [t.2.1, t.2.2]⟩
  | _ => ⟨.not, [t.2.1]⟩

def instructions : List (ℕ × ℕ × ℕ) := [
    (2, 0, 0),
    (2, 1, 1),
    (0, 10, 11),
    (2, 2, 2),
    (2, 3, 3),
    (2, 4, 4),
    (0, 14, 15),
    (0, 13, 16),
    (0, 12, 17),
    (0, 0, 11),
    (0, 17, 19),
    (0, 1, 10),
    (0, 17, 21),
    (0, 0, 1),
    (0, 17, 23),
    (0, 2, 16),
    (0, 12, 25),
    (0, 19, 25),
    (0, 21, 25),
    (0, 23, 25),
    (0, 3, 15),
    (0, 13, 30),
    (0, 12, 31),
    (0, 19, 31),
    (0, 21, 31),
    (0, 23, 31),
    (0, 2, 30),
    (0, 12, 36),
    (0, 19, 36),
    (0, 21, 36),
    (0, 23, 36),
    (0, 4, 14),
    (0, 13, 41),
    (0, 12, 42),
    (0, 19, 42),
    (0, 21, 42),
    (0, 23, 42),
    (0, 2, 41),
    (0, 12, 47),
    (0, 19, 47),
    (0, 21, 47),
    (0, 23, 47),
    (0, 3, 4),
    (0, 13, 52),
    (0, 12, 53),
    (0, 19, 53),
    (0, 21, 53),
    (0, 23, 53),
    (0, 2, 52),
    (0, 12, 58),
    (0, 19, 58),
    (0, 21, 58),
    (0, 23, 58),
    (1, 49, 55),
    (1, 28, 34),
    (1, 18, 33),
    (1, 54, 59),
    (1, 32, 38),
    (1, 24, 26),
    (1, 40, 45),
    (1, 27, 48),
    (1, 35, 61),
    (1, 63, 66),
    (1, 20, 67),
    (1, 56, 68),
    (1, 64, 69),
    (1, 39, 46),
    (1, 22, 51),
    (1, 44, 62),
    (1, 57, 71),
    (1, 60, 70),
    (1, 43, 50),
    (1, 37, 65),
    (1, 18, 64),
    (1, 56, 81),
    (1, 20, 74),
    (1, 45, 80),
    (1, 73, 77),
    (1, 46, 78),
    (1, 26, 76),
    (1, 43, 57),
    (1, 40, 59),
    (1, 37, 79),
    (1, 54, 63),
    (1, 29, 50),
    (1, 67, 92),
    (1, 33, 60),
    (1, 76, 78),
    (1, 44, 72),
    (1, 22, 24),
    (1, 82, 85),
    (1, 63, 68),
    (1, 18, 38),
    (1, 26, 72),
    (1, 62, 75),
    (1, 20, 32),
    (1, 65, 75),
    (1, 56, 77),
    (1, 43, 65),
    (1, 34, 94),
    (1, 57, 87),
    (1, 32, 74),
    (1, 38, 72),
    (1, 66, 73),
    (1, 40, 64),
    (1, 51, 55),
    (1, 75, 96),
    (1, 28, 39),
    (1, 70, 105),
    (1, 59, 101),
    (1, 22, 45),
    (1, 34, 110),
    (1, 54, 83),
    (1, 90, 122),
    (1, 88, 111),
    (1, 35, 65),
    (1, 67, 84),
    (1, 66, 86),
    (1, 40, 79),
    (1, 72, 87),
    (1, 55, 109),
    (1, 70, 79),
    (1, 97, 100),
    (1, 26, 69),
    (1, 71, 117),
    (1, 91, 130),
    (1, 57, 102),
    (1, 46, 75),
    (1, 74, 77),
    (1, 43, 82),
    (1, 46, 99),
    (1, 34, 112),
    (1, 39, 111),
    (1, 131, 132),
    (1, 39, 115),
    (1, 20, 33),
    (1, 90, 113),
    (1, 98, 134),
    (1, 60, 102),
    (1, 83, 94),
    (1, 26, 60),
    (1, 29, 60),
    (1, 125, 138),
    (1, 43, 95),
    (1, 45, 147),
    (1, 22, 65),
    (1, 33, 95),
    (1, 106, 129),
    (1, 84, 157),
    (1, 104, 144),
    (1, 71, 116),
    (1, 108, 119),
    (1, 68, 70),
    (1, 65, 154),
    (1, 93, 106),
    (1, 73, 122),
    (1, 100, 159),
    (1, 114, 139),
    (1, 86, 155),
    (1, 35, 107),
    (1, 85, 98),
    (1, 49, 123),
    (1, 141, 145),
    (1, 83, 153),
    (1, 88, 120),
    (1, 64, 95),
    (1, 121, 133),
    (1, 48, 69),
    (1, 63, 88),
    (1, 18, 78),
    (1, 118, 161),
    (1, 66, 82),
    (1, 33, 128),
    (1, 135, 152),
    (1, 63, 140),
    (1, 84, 117),
    (1, 55, 181),
    (1, 86, 89),
    (1, 99, 160),
    (1, 22, 156),
    (1, 40, 162),
    (1, 65, 184),
    (1, 80, 97),
    (1, 24, 169),
    (1, 170, 182),
    (1, 45, 175),
    (1, 18, 192),
    (1, 71, 124),
    (1, 113, 188),
    (1, 80, 103),
    (1, 115, 177),
    (1, 116, 193),
    (1, 72, 196),
    (1, 104, 119),
    (1, 73, 91),
    (1, 109, 148),
    (1, 84, 121),
    (1, 63, 185),
    (1, 28, 202),
    (1, 96, 120),
    (1, 93, 197),
    (1, 91, 108),
    (1, 126, 179),
    (1, 93, 176),
    (1, 189, 203),
    (1, 204, 207),
    (1, 81, 151),
    (1, 199, 206),
    (1, 76, 164),
    (1, 163, 216),
    (1, 142, 171),
    (1, 103, 107),
    (1, 136, 174),
    (1, 90, 208),
    (1, 114, 191),
    (1, 89, 212),
    (1, 172, 187),
    (1, 127, 173),
    (1, 146, 190),
    (1, 150, 211),
    (1, 118, 137),
    (1, 89, 165),
    (1, 195, 221),
    (1, 186, 230),
    (1, 112, 143),
    (1, 200, 205),
    (1, 149, 178),
    (1, 167, 210),
    (2, 5, 5),
    (0, 231, 238),
    (0, 5, 183),
    (1, 239, 240),
    (0, 215, 238),
    (0, 5, 194),
    (1, 242, 243),
    (0, 234, 238),
    (0, 5, 220),
    (1, 245, 246),
    (0, 222, 238),
    (0, 5, 217),
    (1, 248, 249),
    (0, 218, 238),
    (0, 5, 226),
    (1, 251, 252),
    (0, 219, 238),
    (0, 5, 198),
    (1, 254, 255),
    (0, 236, 238),
    (0, 5, 233),
    (1, 257, 258),
    (0, 224, 238),
    (0, 5, 232),
    (1, 260, 261),
    (0, 213, 238),
    (0, 5, 209),
    (1, 263, 264),
    (0, 235, 238),
    (0, 5, 180),
    (1, 266, 267),
    (0, 237, 238),
    (0, 5, 225),
    (1, 269, 270),
    (0, 214, 238),
    (0, 5, 223),
    (1, 272, 273),
    (0, 85, 238),
    (0, 5, 229),
    (1, 275, 276),
    (0, 201, 238),
    (0, 5, 228),
    (1, 278, 279),
    (0, 166, 238),
    (0, 5, 227),
    (1, 281, 282),
    (0, 158, 238),
    (0, 5, 168),
    (1, 284, 285),
    (2, 6, 6),
    (0, 241, 287),
    (0, 6, 244),
    (1, 288, 289),
    (0, 247, 287),
    (0, 6, 250),
    (1, 291, 292),
    (0, 253, 287),
    (0, 6, 256),
    (1, 294, 295),
    (0, 259, 287),
    (0, 6, 262),
    (1, 297, 298),
    (0, 265, 287),
    (0, 6, 268),
    (1, 300, 301),
    (0, 271, 287),
    (0, 6, 274),
    (1, 303, 304),
    (0, 277, 287),
    (0, 6, 280),
    (1, 306, 307),
    (0, 283, 287),
    (0, 6, 286),
    (1, 309, 310),
    (2, 7, 7),
    (0, 290, 312),
    (0, 7, 293),
    (1, 313, 314),
    (0, 296, 312),
    (0, 7, 299),
    (1, 316, 317),
    (0, 302, 312),
    (0, 7, 305),
    (1, 319, 320),
    (0, 308, 312),
    (0, 7, 311),
    (1, 322, 323),
    (2, 8, 8),
    (0, 315, 325),
    (0, 8, 318),
    (1, 326, 327),
    (0, 321, 325),
    (0, 8, 324),
    (1, 329, 330),
    (2, 9, 9),
    (0, 328, 332),
    (0, 9, 331),
    (1, 333, 334)]

def witness : Circuit := ⟨instructions.map gateOf, 335⟩

theorem basis : FanInTwo witness := by
  intro g hg
  obtain ⟨⟨k,a,b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases k with
  | zero => simp [gateOf]
  | succ k => cases k <;> simp [gateOf]

def words (xs : List ℕ) : BitVec 1024 :=
  BitVec.ofNat 1024 (xs.foldr (fun w rest => w + rest * 2 ^ 64) 0)

def inputTables : List (BitVec 1024) := [
  words [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa],
  words [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc],
  words [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0],
  words [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00],
  words [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000],
  words [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000],
  words [0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]]

def outputTable : BitVec 1024 := words [0x16c08e9d01086553, 0x5f228a1a1661e142, 0xd214559df3a7a3b, 0x3ff12536880e2005, 0x333c6632032cc641, 0x7104af4e73674ac1, 0x131c9763826a04c1, 0x5fa43d540228864d, 0x200402040ba4a516, 0x1231033b22d4a481, 0x844b6111c72b9f59, 0xbb3b4061da24bf5c, 0x300182110400001a, 0x1911a13a24848e4c, 0x79153d618684d65b, 0x2014022517e5a747]

end PEqualNP.Outside.L_meta_17145

open PEqualNP.Outside.L_meta_17145

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_17145 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit (0x59092a9df2bc7573 + 2 ^ 64 * (0x1d58483ac443c8c2 + 2 ^ 64 * (0xa88822901b7982bb + 2 ^ 64 * (0x4140274d0fd25 + 2 ^ 64 * (0xd65a6f1a6879a8a5 + 2 ^ 64 * (0x24508c1a7455fba3 + 2 ^ 64 * (0x68658ad53050a010 + 2 ^ 64 * (0x5e55690e10a00735 + 2 ^ 64 * (0xb014586ab804a4 + 2 ^ 64 * (0xb07351f447af40 + 2 ^ 64 * (0x40d9d7bca88c2290 + 2 ^ 64 * (0x5405808240241486 + 2 ^ 64 * (0x50ddf79e6891afb9 + 2 ^ 64 * (0x28c180f8553080be + 2 ^ 64 * (0xa6860e806ac8ae9e + 2 ^ 64 * 0x10f0105020508c18))))))))))))))) (32 * u.val + v.val))) 330 := by
  exact hcsWitness (n := 10) inputTables outputTable witness 330 _ basis
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
