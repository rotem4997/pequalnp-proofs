import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1730_aux

open PEqualNP.CircuitLowerBounds

def chk (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun i => decide (i < n)) && chk (n + 1) gs

theorem chk_spec : ∀ (gs : List Gate) (n : ℕ), chk n gs = true →
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | g :: gs, n, h, 0, _, i, hi => by
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simpa using h.1 i (by simpa using hi)
  | g :: gs, n, h, j + 1, hj, i, hi => by
    simp only [chk, Bool.and_eq_true] at h
    have := chk_spec gs (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

def Inv (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ (∀ i, w.length ≤ i → m.testBit i = false)

theorem step_inv (w : List Bool) (m : ℕ) (b : Bool) (h : Inv w m) :
    Inv (w ++ [b]) (if b then m ||| 2 ^ w.length else m) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

def mk : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => mk (k + 1) (if b then m ||| 2 ^ k else m) bs

theorem mk_spec : ∀ (bs w : List Bool) (m : ℕ), Inv w m → Inv (w ++ bs) (mk w.length m bs)
  | [], w, m, h => by simpa [mk] using h
  | b :: bs, w, m, h => by
    have := mk_spec bs (w ++ [b]) _ (step_inv w m b h)
    simpa [mk] using this

def run : ℕ → ℕ → List Gate → ℕ
  | _, m, [] => m
  | k, m, g :: gs => run (k + 1) (if g.op.eval (g.inputs.map fun i => m.testBit i) then m ||| 2 ^ k else m) gs

theorem run_spec : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), Inv w m →
    Inv (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (run w.length m gs)
  | [], w, m, h => by simpa [run] using h
  | g :: gs, w, m, h => by
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => m.testBit i) :=
      List.map_congr_left (fun i _ => h.1 i)
    have := run_spec gs _ _ (step_inv w m (g.op.eval (g.inputs.map fun i => w.getD i false)) h)
    simp only [List.foldl_cons, run]
    rw [hmap] at this ⊢
    simpa using this

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run x.length (mk 0 0 x) C.gates).testBit C.output := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 C.output

def mchk (gs : List Gate) : Bool :=
  gs.all (fun g => (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length ≤ 2))

theorem mchk_spec (C : Circuit) (h : mchk C.gates = true) : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [mchk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all

end PEqualNP.Outside.L_meta_1730_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1730 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [79, 68]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [80, 69]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 70]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [82, 71]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [83, 72]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [85, 74]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [86, 75]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [88, 77]⟩], output := 89 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 64 ∧ (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → C.eval (List.ofFn (fun i : Fin 26 => decide (i.val = p.val ∨ i.val = 13 + l.val))) = true) ∧ (∀ m ∈ ([8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376, 1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728, 4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716, 8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282, 14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272, 19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192, 33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152, 35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088, 41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360, 50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672] : List ℕ), (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → ¬ (Nat.testBit m p.val = true ∧ Nat.testBit m (13 + l.val) = true)) ∧ C.eval (List.ofFn (fun j : Fin 26 => Nat.testBit m j.val)) = false) := by
  intro C hC
  subst hC
  refine ⟨PEqualNP.Outside.L_meta_1730_aux.mchk_spec _ (by decide +kernel), rfl, ?_, ?_⟩
  · simp only [PEqualNP.Outside.L_meta_1730_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · intro m hm
    rw [PEqualNP.Outside.L_meta_1730_aux.eval_eq]
    revert hm
    revert m
    set_option maxRecDepth 100000 in decide +kernel
