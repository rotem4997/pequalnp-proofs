import PEqualNP.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264
abbrev Mask := BitVec 16
abbrev Signature := Mask × Mask
def signatures : List Signature := [ (417,51203), (85,8739), (772,3120), (85,8754), (562,34572), (85,8998), (1056,3120), (562,36120), (417,52241), (584,28864), (85,12898), (1160,28864), (417,55425), (1282,34572), (772,36120), (417,52489), (1536,51203), (772,52241), (584,55425), (562,52489), (1536,8739), (1056,8754), (1282,8998), (1160,12898), (597,51203), (631,32771), (605,16387), (853,2051), (1441,8739), (1449,8195), (1443,515), (631,524), (1443,32780), (1798,1036), (117,3120), (501,2096), (631,1072), (1796,8754), (1932,8240), (1798,560), (605,8384), (1449,16576), (272,34572), (341,34568), (433,33540), (501,33536), (788,1796), (853,1792), (1040,8998), (1586,8994), (1296,8742), (1176,8964), (1722,8960), (1432,8708), (1072,804), (1328,548), (1552,774), (1808,518), (288,36120), (1312,34072), (1441,33808), (1314,3344), (1443,3328), (304,3096), (433,3080), (1328,1048), (544,52241), (1568,51217), (1586,34832), (616,19472), (634,19456), (1640,18448), (1568,3089), (1586,3073), (192,28864), (213,28800), (481,28736), (501,28672), (1088,12898), (1608,12834), (1216,8802), (1346,12864), (1866,12800), (1474,8768), (1120,12384), (1640,12320), (1248,8288), (1600,12354), (1728,8258), (640,55425), (1672,55297), (704,51329), (690,53376), (1722,53248), (754,49280), (900,22656), (1932,22528), (964,18560), (1664,20609), (1728,16513), (768,52489), (1794,51457), (784,51209), (840,50440), (844,50176), (1866,49408), (856,49160), (1798,35072), (788,34824), (1792,34057), (1796,33793), (1808,32777), ]
def neighbors : Fin 11 → Mask := ![1536,272,1056,192,1282,772,1160,584,562,417,85]
def incident : Fin 11 → Mask := ![3,12,48,192,772,3088,12352,20608,34056,51201,8738]
def incidentOf (vs : Mask) : Mask :=
  (List.finRange 11).foldl (fun m k => if vs.getLsbD k.val then m ||| incident k else m) 0
def centerMode (s : Signature) (k : Fin 11) : Mask :=
  let leaves := incidentOf (s.1 &&& neighbors k)
  leaves &&& (incident k ||| s.2)
def sigAt : Fin 112 → Signature := ![(417,51203),(85,8739),(772,3120),(85,8754),(562,34572),(85,8998),(1056,3120),(562,36120),(417,52241),(584,28864),(85,12898),(1160,28864),(417,55425),(1282,34572),(772,36120),(417,52489),(1536,51203),(772,52241),(584,55425),(562,52489),(1536,8739),(1056,8754),(1282,8998),(1160,12898),(597,51203),(631,32771),(605,16387),(853,2051),(1441,8739),(1449,8195),(1443,515),(631,524),(1443,32780),(1798,1036),(117,3120),(501,2096),(631,1072),(1796,8754),(1932,8240),(1798,560),(605,8384),(1449,16576),(272,34572),(341,34568),(433,33540),(501,33536),(788,1796),(853,1792),(1040,8998),(1586,8994),(1296,8742),(1176,8964),(1722,8960),(1432,8708),(1072,804),(1328,548),(1552,774),(1808,518),(288,36120),(1312,34072),(1441,33808),(1314,3344),(1443,3328),(304,3096),(433,3080),(1328,1048),(544,52241),(1568,51217),(1586,34832),(616,19472),(634,19456),(1640,18448),(1568,3089),(1586,3073),(192,28864),(213,28800),(481,28736),(501,28672),(1088,12898),(1608,12834),(1216,8802),(1346,12864),(1866,12800),(1474,8768),(1120,12384),(1640,12320),(1248,8288),(1600,12354),(1728,8258),(640,55425),(1672,55297),(704,51329),(690,53376),(1722,53248),(754,49280),(900,22656),(1932,22528),(964,18560),(1664,20609),(1728,16513),(768,52489),(1794,51457),(784,51209),(840,50440),(844,50176),(1866,49408),(856,49160),(1798,35072),(788,34824),(1792,34057),(1796,33793),(1808,32777)]
def submasks (bits p : Nat) : List Nat :=
  match bits with
  | 0 => [0]
  | k + 1 =>
    let prev := submasks k p
    if p.testBit k then prev ++ prev.map (fun m => 2^k + m) else prev
theorem submaskMem (bits p m : Nat) (range : m < 2^bits)
    (sub : ∀ i < bits, m.testBit i = true → p.testBit i = true) : m ∈ submasks bits p := by
  induction bits generalizing m with
  | zero =>
    have h : m = 0 := by simp at range; omega
    subst m
    simp [submasks]
  | succ k ih =>
    by_cases isSmall : m < 2^k
    · have old := ih m isSmall (fun i il => sub i (by omega))
      by_cases pb : p.testBit k = true
      · simp [submasks,pb,old]
      · simp [submasks,pb,old]
    · let r := m - 2^k
      have hm : m = 2^k + r := by dsimp [r]; omega
      have rr : r < 2^k := by
        simp only [Nat.pow_succ] at range
        dsimp [r]
        omega
      have hmb : m.testBit k = true := by
        rw [hm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow rr]
        rfl
      have hp := sub k (by omega) hmb
      have old : r ∈ submasks k p := ih r rr (fun i il re => by
        apply sub i (by omega)
        simpa only [hm, Nat.testBit_two_pow_add_gt il] using re)
      rw [submasks, hp, if_pos rfl]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨r,old,hm.symm⟩)
end LowTop2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264.Four
theorem orLeft (x y z : Mask) : x ||| (y ||| z) = y ||| (x ||| z) := by
  rw [← BitVec.or_assoc, BitVec.or_comm x y, BitVec.or_assoc]
def below (a b : Mask) : Bool := (a &&& b) == a
def envelopes (ranges : List Mask) (m : Mask) : Bool := ranges.any (below m)
theorem below_bit {a b : Mask} (h : below a b = true) (i : ℕ)
    (ha : a.getLsbD i = true) : b.getLsbD i = true := by
  have ht := congrArg (fun w : Mask => w.getLsbD i) (beq_iff_eq.mp h : a &&& b = a)
  simpa only [BitVec.getLsbD_and, ha, Bool.true_and] using ht
theorem below_of_bits {a b : Mask} (h : ∀ i < 16, a.getLsbD i = true → b.getLsbD i = true) :
    below a b = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  cases ha : a.getLsbD i
  · rfl
  · simp [h i hi ha]
theorem below_trans {a b c : Mask} (h : below a b = true) (h' : below b c = true) :
    below a c = true :=
  below_of_bits fun i _ ha => below_bit h' i (below_bit h i ha)
theorem below_or {a b c d : Mask} (h : below a b = true) (h' : below c d = true) :
    below (a ||| c) (b ||| d) = true := by
  apply below_of_bits
  intro i _ hOn
  simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hOn ⊢
  exact hOn.imp (below_bit h i) (below_bit h' i)
theorem below_full {w : Mask} (h : below 65535 w = true) : w = 65535 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have top : (65535 : Mask).getLsbD i = true := by
    change (BitVec.allOnes 16).getLsbD i = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true hi
  exact (below_bit h i top).trans top.symm
theorem envelopes_complete {ms : List Mask} {m : Mask} (h : envelopes ms m = true) :
    ∃ x ∈ ms, below m x = true := List.any_eq_true.mp h
def firstMissing (seed : Mask) := (List.range 16).find? (fun i => !seed.getLsbD i)
def excludesPair (r : List Mask) (seed : Mask) : Bool :=
  match firstMissing seed with
  | none => false
  | some i => r.all fun x => !(x.getLsbD i) || r.all fun y => (seed ||| x ||| y) != 65535
def excludesTriple (r : List Mask) (seed : Mask) : Bool :=
  match firstMissing seed with
  | none => false
  | some i => r.all fun x => !(x.getLsbD i) || excludesPair r (seed ||| x)
theorem pair_sound {r : List Mask} {seed x y : Mask}
    (check : excludesPair r seed = true) (hx : x ∈ r) (hy : y ∈ r) :
    seed ||| x ||| y ≠ 65535 := by
  intro eq
  unfold excludesPair at check
  cases eh : firstMissing seed with
  | none => simp [eh] at check
  | some i =>
    have hi := List.mem_range.mp (List.mem_of_find?_eq_some eh)
    have off : seed.getLsbD i = false := by
      have := List.find?_some eh
      simpa using this
    have on : (65535 : Mask).getLsbD i = true := by
      change (BitVec.allOnes 16).getLsbD i = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true hi
    have phase := congrArg (fun w : Mask => w.getLsbD i) eq
    simp only [BitVec.getLsbD_or, off, Bool.false_or, on, Bool.or_eq_true] at phase
    rw [eh] at check
    rcases phase with h | h
    · have row := List.all_eq_true.mp check x hx
      simp only [h, Bool.not_true, Bool.false_or] at row
      simpa [eq] using List.all_eq_true.mp row y hy
    · have row := List.all_eq_true.mp check y hy
      simp only [h, Bool.not_true, Bool.false_or] at row
      have eq' : seed ||| y ||| x = 65535 := by
        simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using eq
      simpa [eq'] using List.all_eq_true.mp row x hx
theorem triple_sound {r : List Mask} {seed x y z : Mask}
    (check : excludesTriple r seed = true) (hx : x ∈ r) (hy : y ∈ r) (hz : z ∈ r) :
    seed ||| x ||| y ||| z ≠ 65535 := by
  intro eq
  unfold excludesTriple at check
  cases eh : firstMissing seed with
  | none => simp [eh] at check
  | some i =>
    have hi := List.mem_range.mp (List.mem_of_find?_eq_some eh)
    have off : seed.getLsbD i = false := by
      have := List.find?_some eh
      simpa using this
    have on : (65535 : Mask).getLsbD i = true := by
      change (BitVec.allOnes 16).getLsbD i = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true hi
    have phase := congrArg (fun w : Mask => w.getLsbD i) eq
    simp only [BitVec.getLsbD_or, off, Bool.false_or, on, Bool.or_eq_true] at phase
    rw [eh] at check
    have pair {m : Mask} (hm : m ∈ r) (h : m.getLsbD i = true) : excludesPair r (seed ||| m) = true := by
      have row := List.all_eq_true.mp check m hm
      simpa only [h, Bool.not_true, Bool.false_or] using row
    rcases phase with (h | h) | h
    · exact pair_sound (pair hx h) hy hz eq
    · apply pair_sound (pair hy h) hx hz
      simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using eq
    · apply pair_sound (pair hz h) hx hy
      simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using eq
def mode (s : Signature) (m : Mask) : Prop :=
  ∃ k : Fin 11, m = incident k ∨ m = centerMode s k
theorem mode_mono {s t : Signature} (g : below s.1 t.1 = true) (p : below s.2 t.2 = true) (k : Fin 11) :
    below (centerMode s k) (centerMode t k) = true := by
  have extend (l : List (Fin 11)) (a b : Mask)
      (hab : below a b = true) :
      below
        (l.foldl (fun m k' => if (s.1 &&& neighbors k).getLsbD k'.val then m ||| incident k' else m) a)
        (l.foldl (fun m k' => if (t.1 &&& neighbors k).getLsbD k'.val then m ||| incident k' else m) b) = true := by
    induction l generalizing a b with
    | nil => exact hab
    | cons v l ih =>
      simp only [List.foldl_cons]
      apply ih
      have hGB {i : ℕ} (h : (s.1 &&& neighbors k).getLsbD i = true) :
          (t.1 &&& neighbors k).getLsbD i = true := by
        simpa only [BitVec.getLsbD_and, Bool.and_eq_true] using
          (show s.1.getLsbD i = true ∧ (neighbors k).getLsbD i = true by
            simpa only [BitVec.getLsbD_and, Bool.and_eq_true] using h).imp (below_bit g i) id
      by_cases hS : (s.1 &&& neighbors k).getLsbD v.val = true
      · simp only [hS, hGB hS, ite_true]
        exact below_or hab (below_of_bits fun _ _ h => h)
      · simp only [ite_eq_right hS]
        by_cases hT : (t.1 &&& neighbors k).getLsbD v.val = true
        · simp only [hT, ite_true]
          apply below_of_bits
          intro i _ hOn
          simp [BitVec.getLsbD_or, below_bit hab i hOn]
        · simpa only [ite_eq_right hT] using hab
  have spread := extend (List.finRange 11) 0 0 (below_of_bits (by simp))
  have later : below (incident k ||| s.2) (incident k ||| t.2) = true :=
    below_or (below_of_bits fun _ _ h => h) p
  apply below_of_bits
  intro i _ h
  simp only [centerMode, BitVec.getLsbD_and, Bool.and_eq_true] at h ⊢
  exact ⟨below_bit spread i h.1, below_bit later i h.2⟩
end LowTop2264.Four

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264.Four
abbrev ModeRow := Signature × List Mask
abbrev RefRow := Signature × Nat
def oneBounds : List Mask := [3120, 8739, 8754, 8998, 12898, 28864, 34572, 36120, 51203, 52241, 52489, 55425]
def twoBounds : List Mask := [3087, 3863, 8908, 8946, 9190, 11504, 11838, 12086, 12910, 13158, 15443, 15986, 16208, 18672, 20659, 21383, 23692, 24452, 28867, 28876, 28912, 29324, 29410, 29606, 29636, 31410, 31920, 31952, 32306, 34107, 34575, 34620, 34764, 34876, 36123, 36312, 36636, 42798, 42952, 44858, 46411, 46456, 46924, 46954, 48472, 49356, 50116, 52021, 52253, 52433, 52537, 52681, 53005, 53013, 54448, 55180, 55437, 55473, 56197, 56465, 56713, 56728, 59951, 60131, 60199, 60979, 61227, 61516, 62276, 62370, 62920, 63274, 63368, 63601, 63681, 64099, 64163, 64261, 64321, 64593, 64841]
private def decodeInc (x : Nat) : List Mask :=
  ([(0,3),(1,12),(2,48),(3,192),(4,772),(5,3088),(6,12352),(7,20608),(8,34056),(9,51201),(10,8738)] : List (Nat × Mask)).filterMap fun t =>
    if x.testBit t.1 then some t.2 else none
private def decodeMode : Nat → Nat → List ModeRow
  | 0, _ => []
  | n + 1, blob =>
    let head : Signature := (BitVec.ofNat 16 blob, BitVec.ofNat 16 (blob >>> 16))
    let size := (blob >>> 43) &&& 7
    let opts := decodeInc (blob >>> 32) ++
      (List.range size).map (fun i => BitVec.ofNat 16 (blob >>> (46 + 16*i)))
    (head,opts) :: decodeMode n (blob >>> (46 + 16*size))
def starSignature (a b c : Fin 11) : Signature :=
  let guard := neighbors a ||| neighbors b
  (guard, incident c &&& incidentOf guard)
def signatureSources : List Signature :=
  signatures ++ (List.finRange 11).flatMap fun a =>
    (List.finRange 11).flatMap fun b =>
      if b < a || (neighbors a).getLsbD b.val then []
      else (List.finRange 11).map (starSignature a b)
def modeData : List (Nat × Nat) := [
  (8,0xd801cd09c811222383fb200409df400220408c8830063ff8508027787087000083008039be8888809df3424cffcd0902328410800c40c022230d00afd3200407d73426146214308c8a0fd850801f5c80320c007000430020cb7c0888807d73424cffcd0901a1),
  (8,0xd88135ff620406873044ddfcc1101a1870c8518850923228bb61c200554c988bbf3262005523262fbc8c98015734272207200dc10020c2cbac80106bac08080034c000430020cbfe214201aea1c20c98888c88898888eaba222206ba),
  (8,0x870c3bb61c3008cb240614420c308c881c029ed830001f5d80170c0322264ddc00007d762054300c889977508001f5d801326230c066dcc10007d7304488c8344010321d90c1001f5c81122320d100430876c20c007d724048c981c1014400c329ed030401f5),
  (8,0x8d18580022320c118b6c304009de146088c8304420c22db04300277870c23264bb40c1009de1c3088992ed020c0277d881c901c811222385fb200409760c01c20020c1f7b2222025dd801c901c811222387fb200c09563460edf8d180232),
  (8,0xd0008d18850c85092322ab7614200d560c02000dc00030c00832fd822220355d801cd0940c073df20040bcb400130008c01fff850802f2d881cd0951ff200409eb42008c0177f8508027ad0018811850922230803abfa000c09ddc100c9893bf30400277),
  (8,0x8300704008307eef200416a734261c2010c1cfb850805a9c80332622322223286e8888816a60c11c000302020c27ebc80105a3cd09870c043073a61420168f200cc8888c9888ca1ea222205a3c80332222322223287e8888c16876007304724060030888e9dcc8010355),
  (8,0x70802326226222238db888881d2b14230203000dc1016002ebed00006bac50870c05880400398d942001ae960010300881080c0800eff2304006ba87083240223022042203bae88c001aea34613041220030c0200eeda0c1006ba870c3240023002039aa00c101aea1c2088c88898888e2fa23220632),
  (8,0x22320d100c116f6c30c001d488c8bfb2232005522232ff8888c015730472207200e0c01c102d9ec801078cc508c0808d1887088003bb7a14201e30c9888c88888c30c239a2222078cd881cc01c809c8038304b5bb20041d2b420234221c32000e66c8508074a),
  (8,0xd88135ff62040923220489891ff00c001f5c80922260504041887fc003007d7200c888d1fe000301f5d80170c0304274ddc100078724060c301c100c1a5ed830401b1c80337fb200c0685c3014204c889b37708000d5),
  (8,0x8d185880597c304009ea1c308c116ed0304027ac508481032226bfd400009df04012040c889bff5080025dc1015081481122238df9000c0975c300c9893373040025d70c022624cdc830009760c108c993ef0304025d),
  (8,0xc508588050c0320099dd42000bc9c1016000c900c3027b7304002f28d1858004c107b7c30400bca1c308c116ed030402f2c508588059ff42000acb1420c8016ff5080027acd08588059fd300009e9c300c9017373040027a),
  (8,0x8304810123260d10030caf340c100d576207304555fc801034cd0808d18597e14200d334203342167fc5080348cc11377f30440c123460edf8d180304cd0933ff34240c0340031421220103026f7c08002f2),
  (8,0xd801cc1140c0775f20040f13400314223461edf850803c4d881cc01c901800c95f720040d634202342214308c0267d85080358704032624efcc1000d5624021005600088c81032bf90c10035589018003580122230c11af78200c0d5614060c008c8834401c32bcd07000355),
  (8,0xc80332020306023297a8080c168f14221c221431efd8508059832622322020c6ef48888166314221c316ed8508058a326223264ebc8888162a1c30eed870c050223262fbc8c981408c988bbf32620488),
  (8,0xd8012300203077ecc10016a7200cc1088c0880ca5ba200305a9cc110c300700776c304016a720260c301031ded800c05a3d881708055fd4200168f340430c030201c125cb0d0005a3cc110c300c180704972c3040168f2404c800103008c25f9030405a3),
  (8,0xc881c803704076fb60041a2362073007200c20c257ac801066870802262223222238de8888819a1c2008988888db7e32220648c508870c5bb614201708c8888c988301be7222205c2d88170c054dd420016a72205c30153740c005a9),
  (8,0x8d18870c80037b3214201c188c98888c30c1bca22220706232222230c306f6888c81c1334072027200e0c125eec9010702488040c030c07edc03001aea14612040c1800890008eebe003006ba850c020c5bf400301aea14250204c108081800caebb000306ba),
  (8,0x3060232020230c309e6880c01e3310012200200c1c027fe0c10078cd080cd00c008c0038304bdbb04001d2b00213001000c83027f65080074a70802304224022039db8c8001d29c3008c10800df263040074a800c22400d0002039ff00c101d2b30472027200e0c125cec8010706),
  (8,0x70c03cddc30009233044ddfcc110220cc090d00040c77f4302006c63460edf8d180120870c3bb61c3004434001c10130412201200ef9e5800078cd08070c04c1040039c5942001e33400103008c00800e7f63040078c),
  (8,0x1fff62040a021c21c20167f2200027a50c022405ddc030009ea143088116fd000c027acc1058805d7d304009a3420220408c89b7f8100025d8900588022326dec2040097488c820c13fb0030025d),
  (8,0x70c030605cdcc1000d31620080c177b0c10034c83040d10070c03249f341c100c53302724060031dfdc80903108708700020c07bdc88000bc9410122008901fff00c002f2850c22045bf400300bcb600503015f7c88102c0),
  (8,0xc1004c0032007ffd42000d61c300c90173730400358830423040d00030c9fb40c100d6304013040c889bdf5000035522320c304f6c00c00d5604120024889830623df000c0355d080cc105d7f10000d313040c0817df5080034c),
  (8,0x1ffcc98811007ff23260410d08050c04c1030209d5d42000f1302016001304103027d7488003c4d000704030c030609edcc1000f131001600080c1ffb0c1003c4d0804c105d7d62000e13420330230402003277dc0080358),
  (8,0x232222320700020c8fe4888814c2344030c030601c127cb0d1005228d18870804307b6e146014808c8808313fd222605103222223220c06fcc88881380c88883013f7226204c032403efc8c101261c300f3770c00488),
  (8,0xd00023005ffcc1001660c9008c000831fbd22040598c1003240030c7eb40c1016634201c3017375080058ad00023045fbcc100162b0400c9017bf0304058a23043fbcc900150a34221c22143010c26f985080530),
  (8,0x3200230420c07f9c8900170b0400c8017ff030405c2c9013240023076ec0c0016a72044c1800c81dbf003005a9d8012304203077acc000168f2044c08010600c925ef003005a3cc1187000430776e104016874201c30173750800598),
  (8,0x70c0203020037cc8c10019a1c200818080c0808e77a302006688c1058800c3008039d68304019a23462200c20c1eda881006328d090c3008037b68300418cb3047200c20c1ddac8110620d080708050c07ddd4200170b4000c3008c11fa7304005c2),
  (8,0x800c0c18070c7f3410301c1a00303440080dfdc030407060c30032402237f2808c01c1a34261c22000defe85090700d801c803700040c097db20041b01c000c888888c83023f6222206c0c400400320c07fd9420019a330416201200c20c275a48100668),
  (8,0x50c020c05ddc03001d2a003030200c31fed000c074a8009508120420c010306bdbc000c1d2b30072407200e0c020032dfcc80107108d088708850c80039bf214201c420c008c88888c08323fc222207108d108808880383049f3a24001c1a2020200c1c11fee0c100706),
  (8,0x8c188900800c7f7620200c5030c0fdb0c3003048c180d10040c7f74306004c1c300f3770c000c0c10032400d1002039e780c001e3302010300c301fb700c0078c408130420c1103029e7c000c1e3220216200200c1c1276e0c00074a),
  (8,0x20300c305f6c00c00f120c01c2000831f7d2200035889005880040c7df430000d614300890177700c00358810422040c087ffc00300d61c20030c175b2020034c50c020605ddc03000d3080c030c17db0030034c),
  (8,0x580030c020307eccc1001380c080830080c1ff3206004e04c100c305f6c3040138080c0ffb30600460070402305fac0c9010c088c8bfb22320420700020c00c307f4c80800f13020141008181fff00c003c4),
  (8,0x830470405ebf0000162b0200c3017b700c0058ac008030c5fb40030162a3040344030c01c001032fd90c1005308c18070805100430040cbf64106014c224001c100c3008c27e903040530070403200230020c9fa4089014c1c20162014301f77508004e0),
  (8,0xc80337fb200c1800888cbfe222306008304700040c07f9f0000170b0200c2017ff00c005c2c008030c5fb40030170a0c020031c101fbdc0000598c08030c05edc0300166300200c217ff000c0598),
  (8,0x708040035df942041a034202000c10c1f7a8400066850c020c05ddc030019a210408180008dffe0030066884015081204200329dec000c19a1c100800d7be304206408c110c3008037f68304418820c10080d7ee03060610),
  (8,0x83040d00030c02039fb00c101c420c100c080830080e7ec0206071080090c1103067f3c000c1c1a30461c02000dfde84010704708050c040037dd942001b01c20140050301000e776408106c0704030c020037ed8c1001b01c100c0088300800e7b6204206c0),
  (8,0x8300800c0d0008309fe6200014c2204014400c81fff003005308808050403087ffc003014c1c001030020c1ff3480004e0488030805ffc030013812040c0817ff003004e00c303f6c30c0108230260c2204060032000effc80090710),
  (5,0x22400200c1c0010327fc0c00071081040c0803087ffc00301c42040430040c09fff00030710504030805ffc03001b014004c0097ff000306c0),
]
def modeRows : List ModeRow := modeData.flatMap fun p => decodeMode p.1 p.2
def refData : List (Nat × Nat × Nat) := [
  (0,24,0x341a5f50e0211cb70f00168d40f5c0312e0e0c48416171f3b87a41),
  (24,24,0x302942c4206a4cf0496ea3d0a1e088fdbe740e1bcec293092c4219),
  (48,24,0x6c14536d46925a0695769c97cc95ea523d1080bed8c335caf060b6),
  (72,24,0x589606c53501fd3f18893f9acfc67a2d82ba3e2dc2a43203b1a711),
  (96,24,0x5020140804020108090471b8ef70ac11aa92e29108598d45d6892),
  (120,24,0x5024140819020108204201c4e471b91c52c8fb89c52b950201409),
  (144,24,0x748dc72381c8ddc0891b8ddbee56d36db71b8cb6db5296d36a5008),
  (168,24,0x1b8ddca08050246a3405021060804200743c1d8f0748e6f0e90a3b),
  (192,24,0x800402450082014090502064310420902801b8e4708c450e46ee7),
  (216,24,0x980820460091402bf93b017ebf824097f2692afc0202010040202),
  (240,24,0x373218e6e62c24db0836898502714098c45f132ad54280080c0414),
  (264,24,0x80c04140984820140891488f6329915eae7aab5e86479994db0a),
  (288,24,0x5daec100a0482010320402104080400406020984c2410098448a44),
  (312,24,0x3c2081008150b0562a151c4e02a651d054bb923f600ff7eaee4722),
  (336,24,0x190c4108240a00fa7e8b365aed53ec56287d8982014091a8d06408),
  (360,24,0xa04c0201230040201148b056733b9c4e073650ac5208050241408),
  (384,24,0x339996ab359199f0f73319cf50d3db45a07b67430f50b3d0040601),
  (408,24,0x2200406020a04c24022304404445189448572b154a8a22aa844af9),
  (432,24,0x6eb7e3a2a158ac542a159a4542a350a80203010502611081182210),
  (456,24,0x44b9c6ee6729ae0e6c6230cd8c2831ae0a6b432210e8843381bc86),
  (480,24,0x131684e264289c502a160ace6cb389c0e6ca3a1bc6e391c23114e8),
  (504,24,0x2eaa14ea62ebc5e05d2f0e8783b48a411ceb7523c76e9130a04e28),
  (528,24,0x402810351a02010780402010261409d58633117cc6ab55185e45e),
  (552,24,0xd06c5a2f171e4ee75669e1982e3b02014091a8d0643141a090280),
  (576,24,0x24a60904b4f08c44522813c9c9d27a70461a0d86c8e4a0d868921a),
  (600,24,0xf874401e0e0840a040201008180b810301702068369a261293248),
  (624,24,0xa04c2410230448a4400800000f07838000f070005205038189a20),
  (648,14,0x20301030181105830220b0c8040602),
]
def decodeRef (off n blob : Nat) : List RefRow :=
  ((signatureSources.drop off).take n).zipIdx |>.map
    fun (key,i) => (key, (blob >>> (9*i)) &&& 511)
def refRows : List RefRow := refData.flatMap fun (offset,count,payload) => decodeRef offset count payload
end LowTop2264.Four

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264.Four
theorem signaturesInSources {s : Signature} (h : s ∈ signatures) : s ∈ signatureSources :=
  List.mem_append_left _ h
theorem starInSources (a b c : Fin 11) (h : (neighbors a).getLsbD b.val = false)
    (h' : (neighbors b).getLsbD a.val = false) : starSignature a b c ∈ signatureSources := by
  have directed (a b : Fin 11) (ab : ¬ b < a) (h : (neighbors a).getLsbD b.val = false) :
      starSignature a b c ∈ signatureSources := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨a,List.mem_finRange _,List.mem_flatMap.mpr ⟨b,List.mem_finRange _,?_⟩⟩
    simp [ab,h,List.mem_finRange]
  by_cases ab : b < a
  · have w := directed b a (by omega) h'
    simpa only [starSignature, BitVec.or_comm (neighbors b) (neighbors a)] using w
  · exact directed a b ab h
def validRef (r : RefRow) : Bool :=
  match modeRows[r.2]? with
  | some m => below r.1.1 m.1.1 && below r.1.2 m.1.2
  | none => false
def validGroup (r : ModeRow) : Bool :=
  ((List.finRange 11).all fun k => envelopes r.2 (incident k) && envelopes r.2 (centerMode r.1 k)) &&
  (r.2.all fun m => envelopes oneBounds m && r.2.all fun t => envelopes twoBounds (m ||| t)) &&
  (oneBounds.all fun m => excludesTriple r.2 m)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem refKeys : refRows.map Prod.fst = signatureSources := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem twoCheck : twoBounds.all (fun a => twoBounds.all fun b => (a ||| b) != 65535) = true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem modeRowsSound : modeRows.all validGroup = true := by
  simp only [modeRows,List.all_flatMap,modeData,List.all_cons,List.all_nil,Bool.and_eq_true,and_true]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem refRowsSound : refRows.all validRef = true := by
  simp only [refRows,List.all_flatMap,refData,List.all_cons,List.all_nil,Bool.and_eq_true,and_true]
  repeat' apply And.intro
  all_goals decide +kernel
end LowTop2264.Four

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264.Four
theorem chooseModeRow {s : Signature} (source : s ∈ signatureSources) :
    ∃ r ∈ modeRows, ∀ m, mode s m → ∃ v ∈ r.2, below m v = true := by
  rw [← refKeys] at source
  obtain ⟨rr, hr, her⟩ := List.mem_map.mp source
  have href := List.all_eq_true.mp refRowsSound rr hr
  unfold validRef at href
  cases hit : modeRows[rr.2]? with
  | none => simp [hit] at href
  | some r =>
    rw [hit, Bool.and_eq_true_iff] at href
    have hm := List.mem_of_getElem? hit
    refine ⟨r,hm,?_⟩
    intro m hmode
    obtain ⟨k, hk⟩ := hmode
    have data := List.all_eq_true.mp modeRowsSound r hm
    have bits := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp data).1).1
      k (List.mem_finRange _)
    rcases hk with hk | hk
    · rw [hk]
      exact envelopes_complete (Bool.and_eq_true_iff.mp bits).1
    · obtain ⟨v, hv, cv⟩ := envelopes_complete (Bool.and_eq_true_iff.mp bits).2
      refine ⟨v,hv,?_⟩
      rw [hk, ← her]
      exact below_trans (mode_mono href.1 href.2 k) cv
private theorem globalOne {r : ModeRow} (h : validGroup r = true) {m : Mask} (hm : m ∈ r.2) :
    ∃ bound ∈ oneBounds, below m bound = true := by
  apply envelopes_complete
  have check := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp check m hm)).1
private theorem globalTwo {r : ModeRow} (h : validGroup r = true) {x y : Mask} (hx : x ∈ r.2)
    (hy : y ∈ r.2) : ∃ bound ∈ twoBounds, below (x ||| y) bound = true := by
  apply envelopes_complete
  have check := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp check x hx)).2 y hy
private theorem twoTwo {r t : ModeRow} (hr : validGroup r = true) (ht : validGroup t = true)
    {a b c d : Mask} (ha : a ∈ r.2) (hb : b ∈ r.2) (hc : c ∈ t.2) (hd : d ∈ t.2)
    (full : a ||| b ||| c ||| d = 65535) : False := by
  obtain ⟨p,hp,pSub⟩ := globalTwo hr ha hb
  obtain ⟨q,hq,qSub⟩ := globalTwo ht hc hd
  have upper := below_or pSub qSub
  rw [← BitVec.or_assoc (a ||| b) c d, full] at upper
  have all := below_full upper
  have notAll := List.all_eq_true.mp (List.all_eq_true.mp twoCheck p hp) q hq
  simp [all] at notAll
private theorem oneThree {r t : ModeRow} (hr : validGroup r = true) (ht : validGroup t = true)
    {a b c d : Mask} (ha : a ∈ r.2) (hb : b ∈ t.2) (hc : c ∈ t.2) (hd : d ∈ t.2)
    (full : a ||| b ||| c ||| d = 65535) : False := by
  obtain ⟨p,hp,sub⟩ := globalOne hr ha
  have non := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ht).2 p hp
  have reflexive (m : Mask) : below m m = true := below_of_bits (fun _ _ h => h)
  have caseUp := below_or (below_or (below_or sub (reflexive b)) (reflexive c)) (reflexive d)
  rw [full] at caseUp
  exact triple_sound non hb hc hd (below_full caseUp)
theorem fourNoCover {p q : Signature} (hp : p ∈ signatureSources) (hq : q ∈ signatureSources)
    {a b c d : Mask} (ha : mode p a ∨ mode q a) (hb : mode p b ∨ mode q b)
    (hc : mode p c ∨ mode q c) (hd : mode p d ∨ mode q d) :
    a ||| b ||| c ||| d ≠ 65535 := by
  intro full
  obtain ⟨pRow,hpRow,widthP⟩ := chooseModeRow hp
  obtain ⟨qRow,hqRow,widthQ⟩ := chooseModeRow hq
  have pValid := List.all_eq_true.mp modeRowsSound pRow hpRow
  have qValid := List.all_eq_true.mp modeRowsSound qRow hqRow
  have route {m : Mask} (h : mode p m ∨ mode q m) :
      ∃ w, (w ∈ pRow.2 ∨ w ∈ qRow.2) ∧ below m w = true := by
    rcases h with h | h
    · obtain ⟨v,hv,sub⟩ := widthP m h
      exact ⟨v,Or.inl hv,sub⟩
    · obtain ⟨v,hv,sub⟩ := widthQ m h
      exact ⟨v,Or.inr hv,sub⟩
  obtain ⟨wA,hA,subA⟩ := route ha
  obtain ⟨wB,hB,subB⟩ := route hb
  obtain ⟨wC,hC,subC⟩ := route hc
  obtain ⟨wD,hD,subD⟩ := route hd
  have widened := below_or (below_or (below_or subA subB) subC) subD
  rw [full] at widened
  have full' := below_full widened
  rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    rcases hC with hC | hC <;> rcases hD with hD | hD
  · exact twoTwo pValid pValid hA hB hC hD full'
  · exact oneThree qValid pValid hD hA hB hC (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact oneThree qValid pValid hC hA hB hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo pValid qValid hA hB hC hD full'
  · exact oneThree qValid pValid hB hA hC hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo pValid qValid hA hC hB hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo pValid qValid hA hD hB hC (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact oneThree pValid qValid hA hB hC hD full'
  · exact oneThree qValid pValid hA hB hC hD full'
  · exact twoTwo pValid qValid hB hC hA hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo pValid qValid hB hD hA hC (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact oneThree pValid qValid hB hA hC hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo pValid qValid hC hD hA hB (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact oneThree pValid qValid hC hA hB hD (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact oneThree pValid qValid hD hA hB hC (by simpa only [BitVec.or_assoc, BitVec.or_comm, orLeft] using full')
  · exact twoTwo qValid qValid hA hB hC hD full'
end LowTop2264.Four

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264.Four
set_option maxHeartbeats 0 in
private theorem productEnvelope : signatures.all (fun s => envelopes oneBounds s.2) = true := by
  decide +kernel
theorem productTripleNoCover {p q : Signature} (hp : p ∈ signatures) (hq : q ∈ signatureSources)
    {x y z : Mask} (hx : mode q x) (hy : mode q y) (hz : mode q z) :
    p.2 ||| x ||| y ||| z ≠ 65535 := by
  intro full
  obtain ⟨b,hb,pSub⟩ := envelopes_complete (List.all_eq_true.mp productEnvelope p hp)
  obtain ⟨r,hr,dom⟩ := chooseModeRow hq
  obtain ⟨X,hX,xSub⟩ := dom _ hx
  obtain ⟨Y,hY,ySub⟩ := dom _ hy
  obtain ⟨Z,hZ,zSub⟩ := dom _ hz
  have valid := List.all_eq_true.mp modeRowsSound r hr
  have forb := List.all_eq_true.mp (Bool.and_eq_true_iff.mp valid).2 b hb
  have common := below_or (below_or (below_or pSub xSub) ySub) zSub
  rw [full] at common
  exact triple_sound forb hX hY hZ (below_full common)
end LowTop2264.Four

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
def hits (A : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ u ∈ A, x u = true
def safe (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x, hits A x → hits B x → x w = true → graphFun G ∅ x = true
private theorem graph_pair {u v : Fin n} (h : graphFun G ∅ (pairInput u v) = true) :
    G.Adj u v := by
  unfold graphFun at h
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨a,b,hab,ha,hb⟩ := h
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (G.irrefl hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.irrefl hab).elim
theorem common_neighbor {A B : Finset (Fin n)} {w : Fin n}
    (h : safe G A B w) (hw : w ∈ A) : ∀ b ∈ B, G.Adj w b := by
  intro b hb
  apply graph_pair
  have h1 : pairInput w b w = true := by simp [pairInput]
  have h2 : pairInput w b b = true := by simp [pairInput]
  exact h _ ⟨w, hw, h1⟩ ⟨b, hb, h2⟩ h1
theorem common_neighbor' {A B : Finset (Fin n)} {w : Fin n}
    (h : safe G A B w) (hw : w ∈ B) : ∀ a ∈ A, G.Adj w a := by
  exact common_neighbor (G := G) (A := B) (B := A)
    (fun x hB hA hwx => h x hA hB hwx) hw
theorem unique_center {A B : Finset (Fin n)} {u v : Fin n} (hG : NoFourCycle G)
    (hB : 1 < B.card) (hu : u ∈ A) (hv : v ∈ A)
    (hsu : safe G A B u) (hsv : safe G A B v) : u = v := by
  by_contra huv
  have hh := hG u v huv
  have hsub : B ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    simp [common_neighbor hsu hu w hw, common_neighbor hsv hv w hw]
  exact (Nat.not_le_of_lt hB) ((Finset.card_le_card hsub).trans hh)
theorem overlap_neighbor {A B : Finset (Fin n)} {s w : Fin n}
    (hs : s ∈ A ∩ B) (h : safe G A B w) : G.Adj s w := by
  obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hs
  apply graph_pair
  have h1 : pairInput s w s = true := by simp [pairInput]
  have h2 : pairInput s w w = true := by simp [pairInput]
  exact h _ ⟨s, ha, h1⟩ ⟨s, hb, h1⟩ h2
theorem unique_guard_of_overlap {A B : Finset (Fin n)} {u v : Fin n} (hG : NoFourCycle G)
    (hB : 1 < (A ∩ B).card) (hsu : safe G A B u) (hsv : safe G A B v) : u = v := by
  by_contra huv
  have hh := hG u v huv
  have hsub : A ∩ B ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    simp [(overlap_neighbor hw hsu).symm, (overlap_neighbor hw hsv).symm]
  exact (Nat.not_le_of_lt hB) ((Finset.card_le_card hsub).trans hh)
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
theorem safe_triple {A B : Finset (Fin n)} {a b w : Fin n}
    (h : safe G A B w) (ha : a ∈ A) (hb : b ∈ B) :
    G.Adj a b ∨ G.Adj w a ∨ G.Adj w b := by
  classical
  let x (i : Fin n) := decide (i = a ∨ i = b ∨ i = w)
  have hf := h x ⟨a, ha, by simp [x]⟩ ⟨b, hb, by simp [x]⟩ (by simp [x])
  unfold graphFun at hf
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq] at hf
  obtain ⟨i, j, hij, hi, hj⟩ := hf
  simp only [x, decide_eq_true_eq] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · exact (G.irrefl hij).elim
  · exact Or.inl hij
  · exact Or.inr (Or.inl hij.symm)
  · exact Or.inl hij.symm
  · exact (G.irrefl hij).elim
  · exact Or.inr (Or.inr hij.symm)
  · exact Or.inr (Or.inl hij)
  · exact Or.inr (Or.inr hij)
  · exact (G.irrefl hij).elim
theorem no_two_commons (hG : NoFourCycle G) {u v x y : Fin n}
    (huv : u ≠ v) (hxy : x ≠ y) (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : False := by
  have sub : ({x,y} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp [hux,hvx]
    · obtain rfl := Finset.mem_singleton.mp hz
      simp [huy,hvy]
  have ge : 2 ≤ (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card := by
    simpa [hxy] using Finset.card_le_card sub
  have le := hG u v huv
  omega
theorem three_guards_short_arm (hG : NoFourCycle G) {A B : Finset (Fin n)}
    {s u v w : Fin n} (overlap : A ∩ B = {s}) (hu : u ∈ A) (hv : v ∈ B)
    (hwu : w ∉ A) (hwv : w ∉ B)
    (gu : safe G A B u) (gv : safe G A B v) (gw : safe G A B w) :
    A ⊆ {s,u} ∨ B ⊆ {s,v} := by
  by_contra no
  have na : ¬ A ⊆ {s,u} := fun h => no (Or.inl h)
  have nb : ¬ B ⊆ {s,v} := fun h => no (Or.inr h)
  obtain ⟨a, ha, hextra⟩ := Finset.not_subset.mp na
  obtain ⟨b, hb, hextra'⟩ := Finset.not_subset.mp nb
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hextra hextra'
  obtain ⟨has,hau⟩ := hextra
  obtain ⟨hbs,hbv⟩ := hextra'
  have hw_ne_v : w ≠ v := fun e => hwv (e.symm ▸ hv)
  have hw_ne_u : w ≠ u := fun e => hwu (e.symm ▸ hu)
  have hs : s ∈ A ∩ B := by simp [overlap]
  have ⟨hsA,hsB⟩ := Finset.mem_inter.mp hs
  have uv := common_neighbor gu hu v hv
  have ub := common_neighbor gu hu b hb
  have va := common_neighbor' gv hv a ha
  have vs := common_neighbor' gv hv s hsA
  have us := common_neighbor gu hu s hsB
  have ws := (overlap_neighbor hs gw).symm
  rcases safe_triple gw ha hb with ab | wa | wb
  · exact no_two_commons hG (Ne.symm hau) (Ne.symm hbv) uv va.symm ub ab
  · exact no_two_commons hG hw_ne_v (Ne.symm has) ws vs wa va
  · exact no_two_commons hG hw_ne_u (Ne.symm hbs) ws us wb ub
def adjacentPair (G : SimpleGraph (Fin n)) (K : Finset (Fin n)) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v

omit [DecidableRel G.Adj] in
lemma single_adjacentPair {K : Finset (Fin n)} (small : K.card ≤ 1) : adjacentPair G K := by
  intro u hu v hv hne
  exact (hne (Finset.card_le_one.mp small u hu v hv)).elim

omit [DecidableRel G.Adj] in
lemma edge_adjacentPair {u v : Fin n} (h : G.Adj u v) : adjacentPair G {u,v} := by
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact h.symm
  · exact (hab rfl).elim
theorem useful_edge_cover_adjacent (hG : NoFourCycle G) (A B : Finset (Fin n)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧ adjacentPair G K ∧
      ∀ u v, hits A (pairInput u v) → hits B (pairInput u v) →
      (safe G A B u ∨ safe G A B v) → u ∈ K ∨ v ∈ K := by
  classical
  have pairSmall (u v : Fin n) : ({u,v} : Finset (Fin n)).card ≤ 2 := by
    calc
      _ ≤ ({v} : Finset (Fin n)).card + 1 := Finset.card_insert_le u {v}
      _ = 2 := by simp
  have covers_arm {K : Finset (Fin n)} {u v : Fin n} (h : hits K (pairInput u v)) :
      u ∈ K ∨ v ∈ K := by
    obtain ⟨x,hx,ht⟩ := h
    rcases (of_decide_eq_true ht : x = u ∨ x = v) with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  by_cases hA : A.card ≤ 1
  · exact ⟨A, by omega, single_adjacentPair hA, fun _ _ a _ _ => covers_arm a⟩
  by_cases hB : B.card ≤ 1
  · exact ⟨B, by omega, single_adjacentPair hB, fun _ _ _ b _ => covers_arm b⟩
  let insideA := A.filter fun w => safe G A B w
  let insideB := B.filter fun w => safe G A B w
  let inside := insideA ∪ insideB
  have aSmall : insideA.card ≤ 1 := Finset.card_le_one.mpr <| by
    intro u hu v hv
    obtain ⟨hmu,hsu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hmv,hsv⟩ := Finset.mem_filter.mp hv
    exact unique_center hG (by omega) hmu hmv hsu hsv
  have bSmall : insideB.card ≤ 1 := Finset.card_le_one.mpr <| by
    intro u hu v hv
    obtain ⟨hmu,hsu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hmv,hsv⟩ := Finset.mem_filter.mp hv
    exact unique_center (A := B) (B := A) hG (by omega) hmu hmv
      (fun x b a hx => hsu x a b hx) (fun x b a hx => hsv x a b hx)
  have insideSmall : inside.card ≤ 2 :=
    (Finset.card_union_le insideA insideB).trans (by omega)
  have insideAdjacent : adjacentPair G inside := by
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact (huv (Finset.card_le_one.mp aSmall u hu v hv)).elim
    · exact common_neighbor (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hu).1 v
        (Finset.mem_filter.mp hv).1
    · exact common_neighbor' (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hu).1 v
        (Finset.mem_filter.mp hv).1
    · exact (huv (Finset.card_le_one.mp bSmall u hu v hv)).elim
  have covered_inside {u : Fin n} (hu : safe G A B u) (hm : u ∈ A ∨ u ∈ B) :
      u ∈ inside := by
    rcases hm with hm | hm
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hm,hu⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hm,hu⟩))
  have covered_outside {u v : Fin n} (ha : hits A (pairInput u v))
      (hb : hits B (pairInput u v)) (hu : ¬ (u ∈ A ∨ u ∈ B)) : v ∈ A ∩ B := by
    refine Finset.mem_inter.mpr ⟨?_,?_⟩
    · exact (covers_arm ha).resolve_left (fun h => hu (Or.inl h))
    · exact (covers_arm hb).resolve_left (fun h => hu (Or.inr h))
  have covered_outside_right {u v : Fin n} (ha : hits A (pairInput u v))
      (hb : hits B (pairInput u v)) (hv : ¬ (v ∈ A ∨ v ∈ B)) : u ∈ A ∩ B := by
    refine Finset.mem_inter.mpr ⟨?_,?_⟩
    · exact (covers_arm ha).resolve_right (fun h => hv (Or.inl h))
    · exact (covers_arm hb).resolve_right (fun h => hv (Or.inr h))
  by_cases hOutside : ∃ w, w ∉ A ∧ w ∉ B ∧ safe G A B w
  · obtain ⟨w,hwa,hwb,hsw⟩ := hOutside
    by_cases hOverlap : 1 < (A ∩ B).card
    · refine ⟨{w}, by simp, single_adjacentPair (by simp), ?_⟩
      intro u v _ _ h
      rcases h with h | h
      · exact Or.inl (Finset.mem_singleton.mpr (unique_guard_of_overlap hG hOverlap h hsw))
      · exact Or.inr (Finset.mem_singleton.mpr (unique_guard_of_overlap hG hOverlap h hsw))
    · by_cases hEmpty : A ∩ B = ∅
      · refine ⟨inside, insideSmall, insideAdjacent, ?_⟩
        intro u v ha hb h
        rcases h with h | h
        · by_cases hu : u ∈ A ∨ u ∈ B
          · exact Or.inl (covered_inside h hu)
          · simpa [hEmpty] using covered_outside ha hb hu
        · by_cases hv : v ∈ A ∨ v ∈ B
          · exact Or.inr (covered_inside h hv)
          · simpa [hEmpty] using covered_outside_right ha hb hv
      obtain ⟨s, hs⟩ := Finset.card_eq_one.mp
        (show (A ∩ B).card = 1 by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
          omega)
      have hsAB : s ∈ A ∧ s ∈ B :=
        Finset.mem_inter.mp (show s ∈ A ∩ B by simp [hs])
      have insideNeighbor {x : Fin n} (hx : x ∈ inside) : G.Adj x s := by
        rcases Finset.mem_union.mp hx with hx | hx
        · exact common_neighbor (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx).1 s hsAB.2
        · exact common_neighbor' (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx).1 s hsAB.1
      by_cases hBoth : insideA.Nonempty ∧ insideB.Nonempty
      · obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := hBoth
        obtain ⟨hua,hsu⟩ := Finset.mem_filter.mp hu
        obtain ⟨hvb,hsv⟩ := Finset.mem_filter.mp hv
        rcases three_guards_short_arm hG hs hua hvb hwa hwb hsu hsv hsw with ha | hb
        · refine ⟨{s,u}, pairSmall s u, edge_adjacentPair (insideNeighbor
              (Finset.mem_union.mpr (Or.inl hu))).symm, ?_⟩
          intro a b h _ _
          exact (covers_arm h).elim (fun h => Or.inl (ha h)) (fun h => Or.inr (ha h))
        · refine ⟨{s,v}, pairSmall s v, edge_adjacentPair (insideNeighbor
              (Finset.mem_union.mpr (Or.inr hv))).symm, ?_⟩
          intro a b _ h _
          exact (covers_arm h).elim (fun h => Or.inl (hb h)) (fun h => Or.inr (hb h))
      · have small : inside.card ≤ 1 := by
          by_cases hne : insideA.Nonempty
          · have hem : insideB = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp (fun hh => hBoth ⟨hne,hh⟩)
            simpa [inside,hem] using aSmall
          · have hem : insideA = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
            simpa [inside,hem] using bSmall
        have extraAdjacent : adjacentPair G (insert s inside) := by
          intro u hu v hv hn
          have hU : u = s ∨ u ∈ inside := Finset.mem_insert.mp hu
          have hV : v = s ∨ v ∈ inside := Finset.mem_insert.mp hv
          rcases hU with eU | hu' <;> rcases hV with eV | hv'
          · exact (hn (eU.trans eV.symm)).elim
          · rw [eU]
            exact (insideNeighbor hv').symm
          · rw [eV]
            exact insideNeighbor hu'
          · exact insideAdjacent u hu' v hv' hn
        refine ⟨insert s inside, (Finset.card_insert_le s inside).trans (by omega),
          extraAdjacent, ?_⟩
        intro u v ha hb h
        rcases h with h | h
        · by_cases hu : u ∈ A ∨ u ∈ B
          · exact Or.inl (Finset.mem_insert_of_mem (covered_inside h hu))
          · have hv : v = s := by simpa [hs] using covered_outside ha hb hu
            exact Or.inr (Finset.mem_insert.mpr (Or.inl hv))
        · by_cases hv : v ∈ A ∨ v ∈ B
          · exact Or.inr (Finset.mem_insert_of_mem (covered_inside h hv))
          · have hu : u = s := by simpa [hs] using covered_outside_right ha hb hv
            exact Or.inl (Finset.mem_insert.mpr (Or.inl hu))
  · refine ⟨inside, insideSmall, insideAdjacent, ?_⟩
    intro u v _ _ h
    rcases h with h | h
    · exact Or.inl (covered_inside h (by by_contra hn; push Not at hn; exact hOutside ⟨u, hn.1, hn.2, h⟩))
    · exact Or.inr (covered_inside h (by by_contra hn; push Not at hn; exact hOutside ⟨v, hn.1, hn.2, h⟩))
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.EdgeOwnership PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
def prod (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A B : Finset (Fin n)) (u v : Fin n) : Prop :=
  hits A (pairInput u v) ∧ hits B (pairInput u v) ∧ (safe G A B u ∨ safe G A B v)
def nb (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Adj w)
def trimRep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A B : Finset (Fin n)) : Prop :=
  (∃ w s, s ∈ B ∧ A = {w,s} ∧ B ⊆ nb G w) ∨
  (∃ w z, G.Adj w z ∧ w ∈ A ∧ z ∈ B ∧ A ⊆ nb G z ∧ B ⊆ nb G w)
private theorem guardSwap {A B : Finset (Fin n)} {w : Fin n} (h : safe G A B w) : safe G B A w :=
  fun x hB hA hx => h x hA hB hx
private theorem pairFlip (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]
private theorem pairHit {A : Finset (Fin n)} {u v : Fin n} (h : hits A (pairInput u v)) :
    u ∈ A ∨ v ∈ A := by
  obtain ⟨x,hx,hp⟩ := h
  rcases (of_decide_eq_true hp : x = u ∨ x = v) with rfl | rfl
  · exact Or.inl hx
  · exact Or.inr hx
private theorem pairHitLeft {A : Finset (Fin n)} {u v : Fin n} (h : u ∈ A) :
    hits A (pairInput u v) := ⟨u,h,by simp [pairInput]⟩
private theorem outsidePair {A B : Finset (Fin n)} {u v : Fin n}
    (ha : u ∉ A) (hb : u ∉ B) (h : prod G A B u v) : v ∈ A ∩ B :=
  Finset.mem_inter.mpr ⟨(pairHit h.1).resolve_left ha, (pairHit h.2.1).resolve_left hb⟩
private theorem orientedTrim (h4 : NoFourCycle G) {A B : Finset (Fin n)} {w : Fin n}
    (hwa : w ∈ A) (hs : safe G A B w) (hB : 1 < B.card) (small : (A ∩ B).card ≤ 1)
    (noStar : ∀ c : Fin n, ∃ u v, prod G A B u v ∧ u ≠ c ∧ v ≠ c) :
    ∃ A' B', trimRep G A' B' ∧
      (∀ t, safe G A B t → safe G A' B' t) ∧
      ∀ u v, prod G A B u v → prod G A' B' u v := by
  classical
  have hBnb : B ⊆ nb G w := fun v hv => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,common_neighbor hs hwa v hv⟩
  by_cases other : ∃ z ∈ B, safe G A B z
  · obtain ⟨z,hzb,hzs⟩ := other
    have hAnb : A ⊆ nb G z := fun v hv => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,common_neighbor' hzs hzb v hv⟩
    exact ⟨A,B,Or.inr ⟨w,z,common_neighbor hs hwa z hzb,hwa,hzb,hAnb,hBnb⟩,
      fun _ h => h,fun _ _ h => h⟩
  have wNotB : w ∉ B := fun h => G.irrefl (common_neighbor hs hwa w h)
  obtain ⟨u,v,huv,hu,hv⟩ := noStar w
  have exOverlap : (A ∩ B).Nonempty := by
    rcases huv.2.2 with hU | hV
    · have notA : u ∉ A := fun m => hu (unique_center h4 hB m hwa hU hs)
      have notB : u ∉ B := fun m => other ⟨u,m,hU⟩
      exact ⟨v,outsidePair notA notB huv⟩
    · have notA : v ∉ A := fun m => hv (unique_center h4 hB m hwa hV hs)
      have notB : v ∉ B := fun m => other ⟨v,m,hV⟩
      exact ⟨u,outsidePair notA notB ⟨pairFlip u v ▸ huv.1, pairFlip u v ▸ huv.2.1, huv.2.2.symm⟩⟩
  obtain ⟨s,hS⟩ := Finset.card_eq_one.mp (Nat.le_antisymm small (Finset.card_pos.mpr exOverlap))
  have hsm := Finset.mem_inter.mp (show s ∈ A ∩ B by simp [hS])
  let A' : Finset (Fin n) := {w,s}
  have subset : A' ⊆ A := by
    intro v hv
    simp only [A', Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hwa
    · exact hsm.1
  have safe' (t : Fin n) (h : safe G A B t) : safe G A' B t := by
    intro x ha hb hx
    obtain ⟨y,hy,hyx⟩ := ha
    exact h x ⟨y,subset hy,hyx⟩ hb hx
  have keep (p q : Fin n) (h : prod G A B p q) (hP : safe G A B p) : hits A' (pairInput p q) := by
    by_cases hp : p ∈ A
    · have hEq := unique_center h4 hB hp hwa hP hs
      exact pairHitLeft (hEq.symm ▸ (show w ∈ A' by simp [A']))
    · have hm := outsidePair hp (fun m => other ⟨p,m,hP⟩) h
      rw [hS,Finset.mem_singleton] at hm
      exact (pairFlip q p) ▸ pairHitLeft (hm.symm ▸ (show s ∈ A' by simp [A']))
  refine ⟨A',B,Or.inl ⟨w,s,hsm.2,rfl,hBnb⟩,safe',?_⟩
  intro p q h
  refine ⟨?_,h.2.1,h.2.2.imp (safe' p) (safe' q)⟩
  rcases h.2.2 with hP | hQ
  · exact keep p q h hP
  · exact (pairFlip q p) ▸ keep q p ⟨pairFlip p q ▸ h.1, pairFlip p q ▸ h.2.1, h.2.2.symm⟩ hQ
theorem trim_nonstar (h4 : NoFourCycle G) (A B : Finset (Fin n)) (v₀ : Fin n)
    (noStar : ∀ c : Fin n, ∃ u v, prod G A B u v ∧ u ≠ c ∧ v ≠ c) :
    ∃ A' B', trimRep G A' B' ∧
      (∀ t, safe G A B t → safe G A' B' t) ∧
      ∀ u v, prod G A B u v → prod G A' B' u v := by
  classical
  obtain ⟨u₀,v₀',sample,_,_⟩ := noStar v₀
  have large (T : Finset (Fin n)) (every : ∀ u v, prod G A B u v → u ∈ T ∨ v ∈ T) : 1 < T.card := by
    by_contra! few
    have non : T.Nonempty := (every u₀ v₀' sample).elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (Nat.le_antisymm few (Finset.card_pos.mpr non))
    obtain ⟨u,v,edge,hu,hv⟩ := noStar c
    have H := every u v edge
    simp only [hc,Finset.mem_singleton] at H
    exact H.elim hu hv
  have hA := large A (fun _ _ hh => pairHit hh.1)
  have hB := large B (fun _ _ hh => pairHit hh.2.1)
  have small : (A ∩ B).card ≤ 1 := by
    by_contra! big
    obtain ⟨w,hW⟩ : ∃ w, safe G A B w := sample.2.2.elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
    obtain ⟨u,v,edge,hu,hv⟩ := noStar w
    exact edge.2.2.elim (fun h => hu (unique_guard_of_overlap h4 big h hW))
      (fun h => hv (unique_guard_of_overlap h4 big h hW))
  by_cases insideA : ∃ w ∈ A, safe G A B w
  · obtain ⟨w,hm,hs⟩ := insideA
    exact orientedTrim h4 hm hs hB small noStar
  by_cases insideB : ∃ w ∈ B, safe G A B w
  · obtain ⟨w,hm,hs⟩ := insideB
    exact orientedTrim (A := B) (B := A) h4 hm (guardSwap hs) hA (by simpa [Finset.inter_comm] using small)
      (fun v => let ⟨p,q,h,np,nq⟩ := noStar v
        ⟨p,q,⟨h.2.1,h.1,h.2.2.imp guardSwap guardSwap⟩,np,nq⟩) |>.imp (fun A' => by
      rintro ⟨B', rep, safeAll, prodAll⟩
      refine ⟨B', rep, fun t h => safeAll t (guardSwap h), fun u v h => ?_⟩
      exact prodAll u v ⟨h.2.1,h.1,h.2.2.imp guardSwap guardSwap⟩)
  exfalso
  have every (u v : Fin n) (h : prod G A B u v) : u ∈ A ∩ B ∨ v ∈ A ∩ B := by
    rcases h.2.2 with hp | hq
    · exact Or.inr (outsidePair (fun m => insideA ⟨u,m,hp⟩) (fun m => insideB ⟨u,m,hp⟩) h)
    · exact Or.inl (outsidePair (fun m => insideA ⟨v,m,hq⟩) (fun m => insideB ⟨v,m,hq⟩)
        ⟨pairFlip u v ▸ h.1,pairFlip u v ▸ h.2.1,h.2.2.symm⟩)
  exact (Nat.not_le_of_lt (large (A ∩ B) every)) small
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace Profile2264
open PEqualNP.EdgeOwnership
private abbrev V := Fin 11
private def edges : Finset (V × V) :=
  {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}
def leftover (K : Finset V) : Finset (V × V) :=
  edges.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)
private def profile (K : Finset V) : Prop :=
    K.card + max 3 (leftover K).card ≤ 7 →
    K.card = 4 ∧ (leftover K).card = 3 ∧
    (leftover K = {(0,9),(1,4),(3,6)} ∨
      leftover K = {(1,4),(2,5),(6,7)} ∨
      leftover K = {(1,4),(2,5),(3,7)} ∨
      leftover K = {(1,4),(2,5),(3,6)})
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem allProfiles : ∀ K : Finset V, profile K := by
  unfold profile leftover edges
  decide +kernel
def graph : SimpleGraph V :=
  edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def separated (e f : V × V) : Prop :=
  ¬ graph.Adj e.1 f.1 ∧ ¬ graph.Adj e.1 f.2 ∧ ¬ graph.Adj e.2 f.1 ∧ ¬ graph.Adj e.2 f.2
instance (e f : V × V) : Decidable (separated e f) := by unfold separated; infer_instance
private theorem edgesAdj : ∀ e : {e // e ∈ edges}, graph.Adj e.val.1 e.val.2 := by
  decide +kernel
def sym (e : V × V) : Sym2 V := s(e.1,e.2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem symInjective : ∀ e f : {e // e ∈ edges}, sym e.val = sym f.val → e.val = f.val := by
  decide +kernel
theorem seven_cover (K : Finset V) (hK : graph.IsVertexCover (K : Set V)) : 7 ≤ K.card := by
  classical
  let w (i : V) : ℕ := if i ∈ K then 1 else 0
  have ew (u v : V) (he : graph.Adj u v) : 1 ≤ w u + w v := by
    rcases hK he with hu | hv
    · change u ∈ K at hu
      simp [w, hu]
    · change v ∈ K at hv
      simp [w, hv]
  have e0 := ew 1 4 (by decide)
  have e1 := ew 4 8 (by decide)
  have e2 := ew 8 1 (by decide)
  have e3 := ew 3 6 (by decide)
  have e4 := ew 6 7 (by decide)
  have e5 := ew 7 3 (by decide)
  have e6 := ew 0 9 (by decide)
  have e7 := ew 9 5 (by decide)
  have e8 := ew 5 2 (by decide)
  have e9 := ew 2 10 (by decide)
  have e10 := ew 10 0 (by decide)
  have hw : ∑ i, w i = K.card := by simp [w]
  rw [Fin.sum_univ_succ] at hw
  simp [Fin.sum_univ_succ] at hw
  omega
theorem cover_uncovered (K D : Finset V) (U : Finset (Sym2 V))
    (hK : (graph.deleteEdges (U : Set _)).IsVertexCover (K : Set _))
    (hD : ∀ u v : V, s(u,v) ∈ U → u ∈ D ∨ v ∈ D) :
    graph.IsVertexCover (↑(K ∪ D) : Set V) := by
  intro u v he
  by_cases hu : s(u,v) ∈ U
  · rcases hD u v hu with hm | hm
    · exact Or.inl (Finset.mem_union_right _ hm)
    · exact Or.inr (Finset.mem_union_right _ hm)
  · rcases hK (SimpleGraph.deleteEdges_adj.mpr ⟨he, hu⟩) with hm | hm
    · exact Or.inl (Finset.mem_union_left _ hm)
    · exact Or.inr (Finset.mem_union_left _ hm)
theorem two_cover_bounds (K D0 D1 : Finset V) (U : Finset (Sym2 V))
    (hK : (graph.deleteEdges (U : Set _)).IsVertexCover (K : Set _))
    (h0 : D0.card ≤ 2) (h1 : D1.card ≤ 2)
    (hD : ∀ u v : V, s(u,v) ∈ U → u ∈ D0 ∪ D1 ∨ v ∈ D0 ∪ D1) :
    3 ≤ K.card ∧ (K.card = 3 →
      D0.card = 2 ∧ D1.card = 2 ∧ Disjoint D0 D1 ∧ Disjoint K (D0 ∪ D1)) := by
  have ht := seven_cover _ (cover_uncovered K _ U hK hD)
  have ha := Finset.card_union_le D0 D1
  have hb := Finset.card_union_le K (D0 ∪ D1)
  refine ⟨by omega, fun hK3 => ⟨by omega, by omega, ?_, ?_⟩⟩
  · have hc := Finset.card_union_add_card_inter D0 D1
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  · have hc := Finset.card_union_add_card_inter K (D0 ∪ D1)
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
theorem four_cover_ceiling (D : Finset V) (U : Finset (Sym2 V))
    (hD : D.card ≤ 4) (hU : U ⊆ graph.edgeFinset)
    (hit : ∀ u v : V, s(u,v) ∈ U → u ∈ D ∨ v ∈ D) : U.card ≤ 13 := by
  have hl : 3 ≤ (leftover D).card := by
    by_contra! h
    have p := allProfiles D (by omega)
    omega
  have hcount : (leftover D).card ≤ (graph.edgeFinset \ U).card := by
    apply Finset.card_le_card_of_injOn sym
    · intro e he
      have ⟨ee, hn⟩ := Finset.mem_filter.mp he
      refine Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr (edgesAdj ⟨e, ee⟩), ?_⟩
      intro hu
      exact (hit _ _ hu).elim hn.1 hn.2
    · intro e he f hf h
      exact symInjective ⟨e, (Finset.mem_filter.mp he).1⟩ ⟨f, (Finset.mem_filter.mp hf).1⟩ h
  have h16 : graph.edgeFinset.card = 16 := by decide +kernel
  have hsplit := Finset.card_sdiff_add_card_eq_card hU
  omega
end Profile2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264
open PEqualNP.EdgeOwnership
open UsefulJunk2264 (hits safe prod nb trimRep safe_triple)
open Profile2264 (graph)
abbrev Vertex := Fin 11
abbrev EdgeRow := Fin 16
def edgeRow : EdgeRow → Vertex × Vertex :=
  ![(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def enc {w : ℕ} (f : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem enc_get {w : ℕ} (f : Fin w → Bool) (i : Fin w) : (enc f).getLsbD i.val = f i := by
  simp only [enc, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
def subsetOf (a b : Mask) : Bool := (a &&& b) == a
def vertexMask (A : Finset Vertex) : Mask :=
  BitVec.ofNat 16 (enc (fun i : Vertex => decide (i ∈ A))).toNat
def twow (w s : Vertex) : Mask :=
  BitVec.ofNat 16 ((2^w.val) ||| (2^s.val))
def pairCandidates : List (Mask × Mask) :=
  (List.finRange 11).flatMap (fun w => (submasks 11 (neighbors w).toNat).flatMap fun b =>
    (List.finRange 11).filterMap fun s => if b.testBit s.val then some (twow w s, BitVec.ofNat 16 b) else none) ++
  (List.finRange 16).flatMap fun i => [edgeRow i,(edgeRow i).swap].flatMap fun pair =>
    let w := pair.1
    let z := pair.2
    ((submasks 11 (neighbors z).toNat).filter (fun a => a.testBit w.val)).flatMap fun a =>
      ((submasks 11 (neighbors w).toNat).filter (fun b => b.testBit z.val)).map fun b =>
        (BitVec.ofNat 16 a,BitVec.ofNat 16 b)
abbrev AtlasRow := Mask × Mask × Mask × Nat × Bool × Nat
-- Each entry stores the guard mask, eleven 7-bit witnesses, and a target code.
private def atlasTags : Array (Array Nat) := #[
  #[
    0xd9b0000d80366cd9b001a1, 0x10000000000000000000600, 0x100000000000000000007ff, 0x2efdfc7801e007701dc0055,
    0x300000000000000000007ff, 0x3183000c183000c18306110, 0x4780003c78f1e3c00f1e304, 0x500000000000000000007ff,
    0x50060c183000c183060c420, 0x6e7e3c7301cc07301cc0055, 0x700000000000000000007ff, 0x748912000091224489120c0,
    0x8c003060c000060c0030232, 0x900000000000000000007ff, 0x900c003060c183060018502, 0xadfbfb6f01bc06f01bc0055
  ],
  #[
    0xadfbfc6f01bc06f01bc0055, 0xaede3b7601e007601e00055, 0xb00000000000000000007ff, 0xb780003c78f1e3c00f1e304,
    0xc0060c183000c183060c420, 0xd00000000000000000007ff, 0xd0122400912240091224488, 0xec000f1e3c0001e3c00f232,
    0xec002d5ab40005ab402d232, 0xec003060c000060c0030232, 0xf00000000000000000007ff, 0xfa802a540152a00a952a248,
    0x10d87c0003e00f9f3e7c01a1, 0x10d994000ca032e5cb9401a1, 0x10d9b0000d80366cd9b001a1, 0x1100000000000000000007ff
  ],
  #[
    0x11c003060c000060c0030232, 0x12a802a540152a00a952a248, 0x1300000000000000000007ff, 0x13d9b0000d80366cd9b001a1,
    0x14e3c78f501c407101c40055, 0x14e3c78f801c407101c40055, 0x14ebe3af501d407801d40055, 0x1500000000000000000007ff,
    0x15f1e3c7801e007801e00055, 0x160122400912240091224488, 0x18cd98000d203366cd9801a1, 0x18cd98000d803366cd9801a1,
    0x18d9a4000d2034ecd3a401a1, 0x1a00c003060c183060018502, 0x1a00d403162c58b16a018d02, 0x1a019c03b76eddbbce01dd02
  ],
  #[
    0x1c2000010204189000408304, 0x1c20000102041e1000408304, 0x1c700003870e1db800e1c304, 0x1c700003870e1e3800e1c304,
    0x1c780003162c58b100f18b04, 0x1c780003b76eddbb00f1db04, 0x1c780003c78f1e3c00f1e304, 0x1e28500002801a94285001a1,
    0x1e28500002803614285001a1, 0x1ec990000c8033e4c99001a1, 0x1ec990000c803664c99001a1, 0x1ed8d40006a01ab56bb001a1,
    0x1ed99c000ce033e7cfb001a1, 0x200000000000000000000600, 0x2278000050a1428500142b04, 0x2278000376eddbb700ddbb04
  ],
  #[
    0x22780003c78f1e3c00f1e304, 0x227c000376eddbb700ddbb04, 0x22a4000050a1428500142b04, 0x24a4026cd01366809b366a48,
    0x24a402a52014a900a94a9248, 0x24a8026cd01366809b366a48, 0x24a802a540152a00a952a248, 0x26aa00408100000810004232,
    0x26aa02ad5c000060aa02aa32, 0x26be02c58b000058b002c232, 0x26be02fdfc000060be02fa32, 0x26c000408100000810004232,
    0x26c002c58b000058b002c232, 0x280000000000000000000600, 0x2a0060b162c00b162c58b420, 0x2a0060c183000c183060c420
  ],
  #[
    0x2c00b802c58b162c58016502, 0x2c00b802e5cc172e5c017502, 0x2c00c002c58b162c58016502, 0x2c00c003060c183060018502,
    0x2e0112100850a100850a1488, 0x2e0112200891a20089122488, 0x2e0112200892220089122488, 0x2e011a100850a100850a1488,
    0x2e011a4008d1a3008d223488, 0x2e0122100850a100850a1488, 0x308202bc1010404101040255, 0x308203141010404101040255,
    0x30ae02bd7015c062015c0255, 0x30e603af301cc07301cc0255, 0x30e603b7301cc07301cc0255, 0x30ea03af501d407601d40255
  ],
  #[
    0x32c403162000006200000277, 0x32ec03b76000007600000277, 0x34ae02bd7015c000015c025d, 0x34ea03af501d400001d4025d,
    0x368200041010404101040355, 0x36e60007301cc07301cc0355, 0x38007c0003e00f9f3e7c05a1, 0x3800d40006a01ab56b2c05a1,
    0x380194000ca032e5cb9405a1, 0x38019c000ce033e7cfa405a1, 0x3a012c0009602580972c05a9, 0x3a01a4000d203480d3a405a9,
    0x3c00d40006a01ab56a0005a3, 0x3c019c000ce033e7ce0005a3, 0x3ec403162000006200000277, 0x3eec03b76000007600000277
  ],
  #[
    0x4000d40006a01ab56a0005a3, 0x40019c000ce033e7ce0005a3, 0x42000003162c58b100018f06, 0x42000003b76eddbb0001df06,
    0x44c5b7162000006201b40075, 0x44eddfb76000007601dc0075, 0x46dbb4000000006d01b401f5, 0x46efdc000000007701dc01f5,
    0x48c403162000006200000277, 0x48ec03b76000007600000277, 0x4a00000050a1428500142f04, 0x4a000003162c58b1011d8f04,
    0x4a00000376eddbb700ddbf04, 0x4a000003b76eddbb00f5df04, 0x4c00000007af5e8000f5ef8c, 0x4c00000008f1e380011e3f8c
  ],
  #[
    0x4e000003162c58b100018f06, 0x4e000003b76eddbb0001df06, 0x50ae02bd7015c000015c025d, 0x50ea03af501d400001d4025d,
    0x52012c0009602580972c05a9, 0x5201a4000d203480d3a405a9, 0x54183000c183000c18306110, 0x542050010204001028408110,
    0x54719003870e0038c8e1c110, 0x562a54015005401500540155, 0x5683b4041010404101040155, 0x56dfbc06f01bc06f01bc0155,
    0x56e7dc07301cc07301cc0155, 0x5828500002800014285001b1, 0x58c990000c800064c99001b1, 0x5adbb4000000006d01b401f5
  ],
  #[
    0x5aefdc000000007701dc01f5, 0x5c2000010204001000408314, 0x5c700003870e003800e1c314, 0x5e8200041010404101040355,
    0x5ee60007301cc07301cc0355, 0x600036c0b162c00b162c5c10, 0x600036d0d1a4400d1a346c10, 0x600046c0b162c00b162c5c10,
    0x60005c401020400102040c10, 0x60005cf172f0c0172e5cbc10, 0x60010c401020400102040c10, 0x620000408100000810004632,
    0x620000f1e3c0001e3c00f632, 0x620002c58b000058b002c632, 0x620002d5ab40005ab402d632, 0x64003400b162c00b162c5d10
  ],
  #[
    0x64003400d1a4400d1a346d10, 0x64004400b162c00b162c5d10, 0x64005c001020400102040d10, 0x64005c0172f0c0172e5cbd10,
    0x64010c001020400102040d10, 0x660046f00224400022448c98, 0x66010e500870c000870e1c98, 0x6800025009400000940256ba,
    0x680002f00bc00000bc02f6ba, 0x6a0044000224400022448d98, 0x6a010c000870c000870e1d98, 0x6c0036d0d1a0000d1a346c30,
    0x6c005cf172e000172e5cbc30, 0x6e003400d1a0000d1a346d30, 0x6e005c0172e000172e5cbd30, 0x700000401020400102040e10
  ],
  #[
    0x700002c0b162c00b162c5e10, 0x720000001020400102040f10, 0x72000000b162c00b162c5f10, 0x74283400d1a0170d1a346920,
    0x74283400d1a0328d1a346920, 0x74c85c0172e00d172e5cb920, 0x74c85c0172e00f972e5cb920, 0x74d86801a3400d1a347cd120,
    0x74d8b802e5c0172e5d957120, 0x76003400d1a0170d1a346d20, 0x76003400d1a0328d1a346d20, 0x76005c0172e00d172e5cbd20,
    0x76005c0172e00f972e5cbd20, 0x76006801a3400d1a347cd520, 0x7600b802e5c0172e5d957520, 0x78007c0003e00f9f3e7c05a1
  ],
  #[
    0x780194000ca032e5cb9405a1, 0x7a006801a3400d1a3400d522, 0x7a00b802e5c0172e5c017522, 0x7c00d40006a01ab56a0005a3,
    0x7c019c000ce033e7ce0005a3, 0x7e283400d1a0000d1a346930, 0x7ec85c0172e000172e5cb930, 0x8028500002800014285001b1,
    0x80c990000c800064c99001b1, 0x82003400d1a0000d1a346d30, 0x82005c0172e000172e5cbd30, 0x84aa00102040010204081220,
    0x84aa027cfb4027da9f3e7a20, 0x84be00b162c00b162c58b220, 0x84be00e9d3c00e9e3a74ea20, 0x84c000102040010204081220
  ],
  #[
    0x84c000b162c00b162c58b220, 0x860000102040010204081620, 0x860000b162c00b162c58b620, 0x860000e9d3c00e9e3a74ee20,
    0x8600027cfb4027da9f3e7e20, 0x880000f1e3c0001e3c00f632, 0x880002d5ab40005ab402d632, 0x8aaa027cf00027809f3e7a68,
    0x8abe00e9d0000e803a74ea68, 0x8caa02ad50000000aa02aa7a, 0x8cbe02fdf0000000be02fa7a, 0x8e0000e9d0000e803a74ee68,
    0x8e00027cf00027809f3e7e68, 0x900000102040010204081620, 0x900000b162c00b162c58b620, 0x920000408100000810004632
  ],
  #[
    0x920002c58b000058b002c632, 0x9448912000091224489120c0, 0x9656ad58000ac02b00ac00d5, 0x96e3c788001c407101c400d5,
    0x9854a8000000152a54a801e1, 0x98cd980000003366cd9801e1, 0x9adbb4000000006d01b401f5, 0x9aefdc000000007701dc01f5,
    0x9c0064187000c183060c1c40, 0x9c0064c9d00bcc993264cc40, 0x9c008d0cd00850a142850c40, 0x9c008d1cf00951a3468d1c40,
    0x9c00950cd00850a142850c40, 0x9c00bc187000c183060c1c40, 0x9e0000387001c3800e1c3e48, 0x9e0000e9d00cce803a74ee48
  ],
  #[
    0x9e00026cd01366809b366e48, 0x9e00027cf01467809f3e7e48, 0xa00064180000c183060c1cc0, 0xa00064c8000bcc993264ccc0,
    0xa0008d08000850a142850cc0, 0xa0008d18000951a3468d1cc0, 0xa0009508000850a142850cc0, 0xa000bc180000c183060c1cc0,
    0xa2009405100952a54a012d42, 0xa200bc03300bd7af5e017d42, 0xa4000003300cd98066019f4a, 0xa400000510146880a2028f4a,
    0xa6009400000952a54a012dc2, 0xa600bc00000bd7af5e017dc2, 0xa80064c9d0000c993264cc60, 0xa8008d1cf00011a3468d1c60
  ],
  #[
    0xaa0000e9d0000e803a74ee68, 0xaa00027cf00027809f3e7e68, 0xac0064c800000c993264cce0, 0xac008d18000011a3468d1ce0,
    0xae0000187000c183060c1e40, 0xae00010cd00850a142850e40, 0xb00000180000c183060c1ec0, 0xb0000108000850a142850ec0,
    0xb24c0108084850a142850a80, 0xb24c014808e9932652993280, 0xb2520108084850a142850a80, 0xb274001800c0c183060c1a80,
    0xb27402d807ae9d3ab6e9d280, 0xb2b6001800c0c183060c1a80, 0xb400003000c183000c183688, 0xb40002100850a100850a1688
  ],
  #[
    0xb400025008f1e380951e3e88, 0xb40002f007af5e80bcf5ee88, 0xb64c0108000850a142850ac0, 0xb64c014800099326529932c0,
    0xb6520108000850a142850ac0, 0xb67400180000c183060c1ac0, 0xb67402d8000e9d3ab6e9d2c0, 0xb6b600180000c183060c1ac0,
    0xb85201480940002952014ab2, 0xb8b602d80bc0005bb602dab2, 0xba00025009400000940256ba, 0xba0002f00bc00000bc02f6ba,
    0xbc5201480000002952014af2, 0xbcb602d80000005bb602daf2, 0xbe4c000008e9932600993384, 0xbe74000007ae9d3a00e9d384
  ],
  #[
    0xc000000007af5e8000f5ef8c, 0xc000000008f1e380011e3f8c, 0xc24c000000099326009933c4, 0xc2740000000e9d3a00e9d3c4,
    0xc400001800c0c183060c1e80, 0xc4000108084850a142850e80, 0xc60000180000c183060c1ec0, 0xc6000108000850a142850ec0,
    0xc8200000b162d60b162c5b00, 0xc8200000b162db8b162c5b00, 0xc82000010204189024408300, 0xc820000102041e1024408300,
    0xc8240000b162d60b162c5b00, 0xc8240000b162db8b162c5b00, 0xc87000001020420102040b00, 0xc87000001020428102040b00
  ],
  #[
    0xc8700003870e1db89ce1c300, 0xc8700003870e1e389ce1c300, 0xc87800004081020408142300, 0xc8780002c58b162c58dd6300,
    0xc8780003162c58b166f18b00, 0xc8780003b76eddbba2f1db00, 0xc87c0002c58b162c58dd6300, 0xc89c00001020420102040b00,
    0xc89c00001020428102040b00, 0xc8a400004081020408142300, 0xca0000004081020408002702, 0xca000002c58b162c58016702,
    0xca000003162c58b166018f02, 0xca000003b76eddbba201df02, 0xcc200000b162c00b162c5b10, 0xcc2000010204001024408310
  ],
  #[
    0xcc240000b162c00b162c5b10, 0xcc7000001020400102040b10, 0xcc700003870e00389ce1c310, 0xcc9c00001020400102040b10,
    0xce2400012004998024489348, 0xce24000120049f0024489348, 0xce7c0003300cd98066f99b48, 0xce9c0004e013a8809d3a7348,
    0xce9c0004e013a9009d3a7348, 0xcea4000510146880a34a8b48, 0xd07c0003e00f9f0000f9f34c, 0xd0a400052014a900014a934c,
    0xd2000003300cd98066019f4a, 0xd200000510146880a2028f4a, 0xd42400012004800024489358, 0xd49c0004e01380009d3a7358
  ],
  #[
    0xd6000003162c58b100018f06, 0xd6000003b76eddbb0001df06, 0xd82000010204001000408314, 0xd8700003870e003800e1c314,
    0xda0000001020420102040f00, 0xda0000001020428102040f00, 0xda0000004081020408142700, 0xda000000b162d60b162c5f00,
    0xda000000b162db8b162c5f00, 0xda000002c58b162c58dd6700, 0xdc00000050a1428500142f04, 0xdc00000376eddbb700ddbf04,
    0xde0000001020400102040f10, 0xde000000b162c00b162c5f10
  ]
]

private def unpackAtlasRefs : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, n => (n % 512) :: unpackAtlasRefs k (n >>> 9)

private def atlasRefs : List Nat := ([
  0xc0504008078310c11060410c28062184005108a43616048185013060b4400e018005023, 0x150a5c22c148adc22314b842c0b12085c22610895c22810b84360b0e860281e0c8742823,
  0x1c8c85a861e0d45a3a19a183c361c8b50c3c168e90c23190b50c35168cd0c1316a181c05, 0x2490c7e3d251108049228f49446260fc7a191b1307a20218fc7a44201147a1b1f8f42601,
  0x2a1409c4d2a9449e5729134b0532a1389a56279649a16281389a51279489a0e271341001, 0x2e97cbc612e98cca021108844221108844022d088b8222d888c0222d088c422320880402,
  0x341a4d06b341b4d0021389c4e271389c4e023309cce273309cd4273309cd8273309c0402, 0x1687c5e1f1687ce21f1687ce61f1687c0804061b81804068341a0406034de0d060340804,
  0x3a9dcf2070904824073a048ec123c0480e07168b85a70169c85a040f87c3e1f0f87c3e04, 0x3e1f4f87e3e204f8071389c4e271389c4e073d09cf6273d09cfe273d09d00273d09c0e07,
  0x14a10520a0d068340a148690a1a14868140a10a08420a0a8542a0a10855061510854140a, 0x432250c1f44229101f432250c1f4723d1c1f432250c1f4924d241f432250c1f068341a0d,
  0x4321d0c8d432450c0d45a31169045a51160d4321d0c8d432450c0d0f87c3e1f0f87c3e0d, 0x4c26d44274ca7146274d26d48275329d54274c26d4427562715c2757a6d6227068341a0d,
  0x4aa592ea54aaad600d4ea793aa84ea793a0d4fa8142a94fab5640d1389c4e271389c4e0d, 0x598dd721f5c0ed7c1f5a0e1741f0e879801f598dd721f6130d841f62b1d921f090482412,
  0x5aadd6c1c5ab058c121c8f0741e1cb1190125daf578bf5db0594120f87c3e1f0f87c3e12, 0x6591da22266121a8226792da2220c065ac226591da2226bb65b8226eb7da222090482412,
  0x66b39a01766b61bc1224928981924b69c0126934da4d56936da412110884422110884412, 0x70b91c21571b9dc61570b91c2150d068341570b89c21a72b99ca1a70b89c21a0a8542a15,
  0x743b9e42774bbde62776bb9ee277cbe9fa27743b9e4277f4020427823ba0c270a8542a15, 0x753add8f8753fe0a15783c5e0fb78405e0157a3d5ecfc7a40e0e151389c4e271389c4e15,
  0x85c3a2a22864462c2286c3a2e228cc6e3a2285c3a2a228fc8246229243a4c220d068341a, 0x8442615188447a4a1a87c421f1a87c861e1a8944e291c8948a4e1a11088442211088441a,
  0x974ca5e3e974ea8222190d4663619546a622aa55aab5aaa4eab8220f87c3e1f0f87c3e1f, 0x974ca5e3e974ea8222984d66240984f684229bce670429bcea8622a3d26914ba3d369e22,
  0x944aa5944940c2ae1f9dcf2774c9dd42761f9f4fe814e9f54aba1f11088442211088441f, 0x944aa5944940c2ae1f99cd26d46998d2b21f94cae5b45948c6b01f1f900834a1f8dab61f
]).flatMap (unpackAtlasRefs 32)

def atlas : List AtlasRow := pairCandidates.zipWith (fun (a,b) i =>
    let code := (atlasTags[i / 16]!)[i % 16]!
    (a,b,BitVec.ofNat 16 (code % 2048), (code >>> 11) % (2^77), code.testBit 88, code >>> 89))
  atlasRefs

def first (r : AtlasRow) : Mask := r.1
def second (r : AtlasRow) : Mask := r.2.1
def guards (r : AtlasRow) : Mask := r.2.2.1
def witnesses (r : AtlasRow) : Nat := r.2.2.2.1
def targetStar (r : AtlasRow) : Bool := r.2.2.2.2.1
def targetIndex (r : AtlasRow) : Nat := r.2.2.2.2.2
def witness (r : AtlasRow) (w : Vertex) : Vertex × Vertex :=
  let val := (witnesses r >>> (7*w.val)) % 128
  (Fin.ofNat 11 (val / 11),Fin.ofNat 11 (val % 11))
def productiveMask (r : AtlasRow) : Mask :=
  incidentOf (first r) &&& incidentOf (second r) &&& incidentOf (guards r)
def valid (r : AtlasRow) : Bool :=
  ((List.finRange 11).all fun w =>
    (guards r).getLsbD w.val ||
      let (a,b) := witness r w
      (first r).getLsbD a.val && (second r).getLsbD b.val &&
      !(neighbors a).getLsbD b.val && !(neighbors w).getLsbD a.val && !(neighbors w).getLsbD b.val) &&
  if targetStar r then subsetOf (productiveMask r) (incident (Fin.ofNat 11 (targetIndex r)))
  else let s := sigAt (Fin.ofNat 112 (targetIndex r))
    subsetOf (guards r) s.1 && subsetOf (productiveMask r) s.2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem atlasComplete : atlas.map (fun r => (first r,second r)) = pairCandidates := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem atlasValid : atlas.all valid = true := by decide +kernel
end LowTop2264

end PEqualNP.Outside.L_meta_2264

-- OR traces and circuit evaluation follow L-meta-1490.
namespace PEqualNP.Outside.L_meta_2264.Local1490
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k
lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩
open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h
lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
open PEqualNP.EdgeOwnership
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3
lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega
lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
open PEqualNP.CleanedNonEdge
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
end PEqualNP.Outside.L_meta_2264.Local1490

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
theorem pureOrVal (hAO : IsAO2 n C) {w : ℕ}
    (hp : ∀ h, OrReaches n C w h → (gateAt C h).op ≠ GateOp.and)
    (x : Fin n → Bool) : val C (List.ofFn x) w = true ↔
      ∃ t ∈ orIn n C w, x t = true := by
  constructor
  · intro hv
    obtain ⟨w', hr, hv', h'⟩ := or_trace (n := n) (x := List.ofFn x) (by simp) w hv
    rcases h' with htn | ⟨h, hh, rfl, hop⟩
    · refine ⟨⟨w', htn⟩, reach_mem_orIn ⟨w', htn⟩ hr, ?_⟩
      rw [← val_ofFn C x ⟨w', htn⟩]
      exact hv'
    · exact (hp h (reach_orReaches hr h rfl hh)
        ((hAO.1 _ (gateAt_mem hh)).resolve_right hop)).elim
  · rintro ⟨t, ht, hxt⟩
    exact reach_var_val x w t (mem_orIn_reach t ht) hxt
theorem pureJunkOperand (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁}) (h₀₁ : ¬ InCone n C j₀ j₁)
    (h₁₀ : ¬ InCone n C j₁ j₀) {a : ℕ} (ha : a ∈ junk G C) {b : Fin 2} :
    ∀ h, OrReaches n C (opnd C a b) h → (gateAt C h).op ≠ GateOp.and := by
  intro h hr hop
  obtain ⟨hal, hao, _⟩ := junkData ha
  have hh := operandOrAndJunk hAO hT hal hao hr hop
  have hlt := operandReachLt hAO hal hr
  have hc := operandReachCone hAO hal hr
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at ha hh
  rcases ha with rfl | rfl <;> rcases hh with rfl | rfl
  · exact (Nat.lt_irrefl _ hlt)
  · exact h₁₀ hc
  · exact h₀₁ hc
  · exact (Nat.lt_irrefl _ hlt)
theorem eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
theorem pureOppositeOperand (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a) {a j : ℕ}
    (ha : a ∈ tops G C) {b : Fin 2} (hr : OrReaches n C (opnd C a b) j)
    (hj : j = j₀ ∨ j = j₁) :
    ∀ h, OrReaches n C (opnd C a (1 - b)) h → (gateAt C h).op ≠ GateOp.and := by
  intro h hr' hop
  obtain ⟨hal, hao, hab⟩ := topData ha
  have hh := operandOrAndJunk hAO hT hal hao hr' hop
  have hc := operandReachCone hAO hal hr
  have hc' := operandReachCone hAO hal hr'
  have he : h = j := by
    have hm : h = j₀ ∨ h = j₁ := by
      simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using hh
    rcases hj with rfl | rfl <;> rcases hm with rfl | rfl
    · rfl
    · exact (hsep a ha hc hc').elim
    · exact (hsep a ha hc' hc).elim
    · rfl
  subst h
  obtain ⟨_, _, x, hx, hfx⟩ := junkData hh
  have hv : gateVal n C a x = true := (andValOperands hAO hal hao x).mpr (fun c => by
    rcases eitherOperand b c with rfl | rfl
    · exact reachVal hr hx
    · exact reachVal hr' hx)
  rw [hab x hv] at hfx
  contradiction
theorem oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
theorem ustarAttaches (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    {u v : Fin n} {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) (hj : j = j₀ ∨ j = j₁)
    (hv : gateVal n C a (pairInput u v) = true) :
    (u ∈ side (n := n) C a (1 - b) ∨ v ∈ side (n := n) C a (1 - b)) ∧
      side (n := n) C a (1 - b) ⊆ wmax G C j := by
  refine ⟨?_, oppositeSideWmax hAO ha hr⟩
  obtain ⟨hal, hao, _⟩ := topData ha
  have h := (andValOperands hAO hal hao _).mp hv (1 - b)
  obtain ⟨t, ht, hx⟩ := (pureOrVal hAO (pureOppositeOperand hAO hT hs hsep ha hr hj) _).mp h
  rcases (pairInput_true u v t).mp hx with rfl | rfl
  · exact Or.inl ht
  · exact Or.inr ht
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
theorem orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
theorem orInOr (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) :
    orIn n C (n + m) = side C m 0 ∪ side C m 1 := by
  ext x
  constructor
  · intro hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hst, hrem⟩
    · have := x.isLt
      omega
    · obtain ⟨k, hk, he, _, hz, _⟩ := hst
      have e : k = m := by omega
      subst k
      obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hm hz
      have hx' := reach_mem_orIn x hrem
      apply Finset.mem_union.mpr
      fin_cases b
      · exact Or.inl hx'
      · exact Or.inr hx'
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 0)) hx
    · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 1)) hx
theorem orInAnd {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hs, _⟩
  · have := x.isLt
    omega
  · obtain ⟨k, _, he, hk, _, _⟩ := hs
    have e : k = j := by omega
    subst k
    rw [hop] at hk
    contradiction
theorem reachTrans {w m j : ℕ}
    (hwm : OrReaches n C w m) (hmj : OrReaches n C (n + m) j) :
    OrReaches n C w j :=
  reach_orReaches ((orReaches_reach m _ hwm).1.trans (orReaches_reach j _ hmj).1) j rfl
    (orReaches_reach j _ hmj).2
theorem orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
theorem mixingNotLam {m : ℕ} (hm : m ∈ mixing G C) : m ∈ orN G C \ lam G C := by
  rcases Finset.mem_filter.mp hm with ⟨hm, hmix⟩
  refine Finset.mem_sdiff.mpr ⟨hm, ?_⟩
  intro hl
  rcases Finset.mem_filter.mp hl with ⟨_, h0, h1, _⟩
  apply hmix
  simp only [← Finset.not_nonempty_iff_eq_empty, h0, h1]
theorem mixingAlong (hAO : IsAO2 n C) {w j : ℕ} (hr : OrReaches n C w j)
    (hj : (gateAt C j).op = GateOp.and) (hw : (orIn n C w).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C w m ∧ OrReaches n C (n + m) j ∧
      (orIn n C (n + m)).Nonempty := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rcases (orReaches_iff n C k j).mp hr with ⟨hk, rfl | ⟨hop, z, hz, hzb, hr'⟩⟩
    · rw [orInAnd hj] at hw
      exact (Finset.not_nonempty_empty hw).elim
    · obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hk hz
      by_cases hzb' : (side (n := n) C k b).Nonempty
      · obtain ⟨m, hm, hrm, hjm, hnon⟩ := ih _ hzb hr' hzb'
        exact ⟨m, hm, (orReaches_iff n C k m).mpr ⟨hk, Or.inr ⟨hop, _, hz, hzb, hrm⟩⟩,
          hjm, hnon⟩
      · have hempty : side (n := n) C k b = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hzb'
        have hboth : (side (n := n) C k 0 ∪ side (n := n) C k 1).Nonempty :=
          orInOr hAO hk hop ▸ hw
        have hm : k ∈ mixing G C := by
          refine Finset.mem_filter.mpr ⟨orNOfRaw hk hop hw, ?_⟩
          change (side (n := n) C k 0 = ∅) ≠ (side (n := n) C k 1 = ∅)
          fin_cases b
          · change side (n := n) C k 0 = ∅ at hempty
            have h1 : side (n := n) C k 1 ≠ ∅ := by
              rwa [hempty, Finset.empty_union, Finset.nonempty_iff_ne_empty] at hboth
            simp [hempty, h1]
          · change side (n := n) C k 1 = ∅ at hempty
            have h0 : side (n := n) C k 0 ≠ ∅ := by
              rwa [hempty, Finset.union_empty, Finset.nonempty_iff_ne_empty] at hboth
            simp [hempty, h0]
        exact ⟨k, hm, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hr, hw⟩
theorem edgeSlice (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    {u v : Fin n} {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) (hj : j = j₀ ∨ j = j₁)
    (hv : gateVal n C a (pairInput u v) = true) (he : s(u, v) ∈ Ustar G C)
    (hnc : a ∉ centreless G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧ OrReaches n C (n + m) j ∧
      ∃ y ∈ wmax G C j, (y = u ∨ y = v) ∧
        (orIn n C (n + m)).Nonempty ∧
        ∀ x ∈ orIn n C (n + m), G.Adj x y ∧ x ≠ u ∧ x ≠ v := by
  have hjm : j ∈ junk G C := by
    rw [hs, Finset.mem_insert, Finset.mem_singleton]
    exact hj
  have hb : (side (n := n) C a b).Nonempty := by
    by_contra h
    have h' := Finset.not_nonempty_iff_eq_empty.mp h
    apply hnc
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl h'
    · exact Or.inr h'
  obtain ⟨m, hm, hrm, hjm', hnon⟩ :=
    mixingAlong (G := G) hAO hr (junkData hjm).2.1 hb
  obtain ⟨hy, hW⟩ := ustarAttaches hAO hT hs hsep ha hr hj hv
  have hguard : ∃ y ∈ side (n := n) C a (1 - b), y = u ∨ y = v := by
    rcases hy with hy | hy
    · exact ⟨u, hy, Or.inl rfl⟩
    · exact ⟨v, hy, Or.inr rfl⟩
  obtain ⟨y, hys, hyu⟩ := hguard
  refine ⟨m, hm, hrm, hjm', y, hW hys, hyu, hnon, ?_⟩
  intro x hx
  have hxs := orInTrans (orReaches_reach m _ hrm).1 hx
  have hadj : G.Adj x y := by
    fin_cases b
    · exact hstar a ha x hxs y hys
    · exact (hstar a ha y hys x hxs).symm
  refine ⟨hadj, ?_⟩
  have hne : x ≠ y := fun hxy => G.irrefl (hxy ▸ hadj)
  have ns : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp he).2
  have cross : s(x, y) ∈ starEdges G C := by
    unfold starEdges
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, y), Finset.mem_product.mpr ⟨hxs, hys⟩, rfl⟩
    · exact ⟨(y, x), Finset.mem_product.mpr ⟨hys, hxs⟩, Sym2.eq_swap⟩
  rcases hyu with rfl | rfl
  · refine ⟨hne, ?_⟩
    intro h
    subst x
    rw [Sym2.eq_swap] at cross
    exact ns cross
  · refine ⟨?_, hne⟩
    intro h
    subst x
    exact ns cross
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem junkVal (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁}) (h₀₁ : ¬ InCone n C j₀ j₁)
    (h₁₀ : ¬ InCone n C j₁ j₀) {a : ℕ} (ha : a ∈ junk G C) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      (∃ t ∈ side (n := n) C a 0, x t = true) ∧ (∃ t ∈ side (n := n) C a 1, x t = true) := by
  obtain ⟨hal, hao, _⟩ := junkData ha
  rw [andValBoth hAO hal hao, pureOrVal hAO (pureJunkOperand hAO hT hs h₀₁ h₁₀ ha) x,
    pureOrVal hAO (pureJunkOperand hAO hT hs h₀₁ h₁₀ ha) x]
  rfl
theorem graphFunThree {u v w : Fin n} :
    graphFun G ∅ (fun t => decide (t = u ∨ t = v ∨ t = w)) = true ↔
      G.Adj u v ∨ G.Adj u w ∨ G.Adj v w := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, (rfl | rfl | rfl), (rfl | rfl | rfl)⟩
    · exact (G.irrefl hab).elim
    · exact Or.inl hab
    · exact Or.inr (Or.inl hab)
    · exact Or.inl hab.symm
    · exact (G.irrefl hab).elim
    · exact Or.inr (Or.inr hab)
    · exact Or.inr (Or.inl hab.symm)
    · exact Or.inr (Or.inr hab.symm)
    · exact (G.irrefl hab).elim
  · rintro (h | h | h)
    · exact ⟨u, v, h, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨u, w, h, Or.inl rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨v, w, h, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
theorem junkWmax (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁}) (h₀₁ : ¬ InCone n C j₀ j₁)
    (h₁₀ : ¬ InCone n C j₁ j₀) {a : ℕ} (ha : a ∈ junk G C) (w : Fin n) :
    w ∈ wmax G C a ↔ ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1,
      G.Adj u v ∨ G.Adj u w ∨ G.Adj v w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h u hu v hv
    let x : Fin n → Bool := fun t => decide (t = u ∨ t = v ∨ t = w)
    have hx : gateVal n C a x = true := (junkVal hAO hT hs h₀₁ h₁₀ ha x).mpr
      ⟨⟨u, hu, by simp [x]⟩, ⟨v, hv, by simp [x]⟩⟩
    exact graphFunThree.mp (h x hx (by simp [x]))
  · intro h x hx hw
    obtain ⟨⟨u, hu, hxu⟩, ⟨v, hv, hxv⟩⟩ := (junkVal hAO hT hs h₀₁ h₁₀ ha x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    rcases h u hu v hv with hadj | hadj | hadj
    · exact ⟨u, v, hadj, hxu, hxv⟩
    · exact ⟨u, w, hadj, hxu, hw⟩
    · exact ⟨v, w, hadj, hxv, hw⟩
theorem orInRaw {w : ℕ} (hw : w < n) : orIn n C w = {⟨w, hw⟩} := by
  ext x
  constructor
  · intro hx
    apply Finset.mem_singleton.mpr
    apply Fin.ext
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with h | ⟨_, hs, _⟩
    · exact h.symm
    · obtain ⟨k, _, rfl, _⟩ := hs
      omega
  · intro hx
    have he := Finset.mem_singleton.mp hx
    subst x
    exact reach_mem_orIn ⟨w, hw⟩ (Relation.ReflTransGen.refl)
theorem allTrueWire (hAO : IsAO2 n C) : ∀ w < n + C.gates.length,
    val C (List.ofFn fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hraw : w < n
    · exact val_ofFn C (fun _ => true) ⟨w, hraw⟩
    · obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
      have hm : m < C.gates.length := by omega
      rcases hAO.1 _ (gateAt_mem hm) with ha | ho
      · apply (val_and (n := n) (by simp) hm ha).mpr
        intro z hz
        have hzlt := hAO.2.1 m hm z hz
        exact ⟨hzlt, ih z hzlt (by omega)⟩
      · apply (val_or (n := n) (by simp) hm ho).mpr
        have hz := opndBound hAO hm 0
        exact ⟨opnd C m 0, opndMem hAO hm 0, hz, ih _ hz (by omega)⟩
theorem pureOrNonempty (hAO : IsAO2 n C) {w : ℕ} (hw : w < n + C.gates.length)
    (hp : ∀ h, OrReaches n C w h → (gateAt C h).op ≠ GateOp.and) :
    (orIn n C w).Nonempty := by
  obtain ⟨t, ht, _⟩ := (pureOrVal hAO hp (fun _ => true)).mp (allTrueWire hAO _ hw)
  exact ⟨t, ht⟩
theorem pureOrNotMixing (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or)
    (hp : ∀ h, OrReaches n C (n + m) h → (gateAt C h).op ≠ GateOp.and) :
    m ∉ mixing G C := by
  have hn (b : Fin 2) : (side (n := n) C m b).Nonempty := by
    have hb := opndBound hAO hm b
    apply pureOrNonempty hAO (by omega)
    intro h hr
    apply hp h
    exact (orReaches_iff n C m h).mpr ⟨hm, Or.inr ⟨hop, _, opndMem hAO hm b, hb, hr⟩⟩
  intro hmix
  have hm' := (Finset.mem_filter.mp hmix).2
  change (side (n := n) C m 0 = ∅) ≠ (side (n := n) C m 1 = ∅) at hm'
  apply hm'
  exact propext (iff_of_false (hn 0).ne_empty (hn 1).ne_empty)
theorem lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)
theorem pureSupportCharge (hAO : IsAO2 n C) {w : ℕ} (hw : w < n + C.gates.length)
    (hp : ∀ h, OrReaches n C w h → (gateAt C h).op ≠ GateOp.and)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y)
    (hcard : 1 < (orIn n C w).card)
    (hno : ¬ ∃ t : Fin n, ∀ x ∈ orIn n C w, G.Adj t x ∧ s(t,x) ∉ Ustar G C) :
    ∃ m ∈ (orN G C \ lam G C) \ mixing G C, w = n + m := by
  have hge : n ≤ w := by
    by_contra! hlt
    rw [orInRaw hlt, Finset.card_singleton] at hcard
    omega
  obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
  have hml : m < C.gates.length := by omega
  have hop : (gateAt C m).op = GateOp.or :=
    (hAO.1 _ (gateAt_mem hml)).resolve_left
      (hp m ((orReaches_iff n C m m).mpr ⟨hml, Or.inl rfl⟩))
  have hn : (orIn n C (n + m)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hmlam : m ∉ lam G C := fun hm => hno (lamAvoidsUstar hm hstar)
  exact ⟨m, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨orNOfRaw hml hop hn, hmlam⟩,
    pureOrNotMixing hAO hml hop hp⟩, rfl⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
private theorem junkNumber {p q j : ℕ} (he : junk G C = {p,q}) (h : j ∈ junk G C) : j = p ∨ j = q := by
  simpa only [he,Finset.mem_insert,Finset.mem_singleton] using h
private theorem oneJunkPerTop (hAO : IsAO2 n C) {p q a j j' : ℕ}
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (ha : a ∈ tops G C) {b b' : Fin 2}
    (r : OrReaches n C (opnd C a b) j) (r' : OrReaches n C (opnd C a b') j')
    (jNum : j = p ∨ j = q) (j'Num : j' = p ∨ j' = q) : j = j' := by
  have cone := operandReachCone hAO (topData ha).1 r
  have cone' := operandReachCone hAO (topData ha).1 r'
  rcases jNum with rfl | rfl <;> rcases j'Num with rfl | rfl
  · rfl
  · exact (apart a ha cone cone').elim
  · exact (apart a ha cone' cone).elim
  · rfl
theorem pairHitsTop (hL : IsLeastAO G C) {u v : Fin n} (he : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hL.2.1 x
  obtain ⟨a, ha, hano, path, hon⟩ :=
    edge_trace G (graphFun G ∅) (fun u v hx => (graphFun_pair G u v).mp hx)
      hout u v ((graphFun_pair G u v).mpr he)
  have hop := (hL.1.1 _ (gateAt_mem ha)).resolve_right hano
  refine ⟨a, ?_, hon⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,hop,
    fun x hx => below_of_reach _ hout a path x hx⟩
theorem centerModeBound (hAO : IsAO2 n C) (hT : TopForm G C) {p q a : ℕ}
    (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (stars : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y)
    (ha : a ∈ tops G C) {b : Fin 2} {k : Fin n} (hs : side C a b = {k}) :
    (∀ u v : Fin n, gateVal n C a (pairInput u v) = true → u = k ∨ v = k) ∨
    ∃ j, (j = p ∨ j = q) ∧
      ∀ u v : Fin n, gateVal n C a (pairInput u v) = true →
        ((u ∈ wmax G C j ∧ G.Adj k u) ∨ (v ∈ wmax G C j ∧ G.Adj k v)) ∧
        (u = k ∨ v = k ∨ gateVal n C j (pairInput u v) = true) := by
  obtain ⟨hal, hao, _⟩ := topData ha
  by_cases reaches : ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j
  · obtain ⟨j, hjMem, hr⟩ := reaches
    have hnum := junkNumber hj hjMem
    refine Or.inr ⟨j,hnum,fun u v hon => ?_⟩
    obtain ⟨hpair,hsafe⟩ := ustarAttaches hAO hT hj apart ha hr hnum hon
    have inN (x : Fin n) (hx : x ∈ side (n := n) C a (1-b)) : G.Adj k x := by
      have hk : k ∈ side (n := n) C a b := by rw [hs]; simp
      fin_cases b
      · exact stars a ha k hk x hx
      · exact (stars a ha x hx k hk).symm
    refine ⟨hpair.imp (fun h => ⟨hsafe h,inN u h⟩) (fun h => ⟨hsafe h,inN v h⟩),?_⟩
    have hb := (andValOperands hAO hal hao _).mp hon b
    rcases operand_trace u v (opnd C a b) hb with ⟨x, hx, path⟩ | ⟨h, hh, hnot, path, on⟩
    · have hxm : x ∈ side (n := n) C a b := reach_mem_orIn x path
      rw [hs,Finset.mem_singleton] at hxm
      exact hx.elim (fun e => Or.inl (e.symm.trans hxm)) (fun e => Or.inr (Or.inl (e.symm.trans hxm)))
    · have rh := reach_orReaches path h rfl hh
      have hOp := (hAO.1 _ (gateAt_mem hh)).resolve_right hnot
      have hNum := junkNumber hj (operandOrAndJunk hAO hT hal hao rh hOp)
      have heq := oneJunkPerTop hAO apart ha rh hr hNum hnum
      subst h
      exact Or.inr (Or.inr on)
  · refine Or.inl (fun u v hon => ?_)
    have pure (j : ℕ) (hr : OrReaches n C (opnd C a b) j) (op) : False :=
      reaches ⟨j, operandOrAndJunk hAO hT hal hao hr op, hr⟩
    have on := (andValOperands hAO hal hao _).mp hon b
    obtain ⟨x, hx, hv⟩ := (pureOrVal hAO pure (pairInput u v)).mp on
    change x ∈ side (n := n) C a b at hx
    rw [hs,Finset.mem_singleton] at hx
    subst x
    exact ((pairInput_true u v _).mp hv).imp Eq.symm Eq.symm
theorem centrelessModeBound (hAO : IsAO2 n C) (hT : TopForm G C) {p q a : ℕ}
    (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (ha : a ∈ centreless G C) {u v : Fin n} (hon : gateVal n C a (pairInput u v) = true) :
    ∃ j, (j = p ∨ j = q) ∧ InCone n C j a ∧ gateVal n C j (pairInput u v) = true ∧
      (u ∈ wmax G C j ∨ v ∈ wmax G C j) := by
  obtain ⟨haTop, empty⟩ := Finset.mem_filter.mp ha
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, side (n := n) C a b = ∅ :=
    empty.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  obtain ⟨hal, hao, _⟩ := topData haTop
  have on := (andValOperands hAO hal hao _).mp hon b
  rcases operand_trace u v (opnd C a b) on with ⟨x, hx, path⟩ | ⟨j, jl, jNo, path, jOn⟩
  · have trouble : x ∈ side (n := n) C a b := reach_mem_orIn x path
    simp [hb] at trouble
  · have jr := reach_orReaches path j rfl jl
    have jOp := (hAO.1 _ (gateAt_mem jl)).resolve_right jNo
    have jNum := junkNumber hj (operandOrAndJunk hAO hT hal hao jr jOp)
    obtain ⟨hw, hguard⟩ := ustarAttaches hAO hT hj apart haTop jr jNum hon
    exact ⟨j,jNum,operandReachCone hAO hal jr,jOn,
      hw.imp (fun h => hguard h) (fun h => hguard h)⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace LowTop2264
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2264.Local1490 (graphFun_pair)
open UsefulJunk2264 (hits safe prod nb trimRep safe_triple)
open Profile2264 (graph)
theorem neighborsSpec : ∀ x y : Vertex,
    (neighbors x).getLsbD y.val = decide (graph.Adj x y) := by decide +kernel
theorem incidentSpec : ∀ (x : Vertex) (e : EdgeRow),
    (incident x).getLsbD e.val = decide (x = (edgeRow e).1 ∨ x = (edgeRow e).2) := by decide +kernel
theorem rowAdjacent : ∀ e : EdgeRow, graph.Adj (edgeRow e).1 (edgeRow e).2 := by decide +kernel
private theorem rowCovers : ∀ u v : Vertex, graph.Adj u v →
    ∃ e : EdgeRow, edgeRow e = (u,v) ∨ edgeRow e = (v,u) := by decide +kernel
private theorem atMem : ∀ i : Fin 112, sigAt i ∈ signatures := by decide +kernel
private theorem maskTrue {a b : Mask} (h : subsetOf a b = true) (i : Nat)
    (on : a.getLsbD i = true) : b.getLsbD i = true := by
  unfold subsetOf at h
  have hh := beq_iff_eq.mp h
  have result := congrArg (fun x : Mask => x.getLsbD i) hh
  simpa only [BitVec.getLsbD_and,on,Bool.true_and] using result
private theorem encodedNat (A : Finset Vertex) :
    (vertexMask A).toNat = (enc (fun i : Vertex => decide (i ∈ A))).toNat := by
  rw [vertexMask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact (enc (fun i : Vertex => decide (i ∈ A))).isLt.trans (by decide)
private theorem encodedSmall (A : Finset Vertex) : (vertexMask A).toNat < 2^11 := by
  rw [encodedNat]
  exact (enc (fun i : Vertex => decide (i ∈ A))).isLt
private theorem bitEncode (A : Finset Vertex) (x : Vertex) :
    (vertexMask A).getLsbD x.val = decide (x ∈ A) := by
  change (vertexMask A).toNat.testBit x.val = _
  rw [encodedNat]
  exact enc_get (fun i : Vertex => decide (i ∈ A)) x
private theorem encodedPair : ∀ w s : Vertex, vertexMask ({w,s} : Finset Vertex) = twow w s := by
  decide +kernel
private theorem encSubset (S : Finset Vertex) (x : Vertex) (h : S ⊆ nb graph x) :
    (vertexMask S).toNat ∈ submasks 11 (neighbors x).toNat := by
  apply submaskMem 11 _ _ (encodedSmall S)
  intro i hi hv
  let j : Vertex := ⟨i,hi⟩
  change (vertexMask S).getLsbD j.val = true at hv
  rw [bitEncode] at hv
  have hh := (Finset.mem_filter.mp (h (of_decide_eq_true hv))).2
  change (neighbors x).getLsbD j.val = true
  rw [neighborsSpec, decide_eq_true hh]
private theorem repPairMem {A B : Finset Vertex} (h : trimRep graph A B) :
    (vertexMask A,vertexMask B) ∈ pairCandidates := by
  unfold trimRep at h
  rcases h with ⟨w,s,hs,rfl,sub⟩ | ⟨w,z,adj,hw,hz,hA,hB⟩
  · apply List.mem_append_left
    refine List.mem_flatMap.mpr ⟨w, List.mem_finRange _, List.mem_flatMap.mpr
      ⟨(vertexMask B).toNat, encSubset B w sub, ?_⟩⟩
    apply List.mem_filterMap.mpr
    refine ⟨s,List.mem_finRange _,?_⟩
    have bt : (vertexMask B).toNat.testBit s.val = true := by
      change (vertexMask B).getLsbD s.val = true
      rw [bitEncode,decide_eq_true hs]
    simp [bt,encodedPair]
  · apply List.mem_append_right
    obtain ⟨e, row⟩ := rowCovers w z adj
    refine List.mem_flatMap.mpr ⟨e, List.mem_finRange _, List.mem_flatMap.mpr
      ⟨(w,z), ?_, ?_⟩⟩
    · rcases row with e | e <;> simp [e]
    · refine List.mem_flatMap.mpr ⟨(vertexMask A).toNat, List.mem_filter.mpr
      ⟨encSubset A z hA, ?_⟩, List.mem_map.mpr ⟨(vertexMask B).toNat,
        List.mem_filter.mpr ⟨encSubset B w hB,?_⟩,?_⟩⟩
      · change (vertexMask A).getLsbD w.val = true
        rw [bitEncode,decide_eq_true hw]
      · change (vertexMask B).getLsbD z.val = true
        rw [bitEncode,decide_eq_true hz]
      · simp
private theorem bitOfGuard {r : AtlasRow} (h : valid r = true) {A B : Finset Vertex}
    (eA : first r = vertexMask A) (eB : second r = vertexMask B)
    {w : Vertex} (gs : safe graph A B w) : (guards r).getLsbD w.val = true := by
  have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 w (List.mem_finRange _)
  by_contra! h0
  rw [Bool.eq_false_iff.mpr h0, Bool.false_or] at hh
  let aw := (witness r w).1
  let bw := (witness r w).2
  change ((first r).getLsbD aw.val && (second r).getLsbD bw.val &&
      !(neighbors aw).getLsbD bw.val && !(neighbors w).getLsbD aw.val &&
       !(neighbors w).getLsbD bw.val) = true at hh
  simp only [eA,eB,bitEncode,neighborsSpec,Bool.and_eq_true,decide_eq_true_eq] at hh
  rcases hh with ⟨⟨⟨⟨ha,hb⟩,hab⟩,hA⟩,hB⟩
  rcases safe_triple gs ha hb with e | e | e
  · simp [e] at hab
  · simp [e] at hA
  · simp [e] at hB
theorem spreadBit (W : Mask) (e : EdgeRow) (w : Vertex)
    (hv : W.getLsbD w.val = true) (other : w = (edgeRow e).1 ∨ w = (edgeRow e).2) :
    (incidentOf W).getLsbD e.val = true := by
  have own : (incident w).getLsbD e.val = true := by rw [incidentSpec,decide_eq_true other]
  let extend (m : Mask) (k : Vertex) := if W.getLsbD k.val then m ||| incident k else m
  have monotone (m : Mask) (k : Vertex) (on : m.getLsbD e.val = true) :
      (extend m k).getLsbD e.val = true := by
    by_cases h : W.getLsbD k.val = true <;> simp [extend,h,on]
  have preserves (xs : List Vertex) (m : Mask) (on : m.getLsbD e.val = true) :
      (xs.foldl extend m).getLsbD e.val = true := by
    induction xs generalizing m with
    | nil => exact on
    | cons y ys ih => exact ih _ (monotone m y on)
  have reaches (xs : List Vertex) (m : Mask) (hx : w ∈ xs) :
      (xs.foldl extend m).getLsbD e.val = true := by
    induction xs generalizing m with
    | nil => simp at hx
    | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | rem
      · exact preserves ys _ (by simp [extend,hv,own])
      · exact ih _ rem
  exact reaches _ 0 (List.mem_finRange _)
private theorem hitOne {A : Finset Vertex} (e : EdgeRow)
    (has : hits A (pairInput (edgeRow e).1 (edgeRow e).2)) :
    (incidentOf (vertexMask A)).getLsbD e.val = true := by
  obtain ⟨w, hw, hval⟩ := has
  exact spreadBit _ _ w (by rw [bitEncode,decide_eq_true hw]) (of_decide_eq_true hval)
private theorem prodOn {r : AtlasRow} (h : valid r = true) {A B : Finset Vertex}
    (eA : first r = vertexMask A) (eB : second r = vertexMask B)
    (e : EdgeRow) (prodTrue : prod graph A B (edgeRow e).1 (edgeRow e).2) :
    (productiveMask r).getLsbD e.val = true := by
  have wg (u : Vertex) (adj : u = (edgeRow e).1 ∨ u = (edgeRow e).2) (hSafe : safe graph A B u) :
      (incidentOf (guards r)).getLsbD e.val = true :=
    spreadBit _ _ _ (bitOfGuard h eA eB hSafe) adj
  rcases prodTrue with ⟨a,b,w⟩
  simp [productiveMask,eA,eB,hitOne e a,hitOne e b,
    w.elim (wg _ (Or.inl rfl)) (wg _ (Or.inr rfl))]
theorem masksForProduct (A B : Finset Vertex)
    (h4 : PEqualNP.TopForm.NoFourCycle graph)
    (wide : ∀ c : Vertex, ∃ u v, prod graph A B u v ∧ u ≠ c ∧ v ≠ c) :
    ∃ s ∈ signatures,
      (∀ w : Vertex, safe graph A B w → s.1.getLsbD w.val = true) ∧
      ∀ e : EdgeRow, prod graph A B (edgeRow e).1 (edgeRow e).2 → s.2.getLsbD e.val = true := by
  obtain ⟨A',B',rep,gGuard,gProd⟩ := UsefulJunk2264.trim_nonstar h4 A B 0 wide
  have covered := repPairMem rep
  rw [← atlasComplete] at covered
  obtain ⟨r,hr,eq⟩ := List.mem_map.mp covered
  have ea : first r = vertexMask A' := congrArg Prod.fst eq
  have eb : second r = vertexMask B' := congrArg Prod.snd eq
  have proof := List.all_eq_true.mp atlasValid r hr
  have rest := (Bool.and_eq_true_iff.mp proof).2
  by_cases star : targetStar r = true
  · simp only [star,ite_true] at rest
    let k : Vertex := Fin.ofNat 11 (targetIndex r)
    obtain ⟨u,v,on,nu,nv⟩ := wide k
    have either : safe graph A B u ∨ safe graph A B v := on.2.2
    have adj : graph.Adj u v := (graphFun_pair graph u v).mp (either.elim
      (fun h => h _ on.1 on.2.1 (by simp [pairInput]))
      (fun h => h _ on.1 on.2.1 (by simp [pairInput])))
    obtain ⟨e,flip⟩ := rowCovers u v adj
    have switch : pairInput u v = pairInput v u := by
      funext w
      simp [pairInput,or_comm]
    have g : prod graph A B (edgeRow e).1 (edgeRow e).2 := by
      rcases flip with h | h
      · exact h ▸ on
      · rw [h]
        exact ⟨switch ▸ on.1,switch ▸ on.2.1,either.symm⟩
    have gbit := maskTrue rest e.val (prodOn proof ea eb e (gProd _ _ g))
    have c : k = (edgeRow e).1 ∨ k = (edgeRow e).2 :=
      of_decide_eq_true ((incidentSpec k e).symm.trans gbit)
    rcases flip with h | h <;> rw [h] at c
    · exact (c.elim (fun h => nu h.symm) (fun h => nv h.symm)).elim
    · exact (c.elim (fun h => nv h.symm) (fun h => nu h.symm)).elim
  · simp [star] at rest
    let i : Fin 112 := Fin.ofNat 112 (targetIndex r)
    refine ⟨sigAt i, atMem i, ?_, ?_⟩
    · intro w hw
      exact maskTrue rest.1 w.val (bitOfGuard proof ea eb (gGuard _ hw))
    · intro e he
      exact maskTrue rest.2 e.val (prodOn proof ea eb e (gProd _ _ he))
end LowTop2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open LowTop2264 LowTop2264.Four
theorem noFrameCompact {a b c : Vertex}
    {p q : Signature} (hp : p ∈ signatures) (hq : q ∈ signatures)
    {x y z : Mask} (mx : x = incident a ∨ x = centerMode q a)
    (my : y = incident b ∨ y = centerMode q b) (mz : z = incident c ∨ z = centerMode q c)
    (covered : ∀ i : EdgeRow, (p.2 ||| x ||| y ||| z).getLsbD i.val = true) : False := by
  apply productTripleNoCover hp (signaturesInSources hq) ⟨a,mx⟩ ⟨b,my⟩ ⟨c,mz⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [covered ⟨i,hi⟩]
  change true = (BitVec.allOnes 16).getLsbD i
  rw [BitVec.getLsbD_allOnes, decide_eq_true hi]
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem chosenStarCenters
    (hs : ∀ a ∈ tops G C, (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) :
    let non := tops G C \ centreless G C
    ∃ center : {a // a ∈ non} → Fin n,
      (∀ a, side C a.val 0 = {center a} ∨ side C a.val 1 = {center a}) ∧
      let K := non.attach.image center
      K.card ≤ non.card ∧ (G.deleteEdges (Ustar G C : Set _)).IsVertexCover (K : Set _) := by
  classical
  let non := tops G C \ centreless G C
  have ex : ∀ a : {a // a ∈ non}, ∃ w : Fin n, side C a.val 0 = {w} ∨ side C a.val 1 = {w} := by
    intro a
    have hm := Finset.mem_sdiff.mp a.property
    have hne : ¬ (side (n := n) C a.val 0 = ∅ ∨ side (n := n) C a.val 1 = ∅) :=
      fun h => hm.2 (Finset.mem_filter.mpr ⟨hm.1,h⟩)
    have h0 : 0 < (side (n := n) C a.val 0).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun h => hne (Or.inl h))
    have h1 : 0 < (side (n := n) C a.val 1).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun h => hne (Or.inr h))
    rcases hs _ hm.1 with hz | hz
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (show (side (n := n) C a.val 0).card = 1 by omega)
      exact ⟨w, Or.inl hw⟩
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (show (side (n := n) C a.val 1).card = 1 by omega)
      exact ⟨w, Or.inr hw⟩
  let center (a : {a // a ∈ non}) := Classical.choose (ex a)
  have cen (a : {a // a ∈ non}) := Classical.choose_spec (ex a)
  let K := non.attach.image center
  have hcard : K.card ≤ non.card := Finset.card_image_le.trans_eq (Finset.card_attach (s := non))
  refine ⟨center, cen, hcard, ?_⟩
  intro u v hAdj
  have hEdge : s(u,v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.deleteEdges_adj.mp hAdj).1
  have hNo := (SimpleGraph.deleteEdges_adj.mp hAdj).2
  have hStar : s(u,v) ∈ starEdges G C := by
    by_contra h
    exact hNo (Finset.mem_sdiff.mpr ⟨hEdge,h⟩)
  obtain ⟨a, ha, haS⟩ := Finset.mem_biUnion.mp hStar
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp haS
  have ⟨hl,hr⟩ := Finset.mem_product.mp hp
  have hNon : a ∈ non := by
    refine Finset.mem_sdiff.mpr ⟨ha, fun hc => ?_⟩
    rcases (Finset.mem_filter.mp hc).2 with h | h
    · simpa [h] using hl
    · simpa [h] using hr
  let tag : {a // a ∈ non} := ⟨a,hNon⟩
  have hk : center tag ∈ K := Finset.mem_image_of_mem center (Finset.mem_attach non tag)
  have hse : s(p.1,p.2) = s(u,v) := heq
  have hm : center tag ∈ s(p.1,p.2) := by
    rw [Sym2.mem_iff]
    rcases cen tag with h | h
    · exact Or.inl ((Finset.mem_singleton.mp (h ▸ hl)).symm)
    · exact Or.inr ((Finset.mem_singleton.mp (h ▸ hr)).symm)
  rw [hse, Sym2.mem_iff] at hm
  rcases hm with hc | hc
  · exact Or.inl (hc ▸ hk)
  · exact Or.inr (hc ▸ hk)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Profile2264 (graph)
open UsefulJunk2264 (safe hits adjacentPair useful_edge_cover_adjacent)
theorem junkHasTwoCover {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hG : NoFourCycle G) (hAO : IsAO2 n C) (hT : TopForm G C) {p q : ℕ}
    (hj : junk G C = {p,q}) (hPQ : ¬ InCone n C p q) (hQP : ¬ InCone n C q p)
    {j : ℕ} (hmem : j ∈ junk G C) :
    ∃ D : Finset (Fin n), D.card ≤ 2 ∧ adjacentPair G D ∧
      ∀ u v : Fin n, gateVal n C j (pairInput u v) = true →
        (u ∈ wmax G C j ∨ v ∈ wmax G C j) → u ∈ D ∨ v ∈ D := by
  let A := side (n := n) C j 0
  let B := side (n := n) C j 1
  have product (x : Fin n → Bool) : gateVal n C j x = true ↔ hits A x ∧ hits B x :=
    junkVal hAO hT hj hPQ hQP hmem x
  have guard (w : Fin n) (hw : w ∈ wmax G C j) : safe G A B w := by
    intro x hA hB hx
    have hw' := (Finset.mem_filter.mp hw).2
    exact hw' x ((product x).mpr ⟨hA,hB⟩) hx
  obtain ⟨D, hD, hcc, use⟩ := useful_edge_cover_adjacent hG A B
  refine ⟨D,hD,hcc,fun u v hon hW => ?_⟩
  obtain ⟨hA,hB⟩ := (product _).mp hon
  exact use u v hA hB (hW.imp (guard u) (guard v))
theorem circuitCapacity (C : Circuit) (p q : ℕ)
    (hAO : IsAO2 11 C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (hPQ : ¬ InCone 11 C p q) (hQP : ¬ InCone 11 C q p)
    (apart : ∀ a ∈ tops graph C, InCone 11 C p a → ¬ InCone 11 C q a)
    (traces : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      ∃ a ∈ tops graph C, ∃ (b : Fin 2) (j : ℕ), (j = p ∨ j = q) ∧
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true)
    (K : Finset (Fin 11)) (hK : (graph.deleteEdges (Ustar graph C : Set _)).IsVertexCover (K : Set _)) :
    (Ustar graph C).card ≤ 13 ∧ 3 ≤ K.card ∧
    ∃ D0 D1 : Finset (Fin 11), D0.card ≤ 2 ∧ D1.card ≤ 2 ∧
      adjacentPair graph D0 ∧ adjacentPair graph D1 ∧
      (∀ u v : Fin 11, s(u,v) ∈ Ustar graph C → u ∈ D0 ∪ D1 ∨ v ∈ D0 ∪ D1) ∧
      (K.card = 3 → D0.card = 2 ∧ D1.card = 2 ∧ Disjoint D0 D1 ∧ Disjoint K (D0 ∪ D1)) := by
  have h4 : NoFourCycle graph := by decide +kernel
  obtain ⟨D0,d0,c0,cover0⟩ := junkHasTwoCover h4 hAO hT hj hPQ hQP (j := p) (by simp [hj])
  obtain ⟨D1,d1,c1,cover1⟩ := junkHasTwoCover h4 hAO hT hj hPQ hQP (j := q) (by simp [hj])
  have hD (u v : Fin 11) (he : s(u,v) ∈ Ustar graph C) : u ∈ D0 ∪ D1 ∨ v ∈ D0 ∪ D1 := by
    obtain ⟨a, ha, b, j, hJ, hVal, hr, hJVal⟩ := traces u v he
    obtain ⟨hw, hW⟩ := ustarAttaches hAO hT hj apart ha hr hJ hVal
    have guard := hw.imp (fun h => hW h) (fun h => hW h)
    rcases hJ with rfl | rfl
    · exact (cover0 u v hJVal guard).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (cover1 u v hJVal guard).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
  have hb := Profile2264.two_cover_bounds K D0 D1 _ hK d0 d1 hD
  have hn : (D0 ∪ D1).card ≤ 4 := (Finset.card_union_le _ _).trans (by omega)
  exact ⟨Profile2264.four_cover_ceiling _ _ hn Finset.sdiff_subset hD, hb.1,
    D0,D1,d0,d1,c0,c1,hD,hb.2⟩
theorem junkNonstarForThree (C : Circuit) (p q : ℕ)
    (hAO : IsAO2 11 C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (hPQ : ¬ InCone 11 C p q) (hQP : ¬ InCone 11 C q p)
    (apart : ∀ a ∈ tops graph C, InCone 11 C p a → ¬ InCone 11 C q a)
    (traces : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      ∃ a ∈ tops graph C, ∃ (b : Fin 2) (j : ℕ), (j = p ∨ j = q) ∧
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true)
    (K : Finset (Fin 11)) (hK : (graph.deleteEdges (Ustar graph C : Set _)).IsVertexCover (K : Set _))
    (h3 : K.card = 3) :
    ∀ j ∈ junk graph C, ∀ k : Fin 11, ∃ u v : Fin 11, gateVal 11 C j (pairInput u v) = true ∧
      (u ∈ wmax graph C j ∨ v ∈ wmax graph C j) ∧ u ≠ k ∧ v ≠ k := by
  intro j hjm k
  by_contra! covers
  have star (u v : Fin 11) (on : gateVal 11 C j (pairInput u v) = true)
      (guards : u ∈ wmax graph C j ∨ v ∈ wmax graph C j) : u = k ∨ v = k := by
    by_contra! failure
    exact failure.2 (covers u v on guards failure.1)
  have h4 : NoFourCycle graph := by decide +kernel
  obtain ⟨D0,d0,_,cover0⟩ := junkHasTwoCover h4 hAO hT hj hPQ hQP (j := p) (by simp [hj])
  obtain ⟨D1,d1,_,cover1⟩ := junkHasTwoCover h4 hAO hT hj hPQ hQP (j := q) (by simp [hj])
  have hjnum : j = p ∨ j = q := by simpa [hj] using hjm
  have proof (D : Finset (Fin 11)) (d : D.card ≤ 2)
      (e : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C → u ∈ insert k D ∨ v ∈ insert k D) : False := by
    have size := Profile2264.seven_cover _ (Profile2264.cover_uncovered K (insert k D) _ hK e)
    have d' := Finset.card_insert_le k D
    have ful := Finset.card_union_le K (insert k D)
    omega
  rcases hjnum with rfl | rfl
  · apply proof D1 d1
    intro u v edge
    obtain ⟨a,ha,b,i,num,on,reach,prod⟩ := traces u v edge
    obtain ⟨hg,hw⟩ := ustarAttaches hAO hT hj apart ha reach num on
    have guards := hg.imp (fun h => hw h) (fun h => hw h)
    rcases num with rfl | rfl
    · exact (star u v prod guards).imp
        (fun x => Finset.mem_insert.mpr (Or.inl x)) (fun x => Finset.mem_insert.mpr (Or.inl x))
    · exact (cover1 u v prod guards).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  · apply proof D0 d0
    intro u v edge
    obtain ⟨a,ha,b,i,num,on,reach,prod⟩ := traces u v edge
    obtain ⟨hg,hw⟩ := ustarAttaches hAO hT hj apart ha reach num on
    have guards := hg.imp (fun h => hw h) (fun h => hw h)
    rcases num with rfl | rfl
    · exact (cover0 u v prod guards).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
    · exact (star u v prod guards).imp
        (fun x => Finset.mem_insert.mpr (Or.inl x)) (fun x => Finset.mem_insert.mpr (Or.inl x))
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Profile2264 (graph)
open LowTop2264
def represents (C : Circuit) (j : ℕ) (s : Signature) : Prop :=
  (∀ x : Vertex, x ∈ wmax graph C j → s.1.getLsbD x.val = true) ∧
  ∀ e : EdgeRow, gateVal 11 C j (pairInput (edgeRow e).1 (edgeRow e).2) = true →
    ((edgeRow e).1 ∈ wmax graph C j ∨ (edgeRow e).2 ∈ wmax graph C j) →
    s.2.getLsbD e.val = true
theorem signatureOfJunk {C : Circuit} {p q j : ℕ}
    (hL : IsLeastAO graph C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (pq : ¬ InCone 11 C p q) (qp : ¬ InCone 11 C q p)
    (hJ : j ∈ junk graph C)
    (wide : ∀ k : Vertex, ∃ u v : Vertex, gateVal 11 C j (pairInput u v) = true ∧
      (u ∈ wmax graph C j ∨ v ∈ wmax graph C j) ∧ u ≠ k ∧ v ≠ k) :
    ∃ s ∈ signatures, represents C j s := by
  let A := side (n := 11) C j 0
  let B := side (n := 11) C j 1
  have raw (x : Vertex → Bool) : gateVal 11 C j x = true ↔ UsefulJunk2264.hits A x ∧ UsefulJunk2264.hits B x :=
    junkVal hL.1 hT hj pq qp hJ x
  have guard (w : Vertex) (hm : w ∈ wmax graph C j) : UsefulJunk2264.safe graph A B w :=
    fun x a b hx => (Finset.mem_filter.mp hm).2 x ((raw _).mpr ⟨a,b⟩) hx
  have split (u v : Vertex) (hon : gateVal 11 C j (pairInput u v) = true)
      (safe : u ∈ wmax graph C j ∨ v ∈ wmax graph C j) : UsefulJunk2264.prod graph A B u v := by
    obtain ⟨ha,hb⟩ := (raw _).mp hon
    exact ⟨ha,hb,safe.imp (guard _) (guard _)⟩
  obtain ⟨s,hs,hg,hp⟩ := masksForProduct A B (by decide +kernel) (fun c => by
    obtain ⟨u,v,hj,hs,hu,hv⟩ := wide c
    exact ⟨u,v,split u v hj hs,hu,hv⟩)
  exact ⟨s,hs,fun k hk => hg _ (guard _ hk),fun e h w => hp _ (split _ _ h w)⟩
private theorem incidentBit {e : EdgeRow} {x : Vertex}
    (eq : (edgeRow e).1 = x ∨ (edgeRow e).2 = x) : (incident x).getLsbD e.val = true := by
  rw [incidentSpec,decide_eq_true (eq.imp Eq.symm Eq.symm)]
private theorem orBit {x y : Mask} {n : ℕ} (h : x.getLsbD n = true ∨ y.getLsbD n = true) :
    (x ||| y).getLsbD n = true := by
  rcases h with h | h <;> simp [BitVec.getLsbD_or,h]
theorem mixedBit {C : Circuit} {j : ℕ} {s : Signature} (rep : represents C j s)
    (k : Vertex) (e : EdgeRow)
    (attached : (((edgeRow e).1 ∈ wmax graph C j ∧ graph.Adj k (edgeRow e).1) ∨
      ((edgeRow e).2 ∈ wmax graph C j ∧ graph.Adj k (edgeRow e).2)))
    (caught : (edgeRow e).1 = k ∨ (edgeRow e).2 = k ∨
      gateVal 11 C j (pairInput (edgeRow e).1 (edgeRow e).2) = true) :
    (centerMode s k).getLsbD e.val = true := by
  have both (w : Vertex) (adj : w = (edgeRow e).1 ∨ w = (edgeRow e).2)
      (hw : w ∈ wmax graph C j ∧ graph.Adj k w) :
      (incidentOf (s.1 &&& neighbors k)).getLsbD e.val = true :=
    spreadBit _ _ w (by simp only [BitVec.getLsbD_and,rep.1 _ hw.1,neighborsSpec,
      decide_eq_true hw.2,Bool.and_self]) adj
  have m : (incidentOf (s.1 &&& neighbors k)).getLsbD e.val = true :=
    attached.elim (both _ (Or.inl rfl)) (both _ (Or.inr rfl))
  have guard : (edgeRow e).1 ∈ wmax graph C j ∨ (edgeRow e).2 ∈ wmax graph C j :=
    attached.imp And.left And.left
  have n : (incident k ||| s.2).getLsbD e.val = true := by
    apply orBit
    rcases caught with h | h | h
    · exact Or.inl (incidentBit (Or.inl h))
    · exact Or.inl (incidentBit (Or.inr h))
    · exact Or.inr (rep.2 e h guard)
  simp only [centerMode,BitVec.getLsbD_and,m,n,Bool.and_self]
set_option maxHeartbeats 0 in
theorem threeNeedsCentrelessDestination (C : Circuit) (p q : ℕ)
    (hL : IsLeastAO graph C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (pq : ¬ InCone 11 C p q) (qp : ¬ InCone 11 C q p)
    (apart : ∀ a ∈ tops graph C, InCone 11 C p a → ¬ InCone 11 C q a)
    (stars : ∀ a ∈ tops graph C,
      (∀ u ∈ side (n := 11) C a 0, ∀ v ∈ side C a 1, graph.Adj u v) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1))
    (traces : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      ∃ a ∈ tops graph C, ∃ (b : Fin 2) (j : ℕ), (j = p ∨ j = q) ∧
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true)
    (three : (tops graph C \ centreless graph C).card = 3) :
    ∃ a ∈ centreless graph C, InCone 11 C q a := by
  by_contra! noQ
  let T := tops graph C \ centreless graph C
  obtain ⟨f, pick, bound, cover⟩ := chosenStarCenters (G := graph) (C := C)
    (fun a ha => (stars a ha).2)
  let K := T.attach.image f
  change K.card ≤ T.card at bound
  change ((graph.deleteEdges (Ustar graph C : Set _)).IsVertexCover (K : Set _)) at cover
  have hcap := (circuitCapacity C p q hL.1 hT hj pq qp apart traces K cover).2.1
  change T.card = 3 at three
  have k3 : K.card = 3 := by omega
  have inj : Function.Injective f := by
    intro a b he
    apply Finset.injOn_of_card_image_eq (s := T.attach) (f := f) _ (Finset.mem_attach _ a) (Finset.mem_attach _ b) he
    rw [Finset.card_attach,three]
    exact k3
  have hLen : K.sort.length = 3 := by rw [Finset.length_sort,k3]
  obtain ⟨a,b,c,ls⟩ := List.length_eq_three.mp hLen
  have get (x : Vertex) (hx : x ∈ [a,b,c]) : ∃ tag : {a // a ∈ T}, f tag = x := by
    have same : x ∈ K := (Finset.mem_sort (s := K) (fun x y : Vertex => x ≤ y)).mp (ls.symm ▸ hx)
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp same
    exact ⟨t,ht⟩
  obtain ⟨ta,hat⟩ := get a (by simp)
  obtain ⟨tb,hbt⟩ := get b (by simp)
  obtain ⟨tc,hct⟩ := get c (by simp)
  have only (tag : {a // a ∈ T}) : tag = ta ∨ tag = tb ∨ tag = tc := by
    have hm : f tag ∈ K := Finset.mem_image_of_mem f (Finset.mem_attach T tag)
    have foo := (Finset.mem_sort (s := K) (fun x y : Vertex => x ≤ y)).mpr hm
    rw [ls] at foo
    simp only [List.mem_cons,List.not_mem_nil,or_false] at foo
    exact foo.imp (fun h => inj (h.trans hat.symm))
      (fun h => h.imp (fun e => inj (e.trans hbt.symm)) (fun e => inj (e.trans hct.symm)))
  have pJ : p ∈ junk graph C := by simp [hj]
  have qJ : q ∈ junk graph C := by simp [hj]
  have wide := junkNonstarForThree C p q hL.1 hT hj pq qp apart traces K cover k3
  obtain ⟨pMask,hp,pr⟩ := signatureOfJunk hL hT hj pq qp pJ (wide p pJ)
  obtain ⟨qMask,hq,qr⟩ := signatureOfJunk hL hT hj pq qp qJ (wide q qJ)
  have mode (tag : {a // a ∈ T}) : ∃ m : Mask,
      (m = incident (f tag) ∨ m = centerMode qMask (f tag)) ∧
      ∀ e : EdgeRow, gateVal 11 C tag.val (pairInput (edgeRow e).1 (edgeRow e).2) = true →
        (pMask.2 ||| m).getLsbD e.val = true := by
    have hTop := (Finset.mem_sdiff.mp tag.property).1
    obtain ⟨b,hs⟩ : ∃ i : Fin 2, side (n := 11) C tag.val i = {f tag} :=
      (pick tag).elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
    rcases centerModeBound hL.1 hT hj apart (fun t ht => (stars t ht).1) hTop hs with pure | ⟨j,hJ,mix⟩
    · exact ⟨incident (f tag),Or.inl rfl,fun e he => orBit (Or.inr (incidentBit (pure _ _ he)))⟩
    · rcases hJ with hJ | hJ
      · subst j
        refine ⟨incident (f tag),Or.inl rfl,fun e he => orBit ?_⟩
        obtain ⟨attached,on⟩ := mix _ _ he
        have guards := attached.imp And.left And.left
        rcases on with l | r | j
        · exact Or.inr (incidentBit (Or.inl l))
        · exact Or.inr (incidentBit (Or.inr r))
        · exact Or.inl (pr.2 e j guards)
      · subst j
        refine ⟨centerMode qMask (f tag),Or.inr rfl,fun e he => orBit (Or.inr ?_)⟩
        exact mixedBit qr (f tag) e (mix _ _ he).1 (mix _ _ he).2
  obtain ⟨x,mx,hitx⟩ := mode ta
  obtain ⟨y,my,hity⟩ := mode tb
  obtain ⟨z,mz,hitz⟩ := mode tc
  rw [hat] at mx
  rw [hbt] at my
  rw [hct] at mz
  apply noFrameCompact hp hq mx my mz
  intro e
  obtain ⟨j,jt,jOn⟩ := pairHitsTop hL (rowAdjacent e)
  by_cases jC : j ∈ centreless graph C
  · obtain ⟨i,num,cone,io,guard⟩ := centrelessModeBound hL.1 hT hj apart jC jOn
    have num' : i = p := num.resolve_right (fun d => noQ _ jC (d ▸ cone))
    subst i
    have he := pr.2 e io guard
    exact orBit (Or.inl (orBit (Or.inl (orBit (Or.inl he)))))
  · let tag : {a // a ∈ T} := ⟨j,Finset.mem_sdiff.mpr ⟨jt,jC⟩⟩
    have check (t : {a // a ∈ T}) (eq : tag = t) :
        gateVal 11 C t.val (pairInput (edgeRow e).1 (edgeRow e).2) = true := eq ▸ jOn
    rcases only tag with h | h | h
    · exact orBit (Or.inl (orBit (Or.inl (hitx e (check _ h)))))
    · have hh := hity e (check _ h)
      have alt : pMask.2.getLsbD e.val = true ∨ y.getLsbD e.val = true := by
        simpa only [BitVec.getLsbD_or,Bool.or_eq_true] using hh
      rcases alt with h | h
      · exact orBit (Or.inl (orBit (Or.inl (orBit (Or.inl h)))))
      · exact orBit (Or.inl (orBit (Or.inr h)))
    · have hh := hitz e (check _ h)
      have alt : pMask.2.getLsbD e.val = true ∨ z.getLsbD e.val = true := by
        simpa only [BitVec.getLsbD_or,Bool.or_eq_true] using hh
      rcases alt with h | h
      · exact orBit (Or.inl (orBit (Or.inl (orBit (Or.inl h)))))
      · exact orBit (Or.inr h)
theorem threeForcesTwoCentreless (C : Circuit) (p q : ℕ)
    (hL : IsLeastAO graph C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (pq : ¬ InCone 11 C p q) (qp : ¬ InCone 11 C q p)
    (apart : ∀ a ∈ tops graph C, InCone 11 C p a → ¬ InCone 11 C q a)
    (stars : ∀ a ∈ tops graph C,
      (∀ u ∈ side (n := 11) C a 0, ∀ v ∈ side C a 1, graph.Adj u v) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1))
    (traces : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      ∃ a ∈ tops graph C, ∃ (b : Fin 2) (j : ℕ), (j = p ∨ j = q) ∧
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true)
    (three : (tops graph C \ centreless graph C).card = 3) : 2 ≤ (centreless graph C).card := by
  have hj' : junk graph C = {q,p} := by rw [hj,Finset.pair_comm]
  have apart' : ∀ a ∈ tops graph C, InCone 11 C q a → ¬ InCone 11 C p a :=
    fun a ha iq ip => apart a ha ip iq
  have trace' : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      ∃ a ∈ tops graph C, ∃ (b : Fin 2) (j : ℕ), (j = q ∨ j = p) ∧
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true := by
    intro u v hu
    obtain ⟨a,ha,b,j,h,ht,hr,hon⟩ := traces u v hu
    exact ⟨a,ha,b,j,h.symm,ht,hr,hon⟩
  obtain ⟨a,ha,aq⟩ := threeNeedsCentrelessDestination C p q hL hT hj pq qp apart stars traces three
  obtain ⟨b,hb,bp⟩ := threeNeedsCentrelessDestination C q p hL hT hj' qp pq apart' stars trace' three
  have neq : a ≠ b := by
    intro eq
    subst b
    exact apart a (Finset.mem_filter.mp ha).1 bp aq
  exact Finset.one_lt_card_iff.mpr ⟨a,b,ha,hb,neq⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Profile2264 (graph)
open LowTop2264 LowTop2264.Four
private theorem incidentOn {e : EdgeRow} {k : Vertex}
    (found : (edgeRow e).1 = k ∨ (edgeRow e).2 = k) :
    (incident k).getLsbD e.val = true := by
  rw [incidentSpec, decide_eq_true (found.imp Eq.symm Eq.symm)]
theorem signatureOfAnyJunk {C : Circuit} {p q j : ℕ}
    (hL : IsLeastAO graph C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (pq : ¬ InCone 11 C p q) (qp : ¬ InCone 11 C q p)
    (hJ : j ∈ junk graph C) :
    ∃ s ∈ signatureSources, represents C j s := by
  classical
  by_cases wide : ∀ k : Vertex, ∃ u v : Vertex, gateVal 11 C j (pairInput u v) = true ∧
      (u ∈ wmax graph C j ∨ v ∈ wmax graph C j) ∧ u ≠ k ∧ v ≠ k
  · obtain ⟨s,hs,rep⟩ := signatureOfJunk hL hT hj pq qp hJ wide
    exact ⟨s,signaturesInSources hs,rep⟩
  let A := side (n := 11) C j 0
  let B := side (n := 11) C j 1
  have raw (x : Vertex → Bool) : gateVal 11 C j x = true ↔ UsefulJunk2264.hits A x ∧ UsefulJunk2264.hits B x :=
    junkVal hL.1 hT hj pq qp hJ x
  have guard (w : Vertex) (hm : w ∈ wmax graph C j) : UsefulJunk2264.safe graph A B w :=
    fun x a b hx => (Finset.mem_filter.mp hm).2 x ((raw _).mpr ⟨a,b⟩) hx
  obtain ⟨c,covers⟩ := not_forall.mp wide
  have supported (u v : Vertex) (on : gateVal 11 C j (pairInput u v) = true)
      (hm : u ∈ wmax graph C j ∨ v ∈ wmax graph C j) : u = c ∨ v = c := by
    by_contra! notInc
    exact covers ⟨u,v,on,hm,notInc.1,notInc.2⟩
  have dirty : IsDirty 11 graph C j := ((Finset.mem_filter.mp hJ).2).2
  obtain ⟨x,hx,off⟩ := dirty.2
  obtain ⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩ := (raw x).mp hx
  have nonadj : ¬ graph.Adj a b := by
    intro hab
    have found : graphFun graph ∅ x = true := by
      unfold graphFun
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨a,b,hab,hax,hbx⟩
    simp [found] at off
  have b0 : (neighbors a).getLsbD b.val = false := by rw [neighborsSpec, decide_eq_false nonadj]
  have a0 : (neighbors b).getLsbD a.val = false := by
    rw [neighborsSpec, decide_eq_false (fun h => nonadj h.symm)]
  refine ⟨starSignature a b c,starInSources a b c b0 a0,?_⟩
  have isGuard (w : Vertex) (hw : w ∈ wmax graph C j) :
      ((starSignature a b c).1).getLsbD w.val = true := by
    have hv : graph.Adj a w ∨ graph.Adj b w :=
      ((UsefulJunk2264.safe_triple (guard w hw) ha hb).resolve_left nonadj).imp
        (fun h => h.symm) (fun h => h.symm)
    simp only [starSignature, BitVec.getLsbD_or, neighborsSpec, Bool.or_eq_true, decide_eq_true_eq]
    exact hv
  refine ⟨isGuard,?_⟩
  intro e he hW
  have ic := incidentOn (supported _ _ he hW)
  have sc : (incidentOf (starSignature a b c).1).getLsbD e.val = true :=
    hW.elim (fun h => spreadBit _ _ _ (isGuard _ h) (Or.inl rfl))
      (fun h => spreadBit _ _ _ (isGuard _ h) (Or.inr rfl))
  change (incident c &&& incidentOf (starSignature a b c).1).getLsbD e.val = true
  simp [ic,sc]
theorem fourNeedsCentreless (C : Circuit) (p q : ℕ)
    (hL : IsLeastAO graph C) (hT : TopForm graph C)
    (hj : junk graph C = {p,q}) (pq : ¬ InCone 11 C p q) (qp : ¬ InCone 11 C q p)
    (apart : ∀ a ∈ tops graph C, InCone 11 C p a → ¬ InCone 11 C q a)
    (stars : ∀ a ∈ tops graph C,
      (∀ u ∈ side (n := 11) C a 0, ∀ v ∈ side C a 1, graph.Adj u v) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1))
    (four : (tops graph C \ centreless graph C).card = 4)
    (empty : centreless graph C = ∅) : False := by
  classical
  let T := tops graph C \ centreless graph C
  obtain ⟨f,pick,_,_⟩ := chosenStarCenters (G := graph) (C := C) (fun a ha => (stars a ha).2)
  obtain ⟨s,hs,repS⟩ := signatureOfAnyJunk hL hT hj pq qp (show p ∈ junk graph C by simp [hj])
  obtain ⟨t,ht,repT⟩ := signatureOfAnyJunk hL hT hj pq qp (show q ∈ junk graph C by simp [hj])
  have modes (tag : {a // a ∈ T}) : ∃ m : Mask,
      (mode s m ∨ mode t m) ∧
      ∀ e : EdgeRow, gateVal 11 C tag.val (pairInput (edgeRow e).1 (edgeRow e).2) = true →
        m.getLsbD e.val = true := by
    have hTop := (Finset.mem_sdiff.mp tag.property).1
    obtain ⟨b,sideEq⟩ : ∃ i : Fin 2, side (n := 11) C tag.val i = {f tag} :=
      (pick tag).elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
    rcases centerModeBound hL.1 hT hj apart (fun a ha => (stars a ha).1) hTop sideEq with pure | ⟨j,jNum,mix⟩
    · exact ⟨incident (f tag), Or.inl ⟨f tag,Or.inl rfl⟩, fun e he => incidentOn (pure _ _ he)⟩
    · rcases jNum with jp | jq
      · subst j
        exact ⟨centerMode s (f tag),Or.inl ⟨f tag,Or.inr rfl⟩,
          fun e he => mixedBit repS (f tag) e (mix _ _ he).1 (mix _ _ he).2⟩
      · subst j
        exact ⟨centerMode t (f tag),Or.inr ⟨f tag,Or.inr rfl⟩,
          fun e he => mixedBit repT (f tag) e (mix _ _ he).1 (mix _ _ he).2⟩
  let tagOf : Fin 4 ≃ {a // a ∈ T} :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using four)).symm
  let m (i : Fin 4) : Mask := Classical.choose (modes (tagOf i))
  have classified (i : Fin 4) := (Classical.choose_spec (modes (tagOf i))).1
  apply fourNoCover hs ht (classified 0) (classified 1) (classified 2) (classified 3)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let e : EdgeRow := ⟨i,hi⟩
  obtain ⟨a,ha,on⟩ := pairHitsTop hL (rowAdjacent e)
  let tag : {a // a ∈ T} := ⟨a,Finset.mem_sdiff.mpr ⟨ha,by simp [empty]⟩⟩
  let ix : Fin 4 := tagOf.symm tag
  have eq : tagOf ix = tag := tagOf.apply_symm_apply _
  have hit : (m ix).getLsbD i = true := by
    apply (Classical.choose_spec (modes (tagOf ix))).2 e
    rw [eq]
    exact on
  have full : (65535 : Mask).getLsbD i = true := by
    change (BitVec.allOnes 16).getLsbD i = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true hi
  rw [full]
  have exhaustive : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide +kernel
  rcases exhaustive ix with h | h | h | h <;>
    simp only [h, BitVec.getLsbD_or, Bool.or_eq_true] at hit ⊢ <;> tauto
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem routedTopCross {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    {x y : Fin n} (hx : x ∈ side (n := n) C a b)
    (hy : y ∈ side (n := n) C a (1 - b)) :
    s(x, y) ∈ starEdges G C := by
  unfold starEdges
  refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
  fin_cases b
  · exact ⟨(x,y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  · exact ⟨(y,x), Finset.mem_product.mpr ⟨hy, hx⟩, Sym2.eq_swap⟩
def mixingRaw (C : Circuit) (n m : ℕ) : Option (Fin n) :=
  if h : (orIn n C (n+m)).Nonempty then some ((orIn n C (n+m)).min' h) else none
theorem mixingRawMem {m : ℕ} (h : (orIn n C (n+m)).Nonempty) :
    ∃ x ∈ orIn n C (n+m), mixingRaw C n m = some x := by
  exact ⟨_, Finset.min'_mem _ h, by simp [mixingRaw, h]⟩
def mixingLabel (C : Circuit) (n j₀ j₁ m : ℕ) : ℕ × Option (Fin n) :=
  (if OrReaches n C (n+m) j₀ then j₀ else j₁, mixingRaw C n m)
theorem mixingLabelExact (hAO : IsAO2 n C)
    {j₀ j₁ : ℕ} (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    {a j m : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hm : OrReaches n C (opnd C a b) m) (hj : OrReaches n C (n+m) j)
    (hjj : j = j₀ ∨ j = j₁) (h : (orIn n C (n+m)).Nonempty) :
    ∃ x ∈ orIn n C (n+m), mixingLabel C n j₀ j₁ m = (j, some x) := by
  obtain ⟨x, hx, hex⟩ := mixingRawMem h
  refine ⟨x, hx, ?_⟩
  unfold mixingLabel
  rw [hex]
  rcases hjj with rfl | rfl
  · rw [if_pos hj]
  · by_cases hr : OrReaches n C (n+m) j₀
    · have h0 := operandReachCone hAO (topData ha).1 (reachTrans hm hr)
      have h1 := operandReachCone hAO (topData ha).1 (reachTrans hm hj)
      exact (hsep a ha h0 h1).elim
    · rw [if_neg hr]
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem pairInputSwap (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]
theorem uniqueCommonCenter {S : Finset (Fin n)} {t y : Fin n} (h4 : NoFourCycle G)
    (hS : 1 < S.card) (ht : ∀ z ∈ S, G.Adj t z)
    (hy : ∀ z ∈ S, G.Adj y z) : t = y := by
  by_contra he
  have hsub : S ⊆ Finset.univ.filter fun z => G.Adj t z ∧ G.Adj y z := by
    intro z hz
    simp [ht z hz, hy z hz]
  have hl := Finset.card_le_card hsub
  have hu := h4 t y he
  omega

omit [DecidableRel G.Adj] in
theorem wmaxArmLeft {j : ℕ} {y : Fin n}
    (hw : ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
      G.Adj u v ∨ G.Adj u y ∨ G.Adj v y)
    (hy : y ∈ side (n := n) C j 0) :
    ∀ v ∈ side (n := n) C j 1, G.Adj y v := by
  intro v hv
  rcases hw y hy v hv with h | h | h
  · exact h
  · exact (G.irrefl h).elim
  · exact h.symm

omit [DecidableRel G.Adj] in
theorem wmaxArmRight {j : ℕ} {y : Fin n}
    (hw : ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
      G.Adj u v ∨ G.Adj u y ∨ G.Adj v y)
    (hy : y ∈ side (n := n) C j 1) :
    ∀ u ∈ side (n := n) C j 0, G.Adj y u := by
  intro u hu
  rcases hw u hu y hy with h | h | h
  · exact h.symm
  · exact h.symm
  · exact (G.irrefl h).elim

omit [DecidableRel G.Adj] in
theorem wmaxOverlap {j : ℕ} {y : Fin n}
    (hw : ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
      G.Adj u v ∨ G.Adj u y ∨ G.Adj v y) :
    ∀ v ∈ side (n := n) C j 0 ∩ side (n := n) C j 1, G.Adj y v := by
  intro v hv
  obtain ⟨h0, h1⟩ := Finset.mem_inter.mp hv
  rcases hw v h0 v h1 with h | h | h
  · exact (G.irrefl h).elim
  · exact h.symm
  · exact h.symm
theorem pairHits {S : Finset (Fin n)} {y z : Fin n}
    (h : ∃ v ∈ S, pairInput y z v = true) : y ∈ S ∨ z ∈ S := by
  obtain ⟨v, hv, hv'⟩ := h
  rcases (pairInput_true y z v).mp hv' with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv
abbrev HasRoute {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j₀ j₁ : ℕ) : Prop :=
  ∀ u v : Fin n, s(u, v) ∈ Ustar G C → ∃ a ∈ tops G C, ∃ (b : Fin 2) (j : ℕ),
    (j = j₀ ∨ j = j₁) ∧ gateVal n C a (pairInput u v) = true ∧
    OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true
abbrev HasCross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
theorem existsMinCover {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ K, IsMinCover G K := by
  classical
  let P (m : ℕ) := ∃ K : Finset (Fin n), G.IsVertexCover (↑K) ∧ K.card = m
  have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
  refine ⟨K, hK, fun T hT => ?_⟩
  exact hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264.Eligible
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def Available (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset (Fin n)) : Prop :=
  S.card ≤ 1 ∨
    ∃ t : Fin n, ∀ x ∈ S, G.Adj t x ∧ s(t, x) ∉ Ustar G C
instance (S : Finset (Fin n)) : Decidable (Available G C S) := by
  unfold Available
  infer_instance
def ClippedStep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (p q : ℕ) : Prop :=
  OrStep n C p q ∧ ¬ Available G C (orIn n C p)
abbrev ClippedReach (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  Relation.ReflTransGen (ClippedStep G C)
noncomputable def clippedCone (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (w + 1)).filter (ClippedReach G C w)
noncomputable def pureInternals (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) : Finset ℕ :=
  (clippedCone G C w).filter fun z => n ≤ z ∧ ¬ Available G C (orIn n C z)
noncomputable def pureFrontier (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) : Finset ℕ := clippedCone G C w \ pureInternals G C w
theorem clippedAsOr {w z : ℕ} (h : ClippedReach G C w z) :
    Relation.ReflTransGen (OrStep n C) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.1
theorem clipMem {w z : ℕ} : z ∈ clippedCone G C w ↔ ClippedReach G C w z := by
  classical
  simp only [clippedCone, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun hr => ⟨Nat.lt_succ_of_le (orStep_le (clippedAsOr hr)), hr⟩⟩
theorem pureInternalsCharged (hAO : IsAO2 n C) {w : ℕ} (hw : w < n + C.gates.length)
    (hp : ∀ h, OrReaches n C w h → (gateAt C h).op ≠ GateOp.and)
    (hstar : HasCross G C)
    {z : ℕ} (hz : z ∈ pureInternals G C w) :
    z - n ∈ (orN G C \ lam G C) \ mixing G C := by
  obtain ⟨hc, hn, hl⟩ := Finset.mem_filter.mp hz
  have hreach := clippedAsOr (clipMem.mp hc)
  have hle := orStep_le hreach
  obtain ⟨m, rfl⟩ : ∃ m, z = n + m := ⟨z - n, by omega⟩
  have hml : m < C.gates.length := by omega
  have he : n + m - n = m := by omega
  rw [he]
  have hr : OrReaches n C w m := reach_orReaches hreach m rfl hml
  have hpure (j : ℕ) (hj : OrReaches n C (n + m) j) : (gateAt C j).op ≠ GateOp.and :=
    hp j (reachTrans hr hj)
  have hop := (hAO.1 _ (gateAt_mem hml)).resolve_left (hp m hr)
  have hnon : (orIn n C (n + m)).Nonempty := pureOrNonempty hAO (by omega) hpure
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨orNOfRaw hml hop hnon, fun hm => hl (Or.inr (lamAvoidsUstar hm hstar))⟩,
    pureOrNotMixing hAO hml hop hpure⟩
theorem clippedSomeFrontier {w : ℕ} (x : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) w x.val) :
    ∃ z, ClippedReach G C w z ∧ (z < n ∨ Available G C (orIn n C z)) ∧
      Relation.ReflTransGen (OrStep n C) z x.val := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨x.val, Relation.ReflTransGen.refl, Or.inl x.isLt, Relation.ReflTransGen.refl⟩
  | @head a b hs hrest ih =>
    by_cases hl : Available G C (orIn n C a)
    · exact ⟨a, Relation.ReflTransGen.refl, Or.inr hl, Relation.ReflTransGen.head hs hrest⟩
    · obtain ⟨z, h1, h2, h3⟩ := ih
      exact ⟨z, Relation.ReflTransGen.head ⟨hs, hl⟩ h1, h2, h3⟩
theorem pureFrontierUnion {w : ℕ} :
    orIn n C w = (pureFrontier G C w).biUnion (orIn n C) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, h1, h2, h3⟩ := clippedSomeFrontier (G := G) x (mem_orIn_reach x hx)
    apply Finset.mem_biUnion.mpr
    refine ⟨z, Finset.mem_sdiff.mpr ⟨clipMem.mpr h1, ?_⟩, reach_mem_orIn x h3⟩
    intro hi
    obtain ⟨_, hge, hnl⟩ := Finset.mem_filter.mp hi
    rcases h2 with hlt | hl
    · omega
    · exact hnl hl
  · intro hx
    obtain ⟨z, hz, hx⟩ := Finset.mem_biUnion.mp hx
    exact orInTrans (clippedAsOr (clipMem.mp (Finset.mem_sdiff.mp hz).1)) hx
theorem pureFrontierAvailable {w z : ℕ} (hz : z ∈ pureFrontier G C w) :
    Available G C (orIn n C z) := by
  obtain ⟨hc, hn⟩ := Finset.mem_sdiff.mp hz
  by_cases hlt : z < n
  · left
    rw [orInRaw hlt, Finset.card_singleton]
  · by_contra hnl
    exact hn (Finset.mem_filter.mpr ⟨hc, Nat.le_of_not_lt hlt, hnl⟩)
end PEqualNP.Outside.L_meta_2264.Eligible

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
abbrev Guarded (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (x y z : Fin n) : Prop :=
  s(y,z) ∈ Ustar G C ∧ y ∈ wmax G C j ∧ gateVal n C j (pairInput y z) = true ∧
    G.Adj x y ∧ x ≠ z
theorem commonNeighborArm {j : ℕ} {y : Fin n} {b : Fin 2}
    (hW : ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
      G.Adj u v ∨ G.Adj u y ∨ G.Adj v y)
    (hy : y ∈ side (n := n) C j b) :
    ∀ z ∈ side (n := n) C j (1 - b), G.Adj y z := by
  fin_cases b
  · exact wmaxArmLeft hW hy
  · exact wmaxArmRight hW hy
theorem oppositeOpposite (b : Fin 2) : 1 - (1 - b) = b := by
  fin_cases b <;> decide
theorem termsHit {j : ℕ}
    (hJ : ∀ q : Fin n → Bool, gateVal n C j q = true ↔
      (∃ t ∈ side (n := n) C j 0, q t = true) ∧ (∃ t ∈ side (n := n) C j 1, q t = true))
    (b : Fin 2) {y z : Fin n} (h : gateVal n C j (pairInput y z) = true) :
    y ∈ side (n := n) C j b ∨ z ∈ side (n := n) C j b := by
  obtain ⟨hL,hR⟩ := (hJ _).mp h
  fin_cases b
  · exact pairHits hL
  · exact pairHits hR
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
def ActiveInterior (C : Circuit) (j : ℕ) (y : Fin n) : Prop :=
  (∀ b : Fin 2, 1 < (side (n := n) C j b).card) ∧
    ∃ b : Fin 2, y ∈ side (n := n) C j b
abbrev NoPureMix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (orN G C \ lam G C) \ mixing G C
abbrev JunkValModel (C : Circuit) (j : ℕ) (n : ℕ) :=
  ∀ q : Fin n → Bool, gateVal n C j q = true ↔
    (∃ v ∈ side (n := n) C j 0, q v = true) ∧ (∃ v ∈ side (n := n) C j 1, q v = true)
theorem exteriorTail {j : ℕ} {y z : Fin n}
    (hJ : JunkValModel C j n) (hv : gateVal n C j (pairInput y z) = true)
    (hy : ∀ b : Fin 2, y ∉ side (n := n) C j b) :
    z ∈ side (n := n) C j 0 ∩ side (n := n) C j 1 := by
  exact Finset.mem_inter.mpr
    ⟨(termsHit hJ 0 hv).resolve_left (hy 0), (termsHit hJ 1 hv).resolve_left (hy 1)⟩
theorem narrowUniqueTail {j : ℕ}
    (hJ : JunkValModel C j n) (hj : j ∈ junk G C)
    {b : Fin 2} (hsml : (side (n := n) C j b).card ≤ 1)
    {y z y' z' : Fin n} (hy : y ∈ wmax G C j) (hy' : y' ∈ wmax G C j)
    (hv : gateVal n C j (pairInput y z) = true)
    (hv' : gateVal n C j (pairInput y' z') = true) : z = z' := by
  have hAll (q : Fin n → Bool) (hq : gateVal n C j q = true) :
      ∃ v ∈ side (n := n) C j b, q v = true := by
    obtain ⟨hL,hR⟩ := (hJ q).mp hq
    fin_cases b
    · exact hL
    · exact hR
  obtain ⟨s, hsb, _⟩ := hAll _ hv
  have hval (q : Fin n → Bool) (hq : gateVal n C j q = true) : q s = true := by
    obtain ⟨v,hv,hvq⟩ := hAll q hq
    exact (Finset.card_le_one_iff.mp hsml hv hsb) ▸ hvq
  have hs : s ∉ wmax G C j := by
    intro h
    obtain ⟨_,_,q,hq,hn⟩ := junkData hj
    have h' := (Finset.mem_filter.mp h).2
    rw [h' q hq (hval _ hq)] at hn
    contradiction
  have htail (u v : Fin n) (hu : u ∈ wmax G C j)
      (hp : gateVal n C j (pairInput u v) = true) : v = s := by
    rcases (pairInput_true u v s).mp (hval _ hp) with rfl | rfl
    · exact (hs hu).elim
    · rfl
  exact (htail y z hy hv).trans (htail y' z' hy' hv').symm
theorem interiorAndOrdinaryConflict (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (hs : junk G C = {j₀,j₁}) (h₀₁ : ¬ InCone n C j₀ j₁) (h₁₀ : ¬ InCone n C j₁ j₀)
    {j : ℕ} (hj : j ∈ junk G C) {x y z y' z' : Fin n}
    (hi : ActiveInterior C j y) (ho : ¬ ActiveInterior C j y')
    (h : Guarded G C j x y z) (h' : Guarded G C j x y' z') :
    False := by
  obtain ⟨hw,b,hb⟩ := hi
  have hJ := junkVal hAO hT hs h₀₁ h₁₀ hj
  have hNo (b : Fin 2) : y' ∉ side (n := n) C j b := fun hy => ho ⟨hw,b,hy⟩
  have hz := Finset.mem_inter.mp (exteriorTail hJ h'.2.2.1 hNo)
  have hz' : z' ∈ side (n := n) C j (1-b) := by
    fin_cases b
    · exact hz.2
    · exact hz.1
  have hay := (commonNeighborArm ((junkWmax hAO hT hs h₀₁ h₁₀ hj y).mp h.2.1) hb _ hz').symm
  have hay' : G.Adj z' y' := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp h'.1).1).symm
  have H := h4 x z' h'.2.2.2.2
  have heq := Finset.card_le_one_iff.mp H
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.2.1,hay⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'.2.2.2.1,hay'⟩)
  exact hNo b (heq ▸ hb)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264.Eligible
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem familyFrontierCard (hAO : IsAO2 n C) (R : Finset ℕ) :
    (R.biUnion (pureFrontier G C)).card ≤ (R.biUnion (pureInternals G C)).card + R.card := by
  let W := R.biUnion (clippedCone G C)
  let I := R.biUnion (pureInternals G C)
  let T := R.biUnion (pureFrontier G C)
  have hI : I ⊆ W := by
    intro x hx
    obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Finset.mem_filter.mp hi).1⟩
  have hR : R ⊆ W := fun w hw =>
    Finset.mem_biUnion.mpr ⟨w,hw,clipMem.mpr Relation.ReflTransGen.refl⟩
  have ht : T = W \ I := by
    ext x
    constructor
    · intro h
      obtain ⟨w,hw,hs⟩ := Finset.mem_biUnion.mp h
      obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hs
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w,hw,h1⟩, ?_⟩
      intro hi
      obtain ⟨_, _, hC⟩ := Finset.mem_biUnion.mp hi
      exact h2 (Finset.mem_filter.mpr ⟨h1,(Finset.mem_filter.mp hC).2⟩)
    · intro h
      obtain ⟨hW, hI⟩ := Finset.mem_sdiff.mp h
      obtain ⟨w, hw, hC⟩ := Finset.mem_biUnion.mp hW
      exact Finset.mem_biUnion.mpr ⟨w,hw,
        Finset.mem_sdiff.mpr ⟨hC, fun h => hI (Finset.mem_biUnion.mpr ⟨w,hw,h⟩)⟩⟩
  have hbound : W \ R ⊆ I.biUnion (fun z => {opnd C (z - n) 0, opnd C (z - n) 1}) := by
    intro v hv
    obtain ⟨hv, hvR⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨w, hw, hvC⟩ := Finset.mem_biUnion.mp hv
    rcases Relation.ReflTransGen.cases_tail (clipMem.mp hvC) with h | ⟨z,hzs,hs⟩
    · exact (hvR (h ▸ hw)).elim
    · obtain ⟨j,hj,he,_,hz,_⟩ := hs.1
      have hj' : z - n = j := by omega
      apply Finset.mem_biUnion.mpr
      refine ⟨z, Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨clipMem.mpr hzs, by omega, hs.2⟩⟩, ?_⟩
      obtain ⟨b, hb⟩ := inputsAsOpnd hAO hj hz
      rw [hj',hb]
      fin_cases b <;> simp
  have hch : (I.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤ 2 * I.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ _z ∈ I, (2 : ℕ) := Finset.sum_le_sum (fun z _ => by
        exact (Finset.card_insert_le _ _).trans (by simp))
      _ = _ := by simp [Nat.mul_comm]
  have hv := (Finset.card_le_card hbound).trans hch
  have hr := Finset.card_sdiff_add_card_eq_card hR
  have hi := Finset.card_sdiff_add_card_eq_card hI
  change T.card ≤ I.card + R.card
  rw [ht]
  omega
theorem familyForbiddenCapacityLocal (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R : Finset ℕ) (y : Fin n) :
    (R.biUnion (fun w => (orIn n C w).filter fun z => s(y,z) ∈ Ustar G C)).card ≤
      (R.biUnion (pureInternals G C)).card + R.card := by
  let T := R.biUnion (pureFrontier G C)
  let B (v : ℕ) := (orIn n C v).filter fun z => s(y,z) ∈ Ustar G C
  have hT : R.biUnion B = T.biUnion B := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,hz'⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hs,hu⟩ := Finset.mem_filter.mp hz'
      rw [pureFrontierUnion (G := G) (C := C)] at hs
      obtain ⟨v,hv,hvz⟩ := Finset.mem_biUnion.mp hs
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_biUnion.mpr ⟨w,hw,hv⟩,
        Finset.mem_filter.mpr ⟨hvz,hu⟩⟩
    · intro hz
      obtain ⟨v,hv,hz'⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨w,hw,hv'⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨hs,hu⟩ := Finset.mem_filter.mp hz'
      refine Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨?_,hu⟩⟩
      rw [pureFrontierUnion (G := G) (C := C)]
      exact Finset.mem_biUnion.mpr ⟨v,hv',hs⟩
  have hs : ∀ v ∈ T, (B v).card ≤ 1 := by
    intro v hv
    obtain ⟨w,_,hv'⟩ := Finset.mem_biUnion.mp hv
    rcases pureFrontierAvailable hv' with hc | ⟨t,ht⟩
    · exact (Finset.card_filter_le _ _).trans hc
    · by_contra! hl
      have hg (z : Fin n) (hz : z ∈ B v) : G.Adj y z :=
        SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).2).1
      have hty := uniqueCommonCenter h4 hl (fun z hz => (ht z (Finset.mem_filter.mp hz).1).1) hg
      obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (B v).card)
      obtain ⟨hz',hu⟩ := Finset.mem_filter.mp hz
      exact (ht z hz').2 (hty ▸ hu)
  have hcard : (T.biUnion B).card ≤ T.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ v ∈ T, (1 : ℕ) := Finset.sum_le_sum hs
      _ = _ := by simp
  change (R.biUnion B).card ≤ _
  rw [hT]
  exact hcard.trans (familyFrontierCard hAO R)
end PEqualNP.Outside.L_meta_2264.Eligible

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
abbrev HasStar (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ a ∈ tops G C,
    (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1
abbrev ChoosesCenters (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (K : Finset (Fin n)) : Prop :=
  ∀ a ∈ tops G C \ centreless G C,
    ∃ c ∈ K, ∃ b : Fin 2, side (n := n) C a b = {c}
theorem nonCenterlessSides {a : ℕ} (ha : a ∈ tops G C \ centreless G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  obtain ⟨hat, hn⟩ := Finset.mem_sdiff.mp ha
  by_contra h
  apply hn
  refine Finset.mem_filter.mpr ⟨hat, ?_⟩
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  fin_cases b
  · exact Or.inl he
  · exact Or.inr he
theorem singletonSide (hstar : HasStar G C)
    {a : ℕ} (ha : a ∈ tops G C \ centreless G C) :
    ∃ c : Fin n, ∃ b : Fin 2, side (n := n) C a b = {c} := by
  rcases hstar a (Finset.mem_sdiff.mp ha).1 with h | h
  · have hpos := Finset.card_pos.mpr (nonCenterlessSides ha 0)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (show (side (n := n) C a 0).card = 1 by omega)
    exact ⟨c, 0, hc⟩
  · have hpos := Finset.card_pos.mpr (nonCenterlessSides ha 1)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (show (side (n := n) C a 1).card = 1 by omega)
    exact ⟨c, 1, hc⟩
theorem coversStars {K : Finset (Fin n)} (hK : ChoosesCenters G C K) :
    (G.deleteEdges (↑(Ustar G C))).IsVertexCover (↑K) := by
  intro u v huv
  obtain ⟨he, hn⟩ := SimpleGraph.deleteEdges_adj.mp huv
  have he' : s(u,v) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
  have hs : s(u,v) ∈ starEdges G C := by
    by_contra h
    exact hn (Finset.mem_sdiff.mpr ⟨he', h⟩)
  unfold starEdges at hs
  obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨⟨x,y⟩, hz, heq⟩ := Finset.mem_image.mp hb
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
  have hnc : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha, ?_⟩
    intro h
    rcases (Finset.mem_filter.mp h).2 with h | h
    · rw [h] at hx
      exact Finset.notMem_empty _ hx
    · rw [h] at hy
      exact Finset.notMem_empty _ hy
  obtain ⟨c, hc, i, hs⟩ := hK a hnc
  have hxy : x ∈ K ∨ y ∈ K := by
    fin_cases i
    · left
      change side (n := n) C a 0 = {c} at hs
      rw [hs, Finset.mem_singleton] at hx
      change x = c at hx
      exact hx ▸ hc
    · right
      change side (n := n) C a 1 = {c} at hs
      rw [hs, Finset.mem_singleton] at hy
      change y = c at hy
      exact hy ▸ hc
  change s(x,y) = s(u,v) at heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hxy
  · exact hxy.symm
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem availableAdjacentGuardUnique {S : Finset (Fin n)} {y y' z : Fin n}
    (h4 : NoFourCycle G) (h : Eligible.Available G C S)
    (hy : y ∈ S) (hy' : y' ∈ S) (hA : G.Adj z y) (hA' : G.Adj z y')
    (he : s(z,y) ∈ Ustar G C) : y = y' := by
  rcases h with h | ⟨t,ht⟩
  · exact Finset.card_le_one_iff.mp h hy hy'
  by_contra hyEq
  let R : Finset (Fin n) := {y,y'}
  have hR : 1 < R.card := Finset.one_lt_card.mpr ⟨y, by simp [R], y', by simp [R],hyEq⟩
  have htz := uniqueCommonCenter h4 hR (by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | h
    · exact (ht _ hy).1
    · obtain rfl := Finset.mem_singleton.mp h
      exact (ht _ hy').1) (by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | h
    · exact hA
    · obtain rfl := Finset.mem_singleton.mp h
      exact hA')
  exact (ht y hy).2 (htz ▸ he)
theorem chargedSupportSubset {w z : ℕ} (h : z ∈ Eligible.pureInternals G C w) :
    orIn n C z ⊆ orIn n C w :=
  orInTrans (Eligible.clippedAsOr (Eligible.clipMem.mp (Finset.mem_filter.mp h).1))
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def pureForCenter (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (c : Fin n) :
    Finset ℕ :=
  (NoPureMix G C).filter fun k =>
    1 < (orIn n C (n+k)).card ∧ ∀ v ∈ orIn n C (n+k), G.Adj c v
theorem pureForCenterDisjoint (h4 : NoFourCycle G) {a b : Fin n} (hn : a ≠ b) :
    Disjoint (pureForCenter G C a) (pureForCenter G C b) := by
  apply Finset.disjoint_left.mpr
  intro k ha hb
  obtain ⟨_,hc,hA⟩ := Finset.mem_filter.mp ha
  obtain ⟨_,_,hB⟩ := Finset.mem_filter.mp hb
  exact hn (uniqueCommonCenter h4 hc hA hB)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def pureForLeaves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (X : Finset (Fin n)) : Finset ℕ :=
  (NoPureMix G C).filter fun k => 1 < (orIn n C (n+k) ∩ X).card
theorem leavesCenterDisjoint (h4 : NoFourCycle G) {X : Finset (Fin n)} {c d : Fin n} (ne : c ≠ d)
    (adj : ∀ x ∈ X, G.Adj c x) : Disjoint (pureForLeaves G C X) (pureForCenter G C d) := by
  apply Finset.disjoint_left.mpr
  intro k hk hd
  obtain ⟨_,hK⟩ := Finset.mem_filter.mp hk
  obtain ⟨_,_,hD⟩ := Finset.mem_filter.mp hd
  exact ne (uniqueCommonCenter h4 hK
    (fun x hx => adj x (Finset.mem_inter.mp hx).2)
    (fun x hx => hD x (Finset.mem_inter.mp hx).1))
def RelevantStep (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (p q : ℕ) : Prop :=
  OrStep n C p q ∧ 1 < (orIn n C p ∩ X).card
abbrev RelevantReach (n : ℕ) (C : Circuit) (X : Finset (Fin n)) :=
  Relation.ReflTransGen (RelevantStep n C X)
private theorem notAvailable (h4 : NoFourCycle G) {c : Fin n} {X S : Finset (Fin n)}
    (adj : ∀ v ∈ X, G.Adj c v) (hU : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C)
    (big : 1 < (S ∩ X).card) : ¬ Eligible.Available G C S := by
  rintro (few | ⟨t,allowed⟩)
  · exact (Nat.not_le_of_lt big) ((Finset.card_le_card Finset.inter_subset_left).trans few)
  · have eq := uniqueCommonCenter h4 big
      (fun x hx => (allowed x (Finset.mem_inter.mp hx).1).1)
      (fun x hx => adj x (Finset.mem_inter.mp hx).2)
    obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp big
    subst t
    exact (hU x (Finset.mem_inter.mp hx).2 y (Finset.mem_inter.mp hy).2 ne).elim
      (allowed x (Finset.mem_inter.mp hx).1).2 (allowed y (Finset.mem_inter.mp hy).1).2
private theorem relevantImpliesOr {X : Finset (Fin n)} {w z : ℕ}
    (h : RelevantReach n C X w z) : Relation.ReflTransGen (OrStep n C) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step.1
private theorem relevantImpliesClipped (h4 : NoFourCycle G) {c : Fin n} {X : Finset (Fin n)}
    (adj : ∀ v ∈ X, G.Adj c v) (hU : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C) {w z : ℕ}
    (h : RelevantReach n C X w z) : Eligible.ClippedReach G C w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail ⟨step.1,notAvailable h4 adj hU step.2⟩
noncomputable def relevantCone (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (w+1)).filter (RelevantReach n C X w)
private theorem relevantMem {X : Finset (Fin n)} {w z : ℕ} :
    z ∈ relevantCone n C X w ↔ RelevantReach n C X w z := by
  classical
  simp only [relevantCone,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨Nat.lt_succ_of_le (orStep_le (relevantImpliesOr h)),h⟩⟩
private theorem relevantBoundary {X : Finset (Fin n)} {w : ℕ} {x : Fin n}
    (path : Relation.ReflTransGen (OrStep n C) w x.val) :
    ∃ z, RelevantReach n C X w z ∧ (orIn n C z ∩ X).card ≤ 1 ∧ x ∈ orIn n C z := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨x.val,Relation.ReflTransGen.refl, ?_,reach_mem_orIn x Relation.ReflTransGen.refl⟩
    rw [orInRaw x.isLt]
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton _)
  | @head a b step path ih =>
    by_cases many : 1 < (orIn n C a ∩ X).card
    · obtain ⟨z,hz,few,mem⟩ := ih
      exact ⟨z,hz.head ⟨step,many⟩,few,mem⟩
    · exact ⟨a,Relation.ReflTransGen.refl,by omega,reach_mem_orIn x (path.head step)⟩
theorem selectiveForestWithPoolAllowed (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (R : Finset ℕ) (hBound : ∀ w ∈ R, w < n + C.gates.length)
    (hPure : ∀ w ∈ R, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (c : Fin n) (X Q : Finset (Fin n)) (hQ : Q ⊆ X) (adj : ∀ x ∈ X, G.Adj c x)
    (covered : Q ⊆ R.biUnion (orIn n C)) (hU : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C) :
    ∃ P ⊆ pureForLeaves G C X, Q.card ≤ P.card + R.card ∧
      ∀ k ∈ P, ∃ w ∈ R, Relation.ReflTransGen (OrStep n C) w (n+k) := by
  classical
  let cone := R.biUnion (relevantCone n C X)
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let frontier := cone \ internal
  have rootIncluded : R ⊆ cone := by
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨w,hw,relevantMem.mpr Relation.ReflTransGen.refl⟩
  have internalIncluded : internal ⊆ cone := Finset.filter_subset _ _
  have childCoverage : cone \ R ⊆ internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1}) := by
    intro y hy
    obtain ⟨cy, notRoot⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨w,hR,yAt⟩ := Finset.mem_biUnion.mp cy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp yAt) with same | ⟨z,reach,last⟩
    · exact (notRoot (same ▸ hR)).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
        ⟨w,hR,relevantMem.mpr reach⟩,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,?_⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z - n = i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have branchCount : (internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤ 2 * internal.card := by
    refine Finset.card_biUnion_le.trans ?_
    have sum := Finset.sum_le_sum (s := internal) (fun v (_ : v ∈ internal) =>
      (Finset.card_insert_le (opnd C (v-n) 0) {opnd C (v-n) 1}).trans_eq
        (by simp : ({opnd C (v-n) 1} : Finset ℕ).card + 1 = 2))
    simpa [Nat.mul_comm] using sum
  have frontierCard : frontier.card ≤ internal.card + R.card := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    change (cone \ internal).card ≤ internal.card + R.card
    omega
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left : ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := internal.image (fun z => z-n)
  have iCount : P.card = internal.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x hx
    have yN := nle y hy
    change x-n = y-n at e
    omega
  have subP : P ⊆ pureForLeaves G C X := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨here,bigZ⟩ := Finset.mem_filter.mp hz
    obtain ⟨w,hw,zAt⟩ := Finset.mem_biUnion.mp here
    have zz : z ∈ Eligible.pureInternals G C w := Finset.mem_filter.mpr
      ⟨Eligible.clipMem.mpr (relevantImpliesClipped h4 adj hU (relevantMem.mp zAt)),
        nle z hz,notAvailable h4 adj hU bigZ⟩
    have nz := nle z hz
    have eq : n+(z-n)=z := by omega
    exact Finset.mem_filter.mpr ⟨Eligible.pureInternalsCharged hAO (hBound w hw) (hPure w hw) hcross zz,
      eq.symm ▸ bigZ⟩
  have trace (k : ℕ) (hk : k ∈ P) :
      ∃ w ∈ R, Relation.ReflTransGen (OrStep n C) w (n+k) := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨w,hw,here⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hz).1
    have hn := nle z hz
    have eq : n+(z-n)=z := by omega
    exact ⟨w,hw,eq.symm ▸ relevantImpliesOr (relevantMem.mp here)⟩
  let leaves (z : ℕ) := orIn n C z ∩ Q
  have coverage : Q ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨w,hw,rx⟩ := Finset.mem_biUnion.mp (covered hx)
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x rx)
    refine Finset.mem_biUnion.mpr ⟨z, ?_, Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w,hw,relevantMem.mpr zr⟩,
      fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atCone,notInt⟩ := Finset.mem_sdiff.mp hz
    have notBig : (orIn n C z ∩ X).card ≤ 1 :=
      Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
    have sub : leaves z ⊆ orIn n C z ∩ X := by
      intro a ha
      obtain ⟨l,r⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨l,hQ r⟩
    exact (Finset.card_le_card sub).trans notBig
  refine ⟨P,subP,?_,trace⟩
  calc
    Q.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ internal.card + R.card := frontierCard
    _ ≤ P.card + R.card := by omega
theorem selectiveForestWithPool (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (R : Finset ℕ) (hBound : ∀ w ∈ R, w < n + C.gates.length)
    (hPure : ∀ w ∈ R, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (c : Fin n) (X Q : Finset (Fin n)) (hQ : Q ⊆ X) (adj : ∀ x ∈ X, G.Adj c x)
    (covered : Q ⊆ R.biUnion (orIn n C)) (hU : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ pureForLeaves G C X, Q.card ≤ P.card + R.card ∧
      ∀ k ∈ P, ∃ w ∈ R, Relation.ReflTransGen (OrStep n C) w (n+k) :=
  selectiveForestWithPoolAllowed hAO h4 hcross R hBound hPure c X Q hQ adj covered
    (fun u hu _ _ _ => Or.inl (hU u hu))
theorem selectiveForest (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (R : Finset ℕ) (hBound : ∀ w ∈ R, w < n + C.gates.length)
    (hPure : ∀ w ∈ R, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (c : Fin n) (X Q : Finset (Fin n)) (hQ : Q ⊆ X) (adj : ∀ x ∈ X, G.Adj c x)
    (covered : Q ⊆ R.biUnion (orIn n C)) (hU : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    Q.card ≤ (pureForLeaves G C X).card + R.card := by
  obtain ⟨P,hP,hQ,_⟩ := selectiveForestWithPool hAO h4 hcross R hBound hPure c X Q hQ adj covered hU
  have hcard := Finset.card_le_card hP
  omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem guardForestAllowed (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (R : Finset ℕ) (hBound : ∀ w ∈ R, w < n + C.gates.length)
    (hPure : ∀ w ∈ R, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (c : Fin n) (neighbors : ∀ w ∈ R, ∀ v ∈ orIn n C w, G.Adj c v)
    (X : Finset (Fin n)) (sub : X ⊆ R.biUnion (orIn n C))
    (someU : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C) :
    X.card ≤ (pureForCenter G C c).card + R.card := by
  have adj (x : Fin n) (hx : x ∈ X) : G.Adj c x := by
    obtain ⟨w,hw,hxw⟩ := Finset.mem_biUnion.mp (sub hx)
    exact neighbors w hw x hxw
  obtain ⟨P,hp,hcap,ht⟩ := selectiveForestWithPoolAllowed hAO h4 hcross R hBound hPure
    c X X Finset.Subset.rfl adj sub someU
  have hsub : P ⊆ pureForCenter G C c := by
    intro k hk
    obtain ⟨hpay,hwidth⟩ := Finset.mem_filter.mp (hp hk)
    obtain ⟨w,hw,trace⟩ := ht k hk
    exact Finset.mem_filter.mpr ⟨hpay,
      hwidth.trans_le (Finset.card_le_card Finset.inter_subset_left),
      fun x hx => neighbors w hw x (orInTrans trace hx)⟩
  exact hcap.trans (Nat.add_le_add_right (Finset.card_le_card hsub) _)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264.SelectiveAllowed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem selectiveForestAllowed (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (R : Finset ℕ) (hBound : ∀ w ∈ R, w < n + C.gates.length)
    (hPure : ∀ w ∈ R, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (c : Fin n) (X Q : Finset (Fin n)) (hQ : Q ⊆ X) (adj : ∀ x ∈ X, G.Adj c x)
    (covered : Q ⊆ R.biUnion (orIn n C)) (hU : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C) :
    Q.card ≤ (pureForLeaves G C X).card + R.card := by
  obtain ⟨P,hp,hk,_⟩ := selectiveForestWithPoolAllowed hAO h4 hcross R hBound hPure c X Q hQ adj covered hU
  exact hk.trans (Nat.add_le_add_right (Finset.card_le_card hp) _)
end PEqualNP.Outside.L_meta_2264.SelectiveAllowed

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem summedForestOptionalSelective {ι : Type*} [DecidableEq ι] (I : Finset ι) (center : ι → Fin n)
    (roots : ι → Finset ℕ) (leaves : ι → Finset (Fin n)) (special : Option (Fin n))
    (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (hBound : ∀ i ∈ I, ∀ w ∈ roots i, w < n + C.gates.length)
    (hPure : ∀ i ∈ I, ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (hAdj : ∀ i ∈ I, some (center i) ≠ special → ∀ w ∈ roots i, ∀ v ∈ orIn n C w, G.Adj (center i) v)
    (hLeafAdj : ∀ i ∈ I, ∀ v ∈ leaves i, G.Adj (center i) v)
    (hCover : ∀ i ∈ I, leaves i ⊆ (roots i).biUnion (orIn n C))
    (hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → center i = center j → Disjoint (leaves i) (leaves j))
    (hPairs : ∀ i ∈ I, ∀ j ∈ I, center i = center j → ∀ u ∈ leaves i, ∀ v ∈ leaves j, u ≠ v →
      s(center i,u) ∈ Ustar G C ∨ s(center i,v) ∈ Ustar G C) :
    (∑ i ∈ I, (leaves i).card) ≤ (NoPureMix G C).card + ∑ i ∈ I, (roots i).card := by
  classical
  let Centers := I.image center
  let fiber (c : Fin n) := I.filter (fun i => center i = c)
  let targets (c : Fin n) := (fiber c).biUnion leaves
  let pay (c : Fin n) := if some c = special then pureForLeaves G C (targets c) else pureForCenter G C c
  have targetAdj (c v : Fin n) (hv : v ∈ targets c) : G.Adj c v := by
    obtain ⟨i,hi,has⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hI,eq⟩ := Finset.mem_filter.mp hi
    exact eq ▸ hLeafAdj i hI v has
  have each (c : Fin n) :
      (∑ i ∈ fiber c, (leaves i).card) ≤ (pay c).card + ∑ i ∈ fiber c, (roots i).card := by
    let X := (fiber c).biUnion leaves
    let R := (fiber c).biUnion roots
    have fiberDisj : (↑(fiber c) : Set ι).PairwiseDisjoint leaves := by
      intro i hi j hj ne
      obtain ⟨hi,ei⟩ := Finset.mem_filter.mp (show i ∈ fiber c from hi)
      obtain ⟨hj,ej⟩ := Finset.mem_filter.mp (show j ∈ fiber c from hj)
      exact hDisj i hi j hj ne (ei.trans ej.symm)
    have Xcard : X.card = ∑ i ∈ fiber c, (leaves i).card := Finset.card_biUnion fiberDisj
    have Rcard : R.card ≤ ∑ i ∈ fiber c, (roots i).card := Finset.card_biUnion_le
    have rootIndices (w : ℕ) (hw : w ∈ R) : ∃ i ∈ I, center i = c ∧ w ∈ roots i := by
      obtain ⟨i,iF,wi⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨iI,iC⟩ := Finset.mem_filter.mp iF
      exact ⟨i,iI,iC,wi⟩
    have sub : X ⊆ R.biUnion (orIn n C) := by
      intro v hv
      obtain ⟨i,iF,iv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨w,hi,hw⟩ := Finset.mem_biUnion.mp (hCover i (Finset.mem_filter.mp iF).1 iv)
      exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_biUnion.mpr ⟨i,iF,hi⟩,hw⟩
    have PairBits (u : Fin n) (hu : u ∈ X) (v : Fin n) (hv : v ∈ X) (ne : u ≠ v) :
        s(c,u) ∈ Ustar G C ∨ s(c,v) ∈ Ustar G C := by
      obtain ⟨i,iF,iu⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨j,jF,jv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨iI,eI⟩ := Finset.mem_filter.mp iF
      obtain ⟨jI,eJ⟩ := Finset.mem_filter.mp jF
      rw [← eI]
      exact hPairs i iI j jI (eI.trans eJ.symm) u iu v jv ne
    have rb (w : ℕ) (hw : w ∈ R) : w < n+C.gates.length := by
      obtain ⟨i,hI,_,hi⟩ := rootIndices w hw
      exact hBound i hI w hi
    have rp (w : ℕ) (hw : w ∈ R) (k : ℕ) (hr : OrReaches n C w k) :
        (gateAt C k).op ≠ GateOp.and := by
      obtain ⟨i,hI,_,hi⟩ := rootIndices w hw
      exact hPure i hI w hi k hr
    by_cases eq : some c = special
    · have count := SelectiveAllowed.selectiveForestAllowed hAO h4 hcross R rb rp c X X
        Finset.Subset.rfl (targetAdj c) sub PairBits
      change X.card ≤ (pureForLeaves G C (targets c)).card + R.card at count
      simp only [pay, if_pos eq]
      omega
    · have count := guardForestAllowed hAO h4 hcross R rb rp c
        (fun w hw => by
          obtain ⟨i,iI,iC,wi⟩ := rootIndices w hw
          exact iC ▸ hAdj i iI (fun h => eq (by rwa [← iC])) w wi) X sub PairBits
      simp only [pay,eq,if_false]
      omega
  have labelDisj : (↑Centers : Set (Fin n)).PairwiseDisjoint pay := by
    intro a _ b _ ne
    change Disjoint (pay a) (pay b)
    by_cases ea : some a = special
    · have eb : some b ≠ special := fun h => ne (Option.some.inj (ea.trans h.symm))
      simpa [pay,ea,eb] using leavesCenterDisjoint (G := G) (C := C) h4 ne (targetAdj a)
    · by_cases eb : some b = special
      · simpa [pay,ea,eb] using (leavesCenterDisjoint (G := G) (C := C) h4 ne.symm (targetAdj b)).symm
      · simpa [pay,ea,eb] using pureForCenterDisjoint (G := G) (C := C) h4 ne
  have Pcard : (∑ c ∈ Centers, (pay c).card) ≤ (NoPureMix G C).card := by
    rw [← Finset.card_biUnion labelDisj]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨c,_,m⟩ := Finset.mem_biUnion.mp hk
    by_cases h : some c = special
    · have hm : k ∈ pureForLeaves G C (targets c) := by simpa [pay,h] using m
      exact (Finset.mem_filter.mp hm).1
    · have hm : k ∈ pureForCenter G C c := by simpa [pay,h] using m
      exact (Finset.mem_filter.mp hm).1
  have maps : ∀ i ∈ I, center i ∈ Centers := fun _ h => Finset.mem_image_of_mem _ h
  have Lsum := Finset.sum_fiberwise_of_maps_to maps (fun i => (leaves i).card)
  have Rsum := Finset.sum_fiberwise_of_maps_to maps (fun i => (roots i).card)
  change (∑ c ∈ Centers, ∑ i ∈ fiber c, (leaves i).card) = _ at Lsum
  change (∑ c ∈ Centers, ∑ i ∈ fiber c, (roots i).card) = _ at Rsum
  have summed := Finset.sum_le_sum (s := Centers) (fun c _ => each c)
  rw [Finset.sum_add_distrib,Lsum,Rsum] at summed
  omega
theorem summedGuardForest {ι : Type*} [DecidableEq ι] (I : Finset ι) (center : ι → Fin n)
    (roots : ι → Finset ℕ) (leaves : ι → Finset (Fin n))
    (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (hBound : ∀ i ∈ I, ∀ w ∈ roots i, w < n + C.gates.length)
    (hPure : ∀ i ∈ I, ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (hAdj : ∀ i ∈ I, ∀ w ∈ roots i, ∀ v ∈ orIn n C w, G.Adj (center i) v)
    (hCover : ∀ i ∈ I, leaves i ⊆ (roots i).biUnion (orIn n C))
    (hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → center i = center j → Disjoint (leaves i) (leaves j))
    (hPairs : ∀ i ∈ I, ∀ j ∈ I, center i = center j → ∀ u ∈ leaves i, ∀ v ∈ leaves j, u ≠ v →
      s(center i,u) ∈ Ustar G C ∨ s(center i,v) ∈ Ustar G C) :
    (∑ i ∈ I, (leaves i).card) ≤ (NoPureMix G C).card + ∑ i ∈ I, (roots i).card := by
  have hLeafAdj (i : ι) (hi : i ∈ I) (v : Fin n) (hv : v ∈ leaves i) : G.Adj (center i) v := by
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp (hCover i hi hv)
    exact hAdj i hi w hw v hv
  exact summedForestOptionalSelective I center roots leaves none hAO h4 hcross hBound hPure
    (fun i hi _ => hAdj i hi) hLeafAdj hCover hDisj hPairs
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.TopForm PEqualNP.EdgeOwnership
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
def armEdge (u : Fin n) (D : Finset (Fin n)) (x y : Fin n) : Prop :=
  (x = u ∧ y ∈ D) ∨ (y = u ∧ x ∈ D)
def overlapEdge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (s x y : Fin n) : Prop :=
  (x = s ∧ safe G A B y) ∨ (y = s ∧ safe G A B x)
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.EdgeOwnership PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
def supportLeaves (E : Finset (Sym2 (Fin n))) (c : Fin n) (U : Finset (Fin n)) : Finset (Fin n) :=
  U.filter (fun w => s(c,w) ∈ E)
private theorem edgeInjective (c : Fin n) : Function.Injective (fun w : Fin n => s(c,w)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with both | swap
  · exact both.2
  · exact swap.2.trans swap.1
def supportEdges (E : Finset (Sym2 (Fin n))) (c : Fin n) (U : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (supportLeaves E c U).image (fun w => s(c,w))
theorem supportCard (E : Finset (Sym2 (Fin n))) (c : Fin n) (U : Finset (Fin n)) :
    (supportEdges E c U).card = (supportLeaves E c U).card :=
  Finset.card_image_of_injective _ (edgeInjective c)
theorem edgeFromArm {E : Finset (Sym2 (Fin n))} {c x y : Fin n} {D : Finset (Fin n)}
    (hE : s(x,y) ∈ E) (h : armEdge c D x y) : s(x,y) ∈ supportEdges E c D := by
  rcases h with ⟨rfl,hy⟩ | ⟨rfl,hx⟩
  · exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hE⟩,rfl⟩
  · exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,Sym2.eq_swap ▸ hE⟩,Sym2.eq_swap⟩
theorem sharedArmCard {E : Finset (Sym2 (Fin n))} {c d : Fin n} {D F : Finset (Fin n)}
    (hd : d ∈ D) (hc : c ∈ F) (on : s(c,d) ∈ E) :
    1 ≤ (supportEdges E c D ∩ supportEdges E d F).card := by
  apply Finset.card_pos.mpr
  refine ⟨s(c,d),Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · exact edgeFromArm on (Or.inl ⟨rfl,hd⟩)
  · exact edgeFromArm on (Or.inr ⟨rfl,hc⟩)
theorem twoArmTally (E : Finset (Sym2 (Fin n))) (c d : Fin n) (D F : Finset (Fin n))
    (hd : d ∈ D) (hc : c ∈ F) (covers : ∀ x y, s(x,y) ∈ E → armEdge c D x y ∨ armEdge d F x y) :
    E.card + (if s(c,d) ∈ E then 1 else 0) ≤ (supportLeaves E c D).card + (supportLeaves E d F).card := by
  classical
  have sub : E ⊆ supportEdges E c D ∪ supportEdges E d F := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rcases covers x y he with left | right
      · exact Finset.mem_union_left _ (edgeFromArm he left)
      · exact Finset.mem_union_right _ (edgeFromArm he right)
  have card := Finset.card_le_card sub
  have both := Finset.card_union_add_card_inter (supportEdges E c D) (supportEdges E d F)
  rw [supportCard,supportCard] at both
  by_cases edge : s(c,d) ∈ E
  · have common := sharedArmCard hd hc edge
    simp only [if_pos edge]
    omega
  · simp only [if_neg edge]
    omega
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (supportLeaves)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable def ctrByJunk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : Finset ℕ :=
  (centreless G C).filter fun a => InCone n C j a
noncomputable def mixByJunk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact (mixing G C).filter fun m => OrReaches n C (n+m) j ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) m
theorem ctrByJunkDisjoint {p q : ℕ} (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a) :
    Disjoint (ctrByJunk G C p) (ctrByJunk G C q) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have ha' := Finset.mem_filter.mp ha
  exact apart _ (Finset.mem_filter.mp ha'.1).1 ha'.2 (Finset.mem_filter.mp hb).2
theorem mixByJunkDisjoint (hAO : IsAO2 n C) {p q : ℕ}
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a) :
    Disjoint (mixByJunk G C p) (mixByJunk G C q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hmp hmq
  have rp := (Finset.mem_filter.mp hmp).2
  have rq := (Finset.mem_filter.mp hmq).2.1
  obtain ⟨a,ha,b,rb⟩ := rp.2
  have al := (topData ha).1
  exact apart a ha (operandReachCone hAO al (reachTrans rb rp.1))
    (operandReachCone hAO al (reachTrans rb rq))
noncomputable def ctrWitnesses (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact (centreless G C).filter fun a => ∃ b : Fin 2,
    side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) j
noncomputable def ctrRoot (n : ℕ) (C : Circuit) (a : ℕ) : ℕ :=
  if side (n := n) C a 0 = ∅ then opnd C a 1 else opnd C a 0
noncomputable def ctrRoots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : Finset ℕ :=
  (ctrWitnesses G C j).image (ctrRoot n C)
private theorem ctrRootEq {a : ℕ} {b : Fin 2}
    (empty : side (n := n) C a b = ∅) (nonempty : (side (n := n) C a (1-b)).Nonempty) :
    ctrRoot n C a = opnd C a (1-b) := by
  fin_cases b
  · change side (n := n) C a 0 = ∅ at empty
    simp [ctrRoot,empty]
  · change (side (n := n) C a 0).Nonempty at nonempty
    simp [ctrRoot,Finset.nonempty_iff_ne_empty.mp nonempty]
theorem rootProperties (hAO : IsAO2 n C) (hT : TopForm G C) {p q j w : ℕ}
    (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (num : j = p ∨ j = q) (hw : w ∈ ctrRoots G C j) :
    w < n + C.gates.length ∧ (∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and) ∧
      orIn n C w ⊆ wmax G C j := by
  classical
  obtain ⟨a,hA,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨ctr,b,empty,reach⟩ := Finset.mem_filter.mp hA
  have ht := (Finset.mem_filter.mp ctr).1
  have ha := (topData ht).1
  have pure := pureOppositeOperand hAO hT hj apart ht reach num
  have before := opndBound hAO ha (1-b)
  have lt : opnd C a (1-b) < n + C.gates.length := by omega
  have nonempty := pureOrNonempty hAO lt pure
  rw [ctrRootEq empty nonempty]
  exact ⟨lt,pure,oppositeSideWmax hAO ht reach⟩
theorem ctrRootCard (hAO : IsAO2 n C) (j : ℕ) :
    (ctrRoots G C j).card ≤ (ctrByJunk G C j).card := by
  classical
  refine Finset.card_image_le.trans (Finset.card_le_card ?_)
  intro a ha
  obtain ⟨hc,b,_,reach⟩ := Finset.mem_filter.mp ha
  have ht := (Finset.mem_filter.mp hc).1
  exact Finset.mem_filter.mpr ⟨hc,operandReachCone hAO (topData ht).1 reach⟩
def servedBy (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u,v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧
    gateVal n C j (pairInput u v) = true
theorem servedByPair {j : ℕ} {u v : Fin n} (h : servedBy G C j s(u,v)) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨x,y,eq,a,ha,b,haOn,hr,hjOn⟩ := h
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨a,ha,b,haOn,hr,hjOn⟩
  · have flip : pairInput v u = pairInput u v := by funext j; simp [pairInput,or_comm]
    exact ⟨a,ha,b,flip ▸ haOn,hr,flip ▸ hjOn⟩
theorem guardOrMix (hAO : IsAO2 n C) (hT : TopForm G C) (hcross : HasCross G C) {p q j : ℕ}
    (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (num : j = p ∨ j = q) {c y : Fin n} (cn : c ∉ wmax G C j)
    (he : s(c,y) ∈ Ustar G C) (hServed : servedBy G C j s(c,y)) :
    (y ∈ (ctrRoots G C j).biUnion (orIn n C)) ∨
    (∃ m ∈ mixByJunk G C j, (orIn n C (n+m)).Nonempty ∧
      ∀ x ∈ orIn n C (n+m), G.Adj x y ∧ x ≠ c) := by
  classical
  obtain ⟨a,ha,b,on,hr,_⟩ := servedByPair hServed
  by_cases centre : a ∈ centreless G C
  · obtain ⟨choice,guards⟩ := ustarAttaches hAO hT hj apart ha hr num on
    have yes : y ∈ side (n := n) C a (1-b) := choice.resolve_left (fun r => cn (guards r))
    have ne : (side (n := n) C a (1-b)).Nonempty := ⟨_,yes⟩
    have empty : side (n := n) C a b = ∅ := by
      have hh := (Finset.mem_filter.mp centre).2
      fin_cases b
      · exact hh.resolve_right (Finset.nonempty_iff_ne_empty.mp ne)
      · exact hh.resolve_left (Finset.nonempty_iff_ne_empty.mp ne)
    have hRoot : ctrRoot n C a ∈ ctrRoots G C j := Finset.mem_image.mpr
      ⟨a,Finset.mem_filter.mpr ⟨centre,b,empty,hr⟩,rfl⟩
    exact Or.inl (Finset.mem_biUnion.mpr ⟨ctrRoot n C a,hRoot,ctrRootEq empty ne |>.symm ▸ yes⟩)
  · obtain ⟨m,hm,reachM,reachJ,leaf,safe,one,nonnull,edges⟩ :=
      edgeSlice hAO hT hj apart ha hr num on he centre hcross
    have hleaf : leaf = y := one.resolve_left (fun h => cn (h ▸ safe))
    subst leaf
    exact Or.inr ⟨m,Finset.mem_filter.mpr ⟨hm,reachJ,a,ha,b,reachM⟩,nonnull,
      fun x hx => ⟨(edges x hx).1,(edges x hx).2.1⟩⟩
theorem mixedOutsideSet (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    {p q j : ℕ} (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, servedBy G C j e) (c : Fin n) (cn : c ∉ wmax G C j)
    (M : Finset ℕ) (allowed : ∀ v, s(c,v) ∈ E → ∀ m ∈ mixByJunk G C j,
      (orIn n C (n+m)).Nonempty → (∀ x ∈ orIn n C (n+m), G.Adj x v ∧ x ≠ c) → m ∈ M) :
    (supportLeaves E c Finset.univ \ (ctrRoots G C j).biUnion (orIn n C)).card ≤ M.card := by
  classical
  let B := supportLeaves E c Finset.univ \ (ctrRoots G C j).biUnion (orIn n C)
  have good (v : {v // v ∈ B}) : ∃ m ∈ M, (orIn n C (n+m)).Nonempty ∧
      ∀ x ∈ orIn n C (n+m), G.Adj x v.val ∧ x ≠ c := by
    obtain ⟨hx,notRoot⟩ := Finset.mem_sdiff.mp v.property
    have he := (Finset.mem_filter.mp hx).2
    obtain ⟨m,hm,hn,hx⟩ := (guardOrMix hAO hT hcross hj apart num cn (sub he) (serve _ he)).resolve_left notRoot
    exact ⟨m,allowed _ he _ hm hn hx,hn,hx⟩
  let select (v : {v // v ∈ B}) := Classical.choose (good v)
  have result (v : {v // v ∈ B}) := Classical.choose_spec (good v)
  have b := Finset.card_le_card_of_injOn select (s := B.attach) (t := M) (fun v _ => (result v).1) ?_
  · rwa [Finset.card_attach] at b
  · intro v hv w hw eq
    apply Subtype.ext
    obtain ⟨x,hx⟩ := (result v).2.1
    have h1 := (result v).2.2 x hx
    have hx' : x ∈ orIn n C (n + select w) := by rw [← eq]; exact hx
    have h2 := (result w).2.2 x hx'
    have edge (v : {v // v ∈ B}) : G.Adj c v.val := by
      have h := (Finset.mem_filter.mp (Finset.mem_sdiff.mp v.property).1).2
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (sub h)).1
    apply uniqueCommonCenter h4 (S := {c,x}) ?_ ?_ ?_
    · simp [Finset.card_insert_of_notMem,Ne.symm h1.2]
    · intro u hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (edge v).symm
      · exact h1.1.symm
    · intro u hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (edge w).symm
      · exact h2.1.symm
theorem mixedOutsideRoots (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    {p q j : ℕ} (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, servedBy G C j e) (c : Fin n) (cn : c ∉ wmax G C j) :
    (supportLeaves E c Finset.univ \ (ctrRoots G C j).biUnion (orIn n C)).card ≤ (mixByJunk G C j).card :=
  mixedOutsideSet hAO hT h4 hcross hj apart num E sub serve c cn _ (fun _ _ _ h _ _ => h)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (armEdge supportLeaves twoArmTally)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def two {α : Type*} (a b : α) (i : Fin 2) : α := if i = 0 then a else b
theorem two_zero {α : Type*} (a b : α) : two a b 0 = a := by simp [two]
theorem two_one {α : Type*} (a b : α) : two a b 1 = b := by simp [two]
structure PairRequest (E : Finset (Sym2 (Fin n))) (c d : Fin n)
    (extra : Option (Fin 2)) (mixedBudget centreBudget : ℕ) where
  roots : Fin 2 → Finset ℕ
  leaves : Fin 2 → Finset (Fin n)
  mixed : ℕ
  bound : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length
  pure : ∀ i, ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and
  adjacent : ∀ i, ∀ w ∈ roots i, ∀ x ∈ orIn n C w, G.Adj (two c d i) x
  covered : ∀ i, leaves i ⊆ (roots i).biUnion (orIn n C)
  targets : ∀ i x, x ∈ leaves i → s(two c d i,x) ∈ E ∨ (extra = some i ∧ x = two d c i)
  tally : E.card + (if s(c,d) ∈ E then 1 else if extra.isSome then 1 else 0) ≤
    (leaves 0).card + (leaves 1).card + mixed
  cost : (roots 0).card + (roots 1).card + mixed ≤ 1 + mixedBudget + centreBudget
private noncomputable def extendLeaves (base : Finset (Fin n)) (extra : Option (Fin 2))
    (i : Fin 2) (other : Fin n) : Finset (Fin n) :=
  if extra = some i then insert other base else base
private theorem mem_extendLeaves {base : Finset (Fin n)} {extra : Option (Fin 2)}
    {i : Fin 2} {other x : Fin n} (h : x ∈ extendLeaves base extra i other) :
    x ∈ base ∨ (extra = some i ∧ x = other) := by
  classical
  by_cases e : extra = some i
  · rw [extendLeaves,if_pos e,Finset.mem_insert] at h
    exact h.elim (fun r => Or.inr ⟨e,r⟩) Or.inl
  · left
    simpa [extendLeaves,e] using h
private theorem extendLeavesCovered {base all : Finset (Fin n)} (h : base ⊆ all) {extra : Option (Fin 2)}
    {i : Fin 2} {other : Fin n} (hb : other ∈ all) : extendLeaves base extra i other ⊆ all :=
  fun _ hx => (mem_extendLeaves hx).elim (fun r => h r) (fun r => r.2 ▸ hb)
private theorem extendLeavesCard (base : Finset (Fin n)) (extra : Option (Fin 2))
    (i : Fin 2) (other : Fin n) (h : extra = some i → other ∉ base) :
    (extendLeaves base extra i other).card = base.card + (if extra = some i then 1 else 0) := by
  classical
  by_cases e : extra = some i
  · simp [extendLeaves,e,Finset.card_insert_of_notMem (h e)]
  · simp [extendLeaves,e]
private theorem connectorCount (E : Finset (Sym2 (Fin n))) (c d : Fin n) (extra : Option (Fin 2))
    (h : extra.isSome = true → s(c,d) ∉ E) :
    (if s(c,d) ∈ E then 1 else if extra.isSome then 1 else 0 : ℕ) =
    (if s(c,d) ∈ E then 1 else 0) +
      (if extra = some 0 then 1 else 0) + (if extra = some 1 then 1 else 0) := by
  classical
  cases extra with
  | none => by_cases ne : s(c,d) ∈ E <;> simp [ne]
  | some a =>
    have no := h rfl
    fin_cases a <;> simp [no]
private theorem infersLeaf {E : Finset (Sym2 (Fin n))} {u v : Fin n} {B : Finset (Fin n)}
    (h : v ∈ supportLeaves E u B) : s(u,v) ∈ E :=
  (Finset.mem_filter.mp h).2
theorem ordinaryPairRequests (hAO : IsAO2 n C) (hT : TopForm G C) {p q j : ℕ}
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (hmem : j ∈ junk G C) (E : Finset (Sym2 (Fin n))) (c d : Fin n)
    {D F : Finset (Fin n)}
    (dRaw : D = side (n := n) C j 0 ∨ D = side (n := n) C j 1)
    (fRaw : F = side (n := n) C j 0 ∨ F = side (n := n) C j 1)
    (hd : d ∈ D) (hc : c ∈ F) (dAdj : ∀ x ∈ D, G.Adj c x) (fAdj : ∀ x ∈ F, G.Adj d x)
    (covers : ∀ x y, s(x,y) ∈ E → armEdge c D x y ∨ armEdge d F x y)
    (extra : Option (Fin 2)) (no : extra.isSome = true → s(c,d) ∉ E)
    (mixCount ctrCount : ℕ) (hasTag : 1 ≤ mixCount + ctrCount) :
    Nonempty (PairRequest (G := G) (C := C) E c d extra mixCount ctrCount) := by
  classical
  obtain ⟨bi,he⟩ : ∃ i : Fin 2, D = side (n := n) C j i :=
    dRaw.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  obtain ⟨bj,hf⟩ : ∃ i : Fin 2, F = side (n := n) C j i :=
    fRaw.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  subst D F
  let X := supportLeaves E c (side (n := n) C j bi)
  let Y := supportLeaves E d (side (n := n) C j bj)
  let LX := extendLeaves X extra 0 d
  let LY := extendLeaves Y extra 1 c
  have rootBound (i : Fin 2) : opnd C j i < n + C.gates.length :=
    (opndBound hAO (junkData hmem).1 i).trans (Nat.add_lt_add_left (junkData hmem).1 _)
  have rootPure (i : Fin 2) := pureJunkOperand hAO hT hj pq qp hmem (b := i)
  have leftSub : LX ⊆ side (n := n) C j bi :=
    extendLeavesCovered (Finset.filter_subset _ _) hd
  have rightSub : LY ⊆ side (n := n) C j bj :=
    extendLeavesCovered (Finset.filter_subset _ _) hc
  have xc : LX.card = X.card + (if extra = some 0 then 1 else 0) :=
    extendLeavesCard X extra 0 d (fun r hm => no (by simp [r]) (infersLeaf hm))
  have yc : LY.card = Y.card + (if extra = some 1 then 1 else 0) :=
    extendLeavesCard Y extra 1 c (fun r hm => no (by simp [r]) (Sym2.eq_swap ▸ infersLeaf hm))
  refine ⟨⟨two {opnd C j bi} {opnd C j bj},two LX LY,0,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i w hw
    fin_cases i
    · simp [two_zero] at hw; exact hw.symm ▸ rootBound bi
    · simp [two_one] at hw; exact hw.symm ▸ rootBound bj
  · intro i w hw k hr
    fin_cases i
    · simp [two_zero] at hw; exact rootPure bi k (hw ▸ hr)
    · simp [two_one] at hw; exact rootPure bj k (hw ▸ hr)
  · intro i w hw x hx
    fin_cases i
    · simp [two_zero] at hw ⊢; subst w; exact dAdj x (show x ∈ side C j bi from hx)
    · simp [two_one] at hw ⊢; subst w; exact fAdj x (show x ∈ side C j bj from hx)
  · intro i x hx
    fin_cases i
    · exact Finset.mem_biUnion.mpr ⟨opnd C j bi,by simp [two_zero],
        (show x ∈ side C j bi from leftSub (show x ∈ LX from hx))⟩
    · exact Finset.mem_biUnion.mpr ⟨opnd C j bj,by simp [two_one],
        (show x ∈ side C j bj from rightSub (show x ∈ LY from hx))⟩
  · intro i x hx
    fin_cases i
    · simp only [two_zero] at hx ⊢
      exact (mem_extendLeaves hx).imp infersLeaf id
    · simp only [two_one] at hx ⊢
      exact (mem_extendLeaves hx).imp infersLeaf id
  · simp only [two_zero,two_one,xc,yc,Nat.add_zero,connectorCount E c d extra no]
    have h := twoArmTally E c d _ _ hd hc covers
    change E.card + _ ≤ X.card + Y.card at h
    omega
  · simp only [two_zero,two_one,Finset.card_singleton]
    omega
theorem overlapPairRequests (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q j : ℕ} (hj : junk G C = {p,q})
    (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, servedBy G C j e) (c d : Fin n) {D : Finset (Fin n)}
    (dRaw : D = side (n := n) C j 0 ∨ D = side (n := n) C j 1)
    (hd : d ∈ D) (dAdj : ∀ x ∈ D, G.Adj c x) (safe : ∀ w ∈ wmax G C j, G.Adj d w)
    (covers : ∀ x y, s(x,y) ∈ E → armEdge c D x y ∨ armEdge d Finset.univ x y)
    (extra : Option (Fin 2)) (no : extra.isSome = true → s(c,d) ∉ E) (right : extra ≠ some 1)
    (M : Finset ℕ) (allowed : ∀ v, s(d,v) ∈ E → ∀ m ∈ mixByJunk G C j,
      (orIn n C (n+m)).Nonempty → (∀ x ∈ orIn n C (n+m), G.Adj x v ∧ x ≠ d) → m ∈ M) :
    Nonempty (PairRequest (G := G) (C := C) E c d extra M.card (ctrByJunk G C j).card) := by
  classical
  obtain ⟨bi,he⟩ : ∃ i : Fin 2, D = side (n := n) C j i :=
    dRaw.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  subst D
  have hmem : j ∈ junk G C := by simpa [hj] using num
  let X := supportLeaves E c (side (n := n) C j bi)
  let LX := extendLeaves X extra 0 d
  let R := ctrRoots G C j
  let Y := supportLeaves E d Finset.univ
  let LY := Y ∩ R.biUnion (orIn n C)
  let MY := Y \ R.biUnion (orIn n C)
  have properties {w : ℕ} (h : w ∈ R) := rootProperties hAO hT hj apart num h
  have rootBound : opnd C j bi < n + C.gates.length :=
    (opndBound hAO (junkData hmem).1 bi).trans (Nat.add_lt_add_left (junkData hmem).1 _)
  have rootPure := pureJunkOperand hAO hT hj pq qp hmem (b := bi)
  have leftSub : LX ⊆ side (n := n) C j bi :=
    extendLeavesCovered (Finset.filter_subset _ _) hd
  have xc : LX.card = X.card + (if extra = some 0 then 1 else 0) :=
    extendLeavesCard X extra 0 d (fun r hm => no (by simp [r]) (infersLeaf hm))
  have yc : MY.card + LY.card = Y.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : LY ⊆ Y)
    have eq : MY = Y \ LY := by ext x; simp [MY,LY]
    rw [eq]
    exact h
  have mix : MY.card ≤ M.card :=
    mixedOutsideSet hAO hT h4 cross hj apart num E sub serve d (fun dm => G.irrefl (safe d dm)) M allowed
  have cs : R.card ≤ (ctrByJunk G C j).card := ctrRootCard hAO j
  refine ⟨⟨two {opnd C j bi} R,two LX LY,MY.card,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i w hw
    fin_cases i
    · simp [two_zero] at hw; exact hw.symm ▸ rootBound
    · exact (properties (by simpa [two_one] using hw)).1
  · intro i w hw k hr
    fin_cases i
    · simp [two_zero] at hw; exact rootPure k (hw ▸ hr)
    · exact (properties (by simpa [two_one] using hw)).2.1 k hr
  · intro i w hw x hx
    fin_cases i
    · simp [two_zero] at hw ⊢; subst w; exact dAdj x (show x ∈ side C j bi from hx)
    · simp only [two_one] at hw ⊢
      exact safe x ((properties hw).2.2 hx)
  · intro i x hx
    fin_cases i
    · exact Finset.mem_biUnion.mpr ⟨opnd C j bi,by simp [two_zero],
        (show x ∈ side C j bi from leftSub (show x ∈ LX from hx))⟩
    · simp only [two_one] at hx ⊢
      exact (Finset.mem_inter.mp hx).2
  · intro i x hx
    fin_cases i
    · simp only [two_zero] at hx ⊢
      exact (mem_extendLeaves hx).imp infersLeaf id
    · simp only [two_one] at hx ⊢
      exact Or.inl (infersLeaf ((Finset.mem_inter.mp hx).1))
  · simp only [two_zero,two_one,xc,connectorCount E c d extra no,if_neg right,Nat.add_zero]
    have h := twoArmTally E c d _ _ hd (Finset.mem_univ c) covers
    change E.card + _ ≤ X.card + Y.card at h
    omega
  · simp only [two_zero,two_one,Finset.card_singleton]
    omega
theorem two_injective {α : Type*} {a b : α} (h : a ≠ b) :
    Function.Injective (two a b) := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all [two_zero,two_one]
private theorem two_pair {c d : Fin n} (i : Fin 2) :
    s(two c d i,two d c i) = s(c,d) := by
  fin_cases i
  · simp [two_zero]
  · exact (Sym2.eq_swap (a := d) (b := c))
theorem pairedRequestTally (hAO : IsAO2 n C) (h4 : NoFourCycle G) (cross : HasCross G C)
    (E : Bool → Finset (Sym2 (Fin n))) (c d : Bool → Fin n) (extra : Bool → Option (Fin 2))
    (M Z : Bool → ℕ) (B : ∀ b, PairRequest (G := G) (C := C) (E b) (c b) (d b) (extra b) (M b) (Z b))
    (ne : ∀ b, c b ≠ d b) (union : E false ∪ E true = Ustar G C) (dis : Disjoint (E false) (E true))
    (exNo : ∀ b, (extra b).isSome = true → s(c b,d b) ∉ Ustar G C)
    (exApart : ∀ i j, extra false = some i → extra true = some j →
      two (c false) (d false) i ≠ two (c true) (d true) j) :
    (Ustar G C).card +
      (if s(c false,d false) ∈ E false then 1 else if (extra false).isSome then 1 else 0) +
      (if s(c true,d true) ∈ E true then 1 else if (extra true).isSome then 1 else 0) ≤
    (NoPureMix G C).card + 2 + (M false + M true) + (Z false + Z true) := by
  classical
  let I : Finset (Bool × Fin 2) := Finset.univ
  let center (i : Bool × Fin 2) := two (c i.1) (d i.1) i.2
  let roots (i : Bool × Fin 2) := (B i.1).roots i.2
  let leaves (i : Bool × Fin 2) := (B i.1).leaves i.2
  have Sub (b : Bool) : E b ⊆ Ustar G C := by
    cases b
    · exact union ▸ Finset.subset_union_left
    · exact union ▸ Finset.subset_union_right
  have genuine (i : Bool × Fin 2) (x : Fin n) (hx : x ∈ leaves i) :
      s(center i,x) ∈ E i.1 ∨ (extra i.1 = some i.2 ∧ x = two (d i.1) (c i.1) i.2) :=
    (B i.1).targets i.2 x hx
  have extraNo (i : Bool × Fin 2) (x : Fin n)
      (h : extra i.1 = some i.2 ∧ x = two (d i.1) (c i.1) i.2) :
      s(center i,x) ∉ Ustar G C := by
    rw [h.2]
    change s(two (c i.1) (d i.1) i.2,two (d i.1) (c i.1) i.2) ∉ Ustar G C
    rw [two_pair]
    exact exNo i.1 (by rw [h.1]; rfl)
  have same (i j : Bool × Fin 2) (bb : i.1 = j.1) (cc : center i = center j) : i = j := by
    apply Prod.ext bb
    change two (c i.1) (d i.1) i.2 = two (c j.1) (d j.1) j.2 at cc
    rw [← bb] at cc
    exact two_injective (ne _) cc
  have diff (i j : Bool × Fin 2) (cc : center i = center j) (ei : extra i.1 = some i.2)
      (ej : extra j.1 = some j.2) : i = j := by
    by_cases eq : i.1 = j.1
    · exact same _ _ eq cc
    obtain ⟨ii,iii⟩ := i
    obtain ⟨jj,jjj⟩ := j
    cases ii <;> cases jj
    · exact (eq rfl).elim
    · exact (exApart iii jjj ei ej cc).elim
    · exact (exApart jjj iii ej ei cc.symm).elim
    · exact (eq rfl).elim
  have leafDis (i j : Bool × Fin 2) (_ : i ∈ I) (_ : j ∈ I) (neq : i ≠ j)
      (cc : center i = center j) : Disjoint (leaves i) (leaves j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases genuine i x hx with ax | ax <;> rcases genuine j x hy with ay | ay
    · by_cases eq : i.1 = j.1
      · exact neq (same _ _ eq cc)
      rw [← cc] at ay
      obtain ⟨ii,iii⟩ := i
      obtain ⟨jj,jjj⟩ := j
      cases ii <;> cases jj
      · exact eq rfl
      · exact Finset.disjoint_left.mp dis ax ay
      · exact Finset.disjoint_left.mp dis ay ax
      · exact eq rfl
    · exact extraNo _ _ ay (cc ▸ Sub _ ax)
    · exact extraNo _ _ ax (cc.symm ▸ Sub _ ay)
    · exact neq (diff _ _ cc ax.1 ay.1)
  have pairs (i j : Bool × Fin 2) (_ : i ∈ I) (_ : j ∈ I)
      (cc : center i = center j) (x : Fin n) (hx : x ∈ leaves i) (y : Fin n)
      (hy : y ∈ leaves j) (hn : x ≠ y) : s(center i,x) ∈ Ustar G C ∨ s(center i,y) ∈ Ustar G C := by
    rcases genuine i x hx with ax | ax
    · exact Or.inl (Sub _ ax)
    rcases genuine j y hy with ay | ay
    · exact Or.inr (cc.symm ▸ Sub _ ay)
    obtain rfl := diff _ _ cc ax.1 ay.1
    exact (hn (ax.2.trans ay.2.symm)).elim
  have forest := summedGuardForest I center roots leaves hAO h4 cross
    (fun i _ => (B i.1).bound i.2) (fun i _ => (B i.1).pure i.2)
    (fun i _ => (B i.1).adjacent i.2) (fun i _ => (B i.1).covered i.2)
    (fun i hi j hj => leafDis i j hi hj) (fun i hi j hj => pairs i j hi hj)
  change (∑ i : Bool × Fin 2, (leaves i).card) ≤ _ + ∑ i : Bool × Fin 2, (roots i).card at forest
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at forest
  simp only [Fin.sum_univ_two,Fintype.sum_bool,leaves,roots] at forest
  have ct0 := (B false).tally
  have ct1 := (B true).tally
  have pay0 := (B false).cost
  have pay1 := (B true).cost
  have card := Finset.card_union_of_disjoint dis
  rw [union] at card
  omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264

namespace UsefulJunk2264
open PEqualNP.EdgeOwnership PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
abbrev routedEdge (R : Fin n → Fin n → Prop) (x y : Fin n) := R x y ∨ R y x
def routeClosed (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (R : Fin n → Fin n → Prop) : Prop :=
  (∀ x y, R x y → safe G A B x ∧ hits A (pairInput x y) ∧ hits B (pairInput x y)) ∧
  ∀ x y z, R x y → hits A (pairInput x z) → hits B (pairInput x z) → R x z
def routedTwoLabelPlan (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (R : Fin n → Fin n → Prop) : Prop :=
  ∃ (u v : Fin n) (D : Finset (Fin n)), u ≠ v ∧ (D = A ∨ D = B) ∧ v ∈ D ∧
    (∀ x ∈ D, G.Adj u x) ∧ routedEdge R u v ∧
    ((∃ F : Finset (Fin n), (F = A ∨ F = B) ∧ u ∈ F ∧ (∀ x ∈ F, G.Adj v x) ∧
       ∀ x y, routedEdge R x y → armEdge u D x y ∨ armEdge v F x y) ∨
     ((∀ x, safe G A B x → G.Adj v x) ∧
       ∀ x y, routedEdge R x y → armEdge u D x y ∨ overlapEdge G A B v x y))
private theorem pairSwap (a b : Fin n) : pairInput a b = pairInput b a := by
  funext x
  simp [pairInput,or_comm]
private theorem safeSwap {A B : Finset (Fin n)} {x : Fin n} (h : safe G A B x) :
    safe G B A x :=
  fun z b a yes => h z a b yes
private theorem closedSwap {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) : routeClosed G B A R :=
  ⟨fun x y h => let ⟨hs,ha,hb⟩ := closed.1 x y h; ⟨safeSwap hs,hb,ha⟩,
   fun x y z h hb ha => closed.2 x y z h ha hb⟩
private theorem planSwap {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (p : routedTwoLabelPlan G B A R) : routedTwoLabelPlan G A B R := by
  obtain ⟨u,v,D,ne,dRaw,hd,dAdj,hConnector,next⟩ := p
  refine ⟨u,v,D,ne,dRaw.symm,hd,dAdj,hConnector,?_⟩
  rcases next with ⟨F,fRaw,hf,fAdj,covers⟩ | ⟨all,cover⟩
  · exact Or.inl ⟨F,fRaw.symm,hf,fAdj,covers⟩
  · refine Or.inr ⟨fun x h => all x (safeSwap h),fun x y h => ?_⟩
    refine (cover x y h).imp id ?_
    rintro (⟨e,h⟩|⟨e,h⟩)
    · exact Or.inl ⟨e,safeSwap h⟩
    · exact Or.inr ⟨e,safeSwap h⟩
private theorem pairProd {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) {x y : Fin n} (h : routedEdge R x y) :
    prod G A B x y := by
  rcases h with h | h
  · obtain ⟨g,a,b⟩ := closed.1 x y h
    exact ⟨a,b,Or.inl g⟩
  · obtain ⟨g,a,b⟩ := closed.1 y x h
    rw [pairSwap y x] at a b
    exact ⟨a,b,Or.inr g⟩
private theorem connector {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) {u v y : Fin n} (real : R u y)
    (hu : u ∈ A) (hv : v ∈ B) : R u v :=
  closed.2 u y v real ⟨u,hu,by simp [pairInput]⟩ ⟨v,hv,by simp [pairInput]⟩
private theorem oppArm {A B : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ A) (guard : safe G A B u) (p : prod G A B u v) : v ∈ B :=
  (pairHit p.2.1).resolve_left (fun hh => G.irrefl (common_neighbor guard hu u hh))
private theorem oppositeOverlap {A B : Finset (Fin n)} {x y : Fin n}
    (ha : x ∉ A) (hb : x ∉ B) (p : prod G A B x y) : y ∈ A ∩ B :=
  Finset.mem_inter.mpr ⟨(pairHit p.1).resolve_left ha,(pairHit p.2.1).resolve_left hb⟩
private theorem overlapUnguarded {A B : Finset (Fin n)} {s : Fin n} (hs : s ∈ A ∩ B) :
    ¬ safe G A B s :=
  fun g => G.irrefl (overlap_neighbor hs g)
private theorem overlapRoute {A B : Finset (Fin n)} {s x y : Fin n} (hs : s ∈ A ∩ B)
    (p : prod G A B x y) (h : x = s ∨ y = s) : overlapEdge G A B s x y := by
  rcases h with rfl | rfl
  · exact Or.inl ⟨rfl,p.2.2.resolve_left (overlapUnguarded hs)⟩
  · exact Or.inr ⟨rfl,p.2.2.resolve_right (overlapUnguarded hs)⟩
private theorem shortDirected {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) {u y s : Fin n} (ua : u ∈ A) (uy : R u y)
    (hs : s ∈ A ∩ B) (short : A ⊆ {s,u}) : routedTwoLabelPlan G A B R := by
  have guard := (closed.1 u y uy).1
  have une : u ≠ s := fun e => overlapUnguarded hs (e ▸ guard)
  have sb := (Finset.mem_inter.mp hs).2
  refine ⟨u,s,B,une,Or.inr rfl,sb,common_neighbor guard ua,Or.inl (connector closed uy ua sb),
    Or.inr ⟨fun w h => overlap_neighbor hs h,fun x z route => ?_⟩⟩
  by_cases has : x = s ∨ z = s
  · exact Or.inr (overlapRoute hs (pairProd closed route) has)
  have remaining (t : Fin n) (h : t ∈ A) (ne : t ≠ s) : t = u :=
    ((show t = s ∨ t = u by simpa only [Finset.mem_insert,Finset.mem_singleton] using short h)).resolve_left ne
  rcases pairHit (pairProd closed route).1 with hx | hz
  · have hu := remaining x hx (fun h => has (Or.inl h))
    subst x
    exact Or.inl (Or.inl ⟨rfl,oppArm ua guard (pairProd closed route)⟩)
  · have hu := remaining z hz (fun h => has (Or.inr h))
    subst z
    exact Or.inl (Or.inr ⟨rfl,oppArm ua guard (pairProd closed route.symm)⟩)
private theorem orientedDirected {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) (h4 : NoFourCycle G)
    {u y : Fin n} (ua : u ∈ A) (uy : R u y)
    (bigA : 1 < A.card) (bigB : 1 < B.card) (small : (A ∩ B).card ≤ 1)
    (wide : ∀ k : Fin n, ∃ x z, routedEdge R x z ∧ x ≠ k ∧ z ≠ k) :
    routedTwoLabelPlan G A B R := by
  have gu : safe G A B u := (closed.1 u y uy).1
  by_cases other : ∃ v ∈ B, ∃ z, R v z
  · obtain ⟨v,vb,z,vz⟩ := other
    have gv : safe G A B v := (closed.1 v z vz).1
    have uv : u ≠ v := fun e => G.irrefl (e ▸ common_neighbor gu ua v vb)
    by_cases outside : ∃ w ∉ A, w ∉ B ∧ ∃ t, R w t
    · obtain ⟨w,wa,wb,t,wt⟩ := outside
      have mem := oppositeOverlap wa wb (pairProd closed (Or.inl wt))
      obtain ⟨s,hs⟩ := Finset.card_eq_one.mp (le_antisymm small
        (Finset.card_pos.mpr ⟨t,mem⟩))
      have hs' : s ∈ A ∩ B := by simp [hs]
      have gw : safe G A B w := (closed.1 w t wt).1
      rcases three_guards_short_arm h4 hs ua vb wa wb gu gv gw with ar | br
      · exact shortDirected closed ua uy hs' ar
      · exact planSwap (shortDirected (closedSwap closed) vb vz
          (Finset.mem_inter.mpr (Finset.mem_inter.mp hs').symm) br)
    · refine ⟨u,v,B,uv,Or.inr rfl,vb,common_neighbor gu ua,Or.inl (connector closed uy ua vb),
        Or.inl ⟨A,Or.inl rfl,ua,common_neighbor' gv vb,fun x t h => ?_⟩⟩
      have follows (a b : Fin n) (r : R a b) : armEdge u B a b ∨ armEdge v A a b := by
        have g := (closed.1 a b r).1
        by_cases al : a ∈ A
        · have hu := unique_center h4 bigB al ua g gu
          subst a
          exact Or.inl (Or.inl ⟨rfl,oppArm ua gu (pairProd closed (Or.inl r))⟩)
        · have ar : a ∈ B := by by_contra hn; exact outside ⟨a,al,hn,b,r⟩
          have hv := unique_center (A := B) (B := A) h4 bigA ar vb (safeSwap g) (safeSwap gv)
          subst a
          exact Or.inr (Or.inl ⟨rfl,oppArm vb (safeSwap gv) (pairProd (closedSwap closed) (Or.inl r))⟩)
      exact h.elim (follows x t) (fun r => (follows t x r).imp Or.symm Or.symm)
  · have outside {a b : Fin n} (neq : a ≠ u) (r : R a b) : b ∈ A ∩ B := by
      have g := (closed.1 a b r).1
      exact oppositeOverlap (fun h => neq (unique_center h4 bigB h ua g gu))
        (fun h => other ⟨a,h,b,r⟩) (pairProd closed (Or.inl r))
    obtain ⟨a,b,h,na,nb⟩ := wide u
    have nonempty : (A ∩ B).Nonempty := h.elim (fun r => ⟨b,outside na r⟩)
      (fun r => ⟨a,outside nb r⟩)
    obtain ⟨s,hs⟩ := Finset.card_eq_one.mp (le_antisymm small (Finset.card_pos.mpr nonempty))
    have hs' : s ∈ A ∩ B := by simp [hs]
    have une : u ≠ s := fun e => overlapUnguarded hs' (e ▸ gu)
    have sb := (Finset.mem_inter.mp hs').2
    refine ⟨u,s,B,une,Or.inr rfl,sb,common_neighbor gu ua,Or.inl (connector closed uy ua sb),
      Or.inr ⟨fun w g => overlap_neighbor hs' g,fun x t h => ?_⟩⟩
    have follows (a b : Fin n) (r : R a b) : armEdge u B a b ∨ overlapEdge G A B s a b := by
      by_cases eq : a = u
      · subst a
        exact Or.inl (Or.inl ⟨rfl,oppArm ua gu (pairProd closed (Or.inl r))⟩)
      · have hb := outside eq r
        rw [hs,Finset.mem_singleton] at hb
        exact Or.inr (Or.inr ⟨hb,(closed.1 a b r).1⟩)
    exact h.elim (follows x t) (fun r => (follows t x r).imp Or.symm Or.symm)
theorem nonstarDirectedPlan {A B : Finset (Fin n)} {R : Fin n → Fin n → Prop}
    (closed : routeClosed G A B R) (h4 : NoFourCycle G) (initial : Fin n)
    (wide : ∀ k : Fin n, ∃ x y, routedEdge R x y ∧ x ≠ k ∧ y ≠ k) :
    routedTwoLabelPlan G A B R := by
  classical
  obtain ⟨x₀,y₀,sample,_,_⟩ := wide initial
  have large (S : Finset (Fin n)) (cover : ∀ x y, routedEdge R x y → x ∈ S ∨ y ∈ S) :
      1 < S.card := by
    by_contra! small
    have nonempty : S.Nonempty := (cover x₀ y₀ sample).elim (fun h => ⟨x₀,h⟩) (fun h => ⟨y₀,h⟩)
    obtain ⟨s,hs⟩ := Finset.card_eq_one.mp (le_antisymm small (Finset.card_pos.mpr nonempty))
    obtain ⟨x,y,r,nx,ny⟩ := wide s
    have hit := cover x y r
    rw [hs,Finset.mem_singleton,Finset.mem_singleton] at hit
    exact hit.elim nx ny
  have bigA := large A (fun _ _ h => pairHit (pairProd closed h).1)
  have bigB := large B (fun _ _ h => pairHit (pairProd closed h).2.1)
  have small : (A ∩ B).card ≤ 1 := by
    by_contra! many
    obtain ⟨w,g⟩ : ∃ w, safe G A B w := (pairProd closed sample).2.2.elim (fun h => ⟨_,h⟩)
      (fun h => ⟨_,h⟩)
    obtain ⟨x,y,r,nx,ny⟩ := wide w
    exact (pairProd closed r).2.2.elim (fun h => nx (unique_guard_of_overlap h4 many h g))
      (fun h => ny (unique_guard_of_overlap h4 many h g))
  by_cases ga : ∃ u ∈ A, ∃ y, R u y
  · obtain ⟨u,ua,y,uy⟩ := ga
    exact orientedDirected closed h4 ua uy bigA bigB small wide
  by_cases gb : ∃ u ∈ B, ∃ y, R u y
  · obtain ⟨u,ub,y,uy⟩ := gb
    exact planSwap (orientedDirected (closedSwap closed) h4 ub uy bigB bigA
      (by simpa only [Finset.inter_comm A B] using small) wide)
  exfalso
  have cover (u v : Fin n) (h : routedEdge R u v) : u ∈ A ∩ B ∨ v ∈ A ∩ B := by
    have outside {a b : Fin n} (r : R a b) : b ∈ A ∩ B :=
      oppositeOverlap (fun h => ga ⟨a,h,b,r⟩) (fun h => gb ⟨a,h,b,r⟩)
        (pairProd closed (Or.inl r))
    exact h.elim (fun r => Or.inr (outside r)) (fun r => Or.inl (outside r))
  exact (Nat.not_le_of_lt (large _ cover)) small
end UsefulJunk2264

end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def RoutedAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u,v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2,
    gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧
    gateVal n C j (pairInput u v) = true
theorem twoRoutePartition {j₀ j₁ : ℕ} (h : HasRoute G C j₀ j₁) :
    ∃ U₀ U₁ : Finset (Sym2 (Fin n)), Disjoint U₀ U₁ ∧ U₀ ∪ U₁ = Ustar G C ∧
      (∀ e ∈ U₀, RoutedAt G C j₀ e) ∧ ∀ e ∈ U₁, RoutedAt G C j₁ e := by
  classical
  let U := Ustar G C
  let A := U.filter (RoutedAt G C j₀)
  let B := U \ A
  have ha : A ⊆ U := Finset.filter_subset _ _
  refine ⟨A,B,Finset.disjoint_sdiff,Finset.union_sdiff_of_subset ha,?_,?_⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he
    have ⟨heu,hea⟩ := Finset.mem_sdiff.mp he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, hac, b, j, hj, hv, hr, hd⟩ := h u v heu
      rcases hj with rfl | rfl
      · exact (hea (Finset.mem_filter.mpr ⟨heu,u,v,rfl,a,hac,b,hv,hr,hd⟩)).elim
      · exact ⟨u,v,rfl,a,hac,b,hv,hr,hd⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def routedSide (n : ℕ) (C : Circuit) (a j : ℕ) : Fin 2 :=
  if OrReaches n C (opnd C a 0) j then 0 else 1
lemma routedSideEq (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ a j : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (ha : a ∈ tops G C) (hj : j = j₀ ∨ j = j₁)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) j) : routedSide n C a j = b := by
  unfold routedSide
  fin_cases b
  · exact if_pos hr
  · refine if_neg ?_
    have hj' : j ∈ junk G C := by simpa [hJ] using hj
    have hp := pureOppositeOperand hAO hT hJ hsep ha hr hj
    exact fun h => hp j h (junkData hj').2.1
def centreRoutes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) : Finset ℕ :=
  (centreless G C).filter fun a => OrReaches n C (opnd C a (routedSide n C a j)) j
lemma centreRoutesDisjoint (hAO : IsAO2 n C) {j₀ j₁ : ℕ}
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a) :
    Disjoint (centreRoutes G C j₀) (centreRoutes G C j₁) := by
  apply Finset.disjoint_left.mpr
  intro a h0 h1
  have htop := (Finset.mem_filter.mp (Finset.mem_filter.mp h0).1).1
  have hal := (topData htop).1
  exact hsep a htop (operandReachCone hAO hal (Finset.mem_filter.mp h0).2)
    (operandReachCone hAO hal (Finset.mem_filter.mp h1).2)
lemma centreRoutesCard (hAO : IsAO2 n C) {j₀ j₁ : ℕ}
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a) :
    (centreRoutes G C j₀).card + (centreRoutes G C j₁).card ≤ (centreless G C).card := by
  rw [← Finset.card_union_of_disjoint (centreRoutesDisjoint hAO hsep)]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
def centreGuard (C : Circuit) (n a j : ℕ) : ℕ :=
  opnd C a (1-routedSide n C a j)
lemma centreGuardPure (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ j a : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) (ha : a ∈ centreRoutes G C j) :
    centreGuard C n a j < n + C.gates.length ∧
      (∀ k, OrReaches n C (centreGuard C n a j) k → (gateAt C k).op ≠ GateOp.and) ∧
      orIn n C (centreGuard C n a j) ⊆ wmax G C j := by
  obtain ⟨hc,hr⟩ := Finset.mem_filter.mp ha
  have ht := (Finset.mem_filter.mp hc).1
  have hl := (topData ht).1
  have hlt := opndBound hAO hl (1-routedSide n C a j)
  refine ⟨by unfold centreGuard; omega, ?_, ?_⟩
  · exact pureOppositeOperand hAO hT hJ hsep ht hr hj
  · exact oppositeSideWmax hAO ht hr
def mixLabels (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j₀ j₁ j : ℕ) : Finset (Fin n) :=
  (((mixing G C).image (mixingLabel C n j₀ j₁)).filter fun p => p.1 = j).biUnion
    fun p => p.2.toFinset
lemma mixLabelMem {j₀ j₁ j : ℕ} {x : Fin n}
    (h : (j,some x) ∈ (mixing G C).image (mixingLabel C n j₀ j₁)) :
    x ∈ mixLabels G C j₀ j₁ j := by
  apply Finset.mem_biUnion.mpr
  exact ⟨(j,some x), Finset.mem_filter.mpr ⟨h,rfl⟩, by simp⟩
lemma mixLabelsCard {j₀ j₁ : ℕ} (hneq : j₀ ≠ j₁) :
    (mixLabels G C j₀ j₁ j₀).card + (mixLabels G C j₀ j₁ j₁).card ≤ (mixing G C).card := by
  let S := (mixing G C).image (mixingLabel C n j₀ j₁)
  let f (j : ℕ) := S.filter fun p => p.1 = j
  have one (j : ℕ) : (mixLabels G C j₀ j₁ j).card ≤ (f j).card := by
    unfold mixLabels
    change ((f j).biUnion fun p => p.2.toFinset).card ≤ (f j).card
    refine Finset.card_biUnion_le.trans ?_
    calc
      (∑ p ∈ f j, p.2.toFinset.card) ≤ ∑ _p ∈ f j, (1 : ℕ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rcases p.2 with _ | x <;> simp
      _ = (f j).card := by simp
  have hd : Disjoint (f j₀) (f j₁) := by
    apply Finset.disjoint_left.mpr
    intro p h0 h1
    exact hneq ((Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2)
  have hcard : (f j₀).card + (f j₁).card ≤ (mixing G C).card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans
      Finset.card_image_le
  have h0 := one j₀
  have h1 := one j₁
  omega
lemma routedEdgeProfile (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ j : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁)
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) (hr : RoutedAt G C j e) :
    ∃ u v : Fin n, e = s(u,v) ∧ gateVal n C j (pairInput u v) = true ∧
      ((∃ a ∈ centreRoutes G C j,
        u ∈ orIn n C (centreGuard C n a j) ∨ v ∈ orIn n C (centreGuard C n a j)) ∨
      ∃ x ∈ mixLabels G C j₀ j₁ j, ∃ y ∈ wmax G C j, (y = u ∨ y = v) ∧
        G.Adj x y ∧ s(x,y) ∉ Ustar G C ∧ x ≠ u ∧ x ≠ v) := by
  obtain ⟨u,v,rfl,a,ha,b,hv,hr,hval⟩ := hr
  refine ⟨u,v,rfl,hval,?_⟩
  by_cases hc : a ∈ centreless G C
  · have eq := routedSideEq hAO hT hJ hsep ha hj hr
    have hm : a ∈ centreRoutes G C j := Finset.mem_filter.mpr ⟨hc,by rwa [eq]⟩
    have ht := (ustarAttaches hAO hT hJ hsep ha hr hj hv).1
    exact .inl ⟨a,hm,by simpa only [centreGuard,eq,side] using ht⟩
  · obtain ⟨m,hm,hmr,hmj,_,_,_,hn,_⟩ :=
      edgeSlice hAO hT hJ hsep ha hr hj hv he hc hcross
    obtain ⟨x,hx,hlabel⟩ := mixingLabelExact hAO hsep ha hmr hmj hj hn
    have hxm : x ∈ mixLabels G C j₀ j₁ j :=
      mixLabelMem (Finset.mem_image.mpr ⟨m,hm,hlabel⟩)
    have ⟨hsa,hW⟩ := ustarAttaches hAO hT hJ hsep ha hr hj hv
    have hx' : x ∈ side (n := n) C a b := orInTrans (orReaches_reach m _ hmr).1 hx
    have hg (y : Fin n) (hy : y ∈ side (n := n) C a (1-b)) :
        G.Adj x y ∧ s(x,y) ∉ Ustar G C := by
      refine ⟨?_,fun h => (Finset.mem_sdiff.mp h).2 (routedTopCross ha hx' hy)⟩
      fin_cases b
      · exact hcross a ha x hx' y hy
      · exact (hcross a ha y hy x hx').symm
    have build (y : Fin n) (hy : y ∈ side (n := n) C a (1-b)) (heq : y = u ∨ y = v) :
        G.Adj x y ∧ s(x,y) ∉ Ustar G C ∧ x ≠ u ∧ x ≠ v := by
      obtain ⟨hadj,hmiss⟩ := hg y hy
      refine ⟨hadj,hmiss,?_,?_⟩
      · intro e
        rcases heq with rfl | rfl
        · rw [e] at hadj
          exact G.irrefl hadj
        · exact hmiss (e ▸ he)
      · intro e
        rcases heq with rfl | rfl
        · rw [Sym2.eq_swap] at he
          exact hmiss (e ▸ he)
        · rw [e] at hadj
          exact G.irrefl hadj
    rcases hsa with hu | hv
    · exact .inr ⟨x,hxm,u,hW hu,.inl rfl,build u hu (.inl rfl)⟩
    · exact .inr ⟨x,hxm,v,hW hv,.inr rfl,build v hv (.inr rfl)⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable def centreGuardWires (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) : Finset ℕ :=
  (centreRoutes G C j).image fun a => centreGuard C n a j
noncomputable def centreGuardUnion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) : Finset (Fin n) :=
  (centreGuardWires G C j).biUnion (orIn n C)
lemma centreGuardWireCount (j : ℕ) :
    (centreGuardWires G C j).card ≤ (centreRoutes G C j).card :=
  Finset.card_image_le
lemma centreGuardUnionSafe (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ j : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (apart : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) :
    centreGuardUnion G C j ⊆ wmax G C j := by
  intro x hx
  obtain ⟨w,hw,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  exact (centreGuardPure hAO hT hJ apart hj ha).2.2 hx
lemma centreGuardWirePure (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ j : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (apart : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) {w : ℕ} (hw : w ∈ centreGuardWires G C j) :
    w < n + C.gates.length ∧ ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨h1,h2,_⟩ := centreGuardPure hAO hT hJ apart hj ha
  exact ⟨h1,h2⟩
def GuardOption (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j₀ j₁ j : ℕ) (y z : Fin n) : Prop :=
  y ∈ centreGuardUnion G C j ∨
    ∃ x ∈ mixLabels G C j₀ j₁ j, G.Adj x y ∧ x ≠ z
lemma routedThroughGuard (hAO : IsAO2 n C) (hT : TopForm G C) {j₀ j₁ j : ℕ}
    (hJ : junk G C = {j₀,j₁})
    (apart : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁)
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) (hr : RoutedAt G C j e) :
    ∃ y z : Fin n, e = s(y,z) ∧ y ∈ wmax G C j ∧
      gateVal n C j (pairInput y z) = true ∧ GuardOption G C j₀ j₁ j y z := by
  obtain ⟨u,v,heq,hval,opts⟩ := routedEdgeProfile hAO hT hJ apart hcross hj he hr
  have addGuard (a : ℕ) (ha : a ∈ centreRoutes G C j)
      (x : Fin n) (hx : x ∈ orIn n C (centreGuard C n a j)) : x ∈ centreGuardUnion G C j :=
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_image.mpr ⟨a,ha,rfl⟩,hx⟩
  rcases opts with ⟨a,ha,hu | hv⟩ | ⟨x,hx,y,hy,there,adj,_,hxu,hxv⟩
  · have hg := addGuard a ha u hu
    exact ⟨u,v,heq,centreGuardUnionSafe hAO hT hJ apart hj hg,hval,.inl hg⟩
  · have hg := addGuard a ha v hv
    rw [pairInputSwap u v] at hval
    exact ⟨v,u,heq.trans Sym2.eq_swap,centreGuardUnionSafe hAO hT hJ apart hj hg,hval,.inl hg⟩
  · rcases there with here | there
    · subst y
      exact ⟨u,v,heq,hy,hval,.inr ⟨x,hx,adj,hxv⟩⟩
    · subst y
      rw [pairInputSwap u v] at hval
      exact ⟨v,u,heq.trans Sym2.eq_swap,hy,hval,.inr ⟨x,hx,adj,hxu⟩⟩
def exteriorMixKeys (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (L X : Finset (Fin n))
    (s : Fin n) : Finset (Fin n) :=
  L.filter fun x => x ≠ s ∧ ∃ y ∈ X, G.Adj x y
lemma exteriorMixCount (h4 : NoFourCycle G)
    (L X : Finset (Fin n)) (s : Fin n)
    (hAdj : ∀ y ∈ X, G.Adj s y)
    (hRoute : ∀ y ∈ X, ∃ x ∈ L, G.Adj x y ∧ x ≠ s) :
    X.card ≤ (exteriorMixKeys G L X s).card := by
  classical
  have hex (y : {y // y ∈ X}) := hRoute y.val y.property
  choose f hf using hex
  have hsub : X.attach.image f ⊆ exteriorMixKeys G L X s := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨(hf y).1,(hf y).2.2,y.val,y.property,(hf y).2.1⟩
  have hInj : Set.InjOn f (↑X.attach) := by
    intro y _ z _ he
    apply Subtype.ext
    have hcase := h4 (f y) s (hf y).2.2
    have a : y.val ∈ Finset.univ.filter (fun w => G.Adj (f y) w ∧ G.Adj s w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hf y).2.1,hAdj _ y.property⟩
    have b : z.val ∈ Finset.univ.filter (fun w => G.Adj (f y) w ∧ G.Adj s w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ (hf z).2.1,hAdj _ z.property⟩
    exact Finset.card_le_one_iff.mp hcase a b
  have h := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hInj,Finset.card_attach] at h
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma realGuardRoute (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) {e : Sym2 (Fin n)} (he : RoutedAt G C j e) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ y z : Fin n,
      e = s(y,z) ∧ OrReaches n C (opnd C a b) j ∧ y ∈ side (n := n) C a (1-b) ∧
        y ∈ wmax G C j ∧ gateVal n C j (pairInput y z) = true := by
  obtain ⟨u,v,he,a,ha,b,ht,hr,hv⟩ := he
  obtain ⟨hpair,hW⟩ := ustarAttaches hAO hT hJ hsep ha hr hj ht
  rcases hpair with hu | hv'
  · exact ⟨a,ha,b,u,v,he,hr,hu,hW hu,hv⟩
  · exact ⟨a,ha,b,v,u,he.trans Sym2.eq_swap,hr,hv',hW hv',pairInputSwap u v ▸ hv⟩
lemma actualGuardRoutes (hAO : IsAO2 n C)
    {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hReach : OrReaches n C (opnd C a b) j)
    {y z : Fin n} (hy : y ∈ side (n := n) C a (1-b))
    (hJ : gateVal n C j (pairInput y z) = true) :
    RoutedAt G C j s(y,z) := by
  have ⟨hal,hao,_⟩ := topData ha
  refine ⟨y,z,rfl,a,ha,b,?_,hReach,hJ⟩
  apply (andValOperands hAO hal hao _).mpr
  intro k
  rcases eitherOperand b k with rfl | rfl
  · exact reachVal hReach hJ
  · exact reach_var_val (pairInput y z) _ y (mem_orIn_reach y hy) (pairInput_left y z)
lemma twoRoutePartitionWith {j₀ j₁ : ℕ} (h : HasRoute G C j₀ j₁)
    (F₀ F₁ : Finset (Sym2 (Fin n))) (hd : Disjoint F₀ F₁)
    (hF₀ : F₀ ⊆ Ustar G C) (hF₁ : F₁ ⊆ Ustar G C)
    (r₀ : ∀ e ∈ F₀, RoutedAt G C j₀ e) (r₁ : ∀ e ∈ F₁, RoutedAt G C j₁ e) :
    ∃ V₀ V₁ : Finset (Sym2 (Fin n)), Disjoint V₀ V₁ ∧ V₀ ∪ V₁ = Ustar G C ∧
      F₀ ⊆ V₀ ∧ F₁ ⊆ V₁ ∧
      (∀ e ∈ V₀, RoutedAt G C j₀ e) ∧ ∀ e ∈ V₁, RoutedAt G C j₁ e := by
  classical
  let U := Ustar G C
  let A := U.filter (fun e => RoutedAt G C j₀ e ∧ e ∉ F₁)
  let B := U \ A
  have hA : A ⊆ U := Finset.filter_subset _ _
  refine ⟨A,B,Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hA,?_,?_,?_,?_⟩
  · exact fun e he => Finset.mem_filter.mpr ⟨hF₀ he,r₀ e he,Finset.disjoint_left.mp hd he⟩
  · exact fun e he => Finset.mem_sdiff.mpr ⟨hF₁ he,fun hh => (Finset.mem_filter.mp hh).2.2 he⟩
  · exact fun e he => (Finset.mem_filter.mp he).2.1
  · intro e he
    have ⟨heU,hn⟩ := Finset.mem_sdiff.mp he
    by_cases hm : e ∈ F₁
    · exact r₁ e hm
    · induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a,ha,b,j,hj,hv,hr,hjv⟩ := h u v heU
        rcases hj with rfl | rfl
        · exact (hn (Finset.mem_filter.mpr ⟨heU,⟨u,v,rfl,a,ha,b,hv,hr,hjv⟩,hm⟩)).elim
        · exact ⟨u,v,rfl,a,ha,b,hv,hr,hjv⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (hits routedEdge routeClosed routedTwoLabelPlan)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def directedRoute (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (u v : Fin n) : Prop :=
  ∃ a ∈ tops G C, ∃ b : Fin 2,
    OrReaches n C (opnd C a b) j ∧ u ∈ side (n := n) C a (1-b) ∧
    u ∈ wmax G C j ∧ gateVal n C j (pairInput u v) = true
lemma directedRouteToEdge (hAO : IsAO2 n C) {j : ℕ} {u v : Fin n}
    (h : routedEdge (directedRoute G C j) u v) : RoutedAt G C j s(u,v) := by
  have forward {a b : Fin n} (h : directedRoute G C j a b) :
      RoutedAt G C j s(a,b) := by
    obtain ⟨k,hk,i,reach,guard,_,on⟩ := h
    exact actualGuardRoutes hAO hk reach guard on
  exact h.elim forward (fun h => Sym2.eq_swap ▸ forward h)
lemma edgeToDirectedRoute (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) {u v : Fin n} (h : RoutedAt G C j s(u,v)) :
    routedEdge (directedRoute G C j) u v := by
  obtain ⟨k,hk,b,y,z,eq,hr,hy,hw,on⟩ := realGuardRoute hAO hT hJ hsep hj h
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨k,hk,b,hr,hy,hw,on⟩
  · exact Or.inr ⟨k,hk,b,hr,hy,hw,on⟩
lemma directedRouteClosed (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (pq : ¬ InCone n C j₀ j₁) (qp : ¬ InCone n C j₁ j₀)
    (hj : j ∈ junk G C) :
    routeClosed G (side (n := n) C j 0) (side (n := n) C j 1) (directedRoute G C j) := by
  have raw (x : Fin n → Bool) : gateVal n C j x = true ↔
      hits (side (n := n) C j 0) x ∧ hits (side (n := n) C j 1) x :=
    junkVal hAO hT hJ pq qp hj x
  constructor
  · rintro u v ⟨k,hk,b,reach,guard,hSafe,on⟩
    exact ⟨fun x a b ux => (Finset.mem_filter.mp hSafe).2 x ((raw _).mpr ⟨a,b⟩) ux,
      (raw _).mp on⟩
  · rintro u v w ⟨k,hk,b,reach,guard,hSafe,on⟩ a d
    exact ⟨k,hk,b,reach,guard,hSafe,(raw _).mpr ⟨a,d⟩⟩
theorem actualNonstarPlan (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (pq : ¬ InCone n C j₀ j₁) (qp : ¬ InCone n C j₁ j₀)
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hj : j = j₀ ∨ j = j₁) (initial : Fin n)
    (wide : ∀ c : Fin n, ∃ x y : Fin n, RoutedAt G C j s(x,y) ∧ x ≠ c ∧ y ≠ c) :
    routedTwoLabelPlan G (side (n := n) C j 0) (side (n := n) C j 1) (directedRoute G C j) := by
  have hm : j ∈ junk G C := by simpa [hJ] using hj
  apply UsefulJunk2264.nonstarDirectedPlan (directedRouteClosed hAO hT hJ pq qp hm) h4 initial
  intro k
  obtain ⟨x,y,h,hn,hm⟩ := wide k
  exact ⟨x,y,edgeToDirectedRoute hAO hT hJ hsep hj h,hn,hm⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem zeroCentrelessRoutedMix (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcross : HasCross G C) {p q j : ℕ}
    (hJ : junk G C = {p,q}) (hsep : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (zero : (ctrByJunk G C j).card = 0)
    {u c : Fin n} (cn : c ∉ wmax G C j) (route : RoutedAt G C j s(u,c)) :
    ∃ m ∈ mixByJunk G C j, (orIn n C (n+m)).Nonempty ∧
      ∀ x ∈ orIn n C (n+m), G.Adj x u := by
  classical
  have dir : directedRoute G C j u c := by
    refine (edgeToDirectedRoute hAO hT hJ hsep num route).resolve_right ?_
    rintro ⟨_,_,_,_,_,safe,_⟩
    exact cn safe
  obtain ⟨a,ha,b,hr,hu,_,_⟩ := dir
  have jm : j ∈ junk G C := by simpa [hJ] using num
  have noCentre : a ∉ centreless G C := by
    intro hc
    have h : a ∈ ctrByJunk G C j :=
      Finset.mem_filter.mpr ⟨hc,operandReachCone hAO (topData ha).1 hr⟩
    have emp := Finset.card_eq_zero.mp zero
    simp [emp] at h
  have raw : (side (n := n) C a b).Nonempty := by
    by_contra h
    have emp := Finset.not_nonempty_iff_eq_empty.mp h
    apply noCentre
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases b
    · exact Or.inl emp
    · exact Or.inr emp
  obtain ⟨m,hm,rm,rj,ne⟩ := mixingAlong (G := G) hAO hr (junkData jm).2.1 raw
  refine ⟨m,Finset.mem_filter.mpr ⟨hm,rj,a,ha,b,rm⟩,ne,fun x hx => ?_⟩
  have on := orInTrans (orReaches_reach m _ rm).1 hx
  fin_cases b
  · exact hcross a ha x on u hu
  · exact (hcross a ha u hu x on).symm
theorem reservedMixNotCandidate (h4 : NoFourCycle G)
    {u c y : Fin n} (huc : G.Adj u c) (hyc : G.Adj c y) (hne : y ≠ u)
    {m m' : ℕ} (support : (orIn n C (n+m)).Nonempty)
    (res : ∀ x ∈ orIn n C (n+m), G.Adj x u)
    (can : ∀ x ∈ orIn n C (n+m'), G.Adj x y ∧ x ≠ c) : m' ≠ m := by
  rintro rfl
  obtain ⟨x,hx⟩ := support
  have cap := h4 x c (can x hx).2
  have hu : u ∈ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj c w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,res x hx,huc.symm⟩
  have hy : y ∈ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj c w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(can x hx).1,hyc⟩
  exact hne (Finset.card_le_one_iff.mp cap hy hu)
theorem reservedMixPermit (hAO : IsAO2 n C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (hcross : HasCross G C) {p q j : ℕ}
    (hJ : junk G C = {p,q}) (hsep : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (zero : (ctrByJunk G C j).card = 0)
    {u c : Fin n} (cn : c ∉ wmax G C j) (huc : G.Adj u c) (route : RoutedAt G C j s(u,c)) :
    ∃ m ∈ mixByJunk G C j, ∀ (y : Fin n) (k : ℕ), y ≠ u → G.Adj c y →
      (∀ x ∈ orIn n C (n+k), G.Adj x y ∧ x ≠ c) → k ≠ m := by
  obtain ⟨m,hm,nonempty,adj⟩ := zeroCentrelessRoutedMix hAO hT hcross hJ hsep num zero cn route
  exact ⟨m,hm,fun _ _ hne hy can => reservedMixNotCandidate h4 huc hy hne nonempty adj can⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (safe armEdge overlapEdge)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
structure ActualPairPlan (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (c d : Fin n) where
  raw : Finset (Fin n)
  distinct : c ≠ d
  rawSide : raw = side (n := n) C j 0 ∨ raw = side (n := n) C j 1
  connectorLeaf : d ∈ raw
  adjacent : ∀ x ∈ raw, G.Adj c x
  connector : RoutedAt G C j s(c,d)
  ordinary : Bool
  mode :
    if ordinary then
      ∃ other : Finset (Fin n), (other = side (n := n) C j 0 ∨ other = side C j 1) ∧
        c ∈ other ∧ (∀ x ∈ other, G.Adj d x) ∧
        ∀ x y, RoutedAt G C j s(x,y) → armEdge c raw x y ∨ armEdge d other x y
    else
      (∀ x ∈ wmax G C j, G.Adj d x) ∧
        ∀ x y, RoutedAt G C j s(x,y) → armEdge c raw x y ∨ armEdge d Finset.univ x y
theorem actualPairExists (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {p q j : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (initial : Fin n)
    (wide : ∀ c, ∃ x y : Fin n, RoutedAt G C j s(x,y) ∧ x ≠ c ∧ y ≠ c) :
    ∃ c d, Nonempty (ActualPairPlan G C j c d) := by
  let A := side (n := n) C j 0
  let B := side (n := n) C j 1
  obtain ⟨c,d,D,ne,dRaw,hd,dAdj,dConn,plan⟩ := actualNonstarPlan hAO hT h4 hj pq qp apart num initial wide
  have conn := directedRouteToEdge hAO dConn
  have route x y := edgeToDirectedRoute hAO hT hj apart num (u := x) (v := y)
  refine ⟨c,d,?_⟩
  rcases plan with ⟨F,hf,hc,fAdj,routes⟩ | ⟨guard,routes⟩
  · exact ⟨⟨D,ne,dRaw,hd,dAdj,conn,true,⟨F,hf,hc,fAdj,fun x y r => routes x y (route x y r)⟩⟩⟩
  · have hm : j ∈ junk G C := by simpa [hj] using num
    have raw (x : Fin n → Bool) := (junkVal hAO hT hj pq qp hm x).mpr
    have gSafe (w : Fin n) (hw : w ∈ wmax G C j) : safe G A B w :=
      fun x ha hb hx => (Finset.mem_filter.mp hw).2 _ (raw x ⟨ha,hb⟩) hx
    refine ⟨⟨D,ne,dRaw,hd,dAdj,conn,false,fun w hw => guard _ (gSafe w hw),?_⟩⟩
    intro x y hr
    refine (routes x y (route x y hr)).imp id ?_
    rintro (⟨hx,_⟩ | ⟨hy,_⟩)
    · exact Or.inl ⟨hx,Finset.mem_univ _⟩
    · exact Or.inr ⟨hy,Finset.mem_univ _⟩
theorem ActualPairPlan.covers {j : ℕ} {c d : Fin n} (P : ActualPairPlan G C j c d)
    (x y : Fin n) (r : RoutedAt G C j s(x,y)) : x = c ∨ y = c ∨ x = d ∨ y = d := by
  have it {D F : Finset (Fin n)} (h : armEdge c D x y ∨ armEdge d F x y) :
      x = c ∨ y = c ∨ x = d ∨ y = d := by
    rcases h with (⟨h,_⟩|⟨h,_⟩) | (⟨h,_⟩|⟨h,_⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have mode := P.mode
  cases o : P.ordinary
  · simp only [o,Bool.false_eq_true,if_false] at mode
    exact it (mode.2 x y r)
  · simp only [o,if_true] at mode
    obtain ⟨F,_,_,_,cover⟩ := mode
    exact it (cover x y r)
theorem positiveActualRouteTag (hAO : IsAO2 n C) (hT : TopForm G C) (cross : HasCross G C)
    {p q j : ℕ} (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) {E : Finset (Sym2 (Fin n))} (hs : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, RoutedAt G C j e) (ne : E.Nonempty) :
    1 ≤ (mixByJunk G C j).card + (ctrByJunk G C j).card := by
  obtain ⟨e,he⟩ := ne
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨a,ha,b,on,hr,_⟩ := servedByPair (serve _ he)
    by_cases ctr : a ∈ centreless G C
    · have hm : a ∈ ctrByJunk G C j :=
        Finset.mem_filter.mpr ⟨ctr,operandReachCone hAO (topData ha).1 hr⟩
      have H := Finset.card_pos.mpr ⟨a,hm⟩
      omega
    · obtain ⟨m,hm,rM,rJ,_,_,_,_,_⟩ := edgeSlice hAO hT hj apart ha hr num on (hs he) ctr cross
      have mem : m ∈ mixByJunk G C j := Finset.mem_filter.mpr ⟨hm,rJ,a,ha,b,rM⟩
      have H := Finset.card_pos.mpr ⟨m,mem⟩
      omega
theorem ActualPairPlan.request {j : ℕ} {c d : Fin n} (P : ActualPairPlan G C j c d)
    (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {p q : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, RoutedAt G C j e)
    (extra : Option (Fin 2)) (no : extra.isSome = true → s(c,d) ∉ E)
    (modeExtra : P.ordinary = false → extra ≠ some 1)
    (M : Finset ℕ) (tag : P.ordinary = true → 1 ≤ M.card + (ctrByJunk G C j).card)
    (allowed : ∀ v, s(d,v) ∈ E → ∀ m ∈ mixByJunk G C j, (orIn n C (n+m)).Nonempty →
      (∀ x ∈ orIn n C (n+m), G.Adj x v ∧ x ≠ d) → m ∈ M) :
    Nonempty (PairRequest (G := G) (C := C) E c d extra M.card (ctrByJunk G C j).card) := by
  have mode := P.mode
  cases o : P.ordinary
  · simp only [o,Bool.false_eq_true,if_false] at mode
    exact overlapPairRequests hAO hT h4 cross hj pq qp apart num E sub serve c d P.rawSide
      P.connectorLeaf P.adjacent mode.1 (fun x y he => mode.2 x y (serve _ he))
      extra no (modeExtra o) M allowed
  · simp only [o,if_true] at mode
    obtain ⟨F,fRaw,hc,fAdj,cover⟩ := mode
    have hm : j ∈ junk G C := by simpa [hj] using num
    exact ordinaryPairRequests hAO hT hj pq qp hm E c d P.rawSide fRaw P.connectorLeaf
      hc P.adjacent fAdj (fun x y he => cover x y (serve _ he)) extra no _ _ (tag o)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {j₀ j₁ : ℕ}
theorem edgeFamilyCard {E : Finset (Sym2 (Fin n))} {S : Finset (Fin n)} {y : Fin n}
    (h : ∀ e ∈ E, ∃ z ∈ S, e = s(y,z)) : E.card ≤ S.card := by
  have hsub : E ⊆ S.image (fun z => s(y,z)) := by
    intro e he
    obtain ⟨z,hz,hEq⟩ := h e he
    exact Finset.mem_image.mpr ⟨z,hz,hEq.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def forbiddenLeaves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) (c : Fin n) : Finset (Fin n) :=
  (orIn n C w).filter fun v => s(c,v) ∈ Ustar G C
def forbiddenStar (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) (c : Fin n) : Finset (Sym2 (Fin n)) :=
  (forbiddenLeaves G C w c).image (fun v => s(c,v))
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def pureWithinCenter (C : Circuit) (P : Finset ℕ) (c : Fin n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset ℕ :=
  P.filter fun k => 1 < (orIn n C (n+k)).card ∧ ∀ v ∈ orIn n C (n+k), G.Adj c v
theorem pureWithinCenterDisjoint (h4 : NoFourCycle G) (P : Finset ℕ) {a b : Fin n} (hn : a ≠ b) :
    Disjoint (pureWithinCenter C P a G) (pureWithinCenter C P b G) := by
  apply Finset.disjoint_left.mpr
  intro k ha hb
  obtain ⟨_,hc,hA⟩ := Finset.mem_filter.mp ha
  obtain ⟨_,_,hB⟩ := Finset.mem_filter.mp hb
  exact hn (uniqueCommonCenter h4 hc hA hB)
theorem pureWithinCenterSum (h4 : NoFourCycle G) (P : Finset ℕ) (K : Finset (Fin n)) :
    (∑ t ∈ K, (pureWithinCenter C P t G).card) ≤ P.card := by
  have h : (K : Set (Fin n)).PairwiseDisjoint (fun t => pureWithinCenter C P t G) := by
    intro a _ b _ hab
    exact pureWithinCenterDisjoint h4 P hab
  rw [← Finset.card_biUnion h]
  exact Finset.card_le_card (fun k hk => by
    obtain ⟨c,_,hm⟩ := Finset.mem_biUnion.mp hk
    exact (Finset.mem_filter.mp hm).1)
theorem familyLimitedAllowedCapacity (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R : Finset ℕ) {s : Fin n} {Q : Finset (Fin n)}
    (hQ : Q ⊆ R.biUnion (orIn n C)) (hAdj : ∀ v ∈ Q, G.Adj s v)
    (hSome : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → s(s,u) ∈ Ustar G C ∨ s(s,v) ∈ Ustar G C) :
    Q.card ≤ (R.biUnion (Eligible.pureInternals G C)).card + R.card := by
  let T := R.biUnion (Eligible.pureFrontier G C)
  let B (v : ℕ) := Q ∩ orIn n C v
  have hT : Q ⊆ T.biUnion B := by
    intro v hv
    obtain ⟨z,hz,hv'⟩ := Finset.mem_biUnion.mp (hQ hv)
    rw [Eligible.pureFrontierUnion (G := G) (C := C)] at hv'
    obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp hv'
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_biUnion.mpr ⟨z,hz,hu⟩,Finset.mem_inter.mpr ⟨hv,hvu⟩⟩
  have hOne : ∀ v ∈ T, (B v).card ≤ 1 := by
    intro v hv
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    by_contra hab
    obtain ⟨haQ,haS⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbQ,hbS⟩ := Finset.mem_inter.mp hb
    obtain ⟨_,_,hv'⟩ := Finset.mem_biUnion.mp hv
    have hp := Eligible.pureFrontierAvailable hv'
    rcases hSome a haQ b hbQ hab with h | h
    · exact hab (availableAdjacentGuardUnique h4 hp haS hbS (hAdj a haQ) (hAdj b hbQ) h)
    · exact hab (availableAdjacentGuardUnique h4 hp hbS haS (hAdj b hbQ) (hAdj a haQ) h).symm
  have hc : (T.biUnion B).card ≤ T.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ _ ∈ T, (1 : ℕ) := Finset.sum_le_sum hOne
      _ = _ := by simp
  exact (Finset.card_le_card hT).trans (hc.trans (Eligible.familyFrontierCard hAO R))
theorem localFamilyInternalsIn
    (R P : Finset ℕ)
    (hP : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    {c : Fin n} (hAdj : ∀ w ∈ R, ∀ v ∈ orIn n C w, G.Adj c v) :
    (R.biUnion (Eligible.pureInternals G C)).card ≤ (pureWithinCenter C P c G).card := by
  let I := R.biUnion (Eligible.pureInternals G C)
  let f (z : ℕ) := z-n
  have hge {z : ℕ} (hz : z ∈ I) : n ≤ z := by
    obtain ⟨_,_,hz'⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hz').2.1
  have hinj : Set.InjOn f ↑I := by
    intro a ha b hb h
    have h₁ := hge ha
    have h₂ := hge hb
    change a-n=b-n at h
    omega
  have hI : I.image f ⊆ pureWithinCenter C P c G := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨w,hw,hzw⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨_,hn,ha⟩ := Finset.mem_filter.mp hzw
    have hEq : n+f z = z := by change n+(z-n)=z; omega
    refine Finset.mem_filter.mpr ⟨hP z hz,?_⟩
    rw [hEq]
    refine ⟨?_,fun v hv => hAdj w hw v (chargedSupportSubset hzw hv)⟩
    by_contra! h
    exact ha (Or.inl h)
  have h := Finset.card_le_card hI
  rwa [Finset.card_image_of_injOn hinj] at h
theorem localFamilyAssignedIn (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R P : Finset ℕ)
    (hP : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    {c : Fin n} (hAdj : ∀ w ∈ R, ∀ v ∈ orIn n C w, G.Adj c v)
    {X : Finset (Fin n)} (hX : X ⊆ R.biUnion (orIn n C))
    (hU : ∀ v ∈ X, s(c,v) ∈ Ustar G C) :
    X.card ≤ (pureWithinCenter C P c G).card + R.card ∧
      (((R.biUnion (orIn n C)) \ X).Nonempty →
        X.card + 1 ≤ (pureWithinCenter C P c G).card + R.card) := by
  have hI := localFamilyInternalsIn R P hP hAdj
  have hA (v : Fin n) (hv : v ∈ R.biUnion (orIn n C)) : G.Adj c v := by
    obtain ⟨w,hw,hvw⟩ := Finset.mem_biUnion.mp hv
    exact hAdj w hw v hvw
  constructor
  · have h := familyLimitedAllowedCapacity hAO h4 R hX (fun v hv => hA v (hX hv))
      (fun v hv _ _ _ => Or.inl (hU v hv))
    omega
  · rintro ⟨v,hv⟩
    obtain ⟨hIn,hn⟩ := Finset.mem_sdiff.mp hv
    let Q := insert v X
    have hQ : Q ⊆ R.biUnion (orIn n C) := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hIn
      · exact hX ht
    have hCap := familyLimitedAllowedCapacity hAO h4 R hQ (fun u hu => hA u (hQ hu)) (by
      intro a ha b hb hne
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hne rfl).elim
        · exact Or.inr (hU _ hb)
      · exact Or.inl (hU _ ha))
    have hQc : Q.card = X.card + 1 := Finset.card_insert_of_notMem hn
    omega
theorem actualLocalPurePool (hAO : IsAO2 n C) (hcross : HasCross G C)
    {R : Finset ℕ}
    (h : ∀ w ∈ R, w < n+C.gates.length ∧
      ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and) :
    ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ NoPureMix G C := by
  intro z hz
  obtain ⟨w,hw,hzw⟩ := Finset.mem_biUnion.mp hz
  exact Eligible.pureInternalsCharged hAO (h w hw).1 (h w hw).2 hcross hzw
theorem localPureAssignedIn (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {w : ℕ} (P : Finset ℕ) (hP : ∀ z ∈ Eligible.pureInternals G C w, z-n ∈ P)
    {c : Fin n} (hAdj : ∀ v ∈ orIn n C w, G.Adj c v)
    {X : Finset (Fin n)} (hX : X ⊆ orIn n C w) (hU : ∀ v ∈ X, s(c,v) ∈ Ustar G C) :
    X.card ≤ (pureWithinCenter C P c G).card + 1 ∧
      (((orIn n C w) \ X).Nonempty → X.card ≤ (pureWithinCenter C P c G).card) := by
  simpa using localFamilyAssignedIn hAO h4 {w} P (by simpa using hP)
    (by simpa using hAdj) (by simpa using hX) hU
noncomputable def chargedPurePool (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (R : Finset ℕ) : Finset ℕ :=
  (R.biUnion (Eligible.pureInternals G C)).image (fun z => z-n)
theorem chargedPurePoolCard (R : Finset ℕ) :
    (chargedPurePool G C R).card = (R.biUnion (Eligible.pureInternals G C)).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb h
  obtain ⟨_,_,ha'⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨_,_,hb'⟩ := Finset.mem_biUnion.mp hb
  have hA := (Finset.mem_filter.mp ha').2.1
  have hB := (Finset.mem_filter.mp hb').2.1
  change a-n=b-n at h
  omega
theorem arbitraryFamilyAssignedIn (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R P : Finset ℕ) (hP : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    {c : Fin n} {X : Finset (Fin n)} (hX : X ⊆ R.biUnion (orIn n C))
    (hU : ∀ v ∈ X, s(c,v) ∈ Ustar G C) :
    X.card ≤ P.card + R.card := by
  have hAdj (v : Fin n) (hv : v ∈ X) : G.Adj c v :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hU v hv)).1
  have hCap := familyLimitedAllowedCapacity hAO h4 R hX hAdj
    (fun v hv _ _ _ => Or.inl (hU v hv))
  have hSub : chargedPurePool G C R ⊆ P := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    exact hP z hz
  have hc := Finset.card_le_card hSub
  rw [chargedPurePoolCard] at hc
  omega
theorem poolCaptures {R T : Finset ℕ} (h : T ⊆ R) :
    ∀ z ∈ T.biUnion (Eligible.pureInternals G C), z-n ∈ chargedPurePool G C R := by
  intro z hz
  obtain ⟨w,hw,hzw⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨w,h hw,hzw⟩)
theorem chargedPurePoolSubset (hAO : IsAO2 n C) (hcross : HasCross G C)
    {R : Finset ℕ} (h : ∀ w ∈ R, w < n+C.gates.length ∧
      ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and) :
    chargedPurePool G C R ⊆ NoPureMix G C := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  exact actualLocalPurePool hAO hcross h w hw
theorem oneWingBudgetIn (hAO : IsAO2 n C) (h4 : NoFourCycle G) (P : Finset ℕ)
    {u : ℕ} (hpu : ∀ z ∈ Eligible.pureInternals G C u, z-n ∈ P)
    {y : Fin n} (hAy : ∀ v ∈ orIn n C u, G.Adj y v) :
    (forbiddenStar G C u y).card ≤ (pureWithinCenter C P y G).card + 1 := by
  apply Finset.card_image_le.trans
  exact (localPureAssignedIn hAO h4 P hpu hAy
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)).1
theorem oppositeWingsBudgetIn (hAO : IsAO2 n C) (h4 : NoFourCycle G) (P : Finset ℕ)
    {u v : ℕ} (hpu : ∀ z ∈ Eligible.pureInternals G C u, z-n ∈ P)
    (hpv : ∀ z ∈ Eligible.pureInternals G C v, z-n ∈ P)
    {y z : Fin n} (huZ : z ∈ orIn n C u) (hvY : y ∈ orIn n C v)
    (hAy : ∀ t ∈ orIn n C u, G.Adj y t) (hAz : ∀ t ∈ orIn n C v, G.Adj z t) :
    (forbiddenStar G C u y ∪ forbiddenStar G C v z).card ≤
      (pureWithinCenter C P y G).card + (pureWithinCenter C P z G).card + 1 := by
  let X := forbiddenLeaves G C u y
  let Y := forbiddenLeaves G C v z
  let A := forbiddenStar G C u y
  let B := forbiddenStar G C v z
  have hAx := Finset.card_image_le (s := X) (f := fun t => s(y,t))
  have hBy := Finset.card_image_le (s := Y) (f := fun t => s(z,t))
  have hX := localPureAssignedIn hAO h4 P hpu hAy (X := X)
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)
  have hY := localPureAssignedIn hAO h4 P hpv hAz (X := Y)
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)
  change A.card ≤ X.card at hAx
  change B.card ≤ Y.card at hBy
  change (A ∪ B).card ≤ _
  by_cases h : s(y,z) ∈ Ustar G C
  · have hA : s(y,z) ∈ A := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨huZ,h⟩)
    have hB : s(y,z) ∈ B := Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hvY,Sym2.eq_swap ▸ h⟩,Sym2.eq_swap⟩
    have hi := Finset.card_pos.mpr ⟨_,Finset.mem_inter.mpr ⟨hA,hB⟩⟩
    have hc := Finset.card_union_add_card_inter A B
    have h₁ := hX.1
    have h₂ := hY.1
    omega
  · have h₁ := hX.2 ⟨z,Finset.mem_sdiff.mpr ⟨huZ,fun u => h (Finset.mem_filter.mp u).2⟩⟩
    have h₂ := hY.2 ⟨y,Finset.mem_sdiff.mpr
      ⟨hvY,fun u => h (Sym2.eq_swap ▸ (Finset.mem_filter.mp u).2)⟩⟩
    have hc := Finset.card_union_le A B
    omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem interiorRoutesBudgetIn (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ : ℕ} (hs : junk G C = {j₀,j₁})
    (h₀₁ : ¬ InCone n C j₀ j₁) (h₁₀ : ¬ InCone n C j₁ j₀)
    {j : ℕ} (hj : j ∈ junk G C)
    (hWide : ∀ b : Fin 2, 1 < (side (n := n) C j b).card)
    (P : Finset ℕ) (hP : ∀ (b : Fin 2) z, z ∈ Eligible.pureInternals G C (opnd C j b) → z-n ∈ P)
    (V : Finset (Sym2 (Fin n))) (hV : V.Nonempty)
    (W : Sym2 (Fin n) → Fin n → Fin n → Prop)
    (hTotal : ∀ e ∈ V, ∃ y z : Fin n, W e y z)
    (hShape : ∀ e ∈ V, ∀ y z : Fin n, W e y z →
      e = s(y,z) ∧ s(y,z) ∈ Ustar G C ∧ y ∈ wmax G C j ∧
      gateVal n C j (pairInput y z) = true ∧ ∃ b : Fin 2, y ∈ side (n := n) C j b) :
    ∃ K : Finset (Fin n), K.Nonempty ∧ K.card ≤ 2 ∧
      (∀ y ∈ K, ∃ e ∈ V, ∃ z, W e y z) ∧
      (∀ t ∈ side (n := n) C j 0 ∩ side C j 1, t ∉ K) ∧
      V.card ≤ (∑ y ∈ K, (pureWithinCenter C P y G).card) + 1 := by
  classical
  let A := side (n := n) C j 0
  let B := side (n := n) C j 1
  have hJ := junkVal hAO hT hs h₀₁ h₁₀ hj
  have hW := junkWmax hAO hT hs h₀₁ h₁₀ hj
  let T (b : Fin 2) := ∃ y : Fin n, y ∈ side (n := n) C j b ∧ ∃ e ∈ V, ∃ z, W e y z
  have htrace {e : Sym2 (Fin n)} (he : e ∈ V) {y z : Fin n} (h : W e y z)
      {b : Fin 2} (hy : y ∈ side (n := n) C j b) :
      (∀ v ∈ side (n := n) C j (1-b), G.Adj y v) ∧
        e ∈ forbiddenStar G C (opnd C j (1-b)) y := by
    obtain ⟨heq,hU,hSafe,hJTrue,_⟩ := hShape e he y z h
    have hAdj := commonNeighborArm ((hW y).mp hSafe) hy
    have hz := (termsHit hJ (1-b) hJTrue).resolve_left (fun hz => G.irrefl (hAdj y hz))
    exact ⟨hAdj,Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hU⟩,heq.symm⟩⟩
  have hAvailable {y : Fin n} (hw : ∃ e ∈ V, ∃ z, W e y z) :
      y ∉ side (n := n) C j 0 ∩ side C j 1 := by
    intro hy
    obtain ⟨e,he,z,hw⟩ := hw
    have hn := wmaxOverlap ((hW y).mp (hShape e he y z hw).2.2.1)
    exact G.irrefl (hn y hy)
  have hsingle (b : Fin 2) (hb : T b) (hn : ¬ T (1-b)) :
      ∃ K : Finset (Fin n), K.Nonempty ∧ K.card ≤ 2 ∧
        (∀ y ∈ K, ∃ e ∈ V, ∃ z, W e y z) ∧
        (∀ t ∈ side (n := n) C j 0 ∩ side C j 1, t ∉ K) ∧
        V.card ≤ (∑ y ∈ K, (pureWithinCenter C P y G).card) + 1 := by
    obtain ⟨y,hy,e,he,z,hw⟩ := hb
    have hY := htrace he hw hy
    have hsub : V ⊆ forbiddenStar G C (opnd C j (1-b)) y := by
      intro f hf
      obtain ⟨v,w,h⟩ := hTotal f hf
      obtain ⟨i,hi⟩ := (hShape f hf v w h).2.2.2.2
      have hib : i = b := (eitherOperand b i).resolve_right (fun hEq => hn ⟨v,hEq ▸ hi,f,hf,w,h⟩)
      subst i
      have hT := htrace hf h hi
      have hvy := uniqueCommonCenter h4 (hWide (1-b)) hT.1 hY.1
      exact hvy ▸ hT.2
    have hc := (Finset.card_le_card hsub).trans
      (oneWingBudgetIn hAO h4 P (hP (1-b)) hY.1)
    refine ⟨{y},⟨y,by simp⟩,by simp,?_,?_,by simpa using hc⟩
    · intro t ht
      obtain rfl := Finset.mem_singleton.mp ht
      exact ⟨e,he,z,hw⟩
    · intro t ht hn
      obtain rfl := Finset.mem_singleton.mp hn
      exact hAvailable ⟨e,he,z,hw⟩ ht
  by_cases ha : T 0
  · by_cases hb : T 1
    · obtain ⟨y,hy,e,he,a,hwa⟩ := ha
      obtain ⟨z,hz,f,hf,b,hwb⟩ := hb
      have hyB : ∀ v ∈ B, G.Adj y v := (htrace he hwa hy).1
      have hzA : ∀ v ∈ A, G.Adj z v := (htrace hf hwb hz).1
      have hyzn : y ≠ z := fun h => G.irrefl (h ▸ hyB z hz)
      have hsub : V ⊆ forbiddenStar G C (opnd C j 1) y ∪ forbiddenStar G C (opnd C j 0) z := by
        intro g hg
        obtain ⟨v,w,h⟩ := hTotal g hg
        obtain ⟨i,hi⟩ := (hShape g hg v w h).2.2.2.2
        have hI := htrace hg h hi
        fin_cases i
        · have hFuel := uniqueCommonCenter h4 (hWide 1) hI.1 hyB
          exact Finset.mem_union_left _ (hFuel ▸ hI.2)
        · have hFuel := uniqueCommonCenter h4 (hWide 0) hI.1 hzA
          exact Finset.mem_union_right _ (hFuel ▸ hI.2)
      have hBound := oppositeWingsBudgetIn hAO h4 P (hP 1) (hP 0) hz hy hyB hzA
      have hCost := (Finset.card_le_card hsub).trans hBound
      refine ⟨{y,z},⟨y,by simp⟩,by simp [hyzn],?_,?_,by simpa [hyzn] using hCost⟩
      · intro t ht
        simp only [Finset.mem_insert,Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ⟨e,he,a,hwa⟩
        · exact ⟨f,hf,b,hwb⟩
      · intro t ht htn
        simp only [Finset.mem_insert,Finset.mem_singleton] at htn
        rcases htn with rfl | rfl
        · exact hAvailable ⟨e,he,a,hwa⟩ ht
        · exact hAvailable ⟨f,hf,b,hwb⟩ ht
    · exact hsingle 0 ha hb
  · by_cases hb : T 1
    · exact hsingle 1 hb ha
    · obtain ⟨e,he⟩ := hV
      obtain ⟨y,z,hw⟩ := hTotal e he
      obtain ⟨i,hi⟩ := (hShape e he y z hw).2.2.2.2
      fin_cases i
      · exact (ha ⟨y,hi,e,he,z,hw⟩).elim
      · exact (hb ⟨y,hi,e,he,z,hw⟩).elim
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem commonTailKeyCount (h4 : NoFourCycle G) {c : Fin n}
    (X L : Finset (Fin n)) (V : Finset (Sym2 (Fin n)))
    (hRoutes : ∀ e ∈ V, e ∈ Ustar G C ∧ ∃ v, e = s(c,v) ∧
      (v ∈ X ∨ ∃ x ∈ L, G.Adj x v ∧ x ≠ c)) :
    V.card ≤ X.card + L.card := by
  classical
  let Y : Finset (Sym2 (Fin n)) := X.image (fun v => s(c,v))
  let W := V \ Y
  have hCase (e : {e // e ∈ W}) : ∃ x ∈ L, ∃ v, e.val = s(c,v) ∧ G.Adj x v ∧ x ≠ c := by
    obtain ⟨he,hn⟩ := Finset.mem_sdiff.mp e.property
    obtain ⟨_,v,hEq,hc⟩ := hRoutes e.val he
    rcases hc with h | ⟨x,hX,hA,hN⟩
    · exact (hn (Finset.mem_image.mpr ⟨v,h,hEq.symm⟩)).elim
    · exact ⟨x,hX,v,hEq,hA,hN⟩
  choose x hx using hCase
  have hsub : W.attach.image x ⊆ L := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    exact (hx e).1
  have hInj : Set.InjOn x ↑W.attach := by
    intro e _ f _ hEq
    obtain ⟨_,v,he,hA,hN⟩ := hx e
    obtain ⟨_,w,hf,hB,_⟩ := hx f
    rw [← hEq] at hB
    have hUe := (hRoutes e.val (Finset.mem_sdiff.mp e.property).1).1
    have hUf := (hRoutes f.val (Finset.mem_sdiff.mp f.property).1).1
    have hAv : G.Adj c v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (he ▸ hUe)).1
    have hAw : G.Adj c w := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hf ▸ hUf)).1
    have h := Finset.card_le_one_iff.mp (h4 (x e) c hN)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA,hAv⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB,hAw⟩)
    exact Subtype.ext (he.trans (h ▸ hf.symm))
  have hw := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hInj,Finset.card_attach] at hw
  have hc : (V ∩ Y).card ≤ X.card := (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_image_le
  have hs := Finset.card_sdiff_add_card_inter V Y
  change W.card + (V ∩ Y).card = V.card at hs
  omega
theorem commonTailBudgetIn (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R P : Finset ℕ)
    (hP : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    {c : Fin n} (hAdj : ∀ w ∈ R, ∀ v ∈ orIn n C w, G.Adj c v)
    (X L : Finset (Fin n)) (hX : X ⊆ R.biUnion (orIn n C))
    (hU : ∀ v ∈ X, s(c,v) ∈ Ustar G C)
    (V : Finset (Sym2 (Fin n)))
    (hRoutes : ∀ e ∈ V, e ∈ Ustar G C ∧ ∃ v, e = s(c,v) ∧
      (v ∈ X ∨ ∃ x ∈ L, G.Adj x v ∧ x ≠ c)) :
    V.card ≤ (pureWithinCenter C P c G).card + R.card + L.card ∧
      (((R.biUnion (orIn n C)) \ X).Nonempty →
        V.card + 1 ≤ (pureWithinCenter C P c G).card + R.card + L.card) := by
  have h := commonTailKeyCount h4 X L V hRoutes
  have hPcap := localFamilyAssignedIn hAO h4 R P hP hAdj hX hU
  constructor
  · have h := hPcap.1
    omega
  · intro h
    have h' := hPcap.2 h
    omega
theorem commonTailBudgetArbitraryIn (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R P : Finset ℕ)
    (hP : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    {c : Fin n} (X L : Finset (Fin n)) (hX : X ⊆ R.biUnion (orIn n C))
    (hU : ∀ v ∈ X, s(c,v) ∈ Ustar G C)
    (V : Finset (Sym2 (Fin n)))
    (hRoutes : ∀ e ∈ V, e ∈ Ustar G C ∧ ∃ v, e = s(c,v) ∧
      (v ∈ X ∨ ∃ x ∈ L, G.Adj x v ∧ x ≠ c)) :
    V.card ≤ P.card + R.card + L.card := by
  exact (commonTailKeyCount h4 X L V hRoutes).trans
    (Nat.add_le_add_right (arbitraryFamilyAssignedIn hAO h4 R P hP hX hU) _)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
abbrev SoloRoute (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (R : Finset ℕ) (L : Finset (Fin n)) (e : Sym2 (Fin n)) (y z : Fin n) : Prop :=
  e = s(y,z) ∧ y ∈ wmax G C j ∧ gateVal n C j (pairInput y z) = true ∧
    (y ∈ R.biUnion (orIn n C) ∨ ∃ x ∈ L, G.Adj x y ∧ x ≠ z)
theorem soloBlockBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ : ℕ} (hs : junk G C = {j₀,j₁})
    (h₀₁ : ¬ InCone n C j₀ j₁) (h₁₀ : ¬ InCone n C j₁ j₀)
    {j : ℕ} (hj : j ∈ junk G C)
    (R P : Finset ℕ) (L : Finset (Fin n))
    (hPR : ∀ z ∈ R.biUnion (Eligible.pureInternals G C), z-n ∈ P)
    (hPA : ∀ (b : Fin 2) z, z ∈ Eligible.pureInternals G C (opnd C j b) → z-n ∈ P)
    (hSafeR : ∀ w ∈ R, orIn n C w ⊆ wmax G C j)
    (V : Finset (Sym2 (Fin n))) (hV : V ⊆ Ustar G C)
    (hVRoute : ∀ e ∈ V, ∃ y z : Fin n, SoloRoute G C j R L e y z) :
    V.card ≤ P.card + R.card + L.card := by
  classical
  let A := side (n := n) C j 0
  let B := side (n := n) C j 1
  let S := A ∩ B
  let Kraw := R.biUnion (orIn n C)
  let W := SoloRoute G C j R L
  have hJ := junkVal hAO hT hs h₀₁ h₁₀ hj
  have hW := junkWmax hAO hT hs h₀₁ h₁₀ hj
  by_cases hVN : V.Nonempty
  · obtain ⟨e₀,he₀⟩ := hVN
    obtain ⟨y₀,z₀,h₀⟩ := hVRoute e₀ he₀
    have hKey : 0 < R.card + L.card := by
      rcases h₀.2.2.2 with hy | ⟨x,hx,_,_⟩
      · obtain ⟨w,hw,_⟩ := Finset.mem_biUnion.mp hy
        have hp := Finset.card_pos.mpr ⟨w,hw⟩
        omega
      · have hp := Finset.card_pos.mpr ⟨x,hx⟩
        omega
    by_cases hN : ∃ b : Fin 2, (side (n := n) C j b).card ≤ 1
    · obtain ⟨b,hb⟩ := hN
      let X := Kraw.filter fun v => s(z₀,v) ∈ Ustar G C
      apply commonTailBudgetArbitraryIn hAO h4 R P hPR (c := z₀) X L
        (Finset.filter_subset _ _) (fun _ hv => (Finset.mem_filter.mp hv).2) V
      intro e he
      obtain ⟨y,z,h⟩ := hVRoute e he
      have hZ := narrowUniqueTail hJ hj hb h.2.1 h₀.2.1 h.2.2.1 h₀.2.2.1
      subst z
      have heU := hV he
      have heEq := h.1.trans Sym2.eq_swap
      refine ⟨heU,y,heEq,?_⟩
      exact h.2.2.2.imp (fun hY => Finset.mem_filter.mpr ⟨hY,heEq ▸ heU⟩) id
    have hWide (b : Fin 2) : 1 < (side (n := n) C j b).card := by
      by_contra! h
      exact hN ⟨b,h⟩
    by_cases hShared : 1 < S.card
    · have hArm : ∃ b : Fin 2, ∀ z, gateVal n C j (pairInput y₀ z) = true →
          z ∈ side (n := n) C j b := by
        by_cases hy : ∃ b : Fin 2, y₀ ∈ side (n := n) C j b
        · obtain ⟨b,hb⟩ := hy
          have ha := commonNeighborArm ((hW y₀).mp h₀.2.1) hb
          exact ⟨1-b, fun z hz => (termsHit hJ (1-b) hz).resolve_left (fun h => G.irrefl (ha y₀ h))⟩
        · exact ⟨0, fun z hz => (Finset.mem_inter.mp (exteriorTail hJ hz (fun b h => hy ⟨b,h⟩))).1⟩
      obtain ⟨b,hb⟩ := hArm
      let X := (side (n := n) C j b).filter fun z => s(y₀,z) ∈ Ustar G C
      have hx : V.card ≤ X.card := by
        apply edgeFamilyCard
        intro e he
        obtain ⟨y,z,h⟩ := hVRoute e he
        have hEq := uniqueCommonCenter h4 hShared
          (wmaxOverlap ((hW y).mp h.2.1)) (wmaxOverlap ((hW y₀).mp h₀.2.1))
        subst y
        exact ⟨z,Finset.mem_filter.mpr ⟨hb z h.2.2.1,h.1 ▸ hV he⟩,h.1⟩
      have hxSub : X ⊆ orIn n C (opnd C j b) := Finset.filter_subset _ _
      have hc := arbitraryFamilyAssignedIn hAO h4 {opnd C j b} P
        (by simpa using hPA b) (c := y₀) (X := X)
        (by simpa using hxSub) (fun _ hv => (Finset.mem_filter.mp hv).2)
      have hc' : X.card ≤ P.card + 1 := by simpa using hc
      omega
    let I := V.filter fun e => ∃ y z : Fin n, W e y z ∧ ∃ b : Fin 2, y ∈ side (n := n) C j b
    let O := V \ I
    have hSum := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset (fun e => ∃ y z : Fin n, W e y z ∧ ∃ b : Fin 2, y ∈ side (n := n) C j b) V)
    change O.card + I.card = V.card at hSum
    have hIn (e : Sym2 (Fin n)) (he : e ∈ I) : ∃ y z : Fin n, W e y z ∧
        ∃ b : Fin 2, y ∈ side (n := n) C j b := (Finset.mem_filter.mp he).2
    have hVIn : I ⊆ V := Finset.filter_subset _ _
    have hVOut : O ⊆ V := Finset.sdiff_subset
    have hOut (e) (he : e ∈ O) {y z : Fin n} (h : W e y z) :
        ∀ b : Fin 2, y ∉ side (n := n) C j b := by
      intro b hb
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨hVOut he,y,z,h,b,hb⟩)
    have hInteriorBudget (hI : I.Nonempty) :=
      interiorRoutesBudgetIn hAO hT h4 hs h₀₁ h₁₀ hj hWide P hPA I hI
        (fun e y z => W e y z ∧ ∃ b : Fin 2, y ∈ side (n := n) C j b) hIn
        (fun e he y z ⟨h,hi⟩ => ⟨h.1,h.1 ▸ hV (hVIn he),h.2.1,h.2.2.1,hi⟩)
    by_cases hON : O.Nonempty
    · obtain ⟨e,he⟩ := hON
      obtain ⟨y,s,heR⟩ := hVRoute e (hVOut he)
      have hsS : s ∈ S := exteriorTail hJ heR.2.2.1 (hOut e he heR)
      have hTail (e) (he : e ∈ O) {y z : Fin n} (h : W e y z) : z = s :=
        Finset.card_le_one_iff.mp (by omega : S.card ≤ 1)
          (exteriorTail hJ h.2.2.1 (hOut e he h)) hsS
      have hAdjS (w) (hw : w ∈ R) (v : Fin n) (hv : v ∈ orIn n C w) : G.Adj s v :=
        (wmaxOverlap ((hW v).mp (hSafeR w hw hv)) s hsS).symm
      let X := Kraw.filter fun v => (∀ b : Fin 2, v ∉ side (n := n) C j b) ∧ s(s,v) ∈ Ustar G C
      have hX : X ⊆ R.biUnion (orIn n C) := Finset.filter_subset _ _
      have hU (v : Fin n) (hv : v ∈ X) : s(s,v) ∈ Ustar G C := (Finset.mem_filter.mp hv).2.2
      have hCovOuter (L' : Finset (Fin n))
          (hLf : ∀ e∈O, ∀ y z, W e y z → ∀ x∈L,
            G.Adj x y → x ≠ z → x ∈ L') :
          ∀ e∈O, e∈Ustar G C ∧ ∃ v, e=s(s,v) ∧ (v∈X ∨ ∃x∈L', G.Adj x v ∧ x ≠ s) := by
        intro e he
        obtain ⟨y,z,h⟩ := hVRoute e (hVOut he)
        have hs' := hTail e he h
        subst z
        have hE := hV (hVOut he)
        have heq := h.1.trans Sym2.eq_swap
        refine ⟨hE,y,heq,?_⟩
        rcases h.2.2.2 with hy | ⟨x,hx,hA,hN⟩
        · exact Or.inl (Finset.mem_filter.mpr ⟨hy,hOut e he h,heq ▸ hE⟩)
        · exact Or.inr ⟨x,hLf e he y s h x hx hA hN,hA,hN⟩
      by_cases hI : I.Nonempty
      · obtain ⟨K,hK,_,hKTrace,hKOutside,hIcap⟩ := hInteriorBudget hI
        have hOutside := hKOutside s hsS
        have hBudget := pureWithinCenterSum (C := C) h4 P (insert s K)
        rw [Finset.sum_insert hOutside] at hBudget
        by_cases hMix : ∃ e∈I, ∃ y z : Fin n, W e y z ∧
            (∃ b : Fin 2, y ∈ side (n := n) C j b) ∧ ∃ x∈L, G.Adj x y ∧ x ≠ z
        · obtain ⟨ei,hei,yi,zi,hi,hSide,x,hx,hxy,hxz⟩ := hMix
          have hiOn : Guarded G C j x yi zi := ⟨hi.1 ▸ hV (hVIn hei),hi.2.1,hi.2.2.1,hxy,hxz⟩
          have hiActive : ActiveInterior C j yi := ⟨hWide,hSide⟩
          have hDisjoint : ∀ e∈O, ∀ y z, W e y z → ∀ t∈L,
              G.Adj t y → t ≠ z → t ∈ L.erase x := by
            intro e he y z h t ht htA htN
            apply Finset.mem_erase.mpr
            refine ⟨?_,ht⟩
            intro htEq
            subst t
            have ho : ¬ ActiveInterior C j y := fun ⟨_,b,hb⟩ => hOut e he h b hb
            have hoOn : Guarded G C j x y z :=
              ⟨h.1 ▸ hV (hVOut he),h.2.1,h.2.2.1,htA,htN⟩
            exact interiorAndOrdinaryConflict hAO hT h4 hs h₀₁ h₁₀ hj hiActive ho hiOn hoOn
          have hOC := (commonTailBudgetIn hAO h4 R P hPR hAdjS X (L.erase x) hX hU O
            (hCovOuter (L.erase x) hDisjoint)).1
          rw [Finset.card_erase_of_mem hx] at hOC
          have hL := Finset.card_pos.mpr ⟨x,hx⟩
          omega
        · obtain ⟨v,hv⟩ := hK
          obtain ⟨ei,hei,zi,hi,hib⟩ := hKTrace v hv
          have hvR := hi.2.2.2.resolve_right (fun hx => hMix ⟨ei,hei,v,zi,hi,hib,hx⟩)
          have hExtra : ((R.biUnion (orIn n C)) \ X).Nonempty := by
            refine ⟨v,Finset.mem_sdiff.mpr ⟨hvR,?_⟩⟩
            intro h
            obtain ⟨b,hb⟩ := hib
            exact (Finset.mem_filter.mp h).2.1 b hb
          have hOC := (commonTailBudgetIn hAO h4 R P hPR hAdjS X L hX hU O
            (hCovOuter L (fun _ _ _ _ _ _ ht _ _ => ht))).2 hExtra
          omega
      · have hEmpty := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hI)
        have hOC := (commonTailBudgetIn hAO h4 R P hPR hAdjS X L hX hU O
          (hCovOuter L (fun _ _ _ _ _ _ ht _ _ => ht))).1
        have hPool : (pureWithinCenter C P s G).card ≤ P.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        omega
    · have hEmpty := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hON)
      have hIN := Finset.card_pos.mp (show 0 < I.card from by have hp := Finset.card_pos.mpr ⟨e₀,he₀⟩; omega)
      obtain ⟨K,_,_,_,_,hC⟩ := hInteriorBudget hIN
      have hP' := pureWithinCenterSum (C := C) h4 P K
      omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hVN, Finset.card_empty]
    omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable def soloBlockRoots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) : Finset ℕ :=
  insert (opnd C j 0) (insert (opnd C j 1) (centreGuardWires G C j))
noncomputable def soloPurePool (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) : Finset ℕ :=
  chargedPurePool G C (soloBlockRoots G C j)
theorem guardRootsInSolo (j : ℕ) : centreGuardWires G C j ⊆ soloBlockRoots G C j := by
  intro w hw
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
theorem armRootInSolo (j : ℕ) (b : Fin 2) : opnd C j b ∈ soloBlockRoots G C j := by
  fin_cases b <;> simp [soloBlockRoots]
theorem soloPurePoolIsCharged (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (apart : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁) :
    soloPurePool G C j ⊆ NoPureMix G C := by
  apply chargedPurePoolSubset hAO hcross
  intro w hw
  simp only [soloBlockRoots,Finset.mem_insert] at hw
  have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  have hlen := (junkData hjm).1
  rcases hw with rfl | rfl | hw
  · have hlt := opndBound hAO hlen 0
    exact ⟨by omega,pureJunkOperand hAO hT hJ h01 h10 hjm⟩
  · have hlt := opndBound hAO hlen 1
    exact ⟨by omega,pureJunkOperand hAO hT hJ h01 h10 hjm⟩
  · exact centreGuardWirePure hAO hT hJ apart hj hw
theorem soloRoutedBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (apart : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁)
    (V : Finset (Sym2 (Fin n))) (hV : V ⊆ Ustar G C)
    (hRoutes : ∀ e ∈ V, RoutedAt G C j e) :
    V.card ≤ (soloPurePool G C j).card + (centreRoutes G C j).card +
      (mixLabels G C j₀ j₁ j).card := by
  have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  have hpR := poolCaptures (G := G) (C := C) (guardRootsInSolo (G := G) (C := C) j)
  have hpA (b : Fin 2) (z : ℕ) (hz : z ∈ Eligible.pureInternals G C (opnd C j b)) :
      z-n ∈ soloPurePool G C j :=
    poolCaptures (G := G) (C := C)
      (Finset.singleton_subset_iff.mpr (armRootInSolo (G := G) (C := C) j b)) z
      (Finset.mem_biUnion.mpr ⟨_,Finset.mem_singleton_self _,hz⟩)
  have hSafe (w : ℕ) (hw : w ∈ centreGuardWires G C j) : orIn n C w ⊆ wmax G C j := by
    intro v hv
    exact centreGuardUnionSafe hAO hT hJ apart hj (Finset.mem_biUnion.mpr ⟨w,hw,hv⟩)
  have h := soloBlockBudget hAO hT h4 hJ h01 h10 hjm (centreGuardWires G C j)
    (soloPurePool G C j) (mixLabels G C j₀ j₁ j) hpR hpA hSafe V hV
    (fun e he => routedThroughGuard hAO hT hJ apart hcross hj (hV he) (hRoutes e he))
  have hc := centreGuardWireCount (G := G) (C := C) j
  omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma closeFromCharge (slack : ℕ) (ht : slack + 5 ≤ (tops G C).card)
    (hcharge : (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card + slack)
    (hbudget : 17 + (tops G C \ centreless G C).card + 2*(centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card) : 22 ≤ C.size := by
  have hc : centreless G C ⊆ tops G C := Finset.filter_subset _ _
  have ht' := Finset.card_sdiff_add_card_eq_card hc
  omega
lemma numericShortBudget (hsize : C.size ≤ 21)
    (hbudget : 17 + (tops G C \ centreless G C).card + 2*(centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card)
    (b₀ b₁ m₀ m₁ : ℕ) (hb : b₀+b₁ ≤ (centreless G C).card) (hm : m₀+m₁ ≤ (mixing G C).card) :
    (tops G C).card + b₀ + b₁ + m₀ + m₁ + ((orN G C \ lam G C) \ mixing G C).card ≤
      (Ustar G C).card + 4 := by
  have hq := Finset.card_sdiff_add_card_eq_card
    (show centreless G C ⊆ tops G C from Finset.filter_subset _ _)
  have hp := Finset.card_sdiff_add_card_eq_card
    (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
  omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem mixByJunkTotal (hAO : IsAO2 n C) {p q : ℕ}
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) :
    (mixByJunk G C p).card + (mixByJunk G C q).card ≤ (mixing G C).card := by
  rw [← Finset.card_union_of_disjoint (mixByJunkDisjoint hAO apart)]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
theorem ctrByJunkTotal {p q : ℕ}
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) :
    (ctrByJunk G C p).card + (ctrByJunk G C q).card ≤ (centreless G C).card := by
  rw [← Finset.card_union_of_disjoint (ctrByJunkDisjoint apart)]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
theorem allRoutedBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {p q j : ℕ} (jneq : p ≠ q) (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q)
    (qp : ¬ InCone n C q p) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (cross : HasCross G C) (num : j = p ∨ j = q)
    (serve : ∀ e ∈ Ustar G C, RoutedAt G C j e) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  have hsolo := soloRoutedBudget hAO hT h4 hj pq qp apart cross num _ Finset.Subset.rfl serve
  have hP := Finset.card_le_card (soloPurePoolIsCharged hAO hT hj pq qp apart cross num)
  have hc := centreRoutesCard hAO apart
  have hm := mixLabelsCard (G := G) (C := C) jneq
  have hpart := Finset.card_sdiff_add_card_eq_card
    (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
  change (NoPureMix G C).card + (mixing G C).card = (orN G C \ lam G C).card at hpart
  rcases num with rfl | rfl <;> omega
theorem ActualPairPlan.fullRequest {j : ℕ} {c d : Fin n} (P : ActualPairPlan G C j c d)
    (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {p q : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, RoutedAt G C j e) (nonempty : E.Nonempty)
    (extra : Option (Fin 2)) (no : extra.isSome = true → s(c,d) ∉ E)
    (modeExtra : P.ordinary = false → extra ≠ some 1) :
    Nonempty (PairRequest (G := G) (C := C) E c d extra
      (mixByJunk G C j).card (ctrByJunk G C j).card) :=
  P.request hAO hT h4 cross hj pq qp apart num E sub serve extra no modeExtra _
    (fun _ => positiveActualRouteTag hAO hT cross hj apart num sub serve nonempty)
    (fun _ _ _ hm _ _ => hm)
theorem actualPairTally (hAO : IsAO2 n C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {j k : ℕ} {c d a b : Fin n} (jneq : j ≠ k)
    (apart : ∀ a ∈ tops G C, InCone n C j a → ¬ InCone n C k a)
    (E F : Finset (Sym2 (Fin n))) (e f : Option (Fin 2)) (m m' : ℕ)
    (P : PairRequest (G := G) (C := C) E c d e m (ctrByJunk G C j).card)
    (Q : PairRequest (G := G) (C := C) F a b f m' (ctrByJunk G C k).card)
    (ne : c ≠ d) (ne' : a ≠ b) (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (no : e.isSome = true → s(c,d) ∉ Ustar G C)
    (no' : f.isSome = true → s(a,b) ∉ Ustar G C)
    (extraApart : ∀ i t, e = some i → f = some t → two c d i ≠ two a b t) :
    (Ustar G C).card +
      (if s(c,d) ∈ E then 1 else if e.isSome then 1 else 0) +
      (if s(a,b) ∈ F then 1 else if f.isSome then 1 else 0) ≤
    (NoPureMix G C).card + 2 + (m + m') + (centreless G C).card := by
  let EE : Bool → Finset (Sym2 (Fin n)) := fun x => if x then F else E
  let cc : Bool → Fin n := fun x => if x then a else c
  let dd : Bool → Fin n := fun x => if x then b else d
  let ex : Bool → Option (Fin 2) := fun x => if x then f else e
  let mm : Bool → ℕ := fun x => if x then m' else m
  let zz : Bool → ℕ := fun x => if x then (ctrByJunk G C k).card else (ctrByJunk G C j).card
  have B (x : Bool) : PairRequest (G := G) (C := C) (EE x) (cc x) (dd x) (ex x) (mm x) (zz x) := by
    cases x
    · exact P
    · exact Q
  have N (x : Bool) : cc x ≠ dd x := by
    cases x
    · exact ne
    · exact ne'
  have NN (x : Bool) : (ex x).isSome = true → s(cc x,dd x) ∉ Ustar G C := by
    cases x
    · exact no
    · exact no'
  have h := pairedRequestTally hAO h4 cross EE cc dd ex mm zz B N split dis NN extraApart
  change (Ustar G C).card + (if s(c,d) ∈ E then 1 else if e.isSome then 1 else 0) +
    (if s(a,b) ∈ F then 1 else if f.isSome then 1 else 0) ≤
    (NoPureMix G C).card + 2 + (m + m') + ((ctrByJunk G C j).card + (ctrByJunk G C k).card) at h
  have hz := ctrByJunkTotal apart
  omega
theorem twoActualPairsBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (route : HasRoute G C p q) {c d a b : Fin n}
    (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card + 1 := by
  classical
  let U := Ustar G C
  let force : Finset (Sym2 (Fin n)) := if s(c,d) ∈ U then {s(c,d)} else ∅
  have hforce (e : Sym2 (Fin n)) (he : e ∈ force) : e = s(c,d) ∧ e ∈ U := by
    by_cases h : s(c,d) ∈ U
    · have eq : e = s(c,d) := by simpa [force,h] using he
      exact ⟨eq,eq.symm ▸ h⟩
    · simp [force,h] at he
  obtain ⟨E,F,dis,split,forced,_,rE,rF⟩ := twoRoutePartitionWith route force ∅
    (by simp) (fun e he => (hforce e he).2) (Finset.empty_subset _)
    (fun e he => (hforce e he).1.symm ▸ A.connector) (by simp)
  change E ∪ F = U at split
  have hE : E ⊆ U := split ▸ Finset.subset_union_left
  have hF : F ⊆ U := split ▸ Finset.subset_union_right
  by_cases epos : E.Nonempty
  · by_cases fpos : F.Nonempty
    · let extra : Option (Fin 2) := if s(c,d) ∈ U then none else some 0
      have no : extra.isSome = true → s(c,d) ∉ U := by
        by_cases h : s(c,d) ∈ U <;> simp [extra,h]
      have hmode : A.ordinary = false → extra ≠ some 1 := by
        intro _
        by_cases h : s(c,d) ∈ U <;> simp [extra,h]
      obtain ⟨P⟩ := A.fullRequest hAO hT h4 cross hj pq qp apart (.inl rfl) E hE rE epos
        extra (fun hs he => no hs (hE he)) hmode
      obtain ⟨Q⟩ := B.fullRequest hAO hT h4 cross hj pq qp apart (.inr rfl) F hF rF fpos
        none (by simp) (by simp)
      have tally := actualPairTally hAO h4 cross jneq apart E F extra none _ _ P Q A.distinct
        B.distinct split dis no (by simp) (by simp)
      have save : (if s(c,d) ∈ E then 1 else if extra.isSome then 1 else 0 : ℕ) = 1 := by
        by_cases h : s(c,d) ∈ U
        · have hs : s(c,d) ∈ E := forced (by simp [force,h])
          simp [hs]
        · have hs : s(c,d) ∉ E := fun he => h (hE he)
          simp [hs,extra,h]
      have part := Finset.card_sdiff_add_card_eq_card
        (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
      change (NoPureMix G C).card + (mixing G C).card = (orN G C \ lam G C).card at part
      have mix := mixByJunkTotal hAO apart
      omega
    · have eq : E = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp fpos] using split
      have hs := allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inl rfl) (by change ∀ e ∈ U, RoutedAt G C p e; rw [← eq]; exact rE)
      omega
  · have eq : F = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp epos] using split
    have hs := allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inr rfl) (by change ∀ e ∈ U, RoutedAt G C q e; rw [← eq]; exact rF)
    omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma fixedTailRoutesBudget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} {V : Finset (Sym2 (Fin n))} (hV : V ⊆ Ustar G C)
    (z : Fin n)
    (h : ∀ e ∈ V, ∃ y, e = s(y,z) ∧ GuardOption G C j₀ j₁ j y z) :
    V.card ≤ ((centreGuardWires G C j).biUnion (Eligible.pureInternals G C)).card +
      (centreRoutes G C j).card + (mixLabels G C j₀ j₁ j).card := by
  let Y := Finset.univ.filter fun y : Fin n => s(y,z) ∈ V
  let R := centreGuardWires G C j
  let L := mixLabels G C j₀ j₁ j
  let U := centreGuardUnion G C j
  have hY (y : Fin n) : y ∈ Y ↔ s(y,z) ∈ V := by simp [Y]
  have hVY : V ⊆ Y.image (fun y => s(y,z)) := by
    intro e he
    obtain ⟨y,hey,hG⟩ := h e he
    exact Finset.mem_image.mpr ⟨y,(hY y).mpr (hey ▸ he),hey.symm⟩
  have hVy := (Finset.card_le_card hVY).trans Finset.card_image_le
  have YR : Y ∩ U ⊆ R.biUnion (fun w => (orIn n C w).filter fun y => s(z,y) ∈ Ustar G C) := by
    intro y hy
    obtain ⟨hy,hu⟩ := Finset.mem_inter.mp hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_biUnion.mpr ⟨w,hw,
      Finset.mem_filter.mpr ⟨hv,Sym2.eq_swap ▸ hV ((hY y).mp hy)⟩⟩
  have hRY := (Finset.card_le_card YR).trans (Eligible.familyForbiddenCapacityLocal hAO h4 R z)
  have YR' : ∀ y ∈ Y \ U, ∃ x ∈ L, G.Adj x y ∧ x ≠ z := by
    intro y hy
    obtain ⟨hy,hnu⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨y',eq,guard⟩ := h _ ((hY y).mp hy)
    have hh : y = y' := by
      rcases Sym2.eq_iff.mp eq with ⟨hh,_⟩ | ⟨h₁,h₂⟩
      · exact hh
      · exact h₁.trans h₂
    subst y'
    exact guard.resolve_left hnu
  have hAdj (y : Fin n) (hy : y ∈ Y \ U) : G.Adj z y := by
    have he := hV ((hY y).mp (Finset.mem_sdiff.mp hy).1)
    exact (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1).symm
  have hYL := (exteriorMixCount h4 L (Y \ U) z hAdj YR').trans
    (Finset.card_filter_le _ _)
  have hPart := Finset.card_sdiff_add_card_eq_card (show Y ∩ U ⊆ Y from Finset.inter_subset_left)
  have eq : Y \ (Y ∩ U) = Y \ U := by
    ext y
    simp
  rw [eq] at hPart
  have hR := centreGuardWireCount (G := G) (C := C) j
  change V.card ≤ (R.biUnion (Eligible.pureInternals G C)).card +
     (centreRoutes G C j).card + L.card
  change R.card ≤ (centreRoutes G C j).card at hR
  omega
lemma guardOverlapAdj (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hj : j ∈ junk G C) {s y : Fin n}
    (hs : s ∈ side (n := n) C j 0 ∩ side C j 1) (hy : y ∈ wmax G C j) :
    G.Adj s y := by
  obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hs
  have hit := (junkWmax hAO hT hJ h01 h10 hj y).mp hy s ha s hb
  rcases hit with h | h | h
  · exact (G.irrefl h).elim
  · exact h
  · exact h
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (supportLeaves supportEdges supportCard)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
structure StarRequest (E : Finset (Sym2 (Fin n))) (c : Fin n)
    (mixBudget centreBudget : ℕ) where
  roots : Finset ℕ
  leaves : Finset (Fin n)
  mixed : ℕ
  bound : ∀ w ∈ roots, w < n + C.gates.length
  pure : ∀ w ∈ roots, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and
  covered : leaves ⊆ roots.biUnion (orIn n C)
  targets : ∀ x ∈ leaves, s(c,x) ∈ E
  tally : E.card ≤ leaves.card + mixed
  cost : roots.card + mixed ≤ mixBudget + centreBudget
theorem starRequestWithProperties (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q j : ℕ}
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, RoutedAt G C j e) (pos : E.Nonempty) (c : Fin n)
    (star : ∀ e ∈ E, c ∈ e) :
    ∃ R : StarRequest (C := C) E c (mixByJunk G C j).card (ctrByJunk G C j).card,
      ((c ∈ wmax G C j → c ∈ side (n := n) C j 0 ∨ c ∈ side C j 1) ∧
        (c ∉ wmax G C j → (ctrByJunk G C j).card = 0 ∨ c ∈ side (n := n) C j 0 ∩ side C j 1)) →
      ∀ w ∈ R.roots, ∀ x ∈ orIn n C w, G.Adj c x := by
  classical
  let X := supportLeaves E c Finset.univ
  have memE (x : Fin n) (hx : x ∈ X) : s(c,x) ∈ E := (Finset.mem_filter.mp hx).2
  have cardX : E.card ≤ X.card := by
    rw [← supportCard E c Finset.univ]
    apply Finset.card_le_card
    intro e he
    obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp (star e he)
    exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  by_cases safe : c ∈ wmax G C j
  · have jm : j ∈ junk G C := by simpa [hj] using num
    have lack : ∃ b : Fin 2, c ∉ side (n := n) C j b := by
      by_contra! h
      exact G.irrefl (guardOverlapAdj hAO hT hj pq qp jm (Finset.mem_inter.mpr ⟨h 0,h 1⟩) safe)
    obtain ⟨b,hb⟩ := lack
    let w := opnd C j b
    have bw := opndBound hAO (junkData jm).1 b
    have root : X ⊆ orIn n C w := by
      intro x hx
      have v := servedByPair (serve _ (memE x hx))
      obtain ⟨_,_,_,_,_,on⟩ := v
      exact (termsHit (junkVal hAO hT hj pq qp jm) b on).resolve_left hb
    have tag := positiveActualRouteTag hAO hT cross hj apart num sub serve pos
    refine ⟨⟨{w},X,0,?_,?_,?_,memE,by omega,by simpa using tag⟩,?_⟩
    · intro v hv
      rw [Finset.mem_singleton.mp hv]
      exact bw.trans_le (Nat.add_le_add_left (Nat.le_of_lt (junkData jm).1) n)
    · intro v hv
      rw [Finset.mem_singleton.mp hv]
      exact pureJunkOperand hAO hT hj pq qp jm
    · simpa using root
    · intro H v hV x hx
      have hc := H.1 safe
      have hv : v = opnd C j b := Finset.mem_singleton.mp hV
      rw [hv] at hx
      have on : gateVal n C j (pairInput c x) = true := by
        apply (junkVal hAO hT hj pq qp jm _).mpr
        fin_cases b
        · exact ⟨⟨x,hx,by simp [pairInput]⟩,
            ⟨c,hc.resolve_left hb,by simp [pairInput]⟩⟩
        · exact ⟨⟨c,hc.resolve_right hb,by simp [pairInput]⟩,
            ⟨x,hx,by simp [pairInput]⟩⟩
      exact (Local1490.graphFun_pair G c x).mp ((Finset.mem_filter.mp safe).2 _ on (by simp [pairInput]))
  · let R := ctrRoots G C j
    let Y := X ∩ R.biUnion (orIn n C)
    let Z := X \ R.biUnion (orIn n C)
    have ct : R.card ≤ (ctrByJunk G C j).card := ctrRootCard hAO j
    have mt : Z.card ≤ (mixByJunk G C j).card :=
      mixedOutsideRoots hAO hT h4 cross hj apart num E sub serve c safe
    have eq : X \ Y = Z := by ext x; simp [Y,Z]
    have sum := Finset.card_sdiff_add_card_eq_card (show Y ⊆ X from Finset.inter_subset_left)
    rw [eq] at sum
    refine ⟨⟨R,Y,Z.card,fun x hx => (rootProperties hAO hT hj apart num hx).1,
      fun x hx => (rootProperties hAO hT hj apart num hx).2.1,Finset.inter_subset_right,
      fun x hx => memE x (Finset.mem_inter.mp hx).1,by omega,by omega⟩,?_⟩
    intro H w hw x hx
    rcases H.2 safe with zero | inside
    · have no : R = ∅ := Finset.card_eq_zero.mp (by omega)
      simpa [no] using hw
    · have hjm : j ∈ junk G C := by simpa [hj] using num
      exact guardOverlapAdj hAO hT hj pq qp hjm inside ((rootProperties hAO hT hj apart num hw).2.2 hx)
theorem starRequestExists (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q j : ℕ}
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (serve : ∀ e ∈ E, RoutedAt G C j e) (pos : E.Nonempty) (c : Fin n)
    (star : ∀ e ∈ E, c ∈ e) :
    Nonempty (StarRequest (C := C) E c (mixByJunk G C j).card (ctrByJunk G C j).card) := by
  obtain ⟨R,_⟩ := starRequestWithProperties hAO hT h4 cross hj pq qp apart num E sub serve pos c star
  exact ⟨R⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem summedForestOneSelective {ι : Type*} [DecidableEq ι] (I : Finset ι) (center : ι → Fin n)
    (roots : ι → Finset ℕ) (leaves : ι → Finset (Fin n)) (special : Fin n)
    (hAO : IsAO2 n C) (h4 : NoFourCycle G) (hcross : HasCross G C)
    (hBound : ∀ i ∈ I, ∀ w ∈ roots i, w < n + C.gates.length)
    (hPure : ∀ i ∈ I, ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    (hAdj : ∀ i ∈ I, center i ≠ special → ∀ w ∈ roots i, ∀ v ∈ orIn n C w, G.Adj (center i) v)
    (hLeafAdj : ∀ i ∈ I, ∀ v ∈ leaves i, G.Adj (center i) v)
    (hCover : ∀ i ∈ I, leaves i ⊆ (roots i).biUnion (orIn n C))
    (hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → center i = center j → Disjoint (leaves i) (leaves j))
    (hPairs : ∀ i ∈ I, ∀ j ∈ I, center i = center j → ∀ u ∈ leaves i, ∀ v ∈ leaves j, u ≠ v →
      s(center i,u) ∈ Ustar G C ∨ s(center i,v) ∈ Ustar G C) :
    (∑ i ∈ I, (leaves i).card) ≤ (NoPureMix G C).card + ∑ i ∈ I, (roots i).card :=
  summedForestOptionalSelective I center roots leaves (some special) hAO h4 hcross hBound hPure
    (fun i hi neq => hAdj i hi (fun hc => neq (congrArg some hc))) hLeafAdj hCover hDisj hPairs
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem starPairTally (hAO : IsAO2 n C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {E F : Finset (Sym2 (Fin n))} {a c d : Fin n}
    {m₀ m₁ z₀ z₁ : ℕ} {extra : Option (Fin 2)}
    (A : StarRequest (C := C) E a m₀ z₀)
    (B : PairRequest (G := G) (C := C) F c d extra m₁ z₁)
    (ne : c ≠ d) (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (no : extra.isSome = true → s(c,d) ∉ Ustar G C) (conn : G.Adj c d) :
    (Ustar G C).card + (if s(c,d) ∈ F then 1 else if extra.isSome then 1 else 0) ≤
      (NoPureMix G C).card + 1 + (m₀ + m₁) + (z₀ + z₁) := by
  classical
  let center : Fin 3 → Fin n := Fin.cases a (two c d)
  let roots : Fin 3 → Finset ℕ := Fin.cases A.roots B.roots
  let leaves : Fin 3 → Finset (Fin n) := Fin.cases A.leaves B.leaves
  have hE : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have hF : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  have genuine (i : Fin 2) (x : Fin n) (h : x ∈ B.leaves i) :
      s(two c d i,x) ∈ F ∨ (extra = some i ∧ x = two d c i) := B.targets i x h
  have virtual (i : Fin 2) (x : Fin n) (h : extra = some i ∧ x = two d c i) :
      s(two c d i,x) ∉ Ustar G C := by
    rw [h.2]
    have hSame : s(two c d i,two d c i) = s(c,d) := by
      fin_cases i
      · rfl
      · exact Sym2.eq_swap
    rw [hSame]
    exact no (by rw [h.1]; rfl)
  have adj (i : Fin 3) (x : Fin n) (hx : x ∈ leaves i) : G.Adj (center i) x := by
    refine Fin.cases ?_ (fun j => ?_) i hx
    · intro hx
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hE (A.targets x hx))).1
    · intro hx
      rcases genuine j x hx with he | ⟨_,rfl⟩
      · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hF he)).1
      · fin_cases j
        · exact conn
        · exact conn.symm
  have rootAdj (i : Fin 3) (neq : center i ≠ a) (w : ℕ) (hw : w ∈ roots i)
      (x : Fin n) (hx : x ∈ orIn n C w) : G.Adj (center i) x := by
    refine Fin.cases ?_ (fun j => ?_) i neq hw hx
    · intro h _ _
      exact (h rfl).elim
    · exact fun _ hr hx => B.adjacent j w hr x hx
  have rootBound (i : Fin 3) : ∀ w ∈ roots i, w < n+C.gates.length := by
    exact Fin.cases A.bound B.bound i
  have rootPure (i : Fin 3) : ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and := by
    exact Fin.cases A.pure B.pure i
  have covered (i : Fin 3) : leaves i ⊆ (roots i).biUnion (orIn n C) :=
    Fin.cases A.covered B.covered i
  have different (i j : Fin 3) (hne : i ≠ j) (eq : center i = center j) :
      Disjoint (leaves i) (leaves j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have half (j : Fin 2) (eq : a = two c d j) (ha : x ∈ A.leaves) (hb : x ∈ B.leaves j) : False := by
      have he := A.targets x ha
      rw [eq] at he
      rcases genuine j x hb with he' | hv
      · exact Finset.disjoint_left.mp dis he he'
      · exact virtual j x hv (hE he)
    refine Fin.cases ?_ (fun k => ?_) i hne eq hx hy
    · refine Fin.cases ?_ (fun l => ?_) j
      · exact fun h _ _ _ => h rfl
      · exact fun _ hh hA hB => half l hh hA hB
    · refine Fin.cases ?_ (fun l => ?_) j
      · exact fun _ hh hA hB => half k hh.symm hB hA
      · intro h eq _ _
        have hkl : k = l := two_injective ne eq
        exact h (congrArg Fin.succ hkl)
  have pairs (i j : Fin 3) (eq : center i = center j)
      (x : Fin n) (hx : x ∈ leaves i) (y : Fin n) (hy : y ∈ leaves j) (xy : x ≠ y) :
      s(center i,x) ∈ Ustar G C ∨ s(center i,y) ∈ Ustar G C := by
    refine Fin.cases ?_ (fun k => ?_) i eq hx hy
    · exact fun _ hx _ => Or.inl (hE (A.targets x hx))
    · intro eq hx hy
      rcases genuine k x hx with he | hvirt
      · exact Or.inl (hF he)
      · refine Fin.cases ?_ (fun l => ?_) j eq hy
        · exact fun eq hy => Or.inr (eq.symm ▸ hE (A.targets y hy))
        · intro heq hy
          rcases genuine l y hy with he | hvirty
          · exact Or.inr (heq.symm ▸ hF he)
          · have kl : k = l := two_injective ne heq
            subst l
            exact (xy (hvirt.2.trans hvirty.2.symm)).elim
  have forest := summedForestOneSelective Finset.univ center roots leaves a hAO h4 cross
    (fun i _ => rootBound i) (fun i _ => rootPure i) (fun i _ => rootAdj i) (fun i _ => adj i)
    (fun i _ => covered i) (fun i _ j _ => different i j) (fun i _ j _ => pairs i j)
  change (∑ i : Fin 3, (leaves i).card) ≤ _ + ∑ i : Fin 3, (roots i).card at forest
  have counts (f : Fin 3 → ℕ) : (∑ i : Fin 3, f i) = f 0 + f (Fin.succ 0) + f (Fin.succ 1) := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_two,Nat.add_assoc]
  rw [counts (fun i => (leaves i).card),counts (fun i => (roots i).card)] at forest
  simp only [leaves,roots,Fin.cases_zero,Fin.cases_succ] at forest
  have hA := A.tally
  have hB := B.tally
  have cA := A.cost
  have cB := B.cost
  have card := Finset.card_union_of_disjoint dis
  rw [split] at card
  omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem actualStarPairBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (route : HasRoute G C p q) {a c d : Fin n}
    (star : ∀ e, RoutedAt G C p e → a ∈ e)
    (B : ActualPairPlan G C q c d) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  classical
  let U := Ustar G C
  let force : Finset (Sym2 (Fin n)) := if s(c,d) ∈ U then {s(c,d)} else ∅
  have hforce (e : Sym2 (Fin n)) (he : e ∈ force) : e = s(c,d) ∧ e ∈ U := by
    by_cases h : s(c,d) ∈ U
    · have eq : e = s(c,d) := by simpa [force,h] using he
      exact ⟨eq,eq.symm ▸ h⟩
    · simp [force,h] at he
  obtain ⟨E,F,dis,split,_,forced,rE,rF⟩ := twoRoutePartitionWith route ∅ force
    (by simp) (Finset.empty_subset _) (fun e he => (hforce e he).2)
    (by simp) (fun e he => (hforce e he).1.symm ▸ B.connector)
  change E ∪ F = U at split
  have hE : E ⊆ U := split ▸ Finset.subset_union_left
  have hF : F ⊆ U := split ▸ Finset.subset_union_right
  by_cases epos : E.Nonempty
  · by_cases fpos : F.Nonempty
    · let extra : Option (Fin 2) := if s(c,d) ∈ U then none else some 0
      have no : extra.isSome = true → s(c,d) ∉ U := by
        by_cases h : s(c,d) ∈ U <;> simp [extra,h]
      have hmode : B.ordinary = false → extra ≠ some 1 := by
        intro _
        by_cases h : s(c,d) ∈ U <;> simp [extra,h]
      obtain ⟨P⟩ := starRequestExists hAO hT h4 cross hj pq qp apart (.inl rfl) E hE rE epos
        a (fun e he => star e (rE e he))
      obtain ⟨Q⟩ := B.fullRequest hAO hT h4 cross hj pq qp apart (.inr rfl) F hF rF fpos
        extra (fun hs he => no hs (hF he)) hmode
      have tally := starPairTally hAO h4 cross P Q B.distinct split dis no (B.adjacent d B.connectorLeaf)
      have save : (if s(c,d) ∈ F then 1 else if extra.isSome then 1 else 0 : ℕ) = 1 := by
        by_cases h : s(c,d) ∈ U
        · have hs : s(c,d) ∈ F := forced (by simp [force,h])
          simp [hs]
        · have hs : s(c,d) ∉ F := fun he => h (hF he)
          simp [hs,extra,h]
      have part := Finset.card_sdiff_add_card_eq_card
        (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
      change (NoPureMix G C).card + (mixing G C).card = (orN G C \ lam G C).card at part
      have mix := mixByJunkTotal hAO apart
      have ctr := ctrByJunkTotal apart
      omega
    · have eq : E = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp fpos] using split
      exact allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inl rfl)
        (by change ∀ e ∈ U, RoutedAt G C p e; rw [← eq]; exact rE)
  · have eq : F = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp epos] using split
    exact allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inr rfl)
      (by change ∀ e ∈ U, RoutedAt G C q e; rw [← eq]; exact rF)
theorem hasRouteComm {p q : ℕ} (route : HasRoute G C p q) : HasRoute G C q p := by
  intro x y he
  obtain ⟨a,ha,b,j,jnum,on,reach,act⟩ := route x y he
  exact ⟨a,ha,b,j,jnum.symm,on,reach,act⟩
theorem actualPairStarBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (route : HasRoute G C p q) {a c d : Fin n}
    (B : ActualPairPlan G C p c d)
    (star : ∀ e, RoutedAt G C q e → a ∈ e) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card :=
  actualStarPairBudget hAO hT h4 cross jneq.symm (by simpa only [Finset.pair_comm] using hj) qp pq
    (fun a ha hq hp => apart a ha hp hq) (hasRouteComm route) star B
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (safe armEdge overlapEdge)
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem ActualPairPlan.reserveAssigned {j : ℕ} {c d : Fin n} (P : ActualPairPlan G C j c d)
    (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {p q : ℕ} (hj : junk G C = {p,q}) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q) (E : Finset (Sym2 (Fin n))) (sub : E ⊆ Ustar G C)
    (overlap : P.ordinary = false) (zero : (ctrByJunk G C j).card = 0) (notConn : s(c,d) ∉ E) :
    ∃ m ∈ mixByJunk G C j, ∀ v, s(d,v) ∈ E → ∀ k ∈ mixByJunk G C j, (orIn n C (n+k)).Nonempty →
      (∀ x ∈ orIn n C (n+k), G.Adj x v ∧ x ≠ d) → k ∈ (mixByJunk G C j).erase m := by
  have mode := P.mode
  simp only [overlap,Bool.false_eq_true,if_false] at mode
  have no : d ∉ wmax G C j := fun hw => G.irrefl (mode.1 d hw)
  obtain ⟨m,hm,hperm⟩ := reservedMixPermit hAO hT h4 cross hj apart num zero no
    (P.adjacent d P.connectorLeaf) P.connector
  refine ⟨m,hm,fun v hv k hk _ can => Finset.mem_erase.mpr ⟨?_,hk⟩⟩
  have he := sub hv
  have vn : v ≠ c := by
    rintro rfl
    exact notConn (Sym2.eq_swap ▸ hv)
  exact hperm v k vn (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1) can
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
private def connectorSet (U : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Finset (Sym2 (Fin n)) :=
  if e ∈ U then {e} else ∅
private theorem connectorSetMem {U : Finset (Sym2 (Fin n))} {e f : Sym2 (Fin n)} :
    e ∈ connectorSet U f ↔ e = f ∧ e ∈ U := by
  by_cases h : f ∈ U
  · simp only [connectorSet,h,if_true,Finset.mem_singleton]
    exact ⟨fun eq => ⟨eq,eq.symm ▸ h⟩,And.left⟩
  · simp only [connectorSet,h,if_false,Finset.notMem_empty,false_iff]
    exact fun ⟨eq,he⟩ => h (eq ▸ he)
def connectorExtra (U : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (i : Fin 2) : Option (Fin 2) :=
  if e ∈ U then none else some i
theorem connectorExtraNo {U : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)} {i : Fin 2}
    (h : (connectorExtra U e i).isSome = true) : e ∉ U := by
  by_contra! he
  simp [connectorExtra,he] at h
theorem connectorExtraSave {U E : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)} {i : Fin 2}
    (hE : E ⊆ U) (force : e ∈ U → e ∈ E) :
    (if e ∈ E then 1 else if (connectorExtra U e i).isSome then 1 else 0 : ℕ) = 1 := by
  by_cases h : e ∈ U
  · simp [force h]
  · have no := fun h' => h (hE h')
    simp [connectorExtra,h,no]
private theorem pureMixPart : (NoPureMix G C).card + (mixing G C).card =
    (orN G C \ lam G C).card :=
  Finset.card_sdiff_add_card_eq_card (fun _ h => mixingNotLam h)
theorem actualPairAssignedExact (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (E F : Finset (Sym2 (Fin n))) (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (rE : ∀ x ∈ E, RoutedAt G C p x) (rF : ∀ x ∈ F, RoutedAt G C q x)
    (forceA : s(c,d) ∈ Ustar G C → s(c,d) ∈ E)
    (forceB : s(a,b) ∈ Ustar G C → s(a,b) ∈ F)
    (i j : Fin 2) (imode : A.ordinary = false → i ≠ 1) (jmode : B.ordinary = false → j ≠ 1)
    (extraApart : s(c,d) ∉ Ustar G C → s(a,b) ∉ Ustar G C → two c d i ≠ two a b j) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  let U := Ustar G C
  have hE : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have hF : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  by_cases epos : E.Nonempty
  · by_cases fpos : F.Nonempty
    · let e := connectorExtra U s(c,d) i
      let f := connectorExtra U s(a,b) j
      have ne : e.isSome = true → s(c,d) ∉ U := connectorExtraNo
      have nf : f.isSome = true → s(a,b) ∉ U := connectorExtraNo
      have ea : A.ordinary = false → e ≠ some 1 := by
        intro h
        by_cases k : s(c,d) ∈ U <;> simp [e,connectorExtra,k,imode h]
      have fb : B.ordinary = false → f ≠ some 1 := by
        intro h
        by_cases k : s(a,b) ∈ U <;> simp [f,connectorExtra,k,jmode h]
      have hdiff (u v : Fin 2) (he : e = some u) (hf : f = some v) : two c d u ≠ two a b v := by
        have nu := ne (by rw [he]; rfl)
        have nv := nf (by rw [hf]; rfl)
        have hu : i = u := by simpa [e,connectorExtra,nu] using he
        have hv : j = v := by simpa [f,connectorExtra,nv] using hf
        exact hu ▸ hv ▸ extraApart nu nv
      obtain ⟨R⟩ := A.fullRequest hAO hT h4 cross hj pq qp apart (.inl rfl) E hE rE epos
        e (fun hs he => ne hs (hE he)) ea
      obtain ⟨S⟩ := B.fullRequest hAO hT h4 cross hj pq qp apart (.inr rfl) F hF rF fpos
        f (fun hs he => nf hs (hF he)) fb
      have count := actualPairTally hAO h4 cross jneq apart E F e f _ _ R S A.distinct
        B.distinct split dis ne nf hdiff
      have saveE := connectorExtraSave (i := i) hE forceA
      have saveF := connectorExtraSave (i := j) hF forceB
      change (if s(c,d) ∈ E then 1 else if e.isSome then 1 else 0 : ℕ) = 1 at saveE
      change (if s(a,b) ∈ F then 1 else if f.isSome then 1 else 0 : ℕ) = 1 at saveF
      have mix := mixByJunkTotal hAO apart
      have part := pureMixPart (G := G) (C := C)
      omega
    · have eq : E = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp fpos] using split
      exact allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inl rfl)
        (by change ∀ x ∈ U, RoutedAt G C p x; rw [← eq]; exact rE)
  · have eq : F = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp epos] using split
    exact allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inr rfl)
      (by change ∀ x ∈ U, RoutedAt G C q x; rw [← eq]; exact rF)
theorem actualPairAssignedReserved (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (overlap : A.ordinary = false) (zero : (ctrByJunk G C p).card = 0)
    (E F : Finset (Sym2 (Fin n))) (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (rE : ∀ x ∈ E, RoutedAt G C p x) (rF : ∀ x ∈ F, RoutedAt G C q x)
    (noA : s(c,d) ∉ E) (forceB : s(a,b) ∈ Ustar G C → s(a,b) ∈ F) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  let U := Ustar G C
  have hE : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have hF : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  by_cases fpos : F.Nonempty
  · let f := connectorExtra U s(a,b) 0
    have nf : f.isSome = true → s(a,b) ∉ U := connectorExtraNo
    have fb : B.ordinary = false → f ≠ some 1 := by
      intro _
      by_cases k : s(a,b) ∈ U <;> simp [f,connectorExtra,k]
    obtain ⟨m,hm,can⟩ := A.reserveAssigned hAO hT h4 cross hj apart (.inl rfl) E hE overlap zero noA
    let M := (mixByJunk G C p).erase m
    obtain ⟨R⟩ := A.request hAO hT h4 cross hj pq qp apart (.inl rfl) E hE rE none
      (by simp) (by simp) M (fun h => by simp [overlap] at h) can
    obtain ⟨S⟩ := B.fullRequest hAO hT h4 cross hj pq qp apart (.inr rfl) F hF rF fpos
      f (fun hs he => nf hs (hF he)) fb
    have count := actualPairTally hAO h4 cross jneq apart E F none f _ _ R S A.distinct
      B.distinct split dis (by simp) nf (by simp)
    have save := connectorExtraSave (i := 0) hF forceB
    change (if s(a,b) ∈ F then 1 else if f.isSome then 1 else 0 : ℕ) = 1 at save
    have mm := Finset.card_erase_add_one hm
    change M.card + 1 = (mixByJunk G C p).card at mm
    have mix := mixByJunkTotal hAO apart
    have part := pureMixPart (G := G) (C := C)
    omega
  · have eq : E = U := by simpa [Finset.not_nonempty_iff_eq_empty.mp fpos] using split
    exact allRoutedBudget hAO hT h4 jneq hj pq qp apart cross (.inl rfl)
      (by change ∀ x ∈ U, RoutedAt G C p x; rw [← eq]; exact rE)
theorem actualPairCollisionReserved (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) (route : HasRoute G C p q)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (overlap : A.ordinary = false) (zero : (ctrByJunk G C p).card = 0) (eq : s(c,d) = s(a,b)) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  let U := Ustar G C
  let F := connectorSet U s(a,b)
  obtain ⟨E₀,E₁,dis,split,_,force,r₀,r₁⟩ := twoRoutePartitionWith route ∅ F
    (by simp) (Finset.empty_subset _) (fun _ h => (connectorSetMem.mp h).2)
    (by simp) (fun _ h => (connectorSetMem.mp h).1.symm ▸ B.connector)
  have f₁ (h : s(a,b) ∈ U) : s(a,b) ∈ E₁ := force (connectorSetMem.mpr ⟨rfl,h⟩)
  have no (hc : s(c,d) ∈ E₀) : False := by
    have sub : E₀ ⊆ Ustar G C := split ▸ Finset.subset_union_left
    exact Finset.disjoint_left.mp dis hc (eq.symm ▸ f₁ (eq ▸ sub hc))
  exact actualPairAssignedReserved hAO hT h4 cross jneq hj pq qp apart A B overlap zero
    E₀ E₁ split dis r₀ r₁ no f₁
theorem actualPairDistinctExactOr (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) (route : HasRoute G C p q)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (zne : c ≠ a ∨ (ctrByJunk G C p).card = 0 ∨ (ctrByJunk G C q).card = 0)
    (ne : s(c,d) ≠ s(a,b)) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  let U := Ustar G C
  let F₀ := connectorSet U s(c,d)
  let F₁ := connectorSet U s(a,b)
  have fd : Disjoint F₀ F₁ := Finset.disjoint_left.mpr fun _ h k =>
    ne ((connectorSetMem.mp h).1.symm.trans (connectorSetMem.mp k).1)
  obtain ⟨E,F,dis,split,hf₀,hf₁,rE,rF⟩ := twoRoutePartitionWith route F₀ F₁ fd
    (fun _ h => (connectorSetMem.mp h).2) (fun _ h => (connectorSetMem.mp h).2)
    (fun _ h => (connectorSetMem.mp h).1.symm ▸ A.connector)
    (fun _ h => (connectorSetMem.mp h).1.symm ▸ B.connector)
  have f₀ (h : s(c,d) ∈ U) : s(c,d) ∈ E := hf₀ (connectorSetMem.mpr ⟨rfl,h⟩)
  have f₁ (h : s(a,b) ∈ U) : s(a,b) ∈ F := hf₁ (connectorSetMem.mpr ⟨rfl,h⟩)
  have subE : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have subF : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  by_cases hc : c = a
  · by_cases mA : A.ordinary = false
    · by_cases mB : B.ordinary = false
      · by_cases both : s(c,d) ∉ U ∧ s(a,b) ∉ U
        · rcases zne.resolve_left (fun h => h hc) with hz | hz
          · exact actualPairAssignedReserved hAO hT h4 cross jneq hj pq qp apart A B mA hz
              E F split dis rE rF (fun h => both.1 (subE h)) f₁
          · exact actualPairAssignedReserved hAO hT h4 cross jneq.symm
              (by simpa only [Finset.pair_comm] using hj) qp pq (fun x hx qh ph => apart x hx ph qh)
              B A mB hz F E (by rw [Finset.union_comm]; exact split) dis.symm rF rE
              (fun h => both.2 (subF h)) f₀
        · exact actualPairAssignedExact hAO hT h4 cross jneq hj pq qp apart A B E F split dis
            rE rF f₀ f₁ 0 0 (by simp) (by simp) (fun h k => (both ⟨h,k⟩).elim)
      · exact actualPairAssignedExact hAO hT h4 cross jneq hj pq qp apart A B E F split dis
          rE rF f₀ f₁ 0 1 (by simp) (fun h => (mB h).elim)
          (fun _ _ => by simpa only [two_zero,two_one,hc] using B.distinct)
    · exact actualPairAssignedExact hAO hT h4 cross jneq hj pq qp apart A B E F split dis
        rE rF f₀ f₁ 1 0 (fun h => (mA h).elim) (by simp)
        (fun _ _ => by simpa only [two_zero,two_one,← hc] using A.distinct.symm)
  · exact actualPairAssignedExact hAO hT h4 cross jneq hj pq qp apart A B E F split dis
      rE rF f₀ f₁ 0 0 (by simp) (by simp) (fun _ _ => by simpa only [two_zero] using hc)
theorem actualPairDistinctExact (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (jneq : p ≠ q)
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) (route : HasRoute G C p q)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (zne : (ctrByJunk G C p).card = 0 ∨ (ctrByJunk G C q).card = 0)
    (ne : s(c,d) ≠ s(a,b)) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card :=
  actualPairDistinctExactOr hAO hT h4 cross jneq hj pq qp apart route A B (Or.inr zne) ne
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Profile2264 (graph)
theorem routedPairCoverFive {C : Circuit} {p q : ℕ}
    (route : HasRoute graph C p q) (K D : Finset (Fin 11))
    (hK : (graph.deleteEdges (Ustar graph C : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)))
    (hd : D.card ≤ 2)
    (h₀ : ∀ u v, RoutedAt graph C p s(u,v) → u ∈ D ∨ v ∈ D)
    (h₁ : ∀ u v, RoutedAt graph C q s(u,v) → u ∈ D ∨ v ∈ D) :
    5 ≤ K.card := by
  have cover (u v : Fin 11) (e : s(u,v) ∈ Ustar graph C) : u ∈ D ∨ v ∈ D := by
    obtain ⟨a,ha,b,j,jnum,on,reach,act⟩ := route u v e
    rcases jnum with rfl | rfl
    · exact h₀ u v ⟨u,v,rfl,a,ha,b,on,reach,act⟩
    · exact h₁ u v ⟨u,v,rfl,a,ha,b,on,reach,act⟩
  have h₇ := Profile2264.seven_cover _ (Profile2264.cover_uncovered K D _ hK cover)
  have hcap := Finset.card_union_le K D
  omega
theorem sharedConnectorCoverFive {C : Circuit} {p q : ℕ}
    (route : HasRoute graph C p q) (K : Finset (Fin 11))
    (hK : (graph.deleteEdges (Ustar graph C : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)))
    {c d a b : Fin 11} (A : ActualPairPlan graph C p c d) (B : ActualPairPlan graph C q a b)
    (same : s(c,d) = s(a,b)) :
    5 ≤ K.card := by
  let D : Finset (Fin 11) := {c,d}
  have hd : D.card ≤ 2 := (Finset.card_pair A.distinct).le
  have deq : D = {a,b} := by
    rcases Sym2.eq_iff.mp same with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
    · simp only [D,h₀,h₁]
    · simp only [D,h₀,h₁,Finset.pair_comm]
  have r₀ (u v : Fin 11) (r : RoutedAt graph C p s(u,v)) :
      u ∈ D ∨ v ∈ D := by
    have h := A.covers u v r
    simp only [D,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have r₁ (u v : Fin 11) (r : RoutedAt graph C q s(u,v)) :
      u ∈ D ∨ v ∈ D := by
    have h := B.covers u v r
    simp only [deq,Finset.mem_insert,Finset.mem_singleton]
    tauto
  exact routedPairCoverFive route K D hK hd r₀ r₁
theorem twoStarCoverFive {C : Circuit} {p q : ℕ}
    (route : HasRoute graph C p q) (K : Finset (Fin 11))
    (hK : (graph.deleteEdges (Ustar graph C : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)))
    {a b : Fin 11} (A : ∀ e, RoutedAt graph C p e → a ∈ e)
    (B : ∀ e, RoutedAt graph C q e → b ∈ e) :
    5 ≤ K.card := by
  let D : Finset (Fin 11) := {a,b}
  have d : D.card ≤ 2 := (Finset.card_insert_le _ _).trans_eq (by simp)
  have r₀ (u v : Fin 11) (r : RoutedAt graph C p s(u,v)) :
      u ∈ D ∨ v ∈ D := by
    rcases Sym2.mem_iff.mp (A _ r) with h | h
    · exact Or.inl (by simp [D,← h])
    · exact Or.inr (by simp [D,← h])
  have r₁ (u v : Fin 11) (r : RoutedAt graph C q s(u,v)) :
      u ∈ D ∨ v ∈ D := by
    rcases Sym2.mem_iff.mp (B _ r) with h | h
    · exact Or.inl (by simp [D,← h])
    · exact Or.inr (by simp [D,← h])
  exact routedPairCoverFive route K D hK d r₀ r₁
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open UsefulJunk2264 (armEdge)
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem directedMixerAt (hAO : IsAO2 n C) (cross : HasCross G C)
    {j : ℕ} {x y : Fin n} (hj : j ∈ junk G C)
    (hZ : centreless G C = ∅) (route : directedRoute G C j x y) :
    ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, ∃ m ∈ mixByJunk G C j,
      OrReaches n C (opnd C a b) j ∧
      OrReaches n C (opnd C a b) m ∧
      x ∈ side (n := n) C a (1-b) ∧
      (orIn n C (n+m)).Nonempty ∧ ∀ r ∈ orIn n C (n+m), G.Adj r x := by
  obtain ⟨a,ha,b,hr,hx,_,_⟩ := route
  have hA : a ∈ tops G C \ centreless G C := by simpa [hZ] using ha
  obtain ⟨m,hm,rm,rj,hn⟩ := mixingAlong (G := G) hAO hr (junkData hj).2.1 (nonCenterlessSides hA b)
  refine ⟨a,hA,b,m,Finset.mem_filter.mpr ⟨hm,rj,a,ha,b,rm⟩,hr,rm,hx,hn,?_⟩
  intro r rh
  have inSide : r ∈ side (n := n) C a b := orInTrans (orReaches_reach m _ rm).1 rh
  fin_cases b
  · exact cross a ha r inSide x hx
  · exact (cross a ha x hx r inSide).symm
theorem actualWideArms (hAO : IsAO2 n C) (hT : TopForm G C)
    {p q j : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q)
    (qp : ¬ InCone n C q p) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q)
    (wide : ∀ c, ∃ x y, RoutedAt G C j s(x,y) ∧ x ≠ c ∧ y ≠ c) (initial : Fin n) (i : Fin 2) :
    1 < (side (n := n) C j i).card := by
  have hmem : j ∈ junk G C := by simpa [hj] using num
  have hits {x y : Fin n} (r : RoutedAt G C j s(x,y)) :
      x ∈ side (n := n) C j i ∨ y ∈ side (n := n) C j i := by
    rcases edgeToDirectedRoute hAO hT hj apart num r with a | b
    · obtain ⟨_,_,_,_,_,_,on⟩ := a
      exact termsHit (junkVal hAO hT hj pq qp hmem) i on
    · obtain ⟨_,_,_,_,_,_,on⟩ := b
      exact (termsHit (junkVal hAO hT hj pq qp hmem) i on).symm
  by_contra! h
  obtain ⟨x,y,hr,_,_⟩ := wide initial
  have hN : (side (n := n) C j i).Nonempty :=
    (hits hr).elim (fun h => ⟨x,h⟩) (fun h => ⟨y,h⟩)
  obtain ⟨c,hS⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr hN))
  obtain ⟨u,v,huv,hu,hv⟩ := wide c
  have H := hits huv
  rw [hS, Finset.mem_singleton, Finset.mem_singleton] at H
  exact H.elim hu hv
theorem ordinaryDirections (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {p q j : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q)
    (qp : ¬ InCone n C q p) (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q)
    (wide : ∀ c, ∃ x y, RoutedAt G C j s(x,y) ∧ x ≠ c ∧ y ≠ c)
    {c d : Fin n} (P : ActualPairPlan G C j c d) (ord : P.ordinary = true) :
    (∃ x, directedRoute G C j c x) ∧ ∃ y, directedRoute G C j d y := by
  have hmem : j ∈ junk G C := by simpa [hj] using num
  have mode := P.mode
  simp only [ord,ite_true] at mode
  obtain ⟨F,fRaw,hc,fAdj,covers⟩ := mode
  obtain ⟨i,di⟩ : ∃ i : Fin 2, P.raw = side (n := n) C j i :=
    P.rawSide.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  obtain ⟨k,fk⟩ : ∃ k : Fin 2, F = side (n := n) C j k :=
    fRaw.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  have cn : c ∉ P.raw := fun h => G.irrefl (P.adjacent _ h)
  have dn : d ∉ F := fun h => G.irrefl (fAdj _ h)
  have kEq : k = 1-i := by
    apply (eitherOperand i k).resolve_left
    intro h
    apply cn
    rwa [di,←h,←fk]
  have iEq : i = 1-k := by
    rw [kEq]
    fin_cases i <;> decide
  have chooseRoute {a b : Fin n} {D Z : Finset (Fin n)} {u : Fin 2}
      (hD : D = side (n := n) C j u) (hZ : Z = side (n := n) C j (1-u))
      (bAdj : ∀ z ∈ Z, G.Adj b z)
      (hC : ∀ x y, RoutedAt G C j s(x,y) → armEdge a D x y ∨ armEdge b Z x y) :
      ∃ z, directedRoute G C j a z := by
    obtain ⟨x,y,r,xb,yb⟩ := wide b
    have left : armEdge a D x y := (hC x y r).resolve_right
      (fun h => h.elim (fun h => xb h.1) (fun h => yb h.1))
    have finish {z : Fin n} (m : z ∈ D) (ne : z ≠ b)
        (rr : RoutedAt G C j s(a,z)) : directedRoute G C j a z := by
      apply (edgeToDirectedRoute hAO hT hj apart num rr).resolve_right
      rintro ⟨_,_,_,_,_,sw,_⟩
      have hm : z ∈ side (n := n) C j u := hD ▸ m
      have hzAdj := commonNeighborArm ((junkWmax hAO hT hj pq qp hmem z).mp sw) hm
      have other := actualWideArms hAO hT hj pq qp apart num wide a (1-u)
      exact ne (uniqueCommonCenter h4 other hzAdj (fun t ht => bAdj t (hZ.symm ▸ ht)))
    rcases left with ⟨rfl,h⟩ | ⟨rfl,h⟩
    · exact ⟨y,finish h yb r⟩
    · exact ⟨x,finish h xb (Sym2.eq_swap ▸ r)⟩
  exact ⟨chooseRoute di (kEq ▸ fk) fAdj covers,
    chooseRoute fk (iEq ▸ di) P.adjacent (fun x y r => (covers x y r).symm)⟩
theorem singleMixerCommonCentre (hAO : IsAO2 n C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (cross : HasCross G C) {p q j : ℕ}
    (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (num : j = p ∨ j = q)
    (wide : ∀ c, ∃ x y, RoutedAt G C j s(x,y) ∧ x ≠ c ∧ y ≠ c)
    (hZ : centreless G C = ∅) {c d : Fin n}
    (P : ActualPairPlan G C j c d) (ord : P.ordinary = true)
    (hM : (mixByJunk G C j).card ≤ 1)
    (f : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (select : ∀ a, ∃ i : Fin 2, side (n := n) C a.val i = {f a})
    (outside : ∀ a, f a ≠ c ∧ f a ≠ d) :
    ∃ a, InCone n C j a.val ∧ G.Adj (f a) c ∧ G.Adj (f a) d := by
  have hmem : j ∈ junk G C := by simpa [hj] using num
  obtain ⟨⟨x,rx⟩,y,ry⟩ := ordinaryDirections hAO hT h4 hj pq qp apart num wide P ord
  obtain ⟨a,ha,i,m,hm,_,_,_,_,mAdj⟩ := directedMixerAt hAO cross hmem hZ rx
  obtain ⟨b,hb,k,o,ho,_,_,_,_,oAdj⟩ := directedMixerAt hAO cross hmem hZ ry
  have hSame := Finset.card_le_one_iff.mp hM ho hm
  subst o
  have connector {u v : Fin n} (which : u = c ∨ u = d) (r : directedRoute G C j u v) :
      ∃ a, InCone n C j a.val ∧ G.Adj (f a) c ∧ G.Adj (f a) d := by
    obtain ⟨a,ha,i,t,ht,reach,treach,ug,tNon,_⟩ := directedMixerAt hAO cross hmem hZ r
    have ta : a ∈ tops G C := (Finset.mem_sdiff.mp ha).1
    let node : {a // a ∈ tops G C \ centreless G C} := ⟨a,ha⟩
    obtain ⟨b,hb⟩ := select node
    obtain ⟨z,hz⟩ := tNon
    have hmEq := Finset.card_le_one_iff.mp hM ht hm
    subst t
    have hzi : z ∈ side (n := n) C a i := orInTrans (orReaches_reach m _ treach).1 hz
    have ib : b = i := by
      apply (eitherOperand i b).resolve_right
      intro be
      have h : side (n := n) C a (1-i) = {f node} := be ▸ hb
      rw [h,Finset.mem_singleton] at ug
      exact which.elim (fun uc => (outside node).1 (ug.symm.trans uc))
        (fun ud => (outside node).2 (ug.symm.trans ud))
    subst b
    change side (n := n) C a i = {f node} at hb
    rw [hb,Finset.mem_singleton] at hzi
    exact ⟨node,operandReachCone hAO (topData ta).1 reach,hzi ▸ mAdj z hz,hzi ▸ oAdj z hz⟩
  exact (edgeToDirectedRoute hAO hT hj apart num P.connector).elim
    (connector (.inl rfl)) (connector (.inr rfl))
theorem identicalPairCentres (hAO : IsAO2 n C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (cross : HasCross G C) (star : HasStar G C)
    (hseven : ∀ K : Finset (Fin n), G.IsVertexCover (↑K) → 7 ≤ K.card)
    {p q : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (route : HasRoute G C p q) (h5 : (tops G C).card = 5) (hZ : centreless G C = ∅)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (aOrd : A.ordinary = true) (bOrd : B.ordinary = true) (same : s(c,d) = s(a,b))
    (wideP : ∀ c, ∃ x y, RoutedAt G C p s(x,y) ∧ x ≠ c ∧ y ≠ c)
    (wideQ : ∀ c, ∃ x y, RoutedAt G C q s(x,y) ∧ x ≠ c ∧ y ≠ c) :
    3 ≤ (mixing G C).card := by
  classical
  by_contra! hM
  have hpj : p ∈ junk G C := by simp [hj]
  have hqj : q ∈ junk G C := by simp [hj]
  have pos {j u v} (hm : j ∈ junk G C) (num : j = p ∨ j = q)
      (r : RoutedAt G C j s(u,v)) : 0 < (mixByJunk G C j).card := by
    have each {u v} (h : directedRoute G C j u v) : 0 < (mixByJunk G C j).card := by
      obtain ⟨_,_,_,m,hm,_⟩ := directedMixerAt hAO cross hm hZ h
      exact Finset.card_pos.mpr ⟨m,hm⟩
    exact (edgeToDirectedRoute hAO hT hj apart num r).elim each each
  have hP := pos hpj (.inl rfl) A.connector
  have hQ := pos hqj (.inr rfl) B.connector
  have sum := mixByJunkTotal hAO apart
  let T := tops G C \ centreless G C
  let f : {x // x ∈ T} → Fin n := fun x => Classical.choose (singletonSide star x.property)
  let K := T.attach.image f
  let S : Finset (Fin n) := {c,d}
  have select (x : {x // x ∈ T}) : ∃ i : Fin 2, side (n := n) C x.val i = {f x} :=
    Classical.choose_spec (singletonSide star x.property)
  have Kch : ChoosesCenters G C K := by
    intro x hx
    exact ⟨f ⟨x,hx⟩,Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_attach _ _,rfl⟩,select ⟨x,hx⟩⟩
  have Kcov := coversStars Kch
  have Tc : T.card = 5 := by simp [T,hZ,h5]
  have Kc : K.card ≤ 5 := by
    apply Finset.card_image_le.trans
    simp [Finset.card_attach,Tc]
  have Sc : S.card = 2 := by simp [S,A.distinct]
  have sameS : ({a,b} : Finset (Fin n)) = S := by
    rcases Sym2.eq_iff.mp same with ⟨ea,eb⟩ | ⟨ea,eb⟩
    · simp [S,ea,eb]
    · simp [S,ea,eb,Finset.pair_comm]
  obtain ⟨E,F,_,hU,rE,rF⟩ := twoRoutePartition route
  have GS : G.IsVertexCover (↑(K ∪ S)) := by
    intro u v huv
    by_cases he : s(u,v) ∈ Ustar G C
    · have hpair {x y : Fin n} (hEq : ({x,y} : Finset (Fin n)) = S)
          (h : u = x ∨ v = x ∨ u = y ∨ v = y) : u ∈ S ∨ v ∈ S := by
        have hx : x ∈ S := hEq ▸ Finset.mem_insert_self _ _
        have hy : y ∈ S := hEq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rcases h with rfl | rfl | rfl | rfl
        · exact Or.inl hx
        · exact Or.inr hx
        · exact Or.inl hy
        · exact Or.inr hy
      have H : u ∈ S ∨ v ∈ S := (Finset.mem_union.mp (hU.symm ▸ he)).elim
        (fun h => hpair rfl (A.covers u v (rE _ h)))
        (fun h => hpair sameS (B.covers u v (rF _ h)))
      exact H.imp (Finset.mem_union_right _) (Finset.mem_union_right _)
    · exact (Kcov (SimpleGraph.deleteEdges_adj.mpr ⟨huv,he⟩)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  have full := hseven _ GS
  have sizeUnion := Finset.card_union_add_card_inter K S
  have K5 : K.card = T.attach.card := by rw [Finset.card_attach,Tc]; omega
  have dis : Disjoint K S :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  have inj : Set.InjOn f (↑T.attach) := Finset.card_image_iff.mp K5
  have fOut (x : {x // x ∈ T}) : f x ∉ S :=
    fun h => Finset.disjoint_left.mp dis
      (show f x ∈ K from Finset.mem_image_of_mem _ (Finset.mem_attach _ _)) h
  have pd (x : {x // x ∈ T}) : f x ≠ c ∧ f x ≠ d := by
    have h := fOut x
    simpa [S] using h
  have qd (x : {x // x ∈ T}) : f x ≠ a ∧ f x ≠ b := by
    have h := fOut x
    rw [←sameS] at h
    simpa using h
  obtain ⟨k,kr,kc,kd⟩ := singleMixerCommonCentre hAO hT h4 cross hj pq qp apart (.inl rfl)
    wideP hZ A aOrd (by omega) f select pd
  obtain ⟨l,lr,la,lb⟩ := singleMixerCommonCentre hAO hT h4 cross hj pq qp apart (.inr rfl)
    wideQ hZ B bOrd (by omega) f select qd
  have lc : G.Adj (f l) c := by
    rcases Sym2.eq_iff.mp same with ⟨h,_⟩ | ⟨h,_⟩
    · exact h.symm ▸ la
    · exact h.symm ▸ lb
  have ld : G.Adj (f l) d := by
    rcases Sym2.eq_iff.mp same with ⟨_,h⟩ | ⟨_,h⟩
    · exact h.symm ▸ lb
    · exact h.symm ▸ la
  have both (x : Fin n) (hc : G.Adj x c) (hd : G.Adj x d) :
      x ∈ Finset.univ.filter (fun w => G.Adj c w ∧ G.Adj d w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc.symm,hd.symm⟩
  have eqF := Finset.card_le_one_iff.mp (h4 c d A.distinct) (both _ kc kd) (both _ lc ld)
  have equ := inj (Finset.mem_attach _ _) (Finset.mem_attach _ _) eqF
  exact apart k.val (Finset.mem_sdiff.mp k.property).1 kr (equ.symm ▸ lr)
theorem ordinaryFullRawRequest (hAO : IsAO2 n C) (hT : TopForm G C)
    {p q j : ℕ} (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (num : j = p ∨ j = q) {c d : Fin n} (P : ActualPairPlan G C j c d) (ord : P.ordinary = true)
    (E : Finset (Sym2 (Fin n))) (serve : ∀ e ∈ E, RoutedAt G C j e)
    (extra : Option (Fin 2)) (no : extra.isSome = true → s(c,d) ∉ E)
    (z : ℕ) : Nonempty (PairRequest (G := G) (C := C) E c d extra 1 z) := by
  have hm : j ∈ junk G C := by simpa [hj] using num
  have mode := P.mode
  simp only [ord,ite_true] at mode
  obtain ⟨F,fRaw,hc,fAdj,covers⟩ := mode
  exact ordinaryPairRequests hAO hT hj pq qp hm E c d P.rawSide fRaw P.connectorLeaf hc
    P.adjacent fAdj (fun x y he => covers x y (serve _ he)) extra no 1 z (by omega)
theorem bothOrdinaryCommonBudget (hAO : IsAO2 n C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (cross : HasCross G C) (star : HasStar G C)
    (hseven : ∀ K : Finset (Fin n), G.IsVertexCover (↑K) → 7 ≤ K.card)
    {p q : ℕ} (jneq : p ≠ q) (hj : junk G C = {p,q}) (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a)
    (route : HasRoute G C p q) (h5 : (tops G C).card = 5) (hZ : centreless G C = ∅)
    {c d a b : Fin n} (A : ActualPairPlan G C p c d) (B : ActualPairPlan G C q a b)
    (aOrd : A.ordinary = true) (bOrd : B.ordinary = true) (same : s(c,d) = s(a,b))
    (wideP : ∀ c, ∃ x y, RoutedAt G C p s(x,y) ∧ x ≠ c ∧ y ≠ c)
    (wideQ : ∀ c, ∃ x y, RoutedAt G C q s(x,y) ∧ x ≠ c ∧ y ≠ c) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  classical
  have highMix := identicalPairCentres hAO hT h4 cross star hseven hj pq qp apart route h5 hZ
    A B aOrd bOrd same wideP wideQ
  let U := Ustar G C
  let force : Finset (Sym2 (Fin n)) := if s(c,d) ∈ U then {s(c,d)} else ∅
  have hforce (e : Sym2 (Fin n)) (he : e ∈ force) : e = s(c,d) ∧ e ∈ U := by
    by_cases h : s(c,d) ∈ U
    · have eq : e = s(c,d) := by simpa [force,h] using he
      exact ⟨eq,eq.symm ▸ h⟩
    · simp [force,h] at he
  obtain ⟨E,F,dis,split,forced,_,rE,rF⟩ := twoRoutePartitionWith route force ∅
    (by simp) (fun e he => (hforce e he).2) (Finset.empty_subset _)
    (fun e he => (hforce e he).1.symm ▸ A.connector) (by simp)
  change E ∪ F = U at split
  have hE : E ⊆ U := split ▸ Finset.subset_union_left
  let extra : Option (Fin 2) := if s(c,d) ∈ U then none else some 0
  have no : extra.isSome = true → s(c,d) ∉ U := by
    by_cases h : s(c,d) ∈ U <;> simp [extra,h]
  obtain ⟨P⟩ := ordinaryFullRawRequest hAO hT hj pq qp (.inl rfl) A aOrd E rE
    extra (fun hs he => no hs (hE he)) (ctrByJunk G C p).card
  obtain ⟨Q⟩ := ordinaryFullRawRequest hAO hT hj pq qp (.inr rfl) B bOrd F rF
    none (by simp) (ctrByJunk G C q).card
  have tally := actualPairTally hAO h4 cross jneq apart E F extra none _ _ P Q A.distinct
    B.distinct split dis no (by simp) (by simp)
  have save : (if s(c,d) ∈ E then 1 else if extra.isSome then 1 else 0 : ℕ) = 1 := by
    by_cases h : s(c,d) ∈ U
    · have hs : s(c,d) ∈ E := forced (by simp [force,h])
      simp [hs]
    · have hs : s(c,d) ∉ E := fun he => h (hE he)
      simp [hs,extra,h]
  have part := Finset.card_sdiff_add_card_eq_card
    (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
  change (NoPureMix G C).card + (mixing G C).card = (orN G C \ lam G C).card at part
  rw [hZ,Finset.card_empty] at tally ⊢
  omega
end PEqualNP.Outside.L_meta_2264

-- Output tree counting and wire deletion follow L-meta-1491.
namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
namespace S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u
def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)
lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]
lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]
lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]
lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]
def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u
def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false
def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩
def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩
def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu
lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega
lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]
lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl
lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]
lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)
lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]
lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length
def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true
lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega
lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)
lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩
lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)
lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h
lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega
lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega
lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega
lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega
lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)
lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem
lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout.2 j (by omega)
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := htj.elim (fun h => h.symm ▸ c1 j r hr hmr) (fun h => c2 t j r hr h hmr)
    have nh (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) : ¬ Cone t k :=
      hTop t k ht hk hopt hBt hop
    refine ⟨r,hr,hmr,fun k hk hm => ?_,(hL.1 r hr).1.resolve_left (fun h => nh r hr h hc),
      up n C hL hout.2 Cone c2 t nh _ r hr rfl hc⟩
    rcases lt_trichotomy k r with h | h | h
    · exact (two_readers n C hL hout.2 j hB k r h hr hm hmr).elim
    · exact h
    · exact (two_readers n C hL hout.2 j hB r k h hk hmr hm).elim
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega
lemma coneFromReader (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ)
    (hk : k < C.gates.length) (ht : t = i ∨ InCone n C t i)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  obtain ⟨_,a,b,hin,ha,hb⟩ := hA k hk
  have h := hm
  rw [hin] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  exact (Local1490.inCone_iff n C t k).mpr ⟨hk,i,by omega,hm,ht⟩

lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩
lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab
lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩
lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩
lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩
lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl
theorem main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C)
    (fun i k hk => coneFromReader n C hAO i i k hk (.inl rfl))
    (fun t i k hk ht => coneFromReader n C hAO t i k hk (.inr ht))
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
end S98
theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5
lemma junkClassification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma twoJunkSize (hne : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) {j₀ j₁ : ℕ} (hlt : j₀ < j₁)
    (hJ : junk G C = {j₀, j₁}) :
    C.size = 2 * (tops G C).card + (orN G C).card + 1 := by
  have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
    (fun k => (gateAt C k).op = GateOp.or) (BelowF G C) ?_ (tops G C) (junk G C) (orT G C) (orN G C)
    (fun _ => by simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range])
    (junkClassification G C)
    (fun _ => by simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range])
    (fun _ => by simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range])
  · have ht := (S98.main_real n G C hne hL hT).2.2
    have hj : (junk G C).card = 2 := by simp [hJ, hlt.ne]
    change C.gates.length = _
    omega
  · intro k hk
    rcases hL.1.1 _ (gateAt_mem hk) with h | h
    · exact .inl ⟨h, by intro hn; rw [h] at hn; cases hn⟩
    · exact .inr ⟨h, by intro hn; rw [h] at hn; cases hn⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def atomWire (n j₀ j₁ : ℕ) : Fin n ⊕ Bool → ℕ
  | .inl x => x.val
  | .inr false => n+j₀
  | .inr true => n+j₁
noncomputable def atoms (C : Circuit) (n j₀ j₁ w : ℕ) : Finset (Fin n ⊕ Bool) := by
  classical
  exact Finset.univ.filter fun a =>
    if let .inl x := a then x ∈ orIn n C w
    else OrReaches n C w (atomWire n j₀ j₁ a - n)
lemma memAtoms {j₀ j₁ w : ℕ} {a : Fin n ⊕ Bool} :
    a ∈ atoms C n j₀ j₁ w ↔
      Relation.ReflTransGen (OrStep n C) w (atomWire n j₀ j₁ a) ∧
        atomWire n j₀ j₁ a < n + C.gates.length := by
  classical
  unfold atoms
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  cases a with
  | inl x =>
    simp only [atomWire]
    exact ⟨fun h => ⟨mem_orIn_reach x h, by omega⟩, fun h => reach_mem_orIn x h.1⟩
  | inr b =>
    cases b <;> simp only [atomWire, Nat.add_sub_cancel_left]
    · exact ⟨fun h => by obtain ⟨a,b⟩ := orReaches_reach _ _ h; exact ⟨a, by omega⟩,
        fun ⟨h,hlt⟩ => reach_orReaches h _ rfl (by omega)⟩
    · exact ⟨fun h => by obtain ⟨a,b⟩ := orReaches_reach _ _ h; exact ⟨a, by omega⟩,
        fun ⟨h,hlt⟩ => reach_orReaches h _ rfl (by omega)⟩
lemma leastWireDistinct (hL : IsLeastAO G C) {w j : ℕ}
    (hw : w < n+j) (hj : j < C.gates.length) :
    ∃ x : Fin n → Bool, val C (List.ofFn x) w ≠ gateVal n C j x := by
  have hLeast : S98.Least n C := ⟨S98.AO_of_IsAO2 n C hL.1, fun D hAO hfun =>
    hL.2.2 D (S98.IsAO2_of_AO n D hAO) (funext fun x => (hfun x).trans (congrFun hL.2.1 x))⟩
  exact S98.least_nodup n C hLeast w j hw hj
lemma junkIncomparableSides (hL : IsLeastAO G C) (hT : TopForm G C)
    {j₀ j₁ : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    {j : ℕ} (hj : j ∈ junk G C) (b : Fin 2) :
    ¬ side (n := n) C j b ⊆ side C j (1-b) := by
  intro hs
  have hjl := (junkData hj).1
  obtain ⟨x, hx⟩ := leastWireDistinct hL (opndBound hL.1 hjl b) hjl
  apply hx
  apply Bool.eq_iff_iff.mpr
  rw [pureOrVal hL.1 (pureJunkOperand hL.1 hT hJ h01 h10 hj) x,
      andValOperands hL.1 hjl (junkData hj).2.1]
  constructor
  · intro he i
    apply (pureOrVal hL.1 (pureJunkOperand hL.1 hT hJ h01 h10 hj) x).mpr
    rcases eitherOperand b i with rfl | rfl
    · exact he
    · obtain ⟨v, hv, hxv⟩ := he
      exact ⟨v, hs hv, hxv⟩
  · intro he
    exact (pureOrVal hL.1 (pureJunkOperand hL.1 hT hJ h01 h10 hj) x).mp (he b)
end PEqualNP.Outside.L_meta_2264
namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem leastNoWireAlias (hL : IsLeastAO G C) {a w : ℕ}
    (ha : a < C.gates.length) (hw : w < n + a)
    (he : ∀ x : Fin n → Bool, val C (List.ofFn x) w = val C (List.ofFn x) (n + a)) : False := by
  obtain ⟨x, hx⟩ := leastWireDistinct hL hw ha
  exact hx (he x)
private theorem boolEqOfTruth {a b : Bool} (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all
theorem junkArmsIncomparable (hL : IsLeastAO G C) (hT : TopForm G C) {j₀ j₁ : ℕ}
    (hs : junk G C = {j₀, j₁}) (h₀₁ : ¬ InCone n C j₀ j₁)
    (h₁₀ : ¬ InCone n C j₁ j₀) {a : ℕ} (ha : a ∈ junk G C) :
    ¬ side (n := n) C a 0 ⊆ side C a 1 ∧ ¬ side (n := n) C a 1 ⊆ side C a 0 := by
  have hal := (junkData ha).1
  have hAO := hL.1
  constructor
  · intro hsub
    apply leastNoWireAlias hL hal (opndBound hAO hal 0)
    intro x
    apply boolEqOfTruth
    change val C (List.ofFn x) (opnd C a 0) = true ↔ gateVal n C a x = true
    rw [pureOrVal hAO (pureJunkOperand hAO hT hs h₀₁ h₁₀ ha) x,
      junkVal hAO hT hs h₀₁ h₁₀ ha x]
    exact ⟨fun h => ⟨h, by obtain ⟨v, hv, hvx⟩ := h; exact ⟨v, hsub hv, hvx⟩⟩, And.left⟩
  · intro hsub
    apply leastNoWireAlias hL hal (opndBound hAO hal 1)
    intro x
    apply boolEqOfTruth
    change val C (List.ofFn x) (opnd C a 1) = true ↔ gateVal n C a x = true
    rw [pureOrVal hAO (pureJunkOperand hAO hT hs h₀₁ h₁₀ ha) x,
      junkVal hAO hT hs h₀₁ h₁₀ ha x]
    exact ⟨fun h => ⟨by obtain ⟨v, hv, hvx⟩ := h; exact ⟨v, hsub hv, hvx⟩, h⟩, And.right⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem residualCoverFromEdgeCentres
    (hseven : ∀ K : Finset (Fin n), G.IsVertexCover (↑K) → 7 ≤ K.card)
    (hcover : ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges (↑(Ustar G C))) K →
      K.card ≤ (tops G C \ centreless G C).card)
    (S : Finset (Fin n)) (hS : ∀ e ∈ Ustar G C, ∃ x ∈ S, x ∈ e) :
    7 ≤ (tops G C \ centreless G C).card + S.card := by
  classical
  obtain ⟨K,hK⟩ := existsMinCover (G.deleteEdges (↑(Ustar G C)))
  have hc : G.IsVertexCover (↑(K ∪ S)) := by
    intro a b hab
    by_cases h : s(a,b) ∈ Ustar G C
    · obtain ⟨x,hx,he⟩ := hS _ h
      rcases Sym2.mem_iff.mp he with rfl | rfl
      · exact Or.inl (Finset.mem_union_right _ hx)
      · exact Or.inr (Finset.mem_union_right _ hx)
    · rcases hK.1 (SimpleGraph.deleteEdges_adj.mpr ⟨hab,h⟩) with ha | hb
      · exact Or.inl (Finset.mem_union_left _ ha)
      · exact Or.inr (Finset.mem_union_left _ hb)
  exact (hseven _ hc).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (hcover K hK) _))
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open Profile2264 (graph)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def compactDecidable : DecidableRel graph.Adj := inferInstance
def RemainingStars : Prop :=
  ∀ (C : Circuit) (j₀ j₁ : ℕ),
    IsLeastAO graph C → TopForm graph C →
    (∀ a ∈ tops graph C,
      (∀ x ∈ side (n := 11) C a 0, ∀ y ∈ side (n := 11) C a 1, graph.Adj x y) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1)) →
    HasRoute graph C j₀ j₁ →
    17 + (tops graph C \ centreless graph C).card + 2 * (centreless graph C).card +
      (orN graph C \ lam graph C).card ≤ C.size + (Ustar graph C).card →
    (∀ K : Finset (Fin 11), IsMinCover (graph.deleteEdges (↑(Ustar graph C))) K →
      K.card ≤ (tops graph C \ centreless graph C).card) →
    j₀ < j₁ → junk graph C = {j₀,j₁} →
    (¬ InCone 11 C j₀ j₁) → (¬ InCone 11 C j₁ j₀) →
    (∀ a ∈ tops graph C, InCone 11 C j₀ a → ¬ InCone 11 C j₁ a) →
    4 ≤ (tops graph C \ centreless graph C).card →
    5 ≤ (tops graph C).card →
    (∃ v : Fin 11, ∀ e, RoutedAt graph C j₀ e → v ∈ e) →
    (∃ v : Fin 11, ∀ e, RoutedAt graph C j₁ e → v ∈ e) →
    22 ≤ C.size
set_option maxHeartbeats 2000000 in
theorem exactFromStars (hm : RemainingStars) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G d C j₀ j₁ hG
  change G = graph at hG
  subst G
  have hdec : d = compactDecidable := Subsingleton.elim _ _
  subst d
  intro hL hT
  dsimp only
  intro hU hW hbudget hcover hlt hj h01 h10 hsep
  have hcross : HasCross graph C := fun a ha => (hU a ha).1
  have hstar : HasStar graph C := fun a ha => (hU a ha).2
  have hG : NoFourCycle graph := by decide +kernel
  by_contra hs
  have hsz : C.size ≤ 21 := by omega
  let T := (tops graph C \ centreless graph C).card
  let Z := (centreless graph C).card
  have jmem₀ : j₀ ∈ junk graph C := hj.symm ▸ Finset.mem_insert_self _ _
  have jmem₁ : j₁ ∈ junk graph C := hj.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨D₀,d₀,_,r₀⟩ := junkHasTwoCover (G := graph) hG hL.1 hT hj h01 h10 jmem₀
  obtain ⟨D₁,d₁,_,r₁⟩ := junkHasTwoCover (G := graph) hG hL.1 hT hj h01 h10 jmem₁
  have rout (e : Sym2 (Fin 11)) (he : e ∈ Ustar graph C) : ∃ v ∈ D₀ ∪ D₁, v ∈ e := by
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨a,ha,b,j,tag,on,reach,son⟩ := hW x y he
      obtain ⟨r,subset⟩ := ustarAttaches hL.1 hT hj hsep ha reach tag on
      have hw := r.imp (fun h => subset h) (fun h => subset h)
      have choose : x ∈ D₀ ∪ D₁ ∨ y ∈ D₀ ∪ D₁ := by
        rcases tag with rfl | rfl
        · exact (r₀ x y son hw).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
        · exact (r₁ x y son hw).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
      rcases choose with hx | hy
      · exact ⟨x,hx,Sym2.mem_iff.mpr (Or.inl rfl)⟩
      · exact ⟨y,hy,Sym2.mem_iff.mpr (Or.inr rfl)⟩
  have hTmin : 3 ≤ T := by
    have resid := residualCoverFromEdgeCentres Profile2264.seven_cover hcover _ rout
    change 7 ≤ T + (D₀ ∪ D₁).card at resid
    have de := Finset.card_union_le D₀ D₁
    omega
  have hTZ : T+Z = (tops graph C).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have h5 : 5 ≤ (tops graph C).card := by
    by_cases h3 : T = 3
    · have two := threeForcesTwoCentreless C j₀ j₁ hL hT hj h01 h10 hsep hU hW h3
      change 2 ≤ Z at two
      omega
    · by_contra! h
      have h4 : T = 4 := by omega
      have hz : Z = 0 := by omega
      exact fourNeedsCentreless C j₀ j₁ hL hT hj h01 h10 hsep hU h4 (Finset.card_eq_zero.mp hz)
  let Nonstar (j : ℕ) := ∀ c : Fin 11, ∃ x y : Fin 11, RoutedAt graph C j s(x,y) ∧ x ≠ c ∧ y ≠ c
  have wide (j : ℕ) (h : ¬ (∃ v : Fin 11, ∀ e, RoutedAt graph C j e → v ∈ e)) : Nonstar j := by
    dsimp [Nonstar]
    push Not at h
    intro c
    obtain ⟨e,hr,hn⟩ := h c
    induction e using Sym2.ind with
    | _ x y =>
      exact ⟨x,y,hr,
        fun eq => hn (Sym2.mem_iff.mpr (Or.inl eq.symm)),
        fun eq => hn (Sym2.mem_iff.mpr (Or.inr eq.symm))⟩
  have zeroClose
      (h : (Ustar graph C).card ≤ (centreless graph C).card + (orN graph C \ lam graph C).card) :
      False := hs (closeFromCharge 0 h5 (by simpa using h) hbudget)
  have jneq := Nat.ne_of_lt hlt
  by_cases st₀ : ∃ v : Fin 11, ∀ e, RoutedAt graph C j₀ e → v ∈ e
  · by_cases st₁ : ∃ v : Fin 11, ∀ e, RoutedAt graph C j₁ e → v ∈ e
    · obtain ⟨K,hK⟩ := existsMinCover (graph.deleteEdges (↑(Ustar graph C)))
      obtain ⟨c,hc⟩ := st₀
      obtain ⟨d,hd⟩ := st₁
      have hcoverFive := twoStarCoverFive hW K hK.1 hc hd
      have hKtop : K.card ≤ T := hcover K hK
      exact hs (hm C j₀ j₁ hL hT hU hW hbudget hcover hlt hj h01 h10 hsep (by omega) h5
        ⟨c,hc⟩ ⟨d,hd⟩)
    · obtain ⟨v,hv⟩ := st₀
      obtain ⟨a,b,⟨B⟩⟩ := actualPairExists hL.1 hT hG hj h01 h10 hsep (.inr rfl) 0 (wide _ st₁)
      exact zeroClose (actualStarPairBudget hL.1 hT hG hcross jneq hj h01 h10 hsep hW hv B)
  · have w₀ := wide _ st₀
    obtain ⟨c,d,⟨A⟩⟩ := actualPairExists hL.1 hT hG hj h01 h10 hsep (.inl rfl) 0 w₀
    by_cases st₁ : ∃ v : Fin 11, ∀ e, RoutedAt graph C j₁ e → v ∈ e
    · obtain ⟨v,hv⟩ := st₁
      exact zeroClose (actualPairStarBudget hL.1 hT hG hcross jneq hj h01 h10 hsep hW A hv)
    · have w₁ := wide _ st₁
      obtain ⟨a,b,⟨B⟩⟩ := actualPairExists hL.1 hT hG hj h01 h10 hsep (.inr rfl) 0 w₁
      by_cases h6 : 6 ≤ (tops graph C).card
      · exact hs (closeFromCharge 1 h6
          (twoActualPairsBudget hL.1 hT hG hcross jneq hj h01 h10 hsep hW A B) hbudget)
      have eq5 : (tops graph C).card = 5 := by omega
      by_cases h3 : T = 3
      · obtain ⟨K,hK⟩ := existsMinCover (graph.deleteEdges (↑(Ustar graph C)))
        have hKtop : K.card ≤ T := hcover K hK
        let L : Finset (Fin 11) := {c,d}
        let M : Finset (Fin 11) := {a,b}
        have hits (x y : Fin 11) (he : s(x,y) ∈ Ustar graph C) :
            x ∈ L ∪ M ∨ y ∈ L ∪ M := by
          obtain ⟨i,hi,k,j,tag,on,reach,act⟩ := hW x y he
          have route : RoutedAt graph C j s(x,y) := ⟨x,y,rfl,i,hi,k,on,reach,act⟩
          rcases tag with rfl | rfl
          · have hc := A.covers x y route
            simp only [L,M,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
            tauto
          · have hc := B.covers x y route
            simp only [L,M,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
            tauto
        have cover := Profile2264.two_cover_bounds K L M (Ustar graph C) hK.1
          (Finset.card_pair A.distinct).le (Finset.card_pair B.distinct).le hits
        obtain ⟨_,_,dis,disK⟩ := cover.2 (by have := cover.1; omega)
        have mc : c ∈ L := by simp [L]
        have md : d ∈ L := by simp [L]
        have ma : a ∈ M := by simp [M]
        have mb : b ∈ M := by simp [M]
        have clear (x : Fin 11) (hx : x ∈ L ∪ M) : x ∉ K :=
          fun hk => Finset.disjoint_left.mp disK hk hx
        have inside (x y : Fin 11) (hx : x ∈ L ∪ M) (hy : y ∈ L ∪ M)
            (adj : graph.Adj x y) : s(x,y) ∈ Ustar graph C := by
          by_contra h
          exact (hK.1 (SimpleGraph.deleteEdges_adj.mpr ⟨adj,h⟩)).elim (clear x hx) (clear y hy)
        have hA := inside c d (Finset.mem_union_left _ mc) (Finset.mem_union_left _ md)
          (A.adjacent d A.connectorLeaf)
        have hB := inside a b (Finset.mem_union_right _ ma) (Finset.mem_union_right _ mb)
          (B.adjacent b B.connectorLeaf)
        have ne : s(c,d) ≠ s(a,b) := by
          intro equal
          rcases Sym2.eq_iff.mp equal with ⟨eq,_⟩|⟨eq,_⟩
          · exact Finset.disjoint_left.mp dis mc (eq.symm ▸ ma)
          · exact Finset.disjoint_left.mp dis mc (eq.symm ▸ mb)
        have fh : Disjoint ({s(c,d)} : Finset (Sym2 (Fin 11))) {s(a,b)} := by
          simpa using ne
        obtain ⟨E,F,ed,hu,fa,fb,er,fr⟩ := twoRoutePartitionWith hW _ _ fh
          (Finset.singleton_subset_iff.mpr hA) (Finset.singleton_subset_iff.mpr hB)
          (fun _ he => (Finset.mem_singleton.mp he).symm ▸ A.connector)
          (fun _ he => (Finset.mem_singleton.mp he).symm ▸ B.connector)
        exact zeroClose (actualPairAssignedExact hL.1 hT hG hcross jneq hj h01 h10 hsep A B E F hu ed
          er fr (fun _ => fa (Finset.mem_singleton_self _)) (fun _ => fb (Finset.mem_singleton_self _))
          0 0 (fun _ => by decide) (fun _ => by decide) (fun h _ => (h hA).elim))
      have atMostOne : Z ≤ 1 := by omega
      have ctr := ctrByJunkTotal (C := C) hsep
      have hzOr : (ctrByJunk graph C j₀).card = 0 ∨ (ctrByJunk graph C j₁).card = 0 := by
        change (ctrByJunk graph C j₀).card+(ctrByJunk graph C j₁).card ≤ Z at ctr
        omega
      by_cases conn : s(c,d) = s(a,b)
      · obtain ⟨K,hK⟩ := existsMinCover (graph.deleteEdges (↑(Ustar graph C)))
        have hKbig := sharedConnectorCoverFive hW K hK.1 A B conn
        have hKtop : K.card ≤ T := hcover K hK
        have ze : centreless graph C = ∅ := Finset.card_eq_zero.mp (show Z=0 by omega)
        have z (j : ℕ) : (ctrByJunk graph C j).card = 0 := by simp [ctrByJunk,ze]
        cases oa : A.ordinary
        · exact zeroClose (actualPairCollisionReserved hL.1 hT hG hcross jneq hj h01 h10 hsep hW A B oa (z _) conn)
        · cases ob : B.ordinary
          · have hj' : junk graph C = {j₁,j₀} := hj.trans (Finset.pair_comm _ _)
            exact zeroClose (actualPairCollisionReserved (G := graph) (C := C)
              hL.1 hT hG hcross jneq.symm hj' h10 h01
              (fun q hq h₁ h₀ => hsep q hq h₀ h₁) (hasRouteComm hW) B A ob (z _) conn.symm)
          · exact zeroClose (bothOrdinaryCommonBudget hL.1 hT hG hcross hstar Profile2264.seven_cover
              jneq hj h01 h10 hsep hW eq5 ze A B oa ob conn w₀ w₁)
      · exact zeroClose (actualPairDistinctExact hL.1 hT hG hcross jneq hj h01 h10 hsep hW A B hzOr conn)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def assignedStarLeaves (E : Finset (Sym2 (Fin n))) (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y => s(c,y) ∈ E
lemma assignedStarMem {E : Finset (Sym2 (Fin n))} {c y : Fin n} :
    y ∈ assignedStarLeaves E c ↔ s(c,y) ∈ E := by simp [assignedStarLeaves]
lemma starProductBudget (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁)
    (E : Finset (Sym2 (Fin n))) (hE : E ⊆ Ustar G C)
    (hr : ∀ e ∈ E, RoutedAt G C j e)
    (c : Fin n) (hstar : ∀ e ∈ E, c ∈ e) :
    E.card ≤ (pureForLeaves G C (assignedStarLeaves E c)).card +
      (centreRoutes G C j).card + (mixLabels G C j₀ j₁ j).card := by
  let X := assignedStarLeaves E c
  let R := centreGuardWires G C j
  let B := centreGuardUnion G C j
  let L := mixLabels G C j₀ j₁ j
  have Xedge (y : Fin n) (hy : y ∈ X) : s(c,y) ∈ Ustar G C :=
    hE (assignedStarMem.mp hy)
  have Xadj (y : Fin n) (hy : y ∈ X) : G.Adj c y :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Xedge y hy)).1
  have hX : E.card ≤ X.card := by
    apply (Finset.card_le_card (s := E) (t := X.image (fun y => s(c,y))) ?_).trans Finset.card_image_le
    intro e he
    obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp (hstar e he)
    exact Finset.mem_image.mpr ⟨y,assignedStarMem.mpr he,rfl⟩
  have Rcap := centreGuardWireCount (G := G) (C := C) j
  have hroute (y : Fin n) (hy : y ∈ X) :
      (c ∈ wmax G C j ∧ gateVal n C j (pairInput c y) = true ∧
        GuardOption G C j₀ j₁ j c y) ∨
      (y ∈ wmax G C j ∧ gateVal n C j (pairInput y c) = true ∧
        GuardOption G C j₀ j₁ j y c) := by
    have hm : s(c,y) ∈ E := assignedStarMem.mp hy
    obtain ⟨x,z,he,hw,hv,hO⟩ :=
      routedThroughGuard hAO hT hJ hsep hcross hj (hE hm) (hr _ hm)
    rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · subst x
      subst z
      exact .inl ⟨hw,hv,hO⟩
    · subst x
      subst z
      exact .inr ⟨hw,hv,hO⟩
  by_cases hc : c ∈ wmax G C j
  · by_cases he : E.Nonempty
    · have hjm : j ∈ junk G C := by simpa [hJ] using hj
      have lack : ∃ b : Fin 2, c ∉ side (n := n) C j b := by
        by_contra! hh
        exact G.irrefl (guardOverlapAdj hAO hT hJ h01 h10 hjm
          (Finset.mem_inter.mpr ⟨hh 0,hh 1⟩) hc)
      obtain ⟨b,hb⟩ := lack
      let w := opnd C j b
      have hdata := (junkData hjm).1
      have hlt := opndBound hAO hdata b
      have hx : X ⊆ orIn n C w := by
        intro y hy
        have hVal : gateVal n C j (pairInput c y) = true := by
          rcases hroute y hy with h | h
          · exact h.2.1
          · exact pairInputSwap y c ▸ h.2.1
        exact (termsHit (junkVal hAO hT hJ h01 h10 hjm) b hVal).resolve_left hb
      have hw : ∀ z ∈ ({w} : Finset ℕ), z < n+C.gates.length ∧
          ∀ k, OrReaches n C z k → (gateAt C k).op ≠ GateOp.and := by
        intro z hz
        rcases Finset.mem_singleton.mp hz with rfl
        exact ⟨by dsimp [w]; omega,pureJunkOperand hAO hT hJ h01 h10 hjm⟩
      have hp := selectiveForest hAO h4 hcross {w} (fun z hz => (hw z hz).1)
        (fun z hz => (hw z hz).2) c X X (Finset.Subset.rfl) Xadj
        (by simpa using hx) Xedge
      have sourceBudget : 1 ≤ (centreRoutes G C j).card + L.card := by
        obtain ⟨e,he⟩ := he
        obtain ⟨y,z,_,_,_,hO⟩ := routedThroughGuard hAO hT hJ hsep hcross hj (hE he) (hr _ he)
        rcases hO with h | ⟨x,hx,_,_⟩
        · obtain ⟨w,hw,_⟩ := Finset.mem_biUnion.mp h
          obtain ⟨a,ha,_⟩ := Finset.mem_image.mp hw
          have ht := Finset.card_pos.mpr ⟨a,ha⟩
          omega
        · have ht : 0 < L.card := Finset.card_pos.mpr ⟨x,hx⟩
          omega
      change E.card ≤ (pureForLeaves G C X).card + (centreRoutes G C j).card + L.card
      simp only [Finset.card_singleton] at hp
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
      exact Nat.zero_le _
  · let Y := X ∩ B
    let Z := X \ B
    have hY : Y ⊆ R.biUnion (orIn n C) := Finset.inter_subset_right
    have hp := selectiveForest hAO h4 hcross R
      (fun w hw => (centreGuardWirePure hAO hT hJ hsep hj hw).1)
      (fun w hw => (centreGuardWirePure hAO hT hJ hsep hj hw).2)
      c X Y Finset.inter_subset_left Xadj hY Xedge
    have hx (y : Fin n) (hy : y ∈ Z) : ∃ x ∈ L, G.Adj x y ∧ x ≠ c := by
      obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
      rcases hroute y hy with h | h
      · exact (hc h.1).elim
      · exact h.2.2.resolve_left hn
    have hm := (exteriorMixCount h4 L Z c
      (fun y hy => Xadj y (Finset.mem_sdiff.mp hy).1) hx).trans (Finset.card_filter_le _ _)
    have hs := Finset.card_sdiff_add_card_eq_card (show Y ⊆ X from Finset.inter_subset_left)
    have he : X \ Y = Z := by ext y; simp [Y,Z]
    rw [he] at hs
    change R.card ≤ (centreRoutes G C j).card at Rcap
    change E.card ≤ (pureForLeaves G C X).card + (centreRoutes G C j).card + L.card
    change Z.card ≤ L.card at hm
    omega
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {α : Type} [DecidableEq α]
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def rawEmbedding (n : ℕ) : Fin n ↪ Fin n ⊕ Bool :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
lemma pureAtoms {j₀ j₁ w : ℕ}
    (hj₀ : (gateAt C j₀).op = GateOp.and) (hj₁ : (gateAt C j₁).op = GateOp.and)
    (hp : ∀ j, OrReaches n C w j → (gateAt C j).op ≠ GateOp.and) :
    atoms C n j₀ j₁ w = (orIn n C w).map (rawEmbedding n) := by
  ext a
  cases a with
  | inl x =>
    rw [memAtoms, Finset.mem_map]
    change (Relation.ReflTransGen (OrStep n C) w x.val ∧ x.val < _) ↔
      ∃ a ∈ orIn n C w, (Sum.inl a : Fin n ⊕ Bool) = Sum.inl x
    constructor
    · exact fun h => ⟨x, reach_mem_orIn x h.1, rfl⟩
    · rintro ⟨a,ha,he⟩
      cases Sum.inl.inj he
      exact ⟨mem_orIn_reach x ha, by omega⟩
  | inr b =>
    rw [memAtoms, Finset.mem_map]
    change (_ ∧ _) ↔ ∃ a ∈ orIn n C w, (Sum.inl a : Fin n ⊕ Bool) = Sum.inr b
    simp only [Sum.inl_ne_inr, and_false, exists_false, iff_false]
    cases b <;> simp only [atomWire]
    · rintro ⟨hr, hlt⟩
      exact hp j₀ (reach_orReaches hr j₀ rfl (by omega)) hj₀
    · rintro ⟨hr, hlt⟩
      exact hp j₁ (reach_orReaches hr j₁ rfl (by omega)) hj₁
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def IsRawAtoms (n : ℕ) (S : Finset (Fin n ⊕ Bool)) : Prop :=
  Sum.inr false ∉ S ∧ Sum.inr true ∉ S
instance (S : Finset (Fin n ⊕ Bool)) : Decidable (IsRawAtoms n S) := by
  unfold IsRawAtoms
  infer_instance
noncomputable def rawOrs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j₀ j₁ : ℕ) : Finset ℕ :=
  (orN G C).filter fun k => IsRawAtoms n (atoms C n j₀ j₁ (n+k))
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable def rawCone (C : Circuit) (n w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (w+1)).filter fun u => Relation.ReflTransGen (OrStep n C) w u
lemma rawConeMem {w u : ℕ} :
    u ∈ rawCone C n w ↔ Relation.ReflTransGen (OrStep n C) w u := by
  classical
  simp only [rawCone, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨by have := orStep_le h; omega,h⟩⟩
noncomputable def rawConeGates (C : Circuit) (n w : ℕ) : Finset ℕ :=
  (rawCone C n w).filter fun u => n ≤ u
noncomputable def rawConeLeaves (C : Circuit) (n w : ℕ) : Finset ℕ :=
  rawCone C n w \ rawConeGates C n w
lemma rawLeaves (C : Circuit) (n w : ℕ) :
    rawConeLeaves C n w = (orIn n C w).map ⟨Fin.val, Fin.val_injective⟩ := by
  ext u
  rw [Finset.mem_map]
  constructor
  · rintro h
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp h
    have hu : u < n := by
      by_contra hn'
      exact hn (Finset.mem_filter.mpr ⟨hm,by omega⟩)
    exact ⟨⟨u,hu⟩,reach_mem_orIn ⟨u,hu⟩ (rawConeMem.mp hm),rfl⟩
  · rintro ⟨v,hv,hval⟩
    change v.val = u at hval
    subst u
    refine Finset.mem_sdiff.mpr ⟨rawConeMem.mpr (mem_orIn_reach v hv),?_⟩
    exact fun h => Nat.not_le_of_lt v.isLt (Finset.mem_filter.mp h).2
lemma rawConeSize (hAO : IsAO2 n C) (w : ℕ) :
    (orIn n C w).card ≤ (rawConeGates C n w).card + 1 := by
  let I := rawConeGates C n w
  let S := rawCone C n w
  let child (u : ℕ) := ({opnd C (u-n) 0, opnd C (u-n) 1} : Finset ℕ)
  have hchild : S \ {w} ⊆ I.biUnion child := by
    intro u hu
    obtain ⟨hus,hn⟩ := Finset.mem_sdiff.mp hu
    rcases Relation.ReflTransGen.cases_tail (rawConeMem.mp hus) with h | ⟨v,hreach,hs⟩
    · exact (hn (Finset.mem_singleton.mpr h)).elim
    · obtain ⟨k,hl,heq,_,hi,_⟩ := hs
      have hv : v-n = k := by omega
      refine Finset.mem_biUnion.mpr ⟨v,Finset.mem_filter.mpr ⟨rawConeMem.mpr hreach,by omega⟩,?_⟩
      change u ∈ ({opnd C (v-n) 0,opnd C (v-n) 1} : Finset ℕ)
      rw [hv]
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hl hi
      rw [hb]
      fin_cases b <;> simp
  have hb : (I.biUnion child).card ≤ 2*I.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      (∑ u ∈ I, (child u).card) ≤ ∑ _u ∈ I, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro u _
        exact (Finset.card_insert_le _ _).trans (by simp)
      _ = 2*I.card := by simp [Nat.mul_comm]
  have hw : ({w} : Finset ℕ) ⊆ S :=
    Finset.singleton_subset_iff.mpr (rawConeMem.mpr .refl)
  have h1 := Finset.card_sdiff_add_card_eq_card hw
  simp only [Finset.card_singleton] at h1
  have h2 : (rawConeLeaves C n w).card + I.card = S.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have h3 : (rawConeLeaves C n w).card = (orIn n C w).card := by
    rw [rawLeaves,Finset.card_map]
  have h4 := (Finset.card_le_card hchild).trans hb
  change (orIn n C w).card ≤ I.card + 1
  omega
noncomputable def rawConeIndices (C : Circuit) (n w : ℕ) : Finset ℕ :=
  (rawConeGates C n w).image fun u => u-n
lemma rawConeIndicesCard (C : Circuit) (n w : ℕ) :
    (rawConeIndices C n w).card = (rawConeGates C n w).card := by
  have h : Set.InjOn (fun (u : ℕ) => u-n) (↑(rawConeGates C n w) : Set ℕ) := by
    intro x hx y hy he
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change x-n = y-n at he
    omega
  exact Finset.card_image_of_injOn h
lemma rawConeIndicesSub (hAO : IsAO2 n C) {j₀ j₁ w : ℕ}
    (hJ : junk G C = {j₀,j₁}) (hw : w < n+C.gates.length)
    (hp : ∀ j, OrReaches n C w j → (gateAt C j).op ≠ GateOp.and) :
    rawConeIndices C n w ⊆ rawOrs G C j₀ j₁ := by
  intro k hk
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hreach,hn⟩ := Finset.mem_filter.mp hu
  have reach := rawConeMem.mp hreach
  have hlu := orStep_le reach
  let m := u-n
  have hmu : u = n+m := by dsimp [m]; omega
  have hml : m < C.gates.length := by omega
  have hr := reach_orReaches reach m hmu hml
  have pm (k : ℕ) (h : OrReaches n C (n+m) k) : (gateAt C k).op ≠ GateOp.and :=
    hp k (reachTrans hr h)
  have hOp := (hAO.1 _ (gateAt_mem hml)).resolve_left (hp m hr)
  have raw := pureOrNonempty hAO (w := n+m) (by omega) pm
  have hm : m ∈ orN G C := orNOfRaw hml hOp raw
  have hj₀ : j₀ ∈ junk G C := by simp [hJ]
  have hj₁ : j₁ ∈ junk G C := by simp [hJ]
  have HA := pureAtoms (junkData hj₀).2.1 (junkData hj₁).2.1 pm
  refine Finset.mem_filter.mpr ⟨hm,?_⟩
  rw [HA]
  simp only [IsRawAtoms, Finset.mem_map]
  constructor <;> rintro ⟨_,_,h⟩ <;> cases h
lemma rawConeBound (hAO : IsAO2 n C) {w : ℕ} :
    (orIn n C w).card ≤ (rawConeIndices C n w).card + 1 := by
  rw [rawConeIndicesCard]
  exact rawConeSize hAO w
lemma rawConeIndicesReach {w i : ℕ} (hi : i ∈ rawConeIndices C n w) :
    Relation.ReflTransGen (OrStep n C) w (n+i) := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hu
  have he : n+(u-n) = u := by omega
  rw [he]
  exact rawConeMem.mp hs
lemma wideArmIndex {w : ℕ} (hw : 1 < (orIn n C w).card) :
    n ≤ w ∧ w-n ∈ rawConeIndices C n w := by
  have hn : n ≤ w := by
    by_contra! h
    rw [orInRaw h, Finset.card_singleton] at hw
    omega
  exact ⟨hn,Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨rawConeMem.mpr .refl,hn⟩,rfl⟩⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma assignedStarCard2264 {E : Finset (Sym2 (Fin n))} {c : Fin n}
    (h : ∀ e ∈ E, c ∈ e) : (assignedStarLeaves E c).card = E.card := by
  let X := assignedStarLeaves E c
  have hE : X.image (fun y => s(c,y)) = E := by
    ext e
    constructor
    · intro he
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      exact assignedStarMem.mp hy
    · intro he
      obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp (h e he)
      exact Finset.mem_image_of_mem _ (assignedStarMem.mpr he)
  have inj : Set.InjOn (fun y : Fin n => s(c,y)) ↑X := by
    intro x _ y _ e
    rcases Sym2.eq_iff.mp e with ⟨_,e⟩ | ⟨e,e'⟩
    · exact e
    · exact e'.trans e
  change X.card = E.card
  rw [←hE,Finset.card_image_of_injOn inj]
lemma positiveRouteCharge2264 (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) (tag : j = j₀ ∨ j = j₁)
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) (hr : RoutedAt G C j e) :
    1 ≤ (centreRoutes G C j).card + (mixLabels G C j₀ j₁ j).card := by
  obtain ⟨y,z,_,_,_,options⟩ := routedThroughGuard hAO hT hJ sep cross tag he hr
  rcases options with hg | ⟨x,hx,_,_⟩
  · obtain ⟨w,hw,_⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨a,ha,_⟩ := Finset.mem_image.mp hw
    have hc := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  · have hm := Finset.card_pos.mpr ⟨x,hx⟩
    omega
lemma starLeafRoute2264 (hAO : IsAO2 n C) (hT : TopForm G C)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) (tag : j = j₀ ∨ j = j₁)
    {c y : Fin n} (he : s(c,y) ∈ Ustar G C) (hr : RoutedAt G C j s(c,y)) :
    gateVal n C j (pairInput c y) = true ∧
      ((c ∈ wmax G C j ∧ GuardOption G C j₀ j₁ j c y) ∨
        (y ∈ wmax G C j ∧ GuardOption G C j₀ j₁ j y c)) := by
  obtain ⟨x,z,e,hw,hv,hO⟩ := routedThroughGuard hAO hT hJ sep cross tag he hr
  rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hv,.inl ⟨hw,hO⟩⟩
  · exact ⟨pairInputSwap y c ▸ hv,.inr ⟨hw,hO⟩⟩
lemma starSingleRoot2264 (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) (tag : j = j₀ ∨ j = j₁)
    {E : Finset (Sym2 (Fin n))} (sub : E ⊆ Ustar G C) (route : ∀ e ∈ E, RoutedAt G C j e)
    (c : Fin n) (wide : 1 < (assignedStarLeaves E c).card)
    (charge : (centreRoutes G C j).card + (mixLabels G C j₀ j₁ j).card ≤ 1) :
    ∃ w < n+C.gates.length, (∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and) ∧
      assignedStarLeaves E c ⊆ orIn n C w ∧
      ((c ∈ wmax G C j ∧ ∃ b : Fin 2, w = opnd C j b ∧ c ∉ side (n := n) C j b) ∨
        (c ∉ wmax G C j ∧ w ∈ centreGuardWires G C j)) := by
  let X := assignedStarLeaves E c
  let L := mixLabels G C j₀ j₁ j
  have jm : j ∈ junk G C := by simpa [hJ] using tag
  have part (y : Fin n) (hy : y ∈ X) :=
    starLeafRoute2264 hAO hT hJ sep cross tag (sub (assignedStarMem.mp hy)) (route _ (assignedStarMem.mp hy))
  by_cases cw : c ∈ wmax G C j
  · have lack : ∃ b : Fin 2, c ∉ side (n := n) C j b := by
      by_contra! h
      exact G.irrefl (guardOverlapAdj hAO hT hJ h01 h10 jm (Finset.mem_inter.mpr ⟨h 0,h 1⟩) cw)
    obtain ⟨b,hb⟩ := lack
    have bl := opndBound hAO (junkData jm).1 b
    refine ⟨opnd C j b,by have := (junkData jm).1; omega,
      pureJunkOperand hAO hT hJ h01 h10 jm,?_,.inl ⟨cw,b,rfl,hb⟩⟩
    intro y hy
    exact (termsHit (junkVal hAO hT hJ h01 h10 jm) b (part y hy).1).resolve_left hb
  · have other (y : Fin n) (hy : y ∈ X) : GuardOption G C j₀ j₁ j y c :=
      ((part y hy).2.resolve_left (fun hw => cw hw.1)).2
    by_cases hR : (centreGuardWires G C j).Nonempty
    · obtain ⟨w,hw⟩ := hR
      have hc := centreGuardWireCount (G := G) (C := C) j
      have count := Finset.card_pos.mpr ⟨w,hw⟩
      have hSingle : centreGuardWires G C j = {w} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hw,fun _ hv => Finset.card_le_one_iff.mp (by omega) hv hw⟩
      have hL : L = ∅ := Finset.card_eq_zero.mp (by change (mixLabels G C j₀ j₁ j).card = 0; omega)
      obtain ⟨lb,hp⟩ := centreGuardWirePure hAO hT hJ sep tag hw
      refine ⟨w,lb,hp,?_,.inr ⟨cw,hw⟩⟩
      intro y hy
      have hit := (other y hy).resolve_right (by
        rintro ⟨x,hx,_,_⟩
        change x ∈ L at hx
        rw [hL] at hx
        exact Finset.notMem_empty _ hx)
      simpa [centreGuardUnion,hSingle] using hit
    · have hR' := Finset.not_nonempty_iff_eq_empty.mp hR
      have limited : X.card ≤ L.card := (exteriorMixCount h4 L X c
        (fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (sub (assignedStarMem.mp hy))).1)
        (fun y hy => (other y hy).resolve_left (by simp [centreGuardUnion,hR']))).trans (Finset.card_filter_le _ _)
      change (assignedStarLeaves E c).card ≤ (mixLabels G C j₀ j₁ j).card at limited
      omega
lemma commonRawStarRootImpossible2264 (hL : IsLeastAO G C) (hT : TopForm G C)
    (h4 : NoFourCycle G) {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (tag : j = j₀ ∨ j = j₁)
    {w : ℕ} (hw : rawConeIndices C n w = rawOrs G C j₀ j₁)
    {c d : Fin n} (ne : c ≠ d)
    {X Y : Finset (Fin n)} (hx : X ⊆ orIn n C w) (hy : Y ⊆ orIn n C w)
    (hX : 1 < X.card) (hY : 1 < Y.card)
    (yadj : ∀ y ∈ Y, G.Adj d y)
    (val : ∀ x ∈ X, gateVal n C j (pairInput c x) = true)
    (mode : (c ∈ wmax G C j ∧ ∃ b : Fin 2, w = opnd C j b ∧ c ∉ side (n := n) C j b) ∨
      (c ∉ wmax G C j ∧ w ∈ centreGuardWires G C j)) : False := by
  let S := orIn n C w
  have jm : j ∈ junk G C := by simpa [hJ] using tag
  have ht := junkVal hL.1 hT hJ h01 h10 jm
  have inside (b : Fin 2) (hb : n ≤ opnd C j b) : side (n := n) C j b ⊆ S := by
    let u := opnd C j b
    have bl := opndBound hL.1 (junkData jm).1 b
    have jl := (junkData jm).1
    have pure : ∀ k, OrReaches n C u k → (gateAt C k).op ≠ GateOp.and :=
      pureJunkOperand hL.1 hT hJ h01 h10 jm
    have sub := rawConeIndicesSub hL.1 hJ (w := u) (by dsimp [u]; omega) pure
    have hu : u-n ∈ rawConeIndices C n u :=
      Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨rawConeMem.mpr .refl,hb⟩,rfl⟩
    have mem : u-n ∈ rawConeIndices C n w := hw.symm ▸ sub hu
    have eq : n+(u-n)=u := by dsimp [u]; omega
    have reach := rawConeIndicesReach mem
    rw [eq] at reach
    exact orInTrans reach
  have pick := Finset.card_pos.mp (by omega : 0 < X.card)
  obtain ⟨x,hxX⟩ := pick
  rcases mode with ⟨cw,b,he,_⟩ | ⟨cn,wg⟩
  · have notSub : ¬ side (n := n) C j (1-b) ⊆ S := by
      simp only [S,he]
      change ¬ side (n := n) C j (1-b) ⊆ side C j b
      simpa only [oppositeOpposite] using junkIncomparableSides hL hT hJ h01 h10 jm (1-b)
    have raw : opnd C j (1-b) < n := by
      by_contra! h
      exact notSub (inside (1-b) h)
    have eq : side (n := n) C j (1-b) = {⟨opnd C j (1-b),raw⟩} := orInRaw raw
    have xout : x ∉ side (n := n) C j (1-b) := by
      intro h
      apply notSub
      rw [eq] at h ⊢
      rw [←Finset.mem_singleton.mp h]
      exact Finset.singleton_subset_iff.mpr (hx hxX)
    have ca := (termsHit ht (1-b) (val x hxX)).resolve_right xout
    have all := commonNeighborArm (b := 1-b) ((junkWmax hL.1 hT hJ h01 h10 jm c).mp cw) ca
    rw [oppositeOpposite] at all
    have subY : Y ⊆ side (n := n) C j b := by change Y ⊆ orIn n C (opnd C j b); rwa [←he]
    exact ne (uniqueCommonCenter h4 hY (fun y h => all y (subY h)) yadj)
  · have safe : S ⊆ wmax G C j := fun y hy =>
      centreGuardUnionSafe hL.1 hT hJ sep tag (Finset.mem_biUnion.mpr ⟨w,wg,hy⟩)
    have cout : c ∉ S := fun h => cn (safe h)
    have cA : ∃ b : Fin 2, c ∈ side (n := n) C j b := by
      by_contra! hn
      have xi := exteriorTail ht (val x hxX) hn
      exact G.irrefl (wmaxOverlap ((junkWmax hL.1 hT hJ h01 h10 jm x).mp (safe (hx hxX))) x xi)
    obtain ⟨b,cb⟩ := cA
    have raw : opnd C j b < n := by
      by_contra! h
      exact cout (inside b h cb)
    have eq : side (n := n) C j b = {c} := by
      have e : side (n := n) C j b = {⟨opnd C j b,raw⟩} := orInRaw raw
      have cc := Finset.mem_singleton.mp (e ▸ cb)
      rw [e,cc]
    have cOutOther : c ∉ side (n := n) C j (1-b) :=
      fun h => junkIncomparableSides hL hT hJ h01 h10 jm b (by rw [eq]; exact Finset.singleton_subset_iff.mpr h)
    have XOther : X ⊆ side (n := n) C j (1-b) :=
      fun _ hx => (termsHit ht (1-b) (val _ hx)).resolve_left cOutOther
    have bigOther : 1 < (side (n := n) C j (1-b)).card := hX.trans_le (Finset.card_le_card XOther)
    have nle : n ≤ opnd C j (1-b) := (wideArmIndex bigOther).1
    have OtherAdj (y : Fin n) (yy : y ∈ side (n := n) C j (1-b)) : G.Adj c y := by
      have hW := (junkWmax hL.1 hT hJ h01 h10 jm y).mp (safe (inside (1-b) nle yy))
      have h := commonNeighborArm (b := 1-b) hW yy
      rw [oppositeOpposite] at h
      exact (h c cb).symm
    obtain ⟨_,_,z,hz,hn⟩ := junkData jm
    obtain ⟨⟨a,ha,za⟩,⟨a',ha',za'⟩⟩ := (ht z).mp hz
    have hEdge : G.Adj a a' := by
      fin_cases b
      · have ac : a = c := Finset.mem_singleton.mp (eq ▸ ha)
        exact ac ▸ OtherAdj a' ha'
      · have ac : a' = c := Finset.mem_singleton.mp (eq ▸ ha')
        exact ac ▸ (OtherAdj a ha).symm
    have hTrue : graphFun G ∅ z = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨a,a',hEdge,za,za'⟩
    exact Bool.false_ne_true (hn.symm.trans hTrue)
lemma chargedRootAtLeaves2264 (hAO : IsAO2 n C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {w : ℕ} (hw : w < n+C.gates.length)
    (hPure : ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
    {c : Fin n} {X : Finset (Fin n)} (hX : 1 < X.card)
    (hSub : X ⊆ orIn n C w) (adj : ∀ x ∈ X, G.Adj c x)
    (missing : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ k ∈ NoPureMix G C, w = n+k := by
  have wide := hX.trans_le (Finset.card_le_card hSub)
  refine pureSupportCharge hAO hw hPure cross wide ?_
  rintro ⟨d,hd⟩
  have ec := uniqueCommonCenter h4 hX adj (fun x hx => (hd x (hSub hx)).1)
  subst d
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  exact (hd x (hSub hx)).2 (missing x hx)
lemma bothStarsSeven2264 (hne : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (h4 : NoFourCycle G) {j₀ j₁ : ℕ} (hij : j₀ < j₁)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C)
    (ledger : 17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card)
    (degree : ∀ v : Fin n, (G.edgeFinset.filter (fun e => v ∈ e)).card ≤ 4)
    (ht : 7 ≤ (tops G C).card)
    {E F : Finset (Sym2 (Fin n))} (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (er : ∀ e ∈ E, RoutedAt G C j₀ e) (fr : ∀ e ∈ F, RoutedAt G C j₁ e)
    {c d : Fin n} (ne : c ≠ d) (eStar : ∀ e ∈ E, c ∈ e) (fStar : ∀ e ∈ F, d ∈ e) :
    22 ≤ C.size := by
  by_contra! big
  have size : C.size ≤ 21 := by omega
  let P := NoPureMix G C
  let X := assignedStarLeaves E c
  let Y := assignedStarLeaves F d
  let r (j : ℕ) := (centreRoutes G C j).card + (mixLabels G C j₀ j₁ j).card
  have eSub : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have fSub : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  have eBound : E.card ≤ 4 := (Finset.card_le_card (show E ⊆ G.edgeFinset.filter (fun e => c ∈ e) from
    fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (eSub he)).1,eStar e he⟩)).trans (degree c)
  have fBound : F.card ≤ 4 := (Finset.card_le_card (show F ⊆ G.edgeFinset.filter (fun e => d ∈ e) from
    fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (fSub he)).1,fStar e he⟩)).trans (degree d)
  have R := centreRoutesCard hL.1 sep
  have M := mixLabelsCard (G := G) (C := C) hij.ne
  have led := numericShortBudget size ledger (centreRoutes G C j₀).card (centreRoutes G C j₁).card
    (mixLabels G C j₀ j₁ j₀).card (mixLabels G C j₀ j₁ j₁).card R M
  have coverC := Finset.card_union_of_disjoint dis
  rw [split] at coverC
  have total : (tops G C).card + r j₀ + r j₁ + P.card ≤ E.card+F.card+4 := by
    change (tops G C).card + r j₀ + r j₁ + ((orN G C \ lam G C) \ mixing G C).card ≤ _
    dsimp only [r]
    omega
  have pay (Z : Finset (Fin n)) : (pureForLeaves G C Z).card ≤ P.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have eCost := starProductBudget hL.1 hT h4 hJ h01 h10 sep cross (.inl rfl) E eSub er c eStar
  have fCost := starProductBudget hL.1 hT h4 hJ h01 h10 sep cross (.inr rfl) F fSub fr d fStar
  rw [Nat.add_assoc] at eCost fCost
  change E.card ≤ (pureForLeaves G C X).card+r j₀ at eCost
  change F.card ≤ (pureForLeaves G C Y).card+r j₁ at fCost
  have eP : E.card ≤ P.card+r j₀ := by have h := pay X; omega
  have fP : F.card ≤ P.card+r j₁ := by have h := pay Y; omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  obtain ⟨f,hf⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  have re : 1 ≤ r j₀ := positiveRouteCharge2264 hL.1 hT hJ sep cross (.inl rfl) (eSub he) (er e he)
  have rf : 1 ≤ r j₁ := positiveRouteCharge2264 hL.1 hT hJ sep cross (.inr rfl) (fSub hf) (fr f hf)
  have ec : E.card = 4 := by omega
  have fc : F.card = 4 := by omega
  have payC : P.card = 3 := by omega
  have eqX : X.card = 4 := (assignedStarCard2264 eStar).trans ec
  have eqY : Y.card = 4 := (assignedStarCard2264 fStar).trans fc
  have eU : ∀ x ∈ X, s(c,x) ∈ Ustar G C := fun _ hx => eSub (assignedStarMem.mp hx)
  have fU : ∀ x ∈ Y, s(d,x) ∈ Ustar G C := fun _ hx => fSub (assignedStarMem.mp hx)
  have eAdj (x : Fin n) (hx : x ∈ X) : G.Adj c x := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (eU x hx)).1
  have fAdj (x : Fin n) (hx : x ∈ Y) : G.Adj d x := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (fU x hx)).1
  have x1 : 1 < X.card := by omega
  have y1 : 1 < Y.card := by omega
  obtain ⟨a,al,ap,ac,aMode⟩ := starSingleRoot2264 hL.1 hT h4 hJ h01 h10 sep cross (.inl rfl)
    eSub er c x1 (show r j₀ ≤ 1 by omega)
  obtain ⟨b,bl,bp,bc,_⟩ := starSingleRoot2264 hL.1 hT h4 hJ h01 h10 sep cross (.inr rfl)
    fSub fr d y1 (show r j₁ ≤ 1 by omega)
  have trace (Z : Finset (Fin n)) (z : Fin n) (w : ℕ)
      (wl : w < n+C.gates.length) (pure : ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and)
      (cap : Z.card = 4) (cov : Z ⊆ orIn n C w)
      (adj : ∀ x ∈ Z, G.Adj z x) (hU : ∀ x ∈ Z, s(z,x) ∈ Ustar G C) :
      ∀ k ∈ P, Relation.ReflTransGen (OrStep n C) w (n+k) := by
    obtain ⟨Q,hQ,hc,hreach⟩ := selectiveForestWithPool hL.1 h4 cross {w}
      (by simpa using wl) (by simpa using pure) z Z Z Finset.Subset.rfl adj (by simpa using cov) hU
    have Qsub : Q ⊆ P := hQ.trans (Finset.filter_subset _ _)
    rw [Finset.card_singleton] at hc
    have same : Q = P := Finset.eq_of_subset_of_card_le Qsub (by omega)
    intro k hk
    obtain ⟨v,hv,reach⟩ := hreach k (same.symm ▸ hk)
    rwa [Finset.mem_singleton.mp hv] at reach
  obtain ⟨i,hi,aeq⟩ := chargedRootAtLeaves2264 hL.1 h4 cross al ap x1 ac eAdj eU
  obtain ⟨k,hk,beq⟩ := chargedRootAtLeaves2264 hL.1 h4 cross bl bp y1 bc fAdj fU
  have ab := orStep_le (trace X c a al ap eqX ac eAdj eU k hk)
  have ba := orStep_le (trace Y d b bl bp eqY bc fAdj fU i hi)
  rw [←beq] at ab
  rw [←aeq] at ba
  have same : a = b := Nat.le_antisymm ba ab
  have bc : Y ⊆ orIn n C a := same.symm ▸ bc
  have inter : (X ∩ Y).card ≤ 1 := by
    by_contra! k
    exact ne (uniqueCommonCenter h4 k (fun x hx => eAdj x (Finset.mem_inter.mp hx).1)
      (fun x hx => fAdj x (Finset.mem_inter.mp hx).2))
  have hSum := Finset.card_union_add_card_inter X Y
  have wide : (X ∪ Y).card ≤ (orIn n C a).card := Finset.card_le_card (Finset.union_subset ac bc)
  have N := twoJunkSize hne hL hT hij hJ
  have pureCap : (rawOrs G C j₀ j₁).card ≤ 6 := by
    have rr := Finset.card_le_card (show rawOrs G C j₀ j₁ ⊆ orN G C from Finset.filter_subset _ _)
    omega
  have wc := rawConeBound hL.1 (w := a)
  have full : rawConeIndices C n a = rawOrs G C j₀ j₁ :=
    Finset.eq_of_subset_of_card_le (rawConeIndicesSub hL.1 hJ al ap) (by omega)
  exact commonRawStarRootImpossible2264 hL hT h4 hJ h01 h10 sep (.inl rfl) full ne ac bc x1 y1 fAdj
    (fun x hx => (starLeafRoute2264 hL.1 hT hJ sep cross (.inl rfl) (eU x hx) (er _ (assignedStarMem.mp hx))).1) aMode
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem unguardedStarKeys2264 (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) (tag : j = j₀ ∨ j = j₁)
    {E : Finset (Sym2 (Fin n))} (sub : E ⊆ Ustar G C) (route : ∀ e ∈ E, RoutedAt G C j e)
    {c : Fin n} (star : ∀ e ∈ E, c ∈ e) (noGuard : c ∉ wmax G C j)
    (zero : (centreRoutes G C j).card = 0) :
    E.card ≤ (mixLabels G C j₀ j₁ j).card := by
  have R : centreGuardWires G C j = ∅ := by
    apply Finset.card_eq_zero.mp
    have cap := centreGuardWireCount (G := G) (C := C) j
    omega
  have budget := fixedTailRoutesBudget hAO h4 (j₀ := j₀) (j₁ := j₁) (j := j) sub c (by
    intro e he
    obtain ⟨y,eEq⟩ := Sym2.mem_iff_exists.mp (star e he)
    have h := (starLeafRoute2264 hAO hT hJ sep cross tag (eEq ▸ sub he) (eEq ▸ route e he)).2
    exact ⟨y,eEq.trans Sym2.eq_swap,((h.resolve_left (fun h => noGuard h.1))).2⟩)
  simpa [R,zero] using budget
theorem oneZeroCentrelessSix2264 (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ j : ℕ} (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) (tag : j = j₀ ∨ j = j₁)
    {E F : Finset (Sym2 (Fin n))} (esub : E ⊆ Ustar G C)
    (route : ∀ e ∈ E, RoutedAt G C j e)
    {c d : Fin n} (ne : c ≠ d) (star : ∀ e ∈ E, c ∈ e)
    (degree : ∀ v : Fin n, (G.edgeFinset.filter (fun e => v ∈ e)).card ≤ 4)
    (zero : (centreRoutes G C j).card = 0)
    (m : ℕ) (hm : 1 ≤ m)
    (fBound : F.card ≤ 4)
    (fBudget : F.card ≤ (pureForLeaves G C (assignedStarLeaves F d)).card + m)
    (fAdj : ∀ y ∈ assignedStarLeaves F d, G.Adj d y)
    (total : 2 + (NoPureMix G C).card + (mixLabels G C j₀ j₁ j).card + m ≤ E.card+F.card) :
    False := by
  classical
  let P := NoPureMix G C
  let Q := pureForLeaves G C (assignedStarLeaves F d)
  let X := assignedStarLeaves E c
  let L := (mixLabels G C j₀ j₁ j).card
  let I := G.edgeFinset.filter (fun e => c ∈ e)
  have Ih : E ⊆ I := fun _ he => Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (esub he)).1,star _ he⟩
  have eBound : E.card ≤ 4 := (Finset.card_le_card Ih).trans (degree c)
  have qsub : Q ⊆ P := Finset.filter_subset _ _
  have qcard := Finset.card_le_card qsub
  have xCard : X.card = E.card := assignedStarCard2264 star
  change F.card ≤ Q.card + m at fBudget
  change 2+P.card+L+m ≤ E.card+F.card at total
  have positive : 1 ≤ L := by
    obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    have p := positiveRouteCharge2264 hAO hT hJ sep cross tag (esub he) (route e he)
    change 1 ≤ (centreRoutes G C j).card + L at p
    omega
  have cw : c ∈ wmax G C j := by
    by_contra! no
    have ub : E.card ≤ L := unguardedStarKeys2264 hAO hT h4 hJ sep cross tag esub route star no zero
    omega
  have hmem : j ∈ junk G C := by simpa [hJ] using tag
  have eU (y : Fin n) (hy : y ∈ X) : s(c,y) ∈ Ustar G C := esub (assignedStarMem.mp hy)
  have eAdj (y : Fin n) (hy : y ∈ X) : G.Adj c y :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (eU y hy)).1
  have chooseArm (i : Fin 2) (lack : c ∉ side (n := n) C j i) :
      ∃ W ⊆ pureForLeaves G C X, E.card ≤ W.card+L ∧
        ∀ a ∈ W, Relation.ReflTransGen (OrStep n C) (opnd C j i) (n+a) := by
    let w := opnd C j i
    have p := opndBound hAO (junkData hmem).1 i
    have cap : w < n+C.gates.length := p.trans (Nat.add_lt_add_left (junkData hmem).1 _)
    have pr := pureJunkOperand hAO hT hJ h01 h10 hmem (b := i)
    have sub : X ⊆ orIn n C w := by
      intro x hx
      have r := (starLeafRoute2264 hAO hT hJ sep cross tag (eU x hx)
        (route _ (assignedStarMem.mp hx))).1
      exact (termsHit (junkVal hAO hT hJ h01 h10 hmem) i r).resolve_left lack
    obtain ⟨W,hs,hcnt,hreach⟩ := selectiveForestWithPool hAO h4 cross {w}
      (by simpa using cap) (by simpa using pr) c X X (by rfl) eAdj (by simpa using sub) eU
    have capN : E.card ≤ W.card+L := by simp only [Finset.card_singleton] at hcnt; omega
    refine ⟨W,hs,capN,fun a ha => ?_⟩
    obtain ⟨v,hv,reach⟩ := hreach a ha
    rwa [Finset.mem_singleton.mp hv] at reach
  have share (W : Finset ℕ) (hW : W ⊆ pureForLeaves G C X) (cap : E.card ≤ W.card+L) :
      2 ≤ (W ∩ Q).card := by
    have wsub : W ⊆ P := hW.trans (Finset.filter_subset _ _)
    have wc := Finset.card_le_card (Finset.union_subset wsub qsub)
    have wi := Finset.card_union_add_card_inter W Q
    omega
  have noShare (a : ℕ) (hq : a ∈ Q) (adj : ∀ x ∈ orIn n C (n+a), G.Adj c x) : False := by
    have big : 1 < (orIn n C (n+a) ∩ assignedStarLeaves F d).card := (Finset.mem_filter.mp hq).2
    exact ne (uniqueCommonCenter h4 big
      (fun x hx => adj x (Finset.mem_inter.mp hx).1)
      (fun x hx => fAdj x (Finset.mem_inter.mp hx).2))
  by_cases inner : ∃ b : Fin 2, c ∈ side (n := n) C j b
  · obtain ⟨b,hb⟩ := inner
    have all := commonNeighborArm ((junkWmax hAO hT hJ h01 h10 hmem c).mp cw) hb
    have out : c ∉ side (n := n) C j (1-b) := fun h => G.irrefl (all c h)
    obtain ⟨W,hW,hcap,reach⟩ := chooseArm (1-b) out
    have big := share W hW hcap
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (W ∩ Q).card)
    obtain ⟨aw,aq⟩ := Finset.mem_inter.mp ha
    exact noShare a aq (fun x hx => all x (orInTrans (reach a aw) hx))
  push Not at inner
  obtain ⟨A,hA,ac,ar⟩ := chooseArm 0 (inner 0)
  obtain ⟨B,hB,bc,br⟩ := chooseArm 1 (inner 1)
  have smallA := share A hA ac
  have smallB := share B hB bc
  have dis : Disjoint (A ∩ Q) (B ∩ Q) := by
    apply Finset.disjoint_left.mpr
    intro k ka kb
    obtain ⟨ka,kq⟩ := Finset.mem_inter.mp ka
    obtain ⟨kb,_⟩ := Finset.mem_inter.mp kb
    refine noShare k kq (fun x hx => ?_)
    exact (guardOverlapAdj hAO hT hJ h01 h10 hmem
      (Finset.mem_inter.mpr ⟨orInTrans (ar k ka) hx,orInTrans (br k kb) hx⟩) cw).symm
  have bigP := Finset.card_le_card (show (A ∩ Q) ∪ (B ∩ Q) ⊆ P from
    Finset.union_subset (Finset.inter_subset_right.trans qsub) (Finset.inter_subset_right.trans qsub))
  rw [Finset.card_union_of_disjoint dis] at bigP
  have e4 : E.card = 4 := by omega
  have eAll : E = I := Finset.eq_of_subset_of_card_le Ih (by have h := degree c; change I.card ≤ 4 at h; omega)
  have xBig : 1 < X.card := by omega
  have inBoth (x : Fin n) (hx : x ∈ X) : x ∈ side (n := n) C j 0 ∩ side C j 1 := by
    have r := (starLeafRoute2264 hAO hT hJ sep cross tag (eU x hx)
      (route _ (assignedStarMem.mp hx))).1
    exact exteriorTail (junkVal hAO hT hJ h01 h10 hmem) r inner
  have onlyGuard (x : Fin n) (hx : x ∈ wmax G C j) : x = c :=
    uniqueCommonCenter h4 xBig
      (fun y hy => (guardOverlapAdj hAO hT hJ h01 h10 hmem (inBoth y hy) hx).symm) eAdj
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  obtain ⟨u,v,eq,_,opts⟩ := routedEdgeProfile hAO hT hJ sep cross tag (esub he) (route e he)
  rcases opts with ⟨a,ha,_⟩ | ⟨x,_,y,hw,_,hxy,no,_,_⟩
  · have hz := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  · have yc := onlyGuard y hw
    rw [yc] at hxy no
    have hadj : s(c,x) ∈ I := Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr hxy.symm,Sym2.mem_iff.mpr (.inl rfl)⟩
    exact no (Sym2.eq_swap ▸ esub (eAll.symm ▸ hadj))
theorem bothStarsSixExact2264 (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ : ℕ} (hneq : j₀ ≠ j₁) (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (sep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (cross : HasCross G C) 
    (hseven : ∀ K : Finset (Fin n), G.IsVertexCover (↑K) → 7 ≤ K.card)
    (hcover : ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges (↑(Ustar G C))) K →
      K.card ≤ (tops G C \ centreless G C).card)
    (ledger : 17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card)
    (degree : ∀ v : Fin n, (G.edgeFinset.filter (fun e => v ∈ e)).card ≤ 4)
    (ht : (tops G C).card = 6)
    {E F : Finset (Sym2 (Fin n))} (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (er : ∀ e ∈ E, RoutedAt G C j₀ e) (fr : ∀ e ∈ F, RoutedAt G C j₁ e)
    {c d : Fin n} (eStar : ∀ e ∈ E, c ∈ e) (fStar : ∀ e ∈ F, d ∈ e) :
    22 ≤ C.size := by
  classical
  by_contra! size
  let S : Finset (Fin n) := {c,d}
  let P := NoPureMix G C
  let L (j : ℕ) := (mixLabels G C j₀ j₁ j).card
  let Z (j : ℕ) := (centreRoutes G C j).card
  let R (j : ℕ) := Z j + L j
  have hS : ∀ e ∈ Ustar G C, ∃ x ∈ S, x ∈ e := by
    intro e he
    rcases Finset.mem_union.mp (split.symm ▸ he) with he | he
    · exact ⟨c,Finset.mem_insert_self _ _,eStar _ he⟩
    · exact ⟨d,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),fStar _ he⟩
  have totalC := residualCoverFromEdgeCentres hseven hcover S hS
  have S2 : S.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have tn := Finset.card_sdiff_add_card_eq_card
    (show centreless G C ⊆ tops G C from Finset.filter_subset _ _)
  have Rcap : Z j₀ + Z j₁ ≤ (centreless G C).card := centreRoutesCard hAO sep
  have MCap : L j₀ + L j₁ ≤ (mixing G C).card := mixLabelsCard (G := G) (C := C) hneq
  have budget := numericShortBudget (by omega) ledger (Z j₀) (Z j₁) (L j₀) (L j₁) Rcap MCap
  have UV := Finset.card_union_of_disjoint dis
  rw [split] at UV
  have total : 2+P.card+R j₀+R j₁ ≤ E.card+F.card := by
    dsimp only [R]
    change (tops G C).card + Z j₀ + Z j₁ + L j₀ + L j₁ + P.card ≤ (Ustar G C).card + 4 at budget
    omega
  have esub : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have fsub : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  have eQ : E.card ≤ (pureForLeaves G C (assignedStarLeaves E c)).card + R j₀ :=
    by simpa [R,Z,L,Nat.add_assoc] using starProductBudget hAO hT h4 hJ h01 h10 sep cross (.inl rfl) E esub er c eStar
  have fQ : F.card ≤ (pureForLeaves G C (assignedStarLeaves F d)).card + R j₁ :=
    by simpa [R,Z,L,Nat.add_assoc] using starProductBudget hAO hT h4 hJ h01 h10 sep cross (.inr rfl) F fsub fr d fStar
  have pq (V : Finset (Fin n)) : (pureForLeaves G C V).card ≤ P.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have ep := pq (assignedStarLeaves E c)
  have fp := pq (assignedStarLeaves F d)
  have eR : 1 ≤ R j₀ := by
    obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    exact positiveRouteCharge2264 hAO hT hJ sep cross (.inl rfl) (esub he) (er e he)
  have fR : 1 ≤ R j₁ := by
    obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    exact positiveRouteCharge2264 hAO hT hJ sep cross (.inr rfl) (fsub he) (fr e he)
  have ne : c ≠ d := by
    intro cd
    have uStar : ∀ e ∈ Ustar G C, c ∈ e := by
      intro e he
      exact (Finset.mem_union.mp (split.symm ▸ he)).elim (eStar e) (fun h => cd.symm ▸ fStar e h)
    have uB := (Finset.card_le_card (show Ustar G C ⊆ G.edgeFinset.filter (fun e => c ∈ e) from
      fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,uStar e he⟩)).trans (degree c)
    omega
  have degBound {B : Finset (Sym2 (Fin n))} {x : Fin n} (hB : B ⊆ Ustar G C)
      (hs : ∀ e ∈ B, x ∈ e) : B.card ≤ 4 :=
    (Finset.card_le_card (show B ⊆ G.edgeFinset.filter (fun e => x ∈ e) from
      fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hB he)).1,hs e he⟩)).trans (degree x)
  have adjStar {B : Finset (Sym2 (Fin n))} {x y : Fin n} (hB : B ⊆ Ustar G C)
      (hy : y ∈ assignedStarLeaves B x) : G.Adj x y :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hB (assignedStarMem.mp hy))).1
  by_cases zero : Z j₀ = 0
  · exact oneZeroCentrelessSix2264 hAO hT h4 hJ h01 h10 sep cross (.inl rfl) esub er
      ne eStar degree zero (R j₁) fR (degBound fsub fStar) fQ (fun _ h => adjStar fsub h) (by
        change 2+P.card+L j₀+R j₁ ≤ E.card+F.card
        have key : R j₀ = Z j₀ + L j₀ := rfl
        omega)
  · have zero' : Z j₁ = 0 := by omega
    exact oneZeroCentrelessSix2264 hAO hT h4 hJ h01 h10 sep cross (.inr rfl) fsub fr
      ne.symm fStar degree zero' (R j₀) eR (degBound esub eStar) eQ (fun _ h => adjStar esub h) (by
        change 2+P.card+L j₁+R j₀ ≤ F.card+E.card
        have key : R j₁ = Z j₁ + L j₁ := rfl
        omega)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def StarNeighborhood (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (c : Fin n) : Prop :=
  (c ∈ wmax G C j → c ∈ side (n := n) C j 0 ∨ c ∈ side C j 1) ∧
    (c ∉ wmax G C j → (ctrByJunk G C j).card = 0 ∨ c ∈ side (n := n) C j 0 ∩ side C j 1)
theorem twoStarTally (hAO : IsAO2 n C) (h4 : NoFourCycle G) (cross : HasCross G C)
    {E F : Finset (Sym2 (Fin n))} {a b : Fin n} {m₀ m₁ z₀ z₁ : ℕ}
    (A : StarRequest (C := C) E a m₀ z₀) (B : StarRequest (C := C) F b m₁ z₁)
    (split : E ∪ F = Ustar G C) (dis : Disjoint E F)
    (adjB : b ≠ a → ∀ w ∈ B.roots, ∀ x ∈ orIn n C w, G.Adj b x) :
    (Ustar G C).card ≤ (NoPureMix G C).card + (m₀ + m₁) + (z₀ + z₁) := by
  classical
  let center (i : Bool) := if i then b else a
  let roots (i : Bool) := if i then B.roots else A.roots
  let leaves (i : Bool) := if i then B.leaves else A.leaves
  let edges (i : Bool) := if i then F else E
  have sub (i : Bool) : edges i ⊆ Ustar G C := by
    cases i
    · exact split ▸ Finset.subset_union_left
    · exact split ▸ Finset.subset_union_right
  have tar (i : Bool) : ∀ v ∈ leaves i, s(center i,v) ∈ edges i := by
    cases i
    · exact A.targets
    · exact B.targets
  have bd (i : Bool) : ∀ w ∈ roots i, w < n+C.gates.length := by
    cases i
    · exact A.bound
    · exact B.bound
  have pu (i : Bool) : ∀ w ∈ roots i, ∀ k, OrReaches n C w k → (gateAt C k).op ≠ GateOp.and := by
    cases i
    · exact A.pure
    · exact B.pure
  have ad (i : Bool) : center i ≠ a → ∀ w ∈ roots i, ∀ v ∈ orIn n C w, G.Adj (center i) v := by
    cases i
    · exact fun h => (h rfl).elim
    · exact adjB
  have cov (i : Bool) : leaves i ⊆ (roots i).biUnion (orIn n C) := by
    cases i
    · exact A.covered
    · exact B.covered
  have dif (i j : Bool) (ne : i ≠ j) (eq : center i = center j) : Disjoint (leaves i) (leaves j) := by
    apply Finset.disjoint_left.mpr
    intro x hi hj
    have e1 := tar i x hi
    have e2 := tar j x hj
    rw [← eq] at e2
    cases i <;> cases j
    · exact ne rfl
    · exact Finset.disjoint_left.mp dis e1 e2
    · exact Finset.disjoint_left.mp dis e2 e1
    · exact ne rfl
  have forest := summedForestOneSelective Finset.univ center roots leaves a hAO h4 cross
    (fun i _ => bd i) (fun i _ => pu i) (fun i _ => ad i)
    (fun i _ v hv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (sub i (tar i v hv))).1)
    (fun i _ => cov i) (fun i _ j _ => dif i j) (fun i _ _ _ _ x hx _ _ _ => Or.inl (sub i (tar i x hx)))
  change (∑ i : Bool, (leaves i).card) ≤ _ + ∑ i : Bool, (roots i).card at forest
  simp [Fintype.sum_bool,leaves,roots] at forest
  have ea := A.tally
  have eb := B.tally
  have ra := A.cost
  have rb := B.cost
  have card := Finset.card_union_of_disjoint dis
  rw [split] at card
  omega
theorem twoStarBudgetOneNeighborhood (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (cross : HasCross G C) {p q : ℕ} (ne : p ≠ q) (hj : junk G C = {p,q})
    (pq : ¬ InCone n C p q) (qp : ¬ InCone n C q p)
    (apart : ∀ a ∈ tops G C, InCone n C p a → ¬ InCone n C q a) (route : HasRoute G C p q)
    {a b : Fin n}
    (star₀ : ∀ e, RoutedAt G C p e → a ∈ e) (star₁ : ∀ e, RoutedAt G C q e → b ∈ e)
    (near : a ≠ b → StarNeighborhood G C q b) :
    (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card := by
  obtain ⟨E,F,dis,split,rE,rF⟩ := twoRoutePartition route
  have he : E ⊆ Ustar G C := split ▸ Finset.subset_union_left
  have hf : F ⊆ Ustar G C := split ▸ Finset.subset_union_right
  by_cases ep : E.Nonempty
  · by_cases fp : F.Nonempty
    · obtain ⟨A⟩ := starRequestExists hAO hT h4 cross hj pq qp apart (.inl rfl) E he rE ep a
        (fun e h => star₀ e (rE e h))
      obtain ⟨B,adjB⟩ := starRequestWithProperties hAO hT h4 cross hj pq qp apart (.inr rfl) F hf rF fp b
        (fun e h => star₁ e (rF e h))
      have tally := twoStarTally hAO h4 cross A B split dis (fun h => adjB (near h.symm))
      have mt := mixByJunkTotal hAO apart
      have zt := ctrByJunkTotal apart
      have part := Finset.card_sdiff_add_card_eq_card
        (show mixing G C ⊆ orN G C \ lam G C from fun _ h => mixingNotLam h)
      change (NoPureMix G C).card + (mixing G C).card = (orN G C \ lam G C).card at part
      omega
    · have eq : E = Ustar G C := by simpa [Finset.not_nonempty_iff_eq_empty.mp fp] using split
      exact allRoutedBudget hAO hT h4 ne hj pq qp apart cross (.inl rfl) (eq ▸ rE)
  · have eq : F = Ustar G C := by simpa [Finset.not_nonempty_iff_eq_empty.mp ep] using split
    exact allRoutedBudget hAO hT h4 ne hj pq qp apart cross (.inr rfl) (eq ▸ rF)
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
private lemma starLeafCount (V : Finset (Sym2 (Fin n))) (c : Fin n)
    (h : ∀ e ∈ V, c ∈ e) :
    (Finset.univ.filter (fun x => s(c,x) ∈ V)).card = V.card := by
  let L := Finset.univ.filter (fun x => s(c,x) ∈ V)
  have him : L.image (fun x => s(c,x)) = V := by
    ext e
    constructor
    · rintro he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hx).2
    · intro he
      obtain ⟨x,rfl⟩ := Sym2.mem_iff_exists.mp (h e he)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  have hinj : Set.InjOn (fun x : Fin n => s(c,x)) (↑L : Set (Fin n)) := by
    intro x _ y _ he
    rcases Sym2.eq_iff.mp he with ⟨_,eq⟩ | ⟨eq₁,eq₂⟩
    · exact eq
    · exact eq₂.trans eq₁
  exact (Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card him)
private lemma outsideStarArm {j₀ j₁ j : ℕ}
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hj : j = j₀ ∨ j = j₁)
    (V : Finset (Sym2 (Fin n))) (hr : ∀ e ∈ V, RoutedAt G C j e)
    (c : Fin n) (outside : ∀ b : Fin 2, c ∉ side (n := n) C j b) :
    ∀ b : Fin 2, Finset.univ.filter (fun x => s(c,x) ∈ V) ⊆ side (n := n) C j b := by
  have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  intro b x hx
  have he := (Finset.mem_filter.mp hx).2
  obtain ⟨_,_,_,_,_,on⟩ := servedByPair (hr _ he)
  exact (termsHit (junkVal hAO hT hJ h01 h10 hjm) b on).resolve_left (outside b)
private lemma paidArmRoot {j₀ j₁ j : ℕ}
    (hL : IsLeastAO G C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁) (b : Fin 2)
    (c : Fin n) (X : Finset (Fin n)) (hX : 2 ≤ X.card)
    (hU : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (sub : X ⊆ side (n := n) C j b) :
    opnd C j b ∈ (NoPureMix G C).image (n+·) := by
  have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  let w := opnd C j b
  have hn : n ≤ w := by
    by_contra! small
    have hcard := Finset.card_le_card sub
    change _ ≤ (orIn n C w).card at hcard
    rw [orInRaw small,Finset.card_singleton] at hcard
    omega
  have hnot : ¬ Eligible.Available G C (orIn n C w) := by
    rintro (small | ⟨v,good⟩)
    · have hcard : X.card ≤ (orIn n C w).card := Finset.card_le_card sub
      omega
    · have adj (x : Fin n) (hx : x ∈ X) : G.Adj c x :=
        SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hU x hx)).1
      have eq := uniqueCommonCenter h4 (by omega : 1 < X.card)
        (fun x hx => (good x (sub hx)).1) adj
      subst v
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
      exact (good x (sub hx)).2 (hU x hx)
  have bound := (opndBound hL.1 (junkData hjm).1 b).trans
    (Nat.add_lt_add_left (junkData hjm).1 n)
  have hp := pureJunkOperand hL.1 hT hJ h01 h10 hjm (b := b)
  have hin : w ∈ Eligible.pureInternals G C w :=
    Finset.mem_filter.mpr ⟨Eligible.clipMem.mpr Relation.ReflTransGen.refl,hn,hnot⟩
  refine Finset.mem_image.mpr ⟨w-n,Eligible.pureInternalsCharged hL.1 bound hp hcross hin,?_⟩
  omega
private lemma upperExternalStar {j₀ j₁ j : ℕ}
    (hAO : IsAO2 n C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hj : j = j₀ ∨ j = j₁) (hZ : centreless G C = ∅)
    (V : Finset (Sym2 (Fin n))) (hV : V ⊆ Ustar G C) (hu : 2 ≤ V.card)
    (hr : ∀ e ∈ V, RoutedAt G C j e)
    (c : Fin n) (hstar : ∀ e ∈ V, c ∈ e) (hsafe : c ∈ wmax G C j)
    (outside : ∀ b : Fin 2, c ∉ side (n := n) C j b)
    (hdeg : (G.edgeFinset.filter (fun e => c ∈ e)).card ≤ 4) :
    V.card ≤ 3 := by
  let X := Finset.univ.filter (fun x => s(c,x) ∈ V)
  have hX : X.card = V.card := starLeafCount V c hstar
  have hxsite (b : Fin 2) : X ⊆ side (n := n) C j b :=
    outsideStarArm hAO hT hJ h01 h10 hj V hr c outside b
  have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  have unique {w : Fin n} (hw : w ∈ wmax G C j) : w = c := by
    apply uniqueCommonCenter h4 (show 1 < X.card by omega)
    · intro x hx
      exact (guardOverlapAdj hAO hT hJ h01 h10 hjm
        (Finset.mem_inter.mpr ⟨hxsite 0 hx,hxsite 1 hx⟩) hw).symm
    · intro x hx
      exact (guardOverlapAdj hAO hT hJ h01 h10 hjm
        (Finset.mem_inter.mpr ⟨hxsite 0 hx,hxsite 1 hx⟩) hsafe).symm
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
  obtain ⟨_,_,_,_,hc | ⟨a,_,w,hw,_,hadj,hnU,_,_⟩⟩ :=
    routedEdgeProfile hAO hT hJ hsep hcross hj (hV he) (hr e he)
  · obtain ⟨a,ha,_⟩ := hc
    have hm := (Finset.mem_filter.mp ha).1
    rw [hZ] at hm
    exact (Finset.notMem_empty _ hm).elim
  · have eq := unique hw
    subst w
    let e' := s(c,a)
    have eNo : e' ∉ V := fun h => hnU (Sym2.eq_swap ▸ hV h)
    have hsub : insert e' V ⊆ G.edgeFinset.filter (fun e => c ∈ e) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | h
      · exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj.symm,
          Sym2.mem_iff.mpr (.inl rfl)⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hV h)).1,hstar f h⟩
    have h := (Finset.card_le_card hsub).trans hdeg
    rw [Finset.card_insert_of_notMem eNo] at h
    omega
private lemma incomparableRootPairs (W A B : Finset ℕ)
    (hA : A.card = 2) (hB : B.card = 2) (hne : A ≠ B)
    (subA : A ⊆ W) (subB : B ⊆ W) :
    3 ≤ W.card ∧
      (W.card ≤ 3 → (∀ a ∈ A ∪ B, ∃ b ∈ W, b < a ∧
        (a ∈ A → b ∉ A) ∧ (a ∈ B → b ∉ B)) → False) := by
  have hnAB : ¬ A ⊆ B := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
  have hnBA : ¬ B ⊆ A := fun h => hne ((Finset.eq_of_subset_of_card_le h (by omega)).symm)
  obtain ⟨a,ha,han⟩ := Finset.not_subset.mp hnAB
  obtain ⟨b,hb,hbn⟩ := Finset.not_subset.mp hnBA
  have hsup : (A ∪ B).card ≤ W.card := Finset.card_le_card (Finset.union_subset subA subB)
  have hba : B \ A ⊆ A ∪ B := fun _ hz => Finset.mem_union_right _ (Finset.mem_sdiff.mp hz).1
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_union_left : A ⊆ A ∪ B)
  have he : (A ∪ B) \ A = B \ A := by ext z; by_cases h : z ∈ A <;> simp [h]
  rw [he] at hsum
  have hp : 0 < (B \ A).card := Finset.card_pos.mpr ⟨b,Finset.mem_sdiff.mpr ⟨hb,hbn⟩⟩
  refine ⟨by omega,fun hw hreach => ?_⟩
  have eqW : A ∪ B = W := Finset.eq_of_subset_of_card_le (Finset.union_subset subA subB) (by omega)
  obtain ⟨d,hd,hda,na,_⟩ := hreach a (Finset.mem_union_left _ ha)
  have hdA := na ha
  rw [←eqW,Finset.mem_union] at hd
  have hdB := hd.resolve_left hdA
  have hdb : d = b := Finset.card_le_one.mp (by omega : (B \ A).card ≤ 1) d
    (Finset.mem_sdiff.mpr ⟨hdB,hdA⟩) b (Finset.mem_sdiff.mpr ⟨hb,hbn⟩)
  obtain ⟨d,hd,hdb',_,nb⟩ := hreach b (Finset.mem_union_right _ hb)
  have hdB := nb hb
  rw [←eqW,Finset.mem_union] at hd
  have hdA := hd.resolve_right hdB
  have he' : (A ∪ B) \ B = A \ B := by ext z; by_cases h : z ∈ B <;> simp [h]
  have hsum' := Finset.card_sdiff_add_card_eq_card (Finset.subset_union_right : B ⊆ A ∪ B)
  rw [he'] at hsum'
  have hda' : d = a := Finset.card_le_one.mp (by omega : (A \ B).card ≤ 1) d
    (Finset.mem_sdiff.mpr ⟨hdA,hdB⟩) a (Finset.mem_sdiff.mpr ⟨ha,han⟩)
  omega
private lemma rawArmPairsDistinct {j₀ j₁ : ℕ}
    (hL : IsLeastAO G C) (hT : TopForm G C) (hlt : j₀ < j₁)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀) :
    ({opnd C j₀ 0,opnd C j₀ 1} : Finset ℕ) ≠ {opnd C j₁ 0,opnd C j₁ 1} := by
  intro he
  have hm₀ : j₀ ∈ junk G C := hJ.symm ▸ Finset.mem_insert_self _ _
  have hm₁ : j₁ ∈ junk G C := hJ.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  apply leastNoWireAlias hL (junkData hm₁).1 (show n+j₀ < n+j₁ by omega)
  intro x
  have each (j : ℕ) (hj : j ∈ junk G C) : gateVal n C j x = true ↔
      ∀ w ∈ ({opnd C j 0,opnd C j 1} : Finset ℕ), ∃ v ∈ orIn n C w, x v = true := by
    rw [junkVal hL.1 hT hJ h01 h10 hj x]
    simp [side]
  change gateVal n C j₀ x = gateVal n C j₁ x
  apply Bool.eq_iff_iff.mpr
  rw [each j₀ hm₀,each j₁ hm₁,he]
private lemma rawArmReachForbidden {j₀ j₁ j : ℕ}
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : junk G C = {j₀,j₁}) (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hj : j = j₀ ∨ j = j₁) {u v : ℕ}
    (hu : u ∈ ({opnd C j 0,opnd C j 1} : Finset ℕ))
    (hv : v ∈ ({opnd C j 0,opnd C j 1} : Finset ℕ))
    (hne : u ≠ v) :
    ¬ Relation.ReflTransGen (OrStep n C) u v := by
  have hm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
  have h := junkArmsIncomparable hL hT hJ h01 h10 hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  intro hr
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact hne rfl
  · exact h.2 (orInTrans hr)
  · exact h.1 (orInTrans hr)
  · exact hne rfl
theorem exteriorStarPairsZero (hL : IsLeastAO G C) (hT : TopForm G C) (h4 : NoFourCycle G)
    {j₀ j₁ : ℕ} (hlt : j₀ < j₁) (hJ : junk G C = {j₀,j₁})
    (h01 : ¬ InCone n C j₀ j₁) (h10 : ¬ InCone n C j₁ j₀)
    (hsep : ∀ a ∈ tops G C, InCone n C j₀ a → ¬ InCone n C j₁ a)
    (hcross : HasCross G C) (hZ : centreless G C = ∅)
    (V W : Finset (Sym2 (Fin n))) (apart : Disjoint V W) (cover : V ∪ W = Ustar G C)
    (vstars : 2 ≤ V.card) (wstars : 2 ≤ W.card)
    (vroute : ∀ e ∈ V, RoutedAt G C j₀ e) (wroute : ∀ e ∈ W, RoutedAt G C j₁ e)
    (c d : Fin n) (vstar : ∀ e ∈ V, c ∈ e) (wstar : ∀ e ∈ W, d ∈ e)
    (safe₀ : c ∈ wmax G C j₀) (safe₁ : d ∈ wmax G C j₁)
    (out₀ : ∀ b : Fin 2, c ∉ side (n := n) C j₀ b)
    (out₁ : ∀ b : Fin 2, d ∉ side (n := n) C j₁ b)
    (deg : ∀ v : Fin n, (G.edgeFinset.filter (fun e => v ∈ e)).card ≤ 4)
    (ht : 5 ≤ (tops G C).card) (hs : C.size ≤ 21)
    (hBudget : 17 + (tops G C \ centreless G C).card + 2*(centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card) : False := by
  classical
  let P := NoPureMix G C
  let D := P.image (n+·)
  let A := ({opnd C j₀ 0,opnd C j₀ 1} : Finset ℕ)
  let B := ({opnd C j₁ 0,opnd C j₁ 1} : Finset ℕ)
  have vsub : V ⊆ Ustar G C := cover ▸ Finset.subset_union_left
  have wsub : W ⊆ Ustar G C := cover ▸ Finset.subset_union_right
  have leafArm (j : ℕ) (hb : j = j₀ ∨ j = j₁) (E : Finset (Sym2 (Fin n)))
      (hr : ∀ e ∈ E, RoutedAt G C j e) (a : Fin n)
      (ho : ∀ b : Fin 2, a ∉ side (n := n) C j b) (b : Fin 2) :
      (Finset.univ.filter fun v => s(a,v) ∈ E) ⊆ side (n := n) C j b :=
    outsideStarArm hL.1 hT hJ h01 h10 hb E hr a ho b
  have one (j : ℕ) (h : j = j₀ ∨ j = j₁) (E : Finset (Sym2 (Fin n)))
      (ses : E ⊆ Ustar G C) (hr : ∀ e ∈ E, RoutedAt G C j e)
      (e2 : 2 ≤ E.card) (a : Fin n) (star : ∀ e ∈ E, a ∈ e)
      (outside : ∀ b : Fin 2, a ∉ side (n := n) C j b) :
      ∀ b : Fin 2, opnd C j b ∈ D := by
    intro b
    let X := Finset.univ.filter (fun x => s(a,x) ∈ E)
    have hc : X.card = E.card := starLeafCount E a star
    exact paidArmRoot hL hT h4 hJ h01 h10 hcross h b a X (by omega)
      (fun _ hx => ses (Finset.mem_filter.mp hx).2) (leafArm j h E hr a outside b)
  have subA : A ⊆ D := by
    intro w hw
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact one _ (.inl rfl) _ vsub vroute vstars c vstar out₀ 0
    · exact one _ (.inl rfl) _ vsub vroute vstars c vstar out₀ 1
  have subB : B ⊆ D := by
    intro w hw
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact one _ (.inr rfl) _ wsub wroute wstars d wstar out₁ 0
    · exact one _ (.inr rfl) _ wsub wroute wstars d wstar out₁ 1
  have cardTwo (j : ℕ) (hj : j = j₀ ∨ j = j₁) :
      ({opnd C j 0,opnd C j 1} : Finset ℕ).card = 2 := by
    have hmem : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using hj
    have notSub := (junkArmsIncomparable hL hT hJ h01 h10 hmem).1
    have ne : opnd C j 0 ≠ opnd C j 1 := by
      intro eq
      exact notSub (by unfold side; rw [eq])
    simp [ne]
  have comb := incomparableRootPairs D A B (cardTwo _ (.inl rfl)) (cardTwo _ (.inr rfl))
    (rawArmPairsDistinct hL hT hlt hJ h01 h10) subA subB
  have dCard : D.card = P.card := Finset.card_image_of_injOn (fun _ _ _ _ eq => by omega)
  have v3 := upperExternalStar hL.1 hT h4 hJ h01 h10 hsep hcross (.inl rfl)
    hZ V vsub vstars vroute c vstar safe₀ out₀ (deg c)
  have w3 := upperExternalStar hL.1 hT h4 hJ h01 h10 hsep hcross (.inr rfl)
    hZ W wsub wstars wroute d wstar safe₁ out₁ (deg d)
  have tm := mixByJunkTotal hL.1 hsep
  have vm := positiveActualRouteTag hL.1 hT hcross hJ hsep (.inl rfl) vsub vroute
    (Finset.card_pos.mp (by omega))
  have wm := positiveActualRouteTag hL.1 hT hcross hJ hsep (.inr rfl) wsub wroute
    (Finset.card_pos.mp (by omega))
  have ctr (j : ℕ) : (ctrByJunk G C j).card = 0 := by simp [ctrByJunk,hZ]
  rw [ctr,Nat.add_zero] at vm wm
  have cm : 2 ≤ (mixing G C).card := by omega
  have budget := numericShortBudget hs hBudget 0 0 (mixing G C).card 0 (by simp) (by simp)
  have card := Finset.card_union_of_disjoint apart
  rw [cover] at card
  change (tops G C).card + (mixing G C).card + P.card ≤ (Ustar G C).card + 4 at budget
  have lo := comb.1
  have eV : V.card = 3 := by omega
  have eW : W.card = 3 := by omega
  apply comb.2 (by omega)
  have hasChild (j : ℕ) (tag : j = j₀ ∨ j = j₁) (E : Finset (Sym2 (Fin n)))
      (e3 : E.card = 3) (sub : E ⊆ Ustar G C) (hr : ∀ e ∈ E, RoutedAt G C j e)
      (a : Fin n) (star : ∀ e ∈ E, a ∈ e) (out : ∀ b : Fin 2, a ∉ side (n := n) C j b)
      (b : Fin 2) :
      ∃ v ∈ D, v < opnd C j b ∧ Relation.ReflTransGen (OrStep n C) (opnd C j b) v := by
    let X := Finset.univ.filter fun x => s(a,x) ∈ E
    let w := opnd C j b
    have hc : X.card = 3 := (starLeafCount E a star).trans e3
    have hjm : j ∈ junk G C := by simpa only [hJ,Finset.mem_insert,Finset.mem_singleton] using tag
    have bound : w < n + C.gates.length :=
      (opndBound hL.1 (junkData hjm).1 b).trans (Nat.add_lt_add_left (junkData hjm).1 n)
    have pure := pureJunkOperand hL.1 hT hJ h01 h10 hjm (b := b)
    have hi (x : Fin n) (hx : x ∈ X) : s(a,x) ∈ Ustar G C :=
      sub (Finset.mem_filter.mp hx).2
    have adj (x : Fin n) (hx : x ∈ X) : G.Adj a x :=
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hi x hx)).1
    obtain ⟨I,hI,hcount,hreach⟩ := selectiveForestWithPool hL.1 h4 hcross {w}
      (by simpa using bound) (by simpa using pure) a X X Finset.Subset.rfl adj
      (by simpa [w,side] using leafArm j tag E hr a out b) hi
    rw [Finset.card_singleton] at hcount
    have find : ∃ k ∈ I, n+k ≠ w := by
      by_contra! fail
      have small : I.card ≤ 1 := Finset.card_le_one.mpr (fun p hp q hq => by
        have he := (fail p hp).trans (fail q hq).symm
        omega)
      omega
    obtain ⟨k,hk,ne⟩ := find
    obtain ⟨r,hrw,reach⟩ := hreach k hk
    have eq := Finset.mem_singleton.mp hrw
    subst r
    have le := orStep_le reach
    refine ⟨n+k,Finset.mem_image.mpr ⟨k,(Finset.mem_filter.mp (hI hk)).1,rfl⟩,by omega,reach⟩
  intro w hw
  have child : ∃ v ∈ D, v < w ∧ Relation.ReflTransGen (OrStep n C) w v := by
    rcases Finset.mem_union.mp hw with hw | hw
    · simp only [A,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hasChild _ (.inl rfl) _ eV vsub vroute c vstar out₀ 0
      · exact hasChild _ (.inl rfl) _ eV vsub vroute c vstar out₀ 1
    · simp only [B,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hasChild _ (.inr rfl) _ eW wsub wroute d wstar out₁ 0
      · exact hasChild _ (.inr rfl) _ eW wsub wroute d wstar out₁ 1
  obtain ⟨v,hv,lt,reach⟩ := child
  exact ⟨v,hv,lt,
    fun hwA hvA => rawArmReachForbidden hL hT hJ h01 h10 (.inl rfl) hwA hvA
      (Nat.ne_of_gt lt) reach,
    fun hwB hvB => rawArmReachForbidden hL hT hJ h01 h10 (.inr rfl) hwB hvB
      (Nat.ne_of_gt lt) reach⟩
end PEqualNP.Outside.L_meta_2264

namespace PEqualNP.Outside.L_meta_2264
open Profile2264 (graph)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma remainingStarsProof2264 : RemainingStars := by
  intro C j₀ j₁ hL hT top route ledger hcover hlt hJ h01 h10 sep _ h5 only₀ only₁
  obtain ⟨c,hc⟩ := only₀
  obtain ⟨d,hd⟩ := only₁
  have h4 : NoFourCycle graph := by decide +kernel
  have hn : graph.edgeFinset.Nonempty := ⟨s(0,9),by decide +kernel⟩
  have deg (v : Fin 11) : (graph.edgeFinset.filter (fun e => v ∈ e)).card ≤ 4 := by
    fin_cases v <;> decide +kernel
  have cross : HasCross graph C := fun a ha => (top a ha).1
  have jne := Nat.ne_of_lt hlt
  have close (h : (Ustar graph C).card ≤ (centreless graph C).card + (orN graph C \ lam graph C).card) :
      22 ≤ C.size := closeFromCharge 0 h5 (by simpa using h) ledger
  by_cases cd : c = d
  · exact close (twoStarBudgetOneNeighborhood hL.1 hT h4 cross jne hJ h01 h10 sep route hc hd
      (fun h => (h cd).elim))
  obtain ⟨V,W,dis,split,rv,rw⟩ := twoRoutePartition route
  have vs : ∀ e ∈ V, c ∈ e := fun e he => hc e (rv e he)
  have ws : ∀ e ∈ W, d ∈ e := fun e he => hd e (rw e he)
  by_cases seven : 7 ≤ (tops graph C).card
  · exact bothStarsSeven2264 hn hL hT h4 hlt hJ h01 h10 sep cross ledger deg seven
      split dis rv rw cd vs ws
  by_cases six : (tops graph C).card = 6
  · exact bothStarsSixExact2264 hL.1 hT h4 jne hJ h01 h10 sep cross Profile2264.seven_cover
      hcover ledger deg six split dis rv rw vs ws
  have five : (tops graph C).card = 5 := by omega
  let S : Finset (Fin 11) := {c,d}
  have sh : ∀ e ∈ Ustar graph C, ∃ x ∈ S, x ∈ e := by
    intro e he
    rcases Finset.mem_union.mp (split.symm ▸ he) with he | he
    · exact ⟨c,Finset.mem_insert_self _ _,vs e he⟩
    · exact ⟨d,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),ws e he⟩
  have coverC := residualCoverFromEdgeCentres Profile2264.seven_cover hcover S sh
  have s2 : S.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have zSum := Finset.card_sdiff_add_card_eq_card
    (show centreless graph C ⊆ tops graph C from Finset.filter_subset _ _)
  have z : (centreless graph C).card = 0 := by omega
  have zEmpty := Finset.card_eq_zero.mp z
  have zRoute (j : ℕ) : (centreRoutes graph C j).card = 0 := by simp [centreRoutes,zEmpty]
  have zTag (j : ℕ) : (ctrByJunk graph C j).card = 0 := by simp [ctrByJunk,zEmpty]
  have near (j : ℕ) (v : Fin 11)
      (h : ¬ (v ∈ wmax graph C j ∧ ∀ b : Fin 2, v ∉ side (n := 11) C j b)) :
      StarNeighborhood graph C j v := by
    refine ⟨?_,fun _ => .inl (zTag j)⟩
    intro hs
    by_contra! hh
    exact h ⟨hs,by intro b; fin_cases b <;> tauto⟩
  by_cases out₀ : c ∈ wmax graph C j₀ ∧ ∀ b : Fin 2, c ∉ side (n := 11) C j₀ b
  · by_cases out₁ : d ∈ wmax graph C j₁ ∧ ∀ b : Fin 2, d ∉ side (n := 11) C j₁ b
    · by_contra! size
      let P := NoPureMix graph C
      let L (j : ℕ) := (mixLabels graph C j₀ j₁ j).card
      have vSub : V ⊆ Ustar graph C := split ▸ Finset.subset_union_left
      have wSub : W ⊆ Ustar graph C := split ▸ Finset.subset_union_right
      have vCost := starProductBudget hL.1 hT h4 hJ h01 h10 sep cross (.inl rfl) V vSub rv c vs
      have wCost := starProductBudget hL.1 hT h4 hJ h01 h10 sep cross (.inr rfl) W wSub rw d ws
      have vCap := Finset.card_le_card (show pureForLeaves graph C (assignedStarLeaves V c) ⊆ P from
        Finset.filter_subset _ _)
      have wCap := Finset.card_le_card (show pureForLeaves graph C (assignedStarLeaves W d) ⊆ P from
        Finset.filter_subset _ _)
      rw [zRoute j₀,Nat.add_zero] at vCost
      rw [zRoute j₁,Nat.add_zero] at wCost
      change V.card ≤ (pureForLeaves graph C (assignedStarLeaves V c)).card + L j₀ at vCost
      change W.card ≤ (pureForLeaves graph C (assignedStarLeaves W d)).card + L j₁ at wCost
      have hMix := mixLabelsCard (G := graph) (C := C) jne
      have part := numericShortBudget (by omega) ledger 0 0 (L j₀) (L j₁) (by simp) hMix
      have uv := Finset.card_union_of_disjoint dis
      rw [split] at uv
      change (tops graph C).card + 0 + 0 + L j₀ + L j₁ + P.card ≤ (Ustar graph C).card + 4 at part
      have v1 : 1 ≤ L j₀ := by
        obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
        have cost := positiveRouteCharge2264 hL.1 hT hJ sep cross (.inl rfl) (vSub he) (rv e he)
        rw [zRoute j₀,Nat.zero_add] at cost
        exact cost
      have w1 : 1 ≤ L j₁ := by
        obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
        have cost := positiveRouteCharge2264 hL.1 hT hJ sep cross (.inr rfl) (wSub he) (rw e he)
        rw [zRoute j₁,Nat.zero_add] at cost
        exact cost
      exact exteriorStarPairsZero hL hT h4 hlt hJ h01 h10 sep cross zEmpty V W dis split
        (by omega) (by omega) rv rw c d vs ws out₀.1 out₁.1 out₀.2 out₁.2 deg h5 (by omega) ledger
    · exact close (twoStarBudgetOneNeighborhood hL.1 hT h4 cross jne hJ h01 h10 sep route hc hd
        (fun _ => near j₁ d out₁))
  · exact close (twoStarBudgetOneNeighborhood hL.1 hT h4 cross jne.symm
      (by simpa only [Finset.pair_comm] using hJ) h10 h01 (fun a ha h₁ h₀ => sep a ha h₀ h₁)
      (hasRouteComm route) hd hc (fun _ => near j₀ c out₀))
end PEqualNP.Outside.L_meta_2264

open PEqualNP.Outside.L_meta_2264 in
theorem PEqualNP.Outside.L_meta_2264 :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size :=
  exactFromStars remainingStarsProof2264
