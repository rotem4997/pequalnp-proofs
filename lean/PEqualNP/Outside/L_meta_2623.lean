import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2623_aux

def inc (a b : Fin 13) : Bool := [0, 1, 3, 9].contains ((a.val + 13 - b.val) % 13)

theorem inc_iff : ∀ a b : Fin 13,
    (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + d) ↔ inc a b = true := by decide

def missB (f : Fin 13 → Bool) (w : Fin 13) : Bool :=
  (List.finRange 13).all fun p => !(f p && inc p w)

def bitB (f : Fin 13 → Bool) (k : Fin 26) : Bool :=
  if k.val < 13 then f (Fin.ofNat 13 k.val) else missB f (Fin.ofNat 13 (k.val - 13))

def enc : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (enc bs)

theorem enc_testBit : ∀ (l : List Bool) (k : ℕ), (enc l).testBit k = l.getD k false
  | [], k => by simp [enc]
  | b :: bs, 0 => by simp [enc]
  | b :: bs, k + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit bs k]

def X4 (x4 : ℕ × ℕ) (x5 x6 : Fin 13) (x7 : Bool) : Fin (13 + 13) → Bool :=
  let x8 : ℕ → ℕ → Fin 13 → Bool := fun x8 x9 x10 => if x7 = true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6)
  Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1)

def PL : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]

def WL : List (ℕ × (ℕ × ℕ) × Fin 13 × Fin 13 × Bool) := [(7405575, (7, 904), 1, 0, false), (23330829, (13, 2848), 1, 0, false), (14811150, (7, 904), 1, 12, false), (5799955, (19, 708), 1, 0, false), (22282261, (21, 2720), 1, 0, false), (21757977, (25, 2656), 1, 0, false), (46661658, (13, 2848), 1, 12, false), (29622300, (7, 904), 1, 11, false), (21233693, (37, 2440), 9, 5, true), (3735587, (13, 2848), 3, 0, false), (19988517, (37, 2440), 1, 0, false), (11599910, (19, 708), 1, 12, false), (3211303, (13, 2848), 3, 2, true), (19415081, (41, 2370), 1, 0, false), (44564522, (21, 2720), 1, 12, false), (43515954, (25, 2656), 1, 12, false), (26222644, (13, 2848), 1, 11, false), (59244600, (7, 904), 1, 10, false), (42467386, (37, 2440), 9, 9, true), (7372867, (41, 2370), 3, 0, false), (24117317, (37, 2440), 9, 0, false), (7471174, (13, 2848), 3, 10, false), (7340103, (7, 904), 1, 4, true), (23085129, (7, 904), 9, 0, false), (39977034, (37, 2440), 1, 12, false), (23199820, (19, 708), 1, 11, false), (23068749, (13, 2848), 1, 2, true), (6422606, (13, 2848), 3, 12, true), (22052945, (41, 2370), 9, 3, false), (38830162, (41, 2370), 1, 12, false), (5275731, (133, 808), 1, 4, true), (22028372, (21, 2720), 1, 11, false), (22020181, (21, 2720), 1, 2, true), (19939425, (37, 2440), 3, 0, false), (19931236, (25, 2656), 1, 11, false), (19923045, (25, 2656), 1, 2, true), (52445288, (13, 2848), 1, 10, false), (18890857, (7, 904), 9, 4, true), (51388528, (7, 904), 1, 9, false), (17834100, (37, 2440), 9, 0, true), (6389891, (21, 2720), 9, 4, false), (6619269, (133, 808), 1, 0, false), (14745734, (41, 2370), 3, 10, false), (6357127, (41, 2370), 3, 12, true), (6570121, (13, 2848), 9, 2, false), (48234634, (37, 2440), 9, 4, false), (14942348, (13, 2848), 3, 7, false), (6553741, (19, 708), 1, 4, true), (14680206, (7, 904), 1, 3, true), (46170258, (7, 904), 9, 4, false), (12853396, (37, 2440), 1, 11, false), (46399640, (19, 708), 1, 10, false), (46137498, (13, 2848), 1, 1, true), (12845212, (13, 2848), 3, 9, true), (44105890, (41, 2370), 9, 7, false), (10559652, (41, 2370), 1, 11, false), (10551462, (133, 808), 1, 3, true), (44056744, (21, 2720), 1, 10, false), (44040362, (21, 2720), 1, 1, true), (6340801, (21, 2720), 9, 2, false), (39878850, (37, 2440), 3, 10, false), (6324419, (21, 2720), 9, 6, true), (39862472, (25, 2656), 1, 10, false), (6308041, (37, 2440), 3, 10, true), (39846090, (25, 2656), 1, 1, true), (37789904, (13, 2848), 1, 9, false), (37781714, (7, 904), 9, 8, true), (35676384, (7, 904), 1, 8, false), (35668200, (37, 2440), 9, 4, true), (4817155, (37, 2440), 3, 2, false), (12779782, (21, 2720), 9, 8, false), (21512457, (21, 2720), 3, 4, false), (13238538, (133, 808), 1, 12, false), (29491468, (41, 2370), 3, 7, false), (12714254, (41, 2370), 3, 9, true), (21528849, (7, 904), 3, 2, false), (13140242, (13, 2848), 9, 6, false), (4751635, (13, 2848), 9, 8, true), (29368596, (37, 2440), 9, 8, false), (29884696, (13, 2848), 3, 4, false), (21496089, (37, 2440), 1, 2, true), (13107482, (19, 708), 1, 3, true), (29360412, (7, 904), 1, 2, true), (17383713, (21, 2720), 3, 2, false), (25239844, (7, 904), 9, 8, false), (25706792, (37, 2440), 1, 10, false), (17318185, (21, 2720), 3, 6, true), (25698608, (19, 708), 1, 9, false), (25174324, (13, 2848), 1, 0, true), (25690424, (13, 2848), 3, 6, true), (21020993, (133, 808), 1, 7, false), (21111108, (41, 2370), 9, 11, false), (21119304, (41, 2370), 1, 10, false), (20988233, (41, 2370), 1, 12, true), (21102924, (133, 808), 1, 2, true), (21012816, (21, 2720), 1, 9, false), (21004625, (41, 2370), 9, 5, true), (20980052, (21, 2720), 1, 0, true), (4309377, (41, 2370), 3, 5, false), (12681602, (21, 2720), 9, 6, false), (4292995, (21, 2720), 9, 8, true), (12657028, (37, 2440), 3, 7, false), (12648838, (21, 2720), 9, 10, true), (12624272, (25, 2656), 1, 9, false), (12616082, (37, 2440), 3, 7, true), (12591508, (25, 2656), 1, 0, true), (8479136, (13, 2848), 1, 8, false), (8462756, (7, 904), 9, 12, true), (4252096, (7, 904), 1, 7, false), (4243905, (41, 2370), 3, 7, true), (4235728, (37, 2440), 9, 8, true), (18153989, (41, 2370), 9, 0, false), (9634310, (37, 2440), 3, 12, false), (25559564, (21, 2720), 9, 12, false), (18121233, (7, 904), 3, 1, false), (43024914, (21, 2720), 3, 1, false), (26477076, (133, 808), 1, 11, false), (18088469, (41, 2370), 9, 2, true), (58982936, (41, 2370), 3, 4, false), (25428508, (41, 2370), 3, 6, true), (17908257, (7, 904), 3, 0, false), (43057698, (7, 904), 3, 12, false), (26280484, (13, 2848), 9, 10, false), (17891877, (7, 904), 3, 4, true), (9503270, (13, 2848), 9, 12, true), (58737192, (37, 2440), 9, 12, false), (59769392, (13, 2848), 3, 1, false), (42992178, (37, 2440), 1, 1, true), (26214964, (19, 708), 1, 2, true), (58720824, (7, 904), 1, 1, true), (17875521, (13, 2848), 9, 0, false), (34767426, (21, 2720), 3, 12, false), (50479688, (7, 904), 9, 12, false), (51413584, (37, 2440), 1, 9, false), (17859153, (7, 904), 3, 5, true), (34636370, (21, 2720), 3, 3, true), (51397216, (19, 708), 1, 8, false), (17842785, (13, 2848), 9, 2, true), (50348648, (13, 2848), 1, 12, true), (51380848, (13, 2848), 3, 3, true), (377473, (37, 2440), 9, 2, false), (42041986, (133, 808), 1, 6, false), (42222216, (41, 2370), 9, 2, false), (42238608, (41, 2370), 1, 9, false), (41976466, (41, 2370), 1, 11, true), (42205848, (133, 808), 1, 1, true), (42025632, (21, 2720), 1, 8, false), (42009250, (41, 2370), 9, 9, true), (41960104, (21, 2720), 1, 12, true), (16892673, (13, 2848), 3, 2, false), (8618754, (41, 2370), 3, 2, false), (25363204, (21, 2720), 9, 10, false), (8585990, (21, 2720), 9, 12, true), (25314056, (37, 2440), 3, 4, false), (25297676, (21, 2720), 9, 1, true), (25248544, (25, 2656), 1, 8, false), (16859937, (37, 2440), 1, 10, true), (25232164, (37, 2440), 3, 4, true), (25183016, (25, 2656), 1, 12, true), (16958272, (13, 2848), 1, 7, false), (16827201, (19, 708), 1, 11, true), (16925512, (7, 904), 9, 3, true), (8504192, (7, 904), 1, 6, false), (115585, (7, 904), 1, 10, true), (8487810, (41, 2370), 3, 4, true), (8471456, (37, 2440), 9, 12, true), (2720771, (25, 2656), 1, 3, false), (19203077, (41, 2370), 1, 3, false), (19661833, (7, 904), 9, 1, false), (36307978, (41, 2370), 9, 4, false), (19268620, (37, 2440), 3, 9, false), (19137549, (7, 904), 9, 5, true), (17597457, (13, 2848), 9, 3, false), (51119128, (21, 2720), 9, 3, false), (17564697, (37, 2440), 3, 6, true), (19465249, (21, 2720), 3, 0, false), (36242466, (7, 904), 3, 11, false), (2688035, (37, 2440), 1, 5, true), (18949156, (21, 2720), 3, 11, false), (18940965, (21, 2720), 3, 2, true), (52954152, (133, 808), 1, 10, false), (19399721, (41, 2370), 1, 2, true), (36176938, (41, 2370), 9, 6, true), (50865200, (41, 2370), 3, 1, false), (50857016, (41, 2370), 3, 3, true), (35816514, (7, 904), 3, 10, false), (19014724, (7, 904), 3, 9, false), (52560968, (13, 2848), 9, 1, false), (35783754, (7, 904), 3, 1, true), (19006540, (13, 2848), 9, 3, true), (50373712, (37, 2440), 9, 3, false), (52438112, (13, 2848), 3, 11, false), (18883684, (37, 2440), 1, 0, true), (52429928, (19, 708), 1, 1, true), (50340976, (7, 904), 1, 0, true), (2458753, (7, 904), 9, 2, false), (35751042, (13, 2848), 9, 4, false), (2196611, (37, 2440), 3, 2, true), (2434180, (21, 2720), 3, 9, false), (2425989, (41, 2370), 1, 5, true), (33858704, (7, 904), 9, 3, false), (35726496, (37, 2440), 1, 8, false), (35718306, (7, 904), 3, 2, true), (2172068, (21, 2720), 3, 0, true), (35693760, (19, 708), 1, 7, false), (35685570, (13, 2848), 9, 6, true), (33596624, (13, 2848), 1, 11, true), (35661024, (13, 2848), 3, 0, true), (17401089, (37, 2440), 1, 5, false), (754946, (37, 2440), 9, 6, false), (623875, (25, 2656), 1, 7, true), (16983300, (133, 808), 1, 5, false), (17343760, (41, 2370), 9, 6, false), (17335569, (7, 904), 3, 6, true), (17376544, (41, 2370), 1, 8, false), (17368353, (21, 2720), 3, 4, true), (16852260, (41, 2370), 1, 10, true), (17311024, (133, 808), 1, 0, true), (16950592, (21, 2720), 1, 7, false), (16917828, (41, 2370), 9, 0, true), (16819536, (21, 2720), 1, 11, true), (17139201, (19, 708), 1, 4, false), (33785346, (13, 2848), 3, 12, false), (17237508, (41, 2370), 3, 12, false), (17106437, (133, 808), 1, 8, true), (50726408, (21, 2720), 9, 1, false), (17171980, (21, 2720), 9, 3, true), (50628112, (37, 2440), 3, 1, false), (17073681, (13, 2848), 9, 5, true), (50595352, (21, 2720), 9, 5, true), (50497088, (25, 2656), 1, 7, false), (33719874, (37, 2440), 1, 9, true), (50464328, (37, 2440), 3, 1, true), (50366032, (25, 2656), 1, 11, true), (33916544, (13, 2848), 1, 6, false), (362113, (13, 2848), 1, 8, true), (33654402, (19, 708), 1, 10, true), (33851024, (7, 904), 9, 7, true), (17008384, (7, 904), 1, 5, false), (16877313, (13, 2848), 3, 4, true), (231170, (7, 904), 1, 9, true), (16975620, (41, 2370), 3, 1, true), (16942912, (37, 2440), 9, 3, true), (5834755, (13, 2848), 1, 2, false), (5572613, (21, 2720), 1, 2, false), (5441542, (25, 2656), 1, 2, false), (5310471, (37, 2440), 9, 10, true), (4999177, (37, 2440), 1, 2, false), (38406154, (41, 2370), 1, 2, false), (6031377, (37, 2440), 9, 5, false), (39323666, (7, 904), 9, 5, false), (5769235, (13, 2848), 1, 4, true), (5515284, (41, 2370), 9, 8, false), (5507093, (21, 2720), 1, 4, true), (38537240, (37, 2440), 3, 6, false), (4982809, (25, 2656), 1, 4, true), (38275098, (7, 904), 9, 9, true), (1656865, (133, 808), 1, 2, false), (35194914, (13, 2848), 9, 7, false), (1640483, (19, 708), 1, 6, true), (35137584, (21, 2720), 9, 7, false), (35129394, (37, 2440), 3, 3, true), (38930498, (21, 2720), 3, 10, false), (5384260, (7, 904), 3, 8, false), (5376070, (37, 2440), 1, 4, true), (37898312, (21, 2720), 3, 8, false), (37881930, (21, 2720), 3, 12, true), (38807632, (133, 808), 1, 9, false), (38799442, (41, 2370), 1, 1, true), (5253204, (41, 2370), 9, 10, true), (34629728, (41, 2370), 3, 11, false), (34613360, (41, 2370), 3, 0, true), (4540545, (41, 2370), 9, 5, false), (4532356, (7, 904), 3, 7, false), (4524165, (41, 2370), 9, 7, true), (38029448, (7, 904), 3, 6, false), (4475017, (7, 904), 3, 10, true), (38021264, (13, 2848), 9, 5, false), (4466836, (7, 904), 3, 11, true), (38013080, (13, 2848), 9, 7, true), (33646752, (37, 2440), 9, 7, false), (37775552, (13, 2848), 3, 8, false), (37767368, (37, 2440), 1, 12, true), (37759184, (19, 708), 1, 0, true), (33581280, (7, 904), 1, 12, true), (4802817, (41, 2370), 1, 5, false), (4917506, (7, 904), 9, 6, false), (4786435, (7, 904), 9, 10, true), (4401412, (13, 2848), 9, 8, false), (4393222, (37, 2440), 3, 12, true), (4868360, (21, 2720), 3, 6, false), (4737289, (21, 2720), 3, 8, true), (4851978, (41, 2370), 1, 4, true), (616736, (7, 904), 9, 7, false), (608545, (41, 2370), 1, 7, true), (4352320, (37, 2440), 1, 7, false), (4335940, (7, 904), 3, 12, true), (4344136, (21, 2720), 3, 10, true), (4286848, (19, 708), 1, 6, false), (4278657, (133, 808), 1, 10, true), (4270468, (13, 2848), 9, 10, true), (92576, (13, 2848), 1, 10, true), (4221376, (13, 2848), 3, 10, true), (1395201, (21, 2720), 1, 4, false), (34802178, (37, 2440), 1, 4, false), (1509892, (37, 2440), 9, 10, false), (1378821, (21, 2720), 1, 6, true), (1247750, (25, 2656), 1, 6, true), (33966600, (133, 808), 1, 4, false), (34687520, (41, 2370), 9, 10, false), (1133089, (41, 2370), 9, 12, true), (34671138, (7, 904), 3, 3, true), (34753088, (41, 2370), 1, 7, false), (34736706, (21, 2720), 3, 1, true), (33704520, (41, 2370), 1, 9, true), (34622048, (133, 808), 1, 12, true), (33901184, (21, 2720), 1, 6, false), (346753, (21, 2720), 1, 8, true), (33835656, (41, 2370), 9, 4, true), (33639072, (21, 2720), 1, 10, true), (34278402, (19, 708), 1, 3, false), (470020, (13, 2848), 3, 9, false), (34475016, (41, 2370), 3, 9, false), (34212874, (133, 808), 1, 7, true), (34352144, (21, 2720), 9, 5, false), (34343960, (21, 2720), 9, 7, true), (34155552, (37, 2440), 3, 11, false), (34147362, (13, 2848), 9, 9, true), (34090032, (21, 2720), 9, 9, true), (33893504, (25, 2656), 1, 6, false), (339076, (37, 2440), 1, 8, true), (33827984, (37, 2440), 3, 11, true), (33631392, (25, 2656), 1, 10, true), (732416, (13, 2848), 1, 5, false), (724226, (13, 2848), 1, 7, true), (208132, (19, 708), 1, 9, true), (601376, (7, 904), 9, 11, true), (34016768, (7, 904), 1, 4, false), (33754626, (13, 2848), 3, 1, true), (462340, (7, 904), 1, 8, true), (33951240, (41, 2370), 3, 11, true), (33885824, (37, 2440), 9, 7, true), (3706883, (7, 904), 1, 1, false), (11669510, (13, 2848), 1, 1, false), (2904073, (19, 708), 1, 1, false), (11145226, (21, 2720), 1, 1, false), (10883084, (25, 2656), 1, 1, false), (10620942, (37, 2440), 9, 1, true), (1871889, (13, 2848), 3, 3, false), (9998354, (37, 2440), 1, 1, false), (1609747, (13, 2848), 3, 5, true), (9711636, (41, 2370), 1, 1, false), (3690529, (41, 2370), 3, 3, false), (12062754, (37, 2440), 9, 9, false), (3674147, (7, 904), 1, 5, true), (11546660, (7, 904), 9, 9, false), (11538470, (13, 2848), 1, 3, true), (11030568, (41, 2370), 9, 12, false), (2641961, (133, 808), 1, 5, true), (11014186, (21, 2720), 1, 3, true), (9973808, (37, 2440), 3, 3, false), (9965618, (25, 2656), 1, 3, true), (9449524, (7, 904), 9, 0, true), (3199041, (21, 2720), 9, 0, false), (3313730, (133, 808), 1, 1, false), (3182659, (41, 2370), 3, 2, true), (3289156, (13, 2848), 9, 11, false), (3280966, (19, 708), 1, 5, true), (3174496, (21, 2720), 9, 11, false), (3166305, (21, 2720), 9, 2, true), (3158116, (37, 2440), 3, 0, true), (2412673, (37, 2440), 3, 5, false), (10760324, (21, 2720), 3, 7, false), (10768520, (7, 904), 3, 5, false), (2379913, (13, 2848), 9, 4, true), (10752140, (37, 2440), 1, 3, true), (8695952, (21, 2720), 3, 5, false), (8663188, (21, 2720), 3, 9, true), (10514592, (133, 808), 1, 8, false), (10498212, (41, 2370), 1, 0, true), (10506408, (41, 2370), 9, 1, true), (2158784, (41, 2370), 3, 8, false), (2150593, (21, 2720), 9, 4, true), (2126048, (41, 2370), 3, 10, true), (9081090, (41, 2370), 9, 9, false), (9064712, (7, 904), 3, 4, false), (9048330, (41, 2370), 9, 11, true), (8958224, (7, 904), 3, 3, false), (8950034, (7, 904), 3, 7, true), (8941856, (13, 2848), 9, 9, false), (8933672, (7, 904), 3, 8, true), (8925488, (13, 2848), 9, 11, true), (192832, (37, 2440), 9, 11, false), (8450432, (13, 2848), 3, 5, false), (8434064, (37, 2440), 1, 11, true), (8417696, (19, 708), 1, 12, true), (61888, (7, 904), 1, 11, true), (1364481, (25, 2656), 1, 4, false), (9605634, (41, 2370), 1, 4, false), (9835012, (7, 904), 9, 10, false), (9572870, (7, 904), 9, 1, true), (8802824, (13, 2848), 9, 12, false), (8786444, (37, 2440), 3, 9, true), (9736720, (21, 2720), 3, 3, false), (1348113, (37, 2440), 1, 6, true), (9474578, (21, 2720), 3, 5, true), (9703956, (41, 2370), 1, 3, true), (1233472, (7, 904), 9, 11, false), (1102401, (37, 2440), 3, 5, true), (1217090, (41, 2370), 1, 6, true), (8704640, (37, 2440), 1, 6, false), (316033, (25, 2656), 1, 8, true), (8671880, (7, 904), 3, 9, true), (8688272, (21, 2720), 3, 7, true), (8573696, (19, 708), 1, 5, false), (8557314, (133, 808), 1, 9, true), (8540936, (13, 2848), 9, 1, true), (185152, (13, 2848), 1, 9, true), (8442752, (13, 2848), 3, 7, true), (2921473, (13, 2848), 1, 3, false), (2790402, (21, 2720), 1, 3, false), (2659331, (37, 2440), 9, 6, true), (2503684, (37, 2440), 1, 3, false), (3019784, (37, 2440), 9, 1, false), (2888713, (13, 2848), 1, 5, true), (2757642, (21, 2720), 1, 5, true), (2495500, (25, 2656), 1, 5, true), (832528, (133, 808), 1, 3, false), (824337, (19, 708), 1, 7, true), (2274368, (41, 2370), 9, 1, false), (2266178, (41, 2370), 9, 3, true), (2241604, (7, 904), 3, 0, true), (2405504, (41, 2370), 1, 6, false), (2397313, (7, 904), 9, 6, true), (2372740, (21, 2720), 3, 11, true), (308368, (41, 2370), 1, 8, true), (2143424, (133, 808), 1, 11, true), (701696, (21, 2720), 1, 5, false), (693506, (21, 2720), 1, 7, true), (570640, (41, 2370), 9, 8, true), (177472, (21, 2720), 1, 9, true), (1857537, (7, 904), 1, 2, false), (1456132, (19, 708), 1, 2, false), (940040, (13, 2848), 3, 6, false), (808969, (13, 2848), 3, 8, true), (1849360, (41, 2370), 3, 6, false), (1841169, (7, 904), 1, 6, true), (1325076, (133, 808), 1, 6, true), (1603616, (21, 2720), 9, 9, false), (1595425, (41, 2370), 3, 5, true), (1587248, (21, 2720), 9, 11, true), (1210432, (37, 2440), 3, 8, false), (1194052, (13, 2848), 9, 0, true), (1079392, (21, 2720), 9, 0, true), (686336, (25, 2656), 1, 5, false), (678152, (37, 2440), 1, 7, true), (555296, (37, 2440), 3, 8, true), (162112, (25, 2656), 1, 9, true), (1464832, (13, 2848), 1, 4, false), (1333761, (37, 2440), 9, 2, true), (1448452, (13, 2848), 1, 6, true), (416264, (19, 708), 1, 8, true), (1202752, (7, 904), 9, 2, true), (932864, (7, 904), 1, 3, false), (408580, (13, 2848), 3, 11, true), (924680, (7, 904), 1, 7, true), (801808, (41, 2370), 3, 8, true), (670976, (37, 2440), 9, 11, true)]

theorem wok : ∀ e ∈ WL, e.2.1 ∈ PL ∧ e.2.2.1 ∈ [(1 : Fin 13), 3, 9] ∧
    ∀ k : Fin 26, e.1.testBit k.val = X4 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 k := by
  decide +kernel

def h1B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).all fun v => f v || (List.finRange 13).any fun w => missB f w && inc v w

def h2B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).any (fun w => (List.finRange 13).all fun p => !f p || inc p w) ||
  (List.finRange 13).any (fun v => (List.finRange 13).all fun w => !missB f w || inc v w)

def chkF (f : Fin 13 → Bool) : Bool :=
  !h1B f || h2B f || WL.any (fun e => enc ((List.finRange 26).map (bitB f)) == e.1)

theorem key0 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key1 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key2 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key3 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key4 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key5 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key6 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key7 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key8 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key9 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key10 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key11 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key12 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key13 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key14 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key15 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  intro b0 b1 b2 b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact key0
  · exact key1
  · exact key2
  · exact key3
  · exact key4
  · exact key5
  · exact key6
  · exact key7
  · exact key8
  · exact key9
  · exact key10
  · exact key11
  · exact key12
  · exact key13
  · exact key14
  · exact key15

theorem pc : ∀ (k : Fin (13 + 13)) (p : Fin 13), k = Fin.castAdd 13 p ↔ (k.val < 13 ∧ p = Fin.ofNat 13 k.val) := by decide

theorem pn : ∀ (k : Fin (13 + 13)) (w : Fin 13), k = Fin.natAdd 13 w ↔ (¬ k.val < 13 ∧ w = Fin.ofNat 13 (k.val - 13)) := by decide

end PEqualNP.Outside.L_meta_2623_aux

open PEqualNP.Outside.L_meta_2623_aux in
theorem PEqualNP.Outside.L_meta_2623 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x4 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : ℕ × ℕ) (x5 x6 : Fin (13 : ℕ)) (x7 : Bool) =>   have x8 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x8 x9 : ℕ) (x10 : Fin (13 : ℕ)) => if x7 = Bool.true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6);   Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1); ∀ (x5 : Finset (Fin (13 : ℕ))),   let x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x5, ¬x2 x7 x6;   (∀ x7 ∉ x5, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x2 x7 x9) → ((¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x5, x2 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), x6 x9 → x2 x8 x9) → ∃ x9 ∈ x3, ∃ x10 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x11 : Fin (13 : ℕ)) (x12 : Bool), (fun (x13 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x14 ∈ x5, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x6 x14)) = x4 x9 x10 x11 x12 := by
  dsimp only
  intro X h1 h2
  let f : Fin 13 → Bool := fun i => decide (i ∈ X)
  have hf : chkF f = true := by
    have h := key (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12)
    have e : (fun i : Fin 13 => [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12].getD i.val false) = f := by
      funext i
      fin_cases i <;> rfl
    rwa [e] at h
  have hmiss : ∀ w, missB f w = true ↔ ∀ p ∈ X, ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d := by
    intro w
    constructor
    · intro h p hp hi
      simp only [missB, List.all_eq_true] at h
      have := h p (List.mem_finRange p)
      simp [f, hp, (inc_iff p w).1 hi] at this
    · intro h
      simp only [missB, List.all_eq_true]
      intro p _
      by_cases hp : p ∈ X
      · have : inc p w = false := by
          cases hi : inc p w
          · rfl
          · exact absurd ((inc_iff p w).2 hi) (h p hp)
        simp [f, hp, this]
      · simp [f, hp]
  have hh1 : h1B f = true := by
    simp only [h1B, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, hmiss, ← inc_iff, f, decide_eq_true_eq]
    intro v
    by_cases hv : v ∈ X
    · exact Or.inl hv
    · obtain ⟨w, a, b⟩ := h1 v hv
      exact Or.inr ⟨w, trivial, a, b⟩
  have hh2 : h2B f = false := by
    obtain ⟨h2a, h2b⟩ := h2
    cases hc : h2B f
    · rfl
    · exfalso
      simp only [h2B, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', ← inc_iff, f, decide_eq_false_iff_not] at hc
      rcases hc with ⟨w, _, hw⟩ | ⟨v, _, hv⟩
      · apply h2a
        refine ⟨w, fun p hp => ?_⟩
        rcases hw p with h | h
        · exact absurd hp h
        · exact h
      · apply h2b
        refine ⟨v, fun w hw => ?_⟩
        rcases hv w with h | h
        · exact absurd ((hmiss w).2 hw) (by rw [Bool.not_eq_true]; exact h)
        · exact h
  simp only [chkF, hh1, hh2, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at hf
  obtain ⟨e, he, heq⟩ := hf
  obtain ⟨ha, hb, hc⟩ := wok e he
  refine ⟨e.2.1, ha, e.2.2.1, hb, e.2.2.2.1, e.2.2.2.2, ?_⟩
  funext k
  show _ = X4 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 k
  rw [← hc k, ← heq, enc_testBit]
  have : ((List.finRange 26).map (bitB f)).getD k.val false = bitB f k := by
    simp
  rw [this]
  simp only [pc, pn]
  by_cases hk : k.val < 13
  · simp [hk, bitB, f]
  · simp only [hk, bitB, ite_false, false_and, and_false, exists_false, false_or, true_and, not_false_eq_true, exists_eq_left]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hmiss]
