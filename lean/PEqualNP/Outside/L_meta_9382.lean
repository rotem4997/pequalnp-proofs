import PEqualNP.Defs

-- The maximal-box normalization and local charges are adapted from checked L-meta-9376.

namespace PEqualNP.Outside.L_meta_9382
abbrev Pt := Fin 15
abbrev Box := Fin 65
def rowList : List Nat := [0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030]
def rowMask (i : Nat) := rowList.getD i 0
def rows : Box → Nat := ![3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385, 32769, 15, 51, 85, 105, 153, 165, 195, 771, 1285, 1545, 2313, 2565, 3075, 4369, 4641, 5185, 6273, 8481, 8721, 9345, 10305, 12291, 16705, 17025, 17425, 18465, 20485, 24585, 33153, 33345, 33825, 34833, 36873, 40965, 49155, 21845, 13107, 39321, 3855, 42405, 50115, 26985, 255, 43605, 52275, 26265, 61455, 23205, 15555, 38505]
def cols : Box → Nat := ![21845, 13107, 39321, 3855, 42405, 50115, 26985, 255, 43605, 52275, 26265, 61455, 23205, 15555, 38505, 4369, 1285, 771, 33153, 2313, 8481, 16705, 85, 51, 34833, 153, 8721, 17425, 15, 40965, 49155, 24585, 165, 2565, 18465, 17025, 20485, 195, 10305, 3075, 9345, 12291, 6273, 105, 33345, 33825, 1545, 36873, 4641, 5185, 3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385, 32769]
abbrev covered (k : Box) (p q : Pt) : Prop := (rows k).testBit (p.val+1)=true ∧ (cols k).testBit (q.val+1)=true
abbrev zero (p q : Pt) : Prop := (rowMask (p.val+1)).testBit (q.val+1)=false
end PEqualNP.Outside.L_meta_9382
namespace PEqualNP.Outside.L_meta_9382
abbrev Cap := Fin 67
def capRows : Cap → Nat := ![3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385, 32769, 15, 51, 85, 105, 153, 165, 195, 771, 1285, 1545, 2313, 2565, 3075, 4369, 4641, 5185, 6273, 8481, 8721, 9345, 10305, 12291, 16705, 17025, 17425, 18465, 20485, 24585, 33153, 33345, 33825, 34833, 36873, 40965, 49155, 21845, 13107, 39321, 3855, 42405, 50115, 26985, 255, 43605, 52275, 26265, 61455, 23205, 15555, 38505, 1, 65535]
def capCols : Cap → Nat := ![21845, 13107, 39321, 3855, 42405, 50115, 26985, 255, 43605, 52275, 26265, 61455, 23205, 15555, 38505, 4369, 1285, 771, 33153, 2313, 8481, 16705, 85, 51, 34833, 153, 8721, 17425, 15, 40965, 49155, 24585, 165, 2565, 18465, 17025, 20485, 195, 10305, 3075, 9345, 12291, 6273, 105, 33345, 33825, 1545, 36873, 4641, 5185, 3, 5, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097, 8193, 16385, 32769, 65535, 1]
def nextVals : Array (Array Nat) := #[#[0, 15, 15, 16, 16, 21, 21, 22, 22, 27, 27, 36, 36, 49, 49], #[15, 1, 15, 17, 20, 17, 20, 23, 26, 23, 26, 41, 48, 41, 48], #[15, 15, 2, 19, 18, 18, 19, 25, 24, 24, 25, 47, 42, 42, 47], #[16, 17, 19, 3, 16, 17, 19, 28, 33, 39, 46, 28, 33, 39, 46], #[16, 20, 18, 16, 4, 18, 20, 32, 29, 45, 40, 29, 32, 40, 45], #[21, 17, 18, 17, 18, 5, 21, 37, 44, 30, 35, 30, 35, 37, 44], #[21, 20, 19, 19, 20, 21, 6, 43, 38, 34, 31, 31, 34, 38, 43], #[22, 23, 25, 28, 32, 37, 43, 7, 22, 23, 25, 28, 32, 37, 43], #[22, 26, 24, 33, 29, 44, 38, 22, 8, 24, 26, 29, 33, 38, 44], #[27, 23, 24, 39, 45, 30, 34, 23, 24, 9, 27, 30, 34, 39, 45], #[27, 26, 25, 46, 40, 35, 31, 25, 26, 27, 10, 31, 35, 40, 46], #[36, 41, 47, 28, 29, 30, 31, 28, 29, 30, 31, 11, 36, 41, 47], #[36, 48, 42, 33, 32, 35, 34, 32, 33, 34, 35, 36, 12, 42, 48], #[49, 41, 42, 39, 40, 37, 38, 37, 38, 39, 40, 41, 42, 13, 49], #[49, 48, 47, 46, 45, 44, 43, 43, 44, 45, 46, 47, 48, 49, 14], #[15, 15, 15, 57, 57, 57, 57, 53, 53, 53, 53, 61, 61, 61, 61], #[16, 57, 57, 16, 16, 57, 57, 51, 51, 59, 59, 51, 51, 59, 59], #[57, 17, 57, 17, 57, 17, 57, 50, 58, 50, 58, 50, 58, 50, 58], #[57, 57, 18, 57, 18, 18, 57, 56, 64, 64, 56, 64, 56, 56, 64], #[57, 57, 19, 19, 57, 57, 19, 52, 60, 60, 52, 52, 60, 60, 52], #[57, 20, 57, 57, 20, 57, 20, 54, 62, 54, 62, 62, 54, 62, 54], #[21, 57, 57, 57, 57, 21, 21, 55, 55, 63, 63, 63, 63, 55, 55], #[22, 53, 53, 51, 51, 55, 55, 22, 22, 53, 53, 51, 51, 55, 55], #[53, 23, 53, 50, 54, 50, 54, 23, 53, 23, 53, 50, 54, 50, 54], #[53, 53, 24, 60, 64, 64, 60, 53, 24, 24, 53, 64, 60, 60, 64], #[53, 53, 25, 52, 56, 56, 52, 25, 53, 53, 25, 52, 56, 56, 52], #[53, 26, 53, 58, 62, 58, 62, 53, 26, 53, 26, 62, 58, 62, 58], #[27, 53, 53, 59, 59, 63, 63, 53, 53, 27, 27, 63, 63, 59, 59], #[51, 50, 52, 28, 51, 50, 52, 28, 51, 50, 52, 28, 51, 50, 52], #[51, 62, 64, 51, 29, 64, 62, 51, 29, 64, 62, 29, 51, 62, 64], #[63, 50, 64, 50, 64, 30, 63, 50, 64, 30, 63, 30, 63, 50, 64], #[63, 62, 52, 52, 62, 63, 31, 52, 62, 63, 31, 31, 63, 62, 52], #[51, 54, 56, 51, 32, 56, 54, 32, 51, 54, 56, 51, 32, 56, 54], #[51, 58, 60, 33, 51, 58, 60, 51, 33, 60, 58, 51, 33, 60, 58], #[63, 54, 60, 60, 54, 63, 34, 54, 60, 34, 63, 63, 34, 60, 54], #[63, 58, 56, 58, 56, 35, 63, 56, 58, 63, 35, 63, 35, 56, 58], #[36, 61, 61, 51, 51, 63, 63, 51, 51, 63, 63, 36, 36, 61, 61], #[55, 50, 56, 50, 56, 37, 55, 37, 55, 50, 56, 50, 56, 37, 55], #[55, 62, 60, 60, 62, 55, 38, 55, 38, 60, 62, 62, 60, 38, 55], #[59, 50, 60, 39, 59, 50, 60, 50, 60, 39, 59, 50, 60, 39, 59], #[59, 62, 56, 59, 40, 56, 62, 56, 62, 59, 40, 62, 56, 40, 59], #[61, 41, 61, 50, 62, 50, 62, 50, 62, 50, 62, 41, 61, 41, 61], #[61, 61, 42, 60, 56, 56, 60, 56, 60, 60, 56, 61, 42, 42, 61], #[55, 54, 52, 52, 54, 55, 43, 43, 55, 54, 52, 52, 54, 55, 43], #[55, 58, 64, 58, 64, 44, 55, 55, 44, 64, 58, 64, 58, 55, 44], #[59, 54, 64, 59, 45, 64, 54, 54, 64, 45, 59, 64, 54, 59, 45], #[59, 58, 52, 46, 59, 58, 52, 52, 58, 59, 46, 52, 58, 59, 46], #[61, 61, 47, 52, 64, 64, 52, 52, 64, 64, 52, 47, 61, 61, 47], #[61, 48, 61, 58, 54, 58, 54, 54, 58, 54, 58, 61, 48, 61, 48], #[49, 61, 61, 59, 59, 55, 55, 55, 55, 59, 59, 61, 61, 49, 49], #[66, 50, 66, 50, 66, 50, 66, 50, 66, 50, 66, 50, 66, 50, 66], #[51, 66, 66, 51, 51, 66, 66, 51, 51, 66, 66, 51, 51, 66, 66], #[66, 66, 52, 52, 66, 66, 52, 52, 66, 66, 52, 52, 66, 66, 52], #[53, 53, 53, 66, 66, 66, 66, 53, 53, 53, 53, 66, 66, 66, 66], #[66, 54, 66, 66, 54, 66, 54, 54, 66, 54, 66, 66, 54, 66, 54], #[55, 66, 66, 66, 66, 55, 55, 55, 55, 66, 66, 66, 66, 55, 55], #[66, 66, 56, 66, 56, 56, 66, 56, 66, 66, 56, 66, 56, 56, 66], #[57, 57, 57, 57, 57, 57, 57, 66, 66, 66, 66, 66, 66, 66, 66], #[66, 58, 66, 58, 66, 58, 66, 66, 58, 66, 58, 66, 58, 66, 58], #[59, 66, 66, 59, 59, 66, 66, 66, 66, 59, 59, 66, 66, 59, 59], #[66, 66, 60, 60, 66, 66, 60, 66, 60, 60, 66, 66, 60, 60, 66], #[61, 61, 61, 66, 66, 66, 66, 66, 66, 66, 66, 61, 61, 61, 61], #[66, 62, 66, 66, 62, 66, 62, 66, 62, 66, 62, 62, 66, 62, 66], #[63, 66, 66, 66, 66, 63, 63, 66, 66, 63, 63, 63, 63, 66, 66], #[66, 66, 64, 66, 64, 64, 66, 66, 64, 64, 66, 64, 66, 66, 64], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66]]
def grow (e : Cap) (p : Pt) := Fin.ofNat 67 ((nextVals[e.val]!)[p.val]!)
abbrev member (m : Nat) (x : Pt) := m.testBit (x.val+1)=true
theorem initial : ∀ q : Pt, member (capCols 65) q := by decide +kernel
theorem adds : ∀ (e : Cap) (p : Pt), member (capRows (grow e p)) p := by decide +kernel
theorem preserves : ∀ (e : Cap) (p i : Pt),
    member (capRows e) i → member (capRows (grow e p)) i := by decide +kernel
theorem intersects : ∀ (e : Cap) (p j : Pt),
    member (capCols e) j → zero p j → member (capCols (grow e p)) j := by decide +kernel
def project (e : Cap) : Box := Fin.ofNat 65 e.val
theorem proper : ∀ (e : Cap) (p q : Pt),
    member (capRows e) p → member (capCols e) q → covered (project e) p q := by decide +kernel
theorem closure (a b : Finset Pt) (clean : ∀ p∈a,∀ q∈b,zero p q) :
    ∃ e : Cap,(∀ p∈a,member (capRows e) p) ∧ (∀ q∈b,member (capCols e) q) := by
  classical
  induction a using Finset.induction_on with
  | empty => exact ⟨65,by simp,fun q _ => initial q⟩
  | @insert p a fresh ih =>
    obtain ⟨e,hr,hc⟩ := ih (fun i hi => clean i (Finset.mem_insert_of_mem hi))
    refine ⟨grow e p,?_,fun q hq => intersects e p q (hc q hq) (clean p (Finset.mem_insert_self p a) q hq)⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact adds e i
    · exact preserves e p i (hr i h)
def orig (p : Pt) : Fin 16 := ⟨p.val+1,by have := p.isLt;omega⟩
def trim (s : Finset (Fin 16)) := Finset.univ.filter fun p : Pt => orig p∈s
theorem inside (s : Finset (Fin 16)) (p : Pt) : p∈trim s ↔ orig p∈s := by simp [trim]
abbrev Rect := Finset (Fin 16) × Finset (Fin 16)
def pure (r : Rect) := ∀ i∈r.1,∀ j∈r.2,(rowMask i.val).testBit j.val=false
theorem extendBox (r : Rect) (hp : pure r) :
    ∃ k : Box,∀ p q,orig p∈r.1 → orig q∈r.2 → covered k p q := by
  obtain ⟨e,left,right⟩ := closure (trim r.1) (trim r.2)
    (fun p h q hq => hp (orig p) ((inside _ _).mp h) (orig q) ((inside _ _).mp hq))
  exact ⟨project e,fun p q h hq => proper e p q (left p ((inside _ _).mpr h)) (right q ((inside _ _).mpr hq))⟩
theorem normalize (l : List Rect) (good : ∀ r∈l,pure r) :
    ∃ S : Finset Box,S.card≤l.length ∧ ∀ r∈l,∀ p q,orig p∈r.1 → orig q∈r.2 → ∃ k∈S,covered k p q := by
  induction l with
  | nil => exact ⟨∅,by simp,by simp⟩
  | cons r rs ih =>
    obtain ⟨k,hk⟩ := extendBox r (good r (List.mem_cons_self ..))
    obtain ⟨S,size,hh⟩ := ih (fun s hs => good s (List.mem_cons_of_mem r hs))
    refine ⟨insert k S,?_,?_⟩
    · have := Finset.card_insert_le k S
      simp only [List.length_cons]
      omega
    · intro s hs p q hp hq
      rcases List.mem_cons.mp hs with rfl|tail
      · exact ⟨k,Finset.mem_insert_self ..,hk _ _ hp hq⟩
      · obtain ⟨t,ht,h⟩ := hh s tail p q hp hq
        exact ⟨t,Finset.mem_insert_of_mem ht,h⟩
end PEqualNP.Outside.L_meta_9382
namespace PEqualNP.Outside.L_meta_9382
abbrev Side := Fin 2
abbrev Bit := Fin 7
abbrev Tiny := Fin 128
def pick (d : Side) (p : Pt) := 15*d.val+p.val
def neighborhood : Array Nat := #[0xdb97531, 0xcb87430, 0xeba7632, 0xa987210, 0xec97641, 0xed87650, 0xdca7542, 0x6543210, 0xeca8531, 0xeda9430, 0xdc98632, 0xedcb210, 0xdba8641, 0xcba9650, 0xeb98542, 0xdb97531, 0xcb87430, 0xeba7632, 0xa987210, 0xec97641, 0xed87650, 0xdca7542, 0x6543210, 0xeca8531, 0xeda9430, 0xdc98632, 0xedcb210, 0xdba8641, 0xcba9650, 0xeb98542]
def neighbor (d : Side) (p : Pt) (j : Bit) : Pt := Fin.ofNat 15 ((neighborhood[pick d p]! >>> (4*j.val)) &&& 15)
def patches : Array Nat := #[0x8001000200040008001000201a0000000000000000000006100000000000000a400000001e6000000019540000000000000000000000007f, 0x1010000040400001010000040340000000000308000000000000000000000001480000e0004c0000c805400000000000000000000003f80, 0x400001010000040400001010000000c20000000d000000000000000000000000000003d20000000333000054000000000000000000001fc000, 0x4040404000000004040400000d00000000000c20000000029000000007000000000000009800caa000000000000000000000fe00000, 0x400080000200040400080000200000000290000000340000000000000700030800000000000002a013001900000000000000000007f0000000, 0x40400000000404040400000000400000000520000000000038068000000184000000000000015000130c80000000000000000003f800000000, 0x808001000004000808001000000000000000e0000000d00000148000c2000000000000000262a32000000000000000000001fc0000000000, 0x404040404040400000000006800000000308000000520000007000260032a8000000000000000000000000fe000000000000, 0x400080010002000008001000200000000004c000000000d00000000c80000308000a8052001c00000000000000000000007f00000000000000, 0x40400001010000000010100000400000026000000000320000000d0000018400054000520e00000000000000000000003f8000000000000000, 0x80800002020004000010100000000064000000003400000009800000c200000a4a838000000000000000000000001fc00000000000000000, 0x40404040000000000000004040400098000000000c80000002a000000069869070000000000000000000000000000fe0000000000000000000, 0x800101000200040008000020002a000000000d000000000619948c870000000000000000000000000000000007f000000000000000000000, 0x101010100000404000000005500000000000d30cc3348380000000000000000000000000000000000000003f80000000000000000000000, 0x400001000202000008080010001a2ac26694c0e0000000000000000000000000000000000000000000000001fc000000000000000000000000, 0x1fc00000000000003080a402600000000000d002a0000000320000000003800002000400080010002000400080, 0xfe00000000000000000000000061000294c0001a2a0000000006400000000070000040400001010000040400001, 0x7f0000000c348000980000000000000000000680002a0000c8000000000e000000100000404000010100000404000, 0x3f80000000000000000000000000000000000000000000c34a634546400000000000e00000010101010000000010101, 0x1fc000000006100029009800000000000000d002a00000000000000320000700000000100020000080010100020000080, 0xfe0000000030800000052980000000d1500000000000000000000000006438000000000101000000001010101000000001, 0x7f00000000000000000000001840520002600680002a00000000000c800000000001c0000002020004000010002020004000, 0x3f800000000000000000000000000000000000000000000000000000000000030d298d15190e00000000000001010101010101, 0x1fc00000000000000061014804c00000000000000680150000000000064000000000000003800100020004000800002000400080, 0xfe0000000000000003080014a60000000345400000000000000000003200000000000000000070101000004040000000040400001, 0x7f00000000000000000000000000000184000a53000000d15000000000000001900000000e000000002020000080800100000404000, 0x3f800000000000000000030d2980000000d15000000019000000000000000000000000000000000000f01010100000000000000010101, 0x1fc000000000000000000000000000000000030d20130000000000068015000064000000000700000000002000404000800100020000080, 0xfe00000000000000000000000000000000000000000000061a53000068a80003200000000038000000000000040404040000101000000001, 0x7f0000000000000000000000000000c20294c00000000000000000000000d150000000190000000001c0000100000400080800002020004000]
def patch (d : Side) (p : Pt) (k : Box) : Tiny := Fin.ofNat 128 ((patches[pick d p]! >>> (7*k.val)) &&& 127)
def costs : Array Nat := #[0x208208208210000000002000000400090002400000000006, 0x48048048042000010000000000080402010400000000030, 0x1009009009000400080000000000012000480400000000180, 0x1248001240080000400010002000000412000000000c00, 0x1040209040200010002000002010000002082000000006000, 0x1200049200040002000010400080000010090000000030000, 0x241008241000000400080080400000012400000000180000, 0x1249240000400010002002010480000000000c00000, 0x1041040208200002000080010010082080000000006000000, 0x1201200048040010000400080080402400000000030000000, 0x240241009000080002000400400490000000000180000000, 0x1248000001240400010002000492000000000000c00000000, 0x209041040202000080002492000000000000006000000000, 0x49201200050000092490000000000000000030000000000, 0x1008240241012492400000000000000000000180000000000, 0x180000010410000082000400010008208208208, 0xc00000000002012012000080002001201201201, 0x6000480400000000402010000400040240240240, 0x30000000000000000000492480000400049200049, 0x180002010400000082000000402000041008241008, 0xc00010002400090000000000090000048001248001, 0x6000000000082010402000010000080009040209040, 0x30000000000000000000000000012492400000049249, 0x180000002082000000410000080000010041041008208, 0xc00000010090002400000000400000002048048001201, 0x6000000000000080480090000002000400009009040240, 0x30000000012400090002000000000000000449200000049, 0x180000000000000012080000410080002000008241041008, 0xc00000000000000000002480480400010000001248048001, 0x6000000000000412000000000090002000080040209009040]
def cost (d : Side) (p : Pt) (k : Box) := (costs[pick d p]! >>> (3*k.val)) &&& 7
def kind (d : Side) (p : Pt) : Fin 1 := Fin.ofNat 1 (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0][pick d p]!)
def prices : Array Nat := #[0xd6cb24b238dbb238db91b6d2b238db8e369a8da8da6da691b238db8da8da8e369a6da69191b6d26da6916da691491448]
def price (d : Side) (p : Pt) (x : Tiny) := (prices[(kind d p).val]! >>> (3*x.val)) &&& 7
def joinMask (x y : Tiny) : Tiny := Fin.ofNat 128 (x.val ||| y.val)
theorem joinBit : ∀ (x y : Tiny) (j : Bit), (joinMask x y).val.testBit j.val=(x.val.testBit j.val || y.val.testBit j.val) := by decide +kernel
theorem allBits : ∀ x : Tiny, (∀ j : Bit, x.val.testBit j.val=true) → x=127 := by decide +kernel
theorem terminal : ∀ d p, price d p 0=0 ∧ price d p 127=6 := by decide +kernel
def cp (d : Side) (p q : Pt) (k : Box) := if d=0 then covered k p q else covered k q p
abbrev cz (d : Side) (p q : Pt) := if d=0 then zero p q else zero q p
theorem neighZero : ∀ d p j,cz d p (neighbor d p j) := by
  unfold cz zero
  decide +kernel
theorem patchSem : ∀ d p j k, cp d p (neighbor d p j) k → (patch d p k).val.testBit j.val=true := by
  unfold cp covered
  decide +kernel
def ways0 : Array (Nat × Nat) := #[(0,0), (1,1), (2,1), (4,1), (7,2), (8,1), (16,1), (25,2), (32,1), (42,2), (52,2), (64,1), (76,2), (82,2), (97,2), (127,6)]
def ways : Array (Array (Nat × Nat)) := #[ways0]
def values (f : Nat) (x : Tiny) := (prices[f]! >>> (3*x.val)) &&& 7
theorem listed : ∀ d p k, ((patch d p k).val,cost d p k) ∈ (ways[(kind d p).val]!).toList := by decide +kernel
private theorem atlas0 : ∀ x : Tiny, ∀ z∈ways0.toList,
    values 0 (joinMask x (Fin.ofNat 128 z.1))≤values 0 x+z.2 := by decide +kernel
theorem transition (d : Side) (p : Pt) (x : Tiny) (k : Box) :
    price d p (joinMask x (patch d p k)) ≤ price d p x + cost d p k := by
  have h := listed d p k
  change values (kind d p).val _ ≤ values (kind d p).val _ + _
  generalize he : kind d p=y at h ⊢
  fin_cases y
  · simpa only [Fin.ofNat_val_eq_self] using atlas0 x _ h
def charge (k : Box) := ∑ p : Pt,(cost 0 p k+cost 1 p k)
theorem chargeMax : ∀ k, charge k≤13 := by decide +kernel
end PEqualNP.Outside.L_meta_9382
namespace PEqualNP.Outside.L_meta_9382
theorem combineMasks (s : Finset Box) (d : Side) (p : Pt) :
    ∃ x : Tiny, price d p x ≤ ∑ k∈s,cost d p k ∧
       ∀ k∈s,∀ j : Bit,(patch d p k).val.testBit j.val=true → x.val.testBit j.val=true := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0,?_,by simp⟩
    rw [(terminal d p).1]
    simp
  | @insert k s hk ih =>
    obtain ⟨x,hx,inc⟩ := ih
    refine ⟨joinMask x (patch d p k),?_,?_⟩
    · rw [Finset.sum_insert hk]
      have step := transition d p x k
      omega
    · intro u hu j hj
      rw [joinBit]
      rcases Finset.mem_insert.mp hu with rfl|old
      · simp [hj]
      · simp [inc u old j hj]
theorem localCharge (S : Finset Box) (all : ∀ p q, zero p q → ∃ k∈S,covered k p q) (d : Side) (p : Pt) :
    6 ≤ ∑ k∈S,cost d p k := by
  obtain ⟨x,cap,inc⟩ := combineMasks S d p
  have hx : x=127 := by
    apply allBits
    intro j
    have good := neighZero d p j
    have found : ∃ k∈S,cp d p (neighbor d p j) k := by
      by_cases e : d=0
      · simp only [cz,e,if_true] at good
        simpa only [cp,e,if_true] using all p _ good
      · simp only [cz,if_neg e] at good
        simpa only [cp,if_neg e] using all _ p good
    obtain ⟨k,hk,valid⟩ := found
    exact inc k hk j (patchSem d p j k valid)
  rw [hx,(terminal d p).2] at cap
  exact cap
theorem collective (S : Finset Box) (all : ∀ p q,zero p q → ∃ k∈S,covered k p q) : 180≤∑ k∈S,charge k := by
  have each (p : Pt) : 12 ≤ ∑ k∈S,(cost 0 p k+cost 1 p k) := by
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (localCharge S all 0 p) (localCharge S all 1 p)
  calc
    180 = ∑ _ : Pt,12 := by decide +kernel
    _ ≤ ∑ p : Pt,∑ k∈S,(cost 0 p k+cost 1 p k) := Finset.sum_le_sum (fun p _ => each p)
    _ = _ := by rw [Finset.sum_comm];rfl
-- Each mask records which boxes meet the corresponding matching in at most one cell.
abbrev M := Fin 5

def matchRows : Array Nat := #[0x851ed43627c0ab9, 0x50d1c932ae68b47, 0xebac2051769834d, 0x2abe8d54c691307, 0xec1bda857642309]

def matchCol (m : M) (p : Pt) : Pt := Fin.ofNat 15 ((matchRows[m.val]! >>> (4*p.val)) &&& 15)

def goodMasks : Array Nat := #[0x1fffcffde56f5ffff, 0x1ffffe66bebfb7fff, 0x1ffff89fd7d0fffff, 0x1ffff33b7bf7e7fff, 0x1ffff4dc4f6e7ffff]

def goodAt (m : M) (k : Box) : Bool := (goodMasks[m.val]!).testBit k.val

def lineBox (k : Box) : Bool := 15 ≤ k.val && k.val < 50

def hits (m : M) (k : Box) : Finset Pt := Finset.univ.filter fun p => covered k p (matchCol m p)

theorem matchZero : ∀ m p, zero p (matchCol m p) := by decide +kernel

theorem goodHit : ∀ m k, goodAt m k = true → (hits m k).card ≤ 1 := by decide +kernel

theorem starsGood : ∀ m k, lineBox k = false → goodAt m k = true := by decide +kernel

theorem findMatch : ∀ i j : Box, ∃ m : M, goodAt m i = true ∧ goodAt m j = true := by decide +kernel

theorem chargeDeficit : ∀ k : Box, charge k + (if lineBox k then 1 else 0) ≤ 13 := by decide +kernel

theorem twoChoices (T : Finset Box) (hc : T.card ≤ 2) :
    ∃ i j : Box, ∀ k ∈ T, k = i ∨ k = j := by
  by_cases h : T.Nonempty
  · obtain ⟨i,hi⟩ := h
    by_cases he : (T.erase i).Nonempty
    · obtain ⟨j,hj⟩ := he
      refine ⟨i,j,fun k hk => ?_⟩
      by_cases eq : k = i
      · exact .inl eq
      · have hc' : (T.erase i).card ≤ 1 := by rw [Finset.card_erase_of_mem hi]; omega
        exact .inr (Finset.card_le_one.mp hc' k (Finset.mem_erase.mpr ⟨eq,hk⟩) j hj)
    · refine ⟨i,i,fun k hk => ?_⟩
      by_contra! hk'
      exact he ⟨k,Finset.mem_erase.mpr ⟨hk'.1,hk⟩⟩
  · exact ⟨0,0,fun k hk => (h ⟨k,hk⟩).elim⟩

theorem noFourteen (S : Finset Box) (small : S.card ≤ 14)
    (all : ∀ p q, zero p q → ∃ k ∈ S, covered k p q) : False := by
  have lo := collective S all
  have hi := Finset.sum_le_sum (s := S) (fun k _ => chargeDeficit k)
  have counter : (∑ k ∈ S, if lineBox k then 1 else 0) = (S.filter fun k => lineBox k = true).card := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, counter] at hi
  have nlines : (S.filter fun k => lineBox k = true).card ≤ 2 := by omega
  obtain ⟨i,j,hpair⟩ := twoChoices _ nlines
  obtain ⟨m,hmi,hmj⟩ := findMatch i j
  have hHit : ∀ k ∈ S, (hits m k).card ≤ 1 := by
    intro k hk
    apply goodHit
    cases hh : lineBox k with
    | false => exact starsGood m k hh
    | true =>
      rcases hpair k (Finset.mem_filter.mpr ⟨hk,hh⟩) with rfl | rfl
      · exact hmi
      · exact hmj
  have allHit : (Finset.univ : Finset Pt) ⊆ S.biUnion (hits m) := by
    intro u _
    obtain ⟨k,hk,hu⟩ := all u (matchCol m u) (matchZero m u)
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
  have hLo := Finset.card_le_card allHit
  have hHi := Finset.card_biUnion_le_card_mul S (hits m) 1 hHit
  simp only [Finset.card_univ, Fintype.card_fin] at hLo
  omega

end PEqualNP.Outside.L_meta_9382

open PEqualNP.Outside.L_meta_9382 in
theorem PEqualNP.Outside.L_meta_9382 : ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 16)), L.length ≤ 14 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 16), (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨l,len,clean,allZero⟩
  obtain ⟨S,size,hS⟩ := normalize l clean
  apply noFourteen S (size.trans len)
  intro p q hpq
  obtain ⟨r,hr,hi,hj⟩ := allZero (orig p) (orig q) hpq
  exact hS r hr p q hi hj
