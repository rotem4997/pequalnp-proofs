import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19035_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Each row occupies 128 consecutive bits of the packed truth table. -/
def mask128 : ℕ := 2 ^ 128 - 1
def mask16384 : ℕ := 2 ^ 16384 - 1
def packRows (rows : List ℕ) : ℕ := rows.foldr (fun row tail => row + (tail <<< 128)) 0
def colPat : ℕ := packRows (List.replicate 128 1)
def rowTbl : List ℕ :=
  [0x0650c16f3fa4242a5a95d09c81a28695,
   0x20c9e05026fb41fc80230c7648146d40,
   0x0230e178464025a11ec4a3d880c385bc,
   0x1ee01731633b061b5299ea78a3a3be12,
   0x26850870804560132e828869106d6009,
   0x1b1ac0034653a6c90c30204934020620,
   0x164028a4101f2e3375271218b9204501,
   0x0048080a008905300441881c86403489,
   0x2623f89917533b28fe56b7f686ea940c,
   0x2c400060021901020021085800209600,
   0xc10026340097dd81a326ea68ba47ac82,
   0x5c2053a6981f2b2d5d0df8997a0ec96f,
   0xb5fbac173e1a96ddb247aa5b6c86269d,
   0xe777f8e41b8b2aa005f55a4eb8078829,
   0x99a8000c890e0585230048d8f0822007,
   0x1070a13b2c1d075cf8b368d9600e80b5,
   0x9246adc828a500658116a4ee92bdbc94,
   0x90402910148d665d26e2c010c8842411,
   0xcb4966df39baf83b5f8879843b192fbd,
   0x0a08084e2aa56021402e5da228060c68,
   0x1410c21b0e1d341193536ccd0c5b8090,
   0xf13b4288070d2811ea012a2902c32a20,
   0x12de405e2ebe232a5871190a60268930,
   0x1538205ca51125c1a20c094170796789,
   0x021a422120b7e41c82b13000000282c0,
   0xb19020402036d41842200a5823ac0c00,
   0x7113f4438f4f0715842b297c3fe09c38,
   0x3f79244b009b0d793e2a69503b0026cc,
   0x974c7035bb3a032e726300ba55262707,
   0xabef655696cdfe7a9a37bf66fd5acd0d,
   0x4e0bc6473eb1ac804a137963120ebee0,
   0xaa40004718b02810646041008b001001,
   0x62402440940600fc12200048c0ae000f,
   0x0040c001150710fc9a42244847ae9306,
   0x180041520c580ea80e32c7e13c420408,
   0xaf54ce206b1a233402df1dfe9f462d02,
   0xf374e25c25dd2198cd641b7178d74790,
   0x0810000824014c304004480881008008,
   0x00a24119276d0cb05a45a2b8c91389c9,
   0xce6841535d5a66e3466aaabf2e6e2d28,
   0x7f1650571e5302eb960c0be428232441,
   0x89d54250b2d9c01094787b6034486081,
   0x4545d414060149216016f064f9082000,
   0x6bfae259249e6a6de3055879f5ff380a,
   0x06484204a48b400818e012091008c108,
   0x716a08d01ea2004090618023e1db280d,
   0x280d825224975389a0c3a44b26aeb100,
   0x00baf85b2d2d23b1d9b61ff4785f2cb9,
   0x190e080c988803072201104ad202a089,
   0x4841201000934410032409003b400820,
   0x1b28e64971b242f94c0f6a497311074c,
   0x4000081a988740a1322a8088a28220cf,
   0x11544444063100f8cc3422683f290400,
   0xcf012c4c16998cf0c006636b8f08b684,
   0x910421d804542104810c892130c52605,
   0x3a9e405f38ba2b1a6e511052d0429d98,
   0xba9063884676200594a4d82971c14264,
   0x97aff5890747af7d1d5dd93fbb8f9ebe,
   0x8beb7103a56b96b5081ba7273d6a740b,
   0x131000240c130244002130623522800a,
   0x1128201a2e0962073ed0a81c04092c83,
   0x6ced7912b3ca0fb1db77fbbfee595d2f,
   0x9018060a490823124e99009800412499,
   0x5430818b3507008c5a17c09f008a8487,
   0xfd2ed185b67b0f747c468b7bdfca9799,
   0x0aa418513be24a29104bf86e390ab54c,
   0xb119e4013b33d4f10663a89d3700aec4,
   0xa0934441267008086222447698a01000,
   0x20000048024901009820089061420008,
   0xb512e5868b2f05340645ac1f75ea440d,
   0x2250d8140cff2e21063373c13d4284c8,
   0x8b50e82c80ba9b3403137558ff0dacc3,
   0x7318bc7d0a5f0fa4b9377bff3d0680ab,
   0xc8a081209180200b1ee0684ca003848d,
   0x73fb4cc92cf3084ae66bec7dafffbcc9,
   0xd27ac00b9c038561d87900a9a6a09359,
   0x3a12c40b0500c699481e682520428608,
   0xa18b220922af571933d324d4b4dbc8fb,
   0x31bcf05c0e796f31673c63df7f4f7f8a,
   0xc11004059009808190ae2b20ac400029,
   0xd430cad31c9f7239dc7b7cc7340a8541,
   0x36fd6c30123f6d3b64ffd856a06666cc,
   0xb55ea62021fe479e2ba3341e30a68407,
   0x3890206a02330104c03838402002f251,
   0x08108a100a154221200390621003b28a,
   0x4025a0b23b1a4b845e63381a465b29a0,
   0x880280122d20428016400c9f382a2090,
   0xa80f29483e17660346e6dd6fbeaf0e38,
   0x363f2ceb8e7c2f715b8148f88966829d,
   0x3e92665b6e7befb95f3f4e59bb03ce48,
   0x8908c2040219812090207b0275460020,
   0x3db4c3a3287c092d1307fff83cc48ccc,
   0x3309cecc48a60b7504096069c76c248a,
   0xc14a6617fbaad73c018d0c1e75601605,
   0x18964015150902624200000061220a04,
   0xb5b07ad01a2fa25090608312e740404e,
   0x6669785cc6cf60218d251bbf385b6d28,
   0xb2b76af45ff72af9d56e4668a86fd421,
   0xb7f4c0e46862217b47412239d7e40420,
   0xd0700404040300c08444aa252c292400,
   0x008c40000260080002093102080e90e0,
   0x9150028a160f855cf7300360f5470192,
   0x8ac1c004d0d725b1a7606168cbe2d027,
   0x92724875141b84448078ba233422220d,
   0x9338204809920401a20a28d8210022c1,
   0x1cf4102b25720b5d5138789c6a1f3012,
   0x4372a640c6150270806928413fabb495,
   0x20230080810422020e81020001230011,
   0x3aa58c342136689bde8f6a0c2b8ba48f,
   0x04201000000002001000001002000002,
   0x676ccaa2bb0e2ce157b5786fd85f918b,
   0x7b33e7b6950c27b432a6a371f5c3069f,
   0x6530304b2e0422075e8a607c2e6d800b,
   0x05100017aa0d4925162b25b1744c6cc9,
   0xc8ff2258b4d7423ad6a1082731ef6fb0,
   0xd86f44d09e360e425a71602987668930,
   0x0147840026124c8042736860128a2809,
   0xa20906112e9e0f08f73b6470f1571c8a,
   0x01d4000802452828083928f03c0a1008,
   0x8068130329370f6367e889e5b4e724da,
   0x22b0804f2da02089424b787a58d38198,
   0x0478e17a804125a1012727c51859549d,
   0xc4643002041127007b142071b2096003,
   0xff5237388717661a53c5c86db9a3d69b,
   0x77b7d931b1682310d1b22873704f6ca6,
   0x2af7a1a081d62a10d1af2b402b2a50f4,
   0xb092f41b0f68061ddfbb2dbe74738c3a,
   0x61fb729203a72c30c9052a442a425861]
def target16384 : ℕ := packRows rowTbl

def gates0 : List Gate := [
  ⟨GateOp.or, [19, 87]⟩,
  ⟨GateOp.or, [43, 74]⟩,
  ⟨GateOp.or, [61, 110]⟩,
  ⟨GateOp.or, [29, 58]⟩,
  ⟨GateOp.or, [18, 93]⟩,
  ⟨GateOp.or, [3, 123]⟩,
  ⟨GateOp.or, [18, 85]⟩,
  ⟨GateOp.or, [21, 127]⟩,
  ⟨GateOp.or, [53, 64]⟩,
  ⟨GateOp.or, [37, 89]⟩,
  ⟨GateOp.or, [45, 95]⟩,
  ⟨GateOp.or, [88, 115]⟩,
  ⟨GateOp.or, [11, 113]⟩,
  ⟨GateOp.or, [22, 55]⟩,
  ⟨GateOp.or, [69, 111]⟩,
  ⟨GateOp.or, [36, 57]⟩,
  ⟨GateOp.or, [29, 96]⟩,
  ⟨GateOp.or, [13, 35]⟩,
  ⟨GateOp.or, [65, 80]⟩,
  ⟨GateOp.or, [1, 89]⟩,
  ⟨GateOp.or, [101, 117]⟩,
  ⟨GateOp.or, [87, 114]⟩,
  ⟨GateOp.or, [13, 97]⟩,
  ⟨GateOp.or, [28, 35]⟩,
  ⟨GateOp.or, [3, 105]⟩,
  ⟨GateOp.or, [73, 108]⟩,
  ⟨GateOp.or, [61, 124]⟩,
  ⟨GateOp.or, [11, 61]⟩,
  ⟨GateOp.or, [71, 74]⟩,
  ⟨GateOp.or, [32, 33]⟩,
  ⟨GateOp.or, [30, 100]⟩,
  ⟨GateOp.or, [107, 125]⟩,
  ⟨GateOp.or, [66, 260]⟩,
  ⟨GateOp.or, [73, 111]⟩,
  ⟨GateOp.or, [33, 75]⟩,
  ⟨GateOp.or, [26, 106]⟩,
  ⟨GateOp.or, [0, 28]⟩,
  ⟨GateOp.or, [9, 261]⟩,
  ⟨GateOp.or, [16, 126]⟩,
  ⟨GateOp.or, [24, 82]⟩
]

def gates1 : List Gate := [
  ⟨GateOp.or, [41, 102]⟩,
  ⟨GateOp.or, [8, 46]⟩,
  ⟨GateOp.or, [20, 77]⟩,
  ⟨GateOp.or, [18, 31]⟩,
  ⟨GateOp.or, [40, 94]⟩,
  ⟨GateOp.or, [59, 103]⟩,
  ⟨GateOp.or, [4, 81]⟩,
  ⟨GateOp.or, [97, 98]⟩,
  ⟨GateOp.or, [58, 93]⟩,
  ⟨GateOp.or, [75, 258]⟩,
  ⟨GateOp.or, [4, 112]⟩,
  ⟨GateOp.or, [30, 264]⟩,
  ⟨GateOp.or, [15, 124]⟩,
  ⟨GateOp.or, [125, 308]⟩,
  ⟨GateOp.or, [1, 12]⟩,
  ⟨GateOp.or, [0, 120]⟩,
  ⟨GateOp.or, [16, 29]⟩,
  ⟨GateOp.or, [50, 106]⟩,
  ⟨GateOp.or, [14, 104]⟩,
  ⟨GateOp.or, [2, 38]⟩,
  ⟨GateOp.or, [30, 116]⟩,
  ⟨GateOp.or, [67, 117]⟩,
  ⟨GateOp.or, [87, 119]⟩,
  ⟨GateOp.or, [46, 85]⟩,
  ⟨GateOp.or, [15, 101]⟩,
  ⟨GateOp.or, [83, 105]⟩,
  ⟨GateOp.or, [41, 90]⟩,
  ⟨GateOp.or, [56, 91]⟩,
  ⟨GateOp.or, [10, 12]⟩,
  ⟨GateOp.or, [53, 79]⟩,
  ⟨GateOp.or, [52, 99]⟩,
  ⟨GateOp.or, [5, 39]⟩,
  ⟨GateOp.or, [76, 89]⟩,
  ⟨GateOp.or, [6, 70]⟩,
  ⟨GateOp.or, [47, 256]⟩,
  ⟨GateOp.or, [82, 98]⟩,
  ⟨GateOp.or, [71, 102]⟩,
  ⟨GateOp.or, [26, 72]⟩,
  ⟨GateOp.or, [10, 84]⟩,
  ⟨GateOp.or, [12, 120]⟩
]

def gates2 : List Gate := [
  ⟨GateOp.or, [69, 74]⟩,
  ⟨GateOp.or, [54, 271]⟩,
  ⟨GateOp.or, [45, 77]⟩,
  ⟨GateOp.or, [15, 63]⟩,
  ⟨GateOp.or, [75, 103]⟩,
  ⟨GateOp.or, [64, 115]⟩,
  ⟨GateOp.or, [39, 66]⟩,
  ⟨GateOp.or, [25, 87]⟩,
  ⟨GateOp.or, [8, 81]⟩,
  ⟨GateOp.or, [74, 104]⟩,
  ⟨GateOp.or, [27, 125]⟩,
  ⟨GateOp.or, [110, 273]⟩,
  ⟨GateOp.or, [14, 102]⟩,
  ⟨GateOp.or, [119, 276]⟩,
  ⟨GateOp.or, [10, 49]⟩,
  ⟨GateOp.or, [11, 110]⟩,
  ⟨GateOp.or, [0, 57]⟩,
  ⟨GateOp.or, [63, 82]⟩,
  ⟨GateOp.or, [8, 126]⟩,
  ⟨GateOp.or, [79, 126]⟩,
  ⟨GateOp.or, [43, 92]⟩,
  ⟨GateOp.or, [58, 111]⟩,
  ⟨GateOp.or, [17, 111]⟩,
  ⟨GateOp.or, [55, 64]⟩,
  ⟨GateOp.or, [77, 81]⟩,
  ⟨GateOp.or, [43, 61]⟩,
  ⟨GateOp.or, [65, 280]⟩,
  ⟨GateOp.or, [60, 78]⟩,
  ⟨GateOp.or, [38, 91]⟩,
  ⟨GateOp.or, [18, 60]⟩,
  ⟨GateOp.or, [365, 62]⟩,
  ⟨GateOp.or, [366, 107]⟩,
  ⟨GateOp.or, [367, 281]⟩,
  ⟨GateOp.or, [368, 306]⟩,
  ⟨GateOp.or, [17, 42]⟩,
  ⟨GateOp.or, [370, 46]⟩,
  ⟨GateOp.or, [371, 51]⟩,
  ⟨GateOp.or, [372, 302]⟩,
  ⟨GateOp.or, [373, 334]⟩,
  ⟨GateOp.or, [7, 16]⟩
]

def gates3 : List Gate := [
  ⟨GateOp.or, [375, 48]⟩,
  ⟨GateOp.or, [376, 51]⟩,
  ⟨GateOp.or, [377, 53]⟩,
  ⟨GateOp.or, [378, 92]⟩,
  ⟨GateOp.or, [379, 284]⟩,
  ⟨GateOp.or, [17, 31]⟩,
  ⟨GateOp.or, [381, 73]⟩,
  ⟨GateOp.or, [382, 80]⟩,
  ⟨GateOp.or, [383, 278]⟩,
  ⟨GateOp.or, [384, 296]⟩,
  ⟨GateOp.or, [32, 51]⟩,
  ⟨GateOp.or, [386, 79]⟩,
  ⟨GateOp.or, [387, 289]⟩,
  ⟨GateOp.or, [388, 305]⟩,
  ⟨GateOp.or, [17, 105]⟩,
  ⟨GateOp.or, [390, 285]⟩,
  ⟨GateOp.or, [391, 310]⟩,
  ⟨GateOp.or, [392, 320]⟩,
  ⟨GateOp.or, [4, 23]⟩,
  ⟨GateOp.or, [394, 44]⟩,
  ⟨GateOp.or, [395, 69]⟩,
  ⟨GateOp.or, [396, 96]⟩,
  ⟨GateOp.or, [397, 121]⟩,
  ⟨GateOp.or, [398, 268]⟩,
  ⟨GateOp.or, [44, 46]⟩,
  ⟨GateOp.or, [400, 77]⟩,
  ⟨GateOp.or, [401, 114]⟩,
  ⟨GateOp.or, [402, 260]⟩,
  ⟨GateOp.or, [403, 295]⟩,
  ⟨GateOp.or, [24, 66]⟩,
  ⟨GateOp.or, [405, 70]⟩,
  ⟨GateOp.or, [406, 284]⟩,
  ⟨GateOp.or, [407, 286]⟩,
  ⟨GateOp.or, [408, 364]⟩,
  ⟨GateOp.or, [51, 108]⟩,
  ⟨GateOp.or, [410, 285]⟩,
  ⟨GateOp.or, [411, 348]⟩,
  ⟨GateOp.or, [412, 353]⟩,
  ⟨GateOp.or, [8, 111]⟩,
  ⟨GateOp.or, [414, 263]⟩
]

def gates4 : List Gate := [
  ⟨GateOp.or, [415, 278]⟩,
  ⟨GateOp.or, [416, 287]⟩,
  ⟨GateOp.or, [67, 69]⟩,
  ⟨GateOp.or, [418, 82]⟩,
  ⟨GateOp.or, [419, 86]⟩,
  ⟨GateOp.or, [420, 294]⟩,
  ⟨GateOp.or, [421, 304]⟩,
  ⟨GateOp.or, [22, 44]⟩,
  ⟨GateOp.or, [423, 290]⟩,
  ⟨GateOp.or, [424, 315]⟩,
  ⟨GateOp.or, [425, 341]⟩,
  ⟨GateOp.or, [57, 95]⟩,
  ⟨GateOp.or, [427, 109]⟩,
  ⟨GateOp.or, [428, 112]⟩,
  ⟨GateOp.or, [429, 122]⟩,
  ⟨GateOp.or, [430, 280]⟩,
  ⟨GateOp.or, [431, 283]⟩,
  ⟨GateOp.or, [22, 57]⟩,
  ⟨GateOp.or, [433, 72]⟩,
  ⟨GateOp.or, [434, 90]⟩,
  ⟨GateOp.or, [435, 256]⟩,
  ⟨GateOp.or, [436, 286]⟩,
  ⟨GateOp.or, [114, 123]⟩,
  ⟨GateOp.or, [438, 267]⟩,
  ⟨GateOp.or, [439, 287]⟩,
  ⟨GateOp.or, [440, 291]⟩,
  ⟨GateOp.or, [83, 84]⟩,
  ⟨GateOp.or, [442, 293]⟩,
  ⟨GateOp.or, [443, 307]⟩,
  ⟨GateOp.or, [33, 50]⟩,
  ⟨GateOp.or, [445, 94]⟩,
  ⟨GateOp.or, [446, 288]⟩,
  ⟨GateOp.or, [447, 292]⟩,
  ⟨GateOp.or, [62, 86]⟩,
  ⟨GateOp.or, [449, 279]⟩,
  ⟨GateOp.or, [450, 314]⟩,
  ⟨GateOp.or, [451, 342]⟩,
  ⟨GateOp.or, [23, 36]⟩,
  ⟨GateOp.or, [453, 38]⟩,
  ⟨GateOp.or, [454, 50]⟩
]

def gates5 : List Gate := [
  ⟨GateOp.or, [455, 85]⟩,
  ⟨GateOp.or, [456, 120]⟩,
  ⟨GateOp.or, [457, 258]⟩,
  ⟨GateOp.or, [25, 58]⟩,
  ⟨GateOp.or, [459, 71]⟩,
  ⟨GateOp.or, [460, 288]⟩,
  ⟨GateOp.or, [461, 324]⟩,
  ⟨GateOp.or, [6, 64]⟩,
  ⟨GateOp.or, [463, 80]⟩,
  ⟨GateOp.or, [464, 101]⟩,
  ⟨GateOp.or, [465, 262]⟩,
  ⟨GateOp.or, [466, 351]⟩,
  ⟨GateOp.or, [16, 54]⟩,
  ⟨GateOp.or, [468, 57]⟩,
  ⟨GateOp.or, [469, 63]⟩,
  ⟨GateOp.or, [470, 270]⟩,
  ⟨GateOp.or, [471, 323]⟩,
  ⟨GateOp.or, [3, 35]⟩,
  ⟨GateOp.or, [473, 62]⟩,
  ⟨GateOp.or, [474, 89]⟩,
  ⟨GateOp.or, [475, 92]⟩,
  ⟨GateOp.or, [476, 93]⟩,
  ⟨GateOp.or, [477, 313]⟩,
  ⟨GateOp.or, [8, 31]⟩,
  ⟨GateOp.or, [479, 257]⟩,
  ⟨GateOp.or, [480, 317]⟩,
  ⟨GateOp.or, [481, 359]⟩,
  ⟨GateOp.or, [29, 48]⟩,
  ⟨GateOp.or, [483, 55]⟩,
  ⟨GateOp.or, [484, 115]⟩,
  ⟨GateOp.or, [485, 277]⟩,
  ⟨GateOp.or, [486, 300]⟩,
  ⟨GateOp.or, [2, 91]⟩,
  ⟨GateOp.or, [488, 121]⟩,
  ⟨GateOp.or, [489, 289]⟩,
  ⟨GateOp.or, [490, 309]⟩,
  ⟨GateOp.or, [41, 42]⟩,
  ⟨GateOp.or, [492, 52]⟩,
  ⟨GateOp.or, [493, 110]⟩,
  ⟨GateOp.or, [494, 116]⟩
]

def gates6 : List Gate := [
  ⟨GateOp.or, [495, 118]⟩,
  ⟨GateOp.or, [496, 122]⟩,
  ⟨GateOp.or, [497, 312]⟩,
  ⟨GateOp.or, [16, 102]⟩,
  ⟨GateOp.or, [499, 290]⟩,
  ⟨GateOp.or, [500, 291]⟩,
  ⟨GateOp.or, [501, 297]⟩,
  ⟨GateOp.or, [6, 292]⟩,
  ⟨GateOp.or, [503, 293]⟩,
  ⟨GateOp.or, [504, 331]⟩,
  ⟨GateOp.or, [41, 60]⟩,
  ⟨GateOp.or, [506, 86]⟩,
  ⟨GateOp.or, [507, 108]⟩,
  ⟨GateOp.or, [508, 113]⟩,
  ⟨GateOp.or, [509, 114]⟩,
  ⟨GateOp.or, [510, 262]⟩,
  ⟨GateOp.or, [95, 101]⟩,
  ⟨GateOp.or, [512, 259]⟩,
  ⟨GateOp.or, [513, 322]⟩,
  ⟨GateOp.or, [514, 325]⟩,
  ⟨GateOp.or, [74, 92]⟩,
  ⟨GateOp.or, [516, 266]⟩,
  ⟨GateOp.or, [517, 267]⟩,
  ⟨GateOp.or, [518, 303]⟩,
  ⟨GateOp.or, [18, 47]⟩,
  ⟨GateOp.or, [520, 105]⟩,
  ⟨GateOp.or, [521, 121]⟩,
  ⟨GateOp.or, [522, 294]⟩,
  ⟨GateOp.or, [523, 298]⟩,
  ⟨GateOp.or, [0, 2]⟩,
  ⟨GateOp.or, [525, 261]⟩,
  ⟨GateOp.or, [526, 318]⟩,
  ⟨GateOp.or, [527, 358]⟩,
  ⟨GateOp.or, [57, 65]⟩,
  ⟨GateOp.or, [529, 78]⟩,
  ⟨GateOp.or, [530, 97]⟩,
  ⟨GateOp.or, [531, 100]⟩,
  ⟨GateOp.or, [532, 105]⟩,
  ⟨GateOp.or, [533, 118]⟩,
  ⟨GateOp.or, [534, 125]⟩
]

def gates7 : List Gate := [
  ⟨GateOp.or, [43, 50]⟩,
  ⟨GateOp.or, [536, 76]⟩,
  ⟨GateOp.or, [537, 123]⟩,
  ⟨GateOp.or, [538, 256]⟩,
  ⟨GateOp.or, [539, 265]⟩,
  ⟨GateOp.or, [72, 85]⟩,
  ⟨GateOp.or, [541, 295]⟩,
  ⟨GateOp.or, [542, 301]⟩,
  ⟨GateOp.or, [543, 321]⟩,
  ⟨GateOp.or, [4, 114]⟩,
  ⟨GateOp.or, [545, 259]⟩,
  ⟨GateOp.or, [546, 282]⟩,
  ⟨GateOp.or, [547, 296]⟩,
  ⟨GateOp.or, [29, 33]⟩,
  ⟨GateOp.or, [549, 71]⟩,
  ⟨GateOp.or, [550, 80]⟩,
  ⟨GateOp.or, [551, 297]⟩,
  ⟨GateOp.or, [552, 298]⟩,
  ⟨GateOp.or, [30, 115]⟩,
  ⟨GateOp.or, [554, 262]⟩,
  ⟨GateOp.or, [555, 263]⟩,
  ⟨GateOp.or, [556, 283]⟩,
  ⟨GateOp.or, [35, 49]⟩,
  ⟨GateOp.or, [558, 299]⟩,
  ⟨GateOp.or, [559, 332]⟩,
  ⟨GateOp.or, [560, 346]⟩,
  ⟨GateOp.or, [19, 30]⟩,
  ⟨GateOp.or, [562, 269]⟩,
  ⟨GateOp.or, [563, 299]⟩,
  ⟨GateOp.or, [564, 311]⟩,
  ⟨GateOp.or, [23, 97]⟩,
  ⟨GateOp.or, [566, 300]⟩,
  ⟨GateOp.or, [567, 301]⟩,
  ⟨GateOp.or, [568, 326]⟩,
  ⟨GateOp.or, [88, 108]⟩,
  ⟨GateOp.or, [570, 124]⟩,
  ⟨GateOp.or, [571, 302]⟩,
  ⟨GateOp.or, [572, 347]⟩,
  ⟨GateOp.or, [2, 56]⟩,
  ⟨GateOp.or, [574, 96]⟩
]

def gates8 : List Gate := [
  ⟨GateOp.or, [575, 102]⟩,
  ⟨GateOp.or, [576, 303]⟩,
  ⟨GateOp.or, [577, 327]⟩,
  ⟨GateOp.or, [5, 24]⟩,
  ⟨GateOp.or, [579, 30]⟩,
  ⟨GateOp.or, [580, 57]⟩,
  ⟨GateOp.or, [581, 328]⟩,
  ⟨GateOp.or, [582, 340]⟩,
  ⟨GateOp.or, [7, 121]⟩,
  ⟨GateOp.or, [584, 127]⟩,
  ⟨GateOp.or, [585, 304]⟩,
  ⟨GateOp.or, [586, 305]⟩,
  ⟨GateOp.or, [20, 24]⟩,
  ⟨GateOp.or, [588, 36]⟩,
  ⟨GateOp.or, [589, 80]⟩,
  ⟨GateOp.or, [590, 95]⟩,
  ⟨GateOp.or, [591, 97]⟩,
  ⟨GateOp.or, [592, 263]⟩,
  ⟨GateOp.or, [32, 46]⟩,
  ⟨GateOp.or, [594, 97]⟩,
  ⟨GateOp.or, [595, 306]⟩,
  ⟨GateOp.or, [596, 343]⟩,
  ⟨GateOp.or, [597, 356]⟩,
  ⟨GateOp.or, [39, 63]⟩,
  ⟨GateOp.or, [599, 80]⟩,
  ⟨GateOp.or, [600, 282]⟩,
  ⟨GateOp.or, [601, 307]⟩,
  ⟨GateOp.or, [47, 56]⟩,
  ⟨GateOp.or, [603, 114]⟩,
  ⟨GateOp.or, [604, 309]⟩,
  ⟨GateOp.or, [605, 355]⟩,
  ⟨GateOp.or, [66, 108]⟩,
  ⟨GateOp.or, [607, 310]⟩,
  ⟨GateOp.or, [608, 316]⟩,
  ⟨GateOp.or, [609, 319]⟩,
  ⟨GateOp.or, [74, 112]⟩,
  ⟨GateOp.or, [611, 265]⟩,
  ⟨GateOp.or, [612, 311]⟩,
  ⟨GateOp.or, [613, 339]⟩,
  ⟨GateOp.or, [20, 64]⟩
]

def gates9 : List Gate := [
  ⟨GateOp.or, [615, 86]⟩,
  ⟨GateOp.or, [616, 106]⟩,
  ⟨GateOp.or, [617, 271]⟩,
  ⟨GateOp.or, [618, 335]⟩,
  ⟨GateOp.or, [27, 32]⟩,
  ⟨GateOp.or, [620, 53]⟩,
  ⟨GateOp.or, [621, 88]⟩,
  ⟨GateOp.or, [622, 312]⟩,
  ⟨GateOp.or, [623, 313]⟩,
  ⟨GateOp.or, [56, 83]⟩,
  ⟨GateOp.or, [625, 95]⟩,
  ⟨GateOp.or, [626, 127]⟩,
  ⟨GateOp.or, [627, 275]⟩,
  ⟨GateOp.or, [628, 360]⟩,
  ⟨GateOp.or, [21, 23]⟩,
  ⟨GateOp.or, [630, 27]⟩,
  ⟨GateOp.or, [631, 48]⟩,
  ⟨GateOp.or, [632, 314]⟩,
  ⟨GateOp.or, [633, 363]⟩,
  ⟨GateOp.or, [6, 29]⟩,
  ⟨GateOp.or, [635, 38]⟩,
  ⟨GateOp.or, [636, 57]⟩,
  ⟨GateOp.or, [637, 264]⟩,
  ⟨GateOp.or, [638, 265]⟩,
  ⟨GateOp.or, [68, 72]⟩,
  ⟨GateOp.or, [640, 88]⟩,
  ⟨GateOp.or, [641, 96]⟩,
  ⟨GateOp.or, [642, 118]⟩,
  ⟨GateOp.or, [643, 315]⟩,
  ⟨GateOp.or, [644, 354]⟩,
  ⟨GateOp.or, [12, 61]⟩,
  ⟨GateOp.or, [646, 65]⟩,
  ⟨GateOp.or, [647, 103]⟩,
  ⟨GateOp.or, [648, 266]⟩,
  ⟨GateOp.or, [649, 344]⟩,
  ⟨GateOp.or, [29, 56]⟩,
  ⟨GateOp.or, [651, 68]⟩,
  ⟨GateOp.or, [652, 90]⟩,
  ⟨GateOp.or, [653, 266]⟩,
  ⟨GateOp.or, [654, 276]⟩
]

def gates10 : List Gate := [
  ⟨GateOp.or, [13, 36]⟩,
  ⟨GateOp.or, [656, 44]⟩,
  ⟨GateOp.or, [657, 103]⟩,
  ⟨GateOp.or, [658, 272]⟩,
  ⟨GateOp.or, [659, 329]⟩,
  ⟨GateOp.or, [14, 28]⟩,
  ⟨GateOp.or, [661, 48]⟩,
  ⟨GateOp.or, [662, 64]⟩,
  ⟨GateOp.or, [663, 71]⟩,
  ⟨GateOp.or, [664, 93]⟩,
  ⟨GateOp.or, [665, 268]⟩,
  ⟨GateOp.or, [666, 270]⟩,
  ⟨GateOp.or, [42, 53]⟩,
  ⟨GateOp.or, [668, 267]⟩,
  ⟨GateOp.or, [669, 316]⟩,
  ⟨GateOp.or, [670, 317]⟩,
  ⟨GateOp.or, [19, 40]⟩,
  ⟨GateOp.or, [672, 51]⟩,
  ⟨GateOp.or, [673, 75]⟩,
  ⟨GateOp.or, [674, 80]⟩,
  ⟨GateOp.or, [675, 119]⟩,
  ⟨GateOp.or, [676, 268]⟩,
  ⟨GateOp.or, [7, 60]⟩,
  ⟨GateOp.or, [678, 66]⟩,
  ⟨GateOp.or, [679, 99]⟩,
  ⟨GateOp.or, [680, 318]⟩,
  ⟨GateOp.or, [681, 336]⟩,
  ⟨GateOp.or, [13, 40]⟩,
  ⟨GateOp.or, [683, 42]⟩,
  ⟨GateOp.or, [684, 112]⟩,
  ⟨GateOp.or, [685, 123]⟩,
  ⟨GateOp.or, [686, 127]⟩,
  ⟨GateOp.or, [687, 333]⟩,
  ⟨GateOp.or, [61, 64]⟩,
  ⟨GateOp.or, [689, 269]⟩,
  ⟨GateOp.or, [690, 279]⟩,
  ⟨GateOp.or, [691, 319]⟩,
  ⟨GateOp.or, [62, 75]⟩,
  ⟨GateOp.or, [693, 269]⟩,
  ⟨GateOp.or, [694, 320]⟩
]

def gates11 : List Gate := [
  ⟨GateOp.or, [695, 321]⟩,
  ⟨GateOp.or, [11, 18]⟩,
  ⟨GateOp.or, [697, 30]⟩,
  ⟨GateOp.or, [698, 43]⟩,
  ⟨GateOp.or, [699, 322]⟩,
  ⟨GateOp.or, [700, 323]⟩,
  ⟨GateOp.or, [72, 108]⟩,
  ⟨GateOp.or, [702, 324]⟩,
  ⟨GateOp.or, [703, 325]⟩,
  ⟨GateOp.or, [704, 326]⟩,
  ⟨GateOp.or, [34, 46]⟩,
  ⟨GateOp.or, [706, 86]⟩,
  ⟨GateOp.or, [707, 327]⟩,
  ⟨GateOp.or, [708, 328]⟩,
  ⟨GateOp.or, [709, 357]⟩,
  ⟨GateOp.or, [16, 35]⟩,
  ⟨GateOp.or, [711, 74]⟩,
  ⟨GateOp.or, [712, 91]⟩,
  ⟨GateOp.or, [713, 113]⟩,
  ⟨GateOp.or, [714, 117]⟩,
  ⟨GateOp.or, [715, 330]⟩,
  ⟨GateOp.or, [23, 40]⟩,
  ⟨GateOp.or, [717, 41]⟩,
  ⟨GateOp.or, [718, 54]⟩,
  ⟨GateOp.or, [719, 83]⟩,
  ⟨GateOp.or, [720, 103]⟩,
  ⟨GateOp.or, [721, 106]⟩,
  ⟨GateOp.or, [722, 345]⟩,
  ⟨GateOp.or, [17, 96]⟩,
  ⟨GateOp.or, [724, 97]⟩,
  ⟨GateOp.or, [725, 329]⟩,
  ⟨GateOp.or, [726, 330]⟩,
  ⟨GateOp.or, [78, 91]⟩,
  ⟨GateOp.or, [728, 124]⟩,
  ⟨GateOp.or, [729, 331]⟩,
  ⟨GateOp.or, [730, 337]⟩,
  ⟨GateOp.or, [1, 39]⟩,
  ⟨GateOp.or, [732, 78]⟩,
  ⟨GateOp.or, [733, 114]⟩,
  ⟨GateOp.or, [734, 272]⟩
]

def gates12 : List Gate := [
  ⟨GateOp.or, [735, 274]⟩,
  ⟨GateOp.or, [42, 78]⟩,
  ⟨GateOp.or, [737, 90]⟩,
  ⟨GateOp.or, [738, 92]⟩,
  ⟨GateOp.or, [739, 98]⟩,
  ⟨GateOp.or, [740, 270]⟩,
  ⟨GateOp.or, [741, 332]⟩,
  ⟨GateOp.or, [9, 27]⟩,
  ⟨GateOp.or, [743, 36]⟩,
  ⟨GateOp.or, [744, 68]⟩,
  ⟨GateOp.or, [745, 275]⟩,
  ⟨GateOp.or, [746, 333]⟩,
  ⟨GateOp.or, [110, 111]⟩,
  ⟨GateOp.or, [748, 123]⟩,
  ⟨GateOp.or, [749, 334]⟩,
  ⟨GateOp.or, [750, 349]⟩,
  ⟨GateOp.or, [25, 67]⟩,
  ⟨GateOp.or, [752, 91]⟩,
  ⟨GateOp.or, [753, 98]⟩,
  ⟨GateOp.or, [754, 257]⟩,
  ⟨GateOp.or, [755, 335]⟩,
  ⟨GateOp.or, [12, 64]⟩,
  ⟨GateOp.or, [757, 116]⟩,
  ⟨GateOp.or, [758, 123]⟩,
  ⟨GateOp.or, [759, 336]⟩,
  ⟨GateOp.or, [760, 338]⟩,
  ⟨GateOp.or, [21, 56]⟩,
  ⟨GateOp.or, [762, 123]⟩,
  ⟨GateOp.or, [763, 277]⟩,
  ⟨GateOp.or, [764, 337]⟩,
  ⟨GateOp.or, [61, 117]⟩,
  ⟨GateOp.or, [766, 257]⟩,
  ⟨GateOp.or, [767, 272]⟩,
  ⟨GateOp.or, [768, 338]⟩,
  ⟨GateOp.or, [47, 60]⟩,
  ⟨GateOp.or, [770, 80]⟩,
  ⟨GateOp.or, [771, 122]⟩,
  ⟨GateOp.or, [772, 259]⟩,
  ⟨GateOp.or, [773, 339]⟩,
  ⟨GateOp.or, [39, 98]⟩
]

def gates13 : List Gate := [
  ⟨GateOp.or, [775, 99]⟩,
  ⟨GateOp.or, [776, 119]⟩,
  ⟨GateOp.or, [777, 340]⟩,
  ⟨GateOp.or, [778, 341]⟩,
  ⟨GateOp.or, [45, 96]⟩,
  ⟨GateOp.or, [780, 99]⟩,
  ⟨GateOp.or, [781, 106]⟩,
  ⟨GateOp.or, [782, 114]⟩,
  ⟨GateOp.or, [783, 122]⟩,
  ⟨GateOp.or, [784, 257]⟩,
  ⟨GateOp.or, [89, 116]⟩,
  ⟨GateOp.or, [786, 342]⟩,
  ⟨GateOp.or, [787, 343]⟩,
  ⟨GateOp.or, [788, 350]⟩,
  ⟨GateOp.or, [42, 258]⟩,
  ⟨GateOp.or, [790, 273]⟩,
  ⟨GateOp.or, [791, 344]⟩,
  ⟨GateOp.or, [792, 352]⟩,
  ⟨GateOp.or, [50, 127]⟩,
  ⟨GateOp.or, [794, 274]⟩,
  ⟨GateOp.or, [795, 345]⟩,
  ⟨GateOp.or, [796, 346]⟩,
  ⟨GateOp.or, [48, 72]⟩,
  ⟨GateOp.or, [798, 84]⟩,
  ⟨GateOp.or, [799, 274]⟩,
  ⟨GateOp.or, [800, 347]⟩,
  ⟨GateOp.or, [29, 34]⟩,
  ⟨GateOp.or, [802, 67]⟩,
  ⟨GateOp.or, [803, 74]⟩,
  ⟨GateOp.or, [804, 97]⟩,
  ⟨GateOp.or, [805, 121]⟩,
  ⟨GateOp.or, [806, 275]⟩,
  ⟨GateOp.or, [10, 77]⟩,
  ⟨GateOp.or, [808, 122]⟩,
  ⟨GateOp.or, [809, 348]⟩,
  ⟨GateOp.or, [810, 349]⟩,
  ⟨GateOp.or, [36, 93]⟩,
  ⟨GateOp.or, [812, 96]⟩,
  ⟨GateOp.or, [813, 127]⟩,
  ⟨GateOp.or, [814, 350]⟩
]

def gates14 : List Gate := [
  ⟨GateOp.or, [815, 361]⟩,
  ⟨GateOp.or, [28, 47]⟩,
  ⟨GateOp.or, [817, 58]⟩,
  ⟨GateOp.or, [818, 119]⟩,
  ⟨GateOp.or, [819, 124]⟩,
  ⟨GateOp.or, [820, 362]⟩,
  ⟨GateOp.or, [13, 26]⟩,
  ⟨GateOp.or, [822, 49]⟩,
  ⟨GateOp.or, [823, 57]⟩,
  ⟨GateOp.or, [824, 77]⟩,
  ⟨GateOp.or, [825, 96]⟩,
  ⟨GateOp.or, [826, 277]⟩,
  ⟨GateOp.or, [10, 71]⟩,
  ⟨GateOp.or, [828, 72]⟩,
  ⟨GateOp.or, [829, 105]⟩,
  ⟨GateOp.or, [830, 278]⟩,
  ⟨GateOp.or, [831, 351]⟩,
  ⟨GateOp.or, [76, 281]⟩,
  ⟨GateOp.or, [833, 352]⟩,
  ⟨GateOp.or, [834, 353]⟩,
  ⟨GateOp.or, [835, 354]⟩,
  ⟨GateOp.or, [26, 39]⟩,
  ⟨GateOp.or, [837, 58]⟩,
  ⟨GateOp.or, [838, 76]⟩,
  ⟨GateOp.or, [839, 112]⟩,
  ⟨GateOp.or, [840, 113]⟩,
  ⟨GateOp.or, [841, 120]⟩,
  ⟨GateOp.or, [842, 355]⟩,
  ⟨GateOp.or, [59, 72]⟩,
  ⟨GateOp.or, [844, 279]⟩,
  ⟨GateOp.or, [845, 356]⟩,
  ⟨GateOp.or, [846, 357]⟩,
  ⟨GateOp.or, [6, 12]⟩,
  ⟨GateOp.or, [848, 15]⟩,
  ⟨GateOp.or, [849, 28]⟩,
  ⟨GateOp.or, [850, 72]⟩,
  ⟨GateOp.or, [851, 82]⟩,
  ⟨GateOp.or, [852, 358]⟩,
  ⟨GateOp.or, [7, 47]⟩,
  ⟨GateOp.or, [854, 62]⟩
]

def gates15 : List Gate := [
  ⟨GateOp.or, [855, 78]⟩,
  ⟨GateOp.or, [856, 88]⟩,
  ⟨GateOp.or, [857, 359]⟩,
  ⟨GateOp.or, [858, 360]⟩,
  ⟨GateOp.or, [14, 91]⟩,
  ⟨GateOp.or, [860, 281]⟩,
  ⟨GateOp.or, [861, 361]⟩,
  ⟨GateOp.or, [862, 362]⟩,
  ⟨GateOp.or, [3, 71]⟩,
  ⟨GateOp.or, [864, 77]⟩,
  ⟨GateOp.or, [865, 117]⟩,
  ⟨GateOp.or, [866, 126]⟩,
  ⟨GateOp.or, [867, 282]⟩,
  ⟨GateOp.or, [868, 363]⟩,
  ⟨GateOp.or, [39, 64]⟩,
  ⟨GateOp.or, [870, 259]⟩,
  ⟨GateOp.or, [871, 283]⟩,
  ⟨GateOp.or, [872, 364]⟩,
  ⟨GateOp.or, [195, 212]⟩,
  ⟨GateOp.or, [202, 244]⟩,
  ⟨GateOp.or, [150, 168]⟩,
  ⟨GateOp.or, [163, 219]⟩,
  ⟨GateOp.or, [188, 224]⟩,
  ⟨GateOp.or, [178, 237]⟩,
  ⟨GateOp.or, [196, 234]⟩,
  ⟨GateOp.or, [138, 186]⟩,
  ⟨GateOp.or, [197, 228]⟩,
  ⟨GateOp.or, [154, 217]⟩,
  ⟨GateOp.or, [156, 166]⟩,
  ⟨GateOp.or, [174, 203]⟩,
  ⟨GateOp.or, [157, 171]⟩,
  ⟨GateOp.or, [176, 210]⟩,
  ⟨GateOp.or, [168, 169]⟩,
  ⟨GateOp.or, [250, 878]⟩,
  ⟨GateOp.or, [181, 208]⟩,
  ⟨GateOp.or, [149, 193]⟩,
  ⟨GateOp.or, [195, 228]⟩,
  ⟨GateOp.or, [244, 252]⟩,
  ⟨GateOp.or, [185, 202]⟩,
  ⟨GateOp.or, [225, 877]⟩
]

def gates16 : List Gate := [
  ⟨GateOp.or, [253, 880]⟩,
  ⟨GateOp.or, [197, 238]⟩,
  ⟨GateOp.or, [187, 874]⟩,
  ⟨GateOp.or, [165, 249]⟩,
  ⟨GateOp.or, [145, 209]⟩,
  ⟨GateOp.or, [157, 218]⟩,
  ⟨GateOp.or, [137, 166]⟩,
  ⟨GateOp.or, [163, 192]⟩,
  ⟨GateOp.or, [186, 205]⟩,
  ⟨GateOp.or, [169, 252]⟩,
  ⟨GateOp.or, [144, 199]⟩,
  ⟨GateOp.or, [153, 190]⟩,
  ⟨GateOp.or, [152, 196]⟩,
  ⟨GateOp.or, [143, 239]⟩,
  ⟨GateOp.or, [164, 185]⟩,
  ⟨GateOp.or, [146, 243]⟩,
  ⟨GateOp.or, [246, 891]⟩,
  ⟨GateOp.or, [158, 247]⟩,
  ⟨GateOp.or, [164, 211]⟩,
  ⟨GateOp.or, [181, 188]⟩,
  ⟨GateOp.or, [175, 232]⟩,
  ⟨GateOp.or, [214, 238]⟩,
  ⟨GateOp.or, [150, 176]⟩,
  ⟨GateOp.or, [167, 219]⟩,
  ⟨GateOp.or, [201, 236]⟩,
  ⟨GateOp.or, [160, 212]⟩,
  ⟨GateOp.or, [234, 240]⟩,
  ⟨GateOp.or, [160, 243]⟩,
  ⟨GateOp.or, [131, 885]⟩,
  ⟨GateOp.or, [248, 883]⟩,
  ⟨GateOp.or, [181, 212]⟩,
  ⟨GateOp.or, [172, 884]⟩,
  ⟨GateOp.or, [200, 876]⟩,
  ⟨GateOp.or, [142, 190]⟩,
  ⟨GateOp.or, [154, 194]⟩,
  ⟨GateOp.or, [190, 228]⟩,
  ⟨GateOp.or, [190, 227]⟩,
  ⟨GateOp.or, [212, 251]⟩,
  ⟨GateOp.or, [151, 210]⟩,
  ⟨GateOp.or, [182, 209]⟩
]

def gates17 : List Gate := [
  ⟨GateOp.or, [147, 160]⟩,
  ⟨GateOp.or, [166, 173]⟩,
  ⟨GateOp.or, [170, 177]⟩,
  ⟨GateOp.or, [166, 230]⟩,
  ⟨GateOp.or, [141, 221]⟩,
  ⟨GateOp.or, [209, 237]⟩,
  ⟨GateOp.or, [145, 216]⟩,
  ⟨GateOp.or, [215, 243]⟩,
  ⟨GateOp.or, [186, 188]⟩,
  ⟨GateOp.or, [205, 210]⟩,
  ⟨GateOp.or, [156, 211]⟩,
  ⟨GateOp.or, [139, 165]⟩,
  ⟨GateOp.or, [230, 882]⟩,
  ⟨GateOp.or, [213, 230]⟩,
  ⟨GateOp.or, [143, 238]⟩,
  ⟨GateOp.or, [164, 167]⟩,
  ⟨GateOp.or, [152, 899]⟩,
  ⟨GateOp.or, [198, 893]⟩,
  ⟨GateOp.or, [157, 217]⟩,
  ⟨GateOp.or, [177, 239]⟩,
  ⟨GateOp.or, [135, 210]⟩,
  ⟨GateOp.or, [180, 882]⟩,
  ⟨GateOp.or, [875, 881]⟩,
  ⟨GateOp.or, [145, 887]⟩,
  ⟨GateOp.or, [146, 184]⟩,
  ⟨GateOp.or, [128, 225]⟩,
  ⟨GateOp.or, [154, 876]⟩,
  ⟨GateOp.or, [192, 923]⟩,
  ⟨GateOp.or, [139, 913]⟩,
  ⟨GateOp.or, [143, 217]⟩,
  ⟨GateOp.or, [131, 179]⟩,
  ⟨GateOp.or, [181, 925]⟩,
  ⟨GateOp.or, [202, 228]⟩,
  ⟨GateOp.or, [209, 892]⟩,
  ⟨GateOp.or, [161, 176]⟩,
  ⟨GateOp.or, [879, 928]⟩,
  ⟨GateOp.or, [205, 249]⟩,
  ⟨GateOp.or, [238, 241]⟩,
  ⟨GateOp.or, [879, 929]⟩,
  ⟨GateOp.or, [237, 895]⟩
]

def gates18 : List Gate := [
  ⟨GateOp.or, [128, 220]⟩,
  ⟨GateOp.or, [131, 223]⟩,
  ⟨GateOp.or, [149, 241]⟩,
  ⟨GateOp.or, [130, 934]⟩,
  ⟨GateOp.or, [185, 193]⟩,
  ⟨GateOp.or, [140, 208]⟩,
  ⟨GateOp.or, [138, 176]⟩,
  ⟨GateOp.or, [206, 228]⟩,
  ⟨GateOp.or, [207, 248]⟩,
  ⟨GateOp.or, [255, 984]⟩,
  ⟨GateOp.or, [231, 252]⟩,
  ⟨GateOp.or, [140, 203]⟩,
  ⟨GateOp.or, [145, 242]⟩,
  ⟨GateOp.or, [214, 247]⟩,
  ⟨GateOp.or, [219, 949]⟩,
  ⟨GateOp.or, [137, 224]⟩,
  ⟨GateOp.or, [190, 220]⟩,
  ⟨GateOp.or, [250, 936]⟩,
  ⟨GateOp.or, [191, 244]⟩,
  ⟨GateOp.or, [163, 218]⟩,
  ⟨GateOp.or, [174, 932]⟩,
  ⟨GateOp.or, [135, 239]⟩,
  ⟨GateOp.or, [134, 213]⟩,
  ⟨GateOp.or, [141, 189]⟩,
  ⟨GateOp.or, [192, 227]⟩,
  ⟨GateOp.or, [197, 202]⟩,
  ⟨GateOp.or, [145, 217]⟩,
  ⟨GateOp.or, [130, 220]⟩,
  ⟨GateOp.or, [158, 194]⟩,
  ⟨GateOp.or, [226, 946]⟩,
  ⟨GateOp.or, [192, 208]⟩,
  ⟨GateOp.or, [171, 182]⟩,
  ⟨GateOp.or, [154, 208]⟩,
  ⟨GateOp.or, [136, 221]⟩,
  ⟨GateOp.or, [161, 935]⟩,
  ⟨GateOp.or, [233, 238]⟩,
  ⟨GateOp.or, [201, 251]⟩,
  ⟨GateOp.or, [200, 242]⟩,
  ⟨GateOp.or, [248, 252]⟩,
  ⟨GateOp.or, [138, 161]⟩
]

def gates19 : List Gate := [
  ⟨GateOp.or, [152, 158]⟩,
  ⟨GateOp.or, [173, 226]⟩,
  ⟨GateOp.or, [171, 253]⟩,
  ⟨GateOp.or, [165, 884]⟩,
  ⟨GateOp.or, [195, 221]⟩,
  ⟨GateOp.or, [247, 253]⟩,
  ⟨GateOp.or, [165, 218]⟩,
  ⟨GateOp.or, [147, 180]⟩,
  ⟨GateOp.or, [160, 255]⟩,
  ⟨GateOp.or, [171, 206]⟩,
  ⟨GateOp.or, [159, 178]⟩,
  ⟨GateOp.or, [245, 937]⟩,
  ⟨GateOp.or, [159, 189]⟩,
  ⟨GateOp.or, [215, 886]⟩,
  ⟨GateOp.or, [133, 139]⟩,
  ⟨GateOp.or, [156, 208]⟩,
  ⟨GateOp.or, [157, 941]⟩,
  ⟨GateOp.or, [163, 229]⟩,
  ⟨GateOp.or, [150, 165]⟩,
  ⟨GateOp.or, [200, 914]⟩,
  ⟨GateOp.or, [129, 144]⟩,
  ⟨GateOp.or, [201, 914]⟩,
  ⟨GateOp.or, [131, 245]⟩,
  ⟨GateOp.or, [148, 943]⟩,
  ⟨GateOp.or, [138, 890]⟩,
  ⟨GateOp.or, [244, 906]⟩,
  ⟨GateOp.or, [180, 217]⟩,
  ⟨GateOp.or, [889, 895]⟩,
  ⟨GateOp.or, [211, 918]⟩,
  ⟨GateOp.or, [190, 905]⟩,
  ⟨GateOp.or, [187, 195]⟩,
  ⟨GateOp.or, [179, 225]⟩,
  ⟨GateOp.or, [894, 916]⟩,
  ⟨GateOp.or, [128, 241]⟩,
  ⟨GateOp.or, [197, 198]⟩,
  ⟨GateOp.or, [211, 239]⟩,
  ⟨GateOp.or, [205, 241]⟩,
  ⟨GateOp.or, [156, 213]⟩,
  ⟨GateOp.or, [186, 898]⟩,
  ⟨GateOp.or, [881, 898]⟩
]

def gates20 : List Gate := [
  ⟨GateOp.or, [176, 950]⟩,
  ⟨GateOp.or, [174, 903]⟩,
  ⟨GateOp.or, [131, 143]⟩,
  ⟨GateOp.or, [219, 970]⟩,
  ⟨GateOp.or, [216, 910]⟩,
  ⟨GateOp.or, [186, 215]⟩,
  ⟨GateOp.or, [919, 921]⟩,
  ⟨GateOp.or, [924, 957]⟩,
  ⟨GateOp.or, [962, 1063]⟩,
  ⟨GateOp.or, [172, 249]⟩,
  ⟨GateOp.or, [213, 236]⟩,
  ⟨GateOp.or, [245, 253]⟩,
  ⟨GateOp.or, [167, 877]⟩,
  ⟨GateOp.or, [879, 888]⟩,
  ⟨GateOp.or, [875, 901]⟩,
  ⟨GateOp.or, [883, 902]⟩,
  ⟨GateOp.or, [174, 921]⟩,
  ⟨GateOp.or, [181, 874]⟩,
  ⟨GateOp.or, [190, 885]⟩,
  ⟨GateOp.or, [252, 958]⟩,
  ⟨GateOp.or, [912, 1073]⟩,
  ⟨GateOp.or, [922, 1074]⟩,
  ⟨GateOp.or, [875, 896]⟩,
  ⟨GateOp.or, [131, 201]⟩,
  ⟨GateOp.or, [137, 889]⟩,
  ⟨GateOp.or, [155, 960]⟩,
  ⟨GateOp.or, [245, 961]⟩,
  ⟨GateOp.or, [144, 184]⟩,
  ⟨GateOp.or, [187, 188]⟩,
  ⟨GateOp.or, [240, 924]⟩,
  ⟨GateOp.or, [211, 964]⟩,
  ⟨GateOp.or, [201, 874]⟩,
  ⟨GateOp.or, [188, 965]⟩,
  ⟨GateOp.or, [135, 177]⟩,
  ⟨GateOp.or, [152, 249]⟩,
  ⟨GateOp.or, [203, 907]⟩,
  ⟨GateOp.or, [213, 908]⟩,
  ⟨GateOp.or, [150, 198]⟩,
  ⟨GateOp.or, [160, 909]⟩,
  ⟨GateOp.or, [228, 876]⟩
]

def gates21 : List Gate := [
  ⟨GateOp.or, [244, 910]⟩,
  ⟨GateOp.or, [190, 212]⟩,
  ⟨GateOp.or, [195, 205]⟩,
  ⟨GateOp.or, [197, 244]⟩,
  ⟨GateOp.or, [886, 887]⟩,
  ⟨GateOp.or, [911, 912]⟩,
  ⟨GateOp.or, [169, 199]⟩,
  ⟨GateOp.or, [138, 205]⟩,
  ⟨GateOp.or, [971, 1103]⟩,
  ⟨GateOp.or, [142, 184]⟩,
  ⟨GateOp.or, [893, 896]⟩,
  ⟨GateOp.or, [168, 218]⟩,
  ⟨GateOp.or, [252, 894]⟩,
  ⟨GateOp.or, [930, 1107]⟩,
  ⟨GateOp.or, [128, 144]⟩,
  ⟨GateOp.or, [1110, 183]⟩,
  ⟨GateOp.or, [1111, 187]⟩,
  ⟨GateOp.or, [1112, 904]⟩,
  ⟨GateOp.or, [1113, 980]⟩,
  ⟨GateOp.or, [175, 177]⟩,
  ⟨GateOp.or, [1115, 983]⟩,
  ⟨GateOp.or, [1116, 999]⟩,
  ⟨GateOp.or, [1117, 1006]⟩,
  ⟨GateOp.or, [135, 141]⟩,
  ⟨GateOp.or, [1119, 153]⟩,
  ⟨GateOp.or, [1120, 159]⟩,
  ⟨GateOp.or, [1121, 163]⟩,
  ⟨GateOp.or, [1122, 215]⟩,
  ⟨GateOp.or, [1123, 227]⟩,
  ⟨GateOp.or, [1124, 235]⟩,
  ⟨GateOp.or, [174, 181]⟩,
  ⟨GateOp.or, [1126, 182]⟩,
  ⟨GateOp.or, [1127, 255]⟩,
  ⟨GateOp.or, [1128, 976]⟩,
  ⟨GateOp.or, [1129, 1061]⟩,
  ⟨GateOp.or, [159, 254]⟩,
  ⟨GateOp.or, [1131, 915]⟩,
  ⟨GateOp.or, [1132, 976]⟩,
  ⟨GateOp.or, [1133, 977]⟩,
  ⟨GateOp.or, [146, 195]⟩
]

def gates22 : List Gate := [
  ⟨GateOp.or, [1135, 196]⟩,
  ⟨GateOp.or, [1136, 198]⟩,
  ⟨GateOp.or, [1137, 218]⟩,
  ⟨GateOp.or, [1138, 246]⟩,
  ⟨GateOp.or, [1139, 1004]⟩,
  ⟨GateOp.or, [142, 977]⟩,
  ⟨GateOp.or, [1141, 993]⟩,
  ⟨GateOp.or, [1142, 1031]⟩,
  ⟨GateOp.or, [183, 206]⟩,
  ⟨GateOp.or, [1144, 209]⟩,
  ⟨GateOp.or, [1145, 233]⟩,
  ⟨GateOp.or, [1146, 943]⟩,
  ⟨GateOp.or, [1147, 1020]⟩,
  ⟨GateOp.or, [135, 173]⟩,
  ⟨GateOp.or, [1149, 185]⟩,
  ⟨GateOp.or, [1150, 998]⟩,
  ⟨GateOp.or, [1151, 1056]⟩,
  ⟨GateOp.or, [129, 163]⟩,
  ⟨GateOp.or, [1153, 185]⟩,
  ⟨GateOp.or, [1154, 199]⟩,
  ⟨GateOp.or, [1155, 900]⟩,
  ⟨GateOp.or, [1156, 979]⟩,
  ⟨GateOp.or, [169, 231]⟩,
  ⟨GateOp.or, [1158, 240]⟩,
  ⟨GateOp.or, [1159, 942]⟩,
  ⟨GateOp.or, [1160, 1052]⟩,
  ⟨GateOp.or, [1161, 1067]⟩,
  ⟨GateOp.or, [161, 162]⟩,
  ⟨GateOp.or, [1163, 170]⟩,
  ⟨GateOp.or, [1164, 255]⟩,
  ⟨GateOp.or, [1165, 978]⟩,
  ⟨GateOp.or, [1166, 1053]⟩,
  ⟨GateOp.or, [136, 182]⟩,
  ⟨GateOp.or, [1168, 950]⟩,
  ⟨GateOp.or, [1169, 995]⟩,
  ⟨GateOp.or, [1170, 1084]⟩,
  ⟨GateOp.or, [129, 153]⟩,
  ⟨GateOp.or, [1172, 164]⟩,
  ⟨GateOp.or, [1173, 188]⟩,
  ⟨GateOp.or, [1174, 245]⟩
]

def gates23 : List Gate := [
  ⟨GateOp.or, [1175, 250]⟩,
  ⟨GateOp.or, [1176, 920]⟩,
  ⟨GateOp.or, [133, 161]⟩,
  ⟨GateOp.or, [1178, 168]⟩,
  ⟨GateOp.or, [1179, 172]⟩,
  ⟨GateOp.or, [1180, 911]⟩,
  ⟨GateOp.or, [1181, 1002]⟩,
  ⟨GateOp.or, [132, 152]⟩,
  ⟨GateOp.or, [1183, 201]⟩,
  ⟨GateOp.or, [1184, 223]⟩,
  ⟨GateOp.or, [1185, 887]⟩,
  ⟨GateOp.or, [1186, 978]⟩,
  ⟨GateOp.or, [902, 933]⟩,
  ⟨GateOp.or, [1188, 965]⟩,
  ⟨GateOp.or, [1189, 981]⟩,
  ⟨GateOp.or, [152, 216]⟩,
  ⟨GateOp.or, [1191, 897]⟩,
  ⟨GateOp.or, [1192, 991]⟩,
  ⟨GateOp.or, [1193, 1003]⟩,
  ⟨GateOp.or, [141, 255]⟩,
  ⟨GateOp.or, [1195, 1060]⟩,
  ⟨GateOp.or, [1196, 1068]⟩,
  ⟨GateOp.or, [148, 158]⟩,
  ⟨GateOp.or, [1198, 216]⟩,
  ⟨GateOp.or, [1199, 245]⟩,
  ⟨GateOp.or, [1200, 906]⟩,
  ⟨GateOp.or, [1201, 1009]⟩,
  ⟨GateOp.or, [138, 204]⟩,
  ⟨GateOp.or, [1203, 985]⟩,
  ⟨GateOp.or, [1204, 1032]⟩,
  ⟨GateOp.or, [136, 209]⟩,
  ⟨GateOp.or, [1206, 211]⟩,
  ⟨GateOp.or, [1207, 231]⟩,
  ⟨GateOp.or, [1208, 944]⟩,
  ⟨GateOp.or, [1209, 992]⟩,
  ⟨GateOp.or, [178, 194]⟩,
  ⟨GateOp.or, [1211, 916]⟩,
  ⟨GateOp.or, [1212, 979]⟩,
  ⟨GateOp.or, [1213, 986]⟩,
  ⟨GateOp.or, [179, 201]⟩
]

def gates24 : List Gate := [
  ⟨GateOp.or, [1215, 222]⟩,
  ⟨GateOp.or, [1216, 233]⟩,
  ⟨GateOp.or, [1217, 880]⟩,
  ⟨GateOp.or, [1218, 982]⟩,
  ⟨GateOp.or, [224, 253]⟩,
  ⟨GateOp.or, [1220, 987]⟩,
  ⟨GateOp.or, [1221, 1028]⟩,
  ⟨GateOp.or, [1222, 1097]⟩,
  ⟨GateOp.or, [220, 241]⟩,
  ⟨GateOp.or, [1224, 980]⟩,
  ⟨GateOp.or, [1225, 988]⟩,
  ⟨GateOp.or, [1226, 1012]⟩,
  ⟨GateOp.or, [130, 229]⟩,
  ⟨GateOp.or, [1228, 232]⟩,
  ⟨GateOp.or, [1229, 997]⟩,
  ⟨GateOp.or, [1230, 1027]⟩,
  ⟨GateOp.or, [173, 242]⟩,
  ⟨GateOp.or, [1232, 246]⟩,
  ⟨GateOp.or, [1233, 1019]⟩,
  ⟨GateOp.or, [1234, 1023]⟩,
  ⟨GateOp.or, [149, 151]⟩,
  ⟨GateOp.or, [1236, 153]⟩,
  ⟨GateOp.or, [1237, 191]⟩,
  ⟨GateOp.or, [1238, 909]⟩,
  ⟨GateOp.or, [1239, 981]⟩,
  ⟨GateOp.or, [250, 912]⟩,
  ⟨GateOp.or, [1241, 982]⟩,
  ⟨GateOp.or, [1242, 1033]⟩,
  ⟨GateOp.or, [135, 147]⟩,
  ⟨GateOp.or, [1244, 940]⟩,
  ⟨GateOp.or, [1245, 944]⟩,
  ⟨GateOp.or, [1246, 983]⟩,
  ⟨GateOp.or, [211, 888]⟩,
  ⟨GateOp.or, [1248, 985]⟩,
  ⟨GateOp.or, [1249, 1008]⟩,
  ⟨GateOp.or, [159, 986]⟩,
  ⟨GateOp.or, [1251, 990]⟩,
  ⟨GateOp.or, [1252, 1093]⟩,
  ⟨GateOp.or, [132, 148]⟩,
  ⟨GateOp.or, [1254, 162]⟩
]

def gates25 : List Gate := [
  ⟨GateOp.or, [1255, 167]⟩,
  ⟨GateOp.or, [1256, 1000]⟩,
  ⟨GateOp.or, [1257, 1083]⟩,
  ⟨GateOp.or, [132, 138]⟩,
  ⟨GateOp.or, [1259, 151]⟩,
  ⟨GateOp.or, [1260, 159]⟩,
  ⟨GateOp.or, [1261, 183]⟩,
  ⟨GateOp.or, [1262, 1048]⟩,
  ⟨GateOp.or, [147, 155]⟩,
  ⟨GateOp.or, [1264, 179]⟩,
  ⟨GateOp.or, [1265, 987]⟩,
  ⟨GateOp.or, [1266, 988]⟩,
  ⟨GateOp.or, [1267, 989]⟩,
  ⟨GateOp.or, [131, 178]⟩,
  ⟨GateOp.or, [1269, 251]⟩,
  ⟨GateOp.or, [1270, 996]⟩,
  ⟨GateOp.or, [1271, 1025]⟩,
  ⟨GateOp.or, [172, 173]⟩,
  ⟨GateOp.or, [1273, 194]⟩,
  ⟨GateOp.or, [1274, 229]⟩,
  ⟨GateOp.or, [1275, 900]⟩,
  ⟨GateOp.or, [1276, 926]⟩,
  ⟨GateOp.or, [142, 196]⟩,
  ⟨GateOp.or, [1278, 223]⟩,
  ⟨GateOp.or, [1279, 240]⟩,
  ⟨GateOp.or, [1280, 989]⟩,
  ⟨GateOp.or, [1281, 1034]⟩,
  ⟨GateOp.or, [143, 147]⟩,
  ⟨GateOp.or, [1283, 154]⟩,
  ⟨GateOp.or, [1284, 204]⟩,
  ⟨GateOp.or, [1285, 937]⟩,
  ⟨GateOp.or, [1286, 938]⟩,
  ⟨GateOp.or, [173, 187]⟩,
  ⟨GateOp.or, [1288, 254]⟩,
  ⟨GateOp.or, [1289, 1030]⟩,
  ⟨GateOp.or, [1290, 1091]⟩,
  ⟨GateOp.or, [153, 155]⟩,
  ⟨GateOp.or, [1292, 168]⟩,
  ⟨GateOp.or, [1293, 246]⟩,
  ⟨GateOp.or, [1294, 908]⟩
]

def gates26 : List Gate := [
  ⟨GateOp.or, [1295, 933]⟩,
  ⟨GateOp.or, [190, 215]⟩,
  ⟨GateOp.or, [1297, 225]⟩,
  ⟨GateOp.or, [1298, 226]⟩,
  ⟨GateOp.or, [1299, 972]⟩,
  ⟨GateOp.or, [1300, 990]⟩,
  ⟨GateOp.or, [149, 208]⟩,
  ⟨GateOp.or, [1302, 226]⟩,
  ⟨GateOp.or, [1303, 901]⟩,
  ⟨GateOp.or, [1304, 953]⟩,
  ⟨GateOp.or, [183, 229]⟩,
  ⟨GateOp.or, [1306, 235]⟩,
  ⟨GateOp.or, [1307, 242]⟩,
  ⟨GateOp.or, [1308, 972]⟩,
  ⟨GateOp.or, [1309, 1018]⟩,
  ⟨GateOp.or, [133, 222]⟩,
  ⟨GateOp.or, [1311, 249]⟩,
  ⟨GateOp.or, [1312, 903]⟩,
  ⟨GateOp.or, [1313, 904]⟩,
  ⟨GateOp.or, [1314, 917]⟩,
  ⟨GateOp.or, [180, 202]⟩,
  ⟨GateOp.or, [1316, 207]⟩,
  ⟨GateOp.or, [1317, 249]⟩,
  ⟨GateOp.or, [1318, 973]⟩,
  ⟨GateOp.or, [1319, 991]⟩,
  ⟨GateOp.or, [140, 176]⟩,
  ⟨GateOp.or, [1321, 243]⟩,
  ⟨GateOp.or, [1322, 246]⟩,
  ⟨GateOp.or, [1323, 961]⟩,
  ⟨GateOp.or, [1324, 1001]⟩,
  ⟨GateOp.or, [196, 208]⟩,
  ⟨GateOp.or, [1326, 945]⟩,
  ⟨GateOp.or, [1327, 994]⟩,
  ⟨GateOp.or, [1328, 1011]⟩,
  ⟨GateOp.or, [146, 147]⟩,
  ⟨GateOp.or, [1330, 149]⟩,
  ⟨GateOp.or, [1331, 163]⟩,
  ⟨GateOp.or, [1332, 210]⟩,
  ⟨GateOp.or, [1333, 253]⟩,
  ⟨GateOp.or, [1334, 939]⟩
]

def gates27 : List Gate := [
  ⟨GateOp.or, [177, 254]⟩,
  ⟨GateOp.or, [1336, 992]⟩,
  ⟨GateOp.or, [1337, 993]⟩,
  ⟨GateOp.or, [1338, 1015]⟩,
  ⟨GateOp.or, [133, 183]⟩,
  ⟨GateOp.or, [1340, 886]⟩,
  ⟨GateOp.or, [1341, 915]⟩,
  ⟨GateOp.or, [1342, 994]⟩,
  ⟨GateOp.or, [176, 199]⟩,
  ⟨GateOp.or, [1344, 212]⟩,
  ⟨GateOp.or, [1345, 240]⟩,
  ⟨GateOp.or, [1346, 940]⟩,
  ⟨GateOp.or, [1347, 955]⟩,
  ⟨GateOp.or, [143, 221]⟩,
  ⟨GateOp.or, [1349, 244]⟩,
  ⟨GateOp.or, [1350, 995]⟩,
  ⟨GateOp.or, [1351, 996]⟩,
  ⟨GateOp.or, [132, 145]⟩,
  ⟨GateOp.or, [1353, 155]⟩,
  ⟨GateOp.or, [1354, 218]⟩,
  ⟨GateOp.or, [1355, 997]⟩,
  ⟨GateOp.or, [1356, 1007]⟩,
  ⟨GateOp.or, [130, 234]⟩,
  ⟨GateOp.or, [1358, 237]⟩,
  ⟨GateOp.or, [1359, 249]⟩,
  ⟨GateOp.or, [1360, 939]⟩,
  ⟨GateOp.or, [1361, 1050]⟩,
  ⟨GateOp.or, [142, 217]⟩,
  ⟨GateOp.or, [1363, 941]⟩,
  ⟨GateOp.or, [1364, 998]⟩,
  ⟨GateOp.or, [1365, 1021]⟩,
  ⟨GateOp.or, [185, 243]⟩,
  ⟨GateOp.or, [1367, 999]⟩,
  ⟨GateOp.or, [1368, 1000]⟩,
  ⟨GateOp.or, [1369, 1014]⟩,
  ⟨GateOp.or, [203, 208]⟩,
  ⟨GateOp.or, [1371, 908]⟩,
  ⟨GateOp.or, [1372, 1001]⟩,
  ⟨GateOp.or, [1373, 1026]⟩,
  ⟨GateOp.or, [131, 187]⟩
]

def gates28 : List Gate := [
  ⟨GateOp.or, [1375, 214]⟩,
  ⟨GateOp.or, [1376, 227]⟩,
  ⟨GateOp.or, [1377, 951]⟩,
  ⟨GateOp.or, [1378, 1002]⟩,
  ⟨GateOp.or, [175, 228]⟩,
  ⟨GateOp.or, [1380, 235]⟩,
  ⟨GateOp.or, [1381, 1003]⟩,
  ⟨GateOp.or, [1382, 1010]⟩,
  ⟨GateOp.or, [1383, 1038]⟩,
  ⟨GateOp.or, [150, 191]⟩,
  ⟨GateOp.or, [1385, 915]⟩,
  ⟨GateOp.or, [1386, 954]⟩,
  ⟨GateOp.or, [1387, 1016]⟩,
  ⟨GateOp.or, [169, 246]⟩,
  ⟨GateOp.or, [1389, 890]⟩,
  ⟨GateOp.or, [1390, 1005]⟩,
  ⟨GateOp.or, [1391, 1065]⟩,
  ⟨GateOp.or, [128, 200]⟩,
  ⟨GateOp.or, [1393, 223]⟩,
  ⟨GateOp.or, [1394, 1004]⟩,
  ⟨GateOp.or, [1395, 1005]⟩,
  ⟨GateOp.or, [217, 1022]⟩,
  ⟨GateOp.or, [1397, 1077]⟩,
  ⟨GateOp.or, [134, 157]⟩,
  ⟨GateOp.or, [1399, 197]⟩,
  ⟨GateOp.or, [1400, 919]⟩,
  ⟨GateOp.or, [1401, 1006]⟩,
  ⟨GateOp.or, [1402, 1047]⟩,
  ⟨GateOp.or, [162, 175]⟩,
  ⟨GateOp.or, [1404, 881]⟩,
  ⟨GateOp.or, [1405, 1007]⟩,
  ⟨GateOp.or, [1406, 1008]⟩,
  ⟨GateOp.or, [155, 162]⟩,
  ⟨GateOp.or, [1408, 166]⟩,
  ⟨GateOp.or, [1409, 236]⟩,
  ⟨GateOp.or, [1410, 248]⟩,
  ⟨GateOp.or, [1411, 254]⟩,
  ⟨GateOp.or, [1412, 954]⟩,
  ⟨GateOp.or, [201, 1009]⟩,
  ⟨GateOp.or, [1414, 1010]⟩
]

def gates29 : List Gate := [
  ⟨GateOp.or, [1415, 1013]⟩,
  ⟨GateOp.or, [132, 180]⟩,
  ⟨GateOp.or, [1417, 200]⟩,
  ⟨GateOp.or, [1418, 225]⟩,
  ⟨GateOp.or, [1419, 893]⟩,
  ⟨GateOp.or, [1420, 932]⟩,
  ⟨GateOp.or, [156, 171]⟩,
  ⟨GateOp.or, [1422, 172]⟩,
  ⟨GateOp.or, [1423, 174]⟩,
  ⟨GateOp.or, [1424, 933]⟩,
  ⟨GateOp.or, [1425, 1011]⟩,
  ⟨GateOp.or, [155, 178]⟩,
  ⟨GateOp.or, [1427, 191]⟩,
  ⟨GateOp.or, [1428, 234]⟩,
  ⟨GateOp.or, [1429, 1017]⟩,
  ⟨GateOp.or, [1430, 1102]⟩,
  ⟨GateOp.or, [145, 160]⟩,
  ⟨GateOp.or, [1432, 199]⟩,
  ⟨GateOp.or, [1433, 225]⟩,
  ⟨GateOp.or, [1434, 901]⟩,
  ⟨GateOp.or, [1435, 1012]⟩,
  ⟨GateOp.or, [138, 146]⟩,
  ⟨GateOp.or, [1437, 219]⟩,
  ⟨GateOp.or, [1438, 221]⟩,
  ⟨GateOp.or, [1439, 938]⟩,
  ⟨GateOp.or, [1440, 947]⟩,
  ⟨GateOp.or, [128, 141]⟩,
  ⟨GateOp.or, [1442, 179]⟩,
  ⟨GateOp.or, [1443, 191]⟩,
  ⟨GateOp.or, [1444, 212]⟩,
  ⟨GateOp.or, [1445, 230]⟩,
  ⟨GateOp.or, [1446, 886]⟩,
  ⟨GateOp.or, [155, 192]⟩,
  ⟨GateOp.or, [1448, 235]⟩,
  ⟨GateOp.or, [1449, 945]⟩,
  ⟨GateOp.or, [1450, 1040]⟩,
  ⟨GateOp.or, [138, 156]⟩,
  ⟨GateOp.or, [1452, 214]⟩,
  ⟨GateOp.or, [1453, 960]⟩,
  ⟨GateOp.or, [1454, 1013]⟩
]

def gates30 : List Gate := [
  ⟨GateOp.or, [1455, 1014]⟩,
  ⟨GateOp.or, [136, 162]⟩,
  ⟨GateOp.or, [1457, 206]⟩,
  ⟨GateOp.or, [1458, 948]⟩,
  ⟨GateOp.or, [1459, 1015]⟩,
  ⟨GateOp.or, [200, 239]⟩,
  ⟨GateOp.or, [1461, 897]⟩,
  ⟨GateOp.or, [1462, 1016]⟩,
  ⟨GateOp.or, [1463, 1017]⟩,
  ⟨GateOp.or, [230, 890]⟩,
  ⟨GateOp.or, [1465, 1018]⟩,
  ⟨GateOp.or, [1466, 1035]⟩,
  ⟨GateOp.or, [145, 233]⟩,
  ⟨GateOp.or, [1468, 956]⟩,
  ⟨GateOp.or, [1469, 1019]⟩,
  ⟨GateOp.or, [1470, 1036]⟩,
  ⟨GateOp.or, [151, 1020]⟩,
  ⟨GateOp.or, [1472, 1021]⟩,
  ⟨GateOp.or, [1473, 1096]⟩,
  ⟨GateOp.or, [131, 151]⟩,
  ⟨GateOp.or, [1475, 182]⟩,
  ⟨GateOp.or, [1476, 248]⟩,
  ⟨GateOp.or, [1477, 900]⟩,
  ⟨GateOp.or, [1478, 1049]⟩,
  ⟨GateOp.or, [137, 144]⟩,
  ⟨GateOp.or, [1480, 171]⟩,
  ⟨GateOp.or, [1481, 227]⟩,
  ⟨GateOp.or, [1482, 934]⟩,
  ⟨GateOp.or, [1483, 1022]⟩,
  ⟨GateOp.or, [1484, 1024]⟩,
  ⟨GateOp.or, [131, 139]⟩,
  ⟨GateOp.or, [1486, 157]⟩,
  ⟨GateOp.or, [1487, 253]⟩,
  ⟨GateOp.or, [1488, 918]⟩,
  ⟨GateOp.or, [1489, 1039]⟩,
  ⟨GateOp.or, [187, 208]⟩,
  ⟨GateOp.or, [1491, 218]⟩,
  ⟨GateOp.or, [1492, 1023]⟩,
  ⟨GateOp.or, [1493, 1082]⟩,
  ⟨GateOp.or, [154, 165]⟩
]

def gates31 : List Gate := [
  ⟨GateOp.or, [1495, 198]⟩,
  ⟨GateOp.or, [1496, 245]⟩,
  ⟨GateOp.or, [1497, 935]⟩,
  ⟨GateOp.or, [1498, 1024]⟩,
  ⟨GateOp.or, [141, 144]⟩,
  ⟨GateOp.or, [1500, 245]⟩,
  ⟨GateOp.or, [1501, 246]⟩,
  ⟨GateOp.or, [1502, 254]⟩,
  ⟨GateOp.or, [1503, 901]⟩,
  ⟨GateOp.or, [1504, 936]⟩,
  ⟨GateOp.or, [139, 153]⟩,
  ⟨GateOp.or, [1506, 209]⟩,
  ⟨GateOp.or, [1507, 894]⟩,
  ⟨GateOp.or, [1508, 926]⟩,
  ⟨GateOp.or, [1509, 1025]⟩,
  ⟨GateOp.or, [162, 172]⟩,
  ⟨GateOp.or, [1511, 250]⟩,
  ⟨GateOp.or, [1512, 897]⟩,
  ⟨GateOp.or, [1513, 1026]⟩,
  ⟨GateOp.or, [1514, 1042]⟩,
  ⟨GateOp.or, [134, 209]⟩,
  ⟨GateOp.or, [1516, 1027]⟩,
  ⟨GateOp.or, [1517, 1029]⟩,
  ⟨GateOp.or, [145, 235]⟩,
  ⟨GateOp.or, [1519, 927]⟩,
  ⟨GateOp.or, [1520, 1059]⟩,
  ⟨GateOp.or, [155, 181]⟩,
  ⟨GateOp.or, [1522, 917]⟩,
  ⟨GateOp.or, [1523, 938]⟩,
  ⟨GateOp.or, [1524, 939]⟩,
  ⟨GateOp.or, [129, 166]⟩,
  ⟨GateOp.or, [1526, 184]⟩,
  ⟨GateOp.or, [1527, 200]⟩,
  ⟨GateOp.or, [1528, 255]⟩,
  ⟨GateOp.or, [1529, 894]⟩,
  ⟨GateOp.or, [1530, 1028]⟩,
  ⟨GateOp.or, [150, 184]⟩,
  ⟨GateOp.or, [1532, 228]⟩,
  ⟨GateOp.or, [1533, 254]⟩,
  ⟨GateOp.or, [1534, 879]⟩
]

def gates32 : List Gate := [
  ⟨GateOp.or, [1535, 1029]⟩,
  ⟨GateOp.or, [213, 224]⟩,
  ⟨GateOp.or, [1537, 920]⟩,
  ⟨GateOp.or, [1538, 940]⟩,
  ⟨GateOp.or, [1539, 942]⟩,
  ⟨GateOp.or, [240, 1030]⟩,
  ⟨GateOp.or, [1541, 1031]⟩,
  ⟨GateOp.or, [1542, 1032]⟩,
  ⟨GateOp.or, [209, 885]⟩,
  ⟨GateOp.or, [1544, 1033]⟩,
  ⟨GateOp.or, [1545, 1081]⟩,
  ⟨GateOp.or, [138, 162]⟩,
  ⟨GateOp.or, [1547, 909]⟩,
  ⟨GateOp.or, [1548, 942]⟩,
  ⟨GateOp.or, [1549, 1046]⟩,
  ⟨GateOp.or, [173, 177]⟩,
  ⟨GateOp.or, [1551, 192]⟩,
  ⟨GateOp.or, [1552, 224]⟩,
  ⟨GateOp.or, [1553, 966]⟩,
  ⟨GateOp.or, [1554, 1034]⟩,
  ⟨GateOp.or, [129, 201]⟩,
  ⟨GateOp.or, [1556, 248]⟩,
  ⟨GateOp.or, [1557, 930]⟩,
  ⟨GateOp.or, [1558, 952]⟩,
  ⟨GateOp.or, [128, 177]⟩,
  ⟨GateOp.or, [1560, 189]⟩,
  ⟨GateOp.or, [1561, 237]⟩,
  ⟨GateOp.or, [1562, 252]⟩,
  ⟨GateOp.or, [1563, 1037]⟩,
  ⟨GateOp.or, [131, 135]⟩,
  ⟨GateOp.or, [1565, 150]⟩,
  ⟨GateOp.or, [1566, 196]⟩,
  ⟨GateOp.or, [1567, 243]⟩,
  ⟨GateOp.or, [1568, 1035]⟩,
  ⟨GateOp.or, [245, 247]⟩,
  ⟨GateOp.or, [1570, 251]⟩,
  ⟨GateOp.or, [1571, 886]⟩,
  ⟨GateOp.or, [1572, 1057]⟩,
  ⟨GateOp.or, [139, 173]⟩,
  ⟨GateOp.or, [1574, 180]⟩
]

def gates33 : List Gate := [
  ⟨GateOp.or, [1575, 1036]⟩,
  ⟨GateOp.or, [1576, 1037]⟩,
  ⟨GateOp.or, [155, 211]⟩,
  ⟨GateOp.or, [1578, 897]⟩,
  ⟨GateOp.or, [1579, 916]⟩,
  ⟨GateOp.or, [1580, 1038]⟩,
  ⟨GateOp.or, [128, 188]⟩,
  ⟨GateOp.or, [1582, 951]⟩,
  ⟨GateOp.or, [1583, 956]⟩,
  ⟨GateOp.or, [191, 947]⟩,
  ⟨GateOp.or, [1585, 1039]⟩,
  ⟨GateOp.or, [169, 948]⟩,
  ⟨GateOp.or, [1587, 971]⟩,
  ⟨GateOp.or, [1588, 1041]⟩,
  ⟨GateOp.or, [952, 969]⟩,
  ⟨GateOp.or, [1590, 1045]⟩,
  ⟨GateOp.or, [173, 209]⟩,
  ⟨GateOp.or, [1592, 239]⟩,
  ⟨GateOp.or, [1593, 243]⟩,
  ⟨GateOp.or, [1594, 884]⟩,
  ⟨GateOp.or, [1595, 898]⟩,
  ⟨GateOp.or, [1596, 925]⟩,
  ⟨GateOp.or, [1597, 953]⟩,
  ⟨GateOp.or, [1598, 1040]⟩,
  ⟨GateOp.or, [157, 212]⟩,
  ⟨GateOp.or, [1600, 1105]⟩,
  ⟨GateOp.or, [185, 218]⟩,
  ⟨GateOp.or, [1602, 237]⟩,
  ⟨GateOp.or, [1603, 899]⟩,
  ⟨GateOp.or, [1604, 920]⟩,
  ⟨GateOp.or, [1605, 928]⟩,
  ⟨GateOp.or, [1606, 944]⟩,
  ⟨GateOp.or, [130, 143]⟩,
  ⟨GateOp.or, [1608, 178]⟩,
  ⟨GateOp.or, [1609, 252]⟩,
  ⟨GateOp.or, [1610, 959]⟩,
  ⟨GateOp.or, [1611, 1098]⟩,
  ⟨GateOp.or, [202, 963]⟩,
  ⟨GateOp.or, [1613, 1043]⟩,
  ⟨GateOp.or, [1614, 1071]⟩
]

def gates34 : List Gate := [
  ⟨GateOp.or, [230, 909]⟩,
  ⟨GateOp.or, [1616, 1041]⟩,
  ⟨GateOp.or, [1617, 1079]⟩,
  ⟨GateOp.or, [224, 959]⟩,
  ⟨GateOp.or, [1619, 968]⟩,
  ⟨GateOp.or, [1620, 1062]⟩,
  ⟨GateOp.or, [922, 966]⟩,
  ⟨GateOp.or, [228, 1042]⟩,
  ⟨GateOp.or, [1623, 1043]⟩,
  ⟨GateOp.or, [1624, 1044]⟩,
  ⟨GateOp.or, [1625, 1072]⟩,
  ⟨GateOp.or, [1626, 1108]⟩,
  ⟨GateOp.or, [163, 217]⟩,
  ⟨GateOp.or, [1628, 1044]⟩,
  ⟨GateOp.or, [241, 882]⟩,
  ⟨GateOp.or, [1630, 1076]⟩,
  ⟨GateOp.or, [1631, 1086]⟩,
  ⟨GateOp.or, [1632, 1100]⟩,
  ⟨GateOp.or, [135, 902]⟩,
  ⟨GateOp.or, [1634, 968]⟩,
  ⟨GateOp.or, [1635, 1104]⟩,
  ⟨GateOp.or, [1045, 1092]⟩,
  ⟨GateOp.or, [216, 880]⟩,
  ⟨GateOp.or, [1638, 895]⟩,
  ⟨GateOp.or, [1639, 917]⟩,
  ⟨GateOp.or, [1640, 1075]⟩,
  ⟨GateOp.or, [1641, 1109]⟩,
  ⟨GateOp.or, [156, 958]⟩,
  ⟨GateOp.or, [1643, 1046]⟩,
  ⟨GateOp.or, [1644, 1047]⟩,
  ⟨GateOp.or, [1645, 1080]⟩,
  ⟨GateOp.or, [1646, 1085]⟩,
  ⟨GateOp.or, [1647, 1089]⟩,
  ⟨GateOp.or, [217, 874]⟩,
  ⟨GateOp.or, [1649, 911]⟩,
  ⟨GateOp.or, [1650, 915]⟩,
  ⟨GateOp.or, [1651, 931]⟩,
  ⟨GateOp.or, [171, 195]⟩,
  ⟨GateOp.or, [1653, 945]⟩,
  ⟨GateOp.or, [165, 905]⟩
]

def gates35 : List Gate := [
  ⟨GateOp.or, [1655, 919]⟩,
  ⟨GateOp.or, [1656, 946]⟩,
  ⟨GateOp.or, [1657, 1048]⟩,
  ⟨GateOp.or, [1658, 1055]⟩,
  ⟨GateOp.or, [1659, 1064]⟩,
  ⟨GateOp.or, [150, 244]⟩,
  ⟨GateOp.or, [1661, 1051]⟩,
  ⟨GateOp.or, [166, 168]⟩,
  ⟨GateOp.or, [1663, 929]⟩,
  ⟨GateOp.or, [1664, 1054]⟩,
  ⟨GateOp.or, [169, 210]⟩,
  ⟨GateOp.or, [1666, 224]⟩,
  ⟨GateOp.or, [1667, 247]⟩,
  ⟨GateOp.or, [1668, 931]⟩,
  ⟨GateOp.or, [1669, 947]⟩,
  ⟨GateOp.or, [1670, 1049]⟩,
  ⟨GateOp.or, [169, 1101]⟩,
  ⟨GateOp.or, [178, 253]⟩,
  ⟨GateOp.or, [1673, 881]⟩,
  ⟨GateOp.or, [1674, 888]⟩,
  ⟨GateOp.or, [1675, 889]⟩,
  ⟨GateOp.or, [1676, 899]⟩,
  ⟨GateOp.or, [1677, 906]⟩,
  ⟨GateOp.or, [1678, 917]⟩,
  ⟨GateOp.or, [1679, 969]⟩,
  ⟨GateOp.or, [217, 244]⟩,
  ⟨GateOp.or, [158, 191]⟩,
  ⟨GateOp.or, [1682, 900]⟩,
  ⟨GateOp.or, [1683, 1050]⟩,
  ⟨GateOp.or, [1684, 1051]⟩,
  ⟨GateOp.or, [1685, 1052]⟩,
  ⟨GateOp.or, [190, 199]⟩,
  ⟨GateOp.or, [1687, 239]⟩,
  ⟨GateOp.or, [1688, 913]⟩,
  ⟨GateOp.or, [1689, 927]⟩,
  ⟨GateOp.or, [1690, 948]⟩,
  ⟨GateOp.or, [1691, 973]⟩,
  ⟨GateOp.or, [1692, 1069]⟩,
  ⟨GateOp.or, [153, 248]⟩,
  ⟨GateOp.or, [1694, 903]⟩
]

def gates36 : List Gate := [
  ⟨GateOp.or, [1695, 905]⟩,
  ⟨GateOp.or, [1696, 923]⟩,
  ⟨GateOp.or, [1697, 955]⟩,
  ⟨GateOp.or, [1698, 1053]⟩,
  ⟨GateOp.or, [1699, 1054]⟩,
  ⟨GateOp.or, [144, 163]⟩,
  ⟨GateOp.or, [1701, 897]⟩,
  ⟨GateOp.or, [1702, 907]⟩,
  ⟨GateOp.or, [1703, 908]⟩,
  ⟨GateOp.or, [1704, 949]⟩,
  ⟨GateOp.or, [1705, 967]⟩,
  ⟨GateOp.or, [1706, 1055]⟩,
  ⟨GateOp.or, [205, 237]⟩,
  ⟨GateOp.or, [1708, 1095]⟩,
  ⟨GateOp.or, [187, 881]⟩,
  ⟨GateOp.or, [1710, 892]⟩,
  ⟨GateOp.or, [1711, 927]⟩,
  ⟨GateOp.or, [1712, 964]⟩,
  ⟨GateOp.or, [1713, 1056]⟩,
  ⟨GateOp.or, [131, 176]⟩,
  ⟨GateOp.or, [1715, 198]⟩,
  ⟨GateOp.or, [1716, 234]⟩,
  ⟨GateOp.or, [1717, 904]⟩,
  ⟨GateOp.or, [1718, 1057]⟩,
  ⟨GateOp.or, [884, 1058]⟩,
  ⟨GateOp.or, [1720, 1059]⟩,
  ⟨GateOp.or, [194, 217]⟩,
  ⟨GateOp.or, [1722, 237]⟩,
  ⟨GateOp.or, [1723, 877]⟩,
  ⟨GateOp.or, [154, 167]⟩,
  ⟨GateOp.or, [1725, 185]⟩,
  ⟨GateOp.or, [1726, 191]⟩,
  ⟨GateOp.or, [1727, 888]⟩,
  ⟨GateOp.or, [135, 176]⟩,
  ⟨GateOp.or, [1729, 878]⟩,
  ⟨GateOp.or, [1730, 951]⟩,
  ⟨GateOp.or, [153, 214]⟩,
  ⟨GateOp.or, [1732, 252]⟩,
  ⟨GateOp.or, [1733, 888]⟩,
  ⟨GateOp.or, [1734, 1066]⟩
]

def gates37 : List Gate := [
  ⟨GateOp.or, [177, 195]⟩,
  ⟨GateOp.or, [1736, 952]⟩,
  ⟨GateOp.or, [1737, 1088]⟩,
  ⟨GateOp.or, [156, 217]⟩,
  ⟨GateOp.or, [1739, 896]⟩,
  ⟨GateOp.or, [1740, 953]⟩,
  ⟨GateOp.or, [1741, 963]⟩,
  ⟨GateOp.or, [918, 954]⟩,
  ⟨GateOp.or, [1743, 975]⟩,
  ⟨GateOp.or, [1744, 1060]⟩,
  ⟨GateOp.or, [1745, 1078]⟩,
  ⟨GateOp.or, [152, 166]⟩,
  ⟨GateOp.or, [1747, 214]⟩,
  ⟨GateOp.or, [1748, 253]⟩,
  ⟨GateOp.or, [1749, 900]⟩,
  ⟨GateOp.or, [1750, 920]⟩,
  ⟨GateOp.or, [1751, 955]⟩,
  ⟨GateOp.or, [1752, 1061]⟩,
  ⟨GateOp.or, [1753, 1062]⟩,
  ⟨GateOp.or, [1754, 1064]⟩,
  ⟨GateOp.or, [1755, 1070]⟩,
  ⟨GateOp.or, [244, 1065]⟩,
  ⟨GateOp.or, [875, 878]⟩,
  ⟨GateOp.or, [1758, 956]⟩,
  ⟨GateOp.or, [1759, 957]⟩,
  ⟨GateOp.or, [1760, 1094]⟩,
  ⟨GateOp.or, [891, 922]⟩,
  ⟨GateOp.or, [1762, 1090]⟩,
  ⟨GateOp.or, [210, 878]⟩,
  ⟨GateOp.or, [142, 890]⟩,
  ⟨GateOp.or, [1765, 904]⟩,
  ⟨GateOp.or, [1766, 907]⟩,
  ⟨GateOp.or, [1767, 1066]⟩,
  ⟨GateOp.or, [1768, 1067]⟩,
  ⟨GateOp.or, [1769, 1068]⟩,
  ⟨GateOp.or, [1770, 1069]⟩,
  ⟨GateOp.or, [1771, 1070]⟩,
  ⟨GateOp.or, [1772, 1071]⟩,
  ⟨GateOp.or, [1773, 1072]⟩,
  ⟨GateOp.or, [224, 239]⟩
]

def gates38 : List Gate := [
  ⟨GateOp.or, [1775, 252]⟩,
  ⟨GateOp.or, [1776, 1087]⟩,
  ⟨GateOp.or, [146, 157]⟩,
  ⟨GateOp.or, [1778, 179]⟩,
  ⟨GateOp.or, [1779, 902]⟩,
  ⟨GateOp.or, [1780, 959]⟩,
  ⟨GateOp.or, [1781, 1075]⟩,
  ⟨GateOp.or, [1782, 1076]⟩,
  ⟨GateOp.or, [1783, 1077]⟩,
  ⟨GateOp.or, [157, 1078]⟩,
  ⟨GateOp.or, [239, 1079]⟩,
  ⟨GateOp.or, [1786, 1099]⟩,
  ⟨GateOp.or, [150, 171]⟩,
  ⟨GateOp.or, [1788, 883]⟩,
  ⟨GateOp.or, [1789, 910]⟩,
  ⟨GateOp.or, [1790, 975]⟩,
  ⟨GateOp.or, [143, 185]⟩,
  ⟨GateOp.or, [1792, 212]⟩,
  ⟨GateOp.or, [1793, 875]⟩,
  ⟨GateOp.or, [1794, 903]⟩,
  ⟨GateOp.or, [1795, 1080]⟩,
  ⟨GateOp.or, [1796, 1081]⟩,
  ⟨GateOp.or, [1797, 1082]⟩,
  ⟨GateOp.or, [156, 192]⟩,
  ⟨GateOp.or, [1799, 219]⟩,
  ⟨GateOp.or, [1800, 250]⟩,
  ⟨GateOp.or, [1801, 892]⟩,
  ⟨GateOp.or, [1802, 904]⟩,
  ⟨GateOp.or, [1803, 905]⟩,
  ⟨GateOp.or, [1804, 1083]⟩,
  ⟨GateOp.or, [1805, 1084]⟩,
  ⟨GateOp.or, [167, 169]⟩,
  ⟨GateOp.or, [1807, 203]⟩,
  ⟨GateOp.or, [1808, 225]⟩,
  ⟨GateOp.or, [1809, 889]⟩,
  ⟨GateOp.or, [1810, 962]⟩,
  ⟨GateOp.or, [186, 209]⟩,
  ⟨GateOp.or, [1812, 963]⟩,
  ⟨GateOp.or, [1813, 1085]⟩,
  ⟨GateOp.or, [164, 877]⟩
]

def gates39 : List Gate := [
  ⟨GateOp.or, [1815, 883]⟩,
  ⟨GateOp.or, [931, 1086]⟩,
  ⟨GateOp.or, [165, 168]⟩,
  ⟨GateOp.or, [1818, 191]⟩,
  ⟨GateOp.or, [1819, 236]⟩,
  ⟨GateOp.or, [165, 882]⟩,
  ⟨GateOp.or, [1821, 906]⟩,
  ⟨GateOp.or, [1822, 974]⟩,
  ⟨GateOp.or, [1823, 1087]⟩,
  ⟨GateOp.or, [1824, 1088]⟩,
  ⟨GateOp.or, [169, 196]⟩,
  ⟨GateOp.or, [1826, 907]⟩,
  ⟨GateOp.or, [137, 237]⟩,
  ⟨GateOp.or, [1828, 875]⟩,
  ⟨GateOp.or, [1829, 1089]⟩,
  ⟨GateOp.or, [1830, 1090]⟩,
  ⟨GateOp.or, [156, 173]⟩,
  ⟨GateOp.or, [1832, 244]⟩,
  ⟨GateOp.or, [1833, 967]⟩,
  ⟨GateOp.or, [252, 966]⟩,
  ⟨GateOp.or, [1835, 1091]⟩,
  ⟨GateOp.or, [1836, 1092]⟩,
  ⟨GateOp.or, [185, 192]⟩,
  ⟨GateOp.or, [1838, 248]⟩,
  ⟨GateOp.or, [1839, 1093]⟩,
  ⟨GateOp.or, [1840, 1094]⟩,
  ⟨GateOp.or, [137, 244]⟩,
  ⟨GateOp.or, [1842, 880]⟩,
  ⟨GateOp.or, [1843, 1095]⟩,
  ⟨GateOp.or, [219, 225]⟩,
  ⟨GateOp.or, [1845, 237]⟩,
  ⟨GateOp.or, [1846, 930]⟩,
  ⟨GateOp.or, [168, 203]⟩,
  ⟨GateOp.or, [1848, 887]⟩,
  ⟨GateOp.or, [1849, 967]⟩,
  ⟨GateOp.or, [1850, 1096]⟩,
  ⟨GateOp.or, [146, 1097]⟩,
  ⟨GateOp.or, [180, 246]⟩,
  ⟨GateOp.or, [1853, 911]⟩,
  ⟨GateOp.or, [1854, 926]⟩
]

def gates40 : List Gate := [
  ⟨GateOp.or, [1855, 968]⟩,
  ⟨GateOp.or, [179, 186]⟩,
  ⟨GateOp.or, [1857, 249]⟩,
  ⟨GateOp.or, [1858, 969]⟩,
  ⟨GateOp.or, [154, 248]⟩,
  ⟨GateOp.or, [1860, 890]⟩,
  ⟨GateOp.or, [1861, 1098]⟩,
  ⟨GateOp.or, [1862, 1099]⟩,
  ⟨GateOp.or, [1863, 1100]⟩,
  ⟨GateOp.or, [131, 190]⟩,
  ⟨GateOp.or, [1865, 203]⟩,
  ⟨GateOp.or, [1866, 876]⟩,
  ⟨GateOp.or, [1867, 926]⟩,
  ⟨GateOp.or, [1868, 1101]⟩,
  ⟨GateOp.or, [927, 970]⟩,
  ⟨GateOp.or, [228, 244]⟩,
  ⟨GateOp.or, [1871, 1102]⟩,
  ⟨GateOp.or, [1872, 1104]⟩,
  ⟨GateOp.or, [205, 212]⟩,
  ⟨GateOp.or, [1874, 974]⟩,
  ⟨GateOp.or, [188, 216]⟩,
  ⟨GateOp.or, [1876, 237]⟩,
  ⟨GateOp.or, [1877, 892]⟩,
  ⟨GateOp.or, [1878, 972]⟩,
  ⟨GateOp.or, [1879, 1105]⟩,
  ⟨GateOp.or, [1880, 1106]⟩,
  ⟨GateOp.or, [158, 228]⟩,
  ⟨GateOp.or, [1882, 973]⟩,
  ⟨GateOp.or, [177, 184]⟩,
  ⟨GateOp.or, [1884, 249]⟩,
  ⟨GateOp.or, [1885, 974]⟩,
  ⟨GateOp.or, [176, 186]⟩,
  ⟨GateOp.or, [1887, 236]⟩,
  ⟨GateOp.or, [1888, 238]⟩,
  ⟨GateOp.or, [1889, 896]⟩,
  ⟨GateOp.or, [1890, 913]⟩,
  ⟨GateOp.or, [1891, 931]⟩,
  ⟨GateOp.or, [1892, 975]⟩,
  ⟨GateOp.or, [1893, 1108]⟩,
  ⟨GateOp.or, [1894, 1109]⟩
]

def gates41 : List Gate := [
  ⟨GateOp.and, [369, 1114]⟩,
  ⟨GateOp.and, [374, 1118]⟩,
  ⟨GateOp.or, [1896, 1897]⟩,
  ⟨GateOp.and, [380, 1125]⟩,
  ⟨GateOp.or, [1898, 1899]⟩,
  ⟨GateOp.and, [385, 1130]⟩,
  ⟨GateOp.or, [1900, 1901]⟩,
  ⟨GateOp.and, [389, 1134]⟩,
  ⟨GateOp.or, [1902, 1903]⟩,
  ⟨GateOp.and, [393, 1140]⟩,
  ⟨GateOp.or, [1904, 1905]⟩,
  ⟨GateOp.and, [399, 1143]⟩,
  ⟨GateOp.or, [1906, 1907]⟩,
  ⟨GateOp.and, [404, 1148]⟩,
  ⟨GateOp.or, [1908, 1909]⟩,
  ⟨GateOp.and, [409, 1152]⟩,
  ⟨GateOp.or, [1910, 1911]⟩,
  ⟨GateOp.and, [413, 1157]⟩,
  ⟨GateOp.or, [1912, 1913]⟩,
  ⟨GateOp.and, [417, 1162]⟩,
  ⟨GateOp.or, [1914, 1915]⟩,
  ⟨GateOp.and, [422, 1167]⟩,
  ⟨GateOp.or, [1916, 1917]⟩,
  ⟨GateOp.and, [426, 1171]⟩,
  ⟨GateOp.or, [1918, 1919]⟩,
  ⟨GateOp.and, [432, 1177]⟩,
  ⟨GateOp.or, [1920, 1921]⟩,
  ⟨GateOp.and, [437, 1182]⟩,
  ⟨GateOp.or, [1922, 1923]⟩,
  ⟨GateOp.and, [441, 1187]⟩,
  ⟨GateOp.or, [1924, 1925]⟩,
  ⟨GateOp.and, [444, 1190]⟩,
  ⟨GateOp.or, [1926, 1927]⟩,
  ⟨GateOp.and, [448, 1194]⟩,
  ⟨GateOp.or, [1928, 1929]⟩,
  ⟨GateOp.and, [452, 1197]⟩,
  ⟨GateOp.or, [1930, 1931]⟩,
  ⟨GateOp.and, [458, 1202]⟩,
  ⟨GateOp.or, [1932, 1933]⟩,
  ⟨GateOp.and, [462, 1205]⟩
]

def gates42 : List Gate := [
  ⟨GateOp.or, [1934, 1935]⟩,
  ⟨GateOp.and, [467, 1210]⟩,
  ⟨GateOp.or, [1936, 1937]⟩,
  ⟨GateOp.and, [472, 1214]⟩,
  ⟨GateOp.or, [1938, 1939]⟩,
  ⟨GateOp.and, [478, 1219]⟩,
  ⟨GateOp.or, [1940, 1941]⟩,
  ⟨GateOp.and, [482, 1223]⟩,
  ⟨GateOp.or, [1942, 1943]⟩,
  ⟨GateOp.and, [487, 1227]⟩,
  ⟨GateOp.or, [1944, 1945]⟩,
  ⟨GateOp.and, [491, 1231]⟩,
  ⟨GateOp.or, [1946, 1947]⟩,
  ⟨GateOp.and, [498, 1235]⟩,
  ⟨GateOp.or, [1948, 1949]⟩,
  ⟨GateOp.and, [502, 1240]⟩,
  ⟨GateOp.or, [1950, 1951]⟩,
  ⟨GateOp.and, [505, 1243]⟩,
  ⟨GateOp.or, [1952, 1953]⟩,
  ⟨GateOp.and, [511, 1247]⟩,
  ⟨GateOp.or, [1954, 1955]⟩,
  ⟨GateOp.and, [515, 1250]⟩,
  ⟨GateOp.or, [1956, 1957]⟩,
  ⟨GateOp.and, [519, 1253]⟩,
  ⟨GateOp.or, [1958, 1959]⟩,
  ⟨GateOp.and, [524, 1258]⟩,
  ⟨GateOp.or, [1960, 1961]⟩,
  ⟨GateOp.and, [528, 1263]⟩,
  ⟨GateOp.or, [1962, 1963]⟩,
  ⟨GateOp.and, [535, 1268]⟩,
  ⟨GateOp.or, [1964, 1965]⟩,
  ⟨GateOp.and, [540, 1272]⟩,
  ⟨GateOp.or, [1966, 1967]⟩,
  ⟨GateOp.and, [544, 1277]⟩,
  ⟨GateOp.or, [1968, 1969]⟩,
  ⟨GateOp.and, [548, 1282]⟩,
  ⟨GateOp.or, [1970, 1971]⟩,
  ⟨GateOp.and, [553, 1287]⟩,
  ⟨GateOp.or, [1972, 1973]⟩,
  ⟨GateOp.and, [557, 1291]⟩
]

def gates43 : List Gate := [
  ⟨GateOp.or, [1974, 1975]⟩,
  ⟨GateOp.and, [561, 1296]⟩,
  ⟨GateOp.or, [1976, 1977]⟩,
  ⟨GateOp.and, [565, 1301]⟩,
  ⟨GateOp.or, [1978, 1979]⟩,
  ⟨GateOp.and, [569, 1305]⟩,
  ⟨GateOp.or, [1980, 1981]⟩,
  ⟨GateOp.and, [573, 1310]⟩,
  ⟨GateOp.or, [1982, 1983]⟩,
  ⟨GateOp.and, [578, 1315]⟩,
  ⟨GateOp.or, [1984, 1985]⟩,
  ⟨GateOp.and, [583, 1320]⟩,
  ⟨GateOp.or, [1986, 1987]⟩,
  ⟨GateOp.and, [587, 1325]⟩,
  ⟨GateOp.or, [1988, 1989]⟩,
  ⟨GateOp.and, [593, 1329]⟩,
  ⟨GateOp.or, [1990, 1991]⟩,
  ⟨GateOp.and, [598, 1335]⟩,
  ⟨GateOp.or, [1992, 1993]⟩,
  ⟨GateOp.and, [602, 1339]⟩,
  ⟨GateOp.or, [1994, 1995]⟩,
  ⟨GateOp.and, [606, 1343]⟩,
  ⟨GateOp.or, [1996, 1997]⟩,
  ⟨GateOp.and, [610, 1348]⟩,
  ⟨GateOp.or, [1998, 1999]⟩,
  ⟨GateOp.and, [614, 1352]⟩,
  ⟨GateOp.or, [2000, 2001]⟩,
  ⟨GateOp.and, [619, 1357]⟩,
  ⟨GateOp.or, [2002, 2003]⟩,
  ⟨GateOp.and, [624, 1362]⟩,
  ⟨GateOp.or, [2004, 2005]⟩,
  ⟨GateOp.and, [629, 1366]⟩,
  ⟨GateOp.or, [2006, 2007]⟩,
  ⟨GateOp.and, [634, 1370]⟩,
  ⟨GateOp.or, [2008, 2009]⟩,
  ⟨GateOp.and, [639, 1374]⟩,
  ⟨GateOp.or, [2010, 2011]⟩,
  ⟨GateOp.and, [645, 1379]⟩,
  ⟨GateOp.or, [2012, 2013]⟩,
  ⟨GateOp.and, [650, 1384]⟩
]

def gates44 : List Gate := [
  ⟨GateOp.or, [2014, 2015]⟩,
  ⟨GateOp.and, [655, 1388]⟩,
  ⟨GateOp.or, [2016, 2017]⟩,
  ⟨GateOp.and, [660, 1392]⟩,
  ⟨GateOp.or, [2018, 2019]⟩,
  ⟨GateOp.and, [667, 1396]⟩,
  ⟨GateOp.or, [2020, 2021]⟩,
  ⟨GateOp.and, [671, 1398]⟩,
  ⟨GateOp.or, [2022, 2023]⟩,
  ⟨GateOp.and, [677, 1403]⟩,
  ⟨GateOp.or, [2024, 2025]⟩,
  ⟨GateOp.and, [682, 1407]⟩,
  ⟨GateOp.or, [2026, 2027]⟩,
  ⟨GateOp.and, [688, 1413]⟩,
  ⟨GateOp.or, [2028, 2029]⟩,
  ⟨GateOp.and, [692, 1416]⟩,
  ⟨GateOp.or, [2030, 2031]⟩,
  ⟨GateOp.and, [696, 1421]⟩,
  ⟨GateOp.or, [2032, 2033]⟩,
  ⟨GateOp.and, [701, 1426]⟩,
  ⟨GateOp.or, [2034, 2035]⟩,
  ⟨GateOp.and, [705, 1431]⟩,
  ⟨GateOp.or, [2036, 2037]⟩,
  ⟨GateOp.and, [710, 1436]⟩,
  ⟨GateOp.or, [2038, 2039]⟩,
  ⟨GateOp.and, [716, 1441]⟩,
  ⟨GateOp.or, [2040, 2041]⟩,
  ⟨GateOp.and, [723, 1447]⟩,
  ⟨GateOp.or, [2042, 2043]⟩,
  ⟨GateOp.and, [727, 1451]⟩,
  ⟨GateOp.or, [2044, 2045]⟩,
  ⟨GateOp.and, [731, 1456]⟩,
  ⟨GateOp.or, [2046, 2047]⟩,
  ⟨GateOp.and, [736, 1460]⟩,
  ⟨GateOp.or, [2048, 2049]⟩,
  ⟨GateOp.and, [742, 1464]⟩,
  ⟨GateOp.or, [2050, 2051]⟩,
  ⟨GateOp.and, [747, 1467]⟩,
  ⟨GateOp.or, [2052, 2053]⟩,
  ⟨GateOp.and, [751, 1471]⟩
]

def gates45 : List Gate := [
  ⟨GateOp.or, [2054, 2055]⟩,
  ⟨GateOp.and, [756, 1474]⟩,
  ⟨GateOp.or, [2056, 2057]⟩,
  ⟨GateOp.and, [761, 1479]⟩,
  ⟨GateOp.or, [2058, 2059]⟩,
  ⟨GateOp.and, [765, 1485]⟩,
  ⟨GateOp.or, [2060, 2061]⟩,
  ⟨GateOp.and, [769, 1490]⟩,
  ⟨GateOp.or, [2062, 2063]⟩,
  ⟨GateOp.and, [774, 1494]⟩,
  ⟨GateOp.or, [2064, 2065]⟩,
  ⟨GateOp.and, [779, 1499]⟩,
  ⟨GateOp.or, [2066, 2067]⟩,
  ⟨GateOp.and, [785, 1505]⟩,
  ⟨GateOp.or, [2068, 2069]⟩,
  ⟨GateOp.and, [789, 1510]⟩,
  ⟨GateOp.or, [2070, 2071]⟩,
  ⟨GateOp.and, [793, 1515]⟩,
  ⟨GateOp.or, [2072, 2073]⟩,
  ⟨GateOp.and, [797, 1518]⟩,
  ⟨GateOp.or, [2074, 2075]⟩,
  ⟨GateOp.and, [801, 1521]⟩,
  ⟨GateOp.or, [2076, 2077]⟩,
  ⟨GateOp.and, [807, 1525]⟩,
  ⟨GateOp.or, [2078, 2079]⟩,
  ⟨GateOp.and, [811, 1531]⟩,
  ⟨GateOp.or, [2080, 2081]⟩,
  ⟨GateOp.and, [816, 1536]⟩,
  ⟨GateOp.or, [2082, 2083]⟩,
  ⟨GateOp.and, [821, 1540]⟩,
  ⟨GateOp.or, [2084, 2085]⟩,
  ⟨GateOp.and, [827, 1543]⟩,
  ⟨GateOp.or, [2086, 2087]⟩,
  ⟨GateOp.and, [832, 1546]⟩,
  ⟨GateOp.or, [2088, 2089]⟩,
  ⟨GateOp.and, [836, 1550]⟩,
  ⟨GateOp.or, [2090, 2091]⟩,
  ⟨GateOp.and, [843, 1555]⟩,
  ⟨GateOp.or, [2092, 2093]⟩,
  ⟨GateOp.and, [847, 1559]⟩
]

def gates46 : List Gate := [
  ⟨GateOp.or, [2094, 2095]⟩,
  ⟨GateOp.and, [853, 1564]⟩,
  ⟨GateOp.or, [2096, 2097]⟩,
  ⟨GateOp.and, [859, 1569]⟩,
  ⟨GateOp.or, [2098, 2099]⟩,
  ⟨GateOp.and, [863, 1573]⟩,
  ⟨GateOp.or, [2100, 2101]⟩,
  ⟨GateOp.and, [869, 1577]⟩,
  ⟨GateOp.or, [2102, 2103]⟩,
  ⟨GateOp.and, [873, 1581]⟩,
  ⟨GateOp.or, [2104, 2105]⟩,
  ⟨GateOp.and, [0, 1584]⟩,
  ⟨GateOp.or, [2106, 2107]⟩,
  ⟨GateOp.and, [1, 1586]⟩,
  ⟨GateOp.or, [2108, 2109]⟩,
  ⟨GateOp.and, [2, 1589]⟩,
  ⟨GateOp.or, [2110, 2111]⟩,
  ⟨GateOp.and, [3, 1591]⟩,
  ⟨GateOp.or, [2112, 2113]⟩,
  ⟨GateOp.and, [5, 1599]⟩,
  ⟨GateOp.or, [2114, 2115]⟩,
  ⟨GateOp.and, [6, 1601]⟩,
  ⟨GateOp.or, [2116, 2117]⟩,
  ⟨GateOp.and, [8, 1607]⟩,
  ⟨GateOp.or, [2118, 2119]⟩,
  ⟨GateOp.and, [10, 143]⟩,
  ⟨GateOp.or, [2120, 2121]⟩,
  ⟨GateOp.and, [11, 1612]⟩,
  ⟨GateOp.or, [2122, 2123]⟩,
  ⟨GateOp.and, [12, 1615]⟩,
  ⟨GateOp.or, [2124, 2125]⟩,
  ⟨GateOp.and, [13, 1618]⟩,
  ⟨GateOp.or, [2126, 2127]⟩,
  ⟨GateOp.and, [15, 1621]⟩,
  ⟨GateOp.or, [2128, 2129]⟩,
  ⟨GateOp.and, [18, 1622]⟩,
  ⟨GateOp.or, [2130, 2131]⟩,
  ⟨GateOp.and, [20, 1627]⟩,
  ⟨GateOp.or, [2132, 2133]⟩,
  ⟨GateOp.and, [21, 1629]⟩
]

def gates47 : List Gate := [
  ⟨GateOp.or, [2134, 2135]⟩,
  ⟨GateOp.and, [22, 1633]⟩,
  ⟨GateOp.or, [2136, 2137]⟩,
  ⟨GateOp.and, [23, 1636]⟩,
  ⟨GateOp.or, [2138, 2139]⟩,
  ⟨GateOp.and, [25, 1637]⟩,
  ⟨GateOp.or, [2140, 2141]⟩,
  ⟨GateOp.and, [26, 1642]⟩,
  ⟨GateOp.or, [2142, 2143]⟩,
  ⟨GateOp.and, [27, 1648]⟩,
  ⟨GateOp.or, [2144, 2145]⟩,
  ⟨GateOp.and, [28, 1652]⟩,
  ⟨GateOp.or, [2146, 2147]⟩,
  ⟨GateOp.and, [29, 1654]⟩,
  ⟨GateOp.or, [2148, 2149]⟩,
  ⟨GateOp.and, [34, 1660]⟩,
  ⟨GateOp.or, [2150, 2151]⟩,
  ⟨GateOp.and, [35, 1662]⟩,
  ⟨GateOp.or, [2152, 2153]⟩,
  ⟨GateOp.and, [36, 1665]⟩,
  ⟨GateOp.or, [2154, 2155]⟩,
  ⟨GateOp.and, [38, 1671]⟩,
  ⟨GateOp.or, [2156, 2157]⟩,
  ⟨GateOp.and, [39, 1672]⟩,
  ⟨GateOp.or, [2158, 2159]⟩,
  ⟨GateOp.and, [40, 1680]⟩,
  ⟨GateOp.or, [2160, 2161]⟩,
  ⟨GateOp.and, [41, 1681]⟩,
  ⟨GateOp.or, [2162, 2163]⟩,
  ⟨GateOp.and, [43, 1686]⟩,
  ⟨GateOp.or, [2164, 2165]⟩,
  ⟨GateOp.and, [45, 165]⟩,
  ⟨GateOp.or, [2166, 2167]⟩,
  ⟨GateOp.and, [47, 1693]⟩,
  ⟨GateOp.or, [2168, 2169]⟩,
  ⟨GateOp.and, [48, 1058]⟩,
  ⟨GateOp.or, [2170, 2171]⟩,
  ⟨GateOp.and, [50, 1700]⟩,
  ⟨GateOp.or, [2172, 2173]⟩,
  ⟨GateOp.and, [52, 1707]⟩
]

def gates48 : List Gate := [
  ⟨GateOp.or, [2174, 2175]⟩,
  ⟨GateOp.and, [54, 1709]⟩,
  ⟨GateOp.or, [2176, 2177]⟩,
  ⟨GateOp.and, [55, 1714]⟩,
  ⟨GateOp.or, [2178, 2179]⟩,
  ⟨GateOp.and, [57, 1719]⟩,
  ⟨GateOp.or, [2180, 2181]⟩,
  ⟨GateOp.and, [59, 1721]⟩,
  ⟨GateOp.or, [2182, 2183]⟩,
  ⟨GateOp.and, [60, 1724]⟩,
  ⟨GateOp.or, [2184, 2185]⟩,
  ⟨GateOp.and, [61, 1728]⟩,
  ⟨GateOp.or, [2186, 2187]⟩,
  ⟨GateOp.and, [63, 1731]⟩,
  ⟨GateOp.or, [2188, 2189]⟩,
  ⟨GateOp.and, [64, 1735]⟩,
  ⟨GateOp.or, [2190, 2191]⟩,
  ⟨GateOp.and, [65, 1738]⟩,
  ⟨GateOp.or, [2192, 2193]⟩,
  ⟨GateOp.and, [66, 1742]⟩,
  ⟨GateOp.or, [2194, 2195]⟩,
  ⟨GateOp.and, [69, 1746]⟩,
  ⟨GateOp.or, [2196, 2197]⟩,
  ⟨GateOp.and, [70, 1756]⟩,
  ⟨GateOp.or, [2198, 2199]⟩,
  ⟨GateOp.and, [71, 1757]⟩,
  ⟨GateOp.or, [2200, 2201]⟩,
  ⟨GateOp.and, [72, 1761]⟩,
  ⟨GateOp.or, [2202, 2203]⟩,
  ⟨GateOp.and, [74, 1763]⟩,
  ⟨GateOp.or, [2204, 2205]⟩,
  ⟨GateOp.and, [76, 1106]⟩,
  ⟨GateOp.or, [2206, 2207]⟩,
  ⟨GateOp.and, [77, 1764]⟩,
  ⟨GateOp.or, [2208, 2209]⟩,
  ⟨GateOp.and, [78, 1774]⟩,
  ⟨GateOp.or, [2210, 2211]⟩,
  ⟨GateOp.and, [80, 1777]⟩,
  ⟨GateOp.or, [2212, 2213]⟩,
  ⟨GateOp.and, [81, 1784]⟩
]

def gates49 : List Gate := [
  ⟨GateOp.or, [2214, 2215]⟩,
  ⟨GateOp.and, [82, 1785]⟩,
  ⟨GateOp.or, [2216, 2217]⟩,
  ⟨GateOp.and, [84, 1787]⟩,
  ⟨GateOp.or, [2218, 2219]⟩,
  ⟨GateOp.and, [85, 1791]⟩,
  ⟨GateOp.or, [2220, 2221]⟩,
  ⟨GateOp.and, [88, 1798]⟩,
  ⟨GateOp.or, [2222, 2223]⟩,
  ⟨GateOp.and, [89, 1806]⟩,
  ⟨GateOp.or, [2224, 2225]⟩,
  ⟨GateOp.and, [91, 1811]⟩,
  ⟨GateOp.or, [2226, 2227]⟩,
  ⟨GateOp.and, [92, 1814]⟩,
  ⟨GateOp.or, [2228, 2229]⟩,
  ⟨GateOp.and, [93, 1816]⟩,
  ⟨GateOp.or, [2230, 2231]⟩,
  ⟨GateOp.and, [94, 1817]⟩,
  ⟨GateOp.or, [2232, 2233]⟩,
  ⟨GateOp.and, [96, 1820]⟩,
  ⟨GateOp.or, [2234, 2235]⟩,
  ⟨GateOp.and, [97, 1825]⟩,
  ⟨GateOp.or, [2236, 2237]⟩,
  ⟨GateOp.and, [98, 1827]⟩,
  ⟨GateOp.or, [2238, 2239]⟩,
  ⟨GateOp.and, [104, 1831]⟩,
  ⟨GateOp.or, [2240, 2241]⟩,
  ⟨GateOp.and, [106, 1834]⟩,
  ⟨GateOp.or, [2242, 2243]⟩,
  ⟨GateOp.and, [108, 1837]⟩,
  ⟨GateOp.or, [2244, 2245]⟩,
  ⟨GateOp.and, [110, 1841]⟩,
  ⟨GateOp.or, [2246, 2247]⟩,
  ⟨GateOp.and, [111, 1844]⟩,
  ⟨GateOp.or, [2248, 2249]⟩,
  ⟨GateOp.and, [112, 1847]⟩,
  ⟨GateOp.or, [2250, 2251]⟩,
  ⟨GateOp.and, [113, 1851]⟩,
  ⟨GateOp.or, [2252, 2253]⟩,
  ⟨GateOp.and, [114, 1852]⟩
]

def gates50 : List Gate := [
  ⟨GateOp.or, [2254, 2255]⟩,
  ⟨GateOp.and, [115, 1856]⟩,
  ⟨GateOp.or, [2256, 2257]⟩,
  ⟨GateOp.and, [117, 1859]⟩,
  ⟨GateOp.or, [2258, 2259]⟩,
  ⟨GateOp.and, [118, 1864]⟩,
  ⟨GateOp.or, [2260, 2261]⟩,
  ⟨GateOp.and, [119, 1869]⟩,
  ⟨GateOp.or, [2262, 2263]⟩,
  ⟨GateOp.and, [120, 1870]⟩,
  ⟨GateOp.or, [2264, 2265]⟩,
  ⟨GateOp.and, [121, 1873]⟩,
  ⟨GateOp.or, [2266, 2267]⟩,
  ⟨GateOp.and, [122, 1875]⟩,
  ⟨GateOp.or, [2268, 2269]⟩,
  ⟨GateOp.and, [123, 1881]⟩,
  ⟨GateOp.or, [2270, 2271]⟩,
  ⟨GateOp.and, [124, 1883]⟩,
  ⟨GateOp.or, [2272, 2273]⟩,
  ⟨GateOp.and, [125, 1886]⟩,
  ⟨GateOp.or, [2274, 2275]⟩,
  ⟨GateOp.and, [126, 1895]⟩,
  ⟨GateOp.or, [2276, 2277]⟩
]

def cktGates : List Gate :=
  gates0 ++
  gates1 ++
  gates2 ++
  gates3 ++
  gates4 ++
  gates5 ++
  gates6 ++
  gates7 ++
  gates8 ++
  gates9 ++
  gates10 ++
  gates11 ++
  gates12 ++
  gates13 ++
  gates14 ++
  gates15 ++
  gates16 ++
  gates17 ++
  gates18 ++
  gates19 ++
  gates20 ++
  gates21 ++
  gates22 ++
  gates23 ++
  gates24 ++
  gates25 ++
  gates26 ++
  gates27 ++
  gates28 ++
  gates29 ++
  gates30 ++
  gates31 ++
  gates32 ++
  gates33 ++
  gates34 ++
  gates35 ++
  gates36 ++
  gates37 ++
  gates38 ++
  gates39 ++
  gates40 ++
  gates41 ++
  gates42 ++
  gates43 ++
  gates44 ++
  gates45 ++
  gates46 ++
  gates47 ++
  gates48 ++
  gates49 ++
  gates50

def ckt : Circuit := ⟨cktGates, 2278⟩

def getRev (rw : List ℕ) (n i : ℕ) : ℕ :=
  if i < n then rw.getD (n - 1 - i) 0 else 0

def stepRev (st : ℕ × List ℕ) (g : Gate) : ℕ × List ℕ :=
  let n := st.1
  let rw := st.2
  let v :=
    match g.op, g.inputs with
    | GateOp.and, [a, b] => (getRev rw n a) &&& (getRev rw n b)
    | GateOp.or, [a, b] => (getRev rw n a) ||| (getRev rw n b)
    | GateOp.not, [a] => mask16384 ^^^ (getRev rw n a)
    | _, _ => 0
  (n + 1, v :: rw)

def initList : List ℕ :=
  List.ofFn (fun i : Fin 128 => mask128 <<< (128 * i.val)) ++
  List.ofFn (fun j : Fin 128 => colPat <<< j.val)

def initRev : List ℕ := initList.reverse

def goodGate (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | GateOp.not, [_] => true
  | _, _ => false

theorem mask16384_bit (k : ℕ) (hk : k < 16384) : mask16384.testBit k = true := by
  have h : mask16384 = 2 ^ 16384 - 1 := rfl
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

theorem mask128_bit (k : ℕ) (hk : k < 128) : mask128.testBit k = true := by
  have h : mask128 = 2 ^ 128 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

theorem mask128_bit_ge (k : ℕ) (hk : 128 ≤ k) : mask128.testBit k = false := by
  have h : mask128 = 2 ^ 128 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem colPat_bit (u : Fin 128) (v : Fin 128) (j : Fin 128) :
    (colPat <<< j.val).testBit (128 * u.val + v.val) = decide (j = v) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : j.val ≤ 128 * u.val + v.val
  · simp only [decide_eq_true hle, Bool.true_and]
    have hmod : (128 * u.val + v.val - j.val) % 128 = (128 + v.val - j.val) % 128 := by omega
    have hlt : 128 * u.val + v.val - j.val < 16384 := by omega
    have hcp (k : Fin 16384) : colPat.testBit k.val = decide (k.val % 128 = 0) := by
      have slices : ∀ w : Fin 128, (colPat >>> (128 * w.val)) &&& mask128 = 1 := by decide +kernel
      let w : Fin 128 := ⟨k.val / 128, by omega⟩
      have h := congrArg (fun z : ℕ => z.testBit (k.val % 128)) (slices w)
      have hm : k.val % 128 < 128 := Nat.mod_lt _ (by decide)
      have hi : 128 * w.val + k.val % 128 = k.val := by dsimp [w]; omega
      change (((colPat >>> (128 * w.val)) &&& mask128).testBit (k.val % 128)) = _ at h
      rw [Nat.testBit_and, mask128_bit _ hm, Bool.and_true, Nat.testBit_shiftRight, hi] at h
      have oneBit : ∀ i : Fin 128, (1 : ℕ).testBit i.val = decide (i.val = 0) := by decide +kernel
      exact h.trans (oneBit ⟨_, hm⟩)
    rw [hcp ⟨128 * u.val + v.val - j.val, hlt⟩]
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

theorem rowMask_bit (i u v : Fin 128) :
    (mask128 <<< (128 * i.val)).testBit (128 * u.val + v.val) = decide (i = u) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : 128 * i.val ≤ 128 * u.val + v.val
  · simp only [decide_eq_true hle, Bool.true_and]
    by_cases heq : i = u
    · subst heq
      have h1 : 128 * i.val + v.val - 128 * i.val = v.val := by omega
      rw [h1, mask128_bit v.val v.isLt]
      simp
    · have hlt : i.val < u.val := by
        have hne : i.val ≠ u.val := fun h => heq (Fin.ext h)
        omega
      have hge : 128 ≤ 128 * u.val + v.val - 128 * i.val := by omega
      rw [mask128_bit_ge _ hge]
      simp [heq]
  · simp only [decide_eq_false hle, Bool.false_and]
    symm
    apply decide_eq_false
    intro heq
    subst heq
    omega

theorem initList_len : initList.length = 256 := by simp only [initList, List.length_append, List.length_ofFn]

theorem oneEach_len (u v : Fin 128) : (oneEach u v).length = 256 := by simp only [oneEach, List.length_append, List.length_ofFn]

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

theorem initRev_bit (u v : Fin 128) (i : ℕ) :
    (getRev initRev 256 i).testBit (128 * u.val + v.val) = (oneEach u v).getD i false := by
  have h1 : getRev initRev 256 i = initList.getD i 0 := by
    rw [← initList_len]
    exact getRev_reverse initList i
  rw [h1]
  by_cases hi : i < 256
  · by_cases h32 : i < 128
    · have hl1 : (List.ofFn (fun k : Fin 128 => mask128 <<< (128 * k.val))).length = 128 := by simp only [List.length_ofFn]
      have hl2 : (List.ofFn (fun k : Fin 128 => decide (k = u))).length = 128 := by simp only [List.length_ofFn]
      simp only [initList, oneEach, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [List.getElem?_ofFn, h32, dite_true, Option.getD_some]
      exact rowMask_bit ⟨i, h32⟩ u v
    · have hj : i - 128 < 128 := by omega
      have hl1 : (List.ofFn (fun k : Fin 128 => mask128 <<< (128 * k.val))).length = 128 := by simp only [List.length_ofFn]
      have hl2 : (List.ofFn (fun k : Fin 128 => decide (k = u))).length = 128 := by simp only [List.length_ofFn]
      simp only [initList, oneEach, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp only [hl1, hl2, List.getElem?_ofFn, hj, dite_true, Option.getD_some]
      exact colPat_bit u v ⟨i - 128, hj⟩
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

theorem step_sim (u v : Fin 128) (st : ℕ × List ℕ) (wb : List Bool) (g : Gate)
    (hlen : st.1 = wb.length)
    (hsim : ∀ i, (getRev st.2 st.1 i).testBit (128 * u.val + v.val) = wb.getD i false)
    (hg : goodGate g = true) :
    (stepRev st g).1 = (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).length ∧
    ∀ i, (getRev (stepRev st g).2 (stepRev st g).1 i).testBit (128 * u.val + v.val) =
      (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).getD i false := by
  have hk : 128 * u.val + v.val < 16384 := by omega
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
        · simp only [GateOp.eval, List.map, List.headD, Nat.testBit_xor, mask16384_bit _ hk, Bool.true_bne]
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

theorem foldl_sim (u v : Fin 128) (gs : List Gate) (st : ℕ × List ℕ) (wb : List Bool)
    (hlen : st.1 = wb.length)
    (hsim : ∀ i, (getRev st.2 st.1 i).testBit (128 * u.val + v.val) = wb.getD i false)
    (hgs : ∀ g ∈ gs, goodGate g = true) :
    ∀ i, (getRev (gs.foldl stepRev st).2 (gs.foldl stepRev st).1 i).testBit (128 * u.val + v.val) =
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem hgood : cktGates.all goodGate = true := by decide +kernel

theorem hfan : FanInTwo ckt := by
  intro g hg
  exact good_imp_fanin g (List.all_eq_true.mp hgood g hg)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem hsz : ckt.size ≤ 2046 := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem hval :
    let st := cktGates.foldl stepRev (256, initRev)
    getRev st.2 st.1 2278 = target16384 := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem htarget_bit (u v : Fin 128) :
    target16384.testBit (128 * u.val + v.val) = (rowTbl.getD u.val 0).testBit v.val := by
  have hslice : ∀ u : Fin 128, (target16384 >>> (128 * u.val)) &&& mask128 = rowTbl.getD u.val 0 := by
    decide +kernel
  rw [← hslice u, Nat.testBit_and, mask128_bit v.val v.isLt, Bool.and_true, Nat.testBit_shiftRight]

set_option maxRecDepth 200000 in
theorem hrep : Represents (fun u v : Fin 128 => (rowTbl.getD u.val 0).testBit v.val) ckt := by
  intro u v
  have hgs : ∀ g ∈ cktGates, goodGate g = true := List.all_eq_true.mp hgood
  have hf := foldl_sim u v cktGates (256, initRev) (oneEach u v)
    (by rw [oneEach_len]) (initRev_bit u v) hgs 2278
  have hv : getRev (cktGates.foldl stepRev (256, initRev)).2 (cktGates.foldl stepRev (256, initRev)).1 2278 = target16384 := hval
  rw [hv, htarget_bit u v] at hf
  exact hf.symm

end PEqualNP.Outside.L_meta_19035_aux

theorem PEqualNP.Outside.L_meta_19035 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2046 ∧ PEqualNP.Represents.Represents (fun u v : Fin 128 => (([0x0650c16f3fa4242a5a95d09c81a28695, 0x20c9e05026fb41fc80230c7648146d40, 0x0230e178464025a11ec4a3d880c385bc, 0x1ee01731633b061b5299ea78a3a3be12, 0x26850870804560132e828869106d6009, 0x1b1ac0034653a6c90c30204934020620, 0x164028a4101f2e3375271218b9204501, 0x0048080a008905300441881c86403489, 0x2623f89917533b28fe56b7f686ea940c, 0x2c400060021901020021085800209600, 0xc10026340097dd81a326ea68ba47ac82, 0x5c2053a6981f2b2d5d0df8997a0ec96f, 0xb5fbac173e1a96ddb247aa5b6c86269d, 0xe777f8e41b8b2aa005f55a4eb8078829, 0x99a8000c890e0585230048d8f0822007, 0x1070a13b2c1d075cf8b368d9600e80b5, 0x9246adc828a500658116a4ee92bdbc94, 0x90402910148d665d26e2c010c8842411, 0xcb4966df39baf83b5f8879843b192fbd, 0x0a08084e2aa56021402e5da228060c68, 0x1410c21b0e1d341193536ccd0c5b8090, 0xf13b4288070d2811ea012a2902c32a20, 0x12de405e2ebe232a5871190a60268930, 0x1538205ca51125c1a20c094170796789, 0x021a422120b7e41c82b13000000282c0, 0xb19020402036d41842200a5823ac0c00, 0x7113f4438f4f0715842b297c3fe09c38, 0x3f79244b009b0d793e2a69503b0026cc, 0x974c7035bb3a032e726300ba55262707, 0xabef655696cdfe7a9a37bf66fd5acd0d, 0x4e0bc6473eb1ac804a137963120ebee0, 0xaa40004718b02810646041008b001001, 0x62402440940600fc12200048c0ae000f, 0x0040c001150710fc9a42244847ae9306, 0x180041520c580ea80e32c7e13c420408, 0xaf54ce206b1a233402df1dfe9f462d02, 0xf374e25c25dd2198cd641b7178d74790, 0x0810000824014c304004480881008008, 0x00a24119276d0cb05a45a2b8c91389c9, 0xce6841535d5a66e3466aaabf2e6e2d28, 0x7f1650571e5302eb960c0be428232441, 0x89d54250b2d9c01094787b6034486081, 0x4545d414060149216016f064f9082000, 0x6bfae259249e6a6de3055879f5ff380a, 0x06484204a48b400818e012091008c108, 0x716a08d01ea2004090618023e1db280d, 0x280d825224975389a0c3a44b26aeb100, 0x00baf85b2d2d23b1d9b61ff4785f2cb9, 0x190e080c988803072201104ad202a089, 0x4841201000934410032409003b400820, 0x1b28e64971b242f94c0f6a497311074c, 0x4000081a988740a1322a8088a28220cf, 0x11544444063100f8cc3422683f290400, 0xcf012c4c16998cf0c006636b8f08b684, 0x910421d804542104810c892130c52605, 0x3a9e405f38ba2b1a6e511052d0429d98, 0xba9063884676200594a4d82971c14264, 0x97aff5890747af7d1d5dd93fbb8f9ebe, 0x8beb7103a56b96b5081ba7273d6a740b, 0x131000240c130244002130623522800a, 0x1128201a2e0962073ed0a81c04092c83, 0x6ced7912b3ca0fb1db77fbbfee595d2f, 0x9018060a490823124e99009800412499, 0x5430818b3507008c5a17c09f008a8487, 0xfd2ed185b67b0f747c468b7bdfca9799, 0x0aa418513be24a29104bf86e390ab54c, 0xb119e4013b33d4f10663a89d3700aec4, 0xa0934441267008086222447698a01000, 0x20000048024901009820089061420008, 0xb512e5868b2f05340645ac1f75ea440d, 0x2250d8140cff2e21063373c13d4284c8, 0x8b50e82c80ba9b3403137558ff0dacc3, 0x7318bc7d0a5f0fa4b9377bff3d0680ab, 0xc8a081209180200b1ee0684ca003848d, 0x73fb4cc92cf3084ae66bec7dafffbcc9, 0xd27ac00b9c038561d87900a9a6a09359, 0x3a12c40b0500c699481e682520428608, 0xa18b220922af571933d324d4b4dbc8fb, 0x31bcf05c0e796f31673c63df7f4f7f8a, 0xc11004059009808190ae2b20ac400029, 0xd430cad31c9f7239dc7b7cc7340a8541, 0x36fd6c30123f6d3b64ffd856a06666cc, 0xb55ea62021fe479e2ba3341e30a68407, 0x3890206a02330104c03838402002f251, 0x08108a100a154221200390621003b28a, 0x4025a0b23b1a4b845e63381a465b29a0, 0x880280122d20428016400c9f382a2090, 0xa80f29483e17660346e6dd6fbeaf0e38, 0x363f2ceb8e7c2f715b8148f88966829d, 0x3e92665b6e7befb95f3f4e59bb03ce48, 0x8908c2040219812090207b0275460020, 0x3db4c3a3287c092d1307fff83cc48ccc, 0x3309cecc48a60b7504096069c76c248a, 0xc14a6617fbaad73c018d0c1e75601605, 0x18964015150902624200000061220a04, 0xb5b07ad01a2fa25090608312e740404e, 0x6669785cc6cf60218d251bbf385b6d28, 0xb2b76af45ff72af9d56e4668a86fd421, 0xb7f4c0e46862217b47412239d7e40420, 0xd0700404040300c08444aa252c292400, 0x008c40000260080002093102080e90e0, 0x9150028a160f855cf7300360f5470192, 0x8ac1c004d0d725b1a7606168cbe2d027, 0x92724875141b84448078ba233422220d, 0x9338204809920401a20a28d8210022c1, 0x1cf4102b25720b5d5138789c6a1f3012, 0x4372a640c6150270806928413fabb495, 0x20230080810422020e81020001230011, 0x3aa58c342136689bde8f6a0c2b8ba48f, 0x04201000000002001000001002000002, 0x676ccaa2bb0e2ce157b5786fd85f918b, 0x7b33e7b6950c27b432a6a371f5c3069f, 0x6530304b2e0422075e8a607c2e6d800b, 0x05100017aa0d4925162b25b1744c6cc9, 0xc8ff2258b4d7423ad6a1082731ef6fb0, 0xd86f44d09e360e425a71602987668930, 0x0147840026124c8042736860128a2809, 0xa20906112e9e0f08f73b6470f1571c8a, 0x01d4000802452828083928f03c0a1008, 0x8068130329370f6367e889e5b4e724da, 0x22b0804f2da02089424b787a58d38198, 0x0478e17a804125a1012727c51859549d, 0xc4643002041127007b142071b2096003, 0xff5237388717661a53c5c86db9a3d69b, 0x77b7d931b1682310d1b22873704f6ca6, 0x2af7a1a081d62a10d1af2b402b2a50f4, 0xb092f41b0f68061ddfbb2dbe74738c3a, 0x61fb729203a72c30c9052a442a425861] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_19035_aux.ckt, PEqualNP.Outside.L_meta_19035_aux.hfan,
   PEqualNP.Outside.L_meta_19035_aux.hsz, PEqualNP.Outside.L_meta_19035_aux.hrep⟩

