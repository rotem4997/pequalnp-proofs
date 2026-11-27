import Mathlib
import PEqualNP.Defs

/-!
# L-gct-109

A subspace `K` of doubly centred `3 × 3` complex matrices on which the permanent of
`J + t` (`J` the all-ones matrix) is constantly `6` has dimension at most `1`.

A doubly centred matrix is fixed by its top left `2 × 2` block `(a, b, c, d)`, and there
`perm (J + t) - 6 = q a b c d + c a b c d`, a quadratic plus a cubic form. Both vanish on `K`.
For `v w ∈ K` and a linear form `l`, the vector `l(w) v - l(v) w` lies in `K`, and its
coordinates are linear in the six `2 × 2` minors of the coordinates of `v` and `w`. So `q` and
`c` vanish on those combinations of the minors for every `l`, and that forces the fourth power
of each minor to vanish (`core`, with explicit cofactors). Hence any two elements of `K` are
proportional.
-/

namespace PEqualNP.Outside.L_gct_109_aux

/-- The six permutations of `Fin 3`. -/
theorem perms :
    (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
  decide

/-- The permanent of the `3 × 3` matrix of variables, evaluated. -/
theorem perm_eval (f : Fin 3 × Fin 3 → ℂ) :
    MvPolynomial.eval f (PEqualNP.Gct.permPoly ℂ 3) =
      f (0, 0) * f (1, 1) * f (2, 2) + f (0, 0) * f (1, 2) * f (2, 1)
        + f (0, 1) * f (1, 0) * f (2, 2) + f (0, 1) * f (1, 2) * f (2, 0)
        + f (0, 2) * f (1, 0) * f (2, 1) + f (0, 2) * f (1, 1) * f (2, 0) := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum,
    Fin.prod_univ_three]
  rw [perms, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have e1 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have e3 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have e4 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have e5 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have e6 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  have e7 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have e8 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have e9 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.coe_mul, Function.comp_apply,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, map_mul, MvPolynomial.eval_X]
  ring

/-- The quadratic part of `perm (J + t) - 6` in the coordinates `(a, b, c, d)`. -/
noncomputable def q (a b c d : ℂ) : ℂ :=
  2 * a ^ 2 + 2 * a * b + 2 * a * c + a * d + 2 * b ^ 2 + b * c + 2 * b * d + 2 * c ^ 2
    + 2 * c * d + 2 * d ^ 2

/-- The cubic part of `perm (J + t) - 6` in the coordinates `(a, b, c, d)`. -/
noncomputable def c (a b c d : ℂ) : ℂ :=
  2 * a ^ 2 * d + 4 * a * b * c + 4 * a * b * d + 4 * a * c * d + 2 * a * d ^ 2 + 2 * b ^ 2 * c
    + 2 * b * c ^ 2 + 4 * b * c * d

/-- If `q` and `c` vanish on every combination `l ↦ (∑ i, l i * p j i) j` of an antisymmetric
array of six numbers, the six numbers vanish. -/
theorem core (pab pac pad pbc pbd pcd : ℂ)
    (hq : ∀ l1 l2 l3 l4 : ℂ,
      q (l2 * pab + l3 * pac + l4 * pad) (-l1 * pab + l3 * pbc + l4 * pbd)
        (-l1 * pac - l2 * pbc + l4 * pcd) (-l1 * pad - l2 * pbd - l3 * pcd) = 0)
    (hc : ∀ l1 l2 l3 l4 : ℂ,
      c (l2 * pab + l3 * pac + l4 * pad) (-l1 * pab + l3 * pbc + l4 * pbd)
        (-l1 * pac - l2 * pbc + l4 * pcd) (-l1 * pad - l2 * pbd - l3 * pcd) = 0) :
    pab = 0 ∧ pac = 0 ∧ pad = 0 ∧ pbc = 0 ∧ pbd = 0 ∧ pcd = 0 := by
  simp only [q, c] at hq hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (exp := 4)
      ((1/2)*pab^2 + (-1/18)*pab*pac + (-4/9)*pab*pbd + (-2/3)*pab*pcd) * hq 0 1 1 0 +
      ((-37/9)*pab*pac + (-59/27)*pab*pad + (-97/18)*pab*pbc + (-173/54)*pab*pbd + (59/27)*pab*pcd) * hq 0 1 0 1 +
      ((-4/27)*pab^2 + (-11/2)*pab*pac + (-5/6)*pab*pad + (1)*pab*pbc + (-34/9)*pab*pbd + (-37/54)*pab*pcd + (23/54)*pac*pad + (22/27)*pac*pbc + (1/3)*pac*pbd + (-13/27)*pac*pcd + (1/3)*pad^2 + (1/3)*pad*pbc + (-13/54)*pad*pbd) * hq 0 0 1 1 +
      ((13099/864)*pab + (5071/864)*pac + (697/108)*pad) * hc 0 0 0 1 +
      ((-2660741/106560)*pab + (-34213/63936)*pac + (-388199/63936)*pad) * hc 1 1 0 0 +
      ((-2697673/479520)*pab + (-1389463/239760)*pac + (-15726341/639360)*pad + (21222589/1918080)*pbc + (-13108889/1918080)*pbd + (274301/191808)*pcd) * hc 1 0 1 0 +
      ((5504579/383616)*pab + (-1242479/79920)*pac + (-4459103/959040)*pad + (-4262887/383616)*pbc + (-695671/53280)*pbd + (26514451/1918080)*pcd) * hc 1 0 0 1 +
      ((7419965/383616)*pab + (9598909/479520)*pac + (6124325/383616)*pad + (1318571/319680)*pbc + (1339103/59940)*pbd + (36828421/1918080)*pcd) * hc 0 1 1 0 +
      ((-2805161/959040)*pab + (8724199/1918080)*pac + (-11946113/639360)*pad + (40253353/1918080)*pbc + (-2900309/479520)*pbd + (19213/95904)*pcd) * hc 0 1 0 1 +
      ((-802079/79920)*pab + (96317/31968)*pac + (-496283/35520)*pad + (27668/4995)*pbc + (-4769/1728)*pbd + (-2705399/106560)*pcd) * hc 0 0 1 1 +
      ((173/324)*pab + (11376853/1150848)*pac + (77578609/5754240)*pad + (73289569/5754240)*pbc + (10979581/1150848)*pbd + (407735/127872)*pcd) * hc 1 (-1) 0 0 +
      ((8031469/1918080)*pab + (67/324)*pac + (632003/239760)*pad + (-532843/239760)*pbc + (627949/35520)*pbd + (-370379/639360)*pcd) * hc 1 0 (-1) 0 +
      ((-47037587/5754240)*pab + (-6496715/575424)*pac + (1/6)*pad + (-1676093/719280)*pbc + (88933/11840)*pbd + (73577167/5754240)*pcd) * hc 1 0 0 (-1) +
      ((-38488327/5754240)*pab + (-7956679/2877120)*pac + (1160039/359640)*pad + (1741655/191808)*pbd + (1599251/155520)*pcd) * hc 0 1 (-1) 0 +
      ((1520303/639360)*pab + (-627949/35520)*pac + (-1063039/479520)*pad + (1024559/479520)*pbc + (-13/324)*pbd + (-7796257/1918080)*pcd) * hc 0 1 0 (-1) +
      ((-781573/383616)*pab + (-58217813/5754240)*pac + (-84832033/5754240)*pad + (-83233633/5754240)*pbc + (-65447813/5754240)*pbd) * hc 0 0 1 (-1) +
      ((1173203/89910)*pab + (226213/1438560)*pac + (9202537/575424)*pad + (9118949/5754240)*pbc + (-83175073/5754240)*pbd + (-60104857/5754240)*pcd) * hc 1 1 1 0 +
      ((45193271/2877120)*pab + (22067221/1918080)*pac + (-3493453/1918080)*pad + (-6118987/575424)*pbc + (9319297/1438560)*pbd + (-30507737/5754240)*pcd) * hc 1 1 0 1 +
      ((-32901109/5754240)*pab + (1678057/287712)*pac + (969293/1150848)*pad + (-26993207/2877120)*pbc + (67401583/5754240)*pbd + (38589109/2877120)*pcd) * hc 1 0 1 1 +
      ((-61084829/5754240)*pab + (-29433811/1918080)*pac + (43369997/2877120)*pad + (-188503/127872)*pbc + (-79153/143856)*pbd + (4307083/359640)*pcd) * hc 0 1 1 1
  · linear_combination (exp := 4)
      ((2381/432)*pab*pac + (1595/432)*pab*pad + (-245/144)*pab*pbc + (181/288)*pab*pbd + (451/144)*pab*pcd + (-5/8)*pac^2 + (-17/24)*pac*pad + (-1519/432)*pac*pbc + (-77/216)*pac*pbd + (14/9)*pac*pcd + (17/24)*pad^2 + (71/216)*pad*pbc + (115/108)*pad*pbd + (-301/216)*pad*pcd + (647/216)*pbc*pcd + (23/72)*pbd^2 + (575/864)*pbd*pcd + (-193/108)*pcd^2) * hq 1 0 0 0 +
      ((-2305/864)*pab*pac + (-1451/432)*pab*pad + (245/144)*pab*pbc + (-89/144)*pab*pbd + (-451/144)*pab*pcd + (449/432)*pac^2 + (119/432)*pac*pbc + (1/18)*pac*pbd + (25/144)*pad*pbd + (539/216)*pad*pcd + (157/144)*pbc^2 + (-1381/432)*pbc*pcd + (-119/216)*pbd^2 + (517/144)*pcd^2) * hq 0 1 0 0 +
      ((187/72)*pab^2 + (-793/216)*pab*pac + (1667/432)*pab*pad + (-187/72)*pab*pbc + (77/48)*pab*pbd + (-575/216)*pab*pcd + (9/8)*pac^2 + (1969/432)*pac*pbc + (71/216)*pac*pbd + (-277/144)*pac*pcd + (539/216)*pad^2 + (899/216)*pad*pbd + (-157/144)*pbc^2 + (-61/144)*pbc*pbd + (461/216)*pbc*pcd + (1223/432)*pbd^2 + (97/96)*pbd*pcd + (227/108)*pcd^2) * hq 0 0 1 0 +
      ((-1901/432)*pab^2 + (1987/864)*pab*pac + (-1901/432)*pab*pad + (1451/432)*pab*pbc + (-313/216)*pab*pbd + (575/216)*pab*pcd + (-94/27)*pac^2 + (-659/216)*pac*pbc + (-31/72)*pac*pbd + (833/864)*pac*pcd + (-17/24)*pad^2 + (-71/216)*pad*pbc + (-229/432)*pad*pbd + (227/108)*pad*pcd + (-539/216)*pbc^2 + (215/216)*pbc*pbd + (65/216)*pbc*pcd + (269/216)*pbd^2 + (-179/432)*pbd*pcd + (-227/108)*pcd^2) * hq 0 0 0 1 +
      ((-1/3)*pbc*pcd + (-1/9)*pbd^2) * hq 1 0 0 1 +
      ((-8/9)*pab*pac + (-1/3)*pab*pad + (1/36)*pac*pbd + (-8/9)*pad*pbd + (-4/9)*pbc*pbd + (-7/12)*pbd^2) * hq 0 1 1 0 +
      ((-157/144)*pab + (197/48)*pac + (193/32)*pad + (-43/72)*pbc + (-463/288)*pbd + (1529/288)*pcd) * hc 1 0 0 0 +
      ((1/96)*pab + (599/144)*pac + (167/96)*pad + (1/2)*pbc + (-179/96)*pbd + (41/144)*pcd) * hc 0 1 0 0 +
      ((-11/9)*pab + (1267/288)*pac + (539/144)*pad + (-565/288)*pbc + (-49/16)*pbd + (485/96)*pcd) * hc 0 0 1 0 +
      ((89/288)*pab + (115/32)*pac + (163/144)*pad + (3/32)*pbc + (-83/36)*pbd + (17/24)*pcd) * hc 0 0 0 1 +
      ((-307/144)*pac + (-143/72)*pbc + (905/288)*pbd) * hc 1 1 0 0 +
      ((877/288)*pab + (7/4)*pac + (539/144)*pbc + (-73/24)*pcd) * hc 1 0 1 0 +
      ((-49/144)*pad + (-73/288)*pcd) * hc 0 1 0 1 +
      ((-911/288)*pac + (-1/36)*pbc + (239/72)*pbd) * hc 0 0 1 1 +
      ((5/36)*pac + (1/6)*pbd) * hc 1 0 (-1) 0 +
      ((1/9)*pac + (1/6)*pad) * hc 0 1 0 (-1)
  · linear_combination (exp := 4)
      ((1/9)*pab*pac) * hq 0 1 1 0 +
      ((29/18)*pab*pac + (185/108)*pab*pad + (53/36)*pab*pbc + (95/54)*pab*pbd + (31/108)*pab*pcd + (-1/6)*pac^2 + (-1/2)*pac*pad + (-1/6)*pac*pbc) * hq 0 1 0 1 +
      ((-85/54)*pab^2 + (-79/18)*pab*pac + (-7/6)*pab*pad + (1/2)*pab*pbc + (4/9)*pab*pbd + (-79/108)*pab*pcd + (-493/108)*pac*pad + (275/108)*pac*pbc + (-4/9)*pac*pbd + (-223/54)*pac*pcd + (-1/3)*pad^2 + (-53/36)*pad*pbc + (-49/27)*pad*pbd) * hq 0 0 1 1 +
      ((-3835/864)*pab + (-1279/864)*pac + (-124/27)*pad) * hc 0 0 0 1 +
      ((4891229/213120)*pab + (5759/1998)*pac + (997087/127872)*pad) * hc 1 1 0 0 +
      ((15466009/1918080)*pab + (4552187/479520)*pac + (9848683/426240)*pad + (-59058761/3836160)*pbc + (1977241/3836160)*pbd + (2786477/383616)*pcd) * hc 1 0 1 0 +
      ((-8096233/767232)*pab + (8479589/639360)*pac + (9312787/1918080)*pad + (6664079/767232)*pbc + (7778779/639360)*pbd + (-37024889/3836160)*pcd) * hc 1 0 0 1 +
      ((-13624099/767232)*pab + (-37034407/1918080)*pac + (-11668429/767232)*pad + (-2511119/639360)*pbc + (-38870437/1918080)*pbd + (-66830939/3836160)*pcd) * hc 0 1 1 0 +
      ((8061199/1918080)*pab + (-7340291/3836160)*pac + (8128769/426240)*pad + (-66261827/3836160)*pbc + (5151421/959040)*pbd + (2216603/383616)*pcd) * hc 0 1 0 1 +
      ((1967417/319680)*pab + (137483/63936)*pac + (1450423/106560)*pad + (-2225263/639360)*pbc + (4199/1728)*pbd + (5550031/213120)*pcd) * hc 0 0 1 1 +
      ((13/324)*pab + (-25655255/2301696)*pac + (-156611981/11508480)*pad + (-153415181/11508480)*pbc + (-21858329/2301696)*pbd + (-993535/255744)*pcd) * hc 1 (-1) 0 0 +
      ((-16753511/3836160)*pab + (-109/324)*pac + (-1841647/479520)*pad + (1432427/479520)*pbc + (-1162721/71040)*pbd + (-570989/1278720)*pcd) * hc 1 0 (-1) 0 +
      ((81244663/11508480)*pab + (8850727/1150848)*pac + (-5/12)*pad + (98587/89910)*pbc + (-73591/11840)*pbd + (-98082953/11508480)*pcd) * hc 1 0 0 (-1) +
      ((72066383/11508480)*pab + (31031921/5754240)*pac + (-414811/719280)*pad + (-1029953/191808)*pbd + (-1846789/311040)*pcd) * hc 0 1 (-1) 0 +
      ((-362467/1278720)*pab + (1136081/71040)*pac + (5442787/1918080)*pad + (-6896147/1918080)*pbc + (-49/162)*pbd + (19902743/3836160)*pcd) * hc 0 1 0 (-1) +
      ((3042173/767232)*pab + (108791437/11508480)*pac + (148387907/11508480)*pad + (144498467/11508480)*pbc + (116152147/11508480)*pbd) * hc 0 0 1 (-1) +
      ((-66693539/5754240)*pab + (-3061069/5754240)*pac + (-14565173/1150848)*pad + (10240319/11508480)*pbc + (160366877/11508480)*pbd + (90954173/11508480)*pcd) * hc 1 1 1 0 +
      ((-18633451/1438560)*pab + (-47577359/3836160)*pac + (-2202463/3836160)*pad + (9532811/1150848)*pbc + (-16480793/2877120)*pbd + (6201853/11508480)*pcd) * hc 1 1 0 1 +
      ((-2230129/11508480)*pab + (-6221131/1150848)*pac + (-5923225/2301696)*pad + (54702343/5754240)*pbc + (-144247427/11508480)*pbd + (-79918181/5754240)*pcd) * hc 1 0 1 1 +
      ((90493471/11508480)*pab + (44170049/3836160)*pac + (-85058953/5754240)*pad + (20755/28416)*pbc + (-158419/287712)*pbd + (-4370791/359640)*pcd) * hc 0 1 1 1
  · linear_combination (exp := 4)
      ((409/18)*pab*pac + (353/54)*pab*pad + (739/108)*pab*pbc + (1367/216)*pab*pbd + (193/54)*pab*pcd + (-1019/36)*pac^2 + (353/54)*pac*pad + (-949/27)*pac*pbc + (193/54)*pac*pbd + (553/27)*pac*pcd + (86/27)*pad^2 + (17/3)*pad*pbd + (17/3)*pad*pcd + (-2827/108)*pbc^2 + (85/108)*pbc*pbd + (743/27)*pbc*pcd + (965/108)*pbd^2 + (467/108)*pbd*pcd + (-523/27)*pcd^2) * hq 1 0 0 0 +
      ((-1019/72)*pab*pac + (-733/108)*pab*pad + (-178/27)*pab*pbc + (-355/108)*pab*pbd + (-193/54)*pab*pcd + (983/36)*pac^2 + (-1/12)*pac*pad + (797/27)*pac*pbc + (-22/27)*pac*pbd + (-1379/108)*pac*pcd + (-353/36)*pad^2 + (-128/27)*pad*pbc + (-65/18)*pad*pbd + (-493/54)*pad*pcd + (505/18)*pbc^2 + (-61/27)*pbc*pbd + (-805/27)*pbc*pcd + (-353/54)*pbd^2 + (-85/36)*pbd*pcd + (514/27)*pcd^2) * hq 0 1 0 0 +
      ((254/9)*pab*pad + (1409/54)*pab*pbc + (406/27)*pab*pbd + (-22/27)*pab*pcd + (1019/36)*pac^2 + (581/27)*pac*pad + (178/27)*pac*pbc + (-193/54)*pac*pbd + (-355/108)*pac*pcd + (37/2)*pad^2 + (128/27)*pad*pbc + (-493/54)*pad*pbd + (-65/18)*pad*pcd + (-248/9)*pbc^2 + (-1393/54)*pbc*pbd + (61/27)*pbc*pcd + (-1975/54)*pbd^2 + (-85/36)*pbd*pcd + (-353/54)*pcd^2) * hq 0 0 1 0 +
      ((-175/18)*pab*pad + (-437/54)*pab*pbc + (-859/108)*pab*pbd + (53/54)*pab*pcd + (-175/18)*pac*pad + (437/54)*pac*pbc + (53/54)*pac*pbd + (-859/108)*pac*pcd + (-86/27)*pad^2 + (-76/27)*pad*pbd + (-76/27)*pad*pcd + (472/27)*pbc^2 + (451/54)*pbc*pbd + (-451/54)*pbc*pcd + (335/54)*pbd^2 + (-175/54)*pbd*pcd + (335/54)*pcd^2) * hq 0 0 0 1 +
      ((2/9)*pad*pbd + (2/9)*pad*pcd + (4/9)*pbc*pbd + (-4/9)*pbc*pcd + (4/9)*pbd^2 + (-13/18)*pbd*pcd + (4/9)*pcd^2) * hq 1 0 0 1 +
      ((-1/9)*pbd^2 + (-1/9)*pcd^2) * hq 0 1 1 0 +
      ((169/24)*pab + (169/24)*pac + (737/36)*pad + (151/18)*pbd + (151/18)*pcd) * hc 1 0 0 0 +
      ((67/24)*pab + (15/2)*pac + (227/18)*pad + (133/36)*pbc + (289/36)*pbd + (79/36)*pcd) * hc 0 1 0 0 +
      ((15/2)*pab + (67/24)*pac + (227/18)*pad + (-133/36)*pbc + (79/36)*pbd + (289/36)*pcd) * hc 0 0 1 0 +
      ((29/12)*pab + (29/12)*pac + (65/18)*pad + (29/9)*pbd + (29/9)*pcd) * hc 0 0 0 1 +
      ((16/9)*pac + (-77/9)*pbc + (7/9)*pbd + (-7/12)*pcd) * hc 1 1 0 0 +
      ((16/9)*pab + (77/9)*pbc + (-7/12)*pbd + (7/9)*pcd) * hc 1 0 1 0 +
      ((-1/12)*pab + (-1/12)*pcd) * hc 1 (-1) 0 0 +
      ((-1/12)*pac + (-1/12)*pbd) * hc 1 0 (-1) 0
  · linear_combination (exp := 4)
      ((-25/162)*pab^2 + (815/648)*pab*pac + (25/162)*pab*pad + (-283/162)*pab*pbc + (-463/648)*pab*pbd + (653/324)*pab*pcd + (-1531/648)*pac^2 + (-38/27)*pac*pbc + (283/162)*pac*pbd + (20/81)*pac*pcd + (59/27)*pad*pbc + (130/27)*pad*pbd + (-325/108)*pad*pcd + (499/81)*pbc*pbd + (131/162)*pbc*pcd + (386/81)*pbd^2 + (-1523/648)*pbd*pcd + (-173/54)*pcd^2) * hq 1 0 0 0 +
      ((25/162)*pab^2 + (154/81)*pab*pbc + (73/36)*pab*pbd + (-653/324)*pab*pcd + (337/81)*pac^2 + (37/18)*pac*pad + (181/54)*pac*pbc + (199/648)*pac*pbd + (-1/81)*pac*pcd + (-1/108)*pad^2 + (164/81)*pad*pbc + (1301/324)*pad*pbd + (499/324)*pad*pcd + (707/162)*pbc^2 + (281/81)*pbc*pbd + (-1145/324)*pbc*pcd + (67/162)*pbd^2 + (233/108)*pbd*pcd + (1085/324)*pcd^2) * hq 0 1 0 0 +
      ((-25/162)*pab^2 + (-2)*pab*pac + (164/81)*pab*pad + (1/9)*pab*pbd + (-4/3)*pab*pcd + (1531/648)*pac^2 + (-77/162)*pac*pad + (137/162)*pac*pbc + (-373/162)*pac*pbd + (-2453/648)*pac*pcd + (1/108)*pad^2 + (-164/81)*pad*pbc + (-2209/324)*pad*pbd + (-385/108)*pad*pcd + (-707/162)*pbc^2 + (-47/6)*pbc*pbd + (-269/324)*pbc*pcd + (-2681/324)*pbd^2 + (-1583/648)*pbd*pcd) * hq 0 0 1 0 +
      ((1/108)*pab^2 + (617/216)*pab*pac + (-25/162)*pab*pad + (653/324)*pab*pbc + (-149/324)*pab*pbd + (4/3)*pab*pcd + (-85/324)*pac^2 + (-151/108)*pac*pbc + (-595/648)*pac*pbd + (181/81)*pac*pcd + (-59/27)*pad*pbc + (-130/27)*pad*pbd + (325/108)*pad*pcd + (-1285/324)*pbc*pbd + (449/324)*pbc*pcd + (16/81)*pbd^2 + (649/324)*pbd*pcd) * hq 0 0 0 1 +
      ((-8/27)*pac*pbc + (-1/9)*pbd^2) * hq 1 0 0 1 +
      ((-1/3)*pab*pac + (2/3)*pac*pbc + (5/9)*pac*pbd + (14/27)*pad*pbd) * hq 0 1 1 0 +
      ((61/72)*pab + (-29/48)*pac + (589/216)*pad + (-89/108)*pbc + (-47/36)*pbd + (67/72)*pcd) * hc 1 0 0 0 +
      ((-109/36)*pab + (17/432)*pac + (8/9)*pad + (-203/216)*pbc + (-491/216)*pbd + (97/18)*pcd) * hc 0 1 0 0 +
      ((89/216)*pab + (-871/432)*pac + (-1/2)*pad + (-461/216)*pbc + (-875/216)*pbd + (455/216)*pcd) * hc 0 0 1 0 +
      ((-157/54)*pab + (-457/432)*pac + (-67/72)*pad + (-253/108)*pbc + (-463/108)*pbd + (421/108)*pcd) * hc 0 0 0 1 +
      ((32/27)*pac + (-133/54)*pbc + (167/216)*pbd) * hc 1 1 0 0 +
      ((541/216)*pac + (17/18)*pbc) * hc 1 0 1 0 +
      ((307/72)*pab + (1219/216)*pac + (-289/72)*pcd) * hc 0 1 0 1 +
      ((-115/216)*pac) * hc 0 0 1 1 +
      ((5/27)*pcd) * hc 1 (-1) 0 0 +
      ((-1/9)*pac + (-1/9)*pbc) * hc 1 0 (-1) 0 +
      ((-1/36)*pbd) * hc 0 1 0 (-1) +
      ((-5/27)*pcd) * hc 0 0 1 (-1)
  · linear_combination (exp := 4)
      ((-9563/13392)*pab*pac + (-167/1116)*pab*pad + (-15001/13392)*pab*pbc + (-5039/2976)*pab*pbd + (-179/1674)*pab*pcd + (2/3)*pac^2 + (-1967/3348)*pac*pad + (7549/3348)*pac*pbc + (1945/3348)*pac*pbd + (-29905/13392)*pac*pcd + (-3415/3348)*pad*pbc + (-931/558)*pad*pbd + (157/1674)*pad*pcd + (-121/432)*pbc^2 + (-121/432)*pbc*pbd + (2/3)*pbc*pcd + (-8641/4464)*pbd^2 + (3017/13392)*pbd*pcd + (-4985/3348)*pcd^2) * hq 1 0 0 0 +
      ((-39671/26784)*pab*pac + (-721/1488)*pab*pad + (2371/3348)*pab*pbc + (-6577/4464)*pab*pbd + (-1123/1674)*pab*pcd + (121/432)*pac^2 + (18055/13392)*pac*pad + (9803/4464)*pac*pcd + (-1783/4464)*pad^2 + (5543/3348)*pad*pbc + (-1303/558)*pad*pbd + (-43/3348)*pad*pcd + (-6991/3348)*pbc^2 + (281/279)*pbc*pbd + (6457/3348)*pbc*pcd + (-8887/4464)*pbd*pcd + (-3247/3348)*pcd^2) * hq 0 1 0 0 +
      ((3149/1116)*pab^2 + (22385/13392)*pab*pac + (2701/1116)*pab*pad + (-151/54)*pab*pbc + (1793/4464)*pab*pbd + (457/3348)*pab*pcd + (-265/3348)*pac*pad + (-7549/3348)*pac*pbc + (-1945/3348)*pac*pbd + (18239/6696)*pac*pcd + (-391/279)*pad^2 + (-5543/3348)*pad*pbc + (-112/279)*pad*pbd + (-6329/3348)*pad*pcd + (6991/3348)*pbc^2 + (3619/3348)*pbc*pbd + (89/558)*pbc*pcd + (3607/13392)*pbd*pcd + (-2056/837)*pcd^2) * hq 0 0 1 0 +
      ((17/124)*pab^2 + (42571/13392)*pab*pac + (-205/1116)*pab*pad + (47/27)*pab*pbc + (4447/4464)*pab*pbd + (-3247/3348)*pab*pcd + (6659/3348)*pac^2 + (1967/3348)*pac*pad + (-10379/4464)*pac*pcd + (3415/3348)*pad*pbc + (931/558)*pad*pbd + (-776/837)*pad*pcd + (3619/3348)*pbc^2 + (-95/279)*pbc*pbd + (-8107/3348)*pbc*pcd + (1837/2232)*pbd*pcd + (5135/1674)*pcd^2) * hq 0 0 0 1 +
      ((2/9)*pab*pad + (200/279)*pab*pbd + (7/9)*pab*pcd + (2/3)*pbc^2 + (-4/9)*pbc*pcd + (-7/2232)*pbd*pcd) * hq 1 0 0 1 +
      ((-2/3)*pac^2 + (-391/2232)*pac*pcd + (-1/9)*pcd^2) * hq 0 1 1 0 +
      ((881/2976)*pab + (649/2232)*pac + (-2273/4464)*pad + (5275/4464)*pbc + (-245/2232)*pbd + (-611/248)*pcd) * hc 1 0 0 0 +
      ((3431/8928)*pab + (-829/2232)*pac + (-5543/4464)*pad + (2183/1488)*pbc + (539/2232)*pbd + (-3659/1116)*pcd) * hc 0 1 0 0 +
      ((-895/1488)*pab + (2897/4464)*pac + (-1451/4464)*pad + (1777/1116)*pbc + (7577/4464)*pbd + (-3869/1488)*pcd) * hc 0 0 1 0 +
      ((-619/4464)*pab + (2839/4464)*pac + (-83/93)*pad + (7879/4464)*pbc + (2251/4464)*pbd + (-9601/4464)*pcd) * hc 0 0 0 1 +
      ((613/1488)*pab + (-427/372)*pbd) * hc 1 1 0 0 +
      ((-1547/744)*pab + (209/248)*pcd) * hc 1 0 1 0 +
      ((-1/3)*pac) * hc 1 0 0 1 +
      ((-901/372)*pab + (-2/3)*pbd) * hc 0 1 0 1 +
      ((-5/6)*pad) * hc 0 0 1 1 +
      ((-1/6)*pbc + (1/6)*pbd) * hc 1 0 (-1) 0 +
      ((1/12)*pcd) * hc 0 0 1 (-1)

end PEqualNP.Outside.L_gct_109_aux

open PEqualNP.Outside.L_gct_109_aux in
theorem PEqualNP.Outside.L_gct_109 : ∀ K : Submodule ℂ (Fin 3 × Fin 3 → ℂ), (∀ t ∈ K, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)) → (∀ t ∈ K, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) → Module.finrank ℂ K ≤ 1 := by
  intro K hcen hperm
  -- a doubly centred matrix is fixed by its top left block
  have ent : ∀ t ∈ K, t (0, 2) = -t (0, 0) - t (0, 1) ∧ t (1, 2) = -t (1, 0) - t (1, 1) ∧
      t (2, 0) = -t (0, 0) - t (1, 0) ∧ t (2, 1) = -t (0, 1) - t (1, 1) ∧
      t (2, 2) = t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) := by
    intro t ht
    obtain ⟨hr, hcol⟩ := hcen t ht
    have r0 := hr 0
    have r1 := hr 1
    have r2 := hr 2
    have c0 := hcol 0
    have c1 := hcol 1
    simp only [Fin.sum_univ_three] at r0 r1 r2 c0 c1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination r0
    · linear_combination r1
    · linear_combination c0
    · linear_combination c1
    · linear_combination r2 - c0 - c1
  -- the permanent condition in those coordinates
  have key : ∀ t ∈ K, q (t (0, 0)) (t (0, 1)) (t (1, 0)) (t (1, 1))
      + c (t (0, 0)) (t (0, 1)) (t (1, 0)) (t (1, 1)) = 0 := by
    intro t ht
    obtain ⟨e02, e12, e20, e21, e22⟩ := ent t ht
    have hp := hperm t ht
    rw [perm_eval] at hp
    simp only [e02, e12, e20, e21, e22] at hp
    simp only [q, c]
    linear_combination hp
  -- the quadratic and the cubic part vanish separately, because `K` is closed under negation
  have keyq : ∀ t ∈ K, q (t (0, 0)) (t (0, 1)) (t (1, 0)) (t (1, 1)) = 0 := by
    intro t ht
    have h1 := key t ht
    have h2 := key (-t) (K.neg_mem ht)
    simp only [Pi.neg_apply, q, c] at h1 h2 ⊢
    linear_combination (1 / 2) * h1 + (1 / 2) * h2
  have keyc : ∀ t ∈ K, c (t (0, 0)) (t (0, 1)) (t (1, 0)) (t (1, 1)) = 0 := by
    intro t ht
    have h1 := key t ht
    have h2 := key (-t) (K.neg_mem ht)
    simp only [Pi.neg_apply, q, c] at h1 h2 ⊢
    linear_combination (1 / 2) * h1 - (1 / 2) * h2
  -- the six minors of the coordinates of two elements of `K` vanish
  have minors : ∀ v ∈ K, ∀ w ∈ K,
      v (0, 0) * w (0, 1) - v (0, 1) * w (0, 0) = 0 ∧
      v (0, 0) * w (1, 0) - v (1, 0) * w (0, 0) = 0 ∧
      v (0, 0) * w (1, 1) - v (1, 1) * w (0, 0) = 0 ∧
      v (0, 1) * w (1, 0) - v (1, 0) * w (0, 1) = 0 ∧
      v (0, 1) * w (1, 1) - v (1, 1) * w (0, 1) = 0 ∧
      v (1, 0) * w (1, 1) - v (1, 1) * w (1, 0) = 0 := by
    intro v hv w hw
    have mem : ∀ l1 l2 l3 l4 : ℂ,
        (l1 * w (0, 0) + l2 * w (0, 1) + l3 * w (1, 0) + l4 * w (1, 1)) • v
          - (l1 * v (0, 0) + l2 * v (0, 1) + l3 * v (1, 0) + l4 * v (1, 1)) • w ∈ K :=
      fun l1 l2 l3 l4 => K.sub_mem (K.smul_mem _ hv) (K.smul_mem _ hw)
    apply core
    · intro l1 l2 l3 l4
      have h := keyq _ (mem l1 l2 l3 l4)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, q] at h ⊢
      linear_combination h
    · intro l1 l2 l3 l4
      have h := keyc _ (mem l1 l2 l3 l4)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c] at h ⊢
      linear_combination h
  -- an element of `K` is fixed by its four coordinates
  have ext4 : ∀ v ∈ K, ∀ w ∈ K, ∀ k : ℂ, k * v (0, 0) = w (0, 0) → k * v (0, 1) = w (0, 1) →
      k * v (1, 0) = w (1, 0) → k * v (1, 1) = w (1, 1) → k • v = w := by
    intro v hv w hw k h00 h01 h10 h11
    obtain ⟨v02, v12, v20, v21, v22⟩ := ent v hv
    obtain ⟨w02, w12, w20, w21, w22⟩ := ent w hw
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j
    · show k * v (0, 0) = w (0, 0)
      exact h00
    · show k * v (0, 1) = w (0, 1)
      exact h01
    · show k * v (0, 2) = w (0, 2)
      rw [v02, w02]
      linear_combination -h00 - h01
    · show k * v (1, 0) = w (1, 0)
      exact h10
    · show k * v (1, 1) = w (1, 1)
      exact h11
    · show k * v (1, 2) = w (1, 2)
      rw [v12, w12]
      linear_combination -h10 - h11
    · show k * v (2, 0) = w (2, 0)
      rw [v20, w20]
      linear_combination -h00 - h10
    · show k * v (2, 1) = w (2, 1)
      rw [v21, w21]
      linear_combination -h01 - h11
    · show k * v (2, 2) = w (2, 2)
      rw [v22, w22]
      linear_combination h00 + h01 + h10 + h11
  by_cases hK : ∀ t ∈ K, t = 0
  · -- `K` is zero
    apply finrank_le_one (⟨0, K.zero_mem⟩ : K)
    intro w
    refine ⟨0, Subtype.ext ?_⟩
    show (0 : ℂ) • (0 : Fin 3 × Fin 3 → ℂ) = w.1
    rw [hK w.1 w.2, smul_zero]
  · -- `K` holds a nonzero `v`; every element is a multiple of it
    push Not at hK
    obtain ⟨v, hv, hv0⟩ := hK
    have hne : v (0, 0) ≠ 0 ∨ v (0, 1) ≠ 0 ∨ v (1, 0) ≠ 0 ∨ v (1, 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨z00, z01, z10, z11⟩ := hcon
      apply hv0
      have h := ext4 v hv 0 K.zero_mem 1 (by rw [z00]; simp) (by rw [z01]; simp)
        (by rw [z10]; simp) (by rw [z11]; simp)
      rwa [one_smul] at h
    apply finrank_le_one (⟨v, hv⟩ : K)
    intro w
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := minors v hv w.1 w.2
    rcases hne with h | h | h | h
    · refine ⟨w.1 (0, 0) / v (0, 0), Subtype.ext ?_⟩
      show (w.1 (0, 0) / v (0, 0)) • v = w.1
      apply ext4 v hv w.1 w.2
      · exact div_mul_cancel₀ _ h
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m1
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m2
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m3
    · refine ⟨w.1 (0, 1) / v (0, 1), Subtype.ext ?_⟩
      show (w.1 (0, 1) / v (0, 1)) • v = w.1
      apply ext4 v hv w.1 w.2
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m1
      · exact div_mul_cancel₀ _ h
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m4
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m5
    · refine ⟨w.1 (1, 0) / v (1, 0), Subtype.ext ?_⟩
      show (w.1 (1, 0) / v (1, 0)) • v = w.1
      apply ext4 v hv w.1 w.2
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m2
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m4
      · exact div_mul_cancel₀ _ h
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination -m6
    · refine ⟨w.1 (1, 1) / v (1, 1), Subtype.ext ?_⟩
      show (w.1 (1, 1) / v (1, 1)) • v = w.1
      apply ext4 v hv w.1 w.2
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m3
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m5
      · rw [div_mul_eq_mul_div, div_eq_iff h]
        linear_combination m6
      · exact div_mul_cancel₀ _ h
