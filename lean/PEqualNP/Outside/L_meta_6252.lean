import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6252_aux

private def masks : List Nat := [0, 1, 3, 7, 15, 19, 23, 31, 95, 389, 1369, 1371, 5501, 6799, 54781, 503803, 2097151]
private def lineDiffs : List (Fin 21) := [0, 1, 4, 14, 16]

private def maskAt (i : Nat) : Nat :=
  if i < 8 then
    if i < 4 then
      if i < 2 then
        if i < 1 then
          0
        else
          1
      else
        if i < 3 then
          3
        else
          7
    else
      if i < 6 then
        if i < 5 then
          15
        else
          19
      else
        if i < 7 then
          23
        else
          31
  else
    if i < 12 then
      if i < 10 then
        if i < 9 then
          95
        else
          389
      else
        if i < 11 then
          1369
        else
          1371
    else
      if i < 14 then
        if i < 13 then
          5501
        else
          6799
      else
        if i < 15 then
          54781
        else
          if i < 16 then
            503803
          else
            2097151

private def fRow (k : Nat) : Nat :=
  if k < 34 then
    if k < 17 then
      if k < 8 then
        if k < 4 then
          if k < 2 then
            if k < 1 then
              26128640051322339214200517265440
            else
              24813898953607140862476909904903
          else
            if k < 3 then
              17203895280253816159694795932896
            else
              17175393232906900941321310115844
        else
          if k < 6 then
            if k < 5 then
              21966257299434833961921477116514
            else
              14561328047759874090241348409792
          else
            if k < 7 then
              22314382367803922416548237577218
            else
              26043294529103916934473350103297
      else
        if k < 12 then
          if k < 10 then
            if k < 9 then
              14480577827612650193826733950144
            else
              23278309705915869710356698072622
          else
            if k < 11 then
              18441069505009839862296965620355
            else
              14714832893798081005423361655878
        else
          if k < 14 then
            if k < 13 then
              12207924409300071413099855457409
            else
              20657714744360532644247460926017
          else
            if k < 15 then
              18434458146225094426631335425538
            else
              if k < 16 then
                14547715741767002600923803458003
              else
                22074496548205458340108318023850
    else
      if k < 25 then
        if k < 21 then
          if k < 19 then
            if k < 18 then
              24896503911422034400277749073938
            else
              20656476739529373549130951116259
          else
            if k < 20 then
              24900332505998809230953231353984
            else
              19708719189426405805671458014563
        else
          if k < 23 then
            if k < 22 then
              14508101614354981855063611484740
            else
              20492018686481686676451194155010
          else
            if k < 24 then
              19471851936920584621100890075651
            else
              21082872541280809049950056229925
      else
        if k < 29 then
          if k < 27 then
            if k < 26 then
              16933027789325356508810888479842
            else
              22153724473636156892520228325834
          else
            if k < 28 then
              14476640355017690743826899095072
            else
              24803959002151533877479618164358
        else
          if k < 31 then
            if k < 30 then
              6626857879195972913152895594986
            else
              21803384769563359175305443975298
          else
            if k < 32 then
              14428873538836967446049506793891
            else
              if k < 33 then
                20723627959666463497618577802442
              else
                18089369036750541204011806431363
  else
    if k < 51 then
      if k < 42 then
        if k < 38 then
          if k < 36 then
            if k < 35 then
              9357058356527344066374668391554
            else
              14676573830744051042717582656739
          else
            if k < 37 then
              17251165081228840641962742711556
            else
              16973726604100021659527147459731
        else
          if k < 40 then
            if k < 39 then
              21013240776427897585290960083429
            else
              21613988207790880550090387570092
          else
            if k < 41 then
              13992569866453551972491041491153
            else
              24617681952189919170974458162436
      else
        if k < 46 then
          if k < 44 then
            if k < 43 then
              21082136260593879144647745783109
            else
              19317561497745396433341924919340
          else
            if k < 45 then
              25890646934259391532944022897255
            else
              10669001736696148768353804130435
        else
          if k < 48 then
            if k < 47 then
              12104888492907850353957130382340
            else
              1718344589693452266934435558548
          else
            if k < 49 then
              24740286552688872187637967298850
            else
              if k < 50 then
                25965186894455090375275450797633
              else
                9333427354911529649547415783472
    else
      if k < 60 then
        if k < 55 then
          if k < 53 then
            if k < 52 then
              11819088187315415039659264182726
            else
              10629733436838364059068519615494
          else
            if k < 54 then
              9484294243433646598779742402657
            else
              18009018942671095138757652890635
        else
          if k < 57 then
            if k < 56 then
              10516518670372261165388667030978
            else
              10838383081772303347153697323104
          else
            if k < 58 then
              18084198229813085264475067619947
            else
              if k < 59 then
                12964380467071460888105349907534
              else
                14361623439572985313408405682756
      else
        if k < 64 then
          if k < 62 then
            if k < 61 then
              25961124186085843124800214994050
            else
              11632273832073820106954730674307
          else
            if k < 63 then
              10629387684055609277697381041742
            else
              13368031275669773368941610139842
        else
          if k < 66 then
            if k < 65 then
              24579966113284063732062382274753
            else
              11949338607524075333646020055150
          else
            if k < 67 then
              3180755746595451889020656851297
            else
              if k < 68 then
                19774329986206531376174083713028
              else
                19749612060084141179970981831684

private def gRow (k : Nat) : Nat :=
  if k < 34 then
    if k < 17 then
      if k < 8 then
        if k < 4 then
          if k < 2 then
            if k < 1 then
              26128640051322339214200517265440
            else
              10957531098972130279381787578433
          else
            if k < 3 then
              19514005977230155610773723910208
            else
              12897613980718192271093657701505
        else
          if k < 6 then
            if k < 5 then
              5125867746194853019142433603682
            else
              11748728690456574755735674752128
          else
            if k < 7 then
              7100370087176331540190904516705
            else
              26039568433642800027290133734408
      else
        if k < 12 then
          if k < 10 then
            if k < 9 then
              6908411672264421244643617049664
            else
              23317891131002374044979898401863
          else
            if k < 11 then
              1527137484601746284683629439236
            else
              14714832893798081005423361655878
        else
          if k < 14 then
            if k < 13 then
              24416373208708697156888109885444
            else
              2695484567525047959841607460867
          else
            if k < 15 then
              16618843686905048025607013793994
            else
              if k < 16 then
                20299172079691195222120160628840
              else
                21886329246932153768881167669571
    else
      if k < 25 then
        if k < 21 then
          if k < 19 then
            if k < 18 then
              24878272365589376133850471958625
            else
              18040601801905391794771537706148
          else
            if k < 20 then
              24900332505998809230953231353984
            else
              16699330752513190177884285710403
        else
          if k < 23 then
            if k < 22 then
              20680457406074150853586935226565
            else
              10595746751610820125420647710913
          else
            if k < 24 then
              16896103973125149341544293077251
            else
              24765556876471609159939409580074
      else
        if k < 29 then
          if k < 27 then
            if k < 26 then
              13169535252202151903071831097414
            else
              21765009142789622618847564663171
          else
            if k < 28 then
              7702514061299244183901976038784
            else
              2083774102051242563769433496015
        else
          if k < 31 then
            if k < 30 then
              11581216845431992470011699636424
            else
              21953175815335454783096619204712
          else
            if k < 32 then
              20687887497001319558345687834820
            else
              if k < 33 then
                17874718274680082161605739227272
              else
                22990335197119426439095581155530
  else
    if k < 51 then
      if k < 42 then
        if k < 38 then
          if k < 36 then
            if k < 35 then
              6597268202577683417169634066691
            else
              22128808748399339327186498754634
          else
            if k < 37 then
              5840847206332637724922643385416
            else
              6357456270266259067351606630504
        else
          if k < 40 then
            if k < 39 then
              11710318039294626468496068196488
            else
              22280000029757729443202782638703
          else
            if k < 41 then
              16957321038106802690233870095976
            else
              5880730475418163129530701682065
      else
        if k < 46 then
          if k < 44 then
            if k < 43 then
              24487793750343424064154045129073
            else
              23493908515204674541817204713512
          else
            if k < 45 then
              25415539322742268933381326052770
            else
              7773576980627309113447032040553
        else
          if k < 48 then
            if k < 47 then
              15472526869925754379407410380289
            else
              493055987295955929547314316935
          else
            if k < 49 then
              17283600656822823689822566253095
            else
              if k < 50 then
                25513075731584051556134227612684
              else
                8332768494176110819885692749870
    else
      if k < 60 then
        if k < 55 then
          if k < 53 then
            if k < 52 then
              6941294593691284172789168572707
            else
              21722646646900063248057889791361
          else
            if k < 54 then
              16890696402003864395763369944075
            else
              10875389442925981291405413290305
        else
          if k < 57 then
            if k < 56 then
              20454880478220585616825759367555
            else
              21007349378939383988438751546592
          else
            if k < 58 then
              12736413552052154796599274477701
            else
              if k < 59 then
                17917373704912268058176227738699
              else
                5468687735484431874044574704875
      else
        if k < 64 then
          if k < 62 then
            if k < 61 then
              25956092625107907238546935709996
            else
              23386090349305168941377030986860
          else
            if k < 63 then
              7805724683933507789508924810315
            else
              13368031275669773368941610139842
        else
          if k < 66 then
            if k < 65 then
              18543771858465876113596811096071
            else
              23495067596973707791898844901611
          else
            if k < 67 then
              14595839523382687634286651527174
            else
              if k < 68 then
                13450429654672031801215138603137
              else
                8303580299952540261981639483521

private def lRow (k : Nat) : Nat :=
  if k < 34 then
    if k < 17 then
      if k < 8 then
        if k < 4 then
          if k < 2 then
            if k < 1 then
              26128640051322339214200517265440
            else
              4537532770090799589743624527879
          else
            if k < 3 then
              26083605942338767143108512653511
            else
              11945053310057111363664495020192
        else
          if k < 6 then
            if k < 5 then
              1959752561855408496588464783539
            else
              9327317825966197728807940557216
          else
            if k < 7 then
              1393047014527754414929740374663
            else
              8256542085921563720315991863784
      else
        if k < 12 then
          if k < 10 then
            if k < 9 then
              9603371087088258601766176982213
            else
              18480706790720564802763779971117
          else
            if k < 11 then
              13211390448090494999836708355220
            else
              14681253765693408561919219040290
        else
          if k < 14 then
            if k < 13 then
              10780038205220603844896415689056
            else
              651210006781107178914448593042
          else
            if k < 15 then
              24620439881107327882368661965186
            else
              if k < 16 then
                23270933028556246275222242630067
              else
                22080150694527309405676774235274
    else
      if k < 25 then
        if k < 21 then
          if k < 19 then
            if k < 18 then
              23595682992231491321773161645297
            else
              3186859387102894551721199186996
          else
            if k < 20 then
              7096548716091229664916629817632
            else
              25412527928127239460196418355786
        else
          if k < 23 then
            if k < 22 then
              14357764707350688419951037291044
            else
              3017226348142826318603183530535
          else
            if k < 24 then
              25808707616456533355231454676354
            else
              15853272476160505709342111673921
      else
        if k < 29 then
          if k < 27 then
            if k < 26 then
              12135038420719319005128679588098
            else
              21607257332161477572336100712042
          else
            if k < 28 then
              9602714652953191877106339204209
            else
              7056702541992992158347548894854
        else
          if k < 31 then
            if k < 30 then
              13169559427614831249059352781167
            else
              1797005570530676817069186687113
          else
            if k < 32 then
              13127252310643479608297948486068
            else
              if k < 33 then
                19662564591644789146300768128422
              else
                13197231739661567060817567258979
  else
    if k < 51 then
      if k < 42 then
        if k < 38 then
          if k < 36 then
            if k < 35 then
              9362635131591499765683965170825
            else
              13407684341465345711439210480835
          else
            if k < 37 then
              12140918220332303530706076271876
            else
              23307293779101829134149413504131
        else
          if k < 40 then
            if k < 39 then
              15308773389813497237013407544673
            else
              21612711581608710230427076607628
          else
            if k < 41 then
              21003018867580066326661368657997
            else
              4532104998956901521814357420260
      else
        if k < 46 then
          if k < 44 then
            if k < 43 then
              15853254302280635295273962845738
            else
              14506934824673520859743185375816
          else
            if k < 45 then
              8421029582583463696883069011107
            else
              10667725111289498280689845999971
        else
          if k < 48 then
            if k < 47 then
              12063890137448631756250275039456
            else
              8333311038193524361035975471396
          else
            if k < 49 then
              24699440583774954975047531377929
            else
              if k < 50 then
                8415536161242053214595741886546
              else
                15511986286046002527982912392224
    else
      if k < 60 then
        if k < 55 then
          if k < 53 then
            if k < 52 then
              6707594934525342896622171364973
            else
              16817652847717155562203574282885
          else
            if k < 54 then
              8185964921412598523387340764488
            else
              13198392269599219565158913347111
        else
          if k < 57 then
            if k < 56 then
              9207842151433889397633627378003
            else
              9392449968056202256524747263316
          else
            if k < 58 then
              13210694219829936929335637444786
            else
              if k < 59 then
                12923379993652707906880674046003
              else
                14361467483426358546952108586436
      else
        if k < 64 then
          if k < 62 then
            if k < 61 then
              24891539011246796254956973664361
            else
              10345018082095194679620847835491
          else
            if k < 63 then
              16817811217001892777888157375054
            else
              12099141786391045132637008134306
        else
          if k < 66 then
            if k < 65 then
              23584038478387176276670646106534
            else
              18129135467808091567926880571498
          else
            if k < 67 then
              1367018841815088092078451070322
            else
              if k < 68 then
                14544729921086204391690644040224
              else
                14519933003164796317510724567200

private def pTargetRow (i : Nat) : Nat :=
  if i < 8 then
    if i < 4 then
      if i < 2 then
        if i < 1 then
          0
        else
          40853269219844248009329116192
      else
        if i < 3 then
          1348157884254860184307860834336
        else
          2617086358072029297966373242913
    else
      if i < 6 then
        if i < 5 then
          2657978312918100087144267745346
        else
          2735931097690171043305389888576
      else
        if i < 7 then
          4004859571507340156963902297153
        else
          4045751526353410946141796799586
  else
    if i < 12 then
      if i < 10 then
        if i < 9 then
          5356847332721808843687249187973
        else
          6547669371232075186602280916133
      else
        if i < 11 then
          5479289608721095506233248584004
        else
          9321972871096750663832914074948
    else
      if i < 14 then
        if i < 13 then
          14395091199084216532589280076139
        else
          10468340629673537298048910369032
      else
        if i < 15 then
          15704988958821862956627627749772
        else
          if i < 16 then
            18359209852297350616232998943182
          else
            19628138326114519765110243180015

private def pAutRow (i : Nat) : Nat :=
  if i < 8 then
    if i < 4 then
      if i < 2 then
        if i < 1 then
          0
        else
          0
      else
        if i < 3 then
          1393797239522161838803918844507037047455744
        else
          1393967380705622308035650675934737100439556
    else
      if i < 6 then
        if i < 5 then
          1459482370161869241579388861378151468500612
        else
          4181817071525136689491086112090361274827392
      else
        if i < 7 then
          1393967380705622308035650677060637007282820
        else
          1426634487930032400528189979606307884237444
  else
    if i < 12 then
      if i < 10 then
        if i < 9 then
          15369796189247195100157774921535495591690884
        else
          12620398406214918989735926282871744806110089
      else
        if i < 11 then
          44601514987982022115787355611774117486952477
        else
          33451142388635580906647391113493037255295005
    else
      if i < 14 then
        if i < 13 then
          53160310373706471421887144722459428068166927
        else
          91178586761043705940402531089917491431873982
      else
        if i < 15 then
          21288094118522833646527080168211127336143409
        else
          if i < 16 then
            55752633342080137791494290826397529364204557
          else
            19514093843587909130915579273233945866980612

private def unpack21 (row : Nat) (x : Fin 21) : Fin 21 :=
  Fin.ofNat 21 ((row >>> (x.val * 5)) &&& 31)

private def fAt (k : Nat) (x : Fin 21) : Fin 21 := unpack21 (fRow k) x
private def gAt (k : Nat) (x : Fin 21) : Fin 21 := unpack21 (gRow k) x
private def lAt (k : Nat) (x : Fin 21) : Fin 21 := unpack21 (lRow k) x

private def pTarget (i5 : Nat) (x7 : Fin 21) : Nat :=
  (pTargetRow i5 >>> (x7.val * 5)) &&& 31

private def pAut (i5 : Nat) (x7 : Fin 21) : Nat :=
  (pAutRow i5 >>> (x7.val * 7)) &&& 127

private def inLine (x : Fin 21) : Bool := (81939 : Nat).testBit x.val

private theorem inLine_eq_decide (x : Fin 21) : inLine x = decide (x ∈ lineDiffs) := by
  revert x; decide

private theorem maskAt_mem (i : Nat) (hi : i < 17) : maskAt i ∈ masks := by
  revert i; decide

private def okInvL (k : Nat) : Bool :=
  let fr := fRow k
  let gr := gRow k
  (List.finRange 21).all fun x => unpack21 gr (unpack21 fr x) == x

private def okInvR (k : Nat) : Bool :=
  let fr := fRow k
  let gr := gRow k
  (List.finRange 21).all fun x => unpack21 fr (unpack21 gr x) == x

private def okLines (k : Nat) : Bool :=
  let fr := fRow k
  let lr := lRow k
  (List.finRange 21).all fun u =>
    (List.finRange 21).all fun v =>
      inLine (v - u) == inLine (unpack21 fr v - unpack21 lr u)

private theorem all_invL : (List.range 69).all okInvL = true := by decide
private theorem all_invR : (List.range 69).all okInvR = true := by decide
private theorem all_lines : (List.range 69).all okLines = true := by decide

private def okPair (i5 : Nat) (x7 : Fin 21) : Bool :=
  let i8 := pTarget i5 x7
  let k := pAut i5 x7
  let m5 := maskAt i5
  let m8 := maskAt i8
  let fr := fRow k
  (i8 < 17) &&
  (k < 69) &&
  (List.finRange 21).all fun x10 =>
    (m5.testBit x10.val && !(inLine (x10 - x7))) == m8.testBit (unpack21 fr x10).val

private theorem all_pairs : (List.range 17).all (fun i5 => (List.finRange 21).all (okPair i5)) = true := by decide

private def autEquiv (k : Nat) (hk : k < 69) : Fin 21 ≃ Fin 21 where
  toFun := fAt k
  invFun := gAt k
  left_inv x := by
    have h := List.all_eq_true.mp (List.all_eq_true.mp all_invL k (List.mem_range.mpr hk)) x (List.mem_finRange x)
    exact beq_iff_eq.mp h
  right_inv x := by
    have h := List.all_eq_true.mp (List.all_eq_true.mp all_invR k (List.mem_range.mpr hk)) x (List.mem_finRange x)
    exact beq_iff_eq.mp h

private theorem main_proof :
    have x1 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (7 : ℕ), (15 : ℕ), (19 : ℕ), (23 : ℕ), (31 : ℕ), (95 : ℕ), (389 : ℕ), (1369 : ℕ), (1371 : ℕ), (5501 : ℕ), (6799 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)];
    have x2 : List (Fin (21 : ℕ)) := [(0 : Fin (21 : ℕ)), (1 : Fin (21 : ℕ)), (4 : Fin (21 : ℕ)), (14 : Fin (21 : ℕ)), (16 : Fin (21 : ℕ))];
    let x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x3 x4 : Fin (21 : ℕ)) => x3 - x4 ∈ x2;
    have x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ) → Prop := fun (x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)) => ∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin (21 : ℕ)), ∀ (x7 : Fin (21 : ℕ)), x3 x7 x5 ↔ x3 (x4 x7) x6;
    ∀ x5 ∈ x1, ∀ (x7 : Fin (21 : ℕ)), ∃ x8 ∈ x1, ∃ (x9 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)), x4 x9 ∧ ∀ (x10 : Fin (21 : ℕ)), (x5.testBit ↑x10 && !Decidable.decide (x3 x10 x7)) = x8.testBit ↑(x9 x10) := by
  intro x1 x2 x3 x4 x5 hx5 x7
  have hm : x1 = masks := rfl
  have hl : x2 = lineDiffs := rfl
  obtain ⟨i5, hi5lt, rfl⟩ : ∃ i5 < 17, maskAt i5 = x5 := by
    rw [hm] at hx5
    obtain ⟨i5, hi5, hget⟩ := List.getElem_of_mem hx5
    have hmeq : maskAt i5 = masks[i5] := by
      clear hx5 hget
      revert i5 hi5
      decide
    exact ⟨i5, hi5, hmeq.trans hget⟩
  have hpair_b : okPair i5 x7 = true :=
    List.all_eq_true.mp (List.all_eq_true.mp all_pairs i5 (List.mem_range.mpr hi5lt)) x7 (List.mem_finRange x7)
  set i8 := pTarget i5 x7
  set k := pAut i5 x7
  have hba : okPair i5 x7 = true := hpair_b
  unfold okPair at hba
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hba
  have hi8lt : i8 < 17 := hba.1.1
  have hklt : k < 69 := hba.1.2
  have hbits : ∀ x10 : Fin 21,
      ((maskAt i5).testBit x10.val && !(inLine (x10 - x7))) =
      (maskAt i8).testBit (fAt k x10).val := by
    intro x10
    exact beq_iff_eq.mp (List.all_eq_true.mp hba.2 x10 (List.mem_finRange x10))
  refine ⟨maskAt i8, ?_, autEquiv k hklt, ?_, ?_⟩
  · rw [hm]
    exact maskAt_mem i8 hi8lt
  · intro u
    refine ⟨lAt k u, fun v => ?_⟩
    have hline_b := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all_lines k (List.mem_range.mpr hklt)) u (List.mem_finRange u)) v (List.mem_finRange v)
    have hdec : inLine (v - u) = inLine (fAt k v - lAt k u) := beq_iff_eq.mp hline_b
    rw [inLine_eq_decide, inLine_eq_decide] at hdec
    change (v - u ∈ x2) ↔ (fAt k v - lAt k u ∈ x2)
    rw [hl, ← decide_eq_true_eq (p := v - u ∈ lineDiffs), ← decide_eq_true_eq (p := fAt k v - lAt k u ∈ lineDiffs), hdec]
  · intro x10
    have hb := hbits x10
    rw [inLine_eq_decide] at hb
    have hdec3 : Decidable.decide (x3 x10 x7) = decide (x10 - x7 ∈ lineDiffs) := by
      simp [x3, hl]
    rw [hdec3]
    exact hb

end PEqualNP.Outside.L_meta_6252_aux

theorem PEqualNP.Outside.L_meta_6252 :
    have x1 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (7 : ℕ), (15 : ℕ), (19 : ℕ), (23 : ℕ), (31 : ℕ), (95 : ℕ), (389 : ℕ), (1369 : ℕ), (1371 : ℕ), (5501 : ℕ), (6799 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)];
    have x2 : List (Fin (21 : ℕ)) := [(0 : Fin (21 : ℕ)), (1 : Fin (21 : ℕ)), (4 : Fin (21 : ℕ)), (14 : Fin (21 : ℕ)), (16 : Fin (21 : ℕ))];
    let x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x3 x4 : Fin (21 : ℕ)) => x3 - x4 ∈ x2;
    have x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ) → Prop := fun (x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)) => ∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin (21 : ℕ)), ∀ (x7 : Fin (21 : ℕ)), x3 x7 x5 ↔ x3 (x4 x7) x6;
    ∀ x5 ∈ x1, ∀ (x7 : Fin (21 : ℕ)), ∃ x8 ∈ x1, ∃ (x9 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)), x4 x9 ∧ ∀ (x10 : Fin (21 : ℕ)), (x5.testBit ↑x10 && !Decidable.decide (x3 x10 x7)) = x8.testBit ↑(x9 x10) :=
  PEqualNP.Outside.L_meta_6252_aux.main_proof
