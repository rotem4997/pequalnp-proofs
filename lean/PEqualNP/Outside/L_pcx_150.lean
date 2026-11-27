import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_150_aux

open PEqualNP.ProofComplexity

abbrev Row := Fin 4
abbrev Hole := Fin 3
abbrev V := Row × Hole
abbrev C := Clause V

def rowAx (i : Row) : C := (Finset.univ : Finset Hole).image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

def Coll (N : C) : Prop := ∃ (i k : Row) (j : Hole), i ≠ k ∧ N = colAx i k j

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 4 3 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

def Controls (π : List C) (U : Finset C) : Prop :=
  ∀ a : V → Bool, (∀ B ∈ PHP 4 3, ¬ Coll B → ClauseSat a B) →
    (∀ B ∈ U, Coll B → ClauseSat a B) →
    ∀ R ∈ π, ¬ Coll R → ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem collisionNoPos {N : C} (hN : Coll N) (v : V) : (v, true) ∉ N := by
  obtain ⟨i, k, j, _, rfl⟩ := hN
  simp [colAx]

theorem collisionNonempty {N : C} (hN : Coll N) : N ≠ ∅ := by
  obtain ⟨i, k, j, _, rfl⟩ := hN
  simp [colAx]

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 4 3 := by
  obtain ⟨i, k, j, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

theorem phpCases {B : C} : B ∈ PHP 4 3 ↔ (∃ r : Row, B = rowAx r) ∨ Coll B := by
  change ((∃ r : Row, B = rowAx r) ∨ (∃ i k : Row, ∃ j : Hole, i ≠ k ∧ B = colAx i k j)) ↔ _
  rfl

def rowMatch (i : Row) (v : V) : Bool :=
  (v.1 != i) && ((if v.1.val < i.val then v.1.val else v.1.val - 1) == v.2.val)

theorem rowMatch_spec :
    ∀ i : Row,
      (∀ j : Hole, rowMatch i (i, j) = false) ∧
      (∀ r : Row, r ≠ i → ∃ j : Hole, rowMatch i (r, j) = true) ∧
      (∀ r s : Row, ∀ j : Hole, rowMatch i (r, j) = true → rowMatch i (s, j) = true → r = s) := by
  decide +kernel

def colMatch (i k : Row) (j : Hole) (v : V) : Bool :=
  if v.1 == i || v.1 == k then v.2 == j
  else if v.2 == j then false
  else
    let rk := v.1.val - (if i.val < v.1.val then 1 else 0) - (if k.val < v.1.val then 1 else 0)
    let hq := v.2.val - (if j.val < v.2.val then 1 else 0)
    rk == hq

theorem colMatch_spec :
    ∀ i k : Row, ∀ j : Hole, i ≠ k →
      colMatch i k j (i, j) = true ∧
      colMatch i k j (k, j) = true ∧
      (∀ r : Row, ∃ q : Hole, colMatch i k j (r, q) = true) ∧
      (∀ r s : Row, ∀ q : Hole, r ≠ s →
        colMatch i k j (r, q) = true → colMatch i k j (s, q) = true →
        q = j ∧ ((r = i ∧ s = k) ∨ (r = k ∧ s = i))) := by
  decide +kernel

theorem satRowOf {a : V → Bool} {r : Row} {j : Hole} (h : a (r, j) = true) :
    ClauseSat a (rowAx r) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, h⟩

theorem satColOf {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

theorem critical {B : C} (hB : B ∈ PHP 4 3) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 4 3, D ≠ B → ClauseSat a D := by
  rcases phpCases.mp hB with ⟨i, rfl⟩ | ⟨i, k, j, hik, rfl⟩
  · obtain ⟨h0, hrow, hinj⟩ := rowMatch_spec i
    refine ⟨rowMatch i, ?_, ?_⟩
    · rintro ⟨l, hl, hal⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
      have := h0 j
      simp [this] at hal
    · intro D hD hne
      rcases phpCases.mp hD with ⟨r, rfl⟩ | ⟨r, s, q, hrs, rfl⟩
      · have hri : r ≠ i := fun e => hne (congrArg rowAx e)
        obtain ⟨j, hj⟩ := hrow r hri
        exact satRowOf hj
      · exact satColOf (fun ⟨hr, hs⟩ => hrs (hinj r s q hr hs))
  · obtain ⟨hi, hk, hrow, hinj⟩ := colMatch_spec i k j hik
    refine ⟨colMatch i k j, ?_, ?_⟩
    · rintro ⟨l, hl, hal⟩
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · simp [hi] at hal
      · simp [hk] at hal
    · intro D hD hne
      rcases phpCases.mp hD with ⟨r, rfl⟩ | ⟨r, s, q, hrs, rfl⟩
      · obtain ⟨q, hq⟩ := hrow r
        exact satRowOf hq
      · apply satColOf
        intro ⟨hr, hs⟩
        obtain ⟨hqj, ⟨hri, hsk⟩ | ⟨hrk, hsi⟩⟩ := hinj r s q hrs hr hs
        · rw [hri, hsk, hqj] at hne; exact hne rfl
        · rw [hrk, hsi, hqj] at hne; exact hne (Finset.pair_comm ((k, j), false) ((i, j), false))

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Coll B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, k, j, ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, k, j, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · refine Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, ?_⟩
      exact Finset.pair_comm ((k, j), false) ((i, j), false)

theorem collisionBank_card : collisionBank.card = 18 := by decide +kernel

def axiomBank : Finset C :=
  (Finset.univ.image (fun r : Row => rowAx r)) ∪ collisionBank

theorem mem_axiomBank (B : C) : B ∈ axiomBank ↔ B ∈ PHP 4 3 := by
  rw [phpCases]
  simp only [axiomBank, Finset.mem_union, mem_collisionBank, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h

theorem axiomBank_card : axiomBank.card = 22 := by decide +kernel

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

theorem requiredCollisions {π : List C} {U : Finset C} (hc : Controls π U)
    (he : (∅ : C) ∈ π) : collisionBank ⊆ U := by
  classical
  intro B hB
  have hcolB : Coll B := (mem_collisionBank B).mp hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical (collisionPHP hcolB)
  have hr : ∀ D ∈ PHP 4 3, ¬ Coll D → ClauseSat a D := by
    intro D hDP hDC
    exact hrest D hDP (fun e => hDC (e.symm ▸ hcolB))
  have hu : ∀ D ∈ U, Coll D → ClauseSat a D := by
    intro D hDU hDC
    exact hrest D (collisionPHP hDC) (fun e => hm (e ▸ hDU))
  exact emptyUnsat a (hc a hr hu ∅ he (fun h => collisionNonempty h rfl))


def fBits : Nat := (((((((((419296182304 + (1047435174304 <<< 48)) + ((9499930791968 + (1256814862368 <<< 48)) <<< 96)) + (((9838159462496 + (1256814805920 <<< 48)) + ((9703874625568 + (1396334707484 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (0 <<< 48)) + ((0 + (8589934592 <<< 48)) <<< 96)) + (((0 + (549755813888 <<< 48)) + ((8796126838784 + (67633152 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((419296719072 + (1047435174304 <<< 48)) + ((13818520691104 + (1116121653792 <<< 48)) <<< 96)) + (((13547937751456 + (1048475894688 <<< 48)) + ((40001648218464 + (1117112025882 <<< 48)) <<< 96)) <<< 192)) + ((((8796093022208 + (279172874242 <<< 48)) + ((8870181208064 + (759303786688 <<< 48)) <<< 96)) + (((9140764147712 + (218137899328 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((962609549344 + (1256815371232 <<< 48)) + ((18774846361632 + (1598181938012 <<< 48)) <<< 96)) + (((5852362761115 + (1326524441948 <<< 48)) + ((19190300865435 + (1462873187355 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (137438957633 <<< 48)) + ((17597555015680 + (4329046144 <<< 48)) <<< 96)) + (((69793218560 + (488553054209 <<< 48)) + ((22546431344832 + (150475670016 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((9560043839648 + (1324444062496 <<< 48)) + ((36158743290400 + (1453142893275 <<< 48)) <<< 96)) + (((22755240620382 + (1320099054234 <<< 48)) + ((9908944151323 + (1186855457753 <<< 48)) <<< 96)) <<< 192)) + ((((17868188024833 + (626093732036 <<< 48)) + ((13747167428800 + (696053694723 <<< 48)) <<< 96)) + (((13540975181824 + (487580250438 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) + (((((((15569256544 + (1256815391392 <<< 48)) + ((5108259677083 + (1326524486300 <<< 48)) <<< 96)) + (((18504263401824 + (1124661777500 <<< 48)) + ((18716780717019 + (1259935958427 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (2147487809 <<< 48)) + ((69793218560 + (488553054209 <<< 48)) <<< 96)) + (((17935783690240 + (274911993856 <<< 48)) + ((22411139887104 + (826933019136 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((9289460883872 + (1189152604768 <<< 48)) + ((22552303391454 + (914224620570 <<< 48)) <<< 96)) + (((35955806077600 + (641394062235 <<< 48)) + ((9638361219739 + (1186855449689 <<< 48)) <<< 96)) <<< 192)) + ((((17665250820097 + (490802262212 <<< 48)) + ((13405683712000 + (419934523590 <<< 48)) <<< 96)) + (((13408938766336 + (560762208771 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((9634081407008 + (1396334711644 <<< 48)) + ((10325555475355 + (1462873715735 <<< 48)) <<< 96)) + (((9919681061851 + (1259936482775 <<< 48)) + ((18709315384276 + (907648500762 <<< 48)) <<< 96)) <<< 192)) + ((((69793218563 + (349100834820 <<< 48)) + ((22135289679936 + (564856643976 <<< 48)) <<< 96)) + (((22473518354496 + (970731053448 <<< 48)) + ((4956561096965 + (279426384130 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((31624331613535 + (837938381854 <<< 48)) + ((14374636647193 + (904394507035 <<< 48)) <<< 96)) + (((13968762257881 + (701457286171 <<< 48)) + ((22548882703126 + (1047251194962 <<< 48)) <<< 96)) <<< 192)) + ((((13961932836929 + (767944315207 <<< 48)) + ((5157250417154 + (694897111308 <<< 48)) <<< 96)) + (((4616084553986 + (491959894476 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) <<< 3072)) + ((((((((419296719072 + (1047435174304 <<< 48)) + ((5029943861408 + (1324444332511 <<< 48)) <<< 96)) + (((5232881050016 + (1189152846559 <<< 48)) + ((5515242198367 + (837939938077 <<< 48)) <<< 96)) <<< 192)) + ((((13543105626112 + (349049983041 <<< 48)) + ((556298928128 + (143965552704 <<< 48)) <<< 96)) + (((421007458304 + (414548496384 <<< 48)) + ((17871392473088 + (279207240065 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((9703942283680 + (1117161837408 <<< 48)) + ((14025719836768 + (1181570098016 <<< 48)) <<< 96)) + (((13619845403104 + (843341419424 <<< 48)) + ((22897998209696 + (1186922566747 <<< 48)) <<< 96)) <<< 192)) + ((((4816923537601 + (488636956933 <<< 48)) + ((13676350816327 + (557407305733 <<< 48)) <<< 96)) + (((13270476394759 + (489761538565 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((9767292789152 + (1116121895264 <<< 48)) + ((18566523691552 + (1453143941853 <<< 48)) <<< 96)) + (((9500904411870 + (914225398494 <<< 48)) + ((31899176956697 + (904393462491 <<< 48)) <<< 96)) <<< 192)) + ((((17940179845121 + (418843480325 <<< 48)) + ((22409143136320 + (695987101894 <<< 48)) <<< 96)) + (((421041541377 + (558530830727 <<< 48)) + ((57662235517376 + (423122710790 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((18568755048544 + (1181569827230 <<< 48)) + ((18498878219104 + (914090939163 <<< 48)) <<< 96)) + (((13963408998944 + (977458217692 <<< 48)) + ((62413829366431 + (912027345555 <<< 48)) <<< 96)) <<< 192)) + ((((17944507855041 + (490884833539 <<< 48)) + ((13612010717576 + (622905020680 <<< 48)) <<< 96)) + (((214883397956 + (283535753672 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) + (((((((9361418379680 + (1048476144224 <<< 48)) + ((9906778845534 + (1320099820062 <<< 48)) <<< 96)) + (((18363586478752 + (641395110813 <<< 48)) + ((31628594037209 + (701456233563 <<< 48)) <<< 96)) <<< 192)) + ((((17872534110209 + (418843476293 <<< 48)) + ((556333023297 + (558530846855 <<< 48)) <<< 96)) + (((22409143128256 + (560695619974 <<< 48)) + ((57594589770368 + (693705654470 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((18501109289440 + (843341128478 <<< 48)) + ((14031054733856 + (977458213660 <<< 48)) <<< 96)) + (((18431232496288 + (1319965344603 <<< 48)) + ((62616766555039 + (1182610269075 <<< 48)) <<< 96)) <<< 192)) + ((((18147445059777 + (626176311427 <<< 48)) + ((553112064452 + (554118705416 <<< 48)) <<< 96)) + (((13544364990728 + (284676342088 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((18430141419872 + (1117113311644 <<< 48)) + ((27573037343515 + (1186854404891 <<< 48)) <<< 96)) + (((27437745881755 + (1186854388763 <<< 48)) + ((9982882136854 + (1047251943954 <<< 48)) <<< 96)) <<< 192)) + ((((22409126346752 + (139804549257 <<< 48)) + ((18220476817798 + (489795907974 <<< 48)) <<< 96)) + (((18220476817798 + (557441638854 <<< 48)) + ((698069053897 + (134234375 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((27575217595040 + (1186922287963 <<< 48)) + ((18565317059231 + (912029959130 <<< 48)) <<< 96)) + (((18294734103455 + (1182612910874 <<< 48)) + ((768063624020 + (436253396 <<< 48)) <<< 96)) <<< 192)) + ((((22548680028357 + (767910494467 <<< 48)) + ((966502670662 + (83923589 <<< 48)) <<< 96)) + (((290045317510 + (83927621 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) <<< 3072)) <<< 6144)) + (((((((((0 + (0 <<< 48)) + ((69809995776 + (137438953472 <<< 48)) <<< 96)) + (((69809995776 + (2147483648 <<< 48)) + ((8796160131075 + (349100314688 <<< 48)) <<< 96)) <<< 192)) + ((((524288 + (0 <<< 48)) + ((0 + (524288 <<< 48)) <<< 96)) + (((0 + (524288 <<< 48)) + ((22199612211200 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((69809995776 + (349050786112 <<< 48)) + ((4746023534593 + (418844266758 <<< 48)) <<< 96)) + (((4678377799681 + (418844262726 <<< 48)) + ((139737694208 + (139805876616 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (139653820608 <<< 48)) + ((0 + (487529918469 <<< 48)) <<< 96)) + (((0 + (419884171461 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((0 + (8589934592 <<< 48)) + ((8798240768000 + (4329570624 <<< 48)) <<< 96)) + (((8796109799424 + (488552534080 <<< 48)) + ((22409127399488 + (564856627654 <<< 48)) <<< 96)) <<< 192)) + ((((8796093022208 + (0 <<< 48)) + ((17593260048384 + (348983918656 <<< 48)) <<< 96)) + (((22058952032256 + (209380966464 <<< 48)) + ((26737279500352 + (213709512832 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((4399120252928 + (143965323654 <<< 48)) + ((18007825068096 + (695987364233 <<< 48)) <<< 96)) + (((9210675347521 + (558530331016 <<< 48)) + ((31273905840518 + (489795129929 <<< 48)) <<< 96)) <<< 192)) + ((((4398046511104 + (142926160130 <<< 48)) + ((17870369849664 + (622838169926 <<< 48)) <<< 96)) + (((8935763345408 + (280313999552 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) + (((((((0 + (549755813888 <<< 48)) + ((8796109799424 + (488552534080 <<< 48)) <<< 96)) + (((8933532237824 + (274912530432 <<< 48)) + ((22409127399488 + (970731057286 <<< 48)) <<< 96)) <<< 192)) + ((((8796093022208 + (0 <<< 48)) + ((21991306297344 + (209380970496 <<< 48)) <<< 96)) + (((17660905783296 + (348983922688 <<< 48)) + ((26737279504384 + (484292436352 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((4466765987840 + (414548255238 <<< 48)) + ((8940092395777 + (558530322952 <<< 48)) <<< 96)) + (((17804887855296 + (560695894409 <<< 48)) + ((31206260105606 + (557440864841 <<< 48)) <<< 96)) <<< 192)) + ((((4398046511104 + (345863372930 <<< 48)) + ((8935763345408 + (347959734464 <<< 48)) <<< 96)) + (((17802724134912 + (284609499398 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((8796093284352 + (67633154 <<< 48)) + ((13752485806272 + (150476194176 <<< 48)) <<< 96)) + (((13752485818368 + (826933535232 <<< 48)) + ((31065533071621 + (279424827914 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (1323200 <<< 48)) + ((22404697686080 + (213709771074 <<< 48)) <<< 96)) + (((22134114750464 + (484292710722 <<< 48)) + ((349085397440 + (50352455 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((13612915621888 + (279207493890 <<< 48)) + ((22200787706304 + (423124824457 <<< 48)) <<< 96)) + (((22268433429120 + (693707760073 <<< 48)) + ((279292965321 + (134259336 <<< 48)) <<< 96)) <<< 192)) + ((((418810429440 + (349034533186 <<< 48)) + ((484341985476 + (33575111 <<< 48)) <<< 96)) + (((213759045828 + (33567047 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) <<< 3072)) + ((((((((33554432 + (279173398528 <<< 48)) + ((26597725831169 + (626093211715 <<< 48)) <<< 96)) + (((26597725831169 + (490801729795 <<< 48)) + ((13543223857217 + (767944340164 <<< 48)) <<< 96)) <<< 192)) + ((((4607426166784 + (139653545984 <<< 48)) + ((17733953519616 + (142925365248 <<< 48)) <<< 96)) + (((17869244989440 + (345862569984 <<< 48)) + ((22339232989184 + (349033226627 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((9075350057153 + (488636703111 <<< 48)) + ((4539831038145 + (490885632520 <<< 48)) <<< 96)) + (((4675122507969 + (626177114440 <<< 48)) + ((9075317289157 + (767911297542 <<< 48)) <<< 96)) <<< 192)) + ((((17731823079488 + (349067812995 <<< 48)) + ((9141905809408 + (279240790080 <<< 48)) <<< 96)) + (((8938968580480 + (279240773952 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((9142911631360 + (759303770432 <<< 48)) + ((9350194659520 + (696053956803 <<< 48)) <<< 96)) + (((13541059067904 + (419934515521 <<< 48)) + ((26873813025282 + (694895816900 <<< 48)) <<< 96)) <<< 192)) + ((((13400381849600 + (487529119744 <<< 48)) + ((13474487599424 + (622838431941 <<< 48)) <<< 96)) + (((4607426166784 + (347959992453 <<< 48)) + ((346936586436 + (33583301 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((18142026285127 + (557407039558 <<< 48)) + ((9144120656264 + (622905286987 <<< 48)) <<< 96)) + (((13679605862852 + (554117923016 <<< 48)) + ((629297406278 + (83943688 <<< 48)) <<< 96)) <<< 192)) + ((((13538811469824 + (279240528004 <<< 48)) + ((209430790273 + (151007427 <<< 48)) <<< 96)) + (((207265730625 + (100667586 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) + (((((((9007620161536 + (218137907264 <<< 48)) + ((13405767598080 + (487580258497 <<< 48)) <<< 96)) + (((9079611731968 + (560762466819 <<< 48)) + ((26670875836674 + (491958579908 <<< 48)) <<< 96)) <<< 192)) + ((((13197444644864 + (419883384832 <<< 48)) + ((4607426166784 + (280314257541 <<< 48)) <<< 96)) + (((13542133354496 + (284609753349 <<< 48)) + ((211645116612 + (33567173 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((17600860393735 + (489761280454 <<< 48)) + ((13476668666180 + (283534963208 <<< 48)) <<< 96)) + (((9076474929416 + (284676608395 <<< 48)) + ((696943137158 + (83903368 <<< 48)) <<< 96)) <<< 192)) + ((((13268228505984 + (279240515908 <<< 48)) + ((71974260801 + (100675650 <<< 48)) <<< 96)) + (((209430782209 + (151007427 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) + ((((((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) + (((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) + (((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) + (((((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) + (((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) + ((((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) + (((0 + (0 <<< 48)) + ((0 + (0 <<< 48)) <<< 96)) <<< 192)) <<< 384)) <<< 768)) <<< 1536)) <<< 3072)) <<< 6144)) <<< 12288))

def fVal (c : Nat) : Nat := (fBits >>> (6 * c)) &&& 63

def pLut (p : Fin 24) : Nat :=
  match p.val with
  | 0 => 1070935975390360080
  | 1 => 1070860917687202320
  | 2 => 1061403209575322640
  | 3 => 1061290623020586000
  | 4 => 1042262620242090000
  | 5 => 1042225091390511120
  | 6 => 1003380950171922720
  | 7 => 1003305892468764960
  | 8 => 989081801449366560
  | 9 => 988950450468840480
  | 10 => 969941212116133920
  | 11 => 969884918838765600
  | 12 => 858738133920010560
  | 13 => 858625547365273920
  | 14 => 853971751012491840
  | 15 => 853840400031965760
  | 16 => 825260867012642880
  | 17 => 825242102586853440
  | 18 => 569377443713028480
  | 19 => 569339914861449600
  | 20 => 564611060805509760
  | 21 => 564554767528141440
  | 22 => 555040766138893440
  | _ => 555022001713104000


def mapNib (lut nib : Nat) : Nat := (lut >>> (4 * nib)) &&& 15

def pack3 (n0 n1 n2 : Nat) : Nat := n0 ||| (n1 <<< 4) ||| (n2 <<< 8)

def nib (c : Nat) (j : Hole) : Nat := (c >>> (4 * j.val)) &&& 15

def bitIn (m : Nat) (p : Row) : Bool := ((m >>> p.val) &&& 1) == 1

def is3 (x : Nat) : Bool := x == 7 || x == 11 || x == 13 || x == 14

def isReach3 (c0 c1 c2 : Nat) : Bool :=
  c0 != 15 && c1 != 15 && c2 != 15 && !(is3 c0 && is3 c1 && is3 c2)

def isReach (c : Nat) : Bool :=
  c < 4096 && isReach3 (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15)

def no15 (c : Nat) : Bool :=
  c < 4096 && (c &&& 15) < 15 && ((c >>> 4) &&& 15) < 15 && ((c >>> 8) &&& 15) < 15

def applyH6 (ht n0 n1 n2 : Nat) : Nat :=
  match ht with
  | 0 => pack3 n0 n1 n2
  | 1 => pack3 n0 n2 n1
  | 2 => pack3 n1 n0 n2
  | 3 => pack3 n1 n2 n0
  | 4 => pack3 n2 n0 n1
  | _ => pack3 n2 n1 n0

def actG3 (p : Fin 24) (h : Fin 6) (n0 n1 n2 : Nat) : Nat :=
  let lut := pLut p
  applyH6 h.val (mapNib lut n0) (mapNib lut n1) (mapNib lut n2)

def actG (p : Fin 24) (h : Fin 6) (c : Nat) : Nat :=
  actG3 p h (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15)


def compPNat (p1 p2 : Fin 24) : Nat :=
  match p1.val with
  | 0 => if p2.val < 12 then (407901468851537952 >>> (5 * p2.val)) &&& 31 else (854193664183220652 >>> (5 * (p2.val - 12))) &&& 31
  | 1 => if p2.val < 12 then (333664609412222977 >>> (5 * p2.val)) &&& 31 else (631047566933021298 >>> (5 * (p2.val - 12))) &&& 31
  | 2 => if p2.val < 12 then (631047566276984930 >>> (5 * p2.val)) &&& 31 else (779956804605223142 >>> (5 * (p2.val - 12))) &&& 31
  | 3 => if p2.val < 12 then (556810706801005635 >>> (5 * p2.val)) &&& 31 else (407901469405862483 >>> (5 * (p2.val - 12))) &&& 31
  | 4 => if p2.val < 12 then (854193663665767588 >>> (5 * p2.val)) &&& 31 else (556810707078064327 >>> (5 * (p2.val - 12))) &&& 31
  | 5 => if p2.val < 12 then (779956804226452613 >>> (5 * p2.val)) &&& 31 else (333664609827864973 >>> (5 * (p2.val - 12))) &&& 31
  | 6 => if p2.val < 12 then (184755371601338598 >>> (5 * p2.val)) &&& 31 else (819218270138053102 >>> (5 * (p2.val - 12))) &&& 31
  | 7 => if p2.val < 12 then (110518512162023623 >>> (5 * p2.val)) &&& 31 else (596072172887853748 >>> (5 * (p2.val - 12))) &&& 31
  | 8 => if p2.val < 12 then (596072172472211752 >>> (5 * p2.val)) &&& 31 else (705613396552288288 >>> (5 * (p2.val - 12))) &&& 31
  | 9 => if p2.val < 12 then (482467299163712777 >>> (5 * p2.val)) &&& 31 else (184755371878604437 >>> (5 * (p2.val - 12))) &&& 31
  | 10 => if p2.val < 12 then (819218269860994410 >>> (5 * p2.val)) &&& 31 else (482467299025129473 >>> (5 * (p2.val - 12))) &&& 31
  | 11 => if p2.val < 12 then (705613396589159755 >>> (5 * p2.val)) &&& 31 else (110518512300606927 >>> (5 * (p2.val - 12))) &&& 31
  | 12 => if p2.val < 12 then (149779977796565420 >>> (5 * p2.val)) &&& 31 else (744874862085118248 >>> (5 * (p2.val - 12))) &&& 31
  | 13 => if p2.val < 12 then (36175104524730765 >>> (5 * p2.val)) &&& 31 else (372926075360595702 >>> (5 * (p2.val - 12))) &&& 31
  | 14 => if p2.val < 12 then (372926075222012398 >>> (5 * p2.val)) &&& 31 else (670638002507120738 >>> (5 * (p2.val - 12))) &&& 31
  | 15 => if p2.val < 12 then (259321201913513423 >>> (5 * p2.val)) &&& 31 else (149779977833436887 >>> (5 * (p2.val - 12))) &&& 31
  | 16 => if p2.val < 12 then (744874862223701552 >>> (5 * p2.val)) &&& 31 else (259321201497871427 >>> (5 * (p2.val - 12))) &&& 31
  | 17 => if p2.val < 12 then (670638002784386577 >>> (5 * p2.val)) &&& 31 else (36175104247672073 >>> (5 * (p2.val - 12))) &&& 31
  | 18 => if p2.val < 12 then (75436570159272562 >>> (5 * p2.val)) &&& 31 else (521728764557860202 >>> (5 * (p2.val - 12))) &&& 31
  | 19 => if p2.val < 12 then (1199710719957587 >>> (5 * p2.val)) &&& 31 else (298582667307660848 >>> (5 * (p2.val - 12))) &&& 31
  | 20 => if p2.val < 12 then (298582667584719540 >>> (5 * p2.val)) &&& 31 else (447491904979862692 >>> (5 * (p2.val - 12))) &&& 31
  | 21 => if p2.val < 12 then (224345808108740245 >>> (5 * p2.val)) &&& 31 else (75436569780502033 >>> (5 * (p2.val - 12))) &&& 31
  | 22 => if p2.val < 12 then (521728764973502198 >>> (5 * p2.val)) &&& 31 else (224345807452703877 >>> (5 * (p2.val - 12))) &&& 31
  | _ => if p2.val < 12 then (447491905534187223 >>> (5 * p2.val)) &&& 31 else (1199710202504523 >>> (5 * (p2.val - 12))) &&& 31

theorem compPNat_lt : ∀ p1 p2 : Fin 24, compPNat p1 p2 < 24 := by decide +kernel

def compP (p1 p2 : Fin 24) : Fin 24 := ⟨compPNat p1 p2, compPNat_lt p1 p2⟩

def invP (p : Fin 24) : Fin 24 :=
  match p.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨3, by decide⟩
  | 5 => ⟨5, by decide⟩
  | 6 => ⟨6, by decide⟩
  | 7 => ⟨7, by decide⟩
  | 8 => ⟨12, by decide⟩
  | 9 => ⟨18, by decide⟩
  | 10 => ⟨13, by decide⟩
  | 11 => ⟨19, by decide⟩
  | 12 => ⟨8, by decide⟩
  | 13 => ⟨10, by decide⟩
  | 14 => ⟨14, by decide⟩
  | 15 => ⟨20, by decide⟩
  | 16 => ⟨16, by decide⟩
  | 17 => ⟨22, by decide⟩
  | 18 => ⟨9, by decide⟩
  | 19 => ⟨11, by decide⟩
  | 20 => ⟨15, by decide⟩
  | 21 => ⟨21, by decide⟩
  | 22 => ⟨17, by decide⟩
  | _ => ⟨23, by decide⟩

def compHNat (h1 h2 : Fin 6) : Nat :=
  match h1.val with
  | 0 => (181896 >>> (3 * h2.val)) &&& 7
  | 1 => (152769 >>> (3 * h2.val)) &&& 7
  | 2 => (104994 >>> (3 * h2.val)) &&& 7
  | 3 => (67691 >>> (3 * h2.val)) &&& 7
  | 4 => (45396 >>> (3 * h2.val)) &&& 7
  | _ => (8989 >>> (3 * h2.val)) &&& 7

theorem compHNat_lt : ∀ h1 h2 : Fin 6, compHNat h1 h2 < 6 := by decide +kernel

def compH (h1 h2 : Fin 6) : Fin 6 := ⟨compHNat h1 h2, compHNat_lt h1 h2⟩

def invH (h : Fin 6) : Fin 6 :=
  match h.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨3, by decide⟩
  | _ => ⟨5, by decide⟩


theorem compP_invR : ∀ p1 p2 : Fin 24, compP (compP p1 p2) (invP p2) = p1 := by decide +kernel
theorem compP_invL : ∀ p1 p2 : Fin 24, compP (compP p1 (invP p2)) p2 = p1 := by decide +kernel
theorem compH_invR : ∀ h1 h2 : Fin 6, compH (compH h1 h2) (invH h2) = h1 := by decide +kernel
theorem compH_invL : ∀ h1 h2 : Fin 6, compH (compH h1 (invH h2)) h2 = h1 := by decide +kernel

theorem mapNib_lt15 : ∀ p : Fin 24, ∀ x : Fin 15, mapNib (pLut p) x.val < 15 := by decide +kernel

theorem mapNib_comp : ∀ p1 p2 : Fin 24, ∀ x : Fin 15,
    mapNib (pLut p1) (mapNib (pLut p2) x.val) = mapNib (pLut (compP p1 p2)) x.val := by
  decide +kernel

theorem nib_pack3 : ∀ a b c : Fin 15,
    (pack3 a.val b.val c.val &&& 15) = a.val ∧
    ((pack3 a.val b.val c.val >>> 4) &&& 15) = b.val ∧
    ((pack3 a.val b.val c.val >>> 8) &&& 15) = c.val ∧
    pack3 a.val b.val c.val < 4096 := by
  decide +kernel

def hCoord (h : Fin 6) (q : Fin 3) : Fin 3 :=
  match h.val, q.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2
  | 3, 0 => 1 | 3, 1 => 2 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, _ => 1
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

theorem hCoord_comp : ∀ h1 h2 : Fin 6, ∀ q : Fin 3,
    hCoord (compH h1 h2) q = hCoord h2 (hCoord h1 q) := by
  decide +kernel

theorem applyH6_eq_pack3 (h : Fin 6) (a : Fin 3 → Nat) :
    applyH6 h.val (a 0) (a 1) (a 2) = pack3 (a (hCoord h 0)) (a (hCoord h 1)) (a (hCoord h 2)) := by
  fin_cases h <;> rfl

theorem actG_no15 (p : Fin 24) (h : Fin 6) (c : Nat) (hc : no15 c = true) :
    no15 (actG p h c) = true := by
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
  obtain ⟨⟨⟨_, h0⟩, h1⟩, h2⟩ := hc
  let a : Fin 3 → Nat := fun q =>
    match q.val with
    | 0 => mapNib (pLut p) (c &&& 15)
    | 1 => mapNib (pLut p) ((c >>> 4) &&& 15)
    | _ => mapNib (pLut p) ((c >>> 8) &&& 15)
  have ha : ∀ q : Fin 3, a q < 15 := by
    intro q
    fin_cases q
    · exact mapNib_lt15 p ⟨c &&& 15, h0⟩
    · exact mapNib_lt15 p ⟨(c >>> 4) &&& 15, h1⟩
    · exact mapNib_lt15 p ⟨(c >>> 8) &&& 15, h2⟩
  have hact : actG p h c = pack3 (a (hCoord h 0)) (a (hCoord h 1)) (a (hCoord h 2)) := by
    change applyH6 h.val (a 0) (a 1) (a 2) = _
    exact applyH6_eq_pack3 h a
  rw [hact]
  have hp := nib_pack3 ⟨a (hCoord h 0), ha _⟩ ⟨a (hCoord h 1), ha _⟩ ⟨a (hCoord h 2), ha _⟩
  exact ⟨⟨⟨hp.2.2.2, by rw [hp.1]; exact ha _⟩, by rw [hp.2.1]; exact ha _⟩, by rw [hp.2.2.1]; exact ha _⟩

theorem actG_comp (p1 p2 : Fin 24) (h1 h2 : Fin 6) (c : Nat) (hc : no15 c = true) :
    actG p1 h1 (actG p2 h2 c) = actG (compP p1 p2) (compH h1 h2) c := by
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨_, h0⟩, h1c⟩, h2c⟩ := hc
  let b : Fin 3 → Nat := fun q =>
    match q.val with
    | 0 => c &&& 15
    | 1 => (c >>> 4) &&& 15
    | _ => (c >>> 8) &&& 15
  have hb : ∀ q : Fin 3, b q < 15 := by
    intro q; fin_cases q <;> assumption
  let a2 : Fin 3 → Nat := fun q => mapNib (pLut p2) (b q)
  have ha2 : ∀ q : Fin 3, a2 q < 15 := fun q => mapNib_lt15 p2 ⟨b q, hb q⟩
  have hinner : actG p2 h2 c = pack3 (a2 (hCoord h2 0)) (a2 (hCoord h2 1)) (a2 (hCoord h2 2)) := by
    change applyH6 h2.val (a2 0) (a2 1) (a2 2) = _
    exact applyH6_eq_pack3 h2 a2
  rw [hinner]
  have hp := nib_pack3 ⟨a2 (hCoord h2 0), ha2 _⟩ ⟨a2 (hCoord h2 1), ha2 _⟩ ⟨a2 (hCoord h2 2), ha2 _⟩
  unfold actG actG3
  rw [hp.1, hp.2.1, hp.2.2.1]
  let a1 : Fin 3 → Nat := fun q => mapNib (pLut p1) (a2 (hCoord h2 q))
  change applyH6 h1.val (a1 0) (a1 1) (a1 2) = _
  rw [applyH6_eq_pack3 h1 a1]
  let a12 : Fin 3 → Nat := fun q => mapNib (pLut (compP p1 p2)) (b q)
  change _ = applyH6 (compH h1 h2).val (a12 0) (a12 1) (a12 2)
  rw [applyH6_eq_pack3 (compH h1 h2) a12]
  have heq : ∀ q : Fin 3, a1 (hCoord h1 q) = a12 (hCoord (compH h1 h2) q) := by
    intro q
    rw [hCoord_comp h1 h2 q]
    exact mapNib_comp p1 p2 ⟨b (hCoord h2 (hCoord h1 q)), hb _⟩
  rw [heq 0, heq 1, heq 2]

theorem and15_lt (x : Nat) : (x &&& 15) < 16 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem and1_lt (x : Nat) : (x &&& 1) < 2 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem isReach_no15 {c : Nat} (hc : isReach c = true) : no15 c = true := by
  simp only [isReach, isReach3, no15, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc ⊢
  obtain ⟨hlt, ⟨⟨⟨h0, h1⟩, h2⟩, _⟩⟩ := hc
  have hm0 : (c &&& 15) < 16 := and15_lt c
  have hm1 : ((c >>> 4) &&& 15) < 16 := and15_lt (c >>> 4)
  have hm2 : ((c >>> 8) &&& 15) < 16 := and15_lt (c >>> 8)
  exact ⟨⟨⟨hlt, by omega⟩, by omega⟩, by omega⟩


def hElem (t : Fin 4) : Fin 24 × Fin 6 :=
  match t.val with
  | 0 => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | 1 => (⟨6, by decide⟩, ⟨0, by decide⟩)
  | 2 => (⟨1, by decide⟩, ⟨1, by decide⟩)
  | _ => (⟨7, by decide⟩, ⟨1, by decide⟩)

def reps36 (k : Fin 36) : Fin 24 × Fin 6 :=
  match k.val with
  | 0 => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | 1 => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨4, by decide⟩)
  | 3 => (⟨1, by decide⟩, ⟨0, by decide⟩)
  | 4 => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | 5 => (⟨1, by decide⟩, ⟨4, by decide⟩)
  | 6 => (⟨2, by decide⟩, ⟨0, by decide⟩)
  | 7 => (⟨2, by decide⟩, ⟨2, by decide⟩)
  | 8 => (⟨2, by decide⟩, ⟨4, by decide⟩)
  | 9 => (⟨3, by decide⟩, ⟨0, by decide⟩)
  | 10 => (⟨3, by decide⟩, ⟨2, by decide⟩)
  | 11 => (⟨3, by decide⟩, ⟨4, by decide⟩)
  | 12 => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | 13 => (⟨4, by decide⟩, ⟨2, by decide⟩)
  | 14 => (⟨4, by decide⟩, ⟨4, by decide⟩)
  | 15 => (⟨5, by decide⟩, ⟨0, by decide⟩)
  | 16 => (⟨5, by decide⟩, ⟨2, by decide⟩)
  | 17 => (⟨5, by decide⟩, ⟨4, by decide⟩)
  | 18 => (⟨12, by decide⟩, ⟨0, by decide⟩)
  | 19 => (⟨12, by decide⟩, ⟨2, by decide⟩)
  | 20 => (⟨12, by decide⟩, ⟨4, by decide⟩)
  | 21 => (⟨13, by decide⟩, ⟨0, by decide⟩)
  | 22 => (⟨13, by decide⟩, ⟨2, by decide⟩)
  | 23 => (⟨13, by decide⟩, ⟨4, by decide⟩)
  | 24 => (⟨16, by decide⟩, ⟨0, by decide⟩)
  | 25 => (⟨16, by decide⟩, ⟨2, by decide⟩)
  | 26 => (⟨16, by decide⟩, ⟨4, by decide⟩)
  | 27 => (⟨18, by decide⟩, ⟨0, by decide⟩)
  | 28 => (⟨18, by decide⟩, ⟨2, by decide⟩)
  | 29 => (⟨18, by decide⟩, ⟨4, by decide⟩)
  | 30 => (⟨19, by decide⟩, ⟨0, by decide⟩)
  | 31 => (⟨19, by decide⟩, ⟨2, by decide⟩)
  | 32 => (⟨19, by decide⟩, ⟨4, by decide⟩)
  | 33 => (⟨22, by decide⟩, ⟨0, by decide⟩)
  | 34 => (⟨22, by decide⟩, ⟨2, by decide⟩)
  | _ => (⟨22, by decide⟩, ⟨4, by decide⟩)

def cosetMap (x : Fin 4 × Fin 36) : Fin 24 × Fin 6 :=
  (compP (hElem x.1).1 (reps36 x.2).1, compH (hElem x.1).2 (reps36 x.2).2)

def cosetInvRow (p : Fin 24) : Nat :=
  match p.val with
  | 0 => 84672260426496
  | 1 => 81386560309251
  | 2 => 94593786270726
  | 3 => 97905256584969
  | 4 => 88022386036236
  | 5 => 91333856350479
  | 6 => 124409904197412
  | 7 => 121124204080167
  | 8 => 134331430041642
  | 9 => 137642900355885
  | 10 => 127760029807152
  | 11 => 131071500121395
  | 12 => 111138252743442
  | 13 => 114449723057685
  | 14 => 150875896514358
  | 15 => 154187366828601
  | 16 => 117761193371928
  | 17 => 157498837142844
  | 18 => 101281152391707
  | 19 => 104592622705950
  | 20 => 141018796162623
  | 21 => 144330266476866
  | 22 => 107904093020193
  | _ => 147641736791109


def cosetInvCode (g : Fin 24 × Fin 6) : Nat :=
  (cosetInvRow g.1 >>> (8 * g.2.val)) &&& 255

theorem cosetInv_lt : ∀ g : Fin 24 × Fin 6, cosetInvCode g < 144 := by decide +kernel

def cosetInv (g : Fin 24 × Fin 6) : Fin 4 × Fin 36 :=
  (⟨cosetInvCode g / 36, by have := cosetInv_lt g; omega⟩,
   ⟨cosetInvCode g % 36, Nat.mod_lt _ (by decide)⟩)

theorem cosetMap_left_inv : ∀ x : Fin 4 × Fin 36, cosetInv (cosetMap x) = x := by decide +kernel
theorem cosetMap_right_inv : ∀ g : Fin 24 × Fin 6, cosetMap (cosetInv g) = g := by decide +kernel

def checkRange (P : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => P k && checkRange P k

theorem checkRange_sound {P : Nat → Bool} {n : Nat} (h : checkRange P n = true) :
    ∀ x, x < n → P x = true := by
  induction n with
  | zero => intro x hx; omega
  | succ k ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    intro x hx
    by_cases hxk : x = k
    · exact hxk ▸ h.1
    · exact ih h.2 x (by omega)

set_option maxRecDepth 20000 in
theorem fVal_hElem_check :
    checkRange (fun c => !no15 c ||
      (fVal (actG (hElem 0).1 (hElem 0).2 c) == fVal c &&
       fVal (actG (hElem 1).1 (hElem 1).2 c) == fVal c &&
       fVal (actG (hElem 2).1 (hElem 2).2 c) == fVal c &&
       fVal (actG (hElem 3).1 (hElem 3).2 c) == fVal c)) 4096 = true := by
  decide +kernel

theorem fVal_hElem (c : Nat) (hlt : c < 4096) (hc : no15 c = true) (t : Fin 4) :
    fVal (actG (hElem t).1 (hElem t).2 c) = fVal c := by
  have h := checkRange_sound fVal_hElem_check c hlt
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  fin_cases t
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

set_option maxRecDepth 20000 in
theorem fVal_le_32_check : checkRange (fun c => decide (fVal c ≤ 32)) 4096 = true := by
  decide +kernel

theorem fVal_le_32 (c : Nat) (hlt : c < 4096) : fVal c ≤ 32 :=
  of_decide_eq_true (checkRange_sound fVal_le_32_check c hlt)

theorem actG_zero : ∀ g : Fin 24 × Fin 6, actG g.1 g.2 0 = 0 := by decide +kernel

theorem fVal_zero : fVal 0 = 32 := by decide +kernel

def maxOver (g : Fin 24 × Fin 6) : List Nat → Nat
  | [] => 0
  | x :: xs => max (fVal (actG g.1 g.2 x)) (maxOver g xs)

theorem le_maxOver {g : Fin 24 × Fin 6} {x : Nat} {L : List Nat} (hx : x ∈ L) :
    fVal (actG g.1 g.2 x) ≤ maxOver g L := by
  induction L with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact le_trans (ih hx) (Nat.le_max_right _ _)

def Psi144 (L : List Nat) : Nat :=
  ∑ g : Fin 24 × Fin 6, maxOver g L

def deltaTerm (g : Fin 24 × Fin 6) (c d e : Nat) : Nat :=
  fVal (actG g.1 g.2 e) - max (fVal (actG g.1 g.2 c)) (fVal (actG g.1 g.2 d))

def delta144 (c d e : Nat) : Nat :=
  ∑ g : Fin 24 × Fin 6, deltaTerm g c d e

def delta36 (c d e : Nat) : Nat :=
  ∑ k : Fin 36, deltaTerm (reps36 k) c d e

theorem Psi144_cons_le {L : List Nat} {c d e : Nat} (hc : c ∈ L) (hd : d ∈ L) :
    Psi144 (e :: L) ≤ Psi144 L + delta144 c d e := by
  unfold Psi144 delta144
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have h1 := le_maxOver (g := g) hc
  have h2 := le_maxOver (g := g) hd
  change max (fVal (actG g.1 g.2 e)) (maxOver g L) ≤ maxOver g L + deltaTerm g c d e
  unfold deltaTerm
  omega

def initBoxes : List Nat := [273, 546, 1092, 2184]

theorem Psi144_init : Psi144 initBoxes = 0 := by decide +kernel

theorem initBoxes_reach : ∀ x ∈ initBoxes, isReach x = true := by decide +kernel

theorem Psi144_zero_le {L : List Nat} (h0 : 0 ∈ L) : 4608 ≤ Psi144 L := by
  unfold Psi144
  have hle : ∑ _g : Fin 24 × Fin 6, (32 : Nat) ≤ ∑ g : Fin 24 × Fin 6, maxOver g L := by
    apply Finset.sum_le_sum
    intro g _
    have h1 := le_maxOver (g := g) h0
    rw [actG_zero g, fVal_zero] at h1
    exact h1
  have hsum : ∑ _g : Fin 24 × Fin 6, (32 : Nat) = 4608 := by decide +kernel
  omega

theorem delta144_actG (p0 : Fin 24) (h0 : Fin 6) (c d e : Nat)
    (hc : no15 c = true) (hd : no15 d = true) (he : no15 e = true) :
    delta144 (actG p0 h0 c) (actG p0 h0 d) (actG p0 h0 e) = delta144 c d e := by
  unfold delta144
  let eqv : (Fin 24 × Fin 6) ≃ (Fin 24 × Fin 6) :=
    ⟨fun g => (compP g.1 p0, compH g.2 h0),
     fun g => (compP g.1 (invP p0), compH g.2 (invH h0)),
     fun g => Prod.ext (compP_invR g.1 p0) (compH_invR g.2 h0),
     fun g => Prod.ext (compP_invL g.1 p0) (compH_invL g.2 h0)⟩
  refine Finset.sum_equiv eqv (fun _ => by simp) (fun g _ => ?_)
  unfold deltaTerm
  simp only [eqv, Equiv.coe_fn_mk]
  rw [actG_comp g.1 p0 g.2 h0 c hc, actG_comp g.1 p0 g.2 h0 d hd, actG_comp g.1 p0 g.2 h0 e he]

theorem delta144_eq_4_delta36 (c d e : Nat)
    (hc : no15 c = true) (hd : no15 d = true) (he : no15 e = true) :
    delta144 c d e = 4 * delta36 c d e := by
  unfold delta144 delta36
  let eqv : (Fin 4 × Fin 36) ≃ (Fin 24 × Fin 6) :=
    ⟨cosetMap, cosetInv, cosetMap_left_inv, cosetMap_right_inv⟩
  have hsum : ∑ g : Fin 24 × Fin 6, deltaTerm g c d e =
      ∑ x : Fin 4 × Fin 36, deltaTerm (cosetMap x) c d e :=
    (Finset.sum_equiv eqv (fun _ => by simp) (fun _ _ => rfl)).symm
  rw [hsum]
  have hterm : ∀ x : Fin 4 × Fin 36, deltaTerm (cosetMap x) c d e = deltaTerm (reps36 x.2) c d e := by
    intro ⟨t, k⟩
    unfold deltaTerm cosetMap
    have hact : ∀ u : Nat, no15 u = true →
        fVal (actG (compP (hElem t).1 (reps36 k).1) (compH (hElem t).2 (reps36 k).2) u) =
        fVal (actG (reps36 k).1 (reps36 k).2 u) := by
      intro u hu
      rw [← actG_comp (hElem t).1 (reps36 k).1 (hElem t).2 (reps36 k).2 u hu]
      have hu' := actG_no15 (reps36 k).1 (reps36 k).2 u hu
      have hlt : actG (reps36 k).1 (reps36 k).2 u < 4096 := by
        simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hu'; exact hu'.1.1.1
      exact fVal_hElem (actG (reps36 k).1 (reps36 k).2 u) hlt hu' t
    rw [hact e he, hact c hc, hact d hd]
  have hrew : ∑ x : Fin 4 × Fin 36, deltaTerm (cosetMap x) c d e =
      ∑ x : Fin 4 × Fin 36, deltaTerm (reps36 x.2) c d e :=
    Finset.sum_congr rfl (fun x _ => hterm x)
  rw [hrew, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]


def permSpec : List (Nat × Nat) := [
  (1070935975390360080, 0),
  (1070935975390360080, 1),
  (1070935975390360080, 2),
  (1070860917687202320, 0),
  (1070860917687202320, 1),
  (1070860917687202320, 2),
  (1061403209575322640, 0),
  (1061403209575322640, 1),
  (1061403209575322640, 2),
  (1061290623020586000, 0),
  (1061290623020586000, 1),
  (1061290623020586000, 2),
  (1042262620242090000, 0),
  (1042262620242090000, 1),
  (1042262620242090000, 2),
  (1042225091390511120, 0),
  (1042225091390511120, 1),
  (1042225091390511120, 2),
  (858738133920010560, 0),
  (858738133920010560, 1),
  (858738133920010560, 2),
  (858625547365273920, 0),
  (858625547365273920, 1),
  (858625547365273920, 2),
  (825260867012642880, 0),
  (825260867012642880, 1),
  (825260867012642880, 2),
  (569377443713028480, 0),
  (569377443713028480, 1),
  (569377443713028480, 2),
  (569339914861449600, 0),
  (569339914861449600, 1),
  (569339914861449600, 2),
  (555040766138893440, 0),
  (555040766138893440, 1),
  (555040766138893440, 2)
]

def applySpec3 (s : Nat × Nat) (n0 n1 n2 : Nat) : Nat :=
  let lut := s.1
  let m0 := mapNib lut n0
  let m1 := mapNib lut n1
  let m2 := mapNib lut n2
  match s.2 with
  | 0 => m0 ||| (m1 <<< 4) ||| (m2 <<< 8)
  | 1 => m1 ||| (m0 <<< 4) ||| (m2 <<< 8)
  | _ => m2 ||| (m0 <<< 4) ||| (m1 <<< 8)

def subOf (m : Nat) : List Nat := (if m < 7 then (if m < 3 then (if m < 1 then [0] else (if m < 2 then [0, 1] else [0, 2])) else (if m < 5 then (if m < 4 then [0, 1, 2, 3] else [0, 4]) else (if m < 6 then [0, 1, 4, 5] else [0, 2, 4, 6]))) else (if m < 11 then (if m < 9 then (if m < 8 then [0, 1, 2, 3, 4, 5, 6, 7] else [0, 8]) else (if m < 10 then [0, 1, 8, 9] else [0, 2, 8, 10])) else (if m < 13 then (if m < 12 then [0, 1, 2, 3, 8, 9, 10, 11] else [0, 4, 8, 12]) else (if m < 14 then [0, 1, 4, 5, 8, 9, 12, 13] else [0, 2, 4, 6, 8, 10, 12, 14]))))
def supOf (m : Nat) : List Nat := (if m < 7 then (if m < 3 then (if m < 1 then [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] else (if m < 2 then [1, 3, 5, 7, 9, 11, 13] else [2, 3, 6, 7, 10, 11, 14])) else (if m < 5 then (if m < 4 then [3, 7, 11] else [4, 5, 6, 7, 12, 13, 14]) else (if m < 6 then [5, 7, 13] else [6, 7, 14]))) else (if m < 11 then (if m < 9 then (if m < 8 then [7] else [8, 9, 10, 11, 12, 13, 14]) else (if m < 10 then [9, 11, 13] else [10, 11, 14])) else (if m < 13 then (if m < 12 then [11] else [12, 13, 14]) else (if m < 14 then [13] else [14]))))


def makeFc (c0 c1 c2 : Nat) : List (Nat × Nat) → List ((Nat × Nat) × Nat)
  | [] => []
  | s :: rest =>
    let fc := fVal (applySpec3 s c0 c1 c2)
    let tail := makeFc c0 c1 c2 rest
    if fc < 32 then (s, fc) :: tail else tail

def insertDesc (x : (Nat × Nat) × Nat × Nat) : List ((Nat × Nat) × Nat × Nat) → List ((Nat × Nat) × Nat × Nat)
  | [] => [x]
  | y :: ys => if x.2.2 - x.2.1 >= y.2.2 - y.2.1 then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List ((Nat × Nat) × Nat × Nat) → List ((Nat × Nat) × Nat × Nat)
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

def scanE (e0 e1 e2 : Nat) : List ((Nat × Nat) × Nat) → Nat × List ((Nat × Nat) × Nat × Nat)
  | [] => (0, [])
  | (s, fc) :: rest =>
    let fe := fVal (applySpec3 s e0 e1 e2)
    let r := scanE e0 e1 e2 rest
    if fe > fc then (r.1 + (fe - fc), (s, fc, fe) :: r.2) else r

def hasCredit (d0 d1 d2 : Nat) : List ((Nat × Nat) × Nat × Nat) → Nat → Bool
  | [], need => need == 0
  | (s, fc, fe) :: rest, need =>
    if need == 0 then true
    else
      let fd := fVal (applySpec3 s d0 d1 d2)
      let cred := min fe fd - fc
      if need <= cred then true
      else hasCredit d0 d1 d2 rest (need - cred)

def checkD0 (act : List ((Nat × Nat) × Nat × Nat)) (need e0 d1 d2 : Nat) : List Nat → Bool
  | [] => true
  | d0 :: rest =>
    let ok :=
      if (e0 &&& d0) == d0 then true
      else if (d0 == 0 && d1 == 0 && d2 == 0) || !isReach3 d0 d1 d2 then true
      else hasCredit d0 d1 d2 act need
    ok && checkD0 act need e0 d1 d2 rest

def checkD2L (act : List ((Nat × Nat) × Nat × Nat)) (need e0 base2 d1 : Nat) : List Nat → Bool
  | [] => true
  | s :: rest =>
    checkD0 act need e0 d1 (base2 ||| s) [0,2,4,6,8,10,12,14] && checkD2L act need e0 base2 d1 rest

def checkD1L (act : List ((Nat × Nat) × Nat × Nat)) (need e0 base1 base2 : Nat) (s2s : List Nat) : List Nat → Bool
  | [] => true
  | s :: rest =>
    checkD2L act need e0 base2 (base1 ||| s) s2s && checkD1L act need e0 base1 base2 s2s rest

def checkCE (fcL : List ((Nat × Nat) × Nat)) (c1 c2 e0 e1 e2 : Nat) (s1s s2s : List Nat) : Bool :=
  let r := scanE e0 e1 e2 fcL
  if r.1 <= 104 then true
  else checkD1L (sortDesc r.2) (r.1 - 104) e0 (e1 ^^^ c1) (e2 ^^^ c2) s2s s1s

def checkC (c : Nat) : Bool :=
  let c0 := c &&& 15; let c1 := (c >>> 4) &&& 15; let c2 := (c >>> 8) &&& 15
  let e0 := c0 &&& 14
  let fcL := makeFc c0 c1 c2 permSpec
  let s1s := subOf c1; let s2s := subOf c2
  (supOf c1).all fun e1 => (supOf c2).all fun e2 => checkCE fcL c1 c2 e0 e1 e2 s1s s2s

def checkList : List Nat → Bool
  | [] => true
  | c :: cs => checkC c && checkList cs

def sumMap {α : Type} (w : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => w x + sumMap w xs

theorem sumMap_insertDesc (w : ((Nat × Nat) × Nat × Nat) → Nat) (x : (Nat × Nat) × Nat × Nat)
    (xs : List ((Nat × Nat) × Nat × Nat)) :
    sumMap w (insertDesc x xs) = w x + sumMap w xs := by
  induction xs with
  | nil => simp [insertDesc, sumMap]
  | cons y ys ih =>
    unfold insertDesc
    split
    · simp [sumMap]
    · simp only [sumMap, ih]; omega

theorem sumMap_sortDesc (w : ((Nat × Nat) × Nat × Nat) → Nat) (xs : List ((Nat × Nat) × Nat × Nat)) :
    sumMap w (sortDesc xs) = sumMap w xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sortDesc, sumMap_insertDesc, sumMap, ih]

def wUpper (x : (Nat × Nat) × Nat × Nat) : Nat := x.2.2 - x.2.1
def wDelta (d0 d1 d2 : Nat) (x : (Nat × Nat) × Nat × Nat) : Nat :=
  x.2.2 - max x.2.1 (fVal (applySpec3 x.1 d0 d1 d2))
def wCredit (d0 d1 d2 : Nat) (x : (Nat × Nat) × Nat × Nat) : Nat :=
  min x.2.2 (fVal (applySpec3 x.1 d0 d1 d2)) - x.2.1

theorem delta_add_credit (d0 d1 d2 : Nat) (xs : List ((Nat × Nat) × Nat × Nat))
    (hxs : ∀ x ∈ xs, x.2.1 ≤ x.2.2) :
    sumMap (wDelta d0 d1 d2) xs + sumMap (wCredit d0 d1 d2) xs = sumMap wUpper xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.2.1 ≤ x.2.2 := hxs x (List.mem_cons_self ..)
    have htail := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [sumMap, wDelta, wCredit, wUpper] at htail ⊢
    omega

theorem delta_le_upper (d0 d1 d2 : Nat) (xs : List ((Nat × Nat) × Nat × Nat)) :
    sumMap (wDelta d0 d1 d2) xs ≤ sumMap wUpper xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [sumMap, wDelta, wUpper]
    omega

theorem hasCredit_sound (d0 d1 d2 : Nat) (xs : List ((Nat × Nat) × Nat × Nat)) :
    ∀ need, hasCredit d0 d1 d2 xs need = true → need ≤ sumMap (wCredit d0 d1 d2) xs := by
  induction xs with
  | nil =>
    intro need h
    simp only [hasCredit, beq_iff_eq] at h
    simp [h, sumMap]
  | cons x xs ih =>
    rcases x with ⟨s, fc, fe⟩
    intro need h
    unfold hasCredit at h
    split at h
    · rename_i hz
      simp only [beq_iff_eq] at hz
      omega
    · dsimp only at h
      split at h
      · rename_i hle
        simp only [sumMap, wCredit]
        omega
      · have ih' := ih _ h
        simp only [sumMap, wCredit] at ih' ⊢
        omega

def deltaFc (e0 e1 e2 d0 d1 d2 : Nat) : List ((Nat × Nat) × Nat) → Nat
  | [] => 0
  | (s, fc) :: rest =>
    (fVal (applySpec3 s e0 e1 e2) - max fc (fVal (applySpec3 s d0 d1 d2))) +
    deltaFc e0 e1 e2 d0 d1 d2 rest

theorem scanE_spec (e0 e1 e2 d0 d1 d2 : Nat) (fcL : List ((Nat × Nat) × Nat)) :
    (scanE e0 e1 e2 fcL).1 = sumMap wUpper (scanE e0 e1 e2 fcL).2 ∧
    (∀ x ∈ (scanE e0 e1 e2 fcL).2, x.2.1 ≤ x.2.2) ∧
    deltaFc e0 e1 e2 d0 d1 d2 fcL = sumMap (wDelta d0 d1 d2) (scanE e0 e1 e2 fcL).2 := by
  induction fcL with
  | nil => simp [scanE, sumMap, deltaFc]
  | cons p rest ih =>
    rcases p with ⟨s, fc⟩
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [scanE]
    split
    · rename_i hgt
      refine ⟨?_, ?_, ?_⟩
      · simp only [sumMap, wUpper, h1]; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · dsimp only; omega
        · exact h2 x hx
      · simp only [deltaFc, sumMap, wDelta, h3]
    · rename_i hng
      refine ⟨h1, h2, ?_⟩
      simp only [deltaFc, h3]
      omega

def deltaSpecs (c0 c1 c2 e0 e1 e2 d0 d1 d2 : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | s :: rest =>
    (fVal (applySpec3 s e0 e1 e2) -
      max (fVal (applySpec3 s c0 c1 c2)) (fVal (applySpec3 s d0 d1 d2))) +
    deltaSpecs c0 c1 c2 e0 e1 e2 d0 d1 d2 rest

theorem pack3_lt4096_fin : ∀ a b c : Fin 16,
    (a.val ||| (b.val <<< 4) ||| (c.val <<< 8)) < 4096 := by
  decide +kernel

theorem applySpec3_lt4096 (s : Nat × Nat) (n0 n1 n2 : Nat) :
    applySpec3 s n0 n1 n2 < 4096 := by
  unfold applySpec3 mapNib
  have h0 : ((s.1 >>> (4 * n0)) &&& 15) < 16 := and15_lt _
  have h1 : ((s.1 >>> (4 * n1)) &&& 15) < 16 := and15_lt _
  have h2 : ((s.1 >>> (4 * n2)) &&& 15) < 16 := and15_lt _
  split
  · exact pack3_lt4096_fin ⟨_, h0⟩ ⟨_, h1⟩ ⟨_, h2⟩
  · exact pack3_lt4096_fin ⟨_, h1⟩ ⟨_, h0⟩ ⟨_, h2⟩
  · exact pack3_lt4096_fin ⟨_, h2⟩ ⟨_, h0⟩ ⟨_, h1⟩

theorem deltaSpecs_eq_makeFc (c0 c1 c2 e0 e1 e2 d0 d1 d2 : Nat) (ss : List (Nat × Nat)) :
    deltaSpecs c0 c1 c2 e0 e1 e2 d0 d1 d2 ss =
    deltaFc e0 e1 e2 d0 d1 d2 (makeFc c0 c1 c2 ss) := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    simp only [deltaSpecs, makeFc]
    split
    · simp only [deltaFc, ih]
    · rename_i hge
      have hfe : fVal (applySpec3 s e0 e1 e2) ≤ 32 :=
        fVal_le_32 (applySpec3 s e0 e1 e2) (applySpec3_lt4096 s e0 e1 e2)
      rw [ih]
      omega

theorem checkD0_sound {act : List ((Nat × Nat) × Nat × Nat)} {need e0 d1 d2 d0 : Nat}
    {ds : List Nat} (h : checkD0 act need e0 d1 d2 ds = true) (hd0 : d0 ∈ ds)
    (hne : (e0 &&& d0) ≠ d0) (hnz : ¬ (d0 = 0 ∧ d1 = 0 ∧ d2 = 0))
    (hr : isReach3 d0 d1 d2 = true) :
    hasCredit d0 d1 d2 act need = true := by
  induction ds with
  | nil => cases hd0
  | cons x xs ih =>
    simp only [checkD0, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd0 with rfl | hd0
    · have h1 := h.1
      have hne' : ((e0 &&& d0) == d0) = false := beq_false_of_ne hne
      have hnz' : (d0 == 0 && d1 == 0 && d2 == 0) = false := by
        cases h0 : (d0 == 0) <;> cases h1' : (d1 == 0) <;> cases h2' : (d2 == 0) <;> simp_all
      simp only [hne', hnz', hr, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
      exact h1
    · exact ih h.2 hd0

theorem checkD2L_sound {act : List ((Nat × Nat) × Nat × Nat)} {need e0 base2 d1 s2 : Nat}
    {s2s : List Nat} (h : checkD2L act need e0 base2 d1 s2s = true) (hs2 : s2 ∈ s2s) :
    checkD0 act need e0 d1 (base2 ||| s2) [0,2,4,6,8,10,12,14] = true := by
  induction s2s with
  | nil => cases hs2
  | cons x xs ih =>
    simp only [checkD2L, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hs2 with rfl | hs2
    · exact h.1
    · exact ih h.2 hs2

theorem checkD1L_sound {act : List ((Nat × Nat) × Nat × Nat)} {need e0 base1 base2 s1 : Nat}
    {s2s s1s : List Nat} (h : checkD1L act need e0 base1 base2 s2s s1s = true) (hs1 : s1 ∈ s1s) :
    checkD2L act need e0 base2 (base1 ||| s1) s2s = true := by
  induction s1s with
  | nil => cases hs1
  | cons x xs ih =>
    simp only [checkD1L, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hs1 with rfl | hs1
    · exact h.1
    · exact ih h.2 hs1

theorem subOf_complete : ∀ m x : Fin 15, (x.val &&& m.val) = x.val → x.val ∈ subOf m.val := by
  decide +kernel

theorem supOf_complete : ∀ m e : Fin 15, (e.val &&& m.val) = m.val → e.val ∈ supOf m.val := by
  decide +kernel

theorem or_decomp : ∀ c e d : Fin 15, (c.val ||| d.val) = e.val →
    (e.val &&& c.val) = c.val ∧
    (d.val &&& c.val) < 15 ∧
    ((d.val &&& c.val) &&& c.val) = (d.val &&& c.val) ∧
    ((e.val ^^^ c.val) ||| (d.val &&& c.val)) = d.val := by
  decide +kernel

theorem d0_mem : ∀ d0 : Fin 15, (d0.val &&& 1) = 0 → d0.val ∈ [0,2,4,6,8,10,12,14] := by
  decide +kernel

theorem list_all_mem {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : l.all p = true) (hx : x ∈ l) : p x = true := by
  exact List.all_eq_true.mp h x hx

theorem checkC_sound {c d0 d1 d2 : Nat} (hc : checkC c = true)
    (hc1 : ((c >>> 4) &&& 15) < 15) (hc2 : ((c >>> 8) &&& 15) < 15)
    (hd0 : d0 < 15) (hd1 : d1 < 15) (hd2 : d2 < 15)
    (he1 : (((c >>> 4) &&& 15) ||| d1) < 15) (he2 : (((c >>> 8) &&& 15) ||| d2) < 15)
    (hd0_even : (d0 &&& 1) = 0)
    (hnotSub : ((((c &&& 15) &&& 14) &&& d0) ≠ d0))
    (hnz : ¬ (d0 = 0 ∧ d1 = 0 ∧ d2 = 0))
    (hr : isReach3 d0 d1 d2 = true) :
    deltaSpecs (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15)
      ((c &&& 15) &&& 14) (((c >>> 4) &&& 15) ||| d1) (((c >>> 8) &&& 15) ||| d2)
      d0 d1 d2 permSpec ≤ 104 := by
  set c0 := c &&& 15
  set c1 := (c >>> 4) &&& 15
  set c2 := (c >>> 8) &&& 15
  set e0 := c0 &&& 14
  set e1 := c1 ||| d1
  set e2 := c2 ||| d2
  have hdec1 := or_decomp ⟨c1, hc1⟩ ⟨e1, he1⟩ ⟨d1, hd1⟩ rfl
  have hdec2 := or_decomp ⟨c2, hc2⟩ ⟨e2, he2⟩ ⟨d2, hd2⟩ rfl
  have he1_mem : e1 ∈ supOf c1 := supOf_complete ⟨c1, hc1⟩ ⟨e1, he1⟩ hdec1.1
  have he2_mem : e2 ∈ supOf c2 := supOf_complete ⟨c2, hc2⟩ ⟨e2, he2⟩ hdec2.1
  unfold checkC at hc
  have hce1 := list_all_mem hc he1_mem
  have hce := list_all_mem hce1 he2_mem
  rw [deltaSpecs_eq_makeFc]
  set fcL := makeFc c0 c1 c2 permSpec
  obtain ⟨hsu, hle_act, hdel⟩ := scanE_spec e0 e1 e2 d0 d1 d2 fcL
  rw [hdel]
  unfold checkCE at hce
  change (if (scanE e0 e1 e2 fcL).1 ≤ 104 then true
    else checkD1L (sortDesc (scanE e0 e1 e2 fcL).2) ((scanE e0 e1 e2 fcL).1 - 104) e0
      (e1 ^^^ c1) (e2 ^^^ c2) (subOf c2) (subOf c1)) = true at hce
  by_cases hle104 : (scanE e0 e1 e2 fcL).1 ≤ 104
  · have := delta_le_upper d0 d1 d2 (scanE e0 e1 e2 fcL).2
    omega
  · simp only [hle104, ↓reduceIte] at hce
    have hs1_mem : (d1 &&& c1) ∈ subOf c1 := subOf_complete ⟨c1, hc1⟩ ⟨d1 &&& c1, hdec1.2.1⟩ hdec1.2.2.1
    have hs2_mem : (d2 &&& c2) ∈ subOf c2 := subOf_complete ⟨c2, hc2⟩ ⟨d2 &&& c2, hdec2.2.1⟩ hdec2.2.2.1
    have h2l := checkD1L_sound hce hs1_mem
    rw [hdec1.2.2.2] at h2l
    have h0l := checkD2L_sound h2l hs2_mem
    rw [hdec2.2.2.2] at h0l
    have hcred := checkD0_sound h0l (d0_mem ⟨d0, hd0⟩ hd0_even) hnotSub hnz hr
    have hcr_le := hasCredit_sound d0 d1 d2 (sortDesc (scanE e0 e1 e2 fcL).2) _ hcred
    rw [sumMap_sortDesc] at hcr_le
    have hsum := delta_add_credit d0 d1 d2 (scanE e0 e1 e2 fcL).2 hle_act
    omega

theorem permSpec_eq_map :
    permSpec = (List.finRange 36).map (fun k : Fin 36 => (pLut (reps36 k).1, (reps36 k).2.val / 2)) := by
  decide +kernel

theorem reps36_h_even : ∀ k : Fin 36,
    (reps36 k).2.val = 0 ∨ (reps36 k).2.val = 2 ∨ (reps36 k).2.val = 4 := by
  decide +kernel

theorem applySpec3_eq_actG3 (k : Fin 36) (n0 n1 n2 : Nat) :
    applySpec3 (pLut (reps36 k).1, (reps36 k).2.val / 2) n0 n1 n2 =
    actG3 (reps36 k).1 (reps36 k).2 n0 n1 n2 := by
  rcases reps36_h_even k with h | h | h <;> simp [applySpec3, actG3, applyH6, pack3, h]

theorem delta36_eq_deltaSpecs (c d e : Nat) :
    delta36 c d e =
    deltaSpecs (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15)
      (e &&& 15) ((e >>> 4) &&& 15) ((e >>> 8) &&& 15)
      (d &&& 15) ((d >>> 4) &&& 15) ((d >>> 8) &&& 15) permSpec := by
  rw [permSpec_eq_map]
  unfold delta36
  have haux : ∀ ks : List (Fin 36),
      (ks.map (fun k => deltaTerm (reps36 k) c d e)).sum =
      deltaSpecs (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15)
        (e &&& 15) ((e >>> 4) &&& 15) ((e >>> 8) &&& 15)
        (d &&& 15) ((d >>> 4) &&& 15) ((d >>> 8) &&& 15)
        (ks.map (fun k => (pLut (reps36 k).1, (reps36 k).2.val / 2))) := by
    intro ks
    induction ks with
    | nil => rfl
    | cons k rest ih =>
      simp only [List.map_cons, List.sum_cons, deltaSpecs, ih]
      congr 1
      unfold deltaTerm actG
      rw [applySpec3_eq_actG3, applySpec3_eq_actG3, applySpec3_eq_actG3]
  rw [← haux (List.finRange 36)]
  rfl


def chunk0 : List Nat := [273]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk0 : checkList chunk0 = true := by decide +kernel


def chunk1 : List Nat := [7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk1 : checkList chunk1 = true := by decide +kernel


def chunk2 : List Nat := [39, 619, 1633, 637, 995, 1905, 3811]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk2 : checkList chunk2 = true := by decide +kernel


def chunk3 : List Nat := [23, 613, 829, 1639, 727, 999, 1913]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk3 : checkList chunk3 = true := by decide +kernel


def chunk4 : List Nat := [17, 363, 377, 855, 1709, 977, 1725]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk4 : checkList chunk4 = true := by decide +kernel


def chunk5 : List Nat := [19, 599, 231, 1641, 733, 1005, 1969]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk5 : checkList chunk5 = true := by decide +kernel


def chunk6 : List Nat := [51, 307, 711, 1697, 739, 1651, 1973]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk6 : checkList chunk6 = true := by decide +kernel


def chunk7 : List Nat := [3, 119, 615, 877, 627, 979, 1761]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk7 : checkList chunk7 = true := by decide +kernel


def chunk8 : List Nat := [35, 359, 617, 961, 629, 981, 1763]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk8 : checkList chunk8 = true := by decide +kernel


def chunk9 : List Nat := [583, 545, 317, 865, 873, 483, 891, 1719]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk9 : checkList chunk9 = true := by decide +kernel


def chunk10 : List Nat := [1, 97, 603, 821, 867, 375, 883, 1659, 3809]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk10 : checkList chunk10 = true := by decide +kernel


def chunk11 : List Nat := [45, 105, 717, 819, 859, 371, 881, 1657, 2025]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk11 : checkList chunk11 = true := by decide +kernel


def chunk12 : List Nat := [295, 547, 563, 817, 851, 1703, 885, 1713]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk12 : checkList chunk12 = true := by decide +kernel


def chunk13 : List Nat := [49, 551, 355, 709, 225, 967, 633, 989, 1769]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk13 : checkList chunk13 = true := by decide +kernel


def chunk14 : List Nat := [37, 279, 705, 611, 823, 963, 631, 983, 1767]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk14 : checkList chunk14 = true := by decide +kernel


def chunk15 : List Nat := [33, 549, 601, 621, 721, 869, 379, 887, 1715]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk15 : checkList chunk15 = true := by decide +kernel


def chunk16 : List Nat := [53, 585, 121, 309, 849, 871, 481, 889, 1717]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk16 : checkList chunk16 = true := by decide +kernel


def chunk17 : List Nat := [291, 55, 305, 605, 625, 857, 369, 749, 2017]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk17 : checkList chunk17 = true := by decide +kernel


def chunk18 : List Nat := [587, 103, 593, 567, 723, 875, 487, 893, 1721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk18 : checkList chunk18 = true := by decide +kernel


def chunk19 : List Nat := [99, 579, 353, 311, 965, 1635, 725, 997, 1907]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk19 : checkList chunk19 = true := by decide +kernel


def chunk20 : List Nat := [293, 275, 595, 597, 115, 1643, 737, 1649, 1971]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk20 : checkList chunk20 = true := by decide +kernel


def chunk21 : List Nat := [289, 577, 361, 707, 123, 973, 635, 993, 1771]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk21 : checkList chunk21 = true := by decide +kernel


def chunk22 : List Nat := [301, 107, 113, 565, 227, 1699, 741, 1655, 2019]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk22 : checkList chunk22 = true := by decide +kernel


def chunk23 : List Nat := [557, 61, 561, 573, 609, 1701, 743, 1723]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t_chunk23 : checkList chunk23 = true := by decide +kernel


def allCReps : List Nat := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++ chunk17 ++ chunk18 ++ chunk19 ++ chunk20 ++ chunk21 ++ chunk22 ++ chunk23

theorem checkList_mem {l : List Nat} {c : Nat} (h : checkList l = true) (hc : c ∈ l) :
    checkC c = true := by
  induction l with
  | nil => cases hc
  | cons x xs ih =>
    simp only [checkList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact ih h.2 hc

theorem checkList_append {l1 l2 : List Nat} (h1 : checkList l1 = true) (h2 : checkList l2 = true) :
    checkList (l1 ++ l2) = true := by
  induction l1 with
  | nil => exact h2
  | cons x xs ih =>
    simp only [List.cons_append, checkList, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih h1.2⟩

theorem checkList_allCReps : checkList allCReps = true := by
  unfold allCReps
  repeat apply checkList_append
  · exact t_chunk0
  · exact t_chunk1
  · exact t_chunk2
  · exact t_chunk3
  · exact t_chunk4
  · exact t_chunk5
  · exact t_chunk6
  · exact t_chunk7
  · exact t_chunk8
  · exact t_chunk9
  · exact t_chunk10
  · exact t_chunk11
  · exact t_chunk12
  · exact t_chunk13
  · exact t_chunk14
  · exact t_chunk15
  · exact t_chunk16
  · exact t_chunk17
  · exact t_chunk18
  · exact t_chunk19
  · exact t_chunk20
  · exact t_chunk21
  · exact t_chunk22
  · exact t_chunk23


-- Glue operation and symmetry canonicalization
def glue (c d : Nat) (j : Hole) (i : Row) : Nat :=
  let c0 := c &&& 15; let c1 := (c >>> 4) &&& 15; let c2 := (c >>> 8) &&& 15
  let d0 := d &&& 15; let d1 := (d >>> 4) &&& 15; let d2 := (d >>> 8) &&& 15
  let m := 15 ^^^ (1 <<< i.val)
  match j.val with
  | 0 => pack3 (c0 &&& m) (c1 ||| d1) (c2 ||| d2)
  | 1 => pack3 (c0 ||| d0) (c1 &&& m) (c2 ||| d2)
  | _ => pack3 (c0 ||| d0) (c1 ||| d1) (c2 &&& m)

def ValidStep (c d e : Nat) : Prop :=
  isReach c = true ∧ isReach d = true ∧ c ≠ 0 ∧ d ≠ 0 ∧
  ∃ (j : Hole) (i : Row),
    bitIn (nib c j) i = true ∧
    bitIn (nib d j) i = false ∧
    e = glue c d j i ∧
    isReach e = true ∧
    (nib e j &&& nib d j) ≠ nib d j

def pSwap0 (i : Row) : Fin 24 :=
  match i.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨6, by decide⟩
  | 2 => ⟨14, by decide⟩
  | _ => ⟨21, by decide⟩

def hSwap0 (j : Hole) : Fin 6 :=
  match j.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨2, by decide⟩
  | _ => ⟨4, by decide⟩

def stab12 (idx : Fin 12) : Fin 24 × Fin 6 :=
  match idx.val with
  | 0 => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | 1 => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | 2 => (⟨1, by decide⟩, ⟨0, by decide⟩)
  | 3 => (⟨1, by decide⟩, ⟨1, by decide⟩)
  | 4 => (⟨2, by decide⟩, ⟨0, by decide⟩)
  | 5 => (⟨2, by decide⟩, ⟨1, by decide⟩)
  | 6 => (⟨3, by decide⟩, ⟨0, by decide⟩)
  | 7 => (⟨3, by decide⟩, ⟨1, by decide⟩)
  | 8 => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | 9 => (⟨4, by decide⟩, ⟨1, by decide⟩)
  | 10 => (⟨5, by decide⟩, ⟨0, by decide⟩)
  | _ => (⟨5, by decide⟩, ⟨1, by decide⟩)

def isStabP (p : Fin 24) : Bool := (mapNib (pLut p) 1) == 1

theorem stab12_fixes_0 : ∀ idx : Fin 12,
    mapNib (pLut (stab12 idx).1) 1 = 1 ∧ hCoord (stab12 idx).2 0 = 0 := by
  decide +kernel

theorem pSwap0_maps_i : ∀ i : Row, mapNib (pLut (pSwap0 i)) (1 <<< i.val) = 1 := by
  decide +kernel

theorem hSwap0_maps_j : ∀ j : Hole, hCoord (hSwap0 j) 0 = j := by
  decide +kernel

-- Bitwise lemmas for mapNib under arbitrary p : Fin 24
theorem mapNib_or : ∀ p : Fin 24, ∀ a b : Fin 15, (a.val ||| b.val) < 15 →
    mapNib (pLut p) (a.val ||| b.val) = (mapNib (pLut p) a.val ||| mapNib (pLut p) b.val) := by
  decide +kernel

theorem mapNib_and : ∀ p : Fin 24, ∀ a b : Fin 15,
    mapNib (pLut p) (a.val &&& b.val) = (mapNib (pLut p) a.val &&& mapNib (pLut p) b.val) := by
  decide +kernel

theorem mapNib_erase_bit : ∀ p : Fin 24, ∀ i : Row, ∀ a : Fin 15,
    mapNib (pLut p) (1 <<< i.val) = 1 →
    mapNib (pLut p) (a.val &&& (15 ^^^ (1 <<< i.val))) = (mapNib (pLut p) a.val &&& 14) := by
  decide +kernel

theorem mapNib_bit0 : ∀ p : Fin 24, ∀ i : Row, ∀ a : Fin 15,
    mapNib (pLut p) (1 <<< i.val) = 1 →
    ((mapNib (pLut p) a.val &&& 1) == 1) = bitIn a.val i := by
  decide +kernel

theorem mapNib_zero : ∀ p : Fin 24, ∀ a : Fin 15,
    mapNib (pLut p) a.val = 0 ↔ a.val = 0 := by
  decide +kernel

theorem mapNib_is3 : ∀ p : Fin 24, ∀ a : Fin 15,
    is3 (mapNib (pLut p) a.val) = is3 a.val := by
  decide +kernel

theorem mapNib_inj : ∀ p : Fin 24, ∀ a b : Fin 15,
    mapNib (pLut p) a.val = mapNib (pLut p) b.val → a.val = b.val := by
  decide +kernel

theorem actG_isReach (p : Fin 24) (h : Fin 6) (c : Nat) (hc : isReach c = true) :
    isReach (actG p h c) = true := by
  have hno := isReach_no15 hc
  have hno' := actG_no15 p h c hno
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hno hno'
  simp only [isReach, isReach3, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq] at hc ⊢
  obtain ⟨_, ⟨⟨⟨_, _⟩, _⟩, hnot3⟩⟩ := hc
  refine ⟨hno'.1.1.1, ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩⟩
  let b : Fin 3 → Nat := fun q =>
    match q.val with | 0 => c &&& 15 | 1 => (c >>> 4) &&& 15 | _ => (c >>> 8) &&& 15
  have hb : ∀ q : Fin 3, b q < 15 := by intro q; fin_cases q <;> [exact hno.1.1.2; exact hno.1.2; exact hno.2]
  let a : Fin 3 → Nat := fun q => mapNib (pLut p) (b q)
  have ha : ∀ q : Fin 3, a q < 15 := fun q => mapNib_lt15 p ⟨b q, hb q⟩
  have hact : actG p h c = pack3 (a (hCoord h 0)) (a (hCoord h 1)) (a (hCoord h 2)) := by
    change applyH6 h.val (a 0) (a 1) (a 2) = _; exact applyH6_eq_pack3 h a
  rw [hact]
  have hp := nib_pack3 ⟨a (hCoord h 0), ha _⟩ ⟨a (hCoord h 1), ha _⟩ ⟨a (hCoord h 2), ha _⟩
  rw [hp.1, hp.2.1, hp.2.2.1]
  have his3 : ∀ q : Fin 3, is3 (a q) = is3 (b q) := fun q => mapNib_is3 p ⟨b q, hb q⟩
  rw [his3, his3, his3]
  fin_cases h <;> simp [hCoord, b] at hnot3 ⊢ <;> tauto

set_option maxRecDepth 20000 in
theorem actG_id_check : checkRange (fun u => !no15 u || (actG 0 0 u == u)) 4096 = true := by
  decide +kernel

theorem actG_id (u : Nat) (hlt : u < 4096) (hno : no15 u = true) : actG 0 0 u = u := by
  have h := checkRange_sound actG_id_check u hlt
  simp only [hno, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact h

theorem actG_ne_zero (p : Fin 24) (h : Fin 6) (c : Nat) (hno : no15 c = true) (hne : c ≠ 0) :
    actG p h c ≠ 0 := by
  intro heq
  have h2 := actG_comp (invP p) p (invH h) h c hno
  rw [heq, actG_zero (invP p, invH h)] at h2
  have hidP : compP (invP p) p = 0 := by
    have : ∀ x : Fin 24, compP (invP x) x = 0 := by decide +kernel
    exact this p
  have hidH : compH (invH h) h = 0 := by
    have : ∀ x : Fin 6, compH (invH x) x = 0 := by decide +kernel
    exact this h
  rw [hidP, hidH] at h2
  have hlt : c < 4096 := by simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hno; exact hno.1.1.1
  rw [actG_id c hlt hno] at h2
  exact hne h2.symm

def repBits : Nat := ((((((35914525573258 + (8362 <<< 48)) + ((176818826 + ((0 + (592705486848 <<< 48)) <<< 48)) <<< 96)) + (((592705486848 + (548020394 <<< 48)) + ((11587998580736 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) <<< 240)) + ((((138 + (35915064541184 <<< 48)) + ((46910348593802 + ((10922 + (35914516529152 <<< 48)) <<< 48)) <<< 96)) + (((548020394 + ((0 + (11587821772970 <<< 48)) <<< 48)) + ((715795114 + ((0 + (35915064549546 <<< 48)) <<< 48)) <<< 144)) <<< 240)) <<< 480)) + (((((0 + (0 <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) + (((0 + ((0 + (0 <<< 48)) <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 144)) <<< 240)) + ((((0 + (0 <<< 48)) + ((176818826 + ((46910180818944 + (11587821764608 <<< 48)) <<< 48)) <<< 96)) + (((0 + ((0 + (2241972928512 <<< 48)) <<< 48)) + ((0 + ((42 + (522 <<< 48)) <<< 48)) <<< 144)) <<< 240)) <<< 528)) <<< 1008)) + ((((((0 + (0 <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) + (((0 + (0 <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) <<< 240)) + ((((0 + (0 <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) + (((0 + ((0 + (0 <<< 48)) <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 144)) <<< 240)) <<< 480)) + (((((0 + (0 <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 96)) + (((0 + ((0 + (0 <<< 48)) <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 144)) <<< 240)) + ((((0 + (0 <<< 48)) + ((0 + ((0 + (655360 <<< 48)) <<< 48)) <<< 96)) + (((0 + ((0 + (0 <<< 48)) <<< 48)) + ((0 + ((0 + (0 <<< 48)) <<< 48)) <<< 144)) <<< 240)) <<< 528)) <<< 1008)) <<< 2064))

def isRepBit (c : Nat) : Bool := ((repBits >>> c) &&& 1) == 1

def bestStabAux (c1 : Nat) : Nat → Fin 12 → Nat → Fin 12
  | 0, best, _ => best
  | k + 1, best, bestV =>
    if hk : k < 12 then
      let idx : Fin 12 := ⟨k, hk⟩
      let v := actG (stab12 idx).1 (stab12 idx).2 c1
      if v < bestV then bestStabAux c1 k idx v else bestStabAux c1 k best bestV
    else bestStabAux c1 k best bestV

def bestStabIdx (c1 : Nat) : Fin 12 :=
  bestStabAux c1 12 0 4096

set_option maxRecDepth 20000 in
theorem stab_min_in_repBits :
    checkRange (fun c1 => !isReach c1 || ((c1 &&& 1) != 1) ||
      isRepBit (actG (stab12 (bestStabIdx c1)).1 (stab12 (bestStabIdx c1)).2 c1)) 4096 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem repBits_in_allCReps :
    checkRange (fun c => !isRepBit c || allCReps.elem c) 4096 = true := by
  decide +kernel

theorem exists_stab_rep (c1 : Nat) (hlt : c1 < 4096) (hrc : isReach c1 = true) (hodd : (c1 &&& 1) = 1) :
    ∃ idx : Fin 12, actG (stab12 idx).1 (stab12 idx).2 c1 ∈ allCReps := by
  refine ⟨bestStabIdx c1, ?_⟩
  have h1 := checkRange_sound stab_min_in_repBits c1 hlt
  simp only [hrc, Bool.not_true, Bool.false_or, hodd, bne_self_eq_false] at h1
  have hact_lt : actG (stab12 (bestStabIdx c1)).1 (stab12 (bestStabIdx c1)).2 c1 < 4096 := by
    have hno := actG_no15 (stab12 (bestStabIdx c1)).1 (stab12 (bestStabIdx c1)).2 c1 (isReach_no15 hrc)
    simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hno; exact hno.1.1.1
  have h2 := checkRange_sound repBits_in_allCReps _ hact_lt
  simp only [h1, Bool.not_true, Bool.false_or] at h2
  exact List.mem_of_elem_eq_true h2

theorem nib_actG (p : Fin 24) (h : Fin 6) (c : Nat) (hc : no15 c = true) (q : Hole) :
    nib (actG p h c) q = mapNib (pLut p) (nib c (hCoord h q)) := by
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hc
  let b : Fin 3 → Nat := fun r =>
    match r.val with | 0 => c &&& 15 | 1 => (c >>> 4) &&& 15 | _ => (c >>> 8) &&& 15
  have hb : ∀ r : Fin 3, b r < 15 := by intro r; fin_cases r <;> [exact hc.1.1.2; exact hc.1.2; exact hc.2]
  have hbn : ∀ r : Fin 3, b r = nib c r := by intro r; fin_cases r <;> rfl
  let a : Fin 3 → Nat := fun r => mapNib (pLut p) (b r)
  have ha : ∀ r : Fin 3, a r < 15 := fun r => mapNib_lt15 p ⟨b r, hb r⟩
  have hact : actG p h c = pack3 (a (hCoord h 0)) (a (hCoord h 1)) (a (hCoord h 2)) := by
    change applyH6 h.val (a 0) (a 1) (a 2) = _; exact applyH6_eq_pack3 h a
  rw [hact]
  have hp := nib_pack3 ⟨a (hCoord h 0), ha _⟩ ⟨a (hCoord h 1), ha _⟩ ⟨a (hCoord h 2), ha _⟩
  fin_cases q
  · change (pack3 _ _ _ &&& 15) = _; rw [hp.1, ← hbn]; rfl
  · change ((pack3 _ _ _ >>> 4) &&& 15) = _; rw [hp.2.1, ← hbn]; rfl
  · change ((pack3 _ _ _ >>> 8) &&& 15) = _; rw [hp.2.2.1, ← hbn]; rfl

theorem nib_pack3_fin16 : ∀ a b e : Fin 16,
    (pack3 a.val b.val e.val &&& 15) = a.val ∧
    ((pack3 a.val b.val e.val >>> 4) &&& 15) = b.val ∧
    ((pack3 a.val b.val e.val >>> 8) &&& 15) = e.val := by
  decide +kernel

theorem nib_glue (c d : Nat) (j : Hole) (i : Row)
    (hc : no15 c = true) (hd : no15 d = true) (he : no15 (glue c d j i) = true) :
    nib (glue c d j i) j = (nib c j &&& (15 ^^^ (1 <<< i.val))) ∧
    ∀ q : Hole, q ≠ j → nib (glue c d j i) q = (nib c q ||| nib d q) := by
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hc hd he
  have hmask : ∀ x : Fin 15, ∀ r : Row, (x.val &&& (15 ^^^ (1 <<< r.val))) < 15 := by decide +kernel
  have hor_lt : ∀ a b : Fin 15, (a.val ||| b.val) < 16 := by decide +kernel
  fin_cases j
  · have h0 : ((c &&& 15) &&& (15 ^^^ (1 <<< i.val))) < 15 := hmask ⟨c &&& 15, hc.1.1.2⟩ i
    have h1' : (((c >>> 4) &&& 15) ||| ((d >>> 4) &&& 15)) < 16 := hor_lt ⟨_, hc.1.2⟩ ⟨_, hd.1.2⟩
    have h2' : (((c >>> 8) &&& 15) ||| ((d >>> 8) &&& 15)) < 16 := hor_lt ⟨_, hc.2⟩ ⟨_, hd.2⟩
    have hp := nib_pack3_fin16 ⟨(c &&& 15) &&& (15 ^^^ (1 <<< i.val)), by omega⟩
      ⟨((c >>> 4) &&& 15) ||| ((d >>> 4) &&& 15), h1'⟩
      ⟨((c >>> 8) &&& 15) ||| ((d >>> 8) &&& 15), h2'⟩
    refine ⟨hp.1, ?_⟩
    intro q hq; fin_cases q
    · exact (hq rfl).elim
    · exact hp.2.1
    · exact hp.2.2
  · have h1 : (((c >>> 4) &&& 15) &&& (15 ^^^ (1 <<< i.val))) < 15 := hmask ⟨_, hc.1.2⟩ i
    have h0' : ((c &&& 15) ||| (d &&& 15)) < 16 := hor_lt ⟨_, hc.1.1.2⟩ ⟨_, hd.1.1.2⟩
    have h2' : (((c >>> 8) &&& 15) ||| ((d >>> 8) &&& 15)) < 16 := hor_lt ⟨_, hc.2⟩ ⟨_, hd.2⟩
    have hp := nib_pack3_fin16 ⟨(c &&& 15) ||| (d &&& 15), h0'⟩
      ⟨((c >>> 4) &&& 15) &&& (15 ^^^ (1 <<< i.val)), by omega⟩
      ⟨((c >>> 8) &&& 15) ||| ((d >>> 8) &&& 15), h2'⟩
    refine ⟨hp.2.1, ?_⟩
    intro q hq; fin_cases q
    · exact hp.1
    · exact (hq rfl).elim
    · exact hp.2.2
  · have h2 : (((c >>> 8) &&& 15) &&& (15 ^^^ (1 <<< i.val))) < 15 := hmask ⟨_, hc.2⟩ i
    have h0' : ((c &&& 15) ||| (d &&& 15)) < 16 := hor_lt ⟨_, hc.1.1.2⟩ ⟨_, hd.1.1.2⟩
    have h1' : (((c >>> 4) &&& 15) ||| ((d >>> 4) &&& 15)) < 16 := hor_lt ⟨_, hc.1.2⟩ ⟨_, hd.1.2⟩
    have hp := nib_pack3_fin16 ⟨(c &&& 15) ||| (d &&& 15), h0'⟩
      ⟨((c >>> 4) &&& 15) ||| ((d >>> 4) &&& 15), h1'⟩
      ⟨((c >>> 8) &&& 15) &&& (15 ^^^ (1 <<< i.val)), by omega⟩
    refine ⟨hp.2.2, ?_⟩
    intro q hq; fin_cases q
    · exact hp.1
    · exact hp.2.1
    · exact (hq rfl).elim

theorem hCoord_inj : ∀ h : Fin 6, ∀ q1 q2 : Fin 3, hCoord h q1 = hCoord h q2 → q1 = q2 := by
  decide +kernel

theorem no15_nib_lt15 {x : Nat} (hx : no15 x = true) (q : Hole) : nib x q < 15 := by
  simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hx
  fin_cases q
  · exact hx.1.1.2
  · exact hx.1.2
  · exact hx.2

set_option maxRecDepth 20000 in
theorem zero_of_nibs_zero_check :
    checkRange (fun x => !((x &&& 15) == 0 && ((x >>> 4) &&& 15) == 0 && ((x >>> 8) &&& 15) == 0) || (x == 0)) 4096 = true := by
  decide +kernel

theorem zero_of_nibs_zero (x : Nat) (hlt : x < 4096) (h0 : (x &&& 15) = 0)
    (h1 : ((x >>> 4) &&& 15) = 0) (h2 : ((x >>> 8) &&& 15) = 0) : x = 0 := by
  have h := checkRange_sound zero_of_nibs_zero_check x hlt
  simp only [h0, h1, h2, beq_self_eq_true, Bool.and_true, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact h

theorem and1_eq_and15_and1 (x : Nat) : (x &&& 1) = ((x &&& 15) &&& 1) := by
  rw [Nat.and_assoc]
  rfl

theorem delta144_le_416 {c d e : Nat} (hstep : ValidStep c d e) : delta144 c d e ≤ 416 := by
  obtain ⟨hrc, hrd, hnc, hnd, j, i, hci, hdi, rfl, hre, hnsub⟩ := hstep
  have hnoc := isReach_no15 hrc
  have hnod := isReach_no15 hrd
  have hnoe := isReach_no15 hre
  let p0 := pSwap0 i
  let h0 := hSwap0 j
  let c1 := actG p0 h0 c
  have hrc1 : isReach c1 = true := actG_isReach p0 h0 c hrc
  have hnoc1 : no15 c1 = true := isReach_no15 hrc1
  have hc1_lt : c1 < 4096 := by simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hnoc1; exact hnoc1.1.1.1
  have hc1_odd : (c1 &&& 1) = 1 := by
    have hnib : nib c1 0 = mapNib (pLut p0) (nib c j) := by
      have := nib_actG p0 h0 c hnoc 0
      rwa [hSwap0_maps_j j] at this
    have hbit := mapNib_bit0 p0 i ⟨nib c j, no15_nib_lt15 hnoc j⟩ (pSwap0_maps_i i)
    rw [hci] at hbit
    have h0' : (c1 &&& 1) = (nib c1 0 &&& 1) := and1_eq_and15_and1 c1
    rw [h0', hnib]
    exact beq_iff_eq.mp hbit
  obtain ⟨idx, hrep⟩ := exists_stab_rep c1 hc1_lt hrc1 hc1_odd
  let p := compP (stab12 idx).1 p0
  let h := compH (stab12 idx).2 h0
  let c' := actG p h c
  let d' := actG p h d
  let e' := actG p h (glue c d j i)
  have hc'_eq : c' = actG (stab12 idx).1 (stab12 idx).2 c1 :=
    (actG_comp (stab12 idx).1 p0 (stab12 idx).2 h0 c hnoc).symm
  have hc'_mem : c' ∈ allCReps := hc'_eq ▸ hrep
  have hch_c' : checkC c' = true := checkList_mem checkList_allCReps hc'_mem
  have hpmap : mapNib (pLut p) (1 <<< i.val) = 1 := by
    have hi_lt : (1 <<< i.val) < 15 := by fin_cases i <;> decide
    rw [← mapNib_comp (stab12 idx).1 p0 ⟨1 <<< i.val, hi_lt⟩, pSwap0_maps_i i]
    exact (stab12_fixes_0 idx).1
  have hhmap : hCoord h 0 = j := by
    rw [hCoord_comp, (stab12_fixes_0 idx).2, hSwap0_maps_j j]
  have hnoc' := actG_no15 p h c hnoc
  have hnod' := actG_no15 p h d hnod
  have hnoe' := actG_no15 p h (glue c d j i) hnoe
  have hrd' : isReach d' = true := actG_isReach p h d hrd
  have hnd' : d' ≠ 0 := actG_ne_zero p h d hnod hnd
  have hglue := nib_glue c d j i hnoc hnod hnoe
  have he'0 : (e' &&& 15) = ((c' &&& 15) &&& 14) := by
    change nib e' 0 = (nib c' 0 &&& 14)
    rw [nib_actG p h _ hnoe 0, nib_actG p h c hnoc 0, hhmap, hglue.1]
    exact mapNib_erase_bit p i ⟨nib c j, no15_nib_lt15 hnoc j⟩ hpmap
  have he'1 : ((e' >>> 4) &&& 15) = (((c' >>> 4) &&& 15) ||| ((d' >>> 4) &&& 15)) := by
    change nib e' 1 = (nib c' 1 ||| nib d' 1)
    have hqne : hCoord h 1 ≠ j := by
      intro eq; rw [← hhmap] at eq; exact absurd (hCoord_inj h 1 0 eq) (by decide)
    rw [nib_actG p h _ hnoe 1, nib_actG p h c hnoc 1, nib_actG p h d hnod 1, hglue.2 _ hqne]
    exact mapNib_or p ⟨nib c _, no15_nib_lt15 hnoc _⟩ ⟨nib d _, no15_nib_lt15 hnod _⟩
      (by rw [← hglue.2 _ hqne]; exact no15_nib_lt15 hnoe _)
  have he'2 : ((e' >>> 8) &&& 15) = (((c' >>> 8) &&& 15) ||| ((d' >>> 8) &&& 15)) := by
    change nib e' 2 = (nib c' 2 ||| nib d' 2)
    have hqne : hCoord h 2 ≠ j := by
      intro eq; rw [← hhmap] at eq; exact absurd (hCoord_inj h 2 0 eq) (by decide)
    rw [nib_actG p h _ hnoe 2, nib_actG p h c hnoc 2, nib_actG p h d hnod 2, hglue.2 _ hqne]
    exact mapNib_or p ⟨nib c _, no15_nib_lt15 hnoc _⟩ ⟨nib d _, no15_nib_lt15 hnod _⟩
      (by rw [← hglue.2 _ hqne]; exact no15_nib_lt15 hnoe _)
  have hd'0_even : ((d' &&& 15) &&& 1) = 0 := by
    change (nib d' 0 &&& 1) = 0
    rw [nib_actG p h d hnod 0, hhmap]
    have hbit := mapNib_bit0 p i ⟨nib d j, no15_nib_lt15 hnod j⟩ hpmap
    rw [hdi] at hbit
    have hlt2 : (mapNib (pLut p) (nib d j) &&& 1) < 2 := and1_lt _
    have hne1 : (mapNib (pLut p) (nib d j) &&& 1) ≠ 1 := by
      intro h1; rw [h1] at hbit; simp at hbit
    omega
  have hnotSub' : (((c' &&& 15) &&& 14) &&& (d' &&& 15)) ≠ (d' &&& 15) := by
    rw [← he'0]
    change (nib e' 0 &&& nib d' 0) ≠ nib d' 0
    rw [nib_actG p h _ hnoe 0, nib_actG p h d hnod 0, hhmap]
    intro heq
    rw [← mapNib_and p ⟨nib (glue c d j i) j, no15_nib_lt15 hnoe j⟩ ⟨nib d j, no15_nib_lt15 hnod j⟩] at heq
    have hand_lt : (nib (glue c d j i) j &&& nib d j) < 15 := by
      have hlt : nib d j < 15 := no15_nib_lt15 hnod j
      have hle : (nib (glue c d j i) j &&& nib d j) ≤ nib d j := Nat.and_le_right
      omega
    exact hnsub (mapNib_inj p ⟨_, hand_lt⟩ ⟨nib d j, no15_nib_lt15 hnod j⟩ heq)
  have hnz' : ¬ ((d' &&& 15) = 0 ∧ ((d' >>> 4) &&& 15) = 0 ∧ ((d' >>> 8) &&& 15) = 0) := by
    rintro ⟨h0', h1', h2'⟩
    have hd'_lt : d' < 4096 := by simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hnod'; exact hnod'.1.1.1
    exact hnd' (zero_of_nibs_zero d' hd'_lt h0' h1' h2')
  have hr3' : isReach3 (d' &&& 15) ((d' >>> 4) &&& 15) ((d' >>> 8) &&& 15) = true := by
    simp only [isReach, Bool.and_eq_true] at hrd'; exact hrd'.2
  have h36 : delta36 c' d' e' ≤ 104 := by
    rw [delta36_eq_deltaSpecs, he'0, he'1, he'2]
    exact checkC_sound hch_c' (no15_nib_lt15 hnoc' 1) (no15_nib_lt15 hnoc' 2)
      (no15_nib_lt15 hnod' 0) (no15_nib_lt15 hnod' 1) (no15_nib_lt15 hnod' 2)
      (by rw [← he'1]; exact no15_nib_lt15 hnoe' 1)
      (by rw [← he'2]; exact no15_nib_lt15 hnoe' 2)
      hd'0_even hnotSub' hnz' hr3'
  have h144 : delta144 c d (glue c d j i) = 4 * delta36 c' d' e' := by
    rw [← delta144_actG p h c d (glue c d j i) hnoc hnod hnoe]
    exact delta144_eq_4_delta36 c' d' e' hnoc' hnod' hnoe'
  omega

-- Section B: Single-occupancy box projection and main derivation induction
def asg (h : Hole → Row) (v : V) : Bool := decide (h v.2 = v.1)

def inBox (c : Nat) (h : Hole → Row) : Prop :=
  ∀ j : Hole, bitIn (nib c j) (h j) = false

def BoxCovers (L : List Nat) (Q : C) : Prop :=
  (∀ h : Hole → Row, ClauseSat (asg h) Q) ∨
  (∃ x ∈ L, ∀ h : Hole → Row, ¬ ClauseSat (asg h) Q → inBox x h)

theorem asg_sat_coll (h : Hole → Row) {N : C} (hN : Coll N) : ClauseSat (asg h) N := by
  obtain ⟨i, k, j, hik, rfl⟩ := hN
  by_cases hi : h j = i
  · refine ⟨((k, j), false), by simp [colAx], ?_⟩
    simp [asg, hi, hik]
  · refine ⟨((i, j), false), by simp [colAx], ?_⟩
    simp [asg, hi]

theorem box_mix {R : C} {h1 h2 h' : Hole → Row}
    (h1u : ¬ ClauseSat (asg h1) R) (h2u : ¬ ClauseSat (asg h2) R)
    (hmix : ∀ q : Hole, h' q = h1 q ∨ h' q = h2 q) : ¬ ClauseSat (asg h') R := by
  rintro ⟨⟨⟨p, q⟩, b⟩, hl, hsat⟩
  rcases hmix q with hq | hq
  · apply h1u
    refine ⟨((p, q), b), hl, ?_⟩
    simpa [asg, hq] using hsat
  · apply h2u
    refine ⟨((p, q), b), hl, ?_⟩
    simpa [asg, hq] using hsat

theorem rowAx_covered (i : Row) :
    ∃ x ∈ initBoxes, ∀ h : Hole → Row, ¬ ClauseSat (asg h) (rowAx i) → inBox x h := by
  have hbit : ∀ i p : Row, p ≠ i → ∀ j : Hole,
      bitIn (nib ((1 <<< i.val) * 273) j) p = false := by decide +kernel
  have hmem : ∀ i : Row, ((1 <<< i.val) * 273) ∈ initBoxes := by decide +kernel
  refine ⟨(1 <<< i.val) * 273, hmem i, fun h hu j => ?_⟩
  have hne : h j ≠ i := by
    intro eq
    apply hu
    exact ⟨((i, j), true), Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, by simp [asg, eq]⟩
  exact hbit i (h j) hne j

theorem nib_zero_of_all_bitIn_false : ∀ m : Fin 16, (∀ p : Row, bitIn m.val p = false) → m.val = 0 := by
  decide +kernel

theorem empty_forces_zero {x : Nat} (hlt : x < 4096) (hall : ∀ h : Hole → Row, inBox x h) :
    x = 0 := by
  have h0 : (x &&& 15) = 0 :=
    nib_zero_of_all_bitIn_false ⟨x &&& 15, and15_lt x⟩ (fun p => hall (fun _ => p) 0)
  have h1 : ((x >>> 4) &&& 15) = 0 :=
    nib_zero_of_all_bitIn_false ⟨(x >>> 4) &&& 15, and15_lt _⟩ (fun p => hall (fun _ => p) 1)
  have h2 : ((x >>> 8) &&& 15) = 0 :=
    nib_zero_of_all_bitIn_false ⟨(x >>> 8) &&& 15, and15_lt _⟩ (fun p => hall (fun _ => p) 2)
  exact zero_of_nibs_zero x hlt h0 h1 h2

theorem bitIn_zero_false : ∀ j : Hole, ∀ p : Row, bitIn (nib 0 j) p = false := by decide +kernel

theorem inBox_zero (h : Hole → Row) : inBox 0 h := fun j => bitIn_zero_false j (h j)

theorem bitIn_erase : ∀ m : Fin 16, ∀ i p : Row,
    (p = i ∨ bitIn m.val p = false) → bitIn (m.val &&& (15 ^^^ (1 <<< i.val))) p = false := by
  decide +kernel

theorem bitIn_or : ∀ a b : Fin 16, ∀ p : Row,
    bitIn a.val p = false → bitIn b.val p = false → bitIn (a.val ||| b.val) p = false := by
  decide +kernel

theorem bitIn_le_of_and : ∀ a b : Fin 16, ∀ p : Row,
    (a.val &&& b.val) = b.val → bitIn a.val p = false → bitIn b.val p = false := by
  decide +kernel

theorem bitIn_of_or_left : ∀ a b : Fin 16, ∀ p : Row,
    bitIn (a.val ||| b.val) p = false → bitIn a.val p = false := by
  decide +kernel

theorem bitIn_of_or_right : ∀ a b : Fin 16, ∀ p : Row,
    bitIn (a.val ||| b.val) p = false → bitIn b.val p = false := by
  decide +kernel

theorem nib_ne15_of_bitIn_false : ∀ m : Fin 16, ∀ p : Row,
    bitIn m.val p = false → m.val < 15 := by
  decide +kernel

theorem isReach_glue_of_ne15 : ∀ c0 c1 c2 d0 d1 d2 : Fin 15, ∀ j : Hole, ∀ i : Row,
    bitIn (match j.val with | 0 => c0.val | 1 => c1.val | _ => c2.val) i = true →
    (match j.val with
      | 0 => (c1.val ||| d1.val) < 15 ∧ (c2.val ||| d2.val) < 15
      | 1 => (c0.val ||| d0.val) < 15 ∧ (c2.val ||| d2.val) < 15
      | _ => (c0.val ||| d0.val) < 15 ∧ (c1.val ||| d1.val) < 15) →
    isReach (glue (pack3 c0.val c1.val c2.val) (pack3 d0.val d1.val d2.val) j i) = true := by
  -- Instead of 15^6, prove algebraically via 1-nibble lemma!
  intro c0 c1 c2 d0 d1 d2 j i hbi hne
  have h1 : ∀ a : Fin 15, ∀ r : Row, bitIn a.val r = true →
      (a.val &&& (15 ^^^ (1 <<< r.val))) < 15 ∧
      is3 (a.val &&& (15 ^^^ (1 <<< r.val))) = false := by decide +kernel
  have hp1 := nib_pack3 c0 c1 c2
  have hp2 := nib_pack3 d0 d1 d2
  unfold glue
  rw [hp1.1, hp1.2.1, hp1.2.2.1, hp2.1, hp2.2.1, hp2.2.2.1]
  fin_cases j
  · dsimp only at hbi hne ⊢
    obtain ⟨h0lt, h0n3⟩ := h1 c0 i hbi
    have hp := nib_pack3 ⟨_, h0lt⟩ ⟨_, hne.1⟩ ⟨_, hne.2⟩
    simp only [isReach, isReach3, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, h0n3, Bool.false_and,
      Bool.not_false, Bool.and_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, true_and]
    exact ⟨⟨Nat.ne_of_lt h0lt, Nat.ne_of_lt hne.1⟩, Nat.ne_of_lt hne.2⟩
  · dsimp only at hbi hne ⊢
    obtain ⟨h1lt, h1n3⟩ := h1 c1 i hbi
    have hp := nib_pack3 ⟨_, hne.1⟩ ⟨_, h1lt⟩ ⟨_, hne.2⟩
    simp only [isReach, isReach3, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, h1n3, Bool.and_false,
      Bool.false_and, Bool.not_false, Bool.and_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, true_and]
    exact ⟨⟨Nat.ne_of_lt hne.1, Nat.ne_of_lt h1lt⟩, Nat.ne_of_lt hne.2⟩
  · dsimp only at hbi hne ⊢
    obtain ⟨h2lt, h2n3⟩ := h1 c2 i hbi
    have hp := nib_pack3 ⟨_, hne.1⟩ ⟨_, hne.2⟩ ⟨_, h2lt⟩
    simp only [isReach, isReach3, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, h2n3, Bool.and_false,
      Bool.not_false, Bool.and_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, true_and]
    exact ⟨⟨Nat.ne_of_lt hne.1, Nat.ne_of_lt hne.2⟩, Nat.ne_of_lt h2lt⟩

set_option maxRecDepth 20000 in
theorem pack3_of_lt4096_check :
    checkRange (fun x => pack3 (x &&& 15) ((x >>> 4) &&& 15) ((x >>> 8) &&& 15) == x) 4096 = true := by
  decide +kernel

theorem pack3_of_lt4096 (x : Nat) (hlt : x < 4096) :
    pack3 (x &&& 15) ((x >>> 4) &&& 15) ((x >>> 8) &&& 15) = x :=
  beq_iff_eq.mp (checkRange_sound pack3_of_lt4096_check x hlt)

theorem glue_res_step {L : List Nat} {P N R : C} {v : V}
    (hLreach : ∀ x ∈ L, isReach x = true)
    (hP : BoxCovers L P) (hN : BoxCovers L N)
    (hp : (v, true) ∈ P) (hn : (v, false) ∈ N)
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) :
    BoxCovers L R ∨
    ∃ c ∈ L, ∃ d ∈ L, ∃ e : Nat, ValidStep c d e ∧
      ∀ h : Hole → Row, ¬ ClauseSat (asg h) R → inBox e h := by
  classical
  by_cases hRsat : ∀ h : Hole → Row, ClauseSat (asg h) R
  · exact Or.inl (Or.inl hRsat)
  rcases hP with hPsat | ⟨c, hcL, hcCov⟩
  · left
    rcases hN with hNsat | ⟨d, hdL, hdCov⟩
    · exact Or.inl (fun h => satResolve hR (hPsat h) (hNsat h))
    · exact Or.inr ⟨d, hdL, fun h hRu => hdCov h (fun hNs => hRu (satResolve hR (hPsat h) hNs))⟩
  rcases hN with hNsat | ⟨d, hdL, hdCov⟩
  · exact Or.inl (Or.inr ⟨c, hcL, fun h hRu => hcCov h (fun hPs => hRu (satResolve hR hPs (hNsat h)))⟩)
  by_cases hc0 : c = 0
  · exact Or.inl (Or.inr ⟨c, hcL, fun h _ => hc0 ▸ inBox_zero h⟩)
  by_cases hd0 : d = 0
  · exact Or.inl (Or.inr ⟨d, hdL, fun h _ => hd0 ▸ inBox_zero h⟩)
  rcases v with ⟨i, j⟩
  -- For any h unsat R: if h j != i then unsat P (so inBox c h); if h j = i then unsat N (so inBox d h)
  have hne_c : ∀ h : Hole → Row, ¬ ClauseSat (asg h) R → h j ≠ i → inBox c h := by
    intro h hRu hne
    apply hcCov h
    intro hPs
    apply hRu
    exact satResolve hR hPs ⟨((i, j), false), hn, by simp [asg, hne]⟩
  have heq_d : ∀ h : Hole → Row, ¬ ClauseSat (asg h) R → h j = i → inBox d h := by
    intro h hRu heq
    apply hdCov h
    intro hNs
    apply hRu
    exact satResolve hR ⟨((i, j), true), hp, by simp [asg, heq]⟩ hNs
  by_cases hex0 : ∃ h0 : Hole → Row, ¬ ClauseSat (asg h0) R ∧ h0 j = i
  · by_cases hex1 : ∃ h1 : Hole → Row, ¬ ClauseSat (asg h1) R ∧ h1 j ≠ i
    · obtain ⟨h0, h0u, h0j⟩ := hex0
      obtain ⟨h1, h1u, h1j⟩ := hex1
      have hrc := hLreach c hcL
      have hrd := hLreach d hdL
      have hnoc := isReach_no15 hrc
      have hnod := isReach_no15 hrd
      have hci_lt : ∀ q : Hole, nib c q < 15 := no15_nib_lt15 hnoc
      have hdi_lt : ∀ q : Hole, nib d q < 15 := no15_nib_lt15 hnod
      have hdi_false : bitIn (nib d j) i = false := by
        have := heq_d h0 h0u h0j j
        rwa [h0j] at this
      -- Every h unsat R satisfies bit conditions for e = glue c d j i
      have hcov_coords : ∀ h : Hole → Row, ¬ ClauseSat (asg h) R →
          bitIn (nib c j &&& (15 ^^^ (1 <<< i.val))) (h j) = false ∧
          ∀ q : Hole, q ≠ j → bitIn (nib c q ||| nib d q) (h q) = false := by
        intro h hRu
        constructor
        · apply bitIn_erase ⟨nib c j, by have := hci_lt j; omega⟩ i (h j)
          by_cases hhj : h j = i
          · exact Or.inl hhj
          · exact Or.inr (hne_c h hRu hhj j)
        · intro q hq
          let hp' : Hole → Row := fun r => if r = j then h1 j else h r
          have hp'u : ¬ ClauseSat (asg hp') R :=
            box_mix h1u hRu (fun r => by dsimp only [hp']; split <;> [exact Or.inl (by simp [*]); exact Or.inr rfl])
          have hp'j : hp' j ≠ i := by simp [hp', h1j]
          have hcq : bitIn (nib c q) (h q) = false := by
            have := hne_c hp' hp'u hp'j q
            simpa [hp', hq] using this
          let hn' : Hole → Row := fun r => if r = j then i else h r
          have hn'u : ¬ ClauseSat (asg hn') R :=
            box_mix h0u hRu (fun r => by dsimp only [hn']; split <;> [exact Or.inl (by simp [*]); exact Or.inr rfl])
          have hn'j : hn' j = i := by simp [hn']
          have hdq : bitIn (nib d q) (h q) = false := by
            have := heq_d hn' hn'u hn'j q
            simpa [hn', hq] using this
          exact bitIn_or ⟨nib c q, by have := hci_lt q; omega⟩ ⟨nib d q, by have := hdi_lt q; omega⟩ (h q) hcq hdq
      -- Check if bitIn (nib c j) i = false -> then c already covers R!
      by_cases hci_true : bitIn (nib c j) i = true
      · -- Check e_q < 15 for all q != j using h0!
        have hor_ne15 : ∀ q : Hole, q ≠ j → (nib c q ||| nib d q) < 15 := by
          intro q hq
          have hbf := (hcov_coords h0 h0u).2 q hq
          have hor16 : ∀ a b : Fin 15, (a.val ||| b.val) < 16 := by decide +kernel
          exact nib_ne15_of_bitIn_false ⟨_, hor16 ⟨nib c q, hci_lt q⟩ ⟨nib d q, hdi_lt q⟩⟩ (h0 q) hbf
        let e := glue c d j i
        have hre : isReach e = true := by
          have hc_lt : c < 4096 := by simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hnoc; exact hnoc.1.1.1
          have hd_lt : d < 4096 := by simp only [no15, Bool.and_eq_true, decide_eq_true_eq] at hnod; exact hnod.1.1.1
          have hcp : c = pack3 (c &&& 15) ((c >>> 4) &&& 15) ((c >>> 8) &&& 15) := (pack3_of_lt4096 c hc_lt).symm
          have hdp : d = pack3 (d &&& 15) ((d >>> 4) &&& 15) ((d >>> 8) &&& 15) := (pack3_of_lt4096 d hd_lt).symm
          change isReach (glue c d j i) = true
          rw [hcp, hdp]
          apply isReach_glue_of_ne15 ⟨_, hci_lt 0⟩ ⟨_, hci_lt 1⟩ ⟨_, hci_lt 2⟩
            ⟨_, hdi_lt 0⟩ ⟨_, hdi_lt 1⟩ ⟨_, hdi_lt 2⟩ j i
          · fin_cases j <;> exact hci_true
          · fin_cases j
            · exact ⟨hor_ne15 1 (by decide), hor_ne15 2 (by decide)⟩
            · exact ⟨hor_ne15 0 (by decide), hor_ne15 2 (by decide)⟩
            · exact ⟨hor_ne15 0 (by decide), hor_ne15 1 (by decide)⟩
        have hnoe := isReach_no15 hre
        have hgn := nib_glue c d j i hnoc hnod hnoe
        have heCov : ∀ h : Hole → Row, ¬ ClauseSat (asg h) R → inBox e h := by
          intro h hRu q
          by_cases hqj : q = j
          · subst q; rw [hgn.1]; exact (hcov_coords h hRu).1
          · rw [hgn.2 q hqj]; exact (hcov_coords h hRu).2 q hqj
        -- Check if (nib e j &&& nib d j) = nib d j -> then d already covers R!
        by_cases hsub : (nib e j &&& nib d j) = nib d j
        · left; right
          refine ⟨d, hdL, fun h hRu q => ?_⟩
          have heq := heCov h hRu q
          by_cases hqj : q = j
          · subst q
            exact bitIn_le_of_and ⟨nib e j, by have := no15_nib_lt15 hnoe j; omega⟩
              ⟨nib d j, by have := hdi_lt j; omega⟩ (h j) hsub heq
          · rw [hgn.2 q hqj] at heq
            exact bitIn_of_or_right ⟨nib c q, by have := hci_lt q; omega⟩
              ⟨nib d q, by have := hdi_lt q; omega⟩ (h q) heq
        · right
          exact ⟨c, hcL, d, hdL, e, ⟨hrc, hrd, hc0, hd0, j, i, hci_true, hdi_false, rfl, hre, hsub⟩, heCov⟩
      · -- bitIn (nib c j) i = false -> c already covers R!
        left; right
        refine ⟨c, hcL, fun h hRu q => ?_⟩
        by_cases hqj : q = j
        · subst q
          by_cases hhj : h j = i
          · rw [hhj]; exact Bool.eq_false_iff.mpr hci_true
          · exact hne_c h hRu hhj j
        · have hor := (hcov_coords h hRu).2 q hqj
          exact bitIn_of_or_left ⟨nib c q, by have := hci_lt q; omega⟩
            ⟨nib d q, by have := hdi_lt q; omega⟩ (h q) hor
    · -- All h unsat R have h j = i -> d covers R!
      left; right
      refine ⟨d, hdL, fun h hRu => heq_d h hRu ?_⟩
      by_contra hne
      exact hex1 ⟨h, hRu, hne⟩
  · -- All h unsat R have h j != i -> c covers R!
    left; right
    refine ⟨c, hcL, fun h hRu => hne_c h hRu ?_⟩
    intro heq
    exact hex0 ⟨h, hRu, heq⟩

theorem collect {π : List C} (h : IsDerivation (PHP 4 3) π) :
    ∃ (A U : Finset C) (L : List Nat) (t : Nat),
      A.card + U.card + t ≤ π.length ∧
      Absorbs π A ∧
      Controls π U ∧
      (∀ x ∈ initBoxes, x ∈ L) ∧
      (∀ x ∈ L, isReach x = true) ∧
      Psi144 L ≤ 416 * t ∧
      (∀ Q ∈ π, BoxCovers L Q) := by
  classical
  induction h with
  | nil =>
    refine ⟨∅, ∅, initBoxes, 0, by simp, by simp [Absorbs], by simp [Controls],
      fun _ hx => hx, initBoxes_reach, by simp [Psi144_init], by simp⟩
  | @ax π R _ hR ih =>
    obtain ⟨A, U, L, t, hbud, ha, hc, hinit, hreach, hpsi, hcov⟩ := ih
    refine ⟨insert R A, U, L, t, ?_, ?_, ?_, hinit, hreach, hpsi, ?_⟩
    · have := Finset.card_insert_le R A
      simp only [List.length_cons]
      omega
    · intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact hA Q (Finset.mem_insert_self _ _) hR
      · exact ha a (fun B hB hBP => hA B (Finset.mem_insert_of_mem hB) hBP) Q hQ
    · intro a hrows hcols Q hQ hnc
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact hrows Q hR hnc
      · exact hc a hrows hcols Q hQ hnc
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · rcases phpCases.mp hR with ⟨i, rfl⟩ | hcol
        · obtain ⟨x, hx, hxc⟩ := rowAx_covered i
          exact Or.inr ⟨x, hinit x hx, hxc⟩
        · exact Or.inl (fun h => asg_sat_coll h hcol)
      · exact hcov Q hQ
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨v, hp, hn, heq⟩ := hR
    obtain ⟨A, U, L, t, hbud, ha, hc, hinit, hreach, hpsi, hcov⟩ := ih
    have ha' : Absorbs (R :: π) A := by
      intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact satResolve heq (ha a hA P hP) (ha a hA N hN)
      · exact ha a hA Q hQ
    by_cases hcolN : Coll N
    · refine ⟨A, insert N U, L, t, ?_, ha', ?_, hinit, hreach, hpsi, ?_⟩
      · have := Finset.card_insert_le N U
        simp only [List.length_cons]
        omega
      · intro a hrows hcols Q hQ hnc
        have ihc := hc a hrows (fun B hBU hBC => hcols B (Finset.mem_insert_of_mem hBU) hBC)
        rcases List.mem_cons.mp hQ with rfl | hQ
        · have sP := ihc P hP (fun hcol => collisionNoPos hcol v hp)
          have sN := hcols N (Finset.mem_insert_self _ _) hcolN
          exact satResolve heq sP sN
        · exact ihc Q hQ hnc
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · rcases hcov P hP with hPsat | ⟨x, hxL, hxCov⟩
          · exact Or.inl (fun h => satResolve heq (hPsat h) (asg_sat_coll h hcolN))
          · exact Or.inr ⟨x, hxL, fun h hRu => hxCov h (fun hPs => hRu (satResolve heq hPs (asg_sat_coll h hcolN)))⟩
        · exact hcov Q hQ
    · have hc' : Controls (R :: π) U := by
        intro a hrows hcols Q hQ hnc
        have ihc := hc a hrows hcols
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact satResolve heq (ihc P hP (fun hcol => collisionNoPos hcol v hp)) (ihc N hN hcolN)
        · exact ihc Q hQ hnc
      rcases glue_res_step hreach (hcov P hP) (hcov N hN) hp hn heq with hRcov | ⟨c, hcL, d, hdL, e, hstep, heCov⟩
      · refine ⟨A, U, L, t + 1, ?_, ha', hc', hinit, hreach, by omega, ?_⟩
        · simp only [List.length_cons]; omega
        · intro Q hQ
          rcases List.mem_cons.mp hQ with rfl | hQ
          · exact hRcov
          · exact hcov Q hQ
      · refine ⟨A, U, e :: L, t + 1, ?_, ha', hc', ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · intro x hx; exact List.mem_cons_of_mem e (hinit x hx)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · obtain ⟨_, _, _, _, _, _, _, _, _, hre, _⟩ := hstep; exact hre
          · exact hreach x hx
        · have hle1 := Psi144_cons_le (e := e) hcL hdL
          have hle2 := delta144_le_416 hstep
          omega
        · intro Q hQ
          rcases List.mem_cons.mp hQ with rfl | hQ
          · exact Or.inr ⟨e, List.mem_cons_self .., heCov⟩
          · rcases hcov Q hQ with hQsat | ⟨x, hxL, hxCov⟩
            · exact Or.inl hQsat
            · exact Or.inr ⟨x, List.mem_cons_of_mem e hxL, hxCov⟩

theorem refutationLower {π : List C} (hπ : IsRefutation (PHP 4 3) π) :
    52 ≤ π.length := by
  obtain ⟨A, U, L, t, hbud, ha, hc, _, hreach, hpsi, hcov⟩ := collect hπ.1
  have hab := Finset.card_le_card (requiredAxioms ha hπ.2)
  rw [axiomBank_card] at hab
  have hub := Finset.card_le_card (requiredCollisions hc hπ.2)
  rw [collisionBank_card] at hub
  have h0L : 0 ∈ L := by
    rcases hcov ∅ hπ.2 with hsat | ⟨x, hxL, hxCov⟩
    · exact (emptyUnsat (asg (fun _ => 0)) (hsat (fun _ => 0))).elim
    · have hlt : x < 4096 := by
        have hr := hreach x hxL
        simp only [isReach, Bool.and_eq_true, decide_eq_true_eq] at hr
        exact hr.1
      have hx0 : x = 0 := empty_forces_zero hlt (fun h => hxCov h (emptyUnsat (asg h)))
      exact hx0 ▸ hxL
  have hlow := Psi144_zero_le h0L
  omega

end PEqualNP.Outside.L_pcx_150_aux

theorem PEqualNP.Outside.L_pcx_150 : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 51) := by
  rintro ⟨π, hπ, hlen⟩
  have := PEqualNP.Outside.L_pcx_150_aux.refutationLower hπ
  omega
