import Mathlib
import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2262_3
  (normaliser : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (p q : ℕ),
    let c := InCone 11 C
    IsLeastAO G C ∧ TopForm G C ∧ p < q ∧ junk G C = {p,q} ∧
      ¬c p q ∧ (∃ j ∈ tops G C, c p j ∧ c q j) →
    let R := Finset.range 40
    ∀ v : Fin 11 → Finset ℕ, (∀ i, v i ⊆ R) →
    let I := Finset.univ.image v
    let col := fun (g : (Fin 11 → Bool) → Bool) => R.filter (fun r => g (fun i => decide (r ∈ v i)))
    let d := col (gateVal 11 C p)
    let e := col (gateVal 11 C q)
    let T := insert 40 (col (circuitFun 11 C))
    ∃ D K : Finset (Finset ℕ),
      let X := insert (insert 40 d) (insert (insert 41 e) I)
      let P := D.filter (· ⊆ R)
      let A := Finset.image₂ (· ∩ ·) P P
      let f := fun a b : Finset ℕ => (a ∩ b ∩ R) ∪ (if {40,41} ⊆ a ∪ b then {40} else ∅)
      d ∈ A ∧ e ∈ A ∧ (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a ⊂ w ∧ b ⊂ w ∧ w = a ∪ b) ∧
      K ⊆ Finset.image₂ f D D ∧ K.biUnion id = T ∧ (D \ X).card + 2*K.card+1 ≤ C.size)
  (exclure :
    let R := Finset.range 40
    let V : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
    let I := V.toFinset.image (fun v => R.filter (fun i => v.testBit i = true))
    let T := insert 40 (Finset.range 16)
    ∀ (d e : Finset ℕ) (D B : Finset (Finset ℕ)),
      let X := insert (insert 40 d) (insert (insert 41 e) I)
      let P := D.filter (· ⊆ R)
      let A := Finset.image₂ (· ∩ ·) P P
      let f := fun a b : Finset ℕ => (a ∩ b ∩ R) ∪ (if {40,41} ⊆ a ∪ b then {40} else ∅)
      let F := Finset.image₂ f D D
      d ∈ A → e ∈ A → ¬d ⊆ Finset.range 16 → ¬e ⊆ Finset.range 16 →
      (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a ⊂ w ∧ b ⊂ w ∧ w = a ∪ b) →
      D ⊆ (Finset.range 42).powerset → 1 ≤ (D \ X).card → (D \ X).card ≤ 18 → B.card ≤ 9 →
      B.biUnion id = T → (∀ b ∈ B, b ∈ F ∧ b ⊆ T ∧ ∀ c ∈ F, c ⊆ T → b ⊆ c → c = b) →
      (∀ b ∈ B, ∃ r ∈ b, ∀ c ∈ B, r ∈ c → c = b) → 21 ≤ (D \ X).card + 2*B.card)
  (casPur : ∀ (I : Finset (Finset ℕ)) (d e : Finset ℕ) (D K : Finset (Finset ℕ))
    (R P : Finset ℕ) (u v : ℕ), u ∉ R → v ∉ R → P ⊆ R →
    (∀ a ∈ I, a ⊆ R ∧ ¬a ⊆ P ∧ ∀ b ∈ I, a ≠ b → (a ∩ b ∩ P).card ≤ 1) →
    D ⊆ insert (insert u d) (insert (insert v e) I) →
    d ∈ Finset.image₂ (· ∩ ·) (D.filter (· ⊆ R)) (D.filter (· ⊆ R)) →
    e ∈ Finset.image₂ (· ∩ ·) (D.filter (· ⊆ R)) (D.filter (· ⊆ R)) →
    K ⊆ Finset.image₂ (fun a b : Finset ℕ => (a ∩ b ∩ R) ∪ (if {u,v} ⊆ a ∪ b then {u} else ∅)) D D →
    K.biUnion id = insert u P → P.card ≤ K.card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  have compacte (F : Finset (Finset ℕ)) (T : Finset ℕ)
      (S : Finset (Finset ℕ)) (sub : S ⊆ F) (hits : S.biUnion id = T) :
      ∃ B : Finset (Finset ℕ), B.card ≤ S.card ∧ B.biUnion id = T ∧
        (∀ b ∈ B, b ∈ F ∧ b ⊆ T ∧ ∀ c ∈ F, c ⊆ T → b ⊆ c → c = b) ∧
        (∀ b ∈ B, ∃ r ∈ b, ∀ c ∈ B, r ∈ c → c = b) := by
    classical
    let good := F.filter (· ⊆ T)
    have extMax (s : Finset ℕ) (hs : s ∈ S) :
        ∃ b ∈ good, s ⊆ b ∧ ∀ c ∈ good, b ⊆ c → c = b := by
      let up := good.filter (s ⊆ ·)
      have su : s ∈ up := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨sub hs, ?_⟩, Finset.Subset.rfl⟩
        intro r hr
        rw [← hits]
        exact Finset.mem_biUnion.mpr ⟨s,hs,hr⟩
      obtain ⟨b,hb,highest⟩ := Finset.exists_max_image up Finset.card ⟨s,su⟩
      obtain ⟨hg,hsb⟩ := Finset.mem_filter.mp hb
      refine ⟨b,hg,hsb,?_⟩
      intro c hc hbc
      exact (Finset.eq_of_subset_of_card_le hbc (highest _ (Finset.mem_filter.mpr
        ⟨hc,hsb.trans hbc⟩))).symm
    choose g hg hsg hmax using extMax
    let M := S.attach.image (fun s => g s.1 s.2)
    have info {b} (hb : b ∈ M) : b ∈ good ∧ ∀ c ∈ good, b ⊆ c → c = b := by
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨hg s s.2,hmax s s.2⟩
    have coverM : M.biUnion id = T := by
      ext r
      constructor
      · intro hr
        obtain ⟨b,hb,hrb⟩ := Finset.mem_biUnion.mp hr
        exact (Finset.mem_filter.mp (info hb).1).2 hrb
      · intro hr
        rw [← hits] at hr
        obtain ⟨s,hs,hrs⟩ := Finset.mem_biUnion.mp hr
        exact Finset.mem_biUnion.mpr ⟨g s hs,Finset.mem_image.mpr
          ⟨⟨s,hs⟩,Finset.mem_attach _ _,rfl⟩,hsg s hs hrs⟩
    let covers := M.powerset.filter (fun B => B.biUnion id = T)
    have hM : M ∈ covers := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl,coverM⟩
    obtain ⟨B,hB,lo⟩ := Finset.exists_min_image covers Finset.card ⟨M,hM⟩
    obtain ⟨bm,bt⟩ := Finset.mem_filter.mp hB
    have incl := Finset.mem_powerset.mp bm
    refine ⟨B,(lo M hM).trans ((Finset.card_image_le).trans_eq Finset.card_attach),bt,?_,?_⟩
    · intro b hb
      obtain ⟨inGood,maximal⟩ := info (incl hb)
      exact ⟨(Finset.mem_filter.mp inGood).1,(Finset.mem_filter.mp inGood).2,
        fun c hc hct => maximal _ (Finset.mem_filter.mpr ⟨hc,hct⟩)⟩
    · intro b hb
      by_contra! none
      have same : (B.erase b).biUnion id = T := by
        rw [← bt]
        ext r
        simp only [Finset.mem_biUnion,id_eq]
        constructor
        · rintro ⟨c,hc,hr⟩
          exact ⟨c,Finset.mem_of_mem_erase hc,hr⟩
        · rintro ⟨c,hc,hr⟩
          by_cases eq : c = b
          · subst c
            obtain ⟨d,hd,hrd,hne⟩ := none r hr
            exact ⟨d,Finset.mem_erase.mpr ⟨hne,hd⟩,hrd⟩
          · exact ⟨c,Finset.mem_erase.mpr ⟨eq,hc⟩,hr⟩
      have smaller := lo (B.erase b) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans incl),same⟩)
      exact (Nat.not_lt_of_ge smaller) (Finset.card_erase_lt_of_mem hb)
  have saleLocale (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (hG : G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)])
    (hao : AndOrOnly C) (hj : j ∈ junk G C) :
    let V : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
    let R := Finset.range 40
    let v := fun i : Fin 11 => R.filter ((V.getD i.val 0).testBit ·)
    ¬ (R.filter (fun r => gateVal 11 C j (fun i => decide (r ∈ v i)) = true)) ⊆ Finset.range 16 := by
    intro V R v hsub
    obtain ⟨x, hx, hF⟩ := (Finset.mem_filter.mp hj).2.2.2
    have e : ∀ a b : Fin 11, G.Adj a b → (x a && x b) = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ||
        decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = false at hF
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists, not_and] at hF
      intro a b hab
      cases ha : x a <;> cases hb : x b <;> first | rfl | exact (hF.2 a b hab ha hb).elim
    -- Toute affectation indépendante est dominée par une des 24 dernières lignes.
    have cle : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
        (b0 && b9) = false → (b0 && b10) = false → (b1 && b4) = false →
        (b1 && b8) = false → (b2 && b5) = false → (b2 && b10) = false →
        (b3 && b6) = false → (b3 && b7) = false → (b4 && b8) = false →
        (b4 && b10) = false → (b5 && b8) = false → (b5 && b9) = false →
        (b6 && b7) = false → (b6 && b10) = false → (b7 && b9) = false → (b8 && b9) = false →
        ∃ r : Fin 24, ∀ i : Fin 11,
          (![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10] : Fin 11 → Bool) i ≤
            (V.getD i.val 0).testBit (16 + r.val) := by
      dsimp only [V]
      decide +kernel
    obtain ⟨r, hle⟩ := cle (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (e 0 9 (by rw [hG]; decide)) (e 0 10 (by rw [hG]; decide))
      (e 1 4 (by rw [hG]; decide)) (e 1 8 (by rw [hG]; decide))
      (e 2 5 (by rw [hG]; decide)) (e 2 10 (by rw [hG]; decide))
      (e 3 6 (by rw [hG]; decide)) (e 3 7 (by rw [hG]; decide))
      (e 4 8 (by rw [hG]; decide)) (e 4 10 (by rw [hG]; decide))
      (e 5 8 (by rw [hG]; decide)) (e 5 9 (by rw [hG]; decide))
      (e 6 7 (by rw [hG]; decide)) (e 6 10 (by rw [hG]; decide))
      (e 7 9 (by rw [hG]; decide)) (e 8 9 (by rw [hG]; decide))
    have hr : 16 + r.val ∈ R := Finset.mem_range.mpr (by omega)
    have hxy : ∀ i : Fin 11, x i ≤ decide (16 + r.val ∈ v i) := by
      intro i
      simp only [v, Finset.mem_filter, hr, true_and, Bool.decide_eq_true]
      have hi := hle i
      fin_cases i <;> exact hi
    -- Les vecteurs des fils restent ordonnés après chaque porte ET ou OU.
    have getLe : ∀ (w w' : List Bool), List.Forall₂ (fun a b => a ≤ b) w w' →
        ∀ i : ℕ, w.getD i false ≤ w'.getD i false := by
      intro w w' h i
      induction h generalizing i with
      | nil => simp
      | cons hab _ ih => cases i with
        | zero => simpa using hab
        | succ i => simpa using ih i
    have bLe : ∀ a b : Bool, a ≤ b ↔ (a = true → b = true) := by decide
    have gateLe : ∀ (g : Gate), (g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
        g.op.eval (g.inputs.map fun i => w.getD i false) ≤
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      intro g hg w w' h
      rw [bLe]
      rcases hg with hg | hg
      · rw [hg]
        change (g.inputs.map (fun i => w.getD i false)).all id = true →
          (g.inputs.map (fun i => w'.getD i false)).all id = true
        simp only [List.all_eq_true, List.mem_map, id]
        intro hall z hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact (bLe _ _).mp (getLe _ _ h i) (hall _ ⟨i, hi, rfl⟩)
      · rw [hg]
        change (g.inputs.map (fun i => w.getD i false)).any id = true →
          (g.inputs.map (fun i => w'.getD i false)).any id = true
        simp only [List.any_eq_true, List.mem_map, id]
        rintro ⟨z, ⟨i, hi, rfl⟩, hz⟩
        exact ⟨_, ⟨i, hi, rfl⟩, (bLe _ _).mp (getLe _ _ h i) hz⟩
    have foldLe : ∀ gs : List Gate, (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
        List.Forall₂ (fun a b => a ≤ b)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
      intro gs
      induction gs with
      | nil => intro hgs w w' h; exact h
      | cons g gs ih =>
        intro hgs w w' h
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        exact List.rel_append h (List.Forall₂.cons (gateLe g (hgs g List.mem_cons_self) _ _ h) List.Forall₂.nil)
    have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x)
        (List.ofFn (fun i => decide (16 + r.val ∈ v i))) := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact hxy _
    have hy : gateVal 11 C j (fun i => decide (16 + r.val ∈ v i)) = true :=
      (bLe _ _).mp (getLe _ _ (foldLe C.gates hao _ _ h0) (11 + j)) hx
    have hlt := Finset.mem_range.mp (hsub (Finset.mem_filter.mpr ⟨hr, hy⟩))
    omega
  intro G inst C p q graph least form T0 Z U cone _ _ _ _ pq junk hp hq shared
  let V : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let R := Finset.range 40
  let v := fun i : Fin 11 => R.filter ((V.getD i.val 0).testBit ·)
  let pos := Finset.range 16
  let target := insert 40 pos
  have valid (i : Fin 11) : v i ⊆ R := Finset.filter_subset _ _
  have inputEq : Finset.univ.image v = V.toFinset.image (fun a => R.filter (fun r => a.testBit r = true)) := by
    have index : Finset.univ.image (fun i : Fin 11 => V.getD i.val 0) = V.toFinset := by decide +kernel
    rw [← index,Finset.image_image]
    rfl
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let H := edgeGraph 11 E
  let hc : DecidableRel H.Adj := inferInstance
  have mask : (R.filter fun r => @NestedCover.graphFun 11 H hc ∅ (fun i => decide (r ∈ v i))) = pos := by
    decide +kernel
  have table : (R.filter fun r => circuitFun 11 C (fun i => decide (r ∈ v i))) = pos := by
    rw [least.2.1]
    change G = H at graph
    subst G
    have hi : inst = hc := Subsingleton.elim _ _
    rw [hi]
    exact mask
  let d := R.filter (fun r => gateVal 11 C p (fun i => decide (r ∈ v i)) = true)
  let e := R.filter (fun r => gateVal 11 C q (fun i => decide (r ∈ v i)) = true)
  have dp : ¬ d ⊆ pos := saleLocale G C p graph least.1.1 (by rw [junk]; simp)
  have ep : ¬ e ⊆ pos := saleLocale G C q graph least.1.1 (by rw [junk]; simp)
  obtain ⟨D,K,hd,he,joins,available,cover,cost⟩ := normaliser G C p q ⟨least,form,pq,junk,hp,shared⟩ v valid
  let X := insert (insert 40 d) (insert (insert 41 e) (V.toFinset.image (fun a => R.filter (fun r => a.testBit r = true))))
  let f := fun a b : Finset ℕ => (a ∩ b ∩ R) ∪ (if {40,41} ⊆ a ∪ b then {40} else ∅)
  let F := Finset.image₂ f D D
  change K.biUnion id = insert 40 (R.filter fun r => circuitFun 11 C (fun i => decide (r ∈ v i))) at cover
  rw [table] at cover
  change K ⊆ F at available
  obtain ⟨B,small,bt,maximal,privateRow⟩ := compacte F target K available cover
  rw [inputEq] at cost joins
  change (D \ X).card + 2*K.card+1 ≤ C.size at cost
  let I := V.toFinset.image (fun a => R.filter (fun r => a.testBit r = true))
  have facts : ∀ a ∈ I, a ⊆ R ∧ ¬ a ⊆ pos ∧ ∀ b ∈ I, a ≠ b → (a ∩ b ∩ pos).card ≤ 1 := by
    decide +kernel
  have endmark : 40 ∈ target := Finset.mem_insert_self _ _
  have bpos : 0 < B.card := by
    rw [← bt] at endmark
    obtain ⟨b,hb,_⟩ := Finset.mem_biUnion.mp endmark
    exact Finset.card_pos.mpr ⟨b,hb⟩
  by_contra! short
  have low : 1 ≤ (D \ X).card := by
    by_contra! nil
    have empty : D \ X = ∅ := Finset.card_eq_zero.mp (by omega)
    have bound := casPur I d e D K R pos 40 41 (by decide) (by decide)
      (by decide) facts (Finset.sdiff_eq_empty_iff_subset.mp empty) hd he available cover
    have : pos.card = 16 := by decide
    omega
  have compactD : D ⊆ (Finset.range 42).powerset := by
    let P := D.filter (· ⊆ R)
    have pure {k : Finset ℕ} (hk : k ∈ Finset.image₂ (· ∩ ·) P P) : k ⊆ R := by
      obtain ⟨a,ha,b,_,rfl⟩ := Finset.mem_image₂.mp hk
      exact Finset.inter_subset_left.trans (Finset.mem_filter.mp ha).2
    have sub : R ⊆ Finset.range 42 := Finset.range_mono (by decide)
    have base (s : Finset ℕ) (hs : s ∈ X) : s ⊆ Finset.range 42 := by
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Finset.insert_subset (by decide) ((pure hd).trans sub)
      rcases Finset.mem_insert.mp hs with rfl | hi
      · exact Finset.insert_subset (by decide) ((pure he).trans sub)
      exact ((facts _ hi).1).trans sub
    have lim (n : ℕ) : ∀ w ∈ D, w.card = n → w ⊆ Finset.range 42 := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro w hw eq
        by_cases hx : w ∈ X
        · exact base w hx
        obtain ⟨a,ha,b,hb,al,bl,eqab⟩ := joins w (Finset.mem_sdiff.mpr ⟨hw,hx⟩)
        have aa := ih a.card (eq ▸ Finset.card_lt_card al) a ha rfl
        have bb := ih b.card (eq ▸ Finset.card_lt_card bl) b hb rfl
        exact eqab ▸ Finset.union_subset aa bb
    exact fun w hw => Finset.mem_powerset.mpr (lim w.card w hw rfl)
  have upper : (D \ X).card ≤ 18 := by omega
  have few : B.card ≤ 9 := by omega
  have stop := exclure d e D B hd he dp ep joins compactD low upper few bt maximal privateRow
  change 21 ≤ (D \ X).card + 2 * B.card at stop
  omega
