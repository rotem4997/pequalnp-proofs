import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5983

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def free (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 65535 ∨ v ∈ S

def comb (o : Bool) (a b : ℕ) : ℕ := if o then a &&& b else a ||| b

def Can (f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => free S f
  | k + 1, S => ∃ (o : Bool) (a b : ℕ), free S a ∧ free S b ∧ Can f k (insert (comb o a b) S)

theorem freeMono {v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : free S v) : free T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem monoC {f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : Can f k S) : Can f k T := by
  induction k generalizing S T with
  | zero => exact freeMono h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    exact ⟨o, a, b, freeMono h ha, freeMono h hb, ih (Finset.insert_subset_insert _ h) hh⟩

theorem stepUp {f k : ℕ} {S : Finset ℕ} (hc : Can f k S) : Can f (k + 1) S :=
  ⟨true, 0, 0, Or.inl rfl, Or.inl rfl, monoC (Finset.subset_insert _ _) hc⟩

theorem small {f k : ℕ} {S : Finset ℕ} (hc : Can f k S) :
    ∃ T ⊆ S, T.card ≤ k + 1 ∧ Can f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅, by simp, by simp, Or.inl h⟩
    · exact ⟨∅, by simp, by simp, Or.inr (Or.inl h)⟩
    · exact ⟨{f}, by simpa, by simp, Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    let v := comb o a b
    obtain ⟨T, hT, hn, hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a, b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a, b} : Finset ℕ), free S w → free U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a, b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a, b} ∩ S) ⊆ {a, b})
      have htwo : ({a, b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U, hU, by dsimp [U]; omega, o, a, b, liftWire a (by simp) ha, liftWire b (by simp) hb, monoC ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hx⟩)))
    · refine ⟨T, ?_, by omega, stepUp hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem monoAgree {f k p q : ℕ} {S : Finset ℕ} (hc : Can f k S)
    (hq1 : (65535 : ℕ).testBit q = true)
    (hs : ∀ v ∈ S, v.testBit q = false → v.testBit p = false) :
    f.testBit q = false → f.testBit p = false := by
  induction k generalizing S with
  | zero =>
    rcases hc with rfl | rfl | h
    · intro _; simp
    · intro h; rw [hq1] at h; cases h
    · exact hs _ h
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    have w {v} (hv : free S v) : v.testBit q = false → v.testBit p = false := by
      rcases hv with rfl | rfl | h
      · intro _; simp
      · intro h; rw [hq1] at h; cases h
      · exact hs _ h
    have hg : (comb o a b).testBit q = false → (comb o a b).testBit p = false := by
      cases o
      · change (a ||| b).testBit q = false → (a ||| b).testBit p = false
        rw [Nat.testBit_lor, Nat.testBit_lor, Bool.or_eq_false_iff, Bool.or_eq_false_iff]
        intro h
        exact ⟨w ha h.1, w hb h.2⟩
      · change (a &&& b).testBit q = false → (a &&& b).testBit p = false
        rw [Nat.testBit_land, Nat.testBit_land, Bool.and_eq_false_iff, Bool.and_eq_false_iff]
        intro h
        rcases h with h | h
        · exact Or.inl (w ha h)
        · exact Or.inr (w hb h)
    apply ih hh
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact hg
    · exact hs _ h

def gt : GateOp → List ℕ → ℕ
  | GateOp.and, [] => 65535
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | _, _ => 0

def tstep (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt g.op (g.inputs.map fun i => T.getD i 0)]

def tabs (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl tstep T0

def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gt_lt (op : GateOp) (l : List ℕ) (hl : ∀ x ∈ l, x < 65536) : gt op l < 65536 := by
  have h16 : (65536 : ℕ) = 2 ^ 16 := rfl
  cases op with
  | and =>
    cases l with
    | nil => decide
    | cons a tl =>
      cases tl with
      | nil => exact hl a (by simp)
      | cons b _ =>
        rw [gt, h16]
        exact Nat.and_lt_two_pow a (hl b (by simp))
  | or =>
    cases l with
    | nil => decide
    | cons a tl =>
      cases tl with
      | nil => exact hl a (by simp)
      | cons b _ =>
        rw [gt, h16]
        exact Nat.or_lt_two_pow (hl a (by simp)) (hl b (by simp))
  | not => exact (by decide : 0 < 65536)
  | mod _ => exact (by decide : 0 < 65536)
  | maj => exact (by decide : 0 < 65536)

theorem getD_lt (T : List ℕ) (hT : ∀ x ∈ T, x < 65536) (i : ℕ) : T.getD i 0 < 65536 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => decide
  | some x => exact hT x (List.mem_of_getElem? h)

theorem tabs_lt (gs : List Gate) : ∀ (T0 : List ℕ), (∀ x ∈ T0, x < 65536) →
    ∀ x ∈ tabs T0 gs, x < 65536 := by
  induction gs with
  | nil => intro T0 hT0; exact hT0
  | cons g gs ih =>
    intro T0 hT0
    apply ih (tstep T0 g)
    intro x hx
    simp only [tstep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hT0 x hx
    · apply gt_lt
      intro y hy
      rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
      exact getD_lt T0 hT0 i

theorem gt_testBit (p : ℕ) (hp : (65535 : ℕ).testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (hl : l.length ≤ 2) :
    (gt op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h <;> rw [h] <;> simp [gt, GateOp.eval, hp]
  | [a], _ => rcases hop with h | h <;> rw [h] <;> simp [gt, GateOp.eval]
  | [a, b], _ => rcases hop with h | h <;> rw [h] <;> simp [gt, GateOp.eval]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabs (p : ℕ) (hp : (65535 : ℕ).testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit p hp g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

theorem getWire (T : List ℕ) (i : ℕ) : free T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoice (T : List ℕ) (g : Gate) (hg : GOk g) :
    ∃ (o : Bool) (a b : ℕ), free T.toFinset a ∧ free T.toFinset b ∧
      gt g.op (g.inputs.map fun i => T.getD i 0) = comb o a b := by
  obtain ⟨hop, hl⟩ := hg
  generalize g.inputs = ins at hl ⊢
  have z : free T.toFinset 0 := Or.inl rfl
  have u : free T.toFinset 65535 := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨false, 65535, 0, u, z, by simp [gt, comb]⟩
    · exact ⟨false, 0, 0, z, z, rfl⟩
  | [i], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨false, _, 0, getWire T i, z, by simp [gt, comb]⟩
    · exact ⟨false, _, 0, getWire T i, z, by simp [gt, comb]⟩
  | [i, j], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨true, _, _, getWire T i, getWire T j, rfl⟩
    · exact ⟨false, _, _, getWire T i, getWire T j, rfl⟩

theorem fromTabs (f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOk g)
    (h : free (tabs T gs).toFinset f) : Can f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o, a, b, ha, hb, e⟩ := gateChoice T g (ok g (by simp))
    have hh := ih (tstep T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o, a, b, ha, hb, ?_⟩
    rw [← e]
    simpa [tstep] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j + 1 => (cuts j xs).map (x :: ·) ++ cuts (j + 1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[], by simp [cuts], h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], by simp [cuts], by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_, by simp, h⟩
      · by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U, hU, sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x :: U, List.mem_append_left _ (List.mem_map.mpr ⟨U, hU, rfl⟩), ?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e, hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U, hU, sub⟩ := ih (j + 1) T hs n
          exact ⟨U, List.mem_append_right _ hU, sub⟩

def covAt (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => if v.testBit q then covAt q vs else v ||| covAt q vs

theorem covAt_false {q p : ℕ} {l : List ℕ} (h : (covAt q l).testBit p = false) :
    ∀ v ∈ l, v.testBit q = false → v.testBit p = false := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro v hv hq
    simp only [covAt] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · simp only [hq, Bool.false_eq_true, ↓reduceIte, Nat.testBit_lor, Bool.or_eq_false_iff] at h
      exact h.1
    · split at h
      · exact ih h v hv hq
      · simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at h
        exact ih h.2 v hv hq

theorem covered_one {f k q : ℕ} {l : List ℕ} (hc : Can f k l.toFinset)
    (hq1 : (65535 : ℕ).testBit q = true) (hfq : f.testBit q = false) :
    covAt q l &&& f = f := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_land]
  cases hfp : f.testBit p
  · simp
  · simp only [Bool.and_true]
    cases he : (covAt q l).testBit p
    · exfalso
      have := monoAgree hc hq1 (fun v hv => covAt_false he v (List.mem_toFinset.mp hv)) hfq
      rw [hfp] at this
      cases this
    · rfl

def okSet (f : ℕ) (ns U : List ℕ) : Bool :=
  ns.all (fun q => (covAt q U &&& f) == f)

theorem covered {f k : ℕ} {ns l : List ℕ} (hc : Can f k l.toFinset)
    (hns : ∀ q ∈ ns, (65535 : ℕ).testBit q = true ∧ f.testBit q = false) :
    okSet f ns l = true := by
  unfold okSet
  rw [List.all_eq_true]
  intro q hq
  simp only [beq_iff_eq]
  exact covered_one hc (hns q hq).1 (hns q hq).2

def myDedup : List ℕ → List ℕ
  | [] => []
  | x :: xs => if xs.contains x then myDedup xs else x :: myDedup xs

theorem mem_myDedup : ∀ (l : List ℕ) (c : ℕ), c ∈ l → c ∈ myDedup l
  | [], _, h => by simp at h
  | a :: l, c, h => by
    unfold myDedup
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i hc; exact mem_myDedup l _ (List.contains_iff_mem.mp hc)
      · simp
    · split
      · exact mem_myDedup l c h
      · exact List.mem_cons_of_mem _ (mem_myDedup l c h)

def uPairs : List ℕ → List ℕ
  | [] => []
  | a :: xs => (xs.flatMap fun b => [a &&& b, a ||| b]) ++ uPairs xs

theorem mem_uPairs {a b : ℕ} {S : List ℕ} (o : Bool) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    comb o a b ∈ uPairs S := by
  induction S with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [uPairs, List.mem_append, List.mem_flatMap]
    rcases List.mem_cons.mp ha with hax | ha1
    · subst hax
      rcases List.mem_cons.mp hb with hbx | hb1
      · exact absurd hbx.symm hne
      · left
        refine ⟨b, hb1, ?_⟩
        cases o <;> simp [comb]
    · rcases List.mem_cons.mp hb with hbx | hb1
      · subst hbx
        left
        refine ⟨a, ha1, ?_⟩
        cases o
        · simp [comb, Nat.lor_comm]
        · simp [comb, Nat.land_comm]
      · exact Or.inr (ih ha1 hb1)

def vals (S : List ℕ) : List ℕ :=
  myDedup (0 :: 65535 :: (S ++ S.map (65535 &&& ·) ++ S.map (65535 ||| ·) ++ uPairs S))

theorem memVals {a b : ℕ} {S : List ℕ} (o : Bool) (ha : free S.toFinset a)
    (hb : free S.toFinset b) : comb o a b ∈ vals S := by
  apply mem_myDedup
  have inBase {w} (hw : free S.toFinset w) :
      w ∈ (0 :: 65535 :: (S ++ S.map (65535 &&& ·) ++ S.map (65535 ||| ·) ++ uPairs S)) := by
    rcases hw with rfl | rfl | hw
    · simp
    · simp
    · simp [List.mem_toFinset.mp hw]
  rcases ha with rfl | rfl | ha'
  · cases o
    · simp only [comb, ↓reduceIte, Nat.zero_or]; exact inBase hb
    · simp [comb]
  · rcases hb with rfl | rfl | hb'
    · cases o <;> simp [comb]
    · cases o <;> simp [comb]
    · cases o
      · simp only [comb, ↓reduceIte]
        have hm : 65535 ||| b ∈ S.map (65535 ||| ·) := List.mem_map.mpr ⟨b, List.mem_toFinset.mp hb', rfl⟩
        simp [hm]
      · simp only [comb, ↓reduceIte]
        have hm : 65535 &&& b ∈ S.map (65535 &&& ·) := List.mem_map.mpr ⟨b, List.mem_toFinset.mp hb', rfl⟩
        simp [hm]
  · rcases hb with rfl | rfl | hb'
    · cases o
      · simp only [comb, ↓reduceIte, Nat.or_zero]; exact inBase (Or.inr (Or.inr ha'))
      · simp [comb]
    · cases o
      · simp only [comb, ↓reduceIte, Nat.lor_comm a 65535]
        have hm : 65535 ||| a ∈ S.map (65535 ||| ·) := List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha', rfl⟩
        simp [hm]
      · simp only [comb, ↓reduceIte, Nat.land_comm a 65535]
        have hm : 65535 &&& a ∈ S.map (65535 &&& ·) := List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha', rfl⟩
        simp [hm]
    · by_cases hne : a = b
      · subst hne
        cases o <;> simp [comb, List.mem_toFinset.mp ha']
      · have hu := mem_uPairs o (List.mem_toFinset.mp ha') (List.mem_toFinset.mp hb') hne
        simp [hu]

def checkSub (f : ℕ) (ns : List ℕ) (U : List ℕ) (localNext : List (List ℕ)) : Bool :=
  !okSet f ns U || localNext.any (fun V => U.all (fun x => V.contains x))

def verifyFast (f : ℕ) (ns : List ℕ) (k : ℕ) (S : List ℕ)
    (localNext nextLevel : List (List ℕ)) : Bool :=
  localNext.all (fun V => nextLevel.contains V) &&
  (cuts (k + 1) S).all (fun U => checkSub f ns U localNext) &&
  (let ws := cuts k S
   (vals S).all fun v =>
     S.contains v || ws.all (fun W => checkSub f ns (v :: W) localNext))

theorem checkSub_sound {f k : ℕ} {ns U : List ℕ} {localNext : List (List ℕ)}
    (hns : ∀ q ∈ ns, (65535 : ℕ).testBit q = true ∧ f.testBit q = false)
    (hcU : Can f k U.toFinset) (hchk : checkSub f ns U localNext = true) :
    ∃ V ∈ localNext, Can f k V.toFinset := by
  unfold checkSub at hchk
  have hcov := covered hcU hns
  simp only [hcov, Bool.not_true, Bool.false_or, List.any_eq_true] at hchk
  obtain ⟨V, hV, hsub⟩ := hchk
  refine ⟨V, hV, monoC ?_ hcU⟩
  intro x hx
  exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hsub _ (List.mem_toFinset.mp hx)))

theorem advanceFast {f k : ℕ} {ns S : List ℕ} {L N : List (List ℕ)}
    (hns : ∀ q ∈ ns, (65535 : ℕ).testBit q = true ∧ f.testBit q = false)
    (hv : verifyFast f ns k S L N = true) (hc : Can f (k + 1) S.toFinset) :
    ∃ V ∈ N, Can f k V.toFinset := by
  unfold verifyFast at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨hLN, hS0⟩, hVals⟩ := hv
  obtain ⟨o, a, b, ha, hb, hh⟩ := hc
  let v := comb o a b
  obtain ⟨T, hT, hn, ht⟩ := small hh
  change T ⊆ insert v S.toFinset at hT
  have liftL : (∃ V ∈ L, Can f k V.toFinset) → ∃ V ∈ N, Can f k V.toFinset := by
    rintro ⟨V, hVL, hcV⟩
    exact ⟨V, List.contains_iff_mem.mp (List.all_eq_true.mp hLN V hVL), hcV⟩
  by_cases hvin : v ∈ S
  · have hTS : T ⊆ S.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with rfl | hx'
      · exact List.mem_toFinset.mpr hvin
      · exact hx'
    obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) S T hTS hn
    exact liftL (checkSub_sound hns (monoC hu ht) (List.all_eq_true.mp hS0 U hU))
  · by_cases hvT : v ∈ T
    · have hTer : T.erase v ⊆ S.toFinset := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hcard : (T.erase v).card ≤ k := by rw [Finset.card_erase_of_mem hvT]; omega
      obtain ⟨W, hW, hw⟩ := cutsSpec k S (T.erase v) hTer hcard
      have hTU : T ⊆ (v :: W).toFinset := by
        intro x hx
        by_cases ex : x = v
        · simp [ex]
        · simp [List.mem_toFinset.mp (hw (Finset.mem_erase.mpr ⟨ex, hx⟩))]
      have hv_row := List.all_eq_true.mp hVals v (memVals o ha hb)
      have hsc : S.contains v = false := Bool.eq_false_iff.mpr (fun hc => hvin (List.contains_iff_mem.mp hc))
      rw [hsc, Bool.false_or] at hv_row
      exact liftL (checkSub_sound hns (monoC hTU ht) (List.all_eq_true.mp hv_row W hW))
    · have hTS : T ⊆ S.toFinset := by
        intro x hx
        exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun ex => hvT (ex ▸ hx))
      obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) S T hTS hn
      exact liftL (checkSub_sound hns (monoC hu ht) (List.all_eq_true.mp hS0 U hU))

theorem mem_pairs_of_fst {α β : Type} : ∀ (ps : List (α × β)) (x : α),
    x ∈ ps.map Prod.fst → ∃ y, (x, y) ∈ ps
  | [], _, h => by simp at h
  | (a, b) :: ps, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨b, List.mem_cons_self⟩
    · obtain ⟨y, hy⟩ := mem_pairs_of_fst ps x h
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem advanceRow {f k : ℕ} {ns : List ℕ} {ps : List (List ℕ × List (List ℕ))} {R N : List (List ℕ)}
    (hns : ∀ q ∈ ns, (65535 : ℕ).testBit q = true ∧ f.testBit q = false)
    (hfst : ps.map Prod.fst = R)
    (hchk : ps.all (fun p => verifyFast f ns k p.1 p.2 N) = true)
    (S : List ℕ) (hS : S ∈ R) (hc : Can f (k + 1) S.toFinset) :
    ∃ V ∈ N, Can f k V.toFinset := by
  rw [← hfst] at hS
  obtain ⟨L, hSL⟩ := mem_pairs_of_fst ps S hS
  exact advanceFast hns (List.all_eq_true.mp hchk (S, L) hSL) hc

def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

def negs : List ℕ := [0, 7, 9, 10, 11, 13, 14, 15]

theorem hnegs : ∀ q ∈ negs, (65535 : ℕ).testBit q = true ∧ (4478 : ℕ).testBit q = false := by
  decide +kernel

def row1 : List (List ℕ) := [
]

def row2 : List (List ℕ) := [
  [248, 4383, 65382],
  [240, 4383, 65390],
  [4383, 30566, 35064],
  [4383, 26214, 39416],
  [4344, 4383, 28518],
  [240, 4383, 32622],
  [504, 4383, 63078],
  [240, 4383, 63342],
  [4383, 4600, 26214],
  [240, 4383, 30574]]

def row3 : List (List ℕ) := [
  [4383, 26214, 35064, 65280],
  [240, 4383, 34952, 65382],
  [240, 4383, 28518, 63624],
  [240, 4383, 36744, 63078],
  [240, 4383, 26214, 65416],
  [248, 4383, 28518, 61440],
  [248, 4383, 17476, 65314],
  [248, 4383, 12066, 62532],
  [248, 4383, 20292, 61986],
  [248, 4383, 8738, 65348],
  [248, 4383, 26214, 65280],
  [248, 3840, 4383, 63078],
  [240, 4383, 28526, 61440],
  [240, 4383, 17476, 65322],
  [240, 4383, 12074, 62532],
  [240, 4383, 20300, 61986],
  [240, 4383, 8738, 65356],
  [240, 4383, 26214, 65288],
  [240, 3848, 4383, 63078],
  [240, 4383, 20292, 61994],
  [240, 4383, 8746, 65348],
  [240, 4383, 26222, 65280],
  [240, 3840, 4383, 63086],
  [240, 4383, 17484, 65314],
  [240, 4383, 12066, 62540],
  [240, 4383, 28518, 61448],
  [8, 240, 4383, 65382],
  [4383, 26214, 35064, 65520],
  [4080, 4383, 35064, 63078],
  [4080, 4383, 26214, 63736],
  [4383, 26214, 36856, 61680],
  [240, 4383, 36856, 63078],
  [240, 4383, 26214, 65528],
  [4383, 26470, 35064, 61440],
  [4383, 26214, 35320, 61440],
  [4383, 26214, 35064, 61696],
  [4383, 26214, 35064, 65314],
  [4383, 26214, 35064, 65348],
  [4383, 26214, 36856, 63736],
  [4383, 26214, 35064, 65528],
  [4383, 13090, 17476, 35064],
  [4383, 8738, 21828, 35064],
  [4383, 8738, 17476, 39416],
  [4352, 4383, 26214, 35064],
  [4383, 26214, 35064, 65382],
  [4383, 7936, 26214, 35064],
  [3840, 4383, 30310, 35064],
  [3840, 4383, 26214, 39160],
  [4383, 28518, 35064, 63078],
  [4383, 28518, 35064, 61680],
  [240, 4383, 35064, 65382],
  [240, 4383, 28518, 63736],
  [4383, 26214, 35064, 65416],
  [496, 4383, 34952, 63078],
  [496, 4383, 26214, 63624],
  [240, 4383, 34952, 63334],
  [240, 4383, 26470, 63624],
  [240, 4383, 35208, 63078],
  [240, 4383, 26214, 63880],
  [4336, 4383, 28518, 34952],
  [240, 4383, 32614, 34952],
  [240, 4383, 28518, 39048],
  [240, 4383, 61422, 65382],
  [240, 4383, 28518, 65518],
  [240, 4383, 65382, 65518],
  [240, 4383, 63624, 65382],
  [240, 4104, 4383, 28518],
  [240, 4383, 44970, 65382],
  [240, 4383, 28518, 65450],
  [240, 4383, 52428, 65382],
  [240, 4383, 28518, 64716],
  [240, 4383, 65382, 65450],
  [240, 4383, 64716, 65382],
  [4344, 4383, 12066, 17476],
  [240, 4383, 16170, 17476],
  [240, 4383, 12066, 21580],
  [240, 4383, 36744, 65382],
  [240, 4383, 28518, 65416],
  [240, 4383, 44970, 63078],
  [240, 4383, 26214, 65450],
  [240, 4383, 43690, 65382],
  [240, 4383, 28518, 64170],
  [240, 4383, 53196, 65382],
  [240, 4383, 28518, 65484],
  [240, 4383, 64170, 65382],
  [240, 4383, 65382, 65484],
  [4344, 4383, 8738, 20292],
  [240, 4383, 12842, 20292],
  [240, 4383, 8738, 24396],
  [240, 4383, 53196, 63078],
  [240, 4383, 26214, 65484],
  [504, 4383, 26214, 61440],
  [504, 4383, 17476, 61986],
  [504, 4383, 8738, 62532],
  [240, 4383, 26478, 61440],
  [240, 4383, 17476, 62250],
  [240, 4383, 9002, 62532],
  [240, 4383, 17740, 61986],
  [240, 4383, 8738, 62796],
  [240, 4383, 26214, 61704],
  [240, 264, 4383, 63078],
  [4336, 4383, 26214, 36744],
  [240, 4383, 30310, 36744],
  [240, 4383, 26214, 40840],
  [240, 4383, 61422, 63078],
  [240, 4383, 26214, 65518],
  [240, 4383, 63078, 65518],
  [240, 4383, 63078, 65416],
  [240, 4360, 4383, 26214],
  [240, 4383, 63078, 65450],
  [240, 4383, 63078, 65484],
  [4383, 4600, 8738, 17476],
  [240, 4383, 13098, 17476],
  [240, 4383, 8738, 21836],
  [4383, 4592, 26214, 34952],
  [240, 4383, 30566, 34952],
  [240, 4383, 26214, 39304],
  [240, 4383, 61166, 65382],
  [240, 4383, 65382, 65416],
  [240, 4383, 28518, 65262],
  [240, 4383, 65262, 65382],
  [3840, 4344, 4383, 26214],
  [240, 4383, 7944, 26214],
  [240, 3840, 4383, 30318],
  [15, 248, 4369, 65382],
  [15, 240, 4369, 65390],
  [15, 4368, 26214, 35064],
  [15, 4369, 30566, 35064],
  [15, 4369, 26214, 39416],
  [14, 240, 4369, 65382]]

def row4 : List (List ℕ) := [
  [4383, 8738, 17476, 35064, 65280],
  [3840, 4383, 26214, 35064, 61440],
  [240, 4383, 28518, 34952, 61440],
  [240, 4383, 17476, 34952, 65314],
  [240, 4383, 12066, 34952, 62532],
  [240, 4383, 12066, 17476, 63624],
  [240, 4383, 20292, 34952, 61986],
  [240, 4383, 8738, 34952, 65348],
  [240, 4383, 8738, 20292, 63624],
  [240, 4383, 26214, 36744, 61440],
  [240, 4383, 17476, 36744, 61986],
  [240, 4383, 8738, 36744, 62532],
  [240, 4383, 8738, 17476, 65416],
  [240, 4383, 26214, 34952, 65280],
  [240, 3840, 4383, 34952, 63078],
  [240, 3840, 4383, 26214, 63624],
  [15, 4369, 26214, 35064, 65280],
  [15, 240, 4369, 34952, 65382],
  [15, 240, 4369, 28518, 63624],
  [15, 240, 4369, 36744, 63078],
  [15, 240, 4369, 26214, 65416],
  [248, 4383, 12066, 17476, 61440],
  [248, 4383, 8738, 20292, 61440],
  [248, 4383, 8738, 17476, 65280],
  [248, 3840, 4383, 26214, 61440],
  [248, 3840, 4383, 17476, 61986],
  [248, 3840, 4383, 8738, 62532],
  [240, 4383, 12074, 17476, 61440],
  [240, 4383, 8738, 20300, 61440],
  [240, 4383, 8738, 17476, 65288],
  [240, 3848, 4383, 26214, 61440],
  [240, 3848, 4383, 17476, 61986],
  [240, 3848, 4383, 8738, 62532],
  [240, 4383, 8746, 20292, 61440],
  [240, 4383, 8746, 17476, 65280],
  [240, 3840, 4383, 26222, 61440],
  [240, 3840, 4383, 17476, 61994],
  [240, 3840, 4383, 8746, 62532],
  [240, 4383, 12066, 17484, 61440],
  [240, 4383, 8738, 17484, 65280],
  [240, 3840, 4383, 17484, 61986],
  [240, 3840, 4383, 8738, 62540],
  [240, 4383, 12066, 17476, 61448],
  [240, 4383, 8738, 20292, 61448],
  [240, 3840, 4383, 26214, 61448],
  [8, 240, 4383, 28518, 61440],
  [8, 240, 4383, 17476, 65314],
  [8, 240, 4383, 12066, 62532],
  [8, 240, 4383, 20292, 61986],
  [8, 240, 4383, 8738, 65348],
  [8, 240, 4383, 26214, 65280],
  [8, 240, 3840, 4383, 63078],
  [4383, 8738, 17476, 35064, 65520],
  [4080, 4383, 26214, 35064, 61440],
  [4080, 4383, 17476, 35064, 61986],
  [4080, 4383, 8738, 35064, 62532],
  [4080, 4383, 8738, 17476, 63736],
  [4383, 8738, 17476, 36856, 61680],
  [4080, 4383, 26214, 34952, 61680],
  [240, 4383, 26214, 36856, 61440],
  [240, 4383, 17476, 36856, 61986],
  [240, 4383, 8738, 36856, 62532],
  [240, 4383, 8738, 17476, 65528],
  [240, 4383, 26214, 34952, 65520],
  [240, 4080, 4383, 34952, 63078],
  [240, 4080, 4383, 26214, 63624],
  [4383, 8994, 17476, 35064, 61440],
  [4383, 8738, 17732, 35064, 61440],
  [4383, 8738, 17476, 35320, 61440],
  [4383, 8738, 17476, 35064, 61696],
  [256, 4383, 26214, 35064, 61440],
  [4383, 12066, 26214, 35064, 61440],
  [4383, 12066, 17476, 35064, 61986],
  [4383, 8738, 17476, 35064, 65314],
  [4383, 20292, 26214, 35064, 61440],
  [4383, 8738, 20292, 35064, 62532],
  [4383, 8738, 17476, 35064, 65348],
  [4383, 26214, 35064, 36856, 61440],
  [4383, 8738, 17476, 36856, 63736],
  [4383, 8738, 17476, 35064, 65528],
  [4352, 4383, 8738, 17476, 35064],
  [15, 4383, 26214, 35064, 65280],
  [4383, 8738, 26214, 35064, 65280],
  [4383, 17476, 26214, 35064, 65280],
  [3840, 4383, 26214, 35064, 65280],
  [4383, 26214, 35064, 61440, 65280],
  [4383, 7936, 8738, 17476, 35064],
  [3840, 4383, 12834, 17476, 35064],
  [3840, 4383, 8738, 21572, 35064],
  [3840, 4383, 8738, 17476, 39160],
  [3840, 4096, 4383, 26214, 35064],
  [4383, 26214, 28518, 35064, 61440],
  [3840, 4383, 26214, 35064, 63078],
  [3840, 4383, 26214, 35064, 63736],
  [3840, 4383, 26214, 35064, 61986],
  [3840, 4383, 26214, 35064, 62532],
  [4383, 12066, 17476, 35064, 61680],
  [4383, 8738, 20292, 35064, 61680],
  [3840, 4383, 26214, 35064, 61680],
  [240, 4383, 28518, 35064, 61440],
  [240, 4383, 17476, 35064, 65314],
  [240, 4383, 12066, 35064, 62532],
  [240, 4383, 12066, 17476, 63736],
  [240, 4383, 20292, 35064, 61986],
  [240, 4383, 8738, 35064, 65348],
  [240, 4383, 8738, 20292, 63736],
  [240, 4383, 26214, 35064, 65280],
  [240, 3840, 4383, 35064, 63078],
  [240, 3840, 4383, 26214, 63736],
  [4383, 26214, 35064, 36744, 61440],
  [4383, 8738, 17476, 35064, 65416],
  [4383, 26214, 34952, 35064, 65280],
  [3840, 4383, 26214, 35064, 63624],
  [240, 4383, 28518, 34952, 61680],
  [240, 4383, 26214, 36744, 61680],
  [496, 4383, 26214, 34952, 61440],
  [496, 4383, 17476, 34952, 61986],
  [496, 4383, 8738, 34952, 62532],
  [496, 4383, 8738, 17476, 63624],
  [240, 4383, 26470, 34952, 61440],
  [240, 4383, 17476, 34952, 62242],
  [240, 4383, 8994, 34952, 62532],
  [240, 4383, 8994, 17476, 63624],
  [240, 4383, 17732, 34952, 61986],
  [240, 4383, 8738, 34952, 62788],
  [240, 4383, 8738, 17732, 63624],
  [240, 4383, 26214, 35208, 61440],
  [240, 4383, 17476, 35208, 61986],
  [240, 4383, 8738, 35208, 62532],
  [240, 4383, 8738, 17476, 63880],
  [240, 4383, 26214, 34952, 61696],
  [240, 256, 4383, 34952, 63078],
  [240, 256, 4383, 26214, 63624],
  [4336, 4383, 12066, 17476, 34952],
  [240, 4383, 16162, 17476, 34952],
  [240, 4383, 12066, 21572, 34952],
  [240, 4383, 12066, 17476, 39048],
  [240, 4096, 4383, 28518, 34952],
  [240, 4383, 28518, 61422, 61440],
  [15, 240, 4383, 34952, 65382],
  [240, 4383, 28518, 34952, 65382],
  [240, 4383, 34952, 61440, 65382],
  [15, 240, 4383, 28518, 63624],
  [240, 4383, 28518, 34952, 63624],
  [240, 4383, 28518, 61440, 63624],
  [240, 4383, 28518, 44970, 61440],
  [240, 4383, 28518, 34952, 65314],
  [240, 4383, 12066, 34952, 65382],
  [240, 4383, 12066, 28518, 63624],
  [240, 4383, 28518, 52428, 61440],
  [240, 4383, 28518, 34952, 62532],
  [240, 4383, 17476, 34952, 65382],
  [240, 4383, 17476, 28518, 63624],
  [240, 4383, 17476, 44970, 65314],
  [240, 4383, 12066, 44970, 62532],
  [240, 4383, 12066, 17476, 65450],
  [240, 4383, 17476, 52428, 65314],
  [240, 4383, 34952, 65314, 65382],
  [240, 4383, 17476, 65314, 65450],
  [240, 4383, 34952, 62532, 65314],
  [240, 4383, 17476, 63624, 65314],
  [240, 4383, 12066, 52428, 62532],
  [240, 4383, 12066, 17476, 64716],
  [240, 4383, 34952, 62532, 65382],
  [240, 4383, 12066, 62532, 64716],
  [240, 4383, 12066, 62532, 63624],
  [240, 4104, 4383, 12066, 17476],
  [240, 4383, 20292, 34952, 65314],
  [240, 4383, 12066, 34952, 65348],
  [240, 4383, 12066, 20292, 63624],
  [240, 4383, 28518, 36744, 61440],
  [240, 4383, 17476, 36744, 65314],
  [240, 4383, 12066, 36744, 62532],
  [240, 4383, 12066, 17476, 65416],
  [240, 4383, 28518, 34952, 65280],
  [240, 3840, 4383, 34952, 65382],
  [240, 3840, 4383, 28518, 63624],
  [240, 4383, 26214, 44970, 61440],
  [240, 4383, 26214, 34952, 65314],
  [240, 4383, 12066, 34952, 63078],
  [240, 4383, 12066, 26214, 63624],
  [240, 4383, 28518, 43690, 61440],
  [240, 4383, 17476, 43690, 65314],
  [240, 4383, 12066, 43690, 62532],
  [240, 4383, 12066, 17476, 64170],
  [240, 4383, 28518, 34952, 61986],
  [240, 4383, 17476, 44970, 61986],
  [240, 4383, 8738, 34952, 65382],
  [240, 4383, 8738, 28518, 63624],
  [240, 4383, 8738, 44970, 62532],
  [240, 4383, 8738, 17476, 65450],
  [4336, 4383, 8738, 20292, 34952],
  [240, 4383, 12834, 20292, 34952],
  [240, 4383, 8738, 24388, 34952],
  [240, 4383, 8738, 20292, 39048],
  [240, 4383, 28518, 53196, 61440],
  [240, 4383, 28518, 34952, 65348],
  [240, 4383, 20292, 34952, 65382],
  [240, 4383, 20292, 28518, 63624],
  [240, 4383, 20292, 43690, 61986],
  [240, 4383, 8738, 43690, 65348],
  [240, 4383, 8738, 20292, 64170],
  [240, 4383, 20292, 53196, 61986],
  [240, 4383, 34952, 61986, 65382],
  [240, 4383, 20292, 61986, 64170],
  [240, 4383, 34952, 61986, 65348],
  [240, 4383, 20292, 61986, 63624],
  [240, 4383, 8738, 53196, 65348],
  [240, 4383, 8738, 20292, 65484],
  [240, 4383, 34952, 65348, 65382],
  [240, 4383, 8738, 65348, 65484],
  [240, 4383, 8738, 63624, 65348],
  [240, 4104, 4383, 8738, 20292],
  [240, 4383, 20292, 36744, 61986],
  [240, 4383, 8738, 36744, 65348],
  [240, 4383, 8738, 20292, 65416],
  [240, 4383, 26214, 53196, 61440],
  [240, 4383, 26214, 34952, 65348],
  [240, 4383, 20292, 34952, 63078],
  [240, 4383, 20292, 26214, 63624],
  [240, 4383, 20292, 52428, 61986],
  [240, 4383, 17476, 53196, 61986],
  [240, 4383, 8738, 52428, 65348],
  [240, 4383, 8738, 20292, 64716],
  [240, 4383, 8738, 53196, 62532],
  [240, 4383, 8738, 17476, 65484],
  [504, 4383, 8738, 17476, 61440],
  [240, 4383, 9002, 17476, 61440],
  [240, 4383, 8738, 17740, 61440],
  [240, 4383, 8738, 17476, 61704],
  [240, 264, 4383, 26214, 61440],
  [240, 264, 4383, 17476, 61986],
  [240, 264, 4383, 8738, 62532],
  [4336, 4383, 8738, 17476, 36744],
  [240, 4383, 12834, 17476, 36744],
  [240, 4383, 8738, 21572, 36744],
  [240, 4383, 8738, 17476, 40840],
  [240, 4096, 4383, 26214, 36744],
  [240, 4383, 26214, 61422, 61440],
  [15, 240, 4383, 36744, 63078],
  [240, 4383, 26214, 36744, 63078],
  [240, 4383, 36744, 61440, 63078],
  [15, 240, 4383, 26214, 65416],
  [240, 4383, 26214, 36744, 65416],
  [240, 4383, 26214, 61440, 65416],
  [240, 4383, 26214, 36744, 61986],
  [240, 4383, 8738, 36744, 63078],
  [240, 4383, 8738, 26214, 65416],
  [240, 4383, 26214, 36744, 62532],
  [240, 4383, 17476, 36744, 63078],
  [240, 4383, 17476, 26214, 65416],
  [240, 4383, 36744, 61986, 63078],
  [240, 4383, 17476, 61986, 65450],
  [240, 4383, 36744, 61986, 62532],
  [240, 4383, 17476, 61986, 65416],
  [240, 4383, 36744, 62532, 63078],
  [240, 4383, 8738, 62532, 65484],
  [240, 4383, 8738, 62532, 65416],
  [240, 4360, 4383, 8738, 17476],
  [240, 4383, 26214, 36744, 65280],
  [240, 3840, 4383, 36744, 63078],
  [240, 3840, 4383, 26214, 65416],
  [240, 4383, 34952, 36744, 63078],
  [240, 4383, 26214, 36744, 63624],
  [240, 4383, 26214, 34952, 65416],
  [4383, 4592, 8738, 17476, 34952],
  [240, 4383, 13090, 17476, 34952],
  [240, 4383, 8738, 21828, 34952],
  [240, 4383, 8738, 17476, 39304],
  [240, 4352, 4383, 26214, 34952],
  [240, 4383, 26214, 61166, 65280],
  [240, 4383, 26214, 34952, 65382],
  [240, 4383, 34952, 65280, 65382],
  [240, 4383, 26214, 65280, 65416],
  [240, 4383, 26214, 43690, 65280],
  [240, 4383, 26214, 52428, 65280],
  [240, 4383, 34952, 65314, 65348],
  [240, 4383, 17476, 65314, 65416],
  [240, 4383, 8738, 65348, 65416],
  [240, 4383, 34952, 63078, 65280],
  [240, 4383, 26214, 63624, 65280],
  [3840, 4336, 4383, 26214, 34952],
  [240, 4383, 7936, 26214, 34952],
  [240, 3840, 4383, 30310, 34952],
  [240, 3840, 4383, 26214, 39048],
  [240, 4383, 28518, 61166, 61440],
  [240, 4383, 28518, 34952, 63078],
  [240, 4383, 26214, 28518, 63624],
  [240, 3840, 4383, 61166, 63078],
  [240, 3840, 4383, 26214, 65262],
  [240, 4383, 34952, 63078, 65382],
  [240, 3840, 4383, 63078, 65262],
  [240, 3840, 4383, 63078, 63624],
  [240, 4383, 26214, 63624, 65416],
  [240, 3840, 4104, 4383, 26214],
  [240, 3840, 4383, 43690, 63078],
  [240, 3840, 4383, 26214, 64170],
  [240, 3840, 4383, 52428, 63078],
  [240, 3840, 4383, 26214, 64716],
  [240, 4383, 34952, 63078, 65314],
  [240, 4383, 17476, 64170, 65314],
  [240, 3840, 4383, 63078, 64170],
  [240, 4383, 34952, 63078, 65348],
  [240, 4383, 8738, 64716, 65348],
  [240, 3840, 4383, 63078, 64716],
  [3840, 4344, 4383, 8738, 17476],
  [240, 4383, 7944, 8738, 17476],
  [240, 3840, 4383, 12842, 17476],
  [240, 3840, 4383, 8738, 21580],
  [4369, 4383, 26214, 35064, 65280],
  [240, 4369, 4383, 34952, 65382],
  [240, 4369, 4383, 28518, 63624],
  [240, 4369, 4383, 36744, 63078],
  [240, 4369, 4383, 26214, 65416],
  [15, 248, 4369, 28518, 61440],
  [15, 248, 4369, 17476, 65314],
  [15, 248, 4369, 12066, 62532],
  [15, 248, 4369, 20292, 61986],
  [15, 248, 4369, 8738, 65348],
  [15, 248, 4369, 26214, 65280],
  [15, 248, 3840, 4369, 63078],
  [15, 240, 4369, 28526, 61440],
  [15, 240, 4369, 17476, 65322],
  [15, 240, 4369, 12074, 62532],
  [15, 240, 4369, 20300, 61986],
  [15, 240, 4369, 8738, 65356],
  [15, 240, 4369, 26214, 65288],
  [15, 240, 3848, 4369, 63078],
  [15, 240, 4369, 20292, 61994],
  [15, 240, 4369, 8746, 65348],
  [15, 240, 4369, 26222, 65280],
  [15, 240, 3840, 4369, 63086],
  [15, 240, 4369, 17484, 65314],
  [15, 240, 4369, 12066, 62540],
  [15, 240, 4369, 28518, 61448],
  [8, 15, 240, 4369, 65382],
  [15, 4368, 8738, 17476, 35064],
  [15, 4369, 26214, 35064, 65520],
  [15, 4080, 4369, 35064, 63078],
  [15, 4080, 4369, 26214, 63736],
  [15, 4369, 26214, 36856, 61680],
  [15, 240, 4369, 36856, 63078],
  [15, 240, 4369, 26214, 65528],
  [15, 240, 4368, 26214, 34952],
  [15, 4369, 28518, 35064, 61680],
  [15, 240, 4369, 28518, 63736],
  [15, 4369, 26470, 35064, 61440],
  [15, 4369, 26214, 35320, 61440],
  [15, 4369, 26214, 35064, 61696],
  [15, 240, 4369, 35064, 65382],
  [15, 4369, 26214, 35064, 65314],
  [15, 4369, 26214, 35064, 65348],
  [15, 4369, 26214, 36856, 63736],
  [15, 4369, 26214, 35064, 65528],
  [15, 4369, 13090, 17476, 35064],
  [15, 4369, 8738, 21828, 35064],
  [15, 4369, 8738, 17476, 39416],
  [15, 4352, 4369, 26214, 35064],
  [15, 4369, 26214, 35064, 65382],
  [15, 4369, 7936, 26214, 35064],
  [15, 3840, 4369, 30310, 35064],
  [15, 3840, 4369, 26214, 39160],
  [15, 4369, 28518, 35064, 63078],
  [15, 4369, 26214, 35064, 65416],
  [15, 240, 4369, 28518, 65416],
  [15, 240, 4369, 36744, 65382],
  [15, 4369, 4592, 26214, 34952],
  [15, 240, 4369, 30566, 34952],
  [15, 240, 4369, 26214, 39304],
  [14, 240, 4369, 26214, 65280],
  [15, 240, 4369, 61166, 65382],
  [15, 240, 4369, 26214, 65518],
  [15, 240, 4369, 65382, 65518],
  [15, 240, 4369, 65382, 65416],
  [15, 240, 4369, 43690, 65382],
  [15, 240, 4369, 26214, 65450],
  [15, 240, 4369, 52428, 65382],
  [15, 240, 4369, 26214, 65484],
  [15, 240, 4369, 65382, 65450],
  [15, 240, 4369, 65382, 65484],
  [15, 240, 4369, 63078, 65416],
  [15, 240, 4369, 63624, 65382],
  [15, 496, 4369, 34952, 63078],
  [15, 496, 4369, 26214, 63624],
  [15, 240, 4369, 34952, 63334],
  [15, 240, 4369, 26470, 63624],
  [15, 240, 4369, 35208, 63078],
  [15, 240, 4369, 26214, 63880],
  [15, 4336, 4369, 28518, 34952],
  [15, 240, 4369, 32614, 34952],
  [15, 240, 4369, 28518, 39048],
  [14, 240, 4369, 28518, 61440],
  [15, 240, 4369, 61422, 65382],
  [15, 240, 4369, 28518, 65518],
  [15, 240, 4369, 44970, 65382],
  [15, 240, 4369, 28518, 65450],
  [15, 240, 4369, 28518, 64716],
  [15, 240, 4369, 64716, 65382],
  [15, 240, 4369, 44970, 63078],
  [15, 240, 4369, 28518, 64170],
  [15, 240, 4369, 53196, 65382],
  [15, 240, 4369, 28518, 65484],
  [15, 240, 4369, 64170, 65382],
  [15, 240, 4369, 53196, 63078],
  [15, 4336, 4369, 26214, 36744],
  [15, 240, 4369, 30310, 36744],
  [15, 240, 4369, 26214, 40840],
  [15, 240, 4369, 61422, 63078],
  [15, 240, 4369, 63078, 65518],
  [15, 240, 4369, 63078, 65450],
  [15, 240, 4369, 63078, 65484],
  [15, 240, 4369, 65262, 65382],
  [14, 240, 3840, 4369, 63078],
  [15, 240, 4369, 28518, 65262]]

def row5 : List (List ℕ) := [
  [3840, 4383, 8738, 17476, 35064, 61440],
  [240, 4383, 12066, 17476, 34952, 61440],
  [240, 4383, 8738, 20292, 34952, 61440],
  [240, 4383, 8738, 17476, 36744, 61440],
  [240, 4383, 8738, 17476, 34952, 65280],
  [240, 3840, 4383, 26214, 34952, 61440],
  [240, 3840, 4383, 17476, 34952, 61986],
  [240, 3840, 4383, 8738, 34952, 62532],
  [240, 3840, 4383, 8738, 17476, 63624],
  [15, 4369, 8738, 17476, 35064, 65280],
  [15, 3840, 4369, 26214, 35064, 61440],
  [15, 240, 4369, 28518, 34952, 61440],
  [15, 240, 4369, 17476, 34952, 65314],
  [15, 240, 4369, 12066, 34952, 62532],
  [15, 240, 4369, 12066, 17476, 63624],
  [15, 240, 4369, 20292, 34952, 61986],
  [15, 240, 4369, 8738, 34952, 65348],
  [15, 240, 4369, 8738, 20292, 63624],
  [15, 240, 4369, 26214, 36744, 61440],
  [15, 240, 4369, 17476, 36744, 61986],
  [15, 240, 4369, 8738, 36744, 62532],
  [15, 240, 4369, 8738, 17476, 65416],
  [15, 240, 4369, 26214, 34952, 65280],
  [15, 240, 3840, 4369, 34952, 63078],
  [15, 240, 3840, 4369, 26214, 63624],
  [248, 3840, 4383, 8738, 17476, 61440],
  [240, 3848, 4383, 8738, 17476, 61440],
  [240, 3840, 4383, 8746, 17476, 61440],
  [240, 3840, 4383, 8738, 17484, 61440],
  [240, 3840, 4383, 8738, 17476, 61448],
  [8, 240, 4383, 12066, 17476, 61440],
  [8, 240, 4383, 8738, 20292, 61440],
  [8, 240, 4383, 8738, 17476, 65280],
  [8, 240, 3840, 4383, 26214, 61440],
  [8, 240, 3840, 4383, 17476, 61986],
  [8, 240, 3840, 4383, 8738, 62532],
  [4080, 4383, 8738, 17476, 35064, 61440],
  [4080, 4383, 8738, 17476, 34952, 61680],
  [240, 4383, 8738, 17476, 36856, 61440],
  [240, 4383, 8738, 17476, 34952, 65520],
  [240, 4080, 4383, 26214, 34952, 61440],
  [240, 4080, 4383, 17476, 34952, 61986],
  [240, 4080, 4383, 8738, 34952, 62532],
  [240, 4080, 4383, 8738, 17476, 63624],
  [256, 4383, 8738, 17476, 35064, 61440],
  [4383, 8738, 12066, 17476, 35064, 61440],
  [4383, 8738, 17476, 20292, 35064, 61440],
  [4383, 8738, 17476, 35064, 36856, 61440],
  [15, 4383, 8738, 17476, 35064, 65280],
  [3840, 4383, 8738, 17476, 35064, 65280],
  [4383, 8738, 17476, 35064, 61440, 65280],
  [3840, 4096, 4383, 8738, 17476, 35064],
  [15, 3840, 4383, 26214, 35064, 61440],
  [3840, 4383, 8738, 26214, 35064, 61440],
  [3840, 4383, 17476, 26214, 35064, 61440],
  [3840, 4383, 8738, 17476, 35064, 61986],
  [3840, 4383, 8738, 17476, 35064, 62532],
  [3840, 4383, 8738, 17476, 35064, 63736],
  [3840, 4383, 8738, 17476, 35064, 61680],
  [240, 4383, 12066, 17476, 35064, 61440],
  [240, 4383, 8738, 20292, 35064, 61440],
  [240, 4383, 8738, 17476, 35064, 65280],
  [240, 3840, 4383, 26214, 35064, 61440],
  [240, 3840, 4383, 17476, 35064, 61986],
  [240, 3840, 4383, 8738, 35064, 62532],
  [240, 3840, 4383, 8738, 17476, 63736],
  [4383, 8738, 17476, 35064, 36744, 61440],
  [4383, 8738, 17476, 34952, 35064, 65280],
  [3840, 4383, 26214, 34952, 35064, 61440],
  [3840, 4383, 8738, 17476, 35064, 63624],
  [240, 4383, 12066, 17476, 34952, 61680],
  [240, 4383, 8738, 20292, 34952, 61680],
  [240, 4383, 8738, 17476, 36744, 61680],
  [240, 3840, 4383, 26214, 34952, 61680],
  [496, 4383, 8738, 17476, 34952, 61440],
  [240, 4383, 8994, 17476, 34952, 61440],
  [240, 4383, 8738, 17732, 34952, 61440],
  [240, 4383, 8738, 17476, 35208, 61440],
  [240, 4383, 8738, 17476, 34952, 61696],
  [240, 256, 4383, 26214, 34952, 61440],
  [240, 256, 4383, 17476, 34952, 61986],
  [240, 256, 4383, 8738, 34952, 62532],
  [240, 256, 4383, 8738, 17476, 63624],
  [240, 4096, 4383, 12066, 17476, 34952],
  [15, 240, 4383, 28518, 34952, 61440],
  [240, 4383, 12066, 28518, 34952, 61440],
  [240, 4383, 17476, 28518, 34952, 61440],
  [240, 4383, 12066, 17476, 44970, 61440],
  [15, 240, 4383, 17476, 34952, 65314],
  [240, 4383, 12066, 17476, 34952, 65314],
  [240, 4383, 17476, 34952, 61440, 65314],
  [240, 4383, 12066, 17476, 52428, 61440],
  [15, 240, 4383, 12066, 34952, 62532],
  [240, 4383, 12066, 17476, 34952, 62532],
  [240, 4383, 12066, 34952, 61440, 62532],
  [15, 240, 4383, 12066, 17476, 63624],
  [240, 4383, 12066, 17476, 34952, 63624],
  [240, 4383, 12066, 17476, 61440, 63624],
  [240, 4383, 12066, 20292, 34952, 61440],
  [240, 4383, 12066, 17476, 36744, 61440],
  [240, 4383, 12066, 17476, 34952, 65280],
  [240, 3840, 4383, 28518, 34952, 61440],
  [240, 3840, 4383, 17476, 34952, 65314],
  [240, 3840, 4383, 12066, 34952, 62532],
  [240, 3840, 4383, 12066, 17476, 63624],
  [240, 4383, 12066, 26214, 34952, 61440],
  [240, 4383, 12066, 17476, 43690, 61440],
  [240, 4383, 12066, 17476, 34952, 61986],
  [240, 4383, 8738, 28518, 34952, 61440],
  [240, 4383, 8738, 17476, 44970, 61440],
  [240, 4383, 8738, 17476, 34952, 65314],
  [240, 4383, 8738, 12066, 34952, 62532],
  [240, 4383, 8738, 12066, 17476, 63624],
  [240, 4096, 4383, 8738, 20292, 34952],
  [240, 4383, 20292, 28518, 34952, 61440],
  [240, 4383, 8738, 20292, 43690, 61440],
  [15, 240, 4383, 20292, 34952, 61986],
  [240, 4383, 8738, 20292, 34952, 61986],
  [240, 4383, 20292, 34952, 61440, 61986],
  [240, 4383, 8738, 20292, 53196, 61440],
  [15, 240, 4383, 8738, 34952, 65348],
  [240, 4383, 8738, 20292, 34952, 65348],
  [240, 4383, 8738, 34952, 61440, 65348],
  [15, 240, 4383, 8738, 20292, 63624],
  [240, 4383, 8738, 20292, 34952, 63624],
  [240, 4383, 8738, 20292, 61440, 63624],
  [240, 4383, 8738, 20292, 36744, 61440],
  [240, 4383, 8738, 20292, 34952, 65280],
  [240, 3840, 4383, 20292, 34952, 61986],
  [240, 3840, 4383, 8738, 34952, 65348],
  [240, 3840, 4383, 8738, 20292, 63624],
  [240, 4383, 20292, 26214, 34952, 61440],
  [240, 4383, 17476, 20292, 34952, 61986],
  [240, 4383, 8738, 20292, 52428, 61440],
  [240, 4383, 8738, 20292, 34952, 62532],
  [240, 4383, 8738, 17476, 53196, 61440],
  [240, 4383, 8738, 17476, 34952, 65348],
  [240, 4383, 8738, 17476, 20292, 63624],
  [240, 264, 4383, 8738, 17476, 61440],
  [240, 4096, 4383, 8738, 17476, 36744],
  [15, 240, 4383, 26214, 36744, 61440],
  [240, 4383, 8738, 26214, 36744, 61440],
  [240, 4383, 17476, 26214, 36744, 61440],
  [15, 240, 4383, 17476, 36744, 61986],
  [240, 4383, 8738, 17476, 36744, 61986],
  [240, 4383, 17476, 36744, 61440, 61986],
  [15, 240, 4383, 8738, 36744, 62532],
  [240, 4383, 8738, 17476, 36744, 62532],
  [240, 4383, 8738, 36744, 61440, 62532],
  [15, 240, 4383, 8738, 17476, 65416],
  [240, 4383, 8738, 17476, 36744, 65416],
  [240, 4383, 8738, 17476, 61440, 65416],
  [240, 4383, 8738, 17476, 36744, 65280],
  [240, 3840, 4383, 26214, 36744, 61440],
  [240, 3840, 4383, 17476, 36744, 61986],
  [240, 3840, 4383, 8738, 36744, 62532],
  [240, 3840, 4383, 8738, 17476, 65416],
  [240, 4383, 26214, 34952, 36744, 61440],
  [240, 4383, 17476, 34952, 36744, 61986],
  [240, 4383, 8738, 34952, 36744, 62532],
  [240, 4383, 8738, 17476, 36744, 63624],
  [240, 4383, 8738, 17476, 34952, 65416],
  [240, 4352, 4383, 8738, 17476, 34952],
  [15, 240, 4383, 26214, 34952, 65280],
  [240, 4383, 8738, 26214, 34952, 65280],
  [240, 4383, 17476, 26214, 34952, 65280],
  [240, 4383, 8738, 17476, 43690, 65280],
  [240, 4383, 17476, 34952, 65280, 65314],
  [240, 4383, 8738, 17476, 52428, 65280],
  [240, 4383, 8738, 34952, 65280, 65348],
  [240, 4383, 8738, 17476, 65280, 65416],
  [240, 3840, 4383, 26214, 34952, 65280],
  [240, 4383, 26214, 34952, 61440, 65280],
  [240, 4383, 17476, 34952, 61986, 65280],
  [240, 4383, 8738, 34952, 62532, 65280],
  [240, 4383, 8738, 17476, 63624, 65280],
  [3840, 4336, 4383, 8738, 17476, 34952],
  [240, 4383, 7936, 8738, 17476, 34952],
  [240, 3840, 4383, 12834, 17476, 34952],
  [240, 3840, 4383, 8738, 21572, 34952],
  [240, 3840, 4383, 8738, 17476, 39048],
  [240, 3840, 4096, 4383, 26214, 34952],
  [240, 4383, 26214, 28518, 34952, 61440],
  [240, 3840, 4383, 26214, 61166, 61440],
  [15, 240, 3840, 4383, 34952, 63078],
  [240, 3840, 4383, 26214, 34952, 63078],
  [240, 3840, 4383, 34952, 61440, 63078],
  [15, 240, 3840, 4383, 26214, 63624],
  [240, 3840, 4383, 26214, 34952, 63624],
  [240, 3840, 4383, 26214, 61440, 63624],
  [240, 3840, 4383, 26214, 43690, 61440],
  [240, 3840, 4383, 26214, 34952, 61986],
  [240, 3840, 4383, 8738, 34952, 63078],
  [240, 3840, 4383, 8738, 26214, 63624],
  [240, 3840, 4383, 26214, 52428, 61440],
  [240, 3840, 4383, 26214, 34952, 62532],
  [240, 3840, 4383, 17476, 34952, 63078],
  [240, 3840, 4383, 17476, 26214, 63624],
  [240, 3840, 4383, 17476, 43690, 61986],
  [240, 3840, 4383, 8738, 43690, 62532],
  [240, 3840, 4383, 8738, 17476, 64170],
  [240, 4383, 17476, 34952, 61986, 65314],
  [240, 3840, 4383, 17476, 52428, 61986],
  [240, 3840, 4383, 34952, 61986, 63078],
  [240, 3840, 4383, 17476, 61986, 64170],
  [240, 3840, 4383, 34952, 61986, 62532],
  [240, 3840, 4383, 17476, 61986, 63624],
  [240, 3840, 4383, 8738, 52428, 62532],
  [240, 3840, 4383, 8738, 17476, 64716],
  [240, 4383, 8738, 34952, 62532, 65348],
  [240, 3840, 4383, 34952, 62532, 63078],
  [240, 3840, 4383, 8738, 62532, 64716],
  [240, 3840, 4383, 8738, 62532, 63624],
  [240, 4383, 8738, 17476, 63624, 65416],
  [240, 3840, 4104, 4383, 8738, 17476],
  [4369, 4383, 8738, 17476, 35064, 65280],
  [3840, 4369, 4383, 26214, 35064, 61440],
  [240, 4369, 4383, 28518, 34952, 61440],
  [240, 4369, 4383, 17476, 34952, 65314],
  [240, 4369, 4383, 12066, 34952, 62532],
  [240, 4369, 4383, 12066, 17476, 63624],
  [240, 4369, 4383, 20292, 34952, 61986],
  [240, 4369, 4383, 8738, 34952, 65348],
  [240, 4369, 4383, 8738, 20292, 63624],
  [240, 4369, 4383, 26214, 36744, 61440],
  [240, 4369, 4383, 17476, 36744, 61986],
  [240, 4369, 4383, 8738, 36744, 62532],
  [240, 4369, 4383, 8738, 17476, 65416],
  [240, 4369, 4383, 26214, 34952, 65280],
  [240, 3840, 4369, 4383, 34952, 63078],
  [240, 3840, 4369, 4383, 26214, 63624],
  [15, 248, 4369, 12066, 17476, 61440],
  [15, 248, 4369, 8738, 20292, 61440],
  [15, 248, 4369, 8738, 17476, 65280],
  [15, 248, 3840, 4369, 26214, 61440],
  [15, 248, 3840, 4369, 17476, 61986],
  [15, 248, 3840, 4369, 8738, 62532],
  [15, 240, 4369, 12074, 17476, 61440],
  [15, 240, 4369, 8738, 20300, 61440],
  [15, 240, 4369, 8738, 17476, 65288],
  [15, 240, 3848, 4369, 26214, 61440],
  [15, 240, 3848, 4369, 17476, 61986],
  [15, 240, 3848, 4369, 8738, 62532],
  [15, 240, 4369, 8746, 20292, 61440],
  [15, 240, 4369, 8746, 17476, 65280],
  [15, 240, 3840, 4369, 26222, 61440],
  [15, 240, 3840, 4369, 17476, 61994],
  [15, 240, 3840, 4369, 8746, 62532],
  [15, 240, 4369, 12066, 17484, 61440],
  [15, 240, 4369, 8738, 17484, 65280],
  [15, 240, 3840, 4369, 17484, 61986],
  [15, 240, 3840, 4369, 8738, 62540],
  [15, 240, 4369, 12066, 17476, 61448],
  [15, 240, 4369, 8738, 20292, 61448],
  [15, 240, 3840, 4369, 26214, 61448],
  [8, 15, 240, 4369, 28518, 61440],
  [8, 15, 240, 4369, 17476, 65314],
  [8, 15, 240, 4369, 12066, 62532],
  [8, 15, 240, 4369, 20292, 61986],
  [8, 15, 240, 4369, 8738, 65348],
  [8, 15, 240, 4369, 26214, 65280],
  [8, 15, 240, 3840, 4369, 63078],
  [15, 4369, 8738, 17476, 35064, 65520],
  [15, 4080, 4369, 26214, 35064, 61440],
  [15, 4080, 4369, 17476, 35064, 61986],
  [15, 4080, 4369, 8738, 35064, 62532],
  [15, 4080, 4369, 8738, 17476, 63736],
  [15, 4369, 8738, 17476, 36856, 61680],
  [15, 4080, 4369, 26214, 34952, 61680],
  [15, 240, 4369, 26214, 36856, 61440],
  [15, 240, 4369, 17476, 36856, 61986],
  [15, 240, 4369, 8738, 36856, 62532],
  [15, 240, 4369, 8738, 17476, 65528],
  [15, 240, 4368, 8738, 17476, 34952],
  [15, 240, 4369, 26214, 34952, 65520],
  [15, 240, 4080, 4369, 34952, 63078],
  [15, 240, 4080, 4369, 26214, 63624],
  [15, 4369, 12066, 17476, 35064, 61680],
  [15, 4369, 8738, 20292, 35064, 61680],
  [15, 3840, 4369, 26214, 35064, 61680],
  [15, 240, 4369, 28518, 34952, 61680],
  [15, 240, 4369, 12066, 17476, 63736],
  [15, 240, 4369, 8738, 20292, 63736],
  [15, 240, 4369, 26214, 36744, 61680],
  [15, 240, 3840, 4369, 26214, 63736],
  [15, 4369, 8994, 17476, 35064, 61440],
  [15, 4369, 8738, 17732, 35064, 61440],
  [15, 4369, 8738, 17476, 35320, 61440],
  [15, 4369, 8738, 17476, 35064, 61696],
  [15, 256, 4369, 26214, 35064, 61440],
  [15, 240, 4369, 28518, 35064, 61440],
  [15, 240, 4369, 17476, 35064, 65314],
  [15, 240, 4369, 12066, 35064, 62532],
  [15, 4369, 12066, 26214, 35064, 61440],
  [15, 4369, 12066, 17476, 35064, 61986],
  [15, 4369, 8738, 17476, 35064, 65314],
  [15, 240, 4369, 20292, 35064, 61986],
  [15, 240, 4369, 8738, 35064, 65348],
  [15, 4369, 20292, 26214, 35064, 61440],
  [15, 4369, 8738, 20292, 35064, 62532],
  [15, 4369, 8738, 17476, 35064, 65348],
  [15, 4369, 26214, 35064, 36856, 61440],
  [15, 4369, 8738, 17476, 36856, 63736],
  [15, 4369, 8738, 17476, 35064, 65528],
  [15, 4352, 4369, 8738, 17476, 35064],
  [15, 240, 4369, 26214, 35064, 65280],
  [15, 4369, 8738, 26214, 35064, 65280],
  [15, 4369, 17476, 26214, 35064, 65280],
  [15, 3840, 4369, 26214, 35064, 65280],
  [15, 4369, 26214, 35064, 61440, 65280],
  [15, 4369, 7936, 8738, 17476, 35064],
  [15, 3840, 4369, 12834, 17476, 35064],
  [15, 3840, 4369, 8738, 21572, 35064],
  [15, 3840, 4369, 8738, 17476, 39160],
  [15, 3840, 4096, 4369, 26214, 35064],
  [15, 4369, 26214, 28518, 35064, 61440],
  [15, 240, 3840, 4369, 35064, 63078],
  [15, 3840, 4369, 26214, 35064, 63078],
  [15, 3840, 4369, 26214, 35064, 63736],
  [15, 3840, 4369, 26214, 35064, 61986],
  [15, 3840, 4369, 26214, 35064, 62532],
  [15, 4369, 26214, 35064, 36744, 61440],
  [15, 4369, 8738, 17476, 35064, 65416],
  [15, 4369, 26214, 34952, 35064, 65280],
  [15, 3840, 4369, 26214, 35064, 63624],
  [15, 240, 4369, 28518, 34952, 65280],
  [15, 240, 4369, 12066, 34952, 65348],
  [15, 240, 4369, 12066, 17476, 65416],
  [15, 240, 4369, 20292, 34952, 65314],
  [15, 240, 4369, 8738, 20292, 65416],
  [15, 240, 4369, 26214, 36744, 65280],
  [15, 240, 4369, 17476, 36744, 65314],
  [15, 240, 4369, 8738, 36744, 65348],
  [15, 4369, 4592, 8738, 17476, 34952],
  [15, 240, 4369, 13090, 17476, 34952],
  [15, 240, 4369, 8738, 21828, 34952],
  [15, 240, 4369, 8738, 17476, 39304],
  [15, 240, 4352, 4369, 26214, 34952],
  [15, 240, 4369, 26214, 61166, 65280],
  [15, 240, 3840, 4369, 34952, 65382],
  [15, 240, 4369, 26214, 34952, 65382],
  [15, 240, 4369, 34952, 65280, 65382],
  [15, 240, 3840, 4369, 26214, 65416],
  [15, 240, 4369, 26214, 34952, 65416],
  [15, 240, 4369, 26214, 65280, 65416],
  [15, 240, 4369, 26214, 43690, 65280],
  [15, 240, 4369, 26214, 34952, 65314],
  [15, 240, 4369, 8738, 34952, 65382],
  [15, 240, 4369, 8738, 26214, 65416],
  [15, 240, 4369, 26214, 52428, 65280],
  [15, 240, 4369, 26214, 34952, 65348],
  [15, 240, 4369, 17476, 34952, 65382],
  [15, 240, 4369, 17476, 26214, 65416],
  [15, 240, 4369, 17476, 43690, 65314],
  [15, 240, 4369, 8738, 43690, 65348],
  [15, 240, 4369, 8738, 17476, 65450],
  [15, 240, 4369, 17476, 52428, 65314],
  [15, 240, 4369, 34952, 65314, 65382],
  [15, 240, 4369, 17476, 65314, 65450],
  [15, 240, 4369, 34952, 65314, 65348],
  [15, 240, 4369, 17476, 65314, 65416],
  [15, 240, 4369, 8738, 52428, 65348],
  [15, 240, 4369, 8738, 17476, 65484],
  [15, 240, 4369, 34952, 65348, 65382],
  [15, 240, 4369, 8738, 65348, 65484],
  [15, 240, 4369, 8738, 65348, 65416],
  [15, 240, 4369, 34952, 63078, 65280],
  [15, 240, 4369, 34952, 61440, 65382],
  [15, 240, 4369, 26214, 63624, 65280],
  [15, 240, 4369, 26214, 61440, 65416],
  [15, 240, 4369, 34952, 61986, 65348],
  [15, 240, 4369, 17476, 61986, 65416],
  [15, 240, 4369, 34952, 62532, 65314],
  [15, 240, 4369, 17476, 63624, 65314],
  [15, 240, 4369, 8738, 62532, 65416],
  [15, 240, 4369, 8738, 63624, 65348],
  [15, 496, 4369, 26214, 34952, 61440],
  [15, 496, 4369, 17476, 34952, 61986],
  [15, 496, 4369, 8738, 34952, 62532],
  [15, 496, 4369, 8738, 17476, 63624],
  [15, 240, 4369, 26470, 34952, 61440],
  [15, 240, 4369, 17476, 34952, 62242],
  [15, 240, 4369, 8994, 34952, 62532],
  [15, 240, 4369, 8994, 17476, 63624],
  [15, 240, 4369, 17732, 34952, 61986],
  [15, 240, 4369, 8738, 34952, 62788],
  [15, 240, 4369, 8738, 17732, 63624],
  [15, 240, 4369, 26214, 35208, 61440],
  [15, 240, 4369, 17476, 35208, 61986],
  [15, 240, 4369, 8738, 35208, 62532],
  [15, 240, 4369, 8738, 17476, 63880],
  [15, 240, 4369, 26214, 34952, 61696],
  [15, 240, 256, 4369, 34952, 63078],
  [15, 240, 256, 4369, 26214, 63624],
  [15, 240, 4369, 12066, 20292, 63624],
  [15, 240, 4369, 28518, 36744, 61440],
  [15, 240, 4369, 12066, 36744, 62532],
  [15, 4336, 4369, 12066, 17476, 34952],
  [15, 240, 4369, 16162, 17476, 34952],
  [15, 240, 4369, 12066, 21572, 34952],
  [15, 240, 4369, 12066, 17476, 39048],
  [15, 240, 4096, 4369, 28518, 34952],
  [15, 240, 4369, 28518, 61422, 61440],
  [15, 240, 4369, 28518, 34952, 65382],
  [15, 240, 3840, 4369, 28518, 63624],
  [15, 240, 4369, 28518, 34952, 63624],
  [15, 240, 4369, 28518, 61440, 63624],
  [15, 240, 4369, 28518, 44970, 61440],
  [15, 240, 4369, 28518, 34952, 65314],
  [15, 240, 4369, 12066, 34952, 65382],
  [15, 240, 4369, 12066, 28518, 63624],
  [15, 240, 4369, 28518, 52428, 61440],
  [15, 240, 4369, 28518, 34952, 62532],
  [15, 240, 4369, 17476, 28518, 63624],
  [15, 240, 4369, 17476, 44970, 65314],
  [15, 240, 4369, 12066, 44970, 62532],
  [15, 240, 4369, 12066, 17476, 65450],
  [15, 240, 4369, 12066, 52428, 62532],
  [15, 240, 4369, 12066, 17476, 64716],
  [15, 240, 4369, 34952, 62532, 65382],
  [15, 240, 4369, 12066, 62532, 64716],
  [15, 240, 4369, 12066, 62532, 63624],
  [15, 240, 4369, 26214, 44970, 61440],
  [15, 240, 4369, 12066, 34952, 63078],
  [15, 240, 4369, 12066, 26214, 63624],
  [15, 240, 4369, 28518, 43690, 61440],
  [15, 240, 4369, 12066, 43690, 62532],
  [15, 240, 4369, 12066, 17476, 64170],
  [15, 240, 4369, 28518, 34952, 61986],
  [15, 240, 4369, 17476, 44970, 61986],
  [15, 240, 4369, 8738, 28518, 63624],
  [15, 240, 4369, 8738, 44970, 62532],
  [15, 240, 4369, 20292, 36744, 61986],
  [15, 4336, 4369, 8738, 20292, 34952],
  [15, 240, 4369, 12834, 20292, 34952],
  [15, 240, 4369, 8738, 24388, 34952],
  [15, 240, 4369, 8738, 20292, 39048],
  [15, 240, 4369, 28518, 53196, 61440],
  [15, 240, 4369, 28518, 34952, 65348],
  [15, 240, 4369, 20292, 34952, 65382],
  [15, 240, 4369, 20292, 28518, 63624],
  [15, 240, 4369, 20292, 43690, 61986],
  [15, 240, 4369, 8738, 20292, 64170],
  [15, 240, 4369, 20292, 53196, 61986],
  [15, 240, 4369, 34952, 61986, 65382],
  [15, 240, 4369, 20292, 61986, 64170],
  [15, 240, 4369, 20292, 61986, 63624],
  [15, 240, 4369, 8738, 53196, 65348],
  [15, 240, 4369, 8738, 20292, 65484],
  [15, 240, 4369, 26214, 53196, 61440],
  [15, 240, 4369, 20292, 34952, 63078],
  [15, 240, 4369, 20292, 26214, 63624],
  [15, 240, 4369, 20292, 52428, 61986],
  [15, 240, 4369, 17476, 53196, 61986],
  [15, 240, 4369, 8738, 20292, 64716],
  [15, 240, 4369, 8738, 53196, 62532],
  [15, 4336, 4369, 8738, 17476, 36744],
  [15, 240, 4369, 12834, 17476, 36744],
  [15, 240, 4369, 8738, 21572, 36744],
  [15, 240, 4369, 8738, 17476, 40840],
  [15, 240, 4096, 4369, 26214, 36744],
  [15, 240, 4369, 26214, 61422, 61440],
  [15, 240, 3840, 4369, 36744, 63078],
  [15, 240, 4369, 26214, 36744, 63078],
  [15, 240, 4369, 36744, 61440, 63078],
  [15, 240, 4369, 26214, 36744, 65416],
  [15, 240, 4369, 26214, 36744, 61986],
  [15, 240, 4369, 8738, 36744, 63078],
  [15, 240, 4369, 26214, 36744, 62532],
  [15, 240, 4369, 17476, 36744, 63078],
  [15, 240, 4369, 36744, 61986, 63078],
  [15, 240, 4369, 17476, 61986, 65450],
  [15, 240, 4369, 36744, 61986, 62532],
  [15, 240, 4369, 36744, 62532, 63078],
  [15, 240, 4369, 8738, 62532, 65484],
  [15, 240, 4369, 34952, 36744, 63078],
  [15, 240, 4369, 26214, 36744, 63624],
  [15, 3840, 4336, 4369, 26214, 34952],
  [15, 240, 4369, 7936, 26214, 34952],
  [15, 240, 3840, 4369, 30310, 34952],
  [15, 240, 3840, 4369, 26214, 39048],
  [15, 240, 4369, 34952, 63078, 65314],
  [15, 240, 4369, 17476, 64170, 65314],
  [15, 240, 3840, 4369, 52428, 63078],
  [15, 240, 4369, 34952, 63078, 65382],
  [15, 240, 3840, 4369, 63078, 65262],
  [15, 240, 3840, 4369, 63078, 63624],
  [15, 240, 3840, 4369, 63078, 64170],
  [15, 240, 3840, 4369, 26214, 64170],
  [15, 240, 3840, 4369, 43690, 63078],
  [15, 240, 4369, 34952, 63078, 65348],
  [15, 240, 4369, 8738, 64716, 65348],
  [15, 240, 3840, 4369, 63078, 64716],
  [15, 240, 3840, 4369, 26214, 64716],
  [15, 240, 4369, 26214, 63624, 65416],
  [15, 240, 4369, 26214, 28518, 63624],
  [15, 240, 3840, 4369, 26214, 65262],
  [15, 240, 4369, 28518, 61166, 61440],
  [15, 240, 4369, 28518, 34952, 63078],
  [14, 240, 3840, 4369, 26214, 61440],
  [15, 240, 3840, 4369, 61166, 63078]]

def row6 : List (List ℕ) := [
  [240, 3840, 4383, 8738, 17476, 34952, 61440],
  [15, 3840, 4369, 8738, 17476, 35064, 61440],
  [15, 240, 4369, 12066, 17476, 34952, 61440],
  [15, 240, 4369, 8738, 20292, 34952, 61440],
  [15, 240, 4369, 8738, 17476, 36744, 61440],
  [15, 240, 4369, 8738, 17476, 34952, 65280],
  [15, 240, 3840, 4369, 26214, 34952, 61440],
  [15, 240, 3840, 4369, 17476, 34952, 61986],
  [15, 240, 3840, 4369, 8738, 34952, 62532],
  [15, 240, 3840, 4369, 8738, 17476, 63624],
  [8, 240, 3840, 4383, 8738, 17476, 61440],
  [240, 4080, 4383, 8738, 17476, 34952, 61440],
  [15, 3840, 4383, 8738, 17476, 35064, 61440],
  [240, 3840, 4383, 8738, 17476, 35064, 61440],
  [3840, 4383, 8738, 17476, 34952, 35064, 61440],
  [240, 3840, 4383, 8738, 17476, 34952, 61680],
  [240, 256, 4383, 8738, 17476, 34952, 61440],
  [15, 240, 4383, 12066, 17476, 34952, 61440],
  [240, 3840, 4383, 12066, 17476, 34952, 61440],
  [240, 4383, 8738, 12066, 17476, 34952, 61440],
  [15, 240, 4383, 8738, 20292, 34952, 61440],
  [240, 3840, 4383, 8738, 20292, 34952, 61440],
  [240, 4383, 8738, 17476, 20292, 34952, 61440],
  [15, 240, 4383, 8738, 17476, 36744, 61440],
  [240, 3840, 4383, 8738, 17476, 36744, 61440],
  [240, 4383, 8738, 17476, 34952, 36744, 61440],
  [15, 240, 4383, 8738, 17476, 34952, 65280],
  [240, 3840, 4383, 8738, 17476, 34952, 65280],
  [240, 4383, 8738, 17476, 34952, 61440, 65280],
  [240, 3840, 4096, 4383, 8738, 17476, 34952],
  [15, 240, 3840, 4383, 26214, 34952, 61440],
  [240, 3840, 4383, 8738, 26214, 34952, 61440],
  [240, 3840, 4383, 17476, 26214, 34952, 61440],
  [240, 3840, 4383, 8738, 17476, 43690, 61440],
  [15, 240, 3840, 4383, 17476, 34952, 61986],
  [240, 3840, 4383, 8738, 17476, 34952, 61986],
  [240, 3840, 4383, 17476, 34952, 61440, 61986],
  [240, 3840, 4383, 8738, 17476, 52428, 61440],
  [15, 240, 3840, 4383, 8738, 34952, 62532],
  [240, 3840, 4383, 8738, 17476, 34952, 62532],
  [240, 3840, 4383, 8738, 34952, 61440, 62532],
  [15, 240, 3840, 4383, 8738, 17476, 63624],
  [240, 3840, 4383, 8738, 17476, 34952, 63624],
  [240, 3840, 4383, 8738, 17476, 61440, 63624],
  [3840, 4369, 4383, 8738, 17476, 35064, 61440],
  [240, 4369, 4383, 12066, 17476, 34952, 61440],
  [240, 4369, 4383, 8738, 20292, 34952, 61440],
  [240, 4369, 4383, 8738, 17476, 36744, 61440],
  [240, 4369, 4383, 8738, 17476, 34952, 65280],
  [240, 3840, 4369, 4383, 26214, 34952, 61440],
  [240, 3840, 4369, 4383, 17476, 34952, 61986],
  [240, 3840, 4369, 4383, 8738, 34952, 62532],
  [240, 3840, 4369, 4383, 8738, 17476, 63624],
  [15, 248, 3840, 4369, 8738, 17476, 61440],
  [15, 240, 3848, 4369, 8738, 17476, 61440],
  [15, 240, 3840, 4369, 8746, 17476, 61440],
  [15, 240, 3840, 4369, 8738, 17484, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 61448],
  [8, 15, 240, 4369, 12066, 17476, 61440],
  [8, 15, 240, 4369, 8738, 20292, 61440],
  [8, 15, 240, 4369, 8738, 17476, 65280],
  [8, 15, 240, 3840, 4369, 26214, 61440],
  [8, 15, 240, 3840, 4369, 17476, 61986],
  [8, 15, 240, 3840, 4369, 8738, 62532],
  [15, 4080, 4369, 8738, 17476, 35064, 61440],
  [15, 4080, 4369, 8738, 17476, 34952, 61680],
  [15, 240, 4369, 8738, 17476, 36856, 61440],
  [15, 240, 4369, 8738, 17476, 34952, 65520],
  [15, 240, 4080, 4369, 26214, 34952, 61440],
  [15, 240, 4080, 4369, 17476, 34952, 61986],
  [15, 240, 4080, 4369, 8738, 34952, 62532],
  [15, 240, 4080, 4369, 8738, 17476, 63624],
  [15, 3840, 4369, 8738, 17476, 35064, 61680],
  [15, 240, 4369, 12066, 17476, 34952, 61680],
  [15, 240, 4369, 8738, 20292, 34952, 61680],
  [15, 240, 4369, 8738, 17476, 36744, 61680],
  [15, 240, 3840, 4369, 26214, 34952, 61680],
  [15, 240, 3840, 4369, 8738, 17476, 63736],
  [15, 256, 4369, 8738, 17476, 35064, 61440],
  [15, 240, 4369, 12066, 17476, 35064, 61440],
  [15, 4369, 8738, 12066, 17476, 35064, 61440],
  [15, 240, 4369, 8738, 20292, 35064, 61440],
  [15, 4369, 8738, 17476, 20292, 35064, 61440],
  [15, 4369, 8738, 17476, 35064, 36856, 61440],
  [15, 240, 4369, 8738, 17476, 35064, 65280],
  [15, 3840, 4369, 8738, 17476, 35064, 65280],
  [15, 4369, 8738, 17476, 35064, 61440, 65280],
  [15, 3840, 4096, 4369, 8738, 17476, 35064],
  [15, 240, 3840, 4369, 26214, 35064, 61440],
  [15, 3840, 4369, 8738, 26214, 35064, 61440],
  [15, 3840, 4369, 17476, 26214, 35064, 61440],
  [15, 240, 3840, 4369, 17476, 35064, 61986],
  [15, 3840, 4369, 8738, 17476, 35064, 61986],
  [15, 240, 3840, 4369, 8738, 35064, 62532],
  [15, 3840, 4369, 8738, 17476, 35064, 62532],
  [15, 3840, 4369, 8738, 17476, 35064, 63736],
  [15, 4369, 8738, 17476, 35064, 36744, 61440],
  [15, 4369, 8738, 17476, 34952, 35064, 65280],
  [15, 3840, 4369, 26214, 34952, 35064, 61440],
  [15, 3840, 4369, 8738, 17476, 35064, 63624],
  [15, 240, 4369, 12066, 17476, 34952, 65280],
  [15, 240, 4369, 8738, 20292, 34952, 65280],
  [15, 240, 4369, 8738, 17476, 36744, 65280],
  [15, 240, 4352, 4369, 8738, 17476, 34952],
  [15, 240, 3840, 4369, 26214, 34952, 65280],
  [15, 240, 4369, 8738, 26214, 34952, 65280],
  [15, 240, 4369, 17476, 26214, 34952, 65280],
  [15, 240, 4369, 8738, 17476, 43690, 65280],
  [15, 240, 3840, 4369, 17476, 34952, 65314],
  [15, 240, 4369, 8738, 17476, 34952, 65314],
  [15, 240, 4369, 17476, 34952, 65280, 65314],
  [15, 240, 4369, 8738, 17476, 52428, 65280],
  [15, 240, 3840, 4369, 8738, 34952, 65348],
  [15, 240, 4369, 8738, 17476, 34952, 65348],
  [15, 240, 4369, 8738, 34952, 65280, 65348],
  [15, 240, 3840, 4369, 8738, 17476, 65416],
  [15, 240, 4369, 8738, 17476, 34952, 65416],
  [15, 240, 4369, 8738, 17476, 65280, 65416],
  [15, 240, 4369, 26214, 34952, 61440, 65280],
  [15, 240, 4369, 17476, 34952, 61986, 65280],
  [15, 240, 4369, 17476, 34952, 61440, 65314],
  [15, 240, 4369, 8738, 34952, 62532, 65280],
  [15, 240, 4369, 8738, 34952, 61440, 65348],
  [15, 240, 4369, 8738, 17476, 63624, 65280],
  [15, 240, 4369, 8738, 17476, 61440, 65416],
  [15, 496, 4369, 8738, 17476, 34952, 61440],
  [15, 240, 4369, 8994, 17476, 34952, 61440],
  [15, 240, 4369, 8738, 17732, 34952, 61440],
  [15, 240, 4369, 8738, 17476, 35208, 61440],
  [15, 240, 4369, 8738, 17476, 34952, 61696],
  [15, 240, 256, 4369, 26214, 34952, 61440],
  [15, 240, 256, 4369, 17476, 34952, 61986],
  [15, 240, 256, 4369, 8738, 34952, 62532],
  [15, 240, 256, 4369, 8738, 17476, 63624],
  [15, 240, 4369, 12066, 20292, 34952, 61440],
  [15, 240, 4369, 12066, 17476, 36744, 61440],
  [15, 240, 4096, 4369, 12066, 17476, 34952],
  [15, 240, 3840, 4369, 28518, 34952, 61440],
  [15, 240, 4369, 12066, 28518, 34952, 61440],
  [15, 240, 4369, 17476, 28518, 34952, 61440],
  [15, 240, 4369, 12066, 17476, 44970, 61440],
  [15, 240, 4369, 12066, 17476, 34952, 65314],
  [15, 240, 4369, 12066, 17476, 52428, 61440],
  [15, 240, 3840, 4369, 12066, 34952, 62532],
  [15, 240, 4369, 12066, 17476, 34952, 62532],
  [15, 240, 4369, 12066, 34952, 61440, 62532],
  [15, 240, 3840, 4369, 12066, 17476, 63624],
  [15, 240, 4369, 12066, 17476, 34952, 63624],
  [15, 240, 4369, 12066, 17476, 61440, 63624],
  [15, 240, 4369, 12066, 26214, 34952, 61440],
  [15, 240, 4369, 12066, 17476, 43690, 61440],
  [15, 240, 4369, 12066, 17476, 34952, 61986],
  [15, 240, 4369, 8738, 28518, 34952, 61440],
  [15, 240, 4369, 8738, 17476, 44970, 61440],
  [15, 240, 4369, 8738, 12066, 34952, 62532],
  [15, 240, 4369, 8738, 12066, 17476, 63624],
  [15, 240, 4369, 8738, 20292, 36744, 61440],
  [15, 240, 4096, 4369, 8738, 20292, 34952],
  [15, 240, 4369, 20292, 28518, 34952, 61440],
  [15, 240, 4369, 8738, 20292, 43690, 61440],
  [15, 240, 3840, 4369, 20292, 34952, 61986],
  [15, 240, 4369, 8738, 20292, 34952, 61986],
  [15, 240, 4369, 20292, 34952, 61440, 61986],
  [15, 240, 4369, 8738, 20292, 53196, 61440],
  [15, 240, 4369, 8738, 20292, 34952, 65348],
  [15, 240, 3840, 4369, 8738, 20292, 63624],
  [15, 240, 4369, 8738, 20292, 34952, 63624],
  [15, 240, 4369, 8738, 20292, 61440, 63624],
  [15, 240, 4369, 20292, 26214, 34952, 61440],
  [15, 240, 4369, 17476, 20292, 34952, 61986],
  [15, 240, 4369, 8738, 20292, 52428, 61440],
  [15, 240, 4369, 8738, 20292, 34952, 62532],
  [15, 240, 4369, 8738, 17476, 53196, 61440],
  [15, 240, 4369, 8738, 17476, 20292, 63624],
  [15, 240, 4096, 4369, 8738, 17476, 36744],
  [15, 240, 3840, 4369, 26214, 36744, 61440],
  [15, 240, 4369, 8738, 26214, 36744, 61440],
  [15, 240, 4369, 17476, 26214, 36744, 61440],
  [15, 240, 3840, 4369, 17476, 36744, 61986],
  [15, 240, 4369, 8738, 17476, 36744, 61986],
  [15, 240, 4369, 17476, 36744, 61440, 61986],
  [15, 240, 3840, 4369, 8738, 36744, 62532],
  [15, 240, 4369, 8738, 17476, 36744, 62532],
  [15, 240, 4369, 8738, 36744, 61440, 62532],
  [15, 240, 4369, 8738, 17476, 36744, 65416],
  [15, 240, 4369, 26214, 34952, 36744, 61440],
  [15, 240, 4369, 17476, 34952, 36744, 61986],
  [15, 240, 4369, 8738, 34952, 36744, 62532],
  [15, 240, 4369, 8738, 17476, 36744, 63624],
  [15, 3840, 4336, 4369, 8738, 17476, 34952],
  [15, 240, 4369, 7936, 8738, 17476, 34952],
  [15, 240, 3840, 4369, 12834, 17476, 34952],
  [15, 240, 3840, 4369, 8738, 21572, 34952],
  [15, 240, 3840, 4369, 8738, 17476, 39048],
  [15, 240, 3840, 4096, 4369, 26214, 34952],
  [15, 240, 4369, 17476, 34952, 61986, 65314],
  [15, 240, 3840, 4369, 17476, 52428, 61986],
  [15, 240, 3840, 4369, 34952, 61986, 62532],
  [15, 240, 3840, 4369, 17476, 34952, 63078],
  [15, 240, 3840, 4369, 34952, 61440, 63078],
  [15, 240, 3840, 4369, 34952, 61986, 63078],
  [15, 240, 3840, 4369, 17476, 61986, 63624],
  [15, 240, 3840, 4369, 17476, 61986, 64170],
  [15, 240, 3840, 4369, 26214, 34952, 61986],
  [15, 240, 3840, 4369, 17476, 43690, 61986],
  [15, 240, 3840, 4369, 8738, 34952, 63078],
  [15, 240, 3840, 4369, 8738, 17476, 64170],
  [15, 240, 4369, 8738, 34952, 62532, 65348],
  [15, 240, 3840, 4369, 8738, 43690, 62532],
  [15, 240, 3840, 4369, 34952, 62532, 63078],
  [15, 240, 3840, 4369, 8738, 62532, 63624],
  [15, 240, 3840, 4369, 8738, 62532, 64716],
  [15, 240, 3840, 4369, 26214, 34952, 62532],
  [15, 240, 3840, 4369, 8738, 52428, 62532],
  [15, 240, 3840, 4369, 8738, 17476, 64716],
  [15, 240, 4369, 8738, 17476, 63624, 65416],
  [15, 240, 3840, 4369, 8738, 26214, 63624],
  [15, 240, 3840, 4369, 17476, 26214, 63624],
  [15, 240, 3840, 4369, 26214, 61440, 63624],
  [15, 240, 3840, 4369, 26214, 34952, 63624],
  [15, 240, 4369, 26214, 28518, 34952, 61440],
  [15, 240, 3840, 4369, 26214, 43690, 61440],
  [15, 240, 3840, 4369, 26214, 61166, 61440],
  [15, 240, 3840, 4369, 26214, 34952, 63078],
  [15, 240, 3840, 4369, 26214, 52428, 61440]]

def row7 : List (List ℕ) := [
  [15, 240, 3840, 4369, 8738, 17476, 34952, 61440],
  [15, 240, 3840, 4383, 8738, 17476, 34952, 61440],
  [240, 3840, 4369, 4383, 8738, 17476, 34952, 61440],
  [8, 15, 240, 3840, 4369, 8738, 17476, 61440],
  [15, 240, 4080, 4369, 8738, 17476, 34952, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 34952, 61680],
  [15, 240, 3840, 4369, 8738, 17476, 35064, 61440],
  [15, 3840, 4369, 8738, 17476, 34952, 35064, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 34952, 65280],
  [15, 240, 4369, 8738, 17476, 34952, 61440, 65280],
  [15, 240, 256, 4369, 8738, 17476, 34952, 61440],
  [15, 240, 3840, 4369, 12066, 17476, 34952, 61440],
  [15, 240, 4369, 8738, 12066, 17476, 34952, 61440],
  [15, 240, 3840, 4369, 8738, 20292, 34952, 61440],
  [15, 240, 4369, 8738, 17476, 20292, 34952, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 36744, 61440],
  [15, 240, 4369, 8738, 17476, 34952, 36744, 61440],
  [15, 240, 3840, 4096, 4369, 8738, 17476, 34952],
  [15, 240, 3840, 4369, 17476, 34952, 61440, 61986],
  [15, 240, 3840, 4369, 8738, 17476, 34952, 61986],
  [15, 240, 3840, 4369, 8738, 34952, 61440, 62532],
  [15, 240, 3840, 4369, 8738, 17476, 34952, 62532],
  [15, 240, 3840, 4369, 8738, 17476, 61440, 63624],
  [15, 240, 3840, 4369, 8738, 17476, 34952, 63624],
  [15, 240, 3840, 4369, 8738, 26214, 34952, 61440],
  [15, 240, 3840, 4369, 17476, 26214, 34952, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 43690, 61440],
  [15, 240, 3840, 4369, 8738, 17476, 52428, 61440]]

def row8 : List (List ℕ) := [
  [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]]

def pairs2 : List (List ℕ × List (List ℕ)) := [
  ([248, 4383, 65382], []),
  ([240, 4383, 65390], []),
  ([4383, 30566, 35064], []),
  ([4383, 26214, 39416], []),
  ([4344, 4383, 28518], []),
  ([240, 4383, 32622], []),
  ([504, 4383, 63078], []),
  ([240, 4383, 63342], []),
  ([4383, 4600, 26214], []),
  ([240, 4383, 30574], [])]

theorem pairs2_fst : pairs2.map Prod.fst = row2 := rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk2 : pairs2.all (fun p => verifyFast 4478 negs 1 p.1 p.2 row1) = true := by
  decide +kernel

def pairs3_0 : List (List ℕ × List (List ℕ)) := [
  ([4383, 26214, 35064, 65280], []),
  ([240, 4383, 34952, 65382], []),
  ([240, 4383, 28518, 63624], []),
  ([240, 4383, 36744, 63078], []),
  ([240, 4383, 26214, 65416], []),
  ([248, 4383, 28518, 61440], [[248, 4383, 65382]]),
  ([248, 4383, 17476, 65314], [[248, 4383, 65382]]),
  ([248, 4383, 12066, 62532], [[248, 4383, 65382]]),
  ([248, 4383, 20292, 61986], [[248, 4383, 65382]]),
  ([248, 4383, 8738, 65348], [[248, 4383, 65382]]),
  ([248, 4383, 26214, 65280], [[248, 4383, 65382]]),
  ([248, 3840, 4383, 63078], [[248, 4383, 65382]]),
  ([240, 4383, 28526, 61440], [[240, 4383, 65390]]),
  ([240, 4383, 17476, 65322], [[240, 4383, 65390]]),
  ([240, 4383, 12074, 62532], [[240, 4383, 65390]]),
  ([240, 4383, 20300, 61986], [[240, 4383, 65390]]),
  ([240, 4383, 8738, 65356], [[240, 4383, 65390]]),
  ([240, 4383, 26214, 65288], [[240, 4383, 65390]]),
  ([240, 3848, 4383, 63078], [[240, 4383, 65390]]),
  ([240, 4383, 20292, 61994], [[240, 4383, 65390]]),
  ([240, 4383, 8746, 65348], [[240, 4383, 65390]]),
  ([240, 4383, 26222, 65280], [[240, 4383, 65390]]),
  ([240, 3840, 4383, 63086], [[240, 4383, 65390]]),
  ([240, 4383, 17484, 65314], [[240, 4383, 65390]]),
  ([240, 4383, 12066, 62540], [[240, 4383, 65390]]),
  ([240, 4383, 28518, 61448], [[240, 4383, 65390]]),
  ([8, 240, 4383, 65382], [[248, 4383, 65382], [240, 4383, 65390]]),
  ([4383, 26214, 35064, 65520], []),
  ([4080, 4383, 35064, 63078], []),
  ([4080, 4383, 26214, 63736], []),
  ([4383, 26214, 36856, 61680], []),
  ([240, 4383, 36856, 63078], []),
  ([240, 4383, 26214, 65528], []),
  ([4383, 26470, 35064, 61440], []),
  ([4383, 26214, 35320, 61440], []),
  ([4383, 26214, 35064, 61696], []),
  ([4383, 26214, 35064, 65314], []),
  ([4383, 26214, 35064, 65348], []),
  ([4383, 26214, 36856, 63736], []),
  ([4383, 26214, 35064, 65528], []),
  ([4383, 13090, 17476, 35064], [[4383, 30566, 35064]]),
  ([4383, 8738, 21828, 35064], [[4383, 30566, 35064]]),
  ([4383, 8738, 17476, 39416], [[4383, 26214, 39416]]),
  ([4352, 4383, 26214, 35064], [[4383, 30566, 35064], [4383, 26214, 39416]]),
  ([4383, 26214, 35064, 65382], []),
  ([4383, 7936, 26214, 35064], []),
  ([3840, 4383, 30310, 35064], []),
  ([3840, 4383, 26214, 39160], []),
  ([4383, 28518, 35064, 63078], []),
  ([4383, 28518, 35064, 61680], [])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk3_0 : pairs3_0.all (fun p => verifyFast 4478 negs 2 p.1 p.2 row2) = true := by
  decide +kernel

def pairs3_1 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 35064, 65382], []),
  ([240, 4383, 28518, 63736], []),
  ([4383, 26214, 35064, 65416], []),
  ([496, 4383, 34952, 63078], []),
  ([496, 4383, 26214, 63624], []),
  ([240, 4383, 34952, 63334], []),
  ([240, 4383, 26470, 63624], []),
  ([240, 4383, 35208, 63078], []),
  ([240, 4383, 26214, 63880], []),
  ([4336, 4383, 28518, 34952], []),
  ([240, 4383, 32614, 34952], []),
  ([240, 4383, 28518, 39048], []),
  ([240, 4383, 61422, 65382], []),
  ([240, 4383, 28518, 65518], []),
  ([240, 4383, 65382, 65518], []),
  ([240, 4383, 63624, 65382], []),
  ([240, 4104, 4383, 28518], [[4344, 4383, 28518], [240, 4383, 32622]]),
  ([240, 4383, 44970, 65382], []),
  ([240, 4383, 28518, 65450], []),
  ([240, 4383, 52428, 65382], []),
  ([240, 4383, 28518, 64716], []),
  ([240, 4383, 65382, 65450], []),
  ([240, 4383, 64716, 65382], []),
  ([4344, 4383, 12066, 17476], [[4344, 4383, 28518]]),
  ([240, 4383, 16170, 17476], [[240, 4383, 32622]]),
  ([240, 4383, 12066, 21580], [[240, 4383, 32622]]),
  ([240, 4383, 36744, 65382], []),
  ([240, 4383, 28518, 65416], []),
  ([240, 4383, 44970, 63078], []),
  ([240, 4383, 26214, 65450], []),
  ([240, 4383, 43690, 65382], []),
  ([240, 4383, 28518, 64170], []),
  ([240, 4383, 53196, 65382], []),
  ([240, 4383, 28518, 65484], []),
  ([240, 4383, 64170, 65382], []),
  ([240, 4383, 65382, 65484], []),
  ([4344, 4383, 8738, 20292], [[4344, 4383, 28518]]),
  ([240, 4383, 12842, 20292], [[240, 4383, 32622]]),
  ([240, 4383, 8738, 24396], [[240, 4383, 32622]]),
  ([240, 4383, 53196, 63078], []),
  ([240, 4383, 26214, 65484], []),
  ([504, 4383, 26214, 61440], [[504, 4383, 63078]]),
  ([504, 4383, 17476, 61986], [[504, 4383, 63078]]),
  ([504, 4383, 8738, 62532], [[504, 4383, 63078]]),
  ([240, 4383, 26478, 61440], [[240, 4383, 63342]]),
  ([240, 4383, 17476, 62250], [[240, 4383, 63342]]),
  ([240, 4383, 9002, 62532], [[240, 4383, 63342]]),
  ([240, 4383, 17740, 61986], [[240, 4383, 63342]]),
  ([240, 4383, 8738, 62796], [[240, 4383, 63342]]),
  ([240, 4383, 26214, 61704], [[240, 4383, 63342]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk3_1 : pairs3_1.all (fun p => verifyFast 4478 negs 2 p.1 p.2 row2) = true := by
  decide +kernel

def pairs3_2 : List (List ℕ × List (List ℕ)) := [
  ([240, 264, 4383, 63078], [[504, 4383, 63078], [240, 4383, 63342]]),
  ([4336, 4383, 26214, 36744], []),
  ([240, 4383, 30310, 36744], []),
  ([240, 4383, 26214, 40840], []),
  ([240, 4383, 61422, 63078], []),
  ([240, 4383, 26214, 65518], []),
  ([240, 4383, 63078, 65518], []),
  ([240, 4383, 63078, 65416], []),
  ([240, 4360, 4383, 26214], [[4383, 4600, 26214], [240, 4383, 30574]]),
  ([240, 4383, 63078, 65450], []),
  ([240, 4383, 63078, 65484], []),
  ([4383, 4600, 8738, 17476], [[4383, 4600, 26214]]),
  ([240, 4383, 13098, 17476], [[240, 4383, 30574]]),
  ([240, 4383, 8738, 21836], [[240, 4383, 30574]]),
  ([4383, 4592, 26214, 34952], [[4383, 26214, 39416]]),
  ([240, 4383, 30566, 34952], [[4383, 30566, 35064]]),
  ([240, 4383, 26214, 39304], [[4383, 26214, 39416]]),
  ([240, 4383, 61166, 65382], []),
  ([240, 4383, 65382, 65416], []),
  ([240, 4383, 28518, 65262], []),
  ([240, 4383, 65262, 65382], []),
  ([3840, 4344, 4383, 26214], [[4344, 4383, 28518]]),
  ([240, 4383, 7944, 26214], [[240, 4383, 32622]]),
  ([240, 3840, 4383, 30318], [[240, 4383, 32622]]),
  ([15, 248, 4369, 65382], [[248, 4383, 65382]]),
  ([15, 240, 4369, 65390], [[240, 4383, 65390]]),
  ([15, 4368, 26214, 35064], []),
  ([15, 4369, 30566, 35064], [[4383, 30566, 35064]]),
  ([15, 4369, 26214, 39416], [[4383, 26214, 39416]]),
  ([14, 240, 4369, 65382], [])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk3_2 : pairs3_2.all (fun p => verifyFast 4478 negs 2 p.1 p.2 row2) = true := by
  decide +kernel

def pairs3 : List (List ℕ × List (List ℕ)) := pairs3_0 ++ pairs3_1 ++ pairs3_2

set_option maxRecDepth 20000 in
theorem pairs3_fst : pairs3.map Prod.fst = row3 := rfl

theorem chk3 : pairs3.all (fun p => verifyFast 4478 negs 2 p.1 p.2 row2) = true := by
  unfold pairs3
  simp only [List.all_append, Bool.and_eq_true, chk3_0, chk3_1, chk3_2, and_self]

def pairs4_0 : List (List ℕ × List (List ℕ)) := [
  ([4383, 8738, 17476, 35064, 65280], [[4383, 26214, 35064, 65280]]),
  ([3840, 4383, 26214, 35064, 61440], [[4383, 26214, 35064, 65280]]),
  ([240, 4383, 28518, 34952, 61440], [[240, 4383, 34952, 65382], [240, 4383, 28518, 63624]]),
  ([240, 4383, 17476, 34952, 65314], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 12066, 34952, 62532], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 12066, 17476, 63624], [[240, 4383, 28518, 63624]]),
  ([240, 4383, 20292, 34952, 61986], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 8738, 34952, 65348], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 8738, 20292, 63624], [[240, 4383, 28518, 63624]]),
  ([240, 4383, 26214, 36744, 61440], [[240, 4383, 36744, 63078], [240, 4383, 26214, 65416]]),
  ([240, 4383, 17476, 36744, 61986], [[240, 4383, 36744, 63078]]),
  ([240, 4383, 8738, 36744, 62532], [[240, 4383, 36744, 63078]]),
  ([240, 4383, 8738, 17476, 65416], [[240, 4383, 26214, 65416]]),
  ([240, 4383, 26214, 34952, 65280], [[4383, 26214, 35064, 65280], [240, 4383, 34952, 65382], [240, 4383, 26214, 65416]]),
  ([240, 3840, 4383, 34952, 63078], [[240, 4383, 36744, 63078], [240, 4383, 34952, 65382]]),
  ([240, 3840, 4383, 26214, 63624], [[240, 4383, 28518, 63624], [240, 4383, 26214, 65416]]),
  ([15, 4369, 26214, 35064, 65280], [[4383, 26214, 35064, 65280]]),
  ([15, 240, 4369, 34952, 65382], [[240, 4383, 34952, 65382]]),
  ([15, 240, 4369, 28518, 63624], [[240, 4383, 28518, 63624]]),
  ([15, 240, 4369, 36744, 63078], [[240, 4383, 36744, 63078]]),
  ([15, 240, 4369, 26214, 65416], [[240, 4383, 26214, 65416]]),
  ([248, 4383, 12066, 17476, 61440], [[248, 4383, 28518, 61440], [248, 4383, 17476, 65314], [248, 4383, 12066, 62532]]),
  ([248, 4383, 8738, 20292, 61440], [[248, 4383, 28518, 61440], [248, 4383, 20292, 61986], [248, 4383, 8738, 65348]]),
  ([248, 4383, 8738, 17476, 65280], [[248, 4383, 26214, 65280], [248, 4383, 17476, 65314], [248, 4383, 8738, 65348]]),
  ([248, 3840, 4383, 26214, 61440], [[248, 4383, 28518, 61440], [248, 4383, 26214, 65280], [248, 3840, 4383, 63078]]),
  ([248, 3840, 4383, 17476, 61986], [[248, 4383, 20292, 61986], [248, 4383, 17476, 65314], [248, 3840, 4383, 63078]]),
  ([248, 3840, 4383, 8738, 62532], [[248, 4383, 12066, 62532], [248, 4383, 8738, 65348], [248, 3840, 4383, 63078]]),
  ([240, 4383, 12074, 17476, 61440], [[240, 4383, 28526, 61440], [240, 4383, 17476, 65322], [240, 4383, 12074, 62532]]),
  ([240, 4383, 8738, 20300, 61440], [[240, 4383, 28526, 61440], [240, 4383, 20300, 61986], [240, 4383, 8738, 65356]]),
  ([240, 4383, 8738, 17476, 65288], [[240, 4383, 26214, 65288], [240, 4383, 17476, 65322], [240, 4383, 8738, 65356]]),
  ([240, 3848, 4383, 26214, 61440], [[240, 4383, 28526, 61440], [240, 4383, 26214, 65288], [240, 3848, 4383, 63078]]),
  ([240, 3848, 4383, 17476, 61986], [[240, 4383, 20300, 61986], [240, 4383, 17476, 65322], [240, 3848, 4383, 63078]]),
  ([240, 3848, 4383, 8738, 62532], [[240, 4383, 12074, 62532], [240, 4383, 8738, 65356], [240, 3848, 4383, 63078]]),
  ([240, 4383, 8746, 20292, 61440], [[240, 4383, 28526, 61440], [240, 4383, 20292, 61994], [240, 4383, 8746, 65348]]),
  ([240, 4383, 8746, 17476, 65280], [[240, 4383, 26222, 65280], [240, 4383, 17476, 65322], [240, 4383, 8746, 65348]]),
  ([240, 3840, 4383, 26222, 61440], [[240, 4383, 28526, 61440], [240, 4383, 26222, 65280], [240, 3840, 4383, 63086]]),
  ([240, 3840, 4383, 17476, 61994], [[240, 4383, 20292, 61994], [240, 4383, 17476, 65322], [240, 3840, 4383, 63086]]),
  ([240, 3840, 4383, 8746, 62532], [[240, 4383, 12074, 62532], [240, 4383, 8746, 65348], [240, 3840, 4383, 63086]]),
  ([240, 4383, 12066, 17484, 61440], [[240, 4383, 28526, 61440], [240, 4383, 17484, 65314], [240, 4383, 12066, 62540]]),
  ([240, 4383, 8738, 17484, 65280], [[240, 4383, 26222, 65280], [240, 4383, 17484, 65314], [240, 4383, 8738, 65356]]),
  ([240, 3840, 4383, 17484, 61986], [[240, 4383, 20300, 61986], [240, 4383, 17484, 65314], [240, 3840, 4383, 63086]]),
  ([240, 3840, 4383, 8738, 62540], [[240, 4383, 12066, 62540], [240, 4383, 8738, 65356], [240, 3840, 4383, 63086]]),
  ([240, 4383, 12066, 17476, 61448], [[240, 4383, 28518, 61448], [240, 4383, 17476, 65322], [240, 4383, 12066, 62540]]),
  ([240, 4383, 8738, 20292, 61448], [[240, 4383, 28518, 61448], [240, 4383, 20292, 61994], [240, 4383, 8738, 65356]]),
  ([240, 3840, 4383, 26214, 61448], [[240, 4383, 28518, 61448], [240, 4383, 26214, 65288], [240, 3840, 4383, 63086]]),
  ([8, 240, 4383, 28518, 61440], [[248, 4383, 28518, 61440], [240, 4383, 28526, 61440], [240, 4383, 28518, 61448], [8, 240, 4383, 65382]]),
  ([8, 240, 4383, 17476, 65314], [[248, 4383, 17476, 65314], [240, 4383, 17484, 65314], [240, 4383, 17476, 65322], [8, 240, 4383, 65382]]),
  ([8, 240, 4383, 12066, 62532], [[248, 4383, 12066, 62532], [240, 4383, 12074, 62532], [240, 4383, 12066, 62540], [8, 240, 4383, 65382]]),
  ([8, 240, 4383, 20292, 61986], [[248, 4383, 20292, 61986], [240, 4383, 20300, 61986], [240, 4383, 20292, 61994], [8, 240, 4383, 65382]]),
  ([8, 240, 4383, 8738, 65348], [[248, 4383, 8738, 65348], [240, 4383, 8746, 65348], [240, 4383, 8738, 65356], [8, 240, 4383, 65382]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_0 : pairs4_0.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_1 : List (List ℕ × List (List ℕ)) := [
  ([8, 240, 4383, 26214, 65280], [[248, 4383, 26214, 65280], [240, 4383, 26222, 65280], [240, 4383, 26214, 65288], [8, 240, 4383, 65382]]),
  ([8, 240, 3840, 4383, 63078], [[248, 3840, 4383, 63078], [240, 3848, 4383, 63078], [240, 3840, 4383, 63086], [8, 240, 4383, 65382]]),
  ([4383, 8738, 17476, 35064, 65520], [[4383, 26214, 35064, 65520]]),
  ([4080, 4383, 26214, 35064, 61440], [[4383, 26214, 35064, 65520], [4080, 4383, 35064, 63078], [4080, 4383, 26214, 63736]]),
  ([4080, 4383, 17476, 35064, 61986], [[4080, 4383, 35064, 63078]]),
  ([4080, 4383, 8738, 35064, 62532], [[4080, 4383, 35064, 63078]]),
  ([4080, 4383, 8738, 17476, 63736], [[4080, 4383, 26214, 63736]]),
  ([4383, 8738, 17476, 36856, 61680], [[4383, 26214, 36856, 61680]]),
  ([4080, 4383, 26214, 34952, 61680], [[4383, 26214, 36856, 61680], [4080, 4383, 26214, 63736]]),
  ([240, 4383, 26214, 36856, 61440], [[4383, 26214, 36856, 61680], [240, 4383, 36856, 63078], [240, 4383, 26214, 65528]]),
  ([240, 4383, 17476, 36856, 61986], [[240, 4383, 36856, 63078]]),
  ([240, 4383, 8738, 36856, 62532], [[240, 4383, 36856, 63078]]),
  ([240, 4383, 8738, 17476, 65528], [[240, 4383, 26214, 65528]]),
  ([240, 4383, 26214, 34952, 65520], [[4383, 26214, 35064, 65520], [240, 4383, 26214, 65528]]),
  ([240, 4080, 4383, 34952, 63078], [[4080, 4383, 35064, 63078], [240, 4383, 36856, 63078]]),
  ([240, 4080, 4383, 26214, 63624], [[4080, 4383, 26214, 63736], [240, 4383, 26214, 65528]]),
  ([4383, 8994, 17476, 35064, 61440], [[4383, 26470, 35064, 61440]]),
  ([4383, 8738, 17732, 35064, 61440], [[4383, 26470, 35064, 61440]]),
  ([4383, 8738, 17476, 35320, 61440], [[4383, 26214, 35320, 61440]]),
  ([4383, 8738, 17476, 35064, 61696], [[4383, 26214, 35064, 61696]]),
  ([256, 4383, 26214, 35064, 61440], [[4383, 26470, 35064, 61440], [4383, 26214, 35320, 61440], [4383, 26214, 35064, 61696]]),
  ([4383, 12066, 26214, 35064, 61440], [[4383, 26214, 35064, 65314]]),
  ([4383, 12066, 17476, 35064, 61986], []),
  ([4383, 8738, 17476, 35064, 65314], [[4383, 26214, 35064, 65314]]),
  ([4383, 20292, 26214, 35064, 61440], [[4383, 26214, 35064, 65348]]),
  ([4383, 8738, 20292, 35064, 62532], []),
  ([4383, 8738, 17476, 35064, 65348], [[4383, 26214, 35064, 65348]]),
  ([4383, 26214, 35064, 36856, 61440], [[4383, 26214, 36856, 63736], [4383, 26214, 35064, 65528]]),
  ([4383, 8738, 17476, 36856, 63736], [[4383, 26214, 36856, 63736]]),
  ([4383, 8738, 17476, 35064, 65528], [[4383, 26214, 35064, 65528]]),
  ([4352, 4383, 8738, 17476, 35064], [[4383, 13090, 17476, 35064], [4383, 8738, 21828, 35064], [4383, 8738, 17476, 39416], [4352, 4383, 26214, 35064]]),
  ([15, 4383, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([4383, 8738, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65314], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([4383, 17476, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65348], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([3840, 4383, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([4383, 26214, 35064, 61440, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([4383, 7936, 8738, 17476, 35064], [[4383, 7936, 26214, 35064]]),
  ([3840, 4383, 12834, 17476, 35064], [[3840, 4383, 30310, 35064]]),
  ([3840, 4383, 8738, 21572, 35064], [[3840, 4383, 30310, 35064]]),
  ([3840, 4383, 8738, 17476, 39160], [[3840, 4383, 26214, 39160]]),
  ([3840, 4096, 4383, 26214, 35064], [[4383, 7936, 26214, 35064], [3840, 4383, 30310, 35064], [3840, 4383, 26214, 39160]]),
  ([4383, 26214, 28518, 35064, 61440], [[4383, 28518, 35064, 63078], [4383, 26214, 35064, 65382]]),
  ([3840, 4383, 26214, 35064, 63078], [[4383, 28518, 35064, 63078], [4383, 26214, 35064, 65382]]),
  ([3840, 4383, 26214, 35064, 63736], [[4383, 26214, 36856, 63736], [4383, 26214, 35064, 65528]]),
  ([3840, 4383, 26214, 35064, 61986], [[4383, 26214, 35064, 65314]]),
  ([3840, 4383, 26214, 35064, 62532], [[4383, 26214, 35064, 65348]]),
  ([4383, 12066, 17476, 35064, 61680], [[4383, 28518, 35064, 61680]]),
  ([4383, 8738, 20292, 35064, 61680], [[4383, 28518, 35064, 61680]]),
  ([3840, 4383, 26214, 35064, 61680], [[4383, 28518, 35064, 61680], [4383, 26214, 36856, 61680], [4383, 26214, 35064, 65520]]),
  ([240, 4383, 28518, 35064, 61440], [[4383, 28518, 35064, 61680], [240, 4383, 35064, 65382], [240, 4383, 28518, 63736]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_1 : pairs4_1.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_2 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 17476, 35064, 65314], [[240, 4383, 35064, 65382]]),
  ([240, 4383, 12066, 35064, 62532], [[240, 4383, 35064, 65382]]),
  ([240, 4383, 12066, 17476, 63736], [[240, 4383, 28518, 63736]]),
  ([240, 4383, 20292, 35064, 61986], [[240, 4383, 35064, 65382]]),
  ([240, 4383, 8738, 35064, 65348], [[240, 4383, 35064, 65382]]),
  ([240, 4383, 8738, 20292, 63736], [[240, 4383, 28518, 63736]]),
  ([240, 4383, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4383, 26214, 35064, 65520], [4352, 4383, 26214, 35064], [240, 4383, 35064, 65382], [4383, 26214, 35064, 65382], [240, 4383, 26214, 65528], [4383, 26214, 35064, 65528]]),
  ([240, 3840, 4383, 35064, 63078], [[4080, 4383, 35064, 63078], [240, 4383, 36856, 63078], [240, 4383, 35064, 65382]]),
  ([240, 3840, 4383, 26214, 63736], [[4080, 4383, 26214, 63736], [240, 4383, 28518, 63736], [240, 4383, 26214, 65528]]),
  ([4383, 26214, 35064, 36744, 61440], [[4383, 26214, 35064, 65416]]),
  ([4383, 8738, 17476, 35064, 65416], [[4383, 26214, 35064, 65416]]),
  ([4383, 26214, 34952, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65416], [4383, 26214, 35064, 65528]]),
  ([3840, 4383, 26214, 35064, 63624], [[4383, 26214, 35064, 65416]]),
  ([240, 4383, 28518, 34952, 61680], [[4383, 28518, 35064, 61680], [240, 4383, 28518, 63736]]),
  ([240, 4383, 26214, 36744, 61680], [[4383, 26214, 36856, 61680], [240, 4383, 26214, 65528]]),
  ([496, 4383, 26214, 34952, 61440], [[4383, 26214, 35320, 61440], [496, 4383, 34952, 63078], [496, 4383, 26214, 63624]]),
  ([496, 4383, 17476, 34952, 61986], [[496, 4383, 34952, 63078]]),
  ([496, 4383, 8738, 34952, 62532], [[496, 4383, 34952, 63078]]),
  ([496, 4383, 8738, 17476, 63624], [[496, 4383, 26214, 63624]]),
  ([240, 4383, 26470, 34952, 61440], [[4383, 26470, 35064, 61440], [240, 4383, 34952, 63334], [240, 4383, 26470, 63624]]),
  ([240, 4383, 17476, 34952, 62242], [[240, 4383, 34952, 63334]]),
  ([240, 4383, 8994, 34952, 62532], [[240, 4383, 34952, 63334]]),
  ([240, 4383, 8994, 17476, 63624], [[240, 4383, 26470, 63624]]),
  ([240, 4383, 17732, 34952, 61986], [[240, 4383, 34952, 63334]]),
  ([240, 4383, 8738, 34952, 62788], [[240, 4383, 34952, 63334]]),
  ([240, 4383, 8738, 17732, 63624], [[240, 4383, 26470, 63624]]),
  ([240, 4383, 26214, 35208, 61440], [[4383, 26214, 35320, 61440], [240, 4383, 35208, 63078], [240, 4383, 26214, 63880]]),
  ([240, 4383, 17476, 35208, 61986], [[240, 4383, 35208, 63078]]),
  ([240, 4383, 8738, 35208, 62532], [[240, 4383, 35208, 63078]]),
  ([240, 4383, 8738, 17476, 63880], [[240, 4383, 26214, 63880]]),
  ([240, 4383, 26214, 34952, 61696], [[4383, 26214, 35064, 61696], [240, 4383, 34952, 63334], [240, 4383, 26214, 63880]]),
  ([240, 256, 4383, 34952, 63078], [[496, 4383, 34952, 63078], [240, 4383, 35208, 63078], [240, 4383, 34952, 63334]]),
  ([240, 256, 4383, 26214, 63624], [[496, 4383, 26214, 63624], [240, 4383, 26470, 63624], [240, 4383, 26214, 63880]]),
  ([4336, 4383, 12066, 17476, 34952], [[4336, 4383, 28518, 34952]]),
  ([240, 4383, 16162, 17476, 34952], [[240, 4383, 32614, 34952]]),
  ([240, 4383, 12066, 21572, 34952], [[240, 4383, 32614, 34952]]),
  ([240, 4383, 12066, 17476, 39048], [[240, 4383, 28518, 39048]]),
  ([240, 4096, 4383, 28518, 34952], [[4336, 4383, 28518, 34952], [240, 4383, 32614, 34952], [240, 4383, 28518, 39048]]),
  ([240, 4383, 28518, 61422, 61440], [[240, 4383, 61422, 65382], [240, 4383, 28518, 65518]]),
  ([15, 240, 4383, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 28518, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 61422, 65382], [240, 4383, 28518, 65518], [240, 4383, 65382, 65518]]),
  ([240, 4383, 34952, 61440, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 63624, 65382], [240, 4383, 65382, 65518]]),
  ([15, 240, 4383, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65518]]),
  ([240, 4383, 28518, 34952, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65518]]),
  ([240, 4383, 28518, 61440, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 63624, 65382], [240, 4383, 28518, 65518]]),
  ([240, 4383, 28518, 44970, 61440], [[240, 4383, 44970, 65382], [240, 4383, 28518, 65450]]),
  ([240, 4383, 28518, 34952, 65314], [[240, 4383, 34952, 65382], [240, 4383, 28518, 65450]]),
  ([240, 4383, 12066, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 44970, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 12066, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65450], [240, 4383, 28518, 65518]]),
  ([240, 4383, 28518, 52428, 61440], [[240, 4383, 52428, 65382], [240, 4383, 28518, 64716]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_2 : pairs4_2.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_3 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 28518, 34952, 62532], [[240, 4383, 34952, 65382], [240, 4383, 28518, 64716]]),
  ([240, 4383, 17476, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 52428, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 17476, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 64716], [240, 4383, 28518, 65518]]),
  ([240, 4383, 17476, 44970, 65314], [[240, 4383, 44970, 65382]]),
  ([240, 4383, 12066, 44970, 62532], [[240, 4383, 44970, 65382]]),
  ([240, 4383, 12066, 17476, 65450], [[240, 4383, 28518, 65450]]),
  ([240, 4383, 17476, 52428, 65314], [[240, 4383, 52428, 65382]]),
  ([240, 4383, 34952, 65314, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65450], [240, 4383, 65382, 65518]]),
  ([240, 4383, 17476, 65314, 65450], [[240, 4383, 65382, 65450]]),
  ([240, 4383, 34952, 62532, 65314], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 17476, 63624, 65314], [[240, 4383, 63624, 65382]]),
  ([240, 4383, 12066, 52428, 62532], [[240, 4383, 52428, 65382]]),
  ([240, 4383, 12066, 17476, 64716], [[240, 4383, 28518, 64716]]),
  ([240, 4383, 34952, 62532, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 64716, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 12066, 62532, 64716], [[240, 4383, 64716, 65382]]),
  ([240, 4383, 12066, 62532, 63624], [[240, 4383, 63624, 65382]]),
  ([240, 4104, 4383, 12066, 17476], [[4344, 4383, 12066, 17476], [240, 4383, 16170, 17476], [240, 4383, 12066, 21580], [240, 4104, 4383, 28518]]),
  ([240, 4383, 20292, 34952, 65314], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 12066, 34952, 65348], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 12066, 20292, 63624], [[240, 4383, 28518, 63624]]),
  ([240, 4383, 28518, 36744, 61440], [[240, 4383, 36744, 65382], [240, 4383, 28518, 65416]]),
  ([240, 4383, 17476, 36744, 65314], [[240, 4383, 36744, 65382]]),
  ([240, 4383, 12066, 36744, 62532], [[240, 4383, 36744, 65382]]),
  ([240, 4383, 12066, 17476, 65416], [[240, 4383, 28518, 65416]]),
  ([240, 4383, 28518, 34952, 65280], [[240, 4383, 34952, 65382], [240, 4383, 28518, 65416]]),
  ([240, 3840, 4383, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [240, 4383, 36744, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65518]]),
  ([240, 3840, 4383, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4383, 28518, 65416], [240, 4104, 4383, 28518], [240, 4383, 28518, 65518]]),
  ([240, 4383, 26214, 44970, 61440], [[240, 4383, 44970, 63078], [240, 4383, 26214, 65450]]),
  ([240, 4383, 26214, 34952, 65314], [[4383, 26214, 35064, 65314], [240, 4383, 34952, 65382], [240, 4383, 26214, 65450]]),
  ([240, 4383, 12066, 34952, 63078], [[240, 4383, 44970, 63078], [240, 4383, 34952, 65382]]),
  ([240, 4383, 12066, 26214, 63624], [[240, 4383, 28518, 63624], [240, 4383, 26214, 65450]]),
  ([240, 4383, 28518, 43690, 61440], [[240, 4383, 43690, 65382], [240, 4383, 28518, 64170]]),
  ([240, 4383, 17476, 43690, 65314], [[240, 4383, 43690, 65382]]),
  ([240, 4383, 12066, 43690, 62532], [[240, 4383, 43690, 65382]]),
  ([240, 4383, 12066, 17476, 64170], [[240, 4383, 28518, 64170]]),
  ([240, 4383, 28518, 34952, 61986], [[240, 4383, 34952, 65382], [240, 4383, 28518, 64170]]),
  ([240, 4383, 17476, 44970, 61986], [[240, 4383, 44970, 63078]]),
  ([240, 4383, 8738, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 43690, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 8738, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 64170], [240, 4383, 28518, 65518]]),
  ([240, 4383, 8738, 44970, 62532], [[240, 4383, 44970, 63078]]),
  ([240, 4383, 8738, 17476, 65450], [[240, 4383, 26214, 65450]]),
  ([4336, 4383, 8738, 20292, 34952], [[4336, 4383, 28518, 34952]]),
  ([240, 4383, 12834, 20292, 34952], [[240, 4383, 32614, 34952]]),
  ([240, 4383, 8738, 24388, 34952], [[240, 4383, 32614, 34952]]),
  ([240, 4383, 8738, 20292, 39048], [[240, 4383, 28518, 39048]]),
  ([240, 4383, 28518, 53196, 61440], [[240, 4383, 53196, 65382], [240, 4383, 28518, 65484]]),
  ([240, 4383, 28518, 34952, 65348], [[240, 4383, 34952, 65382], [240, 4383, 28518, 65484]]),
  ([240, 4383, 20292, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 53196, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 20292, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65484], [240, 4383, 28518, 65518]]),
  ([240, 4383, 20292, 43690, 61986], [[240, 4383, 43690, 65382]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_3 : pairs4_3.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_4 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 8738, 43690, 65348], [[240, 4383, 43690, 65382]]),
  ([240, 4383, 8738, 20292, 64170], [[240, 4383, 28518, 64170]]),
  ([240, 4383, 20292, 53196, 61986], [[240, 4383, 53196, 65382]]),
  ([240, 4383, 34952, 61986, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 64170, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4383, 20292, 61986, 64170], [[240, 4383, 64170, 65382]]),
  ([240, 4383, 34952, 61986, 65348], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 20292, 61986, 63624], [[240, 4383, 63624, 65382]]),
  ([240, 4383, 8738, 53196, 65348], [[240, 4383, 53196, 65382]]),
  ([240, 4383, 8738, 20292, 65484], [[240, 4383, 28518, 65484]]),
  ([240, 4383, 34952, 65348, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65484], [240, 4383, 65382, 65518]]),
  ([240, 4383, 8738, 65348, 65484], [[240, 4383, 65382, 65484]]),
  ([240, 4383, 8738, 63624, 65348], [[240, 4383, 63624, 65382]]),
  ([240, 4104, 4383, 8738, 20292], [[4344, 4383, 8738, 20292], [240, 4383, 12842, 20292], [240, 4383, 8738, 24396], [240, 4104, 4383, 28518]]),
  ([240, 4383, 20292, 36744, 61986], [[240, 4383, 36744, 65382]]),
  ([240, 4383, 8738, 36744, 65348], [[240, 4383, 36744, 65382]]),
  ([240, 4383, 8738, 20292, 65416], [[240, 4383, 28518, 65416]]),
  ([240, 4383, 26214, 53196, 61440], [[240, 4383, 53196, 63078], [240, 4383, 26214, 65484]]),
  ([240, 4383, 26214, 34952, 65348], [[4383, 26214, 35064, 65348], [240, 4383, 34952, 65382], [240, 4383, 26214, 65484]]),
  ([240, 4383, 20292, 34952, 63078], [[240, 4383, 53196, 63078], [240, 4383, 34952, 65382]]),
  ([240, 4383, 20292, 26214, 63624], [[240, 4383, 28518, 63624], [240, 4383, 26214, 65484]]),
  ([240, 4383, 20292, 52428, 61986], [[240, 4383, 52428, 65382]]),
  ([240, 4383, 17476, 53196, 61986], [[240, 4383, 53196, 63078]]),
  ([240, 4383, 8738, 52428, 65348], [[240, 4383, 52428, 65382]]),
  ([240, 4383, 8738, 20292, 64716], [[240, 4383, 28518, 64716]]),
  ([240, 4383, 8738, 53196, 62532], [[240, 4383, 53196, 63078]]),
  ([240, 4383, 8738, 17476, 65484], [[240, 4383, 26214, 65484]]),
  ([504, 4383, 8738, 17476, 61440], [[504, 4383, 26214, 61440], [504, 4383, 17476, 61986], [504, 4383, 8738, 62532]]),
  ([240, 4383, 9002, 17476, 61440], [[240, 4383, 26478, 61440], [240, 4383, 17476, 62250], [240, 4383, 9002, 62532]]),
  ([240, 4383, 8738, 17740, 61440], [[240, 4383, 26478, 61440], [240, 4383, 17740, 61986], [240, 4383, 8738, 62796]]),
  ([240, 4383, 8738, 17476, 61704], [[240, 4383, 26214, 61704], [240, 4383, 17476, 62250], [240, 4383, 8738, 62796]]),
  ([240, 264, 4383, 26214, 61440], [[504, 4383, 26214, 61440], [240, 4383, 26478, 61440], [240, 4383, 26214, 61704], [240, 264, 4383, 63078]]),
  ([240, 264, 4383, 17476, 61986], [[504, 4383, 17476, 61986], [240, 4383, 17740, 61986], [240, 4383, 17476, 62250], [240, 264, 4383, 63078]]),
  ([240, 264, 4383, 8738, 62532], [[504, 4383, 8738, 62532], [240, 4383, 9002, 62532], [240, 4383, 8738, 62796], [240, 264, 4383, 63078]]),
  ([4336, 4383, 8738, 17476, 36744], [[4336, 4383, 26214, 36744]]),
  ([240, 4383, 12834, 17476, 36744], [[240, 4383, 30310, 36744]]),
  ([240, 4383, 8738, 21572, 36744], [[240, 4383, 30310, 36744]]),
  ([240, 4383, 8738, 17476, 40840], [[240, 4383, 26214, 40840]]),
  ([240, 4096, 4383, 26214, 36744], [[4336, 4383, 26214, 36744], [240, 4383, 30310, 36744], [240, 4383, 26214, 40840]]),
  ([240, 4383, 26214, 61422, 61440], [[240, 4383, 61422, 63078], [240, 4383, 26214, 65518]]),
  ([15, 240, 4383, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65518]]),
  ([240, 4383, 26214, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 61422, 63078], [240, 4383, 26214, 65518], [240, 4383, 63078, 65518]]),
  ([240, 4383, 36744, 61440, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65416], [240, 4383, 63078, 65518]]),
  ([15, 240, 4383, 26214, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 36744, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 61440, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 63078, 65416], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 36744, 61986], [[240, 4383, 36744, 63078], [240, 4383, 26214, 65450]]),
  ([240, 4383, 8738, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 44970, 63078], [240, 4383, 63078, 65518]]),
  ([240, 4383, 8738, 26214, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65450], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 36744, 62532], [[240, 4383, 36744, 63078], [240, 4383, 26214, 65484]]),
  ([240, 4383, 17476, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 53196, 63078], [240, 4383, 63078, 65518]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_4 : pairs4_4.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_5 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 17476, 26214, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65484], [240, 4383, 26214, 65518]]),
  ([240, 4383, 36744, 61986, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65450], [240, 4383, 63078, 65518]]),
  ([240, 4383, 17476, 61986, 65450], [[240, 4383, 63078, 65450]]),
  ([240, 4383, 36744, 61986, 62532], [[240, 4383, 36744, 63078]]),
  ([240, 4383, 17476, 61986, 65416], [[240, 4383, 63078, 65416]]),
  ([240, 4383, 36744, 62532, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65484], [240, 4383, 63078, 65518]]),
  ([240, 4383, 8738, 62532, 65484], [[240, 4383, 63078, 65484]]),
  ([240, 4383, 8738, 62532, 65416], [[240, 4383, 63078, 65416]]),
  ([240, 4360, 4383, 8738, 17476], [[4383, 4600, 8738, 17476], [240, 4383, 13098, 17476], [240, 4383, 8738, 21836], [240, 4360, 4383, 26214]]),
  ([240, 4383, 26214, 36744, 65280], [[240, 4383, 36744, 65382], [240, 4383, 26214, 65416]]),
  ([240, 3840, 4383, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 4383, 36744, 65382], [240, 264, 4383, 63078], [240, 4383, 63078, 65518]]),
  ([240, 3840, 4383, 26214, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4383, 28518, 65416], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([240, 4383, 34952, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65518]]),
  ([240, 4383, 26214, 36744, 63624], [[240, 4383, 26214, 65416]]),
  ([240, 4383, 26214, 34952, 65416], [[240, 4383, 26214, 65416], [4383, 26214, 35064, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([4383, 4592, 8738, 17476, 34952], [[4383, 8738, 17476, 39416], [4383, 4592, 26214, 34952]]),
  ([240, 4383, 13090, 17476, 34952], [[4383, 13090, 17476, 35064], [240, 4383, 30566, 34952]]),
  ([240, 4383, 8738, 21828, 34952], [[4383, 8738, 21828, 35064], [240, 4383, 30566, 34952]]),
  ([240, 4383, 8738, 17476, 39304], [[4383, 8738, 17476, 39416], [240, 4383, 26214, 39304]]),
  ([240, 4352, 4383, 26214, 34952], [[4383, 4592, 26214, 34952], [4352, 4383, 26214, 35064], [240, 4383, 30566, 34952], [240, 4383, 26214, 39304]]),
  ([240, 4383, 26214, 61166, 65280], [[240, 4383, 61166, 65382], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [4383, 26214, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 61166, 65382], [240, 4383, 26214, 65518], [240, 4383, 65382, 65518]]),
  ([240, 4383, 34952, 65280, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65416], [240, 4383, 65382, 65518]]),
  ([240, 4383, 26214, 65280, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 65382, 65416], [240, 4383, 26214, 65518]]),
  ([240, 4383, 26214, 43690, 65280], [[240, 4383, 43690, 65382], [240, 4383, 26214, 65450]]),
  ([240, 4383, 26214, 52428, 65280], [[240, 4383, 52428, 65382], [240, 4383, 26214, 65484]]),
  ([240, 4383, 34952, 65314, 65348], [[240, 4383, 34952, 65382]]),
  ([240, 4383, 17476, 65314, 65416], [[240, 4383, 65382, 65416]]),
  ([240, 4383, 8738, 65348, 65416], [[240, 4383, 65382, 65416]]),
  ([240, 4383, 34952, 63078, 65280], [[240, 4383, 63078, 65416], [240, 4383, 34952, 65382]]),
  ([240, 4383, 26214, 63624, 65280], [[240, 4383, 63624, 65382], [240, 4383, 26214, 65416]]),
  ([3840, 4336, 4383, 26214, 34952], [[4336, 4383, 28518, 34952], [4336, 4383, 26214, 36744], [3840, 4383, 26214, 39160]]),
  ([240, 4383, 7936, 26214, 34952], [[4383, 7936, 26214, 35064], [240, 4383, 32614, 34952], [240, 4383, 26214, 40840]]),
  ([240, 3840, 4383, 30310, 34952], [[3840, 4383, 30310, 35064], [240, 4383, 32614, 34952], [240, 4383, 30310, 36744]]),
  ([240, 3840, 4383, 26214, 39048], [[3840, 4383, 26214, 39160], [240, 4383, 28518, 39048], [240, 4383, 26214, 40840]]),
  ([240, 4383, 28518, 61166, 61440], [[240, 4383, 61166, 65382], [240, 4383, 28518, 65262]]),
  ([240, 4383, 28518, 34952, 63078], [[4383, 28518, 35064, 63078], [240, 4383, 61422, 63078], [240, 4383, 34952, 65382], [240, 4383, 28518, 65262]]),
  ([240, 4383, 26214, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65262], [240, 4383, 26214, 65518], [240, 4383, 28518, 65518]]),
  ([240, 3840, 4383, 61166, 63078], [[240, 4383, 61422, 63078], [240, 4383, 61166, 65382]]),
  ([240, 3840, 4383, 26214, 65262], [[240, 4383, 28518, 65262], [240, 4383, 26214, 65518]]),
  ([240, 4383, 34952, 63078, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65262, 65382], [240, 4383, 63078, 65518], [240, 4383, 65382, 65518]]),
  ([240, 3840, 4383, 63078, 65262], [[240, 4383, 65262, 65382], [240, 4383, 63078, 65518]]),
  ([240, 3840, 4383, 63078, 63624], [[240, 4383, 63624, 65382], [240, 4383, 63078, 65416]]),
  ([240, 4383, 26214, 63624, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([240, 3840, 4104, 4383, 26214], [[3840, 4344, 4383, 26214], [240, 4383, 7944, 26214], [240, 4104, 4383, 28518], [240, 3840, 4383, 30318]]),
  ([240, 3840, 4383, 43690, 63078], [[240, 4383, 44970, 63078], [240, 4383, 43690, 65382]]),
  ([240, 3840, 4383, 26214, 64170], [[240, 4383, 28518, 64170], [240, 4383, 26214, 65450]]),
  ([240, 3840, 4383, 52428, 63078], [[240, 4383, 53196, 63078], [240, 4383, 52428, 65382]]),
  ([240, 3840, 4383, 26214, 64716], [[240, 4383, 28518, 64716], [240, 4383, 26214, 65484]]),
  ([240, 4383, 34952, 63078, 65314], [[240, 4383, 63078, 65450], [240, 4383, 34952, 65382]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_5 : pairs4_5.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_6 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 17476, 64170, 65314], [[240, 4383, 64170, 65382]]),
  ([240, 3840, 4383, 63078, 64170], [[240, 4383, 64170, 65382], [240, 4383, 63078, 65450]]),
  ([240, 4383, 34952, 63078, 65348], [[240, 4383, 63078, 65484], [240, 4383, 34952, 65382]]),
  ([240, 4383, 8738, 64716, 65348], [[240, 4383, 64716, 65382]]),
  ([240, 3840, 4383, 63078, 64716], [[240, 4383, 64716, 65382], [240, 4383, 63078, 65484]]),
  ([3840, 4344, 4383, 8738, 17476], [[4344, 4383, 12066, 17476], [4344, 4383, 8738, 20292], [3840, 4344, 4383, 26214]]),
  ([240, 4383, 7944, 8738, 17476], [[240, 4383, 16170, 17476], [240, 4383, 8738, 24396], [240, 4383, 7944, 26214]]),
  ([240, 3840, 4383, 12842, 17476], [[240, 4383, 16170, 17476], [240, 4383, 12842, 20292], [240, 3840, 4383, 30318]]),
  ([240, 3840, 4383, 8738, 21580], [[240, 4383, 12066, 21580], [240, 4383, 8738, 24396], [240, 3840, 4383, 30318]]),
  ([4369, 4383, 26214, 35064, 65280], [[4383, 26214, 35064, 65280], [4352, 4383, 26214, 35064], [4383, 26214, 35064, 65382], [4383, 26214, 35064, 65528]]),
  ([240, 4369, 4383, 34952, 65382], [[240, 4383, 34952, 65382], [240, 4383, 35064, 65382], [8, 240, 4383, 65382], [240, 4383, 65382, 65518]]),
  ([240, 4369, 4383, 28518, 63624], [[240, 4383, 28518, 63624], [240, 4383, 28518, 63736], [240, 4104, 4383, 28518], [240, 4383, 28518, 65518]]),
  ([240, 4369, 4383, 36744, 63078], [[240, 4383, 36744, 63078], [240, 4383, 36856, 63078], [240, 264, 4383, 63078], [240, 4383, 63078, 65518]]),
  ([240, 4369, 4383, 26214, 65416], [[240, 4383, 26214, 65416], [240, 4383, 26214, 65528], [240, 4360, 4383, 26214], [240, 4383, 26214, 65518]]),
  ([15, 248, 4369, 28518, 61440], [[248, 4383, 28518, 61440], [15, 248, 4369, 65382]]),
  ([15, 248, 4369, 17476, 65314], [[248, 4383, 17476, 65314], [15, 248, 4369, 65382]]),
  ([15, 248, 4369, 12066, 62532], [[248, 4383, 12066, 62532], [15, 248, 4369, 65382]]),
  ([15, 248, 4369, 20292, 61986], [[248, 4383, 20292, 61986], [15, 248, 4369, 65382]]),
  ([15, 248, 4369, 8738, 65348], [[248, 4383, 8738, 65348], [15, 248, 4369, 65382]]),
  ([15, 248, 4369, 26214, 65280], [[248, 4383, 26214, 65280], [15, 248, 4369, 65382]]),
  ([15, 248, 3840, 4369, 63078], [[248, 3840, 4383, 63078], [15, 248, 4369, 65382]]),
  ([15, 240, 4369, 28526, 61440], [[240, 4383, 28526, 61440], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 17476, 65322], [[240, 4383, 17476, 65322], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 12074, 62532], [[240, 4383, 12074, 62532], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 20300, 61986], [[240, 4383, 20300, 61986], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 8738, 65356], [[240, 4383, 8738, 65356], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 26214, 65288], [[240, 4383, 26214, 65288], [15, 240, 4369, 65390]]),
  ([15, 240, 3848, 4369, 63078], [[240, 3848, 4383, 63078], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 20292, 61994], [[240, 4383, 20292, 61994], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 8746, 65348], [[240, 4383, 8746, 65348], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 26222, 65280], [[240, 4383, 26222, 65280], [15, 240, 4369, 65390]]),
  ([15, 240, 3840, 4369, 63086], [[240, 3840, 4383, 63086], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 17484, 65314], [[240, 4383, 17484, 65314], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 12066, 62540], [[240, 4383, 12066, 62540], [15, 240, 4369, 65390]]),
  ([15, 240, 4369, 28518, 61448], [[240, 4383, 28518, 61448], [15, 240, 4369, 65390]]),
  ([8, 15, 240, 4369, 65382], [[15, 248, 4369, 65382], [15, 240, 4369, 65390], [8, 240, 4383, 65382]]),
  ([15, 4368, 8738, 17476, 35064], [[15, 4368, 26214, 35064]]),
  ([15, 4369, 26214, 35064, 65520], [[4383, 26214, 35064, 65520], [15, 4368, 26214, 35064]]),
  ([15, 4080, 4369, 35064, 63078], [[4080, 4383, 35064, 63078]]),
  ([15, 4080, 4369, 26214, 63736], [[4080, 4383, 26214, 63736]]),
  ([15, 4369, 26214, 36856, 61680], [[4383, 26214, 36856, 61680]]),
  ([15, 240, 4369, 36856, 63078], [[240, 4383, 36856, 63078]]),
  ([15, 240, 4369, 26214, 65528], [[240, 4383, 26214, 65528]]),
  ([15, 240, 4368, 26214, 34952], [[15, 4368, 26214, 35064]]),
  ([15, 4369, 28518, 35064, 61680], [[4383, 28518, 35064, 61680]]),
  ([15, 240, 4369, 28518, 63736], [[240, 4383, 28518, 63736]]),
  ([15, 4369, 26470, 35064, 61440], [[4383, 26470, 35064, 61440]]),
  ([15, 4369, 26214, 35320, 61440], [[4383, 26214, 35320, 61440]]),
  ([15, 4369, 26214, 35064, 61696], [[4383, 26214, 35064, 61696]]),
  ([15, 240, 4369, 35064, 65382], [[240, 4383, 35064, 65382]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_6 : pairs4_6.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_7 : List (List ℕ × List (List ℕ)) := [
  ([15, 4369, 26214, 35064, 65314], [[4383, 26214, 35064, 65314]]),
  ([15, 4369, 26214, 35064, 65348], [[4383, 26214, 35064, 65348]]),
  ([15, 4369, 26214, 36856, 63736], [[4383, 26214, 36856, 63736]]),
  ([15, 4369, 26214, 35064, 65528], [[4383, 26214, 35064, 65528], [15, 4368, 26214, 35064]]),
  ([15, 4369, 13090, 17476, 35064], [[4383, 13090, 17476, 35064], [15, 4369, 30566, 35064]]),
  ([15, 4369, 8738, 21828, 35064], [[4383, 8738, 21828, 35064], [15, 4369, 30566, 35064]]),
  ([15, 4369, 8738, 17476, 39416], [[4383, 8738, 17476, 39416], [15, 4369, 26214, 39416]]),
  ([15, 4352, 4369, 26214, 35064], [[4352, 4383, 26214, 35064], [15, 4369, 30566, 35064], [15, 4369, 26214, 39416]]),
  ([15, 4369, 26214, 35064, 65382], [[4383, 26214, 35064, 65382]]),
  ([15, 4369, 7936, 26214, 35064], [[4383, 7936, 26214, 35064]]),
  ([15, 3840, 4369, 30310, 35064], [[3840, 4383, 30310, 35064]]),
  ([15, 3840, 4369, 26214, 39160], [[3840, 4383, 26214, 39160]]),
  ([15, 4369, 28518, 35064, 63078], [[4383, 28518, 35064, 63078]]),
  ([15, 4369, 26214, 35064, 65416], [[4383, 26214, 35064, 65416]]),
  ([15, 240, 4369, 28518, 65416], [[240, 4383, 28518, 65416]]),
  ([15, 240, 4369, 36744, 65382], [[240, 4383, 36744, 65382]]),
  ([15, 4369, 4592, 26214, 34952], [[4383, 4592, 26214, 34952], [15, 4369, 26214, 39416]]),
  ([15, 240, 4369, 30566, 34952], [[240, 4383, 30566, 34952], [15, 4369, 30566, 35064]]),
  ([15, 240, 4369, 26214, 39304], [[240, 4383, 26214, 39304], [15, 4369, 26214, 39416]]),
  ([14, 240, 4369, 26214, 65280], [[14, 240, 4369, 65382]]),
  ([15, 240, 4369, 61166, 65382], [[240, 4383, 61166, 65382], [14, 240, 4369, 65382]]),
  ([15, 240, 4369, 26214, 65518], [[240, 4383, 26214, 65518]]),
  ([15, 240, 4369, 65382, 65518], [[240, 4383, 65382, 65518], [14, 240, 4369, 65382]]),
  ([15, 240, 4369, 65382, 65416], [[240, 4383, 65382, 65416]]),
  ([15, 240, 4369, 43690, 65382], [[240, 4383, 43690, 65382]]),
  ([15, 240, 4369, 26214, 65450], [[240, 4383, 26214, 65450]]),
  ([15, 240, 4369, 52428, 65382], [[240, 4383, 52428, 65382]]),
  ([15, 240, 4369, 26214, 65484], [[240, 4383, 26214, 65484]]),
  ([15, 240, 4369, 65382, 65450], [[240, 4383, 65382, 65450]]),
  ([15, 240, 4369, 65382, 65484], [[240, 4383, 65382, 65484]]),
  ([15, 240, 4369, 63078, 65416], [[240, 4383, 63078, 65416]]),
  ([15, 240, 4369, 63624, 65382], [[240, 4383, 63624, 65382]]),
  ([15, 496, 4369, 34952, 63078], [[496, 4383, 34952, 63078]]),
  ([15, 496, 4369, 26214, 63624], [[496, 4383, 26214, 63624]]),
  ([15, 240, 4369, 34952, 63334], [[240, 4383, 34952, 63334]]),
  ([15, 240, 4369, 26470, 63624], [[240, 4383, 26470, 63624]]),
  ([15, 240, 4369, 35208, 63078], [[240, 4383, 35208, 63078]]),
  ([15, 240, 4369, 26214, 63880], [[240, 4383, 26214, 63880]]),
  ([15, 4336, 4369, 28518, 34952], [[4336, 4383, 28518, 34952]]),
  ([15, 240, 4369, 32614, 34952], [[240, 4383, 32614, 34952]]),
  ([15, 240, 4369, 28518, 39048], [[240, 4383, 28518, 39048]]),
  ([14, 240, 4369, 28518, 61440], [[14, 240, 4369, 65382]]),
  ([15, 240, 4369, 61422, 65382], [[240, 4383, 61422, 65382], [14, 240, 4369, 65382]]),
  ([15, 240, 4369, 28518, 65518], [[240, 4383, 28518, 65518]]),
  ([15, 240, 4369, 44970, 65382], [[240, 4383, 44970, 65382]]),
  ([15, 240, 4369, 28518, 65450], [[240, 4383, 28518, 65450]]),
  ([15, 240, 4369, 28518, 64716], [[240, 4383, 28518, 64716]]),
  ([15, 240, 4369, 64716, 65382], [[240, 4383, 64716, 65382]]),
  ([15, 240, 4369, 44970, 63078], [[240, 4383, 44970, 63078]]),
  ([15, 240, 4369, 28518, 64170], [[240, 4383, 28518, 64170]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_7 : pairs4_7.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4_8 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 53196, 65382], [[240, 4383, 53196, 65382]]),
  ([15, 240, 4369, 28518, 65484], [[240, 4383, 28518, 65484]]),
  ([15, 240, 4369, 64170, 65382], [[240, 4383, 64170, 65382]]),
  ([15, 240, 4369, 53196, 63078], [[240, 4383, 53196, 63078]]),
  ([15, 4336, 4369, 26214, 36744], [[4336, 4383, 26214, 36744]]),
  ([15, 240, 4369, 30310, 36744], [[240, 4383, 30310, 36744]]),
  ([15, 240, 4369, 26214, 40840], [[240, 4383, 26214, 40840]]),
  ([15, 240, 4369, 61422, 63078], [[240, 4383, 61422, 63078]]),
  ([15, 240, 4369, 63078, 65518], [[240, 4383, 63078, 65518]]),
  ([15, 240, 4369, 63078, 65450], [[240, 4383, 63078, 65450]]),
  ([15, 240, 4369, 63078, 65484], [[240, 4383, 63078, 65484]]),
  ([15, 240, 4369, 65262, 65382], [[240, 4383, 65262, 65382], [14, 240, 4369, 65382]]),
  ([14, 240, 3840, 4369, 63078], [[14, 240, 4369, 65382]]),
  ([15, 240, 4369, 28518, 65262], [[240, 4383, 28518, 65262]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk4_8 : pairs4_8.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  decide +kernel

def pairs4 : List (List ℕ × List (List ℕ)) := pairs4_0 ++ pairs4_1 ++ pairs4_2 ++ pairs4_3 ++ pairs4_4 ++ pairs4_5 ++ pairs4_6 ++ pairs4_7 ++ pairs4_8

set_option maxRecDepth 20000 in
theorem pairs4_fst : pairs4.map Prod.fst = row4 := rfl

theorem chk4 : pairs4.all (fun p => verifyFast 4478 negs 3 p.1 p.2 row3) = true := by
  unfold pairs4
  simp only [List.all_append, Bool.and_eq_true, chk4_0, chk4_1, chk4_2, chk4_3, chk4_4, chk4_5, chk4_6, chk4_7, chk4_8, and_self]

def pairs5_0 : List (List ℕ × List (List ℕ)) := [
  ([3840, 4383, 8738, 17476, 35064, 61440], [[4383, 8738, 17476, 35064, 65280], [3840, 4383, 26214, 35064, 61440]]),
  ([240, 4383, 12066, 17476, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 17476, 34952, 65314], [240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 17476, 63624]]),
  ([240, 4383, 8738, 20292, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 20292, 34952, 61986], [240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 63624]]),
  ([240, 4383, 8738, 17476, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 17476, 36744, 61986], [240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 65416]]),
  ([240, 4383, 8738, 17476, 34952, 65280], [[4383, 8738, 17476, 35064, 65280], [240, 4383, 26214, 34952, 65280], [240, 4383, 17476, 34952, 65314], [240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 65416]]),
  ([240, 3840, 4383, 26214, 34952, 61440], [[3840, 4383, 26214, 35064, 61440], [240, 4383, 28518, 34952, 61440], [240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 34952, 65280], [240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 26214, 63624]]),
  ([240, 3840, 4383, 17476, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 34952, 65314], [240, 3840, 4383, 34952, 63078]]),
  ([240, 3840, 4383, 8738, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 34952, 65348], [240, 3840, 4383, 34952, 63078]]),
  ([240, 3840, 4383, 8738, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 65416], [240, 3840, 4383, 26214, 63624]]),
  ([15, 4369, 8738, 17476, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [15, 4369, 26214, 35064, 65280]]),
  ([15, 3840, 4369, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [15, 4369, 26214, 35064, 65280]]),
  ([15, 240, 4369, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 63624]]),
  ([15, 240, 4369, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 12066, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 12066, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [15, 240, 4369, 28518, 63624]]),
  ([15, 240, 4369, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 8738, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 8738, 20292, 63624], [[240, 4383, 8738, 20292, 63624], [15, 240, 4369, 28518, 63624]]),
  ([15, 240, 4369, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [15, 240, 4369, 36744, 63078], [15, 240, 4369, 26214, 65416]]),
  ([15, 240, 4369, 17476, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [15, 240, 4369, 36744, 63078]]),
  ([15, 240, 4369, 8738, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [15, 240, 4369, 36744, 63078]]),
  ([15, 240, 4369, 8738, 17476, 65416], [[240, 4383, 8738, 17476, 65416], [15, 240, 4369, 26214, 65416]]),
  ([15, 240, 4369, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [15, 4369, 26214, 35064, 65280], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 26214, 65416]]),
  ([15, 240, 3840, 4369, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [15, 240, 4369, 36744, 63078], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 3840, 4369, 26214, 63624], [[240, 3840, 4383, 26214, 63624], [15, 240, 4369, 28518, 63624], [15, 240, 4369, 26214, 65416]]),
  ([248, 3840, 4383, 8738, 17476, 61440], [[248, 4383, 12066, 17476, 61440], [248, 4383, 8738, 20292, 61440], [248, 4383, 8738, 17476, 65280], [248, 3840, 4383, 26214, 61440], [248, 3840, 4383, 17476, 61986], [248, 3840, 4383, 8738, 62532]]),
  ([240, 3848, 4383, 8738, 17476, 61440], [[240, 4383, 12074, 17476, 61440], [240, 4383, 8738, 20300, 61440], [240, 4383, 8738, 17476, 65288], [240, 3848, 4383, 26214, 61440], [240, 3848, 4383, 17476, 61986], [240, 3848, 4383, 8738, 62532]]),
  ([240, 3840, 4383, 8746, 17476, 61440], [[240, 4383, 12074, 17476, 61440], [240, 4383, 8746, 20292, 61440], [240, 4383, 8746, 17476, 65280], [240, 3840, 4383, 26222, 61440], [240, 3840, 4383, 17476, 61994], [240, 3840, 4383, 8746, 62532]]),
  ([240, 3840, 4383, 8738, 17484, 61440], [[240, 4383, 12066, 17484, 61440], [240, 4383, 8738, 20300, 61440], [240, 4383, 8738, 17484, 65280], [240, 3840, 4383, 26222, 61440], [240, 3840, 4383, 17484, 61986], [240, 3840, 4383, 8738, 62540]]),
  ([240, 3840, 4383, 8738, 17476, 61448], [[240, 4383, 12066, 17476, 61448], [240, 4383, 8738, 20292, 61448], [240, 4383, 8738, 17476, 65288], [240, 3840, 4383, 26214, 61448], [240, 3840, 4383, 17476, 61994], [240, 3840, 4383, 8738, 62540]]),
  ([8, 240, 4383, 12066, 17476, 61440], [[248, 4383, 12066, 17476, 61440], [240, 4383, 12074, 17476, 61440], [240, 4383, 12066, 17484, 61440], [240, 4383, 12066, 17476, 61448], [8, 240, 4383, 28518, 61440], [8, 240, 4383, 17476, 65314], [8, 240, 4383, 12066, 62532]]),
  ([8, 240, 4383, 8738, 20292, 61440], [[248, 4383, 8738, 20292, 61440], [240, 4383, 8746, 20292, 61440], [240, 4383, 8738, 20300, 61440], [240, 4383, 8738, 20292, 61448], [8, 240, 4383, 28518, 61440], [8, 240, 4383, 20292, 61986], [8, 240, 4383, 8738, 65348]]),
  ([8, 240, 4383, 8738, 17476, 65280], [[248, 4383, 8738, 17476, 65280], [240, 4383, 8746, 17476, 65280], [240, 4383, 8738, 17484, 65280], [240, 4383, 8738, 17476, 65288], [8, 240, 4383, 26214, 65280], [8, 240, 4383, 17476, 65314], [8, 240, 4383, 8738, 65348]]),
  ([8, 240, 3840, 4383, 26214, 61440], [[248, 3840, 4383, 26214, 61440], [240, 3848, 4383, 26214, 61440], [240, 3840, 4383, 26222, 61440], [240, 3840, 4383, 26214, 61448], [8, 240, 4383, 28518, 61440], [8, 240, 4383, 26214, 65280], [8, 240, 3840, 4383, 63078]]),
  ([8, 240, 3840, 4383, 17476, 61986], [[248, 3840, 4383, 17476, 61986], [240, 3848, 4383, 17476, 61986], [240, 3840, 4383, 17484, 61986], [240, 3840, 4383, 17476, 61994], [8, 240, 4383, 20292, 61986], [8, 240, 4383, 17476, 65314], [8, 240, 3840, 4383, 63078]]),
  ([8, 240, 3840, 4383, 8738, 62532], [[248, 3840, 4383, 8738, 62532], [240, 3848, 4383, 8738, 62532], [240, 3840, 4383, 8746, 62532], [240, 3840, 4383, 8738, 62540], [8, 240, 4383, 12066, 62532], [8, 240, 4383, 8738, 65348], [8, 240, 3840, 4383, 63078]]),
  ([4080, 4383, 8738, 17476, 35064, 61440], [[4383, 8738, 17476, 35064, 65520], [4080, 4383, 26214, 35064, 61440], [4080, 4383, 17476, 35064, 61986], [4080, 4383, 8738, 35064, 62532], [4080, 4383, 8738, 17476, 63736]]),
  ([4080, 4383, 8738, 17476, 34952, 61680], [[4383, 8738, 17476, 36856, 61680], [4080, 4383, 26214, 34952, 61680], [4080, 4383, 8738, 17476, 63736]]),
  ([240, 4383, 8738, 17476, 36856, 61440], [[4383, 8738, 17476, 36856, 61680], [240, 4383, 26214, 36856, 61440], [240, 4383, 17476, 36856, 61986], [240, 4383, 8738, 36856, 62532], [240, 4383, 8738, 17476, 65528]]),
  ([240, 4383, 8738, 17476, 34952, 65520], [[4383, 8738, 17476, 35064, 65520], [240, 4383, 26214, 34952, 65520], [240, 4383, 8738, 17476, 65528]]),
  ([240, 4080, 4383, 26214, 34952, 61440], [[4080, 4383, 26214, 35064, 61440], [4080, 4383, 26214, 34952, 61680], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 34952, 65520], [240, 4080, 4383, 34952, 63078], [240, 4080, 4383, 26214, 63624]]),
  ([240, 4080, 4383, 17476, 34952, 61986], [[4080, 4383, 17476, 35064, 61986], [240, 4383, 17476, 36856, 61986], [240, 4080, 4383, 34952, 63078]]),
  ([240, 4080, 4383, 8738, 34952, 62532], [[4080, 4383, 8738, 35064, 62532], [240, 4383, 8738, 36856, 62532], [240, 4080, 4383, 34952, 63078]]),
  ([240, 4080, 4383, 8738, 17476, 63624], [[4080, 4383, 8738, 17476, 63736], [240, 4383, 8738, 17476, 65528], [240, 4080, 4383, 26214, 63624]]),
  ([256, 4383, 8738, 17476, 35064, 61440], [[4383, 8994, 17476, 35064, 61440], [4383, 8738, 17732, 35064, 61440], [4383, 8738, 17476, 35320, 61440], [4383, 8738, 17476, 35064, 61696], [256, 4383, 26214, 35064, 61440]]),
  ([4383, 8738, 12066, 17476, 35064, 61440], [[4383, 12066, 26214, 35064, 61440], [4383, 12066, 17476, 35064, 61986], [4383, 8738, 17476, 35064, 65314]]),
  ([4383, 8738, 17476, 20292, 35064, 61440], [[4383, 20292, 26214, 35064, 61440], [4383, 8738, 20292, 35064, 62532], [4383, 8738, 17476, 35064, 65348]]),
  ([4383, 8738, 17476, 35064, 36856, 61440], [[4383, 26214, 35064, 36856, 61440], [4383, 8738, 17476, 36856, 63736], [4383, 8738, 17476, 35064, 65528]]),
  ([15, 4383, 8738, 17476, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [4352, 4383, 8738, 17476, 35064], [15, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 8738, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65348], [4383, 8738, 17476, 35064, 65528]]),
  ([3840, 4383, 8738, 17476, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [4352, 4383, 8738, 17476, 35064], [3840, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 8738, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65348], [4383, 8738, 17476, 35064, 65528]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_0 : pairs5_0.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_1 : List (List ℕ × List (List ℕ)) := [
  ([4383, 8738, 17476, 35064, 61440, 65280], [[4383, 8738, 17476, 35064, 65280], [4352, 4383, 8738, 17476, 35064], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [4383, 8738, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65348], [4383, 8738, 17476, 35064, 65528]]),
  ([3840, 4096, 4383, 8738, 17476, 35064], [[4383, 7936, 8738, 17476, 35064], [3840, 4383, 12834, 17476, 35064], [3840, 4383, 8738, 21572, 35064], [3840, 4383, 8738, 17476, 39160], [3840, 4096, 4383, 26214, 35064]]),
  ([15, 3840, 4383, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [256, 4383, 26214, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [4383, 26214, 35064, 36856, 61440], [15, 4383, 26214, 35064, 65280], [3840, 4383, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [3840, 4383, 26214, 35064, 63078], [3840, 4383, 26214, 35064, 63736]]),
  ([3840, 4383, 8738, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [256, 4383, 26214, 35064, 61440], [4383, 12066, 26214, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [4383, 26214, 35064, 36856, 61440], [3840, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [3840, 4383, 26214, 35064, 61986], [3840, 4383, 26214, 35064, 63078], [3840, 4383, 26214, 35064, 63736]]),
  ([3840, 4383, 17476, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [256, 4383, 26214, 35064, 61440], [4383, 20292, 26214, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [4383, 26214, 35064, 36856, 61440], [3840, 4383, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [3840, 4383, 26214, 35064, 62532], [3840, 4383, 26214, 35064, 63078], [3840, 4383, 26214, 35064, 63736]]),
  ([3840, 4383, 8738, 17476, 35064, 61986], [[4383, 12066, 17476, 35064, 61986], [4383, 8738, 17476, 35064, 65314], [3840, 4383, 26214, 35064, 61986]]),
  ([3840, 4383, 8738, 17476, 35064, 62532], [[4383, 8738, 20292, 35064, 62532], [4383, 8738, 17476, 35064, 65348], [3840, 4383, 26214, 35064, 62532]]),
  ([3840, 4383, 8738, 17476, 35064, 63736], [[4383, 8738, 17476, 36856, 63736], [4383, 8738, 17476, 35064, 65528], [3840, 4383, 26214, 35064, 63736]]),
  ([3840, 4383, 8738, 17476, 35064, 61680], [[4383, 12066, 17476, 35064, 61680], [4383, 8738, 20292, 35064, 61680], [4383, 8738, 17476, 36856, 61680], [4383, 8738, 17476, 35064, 65520], [3840, 4383, 26214, 35064, 61680]]),
  ([240, 4383, 12066, 17476, 35064, 61440], [[4383, 12066, 17476, 35064, 61680], [240, 4383, 28518, 35064, 61440], [240, 4383, 17476, 35064, 65314], [240, 4383, 12066, 35064, 62532], [240, 4383, 12066, 17476, 63736]]),
  ([240, 4383, 8738, 20292, 35064, 61440], [[4383, 8738, 20292, 35064, 61680], [240, 4383, 28518, 35064, 61440], [240, 4383, 20292, 35064, 61986], [240, 4383, 8738, 35064, 65348], [240, 4383, 8738, 20292, 63736]]),
  ([240, 4383, 8738, 17476, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 35064, 65520], [4352, 4383, 8738, 17476, 35064], [240, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [240, 4383, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65314], [240, 4383, 8738, 35064, 65348], [4383, 8738, 17476, 35064, 65348], [240, 4383, 8738, 17476, 65528], [4383, 8738, 17476, 35064, 65528]]),
  ([240, 3840, 4383, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [4080, 4383, 26214, 35064, 61440], [3840, 4383, 26214, 35064, 61680], [256, 4383, 26214, 35064, 61440], [240, 4383, 28518, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [240, 4383, 26214, 36856, 61440], [4383, 26214, 35064, 36856, 61440], [240, 4383, 26214, 35064, 65280], [3840, 4383, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [240, 3840, 4383, 35064, 63078], [3840, 4383, 26214, 35064, 63078], [240, 3840, 4383, 26214, 63736], [3840, 4383, 26214, 35064, 63736]]),
  ([240, 3840, 4383, 17476, 35064, 61986], [[4080, 4383, 17476, 35064, 61986], [240, 4383, 20292, 35064, 61986], [240, 4383, 17476, 36856, 61986], [240, 4383, 17476, 35064, 65314], [240, 3840, 4383, 35064, 63078]]),
  ([240, 3840, 4383, 8738, 35064, 62532], [[4080, 4383, 8738, 35064, 62532], [240, 4383, 12066, 35064, 62532], [240, 4383, 8738, 36856, 62532], [240, 4383, 8738, 35064, 65348], [240, 3840, 4383, 35064, 63078]]),
  ([240, 3840, 4383, 8738, 17476, 63736], [[4080, 4383, 8738, 17476, 63736], [240, 4383, 12066, 17476, 63736], [240, 4383, 8738, 20292, 63736], [240, 4383, 8738, 17476, 65528], [240, 3840, 4383, 26214, 63736]]),
  ([4383, 8738, 17476, 35064, 36744, 61440], [[4383, 26214, 35064, 36744, 61440], [4383, 8738, 17476, 35064, 65416]]),
  ([4383, 8738, 17476, 34952, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [4352, 4383, 8738, 17476, 35064], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [4383, 8738, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65348], [4383, 8738, 17476, 35064, 65416], [4383, 8738, 17476, 35064, 65528]]),
  ([3840, 4383, 26214, 34952, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [256, 4383, 26214, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [4383, 26214, 35064, 36744, 61440], [4383, 26214, 35064, 36856, 61440], [3840, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [3840, 4383, 26214, 35064, 63078], [3840, 4383, 26214, 35064, 63624], [3840, 4383, 26214, 35064, 63736]]),
  ([3840, 4383, 8738, 17476, 35064, 63624], [[4383, 8738, 17476, 35064, 65416], [3840, 4383, 26214, 35064, 63624]]),
  ([240, 4383, 12066, 17476, 34952, 61680], [[4383, 12066, 17476, 35064, 61680], [240, 4383, 28518, 34952, 61680], [240, 4383, 12066, 17476, 63736]]),
  ([240, 4383, 8738, 20292, 34952, 61680], [[4383, 8738, 20292, 35064, 61680], [240, 4383, 28518, 34952, 61680], [240, 4383, 8738, 20292, 63736]]),
  ([240, 4383, 8738, 17476, 36744, 61680], [[4383, 8738, 17476, 36856, 61680], [240, 4383, 26214, 36744, 61680], [240, 4383, 8738, 17476, 65528]]),
  ([240, 3840, 4383, 26214, 34952, 61680], [[4080, 4383, 26214, 34952, 61680], [3840, 4383, 26214, 35064, 61680], [240, 4383, 28518, 34952, 61680], [240, 4383, 26214, 36744, 61680], [240, 4383, 26214, 34952, 65520], [240, 3840, 4383, 26214, 63736]]),
  ([496, 4383, 8738, 17476, 34952, 61440], [[4383, 8738, 17476, 35320, 61440], [496, 4383, 26214, 34952, 61440], [496, 4383, 17476, 34952, 61986], [496, 4383, 8738, 34952, 62532], [496, 4383, 8738, 17476, 63624]]),
  ([240, 4383, 8994, 17476, 34952, 61440], [[4383, 8994, 17476, 35064, 61440], [240, 4383, 26470, 34952, 61440], [240, 4383, 17476, 34952, 62242], [240, 4383, 8994, 34952, 62532], [240, 4383, 8994, 17476, 63624]]),
  ([240, 4383, 8738, 17732, 34952, 61440], [[4383, 8738, 17732, 35064, 61440], [240, 4383, 26470, 34952, 61440], [240, 4383, 17732, 34952, 61986], [240, 4383, 8738, 34952, 62788], [240, 4383, 8738, 17732, 63624]]),
  ([240, 4383, 8738, 17476, 35208, 61440], [[4383, 8738, 17476, 35320, 61440], [240, 4383, 26214, 35208, 61440], [240, 4383, 17476, 35208, 61986], [240, 4383, 8738, 35208, 62532], [240, 4383, 8738, 17476, 63880]]),
  ([240, 4383, 8738, 17476, 34952, 61696], [[4383, 8738, 17476, 35064, 61696], [240, 4383, 26214, 34952, 61696], [240, 4383, 17476, 34952, 62242], [240, 4383, 8738, 34952, 62788], [240, 4383, 8738, 17476, 63880]]),
  ([240, 256, 4383, 26214, 34952, 61440], [[496, 4383, 26214, 34952, 61440], [256, 4383, 26214, 35064, 61440], [240, 4383, 26470, 34952, 61440], [240, 4383, 26214, 35208, 61440], [240, 4383, 26214, 34952, 61696], [240, 256, 4383, 34952, 63078], [240, 256, 4383, 26214, 63624]]),
  ([240, 256, 4383, 17476, 34952, 61986], [[496, 4383, 17476, 34952, 61986], [240, 4383, 17732, 34952, 61986], [240, 4383, 17476, 35208, 61986], [240, 4383, 17476, 34952, 62242], [240, 256, 4383, 34952, 63078]]),
  ([240, 256, 4383, 8738, 34952, 62532], [[496, 4383, 8738, 34952, 62532], [240, 4383, 8994, 34952, 62532], [240, 4383, 8738, 35208, 62532], [240, 4383, 8738, 34952, 62788], [240, 256, 4383, 34952, 63078]]),
  ([240, 256, 4383, 8738, 17476, 63624], [[496, 4383, 8738, 17476, 63624], [240, 4383, 8994, 17476, 63624], [240, 4383, 8738, 17732, 63624], [240, 4383, 8738, 17476, 63880], [240, 256, 4383, 26214, 63624]]),
  ([240, 4096, 4383, 12066, 17476, 34952], [[4336, 4383, 12066, 17476, 34952], [240, 4383, 16162, 17476, 34952], [240, 4383, 12066, 21572, 34952], [240, 4383, 12066, 17476, 39048], [240, 4096, 4383, 28518, 34952]]),
  ([15, 240, 4383, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 61422, 61440], [15, 240, 4383, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [15, 240, 4383, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4383, 12066, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 44970, 61440], [240, 4383, 28518, 34952, 65314], [240, 4383, 28518, 61422, 61440], [240, 4383, 12066, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 12066, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4383, 17476, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 52428, 61440], [240, 4383, 28518, 34952, 62532], [240, 4383, 28518, 61422, 61440], [240, 4383, 17476, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 17476, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4383, 12066, 17476, 44970, 61440], [[240, 4383, 28518, 44970, 61440], [240, 4383, 17476, 44970, 65314], [240, 4383, 12066, 44970, 62532], [240, 4383, 12066, 17476, 65450]]),
  ([15, 240, 4383, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [15, 240, 4383, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4383, 12066, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 28518, 34952, 65314], [240, 4383, 17476, 44970, 65314], [240, 4383, 17476, 52428, 65314], [240, 4383, 12066, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 12066, 17476, 65450], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4383, 17476, 34952, 61440, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [240, 4383, 34952, 62532, 65314], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 63624, 65314], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4383, 12066, 17476, 52428, 61440], [[240, 4383, 28518, 52428, 61440], [240, 4383, 17476, 52428, 65314], [240, 4383, 12066, 52428, 62532], [240, 4383, 12066, 17476, 64716]]),
  ([15, 240, 4383, 12066, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [8, 240, 4383, 12066, 62532], [240, 4383, 12066, 44970, 62532], [15, 240, 4383, 34952, 65382], [240, 4383, 12066, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 62532, 64716]]),
  ([240, 4383, 12066, 17476, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [8, 240, 4383, 12066, 62532], [240, 4383, 28518, 34952, 62532], [240, 4383, 12066, 44970, 62532], [240, 4383, 12066, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 52428, 62532], [240, 4383, 12066, 17476, 64716], [240, 4383, 12066, 62532, 64716]]),
  ([240, 4383, 12066, 34952, 61440, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [8, 240, 4383, 12066, 62532], [240, 4383, 12066, 44970, 62532], [240, 4383, 34952, 62532, 65314], [240, 4383, 12066, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 62532, 63624], [240, 4383, 12066, 62532, 64716]]),
  ([15, 240, 4383, 12066, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4104, 4383, 12066, 17476], [15, 240, 4383, 28518, 63624], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4383, 12066, 17476, 34952, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4104, 4383, 12066, 17476], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4383, 12066, 17476, 61440, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4104, 4383, 12066, 17476], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 28518, 61440, 63624], [240, 4383, 17476, 63624, 65314], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 62532, 63624], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4383, 12066, 20292, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 20292, 34952, 65314], [240, 4383, 12066, 34952, 65348], [240, 4383, 12066, 20292, 63624]]),
  ([240, 4383, 12066, 17476, 36744, 61440], [[240, 4383, 28518, 36744, 61440], [240, 4383, 17476, 36744, 65314], [240, 4383, 12066, 36744, 62532], [240, 4383, 12066, 17476, 65416]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_1 : pairs5_1.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_2 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 12066, 17476, 34952, 65280], [[240, 4383, 28518, 34952, 65280], [240, 4383, 17476, 34952, 65314], [240, 4383, 12066, 34952, 65348], [240, 4383, 12066, 17476, 65416]]),
  ([240, 3840, 4383, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [240, 4383, 28518, 36744, 61440], [240, 4383, 28518, 34952, 65280], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 61422, 61440], [240, 3840, 4383, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 3840, 4383, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 3840, 4383, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [240, 4383, 20292, 34952, 65314], [240, 4383, 17476, 36744, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [240, 3840, 4383, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 65314, 65450]]),
  ([240, 3840, 4383, 12066, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [240, 4383, 12066, 36744, 62532], [240, 4383, 12066, 34952, 65348], [8, 240, 4383, 12066, 62532], [240, 4383, 12066, 44970, 62532], [240, 3840, 4383, 34952, 65382], [240, 4383, 12066, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 62532, 64716]]),
  ([240, 3840, 4383, 12066, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4383, 12066, 20292, 63624], [240, 4383, 12066, 17476, 65416], [240, 4104, 4383, 12066, 17476], [240, 3840, 4383, 28518, 63624], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4383, 12066, 26214, 34952, 61440], [[4383, 12066, 26214, 35064, 61440], [240, 4383, 28518, 34952, 61440], [240, 4383, 26214, 44970, 61440], [240, 4383, 26214, 34952, 65314], [240, 4383, 12066, 34952, 63078], [240, 4383, 12066, 26214, 63624]]),
  ([240, 4383, 12066, 17476, 43690, 61440], [[240, 4383, 28518, 43690, 61440], [240, 4383, 17476, 43690, 65314], [240, 4383, 12066, 43690, 62532], [240, 4383, 12066, 17476, 64170]]),
  ([240, 4383, 12066, 17476, 34952, 61986], [[4383, 12066, 17476, 35064, 61986], [240, 4383, 28518, 34952, 61986], [240, 4383, 17476, 44970, 61986], [240, 4383, 17476, 34952, 65314], [240, 4383, 12066, 34952, 63078], [240, 4383, 12066, 17476, 64170]]),
  ([240, 4383, 8738, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 43690, 61440], [240, 4383, 28518, 34952, 61986], [240, 4383, 28518, 61422, 61440], [240, 4383, 8738, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 8738, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4383, 8738, 17476, 44970, 61440], [[240, 4383, 26214, 44970, 61440], [240, 4383, 17476, 44970, 61986], [240, 4383, 8738, 44970, 62532], [240, 4383, 8738, 17476, 65450]]),
  ([240, 4383, 8738, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 26214, 34952, 65314], [240, 4383, 17476, 43690, 65314], [240, 4383, 17476, 52428, 65314], [240, 4383, 8738, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 8738, 17476, 65450], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4383, 8738, 12066, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [8, 240, 4383, 12066, 62532], [240, 4383, 12066, 43690, 62532], [240, 4383, 12066, 34952, 63078], [240, 4383, 8738, 44970, 62532], [240, 4383, 12066, 44970, 62532], [240, 4383, 8738, 34952, 65382], [240, 4383, 12066, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 62532, 64716]]),
  ([240, 4383, 8738, 12066, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4104, 4383, 12066, 17476], [240, 4383, 12066, 26214, 63624], [240, 4383, 12066, 17476, 64170], [240, 4383, 8738, 28518, 63624], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 8738, 17476, 65450], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4096, 4383, 8738, 20292, 34952], [[4336, 4383, 8738, 20292, 34952], [240, 4383, 12834, 20292, 34952], [240, 4383, 8738, 24388, 34952], [240, 4383, 8738, 20292, 39048], [240, 4096, 4383, 28518, 34952]]),
  ([240, 4383, 20292, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 53196, 61440], [240, 4383, 28518, 34952, 65348], [240, 4383, 28518, 61422, 61440], [240, 4383, 20292, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 20292, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4383, 8738, 20292, 43690, 61440], [[240, 4383, 28518, 43690, 61440], [240, 4383, 20292, 43690, 61986], [240, 4383, 8738, 43690, 65348], [240, 4383, 8738, 20292, 64170]]),
  ([15, 240, 4383, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [8, 240, 4383, 20292, 61986], [240, 4383, 20292, 53196, 61986], [15, 240, 4383, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 20292, 61986, 64170]]),
  ([240, 4383, 8738, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [8, 240, 4383, 20292, 61986], [240, 4383, 28518, 34952, 61986], [240, 4383, 20292, 43690, 61986], [240, 4383, 20292, 53196, 61986], [240, 4383, 8738, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 8738, 20292, 64170], [240, 4383, 20292, 61986, 64170]]),
  ([240, 4383, 20292, 34952, 61440, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [8, 240, 4383, 20292, 61986], [240, 4383, 20292, 53196, 61986], [240, 4383, 34952, 61986, 65348], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 20292, 61986, 63624], [240, 4383, 20292, 61986, 64170]]),
  ([240, 4383, 8738, 20292, 53196, 61440], [[240, 4383, 28518, 53196, 61440], [240, 4383, 20292, 53196, 61986], [240, 4383, 8738, 53196, 65348], [240, 4383, 8738, 20292, 65484]]),
  ([15, 240, 4383, 8738, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [15, 240, 4383, 34952, 65382], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 65348, 65484]]),
  ([240, 4383, 8738, 20292, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 28518, 34952, 65348], [240, 4383, 8738, 43690, 65348], [240, 4383, 8738, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 53196, 65348], [240, 4383, 8738, 20292, 65484], [240, 4383, 8738, 65348, 65484]]),
  ([240, 4383, 8738, 34952, 61440, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [240, 4383, 34952, 61986, 65348], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 63624, 65348], [240, 4383, 8738, 65348, 65484]]),
  ([15, 240, 4383, 8738, 20292, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4104, 4383, 8738, 20292], [15, 240, 4383, 28518, 63624], [240, 4383, 8738, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 20292, 65484]]),
  ([240, 4383, 8738, 20292, 34952, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4104, 4383, 8738, 20292], [240, 4383, 8738, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 20292, 65484]]),
  ([240, 4383, 8738, 20292, 61440, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4104, 4383, 8738, 20292], [240, 4383, 8738, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 28518, 61440, 63624], [240, 4383, 20292, 61986, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 63624, 65348], [240, 4383, 8738, 20292, 65484]]),
  ([240, 4383, 8738, 20292, 36744, 61440], [[240, 4383, 28518, 36744, 61440], [240, 4383, 20292, 36744, 61986], [240, 4383, 8738, 36744, 65348], [240, 4383, 8738, 20292, 65416]]),
  ([240, 4383, 8738, 20292, 34952, 65280], [[240, 4383, 28518, 34952, 65280], [240, 4383, 20292, 34952, 65314], [240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 65416]]),
  ([240, 3840, 4383, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [240, 4383, 20292, 36744, 61986], [240, 4383, 20292, 34952, 65314], [8, 240, 4383, 20292, 61986], [240, 4383, 20292, 53196, 61986], [240, 3840, 4383, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 20292, 61986, 64170]]),
  ([240, 3840, 4383, 8738, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [240, 4383, 12066, 34952, 65348], [240, 4383, 8738, 36744, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [240, 3840, 4383, 34952, 65382], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 65348, 65484]]),
  ([240, 3840, 4383, 8738, 20292, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4383, 12066, 20292, 63624], [240, 4383, 8738, 20292, 65416], [240, 4104, 4383, 8738, 20292], [240, 3840, 4383, 28518, 63624], [240, 4383, 8738, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 20292, 65484]]),
  ([240, 4383, 20292, 26214, 34952, 61440], [[4383, 20292, 26214, 35064, 61440], [240, 4383, 28518, 34952, 61440], [240, 4383, 26214, 53196, 61440], [240, 4383, 26214, 34952, 65348], [240, 4383, 20292, 34952, 63078], [240, 4383, 20292, 26214, 63624]]),
  ([240, 4383, 17476, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [8, 240, 4383, 20292, 61986], [240, 4383, 20292, 52428, 61986], [240, 4383, 20292, 34952, 63078], [240, 4383, 17476, 53196, 61986], [240, 4383, 20292, 53196, 61986], [240, 4383, 17476, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 20292, 61986, 64170]]),
  ([240, 4383, 8738, 20292, 52428, 61440], [[240, 4383, 28518, 52428, 61440], [240, 4383, 20292, 52428, 61986], [240, 4383, 8738, 52428, 65348], [240, 4383, 8738, 20292, 64716]]),
  ([240, 4383, 8738, 20292, 34952, 62532], [[4383, 8738, 20292, 35064, 62532], [240, 4383, 28518, 34952, 62532], [240, 4383, 20292, 34952, 63078], [240, 4383, 8738, 53196, 62532], [240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 64716]]),
  ([240, 4383, 8738, 17476, 53196, 61440], [[240, 4383, 26214, 53196, 61440], [240, 4383, 17476, 53196, 61986], [240, 4383, 8738, 53196, 62532], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4383, 8738, 17476, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [4383, 8738, 17476, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 26214, 34952, 65348], [240, 4383, 8738, 43690, 65348], [240, 4383, 8738, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 52428, 65348], [240, 4383, 8738, 17476, 65484], [240, 4383, 8738, 65348, 65484]]),
  ([240, 4383, 8738, 17476, 20292, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4104, 4383, 8738, 20292], [240, 4383, 20292, 26214, 63624], [240, 4383, 8738, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 20292, 64716], [240, 4383, 8738, 17476, 65484], [240, 4383, 8738, 20292, 65484]]),
  ([240, 264, 4383, 8738, 17476, 61440], [[504, 4383, 8738, 17476, 61440], [240, 4383, 9002, 17476, 61440], [240, 4383, 8738, 17740, 61440], [240, 4383, 8738, 17476, 61704], [240, 264, 4383, 26214, 61440], [240, 264, 4383, 17476, 61986], [240, 264, 4383, 8738, 62532]]),
  ([240, 4096, 4383, 8738, 17476, 36744], [[4336, 4383, 8738, 17476, 36744], [240, 4383, 12834, 17476, 36744], [240, 4383, 8738, 21572, 36744], [240, 4383, 8738, 17476, 40840], [240, 4096, 4383, 26214, 36744]]),
  ([15, 240, 4383, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 61422, 61440], [15, 240, 4383, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 36744, 61440, 63078], [15, 240, 4383, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([240, 4383, 8738, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 44970, 61440], [240, 4383, 26214, 36744, 61986], [240, 4383, 26214, 61422, 61440], [240, 4383, 8738, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 8738, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([240, 4383, 17476, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 53196, 61440], [240, 4383, 26214, 36744, 62532], [240, 4383, 26214, 61422, 61440], [240, 4383, 17476, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([15, 240, 4383, 17476, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 264, 4383, 17476, 61986], [240, 4383, 17476, 53196, 61986], [15, 240, 4383, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 17476, 61986, 65450]]),
  ([240, 4383, 8738, 17476, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 264, 4383, 17476, 61986], [240, 4383, 26214, 36744, 61986], [240, 4383, 17476, 44970, 61986], [240, 4383, 17476, 53196, 61986], [240, 4383, 8738, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 8738, 17476, 65450], [240, 4383, 17476, 61986, 65450]]),
  ([240, 4383, 17476, 36744, 61440, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 264, 4383, 17476, 61986], [240, 4383, 17476, 53196, 61986], [240, 4383, 36744, 61986, 62532], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 17476, 61986, 65416], [240, 4383, 17476, 61986, 65450]]),
  ([15, 240, 4383, 8738, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 264, 4383, 8738, 62532], [240, 4383, 8738, 44970, 62532], [15, 240, 4383, 36744, 63078], [240, 4383, 8738, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 62532, 65484]]),
  ([240, 4383, 8738, 17476, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 264, 4383, 8738, 62532], [240, 4383, 26214, 36744, 62532], [240, 4383, 8738, 44970, 62532], [240, 4383, 8738, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 53196, 62532], [240, 4383, 8738, 17476, 65484], [240, 4383, 8738, 62532, 65484]]),
  ([240, 4383, 8738, 36744, 61440, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 264, 4383, 8738, 62532], [240, 4383, 8738, 44970, 62532], [240, 4383, 36744, 61986, 62532], [240, 4383, 8738, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 62532, 65416], [240, 4383, 8738, 62532, 65484]]),
  ([15, 240, 4383, 8738, 17476, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [15, 240, 4383, 26214, 65416], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_2 : pairs5_2.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_3 : List (List ℕ × List (List ℕ)) := [
  ([240, 4383, 8738, 17476, 36744, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4383, 8738, 17476, 61440, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 61440, 65416], [240, 4383, 17476, 61986, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 62532, 65416], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4383, 8738, 17476, 36744, 65280], [[240, 4383, 26214, 36744, 65280], [240, 4383, 17476, 36744, 65314], [240, 4383, 8738, 36744, 65348], [240, 4383, 8738, 17476, 65416]]),
  ([240, 3840, 4383, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 4383, 28518, 36744, 61440], [240, 4383, 26214, 36744, 65280], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 61422, 61440], [240, 3840, 4383, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 3840, 4383, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([240, 3840, 4383, 17476, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 4383, 20292, 36744, 61986], [240, 4383, 17476, 36744, 65314], [240, 264, 4383, 17476, 61986], [240, 4383, 17476, 53196, 61986], [240, 3840, 4383, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 17476, 61986, 65450]]),
  ([240, 3840, 4383, 8738, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 4383, 12066, 36744, 62532], [240, 4383, 8738, 36744, 65348], [240, 264, 4383, 8738, 62532], [240, 4383, 8738, 44970, 62532], [240, 3840, 4383, 36744, 63078], [240, 4383, 8738, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 62532, 65484]]),
  ([240, 3840, 4383, 8738, 17476, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4383, 12066, 17476, 65416], [240, 4383, 8738, 20292, 65416], [240, 4360, 4383, 8738, 17476], [240, 3840, 4383, 26214, 65416], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4383, 26214, 34952, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [4383, 26214, 35064, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 61422, 61440], [240, 4383, 26214, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 26214, 36744, 63624], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([240, 4383, 17476, 34952, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 264, 4383, 17476, 61986], [240, 4383, 17476, 53196, 61986], [240, 4383, 17476, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 17476, 61986, 65450]]),
  ([240, 4383, 8738, 34952, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 264, 4383, 8738, 62532], [240, 4383, 8738, 44970, 62532], [240, 4383, 8738, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 62532, 65484]]),
  ([240, 4383, 8738, 17476, 36744, 63624], [[240, 4383, 26214, 36744, 63624], [240, 4383, 8738, 17476, 65416]]),
  ([240, 4383, 8738, 17476, 34952, 65416], [[240, 4383, 8738, 17476, 65416], [4383, 8738, 17476, 35064, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4352, 4383, 8738, 17476, 34952], [[4383, 4592, 8738, 17476, 34952], [4352, 4383, 8738, 17476, 35064], [240, 4383, 13090, 17476, 34952], [240, 4383, 8738, 21828, 34952], [240, 4383, 8738, 17476, 39304], [240, 4352, 4383, 26214, 34952]]),
  ([15, 240, 4383, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [15, 4383, 26214, 35064, 65280], [240, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [240, 4383, 26214, 34952, 65520], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 61166, 65280], [15, 240, 4383, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 65280, 65382], [15, 240, 4383, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 4383, 8738, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [240, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [240, 4383, 26214, 34952, 65520], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 43690, 65280], [240, 4383, 26214, 34952, 65314], [240, 4383, 26214, 61166, 65280], [240, 4383, 8738, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 4383, 8738, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 4383, 17476, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [240, 4383, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [240, 4383, 26214, 34952, 65520], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 52428, 65280], [240, 4383, 26214, 34952, 65348], [240, 4383, 26214, 61166, 65280], [240, 4383, 17476, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 4383, 8738, 17476, 43690, 65280], [[240, 4383, 26214, 43690, 65280], [240, 4383, 17476, 43690, 65314], [240, 4383, 8738, 43690, 65348], [240, 4383, 8738, 17476, 65450]]),
  ([240, 4383, 17476, 34952, 65280, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [240, 4383, 34952, 65314, 65348], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 65314, 65416], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4383, 8738, 17476, 52428, 65280], [[240, 4383, 26214, 52428, 65280], [240, 4383, 17476, 52428, 65314], [240, 4383, 8738, 52428, 65348], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4383, 8738, 34952, 65280, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [240, 4383, 34952, 65314, 65348], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 65348, 65416], [240, 4383, 8738, 65348, 65484]]),
  ([240, 4383, 8738, 17476, 65280, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 65280, 65416], [240, 4383, 17476, 65314, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 65348, 65416], [240, 4383, 8738, 17476, 65484]]),
  ([240, 3840, 4383, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [240, 4383, 26214, 35064, 65280], [3840, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [240, 4383, 26214, 34952, 65520], [240, 4383, 28518, 34952, 65280], [240, 4383, 26214, 36744, 65280], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 61166, 65280], [240, 3840, 4383, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 3840, 4383, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 4383, 26214, 34952, 61440, 65280], [[240, 4383, 26214, 34952, 65280], [240, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [240, 4383, 26214, 34952, 65520], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 61166, 65280], [240, 4383, 34952, 63078, 65280], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 65280, 65382], [240, 4383, 26214, 63624, 65280], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 61440, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 4383, 17476, 34952, 61986, 65280], [[240, 4383, 34952, 63078, 65280], [240, 4383, 34952, 61986, 65348], [240, 4383, 17476, 61986, 65416], [240, 4383, 17476, 34952, 65314]]),
  ([240, 4383, 8738, 34952, 62532, 65280], [[240, 4383, 34952, 63078, 65280], [240, 4383, 34952, 62532, 65314], [240, 4383, 8738, 62532, 65416], [240, 4383, 8738, 34952, 65348]]),
  ([240, 4383, 8738, 17476, 63624, 65280], [[240, 4383, 26214, 63624, 65280], [240, 4383, 17476, 63624, 65314], [240, 4383, 8738, 63624, 65348], [240, 4383, 8738, 17476, 65416]]),
  ([3840, 4336, 4383, 8738, 17476, 34952], [[4336, 4383, 12066, 17476, 34952], [4336, 4383, 8738, 20292, 34952], [4336, 4383, 8738, 17476, 36744], [3840, 4383, 8738, 17476, 39160], [3840, 4336, 4383, 26214, 34952]]),
  ([240, 4383, 7936, 8738, 17476, 34952], [[4383, 7936, 8738, 17476, 35064], [240, 4383, 16162, 17476, 34952], [240, 4383, 8738, 24388, 34952], [240, 4383, 8738, 17476, 40840], [240, 4383, 7936, 26214, 34952]]),
  ([240, 3840, 4383, 12834, 17476, 34952], [[3840, 4383, 12834, 17476, 35064], [240, 4383, 16162, 17476, 34952], [240, 4383, 12834, 20292, 34952], [240, 4383, 12834, 17476, 36744], [240, 3840, 4383, 30310, 34952]]),
  ([240, 3840, 4383, 8738, 21572, 34952], [[3840, 4383, 8738, 21572, 35064], [240, 4383, 12066, 21572, 34952], [240, 4383, 8738, 24388, 34952], [240, 4383, 8738, 21572, 36744], [240, 3840, 4383, 30310, 34952]]),
  ([240, 3840, 4383, 8738, 17476, 39048], [[3840, 4383, 8738, 17476, 39160], [240, 4383, 12066, 17476, 39048], [240, 4383, 8738, 20292, 39048], [240, 4383, 8738, 17476, 40840], [240, 3840, 4383, 26214, 39048]]),
  ([240, 3840, 4096, 4383, 26214, 34952], [[3840, 4336, 4383, 26214, 34952], [3840, 4096, 4383, 26214, 35064], [240, 4383, 7936, 26214, 34952], [240, 4096, 4383, 28518, 34952], [240, 4096, 4383, 26214, 36744], [240, 3840, 4383, 30310, 34952], [240, 3840, 4383, 26214, 39048]]),
  ([240, 4383, 26214, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 61166, 61440], [240, 4383, 28518, 34952, 63078], [240, 4383, 26214, 61422, 61440], [240, 4383, 28518, 61422, 61440], [240, 4383, 26214, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 26214, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 3840, 4383, 26214, 61166, 61440], [[240, 4383, 28518, 61166, 61440], [240, 4383, 26214, 61422, 61440], [240, 4383, 26214, 61166, 65280], [240, 3840, 4383, 61166, 63078], [240, 3840, 4383, 26214, 65262]]),
  ([15, 240, 3840, 4383, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [15, 240, 4383, 36744, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [15, 240, 4383, 34952, 65382], [240, 3840, 4383, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 26214, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [3840, 4383, 26214, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 4383, 28518, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 3840, 4383, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 61166, 63078], [240, 3840, 4383, 26214, 65262], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 34952, 61440, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4383, 34952, 63078, 65280], [240, 3840, 4383, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 63078, 63624], [240, 3840, 4383, 63078, 65262]]),
  ([15, 240, 3840, 4383, 26214, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [15, 240, 4383, 28518, 63624], [240, 3840, 4383, 28518, 63624], [240, 4383, 26214, 28518, 63624], [15, 240, 4383, 26214, 65416], [240, 3840, 4383, 26214, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 26214, 65262]]),
  ([240, 3840, 4383, 26214, 34952, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [3840, 4383, 26214, 35064, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [240, 3840, 4383, 28518, 63624], [240, 4383, 26214, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 26214, 36744, 63624], [240, 3840, 4383, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 26214, 65262]]),
  ([240, 3840, 4383, 26214, 61440, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [240, 3840, 4383, 28518, 63624], [240, 4383, 26214, 28518, 63624], [240, 4383, 28518, 61440, 63624], [240, 4383, 26214, 63624, 65280], [240, 3840, 4383, 26214, 65416], [240, 4383, 26214, 61440, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 63078, 63624], [240, 3840, 4383, 26214, 65262]]),
  ([240, 3840, 4383, 26214, 43690, 61440], [[240, 4383, 28518, 43690, 61440], [240, 4383, 26214, 44970, 61440], [240, 4383, 26214, 43690, 65280], [240, 3840, 4383, 43690, 63078], [240, 3840, 4383, 26214, 64170]]),
  ([240, 3840, 4383, 26214, 34952, 61986], [[3840, 4383, 26214, 35064, 61986], [240, 4383, 28518, 34952, 61986], [240, 4383, 26214, 36744, 61986], [240, 4383, 26214, 34952, 65314], [240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 26214, 64170]]),
  ([240, 3840, 4383, 8738, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 4383, 12066, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 8738, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 3840, 4383, 34952, 65382], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 43690, 63078], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 8738, 26214, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [240, 4383, 12066, 26214, 63624], [240, 3840, 4383, 28518, 63624], [240, 4383, 8738, 28518, 63624], [240, 4383, 26214, 28518, 63624], [240, 3840, 4383, 26214, 65416], [240, 4383, 8738, 26214, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 26214, 64170], [240, 3840, 4383, 26214, 65262]]),
  ([240, 3840, 4383, 26214, 52428, 61440], [[240, 4383, 28518, 52428, 61440], [240, 4383, 26214, 53196, 61440], [240, 4383, 26214, 52428, 65280], [240, 3840, 4383, 52428, 63078], [240, 3840, 4383, 26214, 64716]]),
  ([240, 3840, 4383, 26214, 34952, 62532], [[3840, 4383, 26214, 35064, 62532], [240, 4383, 28518, 34952, 62532], [240, 4383, 26214, 36744, 62532], [240, 4383, 26214, 34952, 65348], [240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 26214, 64716]]),
  ([240, 3840, 4383, 17476, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 4383, 20292, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 3840, 4383, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 52428, 63078], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 17476, 26214, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [240, 4383, 20292, 26214, 63624], [240, 3840, 4383, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 26214, 28518, 63624], [240, 3840, 4383, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 26214, 64716], [240, 3840, 4383, 26214, 65262]]),
  ([240, 3840, 4383, 17476, 43690, 61986], [[240, 4383, 20292, 43690, 61986], [240, 4383, 17476, 44970, 61986], [240, 4383, 17476, 43690, 65314], [240, 3840, 4383, 43690, 63078]]),
  ([240, 3840, 4383, 8738, 43690, 62532], [[240, 4383, 12066, 43690, 62532], [240, 4383, 8738, 44970, 62532], [240, 4383, 8738, 43690, 65348], [240, 3840, 4383, 43690, 63078]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_3 : pairs5_3.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_4 : List (List ℕ × List (List ℕ)) := [
  ([240, 3840, 4383, 8738, 17476, 64170], [[240, 4383, 12066, 17476, 64170], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 17476, 65450], [240, 3840, 4383, 26214, 64170]]),
  ([240, 4383, 17476, 34952, 61986, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [240, 4383, 34952, 63078, 65314], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 64170, 65314], [240, 4383, 17476, 61986, 65450], [240, 4383, 17476, 65314, 65450]]),
  ([240, 3840, 4383, 17476, 52428, 61986], [[240, 4383, 20292, 52428, 61986], [240, 4383, 17476, 53196, 61986], [240, 4383, 17476, 52428, 65314], [240, 3840, 4383, 52428, 63078]]),
  ([240, 3840, 4383, 34952, 61986, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 34952, 63078, 65314], [240, 3840, 4383, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 63078, 64170], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 17476, 61986, 64170], [[240, 4383, 20292, 61986, 64170], [240, 4383, 17476, 64170, 65314], [240, 4383, 17476, 61986, 65450], [240, 3840, 4383, 63078, 64170]]),
  ([240, 3840, 4383, 34952, 61986, 62532], [[240, 4383, 36744, 61986, 62532], [240, 4383, 34952, 62532, 65314], [240, 4383, 34952, 61986, 65348], [240, 3840, 4383, 34952, 63078]]),
  ([240, 3840, 4383, 17476, 61986, 63624], [[240, 4383, 20292, 61986, 63624], [240, 4383, 17476, 63624, 65314], [240, 4383, 17476, 61986, 65416], [240, 3840, 4383, 63078, 63624]]),
  ([240, 3840, 4383, 8738, 52428, 62532], [[240, 4383, 12066, 52428, 62532], [240, 4383, 8738, 53196, 62532], [240, 4383, 8738, 52428, 65348], [240, 3840, 4383, 52428, 63078]]),
  ([240, 3840, 4383, 8738, 17476, 64716], [[240, 4383, 12066, 17476, 64716], [240, 4383, 8738, 20292, 64716], [240, 4383, 8738, 17476, 65484], [240, 3840, 4383, 26214, 64716]]),
  ([240, 4383, 8738, 34952, 62532, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [240, 4383, 34952, 63078, 65348], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 64716, 65348], [240, 4383, 8738, 62532, 65484], [240, 4383, 8738, 65348, 65484]]),
  ([240, 3840, 4383, 34952, 62532, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 34952, 63078, 65348], [240, 3840, 4383, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 63078, 64716], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4383, 8738, 62532, 64716], [[240, 4383, 12066, 62532, 64716], [240, 4383, 8738, 64716, 65348], [240, 4383, 8738, 62532, 65484], [240, 3840, 4383, 63078, 64716]]),
  ([240, 3840, 4383, 8738, 62532, 63624], [[240, 4383, 12066, 62532, 63624], [240, 4383, 8738, 63624, 65348], [240, 4383, 8738, 62532, 65416], [240, 3840, 4383, 63078, 63624]]),
  ([240, 4383, 8738, 17476, 63624, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 26214, 63624, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]]),
  ([240, 3840, 4104, 4383, 8738, 17476], [[3840, 4344, 4383, 8738, 17476], [240, 4383, 7944, 8738, 17476], [240, 4104, 4383, 12066, 17476], [240, 4104, 4383, 8738, 20292], [240, 3840, 4383, 12842, 17476], [240, 3840, 4383, 8738, 21580], [240, 3840, 4104, 4383, 26214]]),
  ([4369, 4383, 8738, 17476, 35064, 65280], [[4383, 8738, 17476, 35064, 65280], [4352, 4383, 8738, 17476, 35064], [4369, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [4383, 8738, 17476, 35064, 65314], [4383, 8738, 17476, 35064, 65348], [4383, 8738, 17476, 35064, 65528]]),
  ([3840, 4369, 4383, 26214, 35064, 61440], [[3840, 4383, 26214, 35064, 61440], [256, 4383, 26214, 35064, 61440], [4383, 26214, 28518, 35064, 61440], [4383, 26214, 35064, 36856, 61440], [3840, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [3840, 4096, 4383, 26214, 35064], [3840, 4383, 26214, 35064, 63078], [3840, 4383, 26214, 35064, 63736]]),
  ([240, 4369, 4383, 28518, 34952, 61440], [[240, 4383, 28518, 34952, 61440], [240, 4383, 28518, 35064, 61440], [240, 4383, 28518, 34952, 61680], [8, 240, 4383, 28518, 61440], [240, 4096, 4383, 28518, 34952], [240, 4383, 28518, 61422, 61440], [240, 4369, 4383, 34952, 65382], [240, 4383, 28518, 34952, 65382], [240, 4383, 34952, 61440, 65382], [240, 4369, 4383, 28518, 63624], [240, 4383, 28518, 34952, 63624], [240, 4383, 28518, 61440, 63624]]),
  ([240, 4369, 4383, 17476, 34952, 65314], [[240, 4383, 17476, 34952, 65314], [240, 4383, 17476, 35064, 65314], [8, 240, 4383, 17476, 65314], [240, 4383, 17476, 52428, 65314], [240, 4369, 4383, 34952, 65382], [240, 4383, 17476, 34952, 65382], [240, 4383, 34952, 65314, 65382], [240, 4383, 17476, 65314, 65450]]),
  ([240, 4369, 4383, 12066, 34952, 62532], [[240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 35064, 62532], [8, 240, 4383, 12066, 62532], [240, 4383, 12066, 44970, 62532], [240, 4369, 4383, 34952, 65382], [240, 4383, 12066, 34952, 65382], [240, 4383, 34952, 62532, 65382], [240, 4383, 12066, 62532, 64716]]),
  ([240, 4369, 4383, 12066, 17476, 63624], [[240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 63736], [240, 4104, 4383, 12066, 17476], [240, 4369, 4383, 28518, 63624], [240, 4383, 12066, 28518, 63624], [240, 4383, 17476, 28518, 63624], [240, 4383, 12066, 17476, 65450], [240, 4383, 12066, 17476, 64716]]),
  ([240, 4369, 4383, 20292, 34952, 61986], [[240, 4383, 20292, 34952, 61986], [240, 4383, 20292, 35064, 61986], [8, 240, 4383, 20292, 61986], [240, 4383, 20292, 53196, 61986], [240, 4369, 4383, 34952, 65382], [240, 4383, 20292, 34952, 65382], [240, 4383, 34952, 61986, 65382], [240, 4383, 20292, 61986, 64170]]),
  ([240, 4369, 4383, 8738, 34952, 65348], [[240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 35064, 65348], [8, 240, 4383, 8738, 65348], [240, 4383, 8738, 43690, 65348], [240, 4369, 4383, 34952, 65382], [240, 4383, 8738, 34952, 65382], [240, 4383, 34952, 65348, 65382], [240, 4383, 8738, 65348, 65484]]),
  ([240, 4369, 4383, 8738, 20292, 63624], [[240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 63736], [240, 4104, 4383, 8738, 20292], [240, 4369, 4383, 28518, 63624], [240, 4383, 8738, 28518, 63624], [240, 4383, 20292, 28518, 63624], [240, 4383, 8738, 20292, 64170], [240, 4383, 8738, 20292, 65484]]),
  ([240, 4369, 4383, 26214, 36744, 61440], [[240, 4383, 26214, 36744, 61440], [240, 4383, 26214, 36856, 61440], [240, 4383, 26214, 36744, 61680], [240, 264, 4383, 26214, 61440], [240, 4096, 4383, 26214, 36744], [240, 4383, 26214, 61422, 61440], [240, 4369, 4383, 36744, 63078], [240, 4383, 26214, 36744, 63078], [240, 4383, 36744, 61440, 63078], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 36744, 65416], [240, 4383, 26214, 61440, 65416]]),
  ([240, 4369, 4383, 17476, 36744, 61986], [[240, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36856, 61986], [240, 264, 4383, 17476, 61986], [240, 4383, 17476, 53196, 61986], [240, 4369, 4383, 36744, 63078], [240, 4383, 17476, 36744, 63078], [240, 4383, 36744, 61986, 63078], [240, 4383, 17476, 61986, 65450]]),
  ([240, 4369, 4383, 8738, 36744, 62532], [[240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36856, 62532], [240, 264, 4383, 8738, 62532], [240, 4383, 8738, 44970, 62532], [240, 4369, 4383, 36744, 63078], [240, 4383, 8738, 36744, 63078], [240, 4383, 36744, 62532, 63078], [240, 4383, 8738, 62532, 65484]]),
  ([240, 4369, 4383, 8738, 17476, 65416], [[240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65528], [240, 4360, 4383, 8738, 17476], [240, 4369, 4383, 26214, 65416], [240, 4383, 8738, 26214, 65416], [240, 4383, 17476, 26214, 65416], [240, 4383, 8738, 17476, 65450], [240, 4383, 8738, 17476, 65484]]),
  ([240, 4369, 4383, 26214, 34952, 65280], [[240, 4383, 26214, 34952, 65280], [240, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [240, 4383, 26214, 34952, 65520], [8, 240, 4383, 26214, 65280], [240, 4352, 4383, 26214, 34952], [240, 4383, 26214, 61166, 65280], [240, 4369, 4383, 34952, 65382], [240, 4383, 26214, 34952, 65382], [240, 4383, 34952, 65280, 65382], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 34952, 65416], [240, 4383, 26214, 65280, 65416]]),
  ([240, 3840, 4369, 4383, 34952, 63078], [[240, 3840, 4383, 34952, 63078], [240, 4080, 4383, 34952, 63078], [240, 3840, 4383, 35064, 63078], [240, 256, 4383, 34952, 63078], [240, 3840, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [240, 3840, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 240, 3840, 4383, 63078], [240, 3840, 4383, 63078, 65262]]),
  ([240, 3840, 4369, 4383, 26214, 63624], [[240, 3840, 4383, 26214, 63624], [240, 4080, 4383, 26214, 63624], [240, 3840, 4383, 26214, 63736], [240, 256, 4383, 26214, 63624], [240, 3840, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 26214, 28518, 63624], [240, 3840, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 63624, 65416], [240, 3840, 4104, 4383, 26214], [240, 3840, 4383, 26214, 65262]]),
  ([15, 248, 4369, 12066, 17476, 61440], [[248, 4383, 12066, 17476, 61440], [15, 248, 4369, 28518, 61440], [15, 248, 4369, 17476, 65314], [15, 248, 4369, 12066, 62532]]),
  ([15, 248, 4369, 8738, 20292, 61440], [[248, 4383, 8738, 20292, 61440], [15, 248, 4369, 28518, 61440], [15, 248, 4369, 20292, 61986], [15, 248, 4369, 8738, 65348]]),
  ([15, 248, 4369, 8738, 17476, 65280], [[248, 4383, 8738, 17476, 65280], [15, 248, 4369, 26214, 65280], [15, 248, 4369, 17476, 65314], [15, 248, 4369, 8738, 65348]]),
  ([15, 248, 3840, 4369, 26214, 61440], [[248, 3840, 4383, 26214, 61440], [15, 248, 4369, 28518, 61440], [15, 248, 4369, 26214, 65280], [15, 248, 3840, 4369, 63078]]),
  ([15, 248, 3840, 4369, 17476, 61986], [[248, 3840, 4383, 17476, 61986], [15, 248, 4369, 20292, 61986], [15, 248, 4369, 17476, 65314], [15, 248, 3840, 4369, 63078]]),
  ([15, 248, 3840, 4369, 8738, 62532], [[248, 3840, 4383, 8738, 62532], [15, 248, 4369, 12066, 62532], [15, 248, 4369, 8738, 65348], [15, 248, 3840, 4369, 63078]]),
  ([15, 240, 4369, 12074, 17476, 61440], [[240, 4383, 12074, 17476, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 17476, 65322], [15, 240, 4369, 12074, 62532]]),
  ([15, 240, 4369, 8738, 20300, 61440], [[240, 4383, 8738, 20300, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 20300, 61986], [15, 240, 4369, 8738, 65356]]),
  ([15, 240, 4369, 8738, 17476, 65288], [[240, 4383, 8738, 17476, 65288], [15, 240, 4369, 26214, 65288], [15, 240, 4369, 17476, 65322], [15, 240, 4369, 8738, 65356]]),
  ([15, 240, 3848, 4369, 26214, 61440], [[240, 3848, 4383, 26214, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 26214, 65288], [15, 240, 3848, 4369, 63078]]),
  ([15, 240, 3848, 4369, 17476, 61986], [[240, 3848, 4383, 17476, 61986], [15, 240, 4369, 20300, 61986], [15, 240, 4369, 17476, 65322], [15, 240, 3848, 4369, 63078]]),
  ([15, 240, 3848, 4369, 8738, 62532], [[240, 3848, 4383, 8738, 62532], [15, 240, 4369, 12074, 62532], [15, 240, 4369, 8738, 65356], [15, 240, 3848, 4369, 63078]]),
  ([15, 240, 4369, 8746, 20292, 61440], [[240, 4383, 8746, 20292, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 20292, 61994], [15, 240, 4369, 8746, 65348]]),
  ([15, 240, 4369, 8746, 17476, 65280], [[240, 4383, 8746, 17476, 65280], [15, 240, 4369, 26222, 65280], [15, 240, 4369, 17476, 65322], [15, 240, 4369, 8746, 65348]]),
  ([15, 240, 3840, 4369, 26222, 61440], [[240, 3840, 4383, 26222, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 26222, 65280], [15, 240, 3840, 4369, 63086]]),
  ([15, 240, 3840, 4369, 17476, 61994], [[240, 3840, 4383, 17476, 61994], [15, 240, 4369, 20292, 61994], [15, 240, 4369, 17476, 65322], [15, 240, 3840, 4369, 63086]]),
  ([15, 240, 3840, 4369, 8746, 62532], [[240, 3840, 4383, 8746, 62532], [15, 240, 4369, 12074, 62532], [15, 240, 4369, 8746, 65348], [15, 240, 3840, 4369, 63086]]),
  ([15, 240, 4369, 12066, 17484, 61440], [[240, 4383, 12066, 17484, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 17484, 65314], [15, 240, 4369, 12066, 62540]]),
  ([15, 240, 4369, 8738, 17484, 65280], [[240, 4383, 8738, 17484, 65280], [15, 240, 4369, 26222, 65280], [15, 240, 4369, 17484, 65314], [15, 240, 4369, 8738, 65356]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_4 : pairs5_4.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_5 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 3840, 4369, 17484, 61986], [[240, 3840, 4383, 17484, 61986], [15, 240, 4369, 20300, 61986], [15, 240, 4369, 17484, 65314], [15, 240, 3840, 4369, 63086]]),
  ([15, 240, 3840, 4369, 8738, 62540], [[240, 3840, 4383, 8738, 62540], [15, 240, 4369, 12066, 62540], [15, 240, 4369, 8738, 65356], [15, 240, 3840, 4369, 63086]]),
  ([15, 240, 4369, 12066, 17476, 61448], [[240, 4383, 12066, 17476, 61448], [15, 240, 4369, 28518, 61448], [15, 240, 4369, 17476, 65322], [15, 240, 4369, 12066, 62540]]),
  ([15, 240, 4369, 8738, 20292, 61448], [[240, 4383, 8738, 20292, 61448], [15, 240, 4369, 28518, 61448], [15, 240, 4369, 20292, 61994], [15, 240, 4369, 8738, 65356]]),
  ([15, 240, 3840, 4369, 26214, 61448], [[240, 3840, 4383, 26214, 61448], [15, 240, 4369, 28518, 61448], [15, 240, 4369, 26214, 65288], [15, 240, 3840, 4369, 63086]]),
  ([8, 15, 240, 4369, 28518, 61440], [[15, 248, 4369, 28518, 61440], [15, 240, 4369, 28526, 61440], [15, 240, 4369, 28518, 61448], [8, 240, 4383, 28518, 61440], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 4369, 17476, 65314], [[15, 248, 4369, 17476, 65314], [15, 240, 4369, 17484, 65314], [15, 240, 4369, 17476, 65322], [8, 240, 4383, 17476, 65314], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 4369, 12066, 62532], [[15, 248, 4369, 12066, 62532], [15, 240, 4369, 12074, 62532], [15, 240, 4369, 12066, 62540], [8, 240, 4383, 12066, 62532], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 4369, 20292, 61986], [[15, 248, 4369, 20292, 61986], [15, 240, 4369, 20300, 61986], [15, 240, 4369, 20292, 61994], [8, 240, 4383, 20292, 61986], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 4369, 8738, 65348], [[15, 248, 4369, 8738, 65348], [15, 240, 4369, 8746, 65348], [15, 240, 4369, 8738, 65356], [8, 240, 4383, 8738, 65348], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 4369, 26214, 65280], [[15, 248, 4369, 26214, 65280], [15, 240, 4369, 26222, 65280], [15, 240, 4369, 26214, 65288], [8, 240, 4383, 26214, 65280], [8, 15, 240, 4369, 65382]]),
  ([8, 15, 240, 3840, 4369, 63078], [[15, 248, 3840, 4369, 63078], [15, 240, 3848, 4369, 63078], [15, 240, 3840, 4369, 63086], [8, 240, 3840, 4383, 63078], [8, 15, 240, 4369, 65382]]),
  ([15, 4369, 8738, 17476, 35064, 65520], [[4383, 8738, 17476, 35064, 65520], [15, 4368, 8738, 17476, 35064], [15, 4369, 26214, 35064, 65520]]),
  ([15, 4080, 4369, 26214, 35064, 61440], [[4080, 4383, 26214, 35064, 61440], [15, 4369, 26214, 35064, 65520], [15, 4080, 4369, 35064, 63078], [15, 4080, 4369, 26214, 63736]]),
  ([15, 4080, 4369, 17476, 35064, 61986], [[4080, 4383, 17476, 35064, 61986], [15, 4080, 4369, 35064, 63078]]),
  ([15, 4080, 4369, 8738, 35064, 62532], [[4080, 4383, 8738, 35064, 62532], [15, 4080, 4369, 35064, 63078]]),
  ([15, 4080, 4369, 8738, 17476, 63736], [[4080, 4383, 8738, 17476, 63736], [15, 4080, 4369, 26214, 63736]]),
  ([15, 4369, 8738, 17476, 36856, 61680], [[4383, 8738, 17476, 36856, 61680], [15, 4369, 26214, 36856, 61680]]),
  ([15, 4080, 4369, 26214, 34952, 61680], [[4080, 4383, 26214, 34952, 61680], [15, 4369, 26214, 36856, 61680], [15, 4080, 4369, 26214, 63736]]),
  ([15, 240, 4369, 26214, 36856, 61440], [[240, 4383, 26214, 36856, 61440], [15, 4369, 26214, 36856, 61680], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 26214, 65528]]),
  ([15, 240, 4369, 17476, 36856, 61986], [[240, 4383, 17476, 36856, 61986], [15, 240, 4369, 36856, 63078]]),
  ([15, 240, 4369, 8738, 36856, 62532], [[240, 4383, 8738, 36856, 62532], [15, 240, 4369, 36856, 63078]]),
  ([15, 240, 4369, 8738, 17476, 65528], [[240, 4383, 8738, 17476, 65528], [15, 240, 4369, 26214, 65528]]),
  ([15, 240, 4368, 8738, 17476, 34952], [[15, 4368, 8738, 17476, 35064], [15, 240, 4368, 26214, 34952]]),
  ([15, 240, 4369, 26214, 34952, 65520], [[240, 4383, 26214, 34952, 65520], [15, 4369, 26214, 35064, 65520], [15, 240, 4368, 26214, 34952], [15, 240, 4369, 26214, 65528]]),
  ([15, 240, 4080, 4369, 34952, 63078], [[240, 4080, 4383, 34952, 63078], [15, 4080, 4369, 35064, 63078], [15, 240, 4369, 36856, 63078]]),
  ([15, 240, 4080, 4369, 26214, 63624], [[240, 4080, 4383, 26214, 63624], [15, 4080, 4369, 26214, 63736], [15, 240, 4369, 26214, 65528]]),
  ([15, 4369, 12066, 17476, 35064, 61680], [[4383, 12066, 17476, 35064, 61680], [15, 4369, 28518, 35064, 61680]]),
  ([15, 4369, 8738, 20292, 35064, 61680], [[4383, 8738, 20292, 35064, 61680], [15, 4369, 28518, 35064, 61680]]),
  ([15, 3840, 4369, 26214, 35064, 61680], [[3840, 4383, 26214, 35064, 61680], [15, 4369, 28518, 35064, 61680], [15, 4369, 26214, 36856, 61680], [15, 4369, 26214, 35064, 65520]]),
  ([15, 240, 4369, 28518, 34952, 61680], [[240, 4383, 28518, 34952, 61680], [15, 4369, 28518, 35064, 61680], [15, 240, 4369, 28518, 63736]]),
  ([15, 240, 4369, 12066, 17476, 63736], [[240, 4383, 12066, 17476, 63736], [15, 240, 4369, 28518, 63736]]),
  ([15, 240, 4369, 8738, 20292, 63736], [[240, 4383, 8738, 20292, 63736], [15, 240, 4369, 28518, 63736]]),
  ([15, 240, 4369, 26214, 36744, 61680], [[240, 4383, 26214, 36744, 61680], [15, 4369, 26214, 36856, 61680], [15, 240, 4369, 26214, 65528]]),
  ([15, 240, 3840, 4369, 26214, 63736], [[240, 3840, 4383, 26214, 63736], [15, 4080, 4369, 26214, 63736], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 26214, 65528]]),
  ([15, 4369, 8994, 17476, 35064, 61440], [[4383, 8994, 17476, 35064, 61440], [15, 4369, 26470, 35064, 61440]]),
  ([15, 4369, 8738, 17732, 35064, 61440], [[4383, 8738, 17732, 35064, 61440], [15, 4369, 26470, 35064, 61440]]),
  ([15, 4369, 8738, 17476, 35320, 61440], [[4383, 8738, 17476, 35320, 61440], [15, 4369, 26214, 35320, 61440]]),
  ([15, 4369, 8738, 17476, 35064, 61696], [[4383, 8738, 17476, 35064, 61696], [15, 4369, 26214, 35064, 61696]]),
  ([15, 256, 4369, 26214, 35064, 61440], [[256, 4383, 26214, 35064, 61440], [15, 4369, 26470, 35064, 61440], [15, 4369, 26214, 35320, 61440], [15, 4369, 26214, 35064, 61696]]),
  ([15, 240, 4369, 28518, 35064, 61440], [[240, 4383, 28518, 35064, 61440], [15, 4369, 28518, 35064, 61680], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 28518, 63736]]),
  ([15, 240, 4369, 17476, 35064, 65314], [[240, 4383, 17476, 35064, 65314], [15, 240, 4369, 35064, 65382]]),
  ([15, 240, 4369, 12066, 35064, 62532], [[240, 4383, 12066, 35064, 62532], [15, 240, 4369, 35064, 65382]]),
  ([15, 4369, 12066, 26214, 35064, 61440], [[4383, 12066, 26214, 35064, 61440], [15, 4369, 26214, 35064, 65314]]),
  ([15, 4369, 12066, 17476, 35064, 61986], [[4383, 12066, 17476, 35064, 61986]]),
  ([15, 4369, 8738, 17476, 35064, 65314], [[4383, 8738, 17476, 35064, 65314], [15, 4369, 26214, 35064, 65314]]),
  ([15, 240, 4369, 20292, 35064, 61986], [[240, 4383, 20292, 35064, 61986], [15, 240, 4369, 35064, 65382]]),
  ([15, 240, 4369, 8738, 35064, 65348], [[240, 4383, 8738, 35064, 65348], [15, 240, 4369, 35064, 65382]]),
  ([15, 4369, 20292, 26214, 35064, 61440], [[4383, 20292, 26214, 35064, 61440], [15, 4369, 26214, 35064, 65348]]),
  ([15, 4369, 8738, 20292, 35064, 62532], [[4383, 8738, 20292, 35064, 62532]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_5 : pairs5_5.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_6 : List (List ℕ × List (List ℕ)) := [
  ([15, 4369, 8738, 17476, 35064, 65348], [[4383, 8738, 17476, 35064, 65348], [15, 4369, 26214, 35064, 65348]]),
  ([15, 4369, 26214, 35064, 36856, 61440], [[4383, 26214, 35064, 36856, 61440], [15, 4369, 26214, 36856, 63736], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4369, 8738, 17476, 36856, 63736], [[4383, 8738, 17476, 36856, 63736], [15, 4369, 26214, 36856, 63736]]),
  ([15, 4369, 8738, 17476, 35064, 65528], [[4383, 8738, 17476, 35064, 65528], [15, 4368, 8738, 17476, 35064], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4352, 4369, 8738, 17476, 35064], [[4352, 4383, 8738, 17476, 35064], [15, 4369, 13090, 17476, 35064], [15, 4369, 8738, 21828, 35064], [15, 4369, 8738, 17476, 39416], [15, 4352, 4369, 26214, 35064]]),
  ([15, 240, 4369, 26214, 35064, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [240, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [15, 4369, 26214, 35064, 65520], [15, 4352, 4369, 26214, 35064], [15, 240, 4369, 35064, 65382], [15, 4369, 26214, 35064, 65382], [15, 240, 4369, 26214, 65528], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4369, 8738, 26214, 35064, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 8738, 26214, 35064, 65280], [15, 4352, 4369, 26214, 35064], [15, 4369, 26214, 35064, 65314], [15, 4369, 26214, 35064, 65382], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4369, 17476, 26214, 35064, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 17476, 26214, 35064, 65280], [15, 4352, 4369, 26214, 35064], [15, 4369, 26214, 35064, 65348], [15, 4369, 26214, 35064, 65382], [15, 4369, 26214, 35064, 65528]]),
  ([15, 3840, 4369, 26214, 35064, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [3840, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [15, 4352, 4369, 26214, 35064], [15, 4369, 26214, 35064, 65382], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4369, 26214, 35064, 61440, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 26214, 35064, 61440, 65280], [15, 4352, 4369, 26214, 35064], [15, 4369, 26214, 35064, 65382], [15, 4369, 26214, 35064, 65528]]),
  ([15, 4369, 7936, 8738, 17476, 35064], [[4383, 7936, 8738, 17476, 35064], [15, 4369, 7936, 26214, 35064]]),
  ([15, 3840, 4369, 12834, 17476, 35064], [[3840, 4383, 12834, 17476, 35064], [15, 3840, 4369, 30310, 35064]]),
  ([15, 3840, 4369, 8738, 21572, 35064], [[3840, 4383, 8738, 21572, 35064], [15, 3840, 4369, 30310, 35064]]),
  ([15, 3840, 4369, 8738, 17476, 39160], [[3840, 4383, 8738, 17476, 39160], [15, 3840, 4369, 26214, 39160]]),
  ([15, 3840, 4096, 4369, 26214, 35064], [[3840, 4096, 4383, 26214, 35064], [15, 4369, 7936, 26214, 35064], [15, 3840, 4369, 30310, 35064], [15, 3840, 4369, 26214, 39160]]),
  ([15, 4369, 26214, 28518, 35064, 61440], [[4383, 26214, 28518, 35064, 61440], [15, 4369, 28518, 35064, 63078], [15, 4369, 26214, 35064, 65382]]),
  ([15, 240, 3840, 4369, 35064, 63078], [[240, 3840, 4383, 35064, 63078], [15, 4080, 4369, 35064, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 35064, 65382]]),
  ([15, 3840, 4369, 26214, 35064, 63078], [[3840, 4383, 26214, 35064, 63078], [15, 4369, 28518, 35064, 63078], [15, 4369, 26214, 35064, 65382]]),
  ([15, 3840, 4369, 26214, 35064, 63736], [[3840, 4383, 26214, 35064, 63736], [15, 4369, 26214, 36856, 63736], [15, 4369, 26214, 35064, 65528]]),
  ([15, 3840, 4369, 26214, 35064, 61986], [[3840, 4383, 26214, 35064, 61986], [15, 4369, 26214, 35064, 65314]]),
  ([15, 3840, 4369, 26214, 35064, 62532], [[3840, 4383, 26214, 35064, 62532], [15, 4369, 26214, 35064, 65348]]),
  ([15, 4369, 26214, 35064, 36744, 61440], [[4383, 26214, 35064, 36744, 61440], [15, 4369, 26214, 35064, 65416]]),
  ([15, 4369, 8738, 17476, 35064, 65416], [[4383, 8738, 17476, 35064, 65416], [15, 4369, 26214, 35064, 65416]]),
  ([15, 4369, 26214, 34952, 35064, 65280], [[15, 4369, 26214, 35064, 65280], [15, 4383, 26214, 35064, 65280], [4369, 4383, 26214, 35064, 65280], [4383, 26214, 34952, 35064, 65280], [15, 4352, 4369, 26214, 35064], [15, 4369, 26214, 35064, 65382], [15, 4369, 26214, 35064, 65416], [15, 4369, 26214, 35064, 65528]]),
  ([15, 3840, 4369, 26214, 35064, 63624], [[3840, 4383, 26214, 35064, 63624], [15, 4369, 26214, 35064, 65416]]),
  ([15, 240, 4369, 28518, 34952, 65280], [[240, 4383, 28518, 34952, 65280], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 65416]]),
  ([15, 240, 4369, 12066, 34952, 65348], [[240, 4383, 12066, 34952, 65348], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 12066, 17476, 65416], [[240, 4383, 12066, 17476, 65416], [15, 240, 4369, 28518, 65416]]),
  ([15, 240, 4369, 20292, 34952, 65314], [[240, 4383, 20292, 34952, 65314], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 8738, 20292, 65416], [[240, 4383, 8738, 20292, 65416], [15, 240, 4369, 28518, 65416]]),
  ([15, 240, 4369, 26214, 36744, 65280], [[240, 4383, 26214, 36744, 65280], [15, 240, 4369, 36744, 65382], [15, 240, 4369, 26214, 65416]]),
  ([15, 240, 4369, 17476, 36744, 65314], [[240, 4383, 17476, 36744, 65314], [15, 240, 4369, 36744, 65382]]),
  ([15, 240, 4369, 8738, 36744, 65348], [[240, 4383, 8738, 36744, 65348], [15, 240, 4369, 36744, 65382]]),
  ([15, 4369, 4592, 8738, 17476, 34952], [[4383, 4592, 8738, 17476, 34952], [15, 4369, 8738, 17476, 39416], [15, 4369, 4592, 26214, 34952]]),
  ([15, 240, 4369, 13090, 17476, 34952], [[240, 4383, 13090, 17476, 34952], [15, 4369, 13090, 17476, 35064], [15, 240, 4369, 30566, 34952]]),
  ([15, 240, 4369, 8738, 21828, 34952], [[240, 4383, 8738, 21828, 34952], [15, 4369, 8738, 21828, 35064], [15, 240, 4369, 30566, 34952]]),
  ([15, 240, 4369, 8738, 17476, 39304], [[240, 4383, 8738, 17476, 39304], [15, 4369, 8738, 17476, 39416], [15, 240, 4369, 26214, 39304]]),
  ([15, 240, 4352, 4369, 26214, 34952], [[240, 4352, 4383, 26214, 34952], [15, 4369, 4592, 26214, 34952], [15, 4352, 4369, 26214, 35064], [15, 240, 4369, 30566, 34952], [15, 240, 4369, 26214, 39304]]),
  ([15, 240, 4369, 26214, 61166, 65280], [[240, 4383, 26214, 61166, 65280], [14, 240, 4369, 26214, 65280], [15, 240, 4369, 61166, 65382], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 3840, 4369, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 3840, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 36744, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 26214, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 26214, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 4369, 26214, 35064, 65382], [15, 240, 4369, 61166, 65382], [15, 240, 4369, 26214, 65518], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 34952, 65280, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 65280, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 65382, 65416], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 3840, 4369, 26214, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 3840, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 28518, 65416], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 34952, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 34952, 65416], [15, 4369, 26214, 35064, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 65280, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 65280, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 65382, 65416], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 43690, 65280], [[240, 4383, 26214, 43690, 65280], [15, 240, 4369, 43690, 65382], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 26214, 34952, 65314], [[240, 4383, 26214, 34952, 65314], [15, 4369, 26214, 35064, 65314], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 8738, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 8738, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 43690, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 8738, 26214, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 8738, 26214, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 26214, 65450], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 52428, 65280], [[240, 4383, 26214, 52428, 65280], [15, 240, 4369, 52428, 65382], [15, 240, 4369, 26214, 65484]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_6 : pairs5_6.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_7 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 26214, 34952, 65348], [[240, 4383, 26214, 34952, 65348], [15, 4369, 26214, 35064, 65348], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 26214, 65484]]),
  ([15, 240, 4369, 17476, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 17476, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 52428, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 17476, 26214, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 17476, 26214, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 26214, 65484], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 17476, 43690, 65314], [[240, 4383, 17476, 43690, 65314], [15, 240, 4369, 43690, 65382]]),
  ([15, 240, 4369, 8738, 43690, 65348], [[240, 4383, 8738, 43690, 65348], [15, 240, 4369, 43690, 65382]]),
  ([15, 240, 4369, 8738, 17476, 65450], [[240, 4383, 8738, 17476, 65450], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 17476, 52428, 65314], [[240, 4383, 17476, 52428, 65314], [15, 240, 4369, 52428, 65382]]),
  ([15, 240, 4369, 34952, 65314, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 65314, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 65382, 65450], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 17476, 65314, 65450], [[240, 4383, 17476, 65314, 65450], [15, 240, 4369, 65382, 65450]]),
  ([15, 240, 4369, 34952, 65314, 65348], [[240, 4383, 34952, 65314, 65348], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 17476, 65314, 65416], [[240, 4383, 17476, 65314, 65416], [15, 240, 4369, 65382, 65416]]),
  ([15, 240, 4369, 8738, 52428, 65348], [[240, 4383, 8738, 52428, 65348], [15, 240, 4369, 52428, 65382]]),
  ([15, 240, 4369, 8738, 17476, 65484], [[240, 4383, 8738, 17476, 65484], [15, 240, 4369, 26214, 65484]]),
  ([15, 240, 4369, 34952, 65348, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 65348, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 65382, 65484], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 8738, 65348, 65484], [[240, 4383, 8738, 65348, 65484], [15, 240, 4369, 65382, 65484]]),
  ([15, 240, 4369, 8738, 65348, 65416], [[240, 4383, 8738, 65348, 65416], [15, 240, 4369, 65382, 65416]]),
  ([15, 240, 4369, 34952, 63078, 65280], [[240, 4383, 34952, 63078, 65280], [15, 240, 4369, 63078, 65416], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 34952, 61440, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 61440, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 63624, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 26214, 63624, 65280], [[240, 4383, 26214, 63624, 65280], [15, 240, 4369, 63624, 65382], [15, 240, 4369, 26214, 65416]]),
  ([15, 240, 4369, 26214, 61440, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 61440, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 63078, 65416], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 34952, 61986, 65348], [[240, 4383, 34952, 61986, 65348], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 17476, 61986, 65416], [[240, 4383, 17476, 61986, 65416], [15, 240, 4369, 63078, 65416]]),
  ([15, 240, 4369, 34952, 62532, 65314], [[240, 4383, 34952, 62532, 65314], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 17476, 63624, 65314], [[240, 4383, 17476, 63624, 65314], [15, 240, 4369, 63624, 65382]]),
  ([15, 240, 4369, 8738, 62532, 65416], [[240, 4383, 8738, 62532, 65416], [15, 240, 4369, 63078, 65416]]),
  ([15, 240, 4369, 8738, 63624, 65348], [[240, 4383, 8738, 63624, 65348], [15, 240, 4369, 63624, 65382]]),
  ([15, 496, 4369, 26214, 34952, 61440], [[496, 4383, 26214, 34952, 61440], [15, 4369, 26214, 35320, 61440], [15, 496, 4369, 34952, 63078], [15, 496, 4369, 26214, 63624]]),
  ([15, 496, 4369, 17476, 34952, 61986], [[496, 4383, 17476, 34952, 61986], [15, 496, 4369, 34952, 63078]]),
  ([15, 496, 4369, 8738, 34952, 62532], [[496, 4383, 8738, 34952, 62532], [15, 496, 4369, 34952, 63078]]),
  ([15, 496, 4369, 8738, 17476, 63624], [[496, 4383, 8738, 17476, 63624], [15, 496, 4369, 26214, 63624]]),
  ([15, 240, 4369, 26470, 34952, 61440], [[240, 4383, 26470, 34952, 61440], [15, 4369, 26470, 35064, 61440], [15, 240, 4369, 34952, 63334], [15, 240, 4369, 26470, 63624]]),
  ([15, 240, 4369, 17476, 34952, 62242], [[240, 4383, 17476, 34952, 62242], [15, 240, 4369, 34952, 63334]]),
  ([15, 240, 4369, 8994, 34952, 62532], [[240, 4383, 8994, 34952, 62532], [15, 240, 4369, 34952, 63334]]),
  ([15, 240, 4369, 8994, 17476, 63624], [[240, 4383, 8994, 17476, 63624], [15, 240, 4369, 26470, 63624]]),
  ([15, 240, 4369, 17732, 34952, 61986], [[240, 4383, 17732, 34952, 61986], [15, 240, 4369, 34952, 63334]]),
  ([15, 240, 4369, 8738, 34952, 62788], [[240, 4383, 8738, 34952, 62788], [15, 240, 4369, 34952, 63334]]),
  ([15, 240, 4369, 8738, 17732, 63624], [[240, 4383, 8738, 17732, 63624], [15, 240, 4369, 26470, 63624]]),
  ([15, 240, 4369, 26214, 35208, 61440], [[240, 4383, 26214, 35208, 61440], [15, 4369, 26214, 35320, 61440], [15, 240, 4369, 35208, 63078], [15, 240, 4369, 26214, 63880]]),
  ([15, 240, 4369, 17476, 35208, 61986], [[240, 4383, 17476, 35208, 61986], [15, 240, 4369, 35208, 63078]]),
  ([15, 240, 4369, 8738, 35208, 62532], [[240, 4383, 8738, 35208, 62532], [15, 240, 4369, 35208, 63078]]),
  ([15, 240, 4369, 8738, 17476, 63880], [[240, 4383, 8738, 17476, 63880], [15, 240, 4369, 26214, 63880]]),
  ([15, 240, 4369, 26214, 34952, 61696], [[240, 4383, 26214, 34952, 61696], [15, 4369, 26214, 35064, 61696], [15, 240, 4369, 34952, 63334], [15, 240, 4369, 26214, 63880]]),
  ([15, 240, 256, 4369, 34952, 63078], [[240, 256, 4383, 34952, 63078], [15, 496, 4369, 34952, 63078], [15, 240, 4369, 35208, 63078], [15, 240, 4369, 34952, 63334]]),
  ([15, 240, 256, 4369, 26214, 63624], [[240, 256, 4383, 26214, 63624], [15, 496, 4369, 26214, 63624], [15, 240, 4369, 26470, 63624], [15, 240, 4369, 26214, 63880]]),
  ([15, 240, 4369, 12066, 20292, 63624], [[240, 4383, 12066, 20292, 63624], [15, 240, 4369, 28518, 63624]]),
  ([15, 240, 4369, 28518, 36744, 61440], [[240, 4383, 28518, 36744, 61440], [15, 240, 4369, 36744, 65382], [15, 240, 4369, 28518, 65416]]),
  ([15, 240, 4369, 12066, 36744, 62532], [[240, 4383, 12066, 36744, 62532], [15, 240, 4369, 36744, 65382]]),
  ([15, 4336, 4369, 12066, 17476, 34952], [[4336, 4383, 12066, 17476, 34952], [15, 4336, 4369, 28518, 34952]]),
  ([15, 240, 4369, 16162, 17476, 34952], [[240, 4383, 16162, 17476, 34952], [15, 240, 4369, 32614, 34952]]),
  ([15, 240, 4369, 12066, 21572, 34952], [[240, 4383, 12066, 21572, 34952], [15, 240, 4369, 32614, 34952]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_7 : pairs5_7.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_8 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 12066, 17476, 39048], [[240, 4383, 12066, 17476, 39048], [15, 240, 4369, 28518, 39048]]),
  ([15, 240, 4096, 4369, 28518, 34952], [[240, 4096, 4383, 28518, 34952], [15, 4336, 4369, 28518, 34952], [15, 240, 4369, 32614, 34952], [15, 240, 4369, 28518, 39048]]),
  ([15, 240, 4369, 28518, 61422, 61440], [[240, 4383, 28518, 61422, 61440], [14, 240, 4369, 28518, 61440], [15, 240, 4369, 61422, 65382], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 28518, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 28518, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 61422, 65382], [15, 240, 4369, 28518, 65518], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 3840, 4369, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 3840, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 65416], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 28518, 34952, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 28518, 34952, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 28518, 61440, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 28518, 61440, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 63624, 65382], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 28518, 44970, 61440], [[240, 4383, 28518, 44970, 61440], [15, 240, 4369, 44970, 65382], [15, 240, 4369, 28518, 65450]]),
  ([15, 240, 4369, 28518, 34952, 65314], [[240, 4383, 28518, 34952, 65314], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 65450]]),
  ([15, 240, 4369, 12066, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 12066, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 44970, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 12066, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 12066, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 65450], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 28518, 52428, 61440], [[240, 4383, 28518, 52428, 61440], [15, 240, 4369, 52428, 65382], [15, 240, 4369, 28518, 64716]]),
  ([15, 240, 4369, 28518, 34952, 62532], [[240, 4383, 28518, 34952, 62532], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 64716]]),
  ([15, 240, 4369, 17476, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 17476, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 64716], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 17476, 44970, 65314], [[240, 4383, 17476, 44970, 65314], [15, 240, 4369, 44970, 65382]]),
  ([15, 240, 4369, 12066, 44970, 62532], [[240, 4383, 12066, 44970, 62532], [15, 240, 4369, 44970, 65382]]),
  ([15, 240, 4369, 12066, 17476, 65450], [[240, 4383, 12066, 17476, 65450], [15, 240, 4369, 28518, 65450]]),
  ([15, 240, 4369, 12066, 52428, 62532], [[240, 4383, 12066, 52428, 62532], [15, 240, 4369, 52428, 65382]]),
  ([15, 240, 4369, 12066, 17476, 64716], [[240, 4383, 12066, 17476, 64716], [15, 240, 4369, 28518, 64716]]),
  ([15, 240, 4369, 34952, 62532, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 62532, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 64716, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 12066, 62532, 64716], [[240, 4383, 12066, 62532, 64716], [15, 240, 4369, 64716, 65382]]),
  ([15, 240, 4369, 12066, 62532, 63624], [[240, 4383, 12066, 62532, 63624], [15, 240, 4369, 63624, 65382]]),
  ([15, 240, 4369, 26214, 44970, 61440], [[240, 4383, 26214, 44970, 61440], [15, 240, 4369, 44970, 63078], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 12066, 34952, 63078], [[240, 4383, 12066, 34952, 63078], [15, 240, 4369, 44970, 63078], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 12066, 26214, 63624], [[240, 4383, 12066, 26214, 63624], [15, 240, 4369, 28518, 63624], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 28518, 43690, 61440], [[240, 4383, 28518, 43690, 61440], [15, 240, 4369, 43690, 65382], [15, 240, 4369, 28518, 64170]]),
  ([15, 240, 4369, 12066, 43690, 62532], [[240, 4383, 12066, 43690, 62532], [15, 240, 4369, 43690, 65382]]),
  ([15, 240, 4369, 12066, 17476, 64170], [[240, 4383, 12066, 17476, 64170], [15, 240, 4369, 28518, 64170]]),
  ([15, 240, 4369, 28518, 34952, 61986], [[240, 4383, 28518, 34952, 61986], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 64170]]),
  ([15, 240, 4369, 17476, 44970, 61986], [[240, 4383, 17476, 44970, 61986], [15, 240, 4369, 44970, 63078]]),
  ([15, 240, 4369, 8738, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 8738, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 64170], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 8738, 44970, 62532], [[240, 4383, 8738, 44970, 62532], [15, 240, 4369, 44970, 63078]]),
  ([15, 240, 4369, 20292, 36744, 61986], [[240, 4383, 20292, 36744, 61986], [15, 240, 4369, 36744, 65382]]),
  ([15, 4336, 4369, 8738, 20292, 34952], [[4336, 4383, 8738, 20292, 34952], [15, 4336, 4369, 28518, 34952]]),
  ([15, 240, 4369, 12834, 20292, 34952], [[240, 4383, 12834, 20292, 34952], [15, 240, 4369, 32614, 34952]]),
  ([15, 240, 4369, 8738, 24388, 34952], [[240, 4383, 8738, 24388, 34952], [15, 240, 4369, 32614, 34952]]),
  ([15, 240, 4369, 8738, 20292, 39048], [[240, 4383, 8738, 20292, 39048], [15, 240, 4369, 28518, 39048]]),
  ([15, 240, 4369, 28518, 53196, 61440], [[240, 4383, 28518, 53196, 61440], [15, 240, 4369, 53196, 65382], [15, 240, 4369, 28518, 65484]]),
  ([15, 240, 4369, 28518, 34952, 65348], [[240, 4383, 28518, 34952, 65348], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 65484]]),
  ([15, 240, 4369, 20292, 34952, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 20292, 34952, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 53196, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 20292, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 20292, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 65484], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 4369, 20292, 43690, 61986], [[240, 4383, 20292, 43690, 61986], [15, 240, 4369, 43690, 65382]]),
  ([15, 240, 4369, 8738, 20292, 64170], [[240, 4383, 8738, 20292, 64170], [15, 240, 4369, 28518, 64170]]),
  ([15, 240, 4369, 20292, 53196, 61986], [[240, 4383, 20292, 53196, 61986], [15, 240, 4369, 53196, 65382]]),
  ([15, 240, 4369, 34952, 61986, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 61986, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 64170, 65382], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 4369, 20292, 61986, 64170], [[240, 4383, 20292, 61986, 64170], [15, 240, 4369, 64170, 65382]]),
  ([15, 240, 4369, 20292, 61986, 63624], [[240, 4383, 20292, 61986, 63624], [15, 240, 4369, 63624, 65382]]),
  ([15, 240, 4369, 8738, 53196, 65348], [[240, 4383, 8738, 53196, 65348], [15, 240, 4369, 53196, 65382]]),
  ([15, 240, 4369, 8738, 20292, 65484], [[240, 4383, 8738, 20292, 65484], [15, 240, 4369, 28518, 65484]]),
  ([15, 240, 4369, 26214, 53196, 61440], [[240, 4383, 26214, 53196, 61440], [15, 240, 4369, 53196, 63078], [15, 240, 4369, 26214, 65484]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_8 : pairs5_8.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_9 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 20292, 34952, 63078], [[240, 4383, 20292, 34952, 63078], [15, 240, 4369, 53196, 63078], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 20292, 26214, 63624], [[240, 4383, 20292, 26214, 63624], [15, 240, 4369, 28518, 63624], [15, 240, 4369, 26214, 65484]]),
  ([15, 240, 4369, 20292, 52428, 61986], [[240, 4383, 20292, 52428, 61986], [15, 240, 4369, 52428, 65382]]),
  ([15, 240, 4369, 17476, 53196, 61986], [[240, 4383, 17476, 53196, 61986], [15, 240, 4369, 53196, 63078]]),
  ([15, 240, 4369, 8738, 20292, 64716], [[240, 4383, 8738, 20292, 64716], [15, 240, 4369, 28518, 64716]]),
  ([15, 240, 4369, 8738, 53196, 62532], [[240, 4383, 8738, 53196, 62532], [15, 240, 4369, 53196, 63078]]),
  ([15, 4336, 4369, 8738, 17476, 36744], [[4336, 4383, 8738, 17476, 36744], [15, 4336, 4369, 26214, 36744]]),
  ([15, 240, 4369, 12834, 17476, 36744], [[240, 4383, 12834, 17476, 36744], [15, 240, 4369, 30310, 36744]]),
  ([15, 240, 4369, 8738, 21572, 36744], [[240, 4383, 8738, 21572, 36744], [15, 240, 4369, 30310, 36744]]),
  ([15, 240, 4369, 8738, 17476, 40840], [[240, 4383, 8738, 17476, 40840], [15, 240, 4369, 26214, 40840]]),
  ([15, 240, 4096, 4369, 26214, 36744], [[240, 4096, 4383, 26214, 36744], [15, 4336, 4369, 26214, 36744], [15, 240, 4369, 30310, 36744], [15, 240, 4369, 26214, 40840]]),
  ([15, 240, 4369, 26214, 61422, 61440], [[240, 4383, 26214, 61422, 61440], [15, 240, 4369, 61422, 63078], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 3840, 4369, 36744, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 3840, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 36744, 65382], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 26214, 36744, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 26214, 36744, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 61422, 63078], [15, 240, 4369, 26214, 65518], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 36744, 61440, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 36744, 61440, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 63078, 65416], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 26214, 36744, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 36744, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 36744, 61986], [[240, 4383, 26214, 36744, 61986], [15, 240, 4369, 36744, 63078], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 4369, 8738, 36744, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 8738, 36744, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 44970, 63078], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 26214, 36744, 62532], [[240, 4383, 26214, 36744, 62532], [15, 240, 4369, 36744, 63078], [15, 240, 4369, 26214, 65484]]),
  ([15, 240, 4369, 17476, 36744, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 17476, 36744, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 53196, 63078], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 36744, 61986, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 36744, 61986, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 63078, 65450], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 17476, 61986, 65450], [[240, 4383, 17476, 61986, 65450], [15, 240, 4369, 63078, 65450]]),
  ([15, 240, 4369, 36744, 61986, 62532], [[240, 4383, 36744, 61986, 62532], [15, 240, 4369, 36744, 63078]]),
  ([15, 240, 4369, 36744, 62532, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 36744, 62532, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 63078, 65484], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 8738, 62532, 65484], [[240, 4383, 8738, 62532, 65484], [15, 240, 4369, 63078, 65484]]),
  ([15, 240, 4369, 34952, 36744, 63078], [[15, 240, 4369, 36744, 63078], [15, 240, 4383, 36744, 63078], [240, 4369, 4383, 36744, 63078], [240, 4383, 34952, 36744, 63078], [15, 240, 4369, 36856, 63078], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 4369, 26214, 36744, 63624], [[240, 4383, 26214, 36744, 63624], [15, 240, 4369, 26214, 65416]]),
  ([15, 3840, 4336, 4369, 26214, 34952], [[3840, 4336, 4383, 26214, 34952], [15, 4336, 4369, 28518, 34952], [15, 4336, 4369, 26214, 36744], [15, 3840, 4369, 26214, 39160]]),
  ([15, 240, 4369, 7936, 26214, 34952], [[240, 4383, 7936, 26214, 34952], [15, 4369, 7936, 26214, 35064], [15, 240, 4369, 32614, 34952], [15, 240, 4369, 26214, 40840]]),
  ([15, 240, 3840, 4369, 30310, 34952], [[240, 3840, 4383, 30310, 34952], [15, 3840, 4369, 30310, 35064], [15, 240, 4369, 32614, 34952], [15, 240, 4369, 30310, 36744]]),
  ([15, 240, 3840, 4369, 26214, 39048], [[240, 3840, 4383, 26214, 39048], [15, 3840, 4369, 26214, 39160], [15, 240, 4369, 28518, 39048], [15, 240, 4369, 26214, 40840]]),
  ([15, 240, 4369, 34952, 63078, 65314], [[240, 4383, 34952, 63078, 65314], [15, 240, 4369, 63078, 65450], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 17476, 64170, 65314], [[240, 4383, 17476, 64170, 65314], [15, 240, 4369, 64170, 65382]]),
  ([15, 240, 3840, 4369, 52428, 63078], [[240, 3840, 4383, 52428, 63078], [15, 240, 4369, 53196, 63078], [15, 240, 4369, 52428, 65382]]),
  ([15, 240, 4369, 34952, 63078, 65382], [[15, 240, 4369, 34952, 65382], [15, 240, 4383, 34952, 65382], [240, 4369, 4383, 34952, 65382], [240, 4383, 34952, 63078, 65382], [8, 15, 240, 4369, 65382], [15, 240, 4369, 35064, 65382], [15, 240, 4369, 65262, 65382], [15, 240, 4369, 63078, 65518], [15, 240, 4369, 65382, 65518]]),
  ([15, 240, 3840, 4369, 63078, 65262], [[240, 3840, 4383, 63078, 65262], [14, 240, 3840, 4369, 63078], [15, 240, 4369, 65262, 65382], [15, 240, 4369, 63078, 65518]]),
  ([15, 240, 3840, 4369, 63078, 63624], [[240, 3840, 4383, 63078, 63624], [15, 240, 4369, 63624, 65382], [15, 240, 4369, 63078, 65416]]),
  ([15, 240, 3840, 4369, 63078, 64170], [[240, 3840, 4383, 63078, 64170], [15, 240, 4369, 64170, 65382], [15, 240, 4369, 63078, 65450]]),
  ([15, 240, 3840, 4369, 26214, 64170], [[240, 3840, 4383, 26214, 64170], [15, 240, 4369, 28518, 64170], [15, 240, 4369, 26214, 65450]]),
  ([15, 240, 3840, 4369, 43690, 63078], [[240, 3840, 4383, 43690, 63078], [15, 240, 4369, 44970, 63078], [15, 240, 4369, 43690, 65382]]),
  ([15, 240, 4369, 34952, 63078, 65348], [[240, 4383, 34952, 63078, 65348], [15, 240, 4369, 63078, 65484], [15, 240, 4369, 34952, 65382]]),
  ([15, 240, 4369, 8738, 64716, 65348], [[240, 4383, 8738, 64716, 65348], [15, 240, 4369, 64716, 65382]]),
  ([15, 240, 3840, 4369, 63078, 64716], [[240, 3840, 4383, 63078, 64716], [15, 240, 4369, 64716, 65382], [15, 240, 4369, 63078, 65484]]),
  ([15, 240, 3840, 4369, 26214, 64716], [[240, 3840, 4383, 26214, 64716], [15, 240, 4369, 28518, 64716], [15, 240, 4369, 26214, 65484]]),
  ([15, 240, 4369, 26214, 63624, 65416], [[15, 240, 4369, 26214, 65416], [15, 240, 4383, 26214, 65416], [240, 4369, 4383, 26214, 65416], [240, 4383, 26214, 63624, 65416], [15, 240, 4369, 26214, 65528], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 26214, 28518, 63624], [[15, 240, 4369, 28518, 63624], [15, 240, 4383, 28518, 63624], [240, 4369, 4383, 28518, 63624], [240, 4383, 26214, 28518, 63624], [15, 240, 4369, 28518, 63736], [15, 240, 4369, 28518, 65262], [15, 240, 4369, 26214, 65518], [15, 240, 4369, 28518, 65518]]),
  ([15, 240, 3840, 4369, 26214, 65262], [[240, 3840, 4383, 26214, 65262], [15, 240, 4369, 28518, 65262], [15, 240, 4369, 26214, 65518]]),
  ([15, 240, 4369, 28518, 61166, 61440], [[240, 4383, 28518, 61166, 61440], [14, 240, 4369, 28518, 61440], [15, 240, 4369, 61166, 65382], [15, 240, 4369, 28518, 65262]]),
  ([15, 240, 4369, 28518, 34952, 63078], [[240, 4383, 28518, 34952, 63078], [15, 4369, 28518, 35064, 63078], [15, 240, 4369, 61422, 63078], [15, 240, 4369, 34952, 65382], [15, 240, 4369, 28518, 65262]]),
  ([14, 240, 3840, 4369, 26214, 61440], [[14, 240, 4369, 28518, 61440], [14, 240, 4369, 26214, 65280], [14, 240, 3840, 4369, 63078]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_9 : pairs5_9.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5_10 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 3840, 4369, 61166, 63078], [[240, 3840, 4383, 61166, 63078], [14, 240, 3840, 4369, 63078], [15, 240, 4369, 61422, 63078], [15, 240, 4369, 61166, 65382]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk5_10 : pairs5_10.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  decide +kernel

def pairs5 : List (List ℕ × List (List ℕ)) := pairs5_0 ++ pairs5_1 ++ pairs5_2 ++ pairs5_3 ++ pairs5_4 ++ pairs5_5 ++ pairs5_6 ++ pairs5_7 ++ pairs5_8 ++ pairs5_9 ++ pairs5_10

set_option maxRecDepth 20000 in
theorem pairs5_fst : pairs5.map Prod.fst = row5 := rfl

theorem chk5 : pairs5.all (fun p => verifyFast 4478 negs 4 p.1 p.2 row4) = true := by
  unfold pairs5
  simp only [List.all_append, Bool.and_eq_true, chk5_0, chk5_1, chk5_2, chk5_3, chk5_4, chk5_5, chk5_6, chk5_7, chk5_8, chk5_9, chk5_10, and_self]

def pairs6_0 : List (List ℕ × List (List ℕ)) := [
  ([240, 3840, 4383, 8738, 17476, 34952, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [240, 4383, 12066, 17476, 34952, 61440], [240, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 34952, 65280], [240, 3840, 4383, 26214, 34952, 61440], [240, 3840, 4383, 17476, 34952, 61986], [240, 3840, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 17476, 63624]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [15, 4369, 8738, 17476, 35064, 65280], [15, 3840, 4369, 26214, 35064, 61440]]),
  ([15, 240, 4369, 12066, 17476, 34952, 61440], [[240, 4383, 12066, 17476, 34952, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 17476, 34952, 65314], [15, 240, 4369, 12066, 34952, 62532], [15, 240, 4369, 12066, 17476, 63624]]),
  ([15, 240, 4369, 8738, 20292, 34952, 61440], [[240, 4383, 8738, 20292, 34952, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 20292, 34952, 61986], [15, 240, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 20292, 63624]]),
  ([15, 240, 4369, 8738, 17476, 36744, 61440], [[240, 4383, 8738, 17476, 36744, 61440], [15, 240, 4369, 26214, 36744, 61440], [15, 240, 4369, 17476, 36744, 61986], [15, 240, 4369, 8738, 36744, 62532], [15, 240, 4369, 8738, 17476, 65416]]),
  ([15, 240, 4369, 8738, 17476, 34952, 65280], [[240, 4383, 8738, 17476, 34952, 65280], [15, 4369, 8738, 17476, 35064, 65280], [15, 240, 4369, 26214, 34952, 65280], [15, 240, 4369, 17476, 34952, 65314], [15, 240, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 17476, 65416]]),
  ([15, 240, 3840, 4369, 26214, 34952, 61440], [[240, 3840, 4383, 26214, 34952, 61440], [15, 3840, 4369, 26214, 35064, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 26214, 36744, 61440], [15, 240, 4369, 26214, 34952, 65280], [15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4369, 26214, 63624]]),
  ([15, 240, 3840, 4369, 17476, 34952, 61986], [[240, 3840, 4383, 17476, 34952, 61986], [15, 240, 4369, 20292, 34952, 61986], [15, 240, 4369, 17476, 36744, 61986], [15, 240, 4369, 17476, 34952, 65314], [15, 240, 3840, 4369, 34952, 63078]]),
  ([15, 240, 3840, 4369, 8738, 34952, 62532], [[240, 3840, 4383, 8738, 34952, 62532], [15, 240, 4369, 12066, 34952, 62532], [15, 240, 4369, 8738, 36744, 62532], [15, 240, 4369, 8738, 34952, 65348], [15, 240, 3840, 4369, 34952, 63078]]),
  ([15, 240, 3840, 4369, 8738, 17476, 63624], [[240, 3840, 4383, 8738, 17476, 63624], [15, 240, 4369, 12066, 17476, 63624], [15, 240, 4369, 8738, 20292, 63624], [15, 240, 4369, 8738, 17476, 65416], [15, 240, 3840, 4369, 26214, 63624]]),
  ([8, 240, 3840, 4383, 8738, 17476, 61440], [[248, 3840, 4383, 8738, 17476, 61440], [240, 3848, 4383, 8738, 17476, 61440], [240, 3840, 4383, 8746, 17476, 61440], [240, 3840, 4383, 8738, 17484, 61440], [240, 3840, 4383, 8738, 17476, 61448], [8, 240, 4383, 12066, 17476, 61440], [8, 240, 4383, 8738, 20292, 61440], [8, 240, 4383, 8738, 17476, 65280], [8, 240, 3840, 4383, 26214, 61440], [8, 240, 3840, 4383, 17476, 61986], [8, 240, 3840, 4383, 8738, 62532]]),
  ([240, 4080, 4383, 8738, 17476, 34952, 61440], [[4080, 4383, 8738, 17476, 35064, 61440], [4080, 4383, 8738, 17476, 34952, 61680], [240, 4383, 8738, 17476, 36856, 61440], [240, 4383, 8738, 17476, 34952, 65520], [240, 4080, 4383, 26214, 34952, 61440], [240, 4080, 4383, 17476, 34952, 61986], [240, 4080, 4383, 8738, 34952, 62532], [240, 4080, 4383, 8738, 17476, 63624]]),
  ([15, 3840, 4383, 8738, 17476, 35064, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [256, 4383, 8738, 17476, 35064, 61440], [4383, 8738, 12066, 17476, 35064, 61440], [4383, 8738, 17476, 20292, 35064, 61440], [4383, 8738, 17476, 35064, 36856, 61440], [15, 4383, 8738, 17476, 35064, 65280], [3840, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [3840, 4096, 4383, 8738, 17476, 35064], [15, 3840, 4383, 26214, 35064, 61440], [3840, 4383, 8738, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [3840, 4383, 8738, 17476, 35064, 61986], [3840, 4383, 8738, 17476, 35064, 62532], [3840, 4383, 8738, 17476, 35064, 63736]]),
  ([240, 3840, 4383, 8738, 17476, 35064, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [4080, 4383, 8738, 17476, 35064, 61440], [3840, 4383, 8738, 17476, 35064, 61680], [256, 4383, 8738, 17476, 35064, 61440], [240, 4383, 12066, 17476, 35064, 61440], [4383, 8738, 12066, 17476, 35064, 61440], [240, 4383, 8738, 20292, 35064, 61440], [4383, 8738, 17476, 20292, 35064, 61440], [240, 4383, 8738, 17476, 36856, 61440], [4383, 8738, 17476, 35064, 36856, 61440], [240, 4383, 8738, 17476, 35064, 65280], [3840, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [3840, 4096, 4383, 8738, 17476, 35064], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4383, 8738, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [240, 3840, 4383, 17476, 35064, 61986], [3840, 4383, 8738, 17476, 35064, 61986], [240, 3840, 4383, 8738, 35064, 62532], [3840, 4383, 8738, 17476, 35064, 62532], [240, 3840, 4383, 8738, 17476, 63736], [3840, 4383, 8738, 17476, 35064, 63736]]),
  ([3840, 4383, 8738, 17476, 34952, 35064, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [256, 4383, 8738, 17476, 35064, 61440], [4383, 8738, 12066, 17476, 35064, 61440], [4383, 8738, 17476, 20292, 35064, 61440], [4383, 8738, 17476, 35064, 36744, 61440], [4383, 8738, 17476, 35064, 36856, 61440], [3840, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [3840, 4096, 4383, 8738, 17476, 35064], [3840, 4383, 8738, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [3840, 4383, 8738, 17476, 35064, 61986], [3840, 4383, 8738, 17476, 35064, 62532], [3840, 4383, 8738, 17476, 35064, 63624], [3840, 4383, 8738, 17476, 35064, 63736]]),
  ([240, 3840, 4383, 8738, 17476, 34952, 61680], [[4080, 4383, 8738, 17476, 34952, 61680], [3840, 4383, 8738, 17476, 35064, 61680], [240, 4383, 12066, 17476, 34952, 61680], [240, 4383, 8738, 20292, 34952, 61680], [240, 4383, 8738, 17476, 36744, 61680], [240, 4383, 8738, 17476, 34952, 65520], [240, 3840, 4383, 26214, 34952, 61680], [240, 3840, 4383, 8738, 17476, 63736]]),
  ([240, 256, 4383, 8738, 17476, 34952, 61440], [[496, 4383, 8738, 17476, 34952, 61440], [256, 4383, 8738, 17476, 35064, 61440], [240, 4383, 8994, 17476, 34952, 61440], [240, 4383, 8738, 17732, 34952, 61440], [240, 4383, 8738, 17476, 35208, 61440], [240, 4383, 8738, 17476, 34952, 61696], [240, 256, 4383, 26214, 34952, 61440], [240, 256, 4383, 17476, 34952, 61986], [240, 256, 4383, 8738, 34952, 62532], [240, 256, 4383, 8738, 17476, 63624]]),
  ([15, 240, 4383, 12066, 17476, 34952, 61440], [[240, 4383, 12066, 17476, 34952, 61440], [240, 4383, 12066, 17476, 35064, 61440], [240, 4383, 12066, 17476, 34952, 61680], [8, 240, 4383, 12066, 17476, 61440], [240, 4096, 4383, 12066, 17476, 34952], [15, 240, 4383, 28518, 34952, 61440], [240, 4383, 12066, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 12066, 17476, 44970, 61440], [15, 240, 4383, 17476, 34952, 65314], [240, 4383, 12066, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 12066, 17476, 52428, 61440], [15, 240, 4383, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [15, 240, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [240, 4383, 12066, 17476, 61440, 63624]]),
  ([240, 3840, 4383, 12066, 17476, 34952, 61440], [[240, 4383, 12066, 17476, 34952, 61440], [240, 4383, 12066, 17476, 35064, 61440], [240, 4383, 12066, 17476, 34952, 61680], [240, 4383, 12066, 20292, 34952, 61440], [240, 4383, 12066, 17476, 36744, 61440], [240, 4383, 12066, 17476, 34952, 65280], [8, 240, 4383, 12066, 17476, 61440], [240, 4096, 4383, 12066, 17476, 34952], [240, 3840, 4383, 28518, 34952, 61440], [240, 4383, 12066, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 12066, 17476, 44970, 61440], [240, 3840, 4383, 17476, 34952, 65314], [240, 4383, 12066, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 12066, 17476, 52428, 61440], [240, 3840, 4383, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [240, 3840, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [240, 4383, 12066, 17476, 61440, 63624]]),
  ([240, 4383, 8738, 12066, 17476, 34952, 61440], [[240, 4383, 12066, 17476, 34952, 61440], [240, 4383, 12066, 17476, 35064, 61440], [4383, 8738, 12066, 17476, 35064, 61440], [240, 4383, 12066, 17476, 34952, 61680], [8, 240, 4383, 12066, 17476, 61440], [240, 4096, 4383, 12066, 17476, 34952], [240, 4383, 12066, 26214, 34952, 61440], [240, 4383, 12066, 17476, 43690, 61440], [240, 4383, 12066, 17476, 34952, 61986], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 12066, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 8738, 17476, 44970, 61440], [240, 4383, 12066, 17476, 44970, 61440], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 12066, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 12066, 17476, 52428, 61440], [240, 4383, 8738, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [240, 4383, 8738, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [240, 4383, 12066, 17476, 61440, 63624]]),
  ([15, 240, 4383, 8738, 20292, 34952, 61440], [[240, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 20292, 35064, 61440], [240, 4383, 8738, 20292, 34952, 61680], [8, 240, 4383, 8738, 20292, 61440], [240, 4096, 4383, 8738, 20292, 34952], [15, 240, 4383, 28518, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 20292, 28518, 34952, 61440], [240, 4383, 8738, 20292, 43690, 61440], [15, 240, 4383, 20292, 34952, 61986], [240, 4383, 8738, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [240, 4383, 8738, 20292, 53196, 61440], [15, 240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [15, 240, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [240, 4383, 8738, 20292, 61440, 63624]]),
  ([240, 3840, 4383, 8738, 20292, 34952, 61440], [[240, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 20292, 35064, 61440], [240, 4383, 8738, 20292, 34952, 61680], [240, 4383, 12066, 20292, 34952, 61440], [240, 4383, 8738, 20292, 36744, 61440], [240, 4383, 8738, 20292, 34952, 65280], [8, 240, 4383, 8738, 20292, 61440], [240, 4096, 4383, 8738, 20292, 34952], [240, 3840, 4383, 28518, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 20292, 28518, 34952, 61440], [240, 4383, 8738, 20292, 43690, 61440], [240, 3840, 4383, 20292, 34952, 61986], [240, 4383, 8738, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [240, 4383, 8738, 20292, 53196, 61440], [240, 3840, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [240, 3840, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [240, 4383, 8738, 20292, 61440, 63624]]),
  ([240, 4383, 8738, 17476, 20292, 34952, 61440], [[240, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 20292, 35064, 61440], [4383, 8738, 17476, 20292, 35064, 61440], [240, 4383, 8738, 20292, 34952, 61680], [8, 240, 4383, 8738, 20292, 61440], [240, 4096, 4383, 8738, 20292, 34952], [240, 4383, 20292, 26214, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 20292, 28518, 34952, 61440], [240, 4383, 8738, 20292, 43690, 61440], [240, 4383, 8738, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [240, 4383, 8738, 20292, 52428, 61440], [240, 4383, 8738, 20292, 34952, 62532], [240, 4383, 8738, 17476, 53196, 61440], [240, 4383, 8738, 20292, 53196, 61440], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 20292, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [240, 4383, 8738, 17476, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [240, 4383, 8738, 20292, 61440, 63624]]),
  ([15, 240, 4383, 8738, 17476, 36744, 61440], [[240, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 36856, 61440], [240, 4383, 8738, 17476, 36744, 61680], [240, 264, 4383, 8738, 17476, 61440], [240, 4096, 4383, 8738, 17476, 36744], [15, 240, 4383, 26214, 36744, 61440], [240, 4383, 8738, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [240, 4383, 8738, 17476, 44970, 61440], [15, 240, 4383, 17476, 36744, 61986], [240, 4383, 8738, 17476, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [240, 4383, 8738, 17476, 53196, 61440], [15, 240, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [15, 240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 36744, 65416], [240, 4383, 8738, 17476, 61440, 65416]]),
  ([240, 3840, 4383, 8738, 17476, 36744, 61440], [[240, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 36856, 61440], [240, 4383, 8738, 17476, 36744, 61680], [240, 4383, 12066, 17476, 36744, 61440], [240, 4383, 8738, 20292, 36744, 61440], [240, 4383, 8738, 17476, 36744, 65280], [240, 264, 4383, 8738, 17476, 61440], [240, 4096, 4383, 8738, 17476, 36744], [240, 3840, 4383, 26214, 36744, 61440], [240, 4383, 8738, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [240, 4383, 8738, 17476, 44970, 61440], [240, 3840, 4383, 17476, 36744, 61986], [240, 4383, 8738, 17476, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [240, 4383, 8738, 17476, 53196, 61440], [240, 3840, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [240, 3840, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 36744, 65416], [240, 4383, 8738, 17476, 61440, 65416]]),
  ([240, 4383, 8738, 17476, 34952, 36744, 61440], [[240, 4383, 8738, 17476, 36744, 61440], [4383, 8738, 17476, 35064, 36744, 61440], [240, 4383, 8738, 17476, 36856, 61440], [240, 4383, 8738, 17476, 36744, 61680], [240, 264, 4383, 8738, 17476, 61440], [240, 4096, 4383, 8738, 17476, 36744], [240, 4383, 8738, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [240, 4383, 8738, 17476, 44970, 61440], [240, 4383, 8738, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [240, 4383, 8738, 17476, 53196, 61440], [240, 4383, 8738, 17476, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [240, 4383, 8738, 17476, 36744, 63624], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 36744, 65416], [240, 4383, 8738, 17476, 61440, 65416]]),
  ([15, 240, 4383, 8738, 17476, 34952, 65280], [[240, 4383, 8738, 17476, 34952, 65280], [15, 4383, 8738, 17476, 35064, 65280], [240, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [240, 4383, 8738, 17476, 34952, 65520], [8, 240, 4383, 8738, 17476, 65280], [240, 4352, 4383, 8738, 17476, 34952], [15, 240, 4383, 26214, 34952, 65280], [240, 4383, 8738, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [240, 4383, 8738, 17476, 43690, 65280], [15, 240, 4383, 17476, 34952, 65314], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 17476, 34952, 65280, 65314], [240, 4383, 8738, 17476, 52428, 65280], [15, 240, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 34952, 65280, 65348], [15, 240, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 65280, 65416]]),
  ([240, 3840, 4383, 8738, 17476, 34952, 65280], [[240, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 35064, 65280], [3840, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [240, 4383, 8738, 17476, 34952, 65520], [240, 4383, 12066, 17476, 34952, 65280], [240, 4383, 8738, 20292, 34952, 65280], [240, 4383, 8738, 17476, 36744, 65280], [8, 240, 4383, 8738, 17476, 65280], [240, 4352, 4383, 8738, 17476, 34952], [240, 3840, 4383, 26214, 34952, 65280], [240, 4383, 8738, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [240, 4383, 8738, 17476, 43690, 65280], [240, 3840, 4383, 17476, 34952, 65314], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 17476, 34952, 65280, 65314], [240, 4383, 8738, 17476, 52428, 65280], [240, 3840, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 34952, 65280, 65348], [240, 3840, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 65280, 65416]]),
  ([240, 4383, 8738, 17476, 34952, 61440, 65280], [[240, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [240, 4383, 8738, 17476, 34952, 65520], [8, 240, 4383, 8738, 17476, 65280], [240, 4352, 4383, 8738, 17476, 34952], [240, 4383, 8738, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [240, 4383, 8738, 17476, 43690, 65280], [240, 4383, 17476, 34952, 61986, 65280], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 17476, 34952, 65280, 65314], [240, 4383, 8738, 17476, 52428, 65280], [240, 4383, 8738, 34952, 62532, 65280], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [240, 4383, 8738, 34952, 65280, 65348], [240, 4383, 8738, 17476, 63624, 65280], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 61440, 65416], [240, 4383, 8738, 17476, 65280, 65416]]),
  ([240, 3840, 4096, 4383, 8738, 17476, 34952], [[3840, 4336, 4383, 8738, 17476, 34952], [3840, 4096, 4383, 8738, 17476, 35064], [240, 4383, 7936, 8738, 17476, 34952], [240, 4096, 4383, 12066, 17476, 34952], [240, 4096, 4383, 8738, 20292, 34952], [240, 4096, 4383, 8738, 17476, 36744], [240, 3840, 4383, 12834, 17476, 34952], [240, 3840, 4383, 8738, 21572, 34952], [240, 3840, 4383, 8738, 17476, 39048], [240, 3840, 4096, 4383, 26214, 34952]]),
  ([15, 240, 3840, 4383, 26214, 34952, 61440], [[240, 3840, 4383, 26214, 34952, 61440], [240, 4080, 4383, 26214, 34952, 61440], [15, 3840, 4383, 26214, 35064, 61440], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [240, 3840, 4383, 26214, 34952, 61680], [240, 256, 4383, 26214, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 3840, 4383, 28518, 34952, 61440], [240, 4383, 26214, 28518, 34952, 61440], [15, 240, 4383, 26214, 36744, 61440], [240, 3840, 4383, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [15, 240, 4383, 26214, 34952, 65280], [240, 3840, 4383, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [8, 240, 3840, 4383, 26214, 61440], [240, 3840, 4096, 4383, 26214, 34952], [240, 3840, 4383, 26214, 61166, 61440], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 26214, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [240, 3840, 4383, 26214, 61440, 63624]]),
  ([240, 3840, 4383, 8738, 26214, 34952, 61440], [[240, 3840, 4383, 26214, 34952, 61440], [240, 4080, 4383, 26214, 34952, 61440], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4383, 8738, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [240, 3840, 4383, 26214, 34952, 61680], [240, 256, 4383, 26214, 34952, 61440], [240, 4383, 12066, 26214, 34952, 61440], [240, 3840, 4383, 28518, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 26214, 28518, 34952, 61440], [240, 3840, 4383, 26214, 36744, 61440], [240, 4383, 8738, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [240, 3840, 4383, 26214, 34952, 65280], [240, 4383, 8738, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [8, 240, 3840, 4383, 26214, 61440], [240, 3840, 4096, 4383, 26214, 34952], [240, 3840, 4383, 26214, 43690, 61440], [240, 3840, 4383, 26214, 34952, 61986], [240, 3840, 4383, 26214, 61166, 61440], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 26214, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [240, 3840, 4383, 8738, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [240, 3840, 4383, 26214, 61440, 63624]]),
  ([240, 3840, 4383, 17476, 26214, 34952, 61440], [[240, 3840, 4383, 26214, 34952, 61440], [240, 4080, 4383, 26214, 34952, 61440], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [240, 3840, 4383, 26214, 34952, 61680], [240, 256, 4383, 26214, 34952, 61440], [240, 4383, 20292, 26214, 34952, 61440], [240, 3840, 4383, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 26214, 28518, 34952, 61440], [240, 3840, 4383, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [240, 3840, 4383, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [8, 240, 3840, 4383, 26214, 61440], [240, 3840, 4096, 4383, 26214, 34952], [240, 3840, 4383, 26214, 52428, 61440], [240, 3840, 4383, 26214, 34952, 62532], [240, 3840, 4383, 26214, 61166, 61440], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 26214, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [240, 3840, 4383, 17476, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [240, 3840, 4383, 26214, 61440, 63624]]),
  ([240, 3840, 4383, 8738, 17476, 43690, 61440], [[240, 4383, 12066, 17476, 43690, 61440], [240, 4383, 8738, 20292, 43690, 61440], [240, 4383, 8738, 17476, 44970, 61440], [240, 4383, 8738, 17476, 43690, 65280], [240, 3840, 4383, 26214, 43690, 61440], [240, 3840, 4383, 17476, 43690, 61986], [240, 3840, 4383, 8738, 43690, 62532], [240, 3840, 4383, 8738, 17476, 64170]]),
  ([15, 240, 3840, 4383, 17476, 34952, 61986], [[240, 3840, 4383, 17476, 34952, 61986], [240, 4080, 4383, 17476, 34952, 61986], [240, 3840, 4383, 17476, 35064, 61986], [240, 256, 4383, 17476, 34952, 61986], [15, 240, 4383, 20292, 34952, 61986], [240, 3840, 4383, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [15, 240, 4383, 17476, 36744, 61986], [240, 3840, 4383, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [15, 240, 4383, 17476, 34952, 65314], [240, 3840, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61986, 65314], [8, 240, 3840, 4383, 17476, 61986], [240, 3840, 4383, 17476, 52428, 61986], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 34952, 61986, 63078], [240, 3840, 4383, 17476, 61986, 64170]]),
  ([240, 3840, 4383, 8738, 17476, 34952, 61986], [[240, 3840, 4383, 17476, 34952, 61986], [240, 4080, 4383, 17476, 34952, 61986], [240, 3840, 4383, 17476, 35064, 61986], [3840, 4383, 8738, 17476, 35064, 61986], [240, 256, 4383, 17476, 34952, 61986], [240, 4383, 12066, 17476, 34952, 61986], [240, 3840, 4383, 20292, 34952, 61986], [240, 4383, 8738, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [240, 3840, 4383, 17476, 36744, 61986], [240, 4383, 8738, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [240, 3840, 4383, 17476, 34952, 65314], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61986, 65314], [8, 240, 3840, 4383, 17476, 61986], [240, 3840, 4383, 26214, 34952, 61986], [240, 3840, 4383, 17476, 43690, 61986], [240, 3840, 4383, 17476, 52428, 61986], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 34952, 61986, 63078], [240, 3840, 4383, 8738, 17476, 64170], [240, 3840, 4383, 17476, 61986, 64170]]),
  ([240, 3840, 4383, 17476, 34952, 61440, 61986], [[240, 3840, 4383, 17476, 34952, 61986], [240, 4080, 4383, 17476, 34952, 61986], [240, 3840, 4383, 17476, 35064, 61986], [240, 256, 4383, 17476, 34952, 61986], [240, 3840, 4383, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [240, 3840, 4383, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [240, 4383, 17476, 34952, 61986, 65280], [240, 3840, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 17476, 34952, 61986, 65314], [8, 240, 3840, 4383, 17476, 61986], [240, 3840, 4383, 17476, 52428, 61986], [240, 3840, 4383, 34952, 61986, 62532], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [240, 3840, 4383, 34952, 61986, 63078], [240, 3840, 4383, 17476, 61986, 63624], [240, 3840, 4383, 17476, 61986, 64170]]),
  ([240, 3840, 4383, 8738, 17476, 52428, 61440], [[240, 4383, 12066, 17476, 52428, 61440], [240, 4383, 8738, 20292, 52428, 61440], [240, 4383, 8738, 17476, 53196, 61440], [240, 4383, 8738, 17476, 52428, 65280], [240, 3840, 4383, 26214, 52428, 61440], [240, 3840, 4383, 17476, 52428, 61986], [240, 3840, 4383, 8738, 52428, 62532], [240, 3840, 4383, 8738, 17476, 64716]]),
  ([15, 240, 3840, 4383, 8738, 34952, 62532], [[240, 3840, 4383, 8738, 34952, 62532], [240, 4080, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 35064, 62532], [240, 256, 4383, 8738, 34952, 62532], [15, 240, 4383, 12066, 34952, 62532], [240, 3840, 4383, 12066, 34952, 62532], [240, 4383, 8738, 12066, 34952, 62532], [15, 240, 4383, 8738, 36744, 62532], [240, 3840, 4383, 8738, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [15, 240, 4383, 8738, 34952, 65348], [240, 3840, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 62532, 65348], [8, 240, 3840, 4383, 8738, 62532], [240, 3840, 4383, 8738, 43690, 62532], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 34952, 62532, 63078], [240, 3840, 4383, 8738, 62532, 64716]]),
  ([240, 3840, 4383, 8738, 17476, 34952, 62532], [[240, 3840, 4383, 8738, 34952, 62532], [240, 4080, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 35064, 62532], [3840, 4383, 8738, 17476, 35064, 62532], [240, 256, 4383, 8738, 34952, 62532], [240, 3840, 4383, 12066, 34952, 62532], [240, 4383, 8738, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [240, 4383, 8738, 20292, 34952, 62532], [240, 3840, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [240, 3840, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 34952, 62532, 65348], [8, 240, 3840, 4383, 8738, 62532], [240, 3840, 4383, 26214, 34952, 62532], [240, 3840, 4383, 8738, 43690, 62532], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 34952, 62532, 63078], [240, 3840, 4383, 8738, 52428, 62532], [240, 3840, 4383, 8738, 17476, 64716], [240, 3840, 4383, 8738, 62532, 64716]]),
  ([240, 3840, 4383, 8738, 34952, 61440, 62532], [[240, 3840, 4383, 8738, 34952, 62532], [240, 4080, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 35064, 62532], [240, 256, 4383, 8738, 34952, 62532], [240, 3840, 4383, 12066, 34952, 62532], [240, 4383, 8738, 12066, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [240, 3840, 4383, 8738, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [240, 4383, 8738, 34952, 62532, 65280], [240, 3840, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [240, 4383, 8738, 34952, 62532, 65348], [8, 240, 3840, 4383, 8738, 62532], [240, 3840, 4383, 8738, 43690, 62532], [240, 3840, 4383, 34952, 61986, 62532], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [240, 3840, 4383, 34952, 62532, 63078], [240, 3840, 4383, 8738, 62532, 63624], [240, 3840, 4383, 8738, 62532, 64716]]),
  ([15, 240, 3840, 4383, 8738, 17476, 63624], [[240, 3840, 4383, 8738, 17476, 63624], [240, 4080, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 63736], [240, 256, 4383, 8738, 17476, 63624], [15, 240, 4383, 12066, 17476, 63624], [240, 3840, 4383, 12066, 17476, 63624], [240, 4383, 8738, 12066, 17476, 63624], [15, 240, 4383, 8738, 20292, 63624], [240, 3840, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 20292, 63624], [15, 240, 4383, 8738, 17476, 65416], [240, 3840, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 63624, 65416], [240, 3840, 4104, 4383, 8738, 17476], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4383, 8738, 26214, 63624], [240, 3840, 4383, 17476, 26214, 63624], [240, 3840, 4383, 8738, 17476, 64170], [240, 3840, 4383, 8738, 17476, 64716]]),
  ([240, 3840, 4383, 8738, 17476, 34952, 63624], [[240, 3840, 4383, 8738, 17476, 63624], [240, 4080, 4383, 8738, 17476, 63624], [3840, 4383, 8738, 17476, 35064, 63624], [240, 3840, 4383, 8738, 17476, 63736], [240, 256, 4383, 8738, 17476, 63624], [240, 3840, 4383, 12066, 17476, 63624], [240, 4383, 8738, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [240, 3840, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [240, 4383, 8738, 17476, 36744, 63624], [240, 3840, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 63624, 65416], [240, 3840, 4104, 4383, 8738, 17476], [240, 3840, 4383, 8738, 26214, 63624], [240, 3840, 4383, 17476, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [240, 3840, 4383, 8738, 17476, 64170], [240, 3840, 4383, 8738, 17476, 64716]]),
  ([240, 3840, 4383, 8738, 17476, 61440, 63624], [[240, 3840, 4383, 8738, 17476, 63624], [240, 4080, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 63736], [240, 256, 4383, 8738, 17476, 63624], [240, 3840, 4383, 12066, 17476, 63624], [240, 4383, 8738, 12066, 17476, 63624], [240, 4383, 12066, 17476, 61440, 63624], [240, 3840, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 20292, 63624], [240, 4383, 8738, 20292, 61440, 63624], [240, 4383, 8738, 17476, 63624, 65280], [240, 3840, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 61440, 65416], [240, 4383, 8738, 17476, 63624, 65416], [240, 3840, 4104, 4383, 8738, 17476], [240, 3840, 4383, 8738, 26214, 63624], [240, 3840, 4383, 17476, 26214, 63624], [240, 3840, 4383, 26214, 61440, 63624], [240, 3840, 4383, 17476, 61986, 63624], [240, 3840, 4383, 8738, 17476, 64170], [240, 3840, 4383, 8738, 62532, 63624], [240, 3840, 4383, 8738, 17476, 64716]]),
  ([3840, 4369, 4383, 8738, 17476, 35064, 61440], [[3840, 4383, 8738, 17476, 35064, 61440], [256, 4383, 8738, 17476, 35064, 61440], [4383, 8738, 12066, 17476, 35064, 61440], [4383, 8738, 17476, 20292, 35064, 61440], [4383, 8738, 17476, 35064, 36856, 61440], [3840, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [3840, 4096, 4383, 8738, 17476, 35064], [3840, 4369, 4383, 26214, 35064, 61440], [3840, 4383, 8738, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [3840, 4383, 8738, 17476, 35064, 61986], [3840, 4383, 8738, 17476, 35064, 62532], [3840, 4383, 8738, 17476, 35064, 63736]]),
  ([240, 4369, 4383, 12066, 17476, 34952, 61440], [[240, 4383, 12066, 17476, 34952, 61440], [240, 4383, 12066, 17476, 35064, 61440], [240, 4383, 12066, 17476, 34952, 61680], [8, 240, 4383, 12066, 17476, 61440], [240, 4096, 4383, 12066, 17476, 34952], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 12066, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [240, 4383, 12066, 17476, 44970, 61440], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 12066, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [240, 4383, 12066, 17476, 52428, 61440], [240, 4369, 4383, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [240, 4369, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [240, 4383, 12066, 17476, 61440, 63624]]),
  ([240, 4369, 4383, 8738, 20292, 34952, 61440], [[240, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 20292, 35064, 61440], [240, 4383, 8738, 20292, 34952, 61680], [8, 240, 4383, 8738, 20292, 61440], [240, 4096, 4383, 8738, 20292, 34952], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [240, 4383, 20292, 28518, 34952, 61440], [240, 4383, 8738, 20292, 43690, 61440], [240, 4369, 4383, 20292, 34952, 61986], [240, 4383, 8738, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [240, 4383, 8738, 20292, 53196, 61440], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [240, 4369, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [240, 4383, 8738, 20292, 61440, 63624]]),
  ([240, 4369, 4383, 8738, 17476, 36744, 61440], [[240, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 36856, 61440], [240, 4383, 8738, 17476, 36744, 61680], [240, 264, 4383, 8738, 17476, 61440], [240, 4096, 4383, 8738, 17476, 36744], [240, 4369, 4383, 26214, 36744, 61440], [240, 4383, 8738, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [240, 4383, 8738, 17476, 44970, 61440], [240, 4369, 4383, 17476, 36744, 61986], [240, 4383, 8738, 17476, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [240, 4383, 8738, 17476, 53196, 61440], [240, 4369, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 36744, 65416], [240, 4383, 8738, 17476, 61440, 65416]]),
  ([240, 4369, 4383, 8738, 17476, 34952, 65280], [[240, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [240, 4383, 8738, 17476, 34952, 65520], [8, 240, 4383, 8738, 17476, 65280], [240, 4352, 4383, 8738, 17476, 34952], [240, 4369, 4383, 26214, 34952, 65280], [240, 4383, 8738, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [240, 4383, 8738, 17476, 43690, 65280], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 8738, 17476, 34952, 65314], [240, 4383, 17476, 34952, 65280, 65314], [240, 4383, 8738, 17476, 52428, 65280], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 34952, 65348], [240, 4383, 8738, 34952, 65280, 65348], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 34952, 65416], [240, 4383, 8738, 17476, 65280, 65416]]),
  ([240, 3840, 4369, 4383, 26214, 34952, 61440], [[240, 3840, 4383, 26214, 34952, 61440], [240, 4080, 4383, 26214, 34952, 61440], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4369, 4383, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [240, 3840, 4383, 26214, 34952, 61680], [240, 256, 4383, 26214, 34952, 61440], [240, 3840, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 26214, 28518, 34952, 61440], [240, 3840, 4383, 26214, 36744, 61440], [240, 4369, 4383, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [240, 3840, 4383, 26214, 34952, 65280], [240, 4369, 4383, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [8, 240, 3840, 4383, 26214, 61440], [240, 3840, 4096, 4383, 26214, 34952], [240, 3840, 4383, 26214, 61166, 61440], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 26214, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [240, 3840, 4383, 26214, 61440, 63624]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk6_0 : pairs6_0.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  decide +kernel

def pairs6_1 : List (List ℕ × List (List ℕ)) := [
  ([240, 3840, 4369, 4383, 17476, 34952, 61986], [[240, 3840, 4383, 17476, 34952, 61986], [240, 4080, 4383, 17476, 34952, 61986], [240, 3840, 4383, 17476, 35064, 61986], [240, 256, 4383, 17476, 34952, 61986], [240, 3840, 4383, 20292, 34952, 61986], [240, 4369, 4383, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [240, 3840, 4383, 17476, 36744, 61986], [240, 4369, 4383, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [240, 3840, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61986, 65314], [8, 240, 3840, 4383, 17476, 61986], [240, 3840, 4383, 17476, 52428, 61986], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 17476, 34952, 63078], [240, 3840, 4383, 34952, 61986, 63078], [240, 3840, 4383, 17476, 61986, 64170]]),
  ([240, 3840, 4369, 4383, 8738, 34952, 62532], [[240, 3840, 4383, 8738, 34952, 62532], [240, 4080, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 35064, 62532], [240, 256, 4383, 8738, 34952, 62532], [240, 3840, 4383, 12066, 34952, 62532], [240, 4369, 4383, 12066, 34952, 62532], [240, 4383, 8738, 12066, 34952, 62532], [240, 3840, 4383, 8738, 36744, 62532], [240, 4369, 4383, 8738, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [240, 3840, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 62532, 65348], [8, 240, 3840, 4383, 8738, 62532], [240, 3840, 4383, 8738, 43690, 62532], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 8738, 34952, 63078], [240, 3840, 4383, 34952, 62532, 63078], [240, 3840, 4383, 8738, 62532, 64716]]),
  ([240, 3840, 4369, 4383, 8738, 17476, 63624], [[240, 3840, 4383, 8738, 17476, 63624], [240, 4080, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 63736], [240, 256, 4383, 8738, 17476, 63624], [240, 3840, 4383, 12066, 17476, 63624], [240, 4369, 4383, 12066, 17476, 63624], [240, 4383, 8738, 12066, 17476, 63624], [240, 3840, 4383, 8738, 20292, 63624], [240, 4369, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 20292, 63624], [240, 3840, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 63624, 65416], [240, 3840, 4104, 4383, 8738, 17476], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 8738, 26214, 63624], [240, 3840, 4383, 17476, 26214, 63624], [240, 3840, 4383, 8738, 17476, 64170], [240, 3840, 4383, 8738, 17476, 64716]]),
  ([15, 248, 3840, 4369, 8738, 17476, 61440], [[248, 3840, 4383, 8738, 17476, 61440], [15, 248, 4369, 12066, 17476, 61440], [15, 248, 4369, 8738, 20292, 61440], [15, 248, 4369, 8738, 17476, 65280], [15, 248, 3840, 4369, 26214, 61440], [15, 248, 3840, 4369, 17476, 61986], [15, 248, 3840, 4369, 8738, 62532]]),
  ([15, 240, 3848, 4369, 8738, 17476, 61440], [[240, 3848, 4383, 8738, 17476, 61440], [15, 240, 4369, 12074, 17476, 61440], [15, 240, 4369, 8738, 20300, 61440], [15, 240, 4369, 8738, 17476, 65288], [15, 240, 3848, 4369, 26214, 61440], [15, 240, 3848, 4369, 17476, 61986], [15, 240, 3848, 4369, 8738, 62532]]),
  ([15, 240, 3840, 4369, 8746, 17476, 61440], [[240, 3840, 4383, 8746, 17476, 61440], [15, 240, 4369, 12074, 17476, 61440], [15, 240, 4369, 8746, 20292, 61440], [15, 240, 4369, 8746, 17476, 65280], [15, 240, 3840, 4369, 26222, 61440], [15, 240, 3840, 4369, 17476, 61994], [15, 240, 3840, 4369, 8746, 62532]]),
  ([15, 240, 3840, 4369, 8738, 17484, 61440], [[240, 3840, 4383, 8738, 17484, 61440], [15, 240, 4369, 12066, 17484, 61440], [15, 240, 4369, 8738, 20300, 61440], [15, 240, 4369, 8738, 17484, 65280], [15, 240, 3840, 4369, 26222, 61440], [15, 240, 3840, 4369, 17484, 61986], [15, 240, 3840, 4369, 8738, 62540]]),
  ([15, 240, 3840, 4369, 8738, 17476, 61448], [[240, 3840, 4383, 8738, 17476, 61448], [15, 240, 4369, 12066, 17476, 61448], [15, 240, 4369, 8738, 20292, 61448], [15, 240, 4369, 8738, 17476, 65288], [15, 240, 3840, 4369, 26214, 61448], [15, 240, 3840, 4369, 17476, 61994], [15, 240, 3840, 4369, 8738, 62540]]),
  ([8, 15, 240, 4369, 12066, 17476, 61440], [[15, 248, 4369, 12066, 17476, 61440], [15, 240, 4369, 12074, 17476, 61440], [15, 240, 4369, 12066, 17484, 61440], [15, 240, 4369, 12066, 17476, 61448], [8, 240, 4383, 12066, 17476, 61440], [8, 15, 240, 4369, 28518, 61440], [8, 15, 240, 4369, 17476, 65314], [8, 15, 240, 4369, 12066, 62532]]),
  ([8, 15, 240, 4369, 8738, 20292, 61440], [[15, 248, 4369, 8738, 20292, 61440], [15, 240, 4369, 8746, 20292, 61440], [15, 240, 4369, 8738, 20300, 61440], [15, 240, 4369, 8738, 20292, 61448], [8, 240, 4383, 8738, 20292, 61440], [8, 15, 240, 4369, 28518, 61440], [8, 15, 240, 4369, 20292, 61986], [8, 15, 240, 4369, 8738, 65348]]),
  ([8, 15, 240, 4369, 8738, 17476, 65280], [[15, 248, 4369, 8738, 17476, 65280], [15, 240, 4369, 8746, 17476, 65280], [15, 240, 4369, 8738, 17484, 65280], [15, 240, 4369, 8738, 17476, 65288], [8, 240, 4383, 8738, 17476, 65280], [8, 15, 240, 4369, 26214, 65280], [8, 15, 240, 4369, 17476, 65314], [8, 15, 240, 4369, 8738, 65348]]),
  ([8, 15, 240, 3840, 4369, 26214, 61440], [[15, 248, 3840, 4369, 26214, 61440], [15, 240, 3848, 4369, 26214, 61440], [15, 240, 3840, 4369, 26222, 61440], [15, 240, 3840, 4369, 26214, 61448], [8, 240, 3840, 4383, 26214, 61440], [8, 15, 240, 4369, 28518, 61440], [8, 15, 240, 4369, 26214, 65280], [8, 15, 240, 3840, 4369, 63078]]),
  ([8, 15, 240, 3840, 4369, 17476, 61986], [[15, 248, 3840, 4369, 17476, 61986], [15, 240, 3848, 4369, 17476, 61986], [15, 240, 3840, 4369, 17484, 61986], [15, 240, 3840, 4369, 17476, 61994], [8, 240, 3840, 4383, 17476, 61986], [8, 15, 240, 4369, 20292, 61986], [8, 15, 240, 4369, 17476, 65314], [8, 15, 240, 3840, 4369, 63078]]),
  ([8, 15, 240, 3840, 4369, 8738, 62532], [[15, 248, 3840, 4369, 8738, 62532], [15, 240, 3848, 4369, 8738, 62532], [15, 240, 3840, 4369, 8746, 62532], [15, 240, 3840, 4369, 8738, 62540], [8, 240, 3840, 4383, 8738, 62532], [8, 15, 240, 4369, 12066, 62532], [8, 15, 240, 4369, 8738, 65348], [8, 15, 240, 3840, 4369, 63078]]),
  ([15, 4080, 4369, 8738, 17476, 35064, 61440], [[4080, 4383, 8738, 17476, 35064, 61440], [15, 4369, 8738, 17476, 35064, 65520], [15, 4080, 4369, 26214, 35064, 61440], [15, 4080, 4369, 17476, 35064, 61986], [15, 4080, 4369, 8738, 35064, 62532], [15, 4080, 4369, 8738, 17476, 63736]]),
  ([15, 4080, 4369, 8738, 17476, 34952, 61680], [[4080, 4383, 8738, 17476, 34952, 61680], [15, 4369, 8738, 17476, 36856, 61680], [15, 4080, 4369, 26214, 34952, 61680], [15, 4080, 4369, 8738, 17476, 63736]]),
  ([15, 240, 4369, 8738, 17476, 36856, 61440], [[240, 4383, 8738, 17476, 36856, 61440], [15, 4369, 8738, 17476, 36856, 61680], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 8738, 17476, 65528]]),
  ([15, 240, 4369, 8738, 17476, 34952, 65520], [[240, 4383, 8738, 17476, 34952, 65520], [15, 4369, 8738, 17476, 35064, 65520], [15, 240, 4368, 8738, 17476, 34952], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4369, 8738, 17476, 65528]]),
  ([15, 240, 4080, 4369, 26214, 34952, 61440], [[240, 4080, 4383, 26214, 34952, 61440], [15, 4080, 4369, 26214, 35064, 61440], [15, 4080, 4369, 26214, 34952, 61680], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 4080, 4369, 26214, 63624]]),
  ([15, 240, 4080, 4369, 17476, 34952, 61986], [[240, 4080, 4383, 17476, 34952, 61986], [15, 4080, 4369, 17476, 35064, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4080, 4369, 34952, 63078]]),
  ([15, 240, 4080, 4369, 8738, 34952, 62532], [[240, 4080, 4383, 8738, 34952, 62532], [15, 4080, 4369, 8738, 35064, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4080, 4369, 34952, 63078]]),
  ([15, 240, 4080, 4369, 8738, 17476, 63624], [[240, 4080, 4383, 8738, 17476, 63624], [15, 4080, 4369, 8738, 17476, 63736], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4080, 4369, 26214, 63624]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 61680], [[3840, 4383, 8738, 17476, 35064, 61680], [15, 4369, 12066, 17476, 35064, 61680], [15, 4369, 8738, 20292, 35064, 61680], [15, 4369, 8738, 17476, 36856, 61680], [15, 4369, 8738, 17476, 35064, 65520], [15, 3840, 4369, 26214, 35064, 61680]]),
  ([15, 240, 4369, 12066, 17476, 34952, 61680], [[240, 4383, 12066, 17476, 34952, 61680], [15, 4369, 12066, 17476, 35064, 61680], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4369, 12066, 17476, 63736]]),
  ([15, 240, 4369, 8738, 20292, 34952, 61680], [[240, 4383, 8738, 20292, 34952, 61680], [15, 4369, 8738, 20292, 35064, 61680], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4369, 8738, 20292, 63736]]),
  ([15, 240, 4369, 8738, 17476, 36744, 61680], [[240, 4383, 8738, 17476, 36744, 61680], [15, 4369, 8738, 17476, 36856, 61680], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4369, 8738, 17476, 65528]]),
  ([15, 240, 3840, 4369, 26214, 34952, 61680], [[240, 3840, 4383, 26214, 34952, 61680], [15, 4080, 4369, 26214, 34952, 61680], [15, 3840, 4369, 26214, 35064, 61680], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 3840, 4369, 26214, 63736]]),
  ([15, 240, 3840, 4369, 8738, 17476, 63736], [[240, 3840, 4383, 8738, 17476, 63736], [15, 4080, 4369, 8738, 17476, 63736], [15, 240, 4369, 12066, 17476, 63736], [15, 240, 4369, 8738, 20292, 63736], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 3840, 4369, 26214, 63736]]),
  ([15, 256, 4369, 8738, 17476, 35064, 61440], [[256, 4383, 8738, 17476, 35064, 61440], [15, 4369, 8994, 17476, 35064, 61440], [15, 4369, 8738, 17732, 35064, 61440], [15, 4369, 8738, 17476, 35320, 61440], [15, 4369, 8738, 17476, 35064, 61696], [15, 256, 4369, 26214, 35064, 61440]]),
  ([15, 240, 4369, 12066, 17476, 35064, 61440], [[240, 4383, 12066, 17476, 35064, 61440], [15, 4369, 12066, 17476, 35064, 61680], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 12066, 17476, 63736]]),
  ([15, 4369, 8738, 12066, 17476, 35064, 61440], [[4383, 8738, 12066, 17476, 35064, 61440], [15, 4369, 12066, 26214, 35064, 61440], [15, 4369, 12066, 17476, 35064, 61986], [15, 4369, 8738, 17476, 35064, 65314]]),
  ([15, 240, 4369, 8738, 20292, 35064, 61440], [[240, 4383, 8738, 20292, 35064, 61440], [15, 4369, 8738, 20292, 35064, 61680], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 8738, 20292, 63736]]),
  ([15, 4369, 8738, 17476, 20292, 35064, 61440], [[4383, 8738, 17476, 20292, 35064, 61440], [15, 4369, 20292, 26214, 35064, 61440], [15, 4369, 8738, 20292, 35064, 62532], [15, 4369, 8738, 17476, 35064, 65348]]),
  ([15, 4369, 8738, 17476, 35064, 36856, 61440], [[4383, 8738, 17476, 35064, 36856, 61440], [15, 4369, 26214, 35064, 36856, 61440], [15, 4369, 8738, 17476, 36856, 63736], [15, 4369, 8738, 17476, 35064, 65528]]),
  ([15, 240, 4369, 8738, 17476, 35064, 65280], [[15, 4369, 8738, 17476, 35064, 65280], [15, 4383, 8738, 17476, 35064, 65280], [240, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [15, 4369, 8738, 17476, 35064, 65520], [15, 4352, 4369, 8738, 17476, 35064], [15, 240, 4369, 26214, 35064, 65280], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 240, 4369, 17476, 35064, 65314], [15, 4369, 8738, 17476, 35064, 65314], [15, 240, 4369, 8738, 35064, 65348], [15, 4369, 8738, 17476, 35064, 65348], [15, 240, 4369, 8738, 17476, 65528], [15, 4369, 8738, 17476, 35064, 65528]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 65280], [[15, 4369, 8738, 17476, 35064, 65280], [15, 4383, 8738, 17476, 35064, 65280], [3840, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [15, 4352, 4369, 8738, 17476, 35064], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 4369, 8738, 17476, 35064, 65314], [15, 4369, 8738, 17476, 35064, 65348], [15, 4369, 8738, 17476, 35064, 65528]]),
  ([15, 4369, 8738, 17476, 35064, 61440, 65280], [[15, 4369, 8738, 17476, 35064, 65280], [15, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 35064, 61440, 65280], [15, 4352, 4369, 8738, 17476, 35064], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 4369, 8738, 17476, 35064, 65314], [15, 4369, 8738, 17476, 35064, 65348], [15, 4369, 8738, 17476, 35064, 65528]]),
  ([15, 3840, 4096, 4369, 8738, 17476, 35064], [[3840, 4096, 4383, 8738, 17476, 35064], [15, 4369, 7936, 8738, 17476, 35064], [15, 3840, 4369, 12834, 17476, 35064], [15, 3840, 4369, 8738, 21572, 35064], [15, 3840, 4369, 8738, 17476, 39160], [15, 3840, 4096, 4369, 26214, 35064]]),
  ([15, 240, 3840, 4369, 26214, 35064, 61440], [[15, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4383, 26214, 35064, 61440], [240, 3840, 4383, 26214, 35064, 61440], [3840, 4369, 4383, 26214, 35064, 61440], [15, 4080, 4369, 26214, 35064, 61440], [15, 3840, 4369, 26214, 35064, 61680], [15, 256, 4369, 26214, 35064, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 4369, 26214, 28518, 35064, 61440], [15, 240, 4369, 26214, 36856, 61440], [15, 4369, 26214, 35064, 36856, 61440], [15, 240, 4369, 26214, 35064, 65280], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 3840, 4096, 4369, 26214, 35064], [15, 240, 3840, 4369, 35064, 63078], [15, 3840, 4369, 26214, 35064, 63078], [15, 240, 3840, 4369, 26214, 63736], [15, 3840, 4369, 26214, 35064, 63736]]),
  ([15, 3840, 4369, 8738, 26214, 35064, 61440], [[15, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4383, 26214, 35064, 61440], [3840, 4369, 4383, 26214, 35064, 61440], [3840, 4383, 8738, 26214, 35064, 61440], [15, 256, 4369, 26214, 35064, 61440], [15, 4369, 12066, 26214, 35064, 61440], [15, 4369, 26214, 28518, 35064, 61440], [15, 4369, 26214, 35064, 36856, 61440], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 3840, 4096, 4369, 26214, 35064], [15, 3840, 4369, 26214, 35064, 61986], [15, 3840, 4369, 26214, 35064, 63078], [15, 3840, 4369, 26214, 35064, 63736]]),
  ([15, 3840, 4369, 17476, 26214, 35064, 61440], [[15, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4383, 26214, 35064, 61440], [3840, 4369, 4383, 26214, 35064, 61440], [3840, 4383, 17476, 26214, 35064, 61440], [15, 256, 4369, 26214, 35064, 61440], [15, 4369, 20292, 26214, 35064, 61440], [15, 4369, 26214, 28518, 35064, 61440], [15, 4369, 26214, 35064, 36856, 61440], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 3840, 4096, 4369, 26214, 35064], [15, 3840, 4369, 26214, 35064, 62532], [15, 3840, 4369, 26214, 35064, 63078], [15, 3840, 4369, 26214, 35064, 63736]]),
  ([15, 240, 3840, 4369, 17476, 35064, 61986], [[240, 3840, 4383, 17476, 35064, 61986], [15, 4080, 4369, 17476, 35064, 61986], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 3840, 4369, 35064, 63078]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 61986], [[3840, 4383, 8738, 17476, 35064, 61986], [15, 4369, 12066, 17476, 35064, 61986], [15, 4369, 8738, 17476, 35064, 65314], [15, 3840, 4369, 26214, 35064, 61986]]),
  ([15, 240, 3840, 4369, 8738, 35064, 62532], [[240, 3840, 4383, 8738, 35064, 62532], [15, 4080, 4369, 8738, 35064, 62532], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 3840, 4369, 35064, 63078]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 62532], [[3840, 4383, 8738, 17476, 35064, 62532], [15, 4369, 8738, 20292, 35064, 62532], [15, 4369, 8738, 17476, 35064, 65348], [15, 3840, 4369, 26214, 35064, 62532]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 63736], [[3840, 4383, 8738, 17476, 35064, 63736], [15, 4369, 8738, 17476, 36856, 63736], [15, 4369, 8738, 17476, 35064, 65528], [15, 3840, 4369, 26214, 35064, 63736]]),
  ([15, 4369, 8738, 17476, 35064, 36744, 61440], [[4383, 8738, 17476, 35064, 36744, 61440], [15, 4369, 26214, 35064, 36744, 61440], [15, 4369, 8738, 17476, 35064, 65416]]),
  ([15, 4369, 8738, 17476, 34952, 35064, 65280], [[15, 4369, 8738, 17476, 35064, 65280], [15, 4383, 8738, 17476, 35064, 65280], [4369, 4383, 8738, 17476, 35064, 65280], [4383, 8738, 17476, 34952, 35064, 65280], [15, 4352, 4369, 8738, 17476, 35064], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 4369, 8738, 17476, 35064, 65314], [15, 4369, 8738, 17476, 35064, 65348], [15, 4369, 8738, 17476, 35064, 65416], [15, 4369, 8738, 17476, 35064, 65528]]),
  ([15, 3840, 4369, 26214, 34952, 35064, 61440], [[15, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4383, 26214, 35064, 61440], [3840, 4369, 4383, 26214, 35064, 61440], [3840, 4383, 26214, 34952, 35064, 61440], [15, 256, 4369, 26214, 35064, 61440], [15, 4369, 26214, 28518, 35064, 61440], [15, 4369, 26214, 35064, 36744, 61440], [15, 4369, 26214, 35064, 36856, 61440], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 3840, 4096, 4369, 26214, 35064], [15, 3840, 4369, 26214, 35064, 63078], [15, 3840, 4369, 26214, 35064, 63624], [15, 3840, 4369, 26214, 35064, 63736]]),
  ([15, 3840, 4369, 8738, 17476, 35064, 63624], [[3840, 4383, 8738, 17476, 35064, 63624], [15, 4369, 8738, 17476, 35064, 65416], [15, 3840, 4369, 26214, 35064, 63624]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk6_1 : pairs6_1.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  decide +kernel

def pairs6_2 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 12066, 17476, 34952, 65280], [[240, 4383, 12066, 17476, 34952, 65280], [15, 240, 4369, 28518, 34952, 65280], [15, 240, 4369, 17476, 34952, 65314], [15, 240, 4369, 12066, 34952, 65348], [15, 240, 4369, 12066, 17476, 65416]]),
  ([15, 240, 4369, 8738, 20292, 34952, 65280], [[240, 4383, 8738, 20292, 34952, 65280], [15, 240, 4369, 28518, 34952, 65280], [15, 240, 4369, 20292, 34952, 65314], [15, 240, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 20292, 65416]]),
  ([15, 240, 4369, 8738, 17476, 36744, 65280], [[240, 4383, 8738, 17476, 36744, 65280], [15, 240, 4369, 26214, 36744, 65280], [15, 240, 4369, 17476, 36744, 65314], [15, 240, 4369, 8738, 36744, 65348], [15, 240, 4369, 8738, 17476, 65416]]),
  ([15, 240, 4352, 4369, 8738, 17476, 34952], [[240, 4352, 4383, 8738, 17476, 34952], [15, 4369, 4592, 8738, 17476, 34952], [15, 4352, 4369, 8738, 17476, 35064], [15, 240, 4369, 13090, 17476, 34952], [15, 240, 4369, 8738, 21828, 34952], [15, 240, 4369, 8738, 17476, 39304], [15, 240, 4352, 4369, 26214, 34952]]),
  ([15, 240, 3840, 4369, 26214, 34952, 65280], [[15, 240, 4369, 26214, 34952, 65280], [15, 240, 4383, 26214, 34952, 65280], [240, 3840, 4383, 26214, 34952, 65280], [240, 4369, 4383, 26214, 34952, 65280], [8, 15, 240, 4369, 26214, 65280], [15, 240, 4369, 26214, 35064, 65280], [15, 3840, 4369, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4369, 28518, 34952, 65280], [15, 240, 4369, 26214, 36744, 65280], [15, 240, 4352, 4369, 26214, 34952], [15, 240, 4369, 26214, 61166, 65280], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 65280, 65416]]),
  ([15, 240, 4369, 8738, 26214, 34952, 65280], [[15, 240, 4369, 26214, 34952, 65280], [15, 240, 4383, 26214, 34952, 65280], [240, 4369, 4383, 26214, 34952, 65280], [240, 4383, 8738, 26214, 34952, 65280], [8, 15, 240, 4369, 26214, 65280], [15, 240, 4369, 26214, 35064, 65280], [15, 4369, 8738, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4352, 4369, 26214, 34952], [15, 240, 4369, 26214, 43690, 65280], [15, 240, 4369, 26214, 34952, 65314], [15, 240, 4369, 26214, 61166, 65280], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 65280, 65416]]),
  ([15, 240, 4369, 17476, 26214, 34952, 65280], [[15, 240, 4369, 26214, 34952, 65280], [15, 240, 4383, 26214, 34952, 65280], [240, 4369, 4383, 26214, 34952, 65280], [240, 4383, 17476, 26214, 34952, 65280], [8, 15, 240, 4369, 26214, 65280], [15, 240, 4369, 26214, 35064, 65280], [15, 4369, 17476, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4352, 4369, 26214, 34952], [15, 240, 4369, 26214, 52428, 65280], [15, 240, 4369, 26214, 34952, 65348], [15, 240, 4369, 26214, 61166, 65280], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 65280, 65416]]),
  ([15, 240, 4369, 8738, 17476, 43690, 65280], [[240, 4383, 8738, 17476, 43690, 65280], [15, 240, 4369, 26214, 43690, 65280], [15, 240, 4369, 17476, 43690, 65314], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 8738, 17476, 65450]]),
  ([15, 240, 3840, 4369, 17476, 34952, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 3840, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 20292, 34952, 65314], [15, 240, 4369, 17476, 36744, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 4369, 8738, 17476, 34952, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 8738, 17476, 34952, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 4369, 8738, 17476, 35064, 65314], [15, 240, 4369, 26214, 34952, 65314], [15, 240, 4369, 17476, 43690, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 4369, 17476, 34952, 65280, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 65280, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 34952, 65314, 65348], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 17476, 65314, 65416], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 4369, 8738, 17476, 52428, 65280], [[240, 4383, 8738, 17476, 52428, 65280], [15, 240, 4369, 26214, 52428, 65280], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 8738, 52428, 65348], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 3840, 4369, 8738, 34952, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 3840, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 12066, 34952, 65348], [15, 240, 4369, 8738, 36744, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 4369, 8738, 17476, 34952, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 17476, 34952, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 4369, 8738, 17476, 35064, 65348], [15, 240, 4369, 26214, 34952, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 52428, 65348], [15, 240, 4369, 8738, 17476, 65484], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 4369, 8738, 34952, 65280, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 65280, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 34952, 65314, 65348], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 65348, 65416], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 3840, 4369, 8738, 17476, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 3840, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 12066, 17476, 65416], [15, 240, 4369, 8738, 20292, 65416], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 4369, 8738, 17476, 34952, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 34952, 65416], [15, 4369, 8738, 17476, 35064, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 4369, 8738, 17476, 65280, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 65280, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 65280, 65416], [15, 240, 4369, 17476, 65314, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 65348, 65416], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 4369, 26214, 34952, 61440, 65280], [[15, 240, 4369, 26214, 34952, 65280], [15, 240, 4383, 26214, 34952, 65280], [240, 4369, 4383, 26214, 34952, 65280], [240, 4383, 26214, 34952, 61440, 65280], [8, 15, 240, 4369, 26214, 65280], [15, 240, 4369, 26214, 35064, 65280], [15, 4369, 26214, 34952, 35064, 65280], [15, 4369, 26214, 35064, 61440, 65280], [15, 240, 4369, 26214, 34952, 65520], [15, 240, 4352, 4369, 26214, 34952], [15, 240, 4369, 26214, 61166, 65280], [15, 240, 4369, 34952, 63078, 65280], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 65280, 65382], [15, 240, 4369, 26214, 63624, 65280], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 61440, 65416], [15, 240, 4369, 26214, 65280, 65416]]),
  ([15, 240, 4369, 17476, 34952, 61986, 65280], [[240, 4383, 17476, 34952, 61986, 65280], [15, 240, 4369, 34952, 63078, 65280], [15, 240, 4369, 34952, 61986, 65348], [15, 240, 4369, 17476, 61986, 65416], [15, 240, 4369, 17476, 34952, 65314]]),
  ([15, 240, 4369, 17476, 34952, 61440, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61440, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 34952, 62532, 65314], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 17476, 63624, 65314], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 4369, 8738, 34952, 62532, 65280], [[240, 4383, 8738, 34952, 62532, 65280], [15, 240, 4369, 34952, 63078, 65280], [15, 240, 4369, 34952, 62532, 65314], [15, 240, 4369, 8738, 62532, 65416], [15, 240, 4369, 8738, 34952, 65348]]),
  ([15, 240, 4369, 8738, 34952, 61440, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 61440, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 34952, 61986, 65348], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 63624, 65348], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 4369, 8738, 17476, 63624, 65280], [[240, 4383, 8738, 17476, 63624, 65280], [15, 240, 4369, 26214, 63624, 65280], [15, 240, 4369, 17476, 63624, 65314], [15, 240, 4369, 8738, 63624, 65348], [15, 240, 4369, 8738, 17476, 65416]]),
  ([15, 240, 4369, 8738, 17476, 61440, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 61440, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 61440, 65416], [15, 240, 4369, 17476, 61986, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 62532, 65416], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 496, 4369, 8738, 17476, 34952, 61440], [[496, 4383, 8738, 17476, 34952, 61440], [15, 4369, 8738, 17476, 35320, 61440], [15, 496, 4369, 26214, 34952, 61440], [15, 496, 4369, 17476, 34952, 61986], [15, 496, 4369, 8738, 34952, 62532], [15, 496, 4369, 8738, 17476, 63624]]),
  ([15, 240, 4369, 8994, 17476, 34952, 61440], [[240, 4383, 8994, 17476, 34952, 61440], [15, 4369, 8994, 17476, 35064, 61440], [15, 240, 4369, 26470, 34952, 61440], [15, 240, 4369, 17476, 34952, 62242], [15, 240, 4369, 8994, 34952, 62532], [15, 240, 4369, 8994, 17476, 63624]]),
  ([15, 240, 4369, 8738, 17732, 34952, 61440], [[240, 4383, 8738, 17732, 34952, 61440], [15, 4369, 8738, 17732, 35064, 61440], [15, 240, 4369, 26470, 34952, 61440], [15, 240, 4369, 17732, 34952, 61986], [15, 240, 4369, 8738, 34952, 62788], [15, 240, 4369, 8738, 17732, 63624]]),
  ([15, 240, 4369, 8738, 17476, 35208, 61440], [[240, 4383, 8738, 17476, 35208, 61440], [15, 4369, 8738, 17476, 35320, 61440], [15, 240, 4369, 26214, 35208, 61440], [15, 240, 4369, 17476, 35208, 61986], [15, 240, 4369, 8738, 35208, 62532], [15, 240, 4369, 8738, 17476, 63880]]),
  ([15, 240, 4369, 8738, 17476, 34952, 61696], [[240, 4383, 8738, 17476, 34952, 61696], [15, 4369, 8738, 17476, 35064, 61696], [15, 240, 4369, 26214, 34952, 61696], [15, 240, 4369, 17476, 34952, 62242], [15, 240, 4369, 8738, 34952, 62788], [15, 240, 4369, 8738, 17476, 63880]]),
  ([15, 240, 256, 4369, 26214, 34952, 61440], [[240, 256, 4383, 26214, 34952, 61440], [15, 496, 4369, 26214, 34952, 61440], [15, 256, 4369, 26214, 35064, 61440], [15, 240, 4369, 26470, 34952, 61440], [15, 240, 4369, 26214, 35208, 61440], [15, 240, 4369, 26214, 34952, 61696], [15, 240, 256, 4369, 34952, 63078], [15, 240, 256, 4369, 26214, 63624]]),
  ([15, 240, 256, 4369, 17476, 34952, 61986], [[240, 256, 4383, 17476, 34952, 61986], [15, 496, 4369, 17476, 34952, 61986], [15, 240, 4369, 17732, 34952, 61986], [15, 240, 4369, 17476, 35208, 61986], [15, 240, 4369, 17476, 34952, 62242], [15, 240, 256, 4369, 34952, 63078]]),
  ([15, 240, 256, 4369, 8738, 34952, 62532], [[240, 256, 4383, 8738, 34952, 62532], [15, 496, 4369, 8738, 34952, 62532], [15, 240, 4369, 8994, 34952, 62532], [15, 240, 4369, 8738, 35208, 62532], [15, 240, 4369, 8738, 34952, 62788], [15, 240, 256, 4369, 34952, 63078]]),
  ([15, 240, 256, 4369, 8738, 17476, 63624], [[240, 256, 4383, 8738, 17476, 63624], [15, 496, 4369, 8738, 17476, 63624], [15, 240, 4369, 8994, 17476, 63624], [15, 240, 4369, 8738, 17732, 63624], [15, 240, 4369, 8738, 17476, 63880], [15, 240, 256, 4369, 26214, 63624]]),
  ([15, 240, 4369, 12066, 20292, 34952, 61440], [[240, 4383, 12066, 20292, 34952, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 20292, 34952, 65314], [15, 240, 4369, 12066, 34952, 65348], [15, 240, 4369, 12066, 20292, 63624]]),
  ([15, 240, 4369, 12066, 17476, 36744, 61440], [[240, 4383, 12066, 17476, 36744, 61440], [15, 240, 4369, 28518, 36744, 61440], [15, 240, 4369, 17476, 36744, 65314], [15, 240, 4369, 12066, 36744, 62532], [15, 240, 4369, 12066, 17476, 65416]]),
  ([15, 240, 4096, 4369, 12066, 17476, 34952], [[240, 4096, 4383, 12066, 17476, 34952], [15, 4336, 4369, 12066, 17476, 34952], [15, 240, 4369, 16162, 17476, 34952], [15, 240, 4369, 12066, 21572, 34952], [15, 240, 4369, 12066, 17476, 39048], [15, 240, 4096, 4369, 28518, 34952]]),
  ([15, 240, 3840, 4369, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 3840, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4369, 28518, 36744, 61440], [15, 240, 4369, 28518, 34952, 65280], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 4369, 12066, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 12066, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 44970, 61440], [15, 240, 4369, 28518, 34952, 65314], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 12066, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 4369, 17476, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 17476, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 52428, 61440], [15, 240, 4369, 28518, 34952, 62532], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 4369, 12066, 17476, 44970, 61440], [[240, 4383, 12066, 17476, 44970, 61440], [15, 240, 4369, 28518, 44970, 61440], [15, 240, 4369, 17476, 44970, 65314], [15, 240, 4369, 12066, 44970, 62532], [15, 240, 4369, 12066, 17476, 65450]]),
  ([15, 240, 4369, 12066, 17476, 34952, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 12066, 17476, 34952, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 28518, 34952, 65314], [15, 240, 4369, 17476, 44970, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 12066, 17476, 65450], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 4369, 12066, 17476, 52428, 61440], [[240, 4383, 12066, 17476, 52428, 61440], [15, 240, 4369, 28518, 52428, 61440], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 12066, 52428, 62532], [15, 240, 4369, 12066, 17476, 64716]]),
  ([15, 240, 3840, 4369, 12066, 34952, 62532], [[15, 240, 4369, 12066, 34952, 62532], [15, 240, 4383, 12066, 34952, 62532], [240, 3840, 4383, 12066, 34952, 62532], [240, 4369, 4383, 12066, 34952, 62532], [8, 15, 240, 4369, 12066, 62532], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 12066, 36744, 62532], [15, 240, 4369, 12066, 34952, 65348], [15, 240, 4369, 12066, 44970, 62532], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 12066, 62532, 64716]]),
  ([15, 240, 4369, 12066, 17476, 34952, 62532], [[15, 240, 4369, 12066, 34952, 62532], [15, 240, 4383, 12066, 34952, 62532], [240, 4369, 4383, 12066, 34952, 62532], [240, 4383, 12066, 17476, 34952, 62532], [8, 15, 240, 4369, 12066, 62532], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 28518, 34952, 62532], [15, 240, 4369, 12066, 44970, 62532], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 12066, 52428, 62532], [15, 240, 4369, 12066, 17476, 64716], [15, 240, 4369, 12066, 62532, 64716]]),
  ([15, 240, 4369, 12066, 34952, 61440, 62532], [[15, 240, 4369, 12066, 34952, 62532], [15, 240, 4383, 12066, 34952, 62532], [240, 4369, 4383, 12066, 34952, 62532], [240, 4383, 12066, 34952, 61440, 62532], [8, 15, 240, 4369, 12066, 62532], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 12066, 44970, 62532], [15, 240, 4369, 34952, 62532, 65314], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 12066, 62532, 63624], [15, 240, 4369, 12066, 62532, 64716]]),
  ([15, 240, 3840, 4369, 12066, 17476, 63624], [[15, 240, 4369, 12066, 17476, 63624], [15, 240, 4383, 12066, 17476, 63624], [240, 3840, 4383, 12066, 17476, 63624], [240, 4369, 4383, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 63736], [15, 240, 4369, 12066, 20292, 63624], [15, 240, 4369, 12066, 17476, 65416], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 12066, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 12066, 17476, 65450], [15, 240, 4369, 12066, 17476, 64716]]),
  ([15, 240, 4369, 12066, 17476, 34952, 63624], [[15, 240, 4369, 12066, 17476, 63624], [15, 240, 4383, 12066, 17476, 63624], [240, 4369, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 34952, 63624], [15, 240, 4369, 12066, 17476, 63736], [15, 240, 4369, 12066, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 12066, 17476, 65450], [15, 240, 4369, 12066, 17476, 64716]]),
  ([15, 240, 4369, 12066, 17476, 61440, 63624], [[15, 240, 4369, 12066, 17476, 63624], [15, 240, 4383, 12066, 17476, 63624], [240, 4369, 4383, 12066, 17476, 63624], [240, 4383, 12066, 17476, 61440, 63624], [15, 240, 4369, 12066, 17476, 63736], [15, 240, 4369, 12066, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 28518, 61440, 63624], [15, 240, 4369, 17476, 63624, 65314], [15, 240, 4369, 12066, 17476, 65450], [15, 240, 4369, 12066, 62532, 63624], [15, 240, 4369, 12066, 17476, 64716]]),
  ([15, 240, 4369, 12066, 26214, 34952, 61440], [[240, 4383, 12066, 26214, 34952, 61440], [15, 4369, 12066, 26214, 35064, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 26214, 44970, 61440], [15, 240, 4369, 26214, 34952, 65314], [15, 240, 4369, 12066, 34952, 63078], [15, 240, 4369, 12066, 26214, 63624]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk6_2 : pairs6_2.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  decide +kernel

def pairs6_3 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 4369, 12066, 17476, 43690, 61440], [[240, 4383, 12066, 17476, 43690, 61440], [15, 240, 4369, 28518, 43690, 61440], [15, 240, 4369, 17476, 43690, 65314], [15, 240, 4369, 12066, 43690, 62532], [15, 240, 4369, 12066, 17476, 64170]]),
  ([15, 240, 4369, 12066, 17476, 34952, 61986], [[240, 4383, 12066, 17476, 34952, 61986], [15, 4369, 12066, 17476, 35064, 61986], [15, 240, 4369, 28518, 34952, 61986], [15, 240, 4369, 17476, 44970, 61986], [15, 240, 4369, 17476, 34952, 65314], [15, 240, 4369, 12066, 34952, 63078], [15, 240, 4369, 12066, 17476, 64170]]),
  ([15, 240, 4369, 8738, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 8738, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 43690, 61440], [15, 240, 4369, 28518, 34952, 61986], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 4369, 8738, 17476, 44970, 61440], [[240, 4383, 8738, 17476, 44970, 61440], [15, 240, 4369, 26214, 44970, 61440], [15, 240, 4369, 17476, 44970, 61986], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 8738, 17476, 65450]]),
  ([15, 240, 4369, 8738, 12066, 34952, 62532], [[15, 240, 4369, 12066, 34952, 62532], [15, 240, 4383, 12066, 34952, 62532], [240, 4369, 4383, 12066, 34952, 62532], [240, 4383, 8738, 12066, 34952, 62532], [8, 15, 240, 4369, 12066, 62532], [15, 240, 4369, 12066, 35064, 62532], [15, 240, 4369, 12066, 43690, 62532], [15, 240, 4369, 12066, 34952, 63078], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 12066, 44970, 62532], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 12066, 34952, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 12066, 62532, 64716]]),
  ([15, 240, 4369, 8738, 12066, 17476, 63624], [[15, 240, 4369, 12066, 17476, 63624], [15, 240, 4383, 12066, 17476, 63624], [240, 4369, 4383, 12066, 17476, 63624], [240, 4383, 8738, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 63736], [15, 240, 4369, 12066, 26214, 63624], [15, 240, 4369, 12066, 17476, 64170], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 12066, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 12066, 17476, 65450], [15, 240, 4369, 12066, 17476, 64716]]),
  ([15, 240, 4369, 8738, 20292, 36744, 61440], [[240, 4383, 8738, 20292, 36744, 61440], [15, 240, 4369, 28518, 36744, 61440], [15, 240, 4369, 20292, 36744, 61986], [15, 240, 4369, 8738, 36744, 65348], [15, 240, 4369, 8738, 20292, 65416]]),
  ([15, 240, 4096, 4369, 8738, 20292, 34952], [[240, 4096, 4383, 8738, 20292, 34952], [15, 4336, 4369, 8738, 20292, 34952], [15, 240, 4369, 12834, 20292, 34952], [15, 240, 4369, 8738, 24388, 34952], [15, 240, 4369, 8738, 20292, 39048], [15, 240, 4096, 4369, 28518, 34952]]),
  ([15, 240, 4369, 20292, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 20292, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 53196, 61440], [15, 240, 4369, 28518, 34952, 65348], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 20292, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 4369, 8738, 20292, 43690, 61440], [[240, 4383, 8738, 20292, 43690, 61440], [15, 240, 4369, 28518, 43690, 61440], [15, 240, 4369, 20292, 43690, 61986], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 8738, 20292, 64170]]),
  ([15, 240, 3840, 4369, 20292, 34952, 61986], [[15, 240, 4369, 20292, 34952, 61986], [15, 240, 4383, 20292, 34952, 61986], [240, 3840, 4383, 20292, 34952, 61986], [240, 4369, 4383, 20292, 34952, 61986], [8, 15, 240, 4369, 20292, 61986], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 20292, 36744, 61986], [15, 240, 4369, 20292, 34952, 65314], [15, 240, 4369, 20292, 53196, 61986], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 20292, 61986, 64170]]),
  ([15, 240, 4369, 8738, 20292, 34952, 61986], [[15, 240, 4369, 20292, 34952, 61986], [15, 240, 4383, 20292, 34952, 61986], [240, 4369, 4383, 20292, 34952, 61986], [240, 4383, 8738, 20292, 34952, 61986], [8, 15, 240, 4369, 20292, 61986], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 28518, 34952, 61986], [15, 240, 4369, 20292, 43690, 61986], [15, 240, 4369, 20292, 53196, 61986], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 20292, 61986, 64170]]),
  ([15, 240, 4369, 20292, 34952, 61440, 61986], [[15, 240, 4369, 20292, 34952, 61986], [15, 240, 4383, 20292, 34952, 61986], [240, 4369, 4383, 20292, 34952, 61986], [240, 4383, 20292, 34952, 61440, 61986], [8, 15, 240, 4369, 20292, 61986], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 20292, 53196, 61986], [15, 240, 4369, 34952, 61986, 65348], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 20292, 61986, 63624], [15, 240, 4369, 20292, 61986, 64170]]),
  ([15, 240, 4369, 8738, 20292, 53196, 61440], [[240, 4383, 8738, 20292, 53196, 61440], [15, 240, 4369, 28518, 53196, 61440], [15, 240, 4369, 20292, 53196, 61986], [15, 240, 4369, 8738, 53196, 65348], [15, 240, 4369, 8738, 20292, 65484]]),
  ([15, 240, 4369, 8738, 20292, 34952, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 20292, 34952, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 28518, 34952, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 53196, 65348], [15, 240, 4369, 8738, 20292, 65484], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 3840, 4369, 8738, 20292, 63624], [[15, 240, 4369, 8738, 20292, 63624], [15, 240, 4383, 8738, 20292, 63624], [240, 3840, 4383, 8738, 20292, 63624], [240, 4369, 4383, 8738, 20292, 63624], [15, 240, 4369, 8738, 20292, 63736], [15, 240, 4369, 12066, 20292, 63624], [15, 240, 4369, 8738, 20292, 65416], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 20292, 28518, 63624], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 8738, 20292, 65484]]),
  ([15, 240, 4369, 8738, 20292, 34952, 63624], [[15, 240, 4369, 8738, 20292, 63624], [15, 240, 4383, 8738, 20292, 63624], [240, 4369, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 34952, 63624], [15, 240, 4369, 8738, 20292, 63736], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 20292, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 8738, 20292, 65484]]),
  ([15, 240, 4369, 8738, 20292, 61440, 63624], [[15, 240, 4369, 8738, 20292, 63624], [15, 240, 4383, 8738, 20292, 63624], [240, 4369, 4383, 8738, 20292, 63624], [240, 4383, 8738, 20292, 61440, 63624], [15, 240, 4369, 8738, 20292, 63736], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 20292, 28518, 63624], [15, 240, 4369, 28518, 61440, 63624], [15, 240, 4369, 20292, 61986, 63624], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 8738, 63624, 65348], [15, 240, 4369, 8738, 20292, 65484]]),
  ([15, 240, 4369, 20292, 26214, 34952, 61440], [[240, 4383, 20292, 26214, 34952, 61440], [15, 4369, 20292, 26214, 35064, 61440], [15, 240, 4369, 28518, 34952, 61440], [15, 240, 4369, 26214, 53196, 61440], [15, 240, 4369, 26214, 34952, 65348], [15, 240, 4369, 20292, 34952, 63078], [15, 240, 4369, 20292, 26214, 63624]]),
  ([15, 240, 4369, 17476, 20292, 34952, 61986], [[15, 240, 4369, 20292, 34952, 61986], [15, 240, 4383, 20292, 34952, 61986], [240, 4369, 4383, 20292, 34952, 61986], [240, 4383, 17476, 20292, 34952, 61986], [8, 15, 240, 4369, 20292, 61986], [15, 240, 4369, 20292, 35064, 61986], [15, 240, 4369, 20292, 52428, 61986], [15, 240, 4369, 20292, 34952, 63078], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 20292, 53196, 61986], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 20292, 34952, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 20292, 61986, 64170]]),
  ([15, 240, 4369, 8738, 20292, 52428, 61440], [[240, 4383, 8738, 20292, 52428, 61440], [15, 240, 4369, 28518, 52428, 61440], [15, 240, 4369, 20292, 52428, 61986], [15, 240, 4369, 8738, 52428, 65348], [15, 240, 4369, 8738, 20292, 64716]]),
  ([15, 240, 4369, 8738, 20292, 34952, 62532], [[240, 4383, 8738, 20292, 34952, 62532], [15, 4369, 8738, 20292, 35064, 62532], [15, 240, 4369, 28518, 34952, 62532], [15, 240, 4369, 20292, 34952, 63078], [15, 240, 4369, 8738, 53196, 62532], [15, 240, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 20292, 64716]]),
  ([15, 240, 4369, 8738, 17476, 53196, 61440], [[240, 4383, 8738, 17476, 53196, 61440], [15, 240, 4369, 26214, 53196, 61440], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 8738, 53196, 62532], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 4369, 8738, 17476, 20292, 63624], [[15, 240, 4369, 8738, 20292, 63624], [15, 240, 4383, 8738, 20292, 63624], [240, 4369, 4383, 8738, 20292, 63624], [240, 4383, 8738, 17476, 20292, 63624], [15, 240, 4369, 8738, 20292, 63736], [15, 240, 4369, 20292, 26214, 63624], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 20292, 28518, 63624], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 8738, 20292, 64716], [15, 240, 4369, 8738, 17476, 65484], [15, 240, 4369, 8738, 20292, 65484]]),
  ([15, 240, 4096, 4369, 8738, 17476, 36744], [[240, 4096, 4383, 8738, 17476, 36744], [15, 4336, 4369, 8738, 17476, 36744], [15, 240, 4369, 12834, 17476, 36744], [15, 240, 4369, 8738, 21572, 36744], [15, 240, 4369, 8738, 17476, 40840], [15, 240, 4096, 4369, 26214, 36744]]),
  ([15, 240, 3840, 4369, 26214, 36744, 61440], [[15, 240, 4369, 26214, 36744, 61440], [15, 240, 4383, 26214, 36744, 61440], [240, 3840, 4383, 26214, 36744, 61440], [240, 4369, 4383, 26214, 36744, 61440], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4369, 28518, 36744, 61440], [15, 240, 4369, 26214, 36744, 65280], [15, 240, 4096, 4369, 26214, 36744], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 26214, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 26214, 36744, 65416], [15, 240, 4369, 26214, 61440, 65416]]),
  ([15, 240, 4369, 8738, 26214, 36744, 61440], [[15, 240, 4369, 26214, 36744, 61440], [15, 240, 4383, 26214, 36744, 61440], [240, 4369, 4383, 26214, 36744, 61440], [240, 4383, 8738, 26214, 36744, 61440], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4096, 4369, 26214, 36744], [15, 240, 4369, 26214, 44970, 61440], [15, 240, 4369, 26214, 36744, 61986], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 26214, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 26214, 36744, 65416], [15, 240, 4369, 26214, 61440, 65416]]),
  ([15, 240, 4369, 17476, 26214, 36744, 61440], [[15, 240, 4369, 26214, 36744, 61440], [15, 240, 4383, 26214, 36744, 61440], [240, 4369, 4383, 26214, 36744, 61440], [240, 4383, 17476, 26214, 36744, 61440], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4096, 4369, 26214, 36744], [15, 240, 4369, 26214, 53196, 61440], [15, 240, 4369, 26214, 36744, 62532], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 26214, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 36744, 65416], [15, 240, 4369, 26214, 61440, 65416]]),
  ([15, 240, 3840, 4369, 17476, 36744, 61986], [[15, 240, 4369, 17476, 36744, 61986], [15, 240, 4383, 17476, 36744, 61986], [240, 3840, 4383, 17476, 36744, 61986], [240, 4369, 4383, 17476, 36744, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 20292, 36744, 61986], [15, 240, 4369, 17476, 36744, 65314], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 36744, 61986, 63078], [15, 240, 4369, 17476, 61986, 65450]]),
  ([15, 240, 4369, 8738, 17476, 36744, 61986], [[15, 240, 4369, 17476, 36744, 61986], [15, 240, 4383, 17476, 36744, 61986], [240, 4369, 4383, 17476, 36744, 61986], [240, 4383, 8738, 17476, 36744, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 26214, 36744, 61986], [15, 240, 4369, 17476, 44970, 61986], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 36744, 61986, 63078], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 17476, 61986, 65450]]),
  ([15, 240, 4369, 17476, 36744, 61440, 61986], [[15, 240, 4369, 17476, 36744, 61986], [15, 240, 4383, 17476, 36744, 61986], [240, 4369, 4383, 17476, 36744, 61986], [240, 4383, 17476, 36744, 61440, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 36744, 61986, 62532], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 36744, 61986, 63078], [15, 240, 4369, 17476, 61986, 65416], [15, 240, 4369, 17476, 61986, 65450]]),
  ([15, 240, 3840, 4369, 8738, 36744, 62532], [[15, 240, 4369, 8738, 36744, 62532], [15, 240, 4383, 8738, 36744, 62532], [240, 3840, 4383, 8738, 36744, 62532], [240, 4369, 4383, 8738, 36744, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 12066, 36744, 62532], [15, 240, 4369, 8738, 36744, 65348], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 36744, 62532, 63078], [15, 240, 4369, 8738, 62532, 65484]]),
  ([15, 240, 4369, 8738, 17476, 36744, 62532], [[15, 240, 4369, 8738, 36744, 62532], [15, 240, 4383, 8738, 36744, 62532], [240, 4369, 4383, 8738, 36744, 62532], [240, 4383, 8738, 17476, 36744, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 26214, 36744, 62532], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 36744, 62532, 63078], [15, 240, 4369, 8738, 53196, 62532], [15, 240, 4369, 8738, 17476, 65484], [15, 240, 4369, 8738, 62532, 65484]]),
  ([15, 240, 4369, 8738, 36744, 61440, 62532], [[15, 240, 4369, 8738, 36744, 62532], [15, 240, 4383, 8738, 36744, 62532], [240, 4369, 4383, 8738, 36744, 62532], [240, 4383, 8738, 36744, 61440, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 36744, 61986, 62532], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 36744, 62532, 63078], [15, 240, 4369, 8738, 62532, 65416], [15, 240, 4369, 8738, 62532, 65484]]),
  ([15, 240, 4369, 8738, 17476, 36744, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 36744, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 36744, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 4369, 26214, 34952, 36744, 61440], [[15, 240, 4369, 26214, 36744, 61440], [15, 240, 4383, 26214, 36744, 61440], [240, 4369, 4383, 26214, 36744, 61440], [240, 4383, 26214, 34952, 36744, 61440], [15, 4369, 26214, 35064, 36744, 61440], [15, 240, 4369, 26214, 36856, 61440], [15, 240, 4369, 26214, 36744, 61680], [15, 240, 4096, 4369, 26214, 36744], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 4369, 26214, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 26214, 36744, 63624], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 36744, 65416], [15, 240, 4369, 26214, 61440, 65416]]),
  ([15, 240, 4369, 17476, 34952, 36744, 61986], [[15, 240, 4369, 17476, 36744, 61986], [15, 240, 4383, 17476, 36744, 61986], [240, 4369, 4383, 17476, 36744, 61986], [240, 4383, 17476, 34952, 36744, 61986], [15, 240, 4369, 17476, 36856, 61986], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 61986, 63078], [15, 240, 4369, 17476, 61986, 65450]]),
  ([15, 240, 4369, 8738, 34952, 36744, 62532], [[15, 240, 4369, 8738, 36744, 62532], [15, 240, 4383, 8738, 36744, 62532], [240, 4369, 4383, 8738, 36744, 62532], [240, 4383, 8738, 34952, 36744, 62532], [15, 240, 4369, 8738, 36856, 62532], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 62532, 63078], [15, 240, 4369, 8738, 62532, 65484]]),
  ([15, 240, 4369, 8738, 17476, 36744, 63624], [[240, 4383, 8738, 17476, 36744, 63624], [15, 240, 4369, 26214, 36744, 63624], [15, 240, 4369, 8738, 17476, 65416]]),
  ([15, 3840, 4336, 4369, 8738, 17476, 34952], [[3840, 4336, 4383, 8738, 17476, 34952], [15, 4336, 4369, 12066, 17476, 34952], [15, 4336, 4369, 8738, 20292, 34952], [15, 4336, 4369, 8738, 17476, 36744], [15, 3840, 4369, 8738, 17476, 39160], [15, 3840, 4336, 4369, 26214, 34952]]),
  ([15, 240, 4369, 7936, 8738, 17476, 34952], [[240, 4383, 7936, 8738, 17476, 34952], [15, 4369, 7936, 8738, 17476, 35064], [15, 240, 4369, 16162, 17476, 34952], [15, 240, 4369, 8738, 24388, 34952], [15, 240, 4369, 8738, 17476, 40840], [15, 240, 4369, 7936, 26214, 34952]]),
  ([15, 240, 3840, 4369, 12834, 17476, 34952], [[240, 3840, 4383, 12834, 17476, 34952], [15, 3840, 4369, 12834, 17476, 35064], [15, 240, 4369, 16162, 17476, 34952], [15, 240, 4369, 12834, 20292, 34952], [15, 240, 4369, 12834, 17476, 36744], [15, 240, 3840, 4369, 30310, 34952]]),
  ([15, 240, 3840, 4369, 8738, 21572, 34952], [[240, 3840, 4383, 8738, 21572, 34952], [15, 3840, 4369, 8738, 21572, 35064], [15, 240, 4369, 12066, 21572, 34952], [15, 240, 4369, 8738, 24388, 34952], [15, 240, 4369, 8738, 21572, 36744], [15, 240, 3840, 4369, 30310, 34952]]),
  ([15, 240, 3840, 4369, 8738, 17476, 39048], [[240, 3840, 4383, 8738, 17476, 39048], [15, 3840, 4369, 8738, 17476, 39160], [15, 240, 4369, 12066, 17476, 39048], [15, 240, 4369, 8738, 20292, 39048], [15, 240, 4369, 8738, 17476, 40840], [15, 240, 3840, 4369, 26214, 39048]]),
  ([15, 240, 3840, 4096, 4369, 26214, 34952], [[240, 3840, 4096, 4383, 26214, 34952], [15, 3840, 4336, 4369, 26214, 34952], [15, 3840, 4096, 4369, 26214, 35064], [15, 240, 4369, 7936, 26214, 34952], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4096, 4369, 26214, 36744], [15, 240, 3840, 4369, 30310, 34952], [15, 240, 3840, 4369, 26214, 39048]]),
  ([15, 240, 4369, 17476, 34952, 61986, 65314], [[15, 240, 4369, 17476, 34952, 65314], [15, 240, 4383, 17476, 34952, 65314], [240, 4369, 4383, 17476, 34952, 65314], [240, 4383, 17476, 34952, 61986, 65314], [8, 15, 240, 4369, 17476, 65314], [15, 240, 4369, 17476, 35064, 65314], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 4369, 34952, 63078, 65314], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 34952, 65314, 65382], [15, 240, 4369, 17476, 64170, 65314], [15, 240, 4369, 17476, 61986, 65450], [15, 240, 4369, 17476, 65314, 65450]]),
  ([15, 240, 3840, 4369, 17476, 52428, 61986], [[240, 3840, 4383, 17476, 52428, 61986], [15, 240, 4369, 20292, 52428, 61986], [15, 240, 4369, 17476, 53196, 61986], [15, 240, 4369, 17476, 52428, 65314], [15, 240, 3840, 4369, 52428, 63078]]),
  ([15, 240, 3840, 4369, 34952, 61986, 62532], [[240, 3840, 4383, 34952, 61986, 62532], [15, 240, 4369, 36744, 61986, 62532], [15, 240, 4369, 34952, 62532, 65314], [15, 240, 4369, 34952, 61986, 65348], [15, 240, 3840, 4369, 34952, 63078]]),
  ([15, 240, 3840, 4369, 17476, 34952, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 17476, 34952, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 4369, 20292, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 17476, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 17476, 34952, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 52428, 63078], [15, 240, 3840, 4369, 63078, 65262]]),
  ([15, 240, 3840, 4369, 34952, 61440, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 34952, 61440, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 61440, 63078], [15, 240, 4369, 34952, 63078, 65280], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 63078, 63624], [15, 240, 3840, 4369, 63078, 65262]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk6_3 : pairs6_3.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  decide +kernel

def pairs6_4 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 3840, 4369, 34952, 61986, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 34952, 61986, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 61986, 63078], [15, 240, 4369, 34952, 63078, 65314], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 34952, 61986, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 63078, 64170], [15, 240, 3840, 4369, 63078, 65262]]),
  ([15, 240, 3840, 4369, 17476, 61986, 63624], [[240, 3840, 4383, 17476, 61986, 63624], [15, 240, 4369, 20292, 61986, 63624], [15, 240, 4369, 17476, 63624, 65314], [15, 240, 4369, 17476, 61986, 65416], [15, 240, 3840, 4369, 63078, 63624]]),
  ([15, 240, 3840, 4369, 17476, 61986, 64170], [[240, 3840, 4383, 17476, 61986, 64170], [15, 240, 4369, 20292, 61986, 64170], [15, 240, 4369, 17476, 64170, 65314], [15, 240, 4369, 17476, 61986, 65450], [15, 240, 3840, 4369, 63078, 64170]]),
  ([15, 240, 3840, 4369, 26214, 34952, 61986], [[240, 3840, 4383, 26214, 34952, 61986], [15, 3840, 4369, 26214, 35064, 61986], [15, 240, 4369, 28518, 34952, 61986], [15, 240, 4369, 26214, 36744, 61986], [15, 240, 4369, 26214, 34952, 65314], [15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4369, 26214, 64170]]),
  ([15, 240, 3840, 4369, 17476, 43690, 61986], [[240, 3840, 4383, 17476, 43690, 61986], [15, 240, 4369, 20292, 43690, 61986], [15, 240, 4369, 17476, 44970, 61986], [15, 240, 4369, 17476, 43690, 65314], [15, 240, 3840, 4369, 43690, 63078]]),
  ([15, 240, 3840, 4369, 8738, 34952, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 8738, 34952, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 4369, 12066, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 8738, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 43690, 63078], [15, 240, 3840, 4369, 63078, 65262]]),
  ([15, 240, 3840, 4369, 8738, 17476, 64170], [[240, 3840, 4383, 8738, 17476, 64170], [15, 240, 4369, 12066, 17476, 64170], [15, 240, 4369, 8738, 20292, 64170], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 3840, 4369, 26214, 64170]]),
  ([15, 240, 4369, 8738, 34952, 62532, 65348], [[15, 240, 4369, 8738, 34952, 65348], [15, 240, 4383, 8738, 34952, 65348], [240, 4369, 4383, 8738, 34952, 65348], [240, 4383, 8738, 34952, 62532, 65348], [8, 15, 240, 4369, 8738, 65348], [15, 240, 4369, 8738, 35064, 65348], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 4369, 34952, 63078, 65348], [15, 240, 4369, 8738, 34952, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 34952, 65348, 65382], [15, 240, 4369, 8738, 64716, 65348], [15, 240, 4369, 8738, 62532, 65484], [15, 240, 4369, 8738, 65348, 65484]]),
  ([15, 240, 3840, 4369, 8738, 43690, 62532], [[240, 3840, 4383, 8738, 43690, 62532], [15, 240, 4369, 12066, 43690, 62532], [15, 240, 4369, 8738, 44970, 62532], [15, 240, 4369, 8738, 43690, 65348], [15, 240, 3840, 4369, 43690, 63078]]),
  ([15, 240, 3840, 4369, 34952, 62532, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 34952, 62532, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 4369, 36744, 62532, 63078], [15, 240, 4369, 34952, 63078, 65348], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 34952, 62532, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 63078, 64716], [15, 240, 3840, 4369, 63078, 65262]]),
  ([15, 240, 3840, 4369, 8738, 62532, 63624], [[240, 3840, 4383, 8738, 62532, 63624], [15, 240, 4369, 12066, 62532, 63624], [15, 240, 4369, 8738, 63624, 65348], [15, 240, 4369, 8738, 62532, 65416], [15, 240, 3840, 4369, 63078, 63624]]),
  ([15, 240, 3840, 4369, 8738, 62532, 64716], [[240, 3840, 4383, 8738, 62532, 64716], [15, 240, 4369, 12066, 62532, 64716], [15, 240, 4369, 8738, 64716, 65348], [15, 240, 4369, 8738, 62532, 65484], [15, 240, 3840, 4369, 63078, 64716]]),
  ([15, 240, 3840, 4369, 26214, 34952, 62532], [[240, 3840, 4383, 26214, 34952, 62532], [15, 3840, 4369, 26214, 35064, 62532], [15, 240, 4369, 28518, 34952, 62532], [15, 240, 4369, 26214, 36744, 62532], [15, 240, 4369, 26214, 34952, 65348], [15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4369, 26214, 64716]]),
  ([15, 240, 3840, 4369, 8738, 52428, 62532], [[240, 3840, 4383, 8738, 52428, 62532], [15, 240, 4369, 12066, 52428, 62532], [15, 240, 4369, 8738, 53196, 62532], [15, 240, 4369, 8738, 52428, 65348], [15, 240, 3840, 4369, 52428, 63078]]),
  ([15, 240, 3840, 4369, 8738, 17476, 64716], [[240, 3840, 4383, 8738, 17476, 64716], [15, 240, 4369, 12066, 17476, 64716], [15, 240, 4369, 8738, 20292, 64716], [15, 240, 4369, 8738, 17476, 65484], [15, 240, 3840, 4369, 26214, 64716]]),
  ([15, 240, 4369, 8738, 17476, 63624, 65416], [[15, 240, 4369, 8738, 17476, 65416], [15, 240, 4383, 8738, 17476, 65416], [240, 4369, 4383, 8738, 17476, 65416], [240, 4383, 8738, 17476, 63624, 65416], [15, 240, 4369, 8738, 17476, 65528], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 63624, 65416], [15, 240, 4369, 8738, 17476, 65450], [15, 240, 4369, 8738, 17476, 65484]]),
  ([15, 240, 3840, 4369, 8738, 26214, 63624], [[15, 240, 3840, 4369, 26214, 63624], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 8738, 26214, 63624], [15, 240, 4080, 4369, 26214, 63624], [15, 240, 3840, 4369, 26214, 63736], [15, 240, 256, 4369, 26214, 63624], [15, 240, 4369, 12066, 26214, 63624], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 8738, 28518, 63624], [15, 240, 4369, 26214, 28518, 63624], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 8738, 26214, 65416], [15, 240, 4369, 26214, 63624, 65416], [15, 240, 3840, 4369, 26214, 64170], [15, 240, 3840, 4369, 26214, 65262]]),
  ([15, 240, 3840, 4369, 17476, 26214, 63624], [[15, 240, 3840, 4369, 26214, 63624], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 17476, 26214, 63624], [15, 240, 4080, 4369, 26214, 63624], [15, 240, 3840, 4369, 26214, 63736], [15, 240, 256, 4369, 26214, 63624], [15, 240, 4369, 20292, 26214, 63624], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 17476, 28518, 63624], [15, 240, 4369, 26214, 28518, 63624], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 17476, 26214, 65416], [15, 240, 4369, 26214, 63624, 65416], [15, 240, 3840, 4369, 26214, 64716], [15, 240, 3840, 4369, 26214, 65262]]),
  ([15, 240, 3840, 4369, 26214, 61440, 63624], [[15, 240, 3840, 4369, 26214, 63624], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 26214, 61440, 63624], [15, 240, 4080, 4369, 26214, 63624], [15, 240, 3840, 4369, 26214, 63736], [15, 240, 256, 4369, 26214, 63624], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 26214, 28518, 63624], [15, 240, 4369, 28518, 61440, 63624], [15, 240, 4369, 26214, 63624, 65280], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 26214, 61440, 65416], [15, 240, 4369, 26214, 63624, 65416], [15, 240, 3840, 4369, 63078, 63624], [15, 240, 3840, 4369, 26214, 65262]]),
  ([15, 240, 3840, 4369, 26214, 34952, 63624], [[15, 240, 3840, 4369, 26214, 63624], [15, 240, 3840, 4383, 26214, 63624], [240, 3840, 4369, 4383, 26214, 63624], [240, 3840, 4383, 26214, 34952, 63624], [15, 240, 4080, 4369, 26214, 63624], [15, 3840, 4369, 26214, 35064, 63624], [15, 240, 3840, 4369, 26214, 63736], [15, 240, 256, 4369, 26214, 63624], [15, 240, 3840, 4369, 28518, 63624], [15, 240, 4369, 26214, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 26214, 36744, 63624], [15, 240, 3840, 4369, 26214, 65416], [15, 240, 4369, 26214, 34952, 65416], [15, 240, 4369, 26214, 63624, 65416], [15, 240, 3840, 4369, 26214, 65262]]),
  ([15, 240, 4369, 26214, 28518, 34952, 61440], [[15, 240, 4369, 28518, 34952, 61440], [15, 240, 4383, 28518, 34952, 61440], [240, 4369, 4383, 28518, 34952, 61440], [240, 4383, 26214, 28518, 34952, 61440], [8, 15, 240, 4369, 28518, 61440], [15, 240, 4369, 28518, 35064, 61440], [15, 4369, 26214, 28518, 35064, 61440], [15, 240, 4369, 28518, 34952, 61680], [15, 240, 4096, 4369, 28518, 34952], [15, 240, 4369, 28518, 61166, 61440], [15, 240, 4369, 28518, 34952, 63078], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 4369, 28518, 61422, 61440], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 28518, 34952, 65382], [15, 240, 4369, 34952, 61440, 65382], [15, 240, 4369, 26214, 28518, 63624], [15, 240, 4369, 28518, 34952, 63624], [15, 240, 4369, 28518, 61440, 63624]]),
  ([15, 240, 3840, 4369, 26214, 43690, 61440], [[240, 3840, 4383, 26214, 43690, 61440], [15, 240, 4369, 28518, 43690, 61440], [15, 240, 4369, 26214, 44970, 61440], [15, 240, 4369, 26214, 43690, 65280], [15, 240, 3840, 4369, 43690, 63078], [15, 240, 3840, 4369, 26214, 64170]]),
  ([15, 240, 3840, 4369, 26214, 61166, 61440], [[240, 3840, 4383, 26214, 61166, 61440], [14, 240, 3840, 4369, 26214, 61440], [15, 240, 4369, 28518, 61166, 61440], [15, 240, 4369, 26214, 61422, 61440], [15, 240, 4369, 26214, 61166, 65280], [15, 240, 3840, 4369, 61166, 63078], [15, 240, 3840, 4369, 26214, 65262]]),
  ([15, 240, 3840, 4369, 26214, 34952, 63078], [[15, 240, 3840, 4369, 34952, 63078], [15, 240, 3840, 4383, 34952, 63078], [240, 3840, 4369, 4383, 34952, 63078], [240, 3840, 4383, 26214, 34952, 63078], [8, 15, 240, 3840, 4369, 63078], [15, 240, 4080, 4369, 34952, 63078], [15, 240, 3840, 4369, 35064, 63078], [15, 3840, 4369, 26214, 35064, 63078], [15, 240, 256, 4369, 34952, 63078], [15, 240, 4369, 28518, 34952, 63078], [15, 240, 3840, 4369, 36744, 63078], [15, 240, 4369, 26214, 36744, 63078], [15, 240, 4369, 34952, 36744, 63078], [15, 240, 3840, 4369, 34952, 65382], [15, 240, 4369, 26214, 34952, 65382], [15, 240, 4369, 34952, 63078, 65382], [15, 240, 3840, 4369, 61166, 63078], [15, 240, 3840, 4369, 26214, 65262], [15, 240, 3840, 4369, 63078, 65262]]),
  ([15, 240, 3840, 4369, 26214, 52428, 61440], [[240, 3840, 4383, 26214, 52428, 61440], [15, 240, 4369, 28518, 52428, 61440], [15, 240, 4369, 26214, 53196, 61440], [15, 240, 4369, 26214, 52428, 65280], [15, 240, 3840, 4369, 52428, 63078], [15, 240, 3840, 4369, 26214, 64716]])]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk6_4 : pairs6_4.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  decide +kernel

def pairs6 : List (List ℕ × List (List ℕ)) := pairs6_0 ++ pairs6_1 ++ pairs6_2 ++ pairs6_3 ++ pairs6_4

set_option maxRecDepth 20000 in
theorem pairs6_fst : pairs6.map Prod.fst = row6 := rfl

theorem chk6 : pairs6.all (fun p => verifyFast 4478 negs 5 p.1 p.2 row5) = true := by
  unfold pairs6
  simp only [List.all_append, Bool.and_eq_true, chk6_0, chk6_1, chk6_2, chk6_3, chk6_4, and_self]

def pairs7 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [[240, 3840, 4383, 8738, 17476, 34952, 61440], [15, 3840, 4369, 8738, 17476, 35064, 61440], [15, 240, 4369, 12066, 17476, 34952, 61440], [15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 4369, 8738, 17476, 34952, 65280], [15, 240, 3840, 4369, 26214, 34952, 61440], [15, 240, 3840, 4369, 17476, 34952, 61986], [15, 240, 3840, 4369, 8738, 34952, 62532], [15, 240, 3840, 4369, 8738, 17476, 63624]]),
  ([15, 240, 3840, 4383, 8738, 17476, 34952, 61440], [[240, 3840, 4383, 8738, 17476, 34952, 61440], [240, 4080, 4383, 8738, 17476, 34952, 61440], [15, 3840, 4383, 8738, 17476, 35064, 61440], [240, 3840, 4383, 8738, 17476, 35064, 61440], [3840, 4383, 8738, 17476, 34952, 35064, 61440], [240, 3840, 4383, 8738, 17476, 34952, 61680], [240, 256, 4383, 8738, 17476, 34952, 61440], [15, 240, 4383, 12066, 17476, 34952, 61440], [240, 3840, 4383, 12066, 17476, 34952, 61440], [240, 4383, 8738, 12066, 17476, 34952, 61440], [15, 240, 4383, 8738, 20292, 34952, 61440], [240, 3840, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 17476, 20292, 34952, 61440], [15, 240, 4383, 8738, 17476, 36744, 61440], [240, 3840, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 34952, 36744, 61440], [15, 240, 4383, 8738, 17476, 34952, 65280], [240, 3840, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 34952, 61440, 65280], [8, 240, 3840, 4383, 8738, 17476, 61440], [240, 3840, 4096, 4383, 8738, 17476, 34952], [15, 240, 3840, 4383, 26214, 34952, 61440], [240, 3840, 4383, 8738, 26214, 34952, 61440], [240, 3840, 4383, 17476, 26214, 34952, 61440], [240, 3840, 4383, 8738, 17476, 43690, 61440], [15, 240, 3840, 4383, 17476, 34952, 61986], [240, 3840, 4383, 8738, 17476, 34952, 61986], [240, 3840, 4383, 17476, 34952, 61440, 61986], [240, 3840, 4383, 8738, 17476, 52428, 61440], [15, 240, 3840, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 17476, 34952, 62532], [240, 3840, 4383, 8738, 34952, 61440, 62532], [15, 240, 3840, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 34952, 63624], [240, 3840, 4383, 8738, 17476, 61440, 63624]]),
  ([240, 3840, 4369, 4383, 8738, 17476, 34952, 61440], [[240, 3840, 4383, 8738, 17476, 34952, 61440], [240, 4080, 4383, 8738, 17476, 34952, 61440], [240, 3840, 4383, 8738, 17476, 35064, 61440], [3840, 4369, 4383, 8738, 17476, 35064, 61440], [3840, 4383, 8738, 17476, 34952, 35064, 61440], [240, 3840, 4383, 8738, 17476, 34952, 61680], [240, 256, 4383, 8738, 17476, 34952, 61440], [240, 3840, 4383, 12066, 17476, 34952, 61440], [240, 4369, 4383, 12066, 17476, 34952, 61440], [240, 4383, 8738, 12066, 17476, 34952, 61440], [240, 3840, 4383, 8738, 20292, 34952, 61440], [240, 4369, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 17476, 20292, 34952, 61440], [240, 3840, 4383, 8738, 17476, 36744, 61440], [240, 4369, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 34952, 36744, 61440], [240, 3840, 4383, 8738, 17476, 34952, 65280], [240, 4369, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 34952, 61440, 65280], [8, 240, 3840, 4383, 8738, 17476, 61440], [240, 3840, 4096, 4383, 8738, 17476, 34952], [240, 3840, 4369, 4383, 26214, 34952, 61440], [240, 3840, 4383, 8738, 26214, 34952, 61440], [240, 3840, 4383, 17476, 26214, 34952, 61440], [240, 3840, 4383, 8738, 17476, 43690, 61440], [240, 3840, 4369, 4383, 17476, 34952, 61986], [240, 3840, 4383, 8738, 17476, 34952, 61986], [240, 3840, 4383, 17476, 34952, 61440, 61986], [240, 3840, 4383, 8738, 17476, 52428, 61440], [240, 3840, 4369, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 17476, 34952, 62532], [240, 3840, 4383, 8738, 34952, 61440, 62532], [240, 3840, 4369, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 34952, 63624], [240, 3840, 4383, 8738, 17476, 61440, 63624]]),
  ([8, 15, 240, 3840, 4369, 8738, 17476, 61440], [[15, 248, 3840, 4369, 8738, 17476, 61440], [15, 240, 3848, 4369, 8738, 17476, 61440], [15, 240, 3840, 4369, 8746, 17476, 61440], [15, 240, 3840, 4369, 8738, 17484, 61440], [15, 240, 3840, 4369, 8738, 17476, 61448], [8, 240, 3840, 4383, 8738, 17476, 61440], [8, 15, 240, 4369, 12066, 17476, 61440], [8, 15, 240, 4369, 8738, 20292, 61440], [8, 15, 240, 4369, 8738, 17476, 65280], [8, 15, 240, 3840, 4369, 26214, 61440], [8, 15, 240, 3840, 4369, 17476, 61986], [8, 15, 240, 3840, 4369, 8738, 62532]]),
  ([15, 240, 4080, 4369, 8738, 17476, 34952, 61440], [[240, 4080, 4383, 8738, 17476, 34952, 61440], [15, 4080, 4369, 8738, 17476, 35064, 61440], [15, 4080, 4369, 8738, 17476, 34952, 61680], [15, 240, 4369, 8738, 17476, 36856, 61440], [15, 240, 4369, 8738, 17476, 34952, 65520], [15, 240, 4080, 4369, 26214, 34952, 61440], [15, 240, 4080, 4369, 17476, 34952, 61986], [15, 240, 4080, 4369, 8738, 34952, 62532], [15, 240, 4080, 4369, 8738, 17476, 63624]]),
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 61680], [[240, 3840, 4383, 8738, 17476, 34952, 61680], [15, 4080, 4369, 8738, 17476, 34952, 61680], [15, 3840, 4369, 8738, 17476, 35064, 61680], [15, 240, 4369, 12066, 17476, 34952, 61680], [15, 240, 4369, 8738, 20292, 34952, 61680], [15, 240, 4369, 8738, 17476, 36744, 61680], [15, 240, 4369, 8738, 17476, 34952, 65520], [15, 240, 3840, 4369, 26214, 34952, 61680], [15, 240, 3840, 4369, 8738, 17476, 63736]]),
  ([15, 240, 3840, 4369, 8738, 17476, 35064, 61440], [[15, 3840, 4369, 8738, 17476, 35064, 61440], [15, 3840, 4383, 8738, 17476, 35064, 61440], [240, 3840, 4383, 8738, 17476, 35064, 61440], [3840, 4369, 4383, 8738, 17476, 35064, 61440], [15, 4080, 4369, 8738, 17476, 35064, 61440], [15, 3840, 4369, 8738, 17476, 35064, 61680], [15, 256, 4369, 8738, 17476, 35064, 61440], [15, 240, 4369, 12066, 17476, 35064, 61440], [15, 4369, 8738, 12066, 17476, 35064, 61440], [15, 240, 4369, 8738, 20292, 35064, 61440], [15, 4369, 8738, 17476, 20292, 35064, 61440], [15, 240, 4369, 8738, 17476, 36856, 61440], [15, 4369, 8738, 17476, 35064, 36856, 61440], [15, 240, 4369, 8738, 17476, 35064, 65280], [15, 3840, 4369, 8738, 17476, 35064, 65280], [15, 4369, 8738, 17476, 35064, 61440, 65280], [15, 3840, 4096, 4369, 8738, 17476, 35064], [15, 240, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4369, 8738, 26214, 35064, 61440], [15, 3840, 4369, 17476, 26214, 35064, 61440], [15, 240, 3840, 4369, 17476, 35064, 61986], [15, 3840, 4369, 8738, 17476, 35064, 61986], [15, 240, 3840, 4369, 8738, 35064, 62532], [15, 3840, 4369, 8738, 17476, 35064, 62532], [15, 240, 3840, 4369, 8738, 17476, 63736], [15, 3840, 4369, 8738, 17476, 35064, 63736]]),
  ([15, 3840, 4369, 8738, 17476, 34952, 35064, 61440], [[15, 3840, 4369, 8738, 17476, 35064, 61440], [15, 3840, 4383, 8738, 17476, 35064, 61440], [3840, 4369, 4383, 8738, 17476, 35064, 61440], [3840, 4383, 8738, 17476, 34952, 35064, 61440], [15, 256, 4369, 8738, 17476, 35064, 61440], [15, 4369, 8738, 12066, 17476, 35064, 61440], [15, 4369, 8738, 17476, 20292, 35064, 61440], [15, 4369, 8738, 17476, 35064, 36744, 61440], [15, 4369, 8738, 17476, 35064, 36856, 61440], [15, 3840, 4369, 8738, 17476, 35064, 65280], [15, 4369, 8738, 17476, 34952, 35064, 65280], [15, 4369, 8738, 17476, 35064, 61440, 65280], [15, 3840, 4096, 4369, 8738, 17476, 35064], [15, 3840, 4369, 8738, 26214, 35064, 61440], [15, 3840, 4369, 17476, 26214, 35064, 61440], [15, 3840, 4369, 26214, 34952, 35064, 61440], [15, 3840, 4369, 8738, 17476, 35064, 61986], [15, 3840, 4369, 8738, 17476, 35064, 62532], [15, 3840, 4369, 8738, 17476, 35064, 63624], [15, 3840, 4369, 8738, 17476, 35064, 63736]]),
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 65280], [[15, 240, 4369, 8738, 17476, 34952, 65280], [15, 240, 4383, 8738, 17476, 34952, 65280], [240, 3840, 4383, 8738, 17476, 34952, 65280], [240, 4369, 4383, 8738, 17476, 34952, 65280], [8, 15, 240, 4369, 8738, 17476, 65280], [15, 240, 4369, 8738, 17476, 35064, 65280], [15, 3840, 4369, 8738, 17476, 35064, 65280], [15, 4369, 8738, 17476, 34952, 35064, 65280], [15, 240, 4369, 8738, 17476, 34952, 65520], [15, 240, 4369, 12066, 17476, 34952, 65280], [15, 240, 4369, 8738, 20292, 34952, 65280], [15, 240, 4369, 8738, 17476, 36744, 65280], [15, 240, 4352, 4369, 8738, 17476, 34952], [15, 240, 3840, 4369, 26214, 34952, 65280], [15, 240, 4369, 8738, 26214, 34952, 65280], [15, 240, 4369, 17476, 26214, 34952, 65280], [15, 240, 4369, 8738, 17476, 43690, 65280], [15, 240, 3840, 4369, 17476, 34952, 65314], [15, 240, 4369, 8738, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 65280, 65314], [15, 240, 4369, 8738, 17476, 52428, 65280], [15, 240, 3840, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 17476, 34952, 65348], [15, 240, 4369, 8738, 34952, 65280, 65348], [15, 240, 3840, 4369, 8738, 17476, 65416], [15, 240, 4369, 8738, 17476, 34952, 65416], [15, 240, 4369, 8738, 17476, 65280, 65416]]),
  ([15, 240, 4369, 8738, 17476, 34952, 61440, 65280], [[15, 240, 4369, 8738, 17476, 34952, 65280], [15, 240, 4383, 8738, 17476, 34952, 65280], [240, 4369, 4383, 8738, 17476, 34952, 65280], [240, 4383, 8738, 17476, 34952, 61440, 65280], [8, 15, 240, 4369, 8738, 17476, 65280], [15, 240, 4369, 8738, 17476, 35064, 65280], [15, 4369, 8738, 17476, 34952, 35064, 65280], [15, 4369, 8738, 17476, 35064, 61440, 65280], [15, 240, 4369, 8738, 17476, 34952, 65520], [15, 240, 4352, 4369, 8738, 17476, 34952], [15, 240, 4369, 8738, 26214, 34952, 65280], [15, 240, 4369, 17476, 26214, 34952, 65280], [15, 240, 4369, 26214, 34952, 61440, 65280], [15, 240, 4369, 8738, 17476, 43690, 65280], [15, 240, 4369, 17476, 34952, 61986, 65280], [15, 240, 4369, 8738, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 61440, 65314], [15, 240, 4369, 17476, 34952, 65280, 65314], [15, 240, 4369, 8738, 17476, 52428, 65280], [15, 240, 4369, 8738, 34952, 62532, 65280], [15, 240, 4369, 8738, 17476, 34952, 65348], [15, 240, 4369, 8738, 34952, 61440, 65348], [15, 240, 4369, 8738, 34952, 65280, 65348], [15, 240, 4369, 8738, 17476, 63624, 65280], [15, 240, 4369, 8738, 17476, 34952, 65416], [15, 240, 4369, 8738, 17476, 61440, 65416], [15, 240, 4369, 8738, 17476, 65280, 65416]]),
  ([15, 240, 256, 4369, 8738, 17476, 34952, 61440], [[240, 256, 4383, 8738, 17476, 34952, 61440], [15, 496, 4369, 8738, 17476, 34952, 61440], [15, 256, 4369, 8738, 17476, 35064, 61440], [15, 240, 4369, 8994, 17476, 34952, 61440], [15, 240, 4369, 8738, 17732, 34952, 61440], [15, 240, 4369, 8738, 17476, 35208, 61440], [15, 240, 4369, 8738, 17476, 34952, 61696], [15, 240, 256, 4369, 26214, 34952, 61440], [15, 240, 256, 4369, 17476, 34952, 61986], [15, 240, 256, 4369, 8738, 34952, 62532], [15, 240, 256, 4369, 8738, 17476, 63624]]),
  ([15, 240, 3840, 4369, 12066, 17476, 34952, 61440], [[15, 240, 4369, 12066, 17476, 34952, 61440], [15, 240, 4383, 12066, 17476, 34952, 61440], [240, 3840, 4383, 12066, 17476, 34952, 61440], [240, 4369, 4383, 12066, 17476, 34952, 61440], [8, 15, 240, 4369, 12066, 17476, 61440], [15, 240, 4369, 12066, 17476, 35064, 61440], [15, 240, 4369, 12066, 17476, 34952, 61680], [15, 240, 4369, 12066, 20292, 34952, 61440], [15, 240, 4369, 12066, 17476, 36744, 61440], [15, 240, 4369, 12066, 17476, 34952, 65280], [15, 240, 4096, 4369, 12066, 17476, 34952], [15, 240, 3840, 4369, 28518, 34952, 61440], [15, 240, 4369, 12066, 28518, 34952, 61440], [15, 240, 4369, 17476, 28518, 34952, 61440], [15, 240, 4369, 12066, 17476, 44970, 61440], [15, 240, 3840, 4369, 17476, 34952, 65314], [15, 240, 4369, 12066, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 61440, 65314], [15, 240, 4369, 12066, 17476, 52428, 61440], [15, 240, 3840, 4369, 12066, 34952, 62532], [15, 240, 4369, 12066, 17476, 34952, 62532], [15, 240, 4369, 12066, 34952, 61440, 62532], [15, 240, 3840, 4369, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 34952, 63624], [15, 240, 4369, 12066, 17476, 61440, 63624]]),
  ([15, 240, 4369, 8738, 12066, 17476, 34952, 61440], [[15, 240, 4369, 12066, 17476, 34952, 61440], [15, 240, 4383, 12066, 17476, 34952, 61440], [240, 4369, 4383, 12066, 17476, 34952, 61440], [240, 4383, 8738, 12066, 17476, 34952, 61440], [8, 15, 240, 4369, 12066, 17476, 61440], [15, 240, 4369, 12066, 17476, 35064, 61440], [15, 4369, 8738, 12066, 17476, 35064, 61440], [15, 240, 4369, 12066, 17476, 34952, 61680], [15, 240, 4096, 4369, 12066, 17476, 34952], [15, 240, 4369, 12066, 26214, 34952, 61440], [15, 240, 4369, 12066, 17476, 43690, 61440], [15, 240, 4369, 12066, 17476, 34952, 61986], [15, 240, 4369, 8738, 28518, 34952, 61440], [15, 240, 4369, 12066, 28518, 34952, 61440], [15, 240, 4369, 17476, 28518, 34952, 61440], [15, 240, 4369, 8738, 17476, 44970, 61440], [15, 240, 4369, 12066, 17476, 44970, 61440], [15, 240, 4369, 8738, 17476, 34952, 65314], [15, 240, 4369, 12066, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 61440, 65314], [15, 240, 4369, 12066, 17476, 52428, 61440], [15, 240, 4369, 8738, 12066, 34952, 62532], [15, 240, 4369, 12066, 17476, 34952, 62532], [15, 240, 4369, 12066, 34952, 61440, 62532], [15, 240, 4369, 8738, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 34952, 63624], [15, 240, 4369, 12066, 17476, 61440, 63624]]),
  ([15, 240, 3840, 4369, 8738, 20292, 34952, 61440], [[15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 4383, 8738, 20292, 34952, 61440], [240, 3840, 4383, 8738, 20292, 34952, 61440], [240, 4369, 4383, 8738, 20292, 34952, 61440], [8, 15, 240, 4369, 8738, 20292, 61440], [15, 240, 4369, 8738, 20292, 35064, 61440], [15, 240, 4369, 8738, 20292, 34952, 61680], [15, 240, 4369, 12066, 20292, 34952, 61440], [15, 240, 4369, 8738, 20292, 36744, 61440], [15, 240, 4369, 8738, 20292, 34952, 65280], [15, 240, 4096, 4369, 8738, 20292, 34952], [15, 240, 3840, 4369, 28518, 34952, 61440], [15, 240, 4369, 8738, 28518, 34952, 61440], [15, 240, 4369, 20292, 28518, 34952, 61440], [15, 240, 4369, 8738, 20292, 43690, 61440], [15, 240, 3840, 4369, 20292, 34952, 61986], [15, 240, 4369, 8738, 20292, 34952, 61986], [15, 240, 4369, 20292, 34952, 61440, 61986], [15, 240, 4369, 8738, 20292, 53196, 61440], [15, 240, 3840, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 20292, 34952, 65348], [15, 240, 4369, 8738, 34952, 61440, 65348], [15, 240, 3840, 4369, 8738, 20292, 63624], [15, 240, 4369, 8738, 20292, 34952, 63624], [15, 240, 4369, 8738, 20292, 61440, 63624]]),
  ([15, 240, 4369, 8738, 17476, 20292, 34952, 61440], [[15, 240, 4369, 8738, 20292, 34952, 61440], [15, 240, 4383, 8738, 20292, 34952, 61440], [240, 4369, 4383, 8738, 20292, 34952, 61440], [240, 4383, 8738, 17476, 20292, 34952, 61440], [8, 15, 240, 4369, 8738, 20292, 61440], [15, 240, 4369, 8738, 20292, 35064, 61440], [15, 4369, 8738, 17476, 20292, 35064, 61440], [15, 240, 4369, 8738, 20292, 34952, 61680], [15, 240, 4096, 4369, 8738, 20292, 34952], [15, 240, 4369, 20292, 26214, 34952, 61440], [15, 240, 4369, 8738, 28518, 34952, 61440], [15, 240, 4369, 17476, 28518, 34952, 61440], [15, 240, 4369, 20292, 28518, 34952, 61440], [15, 240, 4369, 8738, 20292, 43690, 61440], [15, 240, 4369, 8738, 20292, 34952, 61986], [15, 240, 4369, 17476, 20292, 34952, 61986], [15, 240, 4369, 20292, 34952, 61440, 61986], [15, 240, 4369, 8738, 20292, 52428, 61440], [15, 240, 4369, 8738, 20292, 34952, 62532], [15, 240, 4369, 8738, 17476, 53196, 61440], [15, 240, 4369, 8738, 20292, 53196, 61440], [15, 240, 4369, 8738, 17476, 34952, 65348], [15, 240, 4369, 8738, 20292, 34952, 65348], [15, 240, 4369, 8738, 34952, 61440, 65348], [15, 240, 4369, 8738, 17476, 20292, 63624], [15, 240, 4369, 8738, 20292, 34952, 63624], [15, 240, 4369, 8738, 20292, 61440, 63624]]),
  ([15, 240, 3840, 4369, 8738, 17476, 36744, 61440], [[15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 4383, 8738, 17476, 36744, 61440], [240, 3840, 4383, 8738, 17476, 36744, 61440], [240, 4369, 4383, 8738, 17476, 36744, 61440], [15, 240, 4369, 8738, 17476, 36856, 61440], [15, 240, 4369, 8738, 17476, 36744, 61680], [15, 240, 4369, 12066, 17476, 36744, 61440], [15, 240, 4369, 8738, 20292, 36744, 61440], [15, 240, 4369, 8738, 17476, 36744, 65280], [15, 240, 4096, 4369, 8738, 17476, 36744], [15, 240, 3840, 4369, 26214, 36744, 61440], [15, 240, 4369, 8738, 26214, 36744, 61440], [15, 240, 4369, 17476, 26214, 36744, 61440], [15, 240, 4369, 8738, 17476, 44970, 61440], [15, 240, 3840, 4369, 17476, 36744, 61986], [15, 240, 4369, 8738, 17476, 36744, 61986], [15, 240, 4369, 17476, 36744, 61440, 61986], [15, 240, 4369, 8738, 17476, 53196, 61440], [15, 240, 3840, 4369, 8738, 36744, 62532], [15, 240, 4369, 8738, 17476, 36744, 62532], [15, 240, 4369, 8738, 36744, 61440, 62532], [15, 240, 3840, 4369, 8738, 17476, 65416], [15, 240, 4369, 8738, 17476, 36744, 65416], [15, 240, 4369, 8738, 17476, 61440, 65416]]),
  ([15, 240, 4369, 8738, 17476, 34952, 36744, 61440], [[15, 240, 4369, 8738, 17476, 36744, 61440], [15, 240, 4383, 8738, 17476, 36744, 61440], [240, 4369, 4383, 8738, 17476, 36744, 61440], [240, 4383, 8738, 17476, 34952, 36744, 61440], [15, 4369, 8738, 17476, 35064, 36744, 61440], [15, 240, 4369, 8738, 17476, 36856, 61440], [15, 240, 4369, 8738, 17476, 36744, 61680], [15, 240, 4096, 4369, 8738, 17476, 36744], [15, 240, 4369, 8738, 26214, 36744, 61440], [15, 240, 4369, 17476, 26214, 36744, 61440], [15, 240, 4369, 26214, 34952, 36744, 61440], [15, 240, 4369, 8738, 17476, 44970, 61440], [15, 240, 4369, 8738, 17476, 36744, 61986], [15, 240, 4369, 17476, 34952, 36744, 61986], [15, 240, 4369, 17476, 36744, 61440, 61986], [15, 240, 4369, 8738, 17476, 53196, 61440], [15, 240, 4369, 8738, 17476, 36744, 62532], [15, 240, 4369, 8738, 34952, 36744, 62532], [15, 240, 4369, 8738, 36744, 61440, 62532], [15, 240, 4369, 8738, 17476, 36744, 63624], [15, 240, 4369, 8738, 17476, 34952, 65416], [15, 240, 4369, 8738, 17476, 36744, 65416], [15, 240, 4369, 8738, 17476, 61440, 65416]]),
  ([15, 240, 3840, 4096, 4369, 8738, 17476, 34952], [[240, 3840, 4096, 4383, 8738, 17476, 34952], [15, 3840, 4336, 4369, 8738, 17476, 34952], [15, 3840, 4096, 4369, 8738, 17476, 35064], [15, 240, 4369, 7936, 8738, 17476, 34952], [15, 240, 4096, 4369, 12066, 17476, 34952], [15, 240, 4096, 4369, 8738, 20292, 34952], [15, 240, 4096, 4369, 8738, 17476, 36744], [15, 240, 3840, 4369, 12834, 17476, 34952], [15, 240, 3840, 4369, 8738, 21572, 34952], [15, 240, 3840, 4369, 8738, 17476, 39048], [15, 240, 3840, 4096, 4369, 26214, 34952]]),
  ([15, 240, 3840, 4369, 17476, 34952, 61440, 61986], [[15, 240, 3840, 4369, 17476, 34952, 61986], [15, 240, 3840, 4383, 17476, 34952, 61986], [240, 3840, 4369, 4383, 17476, 34952, 61986], [240, 3840, 4383, 17476, 34952, 61440, 61986], [8, 15, 240, 3840, 4369, 17476, 61986], [15, 240, 4080, 4369, 17476, 34952, 61986], [15, 240, 3840, 4369, 17476, 35064, 61986], [15, 240, 256, 4369, 17476, 34952, 61986], [15, 240, 3840, 4369, 20292, 34952, 61986], [15, 240, 4369, 17476, 20292, 34952, 61986], [15, 240, 4369, 20292, 34952, 61440, 61986], [15, 240, 3840, 4369, 17476, 36744, 61986], [15, 240, 4369, 17476, 34952, 36744, 61986], [15, 240, 4369, 17476, 36744, 61440, 61986], [15, 240, 4369, 17476, 34952, 61986, 65280], [15, 240, 3840, 4369, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 61440, 65314], [15, 240, 4369, 17476, 34952, 61986, 65314], [15, 240, 3840, 4369, 17476, 52428, 61986], [15, 240, 3840, 4369, 34952, 61986, 62532], [15, 240, 3840, 4369, 17476, 34952, 63078], [15, 240, 3840, 4369, 34952, 61440, 63078], [15, 240, 3840, 4369, 34952, 61986, 63078], [15, 240, 3840, 4369, 17476, 61986, 63624], [15, 240, 3840, 4369, 17476, 61986, 64170]]),
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 61986], [[15, 240, 3840, 4369, 17476, 34952, 61986], [15, 240, 3840, 4383, 17476, 34952, 61986], [240, 3840, 4369, 4383, 17476, 34952, 61986], [240, 3840, 4383, 8738, 17476, 34952, 61986], [8, 15, 240, 3840, 4369, 17476, 61986], [15, 240, 4080, 4369, 17476, 34952, 61986], [15, 240, 3840, 4369, 17476, 35064, 61986], [15, 3840, 4369, 8738, 17476, 35064, 61986], [15, 240, 256, 4369, 17476, 34952, 61986], [15, 240, 4369, 12066, 17476, 34952, 61986], [15, 240, 3840, 4369, 20292, 34952, 61986], [15, 240, 4369, 8738, 20292, 34952, 61986], [15, 240, 4369, 17476, 20292, 34952, 61986], [15, 240, 3840, 4369, 17476, 36744, 61986], [15, 240, 4369, 8738, 17476, 36744, 61986], [15, 240, 4369, 17476, 34952, 36744, 61986], [15, 240, 3840, 4369, 17476, 34952, 65314], [15, 240, 4369, 8738, 17476, 34952, 65314], [15, 240, 4369, 17476, 34952, 61986, 65314], [15, 240, 3840, 4369, 26214, 34952, 61986], [15, 240, 3840, 4369, 17476, 43690, 61986], [15, 240, 3840, 4369, 17476, 52428, 61986], [15, 240, 3840, 4369, 8738, 34952, 63078], [15, 240, 3840, 4369, 17476, 34952, 63078], [15, 240, 3840, 4369, 34952, 61986, 63078], [15, 240, 3840, 4369, 8738, 17476, 64170], [15, 240, 3840, 4369, 17476, 61986, 64170]]),
  ([15, 240, 3840, 4369, 8738, 34952, 61440, 62532], [[15, 240, 3840, 4369, 8738, 34952, 62532], [15, 240, 3840, 4383, 8738, 34952, 62532], [240, 3840, 4369, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 34952, 61440, 62532], [8, 15, 240, 3840, 4369, 8738, 62532], [15, 240, 4080, 4369, 8738, 34952, 62532], [15, 240, 3840, 4369, 8738, 35064, 62532], [15, 240, 256, 4369, 8738, 34952, 62532], [15, 240, 3840, 4369, 12066, 34952, 62532], [15, 240, 4369, 8738, 12066, 34952, 62532], [15, 240, 4369, 12066, 34952, 61440, 62532], [15, 240, 3840, 4369, 8738, 36744, 62532], [15, 240, 4369, 8738, 34952, 36744, 62532], [15, 240, 4369, 8738, 36744, 61440, 62532], [15, 240, 4369, 8738, 34952, 62532, 65280], [15, 240, 3840, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 34952, 61440, 65348], [15, 240, 4369, 8738, 34952, 62532, 65348], [15, 240, 3840, 4369, 8738, 43690, 62532], [15, 240, 3840, 4369, 34952, 61986, 62532], [15, 240, 3840, 4369, 8738, 34952, 63078], [15, 240, 3840, 4369, 34952, 61440, 63078], [15, 240, 3840, 4369, 34952, 62532, 63078], [15, 240, 3840, 4369, 8738, 62532, 63624], [15, 240, 3840, 4369, 8738, 62532, 64716]]),
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 62532], [[15, 240, 3840, 4369, 8738, 34952, 62532], [15, 240, 3840, 4383, 8738, 34952, 62532], [240, 3840, 4369, 4383, 8738, 34952, 62532], [240, 3840, 4383, 8738, 17476, 34952, 62532], [8, 15, 240, 3840, 4369, 8738, 62532], [15, 240, 4080, 4369, 8738, 34952, 62532], [15, 240, 3840, 4369, 8738, 35064, 62532], [15, 3840, 4369, 8738, 17476, 35064, 62532], [15, 240, 256, 4369, 8738, 34952, 62532], [15, 240, 3840, 4369, 12066, 34952, 62532], [15, 240, 4369, 8738, 12066, 34952, 62532], [15, 240, 4369, 12066, 17476, 34952, 62532], [15, 240, 4369, 8738, 20292, 34952, 62532], [15, 240, 3840, 4369, 8738, 36744, 62532], [15, 240, 4369, 8738, 17476, 36744, 62532], [15, 240, 4369, 8738, 34952, 36744, 62532], [15, 240, 3840, 4369, 8738, 34952, 65348], [15, 240, 4369, 8738, 17476, 34952, 65348], [15, 240, 4369, 8738, 34952, 62532, 65348], [15, 240, 3840, 4369, 26214, 34952, 62532], [15, 240, 3840, 4369, 8738, 43690, 62532], [15, 240, 3840, 4369, 8738, 34952, 63078], [15, 240, 3840, 4369, 17476, 34952, 63078], [15, 240, 3840, 4369, 34952, 62532, 63078], [15, 240, 3840, 4369, 8738, 52428, 62532], [15, 240, 3840, 4369, 8738, 17476, 64716], [15, 240, 3840, 4369, 8738, 62532, 64716]]),
  ([15, 240, 3840, 4369, 8738, 17476, 61440, 63624], [[15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624], [240, 3840, 4369, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 61440, 63624], [15, 240, 4080, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 8738, 17476, 63736], [15, 240, 256, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 12066, 17476, 63624], [15, 240, 4369, 8738, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 61440, 63624], [15, 240, 3840, 4369, 8738, 20292, 63624], [15, 240, 4369, 8738, 17476, 20292, 63624], [15, 240, 4369, 8738, 20292, 61440, 63624], [15, 240, 4369, 8738, 17476, 63624, 65280], [15, 240, 3840, 4369, 8738, 17476, 65416], [15, 240, 4369, 8738, 17476, 61440, 65416], [15, 240, 4369, 8738, 17476, 63624, 65416], [15, 240, 3840, 4369, 8738, 26214, 63624], [15, 240, 3840, 4369, 17476, 26214, 63624], [15, 240, 3840, 4369, 26214, 61440, 63624], [15, 240, 3840, 4369, 17476, 61986, 63624], [15, 240, 3840, 4369, 8738, 17476, 64170], [15, 240, 3840, 4369, 8738, 62532, 63624], [15, 240, 3840, 4369, 8738, 17476, 64716]]),
  ([15, 240, 3840, 4369, 8738, 17476, 34952, 63624], [[15, 240, 3840, 4369, 8738, 17476, 63624], [15, 240, 3840, 4383, 8738, 17476, 63624], [240, 3840, 4369, 4383, 8738, 17476, 63624], [240, 3840, 4383, 8738, 17476, 34952, 63624], [15, 240, 4080, 4369, 8738, 17476, 63624], [15, 3840, 4369, 8738, 17476, 35064, 63624], [15, 240, 3840, 4369, 8738, 17476, 63736], [15, 240, 256, 4369, 8738, 17476, 63624], [15, 240, 3840, 4369, 12066, 17476, 63624], [15, 240, 4369, 8738, 12066, 17476, 63624], [15, 240, 4369, 12066, 17476, 34952, 63624], [15, 240, 3840, 4369, 8738, 20292, 63624], [15, 240, 4369, 8738, 17476, 20292, 63624], [15, 240, 4369, 8738, 20292, 34952, 63624], [15, 240, 4369, 8738, 17476, 36744, 63624], [15, 240, 3840, 4369, 8738, 17476, 65416], [15, 240, 4369, 8738, 17476, 34952, 65416], [15, 240, 4369, 8738, 17476, 63624, 65416], [15, 240, 3840, 4369, 8738, 26214, 63624], [15, 240, 3840, 4369, 17476, 26214, 63624], [15, 240, 3840, 4369, 26214, 34952, 63624], [15, 240, 3840, 4369, 8738, 17476, 64170], [15, 240, 3840, 4369, 8738, 17476, 64716]]),
  ([15, 240, 3840, 4369, 8738, 26214, 34952, 61440], [[15, 240, 3840, 4369, 26214, 34952, 61440], [15, 240, 3840, 4383, 26214, 34952, 61440], [240, 3840, 4369, 4383, 26214, 34952, 61440], [240, 3840, 4383, 8738, 26214, 34952, 61440], [8, 15, 240, 3840, 4369, 26214, 61440], [15, 240, 4080, 4369, 26214, 34952, 61440], [15, 240, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4369, 8738, 26214, 35064, 61440], [15, 3840, 4369, 26214, 34952, 35064, 61440], [15, 240, 3840, 4369, 26214, 34952, 61680], [15, 240, 256, 4369, 26214, 34952, 61440], [15, 240, 4369, 12066, 26214, 34952, 61440], [15, 240, 3840, 4369, 28518, 34952, 61440], [15, 240, 4369, 8738, 28518, 34952, 61440], [15, 240, 4369, 26214, 28518, 34952, 61440], [15, 240, 3840, 4369, 26214, 36744, 61440], [15, 240, 4369, 8738, 26214, 36744, 61440], [15, 240, 4369, 26214, 34952, 36744, 61440], [15, 240, 3840, 4369, 26214, 34952, 65280], [15, 240, 4369, 8738, 26214, 34952, 65280], [15, 240, 4369, 26214, 34952, 61440, 65280], [15, 240, 3840, 4096, 4369, 26214, 34952], [15, 240, 3840, 4369, 26214, 43690, 61440], [15, 240, 3840, 4369, 26214, 34952, 61986], [15, 240, 3840, 4369, 26214, 61166, 61440], [15, 240, 3840, 4369, 8738, 34952, 63078], [15, 240, 3840, 4369, 26214, 34952, 63078], [15, 240, 3840, 4369, 34952, 61440, 63078], [15, 240, 3840, 4369, 8738, 26214, 63624], [15, 240, 3840, 4369, 26214, 34952, 63624], [15, 240, 3840, 4369, 26214, 61440, 63624]]),
  ([15, 240, 3840, 4369, 17476, 26214, 34952, 61440], [[15, 240, 3840, 4369, 26214, 34952, 61440], [15, 240, 3840, 4383, 26214, 34952, 61440], [240, 3840, 4369, 4383, 26214, 34952, 61440], [240, 3840, 4383, 17476, 26214, 34952, 61440], [8, 15, 240, 3840, 4369, 26214, 61440], [15, 240, 4080, 4369, 26214, 34952, 61440], [15, 240, 3840, 4369, 26214, 35064, 61440], [15, 3840, 4369, 17476, 26214, 35064, 61440], [15, 3840, 4369, 26214, 34952, 35064, 61440], [15, 240, 3840, 4369, 26214, 34952, 61680], [15, 240, 256, 4369, 26214, 34952, 61440], [15, 240, 4369, 20292, 26214, 34952, 61440], [15, 240, 3840, 4369, 28518, 34952, 61440], [15, 240, 4369, 17476, 28518, 34952, 61440], [15, 240, 4369, 26214, 28518, 34952, 61440], [15, 240, 3840, 4369, 26214, 36744, 61440], [15, 240, 4369, 17476, 26214, 36744, 61440], [15, 240, 4369, 26214, 34952, 36744, 61440], [15, 240, 3840, 4369, 26214, 34952, 65280], [15, 240, 4369, 17476, 26214, 34952, 65280], [15, 240, 4369, 26214, 34952, 61440, 65280], [15, 240, 3840, 4096, 4369, 26214, 34952], [15, 240, 3840, 4369, 26214, 52428, 61440], [15, 240, 3840, 4369, 26214, 34952, 62532], [15, 240, 3840, 4369, 26214, 61166, 61440], [15, 240, 3840, 4369, 17476, 34952, 63078], [15, 240, 3840, 4369, 26214, 34952, 63078], [15, 240, 3840, 4369, 34952, 61440, 63078], [15, 240, 3840, 4369, 17476, 26214, 63624], [15, 240, 3840, 4369, 26214, 34952, 63624], [15, 240, 3840, 4369, 26214, 61440, 63624]]),
  ([15, 240, 3840, 4369, 8738, 17476, 43690, 61440], [[240, 3840, 4383, 8738, 17476, 43690, 61440], [15, 240, 4369, 12066, 17476, 43690, 61440], [15, 240, 4369, 8738, 20292, 43690, 61440], [15, 240, 4369, 8738, 17476, 44970, 61440], [15, 240, 4369, 8738, 17476, 43690, 65280], [15, 240, 3840, 4369, 26214, 43690, 61440], [15, 240, 3840, 4369, 17476, 43690, 61986], [15, 240, 3840, 4369, 8738, 43690, 62532], [15, 240, 3840, 4369, 8738, 17476, 64170]]),
  ([15, 240, 3840, 4369, 8738, 17476, 52428, 61440], [[240, 3840, 4383, 8738, 17476, 52428, 61440], [15, 240, 4369, 12066, 17476, 52428, 61440], [15, 240, 4369, 8738, 20292, 52428, 61440], [15, 240, 4369, 8738, 17476, 53196, 61440], [15, 240, 4369, 8738, 17476, 52428, 65280], [15, 240, 3840, 4369, 26214, 52428, 61440], [15, 240, 3840, 4369, 17476, 52428, 61986], [15, 240, 3840, 4369, 8738, 52428, 62532], [15, 240, 3840, 4369, 8738, 17476, 64716]])]

theorem pairs7_fst : pairs7.map Prod.fst = row7 := rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk7 : pairs7.all (fun p => verifyFast 4478 negs 6 p.1 p.2 row6) = true := by
  decide +kernel

def pairs8 : List (List ℕ × List (List ℕ)) := [
  ([15, 240, 3840, 61440, 4369, 8738, 17476, 34952], [[15, 240, 3840, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4383, 8738, 17476, 34952, 61440], [240, 3840, 4369, 4383, 8738, 17476, 34952, 61440], [8, 15, 240, 3840, 4369, 8738, 17476, 61440], [15, 240, 4080, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 61680], [15, 240, 3840, 4369, 8738, 17476, 35064, 61440], [15, 3840, 4369, 8738, 17476, 34952, 35064, 61440], [15, 240, 3840, 4369, 8738, 17476, 34952, 65280], [15, 240, 4369, 8738, 17476, 34952, 61440, 65280], [15, 240, 256, 4369, 8738, 17476, 34952, 61440], [15, 240, 3840, 4369, 12066, 17476, 34952, 61440], [15, 240, 4369, 8738, 12066, 17476, 34952, 61440], [15, 240, 3840, 4369, 8738, 20292, 34952, 61440], [15, 240, 4369, 8738, 17476, 20292, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 36744, 61440], [15, 240, 4369, 8738, 17476, 34952, 36744, 61440], [15, 240, 3840, 4096, 4369, 8738, 17476, 34952], [15, 240, 3840, 4369, 17476, 34952, 61440, 61986], [15, 240, 3840, 4369, 8738, 17476, 34952, 61986], [15, 240, 3840, 4369, 8738, 34952, 61440, 62532], [15, 240, 3840, 4369, 8738, 17476, 34952, 62532], [15, 240, 3840, 4369, 8738, 17476, 61440, 63624], [15, 240, 3840, 4369, 8738, 17476, 34952, 63624], [15, 240, 3840, 4369, 8738, 26214, 34952, 61440], [15, 240, 3840, 4369, 17476, 26214, 34952, 61440], [15, 240, 3840, 4369, 8738, 17476, 43690, 61440], [15, 240, 3840, 4369, 8738, 17476, 52428, 61440]])]

theorem pairs8_fst : pairs8.map Prod.fst = row8 := rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem chk8 : pairs8.all (fun p => verifyFast 4478 negs 7 p.1 p.2 row7) = true := by
  decide +kernel

theorem excluded (hc : Can 4478 8 inputs.toFinset) : False := by
  obtain ⟨S7, h7, c7⟩ := advanceRow hnegs pairs8_fst chk8 inputs (by simp [row8, inputs]) hc
  obtain ⟨S6, h6, c6⟩ := advanceRow hnegs pairs7_fst chk7 S7 h7 c7
  obtain ⟨S5, h5, c5⟩ := advanceRow hnegs pairs6_fst chk6 S6 h6 c6
  obtain ⟨S4, h4, c4⟩ := advanceRow hnegs pairs5_fst chk5 S5 h5 c5
  obtain ⟨S3, h3, c3⟩ := advanceRow hnegs pairs4_fst chk4 S4 h4 c4
  obtain ⟨S2, h2, c2⟩ := advanceRow hnegs pairs3_fst chk3 S3 h3 c3
  obtain ⟨S1, h1, c1⟩ := advanceRow hnegs pairs2_fst chk2 S2 h2 c2
  simp [row1] at h1

theorem inputMap : ∀ p : Fin 16,
    oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4) = inputs.map (fun t => t.testBit p.val) := by
  decide +kernel

theorem hp16 : ∀ p : Fin 16, (65535 : ℕ).testBit p.val = true := by
  decide +kernel

theorem inputs_lt : ∀ x ∈ inputs, x < 65536 := by
  decide +kernel

theorem eq16 (a b : ℕ) (ha : a < 65536) (hb : b < 65536)
    (h : ∀ p : Fin 16, a.testBit p.val = b.testBit p.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · exact h ⟨i, hi⟩
  · have hp : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have h16 : (65536 : ℕ) = 2 ^ 16 := rfl
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (4478 : ℕ).testBit (4 * u.val + v.val)

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 8) (hr : Represents A C) : False := by
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let out := (tabs inputs C.gates).getD C.output 0
  have hout_lt : out < 65536 := getD_lt _ (tabs_lt C.gates inputs inputs_lt) C.output
  have hout_eq : out = 4478 := by
    apply eq16 out 4478 hout_lt (by decide)
    intro p
    have hrep := hr (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)
    unfold Circuit.eval Circuit.wires A at hrep
    rw [inputMap p, wires_tabs p.val (hp16 p) C.gates inputs hok, getD_map_testBit] at hrep
    have hmod : 4 * (p.val / 4) + p.val % 4 = p.val := Nat.div_add_mod p.val 4
    rw [hmod] at hrep
    exact hrep
  have hc0 : Can out C.gates.length inputs.toFinset :=
    fromTabs out C.gates inputs hok (getWire _ C.output)
  rw [hout_eq] at hc0
  have pad {k j : ℕ} (hj : k ≤ j) (ha : Can 4478 k inputs.toFinset) : Can 4478 j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUp ih
  change C.gates.length ≤ 8 at hs
  exact excluded (pad hs hc0)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [1, 7] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [11, 10] }, { op := GateOp.and, inputs := [12, 8] }, { op := GateOp.or, inputs := [13, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.and, inputs := [14, 15] }],
    output := 16 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_5983

theorem PEqualNP.Outside.L_meta_5983 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4478 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4478 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨PEqualNP.Outside.L_meta_5983.upperC, PEqualNP.Outside.L_meta_5983.upper_mono, by decide, PEqualNP.Outside.L_meta_5983.upper_rep⟩, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_5983.no_small C hm hs hr
