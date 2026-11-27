import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6674

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def embPt (x1 d : ℕ) (p : Fin x1) : Fin (x1 + d) :=
  ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right x1 d)⟩

theorem embPt_inj (x1 d : ℕ) : Function.Injective (embPt x1 d) := by
  intro a b h
  exact Fin.ext (by simpa [embPt] using congrArg (fun z : Fin (x1 + d) => z.val) h)

def extFamily (x1 x2 x3 : ℕ) (S : Fin x2 → Finset (Fin x1)) (hx32 : x3 ≤ x2)
    (l : Fin (x1 + (x2 - x3))) : Finset (Fin (x1 + (x2 - x3))) :=
  if h1 : l.val < x3 then
    (S ⟨l.val, Nat.lt_of_lt_of_le h1 hx32⟩).image (embPt x1 (x2 - x3))
  else if h2 : l.val < x1 then
    {l}
  else
    insert l ((S ⟨x3 + (l.val - x1), by have := l.isLt; omega⟩).image (embPt x1 (x2 - x3)))

theorem extFamily_lt3 {x1 x2 x3 : ℕ} (S : Fin x2 → Finset (Fin x1)) (hx32 : x3 ≤ x2)
    (l : Fin (x1 + (x2 - x3))) (hl : l.val < x3) :
    extFamily x1 x2 x3 S hx32 l =
      (S ⟨l.val, Nat.lt_of_lt_of_le hl hx32⟩).image (embPt x1 (x2 - x3)) := by
  simp [extFamily, hl]

theorem extFamily_mid {x1 x2 x3 : ℕ} (S : Fin x2 → Finset (Fin x1)) (hx32 : x3 ≤ x2)
    (l : Fin (x1 + (x2 - x3))) (hl1 : ¬ l.val < x3) (hl2 : l.val < x1) :
    extFamily x1 x2 x3 S hx32 l = {l} := by
  simp [extFamily, hl1, hl2]

theorem extFamily_ge1 {x1 x2 x3 : ℕ} (S : Fin x2 → Finset (Fin x1)) (hx32 : x3 ≤ x2)
    (l : Fin (x1 + (x2 - x3))) (hl1 : ¬ l.val < x3) (hl2 : ¬ l.val < x1) :
    extFamily x1 x2 x3 S hx32 l =
      insert l ((S ⟨x3 + (l.val - x1), by have := l.isLt; omega⟩).image (embPt x1 (x2 - x3))) := by
  simp [extFamily, hl1, hl2]

theorem extFamily_diag (x1 x2 x3 : ℕ) (S : Fin x2 → Finset (Fin x1))
    (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2)
    (hdiag : ∀ i : Fin x3, Fin.castLE hx31 i ∈ S (Fin.castLE hx32 i))
    (l : Fin (x1 + (x2 - x3))) :
    l ∈ extFamily x1 x2 x3 S hx32 l := by
  by_cases h1 : l.val < x3
  · rw [extFamily_lt3 S hx32 l h1]
    refine Finset.mem_image.mpr ⟨Fin.castLE hx31 ⟨l.val, h1⟩, hdiag ⟨l.val, h1⟩, ?_⟩
    exact Fin.ext rfl
  · by_cases h2 : l.val < x1
    · rw [extFamily_mid S hx32 l h1 h2]
      exact Finset.mem_singleton_self l
    · rw [extFamily_ge1 S hx32 l h1 h2]
      exact Finset.mem_insert_self l _

theorem extFamily_inter (x1 x2 x3 : ℕ) (S : Fin x2 → Finset (Fin x1))
    (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2)
    (hinter : ∀ a b : Fin x2, a ≠ b → (S a ∩ S b).card ≤ 1)
    (a b : Fin (x1 + (x2 - x3))) (hab : a ≠ b) :
    (extFamily x1 x2 x3 S hx32 a ∩ extFamily x1 x2 x3 S hx32 b).card ≤ 1 := by
  have haLt := a.isLt
  have hbLt := b.isLt
  by_cases haMid : ¬ a.val < x3 ∧ a.val < x1
  · rw [extFamily_mid S hx32 a haMid.1 haMid.2]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  · by_cases hbMid : ¬ b.val < x3 ∧ b.val < x1
    · rw [extFamily_mid S hx32 b hbMid.1 hbMid.2]
      exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    · have haOut : a.val < x3 ∨ (¬ a.val < x3 ∧ ¬ a.val < x1) := by omega
      have hbOut : b.val < x3 ∨ (¬ b.val < x3 ∧ ¬ b.val < x1) := by omega
      let ia : Fin x2 := if ha : a.val < x3 then ⟨a.val, Nat.lt_of_lt_of_le ha hx32⟩
        else ⟨x3 + (a.val - x1), by omega⟩
      let ib : Fin x2 := if hb : b.val < x3 then ⟨b.val, Nat.lt_of_lt_of_le hb hx32⟩
        else ⟨x3 + (b.val - x1), by omega⟩
      have hiab : ia ≠ ib := by
        intro h
        have hv : ia.val = ib.val := congrArg (fun z : Fin x2 => z.val) h
        have habv : a.val ≠ b.val := fun e => hab (Fin.ext e)
        by_cases ha1 : a.val < x3 <;> by_cases hb1 : b.val < x3
        · simp only [ia, ib, ha1, hb1, ↓reduceDIte] at hv
          exact habv hv
        · have hbge : x1 ≤ b.val := by omega
          simp only [ia, ib, ha1, hb1, ↓reduceDIte] at hv
          omega
        · have hage : x1 ≤ a.val := by omega
          simp only [ia, ib, ha1, hb1, ↓reduceDIte] at hv
          omega
        · have hage : x1 ≤ a.val := by omega
          have hbge : x1 ≤ b.val := by omega
          simp only [ia, ib, ha1, hb1, ↓reduceDIte] at hv
          omega
      have hsub : extFamily x1 x2 x3 S hx32 a ∩ extFamily x1 x2 x3 S hx32 b ⊆
          (S ia ∩ S ib).image (embPt x1 (x2 - x3)) := by
        intro p hp
        have hpLt := p.isLt
        obtain ⟨hpa, hpb⟩ := Finset.mem_inter.mp hp
        have hp_lt : p.val < x1 := by
          by_contra hge
          have hpa_eq : p = a := by
            rcases haOut with ha1 | ⟨ha1, ha2⟩
            · rw [extFamily_lt3 S hx32 a ha1] at hpa
              obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hpa
              have hqv : q.val = p.val :=
                congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
              exact absurd (hqv ▸ q.isLt) hge
            · rw [extFamily_ge1 S hx32 a ha1 ha2] at hpa
              rcases Finset.mem_insert.mp hpa with rfl | hpa'
              · rfl
              · obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hpa'
                have hqv : q.val = p.val :=
                  congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
                exact absurd (hqv ▸ q.isLt) hge
          have hpb_eq : p = b := by
            rcases hbOut with hb1 | ⟨hb1, hb2⟩
            · rw [extFamily_lt3 S hx32 b hb1] at hpb
              obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hpb
              have hqv : q.val = p.val :=
                congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
              exact absurd (hqv ▸ q.isLt) hge
            · rw [extFamily_ge1 S hx32 b hb1 hb2] at hpb
              rcases Finset.mem_insert.mp hpb with rfl | hpb'
              · rfl
              · obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hpb'
                have hqv : q.val = p.val :=
                  congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
                exact absurd (hqv ▸ q.isLt) hge
          exact hab (hpa_eq.symm.trans hpb_eq)
        have hqa : (⟨p.val, hp_lt⟩ : Fin x1) ∈ S ia := by
          rcases haOut with ha1 | ⟨ha1, ha2⟩
          · rw [extFamily_lt3 S hx32 a ha1] at hpa
            simp only [ia, ha1, ↓reduceDIte]
            obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hpa
            have hqv : q.val = p.val :=
              congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
            have : q = ⟨p.val, hp_lt⟩ := Fin.ext hqv
            rwa [← this]
          · rw [extFamily_ge1 S hx32 a ha1 ha2] at hpa
            simp only [ia, ha1, ↓reduceDIte]
            rcases Finset.mem_insert.mp hpa with rfl | hpa'
            · exact absurd hp_lt ha2
            · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hpa'
              have hqv : q.val = p.val :=
                congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
              have : q = ⟨p.val, hp_lt⟩ := Fin.ext hqv
              rwa [← this]
        have hqb : (⟨p.val, hp_lt⟩ : Fin x1) ∈ S ib := by
          rcases hbOut with hb1 | ⟨hb1, hb2⟩
          · rw [extFamily_lt3 S hx32 b hb1] at hpb
            simp only [ib, hb1, ↓reduceDIte]
            obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hpb
            have hqv : q.val = p.val :=
              congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
            have : q = ⟨p.val, hp_lt⟩ := Fin.ext hqv
            rwa [← this]
          · rw [extFamily_ge1 S hx32 b hb1 hb2] at hpb
            simp only [ib, hb1, ↓reduceDIte]
            rcases Finset.mem_insert.mp hpb with rfl | hpb'
            · exact absurd hp_lt hb2
            · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hpb'
              have hqv : q.val = p.val :=
                congrArg (fun z : Fin (x1 + (x2 - x3)) => z.val) hqe
              have : q = ⟨p.val, hp_lt⟩ := Fin.ext hqv
              rwa [← this]
        exact Finset.mem_image.mpr ⟨⟨p.val, hp_lt⟩, Finset.mem_inter.mpr ⟨hqa, hqb⟩, Fin.ext rfl⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (hinter ia ib hiab))

theorem incidences_card {n m : ℕ} (F : Fin m → Finset (Fin n)) :
    (incidences F).card = ∑ l : Fin m, (F l).card := by
  have heq : incidences F =
      (Finset.univ : Finset (Fin m)).biUnion (fun l => (F l).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp [incidences]
  rw [heq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
  · intro l1 _ l2 _ hne s hs1 hs2 x hx
    obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp (hs1 hx)
    obtain ⟨p2, _, h2⟩ := Finset.mem_image.mp (hs2 hx)
    exact False.elim (hne (Prod.mk.inj h2).2.symm)

theorem univ_sum_eq_range (M : ℕ) (g : Fin M → ℕ) (f : ℕ → ℕ)
    (hfg : ∀ i : Fin M, f i.val = g i) :
    (∑ i : Fin M, g i) = (Finset.range M).sum f := by
  have himg : (Finset.univ : Finset (Fin M)).image Fin.val = Finset.range M := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun hk => ⟨⟨k, hk⟩, rfl⟩⟩
  rw [← himg, Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  exact Finset.sum_congr rfl fun i _ => (hfg i).symm

theorem extFamily_incidences (x1 x2 x3 : ℕ) (S : Fin x2 → Finset (Fin x1))
    (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2) :
    (incidences (extFamily x1 x2 x3 S hx32)).card =
      (incidences S).card + (x1 + (x2 - x3) - x3) := by
  let N := x1 + (x2 - x3)
  rw [incidences_card, incidences_card]
  let fOld : ℕ → ℕ := fun k => if hk : k < x2 then (S ⟨k, hk⟩).card else 0
  let fNew : ℕ → ℕ := fun k => if hk : k < N then (extFamily x1 x2 x3 S hx32 ⟨k, hk⟩).card else 0
  rw [univ_sum_eq_range x2 (fun l => (S l).card) fOld (fun i => by simp [fOld, i.isLt])]
  rw [univ_sum_eq_range N (fun l => (extFamily x1 x2 x3 S hx32 l).card) fNew
    (fun i => by simp [fNew, i.isLt])]
  have hx2 : x2 = x3 + (x2 - x3) := by omega
  have hN : N = x3 + (x1 - x3) + (x2 - x3) := by omega
  have holdSplit : (Finset.range x2).sum fOld =
      (Finset.range x3).sum fOld + (Finset.range (x2 - x3)).sum (fun t => fOld (x3 + t)) := by
    conv_lhs => rw [hx2]
    exact Finset.sum_range_add fOld x3 (x2 - x3)
  have hnewSplit1 : (Finset.range N).sum fNew =
      (Finset.range x3).sum fNew +
      (Finset.range (x1 - x3)).sum (fun t => fNew (x3 + t)) +
      (Finset.range (x2 - x3)).sum (fun t => fNew (x3 + (x1 - x3) + t)) := by
    conv_lhs => rw [hN]
    rw [Finset.sum_range_add fNew (x3 + (x1 - x3)) (x2 - x3),
      Finset.sum_range_add fNew x3 (x1 - x3)]
  have h1 : (Finset.range x3).sum fNew = (Finset.range x3).sum fOld := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk3 : k < x3 := Finset.mem_range.mp hk
    have hk2 : k < x2 := by omega
    have hkN : k < N := by omega
    simp only [fNew, fOld, hkN, hk2, ↓reduceDIte]
    rw [extFamily_lt3 S hx32 ⟨k, hkN⟩ hk3]
    exact Finset.card_image_of_injective _ (embPt_inj x1 (x2 - x3))
  have h2 : (Finset.range (x1 - x3)).sum (fun t => fNew (x3 + t)) = x1 - x3 := by
    have : ∀ t ∈ Finset.range (x1 - x3), fNew (x3 + t) = 1 := by
      intro t ht
      have ht' : t < x1 - x3 := Finset.mem_range.mp ht
      have hkN : x3 + t < N := by omega
      have hn3 : ¬ x3 + t < x3 := by omega
      have hkx1 : x3 + t < x1 := by omega
      simp only [fNew, hkN, ↓reduceDIte]
      rw [extFamily_mid S hx32 ⟨x3 + t, hkN⟩ hn3 hkx1, Finset.card_singleton]
    rw [Finset.sum_congr rfl this]
    simp
  have h3 : (Finset.range (x2 - x3)).sum (fun t => fNew (x3 + (x1 - x3) + t)) =
      (Finset.range (x2 - x3)).sum (fun t => fOld (x3 + t)) + (x2 - x3) := by
    have hterm : ∀ t ∈ Finset.range (x2 - x3), fNew (x3 + (x1 - x3) + t) = fOld (x3 + t) + 1 := by
      intro t ht
      have ht' : t < x2 - x3 := Finset.mem_range.mp ht
      have hkN : x3 + (x1 - x3) + t < N := by omega
      have hk2 : x3 + t < x2 := by omega
      have hn3 : ¬ x3 + (x1 - x3) + t < x3 := by omega
      have hn1 : ¬ x3 + (x1 - x3) + t < x1 := by omega
      let l : Fin N := ⟨x3 + (x1 - x3) + t, hkN⟩
      have hl_not_mem : l ∉ (S ⟨x3 + (l.val - x1), by have := l.isLt; omega⟩).image
          (embPt x1 (x2 - x3)) := by
        intro hm
        obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hm
        have hqv : q.val = l.val := congrArg (fun z : Fin N => z.val) hqe
        change q.val = x3 + (x1 - x3) + t at hqv
        have := q.isLt
        omega
      have hidx : (⟨x3 + (l.val - x1), by have := l.isLt; omega⟩ : Fin x2) = ⟨x3 + t, hk2⟩ := by
        apply Fin.ext; dsimp [l]; omega
      simp only [fNew, fOld, hkN, hk2, ↓reduceDIte]
      change (extFamily x1 x2 x3 S hx32 l).card = (S ⟨x3 + t, hk2⟩).card + 1
      rw [extFamily_ge1 S hx32 l hn3 hn1, Finset.card_insert_of_notMem hl_not_mem,
        Finset.card_image_of_injective _ (embPt_inj x1 (x2 - x3)), hidx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    simp
  rw [hnewSplit1, h1, h2, h3, holdSplit]
  omega

def remap (x1 x2 x3 w : ℕ) : ℕ :=
  let N := x1 + (x2 - x3)
  if w < x1 then w
  else if w < x1 + x3 then N + (w - x1)
  else if w < x1 + x2 then N + (x1 + (w - (x1 + x3)))
  else (N + N) + (w - (x1 + x2))

theorem remap_lt (x1 x2 x3 w j : ℕ) (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2)
    (hw : w < x1 + x2 + j) :
    remap x1 x2 x3 w < (x1 + (x2 - x3)) + (x1 + (x2 - x3)) + j := by
  unfold remap
  dsimp only
  split_ifs <;> omega

def newLineIdx (x1 x2 x3 : ℕ) (hx31 : x3 ≤ x1) (l : Fin x2) : Fin (x1 + (x2 - x3)) :=
  if hl : l.val < x3 then ⟨l.val, by omega⟩
  else ⟨x1 + (l.val - x3), by have := l.isLt; omega⟩

theorem newLineIdx_lt {x1 x2 x3 : ℕ} (hx31 : x3 ≤ x1) (l : Fin x2) (hl : l.val < x3) :
    newLineIdx x1 x2 x3 hx31 l = ⟨l.val, by omega⟩ := by
  simp [newLineIdx, hl]

theorem newLineIdx_ge {x1 x2 x3 : ℕ} (hx31 : x3 ≤ x1) (l : Fin x2) (hl : ¬ l.val < x3) :
    newLineIdx x1 x2 x3 hx31 l = ⟨x1 + (l.val - x3), by have := l.isLt; omega⟩ := by
  simp [newLineIdx, hl]

def oldX (x1 x2 x3 : ℕ) (X : Finset (Fin (x1 + (x2 - x3)))) : Finset (Fin x1) :=
  Finset.univ.filter fun p => embPt x1 (x2 - x3) p ∈ X

def oldY (x1 x2 x3 : ℕ) (hx31 : x3 ≤ x1) (Y : Finset (Fin (x1 + (x2 - x3)))) : Finset (Fin x2) :=
  Finset.univ.filter fun l => newLineIdx x1 x2 x3 hx31 l ∈ Y

theorem inL {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) (w : ℕ) (hw : w < n) :
    (incidenceInput X Y).getD w false = decide ((⟨w, hw⟩ : Fin n) ∈ X) := by
  unfold incidenceInput
  have hw1 : w < (List.ofFn fun p : Fin n => decide (p ∈ X)).length := by simp [hw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw1,
    List.getElem?_eq_getElem hw1, Option.getD_some, List.getElem_ofFn]

theorem inR {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) (w : ℕ) (hw : w < m) :
    (incidenceInput X Y).getD (n + w) false = decide ((⟨w, hw⟩ : Fin m) ∈ Y) := by
  unfold incidenceInput
  have hle : (List.ofFn fun p : Fin n => decide (p ∈ X)).length ≤ n + w := by simp
  have hw2 : n + w - (List.ofFn fun p : Fin n => decide (p ∈ X)).length <
      (List.ofFn fun l : Fin m => decide (l ∈ Y)).length := by simp [hw]
  have hw3 : n + w - (List.ofFn fun p : Fin n => decide (p ∈ X)).length < m := by simp [hw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle,
    List.getElem?_eq_getElem hw2, Option.getD_some, List.getElem_ofFn]
  have heq : (⟨n + w - (List.ofFn fun p : Fin n => decide (p ∈ X)).length, hw3⟩ : Fin m) =
      ⟨w, hw⟩ := by
    apply Fin.ext; simp
  rw [heq]

def baseCircuit (x1 x2 x3 : ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map fun g => ⟨g.op, g.inputs.map (remap x1 x2 x3)⟩
    output := remap x1 x2 x3 C.output }

theorem baseCircuit_ao2 (x1 x2 x3 : ℕ) (C : Circuit) (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2)
    (hAO : IsAO2 (x1 + x2) C) :
    IsAO2 ((x1 + (x2 - x3)) + (x1 + (x2 - x3))) (baseCircuit x1 x2 x3 C) := by
  obtain ⟨h1, h2, h3⟩ := hAO
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact h1 g0 hg0
  · intro j hj i hi
    simp only [baseCircuit, List.length_map] at hj
    have hgj : gateAt (baseCircuit x1 x2 x3 C) j =
        ⟨C.gates[j].op, C.gates[j].inputs.map (remap x1 x2 x3)⟩ := by
      simp [gateAt, baseCircuit, hj]
    have hgj0 : gateAt C j = C.gates[j] := by simp [gateAt, hj]
    rw [hgj] at hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
    apply remap_lt x1 x2 x3 w j hx31 hx32
    exact h2 j hj w (by rw [hgj0]; exact hw)
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simp [h3 g0 hg0]

theorem baseCircuit_wires (x1 x2 x3 : ℕ) (C : Circuit) (hx31 : x3 ≤ x1) (hx32 : x3 ≤ x2)
    (hAO : IsAO2 (x1 + x2) C)
    (X Y : Finset (Fin (x1 + (x2 - x3)))) :
    ∀ k ≤ C.gates.length, ∀ w < x1 + x2 + k,
      (run (baseCircuit x1 x2 x3 C).gates (incidenceInput X Y)).getD (remap x1 x2 x3 w) false =
      (run C.gates (incidenceInput (oldX x1 x2 x3 X) (oldY x1 x2 x3 hx31 Y))).getD w false := by
  let N := x1 + (x2 - x3)
  have hlenNew : (incidenceInput X Y).length = N + N := by simp [incidenceInput, N]
  have hlenOld : (incidenceInput (oldX x1 x2 x3 X) (oldY x1 x2 x3 hx31 Y)).length = x1 + x2 := by
    simp [incidenceInput]
  intro k
  induction k with
  | zero =>
    intro _ w hw
    have hw' : w < x1 + x2 := by omega
    have hrem : remap x1 x2 x3 w < N + N := by
      simpa using remap_lt x1 x2 x3 w 0 hx31 hx32 (by omega)
    rw [run_input _ _ _ (by rw [hlenNew]; exact hrem),
      run_input _ _ _ (by rw [hlenOld]; exact hw')]
    unfold remap
    dsimp only
    by_cases h1 : w < x1
    · simp only [h1, ↓reduceIte]
      have hwN : w < N := by omega
      rw [inL X Y w hwN, inL _ _ w h1]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, decide_eq_true_eq]
      unfold oldX
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
    · by_cases h2 : w < x1 + x3
      · simp only [h1, h2, ↓reduceIte]
        have ht3 : w - x1 < x3 := by omega
        have ht2 : w - x1 < x2 := by omega
        have htN : w - x1 < N := by omega
        have hweq : x1 + (w - x1) = w := by omega
        conv_rhs => rw [← hweq]
        rw [inR X Y (w - x1) htN, inR _ _ (w - x1) ht2]
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, decide_eq_true_eq]
        have hnl : newLineIdx x1 x2 x3 hx31 ⟨w - x1, ht2⟩ = ⟨w - x1, htN⟩ :=
          newLineIdx_lt hx31 ⟨w - x1, ht2⟩ ht3
        unfold oldY
        rw [Finset.mem_filter, hnl]
        exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
      · simp only [h1, h2, hw', ↓reduceIte]
        have ht2 : w - x1 < x2 := by omega
        have htnot : ¬ w - x1 < x3 := by omega
        have hshN : x1 + (w - (x1 + x3)) < N := by omega
        have hweq : x1 + (w - x1) = w := by omega
        conv_rhs => rw [← hweq]
        rw [inR X Y (x1 + (w - (x1 + x3))) hshN, inR _ _ (w - x1) ht2]
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, decide_eq_true_eq]
        have hnl : newLineIdx x1 x2 x3 hx31 ⟨w - x1, ht2⟩ = ⟨x1 + (w - (x1 + x3)), hshN⟩ := by
          rw [newLineIdx_ge hx31 ⟨w - x1, ht2⟩ htnot]
          apply Fin.ext; dsimp; omega
        unfold oldY
        rw [Finset.mem_filter, hnl]
        exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  | succ k ih =>
    intro hk w hw
    rcases Nat.lt_or_ge w (x1 + x2 + k) with hlt | hge
    · exact ih (by omega) w hlt
    · have hweq : w = x1 + x2 + k := by omega
      subst hweq
      have hk' : k < C.gates.length := by omega
      have hkNew : k < (baseCircuit x1 x2 x3 C).gates.length := by simp [baseCircuit, hk']
      have hrem : remap x1 x2 x3 (x1 + x2 + k) = N + N + k := by
        unfold remap; dsimp only
        have hn1 : ¬ x1 + x2 + k < x1 := by omega
        have hn2 : ¬ x1 + x2 + k < x1 + x3 := by omega
        have hn3 : ¬ x1 + x2 + k < x1 + x2 := by omega
        simp only [hn1, hn2, hn3, ↓reduceIte]
        omega
      rw [hrem]
      have rgNew := run_gate (baseCircuit x1 x2 x3 C).gates (incidenceInput X Y) k hkNew
      have rgOld := run_gate C.gates (incidenceInput (oldX x1 x2 x3 X) (oldY x1 x2 x3 hx31 Y)) k hk'
      rw [hlenNew] at rgNew
      rw [hlenOld] at rgOld
      rw [rgNew, rgOld]
      have hbg : (baseCircuit x1 x2 x3 C).gates[k] =
          ⟨C.gates[k].op, C.gates[k].inputs.map (remap x1 x2 x3)⟩ := by
        simp [baseCircuit]
      rw [hbg, List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      have hrb : i < x1 + x2 + k := by
        have hga : gateAt C k = C.gates[k] := by simp [gateAt, hk']
        exact hAO.2.1 k hk' i (by rw [hga]; exact hi)
      have hrem_i : remap x1 x2 x3 i < N + N + k :=
        remap_lt x1 x2 x3 i k hx31 hx32 hrb
      simp only [Function.comp, hrem_i, hrb, ↓reduceIte]
      exact ih (by omega) i hrb

def padDiag (N start : ℕ) : ℕ → Circuit → Circuit
  | 0, C => C
  | d + 1, C =>
    let C' := padDiag N start d C
    let k := start + d
    let wAnd := N + N + C'.gates.length
    { gates := C'.gates ++ [⟨GateOp.and, [k, N + k]⟩, ⟨GateOp.or, [C'.output, wAnd]⟩]
      output := wAnd + 1 }

theorem padDiag_size (N start d : ℕ) (C : Circuit) :
    (padDiag N start d C).gates.length = C.gates.length + 2 * d := by
  induction d with
  | zero => simp [padDiag]
  | succ d ih => simp [padDiag, ih]; omega

theorem padDiag_out (N start d : ℕ) (C : Circuit)
    (hout : C.output < N + N + C.gates.length) :
    (padDiag N start d C).output < N + N + (padDiag N start d C).gates.length := by
  induction d with
  | zero => exact hout
  | succ d _ =>
    simp only [padDiag, List.length_append, List.length_cons, List.length_nil]
    omega

theorem padDiag_ao2 (N start d : ℕ) (C : Circuit)
    (hd : start + d ≤ N) (hAO : IsAO2 (N + N) C)
    (hout : C.output < N + N + C.gates.length) :
    IsAO2 (N + N) (padDiag N start d C) := by
  induction d with
  | zero => exact hAO
  | succ d ih =>
    let C' := padDiag N start d C
    have hAO' : IsAO2 (N + N) C' := ih (by omega)
    have hout' : C'.output < N + N + C'.gates.length := padDiag_out N start d C hout
    let g1 : Gate := ⟨GateOp.and, [start + d, N + (start + d)]⟩
    let g2 : Gate := ⟨GateOp.or, [C'.output, N + N + C'.gates.length]⟩
    let C'' : Circuit := { gates := C'.gates ++ [g1, g2], output := N + N + C'.gates.length + 1 }
    change IsAO2 (N + N) C''
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact hAO'.1 g hg1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg2
        rcases hg2 with rfl | rfl <;> simp [g1, g2]
    · intro j hj i hi
      have hj' : j < C'.gates.length + 2 := by simpa [C''] using hj
      rcases Nat.lt_or_ge j C'.gates.length with hlt | hge
      · have hga : gateAt C'' j = gateAt C' j := by
          simp [C'', gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hga] at hi
        exact hAO'.2.1 j hlt i hi
      · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
        · have hga : gateAt C'' C'.gates.length = g1 := by
            simp [C'', gateAt, List.getD_eq_getElem?_getD]
          rw [hga] at hi
          simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
        · have hjeq : j = C'.gates.length + 1 := by omega
          subst hjeq
          have hga : gateAt C'' (C'.gates.length + 1) = g2 := by
            simp [C'', gateAt, List.getD_eq_getElem?_getD]
          rw [hga] at hi
          simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact hAO'.2.2 g hg1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg2
        rcases hg2 with rfl | rfl <;> simp [g1, g2]

theorem padDiag_eval (N start d : ℕ) (C : Circuit)
    (hd : start + d ≤ N) (hout : C.output < N + N + C.gates.length)
    (X Y : Finset (Fin N)) :
    (padDiag N start d C).eval (incidenceInput X Y) = true ↔
      C.eval (incidenceInput X Y) = true ∨
      ∃ t < d, ∃ ht : start + t < N, (⟨start + t, ht⟩ : Fin N) ∈ X ∧ (⟨start + t, ht⟩ : Fin N) ∈ Y := by
  have hlen : (incidenceInput X Y).length = N + N := by simp [incidenceInput]
  induction d with
  | zero =>
    simp [padDiag]
  | succ d ih =>
    let C' := padDiag N start d C
    have hout' : C'.output < N + N + C'.gates.length := padDiag_out N start d C hout
    let g1 : Gate := ⟨GateOp.and, [start + d, N + (start + d)]⟩
    let g2 : Gate := ⟨GateOp.or, [C'.output, N + N + C'.gates.length]⟩
    have hev : (padDiag N start (d + 1) C).eval (incidenceInput X Y) =
        (run ((C'.gates ++ [g1]) ++ [g2]) (incidenceInput X Y)).getD
          (N + N + C'.gates.length + 1) false := by
      simp [padDiag, C', g1, g2, Circuit.eval, Circuit.wires, run, List.append_assoc]
    rw [hev]
    have hlen1 : (run (C'.gates ++ [g1]) (incidenceInput X Y)).length =
        N + N + C'.gates.length + 1 := by
      rw [run_length, hlen, List.length_append, List.length_singleton]; omega
    have hlen0 : (run C'.gates (incidenceInput X Y)).length = N + N + C'.gates.length := by
      rw [run_length, hlen]
    rw [run_snoc, ← hlen1, getD_at']
    have hvOut : (run (C'.gates ++ [g1]) (incidenceInput X Y)).getD C'.output false =
        C'.eval (incidenceInput X Y) := by
      exact run_prefix C'.gates [g1] (incidenceInput X Y) C'.output (by rw [hlen]; exact hout')
    have hvAnd : (run (C'.gates ++ [g1]) (incidenceInput X Y)).getD
        (N + N + C'.gates.length) false =
        ((incidenceInput X Y).getD (start + d) false &&
          (incidenceInput X Y).getD (N + (start + d)) false) := by
      rw [run_snoc, ← hlen0, getD_at']
      have hkN : start + d < N := by omega
      have h1 : (run C'.gates (incidenceInput X Y)).getD (start + d) false =
          (incidenceInput X Y).getD (start + d) false :=
        run_input _ _ _ (by rw [hlen]; omega)
      have h2 : (run C'.gates (incidenceInput X Y)).getD (N + (start + d)) false =
          (incidenceInput X Y).getD (N + (start + d)) false :=
        run_input _ _ _ (by rw [hlen]; omega)
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id_eq, h1, h2]
    have hkN : start + d < N := by omega
    simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, hvOut, hvAnd, inL X Y (start + d) hkN, inR X Y (start + d) hkN,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    have hih : C'.eval (incidenceInput X Y) = true ↔
        C.eval (incidenceInput X Y) = true ∨
        ∃ t < d, ∃ ht : start + t < N,
          (⟨start + t, ht⟩ : Fin N) ∈ X ∧ (⟨start + t, ht⟩ : Fin N) ∈ Y := ih (by omega)
    rw [hih]
    constructor
    · rintro ((hC | ⟨t, ht, htn, hx, hy⟩) | ⟨hx, hy⟩)
      · exact Or.inl hC
      · exact Or.inr ⟨t, Nat.lt_succ_of_lt ht, htn, hx, hy⟩
      · exact Or.inr ⟨d, Nat.lt_succ_self d, hkN, hx, hy⟩
    · rintro (hC | ⟨t, ht, htn, hx, hy⟩)
      · exact Or.inl (Or.inl hC)
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
        · exact Or.inl (Or.inr ⟨t, hlt, htn, hx, hy⟩)
        · exact Or.inr ⟨hx, hy⟩

theorem solve (x1 x2 x3 : ℕ) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Circuit)
    (x6 : x3 ≤ x1) (x7 : x3 ≤ x2)
    (hdiag : ∀ x8 : Fin x3, Fin.castLE x6 x8 ∈ x4 (Fin.castLE x7 x8))
    (hinter : ∀ x9 x10 : Fin x2, x9 ≠ x10 → (x4 x9 ∩ x4 x10).card ≤ 1)
    (hAO : IsAO2 (x1 + x2) x5)
    (hout : x5.output < x1 + x2 + x5.size)
    (hcomp : ComputesIncidence x4 x5) :
    let x13 : ℕ := x1 + (x2 - x3)
    ∃ (x14 : Fin x13 → Finset (Fin x13)) (x15 : Circuit),
      (∀ x16 : Fin x13, x16 ∈ x14 x16) ∧
      (∀ x16 x17 : Fin x13, x16 ≠ x17 → (x14 x16 ∩ x14 x17).card ≤ 1) ∧
      IsAO2 (x13 + x13) x15 ∧
      ComputesIncidence x14 x15 ∧
      (incidences x14).card = (incidences x4).card + (x13 - x3) ∧
      x15.size = x5.size + 2 * (x13 - x3) := by
  let N := x1 + (x2 - x3)
  let S' := extFamily x1 x2 x3 x4 x7
  let B := baseCircuit x1 x2 x3 x5
  let C' := padDiag N x3 (N - x3) B
  have hB_ao2 : IsAO2 (N + N) B := baseCircuit_ao2 x1 x2 x3 x5 x6 x7 hAO
  have hB_out : B.output < N + N + B.gates.length := by
    simp only [B, baseCircuit, List.length_map]
    exact remap_lt x1 x2 x3 x5.output x5.gates.length x6 x7 hout
  have hd : x3 + (N - x3) ≤ N := by omega
  refine ⟨S', C', extFamily_diag x1 x2 x3 x4 x6 x7 hdiag,
    extFamily_inter x1 x2 x3 x4 x6 x7 hinter,
    padDiag_ao2 N x3 (N - x3) B hd hB_ao2 hB_out, ?_,
    extFamily_incidences x1 x2 x3 x4 x6 x7, ?_⟩
  · intro X Y
    apply Bool.eq_iff_iff.mpr
    rw [padDiag_eval N x3 (N - x3) B hd hB_out X Y]
    have hBeval : B.eval (incidenceInput X Y) =
        incidenceFun x4 (oldX x1 x2 x3 X) (oldY x1 x2 x3 x6 Y) := by
      have hw := baseCircuit_wires x1 x2 x3 x5 x6 x7 hAO X Y x5.gates.length le_rfl x5.output hout
      exact hw.trans (hcomp (oldX x1 x2 x3 X) (oldY x1 x2 x3 x6 Y))
    rw [hBeval]
    simp only [incidenceFun, decide_eq_true_eq]
    constructor
    · rintro (⟨p0, hp0, l0, hl0, hinc0⟩ | ⟨t, ht, htn, hx, hy⟩)
      · simp only [oldX, Finset.mem_filter, Finset.mem_univ, true_and] at hp0
        simp only [oldY, Finset.mem_filter, Finset.mem_univ, true_and] at hl0
        refine ⟨embPt x1 (x2 - x3) p0, hp0, newLineIdx x1 x2 x3 x6 l0, hl0, ?_⟩
        by_cases hl3 : l0.val < x3
        · rw [newLineIdx_lt x6 l0 hl3]
          dsimp only [S']
          rw [extFamily_lt3 x4 x7 ⟨l0.val, by omega⟩ hl3]
          exact Finset.mem_image.mpr ⟨p0, hinc0, rfl⟩
        · rw [newLineIdx_ge x6 l0 hl3]
          dsimp only [S']
          have hl0Lt := l0.isLt
          have hn1 : ¬ x1 + (l0.val - x3) < x3 := by omega
          have hn2 : ¬ x1 + (l0.val - x3) < x1 := by omega
          rw [extFamily_ge1 x4 x7 ⟨x1 + (l0.val - x3), by omega⟩ hn1 hn2]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p0, ?_, rfl⟩)
          have hl_eq : (⟨x3 + ((x1 + (l0.val - x3)) - x1), by omega⟩ : Fin x2) = l0 := by
            apply Fin.ext; dsimp; omega
          rwa [hl_eq]
      · refine ⟨⟨x3 + t, htn⟩, hx, ⟨x3 + t, htn⟩, hy, ?_⟩
        exact extFamily_diag x1 x2 x3 x4 x6 x7 hdiag ⟨x3 + t, htn⟩
    · rintro ⟨p, hp, l, hl, hinc⟩
      have hpLt := p.isLt
      have hlLt := l.isLt
      dsimp only [S'] at hinc
      by_cases hl3 : l.val < x3
      · rw [extFamily_lt3 x4 x7 l hl3] at hinc
        obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hinc
        left
        refine ⟨p0, by simp [oldX, hp], ⟨l.val, Nat.lt_of_lt_of_le hl3 x7⟩, ?_, hp0⟩
        simp [oldY, newLineIdx_lt x6 ⟨l.val, Nat.lt_of_lt_of_le hl3 x7⟩ hl3, hl]
      · by_cases hl1 : l.val < x1
        · rw [extFamily_mid x4 x7 l hl3 hl1] at hinc
          have hpl : p = l := Finset.mem_singleton.mp hinc
          subst hpl
          right
          refine ⟨p.val - x3, by omega, by omega, ?_, ?_⟩ <;>
            (have heq : (⟨x3 + (p.val - x3), by omega⟩ : Fin N) = p := by
              apply Fin.ext; dsimp; omega
             rwa [heq])
        · rw [extFamily_ge1 x4 x7 l hl3 hl1] at hinc
          rcases Finset.mem_insert.mp hinc with rfl | hinc'
          · right
            refine ⟨p.val - x3, by omega, by omega, ?_, ?_⟩ <;>
              (have heq : (⟨x3 + (p.val - x3), by omega⟩ : Fin N) = p := by
                apply Fin.ext; dsimp; omega
               rwa [heq])
          · obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hinc'
            left
            let l0 : Fin x2 := ⟨x3 + (l.val - x1), by omega⟩
            refine ⟨p0, by simp [oldX, hp], l0, ?_, hp0⟩
            have hl0_not : ¬ l0.val < x3 := by dsimp [l0]; omega
            have hnl : newLineIdx x1 x2 x3 x6 l0 = l := by
              rw [newLineIdx_ge x6 l0 hl0_not]
              apply Fin.ext; dsimp [l0]; omega
            simp [oldY, hnl, hl]
  · change (padDiag N x3 (N - x3) B).gates.length = x5.gates.length + 2 * (N - x3)
    rw [padDiag_size]
    simp [B, baseCircuit]

end PEqualNP.Outside.L_meta_6674

theorem PEqualNP.Outside.L_meta_6674 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : x3 ≤ x1) (x7 : x3 ≤ x2),   (∀ (x8 : Fin x3), Fin.castLE x6 x8 ∈ x4 (Fin.castLE x7 x8)) →     (∀ (x9 x10 : Fin x2), x9 ≠ x10 → (x4 x9 ∩ x4 x10).card ≤ (1 : ℕ)) →       PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →         x5.output < x1 + x2 + x5.size →           PEqualNP.GenericRejection.ComputesIncidence x4 x5 →             have x13 : ℕ := x1 + (x2 - x3);             ∃ (x14 : Fin x13 → Finset (Fin x13)) (x15 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x16 : Fin x13), x16 ∈ x14 x16) ∧ (∀ (x16 x17 : Fin x13), x16 ≠ x17 → (x14 x16 ∩ x14 x17).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x13 + x13) x15 ∧ PEqualNP.GenericRejection.ComputesIncidence x14 x15 ∧ (PEqualNP.HeptadCover.incidences x14).card = (PEqualNP.HeptadCover.incidences x4).card + (x13 - x3) ∧ x15.size = x5.size + (2 : ℕ) * (x13 - x3) := by
  exact PEqualNP.Outside.L_meta_6674.solve
