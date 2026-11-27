import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev W := BitVec 13

def mkW (f : Fin 13 → Bool) : W :=
  BitVec.cons (f 12) (BitVec.cons (f 11) (BitVec.cons (f 10) (BitVec.cons (f 9)
  (BitVec.cons (f 8) (BitVec.cons (f 7) (BitVec.cons (f 6) (BitVec.cons (f 5)
  (BitVec.cons (f 4) (BitVec.cons (f 3) (BitVec.cons (f 2) (BitVec.cons (f 1)
  (BitVec.cons (f 0) BitVec.nil))))))))))))

lemma getLsbD_mkW (f : Fin 13 → Bool) (r : ℕ) (hr : r < 13) :
    (mkW f).getLsbD r = f ⟨r, hr⟩ := by
  interval_cases r <;> (simp only [mkW, BitVec.getLsbD_cons]; simp)

def rowData : Fin 13 → Fin 6 → Bool
  | 0, k => decide (k = 0 ∨ k = 3)
  | 1, k => decide (k = 1 ∨ k = 3)
  | 2, k => decide (k = 1 ∨ k = 4)
  | 3, k => decide (k = 2 ∨ k = 4)
  | 4, k => decide (k = 2 ∨ k = 5)
  | 5, k => decide (k = 0 ∨ k = 1 ∨ k = 2)
  | 6, k => decide (k = 2 ∨ k = 3)
  | 7, k => decide (k = 0 ∨ k = 1 ∨ k = 5)
  | 8, k => decide (k = 0 ∨ k = 4 ∨ k = 5)
  | 9, k => decide (k = 3 ∨ k = 4 ∨ k = 5)
  | 10, k => decide (k = 0 ∨ k = 4)
  | 11, k => decide (k = 0 ∨ k = 5)
  | 12, k => decide (k = 1 ∨ k = 5)

def goal : W := BitVec.ofNat 13 31

def isBad (w : W) : Bool :=
  w.getLsbD 6 || w.getLsbD 10 || w.getLsbD 11 || w.getLsbD 12

def stepOp (isAnd : Bool) (a b : W) : W :=
  if isAnd then a &&& b else a ||| b

def inVec (i : Fin 6) : W :=
  mkW fun r : Fin 13 => rowData r i

def initList : List W :=
  [inVec 0, inVec 1, inVec 2, inVec 3, inVec 4, inVec 5]

def initSet : Finset W := initList.toFinset

def Build : ℕ → Finset W → Bool → Prop
  | 0, avail, seen => goal ∈ avail ∧ seen = true
  | k + 1, avail, seen =>
      Build k avail seen ∨
      ∃ a ∈ avail, ∃ b ∈ avail, ∃ isAnd : Bool,
        Build k (insert (stepOp isAnd a b) avail) (seen || (isAnd && isBad (stepOp isAnd a b)))

def Live : ℕ → Finset W → Bool → Prop
  | 0, s, seen => s = {goal} ∧ seen = true
  | k + 1, s, seen =>
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ isAnd : Bool,
        stepOp isAnd a b ∉ s ∧
        ∃ rest : Finset W, s = insert a (insert b rest) ∧
          Live k (insert (stepOp isAnd a b) rest)
            (seen || (isAnd && isBad (stepOp isAnd a b)))

lemma stepOp_idem (isAnd : Bool) (a : W) : stepOp isAnd a a = a := by
  cases isAnd <;> simp [stepOp]

lemma live_seen_mono {k : ℕ} {s : Finset W} {b1 b2 : Bool}
    (h : Live k s b1) (hb : b1 = true → b2 = true) : Live k s b2 := by
  induction k generalizing s b1 b2 with
  | zero => exact ⟨h.1, hb h.2⟩
  | succ k ih =>
    obtain ⟨a, ha, b, hb', hne, isAnd, hnout, rest, hs, htail⟩ := h
    refine ⟨a, ha, b, hb', hne, isAnd, hnout, rest, hs, ih htail ?_⟩
    intro h1
    rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
    · simp [hb h1]
    · simp [h1]

theorem compress_strong {k : ℕ} {avail : Finset W} {seen : Bool}
    (h : Build k avail seen) :
    (∃ s ⊆ avail, Live k s seen) ∨ (∃ k' < k, ∃ s ⊆ avail, Live k' s true) := by
  induction k generalizing avail seen with
  | zero =>
    exact Or.inl ⟨{goal}, Finset.singleton_subset_iff.mpr h.1, rfl, h.2⟩
  | succ k ih =>
    rcases h with hskip | ⟨a, ha, b, hb, isAnd, htail⟩
    · rcases ih hskip with ⟨s, hs, hrun⟩ | ⟨k', hk', s, hs, hrun⟩
      · exact Or.inr ⟨k, Nat.lt_succ_self k, s, hs, live_seen_mono hrun (fun _ => rfl)⟩
      · exact Or.inr ⟨k', Nat.lt_trans hk' (Nat.lt_succ_self k), s, hs, hrun⟩
    · set z := stepOp isAnd a b
      rcases ih htail with ⟨t, ht, hrun⟩ | ⟨k', hk', t, ht, hrun⟩
      · by_cases hsub : t ⊆ avail
        · exact Or.inr ⟨k, Nat.lt_succ_self k, t, hsub, live_seen_mono hrun (fun _ => rfl)⟩
        · have hzmem : z ∈ t := by
            by_contra hn
            apply hsub
            intro u hu
            rcases Finset.mem_insert.mp (ht hu) with rfl | ok
            · exact False.elim (hn hu)
            · exact ok
          have hzout : z ∉ avail := fun hh => hsub ((Finset.insert_eq_of_mem hh) ▸ ht)
          have hne : a ≠ b := by
            intro hab; subst hab
            exact hzout (by simpa [z, stepOp_idem] using ha)
          let rest := t.erase z
          have hrest : rest ⊆ avail := by
            intro u hu
            have hu' := Finset.mem_erase.mp hu
            exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
          let s := insert a (insert b rest)
          have hs : s ⊆ avail := Finset.insert_subset ha (Finset.insert_subset hb hrest)
          refine Or.inl ⟨s, hs, a, by simp [s], b, by simp [s], hne, isAnd,
            fun hm => hzout (hs hm), rest, rfl, ?_⟩
          simpa [rest, Finset.insert_erase hzmem, z] using hrun
      · by_cases hsub : t ⊆ avail
        · exact Or.inr ⟨k', Nat.lt_trans hk' (Nat.lt_succ_self k), t, hsub, hrun⟩
        · have hzmem : z ∈ t := by
            by_contra hn
            apply hsub
            intro u hu
            rcases Finset.mem_insert.mp (ht hu) with rfl | ok
            · exact False.elim (hn hu)
            · exact ok
          have hzout : z ∉ avail := fun hh => hsub ((Finset.insert_eq_of_mem hh) ▸ ht)
          have hne : a ≠ b := by
            intro hab; subst hab
            exact hzout (by simpa [z, stepOp_idem] using ha)
          let rest := t.erase z
          have hrest : rest ⊆ avail := by
            intro u hu
            have hu' := Finset.mem_erase.mp hu
            exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
          let s := insert a (insert b rest)
          have hs : s ⊆ avail := Finset.insert_subset ha (Finset.insert_subset hb hrest)
          refine Or.inr ⟨k' + 1, Nat.succ_lt_succ hk', s, hs, a, by simp [s], b, by simp [s],
            hne, isAnd, fun hm => hzout (hs hm), rest, rfl, ?_⟩
          simpa [rest, Finset.insert_erase hzmem, z] using hrun

lemma live_card {k : ℕ} {s : Finset W} {seen : Bool} (h : Live k s seen) :
    s.card ≤ k + 1 := by
  induction k generalizing s seen with
  | zero => rw [h.1]; simp
  | succ k ih =>
    obtain ⟨a, _, b, _, _, isAnd, hnout, rest, rfl, htail⟩ := h
    have hzrest : stepOp isAnd a b ∉ rest := fun hm => hnout (by simp [hm])
    have ht := ih htail
    rw [Finset.card_insert_of_notMem hzrest] at ht
    have h1 := Finset.card_insert_le a (insert b rest)
    have h2 := Finset.card_insert_le b rest
    omega

def separates (e m : Fin 5) (w : W) : Prop :=
  w.getLsbD e.val = true ∧ w.getLsbD (5 + m.val) = false

lemma stepOp_separates (e m : Fin 5) (isAnd : Bool) (a b : W)
    (h : separates e m (stepOp isAnd a b)) :
    separates e m a ∨ separates e m b := by
  unfold separates at h ⊢
  unfold stepOp at h
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_or, Bool.or_eq_true,
      Bool.or_eq_false_iff] at h
    rcases h with ⟨ha | hb, hma, hmb⟩
    · exact Or.inl ⟨ha, hma⟩
    · exact Or.inr ⟨hb, hmb⟩
  · simp only [↓reduceIte, BitVec.getLsbD_and, Bool.and_eq_true, Bool.and_eq_false_iff] at h
    rcases h with ⟨⟨ha, hb⟩, hma | hmb⟩
    · exact Or.inl ⟨ha, hma⟩
    · exact Or.inr ⟨hb, hmb⟩

lemma live_separates (e m : Fin 5) {k : ℕ} {s : Finset W} {seen : Bool}
    (h : Live k s seen) : ∃ w ∈ s, separates e m w := by
  induction k generalizing s seen with
  | zero =>
    refine ⟨goal, by simp [h.1], ?_⟩
    unfold separates goal
    fin_cases e <;> fin_cases m <;> decide
  | succ k ih =>
    obtain ⟨a, ha, b, hb, _, isAnd, _, rest, rfl, htail⟩ := h
    obtain ⟨w, hw, hsep⟩ := ih htail
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · rcases stepOp_separates e m isAnd a b hsep with h1 | h2
      · exact ⟨a, ha, h1⟩
      · exact ⟨b, hb, h2⟩
    · exact ⟨w, by simp [hwr], hsep⟩

def sepMask (w : W) : BitVec 25 :=
  let m0 : BitVec 25 := (~~~(w.extractLsb' 5 5)).setWidth 25
  (if w.getLsbD 0 then m0 else 0) |||
  (if w.getLsbD 1 then m0 <<< 5 else 0) |||
  (if w.getLsbD 2 then m0 <<< 10 else 0) |||
  (if w.getLsbD 3 then m0 <<< 15 else 0) |||
  (if w.getLsbD 4 then m0 <<< 20 else 0)

def allSep : BitVec 25 := BitVec.ofNat 25 33554431

def cuts (ws : List W) : BitVec 25 :=
  ws.foldr (fun w acc => sepMask w ||| acc) 0

lemma sepMask_bit (e m : Fin 5) (w : W) (h : separates e m w) :
    (sepMask w).getLsbD (5 * e.val + m.val) = true := by
  obtain ⟨he, hm⟩ := h
  fin_cases e <;> fin_cases m <;> simp_all [sepMask]

lemma cuts_bit (e m : Fin 5) (ws : List W) (w : W) (hw : w ∈ ws) (h : separates e m w) :
    (cuts ws).getLsbD (5 * e.val + m.val) = true := by
  induction ws with
  | nil => simp at hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with rfl | hxs
    · simp [cuts, sepMask_bit e m w h]
    · simp only [cuts, List.foldr_cons, BitVec.getLsbD_or, Bool.or_eq_true]
      exact Or.inr (ih hxs)

lemma allSep_bit (i : ℕ) (hi : i < 25) : allSep.getLsbD i = true := by
  have h : ∀ j : Fin 25, allSep.getLsbD j.val = true := by decide
  exact h ⟨i, hi⟩

lemma cuts_eq_allSep {k : ℕ} {ws : List W} {seen : Bool}
    (h : Live k ws.toFinset seen) : cuts ws = allSep := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let e : Fin 5 := ⟨i / 5, by omega⟩
  let m : Fin 5 := ⟨i % 5, by omega⟩
  have hie : i = 5 * e.val + m.val := by dsimp [e, m]; omega
  obtain ⟨w, hw, hsep⟩ := live_separates e m h
  have h1 : (cuts ws).getLsbD i = true := by
    rw [hie]; exact cuts_bit e m ws w (List.mem_toFinset.mp hw) hsep
  rw [h1, allSep_bit i hi]

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      exact ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩),
        (hp.cons x).trans (.swap _ _ _)⟩

lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, hm, hp⟩ := pick_one ha'
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (List.Perm.swap b a r).symm⟩
      · obtain ⟨r, hm, hp⟩ := ih ha' hb'
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def search : ℕ → List W → Bool → Bool
  | 0, ws, seen => seen && decide (ws = [goal])
  | k + 1, ws, seen =>
      if ws.length > k + 2 then false
      else if cuts ws != allSep then false
      else
        (pairs ws).any fun (a, b, tail) =>
          [true, false].any fun isAnd =>
            let z := stepOp isAnd a b
            if z ∈ ws then false
            else
              let nb := seen || (isAnd && isBad z)
              search k (z :: tail) nb ||
              (ws.length ≤ k + 1 && (search k (z :: a :: tail) nb || search k (z :: b :: tail) nb)) ||
              (ws.length ≤ k && search k (z :: a :: b :: tail) nb)

lemma stepOp_comm (isAnd : Bool) (a b : W) : stepOp isAnd a b = stepOp isAnd b a := by
  cases isAnd <;> simp [stepOp, BitVec.and_comm, BitVec.or_comm]

lemma perm_toFinset {α : Type} [DecidableEq α] {l1 l2 : List α} (h : l1.Perm l2) :
    l1.toFinset = l2.toFinset := by
  ext x; simp [h.mem_iff]

lemma search_complete : ∀ (k : ℕ) (ws : List W) (seen : Bool),
    ws.Nodup → Live k ws.toFinset seen → search k ws seen = true := by
  intro k
  induction k with
  | zero =>
    intro ws seen hnd ⟨hset, hseen⟩
    have hlen : ws.length = 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hset]; simp
    cases ws with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil =>
        have hx : x = goal := by
          have : x ∈ ({goal} : Finset W) := by rw [← hset]; simp
          simpa using this
        simp [search, hseen, hx]
      | cons y ys => simp at hlen
  | succ k ih =>
    intro ws seen hnd hlive
    have hcard : ws.length ≤ k + 2 := by
      rw [← List.toFinset_card_of_nodup hnd]
      exact live_card hlive
    have hcuts : cuts ws = allSep := cuts_eq_allSep hlive
    simp only [search, show ¬ (ws.length > k + 2) by omega, ↓reduceIte, hcuts, bne_self_eq_false,
      Bool.false_eq_true, List.any_eq_true]
    obtain ⟨a, ha, b, hb, hne, isAnd, hnout, rest, hs, htail⟩ := hlive
    obtain ⟨tail, hpair, hperm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hne
    have hnd_ab : (a :: b :: tail).Nodup := (hperm.nodup_iff).mp hnd
    have hlen_ab : ws.length = tail.length + 2 := by
      simpa using hperm.length_eq
    have ha_nt : a ∉ tail := by
      intro h; exact (List.nodup_cons.mp hnd_ab).1 (List.mem_cons_of_mem _ h)
    have hb_nt : b ∉ tail := (List.nodup_cons.mp (List.nodup_cons.mp hnd_ab).2).1
    have hnd_t : tail.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd_ab).2).2
    have htail_sub : tail.toFinset ⊆ rest := by
      intro x hx
      have hxs : x ∈ ws.toFinset := by
        rw [perm_toFinset hperm]; simp [List.mem_toFinset.mp hx]
      rw [hs] at hxs
      have hxa : x ≠ a := fun e => ha_nt (e ▸ List.mem_toFinset.mp hx)
      have hxb : x ≠ b := fun e => hb_nt (e ▸ List.mem_toFinset.mp hx)
      rcases Finset.mem_insert.mp hxs with rfl | h1
      · exact False.elim (hxa rfl)
      · rcases Finset.mem_insert.mp h1 with rfl | h2
        · exact False.elim (hxb rfl)
        · exact h2
    have hrest_sub : rest ⊆ (a :: b :: tail).toFinset := by
      intro x hx
      have hxs : x ∈ ws.toFinset := by rw [hs]; simp [hx]
      rwa [perm_toFinset hperm] at hxs
    set z := stepOp isAnd a b
    have hz_nws : z ∉ ws := fun hm => hnout (List.mem_toFinset.mpr hm)
    have hz_nab : z ∉ a :: b :: tail := fun hm => hz_nws (hperm.mem_iff.mpr hm)
    have hz_nt : z ∉ tail := fun hm => hz_nab (by simp [hm])
    have hza : z ≠ a := fun e => hz_nab (by simp [e])
    have hzb : z ≠ b := fun e => hz_nab (by simp [e])
    have hbranch : ∀ (u v : W), (u = a ∧ v = b) ∨ (u = b ∧ v = a) →
        let z' := stepOp isAnd u v
        let nb := seen || (isAnd && isBad z')
        search k (z' :: tail) nb = true ∨
        (ws.length ≤ k + 1 ∧ (search k (z' :: u :: tail) nb = true ∨
          search k (z' :: v :: tail) nb = true)) ∨
        (ws.length ≤ k ∧ search k (z' :: u :: v :: tail) nb = true) := by
      intro u v huv
      have hz' : stepOp isAnd u v = z := by
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact stepOp_comm isAnd u v
      dsimp only
      rw [hz']
      by_cases har : a ∈ rest
      · by_cases hbr : b ∈ rest
        · have hreq : rest = (a :: b :: tail).toFinset := by
            apply Finset.Subset.antisymm hrest_sub
            intro x hx
            simp only [List.toFinset_cons, Finset.mem_insert] at hx
            rcases hx with rfl | rfl | hx
            · exact har
            · exact hbr
            · exact htail_sub hx
          have huv_set : (z :: u :: v :: tail).toFinset = insert z rest := by
            rw [hreq]
            rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp
            · ext x; simp [or_comm, or_left_comm]
          have huv_nd : (z :: u :: v :: tail).Nodup := by
            rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact List.nodup_cons.mpr ⟨hz_nab, hnd_ab⟩
            · exact List.nodup_cons.mpr ⟨fun hm => hz_nab (by simp_all),
                List.nodup_cons.mpr ⟨fun hm => by
                  rcases List.mem_cons.mp hm with rfl | hm
                  · exact hne rfl
                  · exact hb_nt hm,
                List.nodup_cons.mpr ⟨ha_nt, hnd_t⟩⟩⟩
          have hc := live_card htail
          have hlen_le : ws.length ≤ k := by
            rw [← huv_set, List.toFinset_card_of_nodup huv_nd] at hc
            simp only [List.length_cons] at hc
            omega
          exact Or.inr (Or.inr ⟨hlen_le, ih _ _ huv_nd (huv_set.symm ▸ htail)⟩)
        · have hreq : rest = (a :: tail).toFinset := by
            apply Finset.Subset.antisymm
            · intro x hx
              have hx' := hrest_sub hx
              simp only [List.toFinset_cons, Finset.mem_insert] at hx' ⊢
              rcases hx' with rfl | rfl | hx'
              · exact Or.inl rfl
              · exact False.elim (hbr hx)
              · exact Or.inr hx'
            · intro x hx
              simp only [List.toFinset_cons, Finset.mem_insert] at hx
              rcases hx with rfl | hx
              · exact har
              · exact htail_sub hx
          have ha_set : (z :: a :: tail).toFinset = insert z rest := by rw [hreq]; simp
          have ha_nd : (z :: a :: tail).Nodup :=
            List.nodup_cons.mpr ⟨fun hm => by
                rcases List.mem_cons.mp hm with heq | hm
                · exact hza heq
                · exact hz_nt hm,
              List.nodup_cons.mpr ⟨ha_nt, hnd_t⟩⟩
          have hc := live_card htail
          have hlen_le : ws.length ≤ k + 1 := by
            rw [← ha_set, List.toFinset_card_of_nodup ha_nd] at hc
            simp only [List.length_cons] at hc
            omega
          have hok := ih _ _ ha_nd (ha_set.symm ▸ htail)
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨hlen_le, Or.inl hok⟩)
          · exact Or.inr (Or.inl ⟨hlen_le, Or.inr hok⟩)
      · by_cases hbr : b ∈ rest
        · have hreq : rest = (b :: tail).toFinset := by
            apply Finset.Subset.antisymm
            · intro x hx
              have hx' := hrest_sub hx
              simp only [List.toFinset_cons, Finset.mem_insert] at hx' ⊢
              rcases hx' with rfl | rfl | hx'
              · exact False.elim (har hx)
              · exact Or.inl rfl
              · exact Or.inr hx'
            · intro x hx
              simp only [List.toFinset_cons, Finset.mem_insert] at hx
              rcases hx with rfl | hx
              · exact hbr
              · exact htail_sub hx
          have hb_set : (z :: b :: tail).toFinset = insert z rest := by rw [hreq]; simp
          have hb_nd : (z :: b :: tail).Nodup :=
            List.nodup_cons.mpr ⟨fun hm => by
                rcases List.mem_cons.mp hm with heq | hm
                · exact hzb heq
                · exact hz_nt hm,
              List.nodup_cons.mpr ⟨hb_nt, hnd_t⟩⟩
          have hc := live_card htail
          have hlen_le : ws.length ≤ k + 1 := by
            rw [← hb_set, List.toFinset_card_of_nodup hb_nd] at hc
            simp only [List.length_cons] at hc
            omega
          have hok := ih _ _ hb_nd (hb_set.symm ▸ htail)
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨hlen_le, Or.inr hok⟩)
          · exact Or.inr (Or.inl ⟨hlen_le, Or.inl hok⟩)
        · have hreq : rest = tail.toFinset := by
            apply Finset.Subset.antisymm
            · intro x hx
              have hx' := hrest_sub hx
              simp only [List.toFinset_cons, Finset.mem_insert] at hx'
              rcases hx' with rfl | rfl | hx'
              · exact False.elim (har hx)
              · exact False.elim (hbr hx)
              · exact hx'
            · exact htail_sub
          have ht_set : (z :: tail).toFinset = insert z rest := by rw [hreq]; simp
          have ht_nd : (z :: tail).Nodup := List.nodup_cons.mpr ⟨hz_nt, hnd_t⟩
          exact Or.inl (ih _ _ ht_nd (ht_set.symm ▸ htail))
    rcases hpair with hp | hp
    · refine ⟨(a, b, tail), hp, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨isAnd, by cases isAnd <;> simp, ?_⟩
      have hzn : stepOp isAnd a b ∉ ws := hz_nws
      simp only [hzn, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases hbranch a b (Or.inl ⟨rfl, rfl⟩) with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨h1, h2⟩
    · refine ⟨(b, a, tail), hp, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨isAnd, by cases isAnd <;> simp, ?_⟩
      have hzn : stepOp isAnd b a ∉ ws := by rw [stepOp_comm]; exact hz_nws
      simp only [hzn, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases hbranch b a (Or.inr ⟨rfl, rfl⟩) with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨h1, h2⟩

lemma live_init_eq {k : ℕ} {s : Finset W} {seen : Bool}
    (hsub : s ⊆ initSet) (h : Live k s seen) : s = initSet := by
  apply Finset.Subset.antisymm hsub
  have hmem : ∀ i : Fin 6, inVec i ∈ s := by
    have uniq (e m : Fin 5) (i0 : Fin 6)
        (hu : ∀ i : Fin 6, separates e m (inVec i) → i = i0) : inVec i0 ∈ s := by
      obtain ⟨w, hws, hsep⟩ := live_separates e m h
      have hwi := hsub hws
      simp only [initSet, initList, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hwi
      rcases hwi with rfl | rfl | rfl | rfl | rfl | rfl
      · rwa [← hu 0 hsep]
      · rwa [← hu 1 hsep]
      · rwa [← hu 2 hsep]
      · rwa [← hu 3 hsep]
      · rwa [← hu 4 hsep]
      · rwa [← hu 5 hsep]
    intro i
    fin_cases i
    · exact uniq 0 4 0 (by intro j; unfold separates; fin_cases j <;> decide)
    · exact uniq 2 4 1 (by intro j; unfold separates; fin_cases j <;> decide)
    · exact uniq 4 4 2 (by intro j; unfold separates; fin_cases j <;> decide)
    · exact uniq 0 0 3 (by intro j; unfold separates; fin_cases j <;> decide)
    · exact uniq 2 0 4 (by intro j; unfold separates; fin_cases j <;> decide)
    · exact uniq 4 0 5 (by intro j; unfold separates; fin_cases j <;> decide)
  intro w hw
  simp only [initSet, initList, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
    Finset.notMem_empty, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hmem 0
  · exact hmem 1
  · exact hmem 2
  · exact hmem 3
  · exact hmem 4
  · exact hmem 5

lemma initList_nodup : initList.Nodup := by decide

theorem reject_5 : search 5 initList true = false := by decide +kernel
theorem reject_6 : search 6 initList true = false := by decide +kernel
theorem reject_7 : search 7 initList false = false := by decide +kernel

lemma no_live_small {k : ℕ} (hk : k < 7) {s : Finset W} (hsub : s ⊆ initSet)
    (h : Live k s true) : False := by
  have heq := live_init_eq hsub h
  rw [heq] at h
  have hcard : 6 ≤ k + 1 := by
    have hc := live_card h
    have h6 : initSet.card = 6 := by decide
    omega
  have hk56 : k = 5 ∨ k = 6 := by omega
  rcases hk56 with rfl | rfl
  · have := search_complete 5 initList true initList_nodup h
    rw [reject_5] at this; exact Bool.false_ne_true this
  · have := search_complete 6 initList true initList_nodup h
    rw [reject_6] at this; exact Bool.false_ne_true this

lemma no_build_7_bad (h : Build 7 initSet false) : False := by
  rcases compress_strong h with ⟨s, hs, hlive⟩ | ⟨k', hk', s, hs, hlive⟩
  · have heq := live_init_eq hs hlive
    rw [heq] at hlive
    have := search_complete 7 initList false initList_nodup hlive
    rw [reject_7] at this; exact Bool.false_ne_true this
  · exact no_live_small hk' hs hlive

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def opIsAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def wireVec (C : Circuit) (w : ℕ) : W :=
  mkW fun r : Fin 13 => (C.wires (List.ofFn (rowData r))).getD w false

lemma wires_take_getD (gs : List Gate) (inp : List Bool) (j : ℕ) (w : ℕ) (hw : w < inp.length + j) :
    (gs.foldl evalStep inp).getD w false =
      ((gs.take j).foldl evalStep inp).getD w false := by
  have hlen : ∀ (l : List Gate) (acc : List Bool),
      (l.foldl evalStep acc).length = acc.length + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons g l ih => intro acc; rw [List.foldl_cons, ih]; simp [evalStep]; omega
  have hpref : ∀ (l : List Gate) (acc : List Bool) (w : ℕ), w < acc.length →
      (l.foldl evalStep acc).getD w false = acc.getD w false := by
    intro l
    induction l with
    | nil => intro acc w _; rfl
    | cons g l ih =>
      intro acc w hw
      rw [List.foldl_cons, ih _ w (by simp [evalStep]; omega)]
      simp only [evalStep]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_lhs => rw [hsplit, List.foldl_append]
  by_cases hj : j ≤ gs.length
  · apply hpref
    rw [hlen, List.length_take, Nat.min_eq_left hj]
    exact hw
  · have hdrop : gs.drop j = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [hdrop]; rfl

lemma wireVec_input (C : Circuit) (i : Fin 6) : wireVec C i.val = inVec i := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [wireVec, inVec, getLsbD_mkW _ r hr, getLsbD_mkW _ r hr]
  have h0 := wires_take_getD C.gates (List.ofFn (rowData ⟨r, hr⟩)) 0 i.val (by simp [i.isLt])
  change (C.gates.foldl evalStep (List.ofFn (rowData ⟨r, hr⟩))).getD i.val false = _
  rw [h0]
  simp [List.getD_eq_getElem?_getD, i.isLt]
  fin_cases i <;> rfl

lemma wireVec_gate (C : Circuit) (hAO2 : IsAO2 (3 + 3) C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b : ℕ, a < 6 + j ∧ b < 6 + j ∧
      wireVec C (6 + j) = stepOp (opIsAnd (NestedCover.gateAt C j).op) (wireVec C a) (wireVec C b) := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hgat : NestedCover.gateAt C j = C.gates[j] := by
    simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
  have hlen2 : (NestedCover.gateAt C j).inputs.length = 2 := by
    rw [hgat]; exact hAO2.2.2 _ hmem
  have hop : (NestedCover.gateAt C j).op = GateOp.and ∨ (NestedCover.gateAt C j).op = GateOp.or := by
    rw [hgat]
    have h1 := hAO2.1 _ hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  cases hins : (NestedCover.gateAt C j).inputs with
  | nil => simp [hins] at hlen2
  | cons a rest =>
    cases rest with
    | nil => simp [hins] at hlen2
    | cons b rest2 =>
      cases rest2 with
      | cons c cs => simp [hins] at hlen2
      | nil =>
        have ha : a < 6 + j := hAO2.2.1 j hj a (by simp [hins])
        have hb : b < 6 + j := hAO2.2.1 j hj b (by simp [hins])
        refine ⟨a, b, ha, hb, ?_⟩
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        rw [wireVec, getLsbD_mkW _ r hr]
        let inp := List.ofFn (rowData ⟨r, hr⟩)
        have hinp : inp.length = 6 := by simp [inp]
        have h1 := wires_take_getD C.gates inp (j + 1) (6 + j) (by omega)
        change (C.gates.foldl evalStep inp).getD (6 + j) false = _
        rw [h1, List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen_pre : ((C.gates.take j).foldl evalStep inp).length = 6 + j := by
          have hl : ∀ (l : List Gate) (acc : List Bool),
              (l.foldl evalStep acc).length = acc.length + l.length := by
            intro l; induction l with
            | nil => intro acc; simp
            | cons g l ih => intro acc; rw [List.foldl_cons, ih]; simp [evalStep]; omega
          rw [hl, hinp, List.length_take, Nat.min_eq_left (by omega)]
        simp only [evalStep]
        rw [List.getD_eq_getElem?_getD, ← hlen_pre, List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        have ha_eq : (C.wires inp).getD a false =
            ((C.gates.take j).foldl evalStep inp).getD a false :=
          wires_take_getD C.gates inp j a (by omega)
        have hb_eq : (C.wires inp).getD b false =
            ((C.gates.take j).foldl evalStep inp).getD b false :=
          wires_take_getD C.gates inp j b (by omega)
        have hgi : C.gates[j].inputs = [a, b] := by rw [← hgat, hins]
        rcases hop with hand | hor
        · have hg_op : C.gates[j].op = GateOp.and := by rw [← hgat, hand]
          simp only [hg_op, hgi, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true, hand, opIsAnd, stepOp,
            ↓reduceIte, BitVec.getLsbD_and, wireVec, getLsbD_mkW _ r hr]
          rw [ha_eq, hb_eq]
        · have hg_op : C.gates[j].op = GateOp.or := by rw [← hgat, hor]
          simp only [hg_op, hgi, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, hor, opIsAnd, stepOp,
            Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_or, wireVec, getLsbD_mkW _ r hr]
          rw [ha_eq, hb_eq]

lemma wireVec_build (C : Circuit) (hAO2 : IsAO2 (3 + 3) C)
    (jbad : ℕ) (hjbad : jbad < C.gates.length)
    (hand : (NestedCover.gateAt C jbad).op = GateOp.and)
    (hbad : isBad (wireVec C (6 + jbad)) = true)
    (hgoal : wireVec C C.output = goal)
    (hout : C.output < 6 + C.gates.length) :
    Build C.gates.length initSet false := by
  have hgen : ∀ d m, m + d = C.gates.length → ∀ seen : Bool,
      (jbad < m → seen = true) →
      Build d ((Finset.range (6 + m)).image (wireVec C)) seen := by
    intro d
    induction d with
    | zero =>
      intro m hmd seen hseen
      have hmeq : m = C.gates.length := by omega
      subst hmeq
      refine ⟨?_, hseen hjbad⟩
      rw [← hgoal]
      exact Finset.mem_image.mpr ⟨C.output, Finset.mem_range.mpr hout, rfl⟩
    | succ d ih =>
      intro m hmd seen hseen
      have hmlt : m < C.gates.length := by omega
      obtain ⟨a, b, ha, hb, hvec⟩ := wireVec_gate C hAO2 m hmlt
      let isAnd := opIsAnd (NestedCover.gateAt C m).op
      refine Or.inr ⟨wireVec C a, Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩,
        wireVec C b, Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hb, rfl⟩, isAnd, ?_⟩
      have hins : insert (stepOp isAnd (wireVec C a) (wireVec C b))
          ((Finset.range (6 + m)).image (wireVec C)) =
          (Finset.range (6 + (m + 1))).image (wireVec C) := by
        rw [← hvec]
        have : 6 + (m + 1) = (6 + m) + 1 := by omega
        rw [this, Finset.range_add_one, Finset.image_insert]
      rw [hins]
      apply ih (m + 1) (by omega)
      intro hjlt
      by_cases hjm : jbad < m
      · simp [hseen hjm]
      · have hjeq : jbad = m := by omega
        subst hjeq
        have hia : isAnd = true := by simp [isAnd, hand, opIsAnd]
        have hbd : isBad (stepOp isAnd (wireVec C a) (wireVec C b)) = true := by
          rw [← hvec]; exact hbad
        rw [hia] at hbd
        simp [hia, hbd]
  have h0 := hgen C.gates.length 0 (by omega) false (by omega)
  have hinit : (Finset.range (6 + 0)).image (wireVec C) = initSet := by
    ext w
    simp only [Finset.mem_image, Finset.mem_range, initSet, initList, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi6 : i < 6 := by omega
      have hv := wireVec_input C ⟨i, hi6⟩
      interval_cases i <;> simp_all
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, by omega, wireVec_input C 0⟩
      · exact ⟨1, by omega, wireVec_input C 1⟩
      · exact ⟨2, by omega, wireVec_input C 2⟩
      · exact ⟨3, by omega, wireVec_input C 3⟩
      · exact ⟨4, by omega, wireVec_input C 4⟩
      · exact ⟨5, by omega, wireVec_input C 5⟩
  simpa [hinit] using h0

lemma build_mono_k {k1 k2 : ℕ} (hk : k1 ≤ k2) {s : Finset W} {seen : Bool}
    (h : Build k1 s seen) : Build k2 s seen := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

lemma rowData_p6 (r : Fin 13) :
    (decide (∃ p l : Fin 3, (p.val, l.val) ∈ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)] ∧
      rowData r (Fin.castAdd 3 p) = true ∧ rowData r (Fin.natAdd 3 l) = true)) =
      goal.getLsbD r.val := by
  fin_cases r <;> decide

lemma nonedge_row (p0 l0 : Fin 3)
    (hne : (p0.val, l0.val) ∉ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)]) :
    ∃ r : Fin 13, (r.val = 6 ∨ r.val = 10 ∨ r.val = 11 ∨ r.val = 12) ∧
      rowData r = fun k : Fin (3 + 3) => decide (k = Fin.castAdd 3 p0 ∨ k = Fin.natAdd 3 l0) := by
  fin_cases p0 <;> fin_cases l0
  · simp at hne
  · exact ⟨10, by decide, by funext k; fin_cases k <;> decide⟩
  · exact ⟨11, by decide, by funext k; fin_cases k <;> decide⟩
  · simp at hne
  · simp at hne
  · exact ⟨12, by decide, by funext k; fin_cases k <;> decide⟩
  · exact ⟨6, by decide, by funext k; fin_cases k <;> decide⟩
  · simp at hne
  · simp at hne

theorem main_proof :
    ¬ (∃ C : Circuit, IsAO2 (3 + 3) C ∧ C.size ≤ 7 ∧
      (∀ z : Fin (3 + 3) → Bool, circuitFun (3 + 3) C z = true ↔
        ∃ p l : Fin 3, (p.val, l.val) ∈ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)] ∧
          z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) ∧
      ∃ j < C.gates.length, PEqualNP.Core.InOutputCone (3 + 3) C j ∧
        (NestedCover.gateAt C j).op = GateOp.and ∧
        ∃ p0 l0 : Fin 3, (p0.val, l0.val) ∉ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)] ∧
          (C.wires (List.ofFn (fun k : Fin (3 + 3) => decide (k = Fin.castAdd 3 p0 ∨ k = Fin.natAdd 3 l0)))).getD (3 + 3 + j) false = true) := by
  rintro ⟨C, hAO2, hsz, hfun, j, hj, _, hand, p0, l0, hne, hbadw⟩
  have hgoal : wireVec C C.output = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [wireVec, getLsbD_mkW _ r hr]
    have hf := hfun (rowData ⟨r, hr⟩)
    have hrp := rowData_p6 ⟨r, hr⟩
    apply Bool.eq_iff_iff.mpr
    rw [← hrp, decide_eq_true_eq]
    exact hf
  have hout : C.output < 6 + C.gates.length := by
    by_contra hge
    have h0 : (C.wires (List.ofFn (rowData 0))).getD C.output false = false := by
      have hl : (C.wires (List.ofFn (rowData 0))).length = 6 + C.gates.length := by
        have hlen : ∀ (l : List Gate) (acc : List Bool),
            (l.foldl evalStep acc).length = acc.length + l.length := by
          intro l; induction l with
          | nil => intro acc; simp
          | cons g l ih => intro acc; rw [List.foldl_cons, ih]; simp [evalStep]; omega
        change (C.gates.foldl evalStep (List.ofFn (rowData 0))).length = _
        rw [hlen]; simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have ht : (C.wires (List.ofFn (rowData 0))).getD C.output false = true :=
      (hfun (rowData 0)).mpr ⟨0, 0, by simp, by decide, by decide⟩
    rw [h0] at ht; exact Bool.false_ne_true ht
  obtain ⟨r, hr_idx, hrow⟩ := nonedge_row p0 l0 hne
  have hbad : isBad (wireVec C (6 + j)) = true := by
    have hbit : (wireVec C (6 + j)).getLsbD r.val = true := by
      rw [wireVec, getLsbD_mkW _ r.val r.isLt, hrow]
      exact hbadw
    rcases hr_idx with h6 | h10 | h11 | h12
    · simp [isBad, h6 ▸ hbit]
    · simp [isBad, h10 ▸ hbit]
    · simp [isBad, h11 ▸ hbit]
    · simp [isBad, h12 ▸ hbit]
  have hb := wireVec_build C hAO2 j hj hand hbad hgoal hout
  exact no_build_7_bad (build_mono_k hsz hb)

end PEqualNP.Outside.L_meta_3713

theorem PEqualNP.Outside.L_meta_3713 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (3 + 3) C ∧ C.size ≤ 7 ∧ (∀ z : Fin (3 + 3) → Bool, PEqualNP.MetaComplexity.circuitFun (3 + 3) C z = true ↔ ∃ p l : Fin 3, (p.val, l.val) ∈ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)] ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) ∧ ∃ j < C.gates.length, PEqualNP.Core.InOutputCone (3 + 3) C j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ p0 l0 : Fin 3, (p0.val, l0.val) ∉ [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)] ∧ (C.wires (List.ofFn (fun k : Fin (3 + 3) => decide (k = Fin.castAdd 3 p0 ∨ k = Fin.natAdd 3 l0)))).getD (3 + 3 + j) false = true) :=
  PEqualNP.Outside.L_meta_3713.main_proof
