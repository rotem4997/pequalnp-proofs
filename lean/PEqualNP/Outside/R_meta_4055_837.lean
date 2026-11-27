import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_4055_837
    (normalize : ∀ (n : ℕ) (R : List (Finset ℕ × Finset ℕ)),
      let E := fun (S : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) (out : Finset ℕ) =>
        let w := S.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
          decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
        decide (∀ i ∈ out, w.getD i false = true)
      (∀ j (hj : j < R.length), ∀ i ∈ R[j].1 ∪ R[j].2, i < n+1+j) →
      ∃ S : List (Finset ℕ × Finset ℕ), S.length = R.length ∧
        (∀ j (hj : j < S.length), ∀ i ∈ S[j].1 ∪ S[j].2, i < n+1+j) ∧
        (∀ r ∈ S, (r.1.filter (fun i => i < n)).card ≤ 2 ∧ (r.2.filter (fun i => i < n)).card ≤ 2) ∧
        ∀ (x : Fin n → Bool) (out : Finset ℕ),
          ((let support : Finset (Fin n) := Finset.univ.filter fun i : Fin n => x i = true
            support.card ≤ 2) → E S x out = E R x out) ∧
          (E S x out = true → E R x out = true))
    (bound : ∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (∀ r ∈ x1, (r.1.filter (fun i => i < 42)).card ≤ 2 ∧ (r.2.filter (fun i => i < 42)).card ≤ 2) → (104 : ℕ) ≤ x1.length) :
∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (104 : ℕ) ≤ x1.length := by
  let ev (w : List Bool) (A : Finset ℕ) : Bool := decide (∀ i ∈ A, w.getD i false = true)
  let nw (n : ℕ) (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) : List Bool :=
    R.foldl (fun w r => w ++ [ev w r.1 || ev w r.2]) (List.ofFn x ++ [false])
  let raw (n : ℕ) (A : Finset ℕ) : Finset ℕ := A.filter (· < n)
  let clean (n : ℕ) (A : Finset ℕ) : Finset ℕ := if (raw n A).card ≤ 2 then A else {n}
  let cleanRows (n : ℕ) (R : List (Finset ℕ × Finset ℕ)) :=
    R.map (fun r => (clean n r.1, clean n r.2))
  let leW (a b : List Bool) : Prop := a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

  have getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    rcases lt_trichotomy i w.length with hi | hi | hi
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, hi.ne]
    · subst hi; simp [List.getD_eq_getElem?_getD]
    · have h1 : w.length ≤ i := by omega
      have h2 : (w ++ [b]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2, hi.ne']

  have nw_length {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :
      (nw n R x).length = n + 1 + R.length := by
    induction R using List.reverseRecOn with
    | nil => simp [nw]
    | append_singleton R a ih => simp only [nw, List.foldl_append, List.foldl_cons, List.foldl_nil] at *; simp [ih]; omega

  have nw_snoc {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (a : Finset ℕ × Finset ℕ) (x : Fin n → Bool) :
      nw n (R ++ [a]) x = nw n R x ++ [ev (nw n R x) a.1 || ev (nw n R x) a.2] := by
    simp [nw, List.foldl_append]

  have nw_input {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) (i : ℕ) (hi : i ≤ n) :
      (nw n R x).getD i false = (List.ofFn x ++ [false]).getD i false := by
    induction R using List.reverseRecOn with
    | nil => rfl
    | append_singleton R a ih => rw [nw_snoc, getD_snoc, if_neg (by rw [nw_length]; omega), ih]

  have nw_false {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :
      (nw n R x).getD n false = false := by
    rw [nw_input R x n le_rfl]
    simp [List.getD_eq_getElem?_getD]

  have nw_var {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) (i : Fin n) :
      (nw n R x).getD i.val false = x i := by
    rw [nw_input R x i.val (Nat.le_of_lt i.isLt)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (show i.val < (List.ofFn x).length by simpa using i.isLt)]
    simp [i.isLt]

  have clean_small (n : ℕ) (A : Finset ℕ) : (raw n (clean n A)).card ≤ 2 := by
    unfold clean
    split_ifs with h
    · exact h
    · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

  have ev_mono {a b : List Bool} (h : leW a b) (A : Finset ℕ) : ev a A = true → ev b A = true := by
    simp only [ev, decide_eq_true_eq]
    exact fun ha i hi => h.2 i (ha i hi)

  have clean_below {n : ℕ} {a b : List Bool} (hab : leW a b) (ha : a.getD n false = false) (A : Finset ℕ) :
      ev a (clean n A) = true → ev b A = true := by
    unfold clean
    split_ifs with h
    · exact ev_mono hab A
    · intro h
      have hh := (of_decide_eq_true h) n (Finset.mem_singleton_self n)
      rw [ha] at hh
      contradiction

  have leW_snoc {a b : List Bool} {u v : Bool} (h : leW a b) (huv : u = true → v = true) :
      leW (a ++ [u]) (b ++ [v]) := by
    refine ⟨by simp [h.1], fun i hi => ?_⟩
    rw [getD_snoc] at hi ⊢
    rw [← h.1]
    split_ifs at hi ⊢ with heq
    · exact huv hi
    · exact h.2 i hi

  have rows_below {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :
      leW (nw n (cleanRows n R) x) (nw n R x) := by
    induction R using List.reverseRecOn with
    | nil => exact ⟨rfl, fun _ h => h⟩
    | append_singleton R a ih =>
      rw [show cleanRows n (R ++ [a]) = cleanRows n R ++ [(clean n a.1, clean n a.2)] by simp [cleanRows]]
      rw [nw_snoc, nw_snoc]
      apply leW_snoc ih
      intro h
      simp only [Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (clean_below ih (nw_false _ _) _ h)
      · exact Or.inr (clean_below ih (nw_false _ _) _ h)

  have bad_operand_off {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool)
      (hx : (Finset.univ.filter fun i : Fin n => x i = true).card ≤ 2) (A : Finset ℕ)
      (hbad : ¬ (raw n A).card ≤ 2) : ev (nw n R x) A = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hA := of_decide_eq_true h
    let S := (Finset.univ.filter fun i : Fin n => x i = true).image Fin.val
    have hsub : raw n A ⊆ S := by
      intro i hi
      obtain ⟨hiA, hin⟩ := Finset.mem_filter.mp hi
      have hit := hA i hiA
      rw [nw_var R x ⟨i, hin⟩] at hit
      exact Finset.mem_image.mpr ⟨⟨i, hin⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩
    have hcard : S.card ≤ 2 := (Finset.card_image_le).trans hx
    exact hbad ((Finset.card_le_card hsub).trans hcard)

  have clean_on_small {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool)
      (hx : (Finset.univ.filter fun i : Fin n => x i = true).card ≤ 2) (A : Finset ℕ) :
      ev (nw n R x) (clean n A) = ev (nw n R x) A := by
    unfold clean
    split_ifs with h
    · rfl
    · rw [bad_operand_off R x hx A h]
      apply Bool.eq_false_iff.mpr
      intro hon
      have hh := (of_decide_eq_true hon) n (Finset.mem_singleton_self n)
      rw [nw_false] at hh
      contradiction

  have rows_on_small {n : ℕ} (R : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool)
      (hx : (Finset.univ.filter fun i : Fin n => x i = true).card ≤ 2) :
      nw n (cleanRows n R) x = nw n R x := by
    induction R using List.reverseRecOn with
    | nil => rfl
    | append_singleton R a ih =>
      rw [show cleanRows n (R ++ [a]) = cleanRows n R ++ [(clean n a.1, clean n a.2)] by simp [cleanRows]]
      rw [nw_snoc, nw_snoc, ih, clean_on_small R x hx, clean_on_small R x hx]

  have clean_refs {n k : ℕ} (A : Finset ℕ) (hA : ∀ i ∈ A, i < n + 1 + k) :
      ∀ i ∈ clean n A, i < n + 1 + k := by
    unfold clean
    split_ifs with h
    · exact hA
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      omega

  have rows_refs {n : ℕ} (R : List (Finset ℕ × Finset ℕ))
      (hR : ∀ j (hj : j < R.length), ∀ i ∈ R[j].1 ∪ R[j].2, i < n + 1 + j) :
      ∀ j (hj : j < (cleanRows n R).length),
        ∀ i ∈ (cleanRows n R)[j].1 ∪ (cleanRows n R)[j].2, i < n + 1 + j := by
    intro j hj i hi
    have hjR : j < R.length := by simpa [cleanRows] using hj
    have hget : (cleanRows n R)[j] = (clean n R[j].1, clean n R[j].2) := by simp [cleanRows]
    rw [hget] at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact clean_refs R[j].1 (fun t ht => hR j hjR t (Finset.mem_union_left _ ht)) i hi
    · exact clean_refs R[j].2 (fun t ht => hR j hjR t (Finset.mem_union_right _ ht)) i hi

  have rows_raw_small (n : ℕ) (R : List (Finset ℕ × Finset ℕ)) :
      ∀ r ∈ cleanRows n R, (raw n r.1).card ≤ 2 ∧ (raw n r.2).card ≤ 2 := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact ⟨clean_small n s.1, clean_small n s.2⟩

  have normalizer (n : ℕ) (R : List (Finset ℕ × Finset ℕ))
      (hR : ∀ j (hj : j < R.length), ∀ i ∈ R[j].1 ∪ R[j].2, i < n + 1 + j) :
      ∃ S : List (Finset ℕ × Finset ℕ), S.length = R.length ∧
        (∀ j (hj : j < S.length), ∀ i ∈ S[j].1 ∪ S[j].2, i < n + 1 + j) ∧
        (∀ r ∈ S, (raw n r.1).card ≤ 2 ∧ (raw n r.2).card ≤ 2) ∧
        ∀ (x : Fin n → Bool) (out : Finset ℕ),
          ((Finset.univ.filter fun i : Fin n => x i = true).card ≤ 2 →
            ev (nw n S x) out = ev (nw n R x) out) ∧
          (ev (nw n S x) out = true → ev (nw n R x) out = true) := by
    refine ⟨cleanRows n R, by simp [cleanRows], rows_refs R hR, rows_raw_small n R, ?_⟩
    intro x out
    exact ⟨fun hx => congrArg (fun w => ev w out) (rows_on_small R x hx), ev_mono (rows_below R x) out⟩
  intro R out
  dsimp only
  intro refs outRefs positive negative
  obtain ⟨S, hlen, hRefs, hsmall, htest⟩ := normalizer 42 R refs
  have hbound : 104 ≤ S.length := by
    apply bound S out hRefs
    · simpa only [hlen] using outRefs
    · intro p l hpl
      have hcard : (Finset.univ.filter fun i : Fin 42 =>
          decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l) = true).card ≤ 2 := by
        have hsub : (Finset.univ.filter fun i : Fin 42 =>
            decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l) = true) ⊆
            {Fin.castAdd 21 p, Fin.natAdd 21 l} := by
          intro i hi
          simpa only [Finset.mem_insert, Finset.mem_singleton] using
            of_decide_eq_true (Finset.mem_filter.mp hi).2
        have hpair := Finset.card_insert_le (Fin.castAdd 21 p) ({Fin.natAdd 21 l} : Finset (Fin 42))
        exact (Finset.card_le_card hsub).trans (by simpa using hpair)
      exact ((htest (fun i => decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)) out).1 hcard).trans (positive p l hpl)
    · intro x hx hmax
      apply Bool.eq_false_iff.mpr
      intro hy
      have old := (htest x out).2 hy
      exact Bool.false_ne_true ((negative x hx hmax).symm.trans old)
    · exact hsmall
  simpa only [hlen] using hbound
