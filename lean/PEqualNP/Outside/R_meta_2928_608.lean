import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2928_608
    (rename_eval : ∀ (rho : ℕ → ℕ) (C : Circuit) (xs ys : List Bool),
      xs.length = ys.length →
      (∀ i, xs.length ≤ i → rho i = i) →
      (∀ i, i < xs.length → rho i < xs.length ∨ xs.length + C.size ≤ rho i) →
      (∀ i, ys.getD (rho i) false = xs.getD i false) →
      (⟨C.gates.map (fun g => ⟨g.op, g.inputs.map rho⟩), rho C.output⟩ : Circuit).eval ys = C.eval xs)
    (core : ∀ (a b : Fin 11) (C : Circuit),
      11 * a.val + b.val ∈ ([1, 2, 3, 4, 6, 9, 13, 14, 15, 16, 17, 18, 19, 20,
        25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 53, 73, 75] : List ℕ) →
      FanInTwo C → C.size ≤ 13 →
      ∃ k : BitVec 9,
        let x : Fin 9 → Bool := fun i => k.getLsbD i.val
        let u := List.ofFn x ++ [!x 0]
        C.eval (u ++ [u.getD a.val false || u.getD b.val false]) ≠
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
            (5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  intro a b C hab hfan hsize
  let es : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let target (k : BitVec 9) := es.any (fun e => k.getLsbD e.1.val && k.getLsbD e.2.val)
  let feed (k : BitVec 9) := List.ofFn (fun i : Fin 9 => k.getLsbD i.val) ++ [!k.getLsbD 0]
  let inputs (u v : Fin 11) (k : BitVec 9) :=
    feed k ++ [(feed k).getD u.val false || (feed k).getD v.val false]
  let reps : List ℕ := [1, 2, 3, 4, 6, 9, 13, 14, 15, 16, 17, 18, 19, 20,
    25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 53, 73, 75]
  change ∃ k : BitVec 9, C.eval (inputs a b k) ≠ target k
  have feed_len (k : BitVec 9) : (feed k).length = 10 := by simp [feed]
  have inputs_len (u v : Fin 11) (k : BitVec 9) : (inputs u v k).length = 11 := by
    simp [inputs, feed_len]
  have read_low (u v : Fin 11) (k : BitVec 9) (i : ℕ) (hi : i < 10) :
      (inputs u v k).getD i false = (feed k).getD i false :=
    List.getD_append _ _ _ _ (by simpa only [feed_len] using hi)
  have read_last (u v : Fin 11) (k : BitVec 9) :
      (inputs u v k).getD 10 false =
        ((feed k).getD u.val false || (feed k).getD v.val false) := by
    unfold inputs
    rw [List.getD_append_right _ _ _ _ (by rw [feed_len]), feed_len]
    rfl
  have read_high (u v : Fin 11) (k : BitVec 9) (i : ℕ) (hi : 11 ≤ i) :
      (inputs u v k).getD i false = false :=
    List.getD_eq_default _ _ (by simpa only [inputs_len] using hi)
  have missing (k : BitVec 9) : (feed k).getD 10 false = false :=
    List.getD_eq_default _ _ (by rw [feed_len])
  let mapped (rho : ℕ → ℕ) : Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map rho⟩), rho C.output⟩
  have mapped_fan (rho : ℕ → ℕ) : FanInTwo (mapped rho) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g' hg').1, by simpa using (hfan g' hg').2⟩
  have mapped_size (rho : ℕ → ℕ) : (mapped rho).size ≤ 13 := by
    change (C.gates.map (fun g => (⟨g.op, g.inputs.map rho⟩ : Gate))).length ≤ 13
    rw [List.length_map]
    exact hsize
  have eval_transport (rho : ℕ → ℕ) (u v : Fin 11) (k' k : BitVec 9)
      (hfixed : ∀ i, 11 ≤ i → rho i = i)
      (hsafe : ∀ i, i < 11 → rho i < 11 ∨ 11 + C.size ≤ rho i)
      (hinputs : ∀ i, (inputs u v k).getD (rho i) false = (inputs a b k').getD i false)
      (htarget : target k' = target k)
      (hne : (mapped rho).eval (inputs u v k) ≠ target k) :
      C.eval (inputs a b k') ≠ target k' := by
    have he := rename_eval rho C (inputs a b k') (inputs u v k)
      (by simp only [inputs_len]) (by simpa only [inputs_len] using hfixed)
      (by simpa only [inputs_len] using hsafe) hinputs
    change (mapped rho).eval (inputs u v k) = C.eval (inputs a b k') at he
    rwa [he, ← htarget] at hne
  by_cases ha : a.val < 10
  · by_cases hb : b.val < 10
    · by_cases heq : a = b
      · subst b
        let rho (i : ℕ) := if i = 10 then a.val else i
        obtain ⟨k, hk⟩ := core 0 1 (mapped rho) (by decide) (mapped_fan rho) (mapped_size rho)
        refine ⟨k, eval_transport rho 0 1 k k ?_ ?_ ?_ rfl hk⟩
        · intro i hi; simp [rho, show i ≠ 10 by omega]
        · intro i hi; by_cases h : i = 10 <;> simp [rho, h] <;> omega
        · intro i
          by_cases h : i = 10
          · subst i
            simp only [rho, ite_eq_left rfl, read_low _ _ _ _ ha, read_last, Bool.or_self]
          · simp only [rho, ite_eq_right h]
            by_cases hi : i < 10
            · rw [read_low _ _ _ _ hi, read_low _ _ _ _ hi]
            · have hhi : 11 ≤ i := by omega
              rw [read_high _ _ _ _ hhi, read_high _ _ _ _ hhi]
      · let sigma : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
        let tau (i : Fin 11) : Fin 11 :=
          if hi : i.val < 9 then Fin.castLE (by decide) (sigma ⟨i.val, hi⟩) else i
        have horbit : ∀ a b : Fin 11, a < b → b.val < 10 →
            11 * a.val + b.val ∈ reps ∨
              11 * (min (tau a) (tau b)).val + (max (tau a) (tau b)).val ∈ reps := by
          intro u v
          fin_cases u <;> fin_cases v <;> decide
        have hlt : a < b := lt_of_le_of_ne hab heq
        rcases horbit a b hlt hb with hrep | hrep
        · exact core a b C hrep hfan hsize
        · let u := min (tau a) (tau b)
          let v := max (tau a) (tau b)
          let rho (i : ℕ) := if hi : i < 11 then (tau ⟨i, hi⟩).val else i
          let flip (k : BitVec 9) : BitVec 9 :=
            BitVec.ofBoolListLE ([0,5,8,3,4,1,7,6,2].map k.getLsbD)
          have flip_bits (k : BitVec 9) (i : Fin 9) :
              (flip k).getLsbD i.val = k.getLsbD (sigma i).val := by
            dsimp only [flip]
            rw [BitVec.getLsbD_ofBoolListLE]
            fin_cases i <;> rfl
          have feed_bit (k : BitVec 9) (j : Fin 9) :
              (feed k).getD j.val false = k.getLsbD j.val := by
            unfold feed
            rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt)]
            rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
              List.getElem_ofFn]
          have feed_complement (k : BitVec 9) :
              (feed k).getD 9 false = !k.getLsbD 0 := by
            unfold feed
            rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
            rfl
          have flip_feed (k : BitVec 9) (i : Fin 11) :
              (feed (flip k)).getD i.val false = (feed k).getD (tau i).val false := by
            by_cases hi : i.val < 9
            · change (feed (flip k)).getD (⟨i.val,hi⟩ : Fin 9).val false = _
              rw [feed_bit, flip_bits]
              simp only [tau, dite_eq_left hi, Fin.val_castLE, feed_bit]
            · have hj : i = 9 ∨ i = 10 := by
                have hi' := i.isLt
                by_cases h : i.val = 9
                · exact Or.inl (Fin.ext h)
                · exact Or.inr (Fin.ext (by change i.val = 10; omega))
              rcases hj with rfl | rfl
              · change (feed (flip k)).getD 9 false = (feed k).getD 9 false
                rw [feed_complement, feed_complement]
                exact congrArg Bool.not (flip_bits k 0)
              · change (feed (flip k)).getD 10 false = (feed k).getD 10 false
                rw [missing, missing]
          have inv_edges (i j : Fin 9) :
              (sigma i, sigma j) ∈ es ∨ (sigma j, sigma i) ∈ es ↔
                (i,j) ∈ es ∨ (j,i) ∈ es := by
            fin_cases i <;> fin_cases j <;> decide
          have invol (i : Fin 9) : sigma (sigma i) = i := by revert i; decide
          have inv_target (k : BitVec 9) : target (flip k) = target k := by
            apply Bool.eq_iff_iff.mpr
            simp only [target, List.any_eq_true, Bool.and_eq_true, flip_bits]
            constructor
            · rintro ⟨⟨i,j⟩,he,hi,hj⟩
              rcases (inv_edges i j).mpr (Or.inl he) with h | h
              · exact ⟨(sigma i, sigma j),h,hi,hj⟩
              · exact ⟨(sigma j, sigma i),h,hj,hi⟩
            · rintro ⟨⟨i,j⟩,he,hi,hj⟩
              rcases (inv_edges (sigma i) (sigma j)).mp (by simpa only [invol] using (Or.inl he :
                (i,j) ∈ es ∨ (j,i) ∈ es)) with h | h
              · exact ⟨(sigma i, sigma j),h,by simpa only [invol] using hi,by simpa only [invol] using hj⟩
              · exact ⟨(sigma j, sigma i),h,by simpa only [invol] using hj,by simpa only [invol] using hi⟩
          obtain ⟨k,hk⟩ := core u v (mapped rho) hrep (mapped_fan rho) (mapped_size rho)
          refine ⟨flip k, eval_transport rho u v (flip k) k ?_ ?_ ?_ (inv_target k) hk⟩
          · intro i hi; simp [rho, show ¬ i < 11 by omega]
          · intro i hi; exact Or.inl (by simpa only [rho, dite_eq_left hi] using (tau ⟨i,hi⟩).isLt)
          · intro i
            by_cases hi : i < 10
            · have hr : rho i = (tau ⟨i, by omega⟩).val := by
                simp [rho, show i < 11 by omega]
              have htr : (tau ⟨i, by omega⟩).val < 10 := by
                unfold tau
                split <;> first | exact (sigma _).isLt.trans (by decide) | exact hi
              rw [hr, read_low _ _ _ _ hi, read_low _ _ _ _ htr]
              exact (flip_feed k ⟨i, by omega⟩).symm
            · by_cases hj : i = 10
              · subst i
                have h10 : rho 10 = 10 := rfl
                rw [h10, read_last, read_last, flip_feed k a, flip_feed k b]
                dsimp [u, v]
                rcases le_total (tau a).val (tau b).val with h | h
                · rw [min_eq_left h, max_eq_right h]
                · rw [min_eq_right h, max_eq_left h, Bool.or_comm]
              · have hh : 11 ≤ i := by omega
                simp only [rho, dite_eq_right (show ¬ i < 11 by omega), read_high _ _ _ _ hh]
    · have hb10 : b.val = 10 := by omega
      let rho (i : ℕ) := if i = 10 then a.val else i
      obtain ⟨k,hk⟩ := core 0 1 (mapped rho) (by decide) (mapped_fan rho) (mapped_size rho)
      refine ⟨k, eval_transport rho 0 1 k k ?_ ?_ ?_ rfl hk⟩
      · intro i hi; simp [rho, show i ≠ 10 by omega]
      · intro i hi; by_cases h : i = 10 <;> simp [rho,h] <;> omega
      · intro i
        by_cases h : i = 10
        · subst i
          simp only [rho, ite_eq_left rfl, read_low _ _ _ _ ha, read_last, hb10, missing, Bool.or_false]
        · simp only [rho, ite_eq_right h]
          by_cases hi : i < 10
          · rw [read_low _ _ _ _ hi, read_low _ _ _ _ hi]
          · have hh : 11 ≤ i := by omega
            rw [read_high _ _ _ _ hh, read_high _ _ _ _ hh]
  · have ha10 : a.val = 10 := by omega
    have hb10 : b.val = 10 := by
      have h : a.val ≤ b.val := hab
      omega
    let rho (i : ℕ) := if i = 10 then 24 else i
    obtain ⟨k,hk⟩ := core 0 1 (mapped rho) (by decide) (mapped_fan rho) (mapped_size rho)
    refine ⟨k, eval_transport rho 0 1 k k ?_ ?_ ?_ rfl hk⟩
    · intro i hi; simp [rho, show i ≠ 10 by omega]
    · intro i hi; by_cases h : i = 10 <;> simp [rho,h] <;> omega
    · intro i
      by_cases h : i = 10
      · subst i
        simp only [rho, ite_eq_left rfl, read_high _ _ _ _ (by decide : 11 ≤ 24), read_last,
          ha10, hb10, missing, Bool.or_false]
      · simp only [rho, ite_eq_right h]
        by_cases hi : i < 10
        · rw [read_low _ _ _ _ hi, read_low _ _ _ _ hi]
        · have hh : 11 ≤ i := by omega
          rw [read_high _ _ _ _ hh, read_high _ _ _ _ hh]
