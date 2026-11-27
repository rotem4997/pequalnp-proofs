import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds
-- The 21 edge inputs and 37 maximal independent inputs determine every monotone output.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3324_471
    (separate : ∃ C : Circuit, PEqualNP.TopForm.IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      2 ≤ C.size ∧ C.size ≤ 26 ∧ ∀ y : Bool, ∀ r ∈ (if y then [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112] else [127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = y)
    (cover : ∀ (x : Fin 14 → Bool), ∃ y : Bool, ∃ r ∈ (if y then [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112] else [127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ),
      ∀ i : Fin 14, if y then r.testBit i.val = true → x i = true else x i = true → r.testBit i.val = true) : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ (2 : ℕ) ≤ x2.size ∧ x2.size ≤ (26 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Decidable.decide (∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ x1 ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) := by
  let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let pos : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112]
  let neg : List ℕ := [127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
  let encode (e : ℕ × ℕ) := 2^e.1 ||| 2^e.2
  have enc : E.map encode = pos := by rfl
  have bounds : ∀ e ∈ E, e.1 < 14 ∧ e.2 < 14 := by
    have h : E.all (fun e => decide (e.1 < 14 ∧ e.2 < 14)) = true := by decide
    simpa using List.all_eq_true.mp h
  have safe (r : ℕ) (hr : r ∈ neg) (e : ℕ × ℕ) (he : e ∈ E) :
      (r.testBit e.1 && r.testBit e.2) = false := by
    have h : neg.all (fun r => E.all (fun e => !(r.testBit e.1 && r.testBit e.2))) = true := by decide +kernel
    have v := List.all_eq_true.mp (List.all_eq_true.mp h r hr) e he
    change (!(r.testBit e.1 && r.testBit e.2)) = true at v
    simpa only [Bool.not_eq_true'] using v
  have andEq (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have orEq (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evaluation (D : Circuit) (hm : PEqualNP.EdgeOwnership.AndOrOnly D) (u v : Fin 14 → Bool)
      (le : ∀ i, u i = true → v i = true) :
      D.eval (List.ofFn u) = true → D.eval (List.ofFn v) = true := by
    let Le (x y : List Bool) := ∀ j, x.getD j false = true → y.getD j false = true
    have snoc (xs : List Bool) (v : Bool) : (xs ++ [v]).getD xs.length false = v := by simp
    have stepLe (g : Gate) (hop : g.op = .and ∨ g.op = .or) (x y : List Bool) (hl : x.length = y.length) (h : Le x y) :
        Le (step x g) (step y g) := by
      intro j hj
      by_cases hlt : j < x.length
      · unfold step at hj ⊢
        rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h j hj
      by_cases he : j = x.length
      · have hy : j = y.length := he.trans hl
        simp only [step,he,snoc] at hj
        simp only [step,hy,snoc]
        rcases hop with ho | ho <;> rw [ho] at hj ⊢ <;> simp [andEq,orEq] at hj ⊢
        · exact fun i hi => h i (hj i hi)
        · obtain ⟨i,hi,hv⟩ := hj
          exact ⟨i,hi,h i hv⟩
      · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hj
        exact Bool.noConfusion hj
    have foldLe (gs : List Gate) (good : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        ∀ x y : List Bool, x.length = y.length → Le x y → Le (gs.foldl step x) (gs.foldl step y) := by
      induction gs with
      | nil => exact fun _ _ _ h => h
      | cons g gs ih =>
        intro x y hl h
        exact ih (fun t ht => good t (by simp [ht])) _ _ (by simp [step,hl]) (stepLe _ (good _ (by simp)) _ _ hl h)
    apply foldLe D.gates hm _ _ (by simp) _ D.output
    intro j h
    by_cases hj : j < 14
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp;omega)] at h
      exact Bool.noConfusion h
  obtain ⟨C,hC,hn,hl,hu,rows⟩ := separate
  refine ⟨C,hC,hn,hl,hu,?_⟩
  intro x
  change C.eval (List.ofFn x) = decide (∃ a b : Fin 14, (a.val,b.val) ∈ E ∧ x a = true ∧ x b = true)
  obtain ⟨y,r,hr,sub⟩ := cover x
  cases y with
  | true =>
    change r ∈ pos at hr
    change ∀ i : Fin 14, r.testBit i.val = true → x i = true at sub
    have out := evaluation C hC.1 _ x sub (rows true r hr)
    rw [out,eq_comm,decide_eq_true_eq]
    rw [← enc] at hr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha,hb⟩ := bounds e he
    refine ⟨⟨e.1,ha⟩,⟨e.2,hb⟩,he,sub _ ?_,sub _ ?_⟩ <;>
      simp [encode,Nat.testBit_two_pow]
  | false =>
    change r ∈ neg at hr
    change ∀ i : Fin 14, x i = true → r.testBit i.val = true at sub
    have onn := rows false r hr
    have off : C.eval (List.ofFn x) = false := by
      cases z : C.eval (List.ofFn x) with
      | false => rfl
      | true => exact Bool.noConfusion ((evaluation C hC.1 x _ sub z).symm.trans onn)
    rw [off,eq_comm,decide_eq_false_iff_not]
    rintro ⟨a,b,he,ha,hb⟩
    have bad := safe r hr (a.val,b.val) he
    simp [sub a ha,sub b hb] at bad
