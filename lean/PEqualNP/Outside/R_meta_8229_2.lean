import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8229_2 (h1 : let b : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146];
      ∃ (L : List ℕ) (D : Finset ℕ) (T U : List (ℕ × ℕ)),
      L.Nodup ∧ D ⊆ L.toFinset ∧ D.card = 2 ∧ U ≠ [] ∧
      L.length + 2*T.length + U.length + (U.map Prod.fst).toFinset.card ≤ 22 ∧
      (∀ i : Fin L.length, let A := b ++ L.take i.val; ∃ x ∈ A, ∃ y ∈ A, L.get i = if L.get i ∈ D then x &&& y else x ||| y) ∧ (∀ w ∈ D, w &&& 1099511562240 ≠ 0) ∧
      (∀ t ∈ T, t.1 ∈ b ++ L ∧ t.2 ∈ b ++ L ∧ (t.1 &&& t.2) &&& 1099511562240 = 0) ∧
      (∀ t ∈ U, t.1 ∈ b ∧ t.2 ∈ b ∧ (t.1 &&& t.2) &&& 1099511562240 = 0) ∧
      (T ++ U).foldl (fun (z : ℕ) (t : ℕ × ℕ) => z ||| (t.1 &&& t.2)) 0 = 65535)
    (h2 : ∀ (A : List ℕ) (U : List (ℕ × ℕ)) (m z : ℕ), U ≠ [] →
      (∀ t ∈ U, t.1 ∈ A ∧ t.2 ∈ A ∧ (t.1 &&& t.2) &&& m = 0) →
      ∃ (F : List ℕ) (R : List (ℕ × ℕ)), F.Nodup ∧ (∀ f ∈ F, f ∉ A) ∧ R ≠ [] ∧
      F.length + 2*R.length ≤ U.length + (U.map Prod.fst).toFinset.card ∧
      (∀ i : Fin F.length, let B := A ++ F.take i.val; ∃ x ∈ B, ∃ y ∈ B, F.get i = x ||| y) ∧
      (∀ t ∈ R, t.1 ∈ A ++ F ∧ t.2 ∈ A ++ F ∧ (t.1 &&& t.2) &&& m = 0) ∧ R.foldl (fun (z : ℕ) (t : ℕ × ℕ) => z ||| (t.1 &&& t.2)) z = U.foldl (fun (z : ℕ) (t : ℕ × ℕ) => z ||| (t.1 &&& t.2)) z)
    (h3 : ∀ (b L : List ℕ) (D : Finset ℕ) (T : List (ℕ × ℕ)) (m : ℕ), b.length = 11 → L.Nodup → D ⊆ L.toFinset → T ≠ [] → L.length + 2*T.length ≤ 22 →
      (∀ i : Fin L.length, let A := b ++ L.take i.val; ∃ x ∈ A, ∃ y ∈ A, L.get i = if L.get i ∈ D then x &&& y else x ||| y) → (∀ w ∈ D, w &&& m ≠ 0) → (∀ t ∈ T, t.1 ∈ b ++ L ∧ t.2 ∈ b ++ L ∧ (t.1 &&& t.2) &&& m = 0) →
      ∃ (p : Fin 21 → Bool × Fin 32 × Fin 32) (q : ℕ → Bool), let V := (List.ofFn p).foldl (fun (s : List ℕ) (g : Bool × Fin 32 × Fin 32) => s ++ [if g.1 = true then s.getD g.2.1 0 &&& s.getD g.2.2 0 else s.getD g.2.1 0 ||| s.getD g.2.2 0]) b;
      (∀ i, (p i).2.1.val < 11+i.val ∧ (p i).2.2.val < 11+i.val) ∧
      V.getD 31 0 = T.foldl (fun (z : ℕ) (t : ℕ × ℕ) => z ||| (t.1 &&& t.2)) 0 ∧
      (List.ofFn fun i => decide ((p i).1 = true ∧ V.getD (11+i.val) 0 &&& m ≠ 0)).count true = D.card ∧
      (∀ i, (p i).1 = true ∨ q (11+i.val) = true → q (p i).2.1 = true ∧ q (p i).2.2 = true) ∧
      ∀ i, (p i).1 = true → V.getD (11+i.val) 0 &&& m = 0 → q (11+i.val) = false)
    (h4 : ∀ (p : Fin 21 → Bool × Fin 32 × Fin 32) (m : ℕ → Bool),
      (∀ j, (p j).1 = true ∨ m (11+j.val) = true → m (p j).2.1 = true ∧ m (p j).2.2 = true) →
      let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨(List.ofFn p).map (fun g => ⟨if g.1 = true then .and else .or, [g.2.1.val,g.2.2.val]⟩),31⟩;
      ∀ i j : Fin 21, m (11+i.val) = false → (p j).1 = true → ¬ PEqualNP.EdgeOwnership.InCone 11 C i.val j.val) : ∃ (x1 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   (∀ (x2 : Fin (21 : ℕ)), ↑(x1 x2).2.1 < (11 : ℕ) + ↑x2 ∧ ↑(x1 x2).2.2 < (11 : ℕ) + ↑x2) ∧     have x2 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x2 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x2.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x2.2.1, ↑x2.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x1), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };     have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] (List.ofFn x1);     x3.getD (31 : ℕ) (0 : ℕ) = (65535 : ℕ) ∧ List.count Bool.true (List.ofFn fun (x4 : Fin (21 : ℕ)) => Decidable.decide ((x1 x4).1 = Bool.true ∧ x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ))) = (2 : ℕ) ∧ ∀ (x4 x5 : Fin (21 : ℕ)), (x1 x4).1 = Bool.true → x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) = (0 : ℕ) → (x1 x5).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 ↑x4 ↑x5 := by
  let b : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  obtain ⟨L,D,T,U,nd,sub,card,ne,budget,pre,dirty,tops,raw,cover⟩ := h1
  let mix := (fun (z : ℕ) (t : ℕ × ℕ) => z ||| (t.1 &&& t.2))
  obtain ⟨F,R,ndF,fresh,neR,cost,ors,final,eq⟩ := h2 (b ++ L) U 1099511562240 (T.foldl mix 0) ne (fun t ht =>
    ⟨List.mem_append_left _ (raw t ht).1,List.mem_append_left _ (raw t ht).2.1,(raw t ht).2.2⟩)
  have nd' : (L ++ F).Nodup := List.nodup_append.mpr ⟨nd,ndF,by
    intro x hx y hy he
    exact fresh y hy (List.mem_append_right _ (he ▸ hx))⟩
  have sub' : D ⊆ (L ++ F).toFinset := fun x hx => List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (sub hx)))
  have run' (i : Fin (L ++ F).length) : let A := b ++ (L ++ F).take i.val
      ∃ x ∈ A, ∃ y ∈ A, (L ++ F).get i = if (L ++ F).get i ∈ D then x &&& y else x ||| y := by
    by_cases h : i.val < L.length
    · simpa only [List.get_eq_getElem,List.getElem_append_left h,List.take_append_of_le_length h.le] using pre ⟨i.val,h⟩
    · have hi := i.isLt
      simp only [List.length_append] at hi
      let j : Fin F.length := ⟨i.val-L.length,by omega⟩
      have hw := ors j
      have out : F.get j ∉ D := fun hm => fresh _ (List.get_mem F j) (List.mem_append_right _ (List.mem_toFinset.mp (sub hm)))
      have le := Nat.le_of_not_lt h
      change F[i.val-L.length] ∉ D at out
      simpa only [List.get_eq_getElem,List.getElem_append_right le,List.take_append, List.take_of_length_le le, ← List.append_assoc, j, out, ↓reduceIte] using hw
  have oth (t : ℕ × ℕ) (ht : t ∈ T ++ R) : t.1 ∈ b ++ (L ++ F) ∧ t.2 ∈ b ++ (L ++ F) ∧ (t.1 &&& t.2) &&& 1099511562240 = 0 := by
    rw [← List.append_assoc]
    rcases List.mem_append.mp ht with h | h
    · exact ⟨List.mem_append_left _ (tops t h).1,List.mem_append_left _ (tops t h).2.1,(tops t h).2.2⟩
    · exact final t h
  obtain ⟨p,m,back,o,count,guard,clean⟩ := h3 b (L++F) D (T++R) 1099511562240 rfl nd' sub' (by simp [neR]) (by simp only [List.length_append]; omega) run' dirty oth
  refine ⟨p,back,?_,count.trans card,fun i j hi hc hj => h4 p m guard i j (clean i hi hc) hj⟩
  rw [List.foldl_append] at o cover
  exact o.trans (eq.trans cover)
