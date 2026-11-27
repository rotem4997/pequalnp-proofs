import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_1479_1
    (hWitness : let F : (Fin 14 → Bool) → Prop := fun x => ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true; ∃ C : Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧ (∀ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) → C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)) = true) ∧ (∀ x : Fin 14 → Bool, ¬ F x → (∀ y : Fin 14 → Bool, (∀ i, x i = true → y i = true) → x ≠ y → F y) → C.eval (List.ofFn x) = false) ∧ ∀ s : Bool, ((PEqualNP.ReadK.linearParts C (fun i => decide (i = if s then 7 else 0)) (List.ofFn fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7))).getD C.output (false,false)).2 = false)
    (hTrace : ∀ C : Circuit, (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) → ∀ s : Bool, ((PEqualNP.ReadK.linearParts C (fun i => decide (i = if s then 7 else 0)) (List.ofFn fun i : Fin 14 => decide (i.val = 0 ∨ i.val = 7))).getD C.output (false,false)).2 = false → ∃ d : ℕ → Bool, (∀ i : Fin 7, d i.val = (if s then false else decide (i = 0)) ∧ d (7+i.val) = (if s then decide (i = 0) else false)) ∧ (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] → let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))); (g.op = GateOp.and → d (14+j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧ (g.op = GateOp.or → d (14+j) = (d a || d b))) ∧ d C.output = false)
    : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  dsimp only at hWitness
  obtain ⟨C,hs,hshape,hpos,hneg,hflags⟩ := hWitness
  let F (x : Fin 14 → Bool) : Prop :=
    ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
      x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] := by
    intro g hg
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨ho,a,b,hab,_,_,_⟩ := hshape j g (List.getElem?_eq_some_iff.mpr ⟨hj,he⟩)
    exact ⟨ho,a,b,hab⟩
  have stepMono (u v : List Bool) (g : Gate)
      (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b])
      (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
    intro i hi
    by_cases hlt : i < u.length
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases hz : i-u.length = 0
      · simp only [hz, List.getD_cons_zero] at hi ⊢
        obtain ⟨ho,a,b,hab⟩ := hg
        rcases ho with ho | ho
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].all id) = true at hi
          change ([v.getD a false, v.getD b false].all id) = true
          simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hi ⊢
          exact ⟨h a hi.1, h b hi.2⟩
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].any id) = true at hi
          change ([v.getD a false, v.getD b false].any id) = true
          simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hi ⊢
          exact hi.elim (fun ha => Or.inl (h a ha)) (fun hb => Or.inr (h b hb))
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction
  have runMono : ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) →
      ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (run gs u).getD i false = true → (run gs v).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro hg u v hlen h i hi; exact h i hi
    | cons g gs ih =>
      intro hg u v hlen h i hi
      change (run gs (step u g)).getD i false = true at hi
      change (run gs (step v g)).getD i false = true
      exact ih (fun k hk => hg k (by simp [hk])) _ _
        (by simp [step, hlen]) (stepMono u v g (hg g (by simp)) hlen h) i hi
  have evalMono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply runMono C.gates hG _ _ (by simp) ?_ C.output
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    split at hi
    · rename_i hlt
      simp [hlt] at hi ⊢
      exact h _ hi
    · simp at hi
  have hcorrect : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x := by
    intro x
    constructor
    · intro hx
      by_contra hbad
      let support (y : Fin 14 → Bool) : Finset (Fin 14) :=
        Finset.univ.filter fun i => y i = true
      let P (n : ℕ) : Prop := ∃ y : Fin 14 → Bool, ¬ F y ∧
        (∀ i, x i = true → y i = true) ∧ 14 - (support y).card = n
      have hP : ∃ n, P n := ⟨14 - (support x).card, x, hbad, fun _ h => h, rfl⟩
      obtain ⟨y,hybad,hxy,hycard⟩ := Nat.find_spec hP
      have hymax : ∀ z : Fin 14 → Bool,
          (∀ i, y i = true → z i = true) → y ≠ z → F z := by
        intro z hyz hne
        by_contra hzbad
        have hzP : P (14 - (support z).card) :=
          ⟨z,hzbad,fun i hi => hyz i (hxy i hi),rfl⟩
        have hsub : support y ⊆ support z := by
          intro i hi
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact hyz i hi
        have hneq : support y ≠ support z := by
          intro he
          apply hne
          funext i
          have ht : y i = true ↔ z i = true := by
            have hm : i ∈ support y ↔ i ∈ support z := by rw [he]
            simpa [support] using hm
          cases h1 : y i <;> cases h2 : z i
          · rfl
          · have ht0 := ht.mpr h2
            rw [h1] at ht0
            contradiction
          · have ht1 := ht.mp h1
            rw [h2] at ht1
            contradiction
          · rfl
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hneq⟩)
        have hle := Nat.find_min' hP hzP
        have hzcard : (support z).card ≤ 14 := by
          simpa using (Finset.card_le_univ (support z))
        omega
      have hf := hneg y hybad hymax
      have ht := evalMono x y hxy hx
      rw [hf] at ht
      contradiction
    · rintro ⟨u,t,hinc,hp,hl⟩
      apply evalMono (fun i => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)) x ?_ (hpos u t hinc)
      intro i hi
      rcases of_decide_eq_true hi with hi | hi
      · subst i; exact hp
      · subst i; exact hl
  refine ⟨C,hs,hshape,hcorrect,0,0,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,hin,hrec,hout⟩ := hTrace C hshape true (hflags true)
    exact ⟨d,by simpa using hin,by simpa using hrec,hout⟩
  · obtain ⟨d,hin,hrec,hout⟩ := hTrace C hshape false (hflags false)
    exact ⟨d,by simpa using hin,by simpa using hrec,hout⟩
