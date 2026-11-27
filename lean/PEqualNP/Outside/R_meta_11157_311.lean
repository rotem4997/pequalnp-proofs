import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Lines one through three avoid both distinguished inputs. Their gates can all carry weight two.
theorem PEqualNP.Outside.R_meta_11157_311
    (tail : ∃ A : Circuit, A.size = 11 ∧ A.output = 24 ∧
      (∀ j (g : Gate), A.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j ∧ a ≠ 0 ∧ a ≠ 7 ∧ b ≠ 0 ∧ b ≠ 7) ∧
      ∀ x : Fin 14 → Bool, A.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (1 ≤ l.val ∧ l.val ≤ 3) ∧ (p=l ∨ p=l+1 ∨ p=l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (core : ∃ B : Circuit, B.size ≤ 15 ∧ 25 ≤ B.output ∧ B.output < 25+B.size ∧
      (∀ j (g : Gate), B.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j) ∧
      (∀ (x : Fin 14 → Bool) (pad : List Bool), pad.length = 11 →
        (B.eval (List.ofFn x ++ pad) = true ↔
        ∃ p l : Fin 7, ¬ (1 ≤ l.val ∧ l.val ≤ 3) ∧ (p=l ∨ p=l+1 ∨ p=l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
      ∀ s : Bool, ∃ d : ℕ → ℕ, d (if s then 0 else 7) = 0 ∧
        d (if s then 7 else 0) ≤ 1 ∧ (∀ i < 25, i ≠ 0 → i ≠ 7 → d i = 2) ∧
        2 ≤ d B.output ∧ ∀ j (g : Gate) a b, B.gates[j]? = some g → g.inputs = [a,b] →
          (g.op = .and → d (25+j) ≤ d a + d b) ∧ (g.op = .or → d (25+j) ≤ min (d a) (d b))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((14 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((14 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  obtain ⟨A, hA, outA, normA, computesA⟩ := tail
  obtain ⟨B, hB, loB, hiB, normB, computesB, weightsB⟩ := core
  let k := 25+B.size
  let last : Gate := ⟨.or,[24,B.output]⟩
  let D : Circuit := ⟨(A.gates ++ B.gates) ++ [last], k⟩
  have lenA : A.gates.length = 11 := hA
  have lenB : B.gates.length = B.size := rfl
  have shape (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) :
      (j < 11 ∧ A.gates[j]? = some g) ∨
      (∃ t, j = 11+t ∧ B.gates[t]? = some g) ∨ (j = 11+B.size ∧ g = last) := by
    change ((A.gates ++ B.gates) ++ [last])[j]? = some g at hg
    by_cases h : j < (A.gates ++ B.gates).length
    · rw [List.getElem?_append_left h] at hg
      by_cases ha : j < A.gates.length
      · exact Or.inl ⟨by omega, (List.getElem?_append_left ha) ▸ hg⟩
      · rw [List.getElem?_append_right (by omega)] at hg
        exact Or.inr (Or.inl ⟨j-A.gates.length, by omega, hg⟩)
    · have inRange : j < ((A.gates ++ B.gates) ++ [last]).length := by
        by_contra! hh
        rw [List.getElem?_eq_none hh] at hg
        contradiction
      have atEnd : j = (A.gates ++ B.gates).length := by
        simp only [List.length_append,List.length_cons,List.length_nil] at inRange h ⊢
        omega
      subst j
      have eq : last = g := by simpa only [List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using hg
      exact Or.inr (Or.inr ⟨by simp [lenA,lenB],eq.symm⟩)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have extend (gs : List Gate) (w : List Bool) :
      ∃ r : List Bool, gs.foldl step w = w ++ r ∧ r.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨r,hr,hl⟩ := ih (step w g)
      exact ⟨_ :: r, by simpa [step,List.append_assoc] using hr, by simp [hl]⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · change ((A.gates ++ B.gates) ++ [last]).length ≤ 27
    simp [lenA,lenB]
    omega
  · intro j g hg
    rcases shape j g hg with ⟨_,ha⟩ | ⟨t,rfl,hb⟩ | ⟨rfl,rfl⟩
    · obtain ⟨ho,a,b,hi,ne,la,lb,_⟩ := normA j g ha
      exact ⟨ho,a,b,hi,ne,la,lb⟩
    · obtain ⟨ho,a,b,hi,ne,la,lb⟩ := normB t g hb
      exact ⟨ho,a,b,hi,ne,by omega,by omega⟩
    · exact ⟨Or.inr rfl,24,B.output,rfl,by omega,by omega,by omega⟩
  · intro x
    let w := A.wires (List.ofFn x)
    let v := B.wires w
    obtain ⟨pad,hpad,lp⟩ := extend A.gates (List.ofFn x)
    change w = _ at hpad
    obtain ⟨r,hr,lr⟩ := extend B.gates w
    change v = _ at hr
    have lw : w.length = 25 := by simp [hpad,lp,lenA]
    have lv : v.length = k := by simp [hr,lw,lr,lenB,k]
    have h24 : v.getD 24 false = A.eval (List.ofFn x) := by
      rw [hr,List.getD_append _ _ _ _ (by omega)]
      change w.getD 24 false = w.getD A.output false
      rw [outA]
    have hcore := computesB x pad (lp.trans lenA)
    rw [← hpad] at hcore
    have ev : D.eval (List.ofFn x) = (v.getD 24 false || v.getD B.output false) := by
      change ((((A.gates ++ B.gates) ++ [last]).foldl step (List.ofFn x)).getD k false) = _
      rw [List.foldl_append,List.foldl_append]
      change (v ++ [last.op.eval (last.inputs.map fun i => v.getD i false)]).getD k false = _
      rw [← lv,List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self,List.getD_cons_zero]
      change GateOp.or.eval [v.getD 24 false, v.getD B.output false] = _
      cases v.getD 24 false <;> cases v.getD B.output false <;> rfl
    rw [ev,Bool.or_eq_true_iff,h24]
    change (_ ∨ B.eval w = true) ↔ _
    rw [computesA,hcore]
    constructor
    · rintro (⟨p,l,_,h⟩ | ⟨p,l,_,h⟩) <;> exact ⟨p,l,h⟩
    · rintro ⟨p,l,h⟩
      by_cases on : 1 ≤ l.val ∧ l.val ≤ 3
      · exact Or.inl ⟨p,l,on,h⟩
      · exact Or.inr ⟨p,l,on,h⟩
  · intro s
    obtain ⟨d,z,o,ordinary,high,gate⟩ := weightsB s
    let f (i : ℕ) := if i = k then 2 else d i
    have earlier {i : ℕ} (hi : i < k) : f i = d i := by simp [f, show i ≠ k by omega]
    have eraseBool (u : Bool) : (if u = true then 0 else 7 : ℕ) < k ∧
        (if u = true then 7 else 0 : ℕ) < k := by cases u <;> simp [k] <;> omega
    refine ⟨f, (earlier (eraseBool s).1).trans z, (earlier (eraseBool s).2).le.trans o, ?_, ?_⟩
    · change 2 ≤ f k
      simp [f]
    · intro j g a b hg hab
      rcases shape j g hg with ⟨hj,ha⟩ | ⟨t,rfl,hb⟩ | ⟨rfl,rfl⟩
      · obtain ⟨_,aa,bb,he,_,la,lb,a0,a7,b0,b7⟩ := normA j g ha
        obtain ⟨rfl,rfl⟩ : aa=a ∧ bb=b := by simpa using he.symm.trans hab
        have eq {i : ℕ} (h : i < 25) (z : i ≠ 0) (s : i ≠ 7) : f i = 2 :=
          (earlier (by dsimp [k]; omega)).trans (ordinary i h z s)
        rw [eq (by omega) (by omega) (by omega), eq (by omega) a0 a7, eq (by omega) b0 b7]
        simp
      · have ht : t < B.gates.length := by
          by_contra! hh
          rw [List.getElem?_eq_none hh] at hb
          contradiction
        obtain ⟨_,aa,bb,he,_,la,lb⟩ := normB t g hb
        obtain ⟨rfl,rfl⟩ : aa=a ∧ bb=b := by simpa using he.symm.trans hab
        have hj : 14+(11+t) = 25+t := by omega
        rw [hj,earlier (by dsimp [k]; omega),earlier (by dsimp [k]; omega),earlier (by dsimp [k]; omega)]
        exact gate t g _ _ hb hab
      · obtain ⟨rfl,rfl⟩ : 24=a ∧ B.output=b := by simpa [last] using hab
        have hj : 14+(11+B.size) = k := by dsimp [k]; omega
        rw [hj,earlier (i:=24) (by dsimp [k]; omega),earlier (i:=B.output) hiB]
        simp [last,f,ordinary 24 (by decide) (by decide) (by decide),high]
