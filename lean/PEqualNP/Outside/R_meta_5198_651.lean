import Mathlib.Data.List.OfFn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_5198_651
    (coverage : ∀ k : Fin 26, ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      (((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)).getD k.val false = true))
    (bound :
      let S := singerLines3
      let X := fun (P L : Finset (Fin 13)) => (List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ L)
      let V := fun (C : Circuit) (k : ℕ) (x : List Bool) => (C.wires x).getD k false
      ∀ (C : Circuit) (a : ℕ), let b := 25 + C.size
      Monotone2 C → ReadsBack 26 C → 26 ≤ a → a < b →
      (∀ p l, p ∈ S l → V C a (X {p} {l}) = true ∨ V C b (X {p} {l}) = true) →
      (∀ Q, IsQuadrangle S Q → (V C a (X Q (missLines S Q)) || V C b (X Q (missLines S Q))) = false) →
      (∀ r : Bool, ∃ p l, p ∈ S l ∧ V C a (X {p} {l}) = r ∧ V C b (X {p} {l}) = !r) →
      ({j | j < C.size ∧ (gateAt C j).op = GateOp.and ∧ ∃ i ∈ (gateAt C j).inputs,
        26 ≤ i ∧ (gateAt C (i-26)).op = GateOp.and} : Set ℕ).encard ≤ 1 → 63 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  classical
  intro S X V G AND nest C a b mono earlier ha hb pos neg xa xb unique
  have start : ∀ (gs : List Gate) (x : List Bool) (k : ℕ), k < x.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD k false =
        x.getD k false := by
    intro gs
    induction gs with
    | nil => intros; rfl
    | cons g gs ih =>
      intro x k hk
      rw [List.foldl_cons, ih _ _ (by simp; omega)]
      simp only [List.getD_eq_getElem _ _ hk]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hk]
  have hlen : ∀ (gs : List Gate) (x : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
        x.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro; simp
    | cons g gs ih =>
      intro x
      rw [List.foldl_cons, ih]
      simp
      omega
  have lenX (P L : Finset (Fin 13)) : (X P L).length = 26 := by
    simp [X]
  have rawGone (w : ℕ) (off : ∀ Q, IsQuadrangle S Q → V C w (X Q (missLines S Q)) = false) :
      26 ≤ w := by
    by_contra! small
    obtain ⟨Q, hQ, active⟩ := coverage ⟨w,small⟩
    have eq := start C.gates (X Q (missLines S Q)) w (by simp [lenX, small])
    change V C w (X Q (missLines S Q)) = _ at eq
    change (X Q (missLines S Q)).getD w false = true at active
    exact Bool.false_ne_true ((off Q hQ).symm.trans (eq.trans active))
  have ga := rawGone a (fun Q hQ => (neg Q hQ).1)
  have gb := rawGone b (fun Q hQ => (neg Q hQ).2)
  have different : a ≠ b := by
    intro he
    obtain ⟨p,l,_,hy,hn⟩ := xa
    exact Bool.false_ne_true (hn.symm.trans (he ▸ hy))
  let bmax := max a b
  let amin := min a b
  have hmax : bmax < 26 + C.size := max_lt ha hb
  have hamin : 26 ≤ amin := le_min ga gb
  have hab : amin < bmax := by omega
  let t := bmax - 25
  have ht : t ≤ C.size := by omega
  have ht' : t ≤ C.gates.length := ht
  let D : Circuit := ⟨C.gates.take t, bmax⟩
  have sizeD : D.size = t := by
    change (C.gates.take t).length = t
    rw [List.length_take, Nat.min_eq_left ht']
  have maxD : bmax = 25 + D.size := by omega
  have truncV (P L : Finset (Fin 13)) (k : ℕ) (hk : k ≤ bmax) :
      V C k (X P L) = V D k (X P L) := by
    change (C.gates.foldl _ (X P L)).getD k false = ((C.gates.take t).foldl _ (X P L)).getD k false
    conv_lhs => rw [← List.take_append_drop t C.gates]
    rw [List.foldl_append]
    apply start
    rw [hlen, lenX, List.length_take, Nat.min_eq_left ht']
    omega
  have eqgate (j : ℕ) (hj : j < D.size) : gateAt D j = gateAt C j := by
    have a' : j < D.gates.length := hj
    have b' : j < C.gates.length := by change j < C.size; omega
    change D.gates.getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩
    rw [List.getD_eq_getElem _ _ a', List.getD_eq_getElem _ _ b']
    simp [D]
  have monoD : Monotone2 D := by
    intro g hg
    exact mono g (List.mem_of_mem_take hg)
  have earlyD : ReadsBack 26 D := by
    intro j hj k hk
    rw [eqgate j hj] at hk
    exact earlier j (by change j < C.size; change j < D.size at hj; omega) k hk
  have keep (j : ℕ) (hj : j < D.size) : nest D j → nest C j := by
    rintro ⟨h, i, hi, ilo, hop⟩
    have bit : i - 26 < D.size := by
      have hlt := earlyD j hj i hi
      omega
    change (gateAt D j).op = GateOp.and at h
    change i ∈ (gateAt D j).inputs at hi
    change (gateAt D (i - 26)).op = GateOp.and at hop
    change (gateAt C j).op = GateOp.and ∧ ∃ i ∈ (gateAt C j).inputs,
      26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and
    rw [eqgate j hj] at h hi
    rw [eqgate _ bit] at hop
    exact ⟨h, i, hi, ilo, hop⟩
  have cardD : ({j | j < D.size ∧ nest D j} : Set ℕ).encard ≤ 1 := by
    apply Set.encard_le_one_iff.mpr
    rintro j k ⟨hj, hjn⟩ ⟨hk, hkn⟩
    exact unique j (Finset.mem_range.mpr (by omega)) k (Finset.mem_range.mpr (by omega))
      (keep _ hj hjn) (keep _ hk hkn)
  have order_ab : amin = a ∧ bmax = b ∨ amin = b ∧ bmax = a := by
    by_cases le : a ≤ b
    · exact Or.inl ⟨min_eq_left le, max_eq_right le⟩
    · have le' : b ≤ a := by omega
      exact Or.inr ⟨min_eq_right le', max_eq_left le'⟩
  have ab_pos : ∀ p l, p ∈ S l → V D amin (X {p} {l}) = true ∨ V D bmax (X {p} {l}) = true := by
    intro p l hp
    rw [← truncV _ _ _ hab.le, ← truncV _ _ _ le_rfl]
    rcases order_ab with ⟨e1,e2⟩ | ⟨e1,e2⟩
    · rw [e1,e2]; exact pos p l hp
    · rw [e1,e2]; exact (pos p l hp).symm
  have ab_neg : ∀ Q, IsQuadrangle S Q →
      (V D amin (X Q (missLines S Q)) || V D bmax (X Q (missLines S Q))) = false := by
    intro Q hQ
    rw [← truncV _ _ _ hab.le, ← truncV _ _ _ le_rfl]
    obtain ⟨za,zb⟩ := neg Q hQ
    rcases order_ab with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;> simp [e1,e2,za,zb]
  have exclus (r : Bool) : ∃ p l, p ∈ S l ∧ V D amin (X {p} {l}) = r ∧ V D bmax (X {p} {l}) = !r := by
    suffices ex : ∃ p l, p ∈ S l ∧ V C amin (X {p} {l}) = r ∧ V C bmax (X {p} {l}) = !r by
      obtain ⟨p,l,hp,pa,pb⟩ := ex
      exact ⟨p,l,hp,(truncV _ _ _ hab.le).symm.trans pa,(truncV _ _ _ le_rfl).symm.trans pb⟩
    rcases order_ab with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;> rw [e1,e2] <;> cases r
    · obtain ⟨p,l,hp,yes,no⟩ := xb
      exact ⟨p,l,hp,no,yes⟩
    · exact xa
    · obtain ⟨p,l,hp,yes,no⟩ := xa
      exact ⟨p,l,hp,no,yes⟩
    · exact xb
  have hd : 63 ≤ D.size := bound D amin monoD earlyD hamin (maxD ▸ hab)
    (maxD ▸ ab_pos) (maxD ▸ ab_neg) (maxD ▸ exclus) cardD
  omega
