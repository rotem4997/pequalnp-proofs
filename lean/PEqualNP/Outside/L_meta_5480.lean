import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5480

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- one gate step on wire values, as in Circuit.wires
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- one gate step on the sets of input wires each wire depends on
def stepD (d : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  d ++ [g.inputs.toFinset.biUnion (fun i => d.getD i ∅)]

def Dp (gs : List Gate) (n : ℕ) : List (Finset ℕ) :=
  gs.foldl stepD (List.ofFn fun i : Fin n => ({i.val} : Finset ℕ))

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl stepW x = stepW (gs.foldl stepW x) g := by
  simp [List.foldl_append]

theorem Dp_snoc (gs : List Gate) (g : Gate) (n : ℕ) :
    Dp (gs ++ [g]) n = stepD (Dp gs n) g := by
  simp [Dp, List.foldl_append]

theorem len_W (gs : List Gate) : ∀ x : List Bool, (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih => intro x; simp only [List.foldl_cons, ih, stepW, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem len_D (gs : List Gate) : ∀ d : List (Finset ℕ), (gs.foldl stepD d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; simp only [List.foldl_cons, ih, stepD, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem Dp_nil_get (n w : ℕ) (hw : w < n) : (Dp [] n).getD w ∅ = {w} := by
  have hl : w < (List.ofFn fun i : Fin n => ({i.val} : Finset ℕ)).length := by simpa using hw
  simp only [Dp, List.foldl_nil]
  rw [List.getD_eq_getElem _ _ hl]
  simp

theorem Dp_nil_get' (n w : ℕ) (hw : n ≤ w) : (Dp [] n).getD w ∅ = ∅ := by
  simp only [Dp, List.foldl_nil]
  exact List.getD_eq_default _ _ (by simpa using hw)

theorem stepD_get_ne (d : List (Finset ℕ)) (g : Gate) (w : ℕ) (hw : w ≠ d.length) :
    (stepD d g).getD w ∅ = d.getD w ∅ := by
  unfold stepD
  rcases lt_or_gt_of_ne hw with h | h
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem stepD_get_eq (d : List (Finset ℕ)) (g : Gate) :
    (stepD d g).getD d.length ∅ = g.inputs.toFinset.biUnion (fun i => d.getD i ∅) := by
  unfold stepD
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem stepW_get_lt (w : List Bool) (g : Gate) (k : ℕ) (hk : k < w.length) :
    (stepW w g).getD k false = w.getD k false := by
  unfold stepW
  exact List.getD_append _ _ _ _ hk

theorem stepW_get_eq (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold stepW
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem stepW_get_gt (w : List Bool) (g : Gate) (k : ℕ) (hk : w.length < k) :
    (stepW w g).getD k false = false := by
  unfold stepW
  exact List.getD_eq_default _ _ (by simp; omega)

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (n : ℕ)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n) :
    ∀ w, (∀ i ∈ (Dp gs n).getD w ∅, x.getD i false = true → x'.getD i false = true) →
      (gs.foldl stepW x).getD w false = true → (gs.foldl stepW x').getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w h hw
    simp only [List.foldl_nil] at hw ⊢
    have hwn : w < n := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hw
      exact Bool.false_ne_true hw
    exact h w (by rw [Dp_nil_get n w hwn]; simp) hw
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg'' => hg g' (List.mem_append_left _ hg'')
    have ih' := ih hg'
    intro w h hw
    rw [W_snoc] at hw ⊢
    rw [Dp_snoc] at h
    have lW : (gs.foldl stepW x).length = n + gs.length := by rw [len_W]; omega
    have lW' : (gs.foldl stepW x').length = n + gs.length := by rw [len_W]; omega
    have lD : (Dp gs n).length = n + gs.length := by unfold Dp; rw [len_D]; simp
    rcases lt_trichotomy w (n + gs.length) with hlt | heq | hgt
    · rw [stepW_get_lt _ _ _ (by omega)] at hw ⊢
      refine ih' w (fun i hi hxi => h i ?_ hxi) hw
      rw [stepD_get_ne _ _ _ (by omega)]
      exact hi
    · subst heq
      rw [← lW, stepW_get_eq] at hw
      rw [← lW', stepW_get_eq]
      rw [← lD, stepD_get_eq] at h
      have hsub : ∀ i ∈ g.inputs, ∀ j ∈ (Dp gs n).getD i ∅,
          x.getD j false = true → x'.getD j false = true := by
        intro i hi j hj hxj
        exact h j (Finset.mem_biUnion.2 ⟨i, List.mem_toFinset.2 hi, hj⟩) hxj
      rcases hg g (List.mem_append_right _ (List.mem_singleton_self _)) with hop | hop
      · rw [hop] at hw ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, id] at hw ⊢
        intro i hi
        exact ih' i (hsub i hi) (hw i hi)
      · rw [hop] at hw ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id, exists_exists_and_eq_and]
          at hw ⊢
        obtain ⟨i, hi, hv⟩ := hw
        exact ⟨i, hi, ih' i (hsub i hi) hv⟩
    · rw [stepW_get_gt _ _ _ (by omega)] at hw
      exact absurd hw Bool.false_ne_true

theorem count (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (n : ℕ) :
    ∀ S : Finset ℕ, (S.biUnion fun w => (Dp gs n).getD w ∅).card ≤ S.card + gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro S
    have h1 : ∀ w, ((Dp [] n).getD w ∅).card ≤ 1 := by
      intro w
      by_cases hw : w < n
      · rw [Dp_nil_get n w hw]; simp
      · rw [Dp_nil_get' n w (by omega)]; simp
    calc (S.biUnion fun w => (Dp [] n).getD w ∅).card
        ≤ ∑ w ∈ S, ((Dp [] n).getD w ∅).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ S, 1 := Finset.sum_le_sum (fun w _ => h1 w)
      _ = S.card + ([] : List Gate).length := by simp
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 :=
      fun g' hg'' => hg g' (List.mem_append_left _ hg'')
    have hgl : g.inputs.length ≤ 2 := hg g (List.mem_append_right _ (List.mem_singleton_self _))
    have ih' := ih hg'
    intro S
    rw [Dp_snoc]
    simp only [List.length_append, List.length_singleton]
    set d := Dp gs n with hd
    by_cases hm : d.length ∈ S
    · have hsub : (S.biUnion fun w => (stepD d g).getD w ∅) ⊆
          ((S.erase d.length) ∪ g.inputs.toFinset).biUnion (fun w => d.getD w ∅) := by
        intro j hj
        obtain ⟨w, hwS, hjw⟩ := Finset.mem_biUnion.1 hj
        by_cases hwe : w = d.length
        · subst hwe
          rw [stepD_get_eq] at hjw
          obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.1 hjw
          exact Finset.mem_biUnion.2 ⟨i, Finset.mem_union_right _ hi, hji⟩
        · rw [stepD_get_ne _ _ _ hwe] at hjw
          exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwe, hwS⟩), hjw⟩
      have h1 := Finset.card_le_card hsub
      have h2 := ih' ((S.erase d.length) ∪ g.inputs.toFinset)
      have h3 := Finset.card_union_le (S.erase d.length) g.inputs.toFinset
      have h4 := Finset.card_erase_of_mem hm
      have h5 := List.toFinset_card_le g.inputs
      have h6 : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hm⟩
      omega
    · have heq : (S.biUnion fun w => (stepD d g).getD w ∅) = S.biUnion fun w => d.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        exact stepD_get_ne _ _ _ (fun e => hm (e ▸ hw))
      rw [heq]
      have := ih' S
      omega

theorem oe_len (u v : Fin 4) : (oneEach u v).length = 8 := by
  simp [oneEach]

theorem oe_far (u v : Fin 4) (j : ℕ) (hj : 8 ≤ j) : (oneEach u v).getD j false = false :=
  List.getD_eq_default _ _ (by rw [oe_len]; exact hj)

def Agr : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (278 : ℕ).testBit (4 * u.val + v.val)

theorem lower : ¬ RepSizeAtMost Agr 4 := by
  rintro ⟨C, hC, hs, hr⟩
  have hg1 : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have hg2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hC g hg).2
  have hcard := count C.gates hg2 8 {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hcard
  have hsz : C.gates.length ≤ 4 := hs
  have key : ∀ (i : ℕ) (u v u' v' : Fin 4), Agr u v = true → Agr u' v' = false →
      (∀ j, j < 8 → j ≠ i → (oneEach u v).getD j false = true → (oneEach u' v').getD j false = true) →
      i ∈ (Dp C.gates 8).getD C.output ∅ := by
    intro i u v u' v' hA hA' hj
    by_contra hi
    have h1 : C.eval (oneEach u v) = true := by rw [hr u v]; exact hA
    have h2 : C.eval (oneEach u' v') = false := by rw [hr u' v']; exact hA'
    unfold Circuit.eval at h1 h2
    rw [wires_eq] at h1 h2
    have := mono C.gates hg1 8 (oneEach u v) (oneEach u' v') (oe_len u v) (oe_len u' v') C.output
      (fun j hjD hxj => by
        rcases lt_or_ge j 8 with h8 | h8
        · exact hj j h8 (fun e => hi (e ▸ hjD)) hxj
        · rw [oe_far u v j h8] at hxj; exact absurd hxj Bool.false_ne_true) h1
    rw [h2] at this
    exact Bool.false_ne_true this
  have k0 := key 0 0 1 3 1 (by decide) (by decide) (by decide)
  have k1 := key 1 1 0 3 0 (by decide) (by decide) (by decide)
  have k2 := key 2 2 0 3 0 (by decide) (by decide) (by decide)
  have k4 := key 4 1 0 1 3 (by decide) (by decide) (by decide)
  have k5 := key 5 0 1 0 3 (by decide) (by decide) (by decide)
  have k6 := key 6 0 2 0 3 (by decide) (by decide) (by decide)
  have hsub : ({0, 1, 2, 4, 5, 6} : Finset ℕ) ⊆ (Dp C.gates 8).getD C.output ∅ := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have h6 := Finset.card_le_card hsub
  have h7 : ({0, 1, 2, 4, 5, 6} : Finset ℕ).card = 6 := by decide
  omega

def Cup : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [9, 11] }], output := 12 }

theorem upper : RepSizeAtMost Agr 5 := by
  refine ⟨Cup, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Cup, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · unfold Represents Agr Cup; decide

end PEqualNP.Outside.L_meta_5480

theorem PEqualNP.Outside.L_meta_5480 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (278 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (278 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨PEqualNP.Outside.L_meta_5480.upper, PEqualNP.Outside.L_meta_5480.lower⟩
