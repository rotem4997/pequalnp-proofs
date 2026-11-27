import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2838

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma merge_count {τ : Type*} [DecidableEq τ] (f : ℕ → Finset τ) (B : Finset ℕ)
    (h : ∀ w, 2 ≤ (f w).card → (∃ a < w, f w ⊆ f a) ∨
      (w ∈ B ∧ ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b))
    (R : Finset ℕ) : (R.biUnion f).card ≤ R.card + B.card := by
  have key : ∀ n : ℕ, ∀ R : Finset ℕ, (∀ w ∈ R, w < n) →
      (R.biUnion f).card ≤ R.card + (B.filter (· < n)).card := by
    intro n
    induction n with
    | zero =>
      intro R hR
      have : R = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
        have := hR w hw; omega
      simp [this]
    | succ n ih =>
      intro R hR
      have hmonoB : (B.filter (· < n)).card ≤ (B.filter (· < n + 1)).card :=
        Finset.card_le_card fun w hw => by
          simp only [Finset.mem_filter] at hw ⊢
          exact ⟨hw.1, by omega⟩
      by_cases hn : n ∈ R
      · have herase : ∀ w ∈ R.erase n, w < n := fun w hw => by
          have h1 := hR w (Finset.mem_of_mem_erase hw)
          have h2 := Finset.ne_of_mem_erase hw
          omega
        have hcardR : (R.erase n).card + 1 = R.card := Finset.card_erase_add_one hn
        have hsplit : R.biUnion f ⊆ f n ∪ (R.erase n).biUnion f := by
          intro t ht
          rw [Finset.mem_biUnion] at ht
          obtain ⟨w, hw, htw⟩ := ht
          rw [Finset.mem_union]
          by_cases hwn : w = n
          · exact Or.inl (hwn ▸ htw)
          · exact Or.inr (Finset.mem_biUnion.2 ⟨w, Finset.mem_erase.2 ⟨hwn, hw⟩, htw⟩)
        by_cases h2 : 2 ≤ (f n).card
        · rcases h n h2 with ⟨a, ha, hsub⟩ | ⟨hB, a, ha, b, hb, hsub⟩
          · have h3 := ih (insert a (R.erase n)) (fun w hw => by
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact ha
              · exact herase w hw)
            have h4 : R.biUnion f ⊆ (insert a (R.erase n)).biUnion f := by
              rw [Finset.biUnion_insert]
              exact hsplit.trans (Finset.union_subset_union hsub (Finset.Subset.refl _))
            have h5 := Finset.card_le_card h4
            have h6 := Finset.card_insert_le a (R.erase n)
            omega
          · have h3 := ih (insert a (insert b (R.erase n))) (fun w hw => by
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact ha
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact hb
              · exact herase w hw)
            have h4 : R.biUnion f ⊆ (insert a (insert b (R.erase n))).biUnion f := by
              rw [Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
              exact hsplit.trans (Finset.union_subset_union hsub (Finset.Subset.refl _))
            have h5 := Finset.card_le_card h4
            have h6 := Finset.card_insert_le a (insert b (R.erase n))
            have h7 := Finset.card_insert_le b (R.erase n)
            have h8 : (B.filter (· < n)).card + 1 ≤ (B.filter (· < n + 1)).card := by
              have hnot : n ∉ B.filter (· < n) := by simp
              rw [← Finset.card_insert_of_notMem hnot]
              refine Finset.card_le_card fun w hw => ?_
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact Finset.mem_filter.2 ⟨hB, by omega⟩
              · rw [Finset.mem_filter] at hw ⊢
                exact ⟨hw.1, by omega⟩
            omega
        · have h3 := ih (R.erase n) herase
          have h4 := Finset.card_le_card hsplit
          have h5 := Finset.card_union_le (f n) ((R.erase n).biUnion f)
          omega
      · have h3 := ih R (fun w hw => by
          have h1 := hR w hw
          have h2 : w ≠ n := fun e => hn (e ▸ hw)
          omega)
        omega
  have h1 := key (R.sup id + 1) R (fun w hw => by
    have := Finset.le_sup (f := id) hw
    simp only [id] at this
    omega)
  have h2 : (B.filter (· < R.sup id + 1)).card ≤ B.card := Finset.card_filter_le _ _
  omega

lemma gate_op {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    value C x (n + k) = C.gates[k].op.eval
      (C.gates[k].inputs.map fun r => if r < n + k then value C x r else false) := by
  have h := gate_value C x (n + k) (by omega) (by unfold Circuit.size; omega)
  simpa only [Nat.add_sub_cancel_left] using h

lemma and_val {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (ho : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  rw [gate_op C k hk x, ho]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun r _ => ?_
  by_cases h : r < n + k <;> simp [h]

lemma or_val {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (ho : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  rw [gate_op C k hk x, ho]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  by_cases h : r < n + k <;> simp [h]

lemma two_kids (L : List ℕ) (hL : L.length ≤ 2) (w : ℕ) (hw : 0 < w) :
    ∃ a < w, ∃ b < w, ∀ r ∈ L, r < w → r = a ∨ r = b := by
  match L, hL with
  | [], _ => exact ⟨0, hw, 0, hw, by simp⟩
  | [a], _ =>
    by_cases ha : a < w
    · exact ⟨a, ha, a, ha, by simp⟩
    · exact ⟨0, hw, 0, hw, by simp; omega⟩
  | [a, b], _ =>
    by_cases ha : a < w <;> by_cases hb : b < w
    · exact ⟨a, ha, b, hb, by simp⟩
    · exact ⟨a, ha, a, ha, by simp; omega⟩
    · exact ⟨b, hb, b, hb, by simp; omega⟩
    · exact ⟨0, hw, 0, hw, by simp; omega⟩
  | _ :: _ :: _ :: _, h => simp at h

def Serves {n : ℕ} (C : Circuit) (l y : Fin n → Bool) (w : ℕ) : Prop :=
  value C l w = true ∧ value C y w = false

def Counted {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l y : ι → Fin n → Bool)
    (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Serves C (l p) (y p) w ∧ Serves C (l p') (y p') w

lemma gate_sep {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) (l y : Fin n → Bool)
    (h : Serves C l y (n + k)) : ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Serves C l y r := by
  by_contra hcon
  have hy : value C y (n + k) = true := gate_mono C k hk hop l y (fun r hr hlt hv => by
    by_contra hne
    exact hcon ⟨r, hr, hlt, hv, by simpa using hne⟩) h.1
  rw [h.2] at hy
  exact Bool.noConfusion hy

theorem ledger {n : ℕ} {ι : Type*} (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (T : Finset ι) (l y : ι → Fin n → Bool)
    (K : Finset ℕ) (R : Finset ℕ)
    (hR : ∀ t ∈ T, ∃ w ∈ R, Serves C (l t) (y t) w)
    (hin : ∀ v : Fin n, ∀ s ∈ T, ∀ t ∈ T, l s v = true → y s v = false → l t v = true →
      y t v = false → s = t)
    (hK : ∀ k, ∀ hk : k < C.gates.length, Counted C T l y (n + k) →
      (C.gates[k].op = GateOp.and ∧ ∀ s ∈ T, ∀ t ∈ T, y s = y t) ∨
      (C.gates[k].op = GateOp.or ∧ ∀ s ∈ T, ∀ t ∈ T, l s = l t) ∨
      (k ∈ K ∧ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or))) :
    T.card ≤ R.card + K.card := by
  classical
  let f : ℕ → Finset ι := fun w => T.filter fun t => Serves C (l t) (y t) w
  have hmem : ∀ w t, t ∈ f w ↔ t ∈ T ∧ Serves C (l t) (y t) w := fun w t => Finset.mem_filter
  have key := merge_count f (K.image (n + ·)) (by
    intro w hw
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hw
    rw [hmem] at hp hp'
    have hwn : n ≤ w := by
      by_contra hlt
      have hlt : w < n := by omega
      have e : ∀ x : Fin n → Bool, value C x w = x ⟨w, hlt⟩ := fun x =>
        input_value C x ⟨w, hlt⟩
      have h1 := hp.2
      have h2 := hp'.2
      unfold Serves at h1 h2
      rw [e, e] at h1 h2
      exact hne (hin ⟨w, hlt⟩ p hp.1 p' hp'.1 h1.1 h1.2 h2.1 h2.2)
    have hwl : w < n + C.gates.length := by
      by_contra hge
      have h1 := hp.2.1
      rw [missing_value C (l p) w (by unfold Circuit.size; omega)] at h1
      exact Bool.noConfusion h1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hc : Counted C T l y (n + k) := ⟨p, hp.1, p', hp'.1, hne, hp.2, hp'.2⟩
    rcases hK k hk hc with ⟨ho, hy⟩ | ⟨ho, hl⟩ | ⟨hkK, hop⟩
    · left
      have h1 := hp.2.2
      have h2 : ¬ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C (y p) r = true := fun h => by
        rw [(and_val C k hk ho (y p)).mpr h] at h1
        exact Bool.noConfusion h1
      push Not at h2
      obtain ⟨r, hr, hrv⟩ := h2
      have hlt := ((and_val C k hk ho (l p)).mp hp.2.1 r hr).1
      refine ⟨r, hlt, fun t ht => ?_⟩
      rw [hmem] at ht ⊢
      refine ⟨ht.1, ((and_val C k hk ho (l t)).mp ht.2.1 r hr).2, ?_⟩
      rw [hy t ht.1 p hp.1]
      simpa using hrv hlt
    · left
      obtain ⟨r, hr, hlt, hrv⟩ := (or_val C k hk ho (l p)).mp hp.2.1
      refine ⟨r, hlt, fun t ht => ?_⟩
      rw [hmem] at ht ⊢
      refine ⟨ht.1, by rw [hl t ht.1 p hp.1]; exact hrv, ?_⟩
      by_contra hne
      have := (or_val C k hk ho (y t)).mpr ⟨r, hr, hlt, by simpa using hne⟩
      rw [ht.2.2] at this
      exact Bool.noConfusion this
    · right
      refine ⟨Finset.mem_image.mpr ⟨k, hkK, rfl⟩, ?_⟩
      obtain ⟨r0, _, hr0, _⟩ := gate_sep C k hk hop _ _ hp.2
      obtain ⟨a, ha, b, hb, hab⟩ := two_kids _ (hfan _ (List.getElem_mem hk)) (n + k) (by omega)
      refine ⟨a, ha, b, hb, fun t ht => ?_⟩
      rw [hmem] at ht
      obtain ⟨r, hr, hlt, hs⟩ := gate_sep C k hk hop _ _ ht.2
      rw [Finset.mem_union, hmem, hmem]
      rcases hab r hr hlt with rfl | rfl
      · exact Or.inl ⟨ht.1, hs⟩
      · exact Or.inr ⟨ht.1, hs⟩) R
  have hT : T ⊆ R.biUnion f := fun t ht => by
    obtain ⟨w, hw, hs⟩ := hR t ht
    exact Finset.mem_biUnion.mpr ⟨w, hw, (hmem w t).mpr ⟨ht, hs⟩⟩
  have h1 := Finset.card_le_card hT
  have h2 : (K.image (n + ·)).card ≤ K.card := Finset.card_image_le
  omega

-- Lemma R, general form. x is below y for the list: pointwise below on the inputs, and every
-- gate that is not AND/OR and is true at x is true at y.
def Below {n : ℕ} (C : Circuit) (x y : Fin n → Bool) : Prop :=
  (∀ v, x v = true → y v = true) ∧
  ∀ k, ∀ hk : k < C.gates.length,
    ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
    value C x (n + k) = true → value C y (n + k) = true

theorem below_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : Below C x y) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h.1 p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact h.2 (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

open Classical in
theorem pencils {n : ℕ} {κ ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (I : Finset κ) (S : κ → Finset ι) (u : ι → Fin n) (hu : Function.Injective u)
    (hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ s ∈ S i, ∀ t ∈ S i, s ∈ S j → t ∈ S j → s = t)
    (E : κ → Finset ι) (hE : ∀ i ∈ I, E i ⊆ S i) (R : κ → Finset ℕ)
    (hR : ∀ i ∈ I, ∀ t ∈ E i, ∃ w ∈ R i, Serves C (fun v => decide (v = u t))
      (fun v => decide (∃ s, s ∉ S i ∧ v = u s)) w) :
    ∑ i ∈ I, (E i).card ≤ ∑ i ∈ I, (R i).card + ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).card := by
  let l : ι → Fin n → Bool := fun t v => decide (v = u t)
  let y : κ → ι → Fin n → Bool := fun i _ v => decide (∃ s, s ∉ S i ∧ v = u s)
  let K : κ → Finset ℕ := fun i => ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).filter
      fun k => Counted C (E i) l (y i) (n + k)
  have hcard : ∀ i ∈ I, (E i).card ≤ (R i).card + (K i).card := fun i hi =>
    ledger C (fun g hg => (hC g hg).2) (E i) l (y i) (K i) (R i) (hR i hi)
      (fun v s _ t _ h1 _ h3 _ => by
        simp only [l, decide_eq_true_eq] at h1 h3
        exact hu (h1.symm.trans h3))
      (fun k hk hc => by
        rcases (hC _ (List.getElem_mem hk)).1 with ho | ho
        · exact Or.inl ⟨ho, fun _ _ _ _ => rfl⟩
        · refine Or.inr (Or.inr ⟨?_, Or.inr ho⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, hk, ho⟩, hc⟩)
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (K i) (K j) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr fun k hki hkj => ?_
    obtain ⟨s, hs, t, ht, hst, hs1, ht1⟩ := (Finset.mem_filter.mp hki).2
    obtain ⟨r, _, _, _, _, hr1, _⟩ := (Finset.mem_filter.mp hkj).2
    have hin : ∀ e, Serves C (l e) (y i e) (n + k) → e ∈ S j := by
      intro e he
      by_contra hne
      have hb : Below C (l e) (y j r) := by
        refine ⟨fun v hv => ?_, fun m hm hno => absurd (hC _ (List.getElem_mem hm)).1 hno⟩
        simp only [l, decide_eq_true_eq] at hv
        simp only [y, decide_eq_true_eq]
        exact ⟨e, hne, hv⟩
      have := below_mono C _ _ hb (n + k) he.1
      rw [hr1.2] at this
      exact Bool.noConfusion this
    exact hst (hS i hi j hj hij s (hE i hi hs) t (hE i hi ht) (hin s hs1) (hin t ht1))
  have h1 : (I.biUnion K).card ≤ ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).card :=
    Finset.card_le_card fun k hk => by
      obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.mp hk
      exact (Finset.mem_filter.mp hki).1
  rw [Finset.card_biUnion hdisj] at h1
  have h2 := Finset.sum_le_sum hcard
  rw [Finset.sum_add_distrib] at h2
  omega

open PEqualNP.MetaComplexity.NestedCover

lemma value_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ)
    (hw : value C x w = true) : value C y w = true :=
  below_mono C x y ⟨h, fun _ hk hno => absurd (hC _ (List.getElem_mem hk)).1 hno⟩ w hw

def pt {N : ℕ} (p : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)

def ln {N : ℕ} (l : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)

lemma cast_ne {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

lemma pt_cast {N : ℕ} (p p' : Fin N) : pt p (Fin.castAdd N p') = true ↔ p' = p := by
  simp only [pt, decide_eq_true_eq]
  exact (Fin.castAdd_injective N N).eq_iff

lemma pt_nat {N : ℕ} (p l : Fin N) : pt p (Fin.natAdd N l) = true ↔ False := by
  simp only [pt, decide_eq_true_eq, iff_false]
  exact (cast_ne p l).symm

lemma ln_nat {N : ℕ} (l l' : Fin N) : ln l (Fin.natAdd N l') = true ↔ l' = l := by
  simp only [ln, decide_eq_true_eq]
  exact (Fin.natAdd_injective N N).eq_iff

lemma ln_cast {N : ℕ} (l p : Fin N) : ln l (Fin.castAdd N p) = true ↔ False := by
  simp only [ln, decide_eq_true_eq, iff_false]
  exact cast_ne p l

-- gate j is an AND with inputs a and c, sound, with a on at p and c on at l
def Wit {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (j a c : ℕ) (p l : Fin N) : Prop :=
  (∃ hj : j < C.gates.length, C.gates[j].op = GateOp.and) ∧ a ∈ (gateAt C j).inputs ∧
  c ∈ (gateAt C j).inputs ∧ (∀ r ∈ (gateAt C j).inputs, r = a ∨ r = c) ∧
  (∀ x x' : Fin (N + N) → Bool, value C x a = true → value C x' c = true →
    ∃ p0 l0 : Fin N, I p0 l0 ∧ (x (Fin.castAdd N p0) = true ∨ x' (Fin.castAdd N p0) = true) ∧
      (x (Fin.natAdd N l0) = true ∨ x' (Fin.natAdd N l0) = true)) ∧
  value C (pt p) a = true ∧ value C (ln l) c = true

-- the points (lines) at which some input wire of gate j is on
def PA {N : ℕ} (C : Circuit) (j : ℕ) : Set (Fin N) :=
  {p | ∃ r ∈ (gateAt C j).inputs, value C (pt p) r = true}

def LB {N : ℕ} (C : Circuit) (j : ℕ) : Set (Fin N) :=
  {l | ∃ r ∈ (gateAt C j).inputs, value C (ln l) r = true}

lemma wit_pa {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (p' : Fin N) (hp : p' ∈ PA C j) : value C (pt p') a = true := by
  obtain ⟨-, -, -, hall, hs, hpa, -⟩ := h
  obtain ⟨r, hr, hv⟩ := hp
  rcases hall r hr with rfl | rfl
  · exact hv
  · obtain ⟨p0, l0, -, -, h2⟩ := hs (pt p) (pt p') hpa hv
    simp only [pt_nat, or_self] at h2

lemma wit_lb {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (l' : Fin N) (hl : l' ∈ LB C j) : value C (ln l') c = true := by
  obtain ⟨-, -, -, hall, hs, -, hlc⟩ := h
  obtain ⟨r, hr, hv⟩ := hl
  rcases hall r hr with rfl | rfl
  · obtain ⟨p0, l0, -, h1, -⟩ := hs (ln l') (ln l) hv hlc
    simp only [ln_cast, or_self] at h1
  · exact hv

lemma wit_inc {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (p' l' : Fin N) (hp : p' ∈ PA C j) (hl : l' ∈ LB C j) : I p' l' := by
  obtain ⟨p0, l0, hI, h1, h2⟩ := h.2.2.2.2.1 _ _ (wit_pa h p' hp) (wit_lb h l' hl)
  simp only [pt_cast, pt_nat, ln_cast, ln_nat, or_false, false_or] at h1 h2
  subst h1; subst h2
  exact hI

open Classical in
theorem stars (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hI : ∀ p p' l l', p ≠ p' → I p l → I p' l → I p l' → I p' l' → l = l') :
    {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j a c, Wit I C j a c e.1 e.2}.ncard ≤
      2 * C.gates.length := by
  let A : Finset ℕ := (Finset.range C.gates.length).filter
    fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.and
  let O : Finset ℕ := (Finset.range C.gates.length).filter
    fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or
  have hAO : A.card + O.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint]
    · calc (A ∪ O).card ≤ (Finset.range C.gates.length).card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
            (Finset.filter_subset _ _))
        _ = _ := Finset.card_range _
    · refine Finset.disjoint_left.mpr fun k h1 h2 => ?_
      obtain ⟨_, e1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, e2⟩ := (Finset.mem_filter.mp h2).2
      rw [e1] at e2
      exact GateOp.noConfusion e2
  let J1 : Fin N → Finset ℕ := fun p => A.filter fun j => PA C j = {p}
  let J2 : Fin N → Finset ℕ := fun l => A.filter fun j =>
    LB C j = {l} ∧ ¬ ∃ p : Fin N, PA C j = {p}
  let R1 : Fin N → Finset ℕ := fun p => (J1 p).biUnion fun j => (gateAt C j).inputs.toFinset
  let R2 : Fin N → Finset ℕ := fun l => (J2 l).biUnion fun j => (gateAt C j).inputs.toFinset
  let E1 : Fin N → Finset (Fin N) := fun p => Finset.univ.filter fun l =>
    I p l ∧ ∃ j a c, Wit I C j a c p l ∧ PA C j = {p}
  let E2 : Fin N → Finset (Fin N) := fun l => Finset.univ.filter fun p =>
    I p l ∧ ∃ j a c, Wit I C j a c p l ∧ LB C j = {l} ∧ ¬ ∃ p' : Fin N, PA C j = {p'}
  have hfan : ∀ j, (gateAt C j).inputs.toFinset.card ≤ 2 := by
    intro j
    refine (List.toFinset_card_le _).trans ?_
    by_cases hj : j < C.gates.length
    · have : gateAt C j = C.gates[j] := by simp [gateAt, hj]
      rw [this]
      exact (hC _ (List.getElem_mem hj)).2
    · simp [gateAt, hj]
  have hR1 : ∀ p, (R1 p).card ≤ 2 * (J1 p).card := fun p => by
    rw [mul_comm]
    exact Finset.card_biUnion_le_card_mul _ _ _ fun j _ => hfan j
  have hR2 : ∀ l, (R2 l).card ≤ 2 * (J2 l).card := fun l => by
    rw [mul_comm]
    exact Finset.card_biUnion_le_card_mul _ _ _ fun j _ => hfan j
  have hA : ∀ {j a c p l}, Wit I C j a c p l → j ∈ A := fun h => by
    obtain ⟨hj, ho⟩ := h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, ho⟩
  have b1 := pencils C hC Finset.univ (fun p : Fin N => Finset.univ.filter fun l => I p l)
    (fun l : Fin N => Fin.natAdd N l) (Fin.natAdd_injective N N)
    (by
      intro p _ p' _ hp s hs t ht hs' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht hs' ht'
      exact hI p p' s t hp hs hs' ht ht')
    E1
    (fun p _ l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩)
    R1 (by
      intro p _ l hl
      obtain ⟨-, -, j, a, c, hw, hP⟩ := Finset.mem_filter.mp hl
      refine ⟨c, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hA hw, hP⟩,
        List.mem_toFinset.mpr hw.2.2.1⟩, hw.2.2.2.2.2.2, ?_⟩
      by_contra hne
      obtain ⟨p0, l0, h0, h1, h2⟩ := hw.2.2.2.2.1 (pt p) _ hw.2.2.2.2.2.1
        (Bool.not_eq_false _ ▸ hne)
      simp only [pt_cast, pt_nat, decide_eq_true_eq, false_or, Finset.mem_filter,
        Finset.mem_univ, true_and] at h1 h2
      obtain ⟨s, hs, he⟩ := h2
      rw [← (Fin.natAdd_injective N N) he] at hs
      rcases h1 with rfl | ⟨t, _, ht⟩
      · exact hs h0
      · exact cast_ne _ _ ht)
  have b2 := pencils C hC Finset.univ (fun l : Fin N => Finset.univ.filter fun p => I p l)
    (fun p : Fin N => Fin.castAdd N p) (Fin.castAdd_injective N N)
    (by
      intro l _ l' _ hl s hs t ht hs' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht hs' ht'
      by_contra hst
      exact hl (hI s t l l' hst hs ht hs' ht'))
    E2
    (fun p _ l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩)
    R2 (by
      intro l _ p hp
      obtain ⟨-, -, j, a, c, hw, hP⟩ := Finset.mem_filter.mp hp
      refine ⟨a, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hA hw, hP⟩,
        List.mem_toFinset.mpr hw.2.1⟩, hw.2.2.2.2.2.1, ?_⟩
      by_contra hne
      obtain ⟨p0, l0, h0, h1, h2⟩ := hw.2.2.2.2.1 _ (ln l) (Bool.not_eq_false _ ▸ hne)
        hw.2.2.2.2.2.2
      simp only [ln_cast, ln_nat, decide_eq_true_eq, or_false, Finset.mem_filter,
        Finset.mem_univ, true_and] at h1 h2
      obtain ⟨s, hs, he⟩ := h1
      rw [← (Fin.castAdd_injective N N) he] at hs
      rcases h2 with ⟨t, _, ht⟩ | rfl
      · exact cast_ne _ _ ht.symm
      · exact hs h0)
  have hJ : ∑ p, (J1 p).card + ∑ l, (J2 l).card ≤ A.card := by
    rw [← Finset.card_biUnion, ← Finset.card_biUnion, ← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (Finset.union_subset ?_ ?_) <;>
      · refine Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _
    · refine Finset.disjoint_left.mpr fun j h1 h2 => ?_
      obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp h2
      exact (Finset.mem_filter.mp hl).2.2 ⟨p, (Finset.mem_filter.mp hp).2⟩
    · intro l _ l' _ hne
      refine Finset.disjoint_left.mpr fun j h1 h2 => hne ?_
      exact Set.singleton_injective
        ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
    · intro p _ p' _ hne
      refine Finset.disjoint_left.mpr fun j h1 h2 => hne ?_
      exact Set.singleton_injective
        ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hsub : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j a c, Wit I C j a c e.1 e.2} ⊆
      (((Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l)) ∪
        (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l)) :
          Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    rintro ⟨p, l⟩ ⟨he, j, a, c, hw⟩
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image]
    have hp : p ∈ PA C j := ⟨a, hw.2.1, hw.2.2.2.2.2.1⟩
    have hl : l ∈ LB C j := ⟨c, hw.2.2.1, hw.2.2.2.2.2.2⟩
    by_cases h1 : ∃ p' : Fin N, PA C j = {p'}
    · obtain ⟨p', hp'⟩ := h1
      have : p = p' := by rw [hp'] at hp; exact hp
      subst this
      exact Or.inl ⟨p, l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, j, a, c, hw, hp'⟩, rfl⟩
    · refine Or.inr ⟨l, p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, j, a, c, hw, ?_, h1⟩, rfl⟩
      obtain ⟨p', hp', hne⟩ : ∃ p', p' ∈ PA C j ∧ p' ≠ p := by
        by_contra hcon
        push Not at hcon
        exact h1 ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, hcon⟩⟩
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hl, fun l' hl' => ?_⟩
      exact hI p' p l' l hne (wit_inc hw p' l' hp' hl') (wit_inc hw p l' hp hl')
        (wit_inc hw p' l hp' hl) (wit_inc hw p l hp hl)
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  have c1 : (Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l)).card ≤
      ∑ p, (E1 p).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => Finset.card_image_le)
  have c2 : (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l)).card ≤
      ∑ l, (E2 l).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => Finset.card_image_le)
  have c3 := Finset.card_union_le (Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l))
    (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l))
  have d1 : ∑ p, (R1 p).card ≤ 2 * ∑ p, (J1 p).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hR1 p
  have d2 : ∑ l, (R2 l).card ≤ 2 * ∑ l, (J2 l).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hR2 p
  change ∑ p, (E1 p).card ≤ ∑ p, (R1 p).card + O.card at b1
  change ∑ p, (E2 p).card ≤ ∑ p, (R2 p).card + O.card at b2
  omega

lemma wit_of {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hb : ReadsBack (N + N) C) (j a c : ℕ) (p l : Fin N) (hj : j < C.gates.length)
    (ho : (gateAt C j).op = GateOp.and)
    (hi : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hs : ∀ z : Fin (N + N) → Bool, value C z (N + N + j) = true →
      ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true)
    (hp : value C (pt p) a = true) (hl : value C (ln l) c = true) : Wit I C j a c p l := by
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  have hmem : ∀ r, r ∈ (gateAt C j).inputs ↔ r = a ∨ r = c := by
    intro r
    rcases hi with h | h <;> rw [h] <;> simp [or_comm]
  refine ⟨⟨hj, hg ▸ ho⟩, (hmem a).mpr (Or.inl rfl), (hmem c).mpr (Or.inr rfl),
    fun r hr => (hmem r).mp hr, fun x x' hx hx' => ?_, hp, hl⟩
  have hv : value C (fun k => x k || x' k) (N + N + j) = true := by
    rw [and_val C j hj (hg ▸ ho)]
    intro r hr
    rw [← hg] at hr
    refine ⟨hb j hj r hr, ?_⟩
    rcases (hmem r).mp hr with rfl | rfl
    · exact value_mono C hC x _ (fun v h => by simp [h]) _ hx
    · exact value_mono C hC x' _ (fun v h => by simp [h]) _ hx'
  obtain ⟨p0, l0, h0, h1, h2⟩ := hs _ hv
  exact ⟨p0, l0, h0, by simpa using h1, by simpa using h2⟩

end PEqualNP.Outside.L_meta_2838

theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  intro q N I _ C _ _ _ hI hM hb _ _
  have hC : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨(hM g hg).1, (hM g hg).2⟩
  have key := PEqualNP.Outside.L_meta_2838.stars N I C hC
    (fun p p' l l' hp h1 h2 h3 h4 => (hI p p' hp).unique ⟨h1, h2⟩ ⟨h3, h4⟩)
  refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans (key.trans ?_)
  · rintro e ⟨he, j, hj, a, c, ho, hi, hs, hp, hl⟩
    exact ⟨he, j, a, c,
      PEqualNP.Outside.L_meta_2838.wit_of I C hC hb j a c e.1 e.2 hj ho hi hs hp hl⟩
  · unfold PEqualNP.CircuitLowerBounds.Circuit.size
    omega
