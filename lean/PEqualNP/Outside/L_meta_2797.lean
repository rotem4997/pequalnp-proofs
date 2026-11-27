import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2797

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.Core

-- One pass over the gates, each gate appending one value.
def run {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) : List α :=
  gs.foldl (fun R g => R ++ [step R g]) R

lemma run_length {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) :
    (run step R gs).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp [run]
  | cons g gs ih =>
    have := ih (R ++ [step R g])
    simp only [run, List.foldl_cons, List.length_cons] at this ⊢
    rw [this]
    simp
    omega

lemma run_old {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) (d : α) (i : ℕ)
    (hi : i < R.length) : (run step R gs).getD i d = R.getD i d := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    have := ih (R ++ [step R g]) (by simp; omega)
    simp only [run, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ hi]

lemma run_new {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) (d : α) (j : ℕ)
    (hj : j < gs.length) :
    ∃ P : List α, (run step R gs).getD (R.length + j) d = step P gs[j] ∧
      ∀ i < R.length + j, P.getD i d = (run step R gs).getD i d := by
  induction gs generalizing R j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      refine ⟨R, ?_, fun i hi => (run_old step R _ d i (by omega)).symm⟩
      have := run_old step (R ++ [step R g]) gs d R.length (by simp)
      simp only [run, List.foldl_cons, Nat.add_zero] at this ⊢
      rw [this, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    | succ j =>
      obtain ⟨P, h1, h2⟩ := ih (R ++ [step R g]) j (by simpa using hj)
      have hlen : (R ++ [step R g]).length + j = R.length + (j + 1) := by simp; omega
      rw [hlen] at h1 h2
      exact ⟨P, h1, h2⟩

def sB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma two (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) := by
  have h2 := hC.2.2 C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have hr := hC.2.1 j hj
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  rw [hg, hab] at hr
  exact ⟨a, b, hab, hr a (by simp), hr b (by simp), hC.1 _ (List.getElem_mem hj)⟩

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]

lemma wval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    wval C x (n + j) = C.gates[j].op.eval [wval C x a, wval C x b] := by
  obtain ⟨P, h1, h2⟩ := run_new sB (List.ofFn x) C.gates false j hj
  rw [List.length_ofFn] at h1 h2
  change (run sB (List.ofFn x) C.gates).getD (n + j) false = _
  rw [h1]
  unfold sB
  rw [hab]
  simp only [List.map_cons, List.map_nil]
  rw [h2 a ha, h2 b hb]
  rfl

lemma wval_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.and) : wval C x (n + j) = (wval C x a && wval C x b) := by
  rw [wval_gate C x j a b hj hab ha hb, ho]
  simp [GateOp.eval]

lemma wval_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.or) : wval C x (n + j) = (wval C x a || wval C x b) := by
  rw [wval_gate C x j a b hj hab ha hb, ho]
  simp [GateOp.eval]

lemma wval_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) : wval C x i = x i := by
  change (run sB (List.ofFn x) C.gates).getD i false = _
  rw [run_old _ _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma wval_past {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  change (run sB (List.ofFn x) C.gates).getD w false = _
  rw [List.getD_eq_default]
  rw [run_length]; simpa using hw

theorem merge_count {τ : Type*} [DecidableEq τ] (f : ℕ → Finset τ) (B : Finset ℕ)
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


variable {n : ℕ}

def zr (Z : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool := fun i => if i ∈ Z then false else x i

def fv (C : Circuit) (Z : Finset (Fin n)) (w : ℕ) (x : Fin n → Bool) : Bool := wval C (zr Z x) w

def Mg (C : Circuit) (Z : Finset (Fin n)) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ a < n + j, fv C Z (n + j) ≠ fv C Z a) ∧ fv C Z (n + j) ≠ fun _ => false

lemma fv_in (C : Circuit) (Z : Finset (Fin n)) (i : Fin n) (hi : i ∉ Z) : fv C Z i = fun x => x i := by
  funext x
  unfold fv
  rw [wval_in]
  unfold zr
  rw [ite_eq_right hi]

lemma fv_in0 (C : Circuit) (Z : Finset (Fin n)) (i : Fin n) (hi : i ∈ Z) : fv C Z i = fun _ => false := by
  funext x
  unfold fv
  rw [wval_in]
  unfold zr
  rw [ite_eq_left hi]

lemma fv_past (C : Circuit) (Z : Finset (Fin n)) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    fv C Z w = fun _ => false := by
  funext x
  exact wval_past C _ w hw

lemma fv_insert (C : Circuit) (Z : Finset (Fin n)) (a : Fin n) (w : ℕ) :
    fv C (insert a Z) w = fun x => fv C Z w (zr {a} x) := by
  funext x
  unfold fv
  congr 1
  funext i
  unfold zr
  by_cases h1 : i ∈ Z <;> by_cases h2 : i = a <;> simp [h1, h2]

lemma Mg_mono (C : Circuit) (Z : Finset (Fin n)) (a : Fin n) (j : ℕ) (h : Mg C (insert a Z) j) : Mg C Z j := by
  refine ⟨h.1, ?_, ?_⟩
  · intro b hb e
    refine h.2.1 b hb ?_
    rw [fv_insert, fv_insert, e]
  · intro e
    refine h.2.2 ?_
    rw [fv_insert, e]

lemma fv_and (C : Circuit) (Z : Finset (Fin n)) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.and) (x : Fin n → Bool) :
    fv C Z (n + j) x = (fv C Z a x && fv C Z b x) := wval_and C _ j a b hj hab ha hb ho

lemma fv_or (C : Circuit) (Z : Finset (Fin n)) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.or) (x : Fin n → Bool) :
    fv C Z (n + j) x = (fv C Z a x || fv C Z b x) := wval_or C _ j a b hj hab ha hb ho

-- a gate with a false operand is not merging
lemma kill (C : Circuit) (hC : IsAO2 n C) (Z : Finset (Fin n)) (j : ℕ) (hj : j < C.gates.length) (c : ℕ)
    (hc : c ∈ C.gates[j].inputs) (h0 : fv C Z c = fun _ => false) : ¬ Mg C Z j := by
  rintro ⟨_, h1, h2⟩
  obtain ⟨a, b, hab, ha, hb, hop⟩ := two n C hC j hj
  rw [hab] at hc
  have hc : c = a ∨ c = b := by simpa using hc
  rcases hop with ho | ho
  · refine h2 (funext fun x => ?_)
    rw [fv_and C Z j a b hj hab ha hb ho]
    rcases hc with rfl | rfl
    · rw [h0]; rfl
    · rw [h0, Bool.and_false]
  · rcases hc with rfl | rfl
    · refine h1 b hb (funext fun x => ?_)
      rw [fv_or C Z j c b hj hab ha hb ho, h0]; rfl
    · refine h1 a ha (funext fun x => ?_)
      rw [fv_or C Z j a c hj hab ha hb ho, h0, Bool.or_false]

def mk2 (u v : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v)

section
variable (R : Fin n → Fin n → Prop) (C : Circuit)

open Classical in
lemma step (hC : IsAO2 n C) (hsym : ∀ u v, R u v → R v u) (hirr : ∀ u, ¬ R u u)
    (hF : ∀ x : Fin n → Bool, wval C x C.output = true ↔ ∃ u v, R u v ∧ x u = true ∧ x v = true)
    (Z : Finset (Fin n)) (hex : ∃ u v, u ∉ Z ∧ v ∉ Z ∧ R u v)
    (hH : ∀ u v, u ∉ Z → v ∉ Z → u ≠ v → ∃ d, R u d ∧ ¬ R v d ∧ d ≠ v ∧ d ∉ Z) :
    ∃ a, a ∉ Z ∧ ∃ r r', r ≠ r' ∧ Mg C Z r ∧ Mg C Z r' ∧ ¬ Mg C (insert a Z) r ∧ ¬ Mg C (insert a Z) r' := by
  -- values of the output at small inputs
  have out1 : ∀ u v, u ∉ Z → v ∉ Z → R u v → fv C Z C.output (mk2 u v) = true := by
    intro u v hu hv huv
    refine (hF _).mpr ⟨u, v, huv, ?_, ?_⟩
    · unfold zr; rw [ite_eq_right hu]; simp [mk2]
    · unfold zr; rw [ite_eq_right hv]; simp [mk2]
  have out0 : ∀ u v, ¬ R u v → fv C Z C.output (mk2 u v) = false := by
    intro u v huv
    by_contra hne
    have h : fv C Z C.output (mk2 u v) = true := by simpa using hne
    obtain ⟨c, d, hcd, hc, hd⟩ := (hF _).mp h
    have sub : ∀ i, zr Z (mk2 u v) i = true → i = u ∨ i = v := by
      intro i hi
      unfold zr at hi
      split at hi
      · cases hi
      · exact of_decide_eq_true hi
    rcases sub c hc with rfl | rfl <;> rcases sub d hd with rfl | rfl
    · exact hirr _ hcd
    · exact huv hcd
    · exact huv (hsym _ _ hcd)
    · exact hirr _ hcd
  have noP : ¬ (fv C Z C.output = (fun _ => false)) := by
    intro e
    obtain ⟨u, v, hu, hv, huv⟩ := hex
    have := out1 u v hu hv huv
    rw [e] at this; cases this
  have noI : ∀ i, ¬ (fv C Z C.output = fun x => x i) := by
    intro i e
    have := out0 i i (hirr i)
    rw [e] at this
    simp [mk2] at this
  let P : ℕ → Prop := fun w => fv C Z w = (fun _ => false) ∨ ∃ i : Fin n, i ∉ Z ∧ fv C Z w = fun x => x i
  have low : ∀ K, (∀ j < K, ¬ Mg C Z j) → ∀ w, w < n + K → P w := by
    intro K hK w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hlt : w < n
      · by_cases hz : (⟨w, hlt⟩ : Fin n) ∈ Z
        · exact Or.inl (fv_in0 C Z ⟨w, hlt⟩ hz)
        · exact Or.inr ⟨⟨w, hlt⟩, hz, fv_in C Z ⟨w, hlt⟩ hz⟩
      · by_cases hge : n + C.gates.length ≤ w
        · exact Or.inl (fv_past C Z w hge)
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hc : fv C Z (n + j) = fun _ => false
        · exact Or.inl hc
        have hnM := hK j (by omega)
        have : ∃ a < n + j, fv C Z (n + j) = fv C Z a := by
          by_contra hno
          push Not at hno
          exact hnM ⟨hj, hno, hc⟩
        obtain ⟨a, ha, e⟩ := this
        have := ih a ha (by omega)
        change fv C Z (n + j) = _ ∨ _
        rw [e]; exact this
  have hexM : ∃ j, Mg C Z j := by
    by_contra hno
    push Not at hno
    rcases low (C.output + 1) (fun j _ => hno j) C.output (by omega) with e | ⟨i, _, e⟩
    · exact noP e
    · exact noI i e
  let r := Nat.find hexM
  have hr : Mg C Z r := Nat.find_spec hexM
  have hrl : r < C.gates.length := hr.1
  have hlow := low r (fun j hj => Nat.find_min hexM hj)
  obtain ⟨a, b, hab, ha, hb, hop⟩ := two n C hC r hr.1
  have ma : a ∈ C.gates[r].inputs := by rw [hab]; simp
  have mb : b ∈ C.gates[r].inputs := by rw [hab]; simp
  obtain ⟨u, huZ, hu⟩ := (hlow a ha).resolve_left fun e => kill C hC Z r hr.1 a ma e hr
  obtain ⟨v, hvZ, hv⟩ := (hlow b hb).resolve_left fun e => kill C hC Z r hr.1 b mb e hr
  have huv : u ≠ v := by
    rintro rfl
    refine hr.2.1 a ha (funext fun x => ?_)
    rcases hop with ho | ho
    · rw [fv_and C Z r a b hr.1 hab ha hb ho, hu, hv, Bool.and_self]
    · rw [fv_or C Z r a b hr.1 hab ha hb ho, hu, hv, Bool.or_self]
  -- another merging gate reads a copy of u or v
  have hother : ∃ r', r' ≠ r ∧ ∃ hM : Mg C Z r', ∃ c ∈ (C.gates[r']'hM.1).inputs,
      fv C Z c = (fun x => x u) ∨ fv C Z c = fun x => x v := by
    by_contra hno
    let Fac : ℕ → Prop := fun w => ∀ x y : Fin n → Bool, (∀ i, i ≠ u → i ≠ v → x i = y i) →
      fv C Z (n + r) x = fv C Z (n + r) y → fv C Z w x = fv C Z w y
    have fac : ∀ w, fv C Z w = (fun x => x u) ∨ fv C Z w = (fun x => x v) ∨ Fac w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        by_cases hlt : w < n
        · by_cases hz : (⟨w, hlt⟩ : Fin n) ∈ Z
          · have e := fv_in0 C Z ⟨w, hlt⟩ hz
            simp only at e
            refine Or.inr (Or.inr fun x y _ _ => ?_)
            rw [e]
          · have e := fv_in C Z ⟨w, hlt⟩ hz
            simp only at e
            by_cases h1 : (⟨w, hlt⟩ : Fin n) = u
            · left; rw [e, h1]
            by_cases h2 : (⟨w, hlt⟩ : Fin n) = v
            · right; left; rw [e, h2]
            refine Or.inr (Or.inr fun x y hxy _ => ?_)
            rw [e]; exact hxy _ h1 h2
        · by_cases hge : n + C.gates.length ≤ w
          · refine Or.inr (Or.inr fun x y _ _ => ?_)
            rw [fv_past C Z w hge]
          obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < C.gates.length := by omega
          by_cases hjr : j = r
          · subst hjr
            exact Or.inr (Or.inr fun x y _ h => h)
          by_cases hM : Mg C Z j
          · obtain ⟨c, d, hcd, hc, hd, hop'⟩ := two n C hC j hj
            have nc : ∀ t, t ∈ C.gates[j].inputs → t < n + j → Fac t := by
              intro t ht htj
              rcases ih t htj with e | e | e
              · exact (hno ⟨j, hjr, hM, t, ht, Or.inl e⟩).elim
              · exact (hno ⟨j, hjr, hM, t, ht, Or.inr e⟩).elim
              · exact e
            have f1 := nc c (by rw [hcd]; simp) hc
            have f2 := nc d (by rw [hcd]; simp) hd
            refine Or.inr (Or.inr fun x y hxy hr' => ?_)
            rcases hop' with ho | ho
            · rw [fv_and C Z j c d hj hcd hc hd ho, fv_and C Z j c d hj hcd hc hd ho, f1 x y hxy hr',
                f2 x y hxy hr']
            · rw [fv_or C Z j c d hj hcd hc hd ho, fv_or C Z j c d hj hcd hc hd ho, f1 x y hxy hr',
                f2 x y hxy hr']
          · by_cases hcst : fv C Z (n + j) = fun _ => false
            · refine Or.inr (Or.inr fun x y _ _ => ?_)
              rw [hcst]
            have : ∃ t < n + j, fv C Z (n + j) = fv C Z t := by
              by_contra hno'
              push Not at hno'
              exact hM ⟨hj, hno', hcst⟩
            obtain ⟨t, ht, e⟩ := this
            have h := ih t ht
            change _ ∨ _ ∨ (∀ x y : Fin n → Bool, _ → _ → fv C Z (n + j) x = fv C Z (n + j) y)
            rw [e]; exact h
    rcases fac C.output with e | e | e
    · exact noI u e
    · exact noI v e
    · obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hH u v huZ hvZ huv
      have hdu : d ≠ u := by rintro rfl; exact hirr _ hd1
      have t1 := out1 u d huZ hd4 hd1
      rcases hop with ho | ho
      · have t0 := out0 d d (hirr d)
        have := e (mk2 u d) (mk2 d d) (by
          intro i h1 _
          simp [mk2, h1]) (by
          rw [fv_and C Z r a b hr.1 hab ha hb ho, fv_and C Z r a b hr.1 hab ha hb ho, hu, hv]
          simp [mk2, hdu.symm, hd3.symm, huv.symm])
        rw [t1, t0] at this; cases this
      · have t0 := out0 v d hd2
        have := e (mk2 u d) (mk2 v d) (by
          intro i h1 h2
          simp [mk2, h1, h2]) (by
          rw [fv_or C Z r a b hr.1 hab ha hb ho, fv_or C Z r a b hr.1 hab ha hb ho, hu, hv]
          simp [mk2])
        rw [t1, t0] at this; cases this
  obtain ⟨r', hne, hM', c, hc, hcu⟩ := hother
  have zero : ∀ i t, fv C Z t = (fun x => x i) → fv C (insert i Z) t = fun _ => false := by
    intro i t e
    rw [fv_insert, e]
    funext x
    simp [zr]
  rcases hcu with e | e
  · exact ⟨u, huZ, r, r', hne.symm, hr, hM', kill C hC _ r hr.1 a ma (zero u a hu),
      kill C hC _ r' hM'.1 c hc (zero u c e)⟩
  · exact ⟨v, hvZ, r, r', hne.symm, hr, hM', kill C hC _ r hr.1 b mb (zero v b hv),
      kill C hC _ r' hM'.1 c hc (zero v c e)⟩

open Classical in
noncomputable def ess (Z : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ x y : Fin n → Bool, (∀ i, i ≠ u → x i = y i) ∧ fv C Z w x ≠ fv C Z w y

open Classical in
noncomputable def MG (Z : Finset (Fin n)) : Finset ℕ := (Finset.range C.gates.length).filter (Mg C Z)

lemma mem_MG (Z : Finset (Fin n)) (j : ℕ) : j ∈ MG C Z ↔ Mg C Z j := by
  classical
  unfold MG
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma ess_le (hC : IsAO2 n C) (Z : Finset (Fin n)) (w : ℕ) : (ess C Z w).card ≤ 1 + (MG C Z).card := by
  classical
  have key := merge_count (ess C Z) ((MG C Z).image (n + ·)) (by
    intro w hw
    have hne : ¬ (fv C Z w = fun _ => false) := by
      intro e
      have : ess C Z w = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        obtain ⟨x, y, _, h⟩ := (Finset.mem_filter.mp hu).2
        rw [e] at h; exact h rfl
      rw [this] at hw; simp at hw
    by_cases hlt : w < n
    · exfalso
      have hz : (⟨w, hlt⟩ : Fin n) ∉ Z := fun hz => hne (fv_in0 C Z ⟨w, hlt⟩ hz)
      have e := fv_in C Z ⟨w, hlt⟩ hz
      simp only at e
      have : ess C Z w ⊆ {⟨w, hlt⟩} := by
        intro u hu
        obtain ⟨x, y, hxy, h⟩ := (Finset.mem_filter.mp hu).2
        rw [Finset.mem_singleton]
        by_contra hcon
        rw [e] at h
        exact h (hxy _ fun h => hcon h.symm)
      have := Finset.card_le_card this
      simp at this
      omega
    · have hge : w < n + C.gates.length := by
        by_contra hge
        exact hne (fv_past C Z w (by omega))
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hM : Mg C Z j
      · right
        refine ⟨Finset.mem_image_of_mem _ ((mem_MG C Z j).mpr hM), ?_⟩
        obtain ⟨a, b, hab, ha, hb, hop⟩ := two n C hC j hj
        refine ⟨a, ha, b, hb, ?_⟩
        intro u hu
        obtain ⟨x, y, hxy, h⟩ := (Finset.mem_filter.mp hu).2
        rw [Finset.mem_union]
        by_contra hcon
        have na : fv C Z a x = fv C Z a y := by
          by_contra h'
          exact hcon (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, y, hxy, h'⟩))
        have nb : fv C Z b x = fv C Z b y := by
          by_contra h'
          exact hcon (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, y, hxy, h'⟩))
        rcases hop with ho | ho
        · rw [fv_and C Z j a b hj hab ha hb ho, fv_and C Z j a b hj hab ha hb ho, na, nb] at h
          exact h rfl
        · rw [fv_or C Z j a b hj hab ha hb ho, fv_or C Z j a b hj hab ha hb ho, na, nb] at h
          exact h rfl
      · left
        have : ∃ t < n + j, fv C Z (n + j) = fv C Z t := by
          by_contra hno
          push Not at hno
          exact hM ⟨hj, hno, hne⟩
        obtain ⟨t, ht, e⟩ := this
        refine ⟨t, ht, ?_⟩
        unfold ess
        rw [e]) {w}
  rw [Finset.singleton_biUnion, Finset.card_singleton] at key
  exact key.trans (Nat.add_le_add_left Finset.card_image_le _)

theorem lower (hC : IsAO2 n C) (hsym : ∀ u v, R u v → R v u) (hirr : ∀ u, ¬ R u u)
    (hF : ∀ x : Fin n → Bool, wval C x C.output = true ↔ ∃ u v, R u v ∧ x u = true ∧ x v = true)
    (u0 v0 : Fin n) (huv0 : u0 ≠ v0)
    (hH : ∀ u v z, u ≠ v → ∃ d, R u d ∧ ¬ R v d ∧ d ≠ v ∧ d ≠ z) : n + 1 ≤ C.gates.length := by
  classical
  have card_step : ∀ Z : Finset (Fin n), ∀ a r r', r ≠ r' → Mg C Z r → Mg C Z r' → ¬ Mg C (insert a Z) r →
      ¬ Mg C (insert a Z) r' → (MG C (insert a Z)).card + 2 ≤ (MG C Z).card := by
    intro Z a r r' hne h1 h2 h3 h4
    have hsub : MG C (insert a Z) ⊆ ((MG C Z).erase r).erase r' := by
      intro j hj
      rw [mem_MG] at hj
      refine Finset.mem_erase.mpr ⟨fun e => h4 (e ▸ hj), Finset.mem_erase.mpr ⟨fun e => h3 (e ▸ hj), ?_⟩⟩
      rw [mem_MG]; exact Mg_mono C Z a j hj
    have c1 := Finset.card_le_card hsub
    have m1 : r ∈ MG C Z := (mem_MG C Z r).mpr h1
    have m2 : r' ∈ (MG C Z).erase r := Finset.mem_erase.mpr ⟨hne.symm, (mem_MG C Z r').mpr h2⟩
    have c2 := Finset.card_erase_add_one m2
    have c3 := Finset.card_erase_add_one m1
    omega
  have other : ∀ z : Fin n, ∃ u, u ≠ z := by
    intro z
    by_cases h : u0 = z
    · exact ⟨v0, fun e => huv0 (h.trans e.symm)⟩
    · exact ⟨u0, h⟩
  obtain ⟨a1, _, r1, r1', hne1, p1, p2, p3, p4⟩ := step R C hC hsym hirr hF ∅ (by
    obtain ⟨d, hd, _⟩ := hH u0 v0 u0 huv0
    exact ⟨u0, d, by simp, by simp, hd⟩) (by
    intro u v _ _ huv
    obtain ⟨d, h1, h2, h3, _⟩ := hH u v u huv
    exact ⟨d, h1, h2, h3, by simp⟩)
  have c1 := card_step ∅ a1 r1 r1' hne1 p1 p2 p3 p4
  obtain ⟨a2, ha2, r2, r2', hne2, q1, q2, q3, q4⟩ := step R C hC hsym hirr hF (insert a1 ∅) (by
    obtain ⟨u, hu⟩ := other a1
    obtain ⟨d, hd, _, _, hdz⟩ := hH u a1 a1 hu
    exact ⟨u, d, by simp [hu], by simp [hdz], hd⟩) (by
    intro u v _ _ huv
    obtain ⟨d, h1, h2, h3, h4⟩ := hH u v a1 huv
    exact ⟨d, h1, h2, h3, by simp [h4]⟩)
  have c2 := card_step (insert a1 ∅) a2 r2 r2' hne2 q1 q2 q3 q4
  have hess : Finset.univ \ {a1, a2} ⊆ ess C (insert a2 (insert a1 ∅)) C.output := by
    intro u hu
    have hu : u ≠ a1 ∧ u ≠ a2 := by simpa using hu
    obtain ⟨d, hd, _, hd1, hd2⟩ := hH u a1 a2 hu.1
    have hdu : d ≠ u := by rintro rfl; exact hirr _ hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, mk2 u d, mk2 d d, ?_, ?_⟩
    · intro i hi
      simp [mk2, hi]
    · have h1 : fv C (insert a2 (insert a1 ∅)) C.output (mk2 u d) = true := by
        refine (hF _).mpr ⟨u, d, hd, ?_, ?_⟩
        · simp [zr, mk2, hu.1, hu.2]
        · simp [zr, mk2, hd1, hd2]
      have h0 : ¬ fv C (insert a2 (insert a1 ∅)) C.output (mk2 d d) = true := by
        intro h
        obtain ⟨c, e, hce, hc, he⟩ := (hF _).mp h
        have sub : ∀ i, zr (insert a2 (insert a1 ∅)) (mk2 d d) i = true → i = d := by
          intro i hi
          unfold zr at hi
          split at hi
          · cases hi
          · have : i = d ∨ i = d := of_decide_eq_true hi
            exact this.elim id id
        rw [sub c hc, sub e he] at hce
        exact hirr _ hce
      rw [h1]
      intro h
      exact h0 h.symm
  have c3 := (Finset.card_le_card hess).trans (ess_le C hC _ _)
  have c4 : n ≤ (Finset.univ \ {a1, a2} : Finset (Fin n)).card + 2 := by
    have h1 := Finset.card_sdiff_add_card (s := (Finset.univ : Finset (Fin n))) (t := {a1, a2})
    have h2 : ({a1, a2} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have h3 := Finset.card_le_card (Finset.subset_union_left (s₁ := (Finset.univ : Finset (Fin n))) (s₂ := {a1, a2}))
    rw [Finset.card_univ, Fintype.card_fin] at h3
    omega
  have c5 : (MG C (∅ : Finset (Fin n))).card ≤ C.gates.length := by
    unfold MG
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega
end

open Configuration Configuration.ProjectivePlane in
open scoped LinearAlgebra.Projectivization in
theorem plane : ∃ (q N : ℕ) (I : Fin N → Fin N → Prop), 201 ≤ q ∧ N = q ^ 2 + q + 1 ∧ q % 2 = 0 ∧
    (∀ l, Nat.card {p // I p l} = q + 1) ∧ (∀ p, Nat.card {l // I p l} = q + 1) ∧
    (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 8
  have : Finite K := inferInstanceAs (Finite (GaloisField 2 8))
  have hK : Nat.card K = 256 := by
    have := GaloisField.card 2 8 (by norm_num)
    rw [this]; norm_num
  let P := ℙ K (Fin 3 → K)
  have : Finite P := inferInstance
  have : Fintype P := Fintype.ofFinite P
  have hP : Nat.card P = 256 ^ 2 + 256 + 1 := by
    have h := Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp)
    rw [hK] at h
    rw [h]
    simp [Finset.sum_range_succ]
  have ho : order P P = 256 := by
    have h := card_points P P
    rw [← Nat.card_eq_fintype_card, hP] at h
    nlinarith [h]
  generalize hq : (256 : ℕ) = q at hP ho
  let e : Fin (Nat.card P) ≃ P := (Finite.equivFin P).symm
  refine ⟨q, Nat.card P, fun p l => e p ∈ e l, by omega, hP, by omega, ?_, ?_, ?_⟩
  · intro l
    have h := pointCount_eq (P := P) (L := P) (e l)
    rw [ho] at h
    rw [← h]
    exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  · intro p
    have h := lineCount_eq (P := P) (L := P) (e p)
    rw [ho] at h
    rw [← h]
    exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  · intro p p' hne
    obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line P P (e p) (e p') (fun h => hne (e.injective h))
    refine ⟨e.symm l, by simpa using hl, ?_⟩
    intro m hm
    rw [Equiv.eq_symm_apply]
    exact hu _ hm

-- in a set of q + 1 at least 4, avoid a set meeting it once and two more elements
lemma avoid {N q : ℕ} (hq : 201 ≤ q) (A B : Fin N → Prop) (hA : Nat.card {x // A x} = q + 1)
    (hAB : ∀ x y, A x → B x → A y → B y → x = y) (Y : Finset (Fin N)) (hY : Y.card ≤ 2) :
    ∃ d, A d ∧ ¬ B d ∧ d ∉ Y := by
  classical
  by_contra hno
  push Not at hno
  have h1 : (Finset.univ.filter A).card = q + 1 := by
    rw [← hA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : Finset.univ.filter A ⊆ Finset.univ.filter (fun x => A x ∧ B x) ∪ Y := by
    intro x hx
    have hx := (Finset.mem_filter.mp hx).2
    by_cases hb : B x
    · exact Finset.mem_union_left _ (by simp [hx, hb])
    · exact Finset.mem_union_right _ (hno x hx hb)
  have h2 : (Finset.univ.filter (fun x => A x ∧ B x)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx := (Finset.mem_filter.mp hx).2
    have hy := (Finset.mem_filter.mp hy).2
    exact hAB x y hx.1 hx.2 hy.1 hy.2
  have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem main : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3], 201 ≤ x1 →
    x2 = x1 ^ 2 + x1 + 1 → (∀ x7 : Fin x2, Fintype.card {x8 : Fin x2 // x3 x8 x7} = x1 + 1) →
    (∀ x8 x9 : Fin x2, x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % 2 = 0 →
    ∃ C : Circuit, IsAO2 (x2 + x2) C ∧ (∀ x : Fin (x2 + x2) → Bool, circuitFun (x2 + x2) C x =
      decide (∃ (p : Fin x2) (l : Fin x2), x3 p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x2 l) = true)) ∧
      C.size ≤ 2 * x2) := by
  classical
  intro H
  obtain ⟨q, N, I, hq, hN, h2, hpl, hlp, hu⟩ := plane
  obtain ⟨C, hC, hF, hsz⟩ := H q N I hq hN (fun l => by rw [← Nat.card_eq_fintype_card]; exact hpl l) hu h2
  let R : Fin (N + N) → Fin (N + N) → Prop := fun u v => ∃ p l, I p l ∧
    ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
  have ne : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.2
    omega
  have ci : ∀ p p' : Fin N, Fin.castAdd N p = Fin.castAdd N p' → p = p' := by
    intro p p' h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd] at this
    exact Fin.ext this
  have ni : ∀ p p' : Fin N, Fin.natAdd N p = Fin.natAdd N p' → p = p' := by
    intro p p' h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  have Rcn : ∀ p l, R (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
    intro p l
    constructor
    · rintro ⟨p', l', h, ⟨e1, e2⟩ | ⟨e1, _⟩⟩
      · rw [ci _ _ e1, ni _ _ e2]; exact h
      · exact (ne _ _ e1).elim
    · intro h
      exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩
  have Rnc : ∀ p l, R (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l := by
    intro p l
    constructor
    · rintro ⟨p', l', h, ⟨e1, _⟩ | ⟨e1, e2⟩⟩
      · exact (ne _ _ e1.symm).elim
      · rw [ni _ _ e1, ci _ _ e2]; exact h
    · intro h
      exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩
  have Rcc : ∀ p p', ¬ R (Fin.castAdd N p) (Fin.castAdd N p') := by
    rintro p p' ⟨_, _, _, ⟨_, e⟩ | ⟨e, _⟩⟩
    · exact ne _ _ e
    · exact ne _ _ e
  have Rnn : ∀ p p', ¬ R (Fin.natAdd N p) (Fin.natAdd N p') := by
    rintro p p' ⟨_, _, _, ⟨e, _⟩ | ⟨_, e⟩⟩
    · exact ne _ _ e.symm
    · exact ne _ _ e.symm
  have hsym : ∀ u v, R u v → R v u := by
    rintro u v ⟨p, l, h, e | e⟩
    · exact ⟨p, l, h, Or.inr ⟨e.2, e.1⟩⟩
    · exact ⟨p, l, h, Or.inl ⟨e.2, e.1⟩⟩
  have cases' : ∀ u : Fin (N + N), (∃ p, u = Fin.castAdd N p) ∨ ∃ l, u = Fin.natAdd N l := by
    intro u
    induction u using Fin.addCases with
    | left p => exact Or.inl ⟨p, rfl⟩
    | right l => exact Or.inr ⟨l, rfl⟩
  have hirr : ∀ u, ¬ R u u := by
    intro u
    rcases cases' u with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · exact Rcc p p
    · exact Rnn l l
  have pre : ∀ z : Fin (N + N), ∃ Yc Yn : Fin N, (∀ d, d ≠ Yc → Fin.castAdd N d ≠ z) ∧
      (∀ d, d ≠ Yn → Fin.natAdd N d ≠ z) := by
    intro z
    rcases cases' z with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · exact ⟨p, p, fun d hd e => hd (ci _ _ e), fun d _ e => ne _ _ e.symm⟩
    · exact ⟨l, l, fun d _ e => ne _ _ e, fun d hd e => hd (ni _ _ e)⟩
  have twoP : ∀ p p', p ≠ p' → ∀ x y, I p x → I p' x → I p y → I p' y → x = y := by
    intro p p' hne x y h1 h2 h3 h4
    exact (hu p p' hne).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have hH : ∀ u v z, u ≠ v → ∃ d, R u d ∧ ¬ R v d ∧ d ≠ v ∧ d ≠ z := by
    intro u v z huv
    obtain ⟨yc, yn, hyc, hyn⟩ := pre z
    rcases cases' u with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;> rcases cases' v with ⟨p', rfl⟩ | ⟨l', rfl⟩
    · obtain ⟨d, h1, h3, h4⟩ := avoid hq (I p) (I p') (hlp p)
        (fun x y a b c d => twoP p p' (fun e => huv (by rw [e])) x y a b c d) {yn} (by simp)
      refine ⟨Fin.natAdd N d, (Rcn _ _).mpr h1, fun h => h3 ((Rcn _ _).mp h), fun e => ne _ _ e.symm,
        hyn d (by simpa using h4)⟩
    · obtain ⟨d, h1, _, h4⟩ := avoid hq (I p) (fun _ => False) (hlp p) (fun _ _ _ h => h.elim) {yn, l'}
        Finset.card_le_two
      have h4 : d ≠ yn ∧ d ≠ l' := by simpa using h4
      exact ⟨Fin.natAdd N d, (Rcn _ _).mpr h1, Rnn _ _, fun e => h4.2 (ni _ _ e), hyn d h4.1⟩
    · obtain ⟨d, h1, _, h4⟩ := avoid hq (fun x => I x l) (fun _ => False) (hpl l) (fun _ _ _ h => h.elim)
        {yc, p'} Finset.card_le_two
      have h4 : d ≠ yc ∧ d ≠ p' := by simpa using h4
      exact ⟨Fin.castAdd N d, (Rnc _ _).mpr h1, Rcc _ _, fun e => h4.2 (ci _ _ e), hyc d h4.1⟩
    · obtain ⟨d, h1, h3, h4⟩ := avoid hq (fun x => I x l) (fun x => I x l') (hpl l)
        (fun x y a b c d => by
          by_contra hne
          exact huv (by rw [twoP x y hne l l' a c b d])) {yc} (by simp)
      exact ⟨Fin.castAdd N d, (Rnc _ _).mpr h1, fun h => h3 ((Rnc _ _).mp h), ne _ _,
        hyc d (by simpa using h4)⟩
  have hFR : ∀ x : Fin (N + N) → Bool, wval C x C.output = true ↔ ∃ u v, R u v ∧ x u = true ∧ x v = true := by
    intro x
    have e : wval C x C.output = circuitFun (N + N) C x := rfl
    rw [e, hF x, decide_eq_true_iff]
    constructor
    · rintro ⟨p, l, h, h1, h2⟩
      exact ⟨_, _, (Rcn p l).mpr h, h1, h2⟩
    · rintro ⟨u, v, ⟨p, l, h, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩, hu, hv⟩
      · rw [e1] at hu; rw [e2] at hv
        exact ⟨p, l, h, hu, hv⟩
      · rw [e1] at hu; rw [e2] at hv
        exact ⟨p, l, h, hv, hu⟩
  have hpos : 0 < N := by rw [hN]; omega
  have := lower R C hC hsym hirr hFR (Fin.castAdd N ⟨0, hpos⟩) (Fin.natAdd N ⟨0, hpos⟩) (ne _ _) hH
  have hs : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_2797

theorem PEqualNP.Outside.L_meta_2797 : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 ∧ (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) ∧ x10.size ≤ (2 : ℕ) * x2) := by
  intro H
  refine PEqualNP.Outside.L_meta_2797.main ?_
  intro x1 x2 x3 _ h1 h2 h3 h4 h5
  obtain ⟨C, hC, hF, _, hs⟩ := H x1 x2 x3 h1 h2 h3 h4 h5
  exact ⟨C, hC, fun x => by rw [hF x], hs⟩
