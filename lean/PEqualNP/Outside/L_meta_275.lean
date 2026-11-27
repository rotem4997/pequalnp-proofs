import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_275

open PEqualNP.CircuitLowerBounds

def pt {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def ind {n : ℕ} (F : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ F)

def Tset {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val (pt p) w = true)

def GateOK {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (t : ℕ) : Prop :=
  (∀ x, val x t = false) ∨ ∃ a b, a < t ∧ b < t ∧
    ((∀ x, val x t = (val x a && val x b)) ∨ (∀ x, val x t = (val x a || val x b)))

lemma mem_Tset {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (w : ℕ) (p : Fin n) :
    p ∈ Tset val w ↔ val (pt p) w = true := by
  simp [Tset]

lemma mono {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t) :
    ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x y hxy hx
    by_cases hw : w < n
    · have h1 := hin x ⟨w, hw⟩
      have h2 := hin y ⟨w, hw⟩
      simp only at h1 h2
      rw [h2]
      rw [h1] at hx
      exact hxy _ hx
    · rcases hg w (not_lt.mp hw) with h0 | ⟨a, b, ha, hb, h | h⟩
      · rw [h0] at hx
        exact absurd hx (by simp)
      · rw [h] at hx
        rw [h]
        simp only [Bool.and_eq_true] at hx ⊢
        exact ⟨ih a ha x y hxy hx.1, ih b hb x y hxy hx.2⟩
      · rw [h] at hx
        rw [h]
        simp only [Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih a ha x y hxy hx)
        · exact Or.inr (ih b hb x y hxy hx)

lemma tset_input {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (w : ℕ) (hw : w < n) :
    (Tset val w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_Tset] at ha hb
  have h1 := hin (pt a) ⟨w, hw⟩
  have h2 := hin (pt b) ⟨w, hw⟩
  simp only at h1 h2
  rw [h1] at ha
  rw [h2] at hb
  simp only [pt, decide_eq_true_eq] at ha hb
  rw [← ha, ← hb]

lemma core {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t)
    (S : Finset (Fin n)) :
    ∀ t, ∀ W : Finset ℕ, W ⊆ Finset.range t →
      ∃ F D : Finset (Fin n), Disjoint F S ∧
        F.card + D.card ≤ W.card + ((Finset.range t).filter
          (fun w => Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card)).card ∧
        ∀ w ∈ W, val (ind F) w = true ∨ ∀ p ∈ S, val (pt p) w = true → p ∈ D := by
  intro t
  induction t with
  | zero =>
    intro W hW
    refine ⟨∅, ∅, by simp, by simp, ?_⟩
    intro w hw
    have := hW hw
    simp at this
  | succ t ih =>
    intro W hW
    have hcnt : ((Finset.range t).filter
          (fun w => Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card)).card ≤ ((Finset.range (t + 1)).filter
          (fun w => Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ t)))
    by_cases htW : t ∈ W
    swap
    · have hW' : W ⊆ Finset.range t := by
        intro w hw
        have h1 := hW hw
        rw [Finset.mem_range] at h1 ⊢
        have : w ≠ t := by
          rintro rfl
          exact htW hw
        omega
      obtain ⟨F, D, hd, hc, hall⟩ := ih W hW'
      exact ⟨F, D, hd, by omega, hall⟩
    · have hW0 : W.erase t ⊆ Finset.range t := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have h1 := hW hw.2
        rw [Finset.mem_range] at h1 ⊢
        have := hw.1
        omega
      have hW0c : (W.erase t).card + 1 = W.card := Finset.card_erase_add_one htW
      by_cases hpriv : Tset val t ⊆ S ∧ 2 ≤ (Tset val t).card
      · have hfc : ((Finset.range (t + 1)).filter
            (fun w => Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card)).card = ((Finset.range t).filter
            (fun w => Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left_of_eq_true _ _ (eq_true hpriv),
            Finset.card_insert_of_notMem (by simp)]
        have hnt : n ≤ t := by
          by_contra hlt
          have := tset_input val hin t (not_le.mp hlt)
          omega
        rcases hg t hnt with h0 | ⟨a, b, ha, hb, hop⟩
        · exfalso
          have hE : Tset val t = ∅ := by
            ext p
            simp [mem_Tset, h0]
          rw [hE] at hpriv
          simp at hpriv
        · have hsub : insert a (insert b (W.erase t)) ⊆ Finset.range t := by
            intro w hw
            rw [Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact Finset.mem_range.mpr ha
            · exact Finset.mem_range.mpr hb
            · exact hW0 hw
          obtain ⟨F, D, hd, hc, hall⟩ := ih _ hsub
          have hcard : (insert a (insert b (W.erase t))).card ≤ (W.erase t).card + 2 := by
            have h1 := Finset.card_insert_le a (insert b (W.erase t))
            have h2 := Finset.card_insert_le b (W.erase t)
            omega
          refine ⟨F, D, hd, by omega, ?_⟩
          intro w hw
          by_cases hwt : w = t
          · rw [hwt]
            have ha' := hall a (by simp)
            have hb' := hall b (by simp)
            rcases hop with h | h
            · rcases ha' with ha1 | ha2
              · rcases hb' with hb1 | hb2
                · left
                  rw [h, ha1, hb1]
                  rfl
                · right
                  intro p hp hv
                  rw [h] at hv
                  simp only [Bool.and_eq_true] at hv
                  exact hb2 p hp hv.2
              · right
                intro p hp hv
                rw [h] at hv
                simp only [Bool.and_eq_true] at hv
                exact ha2 p hp hv.1
            · rcases ha' with ha1 | ha2
              · left
                rw [h, ha1]
                rfl
              · rcases hb' with hb1 | hb2
                · left
                  rw [h, hb1]
                  simp
                · right
                  intro p hp hv
                  rw [h] at hv
                  simp only [Bool.or_eq_true] at hv
                  rcases hv with hv | hv
                  · exact ha2 p hp hv
                  · exact hb2 p hp hv
          · refine hall w ?_
            rw [Finset.mem_insert, Finset.mem_insert]
            exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hwt, hw⟩))
      · obtain ⟨F, D, hd, hc, hall⟩ := ih _ hW0
        by_cases hsub : Tset val t ⊆ S
        · have hsmall : (Tset val t).card ≤ 1 := by
            by_contra h
            exact hpriv ⟨hsub, by omega⟩
          refine ⟨F, D ∪ Tset val t, hd, ?_, ?_⟩
          · have := Finset.card_union_le D (Tset val t)
            omega
          · intro w hw
            by_cases hwt : w = t
            · right
              intro p hp hv
              rw [hwt] at hv
              exact Finset.mem_union_right _ ((mem_Tset val t p).mpr hv)
            · rcases hall w (Finset.mem_erase.mpr ⟨hwt, hw⟩) with h | h
              · exact Or.inl h
              · right
                intro p hp hv
                exact Finset.mem_union_left _ (h p hp hv)
        · obtain ⟨p, hpT, hpS⟩ := Finset.not_subset.mp hsub
          have hpv : val (pt p) t = true := (mem_Tset val t p).mp hpT
          refine ⟨insert p F, D, ?_, ?_, ?_⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hpS, hd⟩
          · have := Finset.card_insert_le p F
            omega
          · intro w hw
            by_cases hwt : w = t
            · left
              rw [hwt]
              refine mono val hin hg t (pt p) (ind (insert p F)) ?_ hpv
              intro q hq
              simp only [pt, ind, decide_eq_true_eq, Finset.mem_insert] at hq ⊢
              exact Or.inl hq
            · rcases hall w (Finset.mem_erase.mpr ⟨hwt, hw⟩) with h | h
              · left
                refine mono val hin hg w (ind F) (ind (insert p F)) ?_ h
                intro q hq
                simp only [ind, decide_eq_true_eq, Finset.mem_insert] at hq ⊢
                exact Or.inr hq
              · exact Or.inr h

lemma fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp
    omega

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih _)

lemma getD_prefix {w l : List Bool} (h : w <+: l) {i : ℕ} (hi : i < w.length) :
    l.getD i false = w.getD i false := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  fold_len C.gates x

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = (C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hpl : ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + j := by
    rw [fold_len, List.length_take, min_eq_left hj.le]
  have hfull : C.wires x = (C.gates.drop (j + 1)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)]) := by
    conv_lhs => rw [Circuit.wires, hsplit, List.foldl_append, List.foldl_cons]
  have hp1 := fold_prefix (C.gates.drop (j + 1)) (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)])
  rw [← hfull] at hp1
  have hp0 := (List.prefix_append _ _).trans hp1
  rw [getD_prefix hp1 (by rw [List.length_append, hpl]; simp)]
  rw [← hpl, List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · rw [hpl, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    exact (getD_prefix hp0 (by rw [hpl]; exact hi)).symm
  · rw [hpl, ite_eq_right_of_eq_false _ _ (eq_false hi)]
    exact List.getD_eq_default _ _ (by rw [hpl]; omega)

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_prefix (fold_prefix C.gates x) hi

lemma main (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (c : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h4 : ∀ (i : Fin m) (p : Fin n),
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i)
    (h5 : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false)
    (hck : ∀ i : Fin m, c i ≤ k) (hcs : ∀ i : Fin m, c i + 1 ≤ (S i).card) :
    ∑ i : Fin m, c i ≤ C.size := by
  set val : (Fin n → Bool) → ℕ → Bool := fun x w => (C.wires (List.ofFn x)).getD w false
    with hval
  have hin : ∀ x (i : Fin n), val x i = x i := by
    intro x i
    simp only [hval]
    rw [wires_input C _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hdead : ∀ x t, n + C.gates.length ≤ t → val x t = false := by
    intro x t ht
    simp only [hval]
    exact List.getD_eq_default _ _ (by rw [wires_len]; simpa using ht)
  have hg : ∀ t, n ≤ t → GateOK val t := by
    intro t ht
    by_cases htG : n + C.gates.length ≤ t
    · exact Or.inl (fun x => hdead x t htG)
    · have hj : t - n < C.gates.length := by omega
      obtain ⟨hop, hlen⟩ := hgates _ (List.getElem_mem hj)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      have key : ∀ x, val x t = (C.gates[t - n]).op.eval
          [if a < t then val x a else false, if b < t then val x b else false] := by
        intro x
        have h := wires_gate C (List.ofFn x) (t - n) hj
        simp only [List.length_ofFn] at h
        have e : n + (t - n) = t := by omega
        rw [e, hab] at h
        simpa [hval] using h
      by_cases ha : a < t <;> by_cases hb : b < t <;> rcases hop with hop | hop
      all_goals simp only [hop, ha, hb, ↓reduceIte, GateOp.eval] at key
      · exact Or.inr ⟨a, b, ha, hb, Or.inl (fun x => by rw [key x]; simp)⟩
      · exact Or.inr ⟨a, b, ha, hb, Or.inr (fun x => by rw [key x]; simp)⟩
      · exact Or.inl (fun x => by rw [key x]; simp)
      · exact Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by rw [key x]; simp)⟩
      · exact Or.inl (fun x => by rw [key x]; simp)
      · exact Or.inr ⟨b, b, hb, hb, Or.inr (fun x => by rw [key x]; simp)⟩
      · exact Or.inl (fun x => by rw [key x]; simp)
      · exact Or.inl (fun x => by rw [key x]; simp)
  have hbound : ∀ i : Fin m, c i ≤ ((Finset.Ico n (n + C.gates.length)).filter
      (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card)).card := by
    intro i
    obtain ⟨F, D, hd, hc, hall⟩ := core val hin hg (S i) (o i + 1) {o i} (by simp)
    have hle : ((Finset.range (o i + 1)).filter
        (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card)).card ≤
        ((Finset.Ico n (n + C.gates.length)).filter
        (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card)).card := by
      apply Finset.card_le_card
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨?_, hw.2⟩
      rw [Finset.mem_Ico]
      constructor
      · by_contra hlt
        have := tset_input val hin w (not_le.mp hlt)
        omega
      · by_contra hge
        have hE : Tset val w = ∅ := by
          ext p
          simp [mem_Tset, hdead _ w (not_lt.mp hge)]
        rw [hE] at hw
        simp at hw
    rw [Finset.card_singleton] at hc
    rcases hall (o i) (by simp) with h | h
    · have hF : k < F.card := by
        by_contra hk
        have hx := h5 i (ind F) (by
          have : Finset.univ.filter (fun q : Fin n => ind F q = true) = F := by
            ext q
            simp [ind]
          rw [this]
          omega) (by
          intro q hq
          simp only [ind, decide_eq_false_iff_not]
          exact fun hqF => Finset.disjoint_left.mp hd hqF hq)
        have h' : (C.wires (List.ofFn (ind F))).getD (o i) false = true := h
        rw [hx] at h'
        exact absurd h' (by simp)
      have := hck i
      omega
    · have hSD : S i ⊆ D := by
        intro p hp
        exact h p hp ((h4 i p).mpr hp)
      have := Finset.card_le_card hSD
      have := hcs i
      omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint
      ((Finset.Ico n (n + C.gates.length)).filter
        (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card))
      ((Finset.Ico n (n + C.gates.length)).filter
        (fun w => Tset val w ⊆ S j ∧ 2 ≤ (Tset val w).card)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    rw [Finset.mem_filter] at hwi hwj
    have h1 : Tset val w ⊆ S i ∩ S j := Finset.subset_inter hwi.2.1 hwj.2.1
    have h2 := Finset.card_le_card h1
    have h3 := hS i j hij
    have h4 := hwi.2.2
    omega
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, ((Finset.Ico n (n + C.gates.length)).filter
        (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card)).card :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Finset.univ.biUnion (fun i : Fin m => (Finset.Ico n (n + C.gates.length)).filter
        (fun w => Tset val w ⊆ S i ∧ 2 ≤ (Tset val w).card))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_biUnion] at hw
        obtain ⟨i, _, hw⟩ := hw
        exact (Finset.mem_filter.mp hw).1
    _ = C.size := by
        rw [Nat.card_Ico, Circuit.size]
        omega

end PEqualNP.Outside.L_meta_275

theorem PEqualNP.Outside.L_meta_275 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), C.size ≤ 7 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 4, (∀ p : Fin 7, (C.wires (List.ofFn (fun q : Fin 7 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i) ∧ ∀ x : Fin 7 → Bool, (Finset.univ.filter (fun q : Fin 7 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsize, hgates, hout⟩
  have h := PEqualNP.Outside.L_meta_275.main 7 4 2
    (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) C o (fun _ => 2)
    (by decide) hgates (fun i p => (hout i).1 p) (fun i x => (hout i).2 x)
    (fun _ => le_rfl) (by decide)
  have h8 : ∑ _i : Fin 4, 2 = 8 := by decide
  rw [h8] at h
  omega
