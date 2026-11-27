import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2053

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem idx_of (l : List ℕ) (hl : l.length ≤ 2) (p : ℕ) (hp : p ∈ l) :
    ∃ i, i < 2 ∧ l.getD i 0 = p := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  exact ⟨i, by omega, List.getD_eq_getElem _ _ hi⟩

def oh {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k = i)

def pr {n : ℕ} (i j : Fin n) : Fin n → Bool := fun k => decide (k = i) || decide (k = j)

def inp (C : Circuit) (j k : ℕ) : ℕ := (gateAt C j).inputs.getD k 0

theorem oh_le_pr_left {n : ℕ} (i j : Fin n) : ∀ v, oh i v = true → pr i j v = true := by
  intro v hv
  simp only [oh, pr, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
  exact Or.inl hv

theorem oh_le_pr_right {n : ℕ} (i j : Fin n) : ∀ v, oh j v = true → pr i j v = true := by
  intro v hv
  simp only [oh, pr, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
  exact Or.inr hv

theorem cA_ne_nA {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := p.isLt
  omega

theorem cA_inj {N : ℕ} : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  have h1 := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_castAdd] at h1
  exact Fin.ext h1

theorem nA_inj {N : ℕ} : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  have h1 := congrArg Fin.val h
  rw [Fin.val_natAdd, Fin.val_natAdd] at h1
  exact Fin.ext (by omega)

theorem two_slots (L : List ℕ) (hl : L.length ≤ 2) (u1 u2 : ℕ) (h1 : u1 ∈ L) (h2 : u2 ∈ L)
    (hne : u1 ≠ u2) :
    ∃ k, k < 2 ∧ L.getD k 0 = u2 ∧ L.getD (1 - k) 0 = u1 ∧
      ∀ u ∈ L, u = L.getD k 0 ∨ u = L.getD (1 - k) 0 := by
  match L, hl, h1, h2 with
  | [], _, h1, _ => simp at h1
  | [a], _, h1, h2 =>
    simp only [List.mem_singleton] at h1 h2
    omega
  | [a, b], _, h1, h2 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · omega
      · refine ⟨0, by omega, h2.symm, h1.symm, ?_⟩
        intro u hu
        simpa using hu
    · rcases h1 with h1 | h1
      · refine ⟨1, by omega, h2.symm, h1.symm, ?_⟩
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu | hu
        · exact Or.inr hu
        · exact Or.inl hu
      · omega
  | a :: b :: c :: t, hl, _, _ =>
    have : (a :: b :: c :: t).length = t.length + 3 := rfl
    omega

theorem descent (n : ℕ) (C : Circuit) (hm : Monotone2 C) (i1 i2 : Fin n) :
    ∀ w, val C.gates w (pr i1 i2) = true → val C.gates w (oh i1) = false →
      val C.gates w (oh i2) = false →
      ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ ∃ k, k < 2 ∧
        val C.gates (inp C j k) (oh i1) = true ∧ val C.gates (inp C j (1 - k)) (oh i2) = true ∧
        ∀ u ∈ (gateAt C j).inputs, u = inp C j k ∨ u = inp C j (1 - k) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h h1 h2
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn] at h
      rw [val_input C.gates _ w hwn] at h1
      rw [val_input C.gates _ w hwn] at h2
      simp only [pr, oh, Bool.or_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at h h1 h2
      rcases h with h | h
      · exact absurd h h1
      · exact absurd h h2
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        have hga := gateAt_eq C (w - n) hi
        rw [← he] at h h1 h2
        rcases (legal_of C hm C.gates[w - n] (List.getElem_mem hi)) with ⟨ha | ho, hlen⟩
        · have hall := (val_and C.gates _ (w - n) hi ha).1 h
          by_cases hex : ∃ u ∈ C.gates[w - n].inputs,
              val C.gates u (oh i1) = false ∧ val C.gates u (oh i2) = false
          · obtain ⟨u, hu, hu1, hu2⟩ := hex
            exact ih u (by have := (hall u hu).1; omega) (hall u hu).2 hu1 hu2
          · have hx1 : ∃ u ∈ C.gates[w - n].inputs, val C.gates u (oh i1) = false := by
              by_contra hc
              have := (val_and C.gates (oh i1) (w - n) hi ha).2 (fun u hu => ⟨(hall u hu).1, by
                by_contra hq
                exact hc ⟨u, hu, by simpa using hq⟩⟩)
              rw [this] at h1
              exact Bool.noConfusion h1
            have hx2 : ∃ u ∈ C.gates[w - n].inputs, val C.gates u (oh i2) = false := by
              by_contra hc
              have := (val_and C.gates (oh i2) (w - n) hi ha).2 (fun u hu => ⟨(hall u hu).1, by
                by_contra hq
                exact hc ⟨u, hu, by simpa using hq⟩⟩)
              rw [this] at h2
              exact Bool.noConfusion h2
            obtain ⟨u1, hu1m, hu1⟩ := hx1
            obtain ⟨u2, hu2m, hu2⟩ := hx2
            have hu1' : val C.gates u1 (oh i2) = true := by
              by_contra hq
              exact hex ⟨u1, hu1m, hu1, by simpa using hq⟩
            have hu2' : val C.gates u2 (oh i1) = true := by
              by_contra hq
              exact hex ⟨u2, hu2m, by simpa using hq, hu2⟩
            have hne : u1 ≠ u2 := by
              intro hq
              rw [hq, hu2'] at hu1
              exact Bool.noConfusion hu1
            obtain ⟨k, hk, hk2, hk1, hkall⟩ :=
              two_slots C.gates[w - n].inputs hlen u1 u2 hu1m hu2m hne
            refine ⟨w - n, hi, by rw [hga]; exact ha, k, hk, ?_, ?_, ?_⟩
            · unfold inp
              rw [hga, hk2]
              exact hu2'
            · unfold inp
              rw [hga, hk1]
              exact hu1'
            · unfold inp
              rw [hga]
              exact hkall
        · obtain ⟨u, hu, hult, huv⟩ := (val_or C.gates _ (w - n) hi ho).1 h
          have hf1 : val C.gates u (oh i1) = false := by
            by_contra hq
            have := (val_or C.gates (oh i1) (w - n) hi ho).2 ⟨u, hu, hult, by simpa using hq⟩
            rw [this] at h1
            exact Bool.noConfusion h1
          have hf2 : val C.gates u (oh i2) = false := by
            by_contra hq
            have := (val_or C.gates (oh i2) (w - n) hi ho).2 ⟨u, hu, hult, by simpa using hq⟩
            rw [this] at h2
            exact Bool.noConfusion h2
          exact ih u (by omega) huv hf1 hf2

theorem minw (N n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hoff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ i : Fin n, val C.gates (n + j) (oh i) = false)
    (ι : Fin N → Fin n) (hι : Function.Injective ι) (R : Fin N → Prop) (l : Fin N) :
    ∀ b, val C.gates b (oh (ι l)) = true →
      (∃ l', l' ≠ l ∧ val C.gates b (oh (ι l')) = true) →
      (∀ l', val C.gates b (oh (ι l')) = true → R l') →
      ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ∃ k, k < 2 ∧
        (∀ l', val C.gates (inp C j k) (oh (ι l')) = true ↔ l' = l) ∧
        val C.gates (n + j) (oh (ι l)) = true ∧
        (∃ l', l' ≠ l ∧ val C.gates (n + j) (oh (ι l')) = true) ∧
        (∀ l', val C.gates (n + j) (oh (ι l')) = true → R l') := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h1 h2 h3
    obtain ⟨l2, hl2, hw2⟩ := h2
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn] at h1
      rw [val_input C.gates _ w hwn] at hw2
      simp only [oh, decide_eq_true_eq] at h1 hw2
      exact absurd (hι (hw2.symm.trans h1)) hl2
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at h1
        exact Bool.noConfusion h1
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        have hga := gateAt_eq C (w - n) hi
        rcases (legal_of C hm C.gates[w - n] (List.getElem_mem hi)) with ⟨ha | ho, hlen⟩
        · have := hoff (w - n) hi (by rw [hga]; exact ha) (ι l)
          rw [he, h1] at this
          exact Bool.noConfusion this
        · have h1' := h1
          rw [← he] at h1'
          obtain ⟨u, hu, hult, huv⟩ := (val_or C.gates _ (w - n) hi ho).1 h1'
          have hsub : ∀ x : Fin n → Bool, val C.gates u x = true → val C.gates w x = true := by
            intro x hx
            rw [← he]
            exact (val_or C.gates x (w - n) hi ho).2 ⟨u, hu, hult, hx⟩
          by_cases hex : ∃ l', l' ≠ l ∧ val C.gates u (oh (ι l')) = true
          · exact ih u (by omega) huv hex (fun l' hl' => h3 l' (hsub _ hl'))
          · obtain ⟨k, hk, hke⟩ := idx_of C.gates[w - n].inputs hlen u hu
            have hinp : inp C (w - n) k = u := by
              unfold inp
              rw [hga]
              exact hke
            refine ⟨w - n, hi, by rw [hga]; exact ho, k, hk, ?_, by rw [he]; exact h1,
              ⟨l2, hl2, by rw [he]; exact hw2⟩, by rw [he]; exact h3⟩
            rw [hinp]
            intro l'
            constructor
            · intro hl'
              by_contra hne
              exact hex ⟨l', hne, hl'⟩
            · intro hq
              rw [hq]
              exact huv

theorem clean_pair (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C)
    (hoff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ i : Fin (N + N), val C.gates (N + N + j) (oh i) = false)
    (hcl : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
      val C.gates (N + N + j) z = true →
      val C.gates (N + N + j) (fun ka : Fin (N + N) => decide (ka.val < N) && z ka) = true ∨
      val C.gates (N + N + j) (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (a b : ℕ)
    (hab : ∀ u ∈ (gateAt C j).inputs, u = a ∨ u = b) (p l : Fin N)
    (hp : val C.gates a (oh (Fin.castAdd N p)) = true)
    (hl : val C.gates b (oh (Fin.natAdd N l)) = true) : I p l := by
  have legal := legal_of C hm
  have hga := gateAt_eq C j hj
  have hop' : C.gates[j].op = GateOp.and := by rw [← hga]; exact hop
  have hz : val C.gates (N + N + j) (pr (Fin.castAdd N p) (Fin.natAdd N l)) = true := by
    apply (val_and C.gates _ j hj hop').2
    intro u hu
    have hu' : u ∈ (gateAt C j).inputs := by rw [hga]; exact hu
    refine ⟨hrb j hj u hu', ?_⟩
    rcases hab u hu' with hq | hq
    · rw [hq]
      exact val_mono C.gates legal _ _ (oh_le_pr_left _ _) _ hp
    · rw [hq]
      exact val_mono C.gates legal _ _ (oh_le_pr_right _ _) _ hl
  rcases hcl j hj hop _ hz with h | h | ⟨p', l', hI, hp', hl'⟩
  · have := val_mono C.gates legal _ (oh (Fin.castAdd N p)) (fun v hv => by
      simp only [pr, oh, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
      rcases hv with ⟨hlt, hv | hv⟩
      · exact hv
      · rw [hv, Fin.val_natAdd] at hlt
        omega) _ h
    rw [hoff j hj hop] at this
    exact Bool.noConfusion this
  · have := val_mono C.gates legal _ (oh (Fin.natAdd N l)) (fun v hv => by
      simp only [pr, oh, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
      rcases hv with ⟨hlt, hv | hv⟩
      · rw [hv, Fin.val_castAdd] at hlt
        have := p.isLt
        omega
      · exact hv) _ h
    rw [hoff j hj hop] at this
    exact Bool.noConfusion this
  · simp only [pr, Bool.or_eq_true, decide_eq_true_eq] at hp' hl'
    have e1 : p' = p := by
      rcases hp' with hq | hq
      · exact cA_inj hq
      · exact absurd hq (cA_ne_nA p' l)
    have e2 : l' = l := by
      rcases hl' with hq | hq
      · exact absurd hq.symm (cA_ne_nA p l')
      · exact nA_inj hq
    rw [← e1, ← e2]
    exact hI

def Rel (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (e : Fin N × Fin N) (t : ℕ × ℕ) : Prop :=
  ((gateAt C t.1).op = GateOp.and ∧ t.2 < 2 ∧
      (∀ p', val C.gates (inp C t.1 t.2) (oh (Fin.castAdd N p')) = true ↔ p' = e.1) ∧
      (∀ l', val C.gates (inp C t.1 (1 - t.2)) (oh (Fin.natAdd N l')) = true ↔ l' = e.2)) ∨
  ((gateAt C t.1).op = GateOp.or ∧ t.2 < 2 ∧
      (∀ l', val C.gates (inp C t.1 t.2) (oh (Fin.natAdd N l')) = true ↔ l' = e.2) ∧
      (∃ l', l' ≠ e.2 ∧ val C.gates (N + N + t.1) (oh (Fin.natAdd N l')) = true) ∧
      val C.gates (N + N + t.1) (oh (Fin.natAdd N e.2)) = true ∧
      (∀ l', val C.gates (N + N + t.1) (oh (Fin.natAdd N l')) = true → I e.1 l')) ∨
  ((gateAt C t.1).op = GateOp.or ∧ 2 ≤ t.2 ∧
      (∀ p', val C.gates (inp C t.1 (t.2 - 2)) (oh (Fin.castAdd N p')) = true ↔ p' = e.1) ∧
      (∃ p', p' ≠ e.1 ∧ val C.gates (N + N + t.1) (oh (Fin.castAdd N p')) = true) ∧
      val C.gates (N + N + t.1) (oh (Fin.castAdd N e.1)) = true ∧
      (∀ p', val C.gates (N + N + t.1) (oh (Fin.castAdd N p')) = true → I p' e.2))

theorem rel_fun (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (e e' : Fin N × Fin N) (t : ℕ × ℕ) (h : Rel N I C e t) (h' : Rel N I C e' t) : e = e' := by
  obtain ⟨p, l⟩ := e
  obtain ⟨p', l'⟩ := e'
  unfold Rel at h h'
  dsimp only at h h'
  rcases h with ⟨ho, hc, hP, hL⟩ | ⟨ho, hc, hL, ⟨l2, hl2, hl2v⟩, hlv, hI⟩ |
    ⟨ho, hc, hP, ⟨p2, hp2, hp2v⟩, hpv, hI⟩
  · rcases h' with ⟨ho', hc', hP', hL'⟩ | ⟨ho', _⟩ | ⟨ho', _⟩
    · have e1 : p = p' := (hP' p).1 ((hP p).2 rfl)
      have e2 : l = l' := (hL' l).1 ((hL l).2 rfl)
      rw [e1, e2]
    · rw [ho] at ho'
      exact GateOp.noConfusion ho'
    · rw [ho] at ho'
      exact GateOp.noConfusion ho'
  · rcases h' with ⟨ho', _⟩ | ⟨ho', hc', hL', ⟨l3, hl3, hl3v⟩, hlv', hI'⟩ | ⟨ho', hc', _⟩
    · rw [ho] at ho'
      exact GateOp.noConfusion ho'
    · have e2 : l = l' := (hL' l).1 ((hL l).2 rfl)
      subst e2
      have e1 : p = p' := by
        by_contra hne
        exact h4 p p' l l2 hne (Ne.symm hl2) ⟨hI l hlv, hI l2 hl2v, hI' l hlv, hI' l2 hl2v⟩
      rw [e1]
    · omega
  · rcases h' with ⟨ho', _⟩ | ⟨ho', hc', _⟩ | ⟨ho', hc', hP', ⟨p3, hp3, hp3v⟩, hpv', hI'⟩
    · rw [ho] at ho'
      exact GateOp.noConfusion ho'
    · omega
    · have e1 : p = p' := (hP' p).1 ((hP p).2 rfl)
      subst e1
      have e2 : l = l' := by
        by_contra hne
        exact h4 p p2 l l' (Ne.symm hp2) hne ⟨hI p hpv, hI' p hpv, hI p2 hp2v, hI' p2 hp2v⟩
      rw [e2]

theorem exists_rel (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool, val C.gates C.output z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hcl : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
      val C.gates (N + N + j) z = true →
      val C.gates (N + N + j) (fun ka : Fin (N + N) => decide (ka.val < N) && z ka) = true ∨
      val C.gates (N + N + j) (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hoff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ i : Fin (N + N), val C.gates (N + N + j) (oh i) = false)
    (p l : Fin N) (hI : I p l) :
    ∃ t ∈ Finset.range C.gates.length ×ˢ Finset.range 4, Rel N I C (p, l) t := by
  have ho1 : val C.gates C.output (oh (Fin.castAdd N p)) = false := by
    cases hv : val C.gates C.output (oh (Fin.castAdd N p)) with
    | false => rfl
    | true =>
      obtain ⟨p', l', _, h1, h2⟩ := (hf (oh (Fin.castAdd N p))).1 hv
      exact absurd (of_decide_eq_true h2).symm (cA_ne_nA p l')
  have ho2 : val C.gates C.output (oh (Fin.natAdd N l)) = false := by
    cases hv : val C.gates C.output (oh (Fin.natAdd N l)) with
    | false => rfl
    | true =>
      obtain ⟨p', l', _, h1, h2⟩ := (hf (oh (Fin.natAdd N l))).1 hv
      exact absurd (of_decide_eq_true h1) (cA_ne_nA p' l)
  have ho : val C.gates C.output (pr (Fin.castAdd N p) (Fin.natAdd N l)) = true :=
    (hf _).2 ⟨p, l, hI, by simp [pr], by simp [pr]⟩
  obtain ⟨j, hj, hop, k, hk, ha, hb, hab⟩ := descent (N + N) C hm _ _ C.output ho ho1 ho2
  have hcp : ∀ p' l', val C.gates (inp C j k) (oh (Fin.castAdd N p')) = true →
      val C.gates (inp C j (1 - k)) (oh (Fin.natAdd N l')) = true → I p' l' :=
    fun p' l' h1 h2 => clean_pair N I C hm hrb hoff hcl j hj hop _ _ hab p' l' h1 h2
  by_cases hL : ∃ l', l' ≠ l ∧ val C.gates (inp C j (1 - k)) (oh (Fin.natAdd N l')) = true
  · obtain ⟨j', hj', hop', k', hk', hs, hv, hex, hR⟩ :=
      minw N (N + N) C hm hoff (Fin.natAdd N) nA_inj (fun l' => I p l') l
        (inp C j (1 - k)) hb hL (fun l' hl' => hcp p l' ha hl')
    refine ⟨(j', k'), ?_, Or.inr (Or.inl ⟨hop', hk', hs, hex, hv, hR⟩)⟩
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 hj', Finset.mem_range.2 (by omega)⟩
  · by_cases hP : ∃ p', p' ≠ p ∧ val C.gates (inp C j k) (oh (Fin.castAdd N p')) = true
    · obtain ⟨j', hj', hop', k', hk', hs, hv, hex, hR⟩ :=
        minw N (N + N) C hm hoff (Fin.castAdd N) cA_inj (fun p' => I p' l) p
          (inp C j k) ha hP (fun p' hp' => hcp p' l hp' hb)
      have h22 : 2 + k' - 2 = k' := by omega
      refine ⟨(j', 2 + k'), ?_, Or.inr (Or.inr ⟨hop', Nat.le_add_right 2 k', ?_, hex, hv, hR⟩)⟩
      · exact Finset.mem_product.2 ⟨Finset.mem_range.2 hj', Finset.mem_range.2 (by omega)⟩
      · show ∀ p', val C.gates (inp C j' (2 + k' - 2)) (oh (Fin.castAdd N p')) = true ↔ p' = p
        rw [h22]
        exact hs
    · refine ⟨(j, k), ?_, Or.inl ⟨hop, hk, ?_, ?_⟩⟩
      · exact Finset.mem_product.2 ⟨Finset.mem_range.2 hj, Finset.mem_range.2 (by omega)⟩
      · intro p'
        constructor
        · intro hq
          by_contra hne
          exact hP ⟨p', hne, hq⟩
        · intro hq
          rw [hq]
          exact ha
      · intro l'
        constructor
        · intro hq
          by_contra hne
          exact hL ⟨l', hne, hq⟩
        · intro hq
          rw [hq]
          exact hb

theorem main (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hm : Monotone2 C) (hrb : ReadsBack (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool, val C.gates C.output z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hcl : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
      val C.gates (N + N + j) z = true →
      val C.gates (N + N + j) (fun ka : Fin (N + N) => decide (ka.val < N) && z ka) = true ∨
      val C.gates (N + N + j) (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (h6 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∀ p : Fin N, val C.gates (N + N + j) (oh (Fin.castAdd N p)) = false) ∧
      ∀ l : Fin N, val C.gates (N + N + j) (oh (Fin.natAdd N l)) = false) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 5 * C.size + 1 := by
  have hoff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ i : Fin (N + N), val C.gates (N + N + j) (oh i) = false := by
    intro j hj hop i
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · exact (h6 j hj hop).1 p
    · exact (h6 j hj hop).2 l
  refine le_trans (Finset.card_le_card_of_forall_subsingleton (Rel N I C)
    (t := Finset.range C.gates.length ×ˢ Finset.range 4) ?_ ?_) ?_
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨p, l⟩ := e
    exact exists_rel N I C hm hrb hf hcl hoff p l he.2
  · intro t _ e he e2 he2
    exact rel_fun N I C h4 e e2 t he.2 he2.2
  · rw [Finset.card_product, Finset.card_range, Finset.card_range]
    show C.gates.length * 4 ≤ 5 * C.gates.length + 1
    omega

end PEqualNP.Outside.L_meta_2053

theorem PEqualNP.Outside.L_meta_2053 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 5 * C.size + 1 := by
  intro N I _ C h4 hm hrb hf hcl h6
  exact PEqualNP.Outside.L_meta_2053.main N I C h4 hm hrb hf hcl h6
